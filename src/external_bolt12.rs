// This file is Copyright its original authors, visible in version control history.
//
// This file is licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. You may not use this file except in
// accordance with one or both of these licenses.

//! BOLT12 invoices for offers this node carries but does not issue.
//!
//! An external issuer, such as a federation that threshold-signs invoices, can publish offers whose
//! invoice requests reach this node over onion messages. The application installs a handler that
//! claims those requests instead of [`ChannelManager`], obtains a signed invoice elsewhere, and
//! sends it back over the payer's reply path with [`Node::respond_external_bolt12`]. The payment
//! hash comes from the issuer, so the node never learns the preimage up front: the payment surfaces
//! as [`Event::PaymentClaimable`] and is settled with [`Bolt11Payment::claim_for_hash`] or failed
//! with [`Bolt11Payment::fail_for_hash`].
//!
//! Requests for offers the node issued itself still go to [`ChannelManager`].
//!
//! [`ChannelManager`]: lightning::ln::channelmanager::ChannelManager
//! [`Event::PaymentClaimable`]: crate::Event::PaymentClaimable
//! [`Bolt11Payment::claim_for_hash`]: crate::payment::Bolt11Payment::claim_for_hash
//! [`Bolt11Payment::fail_for_hash`]: crate::payment::Bolt11Payment::fail_for_hash

use std::sync::{Arc, Mutex, RwLock};

use bitcoin::secp256k1::Secp256k1;
use lightning::blinded_path::message::{BlindedMessagePath, MessageContext, OffersContext};
use lightning::blinded_path::payment::{
	BlindedPaymentPath, Bolt12OfferContext, PaymentConstraints, PaymentContext,
	UnauthenticatedReceiveTlvs,
};
use lightning::ln::channelmanager::PaymentId;
use lightning::offers::invoice::Bolt12Invoice;
use lightning::offers::invoice_request::{InvoiceRequest, InvoiceRequestFields, PAYER_NOTE_LIMIT};
use lightning::offers::nonce::Nonce;
use lightning::offers::offer::OfferId;
use lightning::onion_message::messenger::{
	MessageSendInstructions, Responder, ResponseInstruction,
};
use lightning::onion_message::offers::{OffersMessage, OffersMessageHandler};
use lightning::sign::NodeSigner;
use lightning_types::payment::PaymentHash;
use lightning_types::string::UntrustedString;

use crate::error::Error;
use crate::payment::{PaymentDetails, PaymentDirection, PaymentKind, PaymentStatus};
use crate::types::ChannelManager;
use crate::Node;

/// The most invoices that may wait to be sent at once.
pub const MAX_PENDING_EXTERNAL_INVOICES: usize = 32;

/// The final CLTV expiry delta an externally issued invoice's payment path advertises.
///
/// The payment is claimed manually once the application learns the preimage, so the payer is asked
/// to leave that much time. Per BOLT 4 the delta is folded into the blinded path's payinfo, not into
/// the final onion payload, so the node cannot enforce it: a payer that ignores the payinfo can
/// still send an HTLC that expires sooner. The application must check the deadline of the HTLC it
/// actually holds.
pub const EXTERNAL_PAYMENT_MIN_FINAL_CLTV_EXPIRY_DELTA: u16 = 144;

/// How long the node accepts a payment for a registered hash.
const EXTERNAL_PAYMENT_EXPIRY_SECS: u32 = 3600;

/// How far beyond the current height a payment path accepts an HTLC's expiry.
const EXTERNAL_PAYMENT_MAX_CLTV_EXPIRY_DELTA: u32 = 2016;

/// An invoice request claimed by the application, together with the payer's reply path.
pub struct ExternalInvoiceRequest {
	request: InvoiceRequest,
	responder: Responder,
}

impl ExternalInvoiceRequest {
	/// The request as the payer signed it.
	pub fn invoice_request(&self) -> &InvoiceRequest {
		&self.request
	}
}

impl std::fmt::Debug for ExternalInvoiceRequest {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("ExternalInvoiceRequest").finish_non_exhaustive()
	}
}

/// Decides, while the onion message is being processed, whether the application takes a request.
///
/// It must return quickly and must not block: anything slow, such as asking a remote signer,
/// belongs in a task the handler hands the request to. Returning `Ok(())` consumes the request,
/// including one the application drops because it is overloaded. Returning the request back passes
/// it on to [`ChannelManager`].
///
/// [`ChannelManager`]: lightning::ln::channelmanager::ChannelManager
pub type ExternalRequestHandler =
	dyn Fn(ExternalInvoiceRequest) -> Result<(), ExternalInvoiceRequest> + Send + Sync;

pub(crate) struct ExternalOffersHandler {
	channel_manager: Arc<ChannelManager>,
	handler: RwLock<Option<Arc<ExternalRequestHandler>>>,
	pending: Mutex<Vec<(OffersMessage, MessageSendInstructions)>>,
}

impl ExternalOffersHandler {
	pub(crate) fn new(channel_manager: Arc<ChannelManager>) -> Self {
		Self { channel_manager, handler: RwLock::new(None), pending: Mutex::new(Vec::new()) }
	}

	/// Offers `request` to the application's handler. Returns it if the handler declined it, or if
	/// none is installed, so it goes on to [`ChannelManager`].
	fn try_external(&self, request: ExternalInvoiceRequest) -> Option<ExternalInvoiceRequest> {
		let Some(handler) = self.handler.read().unwrap().clone() else {
			return Some(request);
		};

		handler(request).err()
	}
}

impl OffersMessageHandler for ExternalOffersHandler {
	fn handle_message(
		&self, message: OffersMessage, context: Option<OffersContext>, responder: Option<Responder>,
	) -> Option<(OffersMessage, ResponseInstruction)> {
		let (message, responder) = match (message, responder) {
			(OffersMessage::InvoiceRequest(request), Some(responder)) => {
				match self.try_external(ExternalInvoiceRequest { request, responder }) {
					None => return None,
					Some(ExternalInvoiceRequest { request, responder }) => {
						(OffersMessage::InvoiceRequest(request), Some(responder))
					},
				}
			},
			other => other,
		};

		self.channel_manager.handle_message(message, context, responder)
	}

	fn release_pending_messages(&self) -> Vec<(OffersMessage, MessageSendInstructions)> {
		let mut pending = std::mem::take(&mut *self.pending.lock().unwrap());

		pending.extend(self.channel_manager.release_pending_messages());
		pending
	}
}

/// The request fields a payment path echoes back when the payment arrives.
fn request_fields(request: &InvoiceRequest) -> InvoiceRequestFields {
	let payer_note_truncated = request.payer_note().map(|note| {
		let mut end = note.0.len().min(PAYER_NOTE_LIMIT);

		while !note.0.is_char_boundary(end) {
			end -= 1;
		}

		UntrustedString(note.0[..end].to_string())
	});

	InvoiceRequestFields {
		payer_signing_pubkey: request.payer_signing_pubkey(),
		quantity: request.quantity(),
		payer_note_truncated,
		human_readable_name: *request.offer_from_hrn(),
	}
}

impl Node {
	/// Installs the handler that decides which invoice requests the application answers itself.
	///
	/// See [`ExternalRequestHandler`] for what the handler may do.
	pub fn set_external_bolt12_request_handler(&self, handler: Arc<ExternalRequestHandler>) {
		*self.external_offers_handler.handler.write().unwrap() = Some(handler);
	}

	/// Queues an externally signed invoice for delivery over the request's reply path.
	///
	/// Fails if [`MAX_PENDING_EXTERNAL_INVOICES`] invoices are already waiting to be sent.
	pub fn respond_external_bolt12(
		&self, request: ExternalInvoiceRequest, invoice: Bolt12Invoice,
	) -> Result<(), Error> {
		let mut pending = self.external_offers_handler.pending.lock().unwrap();

		if pending.len() >= MAX_PENDING_EXTERNAL_INVOICES {
			return Err(Error::InvoiceCreationFailed);
		}

		pending.push((
			OffersMessage::Invoice(invoice),
			request.responder.respond().into_instructions(),
		));

		Ok(())
	}

	/// A blinded path through which payers can send invoice requests to this node.
	///
	/// An external issuer puts it in the offers it publishes.
	pub fn external_bolt12_message_path(&self) -> BlindedMessagePath {
		BlindedMessagePath::one_hop(
			self.node_id(),
			self.keys_manager.get_receive_auth_key(),
			MessageContext::Offers(OffersContext::InvoiceRequest {
				nonce: Nonce::from_entropy_source(&*self.keys_manager),
			}),
			&*self.keys_manager,
			&Secp256k1::new(),
		)
	}

	/// Expects a payment for an externally issued invoice and returns the path the payer must use.
	///
	/// The node does not know the preimage of `payment_hash`, so the payment must be claimed
	/// manually. Registering the same hash again for the same request and amount returns a fresh path
	/// for the existing registration; anything else already known under the hash is refused.
	///
	/// The path asks payers for [`EXTERNAL_PAYMENT_MIN_FINAL_CLTV_EXPIRY_DELTA`] blocks of expiry,
	/// which the node cannot enforce. A caller must check the deadline of the HTLC it actually holds
	/// before acting on it.
	pub fn register_external_bolt12_payment(
		&self, payment_hash: PaymentHash, amount_msat: u64, request: &InvoiceRequest,
		offer_id: OfferId,
	) -> Result<BlindedPaymentPath, Error> {
		let payment_id = PaymentId(payment_hash.0);
		let fields = request_fields(request);

		let payment_secret = match self.payment_store.get(&payment_id) {
			Some(existing) => match existing.kind {
				PaymentKind::Bolt12Offer {
					hash: Some(existing_hash),
					preimage: None,
					secret: Some(secret),
					offer_id: existing_offer_id,
					quantity,
					payer_note,
				} if existing.direction == PaymentDirection::Inbound
					&& existing.status == PaymentStatus::Pending
					&& existing.amount_msat == Some(amount_msat)
					&& existing_hash == payment_hash
					&& existing_offer_id == offer_id
					&& quantity == fields.quantity
					&& payer_note == fields.payer_note_truncated =>
				{
					secret
				},
				_ => return Err(Error::DuplicatePayment),
			},
			None => {
				let secret = self
					.channel_manager
					// The final payload of a blinded payment excludes the path's CLTV delta,
					// so requiring it here would reject every correctly built payment.
					.create_inbound_payment_for_hash(
						payment_hash,
						Some(amount_msat),
						EXTERNAL_PAYMENT_EXPIRY_SECS,
						None,
					)
					.map_err(|()| Error::InvoiceCreationFailed)?;

				let kind = PaymentKind::Bolt12Offer {
					hash: Some(payment_hash),
					preimage: None,
					secret: Some(secret),
					offer_id,
					payer_note: fields.payer_note_truncated.clone(),
					quantity: fields.quantity,
				};

				self.payment_store.insert(PaymentDetails::new(
					payment_id,
					kind,
					Some(amount_msat),
					None,
					PaymentDirection::Inbound,
					PaymentStatus::Pending,
				))?;

				secret
			},
		};

		let tlvs = UnauthenticatedReceiveTlvs {
			payment_secret,
			payment_constraints: PaymentConstraints {
				max_cltv_expiry: self
					.channel_manager
					.current_best_block()
					.height
					.saturating_add(EXTERNAL_PAYMENT_MAX_CLTV_EXPIRY_DELTA)
					.saturating_add(u32::from(EXTERNAL_PAYMENT_MIN_FINAL_CLTV_EXPIRY_DELTA)),
				htlc_minimum_msat: 1,
			},
			payment_context: PaymentContext::Bolt12Offer(Bolt12OfferContext {
				offer_id,
				invoice_request: fields,
			}),
		}
		.authenticate(
			Nonce::from_entropy_source(&*self.keys_manager),
			&self.keys_manager.get_expanded_key(),
		);

		BlindedPaymentPath::one_hop(
			self.node_id(),
			tlvs,
			EXTERNAL_PAYMENT_MIN_FINAL_CLTV_EXPIRY_DELTA,
			&*self.keys_manager,
			&Secp256k1::new(),
		)
		.map_err(|()| Error::InvoiceCreationFailed)
	}
}
