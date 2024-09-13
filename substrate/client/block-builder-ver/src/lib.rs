// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate block builder
//!
//! This crate provides the [`BlockBuilder`] utility and the corresponding runtime api
//! [`BlockBuilder`](sp_block_builder::BlockBuilder).
//!
//! The block builder utility is used in the node as an abstraction over the runtime api to
//! initialize a block, to push extrinsics and to finalize a block.

#![warn(missing_docs)]

use codec::{Decode, Encode};

use sp_api::{
	ApiExt, ApiRef, CallApiAt, Core, ProvideRuntimeApi, StorageChanges, StorageProof,
	TransactionOutcome,
};
use sp_blockchain::{ApplyExtrinsicFailed, Error, HeaderBackend};
use sp_core::{traits::CallContext, ShufflingSeed};
use sp_runtime::{
	legacy,
	traits::{BlakeTwo256, Block as BlockT, Hash, HashingFor, Header as HeaderT, NumberFor, One},
	Digest,
};
use std::marker::PhantomData;

pub use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_ver::extract_inherent_data;
use ver_api::VerApi;

/// A builder for creating an instance of [`BlockBuilder`].
pub struct BlockBuilderBuilder<'a, B, C> {
	call_api_at: &'a C,
	_phantom: PhantomData<B>,
}

impl<'a, B, C> BlockBuilderBuilder<'a, B, C>
where
	B: BlockT,
{
	/// Create a new instance of the builder.
	///
	/// `call_api_at`: Something that implements [`CallApiAt`].
	pub fn new(call_api_at: &'a C) -> Self {
		Self { call_api_at, _phantom: PhantomData }
	}

	/// Specify the parent block to build on top of.
	pub fn on_parent_block(self, parent_block: B::Hash) -> BlockBuilderBuilderStage1<'a, B, C> {
		BlockBuilderBuilderStage1 { call_api_at: self.call_api_at, parent_block }
	}
}

/// The second stage of the [`BlockBuilderBuilder`].
///
/// This type can not be instantiated directly. To get an instance of it
/// [`BlockBuilderBuilder::new`] needs to be used.
pub struct BlockBuilderBuilderStage1<'a, B: BlockT, C> {
	call_api_at: &'a C,
	parent_block: B::Hash,
}

impl<'a, B, C> BlockBuilderBuilderStage1<'a, B, C>
where
	B: BlockT,
{
	/// Fetch the parent block number from the given `header_backend`.
	///
	/// The parent block number is used to initialize the block number of the new block.
	///
	/// Returns an error if the parent block specified in
	/// [`on_parent_block`](BlockBuilderBuilder::on_parent_block) does not exist.
	pub fn fetch_parent_block_number<H: HeaderBackend<B>>(
		self,
		header_backend: &H,
	) -> Result<BlockBuilderBuilderStage2<'a, B, C>, Error> {
		let parent_number = header_backend.number(self.parent_block)?.ok_or_else(|| {
			Error::Backend(format!(
				"Could not fetch block number for block: {:?}",
				self.parent_block
			))
		})?;

		Ok(BlockBuilderBuilderStage2 {
			call_api_at: self.call_api_at,
			enable_proof_recording: false,
			inherent_digests: Default::default(),
			parent_block: self.parent_block,
			parent_number,
		})
	}

	/// Provide the block number for the parent block directly.
	///
	/// The parent block is specified in [`on_parent_block`](BlockBuilderBuilder::on_parent_block).
	/// The parent block number is used to initialize the block number of the new block.
	pub fn with_parent_block_number(
		self,
		parent_number: NumberFor<B>,
	) -> BlockBuilderBuilderStage2<'a, B, C> {
		BlockBuilderBuilderStage2 {
			call_api_at: self.call_api_at,
			enable_proof_recording: false,
			inherent_digests: Default::default(),
			parent_block: self.parent_block,
			parent_number,
		}
	}
}

/// The second stage of the [`BlockBuilderBuilder`].
///
/// This type can not be instantiated directly. To get an instance of it
/// [`BlockBuilderBuilder::new`] needs to be used.
pub struct BlockBuilderBuilderStage2<'a, B: BlockT, C> {
	call_api_at: &'a C,
	enable_proof_recording: bool,
	inherent_digests: Digest,
	parent_block: B::Hash,
	parent_number: NumberFor<B>,
}

impl<'a, B: BlockT, C> BlockBuilderBuilderStage2<'a, B, C> {
	/// Enable proof recording for the block builder.
	pub fn enable_proof_recording(mut self) -> Self {
		self.enable_proof_recording = true;
		self
	}

	/// Enable/disable proof recording for the block builder.
	pub fn with_proof_recording(mut self, enable: bool) -> Self {
		self.enable_proof_recording = enable;
		self
	}

	/// Build the block with the given inherent digests.
	pub fn with_inherent_digests(mut self, inherent_digests: Digest) -> Self {
		self.inherent_digests = inherent_digests;
		self
	}

	/// Create the instance of the [`BlockBuilder`].
	pub fn build(self) -> Result<BlockBuilder<'a, B, C>, Error>
	where
		C: CallApiAt<B> + ProvideRuntimeApi<B>,
		C::Api: BlockBuilderApi<B> + VerApi<B>,
	{
		BlockBuilder::new(
			self.call_api_at,
			self.parent_block,
			self.parent_number,
			self.enable_proof_recording,
			self.inherent_digests,
		)
	}
}

/// use proper api for applying extriniscs based on version
pub fn apply_transaction_wrapper<'a, Block, Api>(
	api: &<Api as ProvideRuntimeApi<Block>>::Api,
	parent_hash: Block::Hash,
	xt: Block::Extrinsic,
) -> Result<sp_runtime::ApplyExtrinsicResult, sp_api::ApiError>
where
	Block: BlockT,
	Api: ProvideRuntimeApi<Block> + 'a,
	Api::Api: BlockBuilderApi<Block>,
{
	let version = api
		.api_version::<dyn BlockBuilderApi<Block>>(parent_hash)?
		.ok_or_else(|| Error::VersionInvalid("BlockBuilderApi".to_string()))?;

	if version < 6 {
		#[allow(deprecated)]
		api.apply_extrinsic_before_version_6(parent_hash, xt)
			.map(legacy::byte_sized_error::convert_to_latest)
	} else {
		api.apply_extrinsic(parent_hash, xt)
	}
}

/// A block that was build by [`BlockBuilder`] plus some additional data.
///
/// This additional data includes the `storage_changes`, these changes can be applied to the
/// backend to get the state of the block. Furthermore an optional `proof` is included which
/// can be used to proof that the build block contains the expected data. The `proof` will
/// only be set when proof recording was activated.
pub struct BuiltBlock<Block: BlockT> {
	/// The actual block that was build.
	pub block: Block,
	/// The changes that need to be applied to the backend to get the state of the build block.
	pub storage_changes: StorageChanges<Block>,
	/// An optional proof that was recorded while building the block.
	pub proof: Option<StorageProof>,
}

impl<Block: BlockT> BuiltBlock<Block> {
	/// Convert into the inner values.
	pub fn into_inner(self) -> (Block, StorageChanges<Block>, Option<StorageProof>) {
		(self.block, self.storage_changes, self.proof)
	}
}

/// Utility for building new (valid) blocks from a stream of extrinsics.
pub struct BlockBuilder<'a, Block: BlockT, C: ProvideRuntimeApi<Block> + 'a> {
	inherents: Vec<Block::Extrinsic>,
	extrinsics: Vec<Block::Extrinsic>,
	api: ApiRef<'a, C::Api>,
	call_api_at: &'a C,
	parent_hash: Block::Hash,
	/// The estimated size of the block header.
	estimated_header_size: usize,
}

impl<'a, Block, C> BlockBuilder<'a, Block, C>
where
	Block: BlockT,
	C: CallApiAt<Block> + ProvideRuntimeApi<Block> + 'a,
	C::Api: BlockBuilderApi<Block> + ApiExt<Block> + VerApi<Block>,
{
	/// Create a new instance of builder based on the given `parent_hash` and `parent_number`.
	///
	/// While proof recording is enabled, all accessed trie nodes are saved.
	/// These recorded trie nodes can be used by a third party to prove the
	/// output of this block builder without having access to the full storage.
	fn new(
		call_api_at: &'a C,
		parent_hash: Block::Hash,
		parent_number: NumberFor<Block>,
		record_proof: bool,
		inherent_digests: Digest,
	) -> Result<Self, Error> {
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			parent_number + One::one(),
			Default::default(),
			Default::default(),
			parent_hash,
			inherent_digests,
		);

		let estimated_header_size = header.encoded_size();

		let mut api = call_api_at.runtime_api();

		if record_proof {
			api.record_proof();
		}

		api.set_call_context(CallContext::Onchain);

		api.initialize_block(parent_hash, &header)?;

		Ok(Self {
			parent_hash,
			inherents: Vec::new(),
			extrinsics: Vec::new(),
			api,
			estimated_header_size,
			call_api_at,
		})
	}

	/// Push onto the block's list of extrinsics.
	///
	/// validate extrinsics but without commiting the change
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> Result<(), Error> {
		let parent_hash = self.parent_hash;
		let inherents = &mut self.inherents;

		self.api.execute_in_transaction(|api| {
			match apply_transaction_wrapper::<Block, C>(api, parent_hash, xt.clone()) {
				Ok(Ok(_)) => {
					inherents.push(xt);
					TransactionOutcome::Commit(Ok(()))
				},
				Ok(Err(tx_validity)) => TransactionOutcome::Rollback(Err(
					ApplyExtrinsicFailed::Validity(tx_validity).into(),
				)),
				Err(e) => TransactionOutcome::Rollback(Err(Error::from(e))),
			}
		})
	}

	/// temporaily apply extrinsics and record them on the list
	pub fn build_with_seed<
		F: FnOnce(
			&'_ Block::Hash,
			&'_ C::Api,
		) -> Vec<(Option<sp_runtime::AccountId20>, Block::Extrinsic)>,
	>(
		mut self,
		seed: ShufflingSeed,
		call: F,
	) -> Result<BuiltBlock<Block>, Error> {
		let parent_hash = self.parent_hash;

		let previous_block_txs = self.api.get_previous_block_txs(parent_hash).unwrap();

		let mut valid_txs = if self.extrinsics.len() == 0 && previous_block_txs.len() > 0 {
			log::info!(target:"block_builder", "Not enough room for (any) StoragQeueue enqueue inherent, producing empty block");
			vec![]
		} else if self.api.can_enqueue_txs(parent_hash).unwrap() {
			self.api.execute_in_transaction(|api| {
				let next_header = api.finalize_block(parent_hash).unwrap();

				api.start_prevalidation(parent_hash).unwrap();

				// create dummy header just to condider N+1 block extrinsics like new session
				let header = <<Block as BlockT>::Header as HeaderT>::new(
					*next_header.number() + One::one(),
					Default::default(),
					Default::default(),
					next_header.hash(),
					Default::default(),
				);

				if api.is_storage_migration_scheduled(parent_hash).unwrap() {
					log::debug!(target:"block_builder", "storage migration scheduled - ignoring any txs");
					TransactionOutcome::Rollback(vec![])
				} else {
					api.initialize_block(parent_hash, &header).unwrap();
					let txs = call(&self.parent_hash, &api);
					TransactionOutcome::Rollback(txs)
				}
			})
		} else {
			log::info!(target:"block_builder", "storage queue is full, no room for new txs");
			vec![]
		};

		// that should be improved at some point
		if valid_txs.len() > 100 {
			valid_txs.truncate(valid_txs.len() * 90 / 100);
		}

		let valid_txs_count = valid_txs.len();
		let store_txs_inherent = self
			.api
			.create_enqueue_txs_inherent(
				parent_hash,
				valid_txs.clone().into_iter().map(|(_, tx)| tx).collect(),
			)
			.unwrap();

		apply_transaction_wrapper::<Block, C>(&self.api, parent_hash, store_txs_inherent.clone())
			.unwrap()
			.unwrap()
			.unwrap();

		for (_, valid_tx) in valid_txs {
			let _ = self.api
				.account_extrinsic_dispatch_weight(
					parent_hash,
					Default::default(),
					valid_tx.clone(),
				)
				.unwrap();
		}

		// TODO get rid of collect
		let mut next_header = self.api.finalize_block(parent_hash)?;

		let proof = self.api.extract_proof();

		let state = self.call_api_at.state_at(self.parent_hash)?;
		let storage_changes = self
			.api
			.into_storage_changes(&state, parent_hash)
			.map_err(sp_blockchain::Error::StorageChanges)?;

		log::debug!(target: "block_builder", "consume {} valid transactios", valid_txs_count);

		// store hash of all extrinsics include in given bloack
		//
		let all_extrinsics: Vec<_> = self
			.inherents
			.iter()
			.chain(self.extrinsics.iter())
			.chain(std::iter::once(&store_txs_inherent))
			.cloned()
			.collect();

		let extrinsics_root = HashingFor::<Block>::ordered_trie_root(
			all_extrinsics.iter().map(Encode::encode).collect(),
			sp_runtime::StateVersion::V0,
		);
		next_header.set_extrinsics_root(extrinsics_root);
		next_header.set_seed(seed);
		next_header.set_count((self.extrinsics.len() as u32).into());

		Ok(BuiltBlock {
			block: <Block as BlockT>::new(next_header, all_extrinsics),
			storage_changes,
			proof,
		})
	}

	/// fetch previous block and apply it
	///
	/// consequence of delayed block execution
	pub fn apply_previous_block_extrinsics<F>(
		&mut self,
		seed: ShufflingSeed,
		block_size: &mut usize,
		max_block_size: usize,
		is_timer_expired: F,
	) where
		F: Fn() -> bool,
	{
		let parent_hash = self.parent_hash;
		self.api.store_seed(self.parent_hash, seed.seed).unwrap();
		let extrinsics = &mut self.extrinsics;

		let previous_block_txs = self.api.get_previous_block_txs(self.parent_hash).unwrap();
		let previous_block_txs_count = previous_block_txs.len();
		log::debug!(target: "block_builder", "previous block enqueued {} txs", previous_block_txs_count);

		for tx_bytes in previous_block_txs {
			if (*block_size + tx_bytes.len()) > max_block_size {
				break
			}

			if let Ok(xt) = <Block as BlockT>::Extrinsic::decode(&mut tx_bytes.as_slice()) {
				if self.api.execute_in_transaction(|api| { // execute tx to get execution status
					match apply_transaction_wrapper::<Block, C>(
						api,
						parent_hash,
						xt.clone(),
					) {

						_ if is_timer_expired() => {
							log::debug!(target: "block_builder", "timer expired no room for other txs from queue");
							TransactionOutcome::Rollback(false)
						},
						Ok(Err(validity_err)) if validity_err.exhausted_resources() => {
							log::debug!(target: "block_builder", "exhaust resources no room for other txs from queue");
							TransactionOutcome::Rollback(false)
						},
						Ok(Ok(_)) => {TransactionOutcome::Commit(true)}
						Ok(Err(validity_err)) => {
							log::warn!(target: "block_builder", "enqueued tx execution {} failed '${}'", BlakeTwo256::hash(&xt.encode()), validity_err);
							TransactionOutcome::Commit(true)
						},
						Err(_e) => {
							log::warn!(target: "block_builder", "enqueued tx execution {} failed - unknwown execution problem", BlakeTwo256::hash(&xt.encode()));
							TransactionOutcome::Commit(true)
						}
					}
				}){
					extrinsics.push(xt);
					*block_size += tx_bytes.len() + sp_core::H256::len_bytes();
				}else{
					break;
				}
			} else {
				log::warn!(target: "block_builder", "cannot decode tx");
			}
		}

		self.api.pop_txs(self.parent_hash, extrinsics.len() as u64).unwrap();
		log::info!(target: "block_builder", "executed {}/{} previous block transactions", extrinsics.len(), previous_block_txs_count);
	}

	/// Create the inherents for the block.
	///
	/// Returns the inherents created by the runtime or an error if something failed.
	pub fn create_inherents(
		&mut self,
		inherent_data: sp_inherents::InherentData,
	) -> Result<(ShufflingSeed, Vec<Block::Extrinsic>), Error> {
		let parent_hash = self.parent_hash;
		let seed = extract_inherent_data(&inherent_data).map_err(|_| {
			sp_blockchain::Error::Backend(String::from(
				"cannot read random seed from inherents data",
			))
		})?;

		self.api
			.execute_in_transaction(move |api| {
				// `create_inherents` should not change any state, to ensure this we always rollback
				// the transaction.
				TransactionOutcome::Rollback(api.inherent_extrinsics(parent_hash, inherent_data))
			})
			.map(|inherents| {
				(ShufflingSeed { seed: seed.seed.into(), proof: seed.proof.into() }, inherents)
			})
			.map_err(|e| Error::Application(Box::new(e)))
	}

	/// Estimate the size of the block in the current state.
	///
	/// If `include_proof` is `true`, the estimated size of the storage proof will be added
	/// to the estimation.
	pub fn estimate_block_size_without_extrinsics(&self, include_proof: bool) -> usize {
		let size = self.estimated_header_size +
			self.inherents.encoded_size() +
			self.api
				.create_enqueue_txs_inherent(self.parent_hash, Default::default())
				.unwrap()
				.encoded_size();

		if include_proof {
			size + self.api.proof_recorder().map(|pr| pr.estimate_encoded_size()).unwrap_or(0)
		} else {
			size
		}
	}
}

/// Verifies if trasaction can be executed
pub fn validate_transaction<'a, Block, Api>(
	at: Block::Hash,
	api: &'_ Api::Api,
	xt: <Block as BlockT>::Extrinsic,
) -> Result<(), Error>
where
	Block: BlockT,
	Api: ProvideRuntimeApi<Block> + 'a,
	Api::Api: VerApi<Block>,
	Api::Api: BlockBuilderApi<Block>,
{
	api.execute_in_transaction(|api| {
		match apply_transaction_wrapper::<Block, Api>(api, at, xt.clone()) {
			Ok(Ok(_)) => TransactionOutcome::Commit(Ok(())),
			Ok(Err(tx_validity)) => TransactionOutcome::Rollback(Err(
				ApplyExtrinsicFailed::Validity(tx_validity).into(),
			)),
			Err(e) => TransactionOutcome::Rollback(Err(Error::from(e))),
		}
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_blockchain::HeaderBackend;
	use sp_core::Blake2Hasher;
	use sp_state_machine::Backend;
	use substrate_test_runtime_client::{DefaultTestClientBuilderExt, TestClientBuilderExt};

	#[test]
	fn block_building_storage_proof_does_not_include_runtime_by_default() {
		let builder = substrate_test_runtime_client::TestClientBuilder::new();
		let backend = builder.backend();
		let client = builder.build();

		let genesis_hash = client.info().best_hash;

		let block = BlockBuilderBuilder::new(&client)
			.on_parent_block(genesis_hash)
			.with_parent_block_number(0)
			.enable_proof_recording()
			.build()
			.unwrap()
			.build_with_seed(Default::default(), |_, _| Default::default())
			.unwrap();

		let proof = block.proof.expect("Proof is build on request");
		let genesis_state_root = client.header(genesis_hash).unwrap().unwrap().state_root;

		let backend =
			sp_state_machine::create_proof_check_backend::<Blake2Hasher>(genesis_state_root, proof)
				.unwrap();

		assert!(backend
			.storage(&sp_core::storage::well_known_keys::CODE)
			.unwrap_err()
			.contains("Database missing expected key"),);
	}
}
