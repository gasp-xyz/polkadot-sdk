use codec::Codec;
use jsonrpsee::{
	core::{async_trait, RpcResult},
	proc_macros::rpc,
	types::error::ErrorObject,
};
pub use pallet_market::CouncilRuntimeApi;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;

use sp_rpc::number::NumberOrHex;
use sp_runtime::traits::{Block as BlockT, MaybeDisplay, MaybeFromStr};
use sp_std::convert::{TryFrom, TryInto};
use std::sync::Arc;
use frame_support::{
	weights::Weight,
};

// We use Weight directly here without transform into a NumberOrHex type because Weight uses u64
// and NumberOrHex supports u64 numbers
#[rpc(client, server)]
pub trait CouncilApi<BlockHash, Call, Hash> {

	#[method(name = "council_get_length_and_weight_for_call")]
	fn get_length_and_weight_for_call(
		call: Call,
		at: Option<BlockHash>,
	) -> RpcResult<Option<(u32, Weight)>>;

	#[method(name = "council_get_length_and_weight_for_proposal")]
	fn get_length_and_weight_for_proposal(
		proposal_hash: Hash,
		at: Option<BlockHash>,
	) -> RpcResult<Option<(u32, Weight)>>;
}

pub struct Council<C, M> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<M>,
}

impl<C, P> Council<C, P> {
	pub fn new(client: Arc<C>) -> Self {
		Self { client, _marker: Default::default() }
	}
}

#[async_trait]
impl<C, Block, Call, Hash> CouncilApiServer<<Block as BlockT>::Hash, Call, Hash>
	for Market<C, Block>
where
	Block: BlockT,
	C: Send + Sync + 'static,
	C: ProvideRuntimeApi<Block>,
	C: HeaderBackend<Block>,
	C::Api: CouncilRuntimeApi<Block, Call, Hash>,
	Call: Codec,
	Hash: Codec,
{

	fn get_length_and_weight_for_call(
		call: Call,
		at: Option<BlockHash>,
	) -> RpcResult<Option<(u32, Weight)>>{
		let api = self.client.runtime_api();
		let at = at.unwrap_or(self.client.info().best_hash);

		api.get_length_and_weight_for_call(at, call)
			.map_err(|e| {
				ErrorObject::owned(1, "Unable to serve the request", Some(format!("{:?}", e)))
			})
	}

	fn get_length_and_weight_for_proposal(
		proposal_hash: Hash,
		at: Option<BlockHash>,
	) -> RpcResult<Option<(u32, Weight)>>{
		let api = self.client.runtime_api();
		let at = at.unwrap_or(self.client.info().best_hash);

		api.get_length_and_weight_for_proposal(at, proposal_hash)
			.map_err(|e| {
				ErrorObject::owned(1, "Unable to serve the request", Some(format!("{:?}", e)))
			})
	}
}
