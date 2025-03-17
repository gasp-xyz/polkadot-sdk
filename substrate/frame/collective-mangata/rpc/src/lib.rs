use codec::Codec;
use jsonrpsee::{
	core::{async_trait, RpcResult},
	proc_macros::rpc,
	types::error::ErrorObject,
};
pub use pallet_collective_mangata::CouncilRuntimeApi;
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
pub trait CouncilApi<BlockHash, Hash> {

	#[method(name = "council_get_length_and_weight_for_proposal")]
	fn get_length_and_weight_for_proposal(
		&self,
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
impl<C, Block, Hash> CouncilApiServer<<Block as BlockT>::Hash, Hash>
	for Council<C, Block>
where
	Block: BlockT,
	C: Send + Sync + 'static,
	C: ProvideRuntimeApi<Block>,
	C: HeaderBackend<Block>,
	C::Api: CouncilRuntimeApi<Block, Hash>,
	Hash: Codec,
{

	fn get_length_and_weight_for_proposal(
		&self,
		proposal_hash: Hash,
		at: Option<<Block as BlockT>::Hash>,
	) -> RpcResult<Option<(u32, Weight)>>{
		let api = self.client.runtime_api();
		let at = at.unwrap_or(self.client.info().best_hash);

		api.get_length_and_weight_for_proposal(at, proposal_hash)
			.map_err(|e| {
				ErrorObject::owned(1, "Unable to serve the request", Some(format!("{:?}", e)))
			})
	}
}
