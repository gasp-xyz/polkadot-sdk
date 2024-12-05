use frame_support::{dispatch::DispatchResult, traits::tokens::CurrencyId};
use sp_core::Get;
use sp_runtime::DispatchError;
use sp_std::vec::Vec;

// trait modeled for stable swap pallet & pools of two assets
// pair of currency ids
pub type PoolPair<CurrencyId> = (CurrencyId, CurrencyId);
pub type PoolReserves<Balance> = (Balance, Balance);
// id, pair, reserves
pub type PoolInfo<CurrencyId, Balance> = (CurrencyId, PoolPair<CurrencyId>, PoolReserves<Balance>);

pub struct SwapResult<Balance> {
	pub amount_out: Balance,
	pub total_fee: Balance,
	pub treasury_fee: Balance,
	pub bnb_fee: Balance,
}

pub trait Inspect {
	type CurrencyId;
	type Balance;

	fn get_pool_info(pool_id: Self::CurrencyId) -> Option<PoolPair<Self::CurrencyId>>;

	fn get_pool_reserves(pool_id: Self::CurrencyId) -> Option<PoolReserves<Self::Balance>>;

	fn get_non_empty_pools() -> Option<Vec<Self::CurrencyId>>;
}

pub trait ComputeBalances: Inspect {
	fn get_dy(
		pool_id: Self::CurrencyId,
		asset_in: Self::CurrencyId,
		asset_out: Self::CurrencyId,
		dx: Self::Balance,
	) -> Option<Self::Balance>;

	fn get_dy_with_impact(
		pool_id: Self::CurrencyId,
		asset_in: Self::CurrencyId,
		asset_out: Self::CurrencyId,
		dx: Self::Balance,
	) -> Option<(Self::Balance, Self::Balance)>;

	fn get_dx(
		pool_id: Self::CurrencyId,
		asset_in: Self::CurrencyId,
		asset_out: Self::CurrencyId,
		dy: Self::Balance,
	) -> Option<Self::Balance>;

	fn get_dx_with_impact(
		pool_id: Self::CurrencyId,
		asset_in: Self::CurrencyId,
		asset_out: Self::CurrencyId,
		dy: Self::Balance,
	) -> Option<(Self::Balance, Self::Balance)>;

	fn get_burn_amounts(
		pool_id: Self::CurrencyId,
		lp_burn_amount: Self::Balance,
	) -> Option<(Self::Balance, Self::Balance)>;

	fn get_mint_amount(
		pool_id: Self::CurrencyId,
		amounts: (Self::Balance, Self::Balance),
	) -> Option<Self::Balance>;
}

pub trait TreasuryBurn: Inspect {
	fn settle_treasury_and_burn(
		asset_id: Self::CurrencyId,
		burn_amount: Self::Balance,
		treasury_amount: Self::Balance,
	) -> DispatchResult;
}

pub trait Mutate<AccountId>: Inspect {
	/// Create a pool for two assets, with possible different decimals
	fn create_pool(
		sender: &AccountId,
		asset_1: Self::CurrencyId,
		amount_1: Self::Balance,
		asset_2: Self::CurrencyId,
		amount_2: Self::Balance,
	) -> Result<Self::CurrencyId, DispatchError>;

	/// Add liquidity to the pool using single asset, with fixed amounts.
	/// Amounts can be zero, to use single token.
	/// Not available for every pool type.
	/// Use `min_amount_lp_tokens` to limit requested amount of LP tokens paid out.
	/// return amount of LP tokens minted
	fn add_liquidity(
		sender: &AccountId,
		pool_id: Self::CurrencyId,
		amounts: (Self::Balance, Self::Balance),
		min_amount_lp_tokens: Self::Balance,
	) -> Result<Self::Balance, DispatchError>;

	/// Remove liquidity.
	/// Use `min_asset_amounts_out` to limit expected asset payouts
	fn remove_liquidity(
		sender: &AccountId,
		pool_id: Self::CurrencyId,
		liquidity_asset_amount: Self::Balance,
		min_asset_amounts_out: (Self::Balance, Self::Balance),
	) -> Result<(Self::Balance, Self::Balance), DispatchError>;

	fn swap(
		sender: &AccountId,
		pool_id: Self::CurrencyId,
		asset_in: Self::CurrencyId,
		asset_out: Self::CurrencyId,
		amount_in: Self::Balance,
		min_amount_out: Self::Balance,
	) -> Result<SwapResult<Self::Balance>, DispatchError>;
}


pub trait Valuate {
	type CurrencyId;
	type Balance;

	fn find_paired_pool(base_id: Self::CurrencyId, asset_id: Self::CurrencyId) -> Result<PoolInfo<Self::CurrencyId, Self::Balance>, DispatchError>;

	fn check_can_valuate(base_id: Self::CurrencyId, pool_id: Self::CurrencyId) -> Result<(), DispatchError>;
	
	fn check_pool_exist(pool_id: Self::CurrencyId) -> Result<(), DispatchError>;

	fn get_reserve_and_lp_supply(base_id: Self::CurrencyId, pool_id: Self::CurrencyId) -> Option<(Self::Balance, Self::Balance)>;

	fn get_valuation_for_paired(base_id: Self::CurrencyId, pool_id: Self::CurrencyId, amount: Self::Balance) -> Self::Balance;

	fn find_valuation(base_id: Self::CurrencyId, asset_id: Self::CurrencyId, amount: Self::Balance) -> Result<Self::Balance, DispatchError>; 
}

pub trait ValuateFor<ForAssetId: Get<Self::CurrencyId>>: Valuate {

	fn find_paired_pool_for(asset_id: Self::CurrencyId) -> Result<PoolInfo<Self::CurrencyId, Self::Balance>, DispatchError> {
		Self::find_paired_pool(ForAssetId::get(), asset_id)
	}

	fn check_can_valuate_for(pool_id: Self::CurrencyId) -> Result<(), DispatchError> {
		Self::check_can_valuate(ForAssetId::get(), pool_id)
	}
	
	fn get_reserve_and_lp_supply_for(pool_id: Self::CurrencyId) -> Option<(Self::Balance, Self::Balance)> {
		Self::get_reserve_and_lp_supply(ForAssetId::get(), pool_id)
	}

	fn get_valuation_for_paired_for(pool_id: Self::CurrencyId, amount: Self::Balance) -> Self::Balance {
		Self::get_valuation_for_paired(ForAssetId::get(), pool_id, amount)
	}

	fn find_valuation_for(asset_id: Self::CurrencyId, amount: Self::Balance) -> Result<Self::Balance, DispatchError> {
		Self::find_valuation(ForAssetId::get(), asset_id, amount)
	}
}