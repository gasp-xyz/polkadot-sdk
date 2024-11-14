use frame_support::dispatch::DispatchResult;
use sp_runtime::DispatchError;
use sp_std::vec::Vec;

// trait modeled for stable swap pallet & pools of two assets
// pair of currency ids
pub type PoolInfo<CurrencyId> = (CurrencyId, CurrencyId);

pub struct SwapResult<Balance> {
	pub amount_out: Balance,
	pub total_fee: Balance,
	pub treasury_fee: Balance,
	pub bnb_fee: Balance,
}

pub trait Inspect<AccountId> {
	type CurrencyId;
	type Balance;

	fn get_pool_info(pool_id: Self::CurrencyId) -> Option<PoolInfo<Self::CurrencyId>>;

	fn get_dy(
		pool_id: Self::CurrencyId,
		asset_in: Self::CurrencyId,
		asset_out: Self::CurrencyId,
		dx: Self::Balance,
	) -> Option<Self::Balance>;

	fn get_dx(
		pool_id: Self::CurrencyId,
		asset_in: Self::CurrencyId,
		asset_out: Self::CurrencyId,
		dy: Self::Balance,
	) -> Option<Self::Balance>;

	fn get_burn_amounts(
		pool_id: Self::CurrencyId,
		lp_burn_amount: Self::Balance,
	) -> Option<(Self::Balance, Self::Balance)>;
	
	fn get_mint_amount(
		pool_id: Self::CurrencyId,
		amounts: (Self::Balance, Self::Balance),
	) -> Option<Self::Balance>;

	fn get_non_empty_pools() -> Option<Vec<Self::CurrencyId>>;
}

pub trait TreasuryBurn<AccountId>: Inspect<AccountId> {
	fn settle_treasury_and_burn(
		asset_id: Self::CurrencyId,
		burn_amount: Self::Balance,
		treasury_amount: Self::Balance,
	) -> DispatchResult;
}

pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Create a pool for two assets, with possible different decimals
	fn create_pool(
		sender: &AccountId,
		asset_1: Self::CurrencyId,
		asset_1_decimals: u32,
		asset_2: Self::CurrencyId,
		asset_2_decimals: u32,
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
