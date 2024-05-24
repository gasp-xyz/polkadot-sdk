#![cfg_attr(not(feature = "std"), no_std)]
use frame_support::pallet_prelude::*;
use mangata_types::multipurpose_liquidity::{ActivateKind, BondKind};
use sp_runtime::Permill;
use sp_std::vec::Vec;
use mangata_types::assets::L1Asset;

pub trait GetMaintenanceStatusTrait {
	fn is_maintenance() -> bool;

	fn is_upgradable() -> bool;
}

pub trait StakingReservesProviderTrait<AccountId, Balance, CurrencyId> {
	fn can_bond(
		token_id: CurrencyId,
		account_id: &AccountId,
		amount: Balance,
		use_balance_from: Option<BondKind>,
	) -> bool;

	fn bond(
		token_id: CurrencyId,
		account_id: &AccountId,
		amount: Balance,
		use_balance_from: Option<BondKind>,
	) -> DispatchResult;

	fn unbond(token_id: CurrencyId, account_id: &AccountId, amount: Balance) -> Balance;
}

pub trait ActivationReservesProviderTrait<AccountId, Balance, CurrencyId> {
	fn get_max_instant_unreserve_amount(token_id: CurrencyId, account_id: &AccountId) -> Balance;

	fn can_activate(
		token_id: CurrencyId,
		account_id: &AccountId,
		amount: Balance,
		use_balance_from: Option<ActivateKind>,
	) -> bool;

	fn activate(
		token_id: CurrencyId,
		account_id: &AccountId,
		amount: Balance,
		use_balance_from: Option<ActivateKind>,
	) -> DispatchResult;

	fn deactivate(token_id: CurrencyId, account_id: &AccountId, amount: Balance) -> Balance;
}

pub trait XykFunctionsTrait<AccountId, Balance, CurrencyId> {
	fn create_pool(
		sender: AccountId,
		first_asset_id: CurrencyId,
		first_asset_amount: Balance,
		second_asset_id: CurrencyId,
		second_asset_amount: Balance,
	) -> DispatchResult;

	fn sell_asset(
		sender: AccountId,
		sold_asset_id: CurrencyId,
		bought_asset_id: CurrencyId,
		sold_asset_amount: Balance,
		min_amount_out: Balance,
		err_upon_bad_slippage: bool,
	) -> Result<Balance, DispatchError>;

	fn multiswap_sell_asset(
		sender: AccountId,
		swap_token_list: Vec<CurrencyId>,
		sold_asset_amount: Balance,
		min_amount_out: Balance,
		err_upon_bad_slippage: bool,
		err_upon_non_slippage_fail: bool,
	) -> Result<Balance, DispatchError>;

	fn do_multiswap_sell_asset(
		sender: AccountId,
		swap_token_list: Vec<CurrencyId>,
		sold_asset_amount: Balance,
		min_amount_out: Balance,
	) -> Result<Balance, DispatchError>;

	fn do_multiswap_buy_asset(
		sender: AccountId,
		swap_token_list: Vec<CurrencyId>,
		bought_asset_amount: Balance,
		max_amount_in: Balance,
	) -> Result<Balance, DispatchError>;

	fn buy_asset(
		sender: AccountId,
		sold_asset_id: CurrencyId,
		bought_asset_id: CurrencyId,
		bought_asset_amount: Balance,
		max_amount_in: Balance,
		err_upon_bad_slippage: bool,
	) -> Result<Balance, DispatchError>;

	fn multiswap_buy_asset(
		sender: AccountId,
		swap_token_list: Vec<CurrencyId>,
		bought_asset_amount: Balance,
		max_amount_in: Balance,
		err_upon_bad_slippage: bool,
		err_upon_non_slippage_fail: bool,
	) -> Result<Balance, DispatchError>;

	fn mint_liquidity(
		sender: AccountId,
		first_asset_id: CurrencyId,
		second_asset_id: CurrencyId,
		first_asset_amount: Balance,
		expected_second_asset_amount: Balance,
		activate_minted_liquidity: bool,
	) -> Result<(CurrencyId, Balance), DispatchError>;

	fn provide_liquidity_with_conversion(
		sender: AccountId,
		first_asset_id: CurrencyId,
		second_asset_id: CurrencyId,
		provided_asset_id: CurrencyId,
		provided_asset_amount: Balance,
		activate_minted_liquidity: bool,
	) -> Result<(CurrencyId, Balance), DispatchError>;

	fn burn_liquidity(
		sender: AccountId,
		first_asset_id: CurrencyId,
		second_asset_id: CurrencyId,
		liquidity_asset_amount: Balance,
	) -> DispatchResult;

	fn get_tokens_required_for_minting(
		liquidity_asset_id: CurrencyId,
		liquidity_token_amount: Balance,
	) -> Result<(CurrencyId, Balance, CurrencyId, Balance), DispatchError>;

	fn do_compound_rewards(
		sender: AccountId,
		liquidity_asset_id: CurrencyId,
		amount_permille: Permill,
	) -> DispatchResult;

	fn is_liquidity_token(liquidity_asset_id: CurrencyId) -> bool;
}

pub trait ProofOfStakeRewardsApi<AccountId, Balance, CurrencyId> {
	#[deprecated(note = "Use `enable_native_rewards` instead.")]
	fn enable(liquidity_token_id: CurrencyId, weight: u8);

	fn enable_native_rewards(liquidity_token_id: CurrencyId, weight: u8) {
		Self::enable(liquidity_token_id, weight)
	}

	#[deprecated(note = "Use `disable_native_rewards` instead.")]
	fn disable(liquidity_token_id: CurrencyId);

	fn disable_native_rewards(liquidity_token_id: CurrencyId, weight: u8) {
		Self::disable(liquidity_token_id)
	}

	#[deprecated(note = "Use `native_rewards_enabled` instead.")]
	fn is_enabled(liquidity_token_id: CurrencyId) -> bool;

	fn native_rewards_enabled(liquidity_token_id: CurrencyId) -> bool {
		Self::is_enabled(liquidity_token_id)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn enable_3rdparty_rewards(
		account: AccountId,
		pool: (CurrencyId, CurrencyId),
		reward_token_id: CurrencyId,
		last_block: u32,
		amount: Balance,
	);

	#[cfg(feature = "runtime-benchmarks")]
	fn activate_liquidity_for_3rdparty_rewards(
		account: AccountId,
		liquidity_token: CurrencyId,
		amount: Balance,
		reward_token_id: CurrencyId,
	);

	fn claim_rewards_all(
		sender: AccountId,
		liquidity_token_id: CurrencyId,
	) -> Result<Balance, DispatchError>;

	// Activation & deactivation should happen in PoS
	fn activate_liquidity(
		sender: AccountId,
		liquidity_token_id: CurrencyId,
		amount: Balance,
		use_balance_from: Option<ActivateKind>,
	) -> DispatchResult;

	// Activation & deactivation should happen in PoS
	fn deactivate_liquidity(
		sender: AccountId,
		liquidity_token_id: CurrencyId,
		amount: Balance,
	) -> DispatchResult;

	fn calculate_rewards_amount(
		user: AccountId,
		liquidity_asset_id: CurrencyId,
	) -> Result<Balance, DispatchError>;
}

fn enable<CurrencyId>(liquidity_token_id: CurrencyId, weight: u8) {
	todo!()
}

pub trait PreValidateSwaps<AccountId, Balance, CurrencyId> {
	fn pre_validate_sell_asset(
		sender: &AccountId,
		sold_asset_id: CurrencyId,
		bought_asset_id: CurrencyId,
		sold_asset_amount: Balance,
		min_amount_out: Balance,
	) -> Result<(Balance, Balance, Balance, Balance, Balance, Balance), DispatchError>;

	fn pre_validate_multiswap_sell_asset(
		sender: &AccountId,
		swap_token_list: Vec<CurrencyId>,
		sold_asset_amount: Balance,
		min_amount_out: Balance,
	) -> Result<(Balance, Balance, Balance, Balance, Balance, CurrencyId, CurrencyId), DispatchError>;

	fn pre_validate_buy_asset(
		sender: &AccountId,
		sold_asset_id: CurrencyId,
		bought_asset_id: CurrencyId,
		bought_asset_amount: Balance,
		max_amount_in: Balance,
	) -> Result<(Balance, Balance, Balance, Balance, Balance, Balance), DispatchError>;

	fn pre_validate_multiswap_buy_asset(
		sender: &AccountId,
		swap_token_list: Vec<CurrencyId>,
		final_bought_asset_amount: Balance,
		max_amount_in: Balance,
	) -> Result<(Balance, Balance, Balance, Balance, Balance, CurrencyId, CurrencyId), DispatchError>;
}

pub trait FeeLockTriggerTrait<AccountId, Balance, CurrencyId> {
	fn process_fee_lock(who: &AccountId) -> DispatchResult;

	fn can_unlock_fee(who: &AccountId) -> DispatchResult;

	fn is_whitelisted(token_id: CurrencyId) -> bool;

	fn get_swap_valuation_for_token(
		valuating_token_id: CurrencyId,
		valuating_token_amount: Balance,
	) -> Option<Balance>;

	fn unlock_fee(who: &AccountId) -> DispatchResult;
}

pub trait ComputeIssuance {
	fn initialize() {}
	fn compute_issuance(n: u32);
}

pub trait GetIssuance<Balance> {
	fn get_all_issuance(n: u32) -> Option<(Balance, Balance)>;
	fn get_liquidity_mining_issuance(n: u32) -> Option<Balance>;
	fn get_staking_issuance(n: u32) -> Option<Balance>;
}

pub trait Valuate<Balance, CurrencyId> {
	fn get_liquidity_asset(
		first_asset_id: CurrencyId,
		second_asset_id: CurrencyId,
	) -> Result<CurrencyId, DispatchError>;

	fn get_liquidity_token_mga_pool(
		liquidity_token_id: CurrencyId,
	) -> Result<(CurrencyId, CurrencyId), DispatchError>;

	fn valuate_liquidity_token(
		liquidity_token_id: CurrencyId,
		liquidity_token_amount: Balance,
	) -> Balance;

	fn valuate_non_liquidity_token(
		liquidity_token_id: CurrencyId,
		liquidity_token_amount: Balance,
	) -> Balance;

	fn scale_liquidity_by_mga_valuation(
		mga_valuation: Balance,
		liquidity_token_amount: Balance,
		mga_token_amount: Balance,
	) -> Balance;

	fn get_pool_state(liquidity_token_id: CurrencyId) -> Option<(Balance, Balance)>;

	fn get_reserves(
		first_asset_id: CurrencyId,
		second_asset_id: CurrencyId,
	) -> Result<(Balance, Balance), DispatchError>;

	fn is_liquidity_token(liquidity_asset_id: CurrencyId) -> bool;
}

pub trait PoolCreateApi<AccountId, Balance, CurrencyId> {
	fn pool_exists(first: CurrencyId, second: CurrencyId) -> bool;

	fn pool_create(
		account: AccountId,
		first: CurrencyId,
		first_amount: Balance,
		second: CurrencyId,
		second_amount: Balance,
	) -> Option<(CurrencyId, Balance)>;
}

pub trait LiquidityMiningApi<Balance> {
	fn distribute_rewards(liquidity_mining_rewards: Balance);
}

pub trait AssetRegistryApi<CurrencyId> {
	fn enable_pool_creation(assets: (CurrencyId, CurrencyId)) -> bool;
}

pub trait SequencerStakingProviderTrait<AccountId, Balance, ChainId> {
	fn is_active_sequencer(chain: ChainId, sequencer: &AccountId) -> bool;

	fn is_selected_sequencer(chain: ChainId,  sequencer: &AccountId) -> bool;

	fn slash_sequencer(chain: ChainId, to_be_slashed: &AccountId, maybe_to_reward: Option<&AccountId>) -> DispatchResult;

}

impl<AccountId, Balance, ChainId> SequencerStakingProviderTrait<AccountId, Balance, ChainId> for (){
	fn is_active_sequencer(_chain: ChainId, _sequencer: &AccountId) -> bool{
		false
	}

	fn is_selected_sequencer(_chain: ChainId, _sequencer: &AccountId) -> bool{
		false
	}

	fn slash_sequencer(_chain: ChainId, _to_be_slashed: &AccountId, _maybe_to_reward: Option<&AccountId>) -> DispatchResult{
		Ok(())
	}

}

pub trait RolldownProviderTrait<ChainId, AccountId> {
	fn new_sequencer_active(chain: ChainId, sequencer: &AccountId);
	fn sequencer_unstaking(chain: ChainId, sequencer: &AccountId)->DispatchResult;
	fn handle_sequencer_deactivations(chain: ChainId, deactivated_sequencers: Vec<AccountId>);
}

impl<ChainId, AccountId> RolldownProviderTrait<ChainId, AccountId> for (){
	fn new_sequencer_active(chain: ChainId, sequencer: &AccountId){}
	fn sequencer_unstaking(chain: ChainId, sequencer: &AccountId)->DispatchResult{ Ok(()) }
	fn handle_sequencer_deactivations(chain: ChainId, deactivated_sequencers: Vec<AccountId>){}
}

pub trait AssetRegistryProviderTrait<AssetId>{
	fn get_l1_asset_id(l1_asset: L1Asset) -> Option<AssetId>;

	fn create_l1_asset(l1_asset: L1Asset) -> Result<AssetId, DispatchError>;
}

pub trait InformSessionDataTrait<AccountId>{
	fn inform_initialized_authorities(accounts: Vec<AccountId>);

	fn inform_on_new_session(accounts: Vec<AccountId>);
}

impl<AccountId> InformSessionDataTrait<AccountId> for (){
	fn inform_initialized_authorities(accounts: Vec<AccountId>){}

	fn inform_on_new_session(accounts: Vec<AccountId>){}
}
