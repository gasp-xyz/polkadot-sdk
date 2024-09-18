// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Test the `frame-executive` crate.

use super::*;

use sp_core::{hexdisplay::AsBytesRef, sr25519, Hasher, Pair, ShufflingSeed, H256, H512};
use sp_keystore::{testing::MemoryKeystore, Keystore};
use sp_runtime::{
	generic::{DigestItem, Era},
	key_types::AURA,
	testing::{BlockVer as Block, Digest, HeaderVer as Header},
	traits::{Block as BlockT, Header as HeaderT},
	transaction_validity::{
		InvalidTransaction, TransactionValidityError, UnknownTransaction, ValidTransaction,
	},
	BuildStorage, DispatchError,
};
use sp_ver::{calculate_next_seed_from_bytes, VrfSignData, VrfTranscript};

use frame_support::{
	assert_err, assert_ok, derive_impl,
	migrations::MultiStepMigrator,
	pallet_prelude::*,
	parameter_types,
	traits::{fungible, ConstU8, Currency, IsInherent},
	weights::{ConstantMultiplier, IdentityFee, RuntimeDbWeight, Weight, WeightMeter, WeightToFee},
};
use frame_system::{pallet_prelude::*, ChainContext, LastRuntimeUpgrade, LastRuntimeUpgradeInfo};
use pallet_balances::Call as BalancesCall;
use pallet_transaction_payment::CurrencyAdapter;

use hex_literal::hex;

const TEST_KEY: &[u8] = b":test:key:";

#[frame_support::pallet(dev_mode)]
mod custom {
	use super::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		// module hooks.
		// one with block number arg and one without
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			Weight::from_parts(175, 0)
		}

		fn on_idle(_: BlockNumberFor<T>, _: Weight) -> Weight {
			Weight::from_parts(175, 0)
		}

		fn on_poll(_: BlockNumberFor<T>, _: &mut WeightMeter) {}

		fn on_finalize(_: BlockNumberFor<T>) {}

		fn on_runtime_upgrade() -> Weight {
			sp_io::storage::set(super::TEST_KEY, "module".as_bytes());
			Weight::from_parts(200, 0)
		}

		fn offchain_worker(n: BlockNumberFor<T>) {
			assert_eq!(BlockNumberFor::<T>::from(1u32), n);
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		pub fn some_function(origin: OriginFor<T>) -> DispatchResult {
			// NOTE: does not make any difference.
			frame_system::ensure_signed(origin)?;
			Ok(())
		}

		#[pallet::weight((200, DispatchClass::Operational))]
		pub fn some_root_operation(origin: OriginFor<T>) -> DispatchResult {
			frame_system::ensure_root(origin)?;
			Ok(())
		}

		pub fn some_unsigned_message(origin: OriginFor<T>) -> DispatchResult {
			frame_system::ensure_none(origin)?;
			Ok(())
		}

		pub fn allowed_unsigned(origin: OriginFor<T>) -> DispatchResult {
			frame_system::ensure_root(origin)?;
			Ok(())
		}

		pub fn unallowed_unsigned(origin: OriginFor<T>) -> DispatchResult {
			frame_system::ensure_root(origin)?;
			Ok(())
		}

		#[pallet::weight((0, DispatchClass::Mandatory))]
		pub fn inherent(origin: OriginFor<T>) -> DispatchResult {
			frame_system::ensure_none(origin)?;
			Ok(())
		}

		pub fn calculate_storage_root(_origin: OriginFor<T>) -> DispatchResult {
			let root = sp_io::storage::root(sp_runtime::StateVersion::V1);
			sp_io::storage::set("storage_root".as_bytes(), &root);
			Ok(())
		}
	}

	#[pallet::inherent]
	impl<T: Config> ProvideInherent for Pallet<T> {
		type Call = Call<T>;

		type Error = sp_inherents::MakeFatalError<()>;

		const INHERENT_IDENTIFIER: [u8; 8] = *b"test1234";

		fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
			None
		}

		fn is_inherent(call: &Self::Call) -> bool {
			*call == Call::<T>::inherent {}
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;

		// Inherent call is accepted for being dispatched
		fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
			match call {
				Call::allowed_unsigned { .. } => Ok(()),
				Call::inherent { .. } => Ok(()),
				_ => Err(UnknownTransaction::NoUnsignedValidator.into()),
			}
		}

		// Inherent call is not validated as unsigned
		fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			match call {
				Call::allowed_unsigned { .. } => Ok(Default::default()),
				_ => UnknownTransaction::NoUnsignedValidator.into(),
			}
		}
	}
}

#[frame_support::pallet(dev_mode)]
mod custom2 {
	use super::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		// module hooks.
		// one with block number arg and one without
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			assert!(
				!MockedSystemCallbacks::pre_inherent_called(),
				"Pre inherent hook goes after on_initialize"
			);

			Weight::from_parts(0, 0)
		}

		fn on_idle(_: BlockNumberFor<T>, _: Weight) -> Weight {
			assert!(
				MockedSystemCallbacks::post_transactions_called(),
				"Post transactions hook goes before after on_idle"
			);
			Weight::from_parts(0, 0)
		}

		fn on_finalize(_: BlockNumberFor<T>) {
			assert!(
				MockedSystemCallbacks::post_transactions_called(),
				"Post transactions hook goes before after on_finalize"
			);
		}

		fn on_runtime_upgrade() -> Weight {
			sp_io::storage::set(super::TEST_KEY, "module".as_bytes());
			Weight::from_parts(0, 0)
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		pub fn allowed_unsigned(origin: OriginFor<T>) -> DispatchResult {
			frame_system::ensure_root(origin)?;
			Ok(())
		}

		pub fn some_call(_: OriginFor<T>) -> DispatchResult {
			assert!(MockedSystemCallbacks::post_inherent_called());
			assert!(!MockedSystemCallbacks::post_transactions_called());
			assert!(System::inherents_applied());

			Ok(())
		}

		#[pallet::weight({0})]
		pub fn optional_inherent(origin: OriginFor<T>) -> DispatchResult {
			frame_system::ensure_none(origin)?;

			assert!(MockedSystemCallbacks::pre_inherent_called());
			assert!(!MockedSystemCallbacks::post_inherent_called(), "Should not already be called");
			assert!(!System::inherents_applied());

			Ok(())
		}

		#[pallet::weight((0, DispatchClass::Mandatory))]
		pub fn inherent(origin: OriginFor<T>) -> DispatchResult {
			frame_system::ensure_none(origin)?;

			assert!(MockedSystemCallbacks::pre_inherent_called());
			assert!(!MockedSystemCallbacks::post_inherent_called(), "Should not already be called");
			assert!(!System::inherents_applied());

			Ok(())
		}
	}

	#[pallet::inherent]
	impl<T: Config> ProvideInherent for Pallet<T> {
		type Call = Call<T>;

		type Error = sp_inherents::MakeFatalError<()>;

		const INHERENT_IDENTIFIER: [u8; 8] = *b"test1235";

		fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
			None
		}

		fn is_inherent(call: &Self::Call) -> bool {
			matches!(call, Call::<T>::inherent {} | Call::<T>::optional_inherent {})
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;

		// Inherent call is accepted for being dispatched
		fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
			match call {
				Call::allowed_unsigned { .. } |
				Call::optional_inherent { .. } |
				Call::inherent { .. } => Ok(()),
				_ => Err(UnknownTransaction::NoUnsignedValidator.into()),
			}
		}

		// Inherent call is not validated as unsigned
		fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			match call {
				Call::allowed_unsigned { .. } => Ok(Default::default()),
				_ => UnknownTransaction::NoUnsignedValidator.into(),
			}
		}
	}
}

frame_support::construct_runtime!(
	pub struct Runtime
	{
		System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		TransactionPayment: pallet_transaction_payment::{Pallet, Storage, Event<T>},
		Custom: custom::{Pallet, Call, ValidateUnsigned, Inherent},
		Custom2: custom2::{Pallet, Call, ValidateUnsigned, Inherent},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::builder()
			.base_block(Weight::from_parts(10, 0))
			.for_class(DispatchClass::all(), |weights| weights.base_extrinsic = Weight::from_parts(5, 0))
			.for_class(DispatchClass::non_mandatory(), |weights| weights.max_total = Weight::from_parts(1024, u64::MAX).into())
			.build_or_panic();
	pub const DbWeight: RuntimeDbWeight = RuntimeDbWeight {
		read: 10,
		write: 100,
	};
}

#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
impl frame_system::Config for Runtime {
	type BlockWeights = BlockWeights;
	type RuntimeOrigin = RuntimeOrigin;
	type Nonce = u64;
	type RuntimeCall = RuntimeCall;
	type Block = TestBlock;
	type RuntimeEvent = RuntimeEvent;
	type Version = RuntimeVersion;
	type AccountData = pallet_balances::AccountData<Balance>;
	type PreInherents = MockedSystemCallbacks;
	type PostInherents = MockedSystemCallbacks;
	type PostTransactions = MockedSystemCallbacks;
	type MultiBlockMigrator = MockedModeGetter;
}

type Balance = u64;

#[derive_impl(pallet_balances::config_preludes::TestDefaultConfig as pallet_balances::DefaultConfig)]
impl pallet_balances::Config for Runtime {
	type Balance = Balance;
	type AccountStore = System;
}

parameter_types! {
	pub const TransactionByteFee: Balance = 0;
}
impl pallet_transaction_payment::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type OnChargeTransaction = CurrencyAdapter<Balances, ()>;
	type OperationalFeeMultiplier = ConstU8<5>;
	type WeightToFee = IdentityFee<Balance>;
	type LengthToFee = ConstantMultiplier<Balance, TransactionByteFee>;
	type FeeMultiplierUpdate = ();
}

impl custom::Config for Runtime {}
impl custom2::Config for Runtime {}

pub struct RuntimeVersion;
impl frame_support::traits::Get<sp_version::RuntimeVersion> for RuntimeVersion {
	fn get() -> sp_version::RuntimeVersion {
		RuntimeVersionTestValues::get().clone()
	}
}

parameter_types! {
	pub static RuntimeVersionTestValues: sp_version::RuntimeVersion =
		Default::default();
}

type SignedExtra = (
	frame_system::CheckEra<Runtime>,
	frame_system::CheckNonce<Runtime>,
	frame_system::CheckWeight<Runtime>,
	pallet_transaction_payment::ChargeTransactionPayment<Runtime>,
);
type TestXt = sp_runtime::testing::TestXt<RuntimeCall, SignedExtra>;
type TestBlock = Block<TestXt>;

// Will contain `true` when the custom runtime logic was called.
const CUSTOM_ON_RUNTIME_KEY: &[u8] = b":custom:on_runtime";

struct CustomOnRuntimeUpgrade;
impl OnRuntimeUpgrade for CustomOnRuntimeUpgrade {
	fn on_runtime_upgrade() -> Weight {
		sp_io::storage::set(TEST_KEY, "custom_upgrade".as_bytes());
		sp_io::storage::set(CUSTOM_ON_RUNTIME_KEY, &true.encode());
		System::deposit_event(frame_system::Event::CodeUpdated);

		assert_eq!(0, System::last_runtime_upgrade_spec_version());

		Weight::from_parts(100, 0)
	}
}

type Executive = super::Executive<
	Runtime,
	Block<TestXt>,
	ChainContext<Runtime>,
	Runtime,
	AllPalletsWithSystem,
	CustomOnRuntimeUpgrade,
>;

parameter_types! {
	pub static SystemCallbacksCalled: u32 = 0;
}

pub struct MockedSystemCallbacks;
impl PreInherents for MockedSystemCallbacks {
	fn pre_inherents() {
		assert_eq!(SystemCallbacksCalled::get(), 0);
		SystemCallbacksCalled::set(1);
		// Change the storage to modify the root hash:
		frame_support::storage::unhashed::put(b":pre_inherent", b"0");
	}
}

impl PostInherents for MockedSystemCallbacks {
	fn post_inherents() {
		assert_eq!(SystemCallbacksCalled::get(), 1);
		SystemCallbacksCalled::set(2);
		// Change the storage to modify the root hash:
		frame_support::storage::unhashed::put(b":post_inherent", b"0");
	}
}

impl PostTransactions for MockedSystemCallbacks {
	fn post_transactions() {
		assert_eq!(SystemCallbacksCalled::get(), 2);
		SystemCallbacksCalled::set(3);
		// Change the storage to modify the root hash:
		frame_support::storage::unhashed::put(b":post_transaction", b"0");
	}
}

impl MockedSystemCallbacks {
	fn pre_inherent_called() -> bool {
		SystemCallbacksCalled::get() >= 1
	}

	fn post_inherent_called() -> bool {
		SystemCallbacksCalled::get() >= 2
	}

	fn post_transactions_called() -> bool {
		SystemCallbacksCalled::get() >= 3
	}

	fn reset() {
		SystemCallbacksCalled::set(0);
		frame_support::storage::unhashed::kill(b":pre_inherent");
		frame_support::storage::unhashed::kill(b":post_inherent");
		frame_support::storage::unhashed::kill(b":post_transaction");
	}
}

parameter_types! {
	pub static MbmActive: bool = false;
}

pub struct MockedModeGetter;
impl MultiStepMigrator for MockedModeGetter {
	fn ongoing() -> bool {
		MbmActive::get()
	}

	fn step() -> Weight {
		Weight::zero()
	}
}

fn extra(nonce: u64, fee: Balance) -> SignedExtra {
	(
		frame_system::CheckEra::from(Era::Immortal),
		frame_system::CheckNonce::from(nonce),
		frame_system::CheckWeight::new(),
		pallet_transaction_payment::ChargeTransactionPayment::from(fee),
	)
}

fn sign_extra(who: u64, nonce: u64, fee: Balance) -> Option<(u64, SignedExtra)> {
	Some((who, extra(nonce, fee)))
}

fn call_transfer(dest: u64, value: u64) -> RuntimeCall {
	RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest, value })
}

fn enqueue_txs(
	txs: Vec<(Option<<Runtime as frame_system::Config>::AccountId>, Vec<u8>)>,
) -> RuntimeCall {
	RuntimeCall::System(frame_system::Call::enqueue_txs { txs })
}

use sp_runtime::generic::{ExtendedCall, MetamaskSigningCtx};
impl ExtendedCall for RuntimeCall {
	fn context(&self) -> Option<MetamaskSigningCtx> {
		None
	}
}

#[test]
fn balance_transfer_dispatch_works() {
	let mut t = frame_system::GenesisConfig::<Runtime>::default().build_storage().unwrap();
	pallet_balances::GenesisConfig::<Runtime> { balances: vec![(1, 211)] }
		.assimilate_storage(&mut t)
		.unwrap();
	let xt = TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0));
	let weight = xt.get_dispatch_info().weight +
		<Runtime as frame_system::Config>::BlockWeights::get()
			.get(DispatchClass::Normal)
			.base_extrinsic;
	let fee: Balance =
		<Runtime as pallet_transaction_payment::Config>::WeightToFee::weight_to_fee(&weight);
	let mut t = sp_io::TestExternalities::new(t);
	t.execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));
		let r = Executive::apply_extrinsic(xt);
		assert!(r.is_ok());
		assert_eq!(<pallet_balances::Pallet<Runtime>>::total_balance(&1), 142 - fee);
		assert_eq!(<pallet_balances::Pallet<Runtime>>::total_balance(&2), 69);
	});
}

fn new_test_ext(balance_factor: Balance) -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::<Runtime>::default().build_storage().unwrap();
	pallet_balances::GenesisConfig::<Runtime> { balances: vec![(1, 111 * balance_factor)] }
		.assimilate_storage(&mut t)
		.unwrap();
	let mut ext: sp_io::TestExternalities = t.into();
	ext.execute_with(|| {
		SystemCallbacksCalled::set(0);
	});
	ext
}

fn new_test_ext_v0(balance_factor: Balance) -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::<Runtime>::default().build_storage().unwrap();
	pallet_balances::GenesisConfig::<Runtime> { balances: vec![(1, 111 * balance_factor)] }
		.assimilate_storage(&mut t)
		.unwrap();
	(t, sp_runtime::StateVersion::V0).into()
}

#[test]
fn block_import_works() {
	block_import_works_inner(
		new_test_ext_v0(1),
		array_bytes::hex_n_into_unchecked(
			"dde9cabea6f323f7d7c02af3ef50cffb08ec0424335b8fea082c99d9b8694bee",
		),
	);
	block_import_works_inner(
		new_test_ext(1),
		array_bytes::hex_n_into_unchecked(
			"d4754c3b50a438692cbd7a788aa05d2464ddbdc36d1d0cf9feb923f449f32a9c",
		),
	);
}
fn block_import_works_inner(mut ext: sp_io::TestExternalities, state_root: H256) {
	ext.execute_with(|| {
		Executive::execute_block(Block {
			header: Header {
				parent_hash: [69u8; 32].into(),
				number: 1,
				state_root,
				extrinsics_root: array_bytes::hex_n_into_unchecked(
					"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314",
				),
				digest: Digest { logs: vec![] },
				count: 0,
				seed: Default::default(),
			},
			extrinsics: vec![],
		});
	});
}

#[test]
#[should_panic]
fn block_import_of_bad_state_root_fails() {
	new_test_ext(1).execute_with(|| {
		Executive::execute_block(Block {
			header: Header {
				parent_hash: [69u8; 32].into(),
				number: 1,
				state_root: [0u8; 32].into(),
				extrinsics_root: array_bytes::hex_n_into_unchecked(
					"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314",
				),
				digest: Digest { logs: vec![] },
				count: 0,
				seed: Default::default(),
			},
			extrinsics: vec![],
		});
	});
}

#[test]
#[should_panic]
fn block_import_of_bad_extrinsic_root_fails() {
	new_test_ext(1).execute_with(|| {
		Executive::execute_block(Block {
			header: Header {
				parent_hash: [69u8; 32].into(),
				number: 1,
				state_root: array_bytes::hex_n_into_unchecked(
					"75e7d8f360d375bbe91bcf8019c01ab6362448b4a89e3b329717eb9d910340e5",
				),
				extrinsics_root: [0u8; 32].into(),
				digest: Digest { logs: vec![] },
				count: 0,
				seed: Default::default(),
			},
			extrinsics: vec![],
		});
	});
}

#[test]
fn bad_extrinsic_not_inserted() {
	let mut t = new_test_ext(1);
	// bad nonce check!
	let xt = TestXt::new(call_transfer(33, 69), sign_extra(1, 30, 0));
	t.execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));
		assert_err!(
			Executive::apply_extrinsic(xt),
			TransactionValidityError::Invalid(InvalidTransaction::Future)
		);
		assert_eq!(<frame_system::Pallet<Runtime>>::extrinsic_index(), Some(0));
	});
}

#[test]
fn block_weight_limit_enforced() {
	let mut t = new_test_ext(10000);
	// given: TestXt uses the encoded len as fixed Len:
	let xt = TestXt::new(
		RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest: 33, value: 0 }),
		sign_extra(1, 0, 0),
	);
	let encoded = xt.encode();
	let encoded_len = encoded.len() as u64;
	// on_initialize weight + base block execution weight
	let block_weights = <Runtime as frame_system::Config>::BlockWeights::get();
	let base_block_weight = Weight::from_parts(175, 0) + block_weights.base_block;
	let limit = block_weights.get(DispatchClass::Normal).max_total.unwrap() - base_block_weight;
	let num_to_exhaust_block = limit.ref_time() / (encoded_len + 5);
	t.execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));
		// Base block execution weight + `on_initialize` weight from the custom module.
		assert_eq!(<frame_system::Pallet<Runtime>>::block_weight().total(), base_block_weight);

		for nonce in 0..=num_to_exhaust_block {
			let xt = TestXt::new(
				RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest: 33, value: 0 }),
				sign_extra(1, nonce.into(), 0),
			);
			let res = Executive::apply_extrinsic(xt);
			if nonce != num_to_exhaust_block {
				assert!(res.is_ok());
				assert_eq!(
					<frame_system::Pallet<Runtime>>::block_weight().total(),
					//--------------------- on_initialize + block_execution + extrinsic_base weight
					Weight::from_parts((encoded_len + 5) * (nonce + 1), 0) + base_block_weight,
				);
				assert_eq!(
					<frame_system::Pallet<Runtime>>::extrinsic_index(),
					Some(nonce as u32 + 1)
				);
			} else {
				assert_eq!(res, Err(InvalidTransaction::ExhaustsResources.into()));
			}
		}
	});
}

#[test]
fn block_weight_and_size_is_stored_per_tx() {
	let xt = TestXt::new(
		RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest: 33, value: 0 }),
		sign_extra(1, 0, 0),
	);
	let x1 = TestXt::new(
		RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest: 33, value: 0 }),
		sign_extra(1, 1, 0),
	);
	let x2 = TestXt::new(
		RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest: 33, value: 0 }),
		sign_extra(1, 2, 0),
	);
	let len = xt.clone().encode().len() as u32;
	let mut t = new_test_ext(1);
	t.execute_with(|| {
		// Block execution weight + on_initialize weight from custom module
		let base_block_weight = Weight::from_parts(175, 0) +
			<Runtime as frame_system::Config>::BlockWeights::get().base_block;

		Executive::initialize_block(&Header::new_from_number(1));

		assert_eq!(<frame_system::Pallet<Runtime>>::block_weight().total(), base_block_weight);
		assert_eq!(<frame_system::Pallet<Runtime>>::all_extrinsics_len(), 0);

		assert!(Executive::apply_extrinsic(xt.clone()).unwrap().is_ok());
		assert!(Executive::apply_extrinsic(x1.clone()).unwrap().is_ok());
		assert!(Executive::apply_extrinsic(x2.clone()).unwrap().is_ok());

		// default weight for `TestXt` == encoded length.
		let extrinsic_weight = Weight::from_parts(len as u64, 0) +
			<Runtime as frame_system::Config>::BlockWeights::get()
				.get(DispatchClass::Normal)
				.base_extrinsic;
		assert_eq!(
			<frame_system::Pallet<Runtime>>::block_weight().total(),
			base_block_weight + 3u64 * extrinsic_weight,
		);
		assert_eq!(<frame_system::Pallet<Runtime>>::all_extrinsics_len(), 3 * len);

		let _ = <frame_system::Pallet<Runtime>>::finalize();
		// All extrinsics length cleaned on `System::finalize`
		assert_eq!(<frame_system::Pallet<Runtime>>::all_extrinsics_len(), 0);

		// Reset to a new block.
		SystemCallbacksCalled::take();
		Executive::initialize_block(&Header::new_from_number(2));

		// Block weight cleaned up on `System::initialize`
		assert_eq!(<frame_system::Pallet<Runtime>>::block_weight().total(), base_block_weight);
	});
}

#[test]
fn validate_unsigned() {
	let valid = TestXt::new(RuntimeCall::Custom(custom::Call::allowed_unsigned {}), None);
	let invalid = TestXt::new(RuntimeCall::Custom(custom::Call::unallowed_unsigned {}), None);
	let mut t = new_test_ext(1);

	t.execute_with(|| {
		assert_eq!(
			Executive::validate_transaction(
				TransactionSource::InBlock,
				valid.clone(),
				Default::default(),
			),
			Ok(ValidTransaction::default()),
		);
		assert_eq!(
			Executive::validate_transaction(
				TransactionSource::InBlock,
				invalid.clone(),
				Default::default(),
			),
			Err(TransactionValidityError::Unknown(UnknownTransaction::NoUnsignedValidator)),
		);
		// Need to initialize the block before applying extrinsics for the `MockedSystemCallbacks`
		// check.
		Executive::initialize_block(&Header::new_from_number(1));
		assert_eq!(Executive::apply_extrinsic(valid), Ok(Err(DispatchError::BadOrigin)));
		assert_eq!(
			Executive::apply_extrinsic(invalid),
			Err(TransactionValidityError::Unknown(UnknownTransaction::NoUnsignedValidator))
		);
	});
}

#[test]
fn can_not_pay_for_tx_fee_on_full_lock() {
	let mut t = new_test_ext(1);
	t.execute_with(|| {
		<pallet_balances::Pallet<Runtime> as fungible::MutateFreeze<u64>>::set_freeze(&(), &1, 110)
			.unwrap();
		let xt = TestXt::new(
			RuntimeCall::System(frame_system::Call::remark { remark: vec![1u8] }),
			sign_extra(1, 0, 0),
		);
		Executive::initialize_block(&Header::new_from_number(1));

		assert_eq!(Executive::apply_extrinsic(xt), Err(InvalidTransaction::Payment.into()),);
		assert_eq!(<pallet_balances::Pallet<Runtime>>::total_balance(&1), 111);
	});
}

#[test]
fn block_hooks_weight_is_stored() {
	new_test_ext(1).execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));
		Executive::finalize_block();
		// NOTE: might need updates over time if new weights are introduced.
		// For now it only accounts for the base block execution weight and
		// the `on_initialize` weight defined in the custom test module.
		assert_eq!(
			<frame_system::Pallet<Runtime>>::block_weight().total(),
			Weight::from_parts(175 + 175 + 10, 0)
		);
	})
}

#[test]
fn runtime_upgraded_should_work() {
	new_test_ext(1).execute_with(|| {
		RuntimeVersionTestValues::mutate(|v| *v = Default::default());
		// It should be added at genesis
		assert!(LastRuntimeUpgrade::<Runtime>::exists());
		assert!(!Executive::runtime_upgraded());

		RuntimeVersionTestValues::mutate(|v| {
			*v = sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
		});
		assert!(Executive::runtime_upgraded());

		RuntimeVersionTestValues::mutate(|v| {
			*v = sp_version::RuntimeVersion {
				spec_version: 1,
				spec_name: "test".into(),
				..Default::default()
			}
		});
		assert!(Executive::runtime_upgraded());

		RuntimeVersionTestValues::mutate(|v| {
			*v = sp_version::RuntimeVersion {
				spec_version: 0,
				impl_version: 2,
				..Default::default()
			}
		});
		assert!(!Executive::runtime_upgraded());

		LastRuntimeUpgrade::<Runtime>::take();
		assert!(Executive::runtime_upgraded());
	})
}

#[test]
fn last_runtime_upgrade_was_upgraded_works() {
	let test_data = vec![
		(0, "", 1, "", true),
		(1, "", 1, "", false),
		(1, "", 1, "test", true),
		(1, "", 0, "", false),
		(1, "", 0, "test", true),
	];

	for (spec_version, spec_name, c_spec_version, c_spec_name, result) in test_data {
		let current = sp_version::RuntimeVersion {
			spec_version: c_spec_version,
			spec_name: c_spec_name.into(),
			..Default::default()
		};

		let last = LastRuntimeUpgradeInfo {
			spec_version: spec_version.into(),
			spec_name: spec_name.into(),
		};

		assert_eq!(result, last.was_upgraded(&current));
	}
}

#[test]
fn custom_runtime_upgrade_is_called_before_modules() {
	new_test_ext(1).execute_with(|| {
		// Make sure `on_runtime_upgrade` is called.
		RuntimeVersionTestValues::mutate(|v| {
			*v = sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
		});

		Executive::initialize_block(&Header::new_from_number(1));

		assert_eq!(&sp_io::storage::get(TEST_KEY).unwrap()[..], *b"module");
		assert_eq!(sp_io::storage::get(CUSTOM_ON_RUNTIME_KEY).unwrap(), true.encode());
		assert_eq!(
			Some(RuntimeVersionTestValues::get().into()),
			LastRuntimeUpgrade::<Runtime>::get(),
		)
	});
}

#[test]
fn event_from_runtime_upgrade_is_included() {
	new_test_ext(1).execute_with(|| {
		// Make sure `on_runtime_upgrade` is called.
		RuntimeVersionTestValues::mutate(|v| {
			*v = sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
		});

		// set block number to non zero so events are not excluded
		System::set_block_number(1);

		Executive::initialize_block(&Header::new_from_number(2));
		System::assert_last_event(frame_system::Event::<Runtime>::CodeUpdated.into());
	});
}

/// Regression test that ensures that the custom on runtime upgrade is called when executive is
/// used through the `ExecuteBlock` trait.
#[test]
fn custom_runtime_upgrade_is_called_when_using_execute_block_trait() {
	let xt = TestXt::new(
		RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest: 33, value: 0 }),
		sign_extra(1, 0, 0),
	);

	let header = new_test_ext(1).execute_with(|| {
		// Make sure `on_runtime_upgrade` is called.
		RuntimeVersionTestValues::mutate(|v| {
			*v = sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
		});

		// Let's build some fake block.
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	// Reset to get the correct new genesis below.
	RuntimeVersionTestValues::mutate(|v| {
		*v = sp_version::RuntimeVersion { spec_version: 0, ..Default::default() }
	});

	new_test_ext(1).execute_with(|| {
		// Make sure `on_runtime_upgrade` is called.
		RuntimeVersionTestValues::mutate(|v| {
			*v = sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
		});

		<Executive as ExecuteBlock<Block<TestXt>>>::execute_block(Block::new(header, vec![xt]));

		assert_eq!(&sp_io::storage::get(TEST_KEY).unwrap()[..], *b"module");
		assert_eq!(sp_io::storage::get(CUSTOM_ON_RUNTIME_KEY).unwrap(), true.encode());
	});
}

#[test]
fn all_weights_are_recorded_correctly() {
	// Reset to get the correct new genesis below.
	RuntimeVersionTestValues::take();

	new_test_ext(1).execute_with(|| {
		// Make sure `on_runtime_upgrade` is called for maximum complexity
		RuntimeVersionTestValues::mutate(|v| {
			*v = sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
		});

		let block_number = 1;

		Executive::initialize_block(&Header::new_from_number(block_number));

		// Reset the last runtime upgrade info, to make the second call to `on_runtime_upgrade`
		// succeed.
		LastRuntimeUpgrade::<Runtime>::take();
		MockedSystemCallbacks::reset();

		// All weights that show up in the `initialize_block_impl`
		let custom_runtime_upgrade_weight = CustomOnRuntimeUpgrade::on_runtime_upgrade();
		let runtime_upgrade_weight =
			<AllPalletsWithSystem as OnRuntimeUpgrade>::on_runtime_upgrade();
		let on_initialize_weight =
			<AllPalletsWithSystem as OnInitialize<u64>>::on_initialize(block_number);
		let base_block_weight = <Runtime as frame_system::Config>::BlockWeights::get().base_block;

		// Weights are recorded correctly
		assert_eq!(
			frame_system::Pallet::<Runtime>::block_weight().total(),
			custom_runtime_upgrade_weight +
				runtime_upgrade_weight +
				on_initialize_weight +
				base_block_weight,
		);
	});
}

#[test]
fn offchain_worker_works_as_expected() {
	new_test_ext(1).execute_with(|| {
		let parent_hash = sp_core::H256::from([69u8; 32]);
		let mut digest = Digest::default();
		digest.push(DigestItem::Seal([1, 2, 3, 4], vec![5, 6, 7, 8]));

		let header = Header::new(1, H256::default(), H256::default(), parent_hash, digest.clone());

		Executive::offchain_worker(&header);

		assert_eq!(digest, System::digest());
		assert_eq!(parent_hash, System::block_hash(0));
		assert_eq!(header.hash(), System::block_hash(1));
	});
}

#[test]
fn calculating_storage_root_twice_works() {
	let call = RuntimeCall::Custom(custom::Call::calculate_storage_root {});
	let xt = TestXt::new(call, sign_extra(1, 0, 0));

	let header = new_test_ext(1).execute_with(|| {
		// Let's build some fake block.
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		Executive::execute_block(Block::new(header, vec![xt]));
	});
}

#[test]
#[should_panic(expected = "Invalid inherent position for extrinsic at index 1")]
fn invalid_inherent_position_fail() {
	let xt1 = TestXt::new(
		RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest: 33, value: 0 }),
		sign_extra(1, 0, 0),
	);
	let xt2 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);

	let header = new_test_ext(1).execute_with(|| {
		// Let's build some fake block.
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
		Executive::apply_extrinsic(xt2.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		Executive::execute_block(Block::new(header, vec![xt1, xt2]));
	});
}

#[test]
fn valid_inherents_position_works() {
	let xt1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);
	let xt2 = TestXt::new(call_transfer(33, 0), sign_extra(1, 0, 0));

	let header = new_test_ext(1).execute_with(|| {
		// Let's build some fake block.
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
		Executive::apply_extrinsic(xt2.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		Executive::execute_block(Block::new(header, vec![xt1, xt2]));
	});
}

#[test]
// there will be some cases when tx execution may fail (because of delayed execution), won't panic
// #[should_panic(expected = "A call was labelled as mandatory, but resulted in an Error.")]
fn invalid_inherents_fail_block_execution() {
	let xt1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), sign_extra(1, 0, 0));

	new_test_ext(1).execute_with(|| {
		Executive::execute_block(Block::new(
			Header::new(
				1,
				H256::default(),
				array_bytes::hex_n_into_unchecked(
					"36e5526ba30052950c70ca652e6ed68473039bc6fe6c1861439ed37ec595dcba",
				),
				[69u8; 32].into(),
				Digest::default(),
			),
			vec![xt1],
		));
	});
}

// Inherents are created by the runtime and don't need to be validated.
#[test]
fn inherents_fail_validate_block() {
	let xt1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);

	new_test_ext(1).execute_with(|| {
		assert_eq!(
			Executive::validate_transaction(TransactionSource::External, xt1, H256::random())
				.unwrap_err(),
			InvalidTransaction::MandatoryValidation.into()
		);
	})
}

/// Inherents still work while `initialize_block` forbids transactions.
#[test]
fn inherents_ok_while_exts_forbidden_works() {
	let xt1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);

	let header = new_test_ext(1).execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
		// This is not applied:
		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		// Tell `initialize_block` to forbid extrinsics:
		Executive::execute_block(Block::new(header, vec![xt1]));
	});
}

/// Refuses to import blocks with transactions during `OnlyInherents` mode.
#[test]
#[should_panic = "Only inherents are allowed in this block"]
fn transactions_in_only_inherents_block_errors() {
	let xt1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);
	let xt2 = TestXt::new(call_transfer(33, 0), sign_extra(1, 0, 0));

	let header = new_test_ext(1).execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
		Executive::apply_extrinsic(xt2.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		MbmActive::set(true);
		Executive::execute_block(Block::new(header, vec![xt1, xt2]));
	});
}

/// Same as above but no error.
#[test]
fn transactions_in_normal_block_works() {
	let xt1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);
	let xt2 = TestXt::new(call_transfer(33, 0), sign_extra(1, 0, 0));

	let header = new_test_ext(1).execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
		Executive::apply_extrinsic(xt2.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		// Tell `initialize_block` to forbid extrinsics:
		Executive::execute_block(Block::new(header, vec![xt1, xt2]));
	});
}

#[test]
#[cfg(feature = "try-runtime")]
fn try_execute_block_works() {
	let xt1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);
	let xt2 = TestXt::new(call_transfer(33, 0), sign_extra(1, 0, 0));

	let header = new_test_ext(1).execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
		Executive::apply_extrinsic(xt2.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		Executive::try_execute_block(
			Block::new(header, vec![xt1, xt2]),
			true,
			true,
			frame_try_runtime::TryStateSelect::All,
		)
		.unwrap();
	});
}

/// Same as `extrinsic_while_exts_forbidden_errors` but using the try-runtime function.
#[test]
#[cfg(feature = "try-runtime")]
#[should_panic = "Only inherents allowed"]
fn try_execute_tx_forbidden_errors() {
	let xt1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);
	let xt2 = TestXt::new(call_transfer(33, 0), sign_extra(1, 0, 0));

	let header = new_test_ext(1).execute_with(|| {
		// Let's build some fake block.
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
		Executive::apply_extrinsic(xt2.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		MbmActive::set(true);
		Executive::try_execute_block(
			Block::new(header, vec![xt1, xt2]),
			true,
			true,
			frame_try_runtime::TryStateSelect::All,
		)
		.unwrap();
	});
}

/// Check that `ensure_inherents_are_first` reports the correct indices.
#[test]
fn ensure_inherents_are_first_works() {
	let in1 = TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None);
	let in2 = TestXt::new(RuntimeCall::Custom2(custom2::Call::inherent {}), None);
	let xt2 = TestXt::new(call_transfer(33, 0), sign_extra(1, 0, 0));

	// Mocked empty header:
	let header = new_test_ext(1).execute_with(|| {
		Executive::initialize_block(&Header::new_from_number(1));
		Executive::finalize_block()
	});

	new_test_ext(1).execute_with(|| {
		assert_ok!(Runtime::ensure_inherents_are_first(&Block::new(header.clone(), vec![]),), 0);
		assert_ok!(
			Runtime::ensure_inherents_are_first(&Block::new(header.clone(), vec![xt2.clone()]),),
			0
		);
		assert_ok!(
			Runtime::ensure_inherents_are_first(&Block::new(header.clone(), vec![in1.clone()])),
			1
		);
		assert_ok!(
			Runtime::ensure_inherents_are_first(&Block::new(
				header.clone(),
				vec![in1.clone(), xt2.clone()]
			),),
			1
		);
		assert_ok!(
			Runtime::ensure_inherents_are_first(&Block::new(
				header.clone(),
				vec![in2.clone(), in1.clone(), xt2.clone()]
			),),
			2
		);

		assert_eq!(
			Runtime::ensure_inherents_are_first(&Block::new(
				header.clone(),
				vec![xt2.clone(), in1.clone()]
			),),
			Err(1)
		);
		assert_eq!(
			Runtime::ensure_inherents_are_first(&Block::new(
				header.clone(),
				vec![xt2.clone(), xt2.clone(), in1.clone()]
			),),
			Err(2)
		);
		assert_eq!(
			Runtime::ensure_inherents_are_first(&Block::new(
				header.clone(),
				vec![xt2.clone(), xt2.clone(), xt2.clone(), in2.clone()]
			),),
			Err(3)
		);
	});
}

/// Check that block execution rejects blocks with transactions in them while MBMs are active and
/// also that all the system callbacks are called correctly.
#[test]
fn callbacks_in_block_execution_works() {
	callbacks_in_block_execution_works_inner(false);
	callbacks_in_block_execution_works_inner(true);
}

fn callbacks_in_block_execution_works_inner(mbms_active: bool) {
	MbmActive::set(mbms_active);

	for (n_in, n_tx) in (0..10usize).zip(0..10usize) {
		let mut extrinsics = Vec::new();

		let header = new_test_ext(10).execute_with(|| {
			MockedSystemCallbacks::reset();
			Executive::initialize_block(&Header::new_from_number(1));
			assert_eq!(SystemCallbacksCalled::get(), 1);

			for i in 0..n_in {
				let xt = if i % 2 == 0 {
					TestXt::new(RuntimeCall::Custom(custom::Call::inherent {}), None)
				} else {
					TestXt::new(RuntimeCall::Custom2(custom2::Call::optional_inherent {}), None)
				};
				Executive::apply_extrinsic(xt.clone()).unwrap().unwrap();
				extrinsics.push(xt);
			}

			for t in 0..n_tx {
				let xt = TestXt::new(
					RuntimeCall::Custom2(custom2::Call::some_call {}),
					sign_extra(1, t as u64, 0),
				);
				// Extrinsics can be applied even when MBMs are active. Only the `execute_block`
				// will reject it.
				Executive::apply_extrinsic(xt.clone()).unwrap().unwrap();
				extrinsics.push(xt);
			}

			Executive::finalize_block()
		});
		assert_eq!(SystemCallbacksCalled::get(), 3);

		new_test_ext(10).execute_with(|| {
			let header = std::panic::catch_unwind(|| {
				Executive::execute_block(Block::new(header, extrinsics));
			});

			match header {
				Err(e) => {
					let err = e.downcast::<&str>().unwrap();
					assert_eq!(*err, "Only inherents are allowed in this block");
					assert!(
						MbmActive::get() && n_tx > 0,
						"Transactions should be rejected when MBMs are active"
					);
				},
				Ok(_) => {
					assert_eq!(SystemCallbacksCalled::get(), 3);
					assert!(
						!MbmActive::get() || n_tx == 0,
						"MBMs should be deactivated after finalization"
					);
				},
			}
		});
	}
}

#[test]
fn post_inherent_called_after_all_inherents() {
	let in1 = TestXt::new(RuntimeCall::Custom2(custom2::Call::inherent {}), None);
	let xt1 = TestXt::new(RuntimeCall::Custom2(custom2::Call::some_call {}), sign_extra(1, 0, 0));

	let header = new_test_ext(1).execute_with(|| {
		// Let's build some fake block.
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(in1.clone()).unwrap().unwrap();
		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	#[cfg(feature = "try-runtime")]
	new_test_ext(1).execute_with(|| {
		Executive::try_execute_block(
			Block::new(header.clone(), vec![in1.clone(), xt1.clone()]),
			true,
			true,
			frame_try_runtime::TryStateSelect::All,
		)
		.unwrap();
		assert!(MockedSystemCallbacks::post_transactions_called());
	});

	new_test_ext(1).execute_with(|| {
		MockedSystemCallbacks::reset();
		Executive::execute_block(Block::new(header, vec![in1, xt1]));
		assert!(MockedSystemCallbacks::post_transactions_called());
	});
}

/// Regression test for AppSec finding #40.
#[test]
fn post_inherent_called_after_all_optional_inherents() {
	let in1 = TestXt::new(RuntimeCall::Custom2(custom2::Call::optional_inherent {}), None);
	let xt1 = TestXt::new(RuntimeCall::Custom2(custom2::Call::some_call {}), sign_extra(1, 0, 0));

	let header = new_test_ext(1).execute_with(|| {
		// Let's build some fake block.
		Executive::initialize_block(&Header::new_from_number(1));

		Executive::apply_extrinsic(in1.clone()).unwrap().unwrap();
		Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();

		Executive::finalize_block()
	});

	#[cfg(feature = "try-runtime")]
	new_test_ext(1).execute_with(|| {
		Executive::try_execute_block(
			Block::new(header.clone(), vec![in1.clone(), xt1.clone()]),
			true,
			true,
			frame_try_runtime::TryStateSelect::All,
		)
		.unwrap();
		assert!(MockedSystemCallbacks::post_transactions_called());
	});

	new_test_ext(1).execute_with(|| {
		MockedSystemCallbacks::reset();
		Executive::execute_block(Block::new(header, vec![in1, xt1]));
		assert!(MockedSystemCallbacks::post_transactions_called());
	});
}

#[test]
fn is_inherent_works() {
	let ext = TestXt::new(RuntimeCall::Custom2(custom2::Call::inherent {}), None);
	assert!(Runtime::is_inherent(&ext));
	let ext = TestXt::new(RuntimeCall::Custom2(custom2::Call::optional_inherent {}), None);
	assert!(Runtime::is_inherent(&ext));

	let ext = TestXt::new(call_transfer(33, 0), sign_extra(1, 0, 0));
	assert!(!Runtime::is_inherent(&ext));

	let ext = TestXt::new(RuntimeCall::Custom2(custom2::Call::allowed_unsigned {}), None);
	assert!(!Runtime::is_inherent(&ext), "Unsigned ext are not automatically inherents");
}
#[test]
#[should_panic(expected = "cannot build public")]
fn ver_block_import_panic_due_to_lack_of_public_key() {
	new_test_ext(1).execute_with(|| {
		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!(
						"58e5aca3629754c5185b50dd676053c5b9466c18488bb1f4c6138a46885cd79d"
					)
					.into(),
					extrinsics_root: hex!(
						"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
					)
					.into(),
					digest: Digest { logs: vec![] },
					count: 0,
					seed: Default::default(),
				},
				extrinsics: vec![],
			},
			vec![],
		);
	});
}

#[should_panic(expected = "shuffling seed verification failed")]
#[test]
fn ver_block_import_panic_due_to_wrong_signature() {
	new_test_ext(1).execute_with(|| {
		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!(
						"58e5aca3629754c5185b50dd676053c5b9466c18488bb1f4c6138a46885cd79d"
					)
					.into(),
					extrinsics_root: hex!(
						"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
					)
					.into(),
					digest: Digest { logs: vec![] },
					count: 0,
					seed: Default::default(),
				},
				extrinsics: vec![],
			},
			vec![0; 32],
		);
	});
}

#[test]
fn ver_block_import_works() {
	new_test_ext(1).execute_with(|| {
		let prev_seed = vec![0u8; 32];
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let data: VrfSignData =
			VrfTranscript::new(b"shuffling_seed", &[(b"prev_seed", &prev_seed)]).into();

		let signature =
			keystore.sr25519_vrf_sign(AURA, &key_pair.public(), &data).unwrap().unwrap();

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();
		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!(
						"1f7989b3ab76d00e837a96e881d7477f79797e6ccd9a9e972a374ed6d83e2d01"
					)
					.into(),
					extrinsics_root: hex!(
						"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
					)
					.into(),
					digest: Digest { logs: vec![] },
					count: 0,
					seed: ShufflingSeed {
						seed: H256::from_slice(signature.pre_output.encode().as_bytes_ref()),
						proof: H512::from_slice(signature.proof.encode().as_bytes_ref()),
					},
				},
				extrinsics: vec![],
			},
			pub_key_bytes,
		);
	});
}

#[test]
fn accept_block_that_fetches_txs_from_the_queue() {
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();
		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let xt = TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0));

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let txs = vec![TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0))];

		let enqueue_txs_inherent = TestXt::new(
			enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
			None,
		);
		let tx_hashes_list = txs
			.clone()
			.iter()
			.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
			.collect::<Vec<_>>();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"42fd4147ca2f13b45f616dc4ca20a71cd66037f000626c3f5e538091f08b7e2f"
					)
					.into(),
					extrinsics_root: hex!(
						"325ff57815f725eb40852ec4cd91526f8bdbbc1bd1c5d79e5a85d5d92704b0c9"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent],
			},
			pub_key_bytes.clone(),
		);

		MockedSystemCallbacks::reset();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 2,
					state_root: hex!(
						"4cbb56eb7f93957f0a2199523710ed40ba67d4cd5c10f3f3a94f5cc413aeba2a"
					)
					.into(),
					extrinsics_root: hex!(
						"c8244f5759b5efd8760f96f5a679c78b2e8ea65c6095403f8f527c0619082694"
					)
					.into(),
					digest: Digest { logs: vec![] },
					count: 1,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![xt.clone()],
			},
			pub_key_bytes.clone(),
		);
	});
}

#[test]
#[should_panic(expected = "Transaction would exhaust the block limits")]
fn rejects_block_that_enqueues_too_many_transactions_to_storage_queue() {
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let txs = (0..100000)
			.map(|nonce| TestXt::new(call_transfer(2, 69), sign_extra(1, nonce, 0)))
			.collect::<Vec<_>>();

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let enqueue_txs_inherent = TestXt::new(
			enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
			None,
		);

		let tx_hashes_list = txs
			.clone()
			.iter()
			.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
			.collect::<Vec<_>>();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"5bc40cfd524119a0f1ca2fbd9f0357806d0041f56e0de1750b1fe0011915ca4c"
					)
					.into(),
					extrinsics_root: hex!(
						"6406786b8a8f590d77d8dc6126c16f7f1621efac35914834d95ec032562f5125"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent],
			},
			pub_key_bytes.clone(),
		);
	});
}

#[test]
#[should_panic(expected = "Collator didnt execute enqueued txs")]
fn rejects_block_that_enqueues_new_txs_but_doesnt_execute_any() {
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let txs = (0..10)
			.map(|nonce| TestXt::new(call_transfer(2, 69), sign_extra(1, nonce, 0)))
			.collect::<Vec<_>>();

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let enqueue_txs_inherent = TestXt::new(
			enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
			None,
		);

		let tx_hashes_list = txs
			.clone()
			.iter()
			.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
			.collect::<Vec<_>>();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"b7f32cbc8889c69c2c988e5eae74c0dadb2ef01eb41ab265b44b309a9f108773"
					)
					.into(),
					extrinsics_root: hex!(
						"f380e937898ceef6feb3fbb47e4fb59d0be185c5f98be64baafa89c778d165c5"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent.clone()],
			},
			pub_key_bytes.clone(),
		);

		MockedSystemCallbacks::reset();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 2,
					state_root: hex!(
						"545b9b54abe19f999e0186186cce55a1615d78814c1571b0db1417570d8b8ca3"
					)
					.into(),
					extrinsics_root: hex!(
						"f380e937898ceef6feb3fbb47e4fb59d0be185c5f98be64baafa89c778d165c5"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent.clone()],
			},
			pub_key_bytes.clone(),
		);
	});
}

#[test]
#[should_panic(expected = "cannot deserialize tx that has been just enqueued")]
fn do_not_allow_to_accept_binary_blobs_that_does_not_deserialize_into_valid_tx() {
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let dummy_paylaod = b"not an extrinsic".to_vec();
		let enqueue_txs_inherent =
			TestXt::new(enqueue_txs(vec![(Some(2), dummy_paylaod.clone())]), None);

		let tx_hashes_list =
			vec![<Runtime as frame_system::Config>::Hashing::hash(&dummy_paylaod[..])];

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"f41b79a2cce94a67f604caf48cf7e76f33d4c0b71593a7ab7904e6f33c7db88d"
					)
					.into(),
					extrinsics_root: hex!(
						"47f1dc33bc8221e453f3d48e6cedb33aa8fec1bdba47da155096bf67f614fb82"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent.clone()],
			},
			pub_key_bytes.clone(),
		);
	});
}

#[test]
fn do_not_panic_when_tx_poped_from_storage_queue_cannot_be_deserialized() {
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let txs = vec![TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0))];

		let enqueue_txs_inherent = TestXt::new(
			enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
			None,
		);
		let tx_hashes_list = txs
			.clone()
			.iter()
			.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
			.collect::<Vec<_>>();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"42fd4147ca2f13b45f616dc4ca20a71cd66037f000626c3f5e538091f08b7e2f"
					)
					.into(),
					extrinsics_root: hex!(
						"325ff57815f725eb40852ec4cd91526f8bdbbc1bd1c5d79e5a85d5d92704b0c9"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent],
			},
			pub_key_bytes.clone(),
		);

		// inject some garbage instead of tx
		let mut queue = frame_system::StorageQueue::<Runtime>::take();
		queue.as_mut().last_mut().unwrap().2 = vec![(Some(2), b"not an extrinsic".to_vec())];
		frame_system::StorageQueue::<Runtime>::put(queue);
		MockedSystemCallbacks::reset();

		// tx is poped but not executed
		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 2,
					state_root: hex!(
						"3f1b1932c7d489a7229a67f46d3c9376ce97037f41e6b0dc8e89df487603a6a5"
					)
					.into(),
					extrinsics_root: hex!(
						"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
					)
					.into(),
					digest: Digest { logs: vec![] },
					count: 1,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![],
			},
			pub_key_bytes.clone(),
		);
	});
}

#[test]
fn do_not_panic_when_tx_poped_from_storage_queue_is_invalid() {
	// inject txs with wrong nonces
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let txs = vec![
			TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0)),
			TestXt::new(call_transfer(2, 69), sign_extra(1, 2, 0)), /* <- this txs is
			                                                         * invalide
			                                                         * because of nonce that
			                                                         * should be == 1 */
		];

		let enqueue_txs_inherent = TestXt::new(
			enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
			None,
		);
		let tx_hashes_list = txs
			.clone()
			.iter()
			.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
			.collect::<Vec<_>>();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"af9112076090e4fb831c5f302bae99385a2bd05eb4d46dadc4c1e65048de7cda"
					)
					.into(),
					extrinsics_root: hex!(
						"0bf3649935d974c08416350641382ffef980a58eace1f4b5b968705d206c7aae"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent],
			},
			pub_key_bytes.clone(),
		);

		MockedSystemCallbacks::reset();

		// tx is poped fails on execution and doeasnt stuck the chain
		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 2,
					state_root: hex!(
						"2459549cbf3eff4af1086c64d4b8dc7aff8bedb400c440c59d847ec727f63385"
					)
					.into(),
					extrinsics_root: hex!(
						"ead5b1f0927906077db74d0a0621707e2b2ee93ce6145f83cee491801a010c14"
					)
					.into(),
					digest: Digest { logs: vec![] },
					count: 2,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: txs,
			},
			pub_key_bytes.clone(),
		);
	});
}

#[test]
#[should_panic(expected = "only unique txs can be passed into queue")]
fn reject_block_that_tries_to_enqueue_same_tx_mulitple_times() {
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let txs = vec![
			TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0)), /* duplicated tx should
			                                                         * be rejected */
			TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0)),
		];

		let enqueue_txs_inherent = TestXt::new(
			enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
			None,
		);
		let tx_hashes_list = txs
			.clone()
			.iter()
			.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
			.collect::<Vec<_>>();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"10b8fe2ef82cb245fc71dab724fde5462bacc4f0d2b3b6bf0581aa89d63ef3a1"
					)
					.into(),
					extrinsics_root: hex!(
						"2b8d0b6c617c1bc4003690d7e83d33cbe69d7237167e52c446bc690e188ce300"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent],
			},
			pub_key_bytes.clone(),
		);
	});
}

#[test]
#[should_panic(expected = "enqueue_txs inherent can only be called once per block")]
fn reject_block_that_enqueus_same_tx_multiple_times() {
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let txs = vec![TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0))];
		let enqueue_txs_inherent = TestXt::new(
			enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
			None,
		);

		let tx_hashes_list = txs
			.clone()
			.iter()
			.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
			.collect::<Vec<_>>();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"10b8fe2ef82cb245fc71dab724fde5462bacc4f0d2b3b6bf0581aa89d63ef3a1"
					)
					.into(),
					extrinsics_root: hex!(
						"c455a6cba17ea145cc03fa905ae969826a26780278ace184c61510e638901a85"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 0,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent.clone(), enqueue_txs_inherent],
			},
			pub_key_bytes.clone(),
		);
	});
}

#[test]
#[should_panic(expected = "not enought elements to pop found")]
fn reject_block_that_tries_to_pop_more_txs_than_available() {
	new_test_ext(1).execute_with(|| {
		let secret_uri = "//Alice";
		let keystore = MemoryKeystore::new();

		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
		keystore
			.insert(AURA, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
			.iter()
			.cloned()
			.collect::<Vec<_>>();

		let txs: Vec<TestXt> = vec![TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0))];
		let enqueue_txs_inherent = TestXt::new(
			enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
			None,
		);

		let tx_hashes_list = txs
			.clone()
			.iter()
			.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
			.collect::<Vec<_>>();

		Executive::execute_block_ver(
			Block {
				header: Header {
					parent_hash: System::parent_hash(),
					number: 1,
					state_root: hex!(
						"c6bbd33a1161f1b0d719594304a81c6cc97a183a64a09e1903cb58ed6e247148"
					)
					.into(),
					extrinsics_root: hex!(
						"9f907f07e03a93bbb696e4071f58237edc3 5a701d24e5a2155cf52a2b32a4ef3"
					)
					.into(),
					digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
					count: 1,
					seed: calculate_next_seed_from_bytes(
						&keystore,
						&key_pair.public(),
						System::block_seed().as_bytes().to_vec(),
					)
					.unwrap(),
				},
				extrinsics: vec![enqueue_txs_inherent.clone(), enqueue_txs_inherent],
			},
			pub_key_bytes.clone(),
		);
	});
}
