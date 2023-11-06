#![cfg_attr(not(feature = "std"), no_std)]
pub use sp_runtime::{
	generic,
	traits::{BlakeTwo256, IdentifyAccount, Verify},
	MultiAddress, MultiSignature, OpaqueExtrinsic,
};
pub mod assets;
pub mod multipurpose_liquidity;
