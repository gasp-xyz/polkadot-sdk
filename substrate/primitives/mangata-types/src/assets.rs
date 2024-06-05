use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A type describing our custom additional metadata stored in the orml-asset-registry.
#[derive(
	Clone,
	Copy,
	Default,
	PartialOrd,
	Ord,
	PartialEq,
	Eq,
	Debug,
	Encode,
	Decode,
	TypeInfo,
	MaxEncodedLen,
)]
pub struct CustomMetadata {
	/// XCM-related metadata, optional.
	pub xcm: Option<XcmMetadata>,
	/// XYK-related metadata, optional
	pub xyk: Option<XykMetadata>,
}

#[derive(
	Clone,
	Copy,
	Default,
	PartialOrd,
	Ord,
	PartialEq,
	Eq,
	Debug,
	Encode,
	Decode,
	TypeInfo,
	MaxEncodedLen,
)]
pub struct XcmMetadata {
	/// The fee charged for every second that an XCM message takes to execute.
	pub fee_per_second: u128,
}

#[derive(
	Clone,
	Copy,
	Default,
	PartialOrd,
	Ord,
	PartialEq,
	Eq,
	Debug,
	Encode,
	Decode,
	TypeInfo,
	MaxEncodedLen,
)]
pub struct XykMetadata {
	/// If the asset can't be used in the xyk operations.
	pub operations_disabled: bool,
}

#[derive(
	Clone,
	PartialOrd,
	Ord,
	PartialEq,
	Eq,
	Debug,
	Encode,
	Decode,
	TypeInfo,
	MaxEncodedLen
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum L1Asset {
	Ethereum([u8;20]),
	Arbitrum([u8;20])
}
