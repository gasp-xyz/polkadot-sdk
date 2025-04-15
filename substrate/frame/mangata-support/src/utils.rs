#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::{traits::{MaybeConvert}, ModuleError, DispatchError};

pub struct ConvertError;
impl MaybeConvert<DispatchError, ModuleError> for ConvertError {
    fn maybe_convert(a: DispatchError) -> Option<ModuleError> {
        // To prevent module error message from causing bloat
        match a.stripped() {
            DispatchError::Module(e) => Some(e),
            _ => None
        }
    }
}
