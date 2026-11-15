// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Source compiler-simplification registration, sharing the compiler recognizer.
use crate::ElabError;
use clean_kernel::{Environment, Name};
pub(crate) fn register(env: &mut Environment, name: &Name) -> Result<(), ElabError> {
    if env.get_const(name).is_none() {
        return Err(ElabError::UnknownIdent(name.to_string()));
    }
    if !clean_kernel::env::csimp::register(env, name) {
        return Err(ElabError::InvalidCsimpTheorem { name: name.clone() });
    }
    Ok(())
}

/// Register a local rule without adding a persistent global attribute marker.
pub(crate) fn register_local(
    env: &mut Environment,
    name: &Name,
) -> Result<clean_kernel::env::csimp::LocalRule, ElabError> {
    if env.get_const(name).is_none() {
        return Err(ElabError::UnknownIdent(name.to_string()));
    }
    clean_kernel::env::csimp::register_local(env, name)
        .ok_or_else(|| ElabError::InvalidCsimpTheorem { name: name.clone() })
}
