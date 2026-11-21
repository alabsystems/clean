// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Select the installed Nat formatter from the checked program that uses it.
use clean_kernel::{Environment, LeanWorld, Name};
use sha2::{Digest, Sha256};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum NatDisplay {
    Bootstrap,
    Compile,
    Original,
}

impl NatDisplay {
    pub(crate) fn select(
        world: Option<LeanWorld>,
        env: &Environment,
        context: Option<&clean_elab::FileContext>,
    ) -> Self {
        if world != Some(LeanWorld::Lean436) {
            return Self::Bootstrap;
        }
        if context
            .and_then(clean_elab::FileContext::stable_nat_dictionary)
            .is_some()
            && original_selection(env)
        {
            Self::Original
        } else {
            Self::Compile
        }
    }

    pub(crate) fn uses_shim(self, symbol: &str) -> bool {
        match symbol {
            // The stable dictionary is an ordinary checked definition. A local
            // instance can provide an entirely different method.
            "l_instToStringNat" if self != Self::Bootstrap => false,
            "l_Nat_reprFast" if self == Self::Original => true,
            _ => super::native_build::is_primitive_denylisted(symbol),
        }
    }
}

fn original_selection(env: &Environment) -> bool {
    let root = Name::interned("instToStringNat");
    let Ok(closure) = clean_compiler::RuntimeBindingClosure::check_executable(env, &[root]) else {
        return false;
    };
    // Hash the full checked compiler selection, including replacement rules,
    // extern descriptors, and the logical declaration digests at their roots.
    let mut bytes = vec![0u8; 26585];
    let mut remaining = bytes.as_mut_slice();
    if serde_json::to_writer(&mut remaining, &closure.selected_binding_records()).is_err()
        || !remaining.is_empty()
    {
        return false;
    }
    let digest: String = Sha256::digest(&bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    digest == ORIGINAL_SELECTION
}

const ORIGINAL_SELECTION: &str = "45bdd707b29edf091c8ca91e7676cbd55ba2c64c050aa7a2169b1bdc3bbed55f";
