// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment seeding for depgraph analysis.
//!
//! Mirrors `crates/clean-mathverse/src/bin/mathverse_shard/native_build.rs::seed_environment`
//! so the depgraph CLI sees the same declaration set as the clean-Native
//! shard builder. If the native-build seed changes (new tier-A tranches,
//! new headline demotions, …) keep this seed in sync so the ranking
//! reflects what the shard builder actually accepts.

use clean_kernel::Environment;

/// Short headline alias → fully qualified kernel `Name`.
///
/// Agents invoke `clean-depgraph --headline T60` with the short form. The
/// CLI and library both resolve via [`headline_name`] so a typo or case
/// slip (e.g. `t60`, `C004`, `c006`) still lands on the canonical
/// declaration. Entries here are the kernel `Declaration::Axiom` or
/// `Declaration::Theorem` registration names.
///
/// Extend this slice when a new headline is promoted into the
/// verification story. The order is informational only.
pub const KNOWN_HEADLINES: &[(&str, &str)] = &[
    ("T60", "NNVerify.Block.blockwise_crown_sound"),
    ("C004", "NNVerify.C004.crown_equals_ibp"),
    ("C006", "NNVerify.C006.blockwise_equals_monolithic"),
    // Additional useful entry points — all currently registered as
    // `Declaration::Axiom` after 2026-04-19 masquerade demotions (#3494,
    // #3495, #3509, #3590) or as plain registrations.
    ("T20", "NNVerify.Block.zonotope_reset"),
    ("T21", "NNVerify.Block.width_preserved"),
    ("T22", "NNVerify.LayerNorm.generators_after_ln"),
    ("T61", "NNVerify.Block.blockwise_complexity"),
];

/// Resolve a headline alias (`"T60"`, `"C004"`, …) into the kernel
/// declaration name. Falls back to the raw input string so agents can
/// also pass a fully-qualified `NNVerify.…` name when they already know
/// the exact kernel identifier.
///
/// Lookup is case-insensitive on the alias side; the fallback is
/// case-sensitive because kernel names are.
#[must_use]
pub fn headline_name(alias: &str) -> String {
    let up = alias.to_ascii_uppercase();
    for (short, full) in KNOWN_HEADLINES {
        if short.eq_ignore_ascii_case(&up) {
            return (*full).to_string();
        }
    }
    alias.to_string()
}

/// Seed a fresh kernel `Environment` with the math-overlay declarations
/// that make headline claims T60 / C004 / C006 reachable.
///
/// Mirrors `mathverse_shard build-native`'s seed step. Each `init_*` call is
/// best-effort (logged, not fatal) so that a future refactor that splits
/// one of the init helpers does not silently break the depgraph CLI.
/// Callers that need hard failure can match on the returned error counts
/// via `Result` wrappers in their own code.
pub fn seed_environment(env: &mut Environment) {
    if let Err(e) = env.init_nn_verify_blockwise_crown_ext() {
        eprintln!("Warning: C006 ext init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_interval_arith_proofs() {
        eprintln!("Warning: interval-arith proofs init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_ibp_width_zero() {
        eprintln!("Warning: ibp_width_zero sub-lemmas init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_min_zero() {
        eprintln!("Warning: tier-A rat_min_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_le_refl_zero() {
        eprintln!("Warning: tier-A rat_le_refl_zero init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_zero_eq_max() {
        eprintln!("Warning: tier-A rat_zero_eq_max init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_zero_eq_min() {
        eprintln!("Warning: tier-A rat_zero_eq_min init failed: {e}");
    }
    if let Err(e) = env.init_nn_verify_tier_a_rat_max_eq_min() {
        eprintln!("Warning: tier-A rat_max_eq_min init failed: {e}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_headlines_resolve() {
        assert_eq!(headline_name("T60"), "NNVerify.Block.blockwise_crown_sound");
        assert_eq!(headline_name("t60"), "NNVerify.Block.blockwise_crown_sound");
        assert_eq!(headline_name("C004"), "NNVerify.C004.crown_equals_ibp");
        assert_eq!(
            headline_name("C006"),
            "NNVerify.C006.blockwise_equals_monolithic"
        );
    }

    #[test]
    fn unknown_alias_passes_through() {
        let raw = "NNVerify.Made.Up";
        assert_eq!(headline_name(raw), raw);
    }

    #[test]
    fn seed_registers_t60() {
        let mut env = Environment::new();
        seed_environment(&mut env);
        let t60 = clean_kernel::Name::from_string("NNVerify.Block.blockwise_crown_sound");
        assert!(env.get_const(&t60).is_some(), "seed must register T60");
    }

    #[test]
    fn seed_registers_c004_and_c006() {
        let mut env = Environment::new();
        seed_environment(&mut env);
        let c004 = clean_kernel::Name::from_string("NNVerify.C004.crown_equals_ibp");
        let c006 = clean_kernel::Name::from_string("NNVerify.C006.blockwise_equals_monolithic");
        assert!(env.get_const(&c004).is_some(), "seed must register C004");
        assert!(env.get_const(&c006).is_some(), "seed must register C006");
    }
}
