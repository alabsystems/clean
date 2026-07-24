// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern matching, monotonicity, and specialized tactics
//!
//! This module contains tactics for:
//! - Monotonicity reasoning (mono)
//! - simpa (simp + assumption)
//! - Continuity and measurability provers
//! - Recursive intro patterns (rintro)
//! - If-then-else splitting (split_ifs)
//! - Existential elimination (choose)
//! - Instance inference (infer_instance)
//! - Nontriviality prover
//! - Linear combinations
//! - Definitional simplification (dsimp)

mod choose;
mod continuity;
mod dsimp;
mod infer_instance;
mod linear_combination;
pub(crate) mod linear_combination_proof;
mod measurability;
mod mono;
mod nontriviality;
mod peel;
mod rintro;
mod simpa;
mod split_ifs;
pub(crate) mod util;

// === Public re-exports (used by tactic/mod.rs pub use pattern::...) ===

// mono
pub use mono::{mono, mono_with_config, MonoConfig, MonoStep};

// simpa
pub use simpa::{simpa, simpa_only, simpa_with_config};

// continuity
pub use continuity::{continuity, continuity_with_config, ContinuityConfig};

// measurability
pub use measurability::{measurability, measurability_with_config, MeasurabilityConfig};

// rintro + peel
pub use peel::peel;
pub use rintro::{destruct_named_hypothesis, rintro, rintro_patterns, RIntroPattern};

// split_ifs
pub use split_ifs::{split_ifs, split_ifs_with_config, split_ifs_with_names, SplitIfsConfig};

// choose
pub use choose::{choose, choose_simple, ChooseConfig};

// infer_instance
pub use infer_instance::{infer_instance, infer_instance_with_config, InferInstanceConfig};

// nontriviality
pub use nontriviality::{
    nontriviality, nontriviality_of, nontriviality_with_config, NontrivialityConfig,
};

// linear_combination
pub use linear_combination::{
    linear_combination, linear_combination_simple, linear_combination_with_config, LinearCoeff,
    LinearCombinationConfig,
};

// dsimp
pub use dsimp::{dsimp, dsimp_all, dsimp_at, dsimp_with_config, DsimpConfig};

// === pub(crate) re-exports (used by tactic/mod.rs pub(crate) use pattern::...) ===

pub(crate) use rintro::contains_unassigned_meta;
pub(crate) use util::exprs_equal;

// === pub(crate) re-exports for #[cfg(test)] in tactic/mod.rs ===
// These items are re-exported from tactic/mod.rs under #[cfg(test)]

#[cfg(test)]
pub(crate) use continuity::is_continuity_goal;
#[cfg(test)]
pub(crate) use dsimp::{occurs_bvar_dsimp, shift_bvars_dsimp};
#[cfg(test)]
pub(crate) use measurability::is_measurability_goal;
#[cfg(test)]
pub(crate) use peel::count_foralls;
#[cfg(test)]
pub(crate) use rintro::{rename_hypothesis, split_pattern_args};
#[cfg(test)]
pub(crate) use split_ifs::{is_dite_const, is_ite_const};
#[cfg(test)]
pub(crate) use util::{
    apply_predicate, extract_binary_args, extract_class_name, find_first_type,
    generate_fresh_hyp_name, get_app_head, infer_simple_type, is_binary_app, is_false_prop,
    is_true_prop, make_relation, try_extract_exists, try_infer_expr_type,
};
