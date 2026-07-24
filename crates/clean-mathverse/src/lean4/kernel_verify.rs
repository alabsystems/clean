// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel re-verification for `.olean`-imported declarations.
//!
//! After `clean_olean::load_module_with_deps` structurally registers
//! constants into a kernel `Environment`, those constants were validated
//! for structural well-formedness (no free variables, no metavariables,
//! level-parameter scope) but NOT for full type-checking.
//!
//! This module provides [`kernel_verify_const`], which re-runs the full
//! Lean 4 `add_decl` Phase 1 validation on a single imported constant:
//!
//! 1. `infer_sort(type)` — the declared type is itself a well-formed type.
//! 2. For theorems: the inferred sort is `Sort 0` (the type is a Prop).
//! 3. For declarations with values: `check_type(value, type)` — the proof
//!    term has the declared type under definitional equality.
//!
//! Unlike [`crate::lean4::shard_verify::verify_shard_into_env`], which
//! reconstructs declarations from shard bytes and feeds them through
//! `add_decl` (populating a fresh env), this function operates on
//! constants ALREADY in the environment. It reuses the entire transitively
//! loaded dependency graph for name resolution. This is the minimal
//! kernel-verification step required for issue #3370: "Imported
//! declarations pass `add_decl` kernel type checking."
//!
//! # Trust Accounting
//!
//! A constant that passes [`kernel_verify_const`] earns
//! [`ImportConfidence::KernelVerified`] status. The corresponding
//! `AxiomProfile` is computed via
//! [`crate::lean4::env_import::compute_env_axiom_profile`].
//!
//! # Example
//!
//! ```text
//! use clean_kernel::env::Environment;
//! use clean_mathverse::lean4::kernel_verify::kernel_verify_const;
//! use clean_mathverse::lean4::mathlib_import::{find_lean_lib_path, load_init_modules};
//!
//! let mut env = Environment::default();
//! let lean_lib = find_lean_lib_path().expect("Lean 4 toolchain");
//! load_init_modules(&mut env, &lean_lib);
//!
//! let result = kernel_verify_const(&env, "Nat.add_zero")
//!     .expect("Nat.add_zero should kernel-verify");
//! assert!(result.verified);
//! assert!(result.has_value);
//! ```

use std::time::Instant;

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_kernel::{ConstantInfo, ConstantKind};
use thiserror::Error;

use crate::lean4::env_import::compute_env_axiom_profile;
use crate::types::{AxiomProfile, ImportConfidence};

/// Outcome of a successful kernel verification pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelVerifyOk {
    /// The verified constant's fully qualified name.
    pub name: String,
    /// Kernel `ConstantKind` of the verified constant.
    pub kind: ConstantKind,
    /// `true` if the constant carries a proof/value term that was also
    /// definitionally checked against the declared type.
    pub has_value: bool,
    /// `true` if the constant is a `Theorem` whose type was re-confirmed
    /// to live in `Prop`.
    pub is_theorem: bool,
    /// Trust-upgraded import confidence for this constant.
    pub confidence: ImportConfidence,
    /// Re-computed axiom profile (CHOICE/PROP_EXT/QUOT bits).
    pub axiom_profile: AxiomProfile,
    /// Wall-clock microseconds spent in the type checker. Useful for
    /// diagnostics on slow proofs (e.g., Mathlib lemmas with large proof
    /// trees). Excludes env/name lookup.
    pub checked_us: u128,
    /// Always `true` on success; present for ergonomic call sites that
    /// want a boolean summary.
    pub verified: bool,
}

/// Errors that can be raised when kernel-verifying an imported constant.
#[derive(Debug, Error)]
pub enum KernelVerifyError {
    /// The requested constant was not found in the environment. Callers
    /// typically load `.olean` dependencies first via
    /// [`clean_olean::load_module_with_deps`].
    #[error("constant not found in environment: {0}")]
    NotFound(String),
    /// The declared type was rejected by the kernel's type checker
    /// (`infer_sort` returned an error).
    #[error("type check failed for `{name}`: {reason}")]
    TypeCheckFailed { name: String, reason: String },
    /// A `Theorem` declaration carried a type that is not in `Prop`
    /// (Sort 0). This mirrors Lean 4's `environment.cpp:add_theorem`
    /// invariant.
    #[error("theorem type is not in Prop for `{name}` (sort: {sort})")]
    TheoremTypeNotProp { name: String, sort: String },
    /// The proof/value term did not check against the declared type.
    #[error("value does not check against declared type for `{name}`: {reason}")]
    ValueTypeMismatch { name: String, reason: String },
}

/// Environment variable that overrides the kernel heartbeat (n_LIMIT) budget
/// used by the sharded kernel-verification workers.
///
/// The value is parsed as a `u32` count of heartbeat ticks. `0` means
/// UNLIMITED — the heavy-tail modules (`CategoryTheory.Limits.*`,
/// `Tactic.Ring.*`) whose WHNF reduction exceeds the default budget then run to
/// completion instead of being budget-rejected. Any other value sets an
/// explicit limit. When the variable is unset or unparseable, the kernel's own
/// `DEFAULT_HEARTBEAT_LIMIT` (2,000,000) is used unchanged.
///
/// # Soundness
/// Raising or removing the heartbeat budget is SOUNDNESS-NEUTRAL: the heartbeat
/// is a resource ceiling, not a proof-acceptance criterion. A larger budget can
/// only let MORE valid proofs finish type-checking; it can never cause an
/// invalid proof to be accepted (the checks themselves are unchanged).
pub const HEARTBEAT_ENV_VAR: &str = "CLEAN_KERNEL_HEARTBEAT";

/// Read the heartbeat override from [`HEARTBEAT_ENV_VAR`].
///
/// Returns:
/// - `Some(n)` when the variable is set and parses as a `u32` (`0` = unlimited);
/// - `None` when the variable is unset or does not parse — callers then keep the
///   kernel's `DEFAULT_HEARTBEAT_LIMIT`.
#[must_use]
pub fn heartbeat_from_env() -> Option<u32> {
    std::env::var(HEARTBEAT_ENV_VAR)
        .ok()
        .and_then(|raw| raw.trim().parse::<u32>().ok())
}

/// Kernel-verify a single imported constant already present in `env`.
///
/// Runs the same checks as `Environment::add_decl`'s Phase 1, but against
/// the constant currently in the environment rather than a freshly
/// supplied `Declaration`. This provides end-to-end kernel verification
/// for `.olean`-imported lemmas without requiring a roundtrip through the
/// `.mathverse` shard format.
///
/// Uses the kernel's `DEFAULT_HEARTBEAT_LIMIT`. To run with a different
/// heartbeat budget (e.g. unlimited, for the heavy-tail modules), use
/// [`kernel_verify_const_with_heartbeat`].
///
/// # REQUIRES
/// - `name` is a well-formed fully qualified Lean constant name
/// - `env` is an [`Environment`] that already contains `name` (e.g., via
///   [`clean_olean::load_module_with_deps`]) AND all of its transitive
///   constant dependencies
///
/// # ENSURES
/// - On success, the returned [`KernelVerifyOk`] certifies that the
///   constant's declared type and (if present) value pass the full Lean 4
///   kernel `add_decl` Phase 1 validation under this environment.
/// - The environment is not modified. All kernel checks run via a scoped
///   [`TypeChecker`] borrow.
pub fn kernel_verify_const(
    env: &Environment,
    name: &str,
) -> Result<KernelVerifyOk, KernelVerifyError> {
    kernel_verify_const_with_heartbeat(env, name, None)
}

/// Kernel-verify a single imported constant with an explicit heartbeat budget.
///
/// Identical to [`kernel_verify_const`] except that `heartbeat_limit` overrides
/// the kernel's `DEFAULT_HEARTBEAT_LIMIT`:
/// - `None` keeps the kernel default unchanged;
/// - `Some(0)` runs UNLIMITED (no heartbeat ceiling — recovers heavy-tail
///   modules that the default budget rejects);
/// - `Some(n)` sets an explicit `n`-tick ceiling.
///
/// # Soundness
/// The heartbeat is a resource ceiling only. Changing it is soundness-neutral:
/// the Phase-1 checks (`infer_sort`, Prop-sort, `check_type`) are unchanged, so
/// a larger budget only lets more valid proofs finish — it never accepts an
/// invalid one. See [`HEARTBEAT_ENV_VAR`].
///
/// # REQUIRES / ENSURES
/// Same contract as [`kernel_verify_const`].
pub fn kernel_verify_const_with_heartbeat(
    env: &Environment,
    name: &str,
    heartbeat_limit: Option<u32>,
) -> Result<KernelVerifyOk, KernelVerifyError> {
    let kname = Name::from_string(name);
    let ci = env
        .get_const(&kname)
        .ok_or_else(|| KernelVerifyError::NotFound(name.to_string()))?;

    let start = Instant::now();

    // Run kernel Phase 1 checks inside a scoped TypeChecker borrow.
    // Mirrors `Environment::add_decl` exactly for the type-check / sort
    // / Prop-sort / check-value steps (see env/decl_add.rs:263-322).
    let is_theorem = ci.kind == ConstantKind::Theorem;
    {
        let mut tc = TypeChecker::new(env);
        // SOUNDNESS-NEUTRAL: the heartbeat is a resource ceiling, not an
        // acceptance criterion. Overriding it only changes how many ticks the
        // checker may spend, never which terms it accepts.
        if let Some(limit) = heartbeat_limit {
            tc.set_heartbeat_limit(limit);
        }

        // 1. The declared type must itself be a well-formed type.
        let sort = tc
            .infer_sort(&ci.type_)
            .map_err(|e| KernelVerifyError::TypeCheckFailed {
                name: name.to_string(),
                reason: format!("{e:?}"),
            })?;

        // 2. For theorems: the type's sort must be exactly 0 (Prop).
        if is_theorem && !sort.is_zero() {
            return Err(KernelVerifyError::TheoremTypeNotProp {
                name: name.to_string(),
                sort: format!("{sort:?}"),
            });
        }

        // 3. For declarations with values: the value must check against
        //    the declared type under the kernel's definitional equality.
        if let Some(value) = &ci.value {
            tc.check_type(value, &ci.type_)
                .map_err(|e| KernelVerifyError::ValueTypeMismatch {
                    name: name.to_string(),
                    reason: format!("{e:?}"),
                })?;
        }
    }

    let checked_us = start.elapsed().as_micros();
    let axiom_profile = compute_env_axiom_profile(ci);
    let confidence = confidence_after_verify(ci);

    Ok(KernelVerifyOk {
        name: name.to_string(),
        kind: ci.kind,
        has_value: ci.value.is_some(),
        is_theorem,
        confidence,
        axiom_profile,
        checked_us,
        verified: true,
    })
}

/// Import confidence assigned to a constant that has passed
/// [`kernel_verify_const`]. Axioms and opaques remain `Axiomatized`; all
/// others (Theorem, Definition with value) promote to `KernelVerified`.
fn confidence_after_verify(ci: &ConstantInfo) -> ImportConfidence {
    match ci.kind {
        // Axioms have no value to verify; they remain axiomatized by
        // definition. An opaque with a value has passed value checking
        // but is still treated as axiomatic for trust (matches the
        // heuristic in [`env_import::confidence_for`]).
        ConstantKind::Axiom | ConstantKind::Opaque => ImportConfidence::Axiomatized,
        ConstantKind::Theorem | ConstantKind::Definition => {
            if ci.value.is_some() {
                ImportConfidence::KernelVerified
            } else {
                // Theorem/Definition without a value shouldn't happen
                // post-.olean load, but treat defensively.
                ImportConfidence::Axiomatized
            }
        }
    }
}

/// Batch-verify a set of imported constants. Returns `(verified, failures)`.
///
/// Short-circuits nothing: every name is attempted. Useful for smoke-
/// testing that a freshly imported module of Mathlib lemmas passes
/// kernel verification end-to-end.
pub fn kernel_verify_all(
    env: &Environment,
    names: &[&str],
) -> (Vec<KernelVerifyOk>, Vec<(String, KernelVerifyError)>) {
    let mut ok = Vec::with_capacity(names.len());
    let mut err = Vec::new();
    for &n in names {
        match kernel_verify_const(env, n) {
            Ok(v) => ok.push(v),
            Err(e) => err.push((n.to_string(), e)),
        }
    }
    (ok, err)
}

#[cfg(test)]
#[path = "kernel_verify_tests.rs"]
mod tests;
