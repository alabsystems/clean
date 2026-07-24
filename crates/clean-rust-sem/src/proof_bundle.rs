// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean-facing ownership proof bundles built from parsed Rust source.

use crate::expr::EvalResult;
use crate::nll::NllResult;
use crate::proof_bundle_builder::{BundleStats, OwnershipObligation};
use crate::proof_obligations::ProofObligation;
use crate::source::SourceProgram;
use crate::translate::{translate_value, TranslationContext};
use crate::vir_lowering::{LoweredProgram, VirLoweringError};
use clean_kernel::Expr as LeanExpr;
use std::collections::BTreeMap;

#[derive(Debug)]
pub struct RustProofBundle {
    pub lowered: LoweredProgram,
    pub borrow_results: BTreeMap<String, NllResult>,
    pub obligations: Vec<ProofObligation>,
    pub translated_types: BTreeMap<String, TranslatedFunctionTypes>,
    pub aliasing_observation: AliasingObservation,
    /// Ownership obligations extracted from NLL borrow-check and aliasing.
    pub ownership_obligations: Vec<OwnershipObligation>,
    /// CONCRETE, kernel-decidable reflections of the NLL verdict, both directions
    /// (see [`crate::concrete_liveness`]). Families: (a) LIVENESS — per live borrow of
    /// a passing function, `1 <= |region|` with the literal from the real region;
    /// (b) ORIGIN WELL-FORMEDNESS — per live borrow, a witness equality
    /// `enc(origin) = enc(witness_point)` re-verifying origin-membership in the region
    /// by kernel computation over injectively-encoded points. Per borrow-check-REJECTED
    /// function each family emits one deliberately-unprovable sentinel (`1 <= 0`) so a
    /// rejected program can never grade Certified downstream. This is the
    /// Trusted→Certified thread of the real obligation stream — unlike
    /// `ownership_obligations`, whose predicates are opaque.
    pub concrete_obligations: Vec<(String, LeanExpr)>,
    /// Summary statistics.
    pub stats: BundleStats,
}

#[derive(Debug, Clone)]
pub struct TranslatedFunctionTypes {
    pub params: Vec<(String, LeanExpr)>,
    pub return_type: LeanExpr,
}

#[derive(Debug, Clone)]
pub struct AliasingObservation {
    /// Whether the runtime aliasing checks affirmatively passed.
    ///
    /// SOUNDNESS (hole 4): this is `true` only when the checks *actually ran*
    /// over reachable code and observed no violation. A program that executes
    /// nothing (no `main` entry point) leaves `ran=false` and `passed=false`:
    /// "nothing executed" is non-committal, never an affirmative pass.
    pub passed: bool,
    /// Whether the aliasing checks executed over reachable code at all. When
    /// `false`, the runtime channel is non-committal and the static NLL
    /// obligations must carry the verdict (fail-closed).
    pub ran: bool,
    pub summary: String,
    pub translated_value: Option<LeanExpr>,
}

pub(crate) fn build_for_program(
    program: &SourceProgram,
) -> Result<RustProofBundle, VirLoweringError> {
    // Delegate to ProofBundleBuilder for the full pipeline.
    crate::proof_bundle_builder::ProofBundleBuilder::new().from_source(program)
}

/// Exposed for `ProofBundleBuilder` to reuse without duplication.
pub(crate) fn observe_aliasing_for_builder(program: &SourceProgram) -> AliasingObservation {
    observe_aliasing(program)
}

/// True if the program has an executable entry point (`main`). Without one,
/// `run_with_aliasing_checks` evaluates nothing and returns a vacuous
/// `Value::Unit`, which must not be read as an affirmative aliasing pass.
fn program_has_entry_point(program: &SourceProgram) -> bool {
    program
        .items()
        .iter()
        .any(|item| matches!(item, crate::item::Item::Fn { name, .. } if name == "main"))
}

fn observe_aliasing(program: &SourceProgram) -> AliasingObservation {
    // SOUNDNESS (hole 4): a library-style program with no `main` executes
    // nothing, so the interpreter returns a vacuous `Value::Unit`. That is NOT
    // evidence the aliasing discipline holds — a genuine stacked-borrows
    // violation in an unreached function would go unobserved. Report the
    // runtime channel as non-committal (`ran=false`, `passed=false`) so the
    // static NLL obligations carry the verdict, fail-closed.
    if !program_has_entry_point(program) {
        return AliasingObservation {
            passed: false,
            ran: false,
            summary: "aliasing checks did not run: no `main` entry point (non-committal)"
                .to_string(),
            translated_value: None,
        };
    }

    let ctx = TranslationContext::new();
    match program.run_with_aliasing_checks() {
        EvalResult::Value(value) | EvalResult::Return(value) => AliasingObservation {
            passed: true,
            ran: true,
            summary: "aliasing checks passed".to_string(),
            translated_value: Some(translate_value(&value, &ctx)),
        },
        EvalResult::Panic(message) => AliasingObservation {
            passed: false,
            ran: true,
            summary: format!("aliasing checks panicked: {message}"),
            translated_value: None,
        },
        EvalResult::Error(message) => AliasingObservation {
            passed: false,
            ran: true,
            summary: format!("aliasing checks failed: {message}"),
            translated_value: None,
        },
        EvalResult::Break { label, .. } => AliasingObservation {
            passed: false,
            ran: true,
            summary: format!("aliasing checks ended with break: {label:?}"),
            translated_value: None,
        },
        EvalResult::Continue { label } => AliasingObservation {
            passed: false,
            ran: true,
            summary: format!("aliasing checks ended with continue: {label:?}"),
            translated_value: None,
        },
    }
}
