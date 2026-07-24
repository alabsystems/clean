// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof bundle builder: orchestrates lowering, NLL, and obligation extraction
//! into a single Lean-facing proof bundle.
//!
//! The builder wires parsed Rust source through the VIR lowering pipeline,
//! runs NLL borrow checking, extracts ownership obligations from borrow-check
//! results, and translates everything into clean kernel terms.

use crate::nll::{NllError, NllResult};
use crate::ownership::Place;
use crate::proof_bundle::{AliasingObservation, RustProofBundle, TranslatedFunctionTypes};
use crate::proof_obligations::ObligationCollector;
use crate::source::SourceProgram;
use crate::translate::{
    mk_aliasing_clean_goal, mk_give_back_refinement_goal, mk_move_clear_goal,
    mk_mut_borrow_exclusive_goal, mk_shared_borrow_valid_goal, TranslationContext,
};
use crate::vir::BorrowKind;
use crate::vir_lowering::VirLoweringError;
use clean_kernel::Expr as LeanExpr;
use std::collections::BTreeMap;

/// An ownership proof obligation extracted from NLL borrow-check results.
///
/// Each obligation represents a property that must hold for the Rust program
/// to be ownership-safe. The `goal` field is the clean proposition to prove.
#[derive(Debug, Clone)]
pub struct OwnershipObligation {
    /// The function containing this obligation.
    pub function: String,
    /// High-level category.
    pub kind: OwnershipObligationKind,
    /// Human-readable description.
    pub description: String,
    /// The clean proposition to prove.
    pub goal: LeanExpr,
    /// Whether this obligation is satisfied (no NLL errors for this site).
    pub satisfied: bool,
    /// Source location, when known.
    pub location: Option<String>,
}

/// Ownership obligation taxonomy.
///
/// Each variant corresponds to a fundamental Rust ownership rule that must
/// hold for the program to be sound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum OwnershipObligationKind {
    /// `&T` borrow: the referent must be valid for the borrow's lifetime.
    SharedBorrowValid,
    /// `&mut T` borrow: exclusive access must be maintained.
    MutableBorrowExclusive,
    /// Move: no live borrows may exist when ownership is transferred.
    MoveWithoutLiveBorrows,
    /// Stacked/tree borrows aliasing: runtime aliasing checks passed.
    AliasingInvalidation,
    /// `&mut` give-back refinement: the give-back view `(f_fwd, f_back)` of a
    /// mutable borrow refines the value-at-address semantics. Stated here, but
    /// discharged only by a Clean refinement certificate (M3) — until then such
    /// an obligation is unsatisfied (`satisfied: false`). See
    /// [`give_back_refinement_obligation`].
    GiveBackRefinement,
    /// Arithmetic panic-freedom: a non-wrapping `Add`/`Sub`/`Mul` must not
    /// overflow, and `Div`/`Rem`/shift must have a valid divisor/shift amount.
    /// The verifier does not yet model integer bounds, so the obligation is
    /// emitted UNKNOWN (`satisfied: false`) — a fail-closed placeholder so an
    /// unchecked overflow is never reported as satisfied. See hole 1.
    ArithmeticSafety,
}

/// Summary statistics for a proof bundle.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BundleStats {
    pub shared_borrow_valid: usize,
    pub mutable_borrow_exclusive: usize,
    pub move_without_live_borrows: usize,
    pub aliasing_invalidation: usize,
    pub give_back_refinement: usize,
    pub arithmetic_safety: usize,
    pub total_satisfied: usize,
    pub total_violated: usize,
}

impl BundleStats {
    /// Compute stats from a slice of ownership obligations.
    #[must_use]
    pub fn from_obligations(obligations: &[OwnershipObligation]) -> Self {
        let mut stats = Self::default();
        for obligation in obligations {
            match obligation.kind {
                OwnershipObligationKind::SharedBorrowValid => stats.shared_borrow_valid += 1,
                OwnershipObligationKind::MutableBorrowExclusive => {
                    stats.mutable_borrow_exclusive += 1;
                }
                OwnershipObligationKind::MoveWithoutLiveBorrows => {
                    stats.move_without_live_borrows += 1;
                }
                OwnershipObligationKind::AliasingInvalidation => {
                    stats.aliasing_invalidation += 1;
                }
                OwnershipObligationKind::GiveBackRefinement => {
                    stats.give_back_refinement += 1;
                }
                OwnershipObligationKind::ArithmeticSafety => {
                    stats.arithmetic_safety += 1;
                }
            }
            if obligation.satisfied {
                stats.total_satisfied += 1;
            } else {
                stats.total_violated += 1;
            }
        }
        stats
    }

    /// Total obligation count.
    #[must_use]
    pub fn total(&self) -> usize {
        self.total_satisfied + self.total_violated
    }

    /// Whether all obligations are satisfied.
    #[must_use]
    pub fn all_satisfied(&self) -> bool {
        self.total_violated == 0
    }
}

/// Orchestrates VIR lowering, NLL analysis, and obligation extraction
/// into a complete proof bundle.
#[derive(Debug)]
pub struct ProofBundleBuilder {
    ctx: TranslationContext,
}

impl Default for ProofBundleBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofBundleBuilder {
    /// Create a new builder with a fresh translation context.
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: TranslationContext::new(),
        }
    }

    /// Build a complete proof bundle from parsed Rust source.
    ///
    /// This is the main entry point. It:
    /// 1. Lowers the source to VIR
    /// 2. Runs NLL borrow checking on each function
    /// 3. Extracts ownership obligations from NLL results
    /// 4. Runs aliasing checks (stacked borrows)
    /// 5. Translates types to clean terms
    pub fn from_source(&self, source: &SourceProgram) -> Result<RustProofBundle, VirLoweringError> {
        let lowered = source.lower_to_vir()?;
        let borrow_results = lowered.check_borrows();
        let vir_obligations = ObligationCollector::collect_program(&lowered);
        let ownership_obligations = self.extract_ownership_obligations(&borrow_results);
        let arithmetic_obligations = self.extract_arithmetic_obligations(&lowered);
        let translated_types = self.collect_translated_types(&lowered);
        let aliasing_observation = crate::proof_bundle::observe_aliasing_for_builder(source);
        let aliasing_obligation = self.aliasing_to_obligation(&aliasing_observation);

        let mut all_ownership = ownership_obligations;
        all_ownership.extend(arithmetic_obligations);
        if let Some(aliasing_obl) = aliasing_obligation {
            all_ownership.push(aliasing_obl);
        }

        let stats = BundleStats::from_obligations(&all_ownership);

        // The concrete (Certified-tier) thread of the stream: the NLL verdict reflected
        // as kernel-decidable goals, fail-closed on rejected functions. Two families:
        // liveness (1 <= |region|) and borrow-origin well-formedness (witness equality).
        let mut concrete_obligations =
            crate::concrete_liveness::concrete_borrow_liveness(&borrow_results);
        concrete_obligations.extend(crate::concrete_liveness::concrete_origin_wellformedness(
            &borrow_results,
        ));
        concrete_obligations.extend(crate::concrete_liveness::concrete_mut_exclusivity(
            &borrow_results,
        ));
        concrete_obligations.extend(crate::concrete_liveness::concrete_use_init(&lowered));

        Ok(RustProofBundle {
            lowered,
            borrow_results,
            obligations: vir_obligations,
            translated_types,
            aliasing_observation,
            ownership_obligations: all_ownership,
            concrete_obligations,
            stats,
        })
    }

    /// Extract ownership obligations from NLL borrow-check results.
    fn extract_ownership_obligations(
        &self,
        borrow_results: &BTreeMap<String, NllResult>,
    ) -> Vec<OwnershipObligation> {
        let mut obligations = Vec::new();

        for (function, result) in borrow_results {
            // Emit one obligation per borrow found
            for borrow in &result.borrows {
                let (kind, description, goal) = match borrow.kind {
                    BorrowKind::Shared => (
                        OwnershipObligationKind::SharedBorrowValid,
                        format!(
                            "shared borrow of `{:?}` must be valid",
                            borrow.borrowed_place
                        ),
                        mk_shared_borrow_valid_goal(&borrow.borrowed_place),
                    ),
                    BorrowKind::Mut { .. } => (
                        OwnershipObligationKind::MutableBorrowExclusive,
                        format!(
                            "mutable borrow of `{:?}` must have exclusive access",
                            borrow.borrowed_place
                        ),
                        mk_mut_borrow_exclusive_goal(&borrow.borrowed_place),
                    ),
                    BorrowKind::Shallow => continue,
                };

                let violated = result
                    .errors
                    .iter()
                    .any(|err| borrow_error_involves_place(err, &borrow.borrowed_place));

                obligations.push(OwnershipObligation {
                    function: function.clone(),
                    kind,
                    description,
                    goal,
                    satisfied: !violated,
                    location: Some(format!(
                        "{function}:bb{}:stmt{}",
                        borrow.origin.block, borrow.origin.statement_index
                    )),
                });
            }

            // Emit move-without-live-borrows obligations from NLL errors
            for error in &result.errors {
                if let NllError::MoveWhileBorrowed { place, .. } = error {
                    obligations.push(OwnershipObligation {
                        function: function.clone(),
                        kind: OwnershipObligationKind::MoveWithoutLiveBorrows,
                        description: format!("move of `{place:?}` while borrowed"),
                        goal: mk_move_clear_goal(place),
                        satisfied: false,
                        location: None,
                    });
                }
            }
        }

        obligations
    }

    /// Extract arithmetic panic-freedom obligations from lowered VIR.
    ///
    /// SOUNDNESS (hole 1): the interpreter wraps integer arithmetic silently
    /// (`wrapping_add`, …) and the collector emits no overflow/div-by-zero VC,
    /// so an overflowing `let z: u8 = 200 + 100` was reported fully satisfied.
    /// We now emit one UNKNOWN (`satisfied: false`) obligation per
    /// overflow-capable operation — non-wrapping `Add`/`Sub`/`Mul`,
    /// `Div`/`Rem` (nonzero divisor), and `Shl`/`Shr` (in-range shift). The
    /// verifier does not yet model integer bounds, so these remain undischarged
    /// (fail-closed: an unchecked overflow can never round-trip to
    /// `all_satisfied()`). Wrapping/`*Unchecked` and comparison/bitwise ops are
    /// not flagged.
    fn extract_arithmetic_obligations(
        &self,
        lowered: &crate::vir_lowering::LoweredProgram,
    ) -> Vec<OwnershipObligation> {
        use crate::translate::mk_arithmetic_safety_goal;
        use crate::vir::{BinOp, Rvalue, Stmt};

        fn op_requires_check(op: BinOp) -> Option<&'static str> {
            match op {
                BinOp::Add => Some("noOverflow(Add)"),
                BinOp::Sub => Some("noOverflow(Sub)"),
                BinOp::Mul => Some("noOverflow(Mul)"),
                BinOp::Div => Some("nonZeroDivisor(Div)"),
                BinOp::Rem => Some("nonZeroDivisor(Rem)"),
                BinOp::Shl => Some("shiftInRange(Shl)"),
                BinOp::Shr => Some("shiftInRange(Shr)"),
                // Comparisons, bitwise, wrapping/unchecked, and pointer offset
                // cannot panic on their integer inputs in the checked model.
                _ => None,
            }
        }

        let mut obligations = Vec::new();
        for (function, body) in &lowered.functions {
            for (block_idx, block) in body.blocks.iter().enumerate() {
                for (stmt_idx, stmt) in block.statements.iter().enumerate() {
                    let Stmt::Assign { rvalue, .. } = stmt else {
                        continue;
                    };
                    let op = match rvalue {
                        Rvalue::BinaryOp { op, .. } | Rvalue::CheckedBinaryOp { op, .. } => *op,
                        _ => continue,
                    };
                    let Some(check) = op_requires_check(op) else {
                        continue;
                    };
                    obligations.push(OwnershipObligation {
                        function: function.clone(),
                        kind: OwnershipObligationKind::ArithmeticSafety,
                        description: format!(
                            "arithmetic `{check}` at {function}:bb{block_idx}:stmt{stmt_idx} \
                             (UNKNOWN: integer bounds not yet modeled)"
                        ),
                        goal: mk_arithmetic_safety_goal(check),
                        satisfied: false,
                        location: Some(format!("{function}:bb{block_idx}:stmt{stmt_idx}")),
                    });
                }
            }
        }
        obligations
    }

    /// Convert aliasing observation into an ownership obligation.
    fn aliasing_to_obligation(
        &self,
        observation: &AliasingObservation,
    ) -> Option<OwnershipObligation> {
        Some(OwnershipObligation {
            function: "<program>".to_string(),
            kind: OwnershipObligationKind::AliasingInvalidation,
            description: observation.summary.clone(),
            goal: mk_aliasing_clean_goal(&observation.summary),
            satisfied: observation.passed,
            location: None,
        })
    }

    /// Translate function types from the lowered program.
    fn collect_translated_types(
        &self,
        lowered: &crate::vir_lowering::LoweredProgram,
    ) -> BTreeMap<String, TranslatedFunctionTypes> {
        use crate::translate::translate_type;

        lowered
            .functions
            .iter()
            .map(|(name, body)| {
                let params = body
                    .locals
                    .iter()
                    .enumerate()
                    .skip(1)
                    .take(body.arg_count as usize)
                    .map(|(idx, local)| {
                        let param_name = local.name.clone().unwrap_or_else(|| format!("_{idx}"));
                        (param_name, translate_type(&local.ty, &self.ctx))
                    })
                    .collect();
                let return_type = body
                    .locals
                    .first()
                    .map(|local| translate_type(&local.ty, &self.ctx))
                    .unwrap_or_else(|| translate_type(&crate::types::RustType::Unit, &self.ctx));
                (
                    name.clone(),
                    TranslatedFunctionTypes {
                        params,
                        return_type,
                    },
                )
            })
            .collect()
    }
}

/// Check whether an NLL error involves a specific place.
fn borrow_error_involves_place(error: &NllError, place: &Place) -> bool {
    match error {
        NllError::UseWhileBorrowed { borrowed, .. }
        | NllError::ConflictingBorrow { borrowed, .. }
        | NllError::AssignWhileBorrowed { borrowed, .. }
        | NllError::MoveWhileBorrowed { borrowed, .. }
        | NllError::BorrowEscapesReferent { borrowed, .. } => borrowed == place,
    }
}

/// Build a give-back refinement obligation for a `&mut` borrow at `place`.
///
/// The returned obligation is **always `satisfied: false` (Pending)**: this
/// function *states* the give-back refinement (its `goal` is the
/// `mk_give_back_refinement_goal` proposition), but discharging it requires a
/// Clean refinement certificate against the value-at-address semantics (M3,
/// deferred — see `designs/2026-06-29-giveback-clean-refinement.md` §4). Mirrors
/// the trust-ir side's `GiveBackRefinement` obligation, which is likewise emitted
/// `Pending` and only becomes `Certified` once kernel-rechecked.
#[must_use]
pub fn give_back_refinement_obligation(function: &str, place: &Place) -> OwnershipObligation {
    OwnershipObligation {
        function: function.to_string(),
        kind: OwnershipObligationKind::GiveBackRefinement,
        description: format!(
            "give-back refinement for &mut `{place:?}`: (f_fwd, f_back) must refine \
             the value-at-address semantics (Pending until a Clean certificate discharges it)"
        ),
        goal: mk_give_back_refinement_goal(place),
        satisfied: false,
        location: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn give_back_obligation_is_pending_with_refinement_goal() {
        let place = Place::Local(0);
        let obl = give_back_refinement_obligation("f", &place);
        assert_eq!(obl.kind, OwnershipObligationKind::GiveBackRefinement);
        assert!(
            !obl.satisfied,
            "give-back refinement must be Pending until M3 discharges it"
        );
        assert_eq!(obl.function, "f");
        // The goal is exactly the schematic refinement proposition over the place.
        assert_eq!(obl.goal, mk_give_back_refinement_goal(&place));
    }

    #[test]
    fn bundle_stats_count_pending_give_back_as_violated() {
        let obls = vec![
            give_back_refinement_obligation("f", &Place::Local(0)),
            give_back_refinement_obligation("g", &Place::Local(1)),
        ];
        let stats = BundleStats::from_obligations(&obls);
        assert_eq!(stats.give_back_refinement, 2);
        assert_eq!(stats.total(), 2);
        assert_eq!(
            stats.total_violated, 2,
            "pending give-back obligations are unsatisfied"
        );
        assert_eq!(stats.total_satisfied, 0);
        assert!(!stats.all_satisfied());
    }
}
