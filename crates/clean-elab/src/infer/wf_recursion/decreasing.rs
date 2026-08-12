// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decreasing proof generation for well-founded recursion.
//!
//! When a recursive function is defined with `termination_by`, each
//! recursive call site generates a proof obligation:
//!   `measure(rec_arg) < measure(current_arg)`
//!
//! This module handles three strategies for discharging these obligations:
//!
//! 1. **`decreasing_by` tactic**: User provides an explicit tactic to prove
//!    all decreasing obligations. The tactic is run on each goal.
//!
//! 2. **Default tactic cascade**: When no `decreasing_by` is specified, try
//!    `simp_arith` then `mathverse` as automatic proof strategies.
//!
//! 3. **Unsolved fallback**: If both the default cascade and user tactic fail,
//!    leave an unresolved proof metavariable for later validation.
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/Fix.lean`
//!            (mkDecreasingProof, solveDecreasingGoals)

use clean_kernel::name::Name;
use clean_kernel::Expr;
use clean_parser::SurfaceTactic;

use super::ElabCtx;
use crate::ElabError;

/// The strategy used to discharge a decreasing proof obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DecreasingStrategy {
    /// User-provided `decreasing_by` tactic succeeded.
    UserTactic,
    /// Default `simp_arith` succeeded.
    SimpArith,
    /// Default `mathverse` succeeded.
    Mathverse,
    /// All strategies failed; an unresolved proof metavariable was inserted.
    Sorry,
}

/// Result of attempting to build a decreasing proof.
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct DecreasingProof {
    /// The proof term of type `measure(arg') < measure(arg)`.
    pub(crate) proof: Expr,
    /// Which strategy produced this proof.
    pub(crate) strategy: DecreasingStrategy,
}

/// A proof obligation for a single recursive call site.
#[derive(Debug, Clone)]
pub(crate) struct DecreasingObligation {
    /// The goal type: `rel rec_arg current_arg` (typically `measure(x') < measure(x)`).
    pub(crate) goal_type: Expr,
    /// The recursive argument expression at this call site.
    pub(crate) rec_arg: Expr,
    /// The current argument being decreased.
    pub(crate) current_arg: Expr,
}

impl DecreasingObligation {
    /// Create a new decreasing obligation.
    pub(crate) fn new(goal_type: Expr, rec_arg: Expr, current_arg: Expr) -> Self {
        Self {
            goal_type,
            rec_arg,
            current_arg,
        }
    }
}

/// Build the decreasing proof goal type for a Nat-valued measure.
///
/// Given `measure : α → Nat`, `rec_arg : α`, `current_arg : α`, produces:
///   `Nat.lt (measure rec_arg) (measure current_arg)`
/// which is:
///   `LT.lt.{0} Nat instLTNat (measure rec_arg) (measure current_arg)`
pub(crate) fn build_nat_decreasing_goal(
    measure_fn: &Expr,
    rec_arg: &Expr,
    current_arg: &Expr,
) -> Expr {
    let measure_rec = Expr::app(measure_fn.clone(), rec_arg.clone());
    let measure_cur = Expr::app(measure_fn.clone(), current_arg.clone());

    // Nat.lt a b is definitionally: @LT.lt Nat instLTNat a b
    // But we can use the simpler encoding via the `<` notation
    let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    Expr::app(Expr::app(nat_lt, measure_rec), measure_cur)
}

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
impl<'a> ElabCtx<'a> {
    /// Discharge a decreasing proof obligation, trying multiple strategies.
    ///
    /// 1. If `decreasing_tactic` is provided, run it on the goal.
    /// 2. Otherwise, try the default cascade: `simp_arith`, then `mathverse`.
    /// 3. If all else fails, produce a `sorry` term.
    pub(crate) fn solve_decreasing_obligation(
        &mut self,
        obligation: &DecreasingObligation,
        decreasing_tactic: Option<&[SurfaceTactic]>,
    ) -> DecreasingProof {
        // Strategy 1: User-provided decreasing_by tactic
        if let Some(tactics) = decreasing_tactic {
            if let Ok(proof) = self.try_tactic_on_goal(&obligation.goal_type, tactics) {
                return DecreasingProof {
                    proof,
                    strategy: DecreasingStrategy::UserTactic,
                };
            }
        }

        // Strategy 2: Default simp_arith
        let simp_arith_tac = vec![SurfaceTactic::Named {
            span: clean_parser::Span::dummy(),
            name: "simp_arith".to_owned(),
            args: vec![],
        }];
        if let Ok(proof) = self.try_tactic_on_goal(&obligation.goal_type, &simp_arith_tac) {
            return DecreasingProof {
                proof,
                strategy: DecreasingStrategy::SimpArith,
            };
        }

        // Strategy 3: Default mathverse
        let mathverse_tac = vec![SurfaceTactic::Named {
            span: clean_parser::Span::dummy(),
            name: "mathverse".to_owned(),
            args: vec![],
        }];
        if let Ok(proof) = self.try_tactic_on_goal(&obligation.goal_type, &mathverse_tac) {
            return DecreasingProof {
                proof,
                strategy: DecreasingStrategy::Mathverse,
            };
        }

        // Fallback: leave the obligation as an unresolved metavariable rather
        // than manufacturing an unchecked proof term.
        let proof = self.fresh_meta(obligation.goal_type.clone());
        DecreasingProof {
            proof,
            strategy: DecreasingStrategy::Sorry,
        }
    }

    /// Try to prove a goal using the given tactics.
    ///
    /// Creates a temporary proof state and attempts to close the goal.
    /// Returns `Ok(proof_term)` on success, `Err` on failure.
    fn try_tactic_on_goal(
        &mut self,
        goal_type: &Expr,
        tactics: &[SurfaceTactic],
    ) -> Result<Expr, ElabError> {
        use crate::tactic::ProofState;

        let elab_locals: Vec<_> = self
            .locals
            .iter()
            .map(|(name, fvar, ty)| crate::tactic::LocalDecl {
                fvar: *fvar,
                name: name.clone(),
                ty: ty.clone(),
                value: None,
            })
            .collect();
        let mut ps = ProofState::with_instances_and_elab_context(
            self.env.clone(),
            goal_type.clone(),
            self.instances.clone(),
            elab_locals,
        );

        for tac in tactics {
            self.eval_tactic(&mut ps, tac)?;
        }

        ps.closed_proof().ok_or_else(|| ElabError::Unsupported {
            feature: "decreasing proof: tactic did not close goal".to_owned(),
        })
    }

    /// Build decreasing proofs for all recursive call sites in a function body.
    ///
    /// Scans the transformed body for sorry placeholders and attempts to
    /// replace them with actual proofs using the specified strategy.
    ///
    /// This is called after `transform_rec_calls` which inserts sorry terms
    /// as placeholders for decreasing proof obligations.
    pub(crate) fn solve_all_decreasing_obligations(
        &mut self,
        body: &Expr,
        _measure_fn: &Expr,
        _current_arg: &Expr,
        _decreasing_tactic: Option<&[SurfaceTactic]>,
    ) -> (Expr, Vec<DecreasingStrategy>) {
        // For now, the sorry-based approach from transform_rec_calls is retained.
        // When we detect sorry terms that serve as decreasing proofs, we attempt
        // to replace them. In the current architecture, sorry terms are inserted
        // directly by the rec call replacement and are not easily distinguishable
        // from other sorry terms.
        //
        // A more refined implementation would:
        // 1. During rec call replacement, tag each sorry with metadata
        // 2. Walk the body and collect all tagged sorry terms
        // 3. For each, build the obligation and try to solve it
        //
        // For now, we report that sorry was used for all obligations.
        (body.clone(), vec![DecreasingStrategy::Sorry])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_nat_decreasing_goal() {
        let measure = Expr::const_str("myMeasure");
        let rec_arg = Expr::const_str("smaller_x");
        let current_arg = Expr::const_str("x");

        let goal = build_nat_decreasing_goal(&measure, &rec_arg, &current_arg);

        // Should produce: Nat.lt (myMeasure smaller_x) (myMeasure x)
        let expected_lhs = Expr::app(Expr::const_str("myMeasure"), Expr::const_str("smaller_x"));
        let expected_rhs = Expr::app(Expr::const_str("myMeasure"), Expr::const_str("x"));
        let expected = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.lt"), vec![]),
                expected_lhs,
            ),
            expected_rhs,
        );
        assert_eq!(format!("{goal:?}"), format!("{expected:?}"));
    }

    #[test]
    fn test_decreasing_obligation_creation() {
        let goal = Expr::const_str("SomeGoal");
        let rec_arg = Expr::const_str("n_minus_1");
        let cur_arg = Expr::const_str("n");
        let ob = DecreasingObligation::new(goal.clone(), rec_arg.clone(), cur_arg.clone());
        assert_eq!(format!("{:?}", ob.goal_type), format!("{goal:?}"));
        assert_eq!(format!("{:?}", ob.rec_arg), format!("{rec_arg:?}"));
        assert_eq!(format!("{:?}", ob.current_arg), format!("{cur_arg:?}"));
    }

    #[test]
    fn test_decreasing_strategy_variants() {
        assert_ne!(DecreasingStrategy::UserTactic, DecreasingStrategy::Sorry);
        assert_eq!(DecreasingStrategy::Mathverse, DecreasingStrategy::Mathverse);
    }
}
