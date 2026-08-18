// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decreasing proof generation for well-founded recursion.
//!
//! When a recursive function is defined with `termination_by`, each
//! recursive call site generates a proof obligation:
//!   `measure(rec_arg) < measure(current_arg)`
//!
//! The PRODUCTION entry point is [`ElabCtx::discharge_decreasing_goal`]
//! (first production caller wired 2026-08-10, WF phase 1): a fail-closed
//! cascade — hypothesis lookup → `Nat.sub_lt` → `omega` → `simp_arith` —
//! where every candidate is strictly re-checked (`infer_type_full` + def-eq
//! against the goal, sorry refused) before it is accepted, and failure
//! returns `None` so the caller rejects the definition loudly. It NEVER
//! falls back to `sorry` or a metavariable.
//!
//! The older `solve_decreasing_obligation` scaffold (user `decreasing_by` →
//! `simp_arith` → `mathverse` → unresolved metavariable) remains staged and
//! unit-tested but has no production caller — its metavariable fallback is
//! exactly what the fail-closed contract forbids.
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/Fix.lean`
//!            (mkDecreasingProof, solveDecreasingGoals)

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId};
use clean_parser::SurfaceTactic;

use super::ElabCtx;
use crate::ElabError;

impl ElabCtx<'_> {
    /// Discharge a decreasing obligation `Nat.lt (measure arg) (measure param)`
    /// against the CURRENT local context (which includes every hypothesis the
    /// call-site traversal has opened, e.g. a `dite` branch's `h : 0 < n`).
    ///
    /// Cascade (first hit wins):
    /// 1. a hypothesis whose type is already def-eq to the goal;
    /// 2. `Nat.sub_lt` — the canonical `n - k < n` shape, keyed on a
    ///    positivity hypothesis in scope;
    /// 3. tactics: `omega`, then `simp_arith`.
    ///
    /// SOUNDNESS: every candidate — including tactic-produced terms — is
    /// re-checked with STRICT kernel inference (`infer_type_full`, the same
    /// standard `Environment::add_decl` applies) before being accepted, and
    /// sorry-carrying terms are refused. `None` means "not discharged": the
    /// caller fails closed; this function never fabricates a proof.
    pub(super) fn discharge_decreasing_goal(&mut self, goal: &Expr) -> Option<Expr> {
        let locals: Vec<(String, FVarId, Expr)> = self.locals.clone();

        // Tier 1: a hypothesis already proves the goal.
        for (_, fvar, ty) in &locals {
            if self.is_def_eq(ty, goal) {
                return Some(Expr::fvar(*fvar));
            }
        }

        // Tier 2: `Nat.sub_lt B k h hk` for the `B - k < B` family.
        if let Some(proof) = self.try_nat_sub_lt_discharge(goal, &locals) {
            return Some(proof);
        }

        // Tier 3: tactic cascade.
        for tactic in ["omega", "simp_arith"] {
            let tacs = [SurfaceTactic::Named {
                span: clean_parser::Span::dummy(),
                name: tactic.to_owned(),
                args: vec![],
            }];
            if let Ok(proof) = self.try_tactic_on_goal(goal, &tacs) {
                if self.recheck_decreasing_proof(&proof, goal) {
                    return Some(proof);
                }
            }
        }

        None
    }

    /// Try `Nat.sub_lt B (succ (k-1)) h (Nat.zero_lt_succ (k-1))` for small
    /// literal `k` and every hypothesis `h` in scope. Wrong candidates are
    /// weeded out by the strict recheck (a hypothesis that is not a
    /// `0 < B` proof simply fails inference), so this needs no syntactic
    /// hypothesis matching — definitional equality does the work, including
    /// unfolding `HSub.hSub`/`OfNat` sugar in the goal.
    fn try_nat_sub_lt_discharge(
        &mut self,
        goal: &Expr,
        locals: &[(String, FVarId, Expr)],
    ) -> Option<Expr> {
        // The caller constructs the goal as `Nat.lt <m arg> <m param>`;
        // extract the right-hand side `B := m param`.
        let ExprKind::App(lhs_fn, rhs) = goal.kind() else {
            return None;
        };
        let ExprKind::App(head, _) = lhs_fn.kind() else {
            return None;
        };
        let nat_lt_name = Name::from_string("Nat.lt");
        match head.kind() {
            ExprKind::Const(n, _) if *n == nat_lt_name => {}
            _ => return None,
        }
        let sub_lt_name = Name::from_string("Nat.sub_lt");
        let zls_name = Name::from_string("Nat.zero_lt_succ");
        if self.env.get_const(&sub_lt_name).is_none() || self.env.get_const(&zls_name).is_none() {
            return None;
        }
        let sub_lt = Expr::const_(sub_lt_name, vec![]);
        let zls = Expr::const_(zls_name, vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let b = Expr::clone(rhs);
        for (_, fvar, _) in locals {
            for k in 1..=4u64 {
                let k_expr = Expr::app(succ.clone(), Expr::nat_lit(k - 1));
                let k_pos = Expr::app(zls.clone(), Expr::nat_lit(k - 1));
                let candidate = Expr::apps(
                    sub_lt.clone(),
                    [b.clone(), k_expr, Expr::fvar(*fvar), k_pos],
                );
                if self.recheck_decreasing_proof(&candidate, goal) {
                    return Some(candidate);
                }
            }
        }
        None
    }

    /// Strict validation of a decreasing-proof candidate: no sorry, and the
    /// STRICTLY-inferred type (App arguments checked) is def-eq to the goal.
    /// Terms with unsolved metavariables fail inference (a meta instantiates
    /// to an unknown fvar) and are therefore refused too.
    fn recheck_decreasing_proof(&self, proof: &Expr, goal: &Expr) -> bool {
        if proof.has_sorry() {
            return false;
        }
        match self.infer_type_full(proof) {
            Ok(ty) => self.is_def_eq(&ty, goal),
            Err(_) => false,
        }
    }
}

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
    // Staged Lean4-parity scaffold, exercised by unit tests only; the live
    // pipeline reads only `goal_type` until the phase-2 proof builder lands.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) rec_arg: Expr,
    /// The current argument being decreased.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) current_arg: Expr,
}

impl DecreasingObligation {
    /// Create a new decreasing obligation.
    // Staged Lean4-parity scaffold, exercised by unit tests only; the live
    // pipeline builds its obligation goals inline in `call_sites`.
    #[cfg_attr(not(test), allow(dead_code))]
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
// Staged Lean4-parity scaffold, exercised by unit tests only; the live
// pipeline builds its obligation goals inline in `call_sites`.
#[cfg_attr(not(test), allow(dead_code))]
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
