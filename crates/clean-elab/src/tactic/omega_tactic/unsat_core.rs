// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The irreducible hypothesis core of a refuted mathverse system.
//!
//! When the equality / `≤` solver inside [`mathverse_check_certified`]
//! refutes a system, it flags EVERY hypothesis in the certificate: it does not
//! track which rows it combined. The hypothesis-only proof builders
//! (`build_linarith_proof`) read those flags as the set to chain or sum, so one
//! irrelevant hypothesis in scope breaks the reconstruction. Spelled
//! `rintro ⟨hlo, _⟩`, `TrustIr/Basic.lean`'s `validChar_of_lt_256` keeps
//! `v ≤ 0xDFFF` beside `hlo : 0xD800 ≤ v` and `h : v < 256` (the source's
//! `rintro ⟨hlo, -⟩` clears it); the three flagged hypotheses neither chain
//! nor sum to a contradiction, although the first two refute each other.
//!
//! [`hypothesis_unsat_core`] shrinks the flags with a one-pass deletion filter
//! that asks the same decision procedure: a hypothesis is dropped when the
//! system without it is still refuted by a linear (not modular) contradiction.
//! No single kept hypothesis could be dropped WHEN IT WAS TESTED. That is not
//! a minimality guarantee: "refuted linearly" need not be monotone (the solver
//! may report a parity contradiction on a superset whose subset it refutes
//! linearly), so a hypothesis kept early may become droppable after a later
//! deletion. The core only guides assembly; `close_goal` re-checks whatever
//! term is built from it, so an imperfect core costs completeness, never
//! soundness.

use super::{
    mathverse_check_certified, CertifiedMathverseConstraint, MathverseCertificate,
    MathverseCertifiedResult, MathverseContradictionType,
};

/// The most flagged hypotheses [`hypothesis_unsat_core`] filters. The
/// deletion filter re-runs the decision procedure once per flagged hypothesis,
/// on a path where the replay has already failed, so its cost is bounded here
/// rather than left linear in the size of the local context. Past the bound
/// the core is not computed and the caller falls through as before.
pub(super) const MAX_UNSAT_CORE_CANDIDATES: usize = 16;

/// The flagged hypotheses of `certificate` shrunk, by one deletion pass, to a
/// linearly refuted subset of `constraints` from which no hypothesis could be
/// dropped when it was tested; `None` when no flagged hypothesis could be
/// dropped or more than [`MAX_UNSAT_CORE_CANDIDATES`] are flagged.
///
/// Rows that carry no hypothesis coefficient — the negated goal, the implicit
/// `0 ≤ x` facts for Nat atoms — are always kept, so `uses_goal_negation` is
/// unchanged.
pub(super) fn hypothesis_unsat_core(
    certificate: &MathverseCertificate,
    constraints: &[CertifiedMathverseConstraint],
) -> Option<MathverseCertificate> {
    let mut kept: Vec<bool> = certificate.coefficients.iter().map(|&c| c != 0).collect();
    let flagged = kept.iter().filter(|&&k| k).count();
    if !(2..=MAX_UNSAT_CORE_CANDIDATES).contains(&flagged) {
        return None;
    }
    let mut dropped_any = false;
    let flagged_indices = certificate
        .coefficients
        .iter()
        .enumerate()
        .filter_map(|(i, &c)| (c != 0).then_some(i));
    for i in flagged_indices {
        kept[i] = false;
        let trial: Vec<CertifiedMathverseConstraint> = constraints
            .iter()
            .filter(|row| row_is_kept(row, &kept))
            .cloned()
            .collect();
        if refuted_linearly(&trial) {
            dropped_any = true;
        } else {
            kept[i] = true;
        }
    }
    if !dropped_any {
        return None;
    }
    let mut core = certificate.clone();
    for (coefficient, &k) in core.coefficients.iter_mut().zip(&kept) {
        if !k {
            *coefficient = 0;
        }
    }
    Some(core)
}

/// A row stays unless it comes from a dropped hypothesis.
fn row_is_kept(row: &CertifiedMathverseConstraint, kept: &[bool]) -> bool {
    row.certificate
        .coefficients
        .iter()
        .zip(kept)
        .all(|(&c, &k)| c == 0 || k)
}

/// `constraints` are refuted by an arithmetic contradiction — the kind the
/// hypothesis-only builders reconstruct — rather than a parity or
/// divisibility one.
fn refuted_linearly(constraints: &[CertifiedMathverseConstraint]) -> bool {
    matches!(
        mathverse_check_certified(constraints),
        MathverseCertifiedResult::Unsat(MathverseCertificate {
            contradiction_type: MathverseContradictionType::Arithmetic
                | MathverseContradictionType::LinearCombination,
            ..
        })
    )
}

#[cfg(test)]
mod tests {
    use super::super::OmegaConstraint;
    use super::*;
    use crate::tactic::arithmetic::LinearExpr;
    use crate::tactic::{Goal, ProofState};
    use clean_kernel::{Expr, FVarId};

    /// `x ≤ k` as the row `x - k ≤ 0` from hypothesis `idx` of `n`.
    fn le(idx: usize, n: usize, k: i64) -> CertifiedMathverseConstraint {
        let mut e = LinearExpr::var(0);
        e.constant = -k;
        CertifiedMathverseConstraint::from_hypothesis(OmegaConstraint::Le(e), idx, n)
    }

    /// `k ≤ x` as the row `k - x ≤ 0` from hypothesis `idx` of `n`.
    fn ge(idx: usize, n: usize, k: i64) -> CertifiedMathverseConstraint {
        let mut e = LinearExpr::var(0).scale(-1);
        e.constant = k;
        CertifiedMathverseConstraint::from_hypothesis(OmegaConstraint::Le(e), idx, n)
    }

    fn flags(coefficients: &[i128]) -> MathverseCertificate {
        let mut cert = MathverseCertificate::new(coefficients.len());
        cert.coefficients = coefficients.to_vec();
        cert
    }

    #[test]
    fn test_hypothesis_unsat_core_drops_the_irrelevant_bound() {
        // x ≤ 3, 5 ≤ x, x ≤ 100: the solver flags all three; {0, 1} refutes.
        let rows = [le(0, 3, 3), ge(1, 3, 5), le(2, 3, 100)];
        assert!(matches!(
            mathverse_check_certified(&rows),
            MathverseCertifiedResult::Unsat(_)
        ));
        let core = hypothesis_unsat_core(&flags(&[1, 1, 1]), &rows)
            .expect("the bound x ≤ 100 is not needed to refute x ≤ 3, 5 ≤ x");
        assert_eq!(core.coefficients, vec![1, 1, 0]);
    }

    #[test]
    fn test_hypothesis_unsat_core_of_an_irreducible_set_is_none() {
        // x ≤ 3, 5 ≤ x: dropping either leaves a satisfiable system.
        let rows = [le(0, 2, 3), ge(1, 2, 5)];
        assert!(hypothesis_unsat_core(&flags(&[1, 1]), &rows).is_none());
    }

    #[test]
    fn test_hypothesis_unsat_core_past_the_candidate_bound_is_none() {
        // x ≤ 3, 5 ≤ x and MAX_UNSAT_CORE_CANDIDATES - 1 irrelevant bounds:
        // one flag too many, so the filter does not run.
        let n = MAX_UNSAT_CORE_CANDIDATES + 1;
        let mut rows = vec![le(0, n, 3), ge(1, n, 5)];
        rows.extend((2..n).map(|i| le(i, n, 100)));
        assert!(hypothesis_unsat_core(&flags(&vec![1; n]), &rows).is_none());
        // At the bound it runs and keeps exactly the refuting pair.
        let n = MAX_UNSAT_CORE_CANDIDATES;
        let mut rows = vec![le(0, n, 3), ge(1, n, 5)];
        rows.extend((2..n).map(|i| le(i, n, 100)));
        let core = hypothesis_unsat_core(&flags(&vec![1; n]), &rows)
            .expect("at the bound the deletion filter runs");
        let mut expected = vec![0; n];
        expected[0] = 1;
        expected[1] = 1;
        assert_eq!(core.coefficients, expected);
    }

    /// `v : Nat`, `h : v < 256`, `hlo : 0xD800 ≤ v`, `hhi : v ≤ 0xDFFF` ⊢
    /// `False` (`validChar_of_lt_256` with the `-` pattern respelled `_`).
    fn surrogate_state() -> (ProofState, Goal) {
        use crate::tactic::tc_app::{nat_le_tc, nat_lt_tc};
        use crate::tactic::LocalDecl;
        use clean_kernel::env::Environment;
        use clean_kernel::Name;

        let v = Expr::fvar(FVarId::new(0));
        let decl = |i: u64, name: &str, ty: Expr| LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(i),
            name: clean_parser::SurfaceName::generated_path(name),
            ty,
            value: None,
        };
        let state = ProofState::with_context(
            Environment::with_prelude(),
            Expr::const_(Name::from_string("False"), vec![]),
            vec![
                decl(0, "v", Expr::const_(Name::from_string("Nat"), vec![])),
                decl(1, "h", nat_lt_tc(v.clone(), Expr::nat_lit(256))),
                decl(2, "hlo", nat_le_tc(Expr::nat_lit(0xD800), v.clone())),
                decl(3, "hhi", nat_le_tc(v, Expr::nat_lit(0xDFFF))),
            ],
        );
        let goal = state.current_goal().expect("one goal").clone();
        (state, goal)
    }

    /// The replay the core exists for: on the certificate that flags all three
    /// hypotheses, `replay_hypothesis_proof` builds no term the kernel takes
    /// (they neither chain nor sum to a contradiction); on
    /// `hypothesis_unsat_core`'s `{h, hlo}` it closes the goal.
    #[test]
    fn test_replay_fails_on_all_flags_and_closes_on_the_core() {
        let (mut state, goal) = surrogate_state();
        let (rows, fvars) = super::super::extract_certified_mathverse_constraints(&state, &goal)
            .expect("the three bounds parse");
        assert_eq!(fvars.len(), 3, "h, hlo and hhi are the parsed hypotheses");
        let MathverseCertifiedResult::Unsat(refutation) = mathverse_check_certified(&rows) else {
            panic!("0xD800 ≤ v < 256 is refuted");
        };
        let mut all_flags = refutation;
        all_flags.coefficients = vec![1; fvars.len()];

        assert!(
            super::super::replay_hypothesis_proof(&mut state, &goal, &all_flags, &fvars).is_err(),
            "the all-flags replay must not close the goal"
        );
        assert!(!state.is_complete());

        let core = hypothesis_unsat_core(&all_flags, &rows).expect("hhi is not needed");
        assert_eq!(core.coefficients, vec![1, 1, 0]);
        let (mut state, goal) = surrogate_state();
        super::super::replay_hypothesis_proof(&mut state, &goal, &core, &fvars)
            .expect("the core replay closes the goal");
        assert!(state.is_complete());
    }

    #[test]
    fn test_hypothesis_unsat_core_of_a_satisfiable_set_drops_nothing() {
        // x ≤ 5, 5 ≤ x, x ≤ 100 is satisfied by x = 5: no subset is refuted,
        // so even a (wrong) all-flags certificate yields no core.
        let rows = [le(0, 3, 5), ge(1, 3, 5), le(2, 3, 100)];
        assert!(hypothesis_unsat_core(&flags(&[1, 1, 1]), &rows).is_none());
    }
}
