// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `auto_cascade` tactic: sequentially tries all available decision procedures.
//!
//! Tries each tactic in a fixed priority order, returning the first success.
//! On failure, state is fully restored before the next attempt. The cascade
//! order is chosen to run cheap/fast tactics first:
//!
//! 1. `decide` — SMT decision procedure (propositional + equality)
//! 2. `simp` — simplification
//! 3. `cert_mathverse` — certificate normalization plus linear integer arithmetic
//! 4. `mathverse` — linear integer arithmetic
//! 5. `linarith` — linear arithmetic over ordered fields
//! 6. `norm_num` — numeric normalization
//! 7. `ring` — ring equalities
//! 8. `nlinarith` — nonlinear arithmetic
//! 9. `aesop` — proof search
//! 10. `positivity` — positivity goals
//! 11. `field_simp` — field simplification
//! 12. `polyrith` — polynomial arithmetic
//! 13. `tauto` — propositional tautologies

use super::combinator::try_tactic_preserving_state;
use super::core::{ProofState, TacticError, TacticResult};

/// Result of a successful `auto_cascade` invocation, recording which
/// sub-tactic closed the goal.
#[derive(Debug, Clone, PartialEq, Eq)]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct CascadeResult {
    /// Name of the sub-tactic that succeeded.
    pub(crate) winner: &'static str,
}

/// The ordered list of sub-tactics to try.
/// Each entry is `(name, function pointer)`.
const CASCADE_TACTICS: &[(&str, fn(&mut ProofState) -> TacticResult)] = &[
    ("decide", super::decide),
    ("simp", super::simp_default),
    ("cert_mathverse", super::cert_mathverse),
    ("omega", super::omega),
    ("linarith", super::linarith),
    ("norm_num", super::norm_num),
    ("ring", super::ring),
    ("nlinarith", super::nlinarith),
    ("aesop", super::aesop),
    ("positivity", super::positivity),
    ("field_simp", super::field_simp),
    ("polyrith", super::polyrith),
    ("tauto", super::tauto),
];

/// Try all decision procedures in sequence, returning the first success.
///
/// Each sub-tactic is run with full state preservation — on failure the
/// proof state is rolled back before trying the next tactic.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok`, the current goal is closed by exactly one sub-tactic.
/// ENSURES: On `Err`, no sub-tactic succeeded; state is unchanged from pre-call.
/// ENSURES: Trust level of the proof term equals that of the winning sub-tactic.
pub fn auto_cascade(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    for &(name, tactic_fn) in CASCADE_TACTICS {
        if try_tactic_preserving_state(state, tactic_fn) {
            tracing::debug!(tactic = "auto_cascade", winner = name, "cascade succeeded");
            return Ok(());
        }
    }

    Err(TacticError::AllTacticsFailed {
        combinator: "auto_cascade".into(),
    })
}

/// Run the cascade and return which tactic succeeded (for programmatic use).
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: Same as `auto_cascade`, plus returns the winner name on success.
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn auto_cascade_with_info(state: &mut ProofState) -> Result<CascadeResult, TacticError> {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    for &(name, tactic_fn) in CASCADE_TACTICS {
        if try_tactic_preserving_state(state, tactic_fn) {
            tracing::debug!(tactic = "auto_cascade", winner = name, "cascade succeeded");
            return Ok(CascadeResult { winner: name });
        }
    }

    Err(TacticError::AllTacticsFailed {
        combinator: "auto_cascade".into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tactic::ProofState;
    use clean_kernel::{env::Declaration, Environment, Expr, FVarId, Level, Name};

    /// Helper: build a proof state with a single goal targeting `ty`.
    fn ps_with_goal(ty: Expr) -> ProofState {
        let env = Environment::new();
        ProofState::new(env, ty)
    }

    #[test]
    fn test_auto_cascade_no_goals_returns_error() {
        let dummy = Expr::const_str("Prop");
        let mut ps = ps_with_goal(dummy);
        // Remove the goal to simulate empty state
        ps.goals.clear();
        let result = auto_cascade(&mut ps);
        assert!(result.is_err());
        match result.unwrap_err() {
            TacticError::NoGoals => {}
            other => panic!("expected NoGoals, got: {other:?}"),
        }
    }

    #[test]
    fn test_auto_cascade_true_succeeds() {
        // Goal: True (should be closable by simp or decide)
        let true_expr = Expr::const_str("True");
        let mut ps = ps_with_goal(true_expr);
        let result = auto_cascade(&mut ps);
        assert!(
            result.is_ok(),
            "auto_cascade should close `True`: {result:?}"
        );
        assert!(ps.goals.is_empty(), "goal should be closed");
    }

    #[test]
    fn test_auto_cascade_prop_eq_refl() {
        // Goal: @Eq Prop True True — uses only Prop-level types, no Nat prelude needed
        let prop = Expr::sort(Level::zero());
        let true_c = Expr::const_str("True");
        let eq_expr = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                    prop,
                ),
                true_c.clone(),
            ),
            true_c,
        );
        let mut ps = ps_with_goal(eq_expr);
        let result = auto_cascade(&mut ps);
        // Should succeed via decide (reflexivity on identical terms)
        assert!(
            result.is_ok(),
            "auto_cascade should close `True = True`: {result:?}"
        );
    }

    #[test]
    fn test_auto_cascade_unsolvable_fails_cleanly() {
        // Goal: False — no tactic should close this
        let false_expr = Expr::const_str("False");
        let mut ps = ps_with_goal(false_expr);
        let goal_count_before = ps.goals.len();
        let result = auto_cascade(&mut ps);
        assert!(result.is_err(), "auto_cascade should not close `False`");
        assert_eq!(
            ps.goals.len(),
            goal_count_before,
            "state should be unchanged after failure"
        );
    }

    #[test]
    fn test_auto_cascade_with_info_returns_winner() {
        let true_expr = Expr::const_str("True");
        let mut ps = ps_with_goal(true_expr);
        let result = auto_cascade_with_info(&mut ps);
        assert!(result.is_ok());
        let info = result.unwrap();
        assert!(!info.winner.is_empty(), "winner name should be non-empty");
    }

    #[test]
    fn test_auto_cascade_tries_cert_mathverse_before_raw_mathverse() {
        let mut env = Environment::with_prelude();
        env.add_decl(Declaration::Definition {
            name: Name::from_string("Cert.PB.checkBound"),
            level_params: vec![],
            type_: Expr::prop(),
            value: Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.le"), vec![]),
                    Expr::nat_lit(5),
                ),
                Expr::nat_lit(3),
            ),
            is_reducible: true,
        })
        .expect("certificate wrapper should register");
        let mut ps = ProofState::with_context(
            env,
            Expr::const_(Name::from_string("False"), vec![]),
            vec![crate::tactic::LocalDecl {
                fvar: FVarId::new(0),
                name: "h".into(),
                ty: Expr::const_(Name::from_string("Cert.PB.checkBound"), vec![]),
                value: None,
            }],
        );

        let result = auto_cascade_with_info(&mut ps).expect("certificate arithmetic should close");

        assert_eq!(result.winner, "cert_mathverse");
        assert!(
            ps.is_complete(),
            "cert_mathverse should close the cascade goal"
        );
    }

    #[test]
    fn test_auto_cascade_with_info_unsolvable() {
        let false_expr = Expr::const_str("False");
        let mut ps = ps_with_goal(false_expr);
        let result = auto_cascade_with_info(&mut ps);
        assert!(result.is_err());
        match result.unwrap_err() {
            TacticError::AllTacticsFailed { combinator } => {
                assert_eq!(combinator, "auto_cascade");
            }
            other => panic!("expected AllTacticsFailed, got: {other:?}"),
        }
    }
}
