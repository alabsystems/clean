// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler implementations for complex-argument built-in tactics.
//!
//! Split from `builtins.rs` (#307). Contains handler functions used by
//! `register_complex_arg_tactics` and `register_ay_tactics`.

use std::sync::Arc;

use clean_kernel::Expr;

use super::builtins::expr_to_hyp_name;
use super::registry::{TacticArgPattern, TacticEntry};
use super::{ProofState, TacticError, TacticResult};

/// Register tactics with complex argument handling.
///
/// REQUIRES: `registry` is initialized
/// ENSURES: all complex-arg tactics (rcases, rintro, obtain, etc.) are registered
pub(crate) fn register_complex_arg_tactics(registry: &mut super::registry::TacticRegistry) {
    // rcases <hyp> [<max_depth>] — defaults: last hypothesis, max_depth=5
    registry.register(TacticEntry {
        name: "rcases".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(rcases_handler),
    });

    // rintro <patterns...> — identifier patterns extracted from args
    registry.register(TacticEntry {
        name: "rintro".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(rintro_handler),
    });

    // obtain <hyp> <var> <new_hyp>
    registry.register(TacticEntry {
        name: "obtain".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(obtain_handler),
    });

    // solve_by_elim [<max_depth>] — default max_depth=6
    registry.register(TacticEntry {
        name: "solve_by_elim".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|ps, _args| super::solve_by_elim(ps, 6)),
    });

    // library_search — returns Vec but we only need success/failure
    registry.register(TacticEntry {
        name: "library_search".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(library_search_handler),
    });

    // convert <proof_term> — pass elaborated Expr directly
    registry.register(TacticEntry {
        name: "convert".to_string(),
        pattern: TacticArgPattern::TermArg,
        handler: Arc::new(convert_handler),
    });

    // wlog <assumption_name> <assumption_expr>
    registry.register(TacticEntry {
        name: "wlog".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(wlog_handler),
    });

    // lift <var_name> [using <hyp>]
    registry.register(TacticEntry {
        name: "lift".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(lift_handler),
    });

    // choose <hyp> <witness_name> <proof_name>
    registry.register(TacticEntry {
        name: "choose".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(choose_handler),
    });

    // monad_pres [field1, field2, ...] — compositional state preservation (#3403)
    registry.register(TacticEntry {
        name: "monad_pres".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(super::monad_pres),
    });
}

/// Register ay SMT tactics. Each reads `AyConfig::from_env()` at invocation
/// time for runtime policy switching. Pipeline activation for #2427.
///
/// REQUIRES: `registry` is initialized
/// ENSURES: ay_omega, ay_bv, ay_smt, ay_decide, ay_lra are registered
pub(crate) fn register_ay_tactics(registry: &mut super::registry::TacticRegistry) {
    type AyFn = fn(&mut ProofState, super::AyConfig) -> TacticResult;
    let tactics: [(&str, AyFn); 5] = [
        ("ay_omega", super::ay_omega),
        ("ay_bv", super::ay_bv),
        ("ay_smt", super::ay_smt),
        ("ay_decide", super::ay_decide),
        ("ay_lra", super::ay_lra),
    ];
    for (name, func) in tactics {
        registry.register(TacticEntry {
            name: name.to_string(),
            pattern: TacticArgPattern::Nullary,
            handler: Arc::new(move |ps, _args| func(ps, super::AyConfig::from_env())),
        });
    }
}

fn rcases_handler(ps: &mut ProofState, args: &[Expr]) -> Result<(), TacticError> {
    let hyp_name = if let Some(arg) = args.first() {
        expr_to_hyp_name(ps, arg)?
    } else {
        ps.current_goal()
            .and_then(|g| g.local_ctx.last())
            .map(|d| d.name.clone())
            .ok_or_else(|| TacticError::HypothesisNotFound("rcases: no hypotheses".into()))?
    };
    super::rcases(ps, &hyp_name, 5)
}

fn rintro_handler(ps: &mut ProofState, args: &[Expr]) -> Result<(), TacticError> {
    let patterns: Vec<String> = args
        .iter()
        .map(|a| expr_to_hyp_name(ps, a))
        .collect::<Result<Vec<_>, _>>()?;
    super::rintro(ps, patterns)
}

fn obtain_handler(ps: &mut ProofState, args: &[Expr]) -> Result<(), TacticError> {
    let [hyp, var, new_hyp, ..] = args else {
        return Err(TacticError::MissingArgument {
            tactic: "obtain".into(),
            expected: "3 arguments: <hyp> <var> <new_hyp>".into(),
        });
    };
    let hyp_name = expr_to_hyp_name(ps, hyp)?;
    let var_name = expr_to_hyp_name(ps, var)?;
    let new_hyp_name = expr_to_hyp_name(ps, new_hyp)?;
    super::obtain(ps, &hyp_name, &var_name, &new_hyp_name)
}

fn library_search_handler(ps: &mut ProofState, _args: &[Expr]) -> Result<(), TacticError> {
    super::library_search_and_apply(ps)
}

fn convert_handler(ps: &mut ProofState, args: &[Expr]) -> Result<(), TacticError> {
    let proof_term = args.first().ok_or_else(|| TacticError::MissingArgument {
        tactic: "convert".into(),
        expected: "a proof term argument".into(),
    })?;
    super::convert(ps, proof_term.clone())
}

fn wlog_handler(ps: &mut ProofState, args: &[Expr]) -> Result<(), TacticError> {
    let [name_expr, assumption, ..] = args else {
        return Err(TacticError::MissingArgument {
            tactic: "wlog".into(),
            expected: "2 arguments: <name> <assumption>".into(),
        });
    };
    let name = expr_to_hyp_name(ps, name_expr)?;
    super::wlog(ps, &name, assumption.clone())
}

fn lift_handler(ps: &mut ProofState, args: &[Expr]) -> Result<(), TacticError> {
    let var_name = args
        .first()
        .map(|a| expr_to_hyp_name(ps, a))
        .transpose()?
        .ok_or_else(|| TacticError::MissingArgument {
            tactic: "lift".into(),
            expected: "a variable name".into(),
        })?;
    let using_hyp = args.get(1).map(|a| expr_to_hyp_name(ps, a)).transpose()?;
    super::lift(ps, &var_name, using_hyp.as_deref())
}

fn choose_handler(ps: &mut ProofState, args: &[Expr]) -> Result<(), TacticError> {
    let [hyp, witness, proof, ..] = args else {
        return Err(TacticError::MissingArgument {
            tactic: "choose".into(),
            expected: "3 arguments: <hyp> <witness> <proof>".into(),
        });
    };
    let hyp_name = expr_to_hyp_name(ps, hyp)?;
    let witness_name = expr_to_hyp_name(ps, witness)?;
    let proof_name = expr_to_hyp_name(ps, proof)?;
    super::choose(ps, &hyp_name, &witness_name, &proof_name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::Declaration;
    use clean_kernel::name::Name;
    use clean_kernel::Environment;

    fn test_state() -> ProofState {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("A"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("test axiom A should register");
        ProofState::new(env, Expr::const_(Name::from_string("A"), vec![]))
    }

    fn intro_test_state() -> ProofState {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("A"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("test proposition A should register");
        let a = Expr::const_(Name::from_string("A"), vec![]);
        ProofState::new(env, Expr::arrow(a.clone(), Expr::arrow(a.clone(), a)))
    }

    fn assert_missing_argument(err: TacticError, tactic_name: &str, expected_args: &str) {
        match err {
            TacticError::MissingArgument { tactic, expected } => {
                assert_eq!(tactic, tactic_name);
                assert_eq!(expected, expected_args);
            }
            other => panic!("expected MissingArgument, got {other:?}"),
        }
    }

    #[test]
    fn test_convert_handler_rejects_missing_proof_term() {
        let mut ps = test_state();
        let err = convert_handler(&mut ps, &[]).expect_err("convert should reject empty args");
        assert_missing_argument(err, "convert", "a proof term argument");
    }

    #[test]
    fn test_obtain_handler_rejects_short_args() {
        let mut ps = test_state();
        let args = [Expr::const_(Name::from_string("h"), vec![])];
        let err = obtain_handler(&mut ps, &args).expect_err("obtain should reject short args");
        assert_missing_argument(err, "obtain", "3 arguments: <hyp> <var> <new_hyp>");
    }

    #[test]
    fn test_wlog_handler_rejects_short_args() {
        let mut ps = test_state();
        let args = [Expr::const_(Name::from_string("h"), vec![])];
        let err = wlog_handler(&mut ps, &args).expect_err("wlog should reject short args");
        assert_missing_argument(err, "wlog", "2 arguments: <name> <assumption>");
    }

    #[test]
    fn test_choose_handler_rejects_short_args() {
        let mut ps = test_state();
        let args = [
            Expr::const_(Name::from_string("h"), vec![]),
            Expr::const_(Name::from_string("w"), vec![]),
        ];
        let err = choose_handler(&mut ps, &args).expect_err("choose should reject short args");
        assert_missing_argument(err, "choose", "3 arguments: <hyp> <witness> <proof>");
    }

    #[test]
    fn test_rintro_handler_rejects_invalid_pattern_without_silently_dropping_it() {
        let mut ps = intro_test_state();
        let args = [
            Expr::const_(Name::from_string("h1"), vec![]),
            Expr::type_(),
            Expr::const_(Name::from_string("h2"), vec![]),
        ];

        let err = rintro_handler(&mut ps, &args).expect_err("invalid patterns should stop rintro");

        assert!(
            matches!(
                err,
                TacticError::InvalidTarget { ref tactic, .. } if tactic == "resolve_ident"
            ),
            "expected invalid identifier extraction error, got {err:?}"
        );
        assert_eq!(
            ps.current_goal()
                .expect("goal should remain present after failed handler")
                .local_ctx
                .len(),
            0,
            "rintro handler must fail before introducing any hypotheses"
        );
    }
}
