// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for simproc infrastructure and built-in simprocs.

use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::tactic::core::ProofState;
use crate::tactic::simp::simproc::{builtin_simprocs, SimprocResult};

/// Helper: create a minimal ProofState + Goal for testing ground simprocs.
///
/// Uses `Environment::default()` instead of `Environment::new()` to avoid
/// stack overflow from deep init chains in debug mode. The simproc functions
/// under test here don't actually inspect the environment.
fn make_test_state() -> (ProofState, crate::tactic::core::Goal) {
    let env = clean_kernel::env::Environment::default();
    let target = Expr::const_(Name::from_string("True"), vec![]);
    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap().clone();
    (state, goal)
}

#[test]
fn test_gcd_basic() {
    fn gcd(mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            let t = b;
            b = a % b;
            a = t;
        }
        a
    }
    assert_eq!(gcd(12, 8), 4);
    assert_eq!(gcd(0, 5), 5);
    assert_eq!(gcd(5, 0), 5);
    assert_eq!(gcd(7, 13), 1);
    assert_eq!(gcd(100, 75), 25);
}

#[test]
fn test_builtin_simprocs_registry_size() {
    let set = builtin_simprocs();
    assert!(
        set.len() > 10,
        "expected >10 built-in simprocs, got {}",
        set.len()
    );
}

#[test]
fn test_simproc_set_matching() {
    let set = builtin_simprocs();

    let add_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );
    let matches = set.get_matching(&add_expr);
    assert!(
        !matches.is_empty(),
        "Nat.add should match at least one simproc"
    );
    assert_eq!(
        matches[0].name,
        Name::from_string("Nat.reduceAdd"),
        "First match should be Nat.reduceAdd"
    );

    let unknown = Expr::app(
        Expr::const_(Name::from_string("Unknown.op"), vec![]),
        Expr::nat_lit(1),
    );
    let no_matches = set.get_matching(&unknown);
    assert!(
        no_matches.is_empty(),
        "Unknown head should match no simprocs"
    );
}

#[test]
fn test_simproc_nat_add_ground() {
    let set = builtin_simprocs();
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );

    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, Expr::nat_lit(5), "2 + 3 should reduce to 5");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_nat_mul_ground() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            Expr::nat_lit(6),
        ),
        Expr::nat_lit(7),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, Expr::nat_lit(42), "6 * 7 should reduce to 42");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_nat_pow_ground() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(10),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, Expr::nat_lit(1024), "2 ^ 10 should reduce to 1024");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_nat_gcd_ground() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.gcd"), vec![]),
            Expr::nat_lit(12),
        ),
        Expr::nat_lit(8),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, Expr::nat_lit(4), "gcd(12, 8) should reduce to 4");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_nat_sub_saturating() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.sub"), vec![]),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(5),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, Expr::nat_lit(0), "3 - 5 should saturate to 0");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_nat_mod_ground() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mod"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, Expr::nat_lit(1), "10 % 3 should reduce to 1");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_nat_div_ground() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.div"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, Expr::nat_lit(3), "10 / 3 should reduce to 3");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_nat_div_by_zero() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.div"), vec![]),
            Expr::nat_lit(5),
        ),
        Expr::nat_lit(0),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(
                sr.expr,
                Expr::nat_lit(0),
                "5 / 0 should reduce to 0 (Lean Nat)"
            );
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_symbolic_args_continue() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::const_(Name::from_string("x"), vec![]),
        ),
        Expr::nat_lit(3),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    assert!(
        matches!(result, SimprocResult::Continue),
        "Symbolic args should return Continue"
    );
}

#[test]
fn test_simproc_succ_ground() {
    let expr = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(41),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, Expr::nat_lit(42), "succ 41 should reduce to 42");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

// ============================================================================
// Bool simproc tests
// ============================================================================

fn bool_true() -> Expr {
    Expr::const_(Name::from_string("Bool.true"), vec![])
}

fn bool_false() -> Expr {
    Expr::const_(Name::from_string("Bool.false"), vec![])
}

#[test]
fn test_simproc_bool_not_true() {
    let expr = Expr::app(
        Expr::const_(Name::from_string("Bool.not"), vec![]),
        bool_true(),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty(), "Bool.not should match a simproc");

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, bool_false(), "not true should reduce to false");
            assert!(sr.proof.is_none(), "Bool reduction is definitional");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_bool_not_false() {
    let expr = Expr::app(
        Expr::const_(Name::from_string("Bool.not"), vec![]),
        bool_false(),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, bool_true(), "not false should reduce to true");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_bool_and_true_b() {
    // Bool.and true b → b
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Bool.and"), vec![]),
            bool_true(),
        ),
        b.clone(),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, b, "true && b should reduce to b");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_bool_and_false_b() {
    // Bool.and false b → false
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Bool.and"), vec![]),
            bool_false(),
        ),
        b,
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, bool_false(), "false && b should reduce to false");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_bool_or_false_b() {
    // Bool.or false b → b
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Bool.or"), vec![]),
            bool_false(),
        ),
        b.clone(),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, b, "false || b should reduce to b");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_bool_or_true_b() {
    // Bool.or true b → true
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Bool.or"), vec![]),
            bool_true(),
        ),
        b,
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, bool_true(), "true || b should reduce to true");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_bool_bne_same() {
    // BNe.bne true true → false
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("BNe.bne"), vec![]),
            bool_true(),
        ),
        bool_true(),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(
                sr.expr,
                bool_false(),
                "bne true true should reduce to false"
            );
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_bool_bne_diff() {
    // BNe.bne true false → true
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("BNe.bne"), vec![]),
            bool_true(),
        ),
        bool_false(),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    match result {
        SimprocResult::Done(sr) => {
            assert_eq!(sr.expr, bool_true(), "bne true false should reduce to true");
        }
        other => panic!("Expected Done, got {other:?}"),
    }
}

#[test]
fn test_simproc_bool_and_symbolic_returns_continue() {
    // Bool.and x y (both symbolic) → Continue
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Bool.and"), vec![]),
            Expr::const_(Name::from_string("x"), vec![]),
        ),
        Expr::const_(Name::from_string("y"), vec![]),
    );

    let set = builtin_simprocs();
    let matches = set.get_matching(&expr);
    assert!(!matches.is_empty());

    let (state, goal) = make_test_state();
    let result = (matches[0].proc)(&state, &goal, &expr);
    assert!(
        matches!(result, SimprocResult::Continue),
        "Symbolic Bool args should return Continue"
    );
}

#[test]
fn test_builtin_simprocs_includes_bool() {
    let set = builtin_simprocs();
    // Verify Bool simprocs are registered by checking matching
    let not_expr = Expr::app(
        Expr::const_(Name::from_string("Bool.not"), vec![]),
        bool_true(),
    );
    assert!(
        !set.get_matching(&not_expr).is_empty(),
        "Bool.not should be registered in builtin simprocs"
    );

    let and_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Bool.and"), vec![]),
            bool_true(),
        ),
        bool_false(),
    );
    assert!(
        !set.get_matching(&and_expr).is_empty(),
        "Bool.and should be registered in builtin simprocs"
    );

    let or_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Bool.or"), vec![]),
            bool_true(),
        ),
        bool_false(),
    );
    assert!(
        !set.get_matching(&or_expr).is_empty(),
        "Bool.or should be registered in builtin simprocs"
    );
}
