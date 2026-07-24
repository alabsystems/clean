// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded simp/simp_rw proof-soundness property tests.
//!
//! Generated rewrite cases exercise the oracle: success implies
//! complete goal closure, zero trusted fallback, extractable proof terms,
//! and a type-checking `closed_proof()`.
//!
//! Part of #1868.

use super::*;
use clean_kernel::env::SimpPriority;
use proptest::prelude::*;
use serial_test::serial;

// ---------------------------------------------------------------------------
// Case language
// ---------------------------------------------------------------------------

/// A bounded simp rewrite case.
#[derive(Debug, Clone)]
enum SimpCase {
    /// Single equality simp lemma: `f(a) = a`, goal `f(a) = a`.
    SingleRewriteBool { fn_name: String, val_name: String },
    /// Two simp lemmas: `a = b`, `b = c`, goal `a = c`.
    TransitivityChainBool {
        name_a: String,
        name_b: String,
        name_c: String,
    },
    /// `not (not b) = b`, goal `not (not b) = b`.
    DoubleNegationBool { val_name: String },
    /// Local equality rewrite: `h : a = b |- a = a` via `simp_rw [h]`.
    LocalEqualityRewrite {
        type_name: String,
        lhs_name: String,
        rhs_name: String,
    },
    /// Reverse local equality rewrite: `h : a = b |- b = b` via `simp_rw [h]`.
    LocalEqualityRewriteReverse {
        type_name: String,
        lhs_name: String,
        rhs_name: String,
    },
    /// Two local equality hypotheses: `h1 : a = b`, `h2 : b = c |- a = c`.
    LocalEqualityRewriteChain {
        type_name: String,
        lhs_name: String,
        mid_name: String,
        rhs_name: String,
    },
}

/// Which simp tactic to invoke.
#[derive(Debug, Clone)]
enum SimpTactic {
    Default,
    RwWithIntro,
    RwWithTwoIntros,
}

// ---------------------------------------------------------------------------
// Per-variant environment builders
// ---------------------------------------------------------------------------

fn add_axiom(env: &mut Environment, name: &str, ty: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
    })
    .unwrap();
}

fn add_simp_lemma(env: &mut Environment, name: &str, ty: Expr) {
    add_axiom(env, name, ty);
    env.register_simp_lemma(Name::from_string(name), SimpPriority::Default);
}

fn bool_eq_env() -> Environment {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_eq().unwrap();
    env
}

fn build_single_rewrite(fn_name: &str, val_name: &str) -> (Environment, Expr, SimpTactic) {
    let mut env = bool_eq_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    add_axiom(&mut env, val_name, bool_ty.clone());
    add_axiom(
        &mut env,
        fn_name,
        Expr::arrow(bool_ty.clone(), bool_ty.clone()),
    );

    let val = Expr::const_(Name::from_string(val_name), vec![]);
    let fn_app = Expr::app(
        Expr::const_(Name::from_string(fn_name), vec![]),
        val.clone(),
    );

    let lemma_name = format!("{fn_name}_simp");
    add_simp_lemma(
        &mut env,
        &lemma_name,
        make_eq(bool_ty.clone(), fn_app.clone(), val.clone()),
    );

    (env, make_eq(bool_ty, fn_app, val), SimpTactic::Default)
}

fn build_transitivity_chain(
    name_a: &str,
    name_b: &str,
    name_c: &str,
) -> (Environment, Expr, SimpTactic) {
    let mut env = bool_eq_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    for name in [name_a, name_b, name_c] {
        add_axiom(&mut env, name, bool_ty.clone());
    }

    let a = Expr::const_(Name::from_string(name_a), vec![]);
    let b = Expr::const_(Name::from_string(name_b), vec![]);
    let c = Expr::const_(Name::from_string(name_c), vec![]);

    let ab_name = format!("{name_a}_to_{name_b}");
    add_simp_lemma(
        &mut env,
        &ab_name,
        make_eq(bool_ty.clone(), a.clone(), b.clone()),
    );

    let bc_name = format!("{name_b}_to_{name_c}");
    add_simp_lemma(&mut env, &bc_name, make_eq(bool_ty.clone(), b, c.clone()));

    (env, make_eq(bool_ty, a, c), SimpTactic::Default)
}

fn build_double_negation(val_name: &str) -> (Environment, Expr, SimpTactic) {
    let mut env = bool_eq_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    add_axiom(&mut env, val_name, bool_ty.clone());

    let val = Expr::const_(Name::from_string(val_name), vec![]);
    let not_val = Expr::app(
        Expr::const_(Name::from_string("Bool.not"), vec![]),
        val.clone(),
    );
    let not_not_val = Expr::app(Expr::const_(Name::from_string("Bool.not"), vec![]), not_val);

    let lemma_name = format!("{val_name}_not_not");
    add_simp_lemma(
        &mut env,
        &lemma_name,
        make_eq(bool_ty.clone(), not_not_val.clone(), val.clone()),
    );

    (env, make_eq(bool_ty, not_not_val, val), SimpTactic::Default)
}

fn build_local_equality(
    type_name: &str,
    lhs_name: &str,
    rhs_name: &str,
) -> (Environment, Expr, SimpTactic) {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    add_axiom(&mut env, type_name, Expr::type_());

    let ty = Expr::const_(Name::from_string(type_name), vec![]);
    for name in [lhs_name, rhs_name] {
        add_axiom(&mut env, name, ty.clone());
    }

    let a = Expr::const_(Name::from_string(lhs_name), vec![]);
    let b = Expr::const_(Name::from_string(rhs_name), vec![]);

    // Goal: (h : a = b) → a = a
    // simp_rw [h] rewrites both `a` occurrences to `b`, giving `b = b`, then rfl.
    let h_ty = make_eq(ty.clone(), a.clone(), b);
    let goal = Expr::pi(BinderInfo::Default, h_ty, make_eq(ty, a.clone(), a));
    (env, goal, SimpTactic::RwWithIntro)
}

fn build_local_equality_reverse(
    type_name: &str,
    lhs_name: &str,
    rhs_name: &str,
) -> (Environment, Expr, SimpTactic) {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    add_axiom(&mut env, type_name, Expr::type_());

    let ty = Expr::const_(Name::from_string(type_name), vec![]);
    for name in [lhs_name, rhs_name] {
        add_axiom(&mut env, name, ty.clone());
    }

    let a = Expr::const_(Name::from_string(lhs_name), vec![]);
    let b = Expr::const_(Name::from_string(rhs_name), vec![]);

    // Goal: (h : a = b) → b = b
    // simp_rw [h] must use Eq.symm h to rewrite both `b` occurrences back to `a`.
    let h_ty = make_eq(ty.clone(), a, b.clone());
    let goal = Expr::pi(BinderInfo::Default, h_ty, make_eq(ty, b.clone(), b));
    (env, goal, SimpTactic::RwWithIntro)
}

fn build_local_equality_chain(
    type_name: &str,
    lhs_name: &str,
    mid_name: &str,
    rhs_name: &str,
) -> (Environment, Expr, SimpTactic) {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    add_axiom(&mut env, type_name, Expr::type_());

    let ty = Expr::const_(Name::from_string(type_name), vec![]);
    for name in [lhs_name, mid_name, rhs_name] {
        add_axiom(&mut env, name, ty.clone());
    }

    let a = Expr::const_(Name::from_string(lhs_name), vec![]);
    let b = Expr::const_(Name::from_string(mid_name), vec![]);
    let c = Expr::const_(Name::from_string(rhs_name), vec![]);

    // Goal: (h1 : a = b) → (h2 : b = c) → a = c
    // simp_rw [h1, h2] should rewrite the left side through both local equalities.
    let h1_ty = make_eq(ty.clone(), a.clone(), b.clone());
    let h2_ty = make_eq(ty.clone(), b, c.clone());
    let goal = Expr::pi(
        BinderInfo::Default,
        h1_ty,
        Expr::pi(BinderInfo::Default, h2_ty, make_eq(ty, a, c)),
    );
    (env, goal, SimpTactic::RwWithTwoIntros)
}

impl SimpCase {
    fn build(&self) -> (Environment, Expr, SimpTactic) {
        match self {
            SimpCase::SingleRewriteBool { fn_name, val_name } => {
                build_single_rewrite(fn_name, val_name)
            }
            SimpCase::TransitivityChainBool {
                name_a,
                name_b,
                name_c,
            } => build_transitivity_chain(name_a, name_b, name_c),
            SimpCase::DoubleNegationBool { val_name } => build_double_negation(val_name),
            SimpCase::LocalEqualityRewrite {
                type_name,
                lhs_name,
                rhs_name,
            } => build_local_equality(type_name, lhs_name, rhs_name),
            SimpCase::LocalEqualityRewriteReverse {
                type_name,
                lhs_name,
                rhs_name,
            } => build_local_equality_reverse(type_name, lhs_name, rhs_name),
            SimpCase::LocalEqualityRewriteChain {
                type_name,
                lhs_name,
                mid_name,
                rhs_name,
            } => build_local_equality_chain(type_name, lhs_name, mid_name, rhs_name),
        }
    }
}

// ---------------------------------------------------------------------------
// Strategies
// ---------------------------------------------------------------------------

/// Safe uppercase identifiers that don't collide with builtins.
fn upper_ident_strategy() -> impl Strategy<Value = String> {
    "[A-Z][a-z0-9]{0,3}".prop_filter("must not collide with builtins", |s| {
        !matches!(
            s.as_str(),
            "Bool" | "Nat" | "Prop" | "Type" | "Sort" | "True" | "False" | "Eq" | "Ne"
        )
    })
}

fn distinct_triple() -> impl Strategy<Value = (String, String, String)> {
    (
        upper_ident_strategy(),
        upper_ident_strategy(),
        upper_ident_strategy(),
    )
        .prop_filter("all three must be distinct", |(a, b, c)| {
            a != b && b != c && a != c
        })
}

fn distinct_quadruple() -> impl Strategy<Value = (String, String, String, String)> {
    (
        upper_ident_strategy(),
        upper_ident_strategy(),
        upper_ident_strategy(),
        upper_ident_strategy(),
    )
        .prop_filter("all four must be distinct", |(a, b, c, d)| {
            a != b && a != c && a != d && b != c && b != d && c != d
        })
}

fn distinct_pair() -> impl Strategy<Value = (String, String)> {
    (upper_ident_strategy(), upper_ident_strategy())
        .prop_filter("must be distinct", |(a, b)| a != b)
}

fn simp_case_strategy() -> impl Strategy<Value = SimpCase> {
    prop_oneof![
        distinct_pair()
            .prop_map(|(fn_name, val_name)| SimpCase::SingleRewriteBool { fn_name, val_name }),
        distinct_triple().prop_map(|(name_a, name_b, name_c)| {
            SimpCase::TransitivityChainBool {
                name_a,
                name_b,
                name_c,
            }
        }),
        upper_ident_strategy()
            .prop_filter("must not shadow Bool.not", |s| s != "Bool")
            .prop_map(|val_name| SimpCase::DoubleNegationBool { val_name }),
        distinct_triple().prop_map(|(type_name, lhs_name, rhs_name)| {
            SimpCase::LocalEqualityRewrite {
                type_name,
                lhs_name,
                rhs_name,
            }
        }),
        distinct_triple().prop_map(|(type_name, lhs_name, rhs_name)| {
            SimpCase::LocalEqualityRewriteReverse {
                type_name,
                lhs_name,
                rhs_name,
            }
        }),
        distinct_quadruple().prop_map(|(type_name, lhs_name, mid_name, rhs_name)| {
            SimpCase::LocalEqualityRewriteChain {
                type_name,
                lhs_name,
                mid_name,
                rhs_name,
            }
        }),
    ]
}

// ---------------------------------------------------------------------------
// Oracle assertions
// ---------------------------------------------------------------------------

/// Full proof-soundness oracle for simp tactic success.
fn assert_simp_soundness_oracle(
    state: &ProofState,
    goal_ty: &Expr,
    case_desc: &str,
    axiom_before: (u64, u64),
) {
    assert!(
        state.is_complete(),
        "{case_desc}: tactic should close the goal"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{case_desc}: must not use trusted axioms"
    );
    assert_no_trusted_axiom_usage(case_desc, "simp soundness proptest", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "{case_desc}: proof_term() must be extractable"
    );

    let closed = state
        .closed_proof()
        .unwrap_or_else(|| panic!("{case_desc}: closed_proof() must be extractable"));

    let tc = TypeChecker::new(state.env());
    let check = tc.check_type(&closed, goal_ty);
    assert!(
        check.is_ok(),
        "{case_desc}: closed proof must type-check against goal type, got {:?}",
        check.err()
    );
}

fn assert_generated_simp_case(case: SimpCase) {
    let case_desc = format!("{:?}", case);
    let (env, goal, tactic) = case.build();
    let goal_ty = goal.clone();

    reset_all_counters();
    let mut state = ProofState::new(env, goal);
    let axiom_before = axiom_snapshot();

    let result = match tactic {
        SimpTactic::Default => simp_default(&mut state),
        SimpTactic::RwWithIntro => {
            intro(&mut state, "h").expect("intro should succeed");
            simp_rw(&mut state, vec!["h".to_string()])
        }
        SimpTactic::RwWithTwoIntros => {
            intro(&mut state, "h1").expect("first intro should succeed");
            intro(&mut state, "h2").expect("second intro should succeed");
            simp_rw(&mut state, vec!["h1".to_string(), "h2".to_string()])
        }
    };

    match result {
        Ok(()) => assert_simp_soundness_oracle(&state, &goal_ty, &case_desc, axiom_before),
        Err(err) => panic!("{case_desc}: tactic should succeed, got {:?}", err),
    }
}

#[test]
#[serial]
fn test_generated_simp_soundness_reverse_local_rewrite_case() {
    assert_generated_simp_case(SimpCase::LocalEqualityRewriteReverse {
        type_name: "T".to_string(),
        lhs_name: "A".to_string(),
        rhs_name: "B".to_string(),
    });
}

#[test]
#[serial]
fn test_generated_simp_soundness_local_rewrite_chain_case() {
    assert_generated_simp_case(SimpCase::LocalEqualityRewriteChain {
        type_name: "T".to_string(),
        lhs_name: "A".to_string(),
        mid_name: "B".to_string(),
        rhs_name: "C".to_string(),
    });
}

// ---------------------------------------------------------------------------
// Property tests
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    /// Property: Every successful generated simp case produces a complete,
    /// trust-free, type-checking proof.
    #[test]
    #[serial]
    fn prop_simp_soundness(case in simp_case_strategy()) {
        assert_generated_simp_case(case);
    }
}
