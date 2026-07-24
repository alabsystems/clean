// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended proof irrelevance tests covering edge cases.
//!
//! Covers: Pi-type propositions, universe polymorphism, definition unfolding,
//! non-typeable expressions, nested App proof terms, lazy delta reduction,
//! higher-order propositions, imax levels, symmetry, and let-bound types.

use super::*;

// ===== Helpers for multi-axiom setup =====

/// Add an axiom to the environment (panics on failure).
fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    use crate::env::Declaration;
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

/// Build `Expr::const_(Name::from_string(name), vec![])`.
fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

// ===== Tests =====

#[test]
fn test_proof_irrelevance_pi_type_proposition() {
    let mut env = Environment::new();
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());

    let imp_ty = Expr::pi(BinderInfo::Default, cst("P"), cst("Q"));
    add_axiom(&mut env, "hpq1", imp_ty.clone());
    add_axiom(&mut env, "hpq2", imp_ty.clone());

    let tc = TypeChecker::new(&env);
    assert_eq!(tc.infer_type(&imp_ty).unwrap(), Expr::prop());
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("hpq1"), &cst("hpq2")),
        Some(true)
    );
    assert!(tc.is_def_eq(&cst("hpq1"), &cst("hpq2")));
}

#[test]
fn test_proof_irrelevance_universe_polymorphic_prop_instantiated_to_prop() {
    use crate::env::Declaration;
    let mut env = Environment::new();
    let u = Name::from_string("u");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("PolyProp"),
        level_params: vec![u.clone()],
        type_: Expr::sort(Level::param(u)),
    })
    .unwrap();

    let poly_prop0 = Expr::const_(Name::from_string("PolyProp"), vec![Level::zero()]);
    add_axiom(&mut env, "poly_pf1", poly_prop0.clone());
    add_axiom(&mut env, "poly_pf2", poly_prop0.clone());

    let tc = TypeChecker::new(&env);
    assert_eq!(tc.infer_type(&poly_prop0).unwrap(), Expr::prop());
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("poly_pf1"), &cst("poly_pf2")),
        Some(true)
    );
    assert!(tc.is_def_eq(&cst("poly_pf1"), &cst("poly_pf2")));
}

#[test]
fn test_proof_irrelevance_through_definition_unfolding() {
    use crate::env::Declaration;
    let mut env = Environment::new();
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "p1", cst("P"));
    add_axiom(&mut env, "p2", cst("P"));

    env.add_decl(Declaration::Definition {
        name: Name::from_string("AliasProp"),
        level_params: vec![],
        type_: Expr::prop(),
        value: cst("P"),
        is_reducible: false,
    })
    .unwrap();

    let alias_prop = cst("AliasProp");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("alias_pf1"),
        level_params: vec![],
        type_: alias_prop.clone(),
        value: cst("p1"),
        is_reducible: false,
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("alias_pf2"),
        level_params: vec![],
        type_: alias_prop,
        value: cst("p2"),
        is_reducible: false,
    })
    .unwrap();

    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("alias_pf1"), &cst("alias_pf2")),
        Some(true)
    );
    assert!(tc.is_def_eq(&cst("alias_pf1"), &cst("alias_pf2")));
}

#[test]
fn test_proof_irrelevance_returns_none_for_nontypeable_expressions() {
    let mut env = Environment::new();
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "p", cst("P"));

    let tc = TypeChecker::new(&env);
    let bad = Expr::bvar(0);
    assert!(matches!(
        tc.infer_type(&bad),
        Err(TypeError::UnboundVariable(0))
    ));
    assert_eq!(tc.is_def_eq_proof_irrel(&bad, &cst("p")), None);
    assert_eq!(tc.is_def_eq_proof_irrel(&cst("p"), &bad), None);
}

#[test]
fn test_proof_irrelevance_nested_app_proof_terms() {
    let mut env = Environment::new();
    for name in ["P", "Q", "R"] {
        add_axiom(&mut env, name, Expr::prop());
    }
    add_axiom(&mut env, "p1", cst("P"));
    add_axiom(&mut env, "p2", cst("P"));
    add_axiom(&mut env, "q1", cst("Q"));
    add_axiom(&mut env, "q2", cst("Q"));

    // f, g : P -> Q -> R
    let proof_fn_ty = Expr::pi(
        BinderInfo::Default,
        cst("P"),
        Expr::pi(BinderInfo::Default, cst("Q"), cst("R")),
    );
    add_axiom(&mut env, "f", proof_fn_ty.clone());
    add_axiom(&mut env, "g", proof_fn_ty);

    let lhs = Expr::app(Expr::app(cst("f"), cst("p1")), cst("q1"));
    let rhs = Expr::app(Expr::app(cst("g"), cst("p2")), cst("q2"));

    let tc = TypeChecker::new(&env);
    tc.reset_proof_irrel_fallback_infer_count_for_tests();
    assert_eq!(
        tc.is_def_eq_proof_irrel(&lhs, &rhs),
        Some(true),
        "multi-argument proof applications should still be proof-irrelevant"
    );
    assert_eq!(
        tc.proof_irrel_fallback_infer_count_for_tests(),
        0,
        "nested App proof terms should stay on the quick inference path"
    );
    assert!(tc.is_def_eq(&lhs, &rhs));
}

/// Lean 4 parity: proof irrelevance is checked ONCE before the lazy delta
/// loop (is_def_eq_core Phase 1.5), not inside it. After delta unfolding,
/// proof irrelevance for the unfolded forms is caught by recursive
/// is_def_eq_core calls in the structural comparison phases, NOT by an
/// explicit check inside the delta loop itself.
///
/// This test verifies the Lean 4-aligned behavior (fix for #3229):
/// - Definitions whose DECLARED types are Type (not Prop) but whose VALUES
///   are proofs will NOT trigger proof irrelevance inside the delta loop.
/// - When the definitions CORRECTLY declare Prop types, proof irrelevance
///   is detected before the delta loop even starts.
///
/// Previous behavior (pre-#3229) checked proof irrelevance inside
/// finish_lazy_delta_reduction_step, which added infer_type overhead on
/// every delta step. Lean 4 type_checker.cpp:935 only calls quick_is_def_eq
/// after each step, not is_def_eq_proof_irrel.
#[test]
fn test_proof_irrelevance_not_checked_inside_lazy_delta_loop() {
    use crate::env::{Declaration, Reducibility};
    let mut env = Environment::new();
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "p1", cst("P"));
    add_axiom(&mut env, "p2", cst("P"));

    // Declarations with INCORRECT types (Type instead of P) — uses unchecked
    // to bypass type validation. After delta unfolding, the values (p1, p2)
    // are proofs but their declared types are Type, so proof irrelevance
    // won't be detected through the standard path.
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("lazy_hi"),
        level_params: vec![],
        type_: Expr::type_(),
        value: cst("p1"),
        is_reducible: false,
    });
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("lazy_lo"),
        level_params: vec![],
        type_: Expr::type_(),
        value: cst("p2"),
        is_reducible: false,
    });

    assert!(env.set_reducibility(&Name::from_string("lazy_hi"), Reducibility::Regular(1)));
    assert!(env.set_reducibility(&Name::from_string("lazy_lo"), Reducibility::Regular(0)));

    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("lazy_hi"), &cst("lazy_lo")),
        None,
        "the unchecked declarations are Type-valued before delta unfolds them"
    );
    // After delta unfolding, these become p1 vs p2 (different Const names).
    // Lean 4 does NOT check proof irrelevance after the delta loop, so these
    // would NOT be detected as equal. This matches Lean 4 behavior.
    // (In practice, well-typed declarations would have Prop as their declared
    // type, and proof irrelevance would be caught before the delta loop.)
    assert!(
        !tc.is_def_eq(&cst("lazy_hi"), &cst("lazy_lo")),
        "ill-typed declarations: proof irrelevance not detected after delta \
         (Lean 4 parity, #3229)"
    );
}

/// Proof irrelevance IS detected when definitions have correct Prop-valued
/// types, because the pre-delta check (is_def_eq_core Phase 1.5) catches it
/// before the delta loop even starts.
#[test]
fn test_proof_irrelevance_correct_types_caught_before_delta_loop() {
    use crate::env::{Declaration, Reducibility};
    let mut env = Environment::new();
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "p1", cst("P"));
    add_axiom(&mut env, "p2", cst("P"));

    // Correctly typed: declared type is P (which is in Prop)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("lazy_hi"),
        level_params: vec![],
        type_: cst("P"),
        value: cst("p1"),
        is_reducible: false,
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("lazy_lo"),
        level_params: vec![],
        type_: cst("P"),
        value: cst("p2"),
        is_reducible: false,
    })
    .unwrap();

    assert!(env.set_reducibility(&Name::from_string("lazy_hi"), Reducibility::Regular(1)));
    assert!(env.set_reducibility(&Name::from_string("lazy_lo"), Reducibility::Regular(0)));

    let tc = TypeChecker::new(&env);
    // With correct types, proof irrelevance is detected by the pre-delta
    // check (is_def_eq_proof_irrel at is_def_eq_core line 333).
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("lazy_hi"), &cst("lazy_lo")),
        Some(true),
        "correctly-typed Prop definitions should trigger proof irrelevance"
    );
    assert!(
        tc.is_def_eq(&cst("lazy_hi"), &cst("lazy_lo")),
        "proof irrelevance detected before delta loop for correctly-typed defs"
    );
}

#[test]
fn test_proof_irrelevance_higher_order_proposition() {
    let mut env = Environment::new();

    // (P : Prop) -> P -> P  is itself in Prop
    let ho_prop = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );

    add_axiom(&mut env, "ho_pf1", ho_prop.clone());
    add_axiom(&mut env, "ho_pf2", ho_prop.clone());

    let tc = TypeChecker::new(&env);
    assert_eq!(tc.infer_type(&ho_prop).unwrap(), Expr::prop());
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("ho_pf1"), &cst("ho_pf2")),
        Some(true)
    );
    assert!(tc.is_def_eq(&cst("ho_pf1"), &cst("ho_pf2")));
}

#[test]
fn test_proof_irrelevance_does_not_apply_to_type_aliases() {
    use crate::env::Declaration;
    let mut env = Environment::new();
    add_axiom(&mut env, "A", Expr::type_());

    env.add_decl(Declaration::Definition {
        name: Name::from_string("AliasType"),
        level_params: vec![],
        type_: Expr::type_(),
        value: cst("A"),
        is_reducible: true,
    })
    .unwrap();

    add_axiom(&mut env, "a1", cst("AliasType"));
    add_axiom(&mut env, "a2", cst("AliasType"));

    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("a1"), &cst("a2")),
        None,
        "Type aliases reduce to Sort(1), so proof irrelevance must not apply"
    );
    assert!(!tc.is_def_eq(&cst("a1"), &cst("a2")));
}

/// Negative complement: universe-polymorphic type at Sort(1) should NOT trigger proof irrelevance.
#[test]
fn test_no_proof_irrelevance_universe_polymorphic_type_at_sort1() {
    use crate::env::Declaration;
    let mut env = Environment::new();
    let u = Name::from_string("u");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("PolyType"),
        level_params: vec![u.clone()],
        type_: Expr::sort(Level::param(u)),
    })
    .unwrap();

    let poly_type1 = Expr::const_(
        Name::from_string("PolyType"),
        vec![Level::succ(Level::zero())],
    );
    add_axiom(&mut env, "x1", poly_type1.clone());
    add_axiom(&mut env, "x2", poly_type1.clone());

    let tc = TypeChecker::new(&env);
    assert_eq!(tc.infer_type(&poly_type1).unwrap(), Expr::type_());
    assert_eq!(tc.is_def_eq_proof_irrel(&cst("x1"), &cst("x2")), None);
    assert!(!tc.is_def_eq(&cst("x1"), &cst("x2")));
}

/// Proof irrelevance for `imax`-level propositions.
/// `(A : Type) -> P` has type `Sort(imax(1, 0)) = Sort(0) = Prop`.
/// Critical for real .olean loading.
#[test]
fn test_proof_irrelevance_imax_level_proposition() {
    let mut env = Environment::new();
    add_axiom(&mut env, "P", Expr::prop());

    let imax_prop = Expr::pi(BinderInfo::Default, Expr::type_(), cst("P"));
    add_axiom(&mut env, "f1", imax_prop.clone());
    add_axiom(&mut env, "f2", imax_prop.clone());

    let tc = TypeChecker::new(&env);
    let imax_sort = tc
        .infer_type(&imax_prop)
        .expect("imax_prop should type-check");
    assert!(
        imax_sort.is_prop(),
        "Sort(imax(1, 0)) should reduce to Prop, got {:?}",
        imax_sort
    );

    assert_eq!(tc.is_def_eq_proof_irrel(&cst("f1"), &cst("f2")), Some(true));
    assert!(tc.is_def_eq(&cst("f1"), &cst("f2")));
}

/// Symmetry: top-level `is_def_eq` must be symmetric even though
/// `is_def_eq_proof_irrel` short-circuits on the first argument.
#[test]
fn test_proof_irrelevance_symmetry() {
    let mut env = Environment::new();
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());
    add_axiom(&mut env, "p1", cst("P"));
    add_axiom(&mut env, "p2", cst("P"));
    add_axiom(&mut env, "q", cst("Q"));
    add_axiom(&mut env, "A", Expr::type_());
    add_axiom(&mut env, "a1", cst("A"));

    let tc = TypeChecker::new(&env);

    // Same Prop type: symmetric
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("p1"), &cst("p2")),
        tc.is_def_eq_proof_irrel(&cst("p2"), &cst("p1"))
    );
    // Different Prop types: symmetric
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("p1"), &cst("q")),
        tc.is_def_eq_proof_irrel(&cst("q"), &cst("p1"))
    );
    // Prop vs Type: asymmetric at proof_irrel level, but is_def_eq is symmetric
    assert_eq!(
        tc.is_def_eq_proof_irrel(&cst("p1"), &cst("a1")),
        Some(false)
    );
    assert_eq!(tc.is_def_eq_proof_irrel(&cst("a1"), &cst("p1")), None);
    assert_eq!(
        tc.is_def_eq(&cst("p1"), &cst("a1")),
        tc.is_def_eq(&cst("a1"), &cst("p1"))
    );
}

/// Proof irrelevance for let-bound proposition types.
#[test]
fn test_proof_irrelevance_let_bound_proposition_type() {
    let mut env = Environment::new();
    add_axiom(&mut env, "P", Expr::prop());
    for name in ["p1", "p2", "p3"] {
        add_axiom(&mut env, name, cst("P"));
    }

    let p_ty = cst("P");
    let let_expr_1 = Expr::let_named(
        Name::from_string("h"),
        p_ty.clone(),
        cst("p1"),
        cst("p2"), // body ignores binding
        false,
    );
    let let_expr_2 = Expr::let_named(Name::from_string("h"), p_ty, cst("p3"), cst("p3"), false);

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&let_expr_1, &let_expr_2),
        "let-bound proof terms of the same Prop should be def_eq via proof irrelevance"
    );
}
