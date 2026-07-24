// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_translate_const() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let t1 = bridge
        .translate_term(&a)
        .expect("constant translation should succeed");

    // Same constant should give same term.
    let t2 = bridge
        .translate_term(&a)
        .expect("re-translating the same constant should succeed");
    assert_eq!(t1, t2);

    // Different constant should give different term.
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let t3 = bridge
        .translate_term(&b)
        .expect("distinct constant translation should succeed");
    assert_ne!(t1, t3);
}

#[test]
fn test_translate_app() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let fa = Expr::app(f.clone(), a.clone());

    let t1 = bridge
        .translate_term(&fa)
        .expect("application translation should succeed");

    // Same application should give same term.
    let t2 = bridge
        .translate_term(&fa)
        .expect("re-translating the same application should succeed");
    assert_eq!(t1, t2);

    // Application term must differ from its sub-terms (f and a individually).
    let t_f = bridge
        .translate_term(&f)
        .expect("function constant translation should succeed");
    let t_a = bridge
        .translate_term(&a)
        .expect("argument constant translation should succeed");
    assert_ne!(t1, t_f, "f(a) should differ from f alone");
    assert_ne!(t1, t_a, "f(a) should differ from a alone");
}

#[test]
fn test_translate_term_populates_sub_term_types() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    // setup_env declares: A : Type, a : A, f : A -> A.
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let fa = Expr::app(f.clone(), a.clone());

    // Translate f(a) — this should populate term_to_type for f, a, and f(a).
    let term_fa = bridge
        .translate_term(&fa)
        .expect("application translation should populate term_to_type");
    let term_a = bridge
        .translate_term(&a)
        .expect("constant translation should populate term_to_type");
    let term_f = bridge
        .translate_term(&f)
        .expect("function translation should populate term_to_type");

    let expected_a_ty = Expr::const_(Name::from_string("A"), vec![]);

    // Access term_to_type directly to verify population.
    let ty_a = bridge.term_to_type.get(&term_a).cloned();
    assert_eq!(
        ty_a,
        Some(expected_a_ty.clone()),
        "Sub-term 'a' should have inferred type A in term_to_type"
    );

    let ty_f = bridge.term_to_type.get(&term_f).cloned();
    let expected_f_ty = Expr::arrow(expected_a_ty.clone(), expected_a_ty.clone());
    assert_eq!(
        ty_f,
        Some(expected_f_ty),
        "Sub-term 'f' should have type A -> A in term_to_type"
    );

    let ty_fa = bridge.term_to_type.get(&term_fa).cloned();
    assert_eq!(
        ty_fa,
        Some(expected_a_ty),
        "f(a) should have type A in term_to_type"
    );
}
