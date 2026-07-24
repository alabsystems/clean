// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — literal handling and type error paths.
//!
//! Covers:
//! - `TypeError::LevelCountMismatch` — wrong universe level count on constants
//! - `string_lit_to_constructor` — string literal to constructor chain conversion
//! - `try_string_lit_expansion` (Phase 7 of is_def_eq) — string literal expansion in def_eq

use super::*;

// ===== TypeError::LevelCountMismatch tests =====
// LevelCountMismatch (tc/mod.rs:5008) fires when a Const is applied with the wrong
// number of universe levels. Added for #1277 but had zero test coverage.

/// Test LevelCountMismatch: too many universe levels.
#[test]
fn test_level_count_mismatch_too_many() {
    use crate::env::Declaration;
    use crate::tc::TypeError;

    let mut env = Environment::new();

    // Declare a constant with 0 universe params
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myAxiom"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add_decl should succeed");

    let tc = TypeChecker::new(&env);

    // Apply myAxiom with 1 universe level — should fail
    let bad_const = Expr::const_(Name::from_string("myAxiom"), vec![Level::zero()]);

    let err = tc
        .infer_type(&bad_const)
        .expect_err("Should reject wrong level count");
    assert!(
        matches!(
            &err,
            TypeError::LevelCountMismatch {
                expected: 0,
                got: 1,
                ..
            }
        ),
        "Expected LevelCountMismatch(expected=0, got=1), got: {err:?}"
    );
}

/// Test LevelCountMismatch: too few universe levels.
#[test]
fn test_level_count_mismatch_too_few() {
    use crate::env::Declaration;
    use crate::tc::TypeError;

    let mut env = Environment::new();

    // Declare a polymorphic constant with 2 universe params
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("polyAxiom"),
        level_params: vec![u, v],
        type_: Expr::type_(),
    })
    .expect("add_decl should succeed");

    let tc = TypeChecker::new(&env);

    // Apply with only 1 universe level — should fail
    let bad_const = Expr::const_(Name::from_string("polyAxiom"), vec![Level::zero()]);

    let err = tc
        .infer_type(&bad_const)
        .expect_err("Should reject too few levels");
    assert!(
        matches!(
            &err,
            TypeError::LevelCountMismatch {
                expected: 2,
                got: 1,
                ..
            }
        ),
        "Expected LevelCountMismatch(expected=2, got=1), got: {err:?}"
    );
}

/// Test LevelCountMismatch: correct count succeeds.
#[test]
fn test_level_count_correct_succeeds() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    let u = Name::from_string("u");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("uniAxiom"),
        level_params: vec![u],
        type_: Expr::sort(Level::param(Name::from_string("u"))),
    })
    .expect("add_decl should succeed");

    let tc = TypeChecker::new(&env);

    // Apply with correct number of universe levels
    let good_const = Expr::const_(Name::from_string("uniAxiom"), vec![Level::zero()]);

    let result = tc.infer_type(&good_const);
    assert!(
        result.is_ok(),
        "Correct level count should succeed, got: {result:?}"
    );
}

// ===== string_lit_to_constructor tests =====
// string_lit_to_constructor (tc/mod.rs:4893) converts string literals to
// String.ofList (List.cons (Char.ofNat <n>) ...) constructor chains.
// Previously had near-zero test coverage.

/// Test string_lit_to_constructor: empty string.
#[test]
fn test_string_lit_to_constructor_empty() {
    use crate::tc::string_lit_to_constructor;

    let result = string_lit_to_constructor("");

    // Should be: String.ofList (List.nil {Char})
    let fn_expr = result.get_app_fn();
    assert!(
        matches!(&fn_expr.kind, ExprKind::Const(name, _) if name.to_string() == "String.ofList"),
        "Empty string should produce String.ofList application, got fn: {fn_expr:?}"
    );

    // The argument should be List.nil applied to Char
    let args = result.get_app_args();
    assert_eq!(
        args.len(),
        1,
        "String.ofList should have exactly 1 argument (the list)"
    );

    let list_expr = &args[0];
    let list_fn = list_expr.get_app_fn();
    assert!(
        matches!(&list_fn.kind, ExprKind::Const(name, _) if name.to_string() == "List.nil"),
        "Empty string list should be List.nil, got: {list_fn:?}"
    );
}

/// Test string_lit_to_constructor: single character.
#[test]
fn test_string_lit_to_constructor_single_char() {
    use crate::tc::string_lit_to_constructor;

    let result = string_lit_to_constructor("A");

    // Should be: String.ofList (List.cons {Char} (Char.ofNat 65) (List.nil {Char}))
    let fn_expr = result.get_app_fn();
    assert!(
        matches!(&fn_expr.kind, ExprKind::Const(name, _) if name.to_string() == "String.ofList"),
        "Single char should produce String.ofList, got: {fn_expr:?}"
    );

    let args = result.get_app_args();
    assert_eq!(args.len(), 1, "String.ofList should have 1 argument");

    // The list argument: List.cons {Char} (Char.ofNat 65) (List.nil {Char})
    let list_expr = &args[0];
    let list_fn = list_expr.get_app_fn();
    assert!(
        matches!(&list_fn.kind, ExprKind::Const(name, _) if name.to_string() == "List.cons"),
        "Non-empty list should start with List.cons, got: {list_fn:?}"
    );
}

/// Test string_lit_to_constructor: multi-character preserves order.
#[test]
fn test_string_lit_to_constructor_multi_char_order() {
    use crate::tc::string_lit_to_constructor;

    let result = string_lit_to_constructor("ab");

    // Should be: String.ofList (List.cons {Char} (Char.ofNat 97) (List.cons {Char} (Char.ofNat 98) (List.nil {Char})))
    // The outermost List.cons should have Char.ofNat 97 ('a'), not 98 ('b')
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);

    // Drill into the list: first cons
    let list_expr = &args[0];
    let list_args = list_expr.get_app_args();
    // List.cons {Char} (Char.ofNat 97) (tail) — 3 args: Char type, char val, tail
    assert_eq!(
        list_args.len(),
        3,
        "List.cons should have 3 args (type, elem, tail)"
    );

    // The element (second arg) should be Char.ofNat applied to 97 ('a')
    let char_app = &list_args[1];
    let char_args = char_app.get_app_args();
    assert_eq!(char_args.len(), 1, "Char.ofNat should have 1 arg (the nat)");

    // Verify it's nat literal 97
    assert!(
        matches!(&char_args[0].kind, ExprKind::Lit(crate::expr::Literal::Nat(n)) if n.to_u64() == Some(97)),
        "First char should be 'a' (97), got: {:?}",
        char_args[0].kind
    );

    // The tail (third arg) should be another List.cons with 'b' (98)
    let tail = &list_args[2];
    let tail_fn = tail.get_app_fn();
    assert!(
        matches!(&tail_fn.kind, ExprKind::Const(name, _) if name.to_string() == "List.cons"),
        "Tail should be List.cons for second char, got: {tail_fn:?}"
    );
}

/// Test string_lit_to_constructor: Unicode character.
#[test]
fn test_string_lit_to_constructor_unicode() {
    use crate::tc::string_lit_to_constructor;

    // U+03B1 = α (Greek alpha) = code point 945
    let result = string_lit_to_constructor("α");

    let args = result.get_app_args();
    assert_eq!(args.len(), 1);

    let list_expr = &args[0];
    let list_args = list_expr.get_app_args();
    assert_eq!(
        list_args.len(),
        3,
        "Should be List.cons for single unicode char"
    );

    let char_app = &list_args[1];
    let char_args = char_app.get_app_args();
    assert!(
        matches!(&char_args[0].kind, ExprKind::Lit(crate::expr::Literal::Nat(n)) if n.to_u64() == Some(945)),
        "Unicode char α should be code point 945, got: {:?}",
        char_args[0].kind
    );
}

// ===== try_string_lit_expansion tests (Phase 7 of is_def_eq) =====
//
// These tests verify that is_def_eq's Phase 7 (string literal expansion)
// correctly equates a string literal with its constructor chain form.
//
// The expected constructor chain is built by `string_lit_to_constructor`,
// which is independently tested structurally above (test_string_lit_to_constructor_*).
// This avoids the tautological pattern of duplicating tree-building logic
// in a `manual_char_list` helper that mirrors the production code. (Part of #1646)

#[test]
fn test_try_string_lit_expansion_basic() {
    use crate::tc::string_lit_to_constructor;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lit = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::String("A".into())));
    let expected = string_lit_to_constructor("A");
    assert!(
        tc.is_def_eq(&lit, &expected),
        "\"A\" literal should be def_eq to its constructor expansion"
    );
}

#[test]
fn test_try_string_lit_expansion_empty() {
    use crate::tc::string_lit_to_constructor;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lit = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::String("".into())));
    let expected = string_lit_to_constructor("");
    assert!(
        tc.is_def_eq(&lit, &expected),
        "empty string literal should be def_eq to empty list constructor"
    );
}

#[test]
fn test_try_string_lit_expansion_multi_char() {
    use crate::tc::string_lit_to_constructor;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lit = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::String("hi".into())));
    let expected = string_lit_to_constructor("hi");
    assert!(
        tc.is_def_eq(&lit, &expected),
        "\"hi\" literal should be def_eq to its constructor expansion"
    );
}

#[test]
fn test_try_string_lit_expansion_symmetric() {
    use crate::tc::string_lit_to_constructor;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lit = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::String("X".into())));
    let expected = string_lit_to_constructor("X");
    assert!(
        // Phase 7 tries both orderings — verify constructor-first also works
        tc.is_def_eq(&expected, &lit),
        "constructor on left, literal on right should also work"
    );
}

#[test]
fn test_try_string_lit_expansion_different_strings() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lit_a = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::String("A".into())));
    let lit_b = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::String("B".into())));
    assert!(
        !tc.is_def_eq(&lit_a, &lit_b),
        "different strings should NOT be def_eq"
    );
}

#[test]
fn test_try_string_lit_expansion_unicode() {
    use crate::tc::string_lit_to_constructor;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lit = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::String("α".into())));
    let expected = string_lit_to_constructor("α");
    assert!(
        tc.is_def_eq(&lit, &expected),
        "Unicode literal α should be def_eq to its constructor expansion"
    );
}

#[test]
fn test_try_string_lit_expansion_wrong_code_detected() {
    use crate::tc::string_lit_to_constructor;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lit = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::String("A".into())));
    let wrong = string_lit_to_constructor("B");
    assert!(
        !tc.is_def_eq(&lit, &wrong),
        "\"A\" literal should NOT be def_eq to \"B\" constructor expansion"
    );
}
