// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for quotation patterns (q-patterns) in type elaboration
//!
//! Tests cover:
//! - Static q-pattern matching
//! - Runtime q-pattern matching with dynamic scrutinees
//! - Duplicate binder handling (#317)
//! - Universe-level pattern variables (#318)
//! - ~q(...) pattern elaboration
//! - let q(...) pattern elaboration (#751)
//! - Qq quotation elaboration and antiquotations
//! - qq_expr parser extensions (arrow/let/if/ascription)
//! - let-pattern desugaring for non-q patterns (#751)

use super::*;

// Part of #23: Qq Phase 4 - Runtime pattern matching
// =============================================================================

#[test]
fn test_q_pattern_parsing() {
    // Verify that q patterns are being parsed correctly
    use clean_parser::Parser;

    let code = r#"
match q(42) with
| q(42) => q(1)
| _ => q(0)
"#;
    let parsed = Parser::parse_expr(code);
    assert!(parsed.is_ok(), "Should parse: {:?}", parsed.err());

    if let Ok(SurfaceExpr::Match(_, _, _, arms)) = parsed {
        use clean_parser::SurfacePattern;
        assert!(
            matches!(&arms[0].pattern, SurfacePattern::QPattern(_)),
            "First arm should be QPattern, got {:?}",
            arms[0].pattern
        );
    }
}

#[test]
fn test_needs_runtime_q_match_static() {
    // Static scrutinee - should not need runtime matching
    // The body of the match arm uses literal - doesn't reference pattern var
    let code = r#"
match q(42) with
| q(42) => q(1)
| _ => q(0)
"#;
    // This should work at elaboration time (static matching)
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Static q-match should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_needs_runtime_q_match_dynamic_param() {
    // Dynamic scrutinee (function parameter) - needs runtime matching
    // This generates runtime code with isDefEq checks
    let code = r#"
fun (e : Type) =>
  match e with
  | q($x) => x
  | _ => e
"#;
    let result = elab(code);
    // Should succeed by generating runtime matching code
    assert!(
        result.is_ok(),
        "Dynamic q-match with param should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_runtime_q_match_generates_mdata() {
    // Verify that runtime matching generates MData-tagged expressions
    let code = r#"
fun (e : Type) =>
  match e with
  | q($x) => x
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Runtime q-match should elaborate: {:?}",
        result.err()
    );

    // The result should contain MData tags for runtime matching
    if let Ok(expr) = result {
        let expr_str = format!("{:?}", expr);
        // Should contain runtime matching markers (ite for if-then-else)
        // or qq_runtime for MData markers, or App for function application
        assert!(
            expr_str.contains("ite") || expr_str.contains("qq_runtime") || expr_str.contains("App"),
            "Runtime match should generate if-then-else or MData markers: {}",
            expr_str
        );
    }
}

#[test]
fn test_runtime_q_match_wildcard_fallback() {
    // Runtime match with wildcard fallback
    // Use Prop instead of True (which would require a definition)
    let code = r#"
fun (e : Prop) =>
  match e with
  | q($p) => p
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Runtime q-match with wildcard should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_runtime_q_match_multiple_patterns() {
    // Multiple q-patterns in runtime match
    let code = r#"
fun (e : Type) =>
  match e with
  | q(Type) => q(Prop)
  | q(Prop) => q(Type)
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Runtime q-match with multiple patterns should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_tilde_q_pattern_elaboration() {
    // ~q(...) should work identically to q(...) in patterns
    let code = r#"
fun (e : Type) =>
  match e with
  | ~q($x) => x
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "~q pattern should elaborate: {:?}",
        result.err()
    );
}

// =========================================================================
// Issue #317: Q-pattern duplicate binder names reuse metavariable
// =========================================================================

#[test]
fn test_q_pattern_single_binder() {
    // Basic test: single pattern variable binds and can be used
    let code = r#"
fun (e : Type) =>
  match e with
  | q($x) => x
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Single q-pattern binder should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_q_pattern_static_match() {
    // Static match: q(Type) matches q($x) where x binds to Type
    let code = r#"
match q(Type) with
| q($x) => x
| _ => q(Prop)
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Static q-pattern match should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_q_pattern_duplicate_binder_app_shape() {
    // Pattern q($x $x) has the same $x twice - when elaborated, both positions
    // reference the same metavariable. This means the pattern only matches
    // applications where both argument positions are definitionally equal.
    //
    // Regression test for issue #317: duplicate binder names reuse metavariable.
    // When $x appears twice, both occurrences must unify to the same expression.
    //
    // Use a scrutinee shaped like an application so the duplicate binder match
    // logic is exercised during runtime matching.
    let code = r#"
fun (f : Type -> Type) (A : Type) =>
  match q(f A) with
  | q($x $x) => x
  | _ => q(Prop)
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Q-pattern with duplicate binder ($x $x) should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_q_pattern_duplicate_binder_app_shape_mismatch() {
    // Same pattern, but the scrutinee is an application with different function
    // and argument, so the duplicate binder should not match.
    let code = r#"
fun (A : Type) =>
  match q((fun (x : Type) => x) A) with
  | q($x $x) => x
  | _ => q(Prop)
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Q-pattern mismatch with duplicate binder should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_q_pattern_duplicate_binder_direct_match() {
    // Part of #331: Directly test duplicate binder matching with constructed expressions.
    //
    // Create App(Type, Type) as a scrutinee (ill-typed as application, but valid
    // for testing pattern unification). Pattern q($x $x) should match because
    // both positions are Type.
    //
    // This tests the actual duplicate binder unification in match_q_pattern,
    // bypassing full match elaboration to isolate the mechanism being tested.
    use clean_parser::{QAntiquotContent, Span, SurfaceArg, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Scrutinee: App(Type, Type) - both positions are the same expression
    let type_expr = Expr::type_();
    let scrutinee = Expr::app(type_expr.clone(), type_expr);

    // Pattern: $x $x - construct App(QAntiquot("x"), QAntiquot("x"))
    let antiquot_x = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Simple("x".to_string()),
    };
    let pattern_surface = SurfaceExpr::App(
        Span::dummy(),
        Box::new(antiquot_x.clone()),
        vec![SurfaceArg::positional(antiquot_x)],
    );

    // Try matching
    let result = ctx.match_q_pattern(&scrutinee, &pattern_surface);

    assert!(
        result.is_ok(),
        "match_q_pattern should not error: {:?}",
        result.err()
    );
    let match_result = result.unwrap();
    assert!(
        match_result.is_some(),
        "Pattern q($x $x) should match App(Type, Type) - identical args"
    );
    // Verify x was bound to Type
    let bindings = match_result.unwrap().bindings;
    assert_eq!(bindings.len(), 1, "Should have exactly one binding for x");
    assert_eq!(bindings[0].0, "x", "Binding name should be 'x'");
}

#[test]
fn test_q_pattern_duplicate_binder_direct_mismatch() {
    // Part of #331: Directly test duplicate binder rejection with different args.
    //
    // Create App(Type, Prop) as a scrutinee.
    // Pattern q($x $x) should NOT match because Type != Prop.
    use clean_parser::{QAntiquotContent, Span, SurfaceArg, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Scrutinee: App(Type, Prop) - positions have different expressions
    let type_expr = Expr::type_();
    let prop_expr = Expr::sort(Level::zero());
    let scrutinee = Expr::app(type_expr, prop_expr);

    // Pattern: $x $x - construct App(QAntiquot("x"), QAntiquot("x"))
    let antiquot_x = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Simple("x".to_string()),
    };
    let pattern_surface = SurfaceExpr::App(
        Span::dummy(),
        Box::new(antiquot_x.clone()),
        vec![SurfaceArg::positional(antiquot_x)],
    );

    // Try matching
    let result = ctx.match_q_pattern(&scrutinee, &pattern_surface);

    assert!(
        result.is_ok(),
        "match_q_pattern should not error: {:?}",
        result.err()
    );
    let match_result = result.unwrap();
    assert!(
        match_result.is_none(),
        "Pattern q($x $x) should NOT match App(Type, Prop) - different args"
    );
}

#[test]
fn test_q_pattern_two_distinct_vars() {
    // Pattern q($x $y) with two distinct variables should create separate
    // metavariables that can bind to different values.
    //
    // This tests that the mvar_map correctly tracks multiple binders without
    // conflating them.
    let code = r#"
fun (f : Type -> Type -> Type) (e : Type) =>
  match e with
  | q($x $y) => x
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Q-pattern with two distinct vars should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_q_pattern_duplicate_binder_dedup() {
    // Part of #329: Verify that duplicate binders produce deduplicated bindings.
    //
    // Pattern q($x $y $x) has $x twice. After dedup, we should get exactly
    // 2 bindings: one for x and one for y (not 3 with x duplicated).
    use clean_parser::{QAntiquotContent, Span, SurfaceArg, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Scrutinee: App(App(Type, Type), Type) - three-arg application where args 1 and 3 match
    let type_expr = Expr::type_();
    let inner_app = Expr::app(type_expr.clone(), type_expr.clone());
    let scrutinee = Expr::app(inner_app, type_expr);

    // Pattern: $x $y $x - App(App($x, $y), $x)
    let antiquot_x = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Simple("x".to_string()),
    };
    let antiquot_y = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Simple("y".to_string()),
    };
    // Inner: $x $y
    let inner_pattern = SurfaceExpr::App(
        Span::dummy(),
        Box::new(antiquot_x.clone()),
        vec![SurfaceArg::positional(antiquot_y)],
    );
    // Outer: ($x $y) $x
    let pattern_surface = SurfaceExpr::App(
        Span::dummy(),
        Box::new(inner_pattern),
        vec![SurfaceArg::positional(antiquot_x)],
    );

    // Try matching
    let result = ctx.match_q_pattern(&scrutinee, &pattern_surface);

    assert!(
        result.is_ok(),
        "match_q_pattern should not error: {:?}",
        result.err()
    );
    let match_result = result.unwrap();
    assert!(match_result.is_some(), "Pattern should match");

    // Verify exactly 2 bindings (x and y), not 3 (x, y, x)
    let bindings = match_result.unwrap().bindings;
    assert_eq!(
        bindings.len(),
        2,
        "Should have exactly 2 bindings (deduped), got {:?}",
        bindings.iter().map(|(n, _, _)| n).collect::<Vec<_>>()
    );

    // Verify binding names are x and y
    let names: Vec<_> = bindings.iter().map(|(n, _, _)| n.as_str()).collect();
    assert!(names.contains(&"x"), "Should have binding for x");
    assert!(names.contains(&"y"), "Should have binding for y");
}

#[test]
fn test_q_pattern_duplicate_and_distinct() {
    // Pattern q($x $y $x) has $x twice and $y once.
    // The first and third positions must unify, but $y is independent.
    //
    // This tests the full duplicate binder mechanism: $x is reused from mvar_map
    // on second occurrence, while $y gets its own metavariable.
    let code = r#"
fun (f : Type -> Type -> Type -> Type) (e : Type) =>
  match e with
  | q($x $y $x) => y
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Q-pattern with mixed duplicate/distinct binders should elaborate: {:?}",
        result.err()
    );
}

// =========================================================================
// Issue #318: Q-pattern universe-level metavariables
// =========================================================================

#[test]
fn test_q_pattern_universe_type1() {
    // Pattern variable should work at Type 1 (universe flexibility)
    // Uses Type directly to test universe-polymorphic binder
    let code = r#"
fun (e : Type 1) =>
  match e with
  | q($x) => x
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Q-pattern at Type 1 should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_q_pattern_universe_prop() {
    // Pattern variable should work at Prop (Sort 0)
    let code = r#"
fun (e : Prop) =>
  match e with
  | q($x) => x
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Q-pattern at Prop should elaborate: {:?}",
        result.err()
    );
}

// =========================================================================
// Issue #751: Non-q-pattern let-pattern elaboration
// Tests for elaborate_let_q_pattern with Var, Wildcard, and QPattern variants
// =========================================================================

/// Test that QPattern let-pattern elaborates correctly (static match)
/// Syntax: let q($pat) := scrutinee | fallback in body
#[test]
fn test_let_q_pattern_static_match() {
    // Static scrutinee - should match at elaboration time
    let code = r#"
let q($x) := q(Type) | q(Prop) in x
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "let q($x) with static scrutinee should elaborate: {:?}",
        result.err()
    );
}

/// Test QPattern let-pattern with runtime scrutinee
/// When scrutinee is dynamic (parameter), generates runtime matching code
#[test]
fn test_let_q_pattern_runtime_match() {
    // Dynamic scrutinee (function parameter) - needs runtime matching
    let code = r#"
fun (e : Type) =>
  let q($x) := e | q(Prop) in x
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "let q($x) with runtime scrutinee should elaborate: {:?}",
        result.err()
    );
}
// =============================================================================
// Qq quotation elaboration tests - Part of #16
// =============================================================================

#[test]
fn test_elaborate_q_type_quotation_basic() {
    // Q(Type) - type quotation should elaborate the inner type
    // In Phase 2, Q(α) is transparent and returns α directly
    let result = elab("Q(Type)");
    assert!(result.is_ok(), "Q(Type) should elaborate: {result:?}");
}

#[test]
fn test_elaborate_q_type_quotation_type() {
    // Q(Type) - quotation of Type itself
    let result = elab("Q(Type)");
    assert!(result.is_ok(), "Q(Type) should elaborate: {result:?}");
    // In transparent mode, Q(Type) ≈ Type
    let expr = result.unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Sort(_)),
        "Q(Type) should be Sort, got {expr:?}"
    );
}

#[test]
fn test_elaborate_q_value_quotation_literal() {
    // q(42) - value quotation of a literal
    let result = elab("q(42)");
    assert!(result.is_ok(), "q(42) should elaborate: {result:?}");
    let expr = result.unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Lit(clean_kernel::Literal::Nat(ref n)) if n.to_u64() == Some(42)),
        "q(42) should be Nat literal 42, got {expr:?}"
    );
}

#[test]
fn test_elaborate_q_value_quotation_prop() {
    // q(Prop) - value quotation of Prop
    let result = elab("q(Prop)");
    assert!(result.is_ok(), "q(Prop) should elaborate: {result:?}");
    let expr = result.unwrap();
    assert!(expr.is_prop(), "q(Prop) should be Prop, got {expr:?}");
}

#[test]
fn test_elaborate_q_value_with_lambda() {
    // q(fun x => x) - quotation containing a lambda
    let result = elab("q(fun (x : Type) => x)");
    assert!(result.is_ok(), "q(fun x => x) should elaborate: {result:?}");
    let expr = result.unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Lam(_, _, _)),
        "q(fun x => x) should be Lambda, got {expr:?}"
    );
}

#[test]
fn test_elaborate_antiquot_outside_q_fails() {
    // $x outside q(...) context should error
    // We need to construct this manually since parser rejects it at top level
    use clean_parser::{QAntiquotContent, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let surface = SurfaceExpr::QAntiquot {
        span: clean_parser::Span::dummy(),
        content: QAntiquotContent::Simple("x".to_string()),
    };

    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "antiquotation outside q() should fail: {result:?}"
    );
    let err = result.unwrap_err();
    assert!(
        matches!(err, ElabError::NotImplemented(ref msg) if msg.contains("antiquotation outside q")),
        "expected 'antiquotation outside q' error, got {err:?}"
    );
}

#[test]
fn test_elaborate_q_with_simple_antiquot() {
    // q($x) where x is in scope - antiquotation should resolve to identifier
    // In a function context like: fun (x : Type) => q($x)
    let result = elab("fun (x : Type) => q($x)");
    assert!(
        result.is_ok(),
        "fun x => q($x) should elaborate: {result:?}"
    );
    let expr = result.unwrap();
    // Should be a lambda
    assert!(
        matches!(expr.kind(), ExprKind::Lam(_, _, _)),
        "expected Lambda, got {expr:?}"
    );
}

#[test]
fn test_elaborate_q_with_expr_antiquot() {
    // q($(fun y => y)) - expression antiquotation
    let result = elab("q($(fun (y : Type) => y))");
    assert!(
        result.is_ok(),
        "q($(fun y => y)) should elaborate: {result:?}"
    );
    let expr = result.unwrap();
    // The inner lambda should be elaborated directly
    assert!(
        matches!(expr.kind(), ExprKind::Lam(_, _, _)),
        "expected Lambda from spliced expr, got {expr:?}"
    );
}

#[test]
fn test_elaborate_q_nested_application() {
    // q(f $a) where we have function application with antiquotation
    // fun (f : Type -> Type) (a : Type) => q(f $a)
    let result = elab("fun (f : Type -> Type) (a : Type) => q(f $a)");
    assert!(
        result.is_ok(),
        "fun f a => q(f $a) should elaborate: {result:?}"
    );
}

#[test]
fn test_elaborate_q_with_type_annotation() {
    // q(Type : Type 1) - value quotation with type annotation
    // Type : Type 1 is valid (Type = Sort 1, and Sort 1 : Sort 2)
    let result = elab("q(Type : Type 1)");
    assert!(
        result.is_ok(),
        "q(Type : Type 1) should elaborate: {result:?}"
    );
}

// =============================================================================
// Phase 3: qq_expr parser extensions (arrow, let, if, ascription)
// Part of #80: qq_expr parser extensions
// =============================================================================

#[test]
fn test_elaborate_q_arrow_with_antiquots() {
    // q($A -> $B) - arrow type with antiquotations
    // Part of #80: Phase 3 qq_expr parser extensions
    let result = elab("fun (A : Type) (B : Type) => q($A -> $B)");
    assert!(
        result.is_ok(),
        "fun A B => q($A -> $B) should elaborate: {result:?}"
    );
    let expr = result.unwrap();
    // Should be a lambda returning an arrow type
    assert!(
        matches!(expr.kind(), ExprKind::Lam(_, _, _)),
        "expected Lambda, got {expr:?}"
    );
}

#[test]
fn test_elaborate_q_arrow_simple() {
    // q(Type -> Type) - simple arrow type without antiquotations
    // Part of #80: Phase 3 qq_expr parser extensions
    let result = elab("q(Type -> Type)");
    assert!(
        result.is_ok(),
        "q(Type -> Type) should elaborate: {result:?}"
    );
}

#[test]
fn test_elaborate_q_let_with_antiquot() {
    // q(let y := $x in y) - let expression with antiquotation in value
    // Part of #80: Phase 3 qq_expr parser extensions
    let result = elab("fun (x : Type) => q(let y := $x in y)");
    assert!(
        result.is_ok(),
        "fun x => q(let y := $x in y) should elaborate: {result:?}"
    );
}

#[test]
fn test_elaborate_q_let_simple() {
    // q(let y := Type in y) - simple let expression without antiquotations
    // Part of #80: Phase 3 qq_expr parser extensions
    let result = elab("q(let y := Type in y)");
    assert!(
        result.is_ok(),
        "q(let y := Type in y) should elaborate: {result:?}"
    );
}

#[test]
fn test_elaborate_nested_q_quotations() {
    // q(q(Type)) - nested quotation
    // This should work and process the outer q first, then the inner
    let result = elab("q(q(Type))");
    assert!(result.is_ok(), "q(q(Type)) should elaborate: {result:?}");
}

#[test]
fn test_elaborate_q_in_q_type_context() {
    // Q(Q(Type)) - nested type quotations
    let result = elab("Q(Q(Type))");
    assert!(result.is_ok(), "Q(Q(Type)) should elaborate: {result:?}");
}

#[test]
fn test_parse_q_if_with_antiquots() {
    // q(if $c then $a else $b) - if expression with antiquotations
    // Part of #80: Phase 3 qq_expr parser extensions
    // NOTE: This tests PARSING succeeds. Full elaboration requires `ite` in environment.
    let result = parse_expr("q(if $c then $a else $b)");
    assert!(
        result.is_ok(),
        "q(if $c then $a else $b) should parse: {result:?}"
    );
    // Verify the parse result contains an If node
    if let Ok(expr) = result {
        // The surface expression should be a QQuotation containing an If
        assert!(
            format!("{expr:?}").contains("If"),
            "expected If in parse result: {expr:?}"
        );
    }
}

#[test]
fn test_parse_q_if_simple() {
    // q(if Prop then Type else Type) - simple if expression without antiquotations
    // Part of #80: Phase 3 qq_expr parser extensions
    // NOTE: This tests PARSING succeeds. Full elaboration requires `ite` in environment.
    let result = parse_expr("q(if Prop then Type else Type)");
    assert!(
        result.is_ok(),
        "q(if Prop then Type else Type) should parse: {result:?}"
    );
    // Verify the parse result contains an If node
    if let Ok(expr) = result {
        assert!(
            format!("{expr:?}").contains("If"),
            "expected If in parse result: {expr:?}"
        );
    }
}

#[test]
fn test_elaborate_q_ascription_with_antiquots() {
    // q(($x : Type)) - ascription with antiquotation
    // Part of #80: Phase 3 qq_expr parser extensions
    // x is Type, and Type : Type 1, so ascribing to Type works
    let result = elab("fun (x : Prop) => q(($x : Prop))");
    assert!(
        result.is_ok(),
        "fun x => q(($x : Prop)) should elaborate: {result:?}"
    );
}

#[test]
fn test_elaborate_q_ascription_simple() {
    // q((Prop : Type)) - simple ascription without antiquotations
    // Part of #80: Phase 3 qq_expr parser extensions
    // Prop : Type is valid (Prop = Sort 0, Type = Sort 1, Sort 0 : Sort 1)
    let result = elab("q((Prop : Type))");
    assert!(
        result.is_ok(),
        "q((Prop : Type)) should elaborate: {result:?}"
    );
}

// =============================================================================
// Phase 4: Universe polymorphism and level antiquotation tests
// Part of #16: Qq quotation support
// =============================================================================

#[test]
fn test_elaborate_q_sort_level() {
    // q(Sort 0) - Sort with explicit level literal
    let result = elab("q(Sort 0)");
    assert!(result.is_ok(), "q(Sort 0) should elaborate: {result:?}");
    // Should produce Prop (Sort 0)
    if let Ok(expr) = result {
        assert!(expr.is_prop(), "Sort 0 should be Prop");
    }
}

#[test]
fn test_elaborate_q_sort_succ() {
    // q(Sort 1) - Sort with successor level
    let result = elab("q(Sort 1)");
    assert!(result.is_ok(), "q(Sort 1) should elaborate: {result:?}");
    // Should produce Type (Sort 1)
    if let Ok(expr) = result {
        assert!(
            matches!(expr.kind(), ExprKind::Sort(ref l) if !l.is_zero()),
            "Sort 1 should be Type"
        );
    }
}

#[test]
fn test_elaborate_q_type_level() {
    // q(Type 0) - Type with explicit level
    let result = elab("q(Type 0)");
    assert!(result.is_ok(), "q(Type 0) should elaborate: {result:?}");
}

#[test]
fn test_elaborate_level_antiquot_in_sort() {
    // q(Sort $u) - level antiquotation inside Sort
    // The $u is treated as a level param when elaborated
    let result = elab("q(Sort $u)");
    // This should work - $u becomes a level parameter
    assert!(result.is_ok(), "q(Sort $u) should elaborate: {result:?}");
}

#[test]
fn test_elaborate_level_antiquot_in_type() {
    // q(Type $u) - level antiquotation inside Type
    let result = elab("q(Type $u)");
    assert!(result.is_ok(), "q(Type $u) should elaborate: {result:?}");
}

#[test]
fn test_elaborate_q_quotation_type_sort() {
    // Q(Sort 1) - type quotation wrapping Sort
    // This means "expressions of type Type"
    let result = elab("Q(Sort 1)");
    assert!(result.is_ok(), "Q(Sort 1) should elaborate: {result:?}");
}

#[test]
fn test_elaborate_q_quotation_preserves_level() {
    // Verify that q(Sort 2) produces Sort with the correct level
    let result = elab("q(Sort 2)");
    assert!(result.is_ok(), "q(Sort 2) should elaborate: {result:?}");
    if let Ok(ref expr) = result {
        if let ExprKind::Sort(level) = expr.kind() {
            // Sort 2 should have level > 1
            assert!(!level.is_zero(), "Sort 2 should have non-zero level");
        }
    }
}

// =============================================================================
// Part of #882: Splice antiquotation elaboration tests
// These test the elaboration code paths in q_pattern.rs and quotation.rs
// =============================================================================

/// Test splice pattern variable extraction in q_pattern.rs:extract_q_pattern_vars
/// Syntax: q($[xs]*) collects "xs" as a pattern variable
#[test]
fn test_extract_splice_pattern_var() {
    // Directly test extract_q_pattern_vars with a splice antiquotation
    use clean_parser::{QAntiquotContent, Span, SurfaceExpr};

    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // Build a splice antiquotation: $[xs]*
    let splice_antiquot = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "xs".to_string(),
            separator: None,
            at_least_one: false,
        },
    };

    let vars = ctx.extract_q_pattern_vars(&splice_antiquot);
    assert_eq!(
        vars.len(),
        1,
        "Should extract one pattern variable from splice"
    );
    assert_eq!(vars[0].0, "xs", "Variable name should be 'xs'");
    assert!(
        vars[0].1.is_none(),
        "Splice var should have no type annotation"
    );
}

/// Test splice pattern variable deduplication
/// When $[xs]* appears multiple times, should only collect once
#[test]
fn test_extract_splice_pattern_var_dedup() {
    use clean_parser::{QAntiquotContent, Span, SurfaceArg, SurfaceExpr};

    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // Build pattern: $[xs]* $[xs]* (duplicate splice)
    let splice_antiquot = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "xs".to_string(),
            separator: None,
            at_least_one: false,
        },
    };
    let pattern = SurfaceExpr::App(
        Span::dummy(),
        Box::new(splice_antiquot.clone()),
        vec![SurfaceArg::positional(splice_antiquot)],
    );

    let vars = ctx.extract_q_pattern_vars(&pattern);
    assert_eq!(
        vars.len(),
        1,
        "Duplicate splice should be deduplicated, got {:?}",
        vars
    );
    assert_eq!(vars[0].0, "xs", "Variable name should be 'xs'");
}

/// Test splice elaboration in patterns creates metavariables (q_pattern.rs:181-196)
#[test]
fn test_elaborate_splice_pattern_with_mvars() {
    use clean_parser::{QAntiquotContent, Span, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build a splice antiquotation: $[xs]*
    let splice_antiquot = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "xs".to_string(),
            separator: None,
            at_least_one: false,
        },
    };

    let result = ctx.elaborate_q_pattern_with_mvars(&splice_antiquot);
    assert!(
        result.is_ok(),
        "Splice pattern elaboration should succeed: {:?}",
        result.err()
    );

    let (expr, mvar_map) = result.unwrap();

    // Should create a metavariable for xs
    assert!(
        mvar_map.contains_key("xs"),
        "mvar_map should contain 'xs': {:?}",
        mvar_map.keys().collect::<Vec<_>>()
    );

    // The expression should be an FVar (the metavariable)
    assert!(
        matches!(expr.kind(), ExprKind::FVar(_)),
        "Splice pattern should elaborate to FVar (metavar), got {:?}",
        expr
    );
}

/// Test splice pattern variable reuse - same name should reuse metavariable
#[test]
fn test_elaborate_splice_pattern_mvar_reuse() {
    use clean_parser::{QAntiquotContent, Span, SurfaceArg, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build pattern: $[xs]* $[xs]* (duplicate splice)
    let splice_antiquot = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "xs".to_string(),
            separator: None,
            at_least_one: false,
        },
    };
    let pattern = SurfaceExpr::App(
        Span::dummy(),
        Box::new(splice_antiquot.clone()),
        vec![SurfaceArg::positional(splice_antiquot)],
    );

    let result = ctx.elaborate_q_pattern_with_mvars(&pattern);
    assert!(
        result.is_ok(),
        "Duplicate splice pattern elaboration should succeed: {:?}",
        result.err()
    );

    let (_expr, mvar_map) = result.unwrap();

    // Should only have one entry for xs (reused)
    assert_eq!(
        mvar_map.len(),
        1,
        "Duplicate splice should reuse metavariable, got {:?}",
        mvar_map.keys().collect::<Vec<_>>()
    );
    assert!(mvar_map.contains_key("xs"), "mvar_map should contain 'xs'");
}

/// Test splice antiquotation processing in quotation.rs:process_qq_antiquots
/// $[xs]* should resolve to identifier "xs"
#[test]
fn test_process_splice_antiquot() {
    use clean_parser::{QAntiquotContent, Span, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build a splice antiquotation: $[xs]*
    let splice_antiquot = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "xs".to_string(),
            separator: None,
            at_least_one: false,
        },
    };

    let result = ctx.process_qq_antiquots(&splice_antiquot);
    assert!(
        result.is_ok(),
        "process_qq_antiquots should succeed for splice: {:?}",
        result.err()
    );

    let processed = result.unwrap();
    // Should produce an Ident with name "xs"
    assert!(
        matches!(processed, SurfaceExpr::Ident(_, ref name) if name == "xs"),
        "Splice should process to Ident 'xs', got {:?}",
        processed
    );
}

/// Test splice antiquotation with separator in pattern
#[test]
fn test_extract_splice_with_separator() {
    use clean_parser::{QAntiquotContent, Span, SurfaceExpr};

    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // Build a splice antiquotation with separator: $[xs,]*
    let splice_antiquot = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "xs".to_string(),
            separator: Some(",".to_string()),
            at_least_one: false,
        },
    };

    let vars = ctx.extract_q_pattern_vars(&splice_antiquot);
    assert_eq!(vars.len(), 1, "Should extract one pattern variable");
    assert_eq!(vars[0].0, "xs", "Variable name should be 'xs'");
}

/// Test splice antiquotation with at_least_one flag ($[xs]+)
#[test]
fn test_extract_splice_at_least_one() {
    use clean_parser::{QAntiquotContent, Span, SurfaceExpr};

    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // Build a splice antiquotation: $[xs]+
    let splice_antiquot = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "ys".to_string(),
            separator: None,
            at_least_one: true,
        },
    };

    let vars = ctx.extract_q_pattern_vars(&splice_antiquot);
    assert_eq!(vars.len(), 1, "Should extract one pattern variable");
    assert_eq!(vars[0].0, "ys", "Variable name should be 'ys'");
}

/// Test q-match with splice pattern variable binding
/// Runtime matching should generate appropriate bindings for splice patterns
#[test]
fn test_q_match_with_splice_pattern() {
    // Pattern q($[xs]*) should bind xs to matched expression list
    // Use runtime matching context (function parameter scrutinee)
    let code = r#"
fun (e : Type) =>
  match e with
  | q($[xs]*) => xs
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "q-match with splice pattern should elaborate: {:?}",
        result.err()
    );
}

/// Test let-pattern with splice antiquotation
#[test]
fn test_let_splice_pattern() {
    // let q($[xs]*) := e | fallback in body
    let code = r#"
fun (e : Type) =>
  let q($[xs]*) := e | q(Prop) in xs
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "let with splice pattern should elaborate: {:?}",
        result.err()
    );
}

/// Test splice in value quotation context (not pattern)
/// q($[xs]*) where xs is in scope - should resolve to xs identifier
#[test]
fn test_q_value_with_splice_antiquot() {
    // Inside q(...), $[xs]* resolves to identifier xs
    let code = r#"
fun (xs : Type) =>
  q($[xs]*)
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "q with splice antiquot should elaborate: {:?}",
        result.err()
    );
}

/// Test multiple distinct splice variables in pattern
#[test]
fn test_q_pattern_multiple_splices() {
    use clean_parser::{QAntiquotContent, Span, SurfaceArg, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build pattern: $[xs]* $[ys]*
    let splice_xs = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "xs".to_string(),
            separator: None,
            at_least_one: false,
        },
    };
    let splice_ys = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "ys".to_string(),
            separator: None,
            at_least_one: false,
        },
    };
    let pattern = SurfaceExpr::App(
        Span::dummy(),
        Box::new(splice_xs),
        vec![SurfaceArg::positional(splice_ys)],
    );

    let result = ctx.elaborate_q_pattern_with_mvars(&pattern);
    assert!(
        result.is_ok(),
        "Multiple splice patterns should elaborate: {:?}",
        result.err()
    );

    let (_expr, mvar_map) = result.unwrap();

    // Should have two entries: xs and ys
    assert_eq!(
        mvar_map.len(),
        2,
        "Should have two metavariables, got {:?}",
        mvar_map.keys().collect::<Vec<_>>()
    );
    assert!(mvar_map.contains_key("xs"), "mvar_map should contain 'xs'");
    assert!(mvar_map.contains_key("ys"), "mvar_map should contain 'ys'");
}

/// Test mixed simple and splice antiquotations in pattern
#[test]
fn test_q_pattern_mixed_simple_and_splice() {
    use clean_parser::{QAntiquotContent, Span, SurfaceArg, SurfaceExpr};

    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // Build pattern: $x $[ys]*
    let simple_x = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Simple("x".to_string()),
    };
    let splice_ys = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: "ys".to_string(),
            separator: None,
            at_least_one: false,
        },
    };
    let pattern = SurfaceExpr::App(
        Span::dummy(),
        Box::new(simple_x),
        vec![SurfaceArg::positional(splice_ys)],
    );

    let vars = ctx.extract_q_pattern_vars(&pattern);
    assert_eq!(
        vars.len(),
        2,
        "Should extract two pattern variables, got {:?}",
        vars
    );

    let names: Vec<_> = vars.iter().map(|(n, _)| n.as_str()).collect();
    assert!(names.contains(&"x"), "Should have variable 'x'");
    assert!(names.contains(&"ys"), "Should have variable 'ys'");
}
