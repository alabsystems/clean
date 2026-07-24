// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 Parser Feature Tests
//!
//! Comprehensive test suite for Lean 4 syntax coverage.
//! Phase 0.1 of Feature Verification Roadmap.
//!
//! Coverage tracked in `docs/PARSER_COVERAGE.md`
//!
//! Note: This module is conditionally compiled via #[cfg(test)] in lib.rs

use crate::{parse_decl, parse_expr, parse_file, SurfaceExpr, SurfaceTactic};

/// Helper to track test results
fn check(name: &str, result: Result<impl std::fmt::Debug, impl std::fmt::Debug>) -> bool {
    match &result {
        Ok(_) => {
            println!("  PASS: {name}");
            true
        }
        Err(e) => {
            println!("  FAIL: {name} - {e:?}");
            false
        }
    }
}

/// Helper for negative tests (should fail to parse)
fn check_reject(name: &str, result: Result<impl std::fmt::Debug, impl std::fmt::Debug>) -> bool {
    if result.is_ok() {
        println!("  FAIL: {name} - expected rejection, got success");
        false
    } else {
        println!("  PASS: {name} (correctly rejected)");
        true
    }
}

// ============================================================================
// Section 1: Universe Levels
// ============================================================================

mod universe_levels {
    use super::*;

    #[test]
    fn type_universe() {
        assert!(check("Type", parse_expr("Type")));
        assert!(check("Type 0", parse_expr("Type 0")));
        assert!(check("Type 1", parse_expr("Type 1")));
        assert!(check("Type u", parse_expr("Type u")));
        assert!(check("Type (u + 1)", parse_expr("Type (u + 1)")));
        assert!(check("Type (max u v)", parse_expr("Type (max u v)")));
        assert!(check("Type (imax u v)", parse_expr("Type (imax u v)")));
    }

    #[test]
    fn sort_universe() {
        assert!(check("Sort", parse_expr("Sort")));
        assert!(check("Sort 0", parse_expr("Sort 0")));
        assert!(check("Sort 1", parse_expr("Sort 1")));
        assert!(check("Sort u", parse_expr("Sort u")));
        assert!(check("Sort (u + 1)", parse_expr("Sort (u + 1)")));
    }

    #[test]
    fn prop() {
        assert!(check("Prop", parse_expr("Prop")));
    }

    #[test]
    fn universe_declaration() {
        assert!(check("universe u", parse_file("universe u")));
        assert!(check("universe u v", parse_file("universe u v")));
        assert!(check("universe u v w", parse_file("universe u v w")));
    }

    #[test]
    fn universe_polymorphism() {
        assert!(check(
            "def with universe",
            parse_file("universe u\ndef foo : Type u := sorry")
        ));
        assert!(check(
            "forall with Type u",
            parse_expr("forall (α : Type u), α → α")
        ));
    }
}

// ============================================================================
// Section 2: Binders
// ============================================================================

mod binders {
    use super::*;

    #[test]
    fn explicit_binder() {
        assert!(check("(x : Nat)", parse_expr("fun (x : Nat) => x")));
        assert!(check("(x y : Nat)", parse_expr("fun (x y : Nat) => x")));
        assert!(check(
            "(x : Nat) (y : Nat)",
            parse_expr("fun (x : Nat) (y : Nat) => x")
        ));
    }

    #[test]
    fn implicit_binder() {
        assert!(check("{x : Nat}", parse_expr("fun {x : Nat} => x")));
        assert!(check("{x y : Nat}", parse_expr("fun {x y : Nat} => x")));
    }

    #[test]
    fn instance_implicit_binder() {
        assert!(check("[x : Nat]", parse_expr("fun [x : Nat] => x")));
        assert!(check(
            "[ToString α]",
            parse_decl("def foo [ToString α] (x : α) : String := sorry")
        ));
    }

    #[test]
    fn strict_implicit_binder() {
        // {{x : T}} - strict implicit binders
        assert!(check("{{x : Nat}}", parse_expr("fun {{x : Nat}} => x")));
    }

    #[test]
    fn anonymous_binder() {
        assert!(check("(_ : Nat)", parse_expr("fun (_ : Nat) => 0")));
    }

    #[test]
    fn binder_without_type() {
        assert!(check("(x)", parse_expr("fun x => x")));
        assert!(check("fun x y", parse_expr("fun x y => x")));
    }
}

// ============================================================================
// Section 3: Lambda Expressions
// ============================================================================

mod lambda {
    use super::*;

    #[test]
    fn simple_lambda() {
        assert!(check("fun x => x", parse_expr("fun x => x")));
        assert!(check("λ x => x", parse_expr("λ x => x")));
    }

    #[test]
    fn typed_lambda() {
        assert!(check(
            "fun (x : Nat) => x",
            parse_expr("fun (x : Nat) => x")
        ));
    }

    #[test]
    fn multi_arg_lambda() {
        assert!(check("fun x y => x", parse_expr("fun x y => x")));
        assert!(check("fun x y z => x", parse_expr("fun x y z => x")));
    }

    #[test]
    fn nested_lambda() {
        assert!(check(
            "fun x => fun y => x",
            parse_expr("fun x => fun y => x")
        ));
    }

    #[test]
    fn pattern_lambda() {
        // fun | pat => body
        assert!(check("fun | 0 => 1", parse_expr("fun | 0 => 1")));
        assert!(check(
            "fun | 0 => 1 | n => n",
            parse_expr("fun | 0 => 1 | n => n")
        ));
    }

    #[test]
    fn multi_pattern_lambda() {
        // Multi-pattern (comma-separated) match-lambda arms: `fun | p1, p2 => e`.
        assert!(check(
            "fun | 0, 0 => 0 | _, _ => 1",
            parse_expr("fun | 0, 0 => 0 | _, _ => 1")
        ));
        assert!(check(
            "fun | 0, 0, 0 => 0 | _, _, _ => 1",
            parse_expr("fun | 0, 0, 0 => 0 | _, _, _ => 1")
        ));
    }

    #[test]
    fn lambda_with_hole() {
        assert!(check("fun (x : _) => x", parse_expr("fun (x : _) => x")));
    }
}

// ============================================================================
// Section 4: Application
// ============================================================================

mod application {
    use super::*;

    #[test]
    fn simple_app() {
        assert!(check("f x", parse_expr("f x")));
        assert!(check("f x y", parse_expr("f x y")));
    }

    #[test]
    fn parenthesized_arg() {
        assert!(check("f (x)", parse_expr("f (x)")));
        assert!(check("f (g x)", parse_expr("f (g x)")));
    }

    #[test]
    fn explicit_app() {
        assert!(check("@f x", parse_expr("@f x")));
        assert!(check("@id Nat 0", parse_expr("@id Nat 0")));
    }

    #[test]
    fn named_argument() {
        assert!(check("f (x := 1)", parse_expr("f (x := 1)")));
    }

    #[test]
    fn forward_pipe() {
        // `x |> f` (application) and `x |>.foo` (projection), plus chaining.
        assert!(check("n |> f", parse_expr("n |> f")));
        assert!(check("n |> (· + 1)", parse_expr("n |> (· + 1)")));
        assert!(check("n |>.succ", parse_expr("n |>.succ")));
        assert!(check("n |> f |> g", parse_expr("n |> f |> g")));
        assert!(check("n |>.succ |>.succ", parse_expr("n |>.succ |>.succ")));
    }

    #[test]
    fn partial_app() {
        // · for partial application placeholder
        assert!(check("f · y", parse_expr("f · y")));
        assert!(check("· + 1", parse_expr("· + 1")));
    }
}

// ============================================================================
// Section 5: Let Expressions
// ============================================================================

mod let_expr {
    use super::*;

    #[test]
    fn simple_let() {
        assert!(check("let x := 1; x", parse_expr("let x := 1; x")));
        assert!(check("let x := 1 in x", parse_expr("let x := 1 in x")));
    }

    #[test]
    fn typed_let() {
        assert!(check(
            "let x : Nat := 1; x",
            parse_expr("let x : Nat := 1; x")
        ));
    }

    #[test]
    fn chained_let() {
        assert!(check(
            "let x := 1; let y := 2; x + y",
            parse_expr("let x := 1; let y := 2; x + y")
        ));
    }

    #[test]
    fn let_rec() {
        assert!(check(
            "let rec f := ...",
            parse_expr("let rec f (n : Nat) : Nat := match n with | 0 => 1 | _ => f 0; f 5")
        ));
    }

    #[test]
    fn let_fun() {
        // let fun is shorthand for let with lambda
        assert!(check("let f x := x; f 0", parse_expr("let f x := x; f 0")));
    }
}

// ============================================================================
// Section 6: Match Expressions
// ============================================================================

mod match_expr {
    use super::*;

    #[test]
    fn simple_match() {
        assert!(check(
            "match x with | 0 => 1",
            parse_expr("match x with | 0 => 1")
        ));
    }

    #[test]
    fn multi_arm_match() {
        assert!(check(
            "match with multiple arms",
            parse_expr("match x with | 0 => 1 | n => n")
        ));
    }

    #[test]
    fn match_with_discriminant_type() {
        assert!(check(
            "match x : Nat with",
            parse_expr("match (x : Nat) with | _ => 0")
        ));
    }

    #[test]
    fn match_multiple_scrutinees() {
        assert!(check(
            "match x, y with",
            parse_expr("match x, y with | a, b => a")
        ));
    }

    #[test]
    fn pattern_wildcards() {
        assert!(check("| _ => e", parse_expr("match x with | _ => 0")));
    }

    #[test]
    fn pattern_constructor() {
        assert!(check(
            "| .cons h t",
            parse_expr("match xs with | .nil => 0 | .cons h t => 1")
        ));
    }

    #[test]
    fn pattern_as() {
        assert!(check(
            "pat@...",
            parse_expr("match x with | n@0 => n | _ => 1")
        ));
    }

    #[test]
    fn pattern_or() {
        assert!(check(
            "| 0 | 1",
            parse_expr("match x with | 0 | 1 => true | _ => false")
        ));
    }

    #[test]
    fn n_plus_k_pattern() {
        // n+1 pattern for Nat
        assert!(check(
            "| n + 1",
            parse_expr("match x with | 0 => 0 | n + 1 => n")
        ));
    }
}

// ============================================================================
// Section 7: Do Notation
// ============================================================================

mod do_notation {
    use super::*;
    use crate::surface::{DoElem, SurfaceExpr, SurfaceLit};

    #[test]
    fn simple_do() {
        assert!(check("do return 1", parse_expr("do return 1")));
    }

    #[test]
    fn do_with_bind() {
        assert!(check("do let x ← m", parse_expr("do let x ← m; return x")));
    }

    #[test]
    fn do_with_let() {
        assert!(check(
            "do let x := 1",
            parse_expr("do let x := 1; return x")
        ));
    }

    #[test]
    fn do_multiline() {
        assert!(check(
            "do block",
            parse_decl("def test : IO Unit := do\n  let x ← pure 1\n  pure ()")
        ));
    }

    #[test]
    fn do_if() {
        assert!(check(
            "do if",
            parse_expr("do if true then return 1 else return 0")
        ));
    }

    #[test]
    fn do_for() {
        assert!(check(
            "do for",
            parse_expr("do for x in xs do IO.println x")
        ));
    }

    #[test]
    fn do_unless() {
        assert!(check("do unless", parse_expr("do unless cond do action")));
    }

    // === Structural tests: verify AST shape ===

    #[test]
    fn test_do_return_produces_do_variant() {
        let expr = parse_expr("do return 1").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1, "expected 1 do element");
                assert!(
                    matches!(&elems[0], DoElem::Return(_, _)),
                    "expected Return, got {:?}",
                    elems[0]
                );
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_return_literal_value() {
        let expr = parse_expr("do return 42").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1);
                match &elems[0] {
                    DoElem::Return(_, val) => match val.as_ref() {
                        SurfaceExpr::Lit(_, SurfaceLit::Nat(42)) => {}
                        other => panic!("expected Lit(Nat(42)), got {other:?}"),
                    },
                    other => panic!("expected Return, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_bind_then_return() {
        let expr = parse_expr("do let x <- f; return x").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2, "expected 2 do elements");
                match &elems[0] {
                    DoElem::Bind(_, binder, action) => {
                        assert_eq!(binder.name, "x");
                        assert!(binder.ty.is_none(), "bind should have no type annotation");
                        assert!(
                            matches!(action.as_ref(), SurfaceExpr::Ident(_, ref n) if n == "f"),
                            "expected ident 'f', got {:?}",
                            action
                        );
                    }
                    other => panic!("expected Bind, got {other:?}"),
                }
                assert!(
                    matches!(&elems[1], DoElem::Return(_, _)),
                    "expected Return, got {:?}",
                    elems[1]
                );
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_bind_unicode_arrow() {
        let expr = parse_expr("do let x ← f; return x").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2);
                assert!(matches!(&elems[0], DoElem::Bind(_, binder, _) if binder.name == "x"));
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_let_pure() {
        let expr = parse_expr("do let x := 1; return x").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2);
                match &elems[0] {
                    DoElem::Let(_, binder, val) => {
                        assert_eq!(binder.name, "x");
                        assert!(matches!(
                            val.as_ref(),
                            SurfaceExpr::Lit(_, SurfaceLit::Nat(1))
                        ));
                    }
                    other => panic!("expected Let, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_let_mut() {
        let expr = parse_expr("do let mut x := 0; return x").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2);
                assert!(
                    matches!(&elems[0], DoElem::LetMut(_, binder, _) if binder.name == "x"),
                    "expected LetMut, got {:?}",
                    elems[0]
                );
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_multiline_let_value_stops_before_next_elem() {
        let decl = parse_decl(
            "def boo : Id Nat := do\n  let mut acc : Nat := 0\n  for i in xs do\n    acc := i\n  return acc",
        )
        .unwrap();
        match decl {
            crate::SurfaceDecl::Def { val, .. } => match val.as_ref() {
                SurfaceExpr::Do(_, elems) => {
                    assert_eq!(elems.len(), 3, "expected let, for, return do elements");
                    assert!(
                        matches!(&elems[0], DoElem::LetMut(_, binder, _) if binder.name == "acc")
                    );
                    assert!(
                        matches!(&elems[1], DoElem::For(_, binder, _, _) if binder.name == "i")
                    );
                    assert!(matches!(&elems[2], DoElem::Return(_, _)));
                }
                other => panic!("expected Do body, got {other:?}"),
            },
            other => panic!("expected Def, got {other:?}"),
        }
    }

    #[test]
    fn test_do_multiline_let_mut_allows_following_reassign() {
        let decl = parse_decl(
            "def adjust : Nat := do\n  let mut f : Nat -> Nat := fun x => x\n  f := fun x => x\n  return f 0",
        )
        .unwrap();
        match decl {
            crate::SurfaceDecl::Def { val, .. } => match val.as_ref() {
                SurfaceExpr::Do(_, elems) => {
                    assert_eq!(elems.len(), 3, "expected let, reassign, return do elements");
                    assert!(
                        matches!(&elems[0], DoElem::LetMut(_, binder, _) if binder.name == "f")
                    );
                    assert!(matches!(&elems[1], DoElem::Reassign(_, name, _) if name == "f"));
                    assert!(matches!(&elems[2], DoElem::Return(_, _)));
                }
                other => panic!("expected Do body, got {other:?}"),
            },
            other => panic!("expected Def, got {other:?}"),
        }
    }

    #[test]
    fn test_do_pure_let_else_pattern() {
        let expr = parse_expr("do\n  let .true := x | return fallback\n  get").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2, "expected let-else plus trailing expression");
                match &elems[0] {
                    DoElem::LetElse(_, pat, action, fallback) => {
                        assert!(
                            matches!(pat, crate::surface::SurfacePattern::Var(name) if name == "true")
                                || matches!(
                                    pat,
                                    crate::surface::SurfacePattern::Ctor(name, _)
                                        if name == "true"
                                ),
                            "expected `.true` to parse as a let-else pattern, got {pat:?}"
                        );
                        assert!(
                            matches!(action.as_ref(), SurfaceExpr::Ident(_, ref name) if name == "x"),
                            "expected pure scrutinee `x`, got {action:?}"
                        );
                        assert_eq!(fallback.len(), 1, "fallback should contain one do element");
                        assert!(matches!(&fallback[0], DoElem::Return(_, _)));
                    }
                    other => panic!("expected DoElem::LetElse, got {other:?}"),
                }
                assert!(matches!(&elems[1], DoElem::Expr(_, _)));
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_expr_statement() {
        let expr = parse_expr("do f; return ()").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2);
                assert!(
                    matches!(&elems[0], DoElem::Expr(_, _)),
                    "expected Expr statement, got {:?}",
                    elems[0]
                );
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_bare_bind() {
        // Bare bind without `let` keyword: `x <- f`
        let expr = parse_expr("do x <- f; return x").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2);
                match &elems[0] {
                    DoElem::Bind(_, binder, action) => {
                        assert_eq!(binder.name, "x");
                        assert!(
                            matches!(action.as_ref(), SurfaceExpr::Ident(_, ref n) if n == "f")
                        );
                    }
                    other => panic!("expected bare Bind, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_braced_block() {
        let expr = parse_expr("do { return 1 }").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1);
                assert!(matches!(&elems[0], DoElem::Return(_, _)));
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_braced_multi_statement() {
        let expr = parse_expr("do { let x <- f; let y := 1; return x }").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 3, "expected 3 do elements");
                assert!(matches!(&elems[0], DoElem::Bind(_, _, _)));
                assert!(matches!(&elems[1], DoElem::Let(_, _, _)));
                assert!(matches!(&elems[2], DoElem::Return(_, _)));
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_bind_with_type_annotation() {
        let expr = parse_expr("do let x : Nat <- f; return x").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2);
                match &elems[0] {
                    DoElem::Bind(_, binder, _) => {
                        assert_eq!(binder.name, "x");
                        assert!(binder.ty.is_some(), "expected type annotation on bind");
                    }
                    other => panic!("expected Bind, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_single_expression() {
        // A do block with just a single expression (no bind/return)
        let expr = parse_expr("do f x").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1);
                assert!(
                    matches!(&elems[0], DoElem::Expr(_, _)),
                    "expected single Expr, got {:?}",
                    elems[0]
                );
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_multiple_binds_chain() {
        let expr = parse_expr("do let a <- f; let b <- g a; return b").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 3);
                assert!(matches!(&elems[0], DoElem::Bind(_, binder, _) if binder.name == "a"));
                assert!(matches!(&elems[1], DoElem::Bind(_, binder, _) if binder.name == "b"));
                assert!(matches!(&elems[2], DoElem::Return(_, _)));
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_empty_block_error() {
        // Empty do block should be a parse error
        let result = parse_expr("do {}");
        assert!(result.is_err(), "empty do block should be a parse error");
    }

    #[test]
    fn test_do_underscore_bind() {
        // `let _ <- action` — discard result
        let expr = parse_expr("do let _ <- f; return ()").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2);
                match &elems[0] {
                    DoElem::Bind(_, binder, _) => {
                        assert_eq!(binder.name, "_");
                    }
                    other => panic!("expected Bind with _, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_in_def_body() {
        // Do notation as body of a def declaration
        let decl = parse_decl("def main : IO Unit := do\n  let x ← pure 1\n  return ()").unwrap();
        match decl {
            crate::SurfaceDecl::Def { name, val, .. } => {
                assert_eq!(name, "main");
                match val.as_ref() {
                    SurfaceExpr::Do(_, elems) => {
                        assert_eq!(elems.len(), 2, "expected 2 do elements in def body");
                    }
                    other => panic!("expected Do body, got {other:?}"),
                }
            }
            other => panic!("expected Def, got {other:?}"),
        }
    }

    // === First-class do-elements: if, for, match ===

    #[test]
    fn test_do_if_then_else() {
        // if-then-else as a first-class do element with do-sequence branches
        let expr = parse_expr("do { if x then return 1 else return 0 }").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1, "expected 1 do element");
                match &elems[0] {
                    DoElem::If(_, _cond, then_branch, else_branch) => {
                        assert_eq!(then_branch.len(), 1, "then branch should have 1 elem");
                        assert!(
                            matches!(&then_branch[0], DoElem::Return(_, _)),
                            "then branch should be a return"
                        );
                        let else_branch = else_branch.as_ref().expect("should have else branch");
                        assert_eq!(else_branch.len(), 1, "else branch should have 1 elem");
                        assert!(
                            matches!(&else_branch[0], DoElem::Return(_, _)),
                            "else branch should be a return"
                        );
                    }
                    other => panic!("expected DoElem::If, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_if_no_else() {
        // if without else in do block
        let expr = parse_expr("do { if x then return 1; return 0 }").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 2, "expected 2 do elements (if + return)");
                assert!(
                    matches!(&elems[0], DoElem::If(_, _, _, None)),
                    "first elem should be If without else"
                );
                assert!(
                    matches!(&elems[1], DoElem::Return(_, _)),
                    "second elem should be Return"
                );
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_for_in() {
        // for-in loop as a first-class do element
        let expr = parse_expr("do { for x in xs do return x }").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1, "expected 1 do element");
                match &elems[0] {
                    DoElem::For(_, binder, _collection, body) => {
                        assert_eq!(binder.name, "x", "loop variable should be x");
                        assert_eq!(body.len(), 1, "for body should have 1 elem");
                        assert!(
                            matches!(&body[0], DoElem::Return(_, _)),
                            "for body should be a return"
                        );
                    }
                    other => panic!("expected DoElem::For, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    /// #1808: `for x in f y do body` should not consume `do` as part of the collection expression.
    /// The `do` keyword after the collection must delimit the loop body.
    #[test]
    fn test_do_for_collection_does_not_consume_do() {
        let expr = parse_expr("do { for x in f y do return x }").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1, "expected 1 do element");
                match &elems[0] {
                    DoElem::For(_, binder, collection, body) => {
                        assert_eq!(binder.name, "x", "loop variable should be x");
                        // Collection should be `f y` (application), NOT `f y (do return x)`
                        match collection.as_ref() {
                            SurfaceExpr::App(_, func, args) => {
                                assert!(
                                    matches!(func.as_ref(), SurfaceExpr::Ident(_, ref n) if n == "f"),
                                    "collection func should be 'f', got {func:?}"
                                );
                                assert_eq!(args.len(), 1, "collection should have 1 arg (y)");
                                assert!(
                                    matches!(&args[0].expr, SurfaceExpr::Ident(_, ref n) if n == "y"),
                                    "collection arg should be 'y', got {:?}",
                                    args[0].expr
                                );
                            }
                            other => panic!("expected App(f, [y]) as collection, got {other:?}"),
                        }
                        assert_eq!(body.len(), 1, "for body should have 1 elem");
                    }
                    other => panic!("expected DoElem::For, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_match_with_arms() {
        // match as a first-class do element with do-sequence arms
        let expr = parse_expr("do { match x with | y => return y }").unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1, "expected 1 do element");
                match &elems[0] {
                    DoElem::Match(_, discrs, arms) => {
                        assert_eq!(discrs.len(), 1, "should have 1 discriminee");
                        assert_eq!(arms.len(), 1, "should have 1 arm");
                        assert_eq!(arms[0].body.len(), 1, "arm body should have 1 elem");
                        assert!(
                            matches!(&arms[0].body[0], DoElem::Return(_, _)),
                            "arm body should be a return"
                        );
                    }
                    other => panic!("expected DoElem::Match, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }

    #[test]
    fn test_do_if_with_multi_elem_branches() {
        // if with multi-element do-sequence branches
        let expr = parse_expr("do { if cond then let x := 1; return x else let y := 2; return y }")
            .unwrap();
        match expr {
            SurfaceExpr::Do(_, elems) => {
                assert_eq!(elems.len(), 1, "expected 1 do element (the if)");
                match &elems[0] {
                    DoElem::If(_, _, then_branch, else_branch) => {
                        assert_eq!(then_branch.len(), 2, "then branch should have 2 elems");
                        let else_branch = else_branch.as_ref().expect("should have else");
                        assert_eq!(else_branch.len(), 2, "else branch should have 2 elems");
                    }
                    other => panic!("expected DoElem::If, got {other:?}"),
                }
            }
            other => panic!("expected Do, got {other:?}"),
        }
    }
}

// ============================================================================
// Section 8: Notation and Operators
// ============================================================================

mod notation {
    use super::*;

    #[test]
    fn infix_notation() {
        assert!(check(
            "infix declaration",
            parse_decl("infix:50 \" ++ \" => append")
        ));
    }

    #[test]
    fn prefix_notation() {
        assert!(check(
            "prefix declaration",
            parse_decl("prefix:100 \"!\" => not")
        ));
    }

    #[test]
    fn postfix_notation() {
        assert!(check(
            "postfix declaration",
            parse_decl("postfix:max \"!\" => factorial")
        ));
    }

    #[test]
    fn notation_declaration() {
        assert!(check(
            "notation declaration",
            parse_decl("notation \"[\" a \", \" b \"]\" => Pair.mk a b")
        ));
    }

    #[test]
    fn macro_declaration() {
        assert!(check(
            "macro declaration",
            parse_decl("macro \"hello\" : term => `(IO.println \"Hello\")")
        ));
    }

    #[test]
    fn macro_rules() {
        assert!(check(
            "macro_rules",
            parse_decl("macro_rules | `(myMacro $x) => `($x + 1)")
        ));
    }

    #[test]
    fn syntax_declaration() {
        assert!(check(
            "syntax declaration",
            parse_decl("syntax \"myKeyword\" term : term")
        ));
    }

    /// Regression (Trust `Trust.Temporal` prelude): the leads-to relation
    /// `F ~> G` — a level-50 `infixl` whose symbol lexes to `Ident("~>")` —
    /// must parse and lower to the binary application `LeadsTo F G` even when
    /// declared alongside the `□`/`◇` prefix notations and the level-45 `⊨`
    /// relation, inside `namespace`s, with `_root_.`-anchored targets.
    ///
    /// Before the low-precedence custom-infix band (45–50) was modeled, `~>`
    /// (50) sat below the custom-operator floor (then 60): the use site
    /// `(F ~> G)` left the operator unconsumed, the enclosing paren failed, and
    /// the theorem collapsed into an error-recovery `RawDecl`
    /// (`error-recovery ~> G   LeadsTo F G`), poisoning the whole prelude.
    #[test]
    fn temporal_leadsto_prelude_parses_without_recovery() {
        use crate::{Projection, SurfaceDecl, SurfaceExpr};

        const SOURCE: &str = concat!(
            "namespace Trust\n",
            "namespace Temporal\n",
            "def Always (F : Nat) : Nat := F\n",
            "def Eventually (F : Nat) : Nat := F\n",
            "def LeadsTo (F G : Nat) : Nat := F\n",
            "def Satisfies (F G : Nat) : Nat := F\n",
            "prefix:100 \"\u{25a1}\" => _root_.Trust.Temporal.Always\n",
            "prefix:100 \"\u{25c7}\" => _root_.Trust.Temporal.Eventually\n",
            "infixl:50 \" ~> \" => _root_.Trust.Temporal.LeadsTo\n",
            "infixl:45 \" \u{22a8} \" => _root_.Trust.Temporal.Satisfies\n",
            "def leads := F ~> G\n",
            "def boxed := \u{25a1} F\n",
            "def diamonded := \u{25c7} F\n",
            "theorem leadsto_unfolds (F G : Nat) : (F ~> G) = LeadsTo F G := rfl\n",
            "end Temporal\n",
            "end Trust\n",
        );

        let decls = parse_file(SOURCE).expect("temporal prelude must parse");

        // Flatten the two nested namespaces.
        fn flatten<'a>(decls: &'a [SurfaceDecl], out: &mut Vec<&'a SurfaceDecl>) {
            for decl in decls {
                out.push(decl);
                if let SurfaceDecl::Namespace { decls, .. } = decl {
                    flatten(decls, out);
                }
            }
        }
        let mut flat = Vec::new();
        flatten(&decls, &mut flat);

        // No declaration may fall into error recovery.
        for decl in &flat {
            if let SurfaceDecl::RawDecl { content, .. } = decl {
                panic!("`~>` regressed into error recovery: {content:?}");
            }
        }

        // The `~>` use site lowers to the application `LeadsTo F G`. The
        // `_root_.Trust.Temporal.LeadsTo` expansion target lowers to a
        // projection chain, so the head is the final `.LeadsTo` projection (or
        // a bare `LeadsTo` ident) — either way it names the leads-to constant.
        fn head_names_leadsto(expr: &SurfaceExpr) -> bool {
            match expr {
                SurfaceExpr::Ident(_, name) => name.ends_with("LeadsTo"),
                SurfaceExpr::Proj(_, _, Projection::Named(field)) => field == "LeadsTo",
                _ => false,
            }
        }
        let leads_val = flat
            .iter()
            .find_map(|decl| match decl {
                SurfaceDecl::Def { name, val, .. } if name == "leads" => Some(val.as_ref()),
                _ => None,
            })
            .expect("`def leads` must parse as a real Def");
        match leads_val {
            SurfaceExpr::App(_, head, args) => {
                assert!(
                    head_names_leadsto(head.as_ref()),
                    "`F ~> G` must lower to a LeadsTo application, got head {head:?}"
                );
                assert_eq!(args.len(), 2, "LeadsTo applied to both operands");
            }
            other => panic!("`F ~> G` must be an application, got {other:?}"),
        }

        // The `□`/`◇` prefix notations still parse (no regression).
        let names: Vec<&str> = flat
            .iter()
            .filter_map(|decl| match decl {
                SurfaceDecl::Def { name, .. } => Some(name.as_str()),
                SurfaceDecl::Theorem { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        assert!(
            names.contains(&"boxed")
                && names.contains(&"diamonded")
                && names.contains(&"leadsto_unfolds"),
            "box/diamond/leadsto declarations must all parse, got {names:?}"
        );
    }
}

// ============================================================================
// Section 9: Structure Declarations
// ============================================================================

mod structure_decl {
    use super::*;

    #[test]
    fn simple_structure() {
        assert!(check(
            "structure Point",
            parse_decl("structure Point where\n  x : Nat\n  y : Nat")
        ));
    }

    #[test]
    fn structure_with_default() {
        assert!(check(
            "structure with default",
            parse_decl("structure Point where\n  x : Nat := 0\n  y : Nat := 0")
        ));
    }

    #[test]
    fn structure_with_parameters() {
        assert!(check(
            "structure with params",
            parse_decl("structure Vec (α : Type) (n : Nat) where\n  data : Array α")
        ));
    }

    #[test]
    fn structure_extends() {
        assert!(check(
            "structure extends",
            parse_decl("structure ColorPoint extends Point where\n  color : Nat")
        ));
    }

    #[test]
    fn structure_constructor() {
        assert!(check(
            "structure with mk",
            parse_decl("structure Point where\n  mk ::\n  x : Nat\n  y : Nat")
        ));
    }
}

// ============================================================================
// Section 10: Class Declarations
// ============================================================================

mod class_decl {
    use super::*;

    #[test]
    fn simple_class() {
        assert!(check(
            "class declaration",
            parse_decl("class Inhabited (α : Type)")
        ));
    }

    #[test]
    fn class_with_method() {
        assert!(check(
            "class with method",
            parse_decl("class ToString (α : Type) where\n  toString : α → String")
        ));
    }

    #[test]
    fn class_extends() {
        assert!(check(
            "class extends",
            parse_decl("class Monad (m : Type → Type) extends Applicative m where\n  bind : m α → (α → m β) → m β")
        ));
    }

    #[test]
    fn abbrev_class() {
        assert!(check(
            "abbrev class",
            parse_decl("abbrev class MonadIO (m : Type → Type) := Monad m")
        ));
    }
}

// ============================================================================
// Section 11: Instance Declarations
// ============================================================================

mod instance_decl {
    use super::*;

    #[test]
    fn simple_instance() {
        assert!(check(
            "instance",
            parse_decl("instance : Inhabited Nat where\n  default := 0")
        ));
    }

    #[test]
    fn named_instance() {
        assert!(check(
            "named instance",
            parse_decl("instance instInhabitedNat : Inhabited Nat where\n  default := 0")
        ));
    }

    #[test]
    fn instance_with_priority() {
        assert!(check(
            "instance priority",
            parse_decl("instance (priority := high) : Inhabited Nat where\n  default := 0")
        ));
    }

    #[test]
    fn instance_with_parameters() {
        assert!(check(
            "instance with params",
            parse_decl("instance [Inhabited α] : Inhabited (List α) where\n  default := []")
        ));
    }
}

// ============================================================================
// Section 12: Inductive Declarations
// ============================================================================

mod inductive_decl {
    use super::*;

    #[test]
    fn simple_inductive() {
        assert!(check(
            "inductive Bool",
            parse_decl("inductive Bool where\n  | false : Bool\n  | true : Bool")
        ));
    }

    #[test]
    fn inductive_with_parameters() {
        assert!(check(
            "inductive List",
            parse_decl("inductive List (α : Type u) where\n  | nil : List α\n  | cons : α → List α → List α")
        ));
    }

    #[test]
    fn inductive_with_indices() {
        assert!(check(
            "inductive Vec",
            parse_decl("inductive Vec (α : Type) : Nat → Type where\n  | nil : Vec α 0\n  | cons : α → Vec α n → Vec α (n + 1)")
        ));
    }

    #[test]
    fn mutual_inductive() {
        assert!(check(
            "mutual inductive",
            parse_file("mutual\n  inductive Even : Nat → Prop\n    | zero : Even 0\n    | succ : Odd n → Even (n + 1)\n  inductive Odd : Nat → Prop\n    | succ : Even n → Odd (n + 1)\nend")
        ));
    }
}

// ============================================================================
// Section 13: Mutual Definitions
// ============================================================================

mod mutual_def {
    use super::*;

    #[test]
    fn mutual_def() {
        assert!(check(
            "mutual def",
            parse_file("mutual\n  def f : Nat → Nat\n    | 0 => 0\n    | n + 1 => g n\n  def g : Nat → Nat\n    | 0 => 1\n    | n + 1 => f n\nend")
        ));
    }
}

// ============================================================================
// Section 14: Where Clauses
// ============================================================================

mod where_clause {
    use super::*;

    #[test]
    fn def_with_where() {
        assert!(check(
            "def with where",
            parse_decl("def foo : Nat := x + y where\n  x := 1\n  y := 2")
        ));
    }

    #[test]
    fn def_where_match() {
        assert!(check(
            "def where match",
            parse_decl("def foo : Nat → Nat where\n  | 0 => 1\n  | n + 1 => n")
        ));
    }
}

// ============================================================================
// Section 15: Calc Blocks
// ============================================================================

mod calc_blocks {
    use super::*;

    #[test]
    fn simple_calc() {
        assert!(check(
            "calc",
            parse_expr("calc a = b := h1\n       _ = c := h2")
        ));
    }

    #[test]
    fn calc_with_transitive_relation() {
        assert!(check(
            "calc with ≤",
            parse_expr("calc a ≤ b := h1\n       _ ≤ c := h2")
        ));
    }
}

// ============================================================================
// Section 16: Have/Let/Show in Terms
// ============================================================================

mod term_have_let_show {
    use super::*;

    #[test]
    fn have_in_term() {
        assert!(check(
            "have in term",
            parse_expr("have h : P := proof; conclusion")
        ));
    }

    #[test]
    fn show_in_term() {
        assert!(check("show in term", parse_expr("show P from proof")));
    }

    #[test]
    fn suffices_in_term() {
        assert!(check(
            "suffices in term",
            parse_expr("suffices h : P by exact h; proof")
        ));
    }

    /// Verify suffices produces a real ByTactic node (not a sorry stub).
    #[test]
    fn suffices_by_produces_tactic_node() {
        let expr = parse_expr("suffices h : P by exact h; proof").unwrap();
        // suffices h : P by tac; body → Let(_, binder, body, ByTactic(...))
        match expr {
            SurfaceExpr::Let(_, binder, _body, tac) => {
                assert_eq!(binder.name, "h", "binder name should be 'h'");
                match *tac {
                    SurfaceExpr::ByTactic(_, ref tactics) => {
                        assert_eq!(tactics.len(), 1, "should have exactly 1 tactic");
                        assert!(
                            matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "exact"),
                            "tactic should be Exact, got {:?}",
                            tactics[0]
                        );
                    }
                    other => panic!("expected ByTactic, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    #[test]
    fn suffices_bad_tactic_recovers_to_synthetic_sorry() {
        let expr = parse_expr("suffices h : P by have : P :=; proof").unwrap();
        match expr {
            SurfaceExpr::Let(_, binder, _body, tac) => {
                assert_eq!(binder.name, "h", "binder name should be 'h'");
                assert!(
                    matches!(&*tac, SurfaceExpr::SyntheticSorry(_)),
                    "bad suffices tactic should recover to synthetic sorry, got {tac:?}"
                );
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    /// `suffices h : P from e; body` is valid Lean 4 term-level syntax
    /// (`Lean.Parser.Term.suffices`) where the goal follows from the proof
    /// term `e` rather than a `by` block.
    #[test]
    fn test_suffices_term_from_clause_parses() {
        assert!(check(
            "suffices from in term",
            parse_expr("suffices h : P from e; proof")
        ));
    }

    /// The `from` justification desugars to `let h : P := body; e`, mirroring
    /// the `by` form but with the proof term `e` as the let-body instead of a
    /// `ByTactic` block.
    #[test]
    fn test_suffices_term_from_desugars_to_let_with_term_body() {
        let expr = parse_expr("suffices h : P from e; proof").unwrap();
        match expr {
            SurfaceExpr::Let(_, binder, body, justification) => {
                assert_eq!(binder.name, "h", "binder name should be 'h'");
                assert!(
                    binder.ty.is_some(),
                    "suffices type annotation should be preserved"
                );
                // The continuation (proof of P) becomes the let value.
                assert!(
                    matches!(&*body, SurfaceExpr::Ident(_, name) if name == "proof"),
                    "let value should be the continuation proof, got {body:?}"
                );
                // The `from` term becomes the let body (no ByTactic node).
                assert!(
                    matches!(&*justification, SurfaceExpr::Ident(_, name) if name == "e"),
                    "from justification should be the plain term `e`, got {justification:?}"
                );
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    /// The `from` justification accepts a compound proof term that references
    /// the introduced hypothesis `h`.
    #[test]
    fn test_suffices_term_from_compound_term_parses() {
        let expr = parse_expr("suffices h : P from g h; proof").unwrap();
        match expr {
            SurfaceExpr::Let(_, _, _, justification) => {
                assert!(
                    matches!(&*justification, SurfaceExpr::App(..)),
                    "from justification `g h` should be an application, got {justification:?}"
                );
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    /// `from` requires a justification term: a bare `suffices h : P from` with
    /// no following term must be rejected, not silently accepted.
    #[test]
    fn test_suffices_term_from_missing_term_rejected() {
        assert!(check_reject(
            "suffices from with no term",
            parse_expr("suffices h : P from")
        ));
    }

    /// `suffices h : P from e` without the `;`-separated continuation proof
    /// is incomplete and must be rejected.
    #[test]
    fn test_suffices_term_from_missing_continuation_rejected() {
        assert!(check_reject(
            "suffices from with no continuation",
            parse_expr("suffices h : P from e")
        ));
    }
}

// ============================================================================
// Section 17: Anonymous Constructor
// ============================================================================

mod anonymous_ctor {
    use super::*;

    #[test]
    fn angle_bracket_ctor() {
        assert!(check("⟨a, b, c⟩", parse_expr("⟨a, b, c⟩")));
        assert!(check("⟨a⟩", parse_expr("⟨a⟩")));
        assert!(check("⟨⟩", parse_expr("⟨⟩")));
    }

    #[test]
    fn nested_angle_bracket() {
        assert!(check("⟨⟨a⟩, b⟩", parse_expr("⟨⟨a⟩, b⟩")));
    }
}

// ============================================================================
// Section 18: Field Notation
// ============================================================================

mod field_notation {
    use super::*;

    #[test]
    fn named_field() {
        assert!(check("x.field", parse_expr("x.field")));
        assert!(check("x.y.z", parse_expr("x.y.z")));
    }

    #[test]
    fn index_field() {
        assert!(check("x.1", parse_expr("x.1")));
        assert!(check("x.2", parse_expr("x.2")));
    }

    #[test]
    fn field_after_app() {
        assert!(check("(f x).field", parse_expr("(f x).field")));
    }

    #[test]
    fn ufcs_field() {
        // Universal function call syntax
        assert!(check("x.foo y", parse_expr("x.foo y")));
    }
}

// ============================================================================
// Section 19: If-then-else
// ============================================================================

mod if_then_else {
    use super::*;

    #[test]
    fn simple_if() {
        assert!(check("if then else", parse_expr("if c then t else e")));
    }

    #[test]
    fn nested_if() {
        assert!(check(
            "nested if",
            parse_expr("if a then (if b then 1 else 2) else 3")
        ));
    }

    #[test]
    fn if_let() {
        assert!(check(
            "if let",
            parse_expr("if let some x := opt then x else 0")
        ));
    }
}

// ============================================================================
// Section 20: Decidable If
// ============================================================================

mod decidable_if {
    use super::*;

    #[test]
    fn decidable_if() {
        // if h : p then t else e
        assert!(check("if h : p", parse_expr("if h : p then t else e")));
    }
}

// ============================================================================
// Section 21: Syntax Quotations
// ============================================================================

mod syntax_quotations {
    use super::*;

    #[test]
    fn simple_quote() {
        assert!(check("`(x)", parse_expr("`(x)")));
        assert!(check("`(1 + 2)", parse_expr("`(1 + 2)")));
    }

    #[test]
    fn antiquotation() {
        assert!(check("`($x)", parse_expr("`($x)")));
    }

    #[test]
    fn typed_antiquotation() {
        assert!(check("`($x:term)", parse_expr("`($x:term)")));
    }

    #[test]
    fn splice_antiquotation() {
        assert!(check("`($[xs]*)", parse_expr("`($[xs]*)")));
    }
}

// ============================================================================
// Section 22: Attributes
// ============================================================================

mod attributes {
    use super::*;

    #[test]
    fn simple_attribute() {
        assert!(check("@[simp]", parse_decl("@[simp] def foo : Nat := 1")));
    }

    #[test]
    fn multiple_attributes() {
        assert!(check(
            "@[simp, local]",
            parse_decl("@[simp, local] def foo : Nat := 1")
        ));
    }

    #[test]
    fn attribute_with_args() {
        assert!(check(
            "@[simp high]",
            parse_decl("@[simp high] def foo : Nat := 1")
        ));
    }

    #[test]
    fn simp_priority_high() {
        use crate::surface::{Attribute, SimpPriority, SurfaceDecl};
        let decl = parse_decl("@[simp high] def foo : Nat := 1").unwrap();
        if let SurfaceDecl::Def { attrs, .. } = &decl {
            assert!(
                attrs.iter().any(|a| matches!(
                    a,
                    Attribute::Simp {
                        priority: Some(SimpPriority::High)
                    }
                )),
                "Expected simp high attribute, got: {attrs:?}"
            );
        } else {
            panic!("Expected Def declaration");
        }
    }

    #[test]
    fn simp_priority_low() {
        use crate::surface::{Attribute, SimpPriority, SurfaceDecl};
        let decl = parse_decl("@[simp low] def foo : Nat := 1").unwrap();
        if let SurfaceDecl::Def { attrs, .. } = &decl {
            assert!(
                attrs.iter().any(|a| matches!(
                    a,
                    Attribute::Simp {
                        priority: Some(SimpPriority::Low)
                    }
                )),
                "Expected simp low attribute, got: {attrs:?}"
            );
        } else {
            panic!("Expected Def declaration");
        }
    }

    #[test]
    fn simp_no_priority() {
        use crate::surface::{Attribute, SurfaceDecl};
        let decl = parse_decl("@[simp] def foo : Nat := 1").unwrap();
        if let SurfaceDecl::Def { attrs, .. } = &decl {
            assert!(
                attrs
                    .iter()
                    .any(|a| matches!(a, Attribute::Simp { priority: None })),
                "Expected simp attribute with no priority, got: {attrs:?}"
            );
        } else {
            panic!("Expected Def declaration");
        }
    }

    #[test]
    fn simp_priority_normal() {
        use crate::surface::{Attribute, SimpPriority, SurfaceDecl};
        let decl = parse_decl("@[simp normal] def foo : Nat := 1").unwrap();
        if let SurfaceDecl::Def { attrs, .. } = &decl {
            assert!(
                attrs.iter().any(|a| matches!(
                    a,
                    Attribute::Simp {
                        priority: Some(SimpPriority::Normal)
                    }
                )),
                "Expected simp normal attribute, got: {attrs:?}"
            );
        } else {
            panic!("Expected Def declaration");
        }
    }

    #[test]
    fn simp_with_other_attribute() {
        // Test simp priority with multiple attributes
        use crate::surface::{Attribute, SimpPriority, SurfaceDecl};
        let decl = parse_decl("@[simp high, inline] def foo : Nat := 1").unwrap();
        if let SurfaceDecl::Def { attrs, .. } = &decl {
            assert!(
                attrs.iter().any(|a| matches!(
                    a,
                    Attribute::Simp {
                        priority: Some(SimpPriority::High)
                    }
                )),
                "Expected simp high attribute, got: {attrs:?}"
            );
            assert!(
                attrs.iter().any(|a| matches!(a, Attribute::Inline)),
                "Expected inline attribute, got: {attrs:?}"
            );
        } else {
            panic!("Expected Def declaration");
        }
    }

    #[test]
    fn inline_attribute() {
        assert!(check(
            "@[inline]",
            parse_decl("@[inline] def foo : Nat := 1")
        ));
    }

    #[test]
    fn scoped_attribute() {
        assert!(check(
            "scoped attribute",
            parse_file("attribute [local simp] foo")
        ));
    }
}

// ============================================================================
// Section 23: Namespace and Section
// ============================================================================

mod namespace_section {
    use super::*;

    #[test]
    fn namespace() {
        assert!(check(
            "namespace",
            parse_file("namespace Foo\ndef bar : Nat := 1\nend Foo")
        ));
    }

    #[test]
    fn nested_namespace() {
        assert!(check(
            "nested namespace",
            parse_file("namespace Foo.Bar\ndef baz : Nat := 1\nend Foo.Bar")
        ));
    }

    #[test]
    fn section() {
        assert!(check(
            "section",
            parse_file("section\nvariable (x : Nat)\ndef foo : Nat := x\nend")
        ));
    }

    #[test]
    fn named_section() {
        assert!(check(
            "named section",
            parse_file("section MySection\ndef foo : Nat := 1\nend MySection")
        ));
    }
}

// ============================================================================
// Section 24: Variable Command
// ============================================================================

mod variable_cmd {
    use super::*;

    #[test]
    fn variable() {
        assert!(check("variable", parse_file("variable (x : Nat)")));
    }

    #[test]
    fn variable_implicit() {
        assert!(check(
            "variable implicit",
            parse_file("variable {α : Type}")
        ));
    }

    #[test]
    fn variable_instance() {
        assert!(check(
            "variable instance",
            parse_file("variable [ToString α]")
        ));
    }
}

// ============================================================================
// Section 25: Open Command
// ============================================================================

mod open_cmd {
    use super::*;

    #[test]
    fn open_namespace() {
        assert!(check("open", parse_file("open Nat")));
    }

    #[test]
    fn open_in() {
        assert!(check("open in", parse_file("open Nat in #check succ")));
    }

    #[test]
    fn open_hiding() {
        assert!(check("open hiding", parse_file("open Nat hiding succ")));
    }

    #[test]
    fn open_renaming() {
        assert!(check(
            "open renaming",
            parse_file("open Nat renaming succ → next")
        ));
    }

    #[test]
    fn open_scoped() {
        // `open scoped X` imports only notations/syntax from namespace X
        assert!(check(
            "open scoped",
            parse_file("open scoped EuclideanGeometry")
        ));
    }

    #[test]
    fn open_scoped_multiple() {
        // Multiple scoped opens
        assert!(check(
            "open scoped multiple",
            parse_file("open scoped EuclideanGeometry Real")
        ));
    }
}

// ============================================================================
// Section 26: Import
// ============================================================================

mod import_cmd {
    use super::*;

    #[test]
    fn import() {
        assert!(check("import", parse_file("import Lean")));
    }

    #[test]
    fn import_multiple() {
        assert!(check(
            "import multiple",
            parse_file("import Lean\nimport Std")
        ));
    }
}

// ============================================================================
// Section 27: Definition Forms
// ============================================================================

mod definition_forms {
    use super::*;

    #[test]
    fn def() {
        assert!(check("def", parse_decl("def foo : Nat := 1")));
    }

    #[test]
    fn theorem() {
        assert!(check("theorem", parse_decl("theorem foo : 1 = 1 := rfl")));
    }

    #[test]
    fn lemma() {
        assert!(check("lemma", parse_decl("lemma foo : 1 = 1 := rfl")));
    }

    #[test]
    fn abbrev() {
        assert!(check("abbrev", parse_decl("abbrev foo : Nat := 1")));
    }

    #[test]
    fn example_cmd() {
        assert!(check("example", parse_decl("example : 1 = 1 := rfl")));
    }

    #[test]
    fn opaque() {
        assert!(check("opaque", parse_decl("opaque foo : Nat")));
    }

    #[test]
    fn axiom() {
        assert!(check("axiom", parse_decl("axiom foo : Nat")));
    }

    #[test]
    fn constant() {
        assert!(check("constant", parse_decl("constant foo : Nat")));
    }
}

// ============================================================================
// Section 28: Deriving
// ============================================================================

mod deriving {
    use super::*;

    #[test]
    fn deriving_repr() {
        assert!(check(
            "deriving Repr",
            parse_decl("structure Point where\n  x : Nat\n  y : Nat\nderiving Repr")
        ));
    }

    #[test]
    fn deriving_multiple() {
        assert!(check(
            "deriving multiple",
            parse_decl("structure Point where\n  x : Nat\nderiving Repr, BEq")
        ));
    }

    // Audit item 3 (CLEAN-VERIFIER-AUDIT-2026-05-27): regression tests for
    // `deriving` clauses on `inductive` declarations and bare structures.
    // The parser must accept these so Mathbot/Bridges files (which use
    // `deriving DecidableEq, Repr` on `Literal`, `CrownLowerCert`, etc.)
    // do not break before the elaborator sees them.

    #[test]
    fn inductive_deriving_repr() {
        assert!(check(
            "inductive Foo deriving Repr",
            parse_decl("inductive Foo deriving Repr")
        ));
    }

    #[test]
    fn inductive_with_ctors_deriving_decidable_eq_and_repr() {
        assert!(check(
            "inductive Bar where | a | b deriving DecidableEq, Repr",
            parse_decl("inductive Bar where\n  | a\n  | b\nderiving DecidableEq, Repr")
        ));
    }

    #[test]
    fn structure_bare_deriving_inhabited() {
        assert!(check(
            "structure Baz where deriving Inhabited",
            parse_decl("structure Baz where\nderiving Inhabited")
        ));
    }
}

// ============================================================================
// Section 29: Comments
// ============================================================================

mod comments {
    use super::*;

    #[test]
    fn line_comment() {
        assert!(check(
            "-- comment",
            parse_file("-- comment\ndef foo : Nat := 1")
        ));
    }

    #[test]
    fn block_comment() {
        assert!(check(
            "/- comment -/",
            parse_file("/- comment -/\ndef foo : Nat := 1")
        ));
    }

    #[test]
    fn nested_block_comment() {
        assert!(check(
            "nested /- /- -/ -/",
            parse_file("/- outer /- inner -/ -/\ndef foo : Nat := 1")
        ));
    }

    #[test]
    fn doc_comment() {
        assert!(check(
            "/-- doc -/",
            parse_file("/-- Documentation -/\ndef foo : Nat := 1")
        ));
    }
}

// ============================================================================
// Section 30: String Literals
// ============================================================================

mod string_literals {
    use super::*;

    #[test]
    fn simple_string() {
        assert!(check("\"hello\"", parse_expr("\"hello\"")));
    }

    #[test]
    fn string_with_escapes() {
        assert!(check("\"\\n\\t\"", parse_expr("\"line1\\nline2\"")));
    }

    #[test]
    fn string_interpolation() {
        assert!(check("s!\"...\"", parse_expr("s!\"hello {name}\"")));
    }

    #[test]
    fn raw_string() {
        // This is a valid test but the syntax may vary
        // assert!(check("r\"...\"", parse_expr("r\"raw string\"")));
    }
}

// ============================================================================
// Section 31: Numeric Literals
// ============================================================================

mod numeric_literals {
    use super::*;
    use crate::surface::SurfaceLit;

    /// Parse `src` and assert it is exactly a `Nat` literal with the given value.
    ///
    /// Pins the parsed AST value, not merely that parsing succeeded — a radix
    /// mis-lex (e.g. `0xFF` as `0` applied to `xFF`) parses to an `App`, so this
    /// helper catches silent mis-parses that `check` (Ok-only) would miss.
    fn assert_nat(src: &str, expected: u64) {
        let expr = parse_expr(src).unwrap_or_else(|e| panic!("parse {src:?} failed: {e:?}"));
        match expr {
            SurfaceExpr::Lit(_, SurfaceLit::Nat(value)) => {
                assert_eq!(value, expected, "value mismatch for {src:?}");
            }
            other => panic!("expected Lit(Nat({expected})) for {src:?}, got {other:?}"),
        }
    }

    #[test]
    fn nat_literal() {
        assert_nat("0", 0);
        assert_nat("42", 42);
        assert_nat("1000000", 1_000_000);
        // Underscore digit separators preserve the value: 1_000 == 1000.
        assert_nat("1_000", 1000);
    }

    #[test]
    fn int_literal() {
        assert!(check("-1", parse_expr("-1")));
        assert!(check("-42", parse_expr("-42")));
    }

    #[test]
    fn hex_literal() {
        // Lean 4: 0xFF == 255 (case-insensitive), 0xFF_FF == 65535.
        assert_nat("0xFF", 255);
        assert_nat("0xff", 255);
        assert_nat("0x1A2B", 0x1A2B);
        assert_nat("0xFF_FF", 65_535);
    }

    #[test]
    fn binary_literal() {
        // Lean 4: 0b1010 == 10.
        assert_nat("0b1010", 10);
    }

    #[test]
    fn octal_literal() {
        // Lean 4: 0o777 == 511.
        assert_nat("0o777", 511);
    }

    #[test]
    fn scientific_notation() {
        assert!(check("1.5e10", parse_expr("1.5e10")));
    }
}

// ============================================================================
// Section 32: Array and List Literals
// ============================================================================

mod collection_literals {
    use super::*;

    #[test]
    fn array_literal() {
        assert!(check("#[1, 2, 3]", parse_expr("#[1, 2, 3]")));
        assert!(check("#[]", parse_expr("#[]")));
    }

    #[test]
    fn list_literal() {
        assert!(check("[1, 2, 3]", parse_expr("[1, 2, 3]")));
        assert!(check("[]", parse_expr("[]")));
    }
}

// ============================================================================
// Section 33: Negative Tests (Should Reject)
// ============================================================================

mod negative_tests {
    use super::*;

    #[test]
    fn reject_incomplete_lambda() {
        assert!(check_reject("incomplete lambda", parse_expr("fun x =>")));
    }

    #[test]
    fn reject_unclosed_paren() {
        assert!(check_reject("unclosed paren", parse_expr("(x")));
    }

    #[test]
    fn reject_unclosed_brace() {
        assert!(check_reject("unclosed brace", parse_expr("{x")));
    }

    #[test]
    fn reject_mismatched_brackets() {
        assert!(check_reject("mismatched brackets", parse_expr("(x}")));
    }

    #[test]
    fn reject_tuple_closed_by_angle_bracket() {
        assert!(check_reject(
            "tuple closed by angle bracket",
            parse_expr("(x, y⟩")
        ));
    }

    #[test]
    fn reject_empty_def() {
        assert!(check_reject("empty def", parse_decl("def")));
    }

    #[test]
    fn reject_structure_no_fields() {
        // Structure without where is technically valid as a class/opaque
        // This tests for proper parsing error on malformed input
        assert!(check_reject(
            "malformed structure",
            parse_decl("structure := bad")
        ));
    }
}

// ============================================================================
// Summary Test - Runs All Categories
// ============================================================================

#[test]
fn parser_coverage_summary() {
    println!();
    println!("=========================================");
    println!("Lean 4 Parser Feature Coverage Summary");
    println!("=========================================");
    println!("See individual test modules for details.");
    println!("Coverage documented in docs/PARSER_COVERAGE.md");
    println!("=========================================");
}
