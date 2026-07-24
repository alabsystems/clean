// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for `do` notation parsing.
//!
//! Tests that `do` expressions produce `SurfaceExpr::Do` with correct
//! `DoElem` variants for let, bind, return, if, if-let, if-decidable,
//! and else-if chaining.
//!
//! Split from `tests_tactic_calc_do.rs` to maintain the 500-line file limit.

#![allow(clippy::unwrap_used)]

use super::*;

// ── do notation basic tests ──────────────────────────────────────────

#[test]
fn test_parse_do_return() {
    let expr = Parser::parse_expr("do return 42").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            assert!(matches!(&elems[0], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_then_return() {
    let expr = Parser::parse_expr("do let x := 42; return x").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            assert!(matches!(&elems[0], DoElem::Let(_, _, _)));
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_bind() {
    let expr = Parser::parse_expr("do let x <- getLine; return x").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            assert!(matches!(&elems[0], DoElem::Bind(_, _, _)));
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_expr() {
    let expr = Parser::parse_expr("do putStrLn \"hello\"").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            assert!(matches!(&elems[0], DoElem::Expr(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

// ── do-if with branches tests ────────────────────────────────────────

#[test]
fn test_parse_do_if_plain() {
    let expr = Parser::parse_expr("do if cond then return 1 else return 0").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::If(_, cond, then_branch, else_branch) => {
                    assert!(matches!(cond.as_ref(), SurfaceExpr::Ident(_, _)));
                    assert_eq!(then_branch.len(), 1);
                    assert!(matches!(&then_branch[0], DoElem::Return(_, _)));
                    let else_b = else_branch.as_ref().expect("should have else branch");
                    assert_eq!(else_b.len(), 1);
                    assert!(matches!(&else_b[0], DoElem::Return(_, _)));
                }
                other => panic!("Expected DoElem::If, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_if_let() {
    let expr = Parser::parse_expr("do if let some x := opt then return x else return 0").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::IfLet(_, pat, scrutinee, then_branch, else_branch) => {
                    assert!(
                        matches!(pat, SurfacePattern::Ctor(name, _) if name == "some"),
                        "Expected Ctor(some, ...) pattern, got {pat:?}"
                    );
                    assert!(
                        matches!(scrutinee.as_ref(), SurfaceExpr::Ident(_, ref n) if n == "opt")
                    );
                    assert_eq!(then_branch.len(), 1);
                    assert!(matches!(&then_branch[0], DoElem::Return(_, _)));
                    let else_b = else_branch.as_ref().expect("should have else branch");
                    assert_eq!(else_b.len(), 1);
                    assert!(matches!(&else_b[0], DoElem::Return(_, _)));
                }
                other => panic!("Expected DoElem::IfLet, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_if_decidable() {
    let expr = Parser::parse_expr("do if h : n > 0 then return h else return sorry").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::IfDecidable(_, witness, _prop, then_branch, else_branch) => {
                    assert_eq!(witness, "h");
                    assert_eq!(then_branch.len(), 1);
                    assert!(matches!(&then_branch[0], DoElem::Return(_, _)));
                    let else_b = else_branch.as_ref().expect("should have else branch");
                    assert_eq!(else_b.len(), 1);
                    assert!(matches!(&else_b[0], DoElem::Return(_, _)));
                }
                other => panic!("Expected DoElem::IfDecidable, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_if_no_else() {
    let expr = Parser::parse_expr("do if cond then return 1").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::If(_, _, then_branch, else_branch) => {
                    assert_eq!(then_branch.len(), 1);
                    assert!(else_branch.is_none(), "No else branch expected");
                }
                other => panic!("Expected DoElem::If, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_if_else_if_chain() {
    let expr =
        Parser::parse_expr("do if a then return 1 else if b then return 2 else return 3").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::If(_, _, then_branch, else_branch) => {
                    assert_eq!(then_branch.len(), 1);
                    let else_b = else_branch.as_ref().expect("should have else branch");
                    assert_eq!(else_b.len(), 1);
                    // The else branch should be a nested DoElem::If
                    assert!(
                        matches!(&else_b[0], DoElem::If(_, _, _, _)),
                        "Expected nested DoElem::If in else branch"
                    );
                }
                other => panic!("Expected DoElem::If, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_unless_requires_do_keyword() {
    let err = Parser::parse_expr("do unless cond return 1").unwrap_err();
    match err {
        ParseError::UnexpectedToken { message, .. } => {
            assert!(message.contains("expected `do` in unless expression"));
        }
        other => panic!("Expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_parse_do_unless_lowers_to_if() {
    let expr = Parser::parse_expr("do\n  unless cond do\n    return 1\n  return 2").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::If(_, cond, then_branch, else_branch) => {
                    assert!(matches!(cond.as_ref(), SurfaceExpr::Ident(_, name) if name == "cond"));
                    assert_eq!(then_branch.len(), 1);
                    // The "skip" branch is a SEQUENCED `pure ()` (Expr), NOT a
                    // `return ()`: inside a block with a later `return`, an early
                    // `return ()` exits the whole block with `Unit`.
                    assert!(matches!(
                        &then_branch[0],
                        DoElem::Expr(_, expr)
                            if matches!(expr.as_ref(), SurfaceExpr::App(_, func, _)
                                if matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "pure"))
                    ));
                    let else_branch = else_branch
                        .as_ref()
                        .expect("unless should have else branch");
                    assert_eq!(else_branch.len(), 1);
                    assert!(matches!(&else_branch[0], DoElem::Return(_, _)));
                }
                other => panic!("Expected DoElem::If, got {other:?}"),
            }
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_when_lowers_to_if() {
    // `when cond do body` is the mirror of `unless`: `if cond then body else
    // pure ()`. The then-branch is the body; the else (skip) branch is a
    // sequenced `pure ()` (NOT `return ()`). Previously `when` was not
    // recognized as a do-statement.
    let expr = Parser::parse_expr("do\n  when cond do\n    return 1\n  return 2").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::If(_, cond, then_branch, else_branch) => {
                    assert!(matches!(cond.as_ref(), SurfaceExpr::Ident(_, name) if name == "cond"));
                    // then-branch = the body (`return 1`).
                    assert_eq!(then_branch.len(), 1);
                    assert!(matches!(&then_branch[0], DoElem::Return(_, _)));
                    // else (skip) branch = a sequenced `pure ()`.
                    let else_branch = else_branch.as_ref().expect("when should have else branch");
                    assert_eq!(else_branch.len(), 1);
                    assert!(matches!(
                        &else_branch[0],
                        DoElem::Expr(_, expr)
                            if matches!(expr.as_ref(), SurfaceExpr::App(_, func, _)
                                if matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "pure"))
                    ));
                }
                other => panic!("Expected DoElem::If, got {other:?}"),
            }
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_have_lowers_to_let() {
    let expr = Parser::parse_expr("do have h : Nat := 1; return h").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            assert!(matches!(&elems[0], DoElem::Let(_, binder, _) if binder.name == "h"));
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_have_with_binders() {
    let expr = Parser::parse_expr("do have f (n : Nat) : Nat := n; return f 0").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::Let(_, binder, val) => {
                    assert_eq!(binder.name, "f");
                    assert!(binder.ty.is_some(), "expected explicit return type");
                    match val.as_ref() {
                        SurfaceExpr::Lambda(_, binders, body) => {
                            assert_eq!(binders.len(), 1);
                            assert_eq!(binders[0].name, "n");
                            assert!(matches!(
                                body.as_ref(),
                                SurfaceExpr::Ident(_, name) if name == "n"
                            ));
                        }
                        other => panic!("Expected lambda-wrapped have value, got {other:?}"),
                    }
                }
                other => panic!("Expected DoElem::Let, got {other:?}"),
            }
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_have_with_binders_wraps_full_function_type() {
    let expr = Parser::parse_expr("do have f (n : Nat) : Nat := n; return f 0").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => match &elems[0] {
            DoElem::Let(_, binder, _) => match binder.ty.as_deref() {
                Some(SurfaceExpr::Pi(_, binders, body)) => {
                    assert_eq!(binders.len(), 1);
                    assert_eq!(binders[0].name, "n");
                    assert!(matches!(
                        body.as_ref(),
                        SurfaceExpr::Ident(_, name) if name == "Nat"
                    ));
                }
                other => panic!("Expected Pi binder type for do-have function, got {other:?}"),
            },
            other => panic!("Expected DoElem::Let, got {other:?}"),
        },
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_rec() {
    let expr = Parser::parse_expr("do let rec f (n : Nat) : Nat := f n; return f 0").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::LetRec(_, decls) => {
                    assert_eq!(decls.len(), 1);
                    assert_eq!(decls[0].0.name, "f");
                    assert!(matches!(decls[0].1.as_ref(), SurfaceExpr::Lambda(_, _, _)));
                }
                other => panic!("Expected DoElem::LetRec, got {other:?}"),
            }
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_rec_with_binders_wraps_full_function_type() {
    let expr = Parser::parse_expr("do let rec f (n : Nat) : Nat := f n; return f 0").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => match &elems[0] {
            DoElem::LetRec(_, decls) => match decls[0].0.ty.as_deref() {
                Some(SurfaceExpr::Pi(_, binders, body)) => {
                    assert_eq!(binders.len(), 1);
                    assert_eq!(binders[0].name, "n");
                    assert!(matches!(
                        body.as_ref(),
                        SurfaceExpr::Ident(_, name) if name == "Nat"
                    ));
                }
                other => panic!("Expected Pi binder type for do-let-rec function, got {other:?}"),
            },
            other => panic!("Expected DoElem::LetRec, got {other:?}"),
        },
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_rec_mutual_and() {
    // Lean 4 `let rec ... and ...` uses indentation: `and` at the do-element
    // indent level causes parse_do_elem_expr to stop before consuming it.
    let expr = Parser::parse_expr(
        "do\n  let rec f (n : Nat) : Nat := g n\n  and g (n : Nat) : Nat := f n\n  return f 0",
    )
    .unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::LetRec(_, decls) => {
                    assert_eq!(decls.len(), 2, "expected 2 mutual declarations");
                    assert_eq!(decls[0].0.name, "f");
                    assert_eq!(decls[1].0.name, "g");
                    assert!(matches!(decls[0].1.as_ref(), SurfaceExpr::Lambda(_, _, _)));
                    assert!(matches!(decls[1].1.as_ref(), SurfaceExpr::Lambda(_, _, _)));
                }
                other => panic!("Expected DoElem::LetRec, got {other:?}"),
            }
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_rec_triple_and() {
    let expr = Parser::parse_expr(
        "do\n  let rec a := b 0\n  and b (n : Nat) := c n\n  and c (n : Nat) := a\n  return a",
    )
    .unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::LetRec(_, decls) => {
                    assert_eq!(decls.len(), 3, "expected 3 mutual declarations");
                    assert_eq!(decls[0].0.name, "a");
                    assert_eq!(decls[1].0.name, "b");
                    assert_eq!(decls[2].0.name, "c");
                }
                other => panic!("Expected DoElem::LetRec, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_assert_as_expr() {
    let expr = Parser::parse_expr("do assert! cond; return ()").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::Expr(_, expr) => match expr.as_ref() {
                    SurfaceExpr::App(_, func, args) => {
                        assert!(
                            matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "assert!")
                        );
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("Expected assert! application, got {other:?}"),
                },
                other => panic!("Expected DoElem::Expr, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_debug_assert_as_expr() {
    let expr = Parser::parse_expr("do debug_assert! cond; return ()").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::Expr(_, expr) => match expr.as_ref() {
                    SurfaceExpr::App(_, func, _) => {
                        assert!(
                            matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "debug_assert!")
                        );
                    }
                    other => panic!("Expected debug_assert! application, got {other:?}"),
                },
                other => panic!("Expected DoElem::Expr, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_match_expr() {
    let expr =
        Parser::parse_expr("do match_expr x with | some y => return y | _ => return x").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::Match(_, discrs, arms) => {
                    assert_eq!(discrs.len(), 1);
                    assert_eq!(arms.len(), 2);
                    assert!(matches!(
                        &arms[0].patterns[0],
                        SurfacePattern::Ctor(name, args) if name == "some" && args.len() == 1
                    ));
                    assert!(matches!(&arms[1].patterns[0], SurfacePattern::Wildcard));
                }
                other => panic!("Expected DoElem::Match, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_match_expr_meta_false() {
    let expr = Parser::parse_expr(
        "do match_expr (meta := false) x with | some y => return y | _ => return x",
    )
    .unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            assert!(matches!(&elems[0], DoElem::Match(_, _, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_expr_pure() {
    let expr =
        Parser::parse_expr("do let_expr some y := x | { return fallback }; return y").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::LetExpr(_, pat, discr, kind, fallback) => {
                    assert!(matches!(pat, SurfacePattern::Ctor(name, _) if name == "some"));
                    assert!(matches!(discr.as_ref(), SurfaceExpr::Ident(_, name) if name == "x"));
                    assert_eq!(*kind, DoLetExprKind::Pure);
                    assert_eq!(fallback.len(), 1);
                    assert!(matches!(&fallback[0], DoElem::Return(_, _)));
                }
                other => panic!("Expected DoElem::LetExpr, got {other:?}"),
            }
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_expr_bind() {
    let expr =
        Parser::parse_expr("do let_expr some y <- x | { return fallback }; return y").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::LetExpr(_, pat, _, kind, fallback) => {
                    assert!(matches!(pat, SurfacePattern::Ctor(name, _) if name == "some"));
                    assert_eq!(*kind, DoLetExprKind::Bind);
                    assert_eq!(fallback.len(), 1);
                    assert!(matches!(&fallback[0], DoElem::Return(_, _)));
                }
                other => panic!("Expected DoElem::LetExpr, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

// ── pattern reassignment tests ──────────────────────────────────────

#[test]
fn test_parse_do_pattern_reassign_pair() {
    let expr = Parser::parse_expr("do (a, b) := getState; return a").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::PatternReassign(_, pat, _val) => {
                    // (a, b) → Prod.mk [Var("a"), Var("b")]
                    match pat {
                        SurfacePattern::Ctor(name, args) => {
                            assert_eq!(name, "Prod.mk");
                            assert_eq!(args.len(), 2);
                            assert!(matches!(&args[0], SurfacePattern::Var(n) if n == "a"));
                            assert!(matches!(&args[1], SurfacePattern::Var(n) if n == "b"));
                        }
                        other => panic!("Expected Ctor(Prod.mk), got {other:?}"),
                    }
                }
                other => panic!("Expected PatternReassign, got {other:?}"),
            }
            assert!(matches!(&elems[1], DoElem::Return(_, _)));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_pattern_reassign_triple() {
    let expr = Parser::parse_expr("do (a, b, c) := val; return a").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::PatternReassign(_, pat, _) => {
                    // (a, b, c) → Prod.mk [Var("a"), Prod.mk [Var("b"), Var("c")]]
                    match pat {
                        SurfacePattern::Ctor(name, args) if name == "Prod.mk" => {
                            assert_eq!(args.len(), 2);
                            assert!(matches!(&args[0], SurfacePattern::Var(n) if n == "a"));
                            assert!(matches!(&args[1], SurfacePattern::Ctor(n, inner)
                                if n == "Prod.mk" && inner.len() == 2));
                        }
                        other => panic!("Expected nested Prod.mk, got {other:?}"),
                    }
                }
                other => panic!("Expected PatternReassign, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

// ── do try/catch flat form tests (#2969) ────────────────────────────

#[test]
fn test_parse_do_try_catch_flat() {
    // Flat single-line: `do try pure 1 catch e => pure 0`
    // The parser must treat `catch` as a clause boundary, not an application arg.
    let expr = Parser::parse_expr("do try pure 1 catch e => pure 0").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1, "expected one TryCatch element");
            match &elems[0] {
                DoElem::TryCatch(_, try_body, catches, finally_body) => {
                    assert_eq!(try_body.len(), 1, "try body should have one element");
                    assert_eq!(catches.len(), 1, "should have one catch clause");
                    assert!(finally_body.is_none(), "no finally clause");
                    assert_eq!(catches[0].binder, "e");
                }
                other => panic!("Expected TryCatch, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_try_finally_flat() {
    // Flat single-line: `do try pure 1 finally pure 2`
    let expr = Parser::parse_expr("do try pure 1 finally pure 2").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::TryCatch(_, try_body, catches, finally_body) => {
                    assert_eq!(try_body.len(), 1);
                    assert!(catches.is_empty(), "no catch clauses");
                    assert!(finally_body.is_some(), "should have finally clause");
                    let fb = finally_body.as_ref().unwrap();
                    assert_eq!(fb.len(), 1, "finally body should have one element");
                }
                other => panic!("Expected TryCatch, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_try_catch_finally_flat() {
    // Flat single-line: `do try pure 1 catch e => pure 0 finally pure 2`
    let expr = Parser::parse_expr("do try pure 1 catch e => pure 0 finally pure 2").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::TryCatch(_, try_body, catches, finally_body) => {
                    assert_eq!(try_body.len(), 1);
                    assert_eq!(catches.len(), 1);
                    assert!(finally_body.is_some());
                }
                other => panic!("Expected TryCatch, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

// ── irrefutable destructuring let in do blocks ───────────────────────
//
// `let (a, b) := e` / `let ⟨a, b⟩ := e` (no `| fallback`) desugars to
// `match e with | pat => rest`, consuming the remaining do-sequence as the
// single irrefutable arm. Regression for the trust-ir `Sem.bindFresh`
// cascade (Track MN): the parenthesized tuple pattern previously fell through
// to the simple-binder path and hard-failed on `(`, dropping the whole decl,
// which then surfaced downstream as "cannot extract type name from Pi".

#[test]
fn test_parse_do_let_tuple_pattern_desugars_to_match() {
    let expr = Parser::parse_expr("do let (a, b) := p; pure (a + b)").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            // The tuple-let consumes the trailing sequence into a single match.
            assert_eq!(elems.len(), 1, "tuple-let should fold rest into a match");
            match &elems[0] {
                DoElem::Match(_, discrs, arms) => {
                    assert_eq!(discrs.len(), 1);
                    assert!(matches!(discrs[0], SurfaceExpr::Ident(_, ref n) if n == "p"));
                    assert_eq!(arms.len(), 1, "irrefutable: exactly one arm");
                    assert!(matches!(
                        &arms[0].patterns[0],
                        SurfacePattern::Ctor(name, args) if name == "Prod.mk" && args.len() == 2
                    ));
                    // The arm body carries the continuation (`pure (a + b)`).
                    assert_eq!(arms[0].body.len(), 1);
                }
                other => panic!("Expected DoElem::Match, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_anon_ctor_pattern_desugars_to_match() {
    let expr = Parser::parse_expr("do let ⟨a, b⟩ := p; pure b").unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            assert!(matches!(
                &elems[0],
                DoElem::Match(_, discrs, arms)
                    if discrs.len() == 1
                        && arms.len() == 1
                        && matches!(
                            &arms[0].patterns[0],
                            SurfacePattern::Ctor(name, args) if name == "Prod.mk" && args.len() == 2
                        )
            ));
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_bare_paren_not_treated_as_destructuring() {
    // `let (x) := e` is a parenthesized *variable*, not a destructuring tuple, so
    // the irrefutable-pattern path must DECLINE it (it parses to `Var("x")`, not
    // a `Prod.mk` ctor) and restore position. Parenthesized single binders are
    // not otherwise supported by the do-let binder grammar (pre-existing), so it
    // surfaces the historical "expected identifier" error rather than a match —
    // confirming the new path does not steal this shape.
    let err = Parser::parse_expr("do let (x) := n; pure x");
    assert!(
        err.is_err(),
        "bare-paren let must not be folded into a destructuring match"
    );
}

#[test]
fn test_parse_do_let_tuple_pattern_multiline_continuation() {
    // The real trust-ir shape: newline-separated continuation after the
    // destructuring let (this is the `Sem.bindFresh` body pattern).
    let src = "do\n  let (a, b) := p\n  let c := a\n  pure (b + c)";
    let expr = Parser::parse_expr(src).unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1, "destructuring let folds the whole tail");
            match &elems[0] {
                DoElem::Match(_, _, arms) => {
                    assert_eq!(arms.len(), 1);
                    // Arm body holds the two trailing statements (`let c`, `pure`).
                    assert_eq!(arms[0].body.len(), 2);
                }
                other => panic!("Expected DoElem::Match, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_tuple_pattern_monadic_bind_desugars() {
    // `let (a, b) ← e` (monadic destructuring bind) previously fell through the
    // irrefutable-`:=`-only path and the simple-binder path, hard-failing on the
    // `(` and tripping decl-level parser recovery ("raw declaration") — exactly
    // the `decodePackLanes`/`decodeExtractLane` shape in trust-ir's
    // Semantics/VectorDialect.lean (`let (elemTy, lanes) ← supportedLaneVectorTy …`).
    // Now it desugars to `e >>= fun __x => match __x with | (a,b) => rest`,
    // expressed as a nested Bind+Match do-block.
    let src = "do\n  let (a, b) ← e\n  pure (a + b)";
    let expr = Parser::parse_expr(src).unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1, "monadic destructuring bind folds the tail");
            // The new element is a `DoElem::Expr` wrapping a nested do-block of
            // [Bind(fresh, e), Match([fresh], | (a,b) => rest)].
            match &elems[0] {
                DoElem::Expr(_, inner) => match inner.as_ref() {
                    SurfaceExpr::Do(_, inner_elems) => {
                        assert_eq!(inner_elems.len(), 2);
                        assert!(matches!(&inner_elems[0], DoElem::Bind(_, _, _)));
                        assert!(matches!(
                            &inner_elems[1],
                            DoElem::Match(_, discrs, arms)
                                if discrs.len() == 1
                                    && arms.len() == 1
                                    && matches!(
                                        &arms[0].patterns[0],
                                        SurfacePattern::Ctor(name, args)
                                            if name == "Prod.mk" && args.len() == 2
                                    )
                        ));
                    }
                    other => panic!("Expected nested Do, got {other:?}"),
                },
                other => panic!("Expected DoElem::Expr wrapping a Do, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_let_anon_ctor_pattern_monadic_bind_desugars() {
    // The `⟨a, b⟩ ←` anonymous-constructor form of the same monadic destructuring
    // bind also parses (rather than tripping parser recovery).
    let src = "do\n  let ⟨a, b⟩ ← e\n  pure (a + b)";
    let expr = Parser::parse_expr(src).unwrap();
    assert!(matches!(expr, SurfaceExpr::Do(_, elems) if elems.len() == 1));
}
