// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::AttributeCommandAttr;
use crate::LevelExpr;

#[test]
fn test_parse_ident() {
    let expr = Parser::parse_expr("x").unwrap();
    assert!(matches!(expr, SurfaceExpr::Ident(_, s) if s == "x"));
}

#[test]
fn test_parse_escaped_ident() {
    let expr = Parser::parse_expr("«if»").unwrap();
    assert!(matches!(expr, SurfaceExpr::Ident(_, s) if s == "if"));
}

#[test]
fn test_parse_nat_lit() {
    let expr = Parser::parse_expr("42").unwrap();
    assert!(matches!(expr, SurfaceExpr::Lit(_, SurfaceLit::Nat(42))));
}

#[test]
fn test_parse_type() {
    let expr = Parser::parse_expr("Type").unwrap();
    assert!(matches!(expr, SurfaceExpr::Universe(_, UniverseExpr::Type)));
}

#[test]
fn test_parse_type_star() {
    // Type* is Mathlib syntax for implicit universe level
    let expr = Parser::parse_expr("Type*").unwrap();
    assert!(matches!(
        expr,
        SurfaceExpr::Universe(_, UniverseExpr::TypeImplicit)
    ));
}

#[test]
fn test_parse_type_star_in_binder() {
    // Common usage: {P : Type*}
    let decls = Parser::parse_file("variable {P : Type*}").unwrap();
    assert_eq!(decls.len(), 1);
}

#[test]
fn test_parse_type_parenthesized_level_expr() {
    let expr = Parser::parse_expr("Type (max u v)").unwrap();
    assert!(
        matches!(
            &expr,
            SurfaceExpr::Universe(
                _,
                UniverseExpr::TypeLevel(level),
            ) if matches!(
                level.as_ref(),
                LevelExpr::Max(lhs, rhs)
                    if matches!(lhs.as_ref(), LevelExpr::Param(lhs) if lhs == "u")
                        && matches!(rhs.as_ref(), LevelExpr::Param(rhs) if rhs == "v")
            )
        ),
        "expected `Type (max u v)` to parse as a universe level expression, got {expr:?}"
    );
}

#[test]
fn test_parse_prop() {
    let expr = Parser::parse_expr("Prop").unwrap();
    assert!(matches!(expr, SurfaceExpr::Universe(_, UniverseExpr::Prop)));
}

#[test]
fn test_parse_app() {
    let expr = Parser::parse_expr("f x y").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, s) if s == "f"));
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected App"),
    }
}

#[test]
fn test_parse_arrow() {
    let expr = Parser::parse_expr("A -> B").unwrap();
    match expr {
        SurfaceExpr::Arrow(_, left, right) => {
            assert!(matches!(*left, SurfaceExpr::Ident(_, s) if s == "A"));
            assert!(matches!(*right, SurfaceExpr::Ident(_, s) if s == "B"));
        }
        _ => panic!("expected Arrow"),
    }
}

#[test]
fn test_parse_arrow_unicode() {
    let expr = Parser::parse_expr("A → B → C").unwrap();
    // Should be right associative: A → (B → C)
    match expr {
        SurfaceExpr::Arrow(_, left, right) => {
            assert!(matches!(*left, SurfaceExpr::Ident(_, s) if s == "A"));
            assert!(matches!(*right, SurfaceExpr::Arrow(_, _, _)));
        }
        _ => panic!("expected Arrow"),
    }
}

#[test]
fn test_parse_lambda() {
    let expr = Parser::parse_expr("fun x => x").unwrap();
    match expr {
        SurfaceExpr::Lambda(_, binders, body) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(binders[0].name, "x");
            assert!(matches!(*body, SurfaceExpr::Ident(_, s) if s == "x"));
        }
        _ => panic!("expected Lambda"),
    }
}

#[test]
fn test_parse_lambda_typed() {
    let expr = Parser::parse_expr("fun (x : Nat) => x").unwrap();
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1);
            let _ty = binders[0]
                .ty
                .as_ref()
                .expect("typed lambda binder should have type annotation");
        }
        _ => panic!("expected Lambda"),
    }
}

#[test]
fn test_parse_lambda_tuple_paren_destructures_to_single_param_match() {
    // `fun (a, b) => a` is a *single*-parameter lambda whose argument is a
    // tuple, pattern-matched. Arity must be 1, not 2. Desugars to the same
    // shape as `fun | (a, b) => a`.
    let expr = Parser::parse_expr("fun (a, b) => a").expect("tuple-destructuring lambda parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            assert_eq!(binders.len(), 1, "tuple lambda has arity 1, not 2");
            match *body {
                SurfaceExpr::Match(_, _, scrutinee, arms) => {
                    assert!(
                        matches!(*scrutinee, SurfaceExpr::Ident(_, ref s) if *s == binders[0].name)
                    );
                    assert_eq!(arms.len(), 1);
                    match &arms[0].pattern {
                        SurfacePattern::Ctor(name, fields) => {
                            assert_eq!(name, "Prod.mk");
                            assert_eq!(fields.len(), 2);
                            assert!(matches!(&fields[0], SurfacePattern::Var(s) if s == "a"));
                            assert!(matches!(&fields[1], SurfacePattern::Var(s) if s == "b"));
                        }
                        other => panic!("expected Prod.mk pattern, got {other:?}"),
                    }
                    assert!(matches!(arms[0].body, SurfaceExpr::Ident(_, ref s) if s == "a"));
                }
                other => panic!("expected Match body, got {other:?}"),
            }
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_tuple_angle_destructures_to_single_param_match() {
    // `fun ⟨a, b⟩ => b` — anonymous-constructor binder, also a single param.
    let expr = Parser::parse_expr("fun ⟨a, b⟩ => b").expect("angle-destructuring lambda parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            assert_eq!(binders.len(), 1);
            match *body {
                SurfaceExpr::Match(_, _, _, arms) => {
                    assert_eq!(arms.len(), 1);
                    assert!(matches!(
                        &arms[0].pattern,
                        SurfacePattern::Ctor(name, fields)
                            if name == "Prod.mk" && fields.len() == 2
                    ));
                }
                other => panic!("expected Match body, got {other:?}"),
            }
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_mixed_binder_and_tuple_keeps_param_order() {
    // `fun x (a, b) => x` — an ordinary binder followed by a tuple binder.
    // Arity is 2 (x and the tuple), with only the tuple pattern-matched.
    let expr = Parser::parse_expr("fun x (a, b) => x").expect("mixed binder/tuple lambda parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            assert_eq!(binders.len(), 2);
            assert_eq!(binders[0].name, "x");
            // The second binder is the fresh scrutinee for the tuple.
            match *body {
                SurfaceExpr::Match(_, _, scrutinee, arms) => {
                    assert!(
                        matches!(*scrutinee, SurfaceExpr::Ident(_, ref s) if *s == binders[1].name)
                    );
                    assert_eq!(arms.len(), 1);
                }
                other => panic!("expected Match body, got {other:?}"),
            }
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_two_tuple_binders_nests_matches() {
    // `fun (a, b) (c, d) => a` — two tuple binders desugar to nested matches
    // with two fresh scrutinee binders.
    let expr = Parser::parse_expr("fun (a, b) (c, d) => a").expect("two-tuple lambda parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            assert_eq!(binders.len(), 2);
            // Outer match is over the first scrutinee; its arm body is the
            // inner match over the second scrutinee.
            match *body {
                SurfaceExpr::Match(_, _, _, arms) => {
                    assert_eq!(arms.len(), 1);
                    assert!(matches!(arms[0].body, SurfaceExpr::Match(_, _, _, _)));
                }
                other => panic!("expected outer Match, got {other:?}"),
            }
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Gap A: `#[...]` array literals desugar to `Array.mk` over a backing `List`.
// ---------------------------------------------------------------------------

#[test]
fn test_parse_array_literal_desugars_to_array_mk_of_list() {
    // `#[1, 2, 3]` desugars to `Array.mk (List.cons 1 (List.cons 2
    // (List.cons 3 List.nil)))` — a single `List` argument, NOT positional
    // varargs. Assert the head is `Array.mk` applied to exactly one arg whose
    // spine is a `List.cons` chain.
    let expr = Parser::parse_expr("#[1, 2, 3]").expect("array literal parses");
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "Array.mk"),
                "array literal head must be Array.mk, got {func:?}"
            );
            assert_eq!(args.len(), 1, "Array.mk takes one (backing List) argument");
            // The single argument is a List.cons chain.
            match &args[0].expr {
                SurfaceExpr::App(_, cons, cons_args) => {
                    assert!(
                        matches!(**cons, SurfaceExpr::Ident(_, ref s) if s == "List.cons"),
                        "backing list head must be List.cons, got {cons:?}"
                    );
                    assert_eq!(cons_args.len(), 2, "List.cons is head + tail");
                    assert!(matches!(
                        cons_args[0].expr,
                        SurfaceExpr::Lit(_, SurfaceLit::Nat(1))
                    ));
                }
                other => panic!("expected List.cons chain, got {other:?}"),
            }
        }
        other => panic!("expected App(Array.mk, ..), got {other:?}"),
    }
}

#[test]
fn test_parse_empty_array_literal_desugars_to_array_mk_nil() {
    // `#[]` must desugar to `Array.mk List.nil` (a fully-applied `Array.mk`),
    // not an under-applied `Array.mk` that leaks a free variable.
    let expr = Parser::parse_expr("#[]").expect("empty array literal parses");
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "Array.mk"));
            assert_eq!(args.len(), 1);
            assert!(
                matches!(&args[0].expr, SurfaceExpr::Ident(_, s) if s == "List.nil"),
                "empty array backing must be List.nil"
            );
        }
        other => panic!("expected App(Array.mk, List.nil), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Gap B: forward pipe `|>` and `|>.`.
// ---------------------------------------------------------------------------

#[test]
fn test_parse_forward_pipe_application_desugars_to_call() {
    // `n |> f` desugars to `f n` (low-precedence application).
    let expr = Parser::parse_expr("n |> f").expect("forward pipe parses");
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "f"));
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0].expr, SurfaceExpr::Ident(_, s) if s == "n"));
        }
        other => panic!("expected App(f, n), got {other:?}"),
    }
}

#[test]
fn test_parse_forward_pipe_projection_desugars_to_proj() {
    // `n |>.succ` desugars to `n.succ` (a projection / dot-notation call).
    let expr = Parser::parse_expr("n |>.succ").expect("forward pipe projection parses");
    match expr {
        SurfaceExpr::Proj(_, base, proj) => {
            assert!(matches!(*base, SurfaceExpr::Ident(_, ref s) if s == "n"));
            assert!(matches!(proj, Projection::Named(ref f) if f == "succ"));
        }
        other => panic!("expected Proj(n, succ), got {other:?}"),
    }
}

#[test]
fn test_parse_forward_pipe_is_left_associative() {
    // `n |> f |> g` desugars to `g (f n)` (left-associative).
    let expr = Parser::parse_expr("n |> f |> g").expect("chained forward pipe parses");
    match expr {
        SurfaceExpr::App(_, outer, outer_args) => {
            assert!(matches!(*outer, SurfaceExpr::Ident(_, ref s) if s == "g"));
            assert_eq!(outer_args.len(), 1);
            match &outer_args[0].expr {
                SurfaceExpr::App(_, inner, inner_args) => {
                    assert!(matches!(**inner, SurfaceExpr::Ident(_, ref s) if s == "f"));
                    assert!(matches!(&inner_args[0].expr, SurfaceExpr::Ident(_, s) if s == "n"));
                }
                other => panic!("expected inner App(f, n), got {other:?}"),
            }
        }
        other => panic!("expected outer App(g, ..), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Gap C: multi-pattern match-lambda `fun | p1, p2 => e`.
// ---------------------------------------------------------------------------

#[test]
fn test_parse_multi_pattern_match_lambda_tuples_patterns() {
    // `fun | 0, 0 => 0 | _, _ => 1` is a two-argument match-lambda. It keeps a
    // single `_x` scrutinee binder (the elaborator peels the arity from the
    // tuple pattern) and combines each arm's two patterns into a `Prod.mk`
    // tuple pattern.
    let expr =
        Parser::parse_expr("fun | 0, 0 => 0 | _, _ => 1").expect("multi-pattern lambda parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            assert_eq!(binders.len(), 1, "match-lambda keeps a single _x binder");
            match *body {
                SurfaceExpr::Match(_, _, scrutinee, arms) => {
                    assert!(
                        matches!(*scrutinee, SurfaceExpr::Ident(_, ref s) if *s == binders[0].name)
                    );
                    assert_eq!(arms.len(), 2);
                    for arm in &arms {
                        match &arm.pattern {
                            SurfacePattern::Ctor(name, fields) => {
                                assert_eq!(name, "Prod.mk");
                                assert_eq!(fields.len(), 2);
                            }
                            other => panic!("expected Prod.mk tuple pattern, got {other:?}"),
                        }
                    }
                }
                other => panic!("expected Match body, got {other:?}"),
            }
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_three_pattern_match_lambda_right_nests_prod() {
    // `fun | 0, 0, 0 => 0 | _, _, _ => 1` combines three patterns into a
    // right-nested `Prod.mk p0 (Prod.mk p1 p2)` tuple pattern.
    let expr = Parser::parse_expr("fun | 0, 0, 0 => 0 | _, _, _ => 1")
        .expect("three-pattern lambda parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            assert_eq!(binders.len(), 1);
            match *body {
                SurfaceExpr::Match(_, _, _, arms) => match &arms[0].pattern {
                    SurfacePattern::Ctor(name, fields) => {
                        assert_eq!(name, "Prod.mk");
                        assert_eq!(fields.len(), 2);
                        // The tail is itself a Prod.mk (right-nested).
                        assert!(matches!(
                            &fields[1],
                            SurfacePattern::Ctor(n, f) if n == "Prod.mk" && f.len() == 2
                        ));
                    }
                    other => panic!("expected right-nested Prod.mk, got {other:?}"),
                },
                other => panic!("expected Match body, got {other:?}"),
            }
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_single_pattern_match_lambda_unchanged() {
    // Regression / control: the single-pattern `fun | p => e` form must still
    // parse to a `PatternMatchLambda` with one binder and a NON-tuple pattern.
    let expr = Parser::parse_expr("fun | 0 => 1 | n => n").expect("single-pattern lambda parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            assert_eq!(binders.len(), 1);
            match *body {
                SurfaceExpr::Match(_, _, _, arms) => {
                    assert_eq!(arms.len(), 2);
                    // Not tupled: the first arm's pattern is a bare literal.
                    assert!(
                        !matches!(&arms[0].pattern, SurfacePattern::Ctor(n, _) if n == "Prod.mk"),
                        "single-pattern arm must not be tupled"
                    );
                }
                other => panic!("expected Match body, got {other:?}"),
            }
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_single_typed_binder_stays_plain_lambda() {
    // Near-miss negative: `fun (x : Nat) => x` is NOT destructuring — the `(`
    // encloses a typed binder, not a tuple. It must remain a plain `Lambda`
    // with one binder, not a PatternMatchLambda.
    let expr = Parser::parse_expr("fun (x : Nat) => x").expect("typed binder lambda parses");
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(binders[0].name, "x");
            assert!(binders[0].ty.is_some(), "binder keeps its type annotation");
        }
        other => panic!("expected plain Lambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_multi_binder_shares_type_annotation() {
    // Regression: an unparenthesized run of binder names `a b : Nat` must
    // distribute the trailing type to EVERY name (matching Lean), not just the
    // last. Previously only `b` got `Nat` and `a` was left untyped, which turned
    // an unused-in-body binder into an unresolved metavariable downstream.
    let expr =
        Parser::parse_expr("fun a b c : Nat => a").expect("multi-binder typed lambda parses");
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 3, "three names bind three params");
            for (i, name) in ["a", "b", "c"].iter().enumerate() {
                assert_eq!(&binders[i].name, name);
                assert!(
                    binders[i].ty.is_some(),
                    "every name in `a b c : Nat` must carry the shared type, incl. `{name}`"
                );
            }
        }
        other => panic!("expected Lambda with 3 typed binders, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_paren_single_name_stays_plain_lambda() {
    // `fun (x) => x` is a parenthesized single binder, not a tuple — no comma,
    // so it stays a plain one-arity Lambda.
    let expr = Parser::parse_expr("fun (x) => x").expect("parenthesized binder lambda parses");
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(binders[0].name, "x");
        }
        other => panic!("expected plain Lambda, got {other:?}"),
    }
}

#[test]
fn test_parse_match_lambda_angle_pattern_parses() {
    // The angle-bracket anonymous-constructor pattern now also works in the
    // explicit match-lambda form `fun | ⟨a, b⟩ => e`.
    let expr = Parser::parse_expr("fun | ⟨a, b⟩ => a").expect("angle match-lambda pattern parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, _, body) => match *body {
            SurfaceExpr::Match(_, _, _, arms) => {
                assert!(matches!(
                    &arms[0].pattern,
                    SurfacePattern::Ctor(name, fields)
                        if name == "Prod.mk" && fields.len() == 2
                ));
            }
            other => panic!("expected Match body, got {other:?}"),
        },
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_match_string_literal_pattern_parses() {
    // String-literal patterns: `match op with | "pack_lanes" => …`. Previously
    // the pattern parser had no `StringLit` case, so string patterns fell to the
    // catch-all error and tripped decl-level recovery ("raw declaration") —
    // exactly the `decode` shape in trust-ir's Semantics/VectorDialect.lean
    // (`match inst.op with | "pack_lanes" => …`).
    let expr = Parser::parse_expr("match op with | \"pack\" => 1 | _ => 0")
        .expect("string-literal pattern parses");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert!(matches!(
                &arms[0].pattern,
                SurfacePattern::Lit(SurfaceLit::String(s)) if s == "pack"
            ));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_match_discr_hyp_binds_name() {
    // Lean's annotated discriminant (`Lean/Parser/Term.lean:275 matchDiscr`):
    // `match h : n with | ...` records the hypothesis name on the Match node
    // (audit d01 -- previously tripped decl-level recovery).
    let expr = Parser::parse_expr("match h : n with | 0 => 0 | k + 1 => k")
        .expect("annotated discriminant parses");
    match expr {
        SurfaceExpr::Match(_, hyp, scrut, arms) => {
            assert_eq!(
                hyp.as_deref(),
                Some("h"),
                "hypothesis name must be recorded"
            );
            assert!(
                matches!(&*scrut, SurfaceExpr::Ident(_, n) if n == "n"),
                "scrutinee must be the bare term after `h : `, got {scrut:?}"
            );
            assert_eq!(arms.len(), 2);
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_match_discr_hyp_underscore_binder() {
    // `binderIdent` includes `_`: `match _ : e with ...`.
    let expr = Parser::parse_expr("match _ : n with | 0 => 0 | _ => 1")
        .expect("underscore-annotated discriminant parses");
    match expr {
        SurfaceExpr::Match(_, hyp, _, _) => {
            assert_eq!(hyp.as_deref(), Some("_"));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_match_plain_discriminant_has_no_hyp() {
    let expr = Parser::parse_expr("match n with | 0 => 0 | _ => 1").expect("plain match parses");
    match expr {
        SurfaceExpr::Match(_, hyp, _, _) => {
            assert_eq!(
                hyp, None,
                "plain `match e with` must not record a hypothesis"
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_match_cons_scrutinee_not_taken_as_hyp() {
    // `h :: t` must stay a cons-expression scrutinee -- only a bare ident
    // followed by a single `:` token is the annotated-discriminant prefix
    // (the `atomic (binderIdent >> " : ")` in Lean's matchDiscr).
    let expr =
        Parser::parse_expr("match h :: t with | [] => 0 | _ => 1").expect("cons scrutinee parses");
    match expr {
        SurfaceExpr::Match(_, hyp, scrut, _) => {
            assert_eq!(hyp, None, "`h :: t` must not be split into a hypothesis");
            assert!(
                matches!(&*scrut, SurfaceExpr::App(..)),
                "scrutinee must be the cons application, got {scrut:?}"
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_match_discr_hyp_multi_discriminant_errors_loud() {
    // Clean packs multi-discriminant matches into one `Prod.mk` scrutinee,
    // which cannot carry a per-discriminant equation -- refuse loudly rather
    // than silently dropping the hypothesis.
    let err = Parser::parse_expr("match h : a, b with | _, _ => 0")
        .expect_err("hypothesis + multiple discriminants must be a parse error");
    assert!(
        format!("{err:?}").contains("multiple discriminants"),
        "error must name the unsupported shape, got {err:?}"
    );
    let err2 = Parser::parse_expr("match a, h : b with | _, _ => 0")
        .expect_err("hypothesis on a later discriminant must be a parse error");
    assert!(
        format!("{err2:?}").contains("multiple discriminants"),
        "error must name the unsupported shape, got {err2:?}"
    );
}

#[test]
fn test_parse_match_char_literal_pattern_parses() {
    // Char-literal patterns: `match c with | 'a' => …`. Same literal-guard
    // lowering as strings.
    let expr = Parser::parse_expr("match c with | 'a' => 1 | _ => 0")
        .expect("char-literal pattern parses");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert!(matches!(
                &arms[0].pattern,
                SurfacePattern::Lit(SurfaceLit::Char(c)) if *c == 'a'
            ));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_ctor_ellipsis_pattern_parses() {
    // `.Ctor ..` — the constructor-field ellipsis used pervasively in
    // `Inst.isTerminator` (`| .Br .. => true`). The `..` must be consumed as a
    // trailing `SurfacePattern::Ellipsis`, not left for the recovery path
    // (which previously produced `ParseError: parser recovery produced raw
    // declaration: DotDot true ...`).
    let expr = Parser::parse_expr("match i with | .Br .. => true | _ => false")
        .expect("ctor `..` pattern parses");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => match &arms[0].pattern {
            SurfacePattern::Ctor(name, args) => {
                assert_eq!(name, "Br");
                assert_eq!(args.len(), 1, "single trailing ellipsis arg");
                assert!(matches!(args[0], SurfacePattern::Ellipsis));
            }
            other => panic!("expected Ctor pattern, got {other:?}"),
        },
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_ctor_leading_pattern_then_ellipsis() {
    // `.Ctor x ..` — explicit leading pattern followed by `..`. The explicit
    // pattern is preserved and the ellipsis is the trailing marker.
    let expr = Parser::parse_expr("match i with | .Br x .. => x | _ => 0")
        .expect("leading pattern + `..` parses");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => match &arms[0].pattern {
            SurfacePattern::Ctor(name, args) => {
                assert_eq!(name, "Br");
                assert_eq!(args.len(), 2);
                assert!(matches!(&args[0], SurfacePattern::Var(v) if v == "x"));
                assert!(matches!(args[1], SurfacePattern::Ellipsis));
            }
            other => panic!("expected Ctor pattern, got {other:?}"),
        },
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_forall() {
    let expr = Parser::parse_expr("forall (x : Type), x").unwrap();
    match expr {
        SurfaceExpr::Pi(_, binders, body) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(binders[0].name, "x");
            assert!(matches!(*body, SurfaceExpr::Ident(_, s) if s == "x"));
        }
        _ => panic!("expected Pi"),
    }
}

#[test]
fn test_parse_let() {
    let expr = Parser::parse_expr("let x := 1 in x").unwrap();
    match expr {
        SurfaceExpr::Let(_, binder, val, body) => {
            assert_eq!(binder.name, "x");
            assert!(matches!(*val, SurfaceExpr::Lit(_, SurfaceLit::Nat(1))));
            assert!(matches!(*body, SurfaceExpr::Ident(_, s) if s == "x"));
        }
        _ => panic!("expected Let"),
    }
}

#[test]
fn test_parse_let_typed() {
    let expr = Parser::parse_expr("let x : Nat := 1 in x").unwrap();
    match expr {
        SurfaceExpr::Let(_, binder, _, _) => {
            let _ty = binder
                .ty
                .as_ref()
                .expect("typed let binder should have type annotation");
        }
        _ => panic!("expected Let"),
    }
}

// Layout-sensitive term-level `let` without an explicit `in`/`;`: the body is
// taken from a following line that dedents to (or below) the `let` keyword's
// column, matching Lean 4's `withPosition` + `checkColGt` for `Term.let`.

#[test]
fn test_parse_let_without_in_newline_body() {
    // `let x := 1` then a newline-aligned body `x + x` (no explicit `in`).
    let expr = Parser::parse_expr("let x := 1\nx + x").expect("let-without-in should parse");
    match expr {
        SurfaceExpr::Let(_, binder, val, body) => {
            assert_eq!(binder.name, "x");
            assert!(
                matches!(*val, SurfaceExpr::Lit(_, SurfaceLit::Nat(1))),
                "value should be just `1`, not `1` applied to the body"
            );
            // body is `x + x`, an application of HAdd.hAdd
            assert!(matches!(*body, SurfaceExpr::App(_, _, _)));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_parse_let_without_in_anon_ctor_body() {
    // `let k := 7` then a newline-aligned `⟨k, k⟩` anonymous-constructor body
    // (no `;`/`in`). The `⟨` (LAngle) must start the implicit let body — a
    // pervasive `let x := v ⏎ ⟨witness, proof⟩` idiom. Regression for the
    // is_implicit_body_start LAngle addition.
    // Previously a ParseError ("error-recovery …") because `⟨` was missing from
    // the implicit-body-start allowlist; now it parses as a `let` whose value is
    // just `7` (not `7` applied to the ⟨⟩ body).
    let expr = Parser::parse_expr("let k := 7\n⟨k, k⟩").expect("let-⟨⟩-body should parse");
    match expr {
        SurfaceExpr::Let(_, binder, val, _body) => {
            assert_eq!(binder.name, "k");
            assert!(
                matches!(*val, SurfaceExpr::Lit(_, SurfaceLit::Nat(7))),
                "value should be `7`, not `7` applied to the ⟨⟩ body, got {val:?}"
            );
        }
        other => panic!("expected Let with ⟨⟩ body, got {other:?}"),
    }
}

#[test]
fn test_parse_let_without_in_body_is_ident() {
    // The body starting with an identifier must not be absorbed as an argument
    // of the value: `let y := 2` / `x + y` parses the body as `x + y`.
    let expr = Parser::parse_expr("let y := 2\nx + y").expect("let-without-in ident body");
    match expr {
        SurfaceExpr::Let(_, binder, val, _body) => {
            assert_eq!(binder.name, "y");
            assert!(matches!(*val, SurfaceExpr::Lit(_, SurfaceLit::Nat(2))));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_parse_chained_let_without_in() {
    // Consecutive `let`s with no `in`, body on the final line.
    let expr = Parser::parse_expr("let x := 1\nlet y := 2\nx + y").expect("chained let-without-in");
    match expr {
        SurfaceExpr::Let(_, b1, _, body) => {
            assert_eq!(b1.name, "x");
            assert!(matches!(*body, SurfaceExpr::Let(_, ref b2, _, _) if b2.name == "y"));
        }
        other => panic!("expected nested Let, got {other:?}"),
    }
}

#[test]
fn test_parse_let_without_in_value_is_application() {
    // The value is itself an application `f a`; the next-line `g x` is the body.
    let expr = Parser::parse_expr("let r := f a\ng x").expect("let app value, app body");
    match expr {
        SurfaceExpr::Let(_, binder, val, body) => {
            assert_eq!(binder.name, "r");
            assert!(matches!(*val, SurfaceExpr::App(_, _, _)), "value is `f a`");
            assert!(matches!(*body, SurfaceExpr::App(_, _, _)), "body is `g x`");
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_parse_let_without_in_multiline_value_continuation() {
    // A continuation line that is *more* indented than the `let` keyword stays
    // part of the value (`f a`); only a line dedented to the keyword column
    // begins the body (`x`). This mirrors Lean's `checkColGt` for app args.
    let expr = Parser::parse_expr("let x := f\n  a\nx").expect("multi-line value continuation");
    match expr {
        SurfaceExpr::Let(_, binder, val, body) => {
            assert_eq!(binder.name, "x");
            assert!(
                matches!(*val, SurfaceExpr::App(_, _, _)),
                "value should be the application `f a` spanning two lines"
            );
            assert!(matches!(*body, SurfaceExpr::Ident(_, s) if s == "x"));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_parse_let_with_explicit_in_still_works() {
    // Regression guard: explicit `in` is unaffected by the layout path.
    let expr = Parser::parse_expr("let x := 1 in x + x").expect("explicit `in` let");
    assert!(matches!(expr, SurfaceExpr::Let(_, _, _, _)));
}

#[test]
fn test_parse_if() {
    let expr = Parser::parse_expr("if c then t else e").unwrap();
    match expr {
        SurfaceExpr::If(_, cond, then_br, else_br) => {
            assert!(matches!(*cond, SurfaceExpr::Ident(_, s) if s == "c"));
            assert!(matches!(*then_br, SurfaceExpr::Ident(_, s) if s == "t"));
            assert!(matches!(*else_br, SurfaceExpr::Ident(_, s) if s == "e"));
        }
        _ => panic!("expected If"),
    }
}

#[test]
fn test_parse_paren() {
    let expr = Parser::parse_expr("(x)").unwrap();
    match expr {
        SurfaceExpr::Paren(_, inner) => {
            assert!(matches!(*inner, SurfaceExpr::Ident(_, s) if s == "x"));
        }
        _ => panic!("expected Paren"),
    }
}

#[test]
fn test_parse_ascription() {
    let expr = Parser::parse_expr("(x : Nat)").unwrap();
    match expr {
        SurfaceExpr::Ascription(_, expr, ty) => {
            assert!(matches!(*expr, SurfaceExpr::Ident(_, s) if s == "x"));
            assert!(matches!(*ty, SurfaceExpr::Ident(_, s) if s == "Nat"));
        }
        _ => panic!("expected Ascription"),
    }
}

#[test]
fn test_show_from_term_produces_ascription() {
    // `show t from e` ascribes the proof term `e` to type `t`.
    let expr = Parser::parse_expr("show True from h").unwrap();
    match expr {
        SurfaceExpr::Ascription(_, value, ty) => {
            assert!(matches!(*value, SurfaceExpr::Ident(_, ref s) if s == "h"));
            assert!(matches!(*ty, SurfaceExpr::Ident(_, ref s) if s == "True"));
        }
        other => panic!("expected Ascription, got {other:?}"),
    }
}

#[test]
fn test_show_by_tactic_produces_ascription_of_by_tactic() {
    // `show t by tac` ascribes a `by` tactic block to type `t`
    // (Lean 4 `Term.show` second form). Without `by` support this previously
    // mis-parsed the type as the application `True (by trivial)`.
    let expr = Parser::parse_expr("show True by trivial").unwrap();
    match expr {
        SurfaceExpr::Ascription(_, value, ty) => {
            assert!(
                matches!(*value, SurfaceExpr::ByTactic(_, _)),
                "expected the justification to be a ByTactic block, got {value:?}"
            );
            assert!(matches!(*ty, SurfaceExpr::Ident(_, ref s) if s == "True"));
        }
        other => panic!("expected Ascription, got {other:?}"),
    }
}

#[test]
fn test_show_by_tactic_with_relation_type_keeps_full_type() {
    // The type before `by` is a full term (here a relation `a = b`),
    // not just an atom: the trailing `by` must not be swallowed into it.
    let expr = Parser::parse_expr("show a = b by rfl").unwrap();
    match expr {
        SurfaceExpr::Ascription(_, value, ty) => {
            assert!(matches!(*value, SurfaceExpr::ByTactic(_, _)));
            // `a = b` desugars to an `Eq a b` application.
            match *ty {
                SurfaceExpr::App(_, ref head, ref args) => {
                    assert!(matches!(**head, SurfaceExpr::Ident(_, ref s) if s == "Eq"));
                    assert_eq!(args.len(), 2);
                }
                other => panic!("expected Eq application as type, got {other:?}"),
            }
        }
        other => panic!("expected Ascription, got {other:?}"),
    }
}

#[test]
fn test_show_by_missing_from_or_by_is_error() {
    // Near-miss: a bare `show t` with neither `from` nor `by` is incomplete
    // and must be rejected rather than silently accepted.
    let result = Parser::parse_expr("show True");
    assert!(
        result.is_err(),
        "bare `show t` without `from`/`by` should be a parse error, got {result:?}"
    );
}

#[test]
fn test_parse_hole() {
    let expr = Parser::parse_expr("_").unwrap();
    assert!(matches!(expr, SurfaceExpr::Hole(_)));
}

#[test]
fn test_parse_def() {
    let decl = Parser::parse_decl("def id (x : Type) := x").unwrap();
    match decl {
        SurfaceDecl::Def { name, binders, .. } => {
            assert_eq!(name, "id");
            assert_eq!(binders.len(), 1);
        }
        _ => panic!("expected Def"),
    }
}

#[test]
fn test_parse_theorem() {
    let decl = Parser::parse_decl("theorem foo : Prop := Prop").unwrap();
    match decl {
        SurfaceDecl::Theorem { name, .. } => {
            assert_eq!(name, "foo");
        }
        _ => panic!("expected Theorem"),
    }
}

#[test]
fn test_parse_complex() {
    // Parse a more complex expression
    let expr = Parser::parse_expr("fun (A : Type) (x : A) => x").unwrap();
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 2);
            assert_eq!(binders[0].name, "A");
            assert_eq!(binders[1].name, "x");
        }
        _ => panic!("expected Lambda"),
    }
}

#[test]
fn test_parse_file() {
    let input = r"
            def id (x : Type) := x
            def const (A : Type) (B : Type) (x : A) := x
            axiom myAxiom : Type
        ";
    let decls = Parser::parse_file(input).unwrap();
    assert_eq!(decls.len(), 3);

    match &decls[0] {
        SurfaceDecl::Def { name, .. } => assert_eq!(name, "id"),
        _ => panic!("expected Def"),
    }

    match &decls[1] {
        SurfaceDecl::Def { name, binders, .. } => {
            assert_eq!(name, "const");
            assert_eq!(binders.len(), 3);
        }
        _ => panic!("expected Def"),
    }

    match &decls[2] {
        SurfaceDecl::Axiom { name, .. } => assert_eq!(name, "myAxiom"),
        _ => panic!("expected Axiom"),
    }
}

#[test]
fn test_parse_empty_file() {
    let decls = Parser::parse_file("").unwrap();
    assert!(decls.is_empty());
}

#[test]
fn test_parse_greek_implicit_binders() {
    // Test implicit binders with Greek letters
    let input = "inductive Imf {α : Type u} {β : Type v} (f : α → β) : β → Type (max u v)\n| mk : (a : α) → Imf f (f a)";
    let decls = Parser::parse_file(input).expect("Failed to parse greek implicit binders");
    assert_eq!(decls.len(), 1, "expected 1 inductive declaration");
    match &decls[0] {
        SurfaceDecl::Inductive { name, ty, .. } => {
            assert_eq!(name, "Imf");
            assert!(
                matches!(
                    ty.as_ref(),
                    SurfaceExpr::Arrow(
                        _,
                        _,
                        right,
                    ) if matches!(
                        right.as_ref(),
                        SurfaceExpr::Universe(
                            _,
                            UniverseExpr::TypeLevel(level),
                        ) if matches!(
                            level.as_ref(),
                            LevelExpr::Max(lhs, rhs)
                                if matches!(lhs.as_ref(), LevelExpr::Param(lhs) if lhs == "u")
                                    && matches!(rhs.as_ref(), LevelExpr::Param(rhs) if rhs == "v")
                        )
                    )
                ),
                "expected inductive result type to end in `Type (max u v)`, got {ty:?}"
            );
        }
        other => panic!("expected Inductive named 'Imf', got {other:?}"),
    }
}

#[test]
fn test_parse_constructor_binder_syntax_preserves_binders() {
    let input = "inductive Foo : Type where\n| bar (n : Nat) : Foo";
    let decls = Parser::parse_file(input).expect("binder-form constructor should parse");
    assert_eq!(decls.len(), 1, "expected a single inductive declaration");

    match &decls[0] {
        SurfaceDecl::Inductive { name, ctors, .. } => {
            assert_eq!(name, "Foo");
            assert_eq!(ctors.len(), 1, "expected a single constructor");

            match &ctors[0].ty {
                SurfaceExpr::Pi(_, binders, body) => {
                    assert_eq!(binders.len(), 1, "expected one constructor binder");
                    assert_eq!(binders[0].name, "n");
                    assert!(
                        matches!(binders[0].ty.as_deref(), Some(SurfaceExpr::Ident(_, ty)) if ty == "Nat"),
                        "expected constructor binder type Nat, got {:?}",
                        binders[0].ty
                    );
                    assert!(
                        matches!(body.as_ref(), SurfaceExpr::Ident(_, ind) if ind == "Foo"),
                        "expected constructor result type Foo, got {body:?}"
                    );
                }
                other => panic!("expected constructor type to desugar into Pi, got {other:?}"),
            }
        }
        other => panic!("expected Inductive declaration, got {other:?}"),
    }
}

#[test]
fn test_parse_constructor_bare_binders_before_colon() {
    let input = "inductive Eq (A : Type) : A → A → Type where\n| refl a : Eq A a a";
    let decls = Parser::parse_file(input).expect("bare-binder constructor should parse");
    assert_eq!(decls.len(), 1, "expected a single inductive declaration");

    match &decls[0] {
        SurfaceDecl::Inductive { name, ctors, .. } => {
            assert_eq!(name, "Eq");
            assert_eq!(ctors.len(), 1, "expected a single constructor");

            match &ctors[0].ty {
                SurfaceExpr::Pi(_, binders, body) => {
                    assert_eq!(binders.len(), 1, "expected one constructor binder");
                    assert_eq!(binders[0].name, "a");
                    assert!(
                        binders[0].ty.is_none(),
                        "expected bare constructor binder to remain untyped, got {:?}",
                        binders[0].ty
                    );
                    assert!(
                        matches!(body.as_ref(), SurfaceExpr::App(_, _, _) | SurfaceExpr::Arrow(_, _, _)),
                        "expected constructor result type to remain an expression application, got {body:?}"
                    );
                }
                other => panic!("expected constructor type to desugar into Pi, got {other:?}"),
            }
        }
        other => panic!("expected Inductive declaration, got {other:?}"),
    }
}

#[test]
fn test_parse_structure_simple() {
    let decl = Parser::parse_decl(
        r"structure Point where
              x : Nat
              y : Nat",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure { name, fields, .. } => {
            assert_eq!(name, "Point");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "x");
            assert_eq!(fields[1].name, "y");
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_structure_colon_eq_fields() {
    // Legacy Lean 4 `:=` field-block form (lean4_compat corpus): the `:=`
    // introduces parenthesized field binders, a multi-name group expanding to
    // one field per name.
    let decl = Parser::parse_decl("structure Point (A : Type) := (x y : A) (label : A)").unwrap();
    match decl {
        SurfaceDecl::Structure {
            name,
            binders,
            fields,
            ..
        } => {
            assert_eq!(name, "Point");
            assert_eq!(binders.len(), 1);
            assert_eq!(fields.len(), 3, "(x y : A) expands to two fields");
            assert_eq!(fields[0].name, "x");
            assert_eq!(fields[1].name, "y");
            assert_eq!(fields[2].name, "label");
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_structure_colon_eq_extends_and_ctor() {
    // `:=` form with `extends` and an explicit constructor name `mk ::`.
    let decl =
        Parser::parse_decl("structure Bar (A : Type) extends Foo A := mk :: (bar : A)").unwrap();
    match decl {
        SurfaceDecl::Structure {
            name,
            extends,
            ctor_name,
            fields,
            ..
        } => {
            assert_eq!(name, "Bar");
            assert_eq!(extends.len(), 1);
            assert_eq!(ctor_name.as_deref(), Some("mk"));
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "bar");
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_class_colon_eq_fields() {
    // The class analogue of the structure `:=` field block (lean4_compat 1102).
    let decl = Parser::parse_decl("class Cls extends Parent := (u v : Unit)").unwrap();
    match decl {
        SurfaceDecl::Class {
            name,
            extends,
            fields,
            ..
        } => {
            assert_eq!(name, "Cls");
            assert_eq!(extends.len(), 1);
            assert_eq!(fields.len(), 2, "(u v : Unit) expands to two fields");
            assert_eq!(fields[0].name, "u");
            assert_eq!(fields[1].name, "v");
        }
        _ => panic!("expected Class"),
    }
}

#[test]
fn test_parse_structure_with_params() {
    let decl = Parser::parse_decl(
        r"structure Pair (A : Type) (B : Type) where
              fst : A
              snd : B",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure {
            name,
            binders,
            fields,
            ..
        } => {
            assert_eq!(name, "Pair");
            assert_eq!(binders.len(), 2);
            assert_eq!(binders[0].name, "A");
            assert_eq!(binders[1].name, "B");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "fst");
            assert_eq!(fields[1].name, "snd");
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_structure_with_type() {
    let decl = Parser::parse_decl(
        r"structure MyType : Type where
              val : Nat",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure { name, ty, .. } => {
            assert_eq!(name, "MyType");
            let _ty = ty
                .as_ref()
                .expect("structure with 'extends' should have type annotation");
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_structure_with_universe_params() {
    let decl = Parser::parse_decl(
        r"structure Container {u} (A : Type u) where
              data : A",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure {
            name,
            universe_params,
            binders,
            fields,
            ..
        } => {
            assert_eq!(name, "Container");
            assert_eq!(universe_params.len(), 1);
            assert_eq!(universe_params[0], "u");
            assert_eq!(binders.len(), 1);
            assert_eq!(fields.len(), 1);
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_structure_dependent_field() {
    // Test: field type that references an earlier field name
    // This tests that `B fst` is parsed as an application, not stopping at `fst`
    let decl = Parser::parse_decl(
        r"structure Sigma (A : Type) (B : A -> Type) where
              fst : A
              snd : B fst",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure {
            name,
            binders,
            fields,
            ..
        } => {
            assert_eq!(name, "Sigma");
            assert_eq!(binders.len(), 2);
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "fst");
            assert_eq!(fields[1].name, "snd");
            // Verify the second field type is an application B fst
            match &fields[1].ty {
                SurfaceExpr::App(_, func, args) => {
                    assert!(
                        matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "B"),
                        "Expected function to be B, got {func:?}"
                    );
                    assert_eq!(args.len(), 1, "Expected one argument (fst)");
                    assert!(
                        matches!(&args[0].expr, SurfaceExpr::Ident(_, name) if name == "fst"),
                        "Expected arg to be fst, got {:?}",
                        args[0].expr
                    );
                }
                other => panic!("Expected App, got {other:?}"),
            }
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_structure_dependent_field_projection_arg() {
    // Test: projection attaches to the last argument in a field type
    let decl = Parser::parse_decl(
        r"structure Sigma2 (A : Type) (B : A -> Type) where
              fst : A
              snd : B fst.snd",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure { fields, .. } => {
            assert_eq!(fields.len(), 2);
            match &fields[1].ty {
                SurfaceExpr::App(_, func, args) => {
                    assert!(
                        matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "B"),
                        "Expected function to be B, got {func:?}"
                    );
                    assert_eq!(args.len(), 1, "Expected one argument (fst.snd)");
                    match &args[0].expr {
                        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                            assert!(
                                matches!(base.as_ref(), SurfaceExpr::Ident(_, name) if name == "fst"),
                                "Expected base to be fst, got {base:?}"
                            );
                            assert_eq!(field, "snd");
                        }
                        other => panic!("expected projection arg, got {other:?}"),
                    }
                }
                other => panic!("Expected App, got {other:?}"),
            }
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_class_simple() {
    let decl = Parser::parse_decl(
        r"class Add (α : Type) where
              add : α → α → α",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Class {
            name,
            binders,
            fields,
            ..
        } => {
            assert_eq!(name, "Add");
            assert_eq!(binders.len(), 1);
            assert_eq!(binders[0].name, "α");
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "add");
        }
        _ => panic!("expected Class"),
    }
}

#[test]
fn test_parse_class_multiple_methods() {
    let decl = Parser::parse_decl(
        r"class Ord (α : Type) where
              lt : α → α → Prop
              le : α → α → Prop
              gt : α → α → Prop",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Class { name, fields, .. } => {
            assert_eq!(name, "Ord");
            assert_eq!(fields.len(), 3);
            assert_eq!(fields[0].name, "lt");
            assert_eq!(fields[1].name, "le");
            assert_eq!(fields[2].name, "gt");
        }
        _ => panic!("expected Class"),
    }
}

#[test]
fn test_parse_class_with_default() {
    let decl = Parser::parse_decl(
        r"class Inhabited (α : Type) where
              default : α",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Class {
            name,
            binders,
            fields,
            ..
        } => {
            assert_eq!(name, "Inhabited");
            assert_eq!(binders.len(), 1);
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "default");
        }
        _ => panic!("expected Class"),
    }
}

#[test]
fn test_parse_instance_named() {
    let decl = Parser::parse_decl(
        r"instance instAddNat : Add Nat where
              add := Nat.add",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance {
            name,
            binders,
            class_type,
            fields,
            ..
        } => {
            assert_eq!(name, Some("instAddNat".to_string()));
            assert!(binders.is_empty());
            // class_type should be `Add Nat`
            match class_type.as_ref() {
                SurfaceExpr::App(_, func, args) => {
                    assert!(matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "Add"));
                    assert_eq!(args.len(), 1);
                }
                _ => panic!("expected App"),
            }
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "add");
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_parse_instance_anonymous() {
    let decl = Parser::parse_decl(
        r"instance : Add Nat where
              add := Nat.add",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance { name, fields, .. } => {
            assert!(
                name.is_none(),
                "anonymous instance should have no name, got {name:?}"
            );
            assert_eq!(fields.len(), 1);
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_parse_instance_with_binders() {
    let decl = Parser::parse_decl(
        r"instance [Add α] [Add β] : Add (Prod α β) where
              add := fun x y => x",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance {
            name,
            binders,
            fields,
            ..
        } => {
            assert!(
                name.is_none(),
                "anonymous instance should have no name, got {name:?}"
            );
            // Two instance binders
            assert_eq!(binders.len(), 2);
            assert_eq!(binders[0].info, SurfaceBinderInfo::Instance);
            assert_eq!(binders[1].info, SurfaceBinderInfo::Instance);
            assert_eq!(fields.len(), 1);
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_parse_instance_multiple_fields() {
    let decl = Parser::parse_decl(
        r"instance : Ord Nat where
              lt := Nat.lt
              le := Nat.le
              gt := Nat.gt",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance { fields, .. } => {
            assert_eq!(fields.len(), 3);
            assert_eq!(fields[0].name, "lt");
            assert_eq!(fields[1].name, "le");
            assert_eq!(fields[2].name, "gt");
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_parse_instance_field_projection_arg() {
    let decl = Parser::parse_decl(
        r"instance : Foo where
              bar := f x.y",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance { fields, .. } => {
            assert_eq!(fields.len(), 1);
            match &fields[0].val {
                SurfaceExpr::App(_, func, args) => {
                    assert!(
                        matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "f"),
                        "Expected function to be f, got {func:?}"
                    );
                    assert_eq!(args.len(), 1);
                    match &args[0].expr {
                        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                            assert!(
                                matches!(base.as_ref(), SurfaceExpr::Ident(_, name) if name == "x"),
                                "Expected base to be x, got {base:?}"
                            );
                            assert_eq!(field, "y");
                        }
                        other => panic!("expected projection arg, got {other:?}"),
                    }
                }
                other => panic!("expected App, got {other:?}"),
            }
        }
        _ => panic!("expected Instance"),
    }
}

// B53: an instance `where`-field whose value is a `fun .. => body` lambda must
// terminate the lambda body at the next `ident :=` field boundary, not swallow
// the next field's name as an application argument.
#[test]
fn test_parse_instance_lambda_field_bounded_at_next_field() {
    let decl = Parser::parse_decl(
        "instance : C T where\n  render := fun _ => Nat.succ Nat.zero\n  tag := 3",
    )
    .unwrap();
    let SurfaceDecl::Instance { fields, .. } = decl else {
        panic!("expected Instance");
    };
    // BOTH fields must be present; `tag` must not be dropped.
    assert_eq!(fields.len(), 2, "expected render and tag, got {fields:?}");
    assert_eq!(fields[0].name, "render");
    assert_eq!(fields[1].name, "tag");

    // render := fun _ => Nat.succ Nat.zero  (lambda body bounded; no `tag` arg)
    let SurfaceExpr::Lambda(_, binders, body) = &fields[0].val else {
        panic!("expected render to be a lambda, got {:?}", fields[0].val);
    };
    assert_eq!(binders.len(), 1, "lambda should have exactly one binder");
    // Body must be `Nat.succ Nat.zero` — App of one argument, NOT two.
    let SurfaceExpr::App(_, func, args) = body.as_ref() else {
        panic!("expected lambda body to be an application, got {body:?}");
    };
    assert!(
        matches!(func.as_ref(), SurfaceExpr::Proj(_, base, Projection::Named(f))
            if f == "succ" && matches!(base.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat")),
        "expected head Nat.succ, got {func:?}"
    );
    assert_eq!(
        args.len(),
        1,
        "lambda body must apply exactly one argument (Nat.zero), \
         the `tag` field name must NOT be eaten as a second arg: {args:?}"
    );

    // tag := 3
    assert!(
        matches!(&fields[1].val, SurfaceExpr::Lit(_, SurfaceLit::Nat(3))),
        "expected tag := 3, got {:?}",
        fields[1].val
    );
}

// B53: a multi-field instance `where`-block with several lambda-valued fields
// must parse ALL fields, each lambda body bounded at the next field.
#[test]
fn test_parse_instance_multiple_lambda_fields() {
    let decl = Parser::parse_decl(
        "instance : C T where\n  f := fun x => g x\n  h := fun y => k y\n  n := 7",
    )
    .unwrap();
    let SurfaceDecl::Instance { fields, .. } = decl else {
        panic!("expected Instance");
    };
    assert_eq!(fields.len(), 3, "expected f, h, n, got {fields:?}");
    assert_eq!(fields[0].name, "f");
    assert_eq!(fields[1].name, "h");
    assert_eq!(fields[2].name, "n");

    for (idx, expected_head) in [(0usize, "g"), (1usize, "k")] {
        let SurfaceExpr::Lambda(_, binders, body) = &fields[idx].val else {
            panic!(
                "expected field {idx} to be a lambda, got {:?}",
                fields[idx].val
            );
        };
        assert_eq!(binders.len(), 1, "lambda {idx} should have one binder");
        let SurfaceExpr::App(_, func, args) = body.as_ref() else {
            panic!("expected lambda {idx} body to be an application, got {body:?}");
        };
        assert!(
            matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == expected_head),
            "lambda {idx} head should be {expected_head}, got {func:?}"
        );
        assert_eq!(
            args.len(),
            1,
            "lambda {idx} body must apply exactly one argument, got {args:?}"
        );
    }

    assert!(
        matches!(&fields[2].val, SurfaceExpr::Lit(_, SurfaceLit::Nat(7))),
        "expected n := 7, got {:?}",
        fields[2].val
    );
}

// B53 guard: a non-lambda field value followed by another field must still
// bound correctly through the shared expression grammar, and a trailing lambda
// field at the end of the where-block parses with no following boundary.
#[test]
fn test_parse_instance_lambda_field_last_in_block() {
    let decl =
        Parser::parse_decl("instance : C T where\n  tag := 3\n  render := fun a => f a").unwrap();
    let SurfaceDecl::Instance { fields, .. } = decl else {
        panic!("expected Instance");
    };
    assert_eq!(fields.len(), 2, "expected tag and render, got {fields:?}");
    assert_eq!(fields[0].name, "tag");
    assert!(matches!(
        &fields[0].val,
        SurfaceExpr::Lit(_, SurfaceLit::Nat(3))
    ));
    assert_eq!(fields[1].name, "render");
    let SurfaceExpr::Lambda(_, binders, body) = &fields[1].val else {
        panic!("expected render to be a lambda, got {:?}", fields[1].val);
    };
    assert_eq!(binders.len(), 1);
    assert!(
        matches!(body.as_ref(), SurfaceExpr::App(_, _, args) if args.len() == 1),
        "expected `f a` with one arg, got {body:?}"
    );
}

// B53 soundness guard: the instance-field boundary fires ONLY on a bare
// `ident :=` at application-argument position. A `let x := v in body` inside a
// field value begins with the `let` keyword (not a bare ident), so it must be
// parsed in full — the `x :=` inside the `let` is NOT a field boundary, and the
// next real field (`tag`) is still recognised. Regression guard proving the new
// flag neither truncates a `let`-bodied field value nor drops the next field.
#[test]
fn test_parse_instance_let_field_value_not_truncated() {
    let decl =
        Parser::parse_decl("instance : C T where\n  v := let x := Nat.zero in x\n  tag := 3")
            .unwrap();
    let SurfaceDecl::Instance { fields, .. } = decl else {
        panic!("expected Instance");
    };
    assert_eq!(fields.len(), 2, "expected v and tag, got {fields:?}");
    assert_eq!(fields[0].name, "v");
    let SurfaceExpr::Let(_, binder, val, body) = &fields[0].val else {
        panic!("expected v to be a let-expression, got {:?}", fields[0].val);
    };
    assert_eq!(binder.name, "x", "let binder name should be x");
    assert!(
        matches!(val.as_ref(), SurfaceExpr::Proj(_, base, Projection::Named(f))
            if f == "zero" && matches!(base.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat")),
        "let value should be Nat.zero, got {val:?}"
    );
    assert!(
        matches!(body.as_ref(), SurfaceExpr::Ident(_, n) if n == "x"),
        "let body should be the bare ident x, got {body:?}"
    );
    assert_eq!(fields[1].name, "tag");
    assert!(
        matches!(&fields[1].val, SurfaceExpr::Lit(_, SurfaceLit::Nat(3))),
        "expected tag := 3, got {:?}",
        fields[1].val
    );
}

// B53 soundness guard: a struct-literal `{ a := .. }` nested inside an instance
// field value must keep ALL of its own fields. The struct-literal's `a := ..`
// boundaries are handled by the struct-literal parser, and the new
// instance-field flag must not interfere with parsing the brace-delimited
// literal as a single atom.
#[test]
fn test_parse_instance_struct_literal_field_value() {
    let decl = Parser::parse_decl(
        "instance : C T where\n  cfg := { a := Nat.zero, b := Nat.zero }\n  tag := 3",
    )
    .unwrap();
    let SurfaceDecl::Instance { fields, .. } = decl else {
        panic!("expected Instance");
    };
    assert_eq!(fields.len(), 2, "expected cfg and tag, got {fields:?}");
    assert_eq!(fields[0].name, "cfg");
    let SurfaceExpr::StructLit {
        fields: inner_fields,
        ..
    } = &fields[0].val
    else {
        panic!(
            "expected cfg to be a struct literal, got {:?}",
            fields[0].val
        );
    };
    assert_eq!(
        inner_fields.len(),
        2,
        "nested struct literal must keep both a and b, got {inner_fields:?}"
    );
    assert_eq!(fields[1].name, "tag");
    assert!(
        matches!(&fields[1].val, SurfaceExpr::Lit(_, SurfaceLit::Nat(3))),
        "expected tag := 3, got {:?}",
        fields[1].val
    );
}

// B53 boundary guard: a lambda field value whose body is a *bare projection*
// (`fun _ => Nat.zero`, no application argument) must still terminate at the
// next `ident :=` field. This pins that the boundary fires after the projection
// and `tag` is recognised as a separate field rather than eaten as
// `Nat.zero tag`.
#[test]
fn test_parse_instance_lambda_field_bare_proj_body_bounded() {
    let decl =
        Parser::parse_decl("instance : C T where\n  render := fun _ => Nat.zero\n  tag := 3")
            .unwrap();
    let SurfaceDecl::Instance { fields, .. } = decl else {
        panic!("expected Instance");
    };
    assert_eq!(fields.len(), 2, "expected render and tag, got {fields:?}");
    assert_eq!(fields[0].name, "render");
    let SurfaceExpr::Lambda(_, binders, body) = &fields[0].val else {
        panic!("expected render to be a lambda, got {:?}", fields[0].val);
    };
    assert_eq!(binders.len(), 1, "lambda should have one binder");
    // Body must be the bare projection Nat.zero (NOT an App applying `tag`).
    assert!(
        matches!(body.as_ref(), SurfaceExpr::Proj(_, base, Projection::Named(f))
            if f == "zero" && matches!(base.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat")),
        "expected lambda body to be the bare projection Nat.zero, got {body:?}"
    );
    assert_eq!(fields[1].name, "tag");
    assert!(
        matches!(&fields[1].val, SurfaceExpr::Lit(_, SurfaceLit::Nat(3))),
        "expected tag := 3, got {:?}",
        fields[1].val
    );
}

// B53 boundary guard: a *nested* lambda field value (`fun _ => fun y => g y`)
// must keep both `fun` layers and still terminate at the next field. The inner
// lambda body is parsed via the boundary-aware `expr` grammar, so the
// `in_instance_field` flag must survive through the nested lambda and stop
// before `tag :=` rather than folding it into the innermost application.
#[test]
fn test_parse_instance_nested_lambda_field_bounded() {
    let decl =
        Parser::parse_decl("instance : C T where\n  render := fun _ => fun y => g y\n  tag := 3")
            .unwrap();
    let SurfaceDecl::Instance { fields, .. } = decl else {
        panic!("expected Instance");
    };
    assert_eq!(fields.len(), 2, "expected render and tag, got {fields:?}");
    assert_eq!(fields[0].name, "render");

    // Outer lambda `fun _ => <inner>`.
    let SurfaceExpr::Lambda(_, outer_binders, outer_body) = &fields[0].val else {
        panic!("expected render to be a lambda, got {:?}", fields[0].val);
    };
    assert_eq!(
        outer_binders.len(),
        1,
        "outer lambda should have one binder"
    );

    // Inner lambda `fun y => g y`.
    let SurfaceExpr::Lambda(_, inner_binders, inner_body) = outer_body.as_ref() else {
        panic!("expected nested lambda, got {outer_body:?}");
    };
    assert_eq!(
        inner_binders.len(),
        1,
        "inner lambda should have one binder"
    );

    // Innermost body must be `g y` — exactly one argument, NOT `g y tag`.
    let SurfaceExpr::App(_, func, args) = inner_body.as_ref() else {
        panic!("expected innermost body to be an application, got {inner_body:?}");
    };
    assert!(
        matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "g"),
        "expected innermost head g, got {func:?}"
    );
    assert_eq!(
        args.len(),
        1,
        "innermost application must take exactly one arg (y); `tag` must NOT be \
         swallowed through the nested lambda: {args:?}"
    );

    assert_eq!(fields[1].name, "tag");
    assert!(
        matches!(&fields[1].val, SurfaceExpr::Lit(_, SurfaceLit::Nat(3))),
        "expected tag := 3, got {:?}",
        fields[1].val
    );
}

#[test]
fn test_parse_outparam() {
    // Test parsing outParam Type
    let expr = Parser::parse_expr("outParam Type").unwrap();
    match expr {
        SurfaceExpr::OutParam(_, inner) => {
            assert!(matches!(
                *inner,
                SurfaceExpr::Universe(_, UniverseExpr::Type)
            ));
        }
        _ => panic!("expected OutParam, got {expr:?}"),
    }
}

#[test]
fn test_parse_outparam_in_binder() {
    // Test parsing outParam in a binder context: (F : outParam Type)
    let expr = Parser::parse_expr("fun (F : outParam Type) => F").unwrap();
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1);
            let binder_ty = binders[0].ty.as_ref().expect("binder should have type");
            assert!(
                matches!(**binder_ty, SurfaceExpr::OutParam(_, _)),
                "binder type should be OutParam"
            );
        }
        _ => panic!("expected Lambda"),
    }
}

#[test]
fn test_parse_class_with_outparam() {
    // Test parsing a class with an out-parameter
    let decl = Parser::parse_decl(
        r"class HAdd (α : Type) (β : Type) (γ : outParam Type) where
              hAdd : α → β → γ",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Class { name, binders, .. } => {
            assert_eq!(name, "HAdd");
            assert_eq!(binders.len(), 3);
            // First two parameters are regular Types
            assert!(matches!(
                binders[0].ty.as_ref().unwrap().as_ref(),
                SurfaceExpr::Universe(_, UniverseExpr::Type)
            ));
            assert!(matches!(
                binders[1].ty.as_ref().unwrap().as_ref(),
                SurfaceExpr::Universe(_, UniverseExpr::Type)
            ));
            // Third parameter is outParam Type
            assert!(
                matches!(
                    binders[2].ty.as_ref().unwrap().as_ref(),
                    SurfaceExpr::OutParam(_, _)
                ),
                "expected OutParam for third binder"
            );
        }
        _ => panic!("expected Class"),
    }
}

#[test]
fn test_parse_semioutparam() {
    // Test parsing semiOutParam Type
    let expr = Parser::parse_expr("semiOutParam Type").unwrap();
    match expr {
        SurfaceExpr::SemiOutParam(_, inner) => {
            assert!(matches!(
                *inner,
                SurfaceExpr::Universe(_, UniverseExpr::Type)
            ));
        }
        _ => panic!("expected SemiOutParam, got {expr:?}"),
    }
}

#[test]
fn test_parse_semioutparam_in_binder() {
    // Test parsing semiOutParam in a binder context: (F : semiOutParam Type)
    let expr = Parser::parse_expr("fun (F : semiOutParam Type) => F").unwrap();
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1);
            let binder_ty = binders[0].ty.as_ref().expect("binder should have type");
            assert!(
                matches!(**binder_ty, SurfaceExpr::SemiOutParam(_, _)),
                "binder type should be SemiOutParam"
            );
        }
        _ => panic!("expected Lambda"),
    }
}

#[test]
fn test_parse_class_with_semioutparam() {
    // Test parsing a class with a semi-out-parameter (like Coe)
    let decl = Parser::parse_decl(
        r"class Coe (α : semiOutParam Type) (β : Type) where
              coe : α → β",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Class { name, binders, .. } => {
            assert_eq!(name, "Coe");
            assert_eq!(binders.len(), 2);
            // First parameter is semiOutParam Type
            assert!(
                matches!(
                    binders[0].ty.as_ref().unwrap().as_ref(),
                    SurfaceExpr::SemiOutParam(_, _)
                ),
                "expected SemiOutParam for first binder"
            );
            // Second parameter is regular Type
            assert!(matches!(
                binders[1].ty.as_ref().unwrap().as_ref(),
                SurfaceExpr::Universe(_, UniverseExpr::Type)
            ));
        }
        _ => panic!("expected Class"),
    }
}

#[test]
fn test_parse_class_with_both_param_types() {
    // Test parsing a class with both outParam and semiOutParam
    let decl = Parser::parse_decl(
        r"class HCoe (α : semiOutParam Type) (β : Type) (γ : outParam Type) where
              hCoe : α → β → γ",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Class { name, binders, .. } => {
            assert_eq!(name, "HCoe");
            assert_eq!(binders.len(), 3);
            // First parameter is semiOutParam
            assert!(
                matches!(
                    binders[0].ty.as_ref().unwrap().as_ref(),
                    SurfaceExpr::SemiOutParam(_, _)
                ),
                "expected SemiOutParam for first binder"
            );
            // Second parameter is regular Type
            assert!(matches!(
                binders[1].ty.as_ref().unwrap().as_ref(),
                SurfaceExpr::Universe(_, UniverseExpr::Type)
            ));
            // Third parameter is outParam
            assert!(
                matches!(
                    binders[2].ty.as_ref().unwrap().as_ref(),
                    SurfaceExpr::OutParam(_, _)
                ),
                "expected OutParam for third binder"
            );
        }
        _ => panic!("expected Class"),
    }
}

// =========================================================================
// Attribute parsing tests
// =========================================================================

#[test]
fn test_parse_instance_with_priority_attribute() {
    // @[instance 50] instance : Add Nat where ...
    let decl = Parser::parse_decl(
        r"@[instance 50] instance : Add Nat where
              add := Nat.add",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance { priority, .. } => {
            assert_eq!(priority, Some(50));
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_parse_instance_with_default_instance_attribute() {
    // @[defaultInstance] instance : ToString Nat where ...
    let decl = Parser::parse_decl(
        r"@[defaultInstance] instance : ToString Nat where
              toString := Nat.repr",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance { priority, .. } => {
            // `@[defaultInstance]` feeds the default-instance table; it does
            // NOT override the instance's ordinary resolution priority (B99).
            assert_eq!(priority, None);
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_parse_instance_without_attribute() {
    // instance : Add Nat where ... (no attribute)
    let decl = Parser::parse_decl(
        r"instance : Add Nat where
              add := Nat.add",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance { priority, .. } => {
            // No attribute means no explicit priority
            assert_eq!(priority, None);
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_parse_attribute_only_instance() {
    // @[instance] instance : Add Nat where ... (attribute without explicit number)
    let decl = Parser::parse_decl(
        r"@[instance] instance : Add Nat where
              add := Nat.add",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Instance { priority, .. } => {
            // @[instance] without number means the Lean default priority
            // (1000; `low` = 100, `high` = 10000) — B99.
            assert_eq!(priority, Some(1000));
        }
        _ => panic!("expected Instance"),
    }
}

// =========================================================================
// Deriving clause tests
// =========================================================================

#[test]
fn test_parse_structure_with_deriving_single() {
    let decl = Parser::parse_decl(
        r"structure Point where
              x : Nat
              y : Nat
            deriving Repr",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure {
            name,
            fields,
            deriving,
            ..
        } => {
            assert_eq!(name, "Point");
            assert_eq!(fields.len(), 2);
            assert_eq!(deriving.len(), 1);
            assert_eq!(deriving[0], "Repr");
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_parse_structure_with_deriving_multiple() {
    let decl = Parser::parse_decl(
        r"structure Point where
              x : Nat
              y : Nat
            deriving Repr, BEq, Hashable",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure { name, deriving, .. } => {
            assert_eq!(name, "Point");
            assert_eq!(deriving.len(), 3);
            assert_eq!(deriving[0], "Repr");
            assert_eq!(deriving[1], "BEq");
            assert_eq!(deriving[2], "Hashable");
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_derive_repr_for_recovers_as_non_lean_command() {
    let code = r"derive Repr for Point
structure Point where
  x : Nat
deriving Repr
";
    let decls = Parser::parse_file(code).expect("file-level recovery should not fail");
    assert_eq!(decls.len(), 2, "expected raw derive plus structure");

    match &decls[0] {
        SurfaceDecl::RawDecl { content, .. } => {
            assert!(
                content.contains("derive") && content.contains("Repr"),
                "RawDecl should preserve unsupported derive command text, got {content:?}"
            );
        }
        other => panic!("expected unsupported derive command to recover as RawDecl, got {other:?}"),
    }

    match &decls[1] {
        SurfaceDecl::Structure { name, deriving, .. } => {
            assert_eq!(name, "Point");
            assert_eq!(deriving, &["Repr"]);
        }
        other => panic!("expected following structure with deriving Repr, got {other:?}"),
    }
}

#[test]
fn test_import_stops_before_identifier_led_command_on_next_line() {
    let code = r#"import Mathlib
local notation "foo" => Nat
"#;
    let decls = Parser::parse_file(code)
        .expect("import followed by local notation should parse as separate commands");
    assert_eq!(decls.len(), 2, "expected import plus local notation");
    match &decls[0] {
        SurfaceDecl::Import { paths, .. } => {
            assert_eq!(paths, &vec![vec!["Mathlib".to_string()]]);
        }
        other => panic!("expected Import, got {other:?}"),
    }
    assert!(
        matches!(&decls[1], SurfaceDecl::Notation { .. }),
        "identifier-led command after import must not become an import path: {:?}",
        decls[1]
    );
}

#[test]
fn test_open_scoped_stops_before_local_notation_and_namespace() {
    let code = r#"import Mathlib
open scoped BigOperators
local notation "foo" => Nat
namespace Mathbot
def witness : Nat := 1
end Mathbot
"#;
    let decls = Parser::parse_file(code).expect("Mathbot-style prelude and namespace should parse");
    assert_eq!(
        decls.len(),
        4,
        "expected import, open scoped, local notation, namespace"
    );
    match &decls[1] {
        SurfaceDecl::Open { scoped, paths, .. } => {
            assert!(*scoped);
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].path, vec!["BigOperators".to_string()]);
        }
        other => panic!("expected Open, got {other:?}"),
    }
    assert!(
        matches!(&decls[2], SurfaceDecl::Notation { .. }),
        "local notation must remain separate from open scoped: {:?}",
        decls[2]
    );
    match &decls[3] {
        SurfaceDecl::Namespace { name, decls, .. } => {
            assert_eq!(name, "Mathbot");
            assert_eq!(decls.len(), 1);
        }
        other => panic!("expected Namespace, got {other:?}"),
    }
}

#[test]
fn test_parse_structure_without_deriving() {
    let decl = Parser::parse_decl(
        r"structure Point where
              x : Nat
              y : Nat",
    )
    .unwrap();
    match decl {
        SurfaceDecl::Structure { deriving, .. } => {
            assert!(deriving.is_empty());
        }
        _ => panic!("expected Structure"),
    }
}

#[test]
fn test_section_without_end() {
    // Test section without explicit `end` (valid in Lean 4)
    let code = r"section
def foo : Nat := 1
#eval 42
";
    let decls = Parser::parse_file(code).expect("Section without end should parse");
    assert_eq!(decls.len(), 1, "expected 1 section declaration");
    assert!(
        matches!(&decls[0], SurfaceDecl::Section { .. }),
        "expected Section, got {:?}",
        decls[0]
    );
}

#[test]
fn test_namespace_without_end() {
    // Test namespace without explicit `end` (valid in Lean 4)
    let code = r"namespace Foo
def bar : Nat := 1
#eval 42
";
    let decls = Parser::parse_file(code).expect("Namespace without end should parse");
    assert_eq!(decls.len(), 1, "expected 1 namespace declaration");
    assert!(
        matches!(&decls[0], SurfaceDecl::Namespace { name, .. } if name == "Foo"),
        "expected Namespace named 'Foo', got {:?}",
        decls[0]
    );
}

#[test]
fn test_namespace_simple_with_end() {
    // Baseline: `namespace Foo ... end Foo` round-trips with no leftovers.
    let code = "namespace Foo\ndef bar : Nat := 1\nend Foo";
    let decls = Parser::parse_file(code).expect("simple namespace should parse");
    assert_eq!(
        decls.len(),
        1,
        "expected exactly one top-level namespace decl, got {decls:?}"
    );
    match &decls[0] {
        SurfaceDecl::Namespace { name, decls, .. } => {
            assert_eq!(name, "Foo");
            assert_eq!(decls.len(), 1);
        }
        other => panic!("expected Namespace, got {other:?}"),
    }
}

#[test]
fn test_namespace_compound_two_segments() {
    // Regression for the Mathbot/Bridges audit item: a two-segment
    // namespace `namespace Foo.Bar ... end Foo.Bar` must parse cleanly.
    let code = "namespace Foo.Bar\ndef baz : Nat := 1\nend Foo.Bar";
    let decls = Parser::parse_file(code).expect("compound namespace should parse");
    assert_eq!(
        decls.len(),
        1,
        "expected exactly one top-level namespace decl, got {decls:?}"
    );
    match &decls[0] {
        SurfaceDecl::Namespace { name, decls, .. } => {
            assert_eq!(name, "Foo.Bar");
            assert_eq!(decls.len(), 1);
        }
        other => panic!("expected Namespace, got {other:?}"),
    }
}

#[test]
fn test_namespace_compound_three_segments() {
    let code = "namespace Foo.Bar.Baz\ndef qux : Nat := 1\nend Foo.Bar.Baz";
    let decls = Parser::parse_file(code).expect("three-segment namespace should parse");
    assert_eq!(
        decls.len(),
        1,
        "expected exactly one top-level namespace decl, got {decls:?}"
    );
    match &decls[0] {
        SurfaceDecl::Namespace { name, decls, .. } => {
            assert_eq!(name, "Foo.Bar.Baz");
            assert_eq!(decls.len(), 1);
        }
        other => panic!("expected Namespace, got {other:?}"),
    }
}

#[test]
fn test_namespace_compound_end_leaf_only_accepted() {
    // Preserve lenient behavior: `end Baz` is accepted as the close of
    // `namespace Foo.Bar.Baz`. The Lean 4 elaborator itself would warn,
    // but clean-parser should not produce a RawDecl recovery node here.
    let code = "namespace Foo.Bar.Baz\ndef qux : Nat := 1\nend Baz";
    let decls = Parser::parse_file(code).expect("leaf-only end should be accepted");
    assert_eq!(decls.len(), 1, "got {decls:?}");
    match &decls[0] {
        SurfaceDecl::Namespace { name, .. } => assert_eq!(name, "Foo.Bar.Baz"),
        other => panic!("expected Namespace, got {other:?}"),
    }
}

#[test]
fn test_namespace_compound_nested() {
    // Nested compound namespaces inside an outer compound namespace —
    // mirrors the shape of `Mathbot/Bridges/PillarIIIConcrete.lean`.
    let code = r"namespace Mathbot.Outer
namespace Inner.Deep
def witness : Nat := 1
end Inner.Deep
end Mathbot.Outer";
    let decls = Parser::parse_file(code).expect("nested compound namespaces should parse");
    assert_eq!(
        decls.len(),
        1,
        "expected only the outer namespace at top level, got {decls:?}"
    );
    match &decls[0] {
        SurfaceDecl::Namespace { name, decls, .. } => {
            assert_eq!(name, "Mathbot.Outer");
            assert_eq!(decls.len(), 1, "expected one inner namespace");
            match &decls[0] {
                SurfaceDecl::Namespace {
                    name: inner_name,
                    decls: inner_decls,
                    ..
                } => {
                    assert_eq!(inner_name, "Inner.Deep");
                    assert_eq!(inner_decls.len(), 1);
                }
                other => panic!("expected inner Namespace, got {other:?}"),
            }
        }
        other => panic!("expected outer Namespace, got {other:?}"),
    }
}

#[test]
fn test_namespace_compound_eof_no_end() {
    // `end` is optional in Lean 4; compound names must still work at EOF.
    let code = "namespace Foo.Bar\ndef baz : Nat := 1\n";
    let decls = Parser::parse_file(code).expect("compound namespace without end should parse");
    assert_eq!(decls.len(), 1, "got {decls:?}");
    match &decls[0] {
        SurfaceDecl::Namespace { name, .. } => assert_eq!(name, "Foo.Bar"),
        other => panic!("expected Namespace, got {other:?}"),
    }
}

#[test]
fn test_namespace_malformed_numeric_name_errors() {
    // `namespace 42` is malformed. Either we error in `decl()` or recover
    // into a RawDecl — both are acceptable as long as we do NOT silently
    // produce a `Namespace` declaration. The audit requires a clear error.
    let code = "namespace 42\nend";
    let decls = Parser::parse_file(code).expect("file-level recovery should not panic");
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::Namespace { .. })),
        "malformed namespace must not parse as a real Namespace decl, got {decls:?}"
    );
}

// ========================================================================
// Macro system parsing tests
// ========================================================================

#[test]
fn test_parse_syntax_simple() {
    let decl = Parser::parse_decl(r#"syntax term "+" term : term"#).unwrap();
    match decl {
        SurfaceDecl::Syntax {
            pattern, category, ..
        } => {
            assert_eq!(category, "term");
            assert_eq!(pattern.len(), 3); // term, "+", term
        }
        _ => panic!("expected Syntax"),
    }
}

#[test]
fn test_parse_syntax_with_precedence() {
    let decl = Parser::parse_decl(r#"syntax:50 term "+" term : term"#).unwrap();
    match decl {
        SurfaceDecl::Syntax {
            precedence,
            category,
            ..
        } => {
            assert_eq!(precedence, Some(50));
            assert_eq!(category, "term");
        }
        _ => panic!("expected Syntax"),
    }
}

#[test]
fn test_parse_syntax_with_name() {
    let decl = Parser::parse_decl(r#"syntax [myAdd] term "+" term : term"#).unwrap();
    match decl {
        SurfaceDecl::Syntax { name, category, .. } => {
            assert_eq!(name, Some("myAdd".to_string()));
            assert_eq!(category, "term");
        }
        _ => panic!("expected Syntax"),
    }
}

#[test]
fn test_parse_declare_syntax_cat() {
    let decl = Parser::parse_decl("declare_syntax_cat myCategory").unwrap();
    match decl {
        SurfaceDecl::DeclareSyntaxCat { name, .. } => {
            assert_eq!(name, "myCategory");
        }
        _ => panic!("expected DeclareSyntaxCat"),
    }
}

#[test]
fn test_parse_macro_simple() {
    let decl = Parser::parse_decl(r#"macro "hello" : term => x"#).unwrap();
    match decl {
        SurfaceDecl::Macro {
            pattern,
            category,
            expansion,
            ..
        } => {
            assert_eq!(pattern.len(), 1); // "hello"
            assert_eq!(category, "term");
            assert!(matches!(*expansion, SurfaceExpr::Ident(_, ref n) if n == "x"));
        }
        _ => panic!("expected Macro"),
    }
}

#[test]
fn test_parse_macro_with_variables() {
    let decl = Parser::parse_decl(r#"macro "unless" cond:term "then" body:term : term => x"#)
        .expect("Should parse macro with variables");
    assert!(
        matches!(decl, SurfaceDecl::Macro { .. }),
        "expected Macro, got {decl:?}"
    );
}

#[test]
fn test_parse_macro_rules() {
    let decl = Parser::parse_decl(r"macro_rules | x => y | a => b").unwrap();
    match decl {
        SurfaceDecl::MacroRules { arms, .. } => {
            assert_eq!(arms.len(), 2);
        }
        _ => panic!("expected MacroRules"),
    }
}

#[test]
fn test_parse_notation_infixl() {
    let decl = Parser::parse_decl(r#"infixl:65 " + " => HAdd.hAdd"#).unwrap();
    match decl {
        SurfaceDecl::Notation {
            kind,
            precedence,
            pattern,
            ..
        } => {
            assert_eq!(kind, NotationKind::Infixl);
            assert_eq!(precedence, Some(65));
            assert!(!pattern.is_empty());
        }
        _ => panic!("expected Notation"),
    }
}

#[test]
fn test_parse_notation_prefix() {
    let decl = Parser::parse_decl(r#"prefix:100 "!" => Not"#).unwrap();
    match decl {
        SurfaceDecl::Notation {
            kind, precedence, ..
        } => {
            assert_eq!(kind, NotationKind::Prefix);
            assert_eq!(precedence, Some(100));
        }
        _ => panic!("expected Notation"),
    }
}

#[test]
fn test_parse_notation_closed_multihole_registers_and_parses() {
    // B100: a CLOSED multi-hole `notation` (leading + trailing literal, holes
    // delimited by literals) must register a parseable mixfix so a later use
    // site parses instead of degrading to an error-recovery raw declaration.
    let src = "def notprec_digits (a b c : Nat) : Nat := a * 100 + b * 10 + c\n\nnotation:max \"⟪\" a \", \" b \", \" c \"⟫\" => notprec_digits a b c\n\ntheorem notprec_multihole : ⟪1, 2, 3⟫ = 123 := rfl\n";
    let decls = crate::parse_file(src).expect("multihole notation file should parse");
    assert_eq!(
        decls.len(),
        3,
        "expected def + notation + theorem: {decls:#?}"
    );
    for decl in &decls {
        assert!(
            !matches!(decl, SurfaceDecl::RawDecl { .. }),
            "no declaration may degrade to raw error-recovery: {decl:#?}"
        );
    }
}

#[test]
fn test_parse_notation_general() {
    let decl = Parser::parse_decl(r#"notation a " ++ " b => List.append a b"#).unwrap();
    match decl {
        SurfaceDecl::Notation { kind, pattern, .. } => {
            assert_eq!(kind, NotationKind::Notation);
            // Should have: a, " ++ ", b
            assert!(pattern.len() >= 2);
        }
        _ => panic!("expected Notation"),
    }
}

#[test]
fn test_parse_file_with_macros() {
    // Test that a file with multiple macro declarations parses
    let code = r#"
syntax term "+" term : term
macro "hello" : term => x
infixl:65 " - " => HSub.hSub
def foo := 42
"#;
    let decls = Parser::parse_file(code).expect("File with macros should parse");
    // Should have at least 4 declarations
    assert!(
        decls.len() >= 3,
        "Expected at least 3 decls, got {}",
        decls.len()
    );
}

// =============================================================================
// Qq quotation tests - Part of #16: Qq quotation support
// =============================================================================

#[test]
fn test_parse_q_type_quotation() {
    // Q(Nat) - type quotation
    let expr = Parser::parse_expr("Q(Nat)").unwrap();
    match expr {
        SurfaceExpr::QQuotation {
            kind,
            inner,
            type_annot,
            ..
        } => {
            assert_eq!(kind, QQuotationKind::Type);
            assert!(matches!(*inner, SurfaceExpr::Ident(_, s) if s == "Nat"));
            assert!(
                type_annot.is_none(),
                "type quotation should not have type annotation, got {type_annot:?}"
            );
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_type_quotation_complex() {
    // Q(List Nat) - type quotation with application
    let expr = Parser::parse_expr("Q(List Nat)").unwrap();
    match expr {
        SurfaceExpr::QQuotation {
            kind,
            inner,
            type_annot,
            ..
        } => {
            assert_eq!(kind, QQuotationKind::Type);
            // Inner should be an App of List to Nat
            assert!(matches!(*inner, SurfaceExpr::App(_, _, _)));
            assert!(
                type_annot.is_none(),
                "type quotation should not have type annotation, got {type_annot:?}"
            );
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_type_quotation_with_annotation() {
    // Q(α : Type) - type quotation with kind annotation
    let expr = Parser::parse_expr("Q(α : Type)").unwrap();
    match expr {
        SurfaceExpr::QQuotation {
            kind,
            inner,
            type_annot,
            ..
        } => {
            assert_eq!(kind, QQuotationKind::Type);
            assert!(matches!(*inner, SurfaceExpr::Ident(_, s) if s == "α"));
            let annot = type_annot.expect("type quotation with annotation should have type_annot");
            assert!(matches!(
                *annot,
                SurfaceExpr::Universe(_, UniverseExpr::Type)
            ));
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_value_quotation_simple() {
    // q(42) - simple value quotation
    let expr = Parser::parse_expr("q(42)").unwrap();
    match expr {
        SurfaceExpr::QQuotation {
            kind,
            inner,
            type_annot,
            ..
        } => {
            assert_eq!(kind, QQuotationKind::Value);
            assert!(matches!(*inner, SurfaceExpr::Lit(_, SurfaceLit::Nat(42))));
            assert!(
                type_annot.is_none(),
                "value quotation without annotation should have no type_annot, got {type_annot:?}"
            );
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_space_paren_is_application_not_quotation() {
    // Regression: `Nat.add q (Nat.succ q)` — a bare `q`/`Q` as a function
    // argument followed by a *space* and a parenthesized argument is an ordinary
    // application, NOT the Qq quotation `q(…)` (which is CONTIGUOUS). Before the
    // fix the parser absorbed `q (Nat.succ q)` into a single `QQuotation`,
    // silently dropping the `q` argument.
    for src in ["Nat.add q (Nat.succ q)", "Nat.add Q (Nat.succ Q)"] {
        let expr =
            Parser::parse_expr(src).unwrap_or_else(|e| panic!("[{src}] parse failed: {e:?}"));
        match expr {
            SurfaceExpr::App(_, _, args) => assert_eq!(
                args.len(),
                2,
                "[{src}] expected 2 application arguments, got {args:?}"
            ),
            other => panic!("[{src}] expected an application, got {other:?}"),
        }
    }
    // A bare `q (x)` (space) is `q` applied to `(x)`, not a quotation.
    match Parser::parse_expr("q (x)").expect("`q (x)` should parse") {
        SurfaceExpr::App(_, head, args) => {
            assert!(matches!(*head, SurfaceExpr::Ident(_, ref n) if n == "q"));
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected `q` applied to `(x)`, got {other:?}"),
    }
    // But CONTIGUOUS `q(x)` is still the Qq value quotation (unchanged).
    assert!(
        matches!(
            Parser::parse_expr("q(x)").expect("`q(x)` should parse"),
            SurfaceExpr::QQuotation { .. }
        ),
        "contiguous `q(x)` must remain a Qq quotation"
    );
}

#[test]
fn test_parse_q_value_quotation_with_type() {
    // q(42 : Nat) - value quotation with type annotation
    let expr = Parser::parse_expr("q(42 : Nat)").unwrap();
    match expr {
        SurfaceExpr::QQuotation {
            kind,
            inner,
            type_annot,
            ..
        } => {
            assert_eq!(kind, QQuotationKind::Value);
            assert!(matches!(*inner, SurfaceExpr::Lit(_, SurfaceLit::Nat(42))));
            let annot =
                type_annot.expect("value quotation with type annotation should have type_annot");
            assert!(matches!(*annot, SurfaceExpr::Ident(_, s) if s == "Nat"));
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_antiquot_simple() {
    // q($x) - simple antiquotation
    let expr = Parser::parse_expr("q($x)").unwrap();
    match expr {
        SurfaceExpr::QQuotation { kind, inner, .. } => {
            assert_eq!(kind, QQuotationKind::Value);
            match *inner {
                SurfaceExpr::QAntiquot { content, .. } => {
                    assert!(matches!(content, QAntiquotContent::Simple(s) if s == "x"));
                }
                _ => panic!("expected QAntiquot inside QQuotation, got {inner:?}"),
            }
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_antiquot_expr() {
    // q($(foo bar)) - expression antiquotation
    let expr = Parser::parse_expr("q($(foo bar))").unwrap();
    match expr {
        SurfaceExpr::QQuotation { kind, inner, .. } => {
            assert_eq!(kind, QQuotationKind::Value);
            match *inner {
                SurfaceExpr::QAntiquot { content, .. } => {
                    match content {
                        QAntiquotContent::Expr(inner_expr) => {
                            // inner_expr should be an App: foo bar
                            assert!(matches!(*inner_expr, SurfaceExpr::App(_, _, _)));
                        }
                        _ => panic!("expected Expr antiquotation, got {content:?}"),
                    }
                }
                _ => panic!("expected QAntiquot inside QQuotation, got {inner:?}"),
            }
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_antiquot_typed() {
    // q($(n : Nat)) - typed antiquotation
    let expr = Parser::parse_expr("q($(n : Nat))").unwrap();
    match expr {
        SurfaceExpr::QQuotation { kind, inner, .. } => {
            assert_eq!(kind, QQuotationKind::Value);
            match *inner {
                SurfaceExpr::QAntiquot { content, .. } => match content {
                    QAntiquotContent::Typed { name, ty } => {
                        assert_eq!(name, "n");
                        assert!(matches!(*ty, SurfaceExpr::Ident(_, s) if s == "Nat"));
                    }
                    _ => panic!("expected Typed antiquotation, got {content:?}"),
                },
                _ => panic!("expected QAntiquot inside QQuotation, got {inner:?}"),
            }
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_antiquot_splice_star() {
    // q($[xs]*) - splice antiquotation with zero or more
    let expr = Parser::parse_expr("q($[xs]*)").unwrap();
    match expr {
        SurfaceExpr::QQuotation { kind, inner, .. } => {
            assert_eq!(kind, QQuotationKind::Value);
            match *inner {
                SurfaceExpr::QAntiquot { content, .. } => match content {
                    QAntiquotContent::Splice {
                        name,
                        separator,
                        at_least_one,
                    } => {
                        assert_eq!(name, "xs");
                        assert_eq!(separator, None);
                        assert!(!at_least_one, "* should mean zero or more");
                    }
                    _ => panic!("expected Splice antiquotation, got {content:?}"),
                },
                _ => panic!("expected QAntiquot inside QQuotation, got {inner:?}"),
            }
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_antiquot_splice_plus() {
    // q($[xs]+) - splice antiquotation with one or more
    let expr = Parser::parse_expr("q($[xs]+)").unwrap();
    match expr {
        SurfaceExpr::QQuotation { kind, inner, .. } => {
            assert_eq!(kind, QQuotationKind::Value);
            match *inner {
                SurfaceExpr::QAntiquot { content, .. } => match content {
                    QAntiquotContent::Splice {
                        name,
                        separator,
                        at_least_one,
                    } => {
                        assert_eq!(name, "xs");
                        assert_eq!(separator, None);
                        assert!(at_least_one, "+ should mean one or more");
                    }
                    _ => panic!("expected Splice antiquotation, got {content:?}"),
                },
                _ => panic!("expected QAntiquot inside QQuotation, got {inner:?}"),
            }
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_antiquot_splice_with_separator() {
    // q($[xs,]*) - splice antiquotation with comma separator
    let expr = Parser::parse_expr("q($[xs,]*)").unwrap();
    match expr {
        SurfaceExpr::QQuotation { kind, inner, .. } => {
            assert_eq!(kind, QQuotationKind::Value);
            match *inner {
                SurfaceExpr::QAntiquot { content, .. } => match content {
                    QAntiquotContent::Splice {
                        name,
                        separator,
                        at_least_one,
                    } => {
                        assert_eq!(name, "xs");
                        assert_eq!(separator, Some(",".to_string()));
                        assert!(!at_least_one);
                    }
                    _ => panic!("expected Splice antiquotation, got {content:?}"),
                },
                _ => panic!("expected QAntiquot inside QQuotation, got {inner:?}"),
            }
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_with_application_and_antiquots() {
    // q(Nat.add $a $b) - application with antiquotations
    // Parser produces: App(Proj(Ident("Nat"), "add"), [QAntiquot("a"), QAntiquot("b")])
    // Note: Nat.add is parsed as Proj because "add" is lowercase
    let expr = Parser::parse_expr("q(Nat.add $a $b)").unwrap();
    match expr {
        SurfaceExpr::QQuotation { kind, inner, .. } => {
            assert_eq!(kind, QQuotationKind::Value);
            // inner should be an App with Proj as function
            match *inner {
                SurfaceExpr::App(_, func, args) => {
                    // Nat.add is parsed as Proj(Nat, "add") because "add" is lowercase
                    match *func {
                        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                            assert!(
                                matches!(*base, SurfaceExpr::Ident(_, ref s) if s == "Nat"),
                                "Base should be Nat"
                            );
                            assert_eq!(field, "add", "Field should be 'add'");
                        }
                        _ => panic!("expected Proj, got {func:?}"),
                    }
                    assert_eq!(args.len(), 2);
                    // Both args should be QAntiquot
                    assert!(
                        matches!(&args[0].expr, SurfaceExpr::QAntiquot { content: QAntiquotContent::Simple(s), .. } if s == "a")
                    );
                    assert!(
                        matches!(&args[1].expr, SurfaceExpr::QAntiquot { content: QAntiquotContent::Simple(s), .. } if s == "b")
                    );
                }
                _ => panic!("expected App inside QQuotation, got {inner:?}"),
            }
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_projection_attaches_to_last_arg() {
    let expr = Parser::parse_expr("q(f x.y)").unwrap();
    match expr {
        SurfaceExpr::QQuotation { kind, inner, .. } => {
            assert_eq!(kind, QQuotationKind::Value);
            match *inner {
                SurfaceExpr::App(_, func, args) => {
                    assert!(
                        matches!(*func, SurfaceExpr::Ident(_, ref name) if name == "f"),
                        "Expected function to be f, got {func:?}"
                    );
                    assert_eq!(args.len(), 1);
                    match &args[0].expr {
                        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                            assert!(
                                matches!(base.as_ref(), SurfaceExpr::Ident(_, name) if name == "x"),
                                "Expected base to be x, got {base:?}"
                            );
                            assert_eq!(field, "y");
                        }
                        other => panic!("expected projection arg, got {other:?}"),
                    }
                }
                other => panic!("expected App inside QQuotation, got {other:?}"),
            }
        }
        _ => panic!("expected QQuotation, got {expr:?}"),
    }
}

#[test]
fn test_parse_q_alone_as_identifier() {
    // Just `q` without parens should be an identifier
    let expr = Parser::parse_expr("q").unwrap();
    assert!(
        matches!(expr, SurfaceExpr::Ident(_, ref s) if s == "q"),
        "expected identifier 'q', got {expr:?}"
    );
}

#[test]
fn test_parse_uppercase_q_alone_as_identifier() {
    // Just `Q` without parens should be an identifier
    let expr = Parser::parse_expr("Q").unwrap();
    assert!(
        matches!(expr, SurfaceExpr::Ident(_, ref s) if s == "Q"),
        "expected identifier 'Q', got {expr:?}"
    );
}

#[test]
fn test_parse_def_with_q_quotation() {
    // def mkAdd (a b : Q(Nat)) : Q(Nat) := q(Nat.add $a $b)
    let code = "def mkAdd (a : Q(Nat)) (b : Q(Nat)) : Q(Nat) := q(Nat.add $a $b)";
    let decl = Parser::parse_decl(code).expect("Should parse def with Qq");
    assert!(
        matches!(decl, SurfaceDecl::Def { ref name, .. } if name == "mkAdd"),
        "expected Def named 'mkAdd', got {decl:?}"
    );
}

// =============================================================================
// Qq Phase 3: Q-pattern tests (pattern matching on Q(α) values)
// Part of #16: Qq quotation support
// =============================================================================

#[test]
fn test_parse_q_pattern_simple() {
    // Match arm with simple q-pattern: q($x)
    let code = r#"
match e with
| q($x) => x
| _ => e
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with q-pattern");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert_eq!(arms.len(), 2);
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::QPattern(_)),
                "first arm should be QPattern, got {:?}",
                arms[0].pattern
            );
            assert!(
                matches!(arms[1].pattern, SurfacePattern::Wildcard),
                "second arm should be Wildcard"
            );
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

#[test]
fn test_parse_q_pattern_addition() {
    // Match arm with q-pattern: q($a + $b)
    let code = r#"
match e with
| q($a + $b) => true
| _ => false
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with q-pattern addition");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert_eq!(arms.len(), 2);
            if let SurfacePattern::QPattern(inner) = &arms[0].pattern {
                // The inner expression should be an application of + to two antiquots
                assert!(
                    matches!(&**inner, SurfaceExpr::App(_, _, args) if !args.is_empty()),
                    "q-pattern should contain an application, got {:?}",
                    inner
                );
            } else {
                panic!("first arm should be QPattern, got {:?}", arms[0].pattern);
            }
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

#[test]
fn test_parse_q_pattern_typed_antiquot() {
    // Match arm with typed antiquotation: q($(a : Nat) + $b)
    let code = r#"
match e with
| q($(a : Nat) + $b) => a
| _ => e
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with typed q-pattern");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert_eq!(arms.len(), 2);
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::QPattern(_)),
                "first arm should be QPattern, got {:?}",
                arms[0].pattern
            );
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

#[test]
fn test_parse_q_pattern_with_application() {
    // Match on function application: q(f $x)
    let code = r#"
match e with
| q(f $x) => x
| _ => e
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with q-pattern application");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            if let SurfacePattern::QPattern(inner) = &arms[0].pattern {
                // Should be App(f, [QAntiquot($x)])
                assert!(
                    matches!(&**inner, SurfaceExpr::App(_, func, _) if matches!(&**func, SurfaceExpr::Ident(_, name) if name == "f")),
                    "q-pattern should be application of f, got {:?}",
                    inner
                );
            } else {
                panic!("first arm should be QPattern, got {:?}", arms[0].pattern);
            }
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

#[test]
fn test_parse_q_pattern_in_function() {
    // Full function with q-pattern matching
    let code = r#"
def isAdd (e : Q(Nat)) : Bool :=
  match e with
  | q($a + $b) => true
  | _ => false
"#;
    let decl = Parser::parse_decl(code).expect("Should parse def with q-pattern match");
    assert!(
        matches!(decl, SurfaceDecl::Def { ref name, .. } if name == "isAdd"),
        "expected Def named 'isAdd', got {decl:?}"
    );
}

#[test]
fn test_parse_q_pattern_extract_args() {
    // Function that extracts arguments from addition
    let code = r#"
def getAddArgs (e : Q(Nat)) : Option (Q(Nat)) :=
  match e with
  | q($a + $b) => some a
  | _ => none
"#;
    let decl = Parser::parse_decl(code).expect("Should parse def extracting q-pattern args");
    assert!(
        matches!(decl, SurfaceDecl::Def { ref name, .. } if name == "getAddArgs"),
        "expected Def named 'getAddArgs', got {decl:?}"
    );
}

#[test]
fn test_parse_q_alone_is_not_pattern() {
    // Just `q` alone in a pattern should be a variable, not a QPattern
    let code = r#"
match e with
| q => q
| _ => e
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with 'q' variable");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::Var(name) if name == "q"),
                "first arm should be Var('q'), got {:?}",
                arms[0].pattern
            );
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

#[test]
fn test_parse_q_pattern_complex_expr() {
    // More complex expression inside q-pattern
    let code = r#"
match e with
| q(Nat.succ (Nat.succ $n)) => n
| _ => e
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with complex q-pattern");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::QPattern(_)),
                "first arm should be QPattern, got {:?}",
                arms[0].pattern
            );
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

// =============================================================================
// Qq Phase 4: Level antiquotation tests (universe polymorphism)
// Part of #16: Qq quotation support
// =============================================================================

#[test]
fn test_parse_level_antiquot_simple() {
    // Parse q(Type $u) - level antiquotation in universe position
    let code = "q(Type $u)";
    let expr = Parser::parse_expr(code).expect("Should parse q(Type $u)");
    assert!(
        matches!(
            expr,
            SurfaceExpr::QQuotation {
                kind: QQuotationKind::Value,
                ..
            }
        ),
        "expected q(...) value quotation, got {expr:?}"
    );
}

#[test]
fn test_parse_level_antiquot_sort() {
    // Parse q(Sort $u) - level antiquotation in Sort
    let code = "q(Sort $u)";
    let expr = Parser::parse_expr(code).expect("Should parse q(Sort $u)");
    assert!(
        matches!(
            expr,
            SurfaceExpr::QQuotation {
                kind: QQuotationKind::Value,
                ..
            }
        ),
        "expected q(...) value quotation, got {expr:?}"
    );
}

#[test]
fn test_parse_level_antiquot_with_succ() {
    // Parse q(Sort ($u + 1)) - level antiquotation with successor
    let code = "q(Sort ($u + 1))";
    let expr = Parser::parse_expr(code).expect("Should parse q(Sort ($u + 1))");
    assert!(
        matches!(
            expr,
            SurfaceExpr::QQuotation {
                kind: QQuotationKind::Value,
                ..
            }
        ),
        "expected q(...) value quotation, got {expr:?}"
    );
}

// Level antiquotations in Q(...) context - type quotation with level antiquotation
// Part of #23: Qq Phase 4 - Now working (enabled from Phase 4)
#[test]
fn test_parse_q_type_with_level_antiquot() {
    // Parse Q(Sort $u) - type quotation with level antiquotation
    let code = "Q(Sort $u)";
    let expr = Parser::parse_expr(code).expect("Should parse Q(Sort $u)");
    assert!(
        matches!(
            expr,
            SurfaceExpr::QQuotation {
                kind: QQuotationKind::Type,
                ..
            }
        ),
        "expected Q(...) type quotation, got {expr:?}"
    );
}

// Universe instantiation with level antiquotations
// Part of #23: Qq Phase 4 - Now working (enabled from Phase 4)
#[test]
fn test_parse_universe_inst_with_level_antiquot() {
    // Parse List.{$u} - explicit universe instantiation with antiquotations
    let code = "List.{$u}";
    let expr = Parser::parse_expr(code).expect("Should parse List.{$u}");
    // Universe instantiation produces an Ident or Proj with universe args
    assert!(
        !matches!(expr, SurfaceExpr::Hole(_)),
        "should not be a hole, got {expr:?}"
    );
}

// Q(...) type quotation with antiquotation inside
// Part of #23: Qq Phase 4 - Q uses parse_q_body for antiquot support
#[test]
fn test_parse_q_type_with_expr_antiquot() {
    // Parse Q($α) - type quotation with expression antiquotation
    let code = "Q($α)";
    let expr = Parser::parse_expr(code).expect("Should parse Q($α)");
    assert!(
        matches!(
            expr,
            SurfaceExpr::QQuotation {
                kind: QQuotationKind::Type,
                ..
            }
        ),
        "expected Q(...) type quotation, got {expr:?}"
    );
}

#[test]
fn test_parse_q_type_with_func_antiquot() {
    // Parse Q($f $α) - type quotation with function and argument antiquots
    let code = "Q($f $α)";
    let expr = Parser::parse_expr(code).expect("Should parse Q($f $α)");
    assert!(
        matches!(
            expr,
            SurfaceExpr::QQuotation {
                kind: QQuotationKind::Type,
                ..
            }
        ),
        "expected Q(...) type quotation, got {expr:?}"
    );
}

// =============================================================================
// Qq Phase 4: let-pattern syntax tests
// Part of #23: Qq Phase 4 - let q($a) := e | fallback in body
// =============================================================================

#[test]
fn test_parse_let_q_pattern_simple() {
    // Parse let q($a) := e | fallback in body
    let code = "let q($a) := e | fallback in a";
    let expr = Parser::parse_expr(code).expect("Should parse let q($a) := e | fallback in a");
    assert!(
        matches!(
            expr,
            SurfaceExpr::LetPattern(_, SurfacePattern::QPattern(_), _, _, _)
        ),
        "expected LetPattern with QPattern, got {expr:?}"
    );
}

#[test]
fn test_parse_let_q_pattern_with_add() {
    // Parse let q($a + $b) := e | fallback in body
    let code = "let q($a + $b) := e | none in some (a, b)";
    let expr = Parser::parse_expr(code).expect("Should parse let q($a + $b) pattern");
    assert!(
        matches!(
            expr,
            SurfaceExpr::LetPattern(_, SurfacePattern::QPattern(_), _, _, _)
        ),
        "expected LetPattern with QPattern, got {expr:?}"
    );
}

#[test]
fn test_parse_let_tilde_q_pattern() {
    // Parse let ~q($a) := e | fallback in body (quote4 style)
    let code = "let ~q($x) := e | none in some x";
    let expr = Parser::parse_expr(code).expect("Should parse let ~q($x) pattern");
    assert!(
        matches!(
            expr,
            SurfaceExpr::LetPattern(_, SurfacePattern::QPattern(_), _, _, _)
        ),
        "expected LetPattern with QPattern, got {expr:?}"
    );
}

// =============================================================================
// Qq Phase 4: ~q(...) pattern syntax tests (quote4 convention)
// Part of #23: Qq Phase 4 - Runtime pattern matching
// =============================================================================

#[test]
fn test_parse_tilde_q_pattern_simple() {
    // Parse ~q($x) - quote4 style pattern syntax
    let code = r#"
match e with
| ~q($x) => x
| _ => e
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with ~q pattern");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::QPattern(_)),
                "first arm should be QPattern, got {:?}",
                arms[0].pattern
            );
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

#[test]
fn test_parse_tilde_q_pattern_addition() {
    // Parse ~q($a + $b) - quote4 style with addition pattern
    let code = r#"
match e with
| ~q($a + $b) => (a, b)
| _ => (e, e)
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with ~q addition pattern");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::QPattern(_)),
                "first arm should be QPattern, got {:?}",
                arms[0].pattern
            );
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

#[test]
fn test_parse_tilde_q_pattern_complex() {
    // Parse ~q(Nat.succ $n) - quote4 style with constructor
    let code = r#"
match e with
| ~q(Nat.succ $n) => n
| ~q(Nat.zero) => zero
| _ => e
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with multiple ~q patterns");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::QPattern(_)),
                "first arm should be QPattern, got {:?}",
                arms[0].pattern
            );
            assert!(
                matches!(&arms[1].pattern, SurfacePattern::QPattern(_)),
                "second arm should be QPattern, got {:?}",
                arms[1].pattern
            );
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

#[test]
fn test_parse_mixed_q_and_tilde_q_patterns() {
    // Both q(...) and ~q(...) should work in the same match
    let code = r#"
match e with
| q($a + $b) => (a, b)
| ~q($a * $b) => (a, b)
| _ => (e, e)
"#;
    let expr = Parser::parse_expr(code).expect("Should parse match with mixed q and ~q patterns");
    match expr {
        SurfaceExpr::Match(_, _, _, arms) => {
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::QPattern(_)),
                "first arm (q) should be QPattern, got {:?}",
                arms[0].pattern
            );
            assert!(
                matches!(&arms[1].pattern, SurfacePattern::QPattern(_)),
                "second arm (~q) should be QPattern, got {:?}",
                arms[1].pattern
            );
        }
        other => panic!("expected Match expression, got {other:?}"),
    }
}

/// Test membership operator ∈ parsing (Part of #105)
#[test]
fn test_parse_membership_operator() {
    // x ∈ S should parse to Membership.mem S x (arguments swapped per Lean 4 spec)
    let expr = Parser::parse_expr("x ∈ S").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(&*func, SurfaceExpr::Ident(_, s) if s == "Membership.mem"),
                "expected Membership.mem function"
            );
            assert_eq!(args.len(), 2, "expected 2 arguments");
            // First arg should be S (the set), second should be x (the element)
            assert!(
                matches!(&args[0].expr, SurfaceExpr::Ident(_, s) if s == "S"),
                "first arg should be S"
            );
            assert!(
                matches!(&args[1].expr, SurfaceExpr::Ident(_, s) if s == "x"),
                "second arg should be x"
            );
        }
        _ => panic!("expected App expression, got {:?}", expr),
    }
}

/// Test not-membership operator ∉ parsing (Part of #105)
#[test]
fn test_parse_not_membership_operator() {
    // x ∉ S should parse to Not (Membership.mem S x)
    let expr = Parser::parse_expr("x ∉ S").unwrap();
    match expr {
        SurfaceExpr::App(_, outer_func, outer_args) => {
            assert!(
                matches!(&*outer_func, SurfaceExpr::Ident(_, s) if s == "Not"),
                "expected Not function"
            );
            assert_eq!(outer_args.len(), 1, "Not should have 1 argument");

            // Inner expression should be Membership.mem S x
            match &outer_args[0].expr {
                SurfaceExpr::App(_, inner_func, inner_args) => {
                    assert!(
                        matches!(&**inner_func, SurfaceExpr::Ident(_, s) if s == "Membership.mem"),
                        "inner should be Membership.mem"
                    );
                    assert_eq!(inner_args.len(), 2, "Membership.mem should have 2 args");
                }
                _ => panic!("expected inner App expression"),
            }
        }
        _ => panic!("expected App expression, got {:?}", expr),
    }
}

#[test]
fn test_lattice_top_bot() {
    // ⊤ should parse as Top.top (Mathlib convention)
    let expr = Parser::parse_expr("⊤").unwrap();
    assert!(matches!(expr, SurfaceExpr::Ident(_, s) if s == "Top.top"));

    // ⊥ should parse as Bot.bot (Mathlib convention)
    let expr = Parser::parse_expr("⊥").unwrap();
    assert!(matches!(expr, SurfaceExpr::Ident(_, s) if s == "Bot.bot"));

    // Should work in definitions
    let decls = Parser::parse_file("def test : Prop := ⊤ = ⊤ ∧ ⊥ = ⊥").unwrap();
    assert!(!decls.is_empty());
}

#[test]
fn test_postfix_bang_keeps_explicit_application_as_prefix_not_argument() {
    let expr = Parser::parse_expr("f !@g").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(&*func, SurfaceExpr::Ident(_, s) if s == "f"));
            assert_eq!(args.len(), 1, "expected one argument after f");
            match &args[0].expr {
                SurfaceExpr::App(_, not_func, not_args) => {
                    assert!(
                        matches!(&**not_func, SurfaceExpr::Ident(_, s) if s == "Not"),
                        "expected prefix Not argument"
                    );
                    assert_eq!(not_args.len(), 1, "Not should wrap exactly one expression");
                    assert!(
                        matches!(
                            &not_args[0].expr,
                            SurfaceExpr::Explicit(_, inner)
                                if matches!(&**inner, SurfaceExpr::Ident(_, s) if s == "g")
                        ),
                        "expected explicit application target @g inside Not"
                    );
                }
                other => panic!("expected Not application argument, got {other:?}"),
            }
        }
        other => panic!("expected application, got {other:?}"),
    }
}

#[test]
fn test_mapsto_lambda() {
    // ↦ (U+21A6) is an alias for => in lambda expressions (Lean 4 / Mathlib style)
    // Simple mapsto: fun x ↦ x
    let expr = Parser::parse_expr("fun x ↦ x").unwrap();
    assert!(matches!(expr, SurfaceExpr::Lambda(..)));

    // With type annotation: fun (x : Nat) ↦ x + 1
    let expr = Parser::parse_expr("fun (x : Nat) ↦ x + 1").unwrap();
    assert!(matches!(expr, SurfaceExpr::Lambda(..)));

    // Should be equivalent to standard => syntax
    let decls = Parser::parse_file("def id : Nat → Nat := fun x ↦ x").unwrap();
    assert!(!decls.is_empty());
}

// ============================================================================
// Structure literal tests (#165)
// ============================================================================

#[test]
fn test_struct_literal_empty() {
    // Empty struct literal: {}
    let expr = Parser::parse_expr("{}").unwrap();
    assert!(matches!(
        expr,
        SurfaceExpr::StructLit { fields, .. } if fields.is_empty()
    ));
}

#[test]
fn test_struct_literal_single_field() {
    // Single field: { x := 42 }
    let expr = Parser::parse_expr("{ x := 42 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { fields, .. } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "x");
        }
        _ => panic!("Expected StructLit"),
    }
}

#[test]
fn test_struct_literal_multiple_fields() {
    // Multiple fields: { x := 1, y := 2 }
    let expr = Parser::parse_expr("{ x := 1, y := 2 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { fields, .. } => {
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "x");
            assert_eq!(fields[1].name, "y");
        }
        _ => panic!("Expected StructLit"),
    }
}

#[test]
fn test_struct_literal_with_type_annotation() {
    // Type annotation: { x := 42 : Foo }
    let expr = Parser::parse_expr("{ x := 42 : Foo }").unwrap();
    match expr {
        SurfaceExpr::StructLit {
            fields,
            struct_type,
            ..
        } => {
            assert_eq!(fields.len(), 1);
            let _st = struct_type
                .as_ref()
                .expect("struct literal with type annotation should have struct_type");
        }
        _ => panic!("Expected StructLit"),
    }
}

#[test]
fn test_struct_literal_no_commas() {
    // Fields without commas (Lean 4 style): { x := 1 y := 2 }
    let expr = Parser::parse_expr("{ x := 1 y := 2 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { fields, .. } => {
            assert_eq!(fields.len(), 2);
        }
        _ => panic!("Expected StructLit"),
    }
}

#[test]
fn test_struct_literal_trailing_comma_single() {
    // Single field with trailing comma: { x := 1, }
    let expr = Parser::parse_expr("{ x := 1, }").unwrap();
    match expr {
        SurfaceExpr::StructLit { fields, .. } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "x");
        }
        _ => panic!("Expected StructLit"),
    }
}

#[test]
fn test_struct_literal_trailing_comma_multiple() {
    // Multiple fields with trailing comma: { x := 1, y := 2, }
    let expr = Parser::parse_expr("{ x := 1, y := 2, }").unwrap();
    match expr {
        SurfaceExpr::StructLit { fields, .. } => {
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "x");
            assert_eq!(fields[1].name, "y");
        }
        _ => panic!("Expected StructLit"),
    }
}

#[test]
fn test_struct_update_syntax_single_field() {
    // Struct update syntax: { s with x := newval }
    // Should produce StructLit with base expression
    let expr = Parser::parse_expr("{ s with x := 1 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { base, fields, .. } => {
            // Base should be the expression `s`
            assert!(base.is_some(), "Should have base expression");
            let base_expr = base.unwrap();
            assert!(
                matches!(*base_expr, SurfaceExpr::Ident(_, ref name) if name == "s"),
                "Base should be identifier 's'"
            );
            // Should have one field update
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "x");
        }
        _ => panic!("Expected StructLit with base"),
    }
}

#[test]
fn test_struct_update_syntax_multiple_fields() {
    // Multiple field updates: { s with x := 1, y := 2 }
    let expr = Parser::parse_expr("{ s with x := 1, y := 2 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { base, fields, .. } => {
            assert!(base.is_some(), "Should have base expression");
            let base_expr = base.unwrap();
            assert!(
                matches!(*base_expr, SurfaceExpr::Ident(_, ref name) if name == "s"),
                "Base should be identifier 's'"
            );
            // Should have two field updates
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "x");
            assert_eq!(fields[1].name, "y");
        }
        _ => panic!("Expected StructLit with base"),
    }
}

#[test]
fn test_struct_update_with_projection_base() {
    // Struct update with projection base: { foo.bar with x := 1 }
    let expr = Parser::parse_expr("{ foo.bar with x := 1 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { base, fields, .. } => {
            assert!(base.is_some(), "Should have base expression");
            let base_expr = base.unwrap();
            // Base should be a projection
            assert!(
                matches!(*base_expr, SurfaceExpr::Proj(..)),
                "Base should be a projection"
            );
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "x");
        }
        _ => panic!("Expected StructLit with projection base"),
    }
}

#[test]
fn test_struct_update_with_application_base() {
    // Struct update with function application base: { f x with y := 1 }
    let expr = Parser::parse_expr("{ f x with y := 1 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { base, fields, .. } => {
            assert!(base.is_some(), "Should have base expression");
            let base_expr = base.unwrap();
            // Base should be an application (f x)
            assert!(
                matches!(*base_expr, SurfaceExpr::App(..)),
                "Base should be an application"
            );
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "y");
        }
        _ => panic!("Expected StructLit with application base"),
    }
}

#[test]
fn test_struct_update_empty_fields() {
    // Struct update with no field updates: { s with }
    // This is a rare but valid case in Lean 4
    let expr = Parser::parse_expr("{ s with }").unwrap();
    match expr {
        SurfaceExpr::StructLit { base, fields, .. } => {
            assert!(base.is_some(), "Should have base expression");
            let base_expr = base.unwrap();
            assert!(
                matches!(*base_expr, SurfaceExpr::Ident(_, ref name) if name == "s"),
                "Base should be identifier 's'"
            );
            // Should have zero field updates
            assert_eq!(fields.len(), 0, "Should have no field updates");
        }
        _ => panic!("Expected StructLit with empty fields"),
    }
}

#[test]
fn test_struct_update_with_parenthesized_base() {
    // Struct update with parenthesized base: { (s) with x := 1 }
    let expr = Parser::parse_expr("{ (s) with x := 1 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { base, fields, .. } => {
            assert!(base.is_some(), "Should have base expression");
            // Base is (s), which parses as Paren wrapper or just s
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "x");
        }
        _ => panic!("Expected StructLit with parenthesized base"),
    }
}

#[test]
fn test_struct_update_nested() {
    // Nested struct update: { { s with x := 1 } with y := 2 }
    // The inner struct update becomes the base of the outer
    let expr = Parser::parse_expr("{ { s with x := 1 } with y := 2 }").unwrap();
    match expr {
        SurfaceExpr::StructLit { base, fields, .. } => {
            assert!(base.is_some(), "Outer should have base expression");
            // Outer has field y := 2
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "y");
            // Base should be inner struct update
            let base_expr = base.unwrap();
            match *base_expr {
                SurfaceExpr::StructLit {
                    base: inner_base,
                    fields: inner_fields,
                    ..
                } => {
                    assert!(inner_base.is_some(), "Inner should have base expression");
                    assert_eq!(inner_fields.len(), 1);
                    assert_eq!(inner_fields[0].name, "x");
                }
                _ => panic!("Inner base should be StructLit"),
            }
        }
        _ => panic!("Expected nested StructLit"),
    }
}

#[test]
fn test_struct_update_with_type_annotation() {
    // Struct update with type annotation: { s with x := 1 : Point }
    let expr = Parser::parse_expr("{ s with x := 1 : Point }").unwrap();
    match expr {
        SurfaceExpr::StructLit {
            base,
            fields,
            struct_type,
            ..
        } => {
            assert!(base.is_some(), "Should have base expression");
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "x");
            assert!(struct_type.is_some(), "Should have type annotation");
        }
        _ => panic!("Expected StructLit with type annotation"),
    }
}

// ============================================================================
// Set builder tests (#429 regression guard)
// ============================================================================

#[test]
fn test_set_builder_simple() {
    // Set builder: {x | x = 1} -> setOf (fun x => x = 1)
    let expr = Parser::parse_expr("{x | x = 1}").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            match *func {
                SurfaceExpr::Ident(_, name) => assert_eq!(name, "setOf"),
                _ => panic!("Expected setOf identifier"),
            }
            assert_eq!(args.len(), 1);
            match &args[0].expr {
                SurfaceExpr::Lambda(_, binders, body) => {
                    assert_eq!(binders.len(), 1);
                    assert_eq!(binders[0].name, "x");
                    assert!(
                        binders[0].ty.is_none(),
                        "untyped lambda binder should have no type, got {:?}",
                        binders[0].ty
                    );
                    assert!(!matches!(**body, SurfaceExpr::Hole(_)));
                }
                _ => panic!("Expected lambda argument"),
            }
        }
        _ => panic!("Expected setOf application"),
    }
}

#[test]
fn test_set_builder_typed_binder() {
    // Typed binder: {x : Nat | x = 0} -> setOf (fun (x : Nat) => x = 0)
    let expr = Parser::parse_expr("{x : Nat | x = 0}").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            match *func {
                SurfaceExpr::Ident(_, name) => assert_eq!(name, "setOf"),
                _ => panic!("Expected setOf identifier"),
            }
            assert_eq!(args.len(), 1);
            match &args[0].expr {
                SurfaceExpr::Lambda(_, binders, _) => {
                    assert_eq!(binders.len(), 1);
                    assert_eq!(binders[0].name, "x");
                    let ty = binders[0].ty.as_ref().expect("expected binder type");
                    match **ty {
                        SurfaceExpr::Ident(_, ref name) => assert_eq!(name, "Nat"),
                        _ => panic!("Expected Nat type"),
                    }
                }
                _ => panic!("Expected lambda argument"),
            }
        }
        _ => panic!("Expected setOf application"),
    }
}

#[test]
fn test_set_builder_separation_membership() {
    // Separation notation `{x ∈ s | p x}` desugars to
    // `setOf (fun x => x ∈ s ∧ p x)` = `setOf (fun x => And (Membership.mem s x) (p x))`
    // (note the `∈` argument swap: `Membership.mem s x`). This must NOT misparse
    // as a struct literal / collection / Hole.
    let expr = Parser::parse_expr("{x ∈ s | p x}").expect("separation set-builder parses");
    assert!(
        !format!("{expr:?}").contains("Hole("),
        "separation `{{x ∈ s | p x}}` must not fabricate a Hole, got {expr:?}"
    );
    let (func, args) = match expr {
        SurfaceExpr::App(_, func, args) => (func, args),
        _ => panic!("expected setOf application, got {expr:?}"),
    };
    match *func {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "setOf"),
        other => panic!("expected setOf identifier, got {other:?}"),
    }
    assert_eq!(args.len(), 1);
    let (binders, body) = match &args[0].expr {
        SurfaceExpr::Lambda(_, binders, body) => (binders, body),
        other => panic!("expected lambda argument, got {other:?}"),
    };
    assert_eq!(binders.len(), 1);
    assert_eq!(binders[0].name, "x");
    assert!(
        binders[0].ty.is_none(),
        "separation binder is untyped, got {:?}",
        binders[0].ty
    );
    // body = And (Membership.mem s x) (p x)
    let (and_head, and_args) = match &**body {
        SurfaceExpr::App(_, head, args) => (head, args),
        other => panic!("expected `And` application body, got {other:?}"),
    };
    match &**and_head {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "And"),
        other => panic!("expected `And` head, got {other:?}"),
    }
    assert_eq!(and_args.len(), 2, "And takes membership ∧ predicate");
    // First conjunct: Membership.mem s x
    let (mem_head, mem_args) = match &and_args[0].expr {
        SurfaceExpr::App(_, head, args) => (head, args),
        other => panic!("expected `Membership.mem` application, got {other:?}"),
    };
    match &**mem_head {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "Membership.mem"),
        other => panic!("expected `Membership.mem` head, got {other:?}"),
    }
    assert_eq!(mem_args.len(), 2);
    match &mem_args[0].expr {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "s", "mem's first arg is the set `s`"),
        other => panic!("expected set `s`, got {other:?}"),
    }
    match &mem_args[1].expr {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "x", "mem's second arg is the element `x`"),
        other => panic!("expected element `x`, got {other:?}"),
    }
    // Second conjunct: the predicate `p x` must be preserved (not a Hole).
    assert!(
        matches!(&and_args[1].expr, SurfaceExpr::App(..)),
        "second conjunct should be the applied predicate `p x`, got {:?}",
        and_args[1].expr
    );
}

#[test]
fn test_set_builder_separation_complex_set_expr() {
    // The set after `∈` is a full expression, and stops at the top-level pipe:
    // `{n ∈ Finset.range k | n = 0}`.
    let expr =
        Parser::parse_expr("{n ∈ Finset.range k | n = 0}").expect("separation with applied set");
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref n) if n == "setOf"));
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0].expr, SurfaceExpr::Lambda(..)));
        }
        other => panic!("expected setOf application, got {other:?}"),
    }
}

// Brick 3 (operator/notation coverage): the brace forms Brick 1 turned into
// loud gaps now parse for real. A bare-ident brace list is Lean's structInst
// field-abbreviation reading (`{A, B, C}` ⇒ `{ A := A, B := B, C := C }`), and a
// literal/expr brace list is a collection literal (`{1, 2, 3}` ⇒
// `insert 1 (insert 2 (singleton 3))`) — never a fabricated `Hole`.
#[test]
fn test_finite_set_bare_idents_parse_as_struct_abbrev() {
    let expr = Parser::parse_expr("{A, B, C}").expect("bare-ident brace list parses (Brick 3)");
    assert!(
        !format!("{expr:?}").contains("Hole("),
        "must not fabricate a Hole, got {expr:?}"
    );
    assert!(
        matches!(expr, SurfaceExpr::StructLit { .. }),
        "bare-ident `{{A, B, C}}` is a structInst field-abbreviation, got {expr:?}"
    );
}

#[test]
fn test_nested_braces_single_level_rejected() {
    Parser::parse_expr("{A, {B}}").expect_err("nested finite set should be rejected loudly");
}

#[test]
fn test_nested_braces_two_levels_rejected() {
    Parser::parse_expr("{A, {B, {C}}}").expect_err("nested finite set should be rejected loudly");
}

#[test]
fn test_nested_braces_multiple_nested_parse() {
    // `{{A}, {B}}` — a collection literal of two singleton-abbrev braces; parses
    // (Brick 3), no fabricated Hole.
    let expr = Parser::parse_expr("{{A}, {B}}").expect("collection of braces parses (Brick 3)");
    assert!(
        !format!("{expr:?}").contains("Hole("),
        "must not fabricate a Hole, got {expr:?}"
    );
}

#[test]
fn test_nested_braces_complex_rejected() {
    Parser::parse_expr("{A, {B, C}, {D, {E}}}")
        .expect_err("nested finite set should be rejected loudly");
}

// =========================================================================
// Property-based tests (#175)
// =========================================================================

use proptest::prelude::*;

proptest! {
    /// Parser never panics on arbitrary input
    #[test]
    fn prop_parser_no_panic(input in "\\PC{0,100}") {
        // Parser should handle any input without panicking (may return Err)
        let _ = Parser::parse_expr(&input);
    }

    /// Parser never panics on declaration input
    #[test]
    fn prop_parser_decl_no_panic(input in "[a-zA-Z0-9_: ()=>{}\\[\\].,\\n ]*") {
        let _ = Parser::parse_decl(&input);
    }

    /// Parsing identifiers always succeeds and produces Ident
    #[test]
    fn prop_ident_parses(name in "[a-zA-Z_][a-zA-Z0-9_]{0,10}") {
        // Filter out keywords (comprehensive list)
        let keywords = [
            "_",
            // Declarations
            "def", "theorem", "lemma", "example", "abbrev", "structure",
            "class", "instance", "inductive", "axiom", "constant", "variable",
            "opaque", "partial", "private", "protected", "scoped", "local",
            // Control flow
            "fun", "forall", "let", "in", "if", "then", "else", "match",
            "with", "where", "do", "return", "by", "have", "show", "calc",
            // Types
            "Type", "Prop", "Sort",
            // Literals/operators
            "true", "false", "and", "or", "not",
            // Module system
            "open", "section", "namespace", "end", "import", "export",
            "universe", "attribute", "syntax", "macro", "mutual", "unsafe",
        ];
        if keywords.contains(&name.as_str()) {
            return Ok(());
        }

        let expr = Parser::parse_expr(&name)?;
        prop_assert!(
            matches!(&expr, SurfaceExpr::Ident(_, s) if s == &name),
            "Expected Ident('{}'), got {:?}",
            name, expr
        );
    }

    /// Natural literals parse correctly
    #[test]
    fn prop_natlit_parses(n in 0u64..1_000_000) {
        let input = n.to_string();
        let expr = Parser::parse_expr(&input)?;
        prop_assert!(
            matches!(expr, SurfaceExpr::Lit(_, SurfaceLit::Nat(v)) if v == n),
            "Expected NatLit({}), got {:?}",
            n, expr
        );
    }

    /// Lambda expressions with valid identifiers parse successfully
    #[test]
    fn prop_lambda_parses(name in "[a-z][a-z0-9]{0,5}") {
        // Skip keywords that would cause parse failures
        let keywords = [
            "fun", "let", "in", "if", "do", "by", "end", "and", "or", "not",
            "match", "with", "where", "return", "have", "show", "calc", "else", "then",
            "rfl", // Reflexivity keyword (TokenKind::Rfl)
        ];
        if keywords.contains(&name.as_str()) {
            return Ok(());
        }

        let input = format!("fun {name} => {name}");
        let expr = Parser::parse_expr(&input)?;
        prop_assert!(
            matches!(expr, SurfaceExpr::Lambda(_, _, _)),
            "Expected Lambda, got {:?}",
            expr
        );
    }

    /// Arrow expressions parse with correct associativity
    #[test]
    fn prop_arrow_right_assoc(a in "[A-Z]", b in "[A-Z]", c in "[A-Z]") {
        let input = format!("{a} → {b} → {c}");
        let expr = Parser::parse_expr(&input)?;
        // Should be A → (B → C), i.e., right associative
        match expr {
            SurfaceExpr::Arrow(_, left, right) => {
                prop_assert!(
                    matches!(*left, SurfaceExpr::Ident(_, _)),
                    "Expected left to be Ident"
                );
                prop_assert!(
                    matches!(*right, SurfaceExpr::Arrow(_, _, _)),
                    "Expected right to be Arrow"
                );
            }
            other => prop_assert!(false, "Expected Arrow, got {:?}", other),
        }
    }

    /// Function application is left associative
    #[test]
    fn prop_app_left_assoc(
        f in "[a-z]",
        x in "[a-z]",
        y in "[a-z]"
    ) {
        prop_assume!(f != x && f != y && x != y);
        let input = format!("{f} {x} {y}");
        let expr = Parser::parse_expr(&input)?;
        // Should be (f x) y, i.e., left associative
        match expr {
            SurfaceExpr::App(_, func, args) => {
                prop_assert!(
                    matches!(*func, SurfaceExpr::Ident(_, _)),
                    "Expected func to be Ident"
                );
                prop_assert_eq!(args.len(), 2, "Expected 2 args");
            }
            other => prop_assert!(false, "Expected App, got {:?}", other),
        }
    }

    /// Forall expressions parse correctly
    #[test]
    fn prop_forall_parses(name in "[a-z][a-z0-9]{0,4}") {
        let keywords = [
            "fun", "let", "in", "if", "do", "by", "end", "and", "or", "not",
            "match", "with", "where", "return", "have", "show", "calc", "else", "then", "forall",
        ];
        if keywords.contains(&name.as_str()) {
            return Ok(());
        }

        let input = format!("forall ({name} : Prop), {name}");
        let expr = Parser::parse_expr(&input)?;
        prop_assert!(
            matches!(expr, SurfaceExpr::Pi(_, _, _)),
            "Expected Pi (forall), got {:?}",
            expr
        );
    }

    /// String literals parse correctly
    #[test]
    fn prop_strlit_parses(s in "[a-zA-Z0-9 ]{0,20}") {
        // Strings that might look like escape sequences need special handling
        if s.contains('\\') || s.contains('"') {
            return Ok(());
        }

        let input = format!("\"{}\"", s);
        let expr = Parser::parse_expr(&input)?;
        prop_assert!(
            matches!(expr, SurfaceExpr::Lit(_, SurfaceLit::String(_))),
            "Expected String literal, got {:?}",
            expr
        );
    }

    /// If-then-else expressions parse correctly
    #[test]
    fn prop_if_then_else_parses(
        cond in "[a-zA-Z]",
        then_val in "[a-zA-Z]",
        else_val in "[a-zA-Z]"
    ) {
        let input = format!("if {cond} then {then_val} else {else_val}");
        let expr = Parser::parse_expr(&input)?;
        prop_assert!(
            matches!(expr, SurfaceExpr::If(_, _, _, _)),
            "Expected If, got {:?}",
            expr
        );
    }
}

// =============================================================================
// Bug #480: Qualified names in nested constructor calls
// =============================================================================

#[test]
fn test_qualified_name_in_nested_constructor_call() {
    // This is the failing case from issue #480:
    // Qualified names like Nat.rec inside nested constructor argument positions
    let code = r#"def test := MicroExpr.bvar (Nat.rec (fun _ => Nat) 0 (fun _ _ => 1) 2)"#;
    let decls =
        Parser::parse_file(code).expect("Should parse qualified name in nested constructor");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_qualified_name_in_match_arm_result() {
    // Match arm with qualified name in result expression
    let code = r#"
match e with
| MicroExpr.bvar i => MicroExpr.bvar (Nat.add i n)
| _ => e
"#;
    let expr =
        Parser::parse_expr(code).expect("Should parse match arm with qualified name in result");
    assert!(
        matches!(expr, SurfaceExpr::Match(_, _, _, ref arms) if arms.len() == 2),
        "expected Match with 2 arms, got {expr:?}"
    );
}

#[test]
fn test_multiple_qualified_names_in_nested_call() {
    // Multiple qualified names in nested positions
    let code = r#"def f := Foo.bar (Nat.succ (Nat.zero)) (List.cons x (List.nil))"#;
    let decls = Parser::parse_file(code).expect("Should parse multiple nested qualified names");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "f"));
}

// =============================================================================
// Bug #484: Generalize keyword handling in qualified names
// =============================================================================

#[test]
fn test_qualified_name_type_keyword() {
    // Type keyword as qualified name part
    let code = r#"def test := Option.Type"#;
    let decls = Parser::parse_file(code).expect("Should parse Type as qualified name part");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_qualified_name_sort_keyword() {
    // Sort keyword as qualified name part
    let code = r#"def test := Level.Sort"#;
    let decls = Parser::parse_file(code).expect("Should parse Sort as qualified name part");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_qualified_name_match_keyword() {
    // match keyword as qualified name part (method name)
    let code = r#"def test := Foo.match"#;
    let decls = Parser::parse_file(code).expect("Should parse match as qualified name part");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_qualified_name_do_keyword() {
    // do keyword as qualified name part (monad method)
    let code = r#"def test := Monad.do"#;
    let decls = Parser::parse_file(code).expect("Should parse do as qualified name part");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_qualified_name_return_keyword() {
    // return keyword as qualified name part
    let code = r#"def test := Monad.return"#;
    let decls = Parser::parse_file(code).expect("Should parse return as qualified name part");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_qualified_name_prop_keyword() {
    // Prop keyword as qualified name part
    let code = r#"def test := Logic.Prop"#;
    let decls = Parser::parse_file(code).expect("Should parse Prop as qualified name part");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_multi_level_qualified_name_with_keyword() {
    // Multiple namespace levels with keyword at end
    let code = r#"def test := Foo.Bar.rec"#;
    let decls =
        Parser::parse_file(code).expect("Should parse multi-level qualified name with keyword");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_keyword_projection_verifies_value() {
    // Verify Nat.rec is parsed as projection
    // Nat.rec -> Proj(Nat, "rec"), elaborator resolves to Nat.rec constant
    let code = "Nat.rec";
    match Parser::parse_expr(code).expect("Should parse Nat.rec") {
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => match base.as_ref() {
            SurfaceExpr::Ident(_, name) => {
                assert_eq!(name, "Nat", "Base should be 'Nat'");
                assert_eq!(field, "rec", "Field should be 'rec'");
            }
            other => panic!("Expected Ident base, got {other:?}"),
        },
        other => panic!("Expected Proj, got {:?}", other),
    }
}

#[test]
fn test_keyword_after_keyword_in_qualified_name() {
    // Edge case: keyword followed by another keyword
    let code = r#"def test := Foo.rec.Type"#;
    let decls =
        Parser::parse_file(code).expect("Should parse keyword after keyword in qualified name");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

// =============================================================================
// Bug #486: qualified_ident keyword segments in command contexts
// =============================================================================

#[test]
fn test_open_command_with_keyword_segment() {
    let code = "open Nat.rec";
    let decls = Parser::parse_file(code)
        .unwrap_or_else(|err| panic!("Should parse open command with keyword segment: {err:?}"));
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Open { paths, .. } => {
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].path, vec!["Nat".to_string(), "rec".to_string()]);
        }
        other => panic!("Expected Open decl, got {other:?}"),
    }
}

#[test]
fn test_open_command_with_keyword_names_list() {
    let code = "open Nat (rec match)";
    let decls = Parser::parse_file(code)
        .unwrap_or_else(|err| panic!("Should parse open command with keyword names list: {err:?}"));
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Open { paths, .. } => {
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].path, vec!["Nat".to_string()]);
            assert_eq!(paths[0].names, vec!["rec".to_string(), "match".to_string()]);
        }
        other => panic!("Expected Open decl, got {other:?}"),
    }
}

#[test]
fn test_open_scoped_with_keyword_segment() {
    let code = "open scoped Foo.match";
    let decls = Parser::parse_file(code)
        .unwrap_or_else(|err| panic!("Should parse open scoped with keyword segment: {err:?}"));
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Open { scoped, paths, .. } => {
            assert!(*scoped);
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].path, vec!["Foo".to_string(), "match".to_string()]);
        }
        other => panic!("Expected Open decl, got {other:?}"),
    }
}

#[test]
fn test_print_command_with_keyword_segment() {
    let code = "#print Nat.rec";
    let decls = Parser::parse_file(code)
        .unwrap_or_else(|err| panic!("Should parse #print with keyword segment: {err:?}"));
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Print { name, .. } => {
            assert_eq!(name, "Nat.rec");
        }
        other => panic!("Expected Print decl, got {other:?}"),
    }
}

#[test]
fn test_attribute_command_with_keyword_segment() {
    let code = "attribute [simp] Nat.rec";
    let decls = Parser::parse_file(code).unwrap_or_else(|err| {
        panic!("Should parse attribute command with keyword segment: {err:?}")
    });
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Attribute { names, .. } => {
            assert_eq!(names, &vec!["Nat.rec".to_string()]);
        }
        other => panic!("Expected Attribute decl, got {other:?}"),
    }
}

#[test]
fn test_attribute_command_removal_syntax() {
    let code = "attribute [-simp] Nat.rec";
    let decls = Parser::parse_file(code)
        .unwrap_or_else(|err| panic!("Should parse attribute removal command: {err:?}"));
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Attribute { attrs, names, .. } => {
            assert_eq!(names, &vec!["Nat.rec".to_string()]);
            assert_eq!(
                attrs,
                &vec![AttributeCommandAttr::Remove("simp".to_string())]
            );
        }
        other => panic!("Expected Attribute decl, got {other:?}"),
    }
}

#[test]
fn test_import_with_keyword_segment() {
    let code = "import Foo.match";
    let decls = Parser::parse_file(code)
        .unwrap_or_else(|err| panic!("Should parse import with keyword segment: {err:?}"));
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Import { paths, .. } => {
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0], vec!["Foo".to_string(), "match".to_string()]);
        }
        other => panic!("Expected Import decl, got {other:?}"),
    }
}

// =============================================================================
// Bug #485: qualified names in terms
// Parser represents dotted terms as projections; elaborator resolves to constants
// when the namespace-qualified name exists.
// =============================================================================

#[test]
fn test_lowercase_qualified_name_in_def() {
    // Lowercase after dot is parsed as projection - elaborator resolves to qualified name
    // namespace foo; def foo.bar : Nat := 1
    let code = r#"def test := foo.bar"#;
    // Parser produces Proj(Ident("foo"), Named("bar"))
    // Elaborator resolves to foo.bar constant via namespace fallback
    let decls = Parser::parse_file(code).expect("Should parse lowercase dotted expr in def");
    if let SurfaceDecl::Def { val, .. } = &decls[0] {
        match val.as_ref() {
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => match base.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, "foo", "Base should be 'foo'");
                    assert_eq!(field, "bar", "Field should be 'bar'");
                }
                other => panic!("Expected Ident base, got {other:?}"),
            },
            other => panic!("Expected Proj, got {other:?}"),
        }
    } else {
        panic!("Expected Def");
    }
}

#[test]
fn test_lowercase_multi_segment_qualified_name() {
    // Multi-segment lowercase: nested projections
    // foo.bar.baz -> Proj(Proj(foo, bar), baz)
    let code = r#"def test := foo.bar.baz"#;
    let decls = Parser::parse_file(code).expect("Should parse multi-segment lowercase dotted expr");
    if let SurfaceDecl::Def { val, .. } = &decls[0] {
        match val.as_ref() {
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                assert_eq!(field, "baz", "Outer field should be 'baz'");
                match base.as_ref() {
                    SurfaceExpr::Proj(_, inner_base, Projection::Named(inner_field)) => {
                        assert_eq!(inner_field, "bar", "Inner field should be 'bar'");
                        match inner_base.as_ref() {
                            SurfaceExpr::Ident(_, name) => {
                                assert_eq!(name, "foo", "Base should be 'foo'");
                            }
                            other => panic!("Expected Ident base, got {other:?}"),
                        }
                    }
                    other => panic!("Expected inner Proj, got {other:?}"),
                }
            }
            other => panic!("Expected Proj, got {other:?}"),
        }
    } else {
        panic!("Expected Def");
    }
}

#[test]
fn test_mixed_case_nested_projections() {
    // Mixed case: foo.Bar.baz
    // All dots are projections, elaborator resolves to qualified names.
    // Result: Proj(Proj(Ident("foo"), "Bar"), "baz")
    let code = r#"def test := foo.Bar.baz"#;
    let decls = Parser::parse_file(code).expect("Should parse foo.Bar.baz");
    if let SurfaceDecl::Def { val, .. } = &decls[0] {
        match val.as_ref() {
            SurfaceExpr::Proj(_, outer_base, Projection::Named(outer_field)) => {
                assert_eq!(outer_field, "baz", "Outer field should be 'baz'");
                match outer_base.as_ref() {
                    SurfaceExpr::Proj(_, inner_base, Projection::Named(inner_field)) => {
                        assert_eq!(inner_field, "Bar", "Inner field should be 'Bar'");
                        match inner_base.as_ref() {
                            SurfaceExpr::Ident(_, name) => {
                                assert_eq!(name, "foo", "Base should be 'foo'");
                            }
                            other => panic!("Expected Ident base, got {other:?}"),
                        }
                    }
                    other => panic!("Expected inner Proj, got {other:?}"),
                }
            }
            other => panic!("Expected outer Proj, got {other:?}"),
        }
    } else {
        panic!("Expected Def");
    }
}

#[test]
fn test_uppercase_base_with_lowercase_segment() {
    // Uppercase base with lowercase segment is parsed as projection.
    // Foo.bar -> Proj(Foo, "bar"), elaborator resolves to Foo.bar constant if it exists.
    let code = r#"def test := Foo.bar"#;
    let decls = Parser::parse_file(code).expect("Should parse Foo.bar");
    if let SurfaceDecl::Def { val, .. } = &decls[0] {
        match val.as_ref() {
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => match base.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, "Foo", "Base should be 'Foo'");
                    assert_eq!(field, "bar", "Field should be 'bar'");
                }
                other => panic!("Expected Ident base, got {other:?}"),
            },
            other => panic!("Expected Proj, got {other:?}"),
        }
    } else {
        panic!("Expected Def");
    }
}

#[test]
fn test_internal_segment_as_projection() {
    // Segments starting with '_' are parsed as projections.
    // foo._private -> Proj(foo, "_private"), elaborator resolves to foo._private if it exists.
    let code = r#"def test := foo._private"#;
    let decls = Parser::parse_file(code).expect("Should parse foo._private");
    if let SurfaceDecl::Def { val, .. } = &decls[0] {
        match val.as_ref() {
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => match base.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, "foo", "Base should be 'foo'");
                    assert_eq!(field, "_private", "Field should be '_private'");
                }
                other => panic!("Expected Ident base, got {other:?}"),
            },
            other => panic!("Expected Proj, got {other:?}"),
        }
    } else {
        panic!("Expected Def");
    }
}

#[test]
fn test_keyword_segment_as_projection() {
    // Keyword segment (like `rec`) is parsed as projection.
    // foo.rec -> Proj(foo, "rec"), elaborator resolves to foo.rec constant if it exists.
    let code = r#"def test := foo.rec"#;
    let decls = Parser::parse_file(code).expect("Should parse foo.rec");
    if let SurfaceDecl::Def { val, .. } = &decls[0] {
        match val.as_ref() {
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => match base.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, "foo", "Base should be 'foo'");
                    assert_eq!(field, "rec", "Field should be 'rec'");
                }
                other => panic!("Expected Ident base, got {other:?}"),
            },
            other => panic!("Expected Proj, got {other:?}"),
        }
    } else {
        panic!("Expected Def");
    }
}

#[test]
fn test_lowercase_qualified_name_in_expression() {
    // Lowercase qualified name used in application
    let code = r#"def test := myModule.helper x y"#;
    let decls =
        Parser::parse_file(code).expect("Should parse lowercase qualified name in application");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "test"));
}

#[test]
fn test_lowercase_qualified_name_in_check() {
    // #check with lowercase qualified name
    let code = r#"#check foo.bar.baz"#;
    let decls =
        Parser::parse_file(code).expect("Should parse #check with lowercase qualified name");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Check { .. }));
}

// =============================================================================
// Bug #486: qualified_ident should accept keywords after dots
// =============================================================================

#[test]
fn test_qualified_ident_accepts_keyword_segments() {
    // qualified_ident is used for commands like #print and open paths
    let code = r#"#print Foo.match"#;
    let decls = Parser::parse_file(code)
        .expect("Should parse #print with keyword segment in qualified name");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Print { .. }));
}

// =============================================================================
// Bug #487: escaped identifiers via «...»
// =============================================================================

#[test]
fn test_def_with_escaped_name() {
    let code = r#"def «match» : Nat := 0"#;
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { name, .. } => assert_eq!(name, "match"),
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_def_with_escaped_qualified_name() {
    let code = r#"def «foo.bar» : Nat := 1"#;
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { name, .. } => assert_eq!(name, "foo.bar"),
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_def_with_escaped_segment_in_qualified_name() {
    let code = r#"def Foo.«match» : Nat := 2"#;
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { name, .. } => assert_eq!(name, "Foo.match"),
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_def_with_dot_universe_params() {
    let code = "def foo.{u} (A : Type u) (x : A) := x";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name,
            universe_params,
            binders,
            ..
        } => {
            assert_eq!(name, "foo");
            assert_eq!(universe_params, &vec!["u".to_string()]);
            assert_eq!(binders.len(), 2);
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_def_with_qualified_dot_universe_params() {
    let code = "def Foo.bar.{u} (A : Type u) (x : A) := x";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name,
            universe_params,
            binders,
            ..
        } => {
            assert_eq!(name, "Foo.bar");
            assert_eq!(universe_params, &vec!["u".to_string()]);
            assert_eq!(binders.len(), 2);
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_check_with_escaped_name() {
    let code = r#"#check «simp»"#;
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Check { expr, .. } => match expr.as_ref() {
            SurfaceExpr::Ident(_, name) => assert_eq!(name, "simp"),
            other => panic!("Expected Ident, got {other:?}"),
        },
        other => panic!("Expected Check, got {other:?}"),
    }
}

#[test]
fn test_open_with_escaped_segment() {
    let code = r#"open Foo.«match»"#;
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Open { paths, scoped, .. } => {
            assert!(!scoped);
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].path, vec!["Foo".to_string(), "match".to_string()]);
        }
        other => panic!("Expected Open, got {other:?}"),
    }
}

#[test]
fn test_namespace_with_escaped_segment() {
    let code = r#"namespace Foo.«match»
def bar : Nat := 1
end «match»"#;
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Namespace { name, decls, .. } => {
            assert_eq!(name, "Foo.match");
            assert_eq!(decls.len(), 1);
        }
        other => panic!("Expected Namespace, got {other:?}"),
    }
}

#[test]
fn test_export_single_name() {
    let code = "export Morning.Sky (star)";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Export {
            namespace, names, ..
        } => {
            assert_eq!(namespace, &["Morning", "Sky"]);
            assert_eq!(names, &["star"]);
        }
        other => panic!("Expected Export, got {other:?}"),
    }
}

#[test]
fn test_export_multiple_names() {
    let code = "export Nat (add mul succ)";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Export {
            namespace, names, ..
        } => {
            assert_eq!(namespace, &["Nat"]);
            assert_eq!(names, &["add", "mul", "succ"]);
        }
        other => panic!("Expected Export, got {other:?}"),
    }
}

#[test]
fn test_export_requires_at_least_one_name() {
    // Error recovery: malformed export becomes RawDecl placeholder
    let decls = Parser::parse_file("export Nat ()").expect("recovery should not fail");
    assert_eq!(decls.len(), 1);
    assert!(
        matches!(&decls[0], SurfaceDecl::RawDecl { .. }),
        "expected RawDecl, got {:?}",
        decls[0]
    );
}

#[test]
fn test_opaque_without_value() {
    let code = "opaque myConstant : Nat → Nat";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Opaque { name, val, .. } => {
            assert_eq!(name, "myConstant");
            assert!(
                val.is_none(),
                "opaque without value should have val=None, got {val:?}"
            );
        }
        other => panic!("Expected Opaque, got {other:?}"),
    }
}

#[test]
fn test_opaque_with_value() {
    let code = "opaque secretImpl : String → Bool := fun _ => true";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Opaque { name, val, .. } => {
            assert_eq!(name, "secretImpl");
            let _val = val.as_ref().expect("opaque with value should have val");
        }
        other => panic!("Expected Opaque, got {other:?}"),
    }
}

#[test]
fn test_opaque_with_binders() {
    let code = "opaque mapImpl (α β : Type) : (α → β) → List α → List β";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Opaque {
            name, binders, val, ..
        } => {
            assert_eq!(name, "mapImpl");
            assert_eq!(binders.len(), 2); // (α β : Type) is two binders
            assert!(
                val.is_none(),
                "opaque without value should have val=None, got {val:?}"
            );
        }
        other => panic!("Expected Opaque, got {other:?}"),
    }
}

// =============================================================================
// Issue #494: Standalone deriving instance command
// =============================================================================

#[test]
fn test_deriving_instance_single_class_single_type() {
    let code = "deriving instance Repr for MyType";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::DerivingInstance { classes, types, .. } => {
            assert_eq!(classes, &["Repr"]);
            assert_eq!(types, &["MyType"]);
        }
        other => panic!("Expected DerivingInstance, got {other:?}"),
    }
}

#[test]
fn test_deriving_instance_multiple_classes_single_type() {
    let code = "deriving instance Repr, BEq for MyType";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::DerivingInstance { classes, types, .. } => {
            assert_eq!(classes, &["Repr", "BEq"]);
            assert_eq!(types, &["MyType"]);
        }
        other => panic!("Expected DerivingInstance, got {other:?}"),
    }
}

#[test]
fn test_deriving_instance_multiple_types() {
    let code = "deriving instance Hashable for Type1, Type2";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::DerivingInstance { classes, types, .. } => {
            assert_eq!(classes, &["Hashable"]);
            assert_eq!(types, &["Type1", "Type2"]);
        }
        other => panic!("Expected DerivingInstance, got {other:?}"),
    }
}

#[test]
fn test_deriving_instance_qualified_names() {
    let code = "deriving instance Std.Repr, MyLib.BEq for Data.MyType";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::DerivingInstance { classes, types, .. } => {
            assert_eq!(classes, &["Std.Repr", "MyLib.BEq"]);
            assert_eq!(types, &["Data.MyType"]);
        }
        other => panic!("Expected DerivingInstance, got {other:?}"),
    }
}

// NOTE: Export command tests are in the issue #492 section above (lines ~2903-2933)

#[test]
fn test_parse_inductive_with_opaque_ctor() {
    // Test that constructor names can be keywords followed by underscore
    // Issue #521: opaque_ was being parsed as Opaque keyword + Underscore
    let code = r#"
inductive MicroExpr : Type
| opaque_ : MicroExpr
"#;
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Inductive { ctors, .. } => {
            assert_eq!(ctors.len(), 1);
            assert_eq!(ctors[0].name, "opaque_");
        }
        other => panic!("Expected Inductive, got {other:?}"),
    }
}

// ============================================================================
// Coinductive tests (#191)
// ============================================================================

#[test]
fn test_parse_coinductive_basic() {
    let code = "coinductive Stream (α : Type) : Type where
| nil : Stream α
| cons : α → Stream α → Stream α";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Coinductive { name, ctors, .. } => {
            assert_eq!(name, "Stream");
            assert_eq!(ctors.len(), 2);
            assert_eq!(ctors[0].name, "nil");
            assert_eq!(ctors[1].name, "cons");
        }
        other => panic!("Expected Coinductive, got {other:?}"),
    }
}

#[test]
fn test_parse_coinductive_pipe_style() {
    let code = "coinductive Colist (α : Type) : Type
| conil : Colist α
| cocons : α → Colist α → Colist α";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Coinductive { name, ctors, .. } => {
            assert_eq!(name, "Colist");
            assert_eq!(ctors.len(), 2);
            assert_eq!(ctors[0].name, "conil");
            assert_eq!(ctors[1].name, "cocons");
        }
        other => panic!("Expected Coinductive, got {other:?}"),
    }
}

// ============================================================================
// Termination hint tests (#1132)
// ============================================================================

#[test]
fn test_parse_termination_by_basic() {
    // Issue #1132: termination_by was being consumed as part of def body
    let code = "def foo (n : Nat) : Nat := n
termination_by n";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, termination, ..
        } => {
            assert_eq!(name, "foo");
            assert!(
                termination.termination_by.is_some(),
                "termination_by should be parsed, not consumed by expression parser"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_termination_by_with_arrow() {
    // Full termination_by syntax with params and arrow
    let code = "def fib (n : Nat) : Nat := match n with
| 0 => 0
| 1 => 1
| n + 2 => fib n + fib (n + 1)
termination_by n => n";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, termination, ..
        } => {
            assert_eq!(name, "fib");
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should be present");
            assert_eq!(tb.params, vec!["n"]);
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_decreasing_by_basic() {
    // decreasing_by clause with tactic
    let code = "def foo (n : Nat) : Nat := n
decreasing_by simp_arith";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, termination, ..
        } => {
            assert_eq!(name, "foo");
            assert!(
                termination.decreasing_by.is_some(),
                "decreasing_by should be parsed"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_both_termination_hints() {
    // Both termination_by and decreasing_by together
    let code = "def ack (m n : Nat) : Nat := match m, n with
| 0, n => n + 1
| m + 1, 0 => ack m 1
| m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
decreasing_by all_goals simp_arith";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, termination, ..
        } => {
            assert_eq!(name, "ack");
            let _tb = termination
                .termination_by
                .as_ref()
                .expect("ack should have termination_by");
            let _db = termination
                .decreasing_by
                .as_ref()
                .expect("ack should have decreasing_by");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_termination_by_not_consumed_as_argument() {
    // Verify termination_by is NOT consumed as a function argument
    // This is the root cause of #1132
    let code = "def f (x : Nat) : Nat := g x
termination_by x";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name,
            val,
            termination,
            ..
        } => {
            assert_eq!(name, "f");
            // val should be `g x`, NOT `g x termination_by x`
            match val.as_ref() {
                SurfaceExpr::App(_, func, args) => {
                    // Should have exactly 1 argument (x), not 3 (x, termination_by, x)
                    assert_eq!(
                        args.len(),
                        1,
                        "termination_by was wrongly consumed as argument"
                    );
                    assert!(matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "g"));
                }
                _ => panic!("Expected App, got {val:?}"),
            }
            let _tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should not be consumed as argument");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_termination_hints_reversed_order() {
    // Test decreasing_by before termination_by (reversed order)
    let code = "def ack (m n : Nat) : Nat := match m, n with
| 0, n => n + 1
| m + 1, 0 => ack m 1
| m + 1, n + 1 => ack m (ack (m + 1) n)
decreasing_by all_goals simp_arith
termination_by m n => (m, n)";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, termination, ..
        } => {
            assert_eq!(name, "ack");
            assert!(
                termination.decreasing_by.is_some(),
                "decreasing_by should be parsed in reversed order"
            );
            assert!(
                termination.termination_by.is_some(),
                "termination_by should be parsed in reversed order"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_termination_by_followed_by_def() {
    // Verify termination_by properly terminates when followed by another definition
    let code = "def foo (n : Nat) : Nat := n
termination_by n

def bar : Nat := 42";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 2);
    match &decls[0] {
        SurfaceDecl::Def {
            name, termination, ..
        } => {
            assert_eq!(name, "foo");
            let _tb = termination
                .termination_by
                .as_ref()
                .expect("foo should have termination_by");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
    match &decls[1] {
        SurfaceDecl::Def { name, .. } => {
            assert_eq!(name, "bar");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_termination_by_structural() {
    // Lean 4.11.0+: termination_by structural <param>
    let code = "def sum (xs : List Nat) : Nat := sum xs
termination_by structural xs";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, termination, ..
        } => {
            assert_eq!(name, "sum");
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should be present");
            assert_eq!(tb.kind, TerminationKind::Structural("xs".to_string()));
            assert!(tb.measure.is_none(), "structural should have no measure");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_termination_by_query() {
    // termination_by? - query mode to show inferred termination
    let code = "def fib (n : Nat) : Nat := fib n
termination_by?";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, termination, ..
        } => {
            assert_eq!(name, "fib");
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by? should be present");
            assert_eq!(tb.kind, TerminationKind::Query);
            assert!(tb.measure.is_none(), "query mode should have no measure");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_termination_by_well_founded_kind() {
    // Verify regular termination_by has WellFounded kind
    let code = "def f (n : Nat) : Nat := n
termination_by n => n";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let tb = termination
                .termination_by
                .as_ref()
                .expect("termination_by should be present");
            assert_eq!(tb.kind, TerminationKind::WellFounded);
            assert!(tb.measure.is_some(), "well-founded should have measure");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_termination_by_structural_without_param() {
    // A structural hint without its required parameter is a recoverable parser
    // error for diagnostic clients, never an empty-name structural hint.
    let code = "def f (x : Nat) : Nat := x
termination_by structural";
    let report = Parser::parse_file_with_diagnostics(code).unwrap();
    assert_eq!(report.decls.len(), 1);
    match &report.decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            assert!(
                termination.termination_by.is_none(),
                "malformed structural hint must be omitted"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
    assert_eq!(report.diagnostics.len(), 1);
    assert_eq!(report.diagnostics[0].code, "parser.recovery");
    assert_eq!(report.diagnostics[0].construct, "termination_by");
    assert!(report.diagnostics[0]
        .message
        .contains("`termination_by structural` requires a parameter name"));
}

#[test]
fn test_parse_legacy_termination_by_underscore_params() {
    // Lean-generated equation compiler output commonly uses anonymous legacy
    // parameters; they are valid binders, not missing syntax.
    let code = "def f (m n : Nat) : Nat := m + n
termination_by _ _ => m + n";
    let decls = Parser::parse_file(code).unwrap();
    match &decls[0] {
        SurfaceDecl::Def { termination, .. } => {
            let hint = termination
                .termination_by
                .as_ref()
                .expect("valid legacy hint should be retained");
            assert_eq!(hint.params, vec!["_", "_"]);
            assert!(hint.measure.is_some());
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

// --- Set/binder operator syntax (Part of #8, #2550) ---

#[test]
fn test_parse_subset_operator() {
    // ⊆ at comparison precedence (infix:50)
    let expr = Parser::parse_expr("A ⊆ B").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "HasSubset.Subset"));
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected App(HasSubset.Subset, ...)"),
    }
}

#[test]
fn test_parse_proper_subset_operator() {
    // ⊂ at comparison precedence (infix:50)
    let expr = Parser::parse_expr("f a ⊂ f b").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "HasSSubset.SSubset"));
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected App(HasSSubset.SSubset, ...)"),
    }
}

#[test]
fn test_parse_union_operator() {
    // ∪ at additive precedence (infixl:65)
    let expr = Parser::parse_expr("A ∪ B").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "Union.union"));
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected App(Union.union, ...)"),
    }
}

#[test]
fn test_parse_inter_operator() {
    // ∩ at multiplicative precedence (infixl:70)
    let expr = Parser::parse_expr("A ∩ B").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "Inter.inter"));
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected App(Inter.inter, ...)"),
    }
}

#[test]
fn test_parse_set_difference_operator() {
    // Lean 4 core notation: infix:70 " \\ " => SDiff.sdiff
    let expr = Parser::parse_expr("T \\ U").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "SDiff.sdiff"));
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected App(SDiff.sdiff, ...)"),
    }
}

#[test]
fn test_parse_set_difference_then_intersection() {
    let expr = Parser::parse_expr("A \\ B ∩ C").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "Inter.inter"));
            assert_eq!(args.len(), 2);
            match &args[0].expr {
                SurfaceExpr::App(_, inner_func, inner_args) => {
                    assert!(
                        matches!(**inner_func, SurfaceExpr::Ident(_, ref s) if s == "SDiff.sdiff")
                    );
                    assert_eq!(inner_args.len(), 2);
                }
                other => panic!("expected nested SDiff.sdiff on the left, got {other:?}"),
            }
        }
        _ => panic!("expected App(Inter.inter, ...)"),
    }
}

#[test]
fn test_parse_empty_set_atom() {
    // ∅ as atom → EmptyCollection.emptyCollection
    let expr = Parser::parse_expr("∅").unwrap();
    assert!(matches!(expr, SurfaceExpr::Ident(_, ref s) if s == "EmptyCollection.emptyCollection"));
}

#[test]
fn test_parse_compose_operator() {
    // ∘ at precedence 90 (infixr)
    let expr = Parser::parse_expr("f ∘ g").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "Function.comp"));
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected App(Function.comp, ...)"),
    }
}

#[test]
fn test_parse_inter_union_precedence() {
    // ∩ binds tighter than ∪: A ∪ B ∩ C = A ∪ (B ∩ C)
    let expr = Parser::parse_expr("A ∪ B ∩ C").unwrap();
    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(*func, SurfaceExpr::Ident(_, ref s) if s == "Union.union"));
            assert_eq!(args.len(), 2);
            // Second arg should be Inter.inter B C
            match &args[1].expr {
                SurfaceExpr::App(_, inner_func, inner_args) => {
                    assert!(
                        matches!(**inner_func, SurfaceExpr::Ident(_, ref s) if s == "Inter.inter")
                    );
                    assert_eq!(inner_args.len(), 2);
                }
                other => panic!("expected nested Inter.inter, got {other:?}"),
            }
        }
        _ => panic!("expected Union.union at top level"),
    }
}

#[test]
fn test_parse_putnam_1962_b2_header() {
    // Real PutnamBench header: ∃ f : ℝ → Set ℕ, ∀ a b : ℝ, a < b → f a ⊂ f b
    let result = Parser::parse_expr("∃ f : ℝ → Set ℕ, ∀ a b : ℝ, a < b → f a ⊂ f b");
    assert!(
        result.is_ok(),
        "should parse PutnamBench 1962_b2-style header: {result:?}"
    );
}

#[test]
fn test_parse_putnam_set_ncard_style() {
    // Pattern from putnam_1962_a1: S.ncard = 5 (dot projection + equality)
    let result = Parser::parse_expr("S.ncard = 5");
    assert!(
        result.is_ok(),
        "should parse dot projection with equality: {result:?}"
    );
}

#[test]
fn test_parse_putnam_convex_hull_set_difference_clause() {
    // Brick 3: this PutnamBench 1962_a1 clause contains a singleton set `{t}`,
    // which now parses (structInst field-abbreviation `{ t := t }`, resolved
    // against the expected type at elaboration) rather than fabricating a `Hole`.
    let expr = Parser::parse_expr("¬∃ t ∈ T, t ∈ convexHull ℝ (T \\ {t})")
        .expect("singleton set `{t}` parses (Brick 3)");
    assert!(
        !format!("{expr:?}").contains("Hole("),
        "must not fabricate a Hole for `{{t}}`, got {expr:?}"
    );
}

#[test]
fn test_parse_putnam_1962_a1_theorem() {
    let code = r"
theorem putnam_1962_a1
(S : Set (ℝ × ℝ))
(hS : S.ncard = 5)
(hnoncol : ∀ s ⊆ S, s.ncard = 3 → ¬Collinear ℝ s)
: ∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T, t ∈ convexHull ℝ (T \ {t}) :=
sorry
";
    let result = Parser::parse_file(code);
    assert!(
        result.is_ok(),
        "should parse PutnamBench 1962_a1 theorem: {result:?}"
    );
}

#[test]
fn test_parse_empty_set_in_expression() {
    // ∅ used in a set equality
    let result = Parser::parse_expr("A ∩ B = ∅");
    assert!(
        result.is_ok(),
        "should parse intersection-equals-empty: {result:?}"
    );
}

/// Render an expr's head-constant spine for compact structural assertions.
fn head_name(e: &SurfaceExpr) -> Option<&str> {
    match e {
        SurfaceExpr::App(_, f, _) => match f.as_ref() {
            SurfaceExpr::Ident(_, n) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

#[test]
fn test_anon_sigma_multi_ident_group_right_nests() {
    // `(a b : Nat) × t` is a bracketedExplicitBinders group in Lean — one
    // nested Sigma per ident, NOT `Prod (a b : Nat) t`.
    let expr =
        Parser::parse_expr("(a b : Nat) × Fin (a + b)").expect("multi-ident anon sigma parses");
    assert_eq!(head_name(&expr), Some("Sigma"), "outer head: {expr:?}");
    // Inner body: Sigma (fun a => Sigma (fun b => ...)).
    let SurfaceExpr::App(_, _, args) = &expr else {
        panic!("expected App, got {expr:?}");
    };
    let SurfaceExpr::Lambda(_, binders, body) = &args[0].expr else {
        panic!("expected outer lambda, got {:?}", args[0].expr);
    };
    assert_eq!(binders[0].name, "a");
    assert_eq!(head_name(body), Some("Sigma"), "inner head: {body:?}");
}

#[test]
fn test_anon_sigma_non_binder_ascription_stays_prod() {
    // `(f 1 : T) × b` — the ascription value is not an ident spine, so this is
    // a plain Prod of an ascription (matches Lean, whose binder-group macro
    // only fires on binderIdent groups).
    let expr = Parser::parse_expr("(f 1 : T) × b").expect("non-binder ascription × parses");
    assert_eq!(head_name(&expr), Some("Prod"), "got {expr:?}");
}

#[test]
fn test_exists_unique_desugar_single_explicit_arg() {
    // Mathlib's `ExistsUnique (p : α → Prop)` takes ONE explicit argument; the
    // binder type rides on the lambda, not as a positional type argument.
    let expr = Parser::parse_expr("∃! x : Nat, x = 1").expect("∃! parses");
    let SurfaceExpr::App(_, f, args) = &expr else {
        panic!("expected App, got {expr:?}");
    };
    assert!(
        matches!(f.as_ref(), SurfaceExpr::Ident(_, n) if n == "ExistsUnique"),
        "head must be ExistsUnique: {expr:?}"
    );
    assert_eq!(args.len(), 1, "one explicit arg (the predicate): {expr:?}");
    let SurfaceExpr::Lambda(_, binders, _) = &args[0].expr else {
        panic!("predicate must be a lambda, got {:?}", args[0].expr);
    };
    assert_eq!(binders[0].name, "x");
    assert!(binders[0].ty.is_some(), "binder keeps its type ascription");
}

#[test]
fn test_parse_bounded_forall_subset() {
    // ∀ s ⊆ S, P s  ≡  ∀ s, s ⊆ S → P s (bounded quantifier with ⊆)
    let result = Parser::parse_expr("∀ s ⊆ S, P s");
    assert!(
        result.is_ok(),
        "should parse bounded forall with subset: {result:?}"
    );
}

#[test]
fn test_parse_bounded_exists_subset() {
    // ∃ T ⊆ S, P T  ≡  ∃ T, T ⊆ S ∧ P T (bounded existential with ⊆)
    let result = Parser::parse_expr("∃ T ⊆ S, P T");
    assert!(
        result.is_ok(),
        "should parse bounded exists with subset: {result:?}"
    );
}

#[test]
fn test_parse_bounded_forall_proper_subset() {
    // ∀ s ⊂ S, P s  ≡  ∀ s, s ⊂ S → P s (bounded quantifier with ⊂)
    let result = Parser::parse_expr("∀ s ⊂ S, P s");
    assert!(
        result.is_ok(),
        "should parse bounded forall with proper subset: {result:?}"
    );
}

#[test]
fn test_parse_bigop_sum_in() {
    // ∑ k in S, f k → Finset.sum S (fun k => f k)
    let result = Parser::parse_expr("∑ k in S, f k");
    assert!(result.is_ok(), "should parse big sum with in: {result:?}");
}

#[test]
fn test_parse_bigop_sum_elem() {
    // ∑ k ∈ S, f k → Finset.sum S (fun k => f k)
    let result = Parser::parse_expr("∑ k ∈ S, f k");
    assert!(result.is_ok(), "should parse big sum with elem: {result:?}");
}

#[test]
fn test_parse_bigop_sum_typed() {
    // ∑ n : ℕ, f n → tsum (fun (n : Nat) => f n)
    let result = Parser::parse_expr("∑ n : T, f n");
    assert!(
        result.is_ok(),
        "should parse big sum with typed binder: {result:?}"
    );
}

#[test]
fn test_parse_bigop_prod_in() {
    // ∏ i ∈ Finset.range n, f i
    let result = Parser::parse_expr("∏ i ∈ S, f i");
    assert!(
        result.is_ok(),
        "should parse big prod with elem: {result:?}"
    );
}

#[test]
fn test_parse_bigop_integral_range() {
    // ∫ x in a..b, f x
    let result = Parser::parse_expr("∫ x in a..b, f x");
    assert!(
        result.is_ok(),
        "should parse integral with range: {result:?}"
    );
}

#[test]
fn test_parse_bigop_tsum_primed() {
    // ∑' n : T, f n (tsum, primed variant)
    let result = Parser::parse_expr("∑' n : T, f n");
    assert!(
        result.is_ok(),
        "should parse tsum with primed operator: {result:?}"
    );
}

#[test]
fn test_parse_bigop_union() {
    // ⋃ p ∈ A, f p
    let result = Parser::parse_expr("⋃ p ∈ A, f p");
    assert!(
        result.is_ok(),
        "should parse big union with elem: {result:?}"
    );
}

#[test]
fn test_parse_range_operator() {
    // a..b → Set.Icc a b
    let result = Parser::parse_expr("a..b");
    assert!(result.is_ok(), "should parse range: {result:?}");
}

// ── Let-destructuring and tuple/angle-bracket binder tests ───────────

#[test]
fn test_parse_let_tuple_destructure() {
    // let (a, b) := e; a + b
    let result = Parser::parse_expr("let (a, b) := pair; a + b");
    assert!(
        result.is_ok(),
        "should parse let tuple destructuring: {result:?}"
    );
}

#[test]
fn test_parse_let_triple_destructure() {
    // let (a, b, c) := e; a + b + c
    let result = Parser::parse_expr("let (a, b, c) := triple; a");
    assert!(
        result.is_ok(),
        "should parse let triple destructuring: {result:?}"
    );
}

#[test]
fn test_parse_let_angle_bracket_destructure() {
    // let ⟨a, b⟩ := e; a + b
    let result = Parser::parse_expr("let ⟨a, b⟩ := pair; a + b");
    assert!(
        result.is_ok(),
        "should parse let angle-bracket destructuring: {result:?}"
    );
}

#[test]
fn test_parse_slice_indexing_desugars_to_to_subarray() {
    // `xs[1:3]` ⇒ `Array.toSubarray xs 1 3` (previously a hard parse error).
    let result = Parser::parse_expr("xs[1:3]").expect("slice xs[1:3] should parse");
    match result {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(&*func, SurfaceExpr::Ident(_, n) if n.as_str() == "Array.toSubarray"),
                "slice head should be Array.toSubarray, got {func:?}"
            );
            assert_eq!(args.len(), 3, "xs[1:3] ⇒ toSubarray xs 1 3 (3 args)");
        }
        other => panic!("expected App(Array.toSubarray, ..), got {other:?}"),
    }
    // `xs[1:]` ⇒ `Array.toSubarray xs 1` (stop defaults to `as.size`).
    let open = Parser::parse_expr("xs[1:]").expect("open slice xs[1:] should parse");
    match open {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(&*func, SurfaceExpr::Ident(_, n) if n.as_str() == "Array.toSubarray"),
                "open-slice head should be Array.toSubarray, got {func:?}"
            );
            assert_eq!(args.len(), 2, "xs[1:] ⇒ toSubarray xs 1 (2 args)");
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_parse_comma_separated_universe_application() {
    // `id.{u, v}` — Lean's canonical comma-separated universe application (was a
    // hard parse error "expected level expression, got Comma").
    let comma = Parser::parse_expr("id.{u, v}").expect("comma universe app should parse");
    match comma {
        SurfaceExpr::UniverseInst(_, _, levels) => {
            assert_eq!(levels.len(), 2, "id.{{u, v}} has 2 levels");
        }
        other => panic!("expected UniverseInst, got {other:?}"),
    }
    // The space-separated form still works (comma is optional).
    let space = Parser::parse_expr("id.{u v}").expect("space universe app should still parse");
    match space {
        SurfaceExpr::UniverseInst(_, _, levels) => assert_eq!(levels.len(), 2),
        other => panic!("expected UniverseInst, got {other:?}"),
    }
}

#[test]
fn test_parse_fun_tuple_binder() {
    // fun (a, b) => a + b
    let result = Parser::parse_expr("fun (a, b) => a + b");
    assert!(
        result.is_ok(),
        "should parse fun with tuple binder: {result:?}"
    );
}

#[test]
fn test_parse_fun_angle_bracket_binder() {
    // fun ⟨a, b⟩ => a + b
    let result = Parser::parse_expr("fun ⟨a, b⟩ => a + b");
    assert!(
        result.is_ok(),
        "should parse fun with angle-bracket binder: {result:?}"
    );
}

#[test]
fn test_parse_bounded_binder_elem() {
    // fun (x ∈ S) => x
    let result = Parser::parse_expr("fun (x ∈ S) => x");
    assert!(
        result.is_ok(),
        "should parse bounded binder with elem: {result:?}"
    );
}

#[test]
fn test_parse_bounded_binder_gt() {
    // fun (x > 0) => x
    let result = Parser::parse_expr("fun (x > 0) => x");
    assert!(
        result.is_ok(),
        "should parse bounded binder with gt: {result:?}"
    );
}

#[test]
fn test_parse_bigop_angle_bracket_binder() {
    // ∑ ⟨i, j⟩ : T, f i j
    let result = Parser::parse_expr("∑ ⟨i, j⟩ : T, f i j");
    assert!(
        result.is_ok(),
        "should parse big sum with angle-bracket binder: {result:?}"
    );
}

#[test]
fn test_parse_bigop_prod_nested_in_forall_binder() {
    // Regression test for #2549: ∏ i ∈ Finset.Icc 1 n, body inside a
    // forall-bounded hypothesis previously failed with "expected RParen, got Comma".
    let result =
        Parser::parse_expr("∀ n > 0, f n = fun x : ℝ => ∏ i ∈ Finset.Icc 1 n, Real.cos (i * x)");
    assert!(
        result.is_ok(),
        "should parse ∏ with ∈ domain inside forall binder: {result:?}"
    );
}

// --- Nesting depth limit tests (#2556) ---

#[test]
fn test_deeply_nested_brackets_returns_error_not_stack_overflow() {
    // 300 levels of nested brackets exceeds MAX_EXPR_DEPTH.
    // Before #2556 fix, this would stack overflow and abort the process.
    // NOTE: With MAX_EXPR_DEPTH=256, this still overflows in debug mode (#2961).
    // Fix: lower MAX_EXPR_DEPTH to 128.
    let input = "[".repeat(300);
    let result = Parser::parse_expr(&input);
    assert!(
        result.is_err(),
        "deeply nested brackets should return an error"
    );
    let err = result.unwrap_err();
    assert!(
        matches!(err, ParseError::NestingTooDeep { .. }),
        "should be NestingTooDeep error, got: {err:?}"
    );
}

#[test]
fn test_deeply_nested_parens_returns_error_not_stack_overflow() {
    // 300 levels of nested parens exceeds MAX_EXPR_DEPTH.
    // NOTE: With MAX_EXPR_DEPTH=256, this still overflows in debug mode (#2961).
    let open = "(".repeat(300);
    let close = ")".repeat(300);
    let input = format!("{open}x{close}");
    let result = Parser::parse_expr(&input);
    assert!(
        result.is_err(),
        "deeply nested parens should return an error"
    );
    let err = result.unwrap_err();
    assert!(
        matches!(err, ParseError::NestingTooDeep { .. }),
        "should be NestingTooDeep error, got: {err:?}"
    );
}

#[test]
fn test_moderate_nesting_still_parses() {
    // 20 levels of nesting should be fine (well under MAX_EXPR_DEPTH limit).
    let open = "(".repeat(20);
    let close = ")".repeat(20);
    let input = format!("{open}x{close}");
    let result = Parser::parse_expr(&input);
    assert!(result.is_ok(), "20-level nesting should parse: {result:?}");
}

#[test]
fn test_lean4_1760_bracket_nesting_parses() {
    // The Lean 4 test 1760.lean has 24 levels of nesting.
    // This should now return a parse error (not a stack overflow).
    let brackets = "[".repeat(24);
    let result = Parser::parse_expr(&brackets);
    // 24 unclosed brackets: may be a parse error but must not stack overflow.
    // The important thing is that we get a Result, not a process abort.
    assert!(result.is_err() || result.is_ok(), "must not abort");
}

#[test]
fn test_lean4_1760_paren_nesting_parses() {
    // 24 levels of balanced parens from 1760.lean — should parse fine.
    let open = "(".repeat(24);
    let close = ")".repeat(24);
    let input = format!("{open}x{close}");
    let result = Parser::parse_expr(&input);
    assert!(
        result.is_ok(),
        "24-level balanced parens should parse: {result:?}"
    );
}

// --- Where local definitions in def/theorem bodies ---

#[test]
fn test_parse_where_local_defs_single() {
    // def foo : Nat := helper 42 where helper (n : Nat) : Nat := n + 1
    let code = "def foo : Nat := helper 42\nwhere\n  helper (n : Nat) : Nat := n + 1";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, where_decls, ..
        } => {
            assert_eq!(name, "foo");
            assert_eq!(where_decls.len(), 1, "should have 1 where local def");
            assert_eq!(where_decls[0].name, "helper");
            assert_eq!(where_decls[0].binders.len(), 1, "helper has 1 binder");
            assert!(
                where_decls[0].ret_ty.is_some(),
                "helper has a return type annotation"
            );
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_where_local_defs_multiple() {
    // def foo : Nat := x + y where x := 1 ; y := 2
    let code = "def foo : Nat := x + y\nwhere\n  x := 1\n  y := 2";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, where_decls, ..
        } => {
            assert_eq!(name, "foo");
            assert_eq!(where_decls.len(), 2, "should have 2 where local defs");
            assert_eq!(where_decls[0].name, "x");
            assert_eq!(where_decls[1].name, "y");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_where_local_defs_no_where() {
    // def bar : Nat := 42
    let code = "def bar : Nat := 42";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, where_decls, ..
        } => {
            assert_eq!(name, "bar");
            assert!(where_decls.is_empty(), "no where clause means empty vec");
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_theorem_where_local_defs() {
    let code = "theorem foo : True := helper\nwhere\n  helper := trivial";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Theorem {
            name, where_decls, ..
        } => {
            assert_eq!(name, "foo");
            assert_eq!(where_decls.len(), 1, "should have 1 where local def");
            assert_eq!(where_decls[0].name, "helper");
            assert!(where_decls[0].binders.is_empty(), "helper has no params");
        }
        other => panic!("Expected Theorem, got {other:?}"),
    }
}

// ============================================================================
// set_option parsing tests
// ============================================================================

/// File-scope `set_option` produces separate declarations.
#[test]
fn test_parse_set_option_file_scope() {
    let decls =
        Parser::parse_file("set_option maxHeartbeats 400000\ndef foo : Nat := 0\n").unwrap();
    assert_eq!(decls.len(), 2, "file-scope: expected 2 decls");
    match &decls[0] {
        SurfaceDecl::SetOption {
            name, value, body, ..
        } => {
            assert_eq!(name, "maxHeartbeats");
            assert_eq!(value.as_deref(), Some("400000"));
            assert!(body.is_none(), "file-scope should have no body");
        }
        other => panic!("expected SetOption, got {other:?}"),
    }
}

/// Per-declaration `set_option ... in <decl>` wraps the inner declaration.
#[test]
fn test_parse_set_option_in_decl() {
    let decls =
        Parser::parse_file("set_option maxHeartbeats 400000 in\ndef bar : Nat := 0\n").unwrap();
    assert_eq!(decls.len(), 1, "per-decl: expected 1 decl (wrapped)");
    match &decls[0] {
        SurfaceDecl::SetOption {
            name, value, body, ..
        } => {
            assert_eq!(name, "maxHeartbeats");
            assert_eq!(value.as_deref(), Some("400000"));
            assert!(body.is_some(), "per-decl should have a body");
            // Inner declaration should be a Def
            assert!(matches!(body.as_deref(), Some(SurfaceDecl::Def { .. })));
        }
        other => panic!("expected SetOption with body, got {other:?}"),
    }
}

/// Boolean option with `in` form (no value, just `set_option pp.all in def ...`).
#[test]
fn test_parse_set_option_bool_in_decl() {
    let decls = Parser::parse_file("set_option pp.all in\ndef baz : Nat := 0\n").unwrap();
    assert_eq!(decls.len(), 1, "bool per-decl: expected 1 decl");
    match &decls[0] {
        SurfaceDecl::SetOption {
            name, value, body, ..
        } => {
            assert_eq!(name, "pp.all");
            assert!(value.is_none(), "boolean toggle has no value");
            assert!(body.is_some(), "per-decl should have a body");
        }
        other => panic!("expected SetOption, got {other:?}"),
    }
}

/// `set_option ... in` followed by more declarations: only the first
/// declaration after `in` is wrapped; subsequent ones are independent.
#[test]
fn test_parse_set_option_in_does_not_capture_subsequent() {
    let code = "set_option maxHeartbeats 1 in\ndef a : Nat := 0\ndef b : Nat := 1\n";
    let decls = Parser::parse_file(code).unwrap();
    assert_eq!(decls.len(), 2, "expected 2 decls: scoped + independent");
    assert!(matches!(
        &decls[0],
        SurfaceDecl::SetOption { body: Some(_), .. }
    ));
    assert!(matches!(&decls[1], SurfaceDecl::Def { .. }));
}

// =============================================================================
// Float and Char literals (surface-level parsing)
// =============================================================================

#[test]
fn test_parse_float_simple_produces_float_lit() {
    let expr = Parser::parse_expr("3.5").expect("should parse float literal");
    match expr {
        SurfaceExpr::Lit(_, SurfaceLit::Float(value)) => {
            assert_eq!(value, "3.5", "exact source text is preserved");
        }
        other => panic!("expected Float literal, got {other:?}"),
    }
}

#[test]
fn test_parse_float_with_exponent_produces_float_lit() {
    let expr = Parser::parse_expr("2.5E10").expect("should parse float with exponent");
    match expr {
        SurfaceExpr::Lit(_, SurfaceLit::Float(value)) => {
            assert_eq!(value, "2.5E10", "exponent case is preserved verbatim");
        }
        other => panic!("expected Float literal, got {other:?}"),
    }
}

#[test]
fn test_parse_float_negative_exponent_produces_float_lit() {
    let expr = Parser::parse_expr("1e-5").expect("should parse negative-exponent float");
    match expr {
        SurfaceExpr::Lit(_, SurfaceLit::Float(value)) => {
            assert_eq!(value, "1e-5", "exact source text is preserved");
        }
        other => panic!("expected Float literal, got {other:?}"),
    }
}

#[test]
fn test_parse_range_does_not_produce_float() {
    // `1..2` must NOT become a float; the inner `1` is still a Nat literal.
    let expr = Parser::parse_expr("1..2").expect("should parse range expression");
    let contains_float = format!("{expr:?}").contains("Float");
    assert!(
        !contains_float,
        "range parsed with a Float literal: {expr:?}"
    );
}

#[test]
fn test_parse_integer_projection_is_proj_not_float() {
    // `x.field` projection is unaffected; digit-dot-ident likewise stays a
    // projection over the integer, never a float.
    let expr = Parser::parse_expr("x.field").expect("should parse named projection");
    match expr {
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            assert!(matches!(base.as_ref(), SurfaceExpr::Ident(_, n) if n == "x"));
            assert_eq!(field, "field");
        }
        other => panic!("expected projection, got {other:?}"),
    }
}

#[test]
fn test_parse_hex_stays_nat_lit() {
    // Hex literals must never be reinterpreted as floats.
    let expr = Parser::parse_expr("0xFF").expect("should parse hex literal");
    assert!(matches!(expr, SurfaceExpr::Lit(_, SurfaceLit::Nat(255))));
}

#[test]
fn test_parse_char_simple_produces_char_lit() {
    let expr = Parser::parse_expr("'a'").expect("should parse char literal");
    assert!(matches!(expr, SurfaceExpr::Lit(_, SurfaceLit::Char('a'))));
}

#[test]
fn test_parse_char_escape_produces_char_lit() {
    let expr = Parser::parse_expr(r"'\n'").expect("should parse escaped char literal");
    assert!(matches!(expr, SurfaceExpr::Lit(_, SurfaceLit::Char('\n'))));
}

#[test]
fn test_parse_char_unicode_escape_produces_char_lit() {
    let expr = Parser::parse_expr(r"'\u{41}'").expect("should parse unicode escape char");
    assert!(matches!(expr, SurfaceExpr::Lit(_, SurfaceLit::Char('A'))));
}

#[test]
fn test_parse_unterminated_char_errors() {
    // An unterminated char literal must surface a parse error, not panic.
    let result = Parser::parse_expr("'a");
    assert!(result.is_err(), "unterminated char should fail to parse");
}

#[test]
fn test_parse_string_gap_produces_joined_string_lit() {
    // A Lean 4 string gap (`\` + newline + indentation) lets a string literal
    // span source lines; the gap is elided so the surface literal is joined.
    let expr = Parser::parse_expr("\"hello \\\n    world\"").expect("should parse string with gap");
    assert!(matches!(
        expr,
        SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "hello world"
    ));
}

#[test]
fn test_parse_string_gap_without_newline_errors() {
    // A backslash followed by whitespace that never reaches a newline before a
    // non-whitespace character is a malformed gap and must fail to parse.
    let result = Parser::parse_expr("\"hello \\ world\"");
    assert!(result.is_err(), "string gap without newline should fail");
}

// ── Type-aware bracket matching in fun-binder destructuring detection ──
//
// Regression tests for the latent bracket-matching bug in
// `paren_group_has_top_level_comma` / `skip_balanced_group`. The original
// single-depth-counter logic incremented on any opener and decremented on
// any closer, ignoring bracket *type*. Two failure modes:
//   1. `{`/`}` were not counted at all, so a comma inside a brace subterm of
//      a typed binder's type (e.g. `Foo {a, b}`) was mistaken for a
//      paren-level tuple separator, wrongly routing the binder into the
//      destructuring path.
//   2. A closer of the wrong type (e.g. a `⟩` `RAngle` from an anonymous
//      constructor) could spuriously balance a paren group.
// The fix tracks a type-aware stack so an opener of type T is only balanced
// by a closer of type T.

#[test]
fn test_parse_lambda_typed_binder_with_brace_subterm_stays_plain_lambda() {
    // `fun (x : Foo {a := 1, b := 2}) => x` is a *typed* binder whose type
    // applies `Foo` to a structure literal `{a := 1, b := 2}`. The comma lives
    // inside the braces, not at the paren level, so this is NOT a tuple
    // destructuring. With the old type-blind counter the brace comma was seen
    // as a paren-level tuple separator and the parse failed ("expected RParen,
    // got Colon"). (A struct literal is used rather than a finite set `{a, b}`
    // because Brick 1 rejects finite-set braces loudly; the internal comma —
    // the actual regression subject — is preserved.)
    let expr = Parser::parse_expr("fun (x : Foo {a := 1, b := 2}) => x")
        .expect("typed binder with brace subterm parses");
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1, "arity 1: a single typed binder");
            assert_eq!(binders[0].name, "x");
            assert!(binders[0].ty.is_some(), "binder keeps its type annotation");
        }
        other => panic!("expected plain Lambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_typed_brace_binder_then_plain_binder_keeps_arity() {
    // `fun (x : F {a := 1, b := 2}) y => x` — a typed brace binder followed by
    // a plain binder. The brace comma must not derail the scan that finds the
    // second binder `y`; arity must be 2. (Struct literal rather than finite
    // set `{a, b}` — Brick 1 rejects finite-set braces loudly — while keeping
    // the internal-comma regression subject.)
    let expr = Parser::parse_expr("fun (x : F {a := 1, b := 2}) y => x")
        .expect("typed brace binder followed by plain binder parses");
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 2);
            assert_eq!(binders[0].name, "x");
            assert_eq!(binders[1].name, "y");
        }
        other => panic!("expected plain Lambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_tuple_with_bracket_element_destructures() {
    // `fun (a, [b, c]) => a` — a genuine paren-level tuple whose second
    // element is a list literal. The top-level comma must still be detected
    // (arity 1 pattern-match lambda) with the bracket nesting tracked.
    let expr =
        Parser::parse_expr("fun (a, [b, c]) => a").expect("tuple with bracket element parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, _) => {
            assert_eq!(binders.len(), 1, "single pattern-matched tuple param");
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_tuple_with_leading_bracket_element_destructures() {
    // `fun ([b, c], a) => a` — list literal as the *first* tuple element,
    // exercising the closer-popping order before the top-level comma.
    let expr = Parser::parse_expr("fun ([b, c], a) => a")
        .expect("tuple with leading bracket element parses");
    assert!(
        matches!(expr, SurfaceExpr::PatternMatchLambda(_, ref b, _) if b.len() == 1),
        "leading-bracket tuple is a single pattern-matched param"
    );
}

#[test]
fn test_parse_lambda_tuple_with_angle_element_destructures() {
    // `fun (a, ⟨b, c⟩) => a` — anonymous-constructor `⟨..⟩` nested inside a
    // paren tuple. Angle brackets are a distinct bracket type and must be
    // matched only by `⟩`.
    let expr = Parser::parse_expr("fun (a, ⟨b, c⟩) => a")
        .expect("tuple with angle-bracket element parses");
    assert!(
        matches!(expr, SurfaceExpr::PatternMatchLambda(_, ref b, _) if b.len() == 1),
        "tuple with angle element is a single pattern-matched param"
    );
}

#[test]
fn test_parse_lambda_nested_paren_tuple_destructures() {
    // `fun ((a, b), c) => a` — nested paren tuple as the first element. The
    // inner comma is at depth 2 and must be ignored; only the outer comma
    // (depth 1) is the top-level separator.
    let expr = Parser::parse_expr("fun ((a, b), c) => a").expect("nested paren tuple parses");
    assert!(
        matches!(expr, SurfaceExpr::PatternMatchLambda(_, ref b, _) if b.len() == 1),
        "nested paren tuple is a single pattern-matched param"
    );
}

#[test]
fn test_parse_lambda_paren_binder_then_angle_binder_keeps_arity() {
    // `fun (a, b) ⟨c, d⟩ => a` — a paren tuple followed by an angle tuple:
    // two destructuring params, arity 2. Exercises `skip_balanced_group`
    // across two distinct bracket types in sequence.
    let expr =
        Parser::parse_expr("fun (a, b) ⟨c, d⟩ => a").expect("paren tuple then angle tuple parses");
    match expr {
        SurfaceExpr::PatternMatchLambda(_, binders, _) => {
            assert_eq!(binders.len(), 2, "two destructuring params");
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_plain_typed_binder_no_brace_stays_lambda() {
    // Near-miss control: the same shape *without* a brace subterm
    // (`fun (x : Foo a) => x`) is a plain typed binder and always parsed —
    // confirming the brace subterm is the discriminating factor.
    let expr = Parser::parse_expr("fun (x : Foo a) => x").expect("plain typed binder parses");
    assert!(
        matches!(expr, SurfaceExpr::Lambda(_, ref b, _) if b.len() == 1 && b[0].ty.is_some()),
        "plain typed binder is arity-1 Lambda with a type"
    );
}

#[test]
fn test_parse_lambda_typed_binder_with_forall_comma_stays_plain_lambda() {
    // `fun (ih : forall (c : Nat), P c) => ih` — the binder's *type* is a
    // `forall` whose quantifier comma sits at the binder's paren depth. The
    // depth-1 binder colon precedes that comma, so this is an ordinary typed
    // binder, not a tuple. With the old type-blind scan the forall comma was
    // mistaken for a tuple separator and the parse failed ("expected RParen,
    // got Colon"). This is the exact shape that produced the clean-verify
    // `spec::core_spec` cascade (nat_sub_zero_implies_sub_succ_zero value).
    let expr = Parser::parse_expr("fun (ih : forall (c : Nat), P c) => ih")
        .expect("typed binder whose type is a forall parses");
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1, "single typed binder, not a tuple");
            assert_eq!(binders[0].name, "ih");
            assert!(binders[0].ty.is_some(), "binder keeps its forall type");
        }
        other => panic!("expected plain Lambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_plain_then_forall_typed_binder_keeps_arity() {
    // `fun (j : Nat) (ih : forall (c : Nat), P c) => j` — a plain binder
    // followed by a forall-typed binder. The forall comma must not be read as
    // a tuple separator that would split the binder list; arity stays 2.
    let expr = Parser::parse_expr("fun (j : Nat) (ih : forall (c : Nat), P c) => j")
        .expect("plain binder then forall-typed binder parses");
    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 2);
            assert_eq!(binders[0].name, "j");
            assert_eq!(binders[1].name, "ih");
        }
        other => panic!("expected plain Lambda, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_tuple_binder_with_no_colon_still_destructures() {
    // Guard against over-correction: a genuine tuple `(a, b)` has no depth-1
    // colon, so it must still be detected as a destructuring binder.
    let expr = Parser::parse_expr("fun (a, b) => a").expect("plain tuple binder parses");
    assert!(
        matches!(expr, SurfaceExpr::PatternMatchLambda(_, ref b, _) if b.len() == 1),
        "comma with no preceding colon is a tuple separator"
    );
}

#[test]
fn test_parse_lambda_nat_sub_witness_value_shape_parses() {
    // The exact value-term shape from clean-verify's
    // `nat_sub_zero_implies_sub_succ_zero` definition: nested `fun` binders
    // whose types are `forall`s with top-level commas. This term is the head
    // of the ~189-failure `spec::core_spec` cascade caused by the
    // bracket-matching bug.
    let src = concat!(
        "fun (c : Nat) (i : Nat) (h : Eq Nat (Nat.sub c i) Nat.zero) => ",
        "(Nat.rec (fun (j : Nat) => forall (c : Nat), ",
        "Eq Nat (Nat.sub c j) Nat.zero -> Eq Nat (Nat.sub c (Nat.succ j)) Nat.zero) ",
        "(fun (j : Nat) (ih : forall (c : Nat), ",
        "Eq Nat (Nat.sub c j) Nat.zero -> Eq Nat (Nat.sub c (Nat.succ j)) Nat.zero) => j) ",
        "i) c h"
    );
    let expr = Parser::parse_expr(src).expect("nat-sub witness value term parses");
    assert!(
        matches!(expr, SurfaceExpr::App(..) | SurfaceExpr::Lambda(..)),
        "value term elaborates to an application/lambda head"
    );
}

// ============================================================================
// Declaration doc comment capture (`/-- ... -/`)
// ============================================================================

#[test]
fn test_doc_comment_associates_with_following_def() {
    let (decls, docs) =
        Parser::parse_file_with_docs("/-- The identity. -/\ndef f := 1").expect("parses");
    // The token stream / decls are unchanged from `parse_file`.
    assert_eq!(decls.len(), 1);
    let def_span = match &decls[0] {
        SurfaceDecl::Def { span, name, .. } => {
            assert_eq!(name, "f");
            *span
        }
        other => panic!("expected def, got {other:?}"),
    };
    assert_eq!(docs.len(), 1, "expected one associated doc");
    assert_eq!(docs[0].text, "The identity.");
    // The returned doc carries the *declaration's* span, not the comment's.
    assert_eq!(docs[0].span, def_span);
}

#[test]
fn test_doc_comment_associates_with_following_theorem() {
    let (decls, docs) =
        Parser::parse_file_with_docs("/-- Reflexivity holds. -/\ntheorem t : a = a := rfl")
            .expect("parses");
    let thm_span = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Theorem { span, name, .. } if name == "t" => Some(*span),
            _ => None,
        })
        .expect("theorem t present");
    assert_eq!(docs.len(), 1);
    assert_eq!(docs[0].text, "Reflexivity holds.");
    assert_eq!(docs[0].span, thm_span);
}

#[test]
fn test_doc_comment_associates_with_following_inductive() {
    let (decls, docs) =
        Parser::parse_file_with_docs("/-- A simple enum. -/\ninductive Color\n| red\n| green")
            .expect("parses");
    let ind_span = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Inductive { span, name, .. } if name == "Color" => Some(*span),
            _ => None,
        })
        .expect("inductive Color present");
    assert_eq!(docs.len(), 1);
    assert_eq!(docs[0].text, "A simple enum.");
    assert_eq!(docs[0].span, ind_span);
}

#[test]
fn test_ordinary_block_comment_not_captured_by_parser() {
    let (decls, docs) =
        Parser::parse_file_with_docs("/- ordinary comment -/\ndef f := 1").expect("parses");
    assert_eq!(decls.len(), 1);
    assert!(docs.is_empty(), "ordinary block comment is not a doc");
}

#[test]
fn test_decl_without_doc_has_no_doc() {
    let (decls, docs) = Parser::parse_file_with_docs("def f := 1").expect("parses");
    assert_eq!(decls.len(), 1);
    assert!(docs.is_empty(), "decl with no doc comment yields none");
}

#[test]
fn test_doc_comments_associate_to_respective_decls() {
    // Two docs, each preceding its own decl, associate independently.
    let src = "/-- first -/\ndef a := 1\n/-- second -/\ndef b := 2";
    let (decls, docs) = Parser::parse_file_with_docs(src).expect("parses");
    assert_eq!(docs.len(), 2);
    assert_eq!(docs[0].text, "first");
    assert_eq!(docs[1].text, "second");
    // First doc -> def a, second doc -> def b.
    let a_span = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Def { span, name, .. } if name == "a" => Some(*span),
            _ => None,
        })
        .expect("def a present");
    let b_span = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Def { span, name, .. } if name == "b" => Some(*span),
            _ => None,
        })
        .expect("def b present");
    assert_eq!(docs[0].span, a_span);
    assert_eq!(docs[1].span, b_span);
}

#[test]
fn test_repeated_doc_comments_last_one_wins() {
    // When several doc comments precede the same declaration, the last wins
    // (matching Lean).
    let src = "/-- first -/\n/-- second -/\ndef f := 1";
    let (decls, docs) = Parser::parse_file_with_docs(src).expect("parses");
    assert_eq!(decls.len(), 1);
    assert_eq!(docs.len(), 1, "the two docs collapse onto one decl");
    assert_eq!(docs[0].text, "second");
}

#[test]
fn test_trailing_doc_comment_with_no_decl_is_dropped() {
    let (decls, docs) =
        Parser::parse_file_with_docs("def f := 1\n/-- trailing doc -/").expect("parses");
    assert_eq!(decls.len(), 1);
    assert!(docs.is_empty(), "doc with no following decl is dropped");
}

#[test]
fn test_parse_functor_map_operator() {
    // `f <$> x` (Functor.map, infixr:100). The `<$>` token was lexed but had no
    // grammar handling, so it tripped decl-level recovery ("raw declaration") —
    // the `decode` shape in trust-ir's Semantics/VectorDialect.lean
    // (`VectorSpec.packLanes <$> decodePackLanes inst`). It now desugars to
    // `Functor.map f x`, binding looser than application so each side groups.
    let expr = Parser::parse_expr("f <$> g x").expect("<$> parses");
    match expr {
        SurfaceExpr::App(_, head, args) => {
            assert!(
                matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if n == "Functor.map"),
                "head is Functor.map, got {head:?}"
            );
            assert_eq!(args.len(), 2, "Functor.map f (g x) — two args");
        }
        other => panic!("expected App(Functor.map, …), got {other:?}"),
    }
}

// Regression: a contextual command keyword (`alias`, `library_note`, …) lexed
// as a soft `Ident` must terminate a preceding declaration-value expression.
// Before the `is_boundary_command_keyword` guard in `is_atom_start_at`, the
// value parser of `def base : Nat := 0` greedily consumed the following
// `alias plainAlias` as application arguments (`0 alias plainAlias`), so the
// `alias` line collapsed into an error-recovery raw declaration and every
// downstream reference to the alias-defined name became an unknown identifier.
// This mirrors the Mathlib/Logic/Basic `alias em := Classical.em` cascade.
#[test]
fn test_alias_after_def_value_is_not_swallowed() {
    let decls = Parser::parse_file("def base : Nat := 0\nalias plainAlias := base")
        .expect("def followed by alias parses");
    assert_eq!(
        decls.len(),
        2,
        "two decls: the def and the alias, got {decls:?}"
    );
    assert!(
        matches!(&decls[0], SurfaceDecl::Def { name, .. } if name == "base"),
        "first decl is `def base`, got {:?}",
        decls[0]
    );
    // The alias desugars to a real `def` named `plainAlias` — NOT a mashed
    // RawDecl error-recovery node.
    assert!(
        matches!(&decls[1], SurfaceDecl::Def { name, .. } if name == "plainAlias"),
        "second decl is the desugared `def plainAlias`, got {:?}",
        decls[1]
    );
    assert!(
        !matches!(&decls[1], SurfaceDecl::RawDecl { .. }),
        "the alias must not collapse to an error-recovery RawDecl"
    );
}

#[test]
fn test_consecutive_aliases_parse_separately() {
    let decls = Parser::parse_file(
        "def base : Nat := 0\nalias firstA := base\nalias secondA := base\ndef after : Nat := 1",
    )
    .expect("consecutive aliases parse");
    assert_eq!(decls.len(), 4, "def + 2 aliases + def, got {decls:?}");
    let names: Vec<&str> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Def { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(
        names,
        vec!["base", "firstA", "secondA", "after"],
        "each alias registers its own def and the trailing def survives"
    );
}

// Regression: a cdot `·` section placeholder inside a PARENTHESIZED TYPE
// ASCRIPTION `(· < · : T)` must still desugar to an anonymous lambda. Before the
// fix, the ascription branch of paren-parsing built `Ascription(· < ·, T)`
// WITHOUT running `cdot::desugar` (the plain-paren branch did), so the `·`
// placeholders leaked as unknown identifiers. Mathlib writes this constantly:
// `swap (· < · : α → α → _)`, `Injective (g ∘ · : …)`.
#[test]
fn test_cdot_section_inside_type_ascription_desugars() {
    // `(· < · : Nat → Nat → Prop)` parses to `Ascription(Lambda([x,y], x < y), T)`
    // — NOT a bare `·` that would leak.
    let expr =
        Parser::parse_expr("(· < · : Nat -> Nat -> Prop)").expect("ascribed cdot section parses");
    let inner = match &expr {
        SurfaceExpr::Paren(_, inner) => inner.as_ref(),
        other => other,
    };
    match inner {
        SurfaceExpr::Ascription(_, value, _) => {
            assert!(
                matches!(value.as_ref(), SurfaceExpr::Lambda(_, binders, _) if binders.len() == 2),
                "ascription value must be a 2-binder cdot lambda, got {value:?}"
            );
        }
        other => panic!("expected Ascription(Lambda, T), got {other:?}"),
    }
}

#[test]
fn test_plain_ascription_without_cdot_unchanged() {
    // No `·` → the ascription value is unchanged (the desugar is a no-op).
    let expr = Parser::parse_expr("(x : Nat)").expect("plain ascription parses");
    let inner = match &expr {
        SurfaceExpr::Paren(_, inner) => inner.as_ref(),
        other => other,
    };
    assert!(
        matches!(inner, SurfaceExpr::Ascription(_, v, _) if matches!(v.as_ref(), SurfaceExpr::Ident(_, n) if n == "x")),
        "plain `(x : Nat)` must stay `Ascription(Ident x, Nat)`, got {inner:?}"
    );
}

// Regression: the setoid/quotient equivalence operator `≈` (U+2248,
// HasEquiv.Equiv) — distinct from `≃` (U+2243, Equiv/iso) — must parse as an
// `infix:50` binary op `a ≈ b → HasEquiv.Equiv a b`. Before this it was not
// lexed, so `a ≈ b` broke the parse (`error-recovery`) — 4 decls on
// Mathlib/Data/Subtype (`Subtype.refl/symm/trans`, `equiv_iff`) plus every
// Setoid/quotient lemma across Mathlib.
#[test]
fn test_approx_operator_parses_as_hasequiv() {
    let expr = Parser::parse_expr("a ≈ b").expect("`a ≈ b` parses");
    match &expr {
        SurfaceExpr::App(_, head, args) => {
            assert!(
                matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if n == "HasEquiv.Equiv"),
                "head must be HasEquiv.Equiv, got {head:?}"
            );
            assert_eq!(args.len(), 2, "`a ≈ b` — two args, got {args:?}");
        }
        other => panic!("expected App(HasEquiv.Equiv, [a, b]), got {other:?}"),
    }
}

#[test]
fn test_approx_distinct_from_equiv_iso() {
    // `≈` (HasEquiv) and `≃` (Equiv/iso) are different operators.
    let approx = Parser::parse_expr("a ≈ b").expect("≈ parses");
    let equiv = Parser::parse_expr("a ≃ b").expect("≃ parses");
    assert!(
        matches!(&approx, SurfaceExpr::App(_, h, _) if matches!(h.as_ref(), SurfaceExpr::Ident(_, n) if n == "HasEquiv.Equiv")),
        "≈ → HasEquiv.Equiv"
    );
    assert!(
        matches!(&equiv, SurfaceExpr::App(_, h, _) if matches!(h.as_ref(), SurfaceExpr::Ident(_, n) if n == "Equiv")),
        "≃ → Equiv (unchanged), got {equiv:?}"
    );
}

// Regression: the postfix inverse `x⁻¹` (U+207B U+00B9, `Inv.inv`) — pervasive
// in group/field theory across Mathlib — must lex the two-codepoint digraph
// and parse as `Inv.inv x` (like the `!` factorial postfix). Before this it was
// not lexed, so `x⁻¹` broke the parse (error-recovery).
#[test]
fn test_postfix_inv_parses_as_inv_inv() {
    let expr = Parser::parse_expr("x⁻¹").expect("`x⁻¹` parses");
    match &expr {
        SurfaceExpr::App(_, head, args) => {
            assert!(
                matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if n == "Inv.inv"),
                "head must be Inv.inv, got {head:?}"
            );
            assert_eq!(args.len(), 1, "`x⁻¹` — one arg, got {args:?}");
        }
        other => panic!("expected App(Inv.inv, [x]), got {other:?}"),
    }
}

#[test]
fn test_postfix_inv_chains() {
    // `x⁻¹⁻¹` → `Inv.inv (Inv.inv x)`.
    let expr = Parser::parse_expr("x⁻¹⁻¹").expect("`x⁻¹⁻¹` parses");
    match &expr {
        SurfaceExpr::App(_, head, args) => {
            assert!(matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if n == "Inv.inv"));
            assert!(
                matches!(&args[0].expr, SurfaceExpr::App(_, h, _) if matches!(h.as_ref(), SurfaceExpr::Ident(_, n) if n == "Inv.inv")),
                "inner must also be Inv.inv, got {:?}",
                args[0].expr
            );
        }
        other => panic!("expected nested Inv.inv, got {other:?}"),
    }
}

// Regression: the lattice `⊔` (Max.max) / `⊓` (Min.min) operators, and their
// PRECEDENCE — `⊔` (68) / `⊓` (69) sit between `+` (65) and `*` (70), so `⊓`
// binds tighter than `⊔`, both tighter than `+`, both looser than `*`. A wrong
// precedence would SILENTLY misparse; this battery pins the grouping. (The full
// 961-test suite separately guards that existing `+`/`*`/`::` parses are
// unchanged by the new chain level.)
fn app_head(e: &SurfaceExpr) -> Option<&str> {
    match e {
        SurfaceExpr::App(_, h, _) => match h.as_ref() {
            SurfaceExpr::Ident(_, n) => Some(n.as_str()),
            _ => None,
        },
        _ => None,
    }
}
/// Head-ident of the `i`-th argument of an application (type inferred to avoid
/// naming `SurfaceArg`).
fn nth_arg_head(e: &SurfaceExpr, i: usize) -> Option<&str> {
    match e {
        SurfaceExpr::App(_, _, a) => app_head(&a.get(i)?.expr),
        _ => None,
    }
}

#[test]
fn test_sup_inf_parse_and_precedence() {
    // a ⊔ b → Max.max a b
    let e = Parser::parse_expr("a ⊔ b").expect("⊔ parses");
    assert_eq!(app_head(&e), Some("Max.max"));
    // a ⊓ b → Min.min a b
    let e = Parser::parse_expr("a ⊓ b").expect("⊓ parses");
    assert_eq!(app_head(&e), Some("Min.min"));
    // a ⊔ b ⊓ c → Max.max a (Min.min b c)   [⊓ tighter than ⊔]
    let e = Parser::parse_expr("a ⊓ b").expect("x");
    let _ = e;
    let e = Parser::parse_expr("a ⊔ b ⊓ c").expect("mixed parses");
    assert_eq!(app_head(&e), Some("Max.max"), "outer is ⊔");
    assert_eq!(nth_arg_head(&e, 1), Some("Min.min"), "RHS is ⊓ (tighter)");
    // a + b ⊔ c → HAdd a (Max.max b c)   [⊔ tighter than +]
    let e = Parser::parse_expr("a + b ⊔ c").expect("mixed + parses");
    assert_eq!(app_head(&e), Some("HAdd.hAdd"), "outer is +");
    assert_eq!(
        nth_arg_head(&e, 1),
        Some("Max.max"),
        "RHS is ⊔ (tighter than +)"
    );
    // a ⊔ b * c → Max.max a (HMul b c)   [* tighter than ⊔]
    let e = Parser::parse_expr("a ⊔ b * c").expect("mixed * parses");
    assert_eq!(app_head(&e), Some("Max.max"), "outer is ⊔");
    assert_eq!(
        nth_arg_head(&e, 1),
        Some("HMul.hMul"),
        "RHS is * (tighter than ⊔)"
    );
}

#[test]
fn test_existing_arith_precedence_unchanged_by_sup_inf() {
    // a + b * c → HAdd a (HMul b c) — MUST be unchanged by the new chain level.
    let e = Parser::parse_expr("a + b * c").expect("a+b*c parses");
    assert_eq!(app_head(&e), Some("HAdd.hAdd"));
    assert_eq!(
        nth_arg_head(&e, 1),
        Some("HMul.hMul"),
        "* still binds tighter than +"
    );
}

// Regression: the indexed big-operators `⨆ i, f i` (iSup) / `⨅ i, f i` (iInf)
// — common in order/lattice/measure theory — must parse via the binder-body
// form (like Σ), desugaring to `iSup (fun i => f i)` / `iInf (fun i => f i)`.
// Before this they were not lexed and broke the parse.
#[test]
fn test_big_sup_inf_binder_desugar() {
    let e = Parser::parse_expr("⨆ i, f i").expect("⨆ parses");
    match &e {
        SurfaceExpr::App(_, head, args) => {
            assert!(
                matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if n == "iSup"),
                "head iSup, got {head:?}"
            );
            assert!(
                matches!(&args[0].expr, SurfaceExpr::Lambda(_, b, _) if b.len() == 1),
                "arg is a 1-binder lambda"
            );
        }
        other => panic!("expected iSup (fun i => ...), got {other:?}"),
    }
    let e = Parser::parse_expr("⨅ i, f i").expect("⨅ parses");
    assert!(
        matches!(&e, SurfaceExpr::App(_, h, _) if matches!(h.as_ref(), SurfaceExpr::Ident(_, n) if n == "iInf"))
    );
}

#[test]
fn test_big_sup_multi_binder_nests() {
    // `⨆ i j, f i` → `iSup (fun i => iSup (fun j => f i))`.
    let e = Parser::parse_expr("⨆ i j, f i").expect("multi-binder ⨆ parses");
    match &e {
        SurfaceExpr::App(_, head, args) => {
            assert!(matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if n == "iSup"));
            // The lambda body is itself an iSup application.
            if let SurfaceExpr::Lambda(_, _, body) = &args[0].expr {
                assert!(
                    matches!(body.as_ref(), SurfaceExpr::App(_, h, _) if matches!(h.as_ref(), SurfaceExpr::Ident(_, n) if n == "iSup")),
                    "nested iSup"
                );
            } else {
                panic!("expected lambda body");
            }
        }
        other => panic!("expected nested iSup, got {other:?}"),
    }
}

// Regression: the Set/Finset product `a ×ˢ b` (SProd.sprod, U+00D7 U+02E2
// digraph, infixr:82) — distinct from `×` (Prod) and `×'` (PSigma). Precedence
// sits between pow/mul (75/70) and `∘` (90): tighter than `*`, so `a * b ×ˢ c`
// = `a * (b ×ˢ c)`. A wrong precedence would silently misparse; the full 965+
// suite separately guards existing `*`/`^` parses (pow_expr operands rerouted).
#[test]
fn test_setprod_parse_and_precedence() {
    let e = Parser::parse_expr("a ×ˢ b").expect("×ˢ parses");
    assert_eq!(app_head(&e), Some("SProd.sprod"));
    // a * b ×ˢ c → HMul a (SProd b c)   [×ˢ (82) tighter than * (70)]
    let e = Parser::parse_expr("a * b ×ˢ c").expect("mixed parses");
    assert_eq!(app_head(&e), Some("HMul.hMul"), "outer is *");
    assert_eq!(
        nth_arg_head(&e, 1),
        Some("SProd.sprod"),
        "RHS is ×ˢ (tighter than *)"
    );
}

#[test]
fn test_setprod_distinct_from_prod_and_psigma() {
    // `×` (Prod type) and `×'` (PSigma) must still parse as before, unaffected.
    let prod = Parser::parse_expr("A × B").expect("× parses");
    assert_eq!(app_head(&prod), Some("Prod"), "× still Prod, got {prod:?}");
}

// Regression: category-morphism composition `f ≫ g` (CategoryStruct.comp,
// scoped infixr:80) — fundamental across CategoryTheory. Right-associative:
// `f ≫ g ≫ h` = `CategoryStruct.comp f (CategoryStruct.comp g h)`. The full
// 967+ suite guards that existing `^`/`*`/`×ˢ` parses are unchanged by the new
// chain level (pow_expr operands rerouted through comp_expr).
#[test]
fn test_cat_comp_parses_right_assoc() {
    let e = Parser::parse_expr("f ≫ g").expect("≫ parses");
    assert_eq!(app_head(&e), Some("CategoryStruct.comp"));
    // f ≫ g ≫ h → comp f (comp g h)
    let e = Parser::parse_expr("f ≫ g ≫ h").expect("chained ≫ parses");
    assert_eq!(app_head(&e), Some("CategoryStruct.comp"), "outer comp");
    assert_eq!(
        nth_arg_head(&e, 1),
        Some("CategoryStruct.comp"),
        "RHS is comp (right-assoc)"
    );
}

// Regression: morphism-type arrow `a ⟶ b` (Quiver.Hom, infixr:10, the loosest
// operator) — fundamental across CategoryTheory. Right-associative:
// `a ⟶ b ⟶ c` = `Quiver.Hom a (Quiver.Hom b c)`. hom_expr sits at the TOP of
// the chain (every expr passes through), so the full 968+ suite is the safety
// net that existing parses (logic, arithmetic, application) are unchanged.
#[test]
fn test_hom_arrow_parses_right_assoc() {
    let e = Parser::parse_expr("a ⟶ b").expect("⟶ parses");
    assert_eq!(app_head(&e), Some("Quiver.Hom"));
    let e = Parser::parse_expr("a ⟶ b ⟶ c").expect("chained ⟶ parses");
    assert_eq!(app_head(&e), Some("Quiver.Hom"), "outer Hom");
    assert_eq!(
        nth_arg_head(&e, 1),
        Some("Quiver.Hom"),
        "RHS is Hom (right-assoc)"
    );
}

#[test]
fn test_hom_arrow_does_not_disturb_ordinary_exprs() {
    // A plain expression with no `⟶` is unchanged by the new top-of-chain level.
    let e = Parser::parse_expr("f x").expect("application parses");
    assert!(
        matches!(&e, SurfaceExpr::App(_, h, _) if matches!(h.as_ref(), SurfaceExpr::Ident(_, n) if n == "f"))
    );
    // Arithmetic still groups correctly.
    let e = Parser::parse_expr("a + b").expect("+ parses");
    assert_eq!(app_head(&e), Some("HAdd.hAdd"));
}
