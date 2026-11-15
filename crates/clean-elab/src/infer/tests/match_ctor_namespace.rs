// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match-pattern constructor resolution through opened namespaces.
//!
//! Term references resolve through opened namespaces (`open Foo` makes `bar`
//! resolve to `Foo.bar`). Match-pattern constructor names must do the same,
//! so `open Foo; match x with | bar => ..` resolves `bar` to the opened
//! constructor `Foo.bar` rather than treating `bar` as a catch-all variable
//! binder (the unsound prior behavior) or failing outright.

use super::*;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

/// Build an environment containing a simple two-constructor `Color` enum:
///
/// ```lean
/// inductive Color where
///   | red : Color
///   | green : Color
/// ```
///
/// plus a top-level axiom `c : Color` to use as a scrutinee.
fn color_env() -> Environment {
    let mut env = Environment::new();
    let color = Name::from_string("Color");
    let color_ref = Expr::const_(color.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: color.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Color.red"),
                    type_: color_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Color.green"),
                    type_: color_ref.clone(),
                },
            ],
        }],
    })
    .expect("Color inductive should register");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c"),
        level_params: vec![],
        type_: color_ref,
    })
    .expect("axiom c : Color should register");
    env
}

/// Arm bodies are `Color` values (`Color.red`) so the branch type is `Color`,
/// avoiding any dependency on `Nat` / a full prelude in the test environment.
fn color_body() -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("Color.red"))
}

/// A `match c with | <arm0> | Color.green => Color.red` expression, where
/// `arm0` is the arm under test (typically a `Var`/`Ctor` pattern naming a
/// constructor). The filler arm is spelled QUALIFIED: a bare `green` resolves
/// only through the scrutinee type's namespace, which is refused (see
/// `test_match_ctor_bare_name_only_through_the_type_is_refused`).
fn match_c_with(arm0: SurfaceMatchArm) -> SurfaceExpr {
    SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("c"),
        )),
        vec![
            arm0,
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Var(SurfaceName::generated_path("Color.green")),
                body: color_body(),
            },
        ],
    )
}

fn var_arm(name: SurfaceName) -> SurfaceMatchArm {
    SurfaceMatchArm {
        span: Span::dummy(),
        pattern: SurfacePattern::Var(name),
        body: color_body(),
    }
}

/// Install an `open`-style alias `short -> target` into the elaborator's
/// namespace state, mirroring what `open Foo` / `export` does for term refs.
fn ctx_with_alias<'a>(env: &'a Environment, short: Name, target: Name) -> ElabCtx<'a> {
    let mut state = crate::namespace::NamespaceState::new();
    state.insert_alias_pub(short, target);
    let mut ctx = ElabCtx::new(env);
    ctx.set_namespace_state(state);
    ctx
}

/// Count `let`-binders in an expression. A constructor-case minor premise has
/// none; a mis-resolved catch-all variable arm introduces one `let` per
/// constructor case, so this distinguishes "matched the ctor" from "bound a
/// fresh variable".
fn count_lets(expr: &Expr) -> usize {
    match expr.kind() {
        ExprKind::Let(_, ty, val, body, _) => {
            1 + count_lets(ty) + count_lets(val) + count_lets(body)
        }
        ExprKind::App(f, a) => count_lets(f) + count_lets(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => count_lets(ty) + count_lets(body),
        _ => 0,
    }
}

#[test]
fn test_match_ctor_bare_name_only_through_the_type_is_refused() {
    // Bare `red` is not found by ordinary name resolution (no `open Color`),
    // so Lean 4 reads it as a catch-all VARIABLE; the `TypeName.ctor`
    // shorthand would read it as the constructor `Color.red`. This test used
    // to pin the shorthand. The two readings differ — `| some c => 0 | _ => 1`
    // proved a false theorem that way (2026-09-24/25) — so the pattern is
    // refused, naming the unambiguous spellings.
    let env = color_env();
    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_c_with(var_arm(SurfaceName::generated_path("red"))));
    assert!(
        matches!(&result, Err(ElabError::Unsupported { feature })
            if feature.contains("is a pattern variable in Lean 4")
                && feature.contains("Color.red")),
        "bare `red` must be refused as ambiguous, not resolved to Color.red: {result:?}"
    );
}

#[test]
fn test_match_ctor_qualified_name_still_resolves() {
    // Baseline: fully-qualified `Color.red` resolves directly to the ctor case.
    let env = color_env();
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&match_c_with(var_arm(SurfaceName::generated_path(
            "Color.red",
        ))))
        .expect("qualified ctor `Color.red` should resolve");
    assert_eq!(
        count_lets(&result),
        0,
        "qualified ctor `Color.red` should compile to a constructor case: {result:?}"
    );
}

#[test]
fn test_match_ctor_opened_namespace_alias_resolves_to_constructor() {
    // GAP + SOUNDNESS: `open Color renaming red -> crimson` installs alias
    // `crimson -> Color.red`. Matching on bare `crimson` must resolve through
    // the opened-namespace alias table to the *constructor* `Color.red`, the
    // same way term references resolve. Previously `crimson` was silently
    // bound as a fresh catch-all variable (one `let` per ctor case), which is
    // semantically wrong.
    let env = color_env();
    let mut ctx = ctx_with_alias(
        &env,
        Name::from_string("crimson"),
        Name::from_string("Color.red"),
    );
    let aliased = ctx
        .elaborate(&match_c_with(var_arm(SurfaceName::generated_path(
            "crimson",
        ))))
        .expect("opened-namespace ctor alias `crimson -> Color.red` should resolve");

    // It must match the constructor, not bind a catch-all variable.
    assert_eq!(
        count_lets(&aliased),
        0,
        "opened ctor alias must compile to a constructor case, not a catch-all binder: {aliased:?}"
    );

    // And it must produce exactly the same elaboration as the qualified form.
    let mut ctx_q = ElabCtx::new(&env);
    let qualified = ctx_q
        .elaborate(&match_c_with(var_arm(SurfaceName::generated_path(
            "Color.red",
        ))))
        .expect("qualified baseline should elaborate");
    assert_eq!(
        aliased, qualified,
        "opened alias `crimson` should elaborate identically to qualified `Color.red`"
    );
}

#[test]
fn test_match_ctor_alias_to_other_inductive_is_not_misresolved() {
    // SOUNDNESS: an alias pointing at a constructor of an *unrelated* inductive
    // (`Bool.true`) must not be accepted as a `Color` constructor or silently
    // become a variable binder. Actual Lean 4.30.0-rc2 rejects a resolved
    // foreign constructor even when it was selected through an opened alias.
    let mut env = color_env();
    let bool_name = Name::from_string("Bool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ref,
                },
            ],
        }],
    })
    .expect("Bool inductive should register");

    // alias `t -> Bool.true`; `t` is NOT a Color constructor.
    let mut ctx = ctx_with_alias(&env, Name::from_string("t"), Name::from_string("Bool.true"));
    let result = ctx.elaborate(&match_c_with(var_arm(SurfaceName::generated_path("t"))));
    assert!(
        matches!(&result, Err(ElabError::TypeMismatch { expected, actual })
            if expected == "constructor of Color" && actual == "constructor Bool.true of Bool"),
        "a resolved foreign constructor must refuse, not become a catch-all binder: {result:?}"
    );
}

#[test]
fn test_match_non_constructor_constant_is_bound_as_variable() {
    // SOUNDNESS: a bare pattern name that resolves to a genuine constant which
    // is NOT a constructor (here the axiom `notACtor : Color`) must be treated
    // as a fresh catch-all variable binder, never mistaken for a ctor case.
    let mut env = color_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("notACtor"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Color"), vec![]),
    })
    .expect("axiom should register");

    // `| notACtor => … | Color.green => …`: read as a binder, `notACtor` is a
    // catch-all, so the `Color.green` alternative is selected by no value and
    // Lean refuses the match ("redundant alternative"; G62). That refusal is
    // what proves the binder reading — a constructor test would leave the
    // second alternative reachable.
    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_c_with(var_arm(SurfaceName::generated_path(
        "notACtor",
    ))));
    assert!(
        matches!(result, Err(ElabError::RedundantAlternative { .. })),
        "a non-constructor constant binds a catch-all variable: {result:?}"
    );
    // With the binder arm last, the match elaborates and binds the variable.
    let binder_last = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("c"),
        )),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Var(SurfaceName::generated_path("Color.green")),
                body: color_body(),
            },
            var_arm(SurfaceName::generated_path("notACtor")),
        ],
    );
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&binder_last)
        .expect("a non-ctor name binds a variable and still elaborates");
    assert!(
        count_lets(&result) > 0,
        "non-constructor constant must bind a variable (catch-all), not match a ctor: {result:?}"
    );
}

#[test]
fn test_resolve_ctor_name_helper_paths() {
    // Direct unit coverage of the resolution helper: bare, qualified, opened
    // alias, and rejection of foreign / non-constructor names.
    let mut env = color_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("notACtor"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Color"), vec![]),
    })
    .expect("axiom should register");

    let mut state = crate::namespace::NamespaceState::new();
    state.insert_alias_pub(Name::from_string("crimson"), Name::from_string("Color.red"));
    state.insert_alias_pub(
        Name::from_string("aliasToConst"),
        Name::from_string("notACtor"),
    );
    let mut ctx = ElabCtx::new(&env);
    ctx.set_namespace_state(state);

    assert_eq!(
        ctx.resolve_ctor_name(
            &SurfaceName::generated_path("red"),
            &SurfaceName::generated_path("Color")
        ),
        Some(SurfaceName::generated_path("Color.red")),
        "bare ctor name should qualify to Color.red"
    );
    assert_eq!(
        ctx.resolve_ctor_name(
            &SurfaceName::generated_path("Color.green"),
            &SurfaceName::generated_path("Color")
        ),
        Some(SurfaceName::generated_path("Color.green")),
        "already-qualified ctor name should resolve as-is"
    );
    assert_eq!(
        ctx.resolve_ctor_name(
            &SurfaceName::generated_path("crimson"),
            &SurfaceName::generated_path("Color")
        ),
        Some(SurfaceName::generated_path("Color.red")),
        "opened-namespace alias should resolve to the qualified ctor"
    );
    assert_eq!(
        ctx.resolve_ctor_name(
            &SurfaceName::generated_path("aliasToConst"),
            &SurfaceName::generated_path("Color")
        ),
        None,
        "alias pointing at a non-constructor constant must not resolve"
    );
    assert_eq!(
        ctx.resolve_ctor_name(
            &SurfaceName::generated_path("nonexistent"),
            &SurfaceName::generated_path("Color")
        ),
        None,
        "an unknown name must not resolve"
    );
}

/// Extend `color_env` with `Pair` wrapping two `Color` fields:
///
/// ```lean
/// inductive Pair where
///   | mk : Color -> Color -> Pair
/// ```
///
/// plus an axiom `p : Pair`.
fn pair_env() -> Environment {
    let mut env = color_env();
    let color_ref = Expr::const_(Name::from_string("Color"), vec![]);
    let pair = Name::from_string("Pair");
    let pair_ref = Expr::const_(pair.clone(), vec![]);
    let mk_ty = Expr::arrow(color_ref.clone(), Expr::arrow(color_ref, pair_ref.clone()));
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Pair inductive should register");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: pair_ref,
    })
    .expect("axiom p : Pair should register");
    env
}

#[test]
fn test_match_nested_ctor_opened_alias_resolves() {
    // SOUNDNESS / GAP in a nested sub-pattern position:
    // `match p with | Pair.mk crimson g => ..` where `crimson -> Color.red`.
    // The nested `crimson` field pattern must dispatch on the `Color.red`
    // constructor (producing an inner `Color.casesOn`), matching the behavior
    // of the explicitly-qualified `Color.red` sub-pattern.
    let env = pair_env();

    // `fallback`: a constructor-valued nested field pattern is partial, so a
    // real covering arm is supplied and its non-matching Color minor is never
    // fabricated with a synthetic proof/value. A binder field makes the first
    // arm a catch-all, and Lean refuses a covering arm behind it ("redundant
    // alternative", G62), so the binder baseline has none.
    let mk_arm = |first: SurfacePattern, fallback: bool| {
        let mut arms = vec![SurfaceMatchArm {
            span: Span::dummy(),
            pattern: SurfacePattern::Ctor(
                SurfaceName::generated_path("Pair.mk"),
                vec![first, SurfacePattern::Var(SurfaceName::generated_path("g"))],
            ),
            body: color_body(),
        }];
        if fallback {
            arms.push(SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("Color.green")),
            });
        }
        SurfaceExpr::Match(
            Span::dummy(),
            None,
            Box::new(SurfaceExpr::Ident(
                Span::dummy(),
                SurfaceName::generated_path("p"),
            )),
            arms,
        )
    };

    // Baseline: an unrelated nested binder (`x`) does NOT dispatch — no inner
    // Color.casesOn is introduced for the first field.
    let mut ctx_var = ElabCtx::new(&env);
    let plain = ctx_var
        .elaborate(&mk_arm(
            SurfacePattern::Var(SurfaceName::generated_path("x")),
            false,
        ))
        .expect("nested plain binder should elaborate");
    assert_eq!(
        count_const(&plain, "Color.casesOn"),
        0,
        "a plain nested binder must not introduce a Color.casesOn dispatch: {plain:?}"
    );

    // The opened ctor alias `crimson -> Color.red` in a nested position must
    // dispatch on the constructor, introducing an inner Color.casesOn whose
    // matched-case value is the `Color.red` constructor.
    let mut ctx = ctx_with_alias(
        &env,
        Name::from_string("crimson"),
        Name::from_string("Color.red"),
    );
    let aliased = ctx
        .elaborate(&mk_arm(
            SurfacePattern::Var(SurfaceName::generated_path("crimson")),
            true,
        ))
        .expect("nested opened ctor alias should elaborate");
    assert!(
        count_const(&aliased, "Color.casesOn") > 0,
        "nested ctor alias should produce an inner Color.casesOn dispatch: {aliased:?}"
    );
    assert!(
        count_const(&aliased, "Color.red") > 0,
        "nested ctor alias should dispatch on the resolved Color.red constructor: {aliased:?}"
    );
}

/// Count occurrences of a named constant in an expression.
fn count_const(expr: &Expr, needle: &str) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) => usize::from(name.to_string() == needle),
        ExprKind::App(f, a) => count_const(f, needle) + count_const(a, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_const(ty, needle) + count_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_const(ty, needle) + count_const(val, needle) + count_const(body, needle)
        }
        _ => 0,
    }
}
