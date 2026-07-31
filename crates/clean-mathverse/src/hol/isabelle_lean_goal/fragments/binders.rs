// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder fragment: the object-level quantifiers and set comprehension, opened
//! from their Isabelle `Abs` predicate argument by the capture-safe de Bruijn
//! instantiation in [`super::super::term::open_abs`].
//!
//! Faithfulness — each mapping is the Isabelle definition *identically* spelled
//! by the Mathlib definition:
//! * `HOL.All (λx. P x)` = `∀x. P x`           → `∀ x, P`   (Lean `∀`).
//! * `HOL.Ex  (λx. P x)` = `∃x. P x`           → `∃ x, P`   (`Exists`).
//! * `HOL.Ex1 (λx. P x)` = `∃!x. P x`          → `∃! x, P`  (`ExistsUnique p`
//!    ≝ `∃x. p x ∧ ∀y. p y → y = x`, identical to Isabelle `Ex1`).
//! * `Set.Ball A (λx. P x)` = `∀x. x∈A ⟶ P x`  → `∀ x ∈ A, P` (Lean binder
//!    notation desugars to `∀ x, x ∈ A → P` — identical).
//! * `Set.Bex A (λx. P x)`  = `∃x. x∈A ∧ P x`  → `∃ x ∈ A, P` (desugars to
//!    `∃ x, x ∈ A ∧ P` — identical).
//! * `Set.Collect (λx. P x)` = `{x. P x}`      → `{x | P}`   (`setOf p`, and a
//!    `Set` *is* its membership predicate — identical).
//!
//! The unbounded quantifiers carry a **concrete** domain annotation (`∀ x : ℕ,
//! …`) when the Isabelle domain type renders variable-free (which needs no shared
//! type context); a domain with type variables is left to Lean inference (`∀ x,
//! …`) — an un-inferable domain surfaces as a *loud* elaboration error
//! downstream, never a silent-wrong statement. Bounded quantifiers and set
//! comprehensions leave the element type to the set / body (their target forms
//! are `∀ x ∈ S, …` and `{x | …}`).
//!
//! A quantifier whose predicate is an η-contracted bare term `P` (not a literal
//! `Abs`, as in the `…_def` lemmas) is η-expanded to a fresh binder applied to
//! it (`∀ x, P x`) — still faithful. Any argument shape that is neither an `Abs`
//! nor a renderable predicate is declined (never guessed).

use super::super::super::isabelle_pure::{IsaTerm, IsaType};
use super::super::lean_type::{render_type, term_type, TyCtx};
use super::super::term::{fresh_name, open_abs, translate_term};
use super::super::types::{BinderKind, LeanTerm, Unsupported};

/// Try to render `n` as a quantifier / bounded quantifier / set comprehension.
pub(super) fn try_translate(n: &str, args: &[&IsaTerm]) -> Option<Result<LeanTerm, Unsupported>> {
    let out = match n {
        "HOL.All" => quantifier(n, BinderKind::Forall, args),
        "HOL.Ex" => quantifier(n, BinderKind::Exists, args),
        "HOL.Ex1" => quantifier(n, BinderKind::ExistsUnique, args),
        "Set.Ball" => bounded(n, BinderKind::Forall, args),
        "Set.Bex" => bounded(n, BinderKind::Exists, args),
        "Set.Collect" => collect(args),
        _ => return None,
    };
    Some(out)
}

/// An unbounded quantifier `HOL.All`/`HOL.Ex`/`HOL.Ex1` applied to one predicate.
fn quantifier(n: &str, kind: BinderKind, args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [pred] = args else {
        return Err(Unsupported::PartialApplication(n.to_string()));
    };
    let (var, ty, body_term) = open_pred(pred)?;
    let body = translate_term(&body_term)?;
    Ok(LeanTerm::Binder {
        kind,
        var,
        ty,
        dom: None,
        body: Box::new(body),
    })
}

/// A bounded quantifier `Set.Ball`/`Set.Bex` applied to a set and a predicate.
/// The domain is pinned by the set, so the binder is emitted untyped
/// (`∀ x ∈ S, …`).
fn bounded(n: &str, kind: BinderKind, args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [set, pred] = args else {
        return Err(Unsupported::PartialApplication(n.to_string()));
    };
    let dom = translate_term(set)?;
    let (var, _ty, body_term) = open_pred(pred)?;
    let body = translate_term(&body_term)?;
    Ok(LeanTerm::Binder {
        kind,
        var,
        ty: None,
        dom: Some(Box::new(dom)),
        body: Box::new(body),
    })
}

/// A set comprehension `Set.Collect (λx. P x)` → `{x | P}` (element type inferred
/// from the body, matching the `{x | …}` target).
fn collect(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [pred] = args else {
        return Err(Unsupported::PartialApplication("Set.Collect".to_string()));
    };
    let (var, _ty, body_term) = open_pred(pred)?;
    let body = translate_term(&body_term)?;
    Ok(LeanTerm::Binder {
        kind: BinderKind::SetOf,
        var,
        ty: None,
        dom: None,
        body: Box::new(body),
    })
}

/// Open a quantifier/comprehension predicate argument to `(binder name, optional
/// concrete type annotation, opened body term)`. Handles the literal `Abs` form
/// (the common case) and η-expands a bare predicate `P` to `λx. P x`.
fn open_pred(pred: &IsaTerm) -> Result<(String, Option<String>, IsaTerm), Unsupported> {
    match pred {
        IsaTerm::Abs { n, t, b } => {
            let (var, ty, body) = open_abs(n, t, b);
            Ok((var, concrete_type(&ty), body))
        }
        // η-contracted predicate `P` (not a lambda): `∀x. P x`. Invent a fresh
        // binder not free in `P` and apply `P` to it. Left untyped (the domain is
        // pinned by `P`'s application).
        _ => {
            let var = fresh_name("x", pred);
            let body = IsaTerm::App {
                f: Box::new(pred.clone()),
                a: Box::new(IsaTerm::Free {
                    n: var.clone(),
                    t: pred_domain(pred),
                }),
            };
            Ok((var, None, body))
        }
    }
}

/// Render an Isabelle domain type to a Lean type annotation **only** when it is
/// fully concrete (interns no type variable, so it needs no shared type context
/// and is unambiguously faithful). A type-variable domain returns `None` (left to
/// inference).
fn concrete_type(t: &IsaType) -> Option<String> {
    let mut probe = TyCtx::default();
    match render_type(t, &mut probe) {
        Ok(s) if probe.is_empty() => Some(s),
        _ => None,
    }
}

/// The domain type of an η-contracted predicate `P : dom ⇒ bool` (recovered from
/// `P`'s type for the synthesized `Free`; the renderer only uses the `Free`'s
/// name, so a `bool` placeholder is harmless when the type is unknown).
fn pred_domain(pred: &IsaTerm) -> IsaType {
    match term_type(pred) {
        Some(IsaType::Type { n, a }) if n == "fun" && a.len() == 2 => a[0].clone(),
        _ => IsaType::Type {
            n: "HOL.bool".to_string(),
            a: vec![],
        },
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::render::render_top;
    use super::*;

    fn nat() -> IsaType {
        IsaType::Type {
            n: "Nat.nat".into(),
            a: vec![],
        }
    }
    fn tvar() -> IsaType {
        IsaType::TVar {
            n: "'a".into(),
            i: 0,
        }
    }
    fn setty() -> IsaType {
        IsaType::Type {
            n: "Set.set".into(),
            a: vec![tvar()],
        }
    }
    fn bound(i: i64) -> IsaTerm {
        IsaTerm::Bound { i }
    }
    fn free(n: &str, t: IsaType) -> IsaTerm {
        IsaTerm::Free { n: n.into(), t }
    }
    fn con(n: &str, t: IsaType) -> IsaTerm {
        IsaTerm::Const { n: n.into(), t }
    }
    fn app(f: IsaTerm, a: IsaTerm) -> IsaTerm {
        IsaTerm::App {
            f: Box::new(f),
            a: Box::new(a),
        }
    }
    fn abs(n: &str, t: IsaType, b: IsaTerm) -> IsaTerm {
        IsaTerm::Abs {
            n: n.into(),
            t,
            b: Box::new(b),
        }
    }
    fn boolfn(dom: IsaType) -> IsaType {
        IsaType::Type {
            n: "fun".into(),
            a: vec![
                dom,
                IsaType::Type {
                    n: "HOL.bool".into(),
                    a: vec![],
                },
            ],
        }
    }
    /// `HOL.eq` at a nat operand, curried spine `= a b`.
    fn eq(a: IsaTerm, b: IsaTerm) -> IsaTerm {
        app(app(con("HOL.eq", boolfn(nat())), a), b)
    }

    #[test]
    fn forall_concrete_domain_is_typed() {
        // ∀ (x::nat). x = x   →   ∀ x : ℕ, x = x
        let pred = abs("x", nat(), eq(bound(0), bound(0)));
        let out = try_translate("HOL.All", &[&pred]).unwrap().unwrap();
        assert_eq!(render_top(&out), "∀ x : ℕ, x = x");
    }

    #[test]
    fn exists_typevar_domain_is_untyped() {
        // ∃ (x::'a). x = x   →   ∃ x, x = x   (domain is a type var → inferred)
        let pred = abs(
            "x",
            tvar(),
            app(app(con("HOL.eq", boolfn(tvar())), bound(0)), bound(0)),
        );
        let out = try_translate("HOL.Ex", &[&pred]).unwrap().unwrap();
        assert_eq!(render_top(&out), "∃ x, x = x");
    }

    #[test]
    fn ex1_renders() {
        let pred = abs("x", nat(), eq(bound(0), bound(0)));
        let out = try_translate("HOL.Ex1", &[&pred]).unwrap().unwrap();
        assert_eq!(render_top(&out), "∃! x : ℕ, x = x");
    }

    #[test]
    fn nested_binders_capture_safe() {
        // ∀x. ∃x. x_outer = x_inner   (Bound 1 = outer, Bound 0 = inner)
        //   →   ∀ x : ℕ, ∃ x_1 : ℕ, x = x_1
        let inner = abs("x", nat(), eq(bound(1), bound(0)));
        let pred = abs("x", nat(), app(con("HOL.Ex", boolfn(nat())), inner));
        let out = try_translate("HOL.All", &[&pred]).unwrap().unwrap();
        assert_eq!(render_top(&out), "∀ x : ℕ, ∃ x_1 : ℕ, x = x_1");
    }

    #[test]
    fn free_var_not_captured_by_binder() {
        // ∀x. x = y_free  with a free `x` in the body's sibling position must NOT
        // reuse the free name. Here the free var is literally named `x`, so the
        // binder must freshen to `x_1`.
        let pred = abs("x", nat(), eq(bound(0), free("x", nat())));
        let out = try_translate("HOL.All", &[&pred]).unwrap().unwrap();
        assert_eq!(render_top(&out), "∀ x_1 : ℕ, x_1 = x");
    }

    #[test]
    fn bounded_ball_and_bex() {
        // ∀ x ∈ A. x ∈ A   (Ball A (λx. member x A))
        let member = |x: IsaTerm, s: IsaTerm| {
            app(
                app(
                    con(
                        "Set.member",
                        IsaType::Type {
                            n: "fun".into(),
                            a: vec![tvar(), boolfn(setty())],
                        },
                    ),
                    x,
                ),
                s,
            )
        };
        let a_set = free("A", setty());
        let pred = abs("x", tvar(), member(bound(0), a_set.clone()));
        let out = try_translate("Set.Ball", &[&a_set, &pred])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "∀ x ∈ A, x ∈ A");
        let pred = abs("x", tvar(), member(bound(0), a_set.clone()));
        let out = try_translate("Set.Bex", &[&a_set, &pred]).unwrap().unwrap();
        assert_eq!(render_top(&out), "∃ x ∈ A, x ∈ A");
    }

    #[test]
    fn collect_is_setof() {
        // {x. x = x}  →  {x | x = x}
        let pred = abs("x", nat(), eq(bound(0), bound(0)));
        let out = try_translate("Set.Collect", &[&pred]).unwrap().unwrap();
        assert_eq!(render_top(&out), "{x | x = x}");
    }

    #[test]
    fn quantifier_wraps_as_operand() {
        // (∀ x, x = x) ∧ p   — a quantifier operand of ∧ must parenthesize.
        let pred = abs(
            "x",
            tvar(),
            app(app(con("HOL.eq", boolfn(tvar())), bound(0)), bound(0)),
        );
        let all = app(con("HOL.All", boolfn(boolfn(tvar()))), pred);
        let conj = app(
            app(
                con(
                    "HOL.conj",
                    boolfn(IsaType::Type {
                        n: "HOL.bool".into(),
                        a: vec![],
                    }),
                ),
                all,
            ),
            free(
                "p",
                IsaType::Type {
                    n: "HOL.bool".into(),
                    a: vec![],
                },
            ),
        );
        let out = translate_term(&conj).unwrap();
        assert_eq!(render_top(&out), "(∀ x, x = x) ∧ p");
    }

    #[test]
    fn eta_contracted_predicate_expands() {
        // HOL.All P  (P a bare predicate var)  →  ∀ x, P x
        let p = free("P", boolfn(nat()));
        let out = try_translate("HOL.All", &[&p]).unwrap().unwrap();
        assert_eq!(render_top(&out), "∀ x, P x");
    }

    #[test]
    fn partial_application_declined() {
        assert!(matches!(
            try_translate("HOL.All", &[]),
            Some(Err(Unsupported::PartialApplication(_)))
        ));
    }
}
