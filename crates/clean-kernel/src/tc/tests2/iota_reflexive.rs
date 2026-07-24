// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iota reduction tests for reflexive/higher-order recursive fields (#1406).
//!
//! Reflexive inductives have constructor fields of the form `(x : B) → I params`,
//! where the recursive reference is behind a Pi binder. The IH must be
//! lambda-wrapped: `λ x. I.rec params motive minor (field x)`.
//!
//! Canonical example: W-types (`W A B` with `mk : (a : A) → (B a → W A B) → W A B`).
//! Lean 4 reference: inductive.cpp:731-741.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Build a W-type environment (universe 0 for simplicity).
///
/// `W : (A : Type) → (B : A → Type) → Type`
/// `W.mk : (A : Type) → (B : A → Type) → (a : A) → (f : B a → W A B) → W A B`
fn make_w_env() -> (Environment, Name) {
    let mut env = Environment::new();
    let w_name = Name::from_string("W");
    let w_c = |lvls: Vec<Level>| Expr::const_(w_name.clone(), lvls);
    let type0 = Expr::type_();

    let w_type = Expr::pi(
        BinderInfo::Default,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), type0.clone()),
            type0.clone(),
        ),
    );

    // Under 3 binders (A, B, a): B a → W A B
    let b_a = Expr::app(Expr::bvar(1), Expr::bvar(0));
    let w_a_b_4 = Expr::app(Expr::app(w_c(vec![]), Expr::bvar(3)), Expr::bvar(2));
    let f_type = Expr::pi(BinderInfo::Default, b_a, w_a_b_4);
    // Under 4 binders (A, B, a, f): W A B
    let w_ret = Expr::app(Expr::app(w_c(vec![]), Expr::bvar(3)), Expr::bvar(2));

    let mk_type = Expr::pi(
        BinderInfo::Default,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), type0),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(BinderInfo::Default, f_type, w_ret),
            ),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: w_name.clone(),
            type_: w_type,
            constructors: vec![Constructor {
                name: Name::from_string("W.mk"),
                type_: mk_type,
            }],
        }],
    })
    .expect("add W");

    (env, w_name)
}

/// Helper: build `W.rec@{0} A B motive minor major` application.
fn build_w_rec_app(a: Expr, b: Expr, motive: Expr, minor: Expr, major: Expr) -> Expr {
    let rec = Expr::const_(Name::from_string("W.rec"), vec![Level::zero()]);
    Expr::app(
        Expr::app(Expr::app(Expr::app(Expr::app(rec, a), b), motive), minor),
        major,
    )
}

/// Helper: build `W.mk A B a f` constructor application.
fn build_w_mk(a: Expr, b: Expr, a_elem: Expr, f: Expr) -> Expr {
    let mk = Expr::const_(Name::from_string("W.mk"), vec![]);
    Expr::app(Expr::app(Expr::app(Expr::app(mk, a), b), a_elem), f)
}

#[test]
fn test_w_type_recursor_metadata() {
    let (env, _) = make_w_env();
    let rec_val = env
        .get_recursor(&Name::from_string("W.rec"))
        .expect("W.rec");
    assert_eq!(
        (rec_val.num_params, rec_val.num_indices, rec_val.num_minors),
        (2, 0, 1)
    );

    let mk_rule = rec_val
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("W.mk"))
        .expect("mk rule");
    assert_eq!(mk_rule.num_fields, 2);
    assert_eq!(mk_rule.recursive_fields, vec![false, true]);
    assert!(mk_rule.rhs.is_lam(), "mk rule RHS should be a lambda");
}

/// Verify the RHS lambda for W.mk encodes `λ x. W.rec A B motive minor (f x)`.
#[test]
fn test_w_type_rhs_has_lambda_wrapped_ih() {
    let (env, _) = make_w_env();
    let rec_val = env
        .get_recursor(&Name::from_string("W.rec"))
        .expect("W.rec");
    let mk_rule = rec_val
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("W.mk"))
        .expect("mk rule");

    // Peel 6 lambdas: params(2) + motive(1) + minor(1) + fields(2)
    let mut expr = mk_rule.rhs.clone();
    let mut lam_count = 0;
    while let ExprKind::Lam(_, _, body) = expr.kind() {
        expr = (**body).clone();
        lam_count += 1;
    }
    assert_eq!(lam_count, 6, "RHS should have 6 lambda binders");

    // Body = App(App(App(minor, a), f), ih); peel outermost to get ih
    let ih = match expr.kind() {
        ExprKind::App(_, ih) => ih.clone(),
        _ => unreachable!("body should be App(..., ih), got: {:?}", expr),
    };

    // IH must be a lambda (the reflexive wrapping)
    assert!(
        matches!(ih.kind(), ExprKind::Lam(_, _, _)),
        "IH should be λ x. ..., not {:?} (missing lambda wrapping)",
        ih
    );
    let ih_body = match ih.kind() {
        ExprKind::Lam(_, _, body) => body,
        _ => unreachable!(),
    };

    // Under 7 binders: ih_body = W.rec A B motive minor (f x)
    let ih_body_fn = ih_body.get_app_fn();
    let ih_body_args = ih_body.get_app_args();

    assert!(
        matches!(ih_body_fn.kind(), ExprKind::Const(n, _) if *n == Name::from_string("W.rec")),
        "IH body head should be W.rec, got {:?}",
        ih_body_fn
    );
    assert_eq!(ih_body_args.len(), 5, "IH rec should have 5 args");

    // Last arg = App(f, x) = App(BVar(1), BVar(0))
    let major = ih_body_args[4];
    assert!(
        matches!(major.kind(), ExprKind::App(f, x)
            if *f.kind() == ExprKind::BVar(1) && *x.kind() == ExprKind::BVar(0)),
        "major premise should be (f x) = App(BVar(1), BVar(0)), got {:?}",
        major
    );
}

/// W.rec applied to (W.mk a f) must reduce via lambda-wrapped IH.
#[test]
fn test_iota_reduction_reflexive_w_type() {
    let (env, w_name) = make_w_env();
    let tc = TypeChecker::new(&env);
    let prop = Expr::prop();
    let a_val = prop.clone();
    let b_val = Expr::lam(BinderInfo::Default, prop.clone(), prop.clone());

    // motive : W A B → Prop = λ _. Prop
    let w_a_b = Expr::app(
        Expr::app(Expr::const_(w_name.clone(), vec![]), a_val.clone()),
        b_val.clone(),
    );
    let motive = Expr::lam(BinderInfo::Default, w_a_b, prop.clone());

    // minor = λ a. λ f. λ ih. Prop (ignores all args)
    let f_ty = Expr::pi(
        BinderInfo::Default,
        Expr::app(b_val.clone(), Expr::bvar(0)),
        Expr::app(
            Expr::app(Expr::const_(w_name.clone(), vec![]), a_val.clone()),
            b_val.clone(),
        ),
    );
    let minor = Expr::lam(
        BinderInfo::Default,
        a_val.clone(),
        Expr::lam(
            BinderInfo::Default,
            f_ty,
            Expr::lam(BinderInfo::Default, prop.clone(), prop.clone()),
        ),
    );

    let f_var = Expr::fvar(FVarId(999));
    let major = build_w_mk(a_val.clone(), b_val.clone(), prop.clone(), f_var);
    let app = build_w_rec_app(a_val, b_val, motive, minor, major);

    let result = tc.whnf(&app);
    assert_ne!(app, result, "W.rec (W.mk ...) must reduce");
    assert_eq!(
        result,
        Expr::prop(),
        "should reduce to Prop via constant minor"
    );
}

/// Verify that W.rec's type has correct Pi domain types in the minor premise's
/// IH binder (#1784 audit: Researcher finding 1 + 3).
///
/// The minor premise type should be:
///   ∀ (a : A) (f : B a → W A B) (ih : ∀ (x : B a), motive (f x)), motive (W.mk A B a f)
///
/// The IH's Pi domain must be `B a` (an App), NOT `Prop`/`Sort 0` (a dummy).
/// Lean 4 ref: inductive.cpp:649-662 uses real `binding_domain` types.
#[test]
fn test_w_type_minor_premise_ih_domain_is_real_type() {
    let (env, _) = make_w_env();
    let rec_val = env
        .get_recursor(&Name::from_string("W.rec"))
        .expect("W.rec");

    // W.rec type is a Pi chain: params(2) + motive(1) + minor(1) + major(1) → return
    // Peel past params (A, B) and motive to get to the minor premise domain.
    let mut ty = rec_val.type_.clone();
    let mut pi_count = 0;
    // Skip 3 Pi binders: A, B, motive
    while pi_count < 3 {
        match ty.kind() {
            ExprKind::Pi(_, _, body) => {
                ty = (**body).clone();
                pi_count += 1;
            }
            _ => panic!("expected Pi at position {pi_count}, got: {:?}", ty),
        }
    }

    // Now `ty` = Pi(_, minor_type, ...). Extract minor_type.
    let minor_type = match ty.kind() {
        ExprKind::Pi(_, domain, _) => (**domain).clone(),
        _ => panic!("expected Pi for minor, got: {:?}", ty),
    };

    // minor_type = ∀ (a : A) (f : B a → W A B) (ih : ∀ (x : ???), motive (f x)), ...
    // Peel past (a : A) and (f : B a → W A B) to get to the IH binder.
    let mut mt = minor_type;
    for label in ["a", "f"] {
        match mt.kind() {
            ExprKind::Pi(_, _, body) => mt = (**body).clone(),
            _ => panic!("expected Pi for field '{label}', got: {:?}", mt),
        }
    }

    // Now `mt` = Pi(_, ih_type, ...) where ih_type = ∀ (x : ???), motive (f x)
    let ih_type = match mt.kind() {
        ExprKind::Pi(_, domain, _) => (**domain).clone(),
        _ => panic!("expected Pi for IH, got: {:?}", mt),
    };

    // ih_type = ∀ (x : ???), motive (f x)
    // The domain of this Pi should be B a (an App), NOT Sort(0)/Prop.
    let ih_domain = match ih_type.kind() {
        ExprKind::Pi(_, domain, _) => (**domain).clone(),
        _ => panic!("IH type should be a Pi (∀ x. ...), got: {:?}", ih_type),
    };

    // The IH Pi domain must NOT be a Sort (dummy type).
    assert!(
        !matches!(ih_domain.kind(), ExprKind::Sort(_)),
        "IH Pi domain should be a real type (B a), not a dummy Sort. Got: {:?}",
        ih_domain
    );
    // It should be an App (B applied to a)
    assert!(
        matches!(ih_domain.kind(), ExprKind::App(_, _)),
        "IH Pi domain should be App (B a), got: {:?}",
        ih_domain
    );
}
