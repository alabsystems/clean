// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional equality and structural equality tests

use crate::cert::*;
use crate::env::Environment;
use crate::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, Literal, MDataValue};
use crate::level::Level;
use crate::name::Name;

fn empty_env() -> Environment {
    Environment::new()
}

#[test]
fn test_def_eq_same_expr() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let e = Expr::from_kind(ExprKind::Sort(Level::zero()));
    // Must return true for identical expressions
    assert!(verifier.def_eq(&e, &e));
}

#[test]
fn test_def_eq_different_exprs() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let e1 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let e2 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    // Must return false for different expressions
    assert!(!verifier.def_eq(&e1, &e2));
}

#[test]
fn test_def_eq_beta_reduction() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    // (λ x. x) applied conceptually should reduce
    // But structurally: λ x. x should equal λ x. x
    let lam1 = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::zero())),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let lam2 = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::zero())),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    assert!(verifier.def_eq(&lam1, &lam2));
}

// --- CertVerifier::structural_eq tests ---

#[test]
fn test_structural_eq_fvar() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let fvar1 = Expr::from_kind(ExprKind::FVar(FVarId(1)));
    let fvar2 = Expr::from_kind(ExprKind::FVar(FVarId(1)));
    let fvar3 = Expr::from_kind(ExprKind::FVar(FVarId(2)));
    // Same ID should match, different should not
    assert!(verifier.structural_eq(&fvar1, &fvar2));
    assert!(!verifier.structural_eq(&fvar1, &fvar3));
}

#[test]
fn test_structural_eq_app() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let app1 = Expr::from_kind(ExprKind::App(prop.clone().into(), prop.clone().into()));
    let app2 = Expr::from_kind(ExprKind::App(prop.clone().into(), prop.clone().into()));
    let app3 = Expr::from_kind(ExprKind::App(prop.clone().into(), type1.clone().into()));
    let app4 = Expr::from_kind(ExprKind::App(type1.clone().into(), prop.clone().into()));

    assert!(verifier.structural_eq(&app1, &app2));
    assert!(!verifier.structural_eq(&app1, &app3)); // Different arg
    assert!(!verifier.structural_eq(&app1, &app4)); // Different fn
}

#[test]
fn test_structural_eq_lam() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let lam1 = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let lam2 = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let lam3 = Expr::lam(
        BinderInfo::Implicit,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let lam4 = Expr::lam(
        BinderInfo::Default,
        type1.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let lam5 = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(1)),
    );

    assert!(verifier.structural_eq(&lam1, &lam2));
    // Binder info is irrelevant for definitional equality in CIC.
    // Lean 4's is_def_eq_binding only checks domain + body, not binder annotations.
    assert!(verifier.structural_eq(&lam1, &lam3)); // Different binder info — still equal
    assert!(!verifier.structural_eq(&lam1, &lam4)); // Different type
    assert!(!verifier.structural_eq(&lam1, &lam5)); // Different body
}

#[test]
fn test_structural_eq_pi() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let pi1 = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());
    let pi2 = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());
    let pi3 = Expr::pi(BinderInfo::Implicit, prop.clone(), prop.clone());
    let pi4 = Expr::pi(BinderInfo::Default, type1.clone(), prop.clone());
    let pi5 = Expr::pi(BinderInfo::Default, prop.clone(), type1.clone());

    assert!(verifier.structural_eq(&pi1, &pi2));
    // Binder info irrelevant for definitional equality (same as Lam)
    assert!(verifier.structural_eq(&pi1, &pi3)); // Different binder info — still equal
    assert!(!verifier.structural_eq(&pi1, &pi4)); // Different arg type
    assert!(!verifier.structural_eq(&pi1, &pi5)); // Different body type
}

#[test]
fn test_structural_eq_let() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let let1 = Expr::let_named(
        Name::anon(),
        prop.clone(),
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
        false,
    );
    let let2 = Expr::let_named(
        Name::anon(),
        prop.clone(),
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
        false,
    );
    let let3 = Expr::let_named(
        Name::anon(),
        type1.clone(),
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
        false,
    );
    let let4 = Expr::let_named(
        Name::anon(),
        prop.clone(),
        type1.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
        false,
    );
    let let5 = Expr::let_named(
        Name::anon(),
        prop.clone(),
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(1)),
        false,
    );

    assert!(verifier.structural_eq(&let1, &let2));
    assert!(!verifier.structural_eq(&let1, &let3)); // Different type
    assert!(!verifier.structural_eq(&let1, &let4)); // Different value
    assert!(!verifier.structural_eq(&let1, &let5)); // Different body
}

#[test]
fn test_structural_eq_lit() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);

    let lit1 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let lit2 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let lit3 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(43))));

    assert!(verifier.structural_eq(&lit1, &lit2));
    assert!(!verifier.structural_eq(&lit1, &lit3));
}

#[test]
fn test_structural_eq_proj() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let name1 = Name::from_string("Foo");
    let name2 = Name::from_string("Bar");

    let proj1 = Expr::proj(name1.clone(), 0, prop.clone());
    let proj2 = Expr::proj(name1.clone(), 0, prop.clone());
    let proj3 = Expr::proj(name2.clone(), 0, prop.clone());
    let proj4 = Expr::proj(name1.clone(), 1, prop.clone());
    let proj5 = Expr::proj(
        name1.clone(),
        0,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
    );

    assert!(verifier.structural_eq(&proj1, &proj2));
    assert!(!verifier.structural_eq(&proj1, &proj3)); // Different name
    assert!(!verifier.structural_eq(&proj1, &proj4)); // Different index
    assert!(!verifier.structural_eq(&proj1, &proj5)); // Different expr
}

#[test]
fn test_structural_eq_const() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let name1 = Name::from_string("Foo");
    let name2 = Name::from_string("Bar");

    let const1 = Expr::const_(name1.clone(), vec![Level::zero()]);
    let const2 = Expr::const_(name1.clone(), vec![Level::zero()]);
    let const3 = Expr::const_(name2.clone(), vec![Level::zero()]);
    let const4 = Expr::const_(name1.clone(), vec![Level::succ(Level::zero())]);
    let const5 = Expr::const_(name1.clone(), vec![]);

    assert!(verifier.structural_eq(&const1, &const2));
    assert!(!verifier.structural_eq(&const1, &const3)); // Different name
    assert!(!verifier.structural_eq(&const1, &const4)); // Different level
    assert!(!verifier.structural_eq(&const1, &const5)); // Different arity
}

// --- CertVerifier::level_eq tests ---

#[test]
fn test_level_eq_same() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let l = Level::succ(Level::zero());
    assert!(verifier.level_eq(&l, &l));
}

#[test]
fn test_level_eq_different() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let l1 = Level::zero();
    let l2 = Level::succ(Level::zero());
    assert!(!verifier.level_eq(&l1, &l2));
}

/// Regression test for #2064: level_eq must normalize before comparing.
/// `max(u, v)` and `max(v, u)` are structurally different but semantically equal.
/// The old implementation used `l1 == l2` which would reject this.
#[test]
fn test_level_eq_max_commutativity() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let max_uv = Level::max(u.clone(), v.clone());
    let max_vu = Level::max(v, u);
    assert!(
        verifier.level_eq(&max_uv, &max_vu),
        "level_eq must treat max(u,v) == max(v,u) after normalization"
    );
}

/// Regression test for #2064: `max(u, max(u, v))` should equal `max(u, v)`
/// after normalization (idempotence + flattening).
#[test]
fn test_level_eq_max_idempotent() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let max_uv = Level::max(u.clone(), v.clone());
    let max_u_max_uv = Level::max(u, max_uv.clone());
    assert!(
        verifier.level_eq(&max_u_max_uv, &max_uv),
        "level_eq must treat max(u, max(u,v)) == max(u,v) after normalization"
    );
}

/// Part of #2064: verify level_eq correctly distinguishes imax from max when
/// the second argument is a parameter (not provably nonzero).
/// `imax(u, v) != max(u, v)` because when v=0, imax(u,0)=0 but max(u,0)=u.
/// The smart constructor leaves imax(u, v) unreduced as IMax(u, v), so
/// normalization must NOT conflate it with Max(u, v).
#[test]
fn test_level_eq_imax_not_equal_to_max_with_param() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let imax_uv = Level::imax(u.clone(), v.clone());
    let max_uv = Level::max(u, v);
    assert!(
        !verifier.level_eq(&imax_uv, &max_uv),
        "level_eq must distinguish imax(u,v) from max(u,v) when v is a parameter"
    );
}

/// Part of #2064: verify level_eq handles succ distributed over imax/max.
/// `succ(max(u, v))` should equal `max(succ(u), succ(v))` after normalization.
/// This exercises the offset distribution path in Level::normalize (#1436).
#[test]
fn test_level_eq_succ_distributes_over_max() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let succ_max = Level::succ(Level::max(u.clone(), v.clone()));
    let max_succ = Level::max(Level::succ(u), Level::succ(v));
    assert!(
        verifier.level_eq(&succ_max, &max_succ),
        "level_eq must treat succ(max(u,v)) == max(succ(u), succ(v))"
    );
}

/// Part of #2064: verify level_eq handles deep Succ chains correctly.
/// `succ^10(u)` should NOT equal `succ^11(u)` — tests normalization doesn't
/// incorrectly conflate different offset depths.
#[test]
fn test_level_eq_deep_succ_distinct() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let u = Level::param(Name::from_string("u"));
    let mut succ10 = u.clone();
    for _ in 0..10 {
        succ10 = Level::succ(succ10);
    }
    let mut succ11 = u;
    for _ in 0..11 {
        succ11 = Level::succ(succ11);
    }
    assert!(
        !verifier.level_eq(&succ10, &succ11),
        "level_eq must distinguish succ^10(u) from succ^11(u)"
    );
}

// --- CertVerifier::def_eq eta expansion tests ---

/// Part of #2064: eta expansion makes (λ x. f x) ≡ f.
/// Without this, valid certificates that rely on eta equivalence are rejected.
#[test]
fn test_def_eq_eta_expansion_lam_vs_non_lam() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // f is FVar(42)
    let f = Expr::from_kind(ExprKind::FVar(FVarId(42)));

    // (λ x : Prop. f x) — eta-expanded form
    let f_lifted = f.lift_from(0, 1); // lift f past the binder
    let body = Expr::app(f_lifted, Expr::bvar(0));
    let lam_f_x = Expr::lam(BinderInfo::Default, prop, body);

    assert!(
        verifier.def_eq(&lam_f_x, &f),
        "def_eq must recognize (λ x. f x) ≡ f via eta expansion"
    );
    // Symmetric
    assert!(
        verifier.def_eq(&f, &lam_f_x),
        "def_eq eta expansion must be symmetric"
    );
}

/// Part of #2064: eta expansion should NOT equate lambdas with different bodies.
#[test]
fn test_def_eq_eta_non_eta_not_equal() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let f = Expr::from_kind(ExprKind::FVar(FVarId(42)));
    let g = Expr::from_kind(ExprKind::FVar(FVarId(99)));

    // (λ x : Prop. f x)
    let f_lifted = f.lift_from(0, 1);
    let body = Expr::app(f_lifted, Expr::bvar(0));
    let lam_f_x = Expr::lam(BinderInfo::Default, prop, body);

    // g is different from f
    assert!(
        !verifier.def_eq(&lam_f_x, &g),
        "def_eq must NOT equate (λ x. f x) with g ≠ f"
    );
}

// --- Binder info irrelevance tests (self-audit finding) ---

/// Self-audit of commit 1290: binder info must be irrelevant for def_eq.
/// In CIC and Lean 4, `(λ [x : Prop]. x)` ≡ `(λ {x : Prop}. x)`.
/// Lean 4 reference: type_checker.cpp is_def_eq_binding only checks domain + body.
#[test]
fn test_def_eq_binder_info_irrelevant_lam() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // (λ [x : Prop]. x)  — default binder
    let lam_default = Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0));
    // (λ {x : Prop}. x)  — implicit binder
    let lam_implicit = Expr::lam(BinderInfo::Implicit, prop.clone(), Expr::bvar(0));
    // (λ ⦃x : Prop⦄. x)  — strict implicit binder
    let lam_strict = Expr::lam(BinderInfo::StrictImplicit, prop.clone(), Expr::bvar(0));

    assert!(
        verifier.def_eq(&lam_default, &lam_implicit),
        "def_eq: binder info (Default vs Implicit) must be irrelevant"
    );
    assert!(
        verifier.def_eq(&lam_default, &lam_strict),
        "def_eq: binder info (Default vs StrictImplicit) must be irrelevant"
    );
    assert!(
        verifier.def_eq(&lam_implicit, &lam_strict),
        "def_eq: binder info (Implicit vs StrictImplicit) must be irrelevant"
    );
}

/// Same as above for Pi types: `(x : Prop) → Prop` ≡ `{x : Prop} → Prop`.
#[test]
fn test_def_eq_binder_info_irrelevant_pi() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let pi_default = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());
    let pi_implicit = Expr::pi(BinderInfo::Implicit, prop.clone(), prop.clone());
    let pi_inst_implicit = Expr::pi(BinderInfo::InstImplicit, prop.clone(), prop.clone());

    assert!(
        verifier.def_eq(&pi_default, &pi_implicit),
        "def_eq: Pi binder info (Default vs Implicit) must be irrelevant"
    );
    assert!(
        verifier.def_eq(&pi_default, &pi_inst_implicit),
        "def_eq: Pi binder info (Default vs InstImplicit) must be irrelevant"
    );
}

// --- CertVerifier::whnf MData transparency tests ---

/// Part of #2064: MData wrappers should be transparent to WHNF.
#[test]
fn test_whnf_mdata_transparency() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let metadata = vec![(Name::from_string("tag"), MDataValue::Bool(true))];
    let mdata = Expr::from_kind(ExprKind::MData(metadata, prop.clone().into()));
    let result = verifier.whnf(&mdata);
    assert!(
        verifier.structural_eq(&result, &prop),
        "WHNF must strip MData wrappers"
    );
}

// --- CertVerifier::whnf projection reduction tests ---

/// Part of #2064: projection of a constructor application should reduce.
#[test]
fn test_whnf_proj_reduces_constructor() {
    use crate::inductive::{ConstructorVal, InductiveVal};

    let mut env = empty_env();
    let struct_name = Name::from_string("Prod");
    let ctor_name = Name::from_string("Prod.mk");

    // Register a structure with 2 type params + 2 fields
    env.register_inductive(InductiveVal {
        name: struct_name.clone(),
        level_params: vec![Name::from_string("u"), Name::from_string("v")],
        type_: Expr::from_kind(ExprKind::Sort(Level::zero())),
        num_params: 2,
        num_indices: 0,
        all_names: vec![struct_name.clone()],
        constructor_names: vec![ctor_name.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    });
    env.register_constructor(ConstructorVal {
        name: ctor_name.clone(),
        inductive_name: struct_name.clone(),
        level_params: vec![Name::from_string("u"), Name::from_string("v")],
        type_: Expr::from_kind(ExprKind::Sort(Level::zero())),
        num_params: 2,
        num_fields: 2,
        constructor_idx: 0,
    });

    let param_a = Expr::from_kind(ExprKind::FVar(FVarId(1)));
    let param_b = Expr::from_kind(ExprKind::FVar(FVarId(2)));
    let field_x = Expr::from_kind(ExprKind::FVar(FVarId(10)));
    let field_y = Expr::from_kind(ExprKind::FVar(FVarId(20)));

    // Build: Prod.mk A B x y
    let ctor_app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::const_(ctor_name, vec![]), param_a), param_b),
            field_x.clone(),
        ),
        field_y.clone(),
    );

    let verifier = CertVerifier::new(&env);

    // Prod.mk A B x y . 0 should reduce to x (field at index 0)
    let proj0 = Expr::proj(struct_name.clone(), 0, ctor_app.clone());
    let result0 = verifier.whnf(&proj0);
    assert!(
        verifier.structural_eq(&result0, &field_x),
        "Proj.0 of constructor should reduce to first field"
    );

    // Prod.mk A B x y . 1 should reduce to y (field at index 1)
    let proj1 = Expr::proj(struct_name, 1, ctor_app);
    let result1 = verifier.whnf(&proj1);
    assert!(
        verifier.structural_eq(&result1, &field_y),
        "Proj.1 of constructor should reduce to second field"
    );
}

// --- def_eq_impl subterm reduction tests (#2478) ---

/// Regression test for #2478: def_eq_impl must recurse with def_eq_impl on
/// subterms, not structural_eq_impl. Before the fix, Pi/Lam/Let/App subterms
/// were compared without WHNF, so nested let-expressions (which need zeta
/// reduction) caused false negatives.
#[test]
fn test_def_eq_pi_domain_needs_zeta_reduction() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Domain 1: `let x := Prop in x` — reduces to Prop via zeta
    let let_prop = Expr::let_named(
        Name::anon(),
        prop.clone(),
        prop.clone(),
        Expr::bvar(0),
        false,
    );

    // Pi(_, let x := Prop in x, Prop) vs Pi(_, Prop, Prop)
    // These are definitionally equal because the domain reduces via zeta.
    let pi_with_let = Expr::pi(BinderInfo::Default, let_prop, prop.clone());
    let pi_direct = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    assert!(
        verifier.def_eq(&pi_with_let, &pi_direct),
        "def_eq must handle Pi domains that need zeta reduction (#2478)"
    );
    // Symmetric
    assert!(
        verifier.def_eq(&pi_direct, &pi_with_let),
        "def_eq Pi domain zeta reduction must be symmetric (#2478)"
    );
}

/// Regression test for #2478: App arguments that are only def-eq after WHNF.
#[test]
fn test_def_eq_app_arg_needs_beta_reduction() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let f = Expr::from_kind(ExprKind::FVar(FVarId(1)));

    // arg 1: (λ x : Prop. x) Prop — beta-reduces to Prop
    let id_lam = Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0));
    let beta_redex = Expr::app(id_lam, prop.clone());

    // App(f, (λ x. x) Prop) vs App(f, Prop)
    let app_with_redex = Expr::app(f.clone(), beta_redex);
    let app_direct = Expr::app(f, prop);

    assert!(
        verifier.def_eq(&app_with_redex, &app_direct),
        "def_eq must handle App arguments that need beta reduction (#2478)"
    );
}

/// Regression test for #2478: Lam body subterms need semantic comparison.
#[test]
fn test_def_eq_lam_body_needs_reduction() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Body 1: let y := BVar(0) in y — reduces to BVar(0) via zeta
    let let_body = Expr::let_named(
        Name::anon(),
        prop.clone(),
        Expr::bvar(0),
        Expr::bvar(0),
        false,
    );

    // λ (x : Prop). (let y := x in y) vs λ (x : Prop). x
    let lam_with_let = Expr::lam(BinderInfo::Default, prop.clone(), let_body);
    let lam_direct = Expr::lam(BinderInfo::Default, prop, Expr::bvar(0));

    assert!(
        verifier.def_eq(&lam_with_let, &lam_direct),
        "def_eq must handle Lam bodies that need zeta reduction (#2478)"
    );
}

// --- CertVerifier::whnf tests ---
