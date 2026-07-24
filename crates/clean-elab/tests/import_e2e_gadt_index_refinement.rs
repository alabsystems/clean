// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: GADT-style **index refinement** in a `match` on an *imported*
//! indexed inductive family (gadt_index_refinement scenario).
//!
//! ## The family
//!
//! ```text
//! inductive Ty   | Ty.nat | Ty.bool
//! inductive GExpr : Ty -> Type
//!   | litNat  : Nat  -> GExpr Ty.nat
//!   | litBool : Bool -> GExpr Ty.bool
//! ```
//!
//! `GExpr` is a typed-expression GADT: each constructor *fixes its own index*
//! to a concrete `Ty` value. A value of `GExpr Ty.nat` can therefore only have
//! been built by `litNat` — the `litBool` constructor is **impossible** for that
//! index, because its return index `Ty.bool` can never unify with `Ty.nat`.
//!
//! ## Index refinement (the GADT discipline)
//!
//! When the scrutinee's index is a *concrete constructor value* (here `Ty.nat`),
//! a refined `match` may legitimately **omit** the arms for the impossible
//! constructors:
//!
//! ```text
//! def evalNat (e : GExpr Ty.nat) : Nat := match e with
//!   | GExpr.litNat n => n        -- the only reachable constructor
//! ```
//!
//! Lean's elaborator refines each constructor's index against the scrutinee's
//! index, discards the `litBool` arm as impossible, and still supplies the
//! eliminator with a (dead, unreachable) minor for `litBool` so the underlying
//! `casesOn` stays fully applied.
//!
//! ## The imported eliminator layout (MajorAfterMotive)
//!
//! A real Lean `.olean` ships the recursor `GExpr.rec` plus a **definitional**
//! `GExpr.casesOn` in the `MajorAfterMotive` layout, and does NOT register
//! `GExpr.casesOn` as a recursor:
//!
//! ```text
//! GExpr.casesOn.{u} :
//!   {motive : (t : Ty) -> GExpr t -> Sort u}
//!     -> (t : Ty)                                   -- index
//!     -> (e : GExpr t)                              -- major (after motive+index)
//!     -> ((n : Nat)  -> motive Ty.nat  (GExpr.litNat  n))   -- minor: litNat
//!     -> ((b : Bool) -> motive Ty.bool (GExpr.litBool b))   -- minor: litBool
//!     -> motive t e
//!   := fun motive t e m_nat m_bool => GExpr.rec motive m_nat m_bool t e
//! ```
//!
//! ## Synthesize-as-import (mirrors `import_e2e_indexed_family_recursor.rs`)
//!
//! We let the kernel build the genuine `GExpr` family + constructors +
//! `GExpr.rec` in a scratch env, copy those verbatim into a fresh env, and
//! synthesize `GExpr.casesOn` as a plain `Declaration::Definition` in the Lean
//! `MajorAfterMotive` layout (kernel-checked via `add_decl_structural`). The
//! result is bit-identical to a real `.olean` member: `GExpr.rec` is a recursor,
//! but `get_recursor("GExpr.casesOn") == None`. We assert that precondition so
//! the test stays honest about exercising the import path.
//!
//! ## The bug this pins (fixed in this change)
//!
//! Before the fix, a refined GADT `match` that *omits the impossible arm* failed
//! to elaborate: the match lowering produced one minor per *written arm*, so the
//! omitted `litBool` minor slot was left empty and the next eliminator argument
//! (the index / major premise) slid into the `litBool` minor position. The
//! kernel then rejected the application with a type mismatch (the index value
//! `Ty` where a `(b : Bool) -> motive …` minor was expected) — a **spurious type
//! error on a legal refined match**. This affected *both* the native and the
//! imported eliminator paths (they share the constructor-ordered minor builder),
//! since the impossible-branch shape only arises for an indexed family matched
//! at a concrete index.
//!
//! The fix (`ctor_order.rs`) detects an *index-impossible* constructor — one
//! whose ground return index is definitionally distinct from the scrutinee's
//! ground index — and synthesizes the missing (dead-code) minor from a genuine
//! default value of the branch type. It is conservative: when either index is
//! non-ground (a *variable* index), the constructor is treated as possible and a
//! genuinely non-exhaustive match is still rejected — so a reachable branch is
//! never silently fabricated. The synthesized minor is axiom-free (a real
//! nullary constructor of the branch type), never a `sorry`.
//!
//! This file drives `match` lowering through both the imported
//! `MajorAfterMotive` `GExpr.casesOn` and the native recursor, kernel-checks the
//! results, and asserts reductions with *distinct* witnesses so a wrong branch /
//! a mis-placed minor / a wrongly-dropped reachable arm surfaces as a different
//! observable result rather than passing silently.

use clean_kernel::env::Declaration;
use clean_kernel::env::Environment;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `GExpr t` (the family applied to its single index).
fn gexpr_at(t: Expr) -> Expr {
    Expr::app(const_("GExpr"), t)
}

fn litnat(n: Expr) -> Expr {
    Expr::app(const_("GExpr.litNat"), n)
}

fn litbool(b: Expr) -> Expr {
    Expr::app(const_("GExpr.litBool"), b)
}

/// `Nat.succ^k Nat.zero`.
fn nat_lit(k: u32) -> Expr {
    let mut e = const_("Nat.zero");
    for _ in 0..k {
        e = Expr::app(const_("Nat.succ"), e);
    }
    e
}

/// Reduce `expr` to weak-head normal form and return its head `Const` name.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn debug_head(env: &Environment, e: &Expr) -> String {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(e);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(n, _) => n.to_string(),
        other => format!("{other:?}"),
    }
}

/// `Ty : Type` with nullary constructors `Ty.nat`, `Ty.bool`.
fn ty_decl() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Ty"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Ty.nat"),
                    type_: const_("Ty"),
                },
                Constructor {
                    name: Name::from_string("Ty.bool"),
                    type_: const_("Ty"),
                },
            ],
        }],
    }
}

/// `GExpr : Ty -> Type` with `litNat : Nat -> GExpr Ty.nat` and
/// `litBool : Bool -> GExpr Ty.bool`. Each constructor fixes its own index.
fn gexpr_decl() -> InductiveDecl {
    let expr_ty = Expr::pi(BinderInfo::Default, const_("Ty"), Expr::type_());
    // litNat : Nat -> GExpr Ty.nat
    let litnat_ty = Expr::pi(
        BinderInfo::Default,
        const_("Nat"),
        gexpr_at(const_("Ty.nat")),
    );
    // litBool : Bool -> GExpr Ty.bool
    let litbool_ty = Expr::pi(
        BinderInfo::Default,
        const_("Bool"),
        gexpr_at(const_("Ty.bool")),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("GExpr"),
            type_: expr_ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("GExpr.litNat"),
                    type_: litnat_ty,
                },
                Constructor {
                    name: Name::from_string("GExpr.litBool"),
                    type_: litbool_ty,
                },
            ],
        }],
    }
}

/// The imported `MajorAfterMotive` `GExpr.casesOn` **type** (see module doc).
fn imported_cases_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    // motive : (t : Ty) -> GExpr t -> Sort u
    let motive_dom = {
        let inner = Expr::pi(BinderInfo::Default, gexpr_at(Expr::bvar(0)), sort_u);
        Expr::pi(BinderInfo::Default, const_("Ty"), inner)
    };
    // result `motive t e` under [motive, t, e, m_nat, m_bool]: motive=4, t=3, e=2
    let result = Expr::app(Expr::app(Expr::bvar(4), Expr::bvar(3)), Expr::bvar(2));
    // m_bool : (b : Bool) -> motive Ty.bool (litBool b)
    //   under [motive, t, e, m_nat, b]: motive=4, b=0
    let m_bool_body = Expr::app(
        Expr::app(Expr::bvar(4), const_("Ty.bool")),
        litbool(Expr::bvar(0)),
    );
    let m_bool_dom = Expr::pi(BinderInfo::Default, const_("Bool"), m_bool_body);
    // m_nat : (n : Nat) -> motive Ty.nat (litNat n)
    //   under [motive, t, e, n]: motive=3, n=0
    let m_nat_body = Expr::app(
        Expr::app(Expr::bvar(3), const_("Ty.nat")),
        litnat(Expr::bvar(0)),
    );
    let m_nat_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_nat_body);
    // e : GExpr t   under [motive, t]: t = BVar0
    let e_dom = gexpr_at(Expr::bvar(0));
    let t_dom = const_("Ty");

    let body = Expr::pi(BinderInfo::Default, m_bool_dom, result);
    let body = Expr::pi(BinderInfo::Default, m_nat_dom, body);
    let body = Expr::pi(BinderInfo::Default, e_dom, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    Expr::pi(BinderInfo::Implicit, motive_dom, body)
}

/// The imported `GExpr.casesOn` **value**, unfolding to `GExpr.rec`:
///
/// ```text
/// fun motive t e m_nat m_bool => GExpr.rec motive m_nat m_bool t e
/// ```
fn imported_cases_value(u: &Name) -> Expr {
    let rec = Expr::const_(
        Name::from_string("GExpr.rec"),
        vec![Level::param(u.clone())],
    );
    let sort_u = Expr::sort(Level::param(u.clone()));

    // body under lambdas [motive, t, e, m_nat, m_bool], innermost-first de Bruijn:
    //   motive=4, t=3, e=2, m_nat=1, m_bool=0
    let body = Expr::app(rec, Expr::bvar(4)); // motive
    let body = Expr::app(body, Expr::bvar(1)); // m_nat minor
    let body = Expr::app(body, Expr::bvar(0)); // m_bool minor
    let body = Expr::app(body, Expr::bvar(3)); // index t
    let body = Expr::app(body, Expr::bvar(2)); // major e

    // Matching lambda telescope (same binder domains as the type).
    let motive_dom = {
        let inner = Expr::pi(BinderInfo::Default, gexpr_at(Expr::bvar(0)), sort_u);
        Expr::pi(BinderInfo::Default, const_("Ty"), inner)
    };
    let m_bool_body = Expr::app(
        Expr::app(Expr::bvar(4), const_("Ty.bool")),
        litbool(Expr::bvar(0)),
    );
    let m_bool_dom = Expr::pi(BinderInfo::Default, const_("Bool"), m_bool_body);
    let m_nat_body = Expr::app(
        Expr::app(Expr::bvar(3), const_("Ty.nat")),
        litnat(Expr::bvar(0)),
    );
    let m_nat_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_nat_body);
    let e_dom = gexpr_at(Expr::bvar(0));
    let t_dom = const_("Ty");

    let body = Expr::lam(BinderInfo::Default, m_bool_dom, body);
    let body = Expr::lam(BinderInfo::Default, m_nat_dom, body);
    let body = Expr::lam(BinderInfo::Default, e_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    Expr::lam(BinderInfo::Implicit, motive_dom, body)
}

/// Copy the kernel-built `GExpr` family / constructors / `GExpr.rec` from a
/// scratch env into `env`, mirroring an `.olean` load.
fn copy_gexpr_core(native: &Environment, env: &mut Environment) {
    let gexpr = native
        .get_inductive(&Name::from_string("GExpr"))
        .cloned()
        .expect("scratch env has GExpr");
    env.register_inductive(gexpr);
    for ctor in ["GExpr.litNat", "GExpr.litBool"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }
    let rv = native
        .get_recursor(&Name::from_string("GExpr.rec"))
        .cloned()
        .expect("GExpr.rec recursor");
    let rc = native
        .get_const(&Name::from_string("GExpr.rec"))
        .cloned()
        .expect("GExpr.rec const");
    env.extend_constants_unchecked(std::iter::once(rc));
    env.register_recursor(rv);
}

/// Build an environment holding a *faithfully imported* `GExpr`: the real
/// kernel-built family + constructors + `GExpr.rec`, but `GExpr.casesOn` as a
/// plain `Declaration::Definition` (so `get_recursor("GExpr.casesOn") == None`).
///
/// `Ty` is a plain (non-indexed) inductive declared natively in both envs — it
/// is only used to *form* the concrete indices, never matched on here.
fn imported_gexpr_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native.init_bool().expect("init_bool");
    native.add_inductive(ty_decl()).expect("Ty should declare");
    native
        .add_inductive(gexpr_decl())
        .expect("GExpr should declare");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_bool().expect("init_bool");
    env.add_inductive(ty_decl()).expect("Ty should declare");
    copy_gexpr_core(&native, &mut env);

    let u = native
        .get_recursor(&Name::from_string("GExpr.rec"))
        .and_then(|r| r.level_params.first().cloned())
        .expect("GExpr.rec has a motive universe parameter");

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body, kernel
    // type-checked by `add_decl_structural` against the casesOn type. This
    // reproduces exactly what an `.olean` import of an indexed-family member
    // ships (recursor present, `.casesOn` a definitional constant, no
    // clean-side recursor registration). No production path is involved.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("GExpr.casesOn"),
        level_params: vec![u.clone()],
        type_: imported_cases_type(&u),
        value: imported_cases_value(&u),
        is_reducible: false,
    })
    .expect("imported GExpr.casesOn definition should kernel-check");

    env
}

/// Native env where `GExpr.casesOn` IS a registered recursor (MajorAfterMinors).
fn native_gexpr_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_bool().expect("init_bool");
    env.add_inductive(ty_decl()).expect("Ty should declare");
    env.add_inductive(gexpr_decl())
        .expect("GExpr should declare");
    env
}

fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

/// Try elaborating `source`, returning the first declaration error (if any).
fn try_elaborate_decls(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Precondition: the synthesized env is genuinely the *import* configuration —
// indexed family + recursor present, `.casesOn` a definitional constant.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_gexpr_is_indexed_gadt_with_cases_on_definition_not_recursor() {
    let env = imported_gexpr_env();

    let ind = env
        .get_inductive(&Name::from_string("GExpr"))
        .expect("GExpr inductive should be imported");
    assert_eq!(
        ind.num_indices, 1,
        "GExpr is an indexed family: exactly one index (the Ty tag)"
    );
    assert_eq!(ind.num_params, 0, "GExpr has no parameters, only the index");

    // Each constructor fixes its own concrete index — the GADT discipline.
    let litnat = env
        .get_constructor(&Name::from_string("GExpr.litNat"))
        .expect("GExpr.litNat ctor");
    assert_eq!(litnat.num_fields, 1, "litNat has one Nat field");
    let litbool = env
        .get_constructor(&Name::from_string("GExpr.litBool"))
        .expect("GExpr.litBool ctor");
    assert_eq!(litbool.num_fields, 1, "litBool has one Bool field");

    // GExpr.rec is a genuine recursor; GExpr.casesOn is a definitional constant
    // (NOT a registered recursor) — this routes the match elaborator through the
    // imported MajorAfterMotive path.
    assert!(
        env.get_recursor(&Name::from_string("GExpr.rec")).is_some(),
        "GExpr.rec must be a registered recursor"
    );
    assert!(
        env.get_recursor(&Name::from_string("GExpr.casesOn"))
            .is_none(),
        "imported GExpr.casesOn must NOT be a registered recursor"
    );
    let cases = env
        .get_const(&Name::from_string("GExpr.casesOn"))
        .expect("GExpr.casesOn const");
    assert!(
        cases.value.is_some(),
        "imported GExpr.casesOn must be a definitional constant with a value"
    );
}

// ---------------------------------------------------------------------------
// Control: the imported `MajorAfterMotive` `GExpr.casesOn` reduces correctly
// when applied by hand (BOTH minors supplied). Isolates any later match-test
// failure to the *elaborator's* lowering rather than the kernel's reduction of
// the imported casesOn / the synthesized definition itself.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_gadt_cases_on_kernel_reduction_is_correct() {
    let env = imported_gexpr_env();

    // motive := fun (_ : Ty) (_ : GExpr _) => Nat
    let motive = Expr::lam(
        BinderInfo::Default,
        const_("Ty"),
        Expr::lam(BinderInfo::Default, gexpr_at(Expr::bvar(0)), const_("Nat")),
    );
    // m_nat := fun (n : Nat) => n   (return the Nat field)
    let m_nat = Expr::lam(BinderInfo::Default, const_("Nat"), Expr::bvar(0));
    // m_bool := fun (_ : Bool) => Nat.zero
    let m_bool = Expr::lam(BinderInfo::Default, const_("Bool"), const_("Nat.zero"));
    let cases = Expr::const_(Name::from_string("GExpr.casesOn"), vec![Level::zero()]);

    // litNat branch: casesOn motive Ty.nat (litNat 4) m_nat m_bool -> 4
    let four = nat_lit(4);
    let app = Expr::app(cases, motive);
    let app = Expr::app(app, const_("Ty.nat")); // index
    let app = Expr::app(app, litnat(four.clone())); // major (MajorAfterMotive)
    let app = Expr::app(app, m_nat);
    let app = Expr::app(app, m_bool);
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&app, &four),
        "imported GExpr.casesOn on litNat must select m_nat and bind the Nat field (4); got head {}",
        debug_head(&env, &app)
    );
    assert!(
        !tc.is_def_eq(&app, &const_("Nat.zero")),
        "the litNat branch must NOT collapse to the m_bool default (0)"
    );
}

// ---------------------------------------------------------------------------
// MAIN PROBE (import path): a refined GADT `match` on `GExpr Ty.nat` that
// *omits the impossible `litBool` arm* must lower through the imported
// `MajorAfterMotive` `GExpr.casesOn` (synthesizing the dead `litBool` minor),
// kernel-check, and reduce to the genuinely correct branch / field.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_refined_match_omits_impossible_arm_and_reduces() {
    let mut env = imported_gexpr_env();

    // Only `litNat` is reachable for `GExpr Ty.nat`; the `litBool` arm is
    // legitimately omitted. Before the fix this failed to elaborate (the index
    // premise slid into the missing litBool minor slot, a spurious type error).
    elaborate_decls_into(
        &mut env,
        "def evalNatI (e : GExpr Ty.nat) : Nat := match e with\n  \
         | GExpr.litNat n => n",
    );

    // Confirm the body compiled through the imported `GExpr.casesOn`.
    let info = env
        .get_const(&Name::from_string("evalNatI"))
        .expect("evalNatI should be registered");
    let body = info.value.as_ref().expect("evalNatI is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("GExpr.casesOn")),
        "evalNatI must compile through the imported GExpr.casesOn, got: {:?}",
        body.collect_constants()
    );

    // evalNatI (litNat 7) -> 7 (the bound Nat field of the reachable branch).
    let seven = nat_lit(7);
    let call = Expr::app(const_("evalNatI"), litnat(seven.clone()));
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&call, &seven),
        "evalNatI (litNat 7) must reduce to the bound field (7); got head {}",
        debug_head(&env, &call)
    );
    // Distinct from the impossible branch's synthesized default (Nat.zero): a
    // mis-routed minor or a wrong major slot would surface here.
    assert!(
        !tc.is_def_eq(&call, &const_("Nat.zero")),
        "the reachable litNat branch must NOT collapse to the dead-branch default (0)"
    );
}

// ---------------------------------------------------------------------------
// Distinct-index probe (import path): the *other* refinement direction. A match
// on `GExpr Ty.bool` omitting the now-impossible `litNat` arm must elaborate and
// reduce, proving the impossibility check is index-symmetric (it refines against
// whichever concrete index the scrutinee carries, not a hard-coded constructor).
// ---------------------------------------------------------------------------

#[test]
fn test_imported_refined_match_other_index_direction() {
    let mut env = imported_gexpr_env();

    // Only `litBool` is reachable for `GExpr Ty.bool`; omit `litNat`.
    elaborate_decls_into(
        &mut env,
        "def toNatB (e : GExpr Ty.bool) : Nat := match e with\n  \
         | GExpr.litBool b => Nat.succ Nat.zero",
    );

    let info = env
        .get_const(&Name::from_string("toNatB"))
        .expect("toNatB should be registered");
    let body = info.value.as_ref().expect("toNatB is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("GExpr.casesOn")),
        "toNatB must compile through the imported GExpr.casesOn"
    );

    // toNatB (litBool true) -> 1 (the body), distinct from the litNat dead
    // branch's default (Nat.zero).
    let call = Expr::app(const_("toNatB"), litbool(const_("Bool.true")));
    let tc = TypeChecker::new(&env);
    let one = nat_lit(1);
    assert!(
        tc.is_def_eq(&call, &one),
        "toNatB (litBool true) must reduce to 1; got head {}",
        debug_head(&env, &call)
    );
    assert!(
        !tc.is_def_eq(&call, &const_("Nat.zero")),
        "the reachable litBool branch must NOT collapse to the litNat dead-branch default (0)"
    );
}

// ---------------------------------------------------------------------------
// SOUNDNESS GUARD: the fix must only fill *impossible* (index-incompatible)
// branches — never a genuinely reachable one. A match on `GExpr t` for a
// *variable* index `t` that omits a reachable constructor must STILL be rejected
// (non-exhaustive). If the fix over-eagerly synthesized minors for variable
// indices, this would wrongly elaborate and silently drop the `litBool` case.
// ---------------------------------------------------------------------------

#[test]
fn test_variable_index_omitting_reachable_arm_is_still_rejected() {
    let mut env = imported_gexpr_env();

    // `t` is a variable index, so BOTH litNat and litBool are reachable. Omitting
    // `litBool` is a genuine non-exhaustive match — it must NOT elaborate.
    let result = try_elaborate_decls(
        &mut env,
        "def szVar (t : Ty) (e : GExpr t) : Nat := match e with\n  \
         | GExpr.litNat n => n",
    );
    assert!(
        result.is_err(),
        "a variable-index match that omits a reachable constructor must be rejected, \
         not silently filled (the fix must only discard provably-impossible branches)"
    );
    assert!(
        env.get_const(&Name::from_string("szVar")).is_none(),
        "szVar must not have been registered after a rejected elaboration"
    );
}

// ---------------------------------------------------------------------------
// Exhaustive control (import path): writing BOTH arms at the variable index
// still elaborates and reduces on each constructor to distinct values — the
// pre-existing indexed-family handling is unchanged by the fix.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_exhaustive_variable_index_match_reduces() {
    let mut env = imported_gexpr_env();

    elaborate_decls_into(
        &mut env,
        "def tagOf (t : Ty) (e : GExpr t) : Nat := match e with\n  \
         | GExpr.litNat n => n\n  \
         | GExpr.litBool b => Nat.zero",
    );

    let body = env
        .get_const(&Name::from_string("tagOf"))
        .and_then(|i| i.value.clone())
        .expect("tagOf should be registered");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("GExpr.casesOn")),
        "tagOf must compile through the imported GExpr.casesOn"
    );

    let tc = TypeChecker::new(&env);
    // litNat branch returns the field; litBool branch returns 0 — distinct.
    let nat_call = Expr::app(
        Expr::app(const_("tagOf"), const_("Ty.nat")),
        litnat(nat_lit(5)),
    );
    assert!(
        tc.is_def_eq(&nat_call, &nat_lit(5)),
        "tagOf Ty.nat (litNat 5) must reduce to 5; got head {}",
        debug_head(&env, &nat_call)
    );
    let bool_call = Expr::app(
        Expr::app(const_("tagOf"), const_("Ty.bool")),
        litbool(const_("Bool.false")),
    );
    assert_eq!(
        whnf_head_const(&env, &bool_call).as_deref(),
        Some("Nat.zero"),
        "tagOf Ty.bool (litBool false) must reduce to the litBool branch (0)"
    );
}

// ---------------------------------------------------------------------------
// Control: the NATIVE path (GExpr.casesOn IS a registered recursor in the
// `MajorAfterMinors` layout) lowers + reduces the refined GADT match too. Both
// paths share the constructor-ordered minor builder that this change fixed, so
// this isolates any regression to the elaborator rather than the
// imported-eliminator handling, and proves the native eliminator is byte-for-
// byte unchanged for the exhaustive case while the refined case now works.
// ---------------------------------------------------------------------------

#[test]
fn test_native_refined_gadt_match_reduces_correctly() {
    let mut env = native_gexpr_env();

    // Native GExpr.casesOn IS a registered recursor (MajorAfterMinors).
    let rec = env
        .get_recursor(&Name::from_string("GExpr.casesOn"))
        .expect("native GExpr.casesOn should be a registered recursor");
    assert_eq!(
        rec.arg_order,
        clean_kernel::RecursorArgOrder::MajorAfterMinors,
        "native casesOn uses the MajorAfterMinors layout"
    );

    elaborate_decls_into(
        &mut env,
        "def evalNatN (e : GExpr Ty.nat) : Nat := match e with\n  \
         | GExpr.litNat n => n",
    );

    let body = env
        .get_const(&Name::from_string("evalNatN"))
        .and_then(|i| i.value.clone())
        .expect("evalNatN body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("GExpr.casesOn")),
        "native evalNatN lowers through GExpr.casesOn (the registered recursor)"
    );

    let tc = TypeChecker::new(&env);
    let nine = nat_lit(9);
    let call = Expr::app(const_("evalNatN"), litnat(nine.clone()));
    assert!(
        tc.is_def_eq(&call, &nine),
        "native evalNatN (litNat 9) must reduce to the bound field (9); got head {}",
        debug_head(&env, &call)
    );
    assert!(
        !tc.is_def_eq(&call, &const_("Nat.zero")),
        "native reachable litNat branch must NOT collapse to the dead-branch default (0)"
    );
}
