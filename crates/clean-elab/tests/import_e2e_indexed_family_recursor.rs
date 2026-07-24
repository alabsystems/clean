// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: `match` / `casesOn` lowering + kernel iota-reduction on an
//! *imported INDEXED INDUCTIVE FAMILY* (indexed_family_recursor scenario).
//!
//! ## What an indexed family adds over B43/B45/B47
//!
//! B45 (`import_e2e_param_recursor_tests`) covered a single *parameterized*
//! inductive; B47 (`import_e2e_mutual_recursor`) covered a *mutual* block. This
//! probe targets an inductive **family indexed by a runtime value** —
//!
//! ```text
//! inductive IVec : Nat -> Type
//!   | inil  : IVec Nat.zero
//!   | icons : (n : Nat) -> (head : Nat) -> (tail : IVec n) -> IVec (Nat.succ n)
//! ```
//!
//! — where (a) the motive and minors carry the **index** `n`, (b) the major
//! premise sits *after* the index in the imported eliminator, and crucially
//! (c) the `icons` constructor has a **dependent field**: `tail : IVec n`
//! references the earlier field `n`. The kernel builds `IVec.rec` /
//! `IVec.casesOn` so the motive is `(n : Nat) -> IVec n -> Sort u` and the
//! `icons` minor binds `n`, `head`, `tail`.
//!
//! ## The imported eliminator layout (MajorAfterMotive)
//!
//! A real Lean `.olean` ships the *recursor* `IVec.rec` plus a **definitional**
//! `IVec.casesOn` constant in the `MajorAfterMotive` layout — and does *not*
//! register `IVec.casesOn` as a recursor:
//!
//! ```text
//! IVec.casesOn.{u} :
//!   {motive : (n : Nat) -> IVec n -> Sort u}
//!     -> (n : Nat)                                       -- index
//!     -> (t : IVec n)                                    -- major (after motive+index)
//!     -> motive Nat.zero IVec.inil                       -- minor: inil
//!     -> ((m : Nat) -> (h : Nat) -> (tl : IVec m)
//!            -> motive (Nat.succ m) (IVec.icons m h tl)) -- minor: icons (NO IH)
//!     -> motive n t
//!   := fun motive n t m_inil m_icons =>
//!        IVec.rec motive m_inil
//!          (fun m h tl _ih => m_icons m h tl)            -- drop the rec's IH
//!          n t
//! ```
//!
//! ## Synthesize-as-import (mirrors B47 exactly)
//!
//! We let the kernel build the genuine `IVec` family + constructors +
//! `IVec.rec` in a scratch env, copy those verbatim into a fresh env, and then
//! synthesize `IVec.casesOn` as a plain `Declaration::Definition` in the Lean
//! `MajorAfterMotive` layout (kernel-checked via `add_decl_structural`). The
//! result is bit-identical to a real `.olean` member: `IVec.rec` is a recursor,
//! but `get_recursor("IVec.casesOn") == None`. We assert that precondition so
//! the test stays honest about exercising the import path.
//!
//! ## The bug this pins (fixed in this change)
//!
//! `compute_ctor_field_types` returns each field's type relative to the
//! constructor's Pi *telescope*: the `icons` `tail` field comes back as
//! `IVec (BVar 1)` (the loose `BVar 1` naming the sibling field `n`). The match
//! arm elaborator bound each field as an independent `FVar` and then
//! re-abstracted them one at a time; `abstract_fvar` lifts loose `BVar`s, so the
//! sibling reference drifted from `BVar 1` to `BVar 3` — an out-of-scope index
//! that the kernel rejected with `UnboundVariable`. (This affected *both* the
//! native and imported eliminator paths, since they share the field-binding
//! loop — the dependent-field shape simply never arose for non-indexed
//! inductives where field types are closed.) The fix opens each dependent field
//! type against the preceding fields' `FVar`s before binding it, so the
//! sibling reference is an `FVar` that `abstract_fvar` rewrites to the right
//! `BVar`. This file drives `match` lowering through the imported
//! `MajorAfterMotive` `IVec.casesOn`, kernel-checks it, and asserts the reduced
//! value with *distinct* witnesses so a wrong branch / wrong index slot / wrong
//! field binding surfaces as a different observable result rather than passing
//! silently. A native control isolates any regression to the elaborator.

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

/// `IVec.icons n head tail`.
fn icons(n: Expr, head: Expr, tail: Expr) -> Expr {
    Expr::app(Expr::app(Expr::app(const_("IVec.icons"), n), head), tail)
}

fn succ(n: Expr) -> Expr {
    Expr::app(const_("Nat.succ"), n)
}

/// `IVec n` (the family applied to a single index).
fn ivec_at(n: Expr) -> Expr {
    Expr::app(const_("IVec"), n)
}

/// Reduce `expr` to weak-head normal form and return its head `Const` name
/// (handles both bare constants and constructor applications).
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

/// Build the `IVec : Nat -> Type` indexed family.
///
/// `inil : IVec Nat.zero` and
/// `icons : (n : Nat) -> (head : Nat) -> (tail : IVec n) -> IVec (Nat.succ n)`.
/// `tail`'s type depends on the earlier field `n` — the dependent-field shape
/// that exercises the fix.
fn ivec_decl() -> InductiveDecl {
    // IVec : Nat -> Type
    let ivec_ty = Expr::pi(BinderInfo::Default, const_("Nat"), Expr::type_());
    // inil : IVec Nat.zero
    let inil_ty = ivec_at(const_("Nat.zero"));
    // icons : (n : Nat) -> (head : Nat) -> (tail : IVec n) -> IVec (Nat.succ n)
    //   Under binders [n, head]: n = BVar(1). Under [n, head, tail]: n = BVar(2).
    let icons_ret = ivec_at(succ(Expr::bvar(2))); // IVec (Nat.succ n)
    let tail_ty = ivec_at(Expr::bvar(1)); // IVec n  (n = BVar(1) under [n, head])
    let icons_ty = Expr::pi(BinderInfo::Default, tail_ty, icons_ret); // tail
    let icons_ty = Expr::pi(BinderInfo::Default, const_("Nat"), icons_ty); // head
    let icons_ty = Expr::pi(BinderInfo::Default, const_("Nat"), icons_ty); // n

    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("IVec"),
            type_: ivec_ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("IVec.inil"),
                    type_: inil_ty,
                },
                Constructor {
                    name: Name::from_string("IVec.icons"),
                    type_: icons_ty,
                },
            ],
        }],
    }
}

/// The imported `MajorAfterMotive` `IVec.casesOn` **type**:
///
/// ```text
/// {motive : (n : Nat) -> IVec n -> Sort u}
///   -> (n : Nat) -> (t : IVec n)
///   -> motive Nat.zero IVec.inil
///   -> ((m : Nat) -> (h : Nat) -> (tl : IVec m)
///         -> motive (Nat.succ m) (IVec.icons m h tl))
///   -> motive n t
/// ```
fn imported_cases_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    // motive domain: (n : Nat) -> IVec n -> Sort u
    let motive_dom = {
        let inner = Expr::pi(BinderInfo::Default, ivec_at(Expr::bvar(0)), sort_u.clone());
        Expr::pi(BinderInfo::Default, const_("Nat"), inner)
    };

    // result `motive n t` under [motive, n, t, m_inil, m_icons]: motive=4, n=3, t=2
    let result = Expr::app(Expr::app(Expr::bvar(4), Expr::bvar(3)), Expr::bvar(2));

    // m_icons domain (under [motive, n, t, m_inil]):
    //   (m : Nat) -> (h : Nat) -> (tl : IVec m) -> motive (succ m) (icons m h tl)
    //   inside tl scope [motive, n, t, m_inil, m, h, tl]: motive=6, m=2, h=1, tl=0
    let icons_body = Expr::app(
        Expr::app(Expr::bvar(6), succ(Expr::bvar(2))),
        icons(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
    );
    let m_icons_dom = Expr::pi(BinderInfo::Default, ivec_at(Expr::bvar(1)), icons_body); // tl : IVec m (m = BVar1 under [.,m,h])
    let m_icons_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_icons_dom); // h
    let m_icons_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_icons_dom); // m

    // m_inil domain under [motive, n, t]: motive Nat.zero IVec.inil (motive = 2)
    let m_inil_dom = Expr::app(
        Expr::app(Expr::bvar(2), const_("Nat.zero")),
        const_("IVec.inil"),
    );

    // t domain under [motive, n]: IVec n (n = BVar0)
    let t_dom = ivec_at(Expr::bvar(0));
    let n_dom = const_("Nat");

    let body = Expr::pi(BinderInfo::Default, m_icons_dom, result);
    let body = Expr::pi(BinderInfo::Default, m_inil_dom, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    let body = Expr::pi(BinderInfo::Default, n_dom, body);
    Expr::pi(BinderInfo::Implicit, motive_dom, body)
}

/// The imported `IVec.casesOn` **value**, unfolding to `IVec.rec`:
///
/// ```text
/// fun motive n t m_inil m_icons =>
///   IVec.rec motive m_inil (fun m h tl _ih => m_icons m h tl) n t
/// ```
///
/// `IVec.rec` uses the `MajorAfterMinors` layout and its `icons` minor carries
/// an extra induction-hypothesis binder (`_ih : motive m tl`) that `casesOn`
/// absorbs — exactly how Lean derives `casesOn` from `rec`.
fn imported_cases_value(u: &Name) -> Expr {
    let rec = Expr::const_(Name::from_string("IVec.rec"), vec![Level::param(u.clone())]);
    let sort_u = Expr::sort(Level::param(u.clone()));

    // icons rec-minor: fun (m : Nat) (h : Nat) (tl : IVec m) (_ih : motive m tl) => m_icons m h tl
    //   scope [motive, n, t, m_inil, m_icons, m, h, tl, ih]: m_icons=4, m=3, h=2, tl=1
    let minor_body = Expr::app(
        Expr::app(Expr::app(Expr::bvar(4), Expr::bvar(3)), Expr::bvar(2)),
        Expr::bvar(1),
    );
    // ih domain `motive m tl`: scope [motive, n, t, m_inil, m_icons, m, h, tl]: motive=7, m=2, tl=0
    let ih_dom = Expr::app(Expr::app(Expr::bvar(7), Expr::bvar(2)), Expr::bvar(0));
    let minor = Expr::lam(BinderInfo::Default, ih_dom, minor_body);
    let minor = Expr::lam(BinderInfo::Default, ivec_at(Expr::bvar(1)), minor); // tl : IVec m (m = BVar1 under [.,m,h])
    let minor = Expr::lam(BinderInfo::Default, const_("Nat"), minor); // h
    let minor = Expr::lam(BinderInfo::Default, const_("Nat"), minor); // m

    // body under [motive(0), n(1), t(2), m_inil(3), m_icons(4)]:
    //   motive=4, n=3, t=2, m_inil=1, m_icons=0
    let body = Expr::app(rec, Expr::bvar(4)); // motive
    let body = Expr::app(body, Expr::bvar(1)); // m_inil (inil minor, no fields)
    let body = Expr::app(body, minor); // icons minor (IH absorbed)
    let body = Expr::app(body, Expr::bvar(3)); // index n
    let body = Expr::app(body, Expr::bvar(2)); // major t

    // Wrap the matching lambda telescope (same binder domains as the type).
    let motive_dom = {
        let inner = Expr::pi(BinderInfo::Default, ivec_at(Expr::bvar(0)), sort_u.clone());
        Expr::pi(BinderInfo::Default, const_("Nat"), inner)
    };
    let n_dom = const_("Nat");
    let t_dom = ivec_at(Expr::bvar(0));
    let m_inil_dom = Expr::app(
        Expr::app(Expr::bvar(2), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    let icons_body = Expr::app(
        Expr::app(Expr::bvar(6), succ(Expr::bvar(2))),
        icons(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
    );
    let m_icons_dom = Expr::pi(BinderInfo::Default, ivec_at(Expr::bvar(1)), icons_body);
    let m_icons_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_icons_dom);
    let m_icons_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_icons_dom);

    let body = Expr::lam(BinderInfo::Default, m_icons_dom, body);
    let body = Expr::lam(BinderInfo::Default, m_inil_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    let body = Expr::lam(BinderInfo::Default, n_dom, body);
    Expr::lam(BinderInfo::Implicit, motive_dom, body)
}

/// Copy the kernel-built `IVec` family / constructors / `IVec.rec` from a
/// scratch env into `env`, mirroring an `.olean` load.
fn copy_ivec_core(native: &Environment, env: &mut Environment) {
    let iv = native
        .get_inductive(&Name::from_string("IVec"))
        .cloned()
        .expect("scratch env has IVec");
    env.register_inductive(iv);
    for ctor in ["IVec.inil", "IVec.icons"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }
    // IVec.rec stays a recursor on import; copy its ConstantInfo so the kernel
    // can type-check the casesOn definition that references it.
    let rv = native
        .get_recursor(&Name::from_string("IVec.rec"))
        .cloned()
        .expect("IVec.rec recursor");
    let rc = native
        .get_const(&Name::from_string("IVec.rec"))
        .cloned()
        .expect("IVec.rec const");
    env.extend_constants_unchecked(std::iter::once(rc));
    env.register_recursor(rv);
}

/// Build an environment holding a *faithfully imported* `IVec`: the real
/// kernel-built family + constructors + `IVec.rec`, but `IVec.casesOn` as a
/// plain `Declaration::Definition` (so `get_recursor("IVec.casesOn") == None`).
fn imported_ivec_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native
        .add_inductive(ivec_decl())
        .expect("IVec should declare");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    copy_ivec_core(&native, &mut env);

    let u = native
        .get_recursor(&Name::from_string("IVec.rec"))
        .and_then(|r| r.level_params.first().cloned())
        .expect("IVec.rec has a motive universe parameter");

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body, kernel
    // type-checked by `add_decl_structural` against the casesOn type. This
    // reproduces exactly what an `.olean` import of an indexed-family member
    // ships (recursor present, `.casesOn` a definitional constant, no
    // clean-side recursor registration). No production path is involved.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("IVec.casesOn"),
        level_params: vec![u.clone()],
        type_: imported_cases_type(&u),
        value: imported_cases_value(&u),
        is_reducible: false,
    })
    .expect("imported IVec.casesOn definition should kernel-check");

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

// ---------------------------------------------------------------------------
// Precondition: the synthesized env is genuinely the *import* configuration —
// indexed family + recursor present, `.casesOn` a definitional constant.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_ivec_is_indexed_with_cases_on_definition_not_recursor() {
    let env = imported_ivec_env();

    let ind = env
        .get_inductive(&Name::from_string("IVec"))
        .expect("IVec inductive should be imported");
    assert_eq!(
        ind.num_indices, 1,
        "IVec is an indexed family: exactly one index (the Nat length)"
    );
    assert_eq!(ind.num_params, 0, "IVec has no parameters, only the index");

    // IVec.rec is a genuine recursor with the index in its metadata.
    let rec = env
        .get_recursor(&Name::from_string("IVec.rec"))
        .expect("IVec.rec recursor");
    assert_eq!(rec.num_indices, 1, "IVec.rec carries the single index");
    assert_eq!(rec.num_motives, 1, "non-mutual family: one motive");
    assert_eq!(rec.num_minors, 2, "one minor per constructor (inil, icons)");

    // IVec.casesOn is a definitional constant (NOT a registered recursor) —
    // this is what routes the match elaborator through the imported path.
    assert!(
        env.get_recursor(&Name::from_string("IVec.casesOn"))
            .is_none(),
        "imported IVec.casesOn must NOT be a registered recursor"
    );
    let cases = env
        .get_const(&Name::from_string("IVec.casesOn"))
        .expect("IVec.casesOn const");
    assert!(
        cases.value.is_some(),
        "imported IVec.casesOn must be a definitional constant with a value"
    );
}

// ---------------------------------------------------------------------------
// Control: the imported `MajorAfterMotive` `IVec.casesOn` reduces correctly
// when applied by hand. Isolates any later match-test failure to the
// *elaborator's* lowering rather than the kernel's reduction of the imported
// casesOn / the synthesized definition itself.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_indexed_cases_on_kernel_reduction_is_correct() {
    let env = imported_ivec_env();

    // motive := fun (_ : Nat) (_ : IVec _) => Nat  (we return a Nat per branch)
    let motive = Expr::lam(
        BinderInfo::Default,
        const_("Nat"),
        Expr::lam(BinderInfo::Default, ivec_at(Expr::bvar(0)), const_("Nat")),
    );
    // m_inil := Nat.zero  (distinct head for the inil branch)
    let m_inil = const_("Nat.zero");
    // m_icons := fun (m : Nat) (h : Nat) (tl : IVec m) => h  (return the head field)
    let m_icons = Expr::lam(
        BinderInfo::Default,
        const_("Nat"),
        Expr::lam(
            BinderInfo::Default,
            const_("Nat"),
            Expr::lam(BinderInfo::Default, ivec_at(Expr::bvar(1)), Expr::bvar(1)),
        ),
    );
    let cases = Expr::const_(Name::from_string("IVec.casesOn"), vec![Level::zero()]);

    // inil branch: casesOn motive 0 inil m_inil m_icons -> m_inil = Nat.zero
    let app = Expr::app(cases.clone(), motive.clone());
    let app = Expr::app(app, const_("Nat.zero")); // index n = 0
    let app = Expr::app(app, const_("IVec.inil")); // major (MajorAfterMotive)
    let app = Expr::app(app, m_inil.clone());
    let app = Expr::app(app, m_icons.clone());
    assert_eq!(
        whnf_head_const(&env, &app).as_deref(),
        Some("Nat.zero"),
        "imported indexed IVec.casesOn on inil must select the inil minor (Nat.zero)"
    );

    // icons branch: build `icons 0 (succ (succ zero)) inil : IVec 1`, head = 2.
    let head_two = succ(succ(const_("Nat.zero")));
    let v = icons(const_("Nat.zero"), head_two.clone(), const_("IVec.inil"));
    let app = Expr::app(cases, motive);
    let app = Expr::app(app, succ(const_("Nat.zero"))); // index n = 1
    let app = Expr::app(app, v); // major
    let app = Expr::app(app, m_inil);
    let app = Expr::app(app, m_icons);
    // m_icons returns the *head* field, so the result must be `2`, distinct from
    // the inil branch's `0` — a wrong field/minor would surface as a different Nat.
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&app, &head_two),
        "imported indexed IVec.casesOn on icons must select m_icons and bind the head field (2); got head {}",
        debug_head(&env, &app)
    );
    assert!(
        !tc.is_def_eq(&app, &const_("Nat.zero")),
        "the icons branch must NOT collapse to the inil branch value (0)"
    );
}

// ---------------------------------------------------------------------------
// MAIN PROBE: clean-elab `match` on the imported indexed family must lower
// through the imported `MajorAfterMotive` `IVec.casesOn` (placing the index +
// major in the right slots, binding the dependent `tail` field correctly) and
// reduce to the genuinely correct branch / field.
// ---------------------------------------------------------------------------

#[test]
fn test_match_on_imported_indexed_family_reduces_to_correct_branch_and_field() {
    let mut env = imported_ivec_env();

    // `headOr0` returns the head of an IVec or 0 for the empty vector. The
    // `icons` branch binds the dependent field `tail : IVec m` (the field type
    // references the earlier field `m`) and returns the distinct `head` field —
    // so a wrong branch, a wrong index slot, or a mis-shifted dependent field
    // binder (the fixed bug) surfaces as a different Nat or an elaboration
    // failure rather than passing silently.
    elaborate_decls_into(
        &mut env,
        "def headOr0 (n : Nat) (v : IVec n) : Nat := match v with\n  \
         | IVec.inil => Nat.zero\n  \
         | IVec.icons m h tl => h",
    );

    // Confirm the body compiled through the imported `IVec.casesOn`.
    let info = env
        .get_const(&Name::from_string("headOr0"))
        .expect("headOr0 should be registered");
    let body = info.value.as_ref().expect("headOr0 is a definition");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("IVec.casesOn")),
        "headOr0 must compile through the imported IVec.casesOn, got: {referenced:?}"
    );

    // inil case: headOr0 0 inil -> Nat.zero.
    let call_inil = Expr::app(
        Expr::app(const_("headOr0"), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    assert_eq!(
        whnf_head_const(&env, &call_inil).as_deref(),
        Some("Nat.zero"),
        "headOr0 0 inil must select the inil branch (Nat.zero)"
    );

    // icons case: headOr0 1 (icons 0 3 inil) -> 3 (the bound head field).
    let head_three = succ(succ(succ(const_("Nat.zero"))));
    let v1 = icons(const_("Nat.zero"), head_three.clone(), const_("IVec.inil"));
    let call_icons = Expr::app(Expr::app(const_("headOr0"), succ(const_("Nat.zero"))), v1);
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&call_icons, &head_three),
        "headOr0 1 (icons 0 3 inil) must reduce to the bound head field (3); got head {}",
        debug_head(&env, &call_icons)
    );
    // Must NOT collapse to the inil branch's 0 — guards against a dropped/wrong
    // minor or a mis-routed major.
    assert!(
        !tc.is_def_eq(&call_icons, &const_("Nat.zero")),
        "the icons branch must NOT collapse to the inil branch value (0)"
    );
}

#[test]
fn test_match_on_imported_indexed_family_uses_dependent_tail_field() {
    let mut env = imported_ivec_env();

    // The sharpest probe for the *fixed* bug: bind the dependent field
    // `tail : IVec m` (its type references the sibling field `m`) AND then
    // **use** it as the scrutinee of a nested match. Before the fix the `tail`
    // binder's domain `IVec m` was mis-shifted to an out-of-scope `BVar`, so
    // the def failed to kernel-check with `UnboundVariable`. The result type is
    // a flat `Nat` (no dependent motive needed — that is the orthogonal gap
    // pinned in `test_dependent_return_type_match_on_index_is_pending`).
    //
    //   def secondOr0 (n : Nat) (v : IVec n) : Nat := match v with
    //     | IVec.inil => Nat.zero
    //     | IVec.icons m h tl => match tl with
    //         | IVec.inil => Nat.zero
    //         | IVec.icons m2 h2 tl2 => h2
    elaborate_decls_into(
        &mut env,
        "def secondOr0 (n : Nat) (v : IVec n) : Nat := match v with\n  \
         | IVec.inil => Nat.zero\n  \
         | IVec.icons m h tl => match tl with\n    \
             | IVec.inil => Nat.zero\n    \
             | IVec.icons m2 h2 tl2 => h2",
    );

    let info = env
        .get_const(&Name::from_string("secondOr0"))
        .expect("secondOr0 should be registered");
    let body = info.value.as_ref().expect("secondOr0 is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("IVec.casesOn")),
        "secondOr0 must compile through the imported IVec.casesOn"
    );

    let tc = TypeChecker::new(&env);

    // length-0: secondOr0 0 inil -> 0.
    let call0 = Expr::app(
        Expr::app(const_("secondOr0"), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    assert_eq!(
        whnf_head_const(&env, &call0).as_deref(),
        Some("Nat.zero"),
        "secondOr0 0 inil must reduce to 0"
    );

    // length-1: secondOr0 1 (icons 0 9 inil) -> 0 (tail is inil, no second).
    let v1 = icons(
        const_("Nat.zero"),
        succ(succ(succ(succ(succ(succ(succ(succ(succ(const_(
            "Nat.zero",
        )))))))))), // 9
        const_("IVec.inil"),
    );
    let call1 = Expr::app(Expr::app(const_("secondOr0"), succ(const_("Nat.zero"))), v1);
    assert!(
        tc.is_def_eq(&call1, &const_("Nat.zero")),
        "secondOr0 1 (icons 0 9 inil) must reduce to 0 (the inner inil branch); got head {}",
        debug_head(&env, &call1)
    );

    // length-2: secondOr0 2 (icons 1 8 (icons 0 4 inil)) -> 4 (the SECOND head),
    // a distinct value reached only by binding `tail` and re-matching on it.
    let inner = icons(
        const_("Nat.zero"),
        succ(succ(succ(succ(const_("Nat.zero"))))), // 4 (second element's head)
        const_("IVec.inil"),
    );
    let outer = icons(
        succ(const_("Nat.zero")),                                           // m = 1
        succ(succ(succ(succ(succ(succ(succ(succ(const_("Nat.zero"))))))))), // 8 (first head)
        inner,
    );
    let call2 = Expr::app(
        Expr::app(const_("secondOr0"), succ(succ(const_("Nat.zero")))),
        outer,
    );
    let four = succ(succ(succ(succ(const_("Nat.zero")))));
    assert!(
        tc.is_def_eq(&call2, &four),
        "secondOr0 2 (icons 1 8 (icons 0 4 inil)) must reduce to the second head (4); got head {}",
        debug_head(&env, &call2)
    );
    // Distinct from both other branch values (0) and the first head (8).
    assert!(
        !tc.is_def_eq(&call2, &const_("Nat.zero")),
        "the two-element case must not collapse to 0"
    );
    let eight = succ(succ(succ(succ(succ(succ(succ(succ(const_("Nat.zero")))))))));
    assert!(
        !tc.is_def_eq(&call2, &eight),
        "the two-element case must select the SECOND head (4), not the first (8) — \
         a mis-bound dependent `tail` field would surface here"
    );
}

// ---------------------------------------------------------------------------
// Pin (flipped on fix): a *dependent return type* over the index
// (`match v : IVec n with ... : IVec n`) needs a motive generalized over the
// index. This was the B48 pending gap (`...is_pending`); it is now implemented
// by `build_indexed_dependent_motive_body` in `elab_match/helpers.rs`, which
// builds `fun (idx) (major) => R[index := idx][scrutinee := major]` for the
// variable-index case and specializes each arm via `arm_branch_ty`. The
// dedicated end-to-end coverage (distinct-witness reductions, native control,
// non-variable-index graceful fallback) lives in
// `import_e2e_dependent_return_match.rs`. This positive assertion keeps the
// scenario pinned here too: dependent rebuild must elaborate, kernel-check, and
// reduce verbatim.
// ---------------------------------------------------------------------------

#[test]
fn test_dependent_return_type_match_on_index_rebuilds_verbatim() {
    let mut env = imported_ivec_env();

    // Result type `IVec n` varies with the scrutinee's index, so each branch's
    // result type differs (`IVec Nat.zero` vs `IVec (Nat.succ m)`). The
    // index-generalized dependent motive lets each arm's body keep its own
    // index, so the def elaborates and rebuilds the vector verbatim.
    elaborate_decls_into(
        &mut env,
        "def rebuild (n : Nat) (v : IVec n) : IVec n := match v with\n  \
         | IVec.inil => IVec.inil\n  \
         | IVec.icons m h tl => IVec.icons m h tl",
    );

    // Compiled through the imported `IVec.casesOn` (not a registered recursor).
    let body = env
        .get_const(&Name::from_string("rebuild"))
        .and_then(|i| i.value.clone())
        .expect("rebuild should be registered");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("IVec.casesOn")),
        "rebuild must compile through the imported IVec.casesOn"
    );

    let tc = TypeChecker::new(&env);

    // `rebuild 0 inil` reduces to `inil`.
    let call0 = Expr::app(
        Expr::app(const_("rebuild"), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    assert_eq!(
        whnf_head_const(&env, &call0).as_deref(),
        Some("IVec.inil"),
        "rebuild 0 inil must reduce to inil"
    );

    // `rebuild 1 (icons 0 7 inil)` rebuilds the vector verbatim.
    let head_seven = succ(succ(succ(succ(succ(succ(succ(const_("Nat.zero"))))))));
    let v1 = icons(const_("Nat.zero"), head_seven, const_("IVec.inil"));
    let call1 = Expr::app(
        Expr::app(const_("rebuild"), succ(const_("Nat.zero"))),
        v1.clone(),
    );
    assert!(
        tc.is_def_eq(&call1, &v1),
        "rebuild 1 (icons 0 7 inil) must rebuild the vector verbatim; got head {}",
        debug_head(&env, &call1)
    );
    // Distinct from the empty vector: a collapsed/wrong branch would surface here.
    assert!(
        !tc.is_def_eq(&call1, &const_("IVec.inil")),
        "rebuild of a non-empty vector must NOT collapse to inil"
    );
}

// ---------------------------------------------------------------------------
// Control: the NATIVE path (IVec.casesOn IS a registered recursor in the
// `MajorAfterMinors` layout) lowers + reduces correctly too. Both paths share
// the dependent-field binding loop that this change fixed, so this isolates any
// regression to the elaborator rather than the imported-eliminator handling.
// ---------------------------------------------------------------------------

#[test]
fn test_native_indexed_family_match_reduces_correctly() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.add_inductive(ivec_decl()).expect("IVec should declare");

    // Native IVec.casesOn IS a registered recursor (MajorAfterMinors).
    let rec = env
        .get_recursor(&Name::from_string("IVec.casesOn"))
        .expect("native IVec.casesOn should be a registered recursor");
    assert_eq!(
        rec.arg_order,
        clean_kernel::RecursorArgOrder::MajorAfterMinors,
        "native casesOn uses the MajorAfterMinors layout"
    );

    elaborate_decls_into(
        &mut env,
        "def headOr0N (n : Nat) (v : IVec n) : Nat := match v with\n  \
         | IVec.inil => Nat.zero\n  \
         | IVec.icons m h tl => h",
    );

    // Native body lowers through the registered recursor, NOT a definitional
    // casesOn constant — confirm we are genuinely on the native path.
    let body = env
        .get_const(&Name::from_string("headOr0N"))
        .and_then(|i| i.value.clone())
        .expect("headOr0N body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("IVec.casesOn")),
        "native headOr0N lowers through IVec.casesOn (the registered recursor)"
    );

    let call_inil = Expr::app(
        Expr::app(const_("headOr0N"), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    assert_eq!(
        whnf_head_const(&env, &call_inil).as_deref(),
        Some("Nat.zero"),
        "native headOr0N 0 inil must reduce to Nat.zero"
    );

    let head_five = succ(succ(succ(succ(succ(const_("Nat.zero")))))); // 5
    let v1 = icons(const_("Nat.zero"), head_five.clone(), const_("IVec.inil"));
    let call_icons = Expr::app(Expr::app(const_("headOr0N"), succ(const_("Nat.zero"))), v1);
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&call_icons, &head_five),
        "native headOr0N 1 (icons 0 5 inil) must reduce to the head field (5); got head {}",
        debug_head(&env, &call_icons)
    );
    assert!(
        !tc.is_def_eq(&call_icons, &const_("Nat.zero")),
        "native icons branch must NOT collapse to the inil branch value (0)"
    );
}
