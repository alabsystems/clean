// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: **dependent-return-type `match` over an index** on an *imported*
//! indexed inductive family (dependent_return_match scenario).
//!
//! ## The gap this closes (B48 PINNED)
//!
//! B48 fixed dependent-*field* binding for indexed families and PINNED, as a
//! flip-on-fix, the orthogonal case where the match's **return type mentions the
//! index** (`import_e2e_indexed_family_recursor.rs`). For
//!
//! ```text
//! def rebuild {n} (v : IVec n) : IVec n := match v with
//!   | inil          => inil
//!   | icons m h tl  => icons m h tl
//! ```
//!
//! each arm's body has a *different* type — `inil : IVec Nat.zero` versus
//! `icons … : IVec (Nat.succ m)` — so the motive cannot be the constant
//! `fun (n') (v') => branch_ty` (that locks the result to the first arm's index
//! `IVec Nat.zero`, and the kernel rejects the `icons` arm with a type
//! mismatch). B48's `match_dependent_motive` only generalized over the
//! *scrutinee*; the return-over-index case additionally needs the motive
//! generalized over the **index**:
//!
//! ```text
//! motive := fun (idx : Nat) (major : IVec idx) => IVec idx
//! ```
//!
//! so the per-arm minor premise type is `motive idx(ctorᵢ) (ctorᵢ fields…)`,
//! which is `IVec Nat.zero` for `inil` and `IVec (Nat.succ m)` for `icons` —
//! exactly the type each arm body has.
//!
//! ## The fix (clean-elab only)
//!
//! `build_indexed_dependent_motive_body` (in `elab_match/helpers.rs`) detects the
//! variable-index dependent-elimination case — scrutinee is a bare `FVar`, every
//! index is a *distinct* `FVar`, and the expected type genuinely depends on
//! them — and abstracts the index fvars + scrutinee fvar into the motive body.
//! `arm_branch_ty` then specializes that body per arm by reading the
//! constructor's own index off its inferred type and instantiating all binders.
//! A non-variable index (e.g. `IVec (Nat.succ k)`) or an index-independent
//! return type falls back to the existing constant motive, byte-for-byte
//! unchanged — the native control below verifies the native path is untouched.
//!
//! ## Synthesize-as-import (mirrors `import_e2e_indexed_family_recursor.rs`)
//!
//! We build the genuine `IVec` family + constructors + `IVec.rec` in a scratch
//! env, copy them verbatim, then synthesize `IVec.casesOn` as a plain
//! `Declaration::Definition` in Lean's `MajorAfterMotive` layout — exactly what
//! an `.olean` ships: `IVec.rec` is a recursor, but
//! `get_recursor("IVec.casesOn") == None`. We assert that precondition so the
//! test stays honest about exercising the *import* path, then drive a
//! dependent-return `match` through it and assert the reduced value with
//! distinct witnesses so a wrong branch / wrong index / wrong field surfaces as a
//! different observable result.

use clean_kernel::env::Declaration;
use clean_kernel::env::Environment;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers (mirror import_e2e_indexed_family_recursor.rs)
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

/// `IVec n`.
fn ivec_at(n: Expr) -> Expr {
    Expr::app(const_("IVec"), n)
}

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
fn ivec_decl() -> InductiveDecl {
    let ivec_ty = Expr::pi(BinderInfo::Default, const_("Nat"), Expr::type_());
    let inil_ty = ivec_at(const_("Nat.zero"));
    // icons : (n : Nat) -> (head : Nat) -> (tail : IVec n) -> IVec (Nat.succ n)
    let icons_ret = ivec_at(succ(Expr::bvar(2)));
    let tail_ty = ivec_at(Expr::bvar(1));
    let icons_ty = Expr::pi(BinderInfo::Default, tail_ty, icons_ret);
    let icons_ty = Expr::pi(BinderInfo::Default, const_("Nat"), icons_ty);
    let icons_ty = Expr::pi(BinderInfo::Default, const_("Nat"), icons_ty);

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

/// Imported `MajorAfterMotive` `IVec.casesOn` type.
fn imported_cases_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    let motive_dom = {
        let inner = Expr::pi(BinderInfo::Default, ivec_at(Expr::bvar(0)), sort_u.clone());
        Expr::pi(BinderInfo::Default, const_("Nat"), inner)
    };
    let result = Expr::app(Expr::app(Expr::bvar(4), Expr::bvar(3)), Expr::bvar(2));
    let icons_body = Expr::app(
        Expr::app(Expr::bvar(6), succ(Expr::bvar(2))),
        icons(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
    );
    let m_icons_dom = Expr::pi(BinderInfo::Default, ivec_at(Expr::bvar(1)), icons_body);
    let m_icons_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_icons_dom);
    let m_icons_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_icons_dom);
    let m_inil_dom = Expr::app(
        Expr::app(Expr::bvar(2), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    let t_dom = ivec_at(Expr::bvar(0));
    let n_dom = const_("Nat");
    let body = Expr::pi(BinderInfo::Default, m_icons_dom, result);
    let body = Expr::pi(BinderInfo::Default, m_inil_dom, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    let body = Expr::pi(BinderInfo::Default, n_dom, body);
    Expr::pi(BinderInfo::Implicit, motive_dom, body)
}

/// Imported `IVec.casesOn` value, unfolding to `IVec.rec`.
fn imported_cases_value(u: &Name) -> Expr {
    let rec = Expr::const_(Name::from_string("IVec.rec"), vec![Level::param(u.clone())]);
    let sort_u = Expr::sort(Level::param(u.clone()));
    let minor_body = Expr::app(
        Expr::app(Expr::app(Expr::bvar(4), Expr::bvar(3)), Expr::bvar(2)),
        Expr::bvar(1),
    );
    let ih_dom = Expr::app(Expr::app(Expr::bvar(7), Expr::bvar(2)), Expr::bvar(0));
    let minor = Expr::lam(BinderInfo::Default, ih_dom, minor_body);
    let minor = Expr::lam(BinderInfo::Default, ivec_at(Expr::bvar(1)), minor);
    let minor = Expr::lam(BinderInfo::Default, const_("Nat"), minor);
    let minor = Expr::lam(BinderInfo::Default, const_("Nat"), minor);
    let body = Expr::app(rec, Expr::bvar(4));
    let body = Expr::app(body, Expr::bvar(1));
    let body = Expr::app(body, minor);
    let body = Expr::app(body, Expr::bvar(3));
    let body = Expr::app(body, Expr::bvar(2));
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

/// Faithfully-imported `IVec`: kernel-built family + ctors + `IVec.rec`, with
/// `IVec.casesOn` a plain `Declaration::Definition`.
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
    // constant; kernel-checked by `add_decl_structural`. Mirrors exactly what an
    // `.olean` import of an indexed-family member ships (recursor present,
    // `.casesOn` a definitional constant, no clean-side recursor registration).
    // No production path is involved.
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
// Precondition: genuinely the import configuration.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_ivec_cases_on_is_definition_not_recursor() {
    let env = imported_ivec_env();

    let ind = env
        .get_inductive(&Name::from_string("IVec"))
        .expect("IVec inductive should be imported");
    assert_eq!(ind.num_indices, 1, "IVec is indexed by one Nat");
    assert_eq!(ind.num_params, 0, "IVec has no parameters");

    assert!(
        env.get_recursor(&Name::from_string("IVec.casesOn"))
            .is_none(),
        "imported IVec.casesOn must NOT be a registered recursor (exercises the import path)"
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
// MAIN PROBE: dependent-return `match` over the index, through the imported
// `MajorAfterMotive` `IVec.casesOn`. Must elaborate (needs the
// index-generalized motive), kernel-check, and reduce verbatim.
// ---------------------------------------------------------------------------

#[test]
fn test_dependent_return_match_rebuilds_imported_indexed_family_verbatim() {
    let mut env = imported_ivec_env();

    // `rebuild` reconstructs the vector. The return type `IVec n` varies with
    // the index, so the `inil` arm has type `IVec Nat.zero` and the `icons` arm
    // `IVec (Nat.succ m)` — only an index-generalized dependent motive accepts
    // both. The dependent `tail` field is also bound (and rebuilt), so a wrong
    // index slot, a mis-bound field, or a collapsed branch surfaces as a
    // different reduced value or an elaboration failure.
    elaborate_decls_into(
        &mut env,
        "def rebuild (n : Nat) (v : IVec n) : IVec n := match v with\n  \
         | IVec.inil => IVec.inil\n  \
         | IVec.icons m h tl => IVec.icons m h tl",
    );

    // Compiled through the imported `IVec.casesOn` (not a registered recursor).
    let info = env
        .get_const(&Name::from_string("rebuild"))
        .expect("rebuild should be registered");
    let body = info.value.as_ref().expect("rebuild is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("IVec.casesOn")),
        "rebuild must compile through the imported IVec.casesOn, got: {:?}",
        body.collect_constants()
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

    // `rebuild 1 (icons 0 7 inil)` rebuilds the one-element vector verbatim.
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
    assert!(
        !tc.is_def_eq(&call1, &const_("IVec.inil")),
        "a non-empty rebuild must NOT collapse to inil (wrong branch / dropped field)"
    );

    // `rebuild 2 (icons 1 8 (icons 0 4 inil))` rebuilds the two-element vector
    // verbatim — and is distinct from both inil and the one-element prefix, so a
    // mis-bound dependent `tail` field or a wrong index would surface here.
    let inner = icons(
        const_("Nat.zero"),
        succ(succ(succ(succ(const_("Nat.zero"))))), // 4
        const_("IVec.inil"),
    );
    let outer = icons(
        succ(const_("Nat.zero")),                                           // m = 1
        succ(succ(succ(succ(succ(succ(succ(succ(const_("Nat.zero"))))))))), // 8
        inner.clone(),
    );
    let call2 = Expr::app(
        Expr::app(const_("rebuild"), succ(succ(const_("Nat.zero")))),
        outer.clone(),
    );
    assert!(
        tc.is_def_eq(&call2, &outer),
        "rebuild 2 (icons 1 8 (icons 0 4 inil)) must rebuild verbatim; got head {}",
        debug_head(&env, &call2)
    );
    assert!(
        !tc.is_def_eq(&call2, &inner),
        "the two-element rebuild must NOT collapse to its one-element tail"
    );
}

// ---------------------------------------------------------------------------
// A dependent-return match where the body genuinely *transforms* the index —
// `tailIndex` returns the predecessor-length vector for `icons` (the bound
// `tail`), or the empty vector for `inil`. Its return type `IVec (predLen n)`
// still varies per branch, so a non-dependent motive would reject it; the bound
// dependent `tail : IVec m` is returned, with a distinct witness.
// ---------------------------------------------------------------------------

#[test]
fn test_dependent_return_match_returns_dependent_tail_field() {
    let mut env = imported_ivec_env();

    // predLen 0 = 0; predLen (succ k) = k. So `dropHead (n) (v : IVec n) : IVec
    // (predLen n)` returns `inil` for the empty vector and the `tail` (an
    // `IVec m`) for `icons m h tl` — a dependent return whose type is the
    // predecessor index. The bound `tail` field is returned directly.
    elaborate_decls_into(
        &mut env,
        "def predLen (n : Nat) : Nat := match n with\n  \
         | Nat.zero => Nat.zero\n  \
         | Nat.succ k => k",
    );
    elaborate_decls_into(
        &mut env,
        "def dropHead (n : Nat) (v : IVec n) : IVec (predLen n) := match v with\n  \
         | IVec.inil => IVec.inil\n  \
         | IVec.icons m h tl => tl",
    );

    let body = env
        .get_const(&Name::from_string("dropHead"))
        .and_then(|i| i.value.clone())
        .expect("dropHead should be registered");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("IVec.casesOn")),
        "dropHead must compile through the imported IVec.casesOn"
    );

    let tc = TypeChecker::new(&env);

    // dropHead 0 inil -> inil.
    let call0 = Expr::app(
        Expr::app(const_("dropHead"), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    assert_eq!(
        whnf_head_const(&env, &call0).as_deref(),
        Some("IVec.inil"),
        "dropHead 0 inil must reduce to inil"
    );

    // dropHead 1 (icons 0 7 inil) -> inil (the bound tail).
    let v1 = icons(
        const_("Nat.zero"),
        succ(succ(succ(succ(succ(succ(succ(const_("Nat.zero")))))))), // 7
        const_("IVec.inil"),
    );
    let call1 = Expr::app(Expr::app(const_("dropHead"), succ(const_("Nat.zero"))), v1);
    assert_eq!(
        whnf_head_const(&env, &call1).as_deref(),
        Some("IVec.inil"),
        "dropHead 1 (icons 0 7 inil) must reduce to its tail (inil)"
    );

    // dropHead 2 (icons 1 8 (icons 0 4 inil)) -> icons 0 4 inil (the bound tail).
    let inner = icons(
        const_("Nat.zero"),
        succ(succ(succ(succ(const_("Nat.zero"))))), // 4
        const_("IVec.inil"),
    );
    let outer = icons(
        succ(const_("Nat.zero")),                                           // m = 1
        succ(succ(succ(succ(succ(succ(succ(succ(const_("Nat.zero"))))))))), // 8
        inner.clone(),
    );
    let call2 = Expr::app(
        Expr::app(const_("dropHead"), succ(succ(const_("Nat.zero")))),
        outer,
    );
    assert!(
        tc.is_def_eq(&call2, &inner),
        "dropHead 2 (icons 1 8 (icons 0 4 inil)) must reduce to the bound tail (icons 0 4 inil); \
         got head {}",
        debug_head(&env, &call2)
    );
    assert!(
        !tc.is_def_eq(&call2, &const_("IVec.inil")),
        "the two-element dropHead must NOT collapse to inil (a dropped tail field)"
    );
}

// ---------------------------------------------------------------------------
// Regression guard: a *flat* (non-dependent) return type on the SAME imported
// indexed family must keep using the constant motive — the index-dependent
// detection must not fire and perturb the existing path. `headOr0` returns a
// plain `Nat`, so the expected type does not depend on the index.
// ---------------------------------------------------------------------------

#[test]
fn test_flat_return_match_on_imported_indexed_family_unchanged() {
    let mut env = imported_ivec_env();

    elaborate_decls_into(
        &mut env,
        "def headOr0 (n : Nat) (v : IVec n) : Nat := match v with\n  \
         | IVec.inil => Nat.zero\n  \
         | IVec.icons m h tl => h",
    );

    let tc = TypeChecker::new(&env);

    let call_inil = Expr::app(
        Expr::app(const_("headOr0"), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    assert_eq!(
        whnf_head_const(&env, &call_inil).as_deref(),
        Some("Nat.zero"),
        "headOr0 0 inil must select the inil branch (Nat.zero)"
    );

    let head_three = succ(succ(succ(const_("Nat.zero"))));
    let v1 = icons(const_("Nat.zero"), head_three.clone(), const_("IVec.inil"));
    let call_icons = Expr::app(Expr::app(const_("headOr0"), succ(const_("Nat.zero"))), v1);
    assert!(
        tc.is_def_eq(&call_icons, &head_three),
        "headOr0 1 (icons 0 3 inil) must reduce to the head field (3); got head {}",
        debug_head(&env, &call_icons)
    );
    assert!(
        !tc.is_def_eq(&call_icons, &const_("Nat.zero")),
        "the icons branch must NOT collapse to the inil branch value (0)"
    );
}

// ---------------------------------------------------------------------------
// Control: the NATIVE path (IVec.casesOn IS a registered recursor in the
// `MajorAfterMinors` layout) handles the dependent-return match identically.
// Both paths share the motive-construction + arm-specialization logic, so this
// isolates any regression to the elaborator rather than the imported-eliminator
// handling, and proves the native path is genuinely unchanged for the flat case.
// ---------------------------------------------------------------------------

#[test]
fn test_native_indexed_family_dependent_and_flat_match_reduce_correctly() {
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

    // Dependent-return rebuild on the native path.
    elaborate_decls_into(
        &mut env,
        "def rebuildN (n : Nat) (v : IVec n) : IVec n := match v with\n  \
         | IVec.inil => IVec.inil\n  \
         | IVec.icons m h tl => IVec.icons m h tl",
    );
    // Flat-return headOr0 on the native path (constant-motive path unchanged).
    elaborate_decls_into(
        &mut env,
        "def headOr0N (n : Nat) (v : IVec n) : Nat := match v with\n  \
         | IVec.inil => Nat.zero\n  \
         | IVec.icons m h tl => h",
    );

    let tc = TypeChecker::new(&env);

    // rebuildN 0 inil -> inil; rebuildN 1 (icons 0 5 inil) -> verbatim.
    let call0 = Expr::app(
        Expr::app(const_("rebuildN"), const_("Nat.zero")),
        const_("IVec.inil"),
    );
    assert_eq!(
        whnf_head_const(&env, &call0).as_deref(),
        Some("IVec.inil"),
        "native rebuildN 0 inil must reduce to inil"
    );
    let head_five = succ(succ(succ(succ(succ(const_("Nat.zero"))))));
    let v1 = icons(const_("Nat.zero"), head_five, const_("IVec.inil"));
    let call1 = Expr::app(
        Expr::app(const_("rebuildN"), succ(const_("Nat.zero"))),
        v1.clone(),
    );
    assert!(
        tc.is_def_eq(&call1, &v1),
        "native rebuildN 1 (icons 0 5 inil) must rebuild verbatim; got head {}",
        debug_head(&env, &call1)
    );
    assert!(
        !tc.is_def_eq(&call1, &const_("IVec.inil")),
        "native rebuild of a non-empty vector must NOT collapse to inil"
    );

    // headOr0N flat path unchanged.
    let call_icons = Expr::app(
        Expr::app(const_("headOr0N"), succ(const_("Nat.zero"))),
        icons(
            const_("Nat.zero"),
            succ(succ(succ(succ(succ(const_("Nat.zero")))))),
            const_("IVec.inil"),
        ),
    );
    let five = succ(succ(succ(succ(succ(const_("Nat.zero"))))));
    assert!(
        tc.is_def_eq(&call_icons, &five),
        "native headOr0N 1 (icons 0 5 inil) must reduce to the head field (5); got head {}",
        debug_head(&env, &call_icons)
    );
}
