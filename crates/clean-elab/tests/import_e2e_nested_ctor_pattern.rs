// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: **nested constructor sub-patterns** (and as-patterns) in a
//! `match` on an *imported* inductive (nested_ctor_pattern scenario).
//!
//! ## Background — the import probe vein
//!
//! B43/B44/B45/B47/B48 found correctness bugs where the elaborator computes
//! eliminator / projection / motive LAYOUT from clean-side *native* metadata
//! that a real Lean `.olean` does not ship. A genuine import carries only the
//! definitional `T.casesOn` constant (Lean's `MajorAfterMotive` layout:
//! `motive → indices → major → minors`), registered as a plain `Definition`,
//! NOT as a recursor — so `get_recursor("T.casesOn") == None` and there is no
//! clean-side `structure_fields` table.
//!
//! The top-level `match` lowering in `elab_match/mod.rs` *does* consult
//! `get_recursor` to choose between the native `MajorAfterMinors` layout and
//! the imported `MajorAfterMotive` layout (the `major_after_motive` flag).
//!
//! ## The bug this file pins (fixed in this change)
//!
//! NESTED constructor sub-patterns — e.g. `MyOption.some (MyOption.some x)` —
//! lower the *inner* `MyOption.some x` sub-pattern through
//! `wrap_with_nested_ctor_caseson_with_fallback` in
//! `infer/elab_match/nested_ctor.rs`. That helper built the inner `casesOn`
//! application UNCONDITIONALLY in the native `MajorAfterMinors` layout:
//!
//! ```text
//!   T.casesOn motive minor₀ minor₁ … major          (major LAST)
//! ```
//!
//! It never consulted `get_recursor`, so for an *imported* `T.casesOn`
//! (definitional `MajorAfterMotive`: `T.casesOn motive major minor₀ minor₁ …`)
//! the major premise (the bound field) landed in a MINOR-premise slot and a
//! minor landed in the major slot. The kernel then either rejected the term or
//! — worse — reduced the wrong branch, binding the inner field to the wrong
//! slot. The fix mirrors the top-level lowering: detect the imported layout via
//! `get_recursor(...).arg_order` (absent ⇒ `MajorAfterMotive`) and place the
//! major premise immediately after the motive, before the minors, for the
//! imported case; the native `MajorAfterMinors` path is byte-for-byte unchanged.
//!
//! ## Synthesize-as-import (mirrors B47/B48)
//!
//! `MyOption (A : Type)` + its constructors + `MyOption.rec` are built by the
//! kernel in a scratch env and copied verbatim into a fresh env;
//! `MyOption.casesOn` is then synthesized as a plain `Declaration::Definition`
//! in the `MajorAfterMotive` layout (kernel-checked via `add_decl_structural`).
//! A precondition test asserts `get_recursor("MyOption.casesOn") == None`,
//! proving the nested-pattern lowering below runs through the import path.
//!
//! A NATIVE control (where `MyOption.casesOn` IS a recursor) drives the SAME
//! nested patterns so the fix is shown general, not import-specific.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Declaration;
use clean_kernel::env::Environment;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Reduce `expr` to WHNF and return the head `Const` name (handles a bare
/// constructor and a constructor applied to fields alike).
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn def_eq(env: &Environment, a: &Expr, b: &Expr) -> bool {
    TypeChecker::new(env).is_def_eq(a, b)
}

/// `MyOption.some` applied to an explicit element type and a value.
fn some_of(elem_ty: Expr, value: Expr) -> Expr {
    Expr::app(Expr::app(const_("MyOption.some"), elem_ty), value)
}

/// `MyOption.none` at an explicit element type.
fn none_of(elem_ty: Expr) -> Expr {
    Expr::app(const_("MyOption.none"), elem_ty)
}

/// `MyOption A` (the family applied to its single parameter).
fn myoption_of(elem_ty: Expr) -> Expr {
    Expr::app(const_("MyOption"), elem_ty)
}

fn succ(n: Expr) -> Expr {
    Expr::app(const_("Nat.succ"), n)
}

/// `inductive MyOption (A : Type) : Type | none | some (a : A)`.
fn myoption_decl() -> InductiveDecl {
    let ind_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    // none : {A : Type} -> MyOption A
    let none_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::app(const_("MyOption"), Expr::bvar(0)),
    );
    // some : {A : Type} -> A -> MyOption A
    let some_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(const_("MyOption"), Expr::bvar(1)),
        ),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("MyOption"),
            type_: ind_ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyOption.none"),
                    type_: none_ty,
                },
                Constructor {
                    name: Name::from_string("MyOption.some"),
                    type_: some_ty,
                },
            ],
        }],
    }
}

/// Imported `MyOption.casesOn` **type** in Lean's `MajorAfterMotive` layout
/// (the inductive parameter `A` precedes the motive):
///
/// ```text
/// {A : Type} -> {motive : MyOption A -> Sort u} -> (t : MyOption A)
///   -> motive MyOption.none
///   -> ((a : A) -> motive (MyOption.some a))
///   -> motive t
/// ```
fn imported_cases_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    // Telescope (outer -> inner): A, motive, t, m_none, m_some.
    // result `motive t` under [A, motive, t, m_none, m_some]: motive=3, t=2.
    let result = Expr::app(Expr::bvar(3), Expr::bvar(2));

    // m_some domain under [A, motive, t, m_none]:
    //   (a : A) -> motive (MyOption.some A a)
    //   inside the `a` binder [A, motive, t, m_none, a]: A=4, motive=3, a=0.
    let some_app = some_of(Expr::bvar(4), Expr::bvar(0));
    let m_some_body = Expr::app(Expr::bvar(3), some_app);
    let m_some_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_some_body); // a : A (A = BVar3 under [A,motive,t,m_none])

    // m_none domain under [A, motive, t]: motive (MyOption.none A) (motive=1, A=2).
    let m_none_dom = Expr::app(Expr::bvar(1), none_of(Expr::bvar(2)));

    // t domain under [A, motive]: MyOption A (A = BVar1).
    let t_dom = myoption_of(Expr::bvar(1));
    // motive domain under [A]: MyOption A -> Sort u (A = BVar0).
    let motive_dom = Expr::pi(BinderInfo::Default, myoption_of(Expr::bvar(0)), sort_u);

    let body = Expr::pi(BinderInfo::Default, m_some_dom, result);
    let body = Expr::pi(BinderInfo::Default, m_none_dom, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    let body = Expr::pi(BinderInfo::Implicit, motive_dom, body);
    Expr::pi(BinderInfo::Implicit, Expr::type_(), body)
}

/// Imported `MyOption.casesOn` **value**, unfolding to `MyOption.rec`:
///
/// ```text
/// fun A motive t m_none m_some =>
///   MyOption.rec.{u} A motive m_none m_some t
/// ```
///
/// `MyOption.rec` is `MajorAfterMinors` (params → motive → minors → major) and
/// the `some` minor carries no induction hypothesis (`A` is not recursive), so
/// the casesOn body just reorders the major to the end.
fn imported_cases_value(u: &Name) -> Expr {
    let rec = Expr::const_(
        Name::from_string("MyOption.rec"),
        vec![Level::param(u.clone())],
    );
    let sort_u = Expr::sort(Level::param(u.clone()));

    // body under [A(4), motive(3), t(2), m_none(1), m_some(0)]:
    //   MyOption.rec A motive m_none m_some t
    let body = Expr::app(rec, Expr::bvar(4)); // A (param first)
    let body = Expr::app(body, Expr::bvar(3)); // motive
    let body = Expr::app(body, Expr::bvar(1)); // m_none
    let body = Expr::app(body, Expr::bvar(0)); // m_some
    let body = Expr::app(body, Expr::bvar(2)); // major t (MajorAfterMinors)

    // Rebuild the binder domains (mirroring the casesOn type).
    let some_app = some_of(Expr::bvar(4), Expr::bvar(0));
    let m_some_body = Expr::app(Expr::bvar(3), some_app);
    let m_some_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_some_body);
    let m_none_dom = Expr::app(Expr::bvar(1), none_of(Expr::bvar(2)));
    let t_dom = myoption_of(Expr::bvar(1));
    let motive_dom = Expr::pi(BinderInfo::Default, myoption_of(Expr::bvar(0)), sort_u);

    let body = Expr::lam(BinderInfo::Default, m_some_dom, body);
    let body = Expr::lam(BinderInfo::Default, m_none_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    let body = Expr::lam(BinderInfo::Implicit, motive_dom, body);
    Expr::lam(BinderInfo::Implicit, Expr::type_(), body)
}

/// Copy the kernel-built `MyOption` family / constructors / `MyOption.rec` from
/// a scratch env into `env`, mirroring an `.olean` load (no clean-side field
/// table / no recursor registration for the casesOn).
fn copy_myoption_core(native: &Environment, env: &mut Environment) {
    let iv = native
        .get_inductive(&Name::from_string("MyOption"))
        .cloned()
        .expect("scratch env has MyOption");
    env.register_inductive(iv);
    for ctor in ["MyOption.none", "MyOption.some"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }
    let rv = native
        .get_recursor(&Name::from_string("MyOption.rec"))
        .cloned()
        .expect("MyOption.rec recursor");
    let rc = native
        .get_const(&Name::from_string("MyOption.rec"))
        .cloned()
        .expect("MyOption.rec const");
    env.extend_constants_unchecked(std::iter::once(rc));
    env.register_recursor(rv);
}

/// Build an environment with a *faithfully imported* `MyOption`: the real
/// kernel-built family + constructors + `MyOption.rec`, but `MyOption.casesOn`
/// as a plain `Declaration::Definition` (so `get_recursor` returns `None`).
fn imported_myoption_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native
        .add_inductive(myoption_decl())
        .expect("MyOption should declare");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    copy_myoption_core(&native, &mut env);

    let u = native
        .get_recursor(&Name::from_string("MyOption.rec"))
        .and_then(|r| r.level_params.first().cloned())
        .expect("MyOption.rec has a motive universe parameter");

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body, kernel
    // type-checked by `add_decl_structural` against the casesOn type. This
    // reproduces exactly what an `.olean` import of a parameterized member
    // ships (recursor present, `.casesOn` a definitional `MajorAfterMotive`
    // constant, no clean-side recursor registration). No production path is
    // involved; mirrors B47/B48 import fixtures. Tracking: import-probe vein.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("MyOption.casesOn"),
        level_params: vec![u.clone()],
        type_: imported_cases_type(&u),
        value: imported_cases_value(&u),
        is_reducible: false,
    })
    .expect("imported MyOption.casesOn definition should kernel-check");

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

// ===========================================================================
// Precondition: the synthesized `MyOption` matches the IMPORT configuration
// (inductive + `.rec` + definitional `.casesOn`, `.casesOn` NOT a registered
// recursor). This proves the nested-pattern tests below exercise the import
// path rather than the native recursor path.
// ===========================================================================

#[test]
fn test_imported_myoption_cases_on_is_definitional_not_recursor() {
    let env = imported_myoption_env();

    let ind = env
        .get_inductive(&Name::from_string("MyOption"))
        .expect("MyOption inductive should be imported");
    assert_eq!(ind.num_params, 1, "MyOption has one parameter (A)");
    assert_eq!(ind.num_indices, 0, "MyOption is parameterized, not indexed");

    assert!(
        env.get_recursor(&Name::from_string("MyOption.rec"))
            .is_some(),
        "MyOption.rec stays a registered recursor on import"
    );
    assert!(
        env.get_recursor(&Name::from_string("MyOption.casesOn"))
            .is_none(),
        "imported MyOption.casesOn must NOT be a registered recursor — this is the \
         exact condition that routes nested-pattern lowering through the imported \
         MajorAfterMotive path"
    );
    let cases = env
        .get_const(&Name::from_string("MyOption.casesOn"))
        .expect("MyOption.casesOn const should exist");
    assert!(
        cases.value.is_some(),
        "imported MyOption.casesOn must be a definitional constant with a value"
    );
}

// ===========================================================================
// MAIN PROBE: a nested constructor sub-pattern `MyOption.some (MyOption.some x)`
// on an imported `MyOption (MyOption Nat)`. The OUTER `some` is the top-level
// casesOn (which already handles MajorAfterMotive); the INNER `some x`
// sub-pattern lowers through `wrap_with_nested_ctor_caseson_with_fallback`,
// which must ALSO use the imported MajorAfterMotive layout.
//
// Distinct branch values make a wrong layout observable: a mis-ordered inner
// casesOn either fails to kernel-check or reduces the wrong branch / binds the
// inner field to the wrong slot.
// ===========================================================================

#[test]
fn test_nested_some_some_pattern_on_imported_myoption_reduces_correctly() {
    let mut env = imported_myoption_env();

    // unwrap2 : MyOption (MyOption Nat) -> Nat
    //   | some (some x) => x      -- inner field bound by a nested casesOn
    //   | some none     => 1      -- distinct from the some-some value
    //   | none          => 0      -- distinct again
    elaborate_decls_into(
        &mut env,
        "def unwrap2 (o : MyOption (MyOption Nat)) : Nat := match o with\n  \
         | MyOption.some (MyOption.some x) => x\n  \
         | MyOption.some MyOption.none => Nat.succ Nat.zero\n  \
         | MyOption.none => Nat.zero",
    );

    // The body must compile through the imported MyOption.casesOn (the only
    // eliminator available), proving the import path.
    let info = env
        .get_const(&Name::from_string("unwrap2"))
        .expect("unwrap2 should be registered");
    let body = info.value.as_ref().expect("unwrap2 is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("MyOption.casesOn")),
        "unwrap2 must compile through the imported MyOption.casesOn, got: {:?}",
        body.collect_constants()
    );

    let nat = const_("Nat");
    let opt_nat = myoption_of(nat.clone());

    // some (some 7) -> 7 (the bound inner field).
    let seven = succ(succ(succ(succ(succ(succ(succ(const_("Nat.zero")))))))); // 7
    let some_some_7 = some_of(opt_nat.clone(), some_of(nat.clone(), seven.clone()));
    let call_ss = Expr::app(const_("unwrap2"), some_some_7);
    assert!(
        def_eq(&env, &call_ss, &seven),
        "unwrap2 (some (some 7)) must reduce to the inner field (7); got head {:?}",
        TypeChecker::new(&env).whnf(&call_ss).kind()
    );
    // It must NOT collapse to either of the other branches' distinct values.
    assert!(
        !def_eq(&env, &call_ss, &const_("Nat.zero")),
        "the some-some branch must not collapse to the none value (0)"
    );
    assert!(
        !def_eq(&env, &call_ss, &succ(const_("Nat.zero"))),
        "the some-some branch must not collapse to the some-none value (1)"
    );

    // some none -> 1.
    let some_none = some_of(opt_nat.clone(), none_of(nat.clone()));
    let call_sn = Expr::app(const_("unwrap2"), some_none);
    assert!(
        def_eq(&env, &call_sn, &succ(const_("Nat.zero"))),
        "unwrap2 (some none) must reduce to the some-none branch (1); got head {:?}",
        TypeChecker::new(&env).whnf(&call_sn).kind()
    );

    // none -> 0.
    let none_outer = none_of(opt_nat);
    let call_n = Expr::app(const_("unwrap2"), none_outer);
    assert_eq!(
        whnf_head_const(&env, &call_n).as_deref(),
        Some("Nat.zero"),
        "unwrap2 none must reduce to the none branch (0)"
    );

    // All three branches reduce to genuinely distinct values, so a wrong inner
    // layout (the fixed bug) surfaces as a different result rather than silently.
    assert!(
        !def_eq(&env, &call_ss, &call_sn) && !def_eq(&env, &call_sn, &call_n),
        "the three branches must reduce to distinct values (7, 1, 0)"
    );
}

// ===========================================================================
// A nested sub-pattern that binds a field within the inner constructor and
// re-uses it. `MyPair`-free variant: a `MyOption (MyOption Nat)` where the
// inner `some` binds a field that is itself returned (distinct from the outer
// none/some-none values). This is the same lowering path but pins that the
// inner field is bound to the CORRECT slot (a layout swap would bind the wrong
// thing or fail to type-check).
// ===========================================================================

#[test]
fn test_nested_some_some_binds_inner_field_distinct_values() {
    let mut env = imported_myoption_env();

    // addOne maps `some (some x) => x + 1`, distinguishing the inner field from
    // a constant; the some-none / none branches return fixed distinct values.
    elaborate_decls_into(
        &mut env,
        "def addOne (o : MyOption (MyOption Nat)) : Nat := match o with\n  \
         | MyOption.some (MyOption.some x) => Nat.succ x\n  \
         | MyOption.some MyOption.none => Nat.zero\n  \
         | MyOption.none => Nat.zero",
    );

    let nat = const_("Nat");
    let opt_nat = myoption_of(nat.clone());

    // some (some 4) -> 5.
    let four = succ(succ(succ(succ(const_("Nat.zero")))));
    let five = succ(four.clone());
    let val = some_of(opt_nat.clone(), some_of(nat.clone(), four));
    let call = Expr::app(const_("addOne"), val);
    assert!(
        def_eq(&env, &call, &five),
        "addOne (some (some 4)) must reduce to 4 + 1 = 5; got head {:?}",
        TypeChecker::new(&env).whnf(&call).kind()
    );
    // A different inner field gives a different result — the field binding is
    // genuinely consumed, not constant-folded.
    let zero_val = some_of(opt_nat.clone(), some_of(nat.clone(), const_("Nat.zero")));
    let call_zero = Expr::app(const_("addOne"), zero_val);
    assert!(
        def_eq(&env, &call_zero, &succ(const_("Nat.zero"))),
        "addOne (some (some 0)) must reduce to 0 + 1 = 1"
    );
    assert!(
        !def_eq(&env, &call, &call_zero),
        "different inner fields must yield different results (5 vs 1)"
    );
}

// ===========================================================================
// As-pattern (`x@(some y)`) on an imported inductive. The alias `x` binds the
// whole sub-term while the inner pattern `some y` still dispatches through a
// nested casesOn. Drives both the alias plan and the nested-ctor plan on the
// import path.
// ===========================================================================

#[test]
fn test_nested_as_pattern_on_imported_myoption() {
    let mut env = imported_myoption_env();

    // `aliasInner` matches the inner `some` via an as-pattern `p@(some y)`,
    // returning the inner field `y`; the some-none / none branches return
    // distinct constants. Confirms the alias binding does not disturb the
    // imported nested casesOn layout (the alias plan wraps the nested-ctor plan,
    // so both run through the fixed import-layout path).
    elaborate_decls_into(
        &mut env,
        "def aliasInner (o : MyOption (MyOption Nat)) : Nat := match o with\n  \
         | MyOption.some (p@(MyOption.some y)) => y\n  \
         | MyOption.some MyOption.none => Nat.succ Nat.zero\n  \
         | MyOption.none => Nat.zero",
    );

    // The body must compile through the imported MyOption.casesOn.
    let info = env
        .get_const(&Name::from_string("aliasInner"))
        .expect("aliasInner should be registered");
    let body = info.value.as_ref().expect("aliasInner is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("MyOption.casesOn")),
        "aliasInner must compile through the imported MyOption.casesOn, got: {:?}",
        body.collect_constants()
    );

    let nat = const_("Nat");
    let opt_nat = myoption_of(nat.clone());

    // some (some 3) -> 3 (the inner field via the as-pattern's inner `some y`).
    let three = succ(succ(succ(const_("Nat.zero"))));
    let val = some_of(opt_nat.clone(), some_of(nat.clone(), three.clone()));
    let call = Expr::app(const_("aliasInner"), val);
    assert!(
        def_eq(&env, &call, &three),
        "aliasInner (some (some 3)) must reduce to the inner field (3); got head {:?}",
        TypeChecker::new(&env).whnf(&call).kind()
    );
    // some none -> 1, none -> 0 (distinct branches still route correctly).
    let some_none = some_of(opt_nat.clone(), none_of(nat.clone()));
    assert!(
        def_eq(
            &env,
            &Expr::app(const_("aliasInner"), some_none),
            &succ(const_("Nat.zero"))
        ),
        "aliasInner (some none) must reduce to 1"
    );
    let none_outer = none_of(opt_nat);
    assert_eq!(
        whnf_head_const(&env, &Expr::app(const_("aliasInner"), none_outer)).as_deref(),
        Some("Nat.zero"),
        "aliasInner none must reduce to 0"
    );
}

// ===========================================================================
// Control: the SAME nested patterns work on the NATIVE path (where
// MyOption.casesOn IS a registered recursor in the MajorAfterMinors layout).
// The nested-ctor lowering fix is general — not import-specific — so this
// passing alongside the imported test confirms native behavior is correct and
// byte-for-byte unchanged.
// ===========================================================================

#[test]
fn test_nested_some_some_pattern_on_native_myoption_reduces_correctly() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.add_inductive(myoption_decl())
        .expect("MyOption should declare");

    // Native MyOption.casesOn IS a registered recursor (MajorAfterMinors).
    let rec = env
        .get_recursor(&Name::from_string("MyOption.casesOn"))
        .expect("native MyOption.casesOn should be a registered recursor");
    assert_eq!(
        rec.arg_order,
        clean_kernel::RecursorArgOrder::MajorAfterMinors,
        "native casesOn uses the MajorAfterMinors layout"
    );

    elaborate_decls_into(
        &mut env,
        "def unwrap2N (o : MyOption (MyOption Nat)) : Nat := match o with\n  \
         | MyOption.some (MyOption.some x) => x\n  \
         | MyOption.some MyOption.none => Nat.succ Nat.zero\n  \
         | MyOption.none => Nat.zero",
    );

    let nat = const_("Nat");
    let opt_nat = myoption_of(nat.clone());

    let six = succ(succ(succ(succ(succ(succ(const_("Nat.zero"))))))); // 6
    let some_some = some_of(opt_nat.clone(), some_of(nat.clone(), six.clone()));
    assert!(
        def_eq(&env, &Expr::app(const_("unwrap2N"), some_some), &six),
        "native unwrap2N (some (some 6)) must reduce to the inner field (6)"
    );
    let some_none = some_of(opt_nat.clone(), none_of(nat.clone()));
    assert!(
        def_eq(
            &env,
            &Expr::app(const_("unwrap2N"), some_none),
            &succ(const_("Nat.zero"))
        ),
        "native unwrap2N (some none) must reduce to 1"
    );
    let none_outer = none_of(opt_nat);
    assert_eq!(
        whnf_head_const(&env, &Expr::app(const_("unwrap2N"), none_outer)).as_deref(),
        Some("Nat.zero"),
        "native unwrap2N none must reduce to 0"
    );
}
