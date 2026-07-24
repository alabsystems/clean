// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: **Nat-literal / numeric patterns** in a `match` on an *imported*
//! `Nat` (literal_nat_pattern scenario).
//!
//! ## Background — the import probe vein
//!
//! A real Lean `.olean` ships an inductive `T` with ONLY its projection
//! functions + a *definitional* `T.casesOn` constant (Lean's `MajorAfterMotive`
//! layout: `motive → indices → major → minors`), registered as a plain
//! `Definition`, NOT as a recursor — so `get_recursor("T.casesOn") == None` and
//! there is no clean-side metadata. Several elaborator paths historically
//! computed eliminator / minor-premise layout from clean-side *native* metadata
//! a genuine import does not carry; for an imported `T.casesOn` the major
//! premise can land in a minor slot (kernel reject, or — worse — a silent wrong
//! reduction that type-checks but selects the wrong branch).
//!
//! ## What this file probes
//!
//! `match n with | 0 => … | Nat.succ k => …` and the literal-sugar variants
//! `| 0 => … | n + 1 => …` lower the literal `0` to a `Nat.zero` minor premise
//! and the non-zero / numeral-add arms to `Nat.succ` minor premises (see
//! `elab_match/mod.rs::desugar_nonzero_nat_lit` and
//! `desugar_nat_numeral_add_pattern`). Those minor premises are slotted into a
//! `Nat.casesOn` application built by the *top-level* match lowering, which must
//! place the scrutinee (major premise) in the position the *imported*
//! `MajorAfterMotive` `Nat.casesOn` actually expects. If the literal-pattern
//! path mislaid the major premise for the imported layout, a `0`-arm vs a
//! `succ`-arm would select the wrong branch or fail to reduce.
//!
//! The literal/numeric pattern path is gated to `Nat` scrutinees
//! (`ensure_nat_pattern_scrutinee`), so the import probe uses a faithfully
//! *imported* `Nat`: the real kernel-built `Nat` family + constructors +
//! `Nat.rec`, but `Nat.casesOn` synthesized as a plain `Declaration::Definition`
//! in the `MajorAfterMotive` layout. A precondition test asserts
//! `get_recursor("Nat.casesOn") == None`, proving the literal-pattern lowering
//! below runs through the import path.
//!
//! ## Result
//!
//! Imported Nat-literal patterns already lower correctly: the top-level match
//! builder consults `get_recursor(...).arg_order` (absent ⇒ `MajorAfterMotive`)
//! and the literal arms route through the shared minor-premise builders, so the
//! scrutinee is placed correctly. This file LOCKS IN that behavior with
//! distinct branch values (so a wrong slot would surface as a different result,
//! not silently) across the `0 | succ k`, `0 | n+1`, and multi-literal
//! (`0 | 1 | 2 | _`) forms. A NATIVE control (where `Nat.casesOn` IS a
//! registered recursor) drives the SAME patterns so the behavior is shown
//! general, not import-specific.

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

/// Reduce `expr` to WHNF and return the head `Const` name.
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

fn zero() -> Expr {
    const_("Nat.zero")
}

fn succ(n: Expr) -> Expr {
    Expr::app(const_("Nat.succ"), n)
}

/// The Church-style numeral `Nat.succ^k Nat.zero`.
fn nat_lit(k: u64) -> Expr {
    let mut e = zero();
    for _ in 0..k {
        e = succ(e);
    }
    e
}

/// `inductive Nat : Type | zero | succ (n : Nat)` — the canonical kernel `Nat`.
fn nat_decl() -> InductiveDecl {
    let nat_const = const_("Nat");
    // Nat : Type
    let nat_type = Expr::sort(Level::succ(Level::zero()));
    // Nat.zero : Nat
    let zero_ty = nat_const.clone();
    // Nat.succ : Nat -> Nat
    let succ_ty = Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone());
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Nat"),
            type_: nat_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: zero_ty,
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: succ_ty,
                },
            ],
        }],
    }
}

/// Imported `Nat.casesOn` **type** in Lean's `MajorAfterMotive` layout
/// (`Nat` has no parameters and no indices, so the major premise comes right
/// after the motive):
///
/// ```text
/// {motive : Nat -> Sort u} -> (t : Nat)
///   -> motive Nat.zero
///   -> ((n : Nat) -> motive (Nat.succ n))
///   -> motive t
/// ```
fn imported_cases_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    let nat = const_("Nat");

    // Telescope (outer -> inner): motive, t, m_zero, m_succ.
    // result `motive t` under [motive, t, m_zero, m_succ]: motive=3, t=2.
    let result = Expr::app(Expr::bvar(3), Expr::bvar(2));

    // m_succ domain under [motive, t, m_zero]:
    //   (n : Nat) -> motive (Nat.succ n)
    //   inside the `n` binder [motive, t, m_zero, n]: motive=3, n=0.
    let m_succ_body = Expr::app(Expr::bvar(3), succ(Expr::bvar(0)));
    let m_succ_dom = Expr::pi(BinderInfo::Default, nat.clone(), m_succ_body);

    // m_zero domain under [motive, t]: motive Nat.zero (motive=1).
    let m_zero_dom = Expr::app(Expr::bvar(1), zero());

    // t domain under [motive]: Nat.
    let t_dom = nat.clone();
    // motive domain (outermost): Nat -> Sort u.
    let motive_dom = Expr::pi(BinderInfo::Default, nat, sort_u);

    let body = Expr::pi(BinderInfo::Default, m_succ_dom, result);
    let body = Expr::pi(BinderInfo::Default, m_zero_dom, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    Expr::pi(BinderInfo::Implicit, motive_dom, body)
}

/// Imported `Nat.casesOn` **value**, unfolding to `Nat.rec`:
///
/// ```text
/// fun motive t m_zero m_succ =>
///   Nat.rec.{u} motive m_zero (fun n _ih => m_succ n) t
/// ```
///
/// `Nat.rec` is `MajorAfterMinors` (motive → minors → major) and its `succ`
/// minor carries an induction hypothesis `(n : Nat) → motive n → motive
/// (succ n)`; `casesOn`'s `succ` minor takes only `(n : Nat)`, so the body
/// drops the IH and reorders the major to the end.
fn imported_cases_value(u: &Name) -> Expr {
    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::param(u.clone())]);
    let sort_u = Expr::sort(Level::param(u.clone()));
    let nat = const_("Nat");

    // We need a `Nat.rec`-shaped succ minor `fun (n : Nat) (_ih : motive n) =>
    // m_succ n`. Build it under [motive, t, m_zero, m_succ, n, ih]:
    //   motive=5, m_succ=2, n=1.
    // Body `m_succ n`: m_succ=#2, n=#1.
    let rec_succ_body = Expr::app(Expr::bvar(2), Expr::bvar(1));
    // ih domain under [motive, t, m_zero, m_succ, n]: motive n (motive=4, n=0).
    let ih_dom = Expr::app(Expr::bvar(4), Expr::bvar(0));
    let rec_succ_minor = Expr::lam(BinderInfo::Default, ih_dom, rec_succ_body);
    // n domain under [motive, t, m_zero, m_succ]: Nat.
    let rec_succ_minor = Expr::lam(BinderInfo::Default, nat.clone(), rec_succ_minor);

    // body under [motive(3), t(2), m_zero(1), m_succ(0)]:
    //   Nat.rec motive m_zero rec_succ_minor t
    let body = Expr::app(rec, Expr::bvar(3)); // motive
    let body = Expr::app(body, Expr::bvar(1)); // m_zero
    let body = Expr::app(body, rec_succ_minor); // succ minor (with IH)
    let body = Expr::app(body, Expr::bvar(2)); // major t (MajorAfterMinors)

    // Rebuild the binder domains (mirroring the casesOn type), as lambdas.
    let m_succ_body = Expr::app(Expr::bvar(3), succ(Expr::bvar(0)));
    let m_succ_dom = Expr::pi(BinderInfo::Default, nat.clone(), m_succ_body);
    let m_zero_dom = Expr::app(Expr::bvar(1), zero());
    let t_dom = nat.clone();
    let motive_dom = Expr::pi(BinderInfo::Default, nat, sort_u);

    let body = Expr::lam(BinderInfo::Default, m_succ_dom, body);
    let body = Expr::lam(BinderInfo::Default, m_zero_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    Expr::lam(BinderInfo::Implicit, motive_dom, body)
}

/// Copy the kernel-built `Nat` family / constructors / `Nat.rec` from a scratch
/// env into `env`, mirroring an `.olean` load (no recursor registration for the
/// `.casesOn`).
fn copy_nat_core(native: &Environment, env: &mut Environment) {
    let iv = native
        .get_inductive(&Name::from_string("Nat"))
        .cloned()
        .expect("scratch env has Nat");
    env.register_inductive(iv);
    for ctor in ["Nat.zero", "Nat.succ"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }
    let rv = native
        .get_recursor(&Name::from_string("Nat.rec"))
        .cloned()
        .expect("Nat.rec recursor");
    let rc = native
        .get_const(&Name::from_string("Nat.rec"))
        .cloned()
        .expect("Nat.rec const");
    env.extend_constants_unchecked(std::iter::once(rc));
    env.register_recursor(rv);
}

/// Build an environment with a *faithfully imported* `Nat`: the real
/// kernel-built family + constructors + `Nat.rec`, but `Nat.casesOn` as a plain
/// `Declaration::Definition` (so `get_recursor("Nat.casesOn")` returns `None`).
///
/// The `Nat` family is built from a fresh `add_inductive(nat_decl())` (NOT
/// `init_nat`, which would register `Nat.casesOn` as a recursor — defeating the
/// import probe).
fn imported_nat_env() -> Environment {
    let mut native = Environment::new();
    native
        .add_inductive(nat_decl())
        .expect("Nat should declare in scratch env");

    let mut env = Environment::new();
    copy_nat_core(&native, &mut env);

    let u = native
        .get_recursor(&Name::from_string("Nat.rec"))
        .and_then(|r| r.level_params.first().cloned())
        .expect("Nat.rec has a motive universe parameter");

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body, kernel
    // type-checked against the casesOn type by `add_decl_structural`. This
    // reproduces exactly what an `.olean` import of `Nat` ships (recursor
    // present, `.casesOn` a definitional `MajorAfterMotive` constant, no
    // clean-side recursor registration). No production path is involved;
    // mirrors the B43+ import fixtures. Tracking: import-probe vein.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("Nat.casesOn"),
        level_params: vec![u.clone()],
        type_: imported_cases_type(&u),
        value: imported_cases_value(&u),
        is_reducible: false,
    })
    .expect("imported Nat.casesOn definition should kernel-check");

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
// Precondition: the synthesized `Nat` matches the IMPORT configuration
// (inductive + `Nat.rec` + definitional `Nat.casesOn`, `.casesOn` NOT a
// registered recursor). This proves the literal-pattern tests below exercise
// the import path rather than the native recursor path.
// ===========================================================================

#[test]
fn test_imported_nat_cases_on_is_definitional_not_recursor() {
    let env = imported_nat_env();

    let ind = env
        .get_inductive(&Name::from_string("Nat"))
        .expect("Nat inductive should be imported");
    assert_eq!(ind.num_params, 0, "Nat has no parameters");
    assert_eq!(ind.num_indices, 0, "Nat has no indices");

    assert!(
        env.get_recursor(&Name::from_string("Nat.rec")).is_some(),
        "Nat.rec stays a registered recursor on import"
    );
    assert!(
        env.get_recursor(&Name::from_string("Nat.casesOn"))
            .is_none(),
        "imported Nat.casesOn must NOT be a registered recursor — this is the \
         exact condition that routes literal-pattern lowering through the \
         imported MajorAfterMotive path"
    );
    let cases = env
        .get_const(&Name::from_string("Nat.casesOn"))
        .expect("Nat.casesOn const should exist");
    assert!(
        cases.value.is_some(),
        "imported Nat.casesOn must be a definitional constant with a value"
    );
}

// ===========================================================================
// MAIN PROBE: literal `0` arm + explicit `Nat.succ k` arm on an imported `Nat`.
// The `0` literal lowers to a `Nat.zero` minor premise; the `Nat.succ k` arm to
// a `Nat.succ` minor premise binding the predecessor. The top-level match
// builder must place the scrutinee (major) in the imported MajorAfterMotive
// slot so each literal arm selects the correct branch.
//
// Distinct branch values make a wrong layout observable: a mis-ordered casesOn
// either fails to kernel-check or reduces the wrong branch.
// ===========================================================================

#[test]
fn test_zero_succ_literal_pattern_on_imported_nat_reduces_correctly() {
    let mut env = imported_nat_env();

    // classify : Nat -> Nat
    //   | 0          => 7      -- literal-zero arm (Nat.zero minor)
    //   | Nat.succ k => k      -- predecessor (binds the succ field)
    elaborate_decls_into(
        &mut env,
        "def classify (n : Nat) : Nat := match n with\n  \
         | 0 => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))\n  \
         | Nat.succ k => k",
    );

    // The body must compile through the imported Nat.casesOn (the only
    // eliminator available for a non-recursive match), proving the import path.
    let info = env
        .get_const(&Name::from_string("classify"))
        .expect("classify should be registered");
    let body = info.value.as_ref().expect("classify is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Nat.casesOn")),
        "classify must compile through the imported Nat.casesOn, got: {:?}",
        body.collect_constants()
    );

    // classify 0 -> 7 (literal-zero branch).
    let call_zero = Expr::app(const_("classify"), nat_lit(0));
    assert!(
        def_eq(&env, &call_zero, &nat_lit(7)),
        "classify 0 must reduce to the literal-zero branch (7); got head {:?}",
        TypeChecker::new(&env).whnf(&call_zero).kind()
    );

    // classify 5 -> 4 (predecessor; succ branch binds the field).
    let call_five = Expr::app(const_("classify"), nat_lit(5));
    assert!(
        def_eq(&env, &call_five, &nat_lit(4)),
        "classify 5 must reduce to the predecessor (4); got head {:?}",
        TypeChecker::new(&env).whnf(&call_five).kind()
    );

    // classify 1 -> 0 (predecessor of 1). Distinct from the zero branch (7).
    let call_one = Expr::app(const_("classify"), nat_lit(1));
    assert!(
        def_eq(&env, &call_one, &nat_lit(0)),
        "classify 1 must reduce to the predecessor (0); got head {:?}",
        TypeChecker::new(&env).whnf(&call_one).kind()
    );

    // The zero branch and the succ branch reduce to genuinely distinct values,
    // so a wrong slot (the bug class) surfaces as a different result.
    assert!(
        !def_eq(&env, &call_zero, &call_one),
        "the zero branch (7) and the succ-of-zero branch (0) must differ — \
         confirming the literal arm does not collapse into the succ arm"
    );
    assert!(
        !def_eq(&env, &call_five, &call_zero),
        "classify 5 (4) must not collapse to the zero branch (7)"
    );
}

// ===========================================================================
// `n + 1` numeral-add sugar on an imported `Nat`. `| 0 => … | n + 1 => …` is
// the idiomatic Lean form; the `n + 1` pattern lowers to a `Nat.succ n` minor
// premise (binding the predecessor `n`) via `desugar_nat_numeral_add_pattern`.
// Confirms the numeral-add path slots the major correctly for the import layout.
// ===========================================================================

#[test]
fn test_numeral_add_pattern_on_imported_nat_reduces_correctly() {
    let mut env = imported_nat_env();

    // pred : Nat -> Nat
    //   | 0     => 0
    //   | n + 1 => n        -- predecessor via numeral-add sugar
    elaborate_decls_into(
        &mut env,
        "def predOr (m : Nat) : Nat := match m with\n  \
         | 0 => Nat.zero\n  \
         | n + 1 => n",
    );

    let info = env
        .get_const(&Name::from_string("predOr"))
        .expect("predOr should be registered");
    let body = info.value.as_ref().expect("predOr is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Nat.casesOn")),
        "predOr must compile through the imported Nat.casesOn, got: {:?}",
        body.collect_constants()
    );

    // predOr 0 -> 0.
    let call_zero = Expr::app(const_("predOr"), nat_lit(0));
    assert_eq!(
        whnf_head_const(&env, &call_zero).as_deref(),
        Some("Nat.zero"),
        "predOr 0 must reduce to the zero branch (0)"
    );

    // predOr 3 -> 2 (predecessor binds n correctly through the import layout).
    let call_three = Expr::app(const_("predOr"), nat_lit(3));
    assert!(
        def_eq(&env, &call_three, &nat_lit(2)),
        "predOr 3 must reduce to the predecessor (2); got head {:?}",
        TypeChecker::new(&env).whnf(&call_three).kind()
    );

    // predOr 1 -> 0 (predecessor of 1). Distinct binding from the literal-zero
    // arm: both reduce to 0, but via genuinely different branches (zero vs succ).
    // (`def_eq` rather than a head-const check: the kernel may normalize a fully
    // reduced `Nat.zero` to its literal representation `Lit(Nat(0))`.)
    let call_one = Expr::app(const_("predOr"), nat_lit(1));
    assert!(
        def_eq(&env, &call_one, &nat_lit(0)),
        "predOr 1 must reduce to the predecessor (0); got {:?}",
        TypeChecker::new(&env).whnf(&call_one).kind()
    );

    // The numeral-add field binding is genuinely consumed, not constant-folded:
    // distinct inputs give distinct predecessors.
    assert!(
        !def_eq(&env, &call_three, &call_one),
        "predOr 3 (2) and predOr 1 (0) must differ — the numeral-add field is \
         genuinely bound, not constant-folded"
    );
}

// ===========================================================================
// MULTI-LITERAL dispatch: `| 0 => … | 1 => … | 2 => … | _ => …` on an imported
// `Nat`. The non-zero literals `1` and `2` desugar to NESTED `Nat.succ`
// patterns (`Nat.succ Nat.zero`, `Nat.succ (Nat.succ Nat.zero)`), whose inner
// sub-patterns lower through the nested-ctor casesOn — which must ALSO use the
// imported MajorAfterMotive layout. Four distinct branch values make any
// mis-dispatch (wrong literal selecting the wrong branch) observable.
// ===========================================================================

#[test]
fn test_multi_literal_pattern_on_imported_nat_reduces_correctly() {
    let mut env = imported_nat_env();

    // grade : Nat -> Nat
    //   | 0 => 10   | 1 => 20   | 2 => 30   | _ => 40
    // Distinct values so a wrong literal-arm dispatch is visible.
    elaborate_decls_into(
        &mut env,
        "def grade (n : Nat) : Nat := match n with\n  \
         | 0 => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))\n  \
         | 1 => Nat.succ Nat.zero\n  \
         | 2 => Nat.zero\n  \
         | _ => Nat.succ (Nat.succ Nat.zero)",
    );

    let info = env
        .get_const(&Name::from_string("grade"))
        .expect("grade should be registered");
    let body = info.value.as_ref().expect("grade is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Nat.casesOn")),
        "grade must compile through the imported Nat.casesOn, got: {:?}",
        body.collect_constants()
    );

    // grade 0 -> 10.
    let call0 = Expr::app(const_("grade"), nat_lit(0));
    assert!(
        def_eq(&env, &call0, &nat_lit(10)),
        "grade 0 must reduce to 10; got head {:?}",
        TypeChecker::new(&env).whnf(&call0).kind()
    );
    // grade 1 -> 1 (Nat.succ Nat.zero).
    let call1 = Expr::app(const_("grade"), nat_lit(1));
    assert!(
        def_eq(&env, &call1, &nat_lit(1)),
        "grade 1 must reduce to 1; got head {:?}",
        TypeChecker::new(&env).whnf(&call1).kind()
    );
    // grade 2 -> 0.
    let call2 = Expr::app(const_("grade"), nat_lit(2));
    assert_eq!(
        whnf_head_const(&env, &call2).as_deref(),
        Some("Nat.zero"),
        "grade 2 must reduce to 0"
    );
    // grade 3 (the wildcard) -> 2.
    let call3 = Expr::app(const_("grade"), nat_lit(3));
    assert!(
        def_eq(&env, &call3, &nat_lit(2)),
        "grade 3 must reduce to the wildcard branch (2); got head {:?}",
        TypeChecker::new(&env).whnf(&call3).kind()
    );

    // All four literal arms select genuinely distinct branches.
    assert!(
        !def_eq(&env, &call0, &call1)
            && !def_eq(&env, &call1, &call2)
            && !def_eq(&env, &call2, &call3)
            && !def_eq(&env, &call0, &call3),
        "the four literal/wildcard arms (10, 1, 0, 2) must each select a \
         genuinely distinct branch — a wrong literal dispatch would collapse two"
    );
}

// ===========================================================================
// Control: the SAME literal/numeric patterns work on the NATIVE path (where
// `Nat.casesOn` IS a registered recursor in the MajorAfterMinors layout). This
// passing alongside the imported tests confirms the literal-pattern lowering is
// general — not import-specific — and that native behavior is unchanged.
// ===========================================================================

#[test]
fn test_literal_patterns_on_native_nat_reduce_correctly() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    // Native Nat.casesOn IS a registered recursor (MajorAfterMinors).
    let rec = env
        .get_recursor(&Name::from_string("Nat.casesOn"))
        .expect("native Nat.casesOn should be a registered recursor");
    assert_eq!(
        rec.arg_order,
        clean_kernel::RecursorArgOrder::MajorAfterMinors,
        "native casesOn uses the MajorAfterMinors layout"
    );

    elaborate_decls_into(
        &mut env,
        "def classifyN (n : Nat) : Nat := match n with\n  \
         | 0 => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))\n  \
         | Nat.succ k => k\n\
         def predOrN (m : Nat) : Nat := match m with\n  \
         | 0 => Nat.zero\n  \
         | n + 1 => n",
    );

    // classifyN 0 -> 7, classifyN 5 -> 4 (same as imported).
    assert!(
        def_eq(
            &env,
            &Expr::app(const_("classifyN"), nat_lit(0)),
            &nat_lit(7)
        ),
        "native classifyN 0 must reduce to 7"
    );
    assert!(
        def_eq(
            &env,
            &Expr::app(const_("classifyN"), nat_lit(5)),
            &nat_lit(4)
        ),
        "native classifyN 5 must reduce to the predecessor (4)"
    );

    // predOrN 3 -> 2, predOrN 0 -> 0 (numeral-add).
    assert!(
        def_eq(&env, &Expr::app(const_("predOrN"), nat_lit(3)), &nat_lit(2)),
        "native predOrN 3 must reduce to the predecessor (2)"
    );
    assert_eq!(
        whnf_head_const(&env, &Expr::app(const_("predOrN"), nat_lit(0))).as_deref(),
        Some("Nat.zero"),
        "native predOrN 0 must reduce to 0"
    );
}
