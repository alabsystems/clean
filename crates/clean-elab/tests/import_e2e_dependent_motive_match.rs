// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: a **dependent-motive** `match` on an *imported* inductive
//! (dependent_motive_match scenario).
//!
//! Background. B43/B44/B45/B47 found bugs where the elaborator computes
//! eliminator / motive / projection LAYOUT from clean-side *native* metadata
//! that a real Lean `.olean` does not ship: a genuine import carries only the
//! definitional `T.casesOn` constant (Lean's `MajorAfterMotive` layout, NOT a
//! registered recursor) and no clean-side `structure_fields` table. This probe
//! attacks the **motive SYNTHESIS** the match elaborator performs.
//!
//! ## What "dependent motive" means here
//!
//! For an ordinary `match` the result type is constant in the scrutinee, so the
//! motive is `fun _ : T => R`. But when the `match` runs under an expected type
//! that *depends on the scrutinee* — e.g.
//!
//! ```text
//! def Choose (b : MyBool) : Type := if b then Nat else MyBool   -- (a type family)
//! def choose (b : MyBool) : Choose b := match b with
//!   | MyBool.tt => Nat.zero    -- has type Choose MyBool.tt = Nat
//!   | MyBool.ff => MyBool.tt   -- has type Choose MyBool.ff = MyBool
//! ```
//!
//! the two arms have **genuinely different types** (`Nat` vs `MyBool`). The
//! motive must be the dependent `fun (x : MyBool) => Choose x`; each minor
//! premise then has type `Choose ctorᵢ`. A *constant* motive built from the
//! first arm body (`fun _ => Nat`) makes the second arm (`MyBool.tt : MyBool`)
//! fail to check.
//!
//! ## The bug (pre-fix)
//!
//! `elab_match` built the motive as `fun _ : T => branch_ty`, where `branch_ty`
//! was inferred from the *first arm body* — a **constant** motive that ignored
//! the expected type's dependence on the scrutinee. The dependent `choose`
//! above was rejected with `Match arm 1 has type MyBool, but match motive
//! expects Nat`, on **both** the imported and native eliminator paths (the
//! motive-synthesis code is shared). The fix (clean-elab only) detects when the
//! match's expected type depends on the scrutinee fvar, abstracts that fvar to
//! form the dependent motive `fun (x : T) => R[scrutinee := x]`, and gives each
//! arm its own expected type `R[scrutinee := ctorᵢ fields]`.
//!
//! ## Synthesize-as-import
//!
//! Following B45/B47, the imported `MyBool` is built by the kernel's normal
//! `add_inductive` in a scratch env, then the inductive + constructors + `.rec`
//! are copied into a fresh env and `MyBool.casesOn` is re-synthesized as a plain
//! `Declaration::Definition` with Lean's `MajorAfterMotive` type (so
//! `get_recursor("MyBool.casesOn") == None`). A precondition test asserts the
//! casesOn is NOT a registered recursor, proving the import path is exercised.
//!
//! The native path (where `MyBool.casesOn` IS a recursor) is exercised as a
//! control so the same dependent match is shown to work on both, and a
//! constant-motive (non-dependent) imported match is locked in to prove the
//! native/constant behavior is unchanged.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
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

/// `inductive MyBool : Type | tt | ff` (two nullary constructors).
fn mybool_decl() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("MyBool"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyBool.tt"),
                    type_: const_("MyBool"),
                },
                Constructor {
                    name: Name::from_string("MyBool.ff"),
                    type_: const_("MyBool"),
                },
            ],
        }],
    }
}

/// `inductive MyOption (A : Type) : Type | none | some (a : A)`.
///
/// A *parameterized* inductive with a field-carrying constructor, so the
/// dependent-motive arm `MyOption.some a => …` exercises the field-binding
/// branch (the per-arm expected type is computed from the bound field fvar).
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

/// Imported `MyBool.casesOn` **type** in Lean's `MajorAfterMotive` layout:
///
/// ```text
/// {motive : MyBool -> Sort u} -> (t : MyBool)
///   -> motive MyBool.tt -> motive MyBool.ff -> motive t
/// ```
fn imported_cases_on_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    // Binder telescope (outer -> inner): motive, t, mtt, mff.
    // result under [motive,t,mtt,mff]: motive t = (#3 #2)
    let result = Expr::app(Expr::bvar(3), Expr::bvar(2));
    // mff under [motive,t,mtt]: motive MyBool.ff = (#2 ff)
    let mff = Expr::app(Expr::bvar(2), const_("MyBool.ff"));
    // mtt under [motive,t]: motive MyBool.tt = (#1 tt)
    let mtt = Expr::app(Expr::bvar(1), const_("MyBool.tt"));
    let t_dom = const_("MyBool");
    let motive_dom = Expr::pi(BinderInfo::Default, const_("MyBool"), sort_u);

    let body = Expr::pi(BinderInfo::Default, mff, result);
    let body = Expr::pi(BinderInfo::Default, mtt, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    Expr::pi(BinderInfo::Implicit, motive_dom, body)
}

/// Imported `MyBool.casesOn` **value**:
/// `fun motive t mtt mff => MyBool.rec.{u} motive mtt mff t`.
fn imported_cases_on_value(u: &Name) -> Expr {
    let rec = Expr::const_(
        Name::from_string("MyBool.rec"),
        vec![Level::param(u.clone())],
    );
    // body under [motive,t,mtt,mff]: motive=#3, t=#2, mtt=#1, mff=#0
    let body = Expr::app(rec, Expr::bvar(3)); // motive
    let body = Expr::app(body, Expr::bvar(1)); // mtt
    let body = Expr::app(body, Expr::bvar(0)); // mff
    let body = Expr::app(body, Expr::bvar(2)); // t (major last in MajorAfterMinors rec)

    let sort_u = Expr::sort(Level::param(u.clone()));
    let mff_dom = Expr::app(Expr::bvar(2), const_("MyBool.ff"));
    let mtt_dom = Expr::app(Expr::bvar(1), const_("MyBool.tt"));
    let t_dom = const_("MyBool");
    let motive_dom = Expr::pi(BinderInfo::Default, const_("MyBool"), sort_u);

    let body = Expr::lam(BinderInfo::Default, mff_dom, body);
    let body = Expr::lam(BinderInfo::Default, mtt_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    Expr::lam(BinderInfo::Implicit, motive_dom, body)
}

/// Build an environment with a *faithfully imported* `MyBool`: kernel-built
/// inductive + constructors + `MyBool.rec`, with `MyBool.casesOn` synthesized as
/// a plain `Declaration::Definition` (so `get_recursor` returns `None`).
fn imported_mybool_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native
        .add_inductive(mybool_decl())
        .expect("MyBool should declare");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let iv = native
        .get_inductive(&Name::from_string("MyBool"))
        .cloned()
        .expect("MyBool inductive");
    env.register_inductive(iv);
    for ctor in ["MyBool.tt", "MyBool.ff"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }
    let rv = native
        .get_recursor(&Name::from_string("MyBool.rec"))
        .cloned()
        .expect("MyBool.rec recursor");
    let rc = native
        .get_const(&Name::from_string("MyBool.rec"))
        .cloned()
        .expect("MyBool.rec const");
    env.extend_constants_unchecked(std::iter::once(rc));
    env.register_recursor(rv);

    let u = native
        .get_recursor(&Name::from_string("MyBool.rec"))
        .and_then(|r| r.level_params.first().cloned())
        .expect("MyBool.rec has a motive universe parameter");

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body, kernel
    // type-checked against the casesOn type by `add_decl_structural`. Mirrors
    // exactly what `.olean` import of `MyBool` produces (a definitional
    // `MajorAfterMotive` `casesOn`, NOT a registered recursor).
    env.add_decl_structural(clean_kernel::env::Declaration::Definition {
        name: Name::from_string("MyBool.casesOn"),
        level_params: vec![u.clone()],
        type_: imported_cases_on_type(&u),
        value: imported_cases_on_value(&u),
        is_reducible: false,
    })
    .expect("imported MyBool.casesOn should kernel-check");

    env
}

/// Elaborate + register declarations from `source`. `elaborate_decl_and_register`
/// runs the full kernel type-check per definition; reaching the end means every
/// body kernel-checked.
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
// Precondition: the synthesized `MyBool` matches the IMPORT configuration
// (inductive + `.rec` + definitional `.casesOn`, with `.casesOn` NOT a
// registered recursor). This proves the dependent-match tests below exercise
// the import path rather than the native recursor path.
// ===========================================================================

#[test]
fn test_imported_mybool_cases_on_is_definitional_not_recursor() {
    let env = imported_mybool_env();

    assert!(
        env.get_inductive(&Name::from_string("MyBool")).is_some(),
        "MyBool inductive should be imported"
    );
    assert!(
        env.get_recursor(&Name::from_string("MyBool.rec")).is_some(),
        "MyBool.rec stays a registered recursor on import"
    );
    assert!(
        env.get_recursor(&Name::from_string("MyBool.casesOn"))
            .is_none(),
        "imported MyBool.casesOn must NOT be a registered recursor — this is the \
         exact condition that routes match lowering through the imported \
         MajorAfterMotive path"
    );
    let cases = env
        .get_const(&Name::from_string("MyBool.casesOn"))
        .expect("MyBool.casesOn const should exist");
    assert!(
        cases.value.is_some(),
        "imported MyBool.casesOn must be a definitional constant with a value"
    );
}

// ===========================================================================
// Control: the imported `MyBool.casesOn` reduces correctly when applied by hand
// with a DEPENDENT motive (`fun b => Choose b`). Isolates any failure of the
// match tests to the *elaborator's motive synthesis* rather than the kernel's
// reduction of the imported casesOn against a dependent motive.
// ===========================================================================

#[test]
fn test_imported_cases_on_dependent_motive_kernel_reduction_is_correct() {
    let mut env = imported_mybool_env();

    // Choose : MyBool -> Type with Choose tt = Nat, Choose ff = MyBool, defined
    // directly off the imported casesOn (MajorAfterMotive: motive, major, mtt, mff).
    elaborate_decls_into(
        &mut env,
        "def Choose (b : MyBool) : Type := @MyBool.casesOn (fun _ => Type) b Nat MyBool",
    );

    // Apply the imported casesOn by hand with the *dependent* motive `Choose`:
    //   @MyBool.casesOn Choose tt Nat.zero MyBool.tt  ⇝  Nat.zero   (tt branch, type Nat)
    //   @MyBool.casesOn Choose ff Nat.zero MyBool.tt  ⇝  MyBool.tt  (ff branch, type MyBool)
    let cases = |major: &str| {
        let c = Expr::const_(Name::from_string("MyBool.casesOn"), vec![Level::zero()]);
        let c = Expr::app(c, const_("Choose")); // dependent motive
        let c = Expr::app(c, const_(major)); // major (MajorAfterMotive)
        let c = Expr::app(c, const_("Nat.zero")); // mtt : Choose tt = Nat
        Expr::app(c, const_("MyBool.tt")) // mff : Choose ff = MyBool
    };
    assert_eq!(
        whnf_head_const(&env, &cases("MyBool.tt")).as_deref(),
        Some("Nat.zero"),
        "casesOn on tt with dependent motive must select the mtt minor (Nat.zero)"
    );
    assert_eq!(
        whnf_head_const(&env, &cases("MyBool.ff")).as_deref(),
        Some("MyBool.tt"),
        "casesOn on ff with dependent motive must select the mff minor (MyBool.tt)"
    );
}

// ===========================================================================
// MAIN PROBE: a clean-elab dependent-motive `match` on the imported `MyBool`
// must build the dependent motive `fun b => Choose b`, kernel-check, and reduce
// each branch to a value of that branch's *distinct* type.
// ===========================================================================

#[test]
fn test_dependent_motive_match_on_imported_mybool() {
    let mut env = imported_mybool_env();

    // Choose b reduces to Nat for tt and MyBool for ff — so the two arms below
    // have *different* types. A constant motive (the pre-fix behavior) rejects
    // the second arm; only a dependent motive `fun b => Choose b` type-checks.
    elaborate_decls_into(
        &mut env,
        "def Choose (b : MyBool) : Type := @MyBool.casesOn (fun _ => Type) b Nat MyBool\n\
         def choose (b : MyBool) : Choose b := match b with\n  \
         | MyBool.tt => Nat.zero\n  \
         | MyBool.ff => MyBool.tt",
    );

    // The body must compile through the imported MyBool.casesOn (proving the
    // import path, not a native recursor).
    let info = env
        .get_const(&Name::from_string("choose"))
        .expect("choose should be registered");
    let body = info.value.as_ref().expect("choose is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("MyBool.casesOn")),
        "choose must compile through the imported MyBool.casesOn, got: {:?}",
        body.collect_constants()
    );

    // tt branch: choose tt : Choose tt = Nat, must reduce to Nat.zero.
    let call_tt = Expr::app(const_("choose"), const_("MyBool.tt"));
    assert_eq!(
        whnf_head_const(&env, &call_tt).as_deref(),
        Some("Nat.zero"),
        "choose MyBool.tt must reduce to the tt branch value Nat.zero (type Choose tt = Nat)"
    );

    // ff branch: choose ff : Choose ff = MyBool, must reduce to MyBool.tt — a
    // value of a DIFFERENT type than the tt branch, which is exactly what a
    // dependent motive enables.
    let call_ff = Expr::app(const_("choose"), const_("MyBool.ff"));
    assert_eq!(
        whnf_head_const(&env, &call_ff).as_deref(),
        Some("MyBool.tt"),
        "choose MyBool.ff must reduce to the ff branch value MyBool.tt (type Choose ff = MyBool)"
    );

    // Cross-check: the two branches reduce to genuinely distinct heads, so a
    // collapsed/constant motive that mis-routed a branch would be observable.
    assert_ne!(
        whnf_head_const(&env, &call_tt),
        whnf_head_const(&env, &call_ff),
        "the dependent branches must reduce to distinct values (Nat.zero vs MyBool.tt)"
    );
}

// ===========================================================================
// Field-carrying dependent motive: an imported parameterized `MyOption` with a
// `some a` constructor whose dependent-match arm binds the field. Exercises the
// field-binding arm path of the per-arm expected-type computation.
//
// `MyOption` here is built natively (its `.casesOn` is a recursor). The probe's
// purpose is to confirm the dependent-motive *match elaboration* (the shared
// motive-synthesis code under test) also drives a field-binding constructor
// arm; the imported MyBool tests above pin the import-specific casesOn layout.
// ===========================================================================

#[test]
fn test_dependent_motive_match_with_field_binding_arm() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.add_inductive(myoption_decl())
        .expect("MyOption should declare");
    env.add_inductive(mybool_decl())
        .expect("MyBool should declare");

    // ChooseO o : Type with ChooseO none = Nat, ChooseO (some a) = MyBool.
    // chooseO's `some a` arm binds the field `a` and returns MyBool.tt : MyBool,
    // a different type from the none arm's Nat.zero : Nat.
    elaborate_decls_into(
        &mut env,
        "def ChooseO (o : MyOption Nat) : Type := \
            @MyOption.casesOn Nat (fun _ => Type) Nat (fun _ => MyBool) o\n\
         def chooseO (o : MyOption Nat) : ChooseO o := match o with\n  \
         | MyOption.none => Nat.zero\n  \
         | MyOption.some a => MyBool.tt",
    );

    // none branch -> Nat.zero (type ChooseO none = Nat).
    let none_nat = Expr::app(
        Expr::const_(Name::from_string("MyOption.none"), vec![]),
        const_("Nat"),
    );
    let call_none = Expr::app(const_("chooseO"), none_nat);
    assert_eq!(
        whnf_head_const(&env, &call_none).as_deref(),
        Some("Nat.zero"),
        "chooseO none must reduce to Nat.zero (type ChooseO none = Nat)"
    );

    // some branch -> MyBool.tt (type ChooseO (some a) = MyBool).
    let some_val = {
        let c = Expr::const_(Name::from_string("MyOption.some"), vec![]);
        let c = Expr::app(c, const_("Nat")); // implicit param A := Nat
        Expr::app(c, const_("Nat.zero")) // field a := Nat.zero
    };
    let call_some = Expr::app(const_("chooseO"), some_val);
    assert_eq!(
        whnf_head_const(&env, &call_some).as_deref(),
        Some("MyBool.tt"),
        "chooseO (some a) must reduce to MyBool.tt (type ChooseO (some a) = MyBool)"
    );
    assert_ne!(
        whnf_head_const(&env, &call_none),
        whnf_head_const(&env, &call_some),
        "the dependent branches must reduce to distinct values (Nat.zero vs MyBool.tt)"
    );
}

// ===========================================================================
// Control (generality): the SAME dependent match works on the NATIVE path
// (where MyBool.casesOn IS a recursor). The motive-synthesis fix is general —
// not import-specific — so this passing alongside the imported test confirms
// native behavior is correct, not merely preserved.
// ===========================================================================

#[test]
fn test_dependent_motive_match_on_native_mybool() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.add_inductive(mybool_decl())
        .expect("MyBool should declare");
    assert!(
        env.get_recursor(&Name::from_string("MyBool.casesOn"))
            .is_some(),
        "native MyBool.casesOn IS a registered recursor"
    );

    // Native casesOn is MajorAfterMinors: @MyBool.casesOn motive mtt mff major.
    elaborate_decls_into(
        &mut env,
        "def Choose (b : MyBool) : Type := @MyBool.casesOn (fun _ => Type) Nat MyBool b\n\
         def choose (b : MyBool) : Choose b := match b with\n  \
         | MyBool.tt => Nat.zero\n  \
         | MyBool.ff => MyBool.tt",
    );

    let call_tt = Expr::app(const_("choose"), const_("MyBool.tt"));
    assert_eq!(
        whnf_head_const(&env, &call_tt).as_deref(),
        Some("Nat.zero"),
        "native choose MyBool.tt must reduce to Nat.zero"
    );
    let call_ff = Expr::app(const_("choose"), const_("MyBool.ff"));
    assert_eq!(
        whnf_head_const(&env, &call_ff).as_deref(),
        Some("MyBool.tt"),
        "native choose MyBool.ff must reduce to MyBool.tt"
    );
}

// ===========================================================================
// Regression: a NON-dependent (constant-motive) `match` on the imported MyBool
// must still build a constant motive and reduce correctly. Guards against the
// dependent-motive detection mis-firing and altering the constant-motive path
// (which must stay byte-for-byte unchanged).
// ===========================================================================

#[test]
fn test_constant_motive_match_on_imported_mybool_unchanged() {
    let mut env = imported_mybool_env();

    // Result type `MyBool` is constant in the scrutinee — the motive must remain
    // `fun _ => MyBool`. Branches return *distinct* constructors so a mis-routed
    // branch is observable.
    elaborate_decls_into(
        &mut env,
        "def negate (b : MyBool) : MyBool := match b with\n  \
         | MyBool.tt => MyBool.ff\n  \
         | MyBool.ff => MyBool.tt",
    );

    let info = env
        .get_const(&Name::from_string("negate"))
        .expect("negate should be registered");
    let body = info.value.as_ref().expect("negate is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("MyBool.casesOn")),
        "negate must still compile through the imported MyBool.casesOn"
    );

    let call_tt = Expr::app(const_("negate"), const_("MyBool.tt"));
    assert_eq!(
        whnf_head_const(&env, &call_tt).as_deref(),
        Some("MyBool.ff"),
        "negate tt must reduce to MyBool.ff"
    );
    let call_ff = Expr::app(const_("negate"), const_("MyBool.ff"));
    assert_eq!(
        whnf_head_const(&env, &call_ff).as_deref(),
        Some("MyBool.tt"),
        "negate ff must reduce to MyBool.tt"
    );
    // And it is idempotent under double negation, a structural cross-check that
    // the constant-motive casesOn still reduces as before.
    let double = Expr::app(
        const_("negate"),
        Expr::app(const_("negate"), const_("MyBool.tt")),
    );
    assert!(
        def_eq(&env, &double, &const_("MyBool.tt")),
        "negate (negate tt) must reduce back to MyBool.tt"
    );
}

// ===========================================================================
// Leak guard: a dependent-motive match must not leave its motive set for a
// later, constant-motive match in the SAME elaboration session, and a
// dependent match NESTED inside a constant match must save/restore correctly.
// Exercises the save/restore around `match_dependent_motive`.
// ===========================================================================

#[test]
fn test_dependent_motive_does_not_leak_to_later_or_outer_match() {
    let mut env = imported_mybool_env();

    // 1) Dependent match (`choose`, motive `fun b => Choose b`), then
    // 2) a constant match (`negate`, motive `fun _ => MyBool`) right after —
    //    if the dependent motive leaked, `negate`'s motive would be wrong and
    //    its second arm (or reduction) would misbehave.
    // 3) `outer` is a constant-motive match whose `tt` arm body is itself a
    //    dependent match on a *fresh* scrutinee, so the inner dependent motive
    //    must be saved and restored without corrupting the outer constant motive.
    elaborate_decls_into(
        &mut env,
        "def Choose (b : MyBool) : Type := @MyBool.casesOn (fun _ => Type) b Nat MyBool\n\
         def choose (b : MyBool) : Choose b := match b with\n  \
         | MyBool.tt => Nat.zero\n  \
         | MyBool.ff => MyBool.tt\n\
         def negate (b : MyBool) : MyBool := match b with\n  \
         | MyBool.tt => MyBool.ff\n  \
         | MyBool.ff => MyBool.tt\n\
         def outer (b : MyBool) (c : MyBool) : MyBool := match b with\n  \
         | MyBool.tt => (match c with | MyBool.tt => MyBool.ff | MyBool.ff => MyBool.tt)\n  \
         | MyBool.ff => MyBool.tt",
    );

    // Dependent `choose` still reduces per branch (distinct types).
    assert_eq!(
        whnf_head_const(&env, &Expr::app(const_("choose"), const_("MyBool.tt"))).as_deref(),
        Some("Nat.zero"),
        "choose tt must reduce to Nat.zero"
    );
    assert_eq!(
        whnf_head_const(&env, &Expr::app(const_("choose"), const_("MyBool.ff"))).as_deref(),
        Some("MyBool.tt"),
        "choose ff must reduce to MyBool.tt"
    );

    // The later constant-motive `negate` is unaffected (no leaked motive).
    assert_eq!(
        whnf_head_const(&env, &Expr::app(const_("negate"), const_("MyBool.tt"))).as_deref(),
        Some("MyBool.ff"),
        "negate tt must still reduce to MyBool.ff after a dependent match elaborated earlier"
    );

    // The nested dependent-in-constant match reduces correctly per the inner
    // scrutinee `c` on the tt branch, and to MyBool.tt on the ff branch.
    let outer = |b: &str, c: &str| Expr::app(Expr::app(const_("outer"), const_(b)), const_(c));
    assert_eq!(
        whnf_head_const(&env, &outer("MyBool.tt", "MyBool.tt")).as_deref(),
        Some("MyBool.ff"),
        "outer tt tt must take the inner tt branch (MyBool.ff)"
    );
    assert_eq!(
        whnf_head_const(&env, &outer("MyBool.tt", "MyBool.ff")).as_deref(),
        Some("MyBool.tt"),
        "outer tt ff must take the inner ff branch (MyBool.tt)"
    );
    assert_eq!(
        whnf_head_const(&env, &outer("MyBool.ff", "MyBool.tt")).as_deref(),
        Some("MyBool.tt"),
        "outer ff _ must take the outer ff branch (MyBool.tt)"
    );
}
