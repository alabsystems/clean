// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: `optParam` / `autoParam` DEFAULT ARGUMENTS on an *imported*
//! declaration (autoparam_optparam scenario).
//!
//! ## What a real `.olean` ships
//!
//! In Lean 4 a parameter with a default value `(x : α := v)` is *not* recorded
//! as clean-side metadata. It is encoded in the kernel/`.olean` as a parameter
//! whose **type is literally `optParam α v`**, where
//!
//! ```text
//! @[reducible] def optParam.{u} (α : Sort u) (default : α) : Sort u := α
//! ```
//!
//! When the optional argument is omitted at a use site, the *elaborator* inserts
//! `v`. A tactic-default `(x : α := by tac)` is encoded as `autoParam α tac`
//! (the `tac` slot is a `Syntax`); the elaborator runs `tac` to synthesise the
//! argument. A real `.olean` therefore ships only the function/constructor whose
//! parameter type is the raw `optParam …` / `autoParam …` application — no
//! default-argument table, no `ParamDesc.default_value`, nothing on the
//! clean side.
//!
//! ## Synthesize-as-import (mirrors the other `import_e2e_*` probes)
//!
//! We register the reducible `optParam` definition exactly as Lean's prelude
//! does, then synthesize an imported `def` / structure constructor whose
//! parameter type is literally `optParam.{1} Nat <default>`, kernel-checked via
//! `add_decl_structural`. The result is bit-identical to a real `.olean` member:
//! the parameter type is the raw `optParam` application, and there is **no**
//! clean-side default metadata. Preconditions assert that configuration so the
//! test stays honest about exercising the import path.
//!
//! ## The bug this pins (fixed in this change)
//!
//! clean-elab's application / bidirectional-checking machinery never detected an
//! explicit `optParam α default` parameter, so for an *imported* declaration the
//! default was **not inserted**: `def useDefault : Nat := addDefault` elaborated
//! `addDefault` as a bare function value (`optParam Nat 2 → Nat`) and failed the
//! kernel check with `expected Nat, got Pi(optParam Nat 2 → Nat)` — an arity
//! error rather than the value `2`. The fix teaches `apply_implicit_to_expected_type`
//! and the end of the application loop to recognise the raw `optParam` parameter
//! type and supply its packaged default. Distinct default values (2 / 3 / 5)
//! make a missing or wrong default observable rather than masked.
//!
//! `autoParam` (tactic-synthesised defaults) is a genuine, larger gap — the
//! elaborator does not yet run the named tactic at application sites — and is
//! pinned with a flip-on-fix assertion below (NOT `#[ignore]`), so it converts
//! to a failure the moment the feature lands.

use clean_kernel::env::{Declaration, Environment};
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

fn succ(n: Expr) -> Expr {
    Expr::app(const_("Nat.succ"), n)
}

/// The Church numeral for `n` built from `Nat.zero` / `Nat.succ` (distinct,
/// kernel-reducible witnesses — no `OfNat`/literal machinery needed).
fn nat(n: u32) -> Expr {
    let mut e = const_("Nat.zero");
    for _ in 0..n {
        e = succ(e);
    }
    e
}

/// `optParam.{1} Nat default` — the parameter type a real `.olean` ships for an
/// explicit `(x : Nat := default)`. `Nat : Type 0 = Sort 1`, so the carrier's
/// universe is `Level::succ(Level::zero())`; the constant must carry that level
/// or the reducible `optParam` definition cannot delta-unfold to `Nat`.
fn opt_param_nat(default: Expr) -> Expr {
    let op = Expr::const_(
        Name::from_string("optParam"),
        vec![Level::succ(Level::zero())],
    );
    Expr::app(Expr::app(op, const_("Nat")), default)
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

/// Register the reducible `optParam` definition exactly as Lean's prelude does:
/// `@[reducible] def optParam.{u} (α : Sort u) (default : α) : Sort u := α`.
fn register_opt_param(env: &mut Environment) {
    let u = Name::from_string("u");
    let sort_u = Expr::sort(Level::param(u.clone()));
    // (α : Sort u) → (default : α) → Sort u
    let ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), sort_u.clone()),
    );
    // fun (α : Sort u) (default : α) => α
    let value = Expr::lam(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    // SOUNDNESS: test-only synthesis of the prelude `optParam` constant, the
    // exact reducible definition every Lean `.olean` carries. Kernel
    // type-checked by `add_decl_structural`; no production path is involved.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("optParam"),
        level_params: vec![u],
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("optParam should kernel-check and declare");
}

/// Base env with `Nat` and the reducible `optParam` definition — the imported
/// surface a real `.olean` provides before any default-argument-using member.
fn base_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    register_opt_param(&mut env);
    env
}

/// Imported `addDefault (x : optParam Nat 2) : Nat := x` — a single explicit
/// optional parameter, default `2`.
fn env_with_add_default() -> Environment {
    let mut env = base_env();
    let ty = Expr::pi(BinderInfo::Default, opt_param_nat(nat(2)), const_("Nat"));
    let value = Expr::lam(BinderInfo::Default, const_("Nat"), Expr::bvar(0));
    // SOUNDNESS: test-only synthesis of an imported member whose parameter type
    // is the raw `optParam Nat 2` application, exactly as a real `.olean`
    // encodes `(x : Nat := 2)`. Kernel type-checked by `add_decl_structural`.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("addDefault"),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: false,
    })
    .expect("addDefault should kernel-check and declare");
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

/// Try-version: returns the elaboration/registration error instead of panicking.
fn try_elaborate_decls_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse: {e}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| format!("{e}"))?;
    }
    Ok(())
}

// ===========================================================================
// Preconditions: this is genuinely the imported configuration — `optParam` is a
// reducible definition the kernel can unfold, the parameter type is the raw
// `optParam Nat 2` application, and there is NO clean-side default metadata.
// ===========================================================================

#[test]
fn test_imported_optparam_decl_has_raw_optparam_param_type_and_no_metadata() {
    let env = env_with_add_default();

    // optParam imported as a reducible definition (the prelude shape).
    let op = env
        .get_const(&Name::from_string("optParam"))
        .expect("optParam should be imported as a definition");
    assert!(
        op.value.is_some(),
        "optParam must be a definitional constant the kernel can unfold"
    );

    // addDefault's parameter type is literally `optParam.{1} Nat 2` (not a
    // pre-reduced `Nat`, and not desugared into clean-side default metadata).
    let add = env
        .get_const(&Name::from_string("addDefault"))
        .expect("addDefault should be imported");
    let ExprKind::Pi(bi, param_ty, _) = add.type_.kind() else {
        panic!("addDefault must be a Pi type, got {:?}", add.type_.kind());
    };
    assert_eq!(
        bi.info,
        BinderInfo::Default,
        "the optional parameter is an *explicit* binder"
    );
    let head = param_ty.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.last_component().as_deref() == Some("optParam")),
        "addDefault's parameter type must be a raw `optParam …` application, got {:?}",
        param_ty.kind()
    );
    let args: Vec<_> = param_ty.get_app_args().into_iter().collect();
    assert_eq!(
        args.len(),
        2,
        "the `optParam` application carries exactly (carrier, default)"
    );

    // The kernel CAN unfold `optParam.{1} Nat 2` to `Nat` — so the inserted
    // default (typed `Nat`) is accepted at the `optParam Nat 2` parameter.
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&opt_param_nat(nat(2)), &const_("Nat")),
        "optParam.{{1}} Nat 2 must be def-eq to Nat (reducible unfolding)"
    );
}

// ===========================================================================
// Control: the kernel accepts the function applied to its argument explicitly.
// Isolates any failure below to the elaborator's *default insertion* rather
// than to the synthesized fixture or the kernel's `optParam` reduction.
// ===========================================================================

#[test]
fn test_imported_optparam_applied_explicitly_kernel_reduces() {
    let env = env_with_add_default();
    let tc = TypeChecker::new(&env);

    // addDefault 7 reduces to 7 (the function is identity on its argument).
    let app = Expr::app(const_("addDefault"), nat(7));
    assert!(tc.is_def_eq(&app, &nat(7)), "addDefault 7 must reduce to 7");
    // And kernel-infers a `Nat` type.
    let inferred = tc.infer_type(&app).expect("addDefault 7 type-checks");
    assert!(
        tc.is_def_eq(&inferred, &const_("Nat")),
        "addDefault 7 : Nat"
    );
}

// ===========================================================================
// MAIN PROBE (the fixed bug): USE the imported declaration WITHOUT supplying
// the optional argument. The elaborator must insert the packaged default (2)
// so the body kernel-checks at the declared result type and reduces to 2 —
// distinct from a missing/zero default.
// ===========================================================================

#[test]
fn test_imported_optparam_default_inserted_when_omitted() {
    let mut env = env_with_add_default();

    // `useDefault : Nat := addDefault` — the optional `x` is omitted, so the
    // elaborator must supply the packaged default `2`. Before the fix this
    // failed to kernel-check (`expected Nat, got optParam Nat 2 → Nat`).
    elaborate_decls_into(&mut env, "def useDefault : Nat := addDefault");

    let info = env
        .get_const(&Name::from_string("useDefault"))
        .expect("useDefault should be registered");
    let value = info.value.as_ref().expect("useDefault is a definition");

    // The value must reduce to the DEFAULT (2), not 0 (a dropped/zeroed default)
    // and not stay stuck as a partial application.
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(value, &nat(2)),
        "omitted optParam must insert the default 2; got head {:?}",
        whnf_head_const(&env, value)
    );
    assert!(
        !tc.is_def_eq(value, &nat(0)),
        "the default must be the packaged value 2, not 0 — a wrong/zeroed default would surface here"
    );
    // And the declared type is reached (the def kernel-checked at `Nat`).
    let ty = info.type_.clone();
    assert!(tc.is_def_eq(&ty, &const_("Nat")), "useDefault : Nat");
}

// ===========================================================================
// Probe: a TRAILING optParam after a supplied explicit argument. The user
// provides the leading `Nat` positionally; the trailing optParam must be
// defaulted at the end of the application loop (distinct default 3).
// ===========================================================================

#[test]
fn test_imported_trailing_optparam_defaulted_after_explicit_arg() {
    let mut env = base_env();

    // addTrailing (x : Nat) (y : optParam Nat 3) : Nat := y   (returns the
    // optional field, so the result is observably the default when omitted).
    let ty = Expr::pi(
        BinderInfo::Default,
        const_("Nat"),
        Expr::pi(BinderInfo::Default, opt_param_nat(nat(3)), const_("Nat")),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        const_("Nat"),
        Expr::lam(BinderInfo::Default, const_("Nat"), Expr::bvar(0)),
    );
    // SOUNDNESS: test-only synthesis of an imported member with a leading
    // explicit `Nat` parameter and a trailing raw `optParam Nat 3` parameter,
    // as a real `.olean` encodes `(x : Nat) (y : Nat := 3)`. Kernel-checked.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("addTrailing"),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: false,
    })
    .expect("addTrailing should kernel-check and declare");

    // Supply only the leading explicit `x`; `y` must default to 3.
    elaborate_decls_into(&mut env, "def useTrailing : Nat := addTrailing Nat.zero");

    let value = env
        .get_const(&Name::from_string("useTrailing"))
        .and_then(|i| i.value.clone())
        .expect("useTrailing should be registered with a value");
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&value, &nat(3)),
        "trailing optParam must default to 3; got head {:?}",
        whnf_head_const(&env, &value)
    );
    assert!(
        !tc.is_def_eq(&value, &nat(0)),
        "the trailing default must be 3, not 0"
    );
}

// ===========================================================================
// Probe: a STRUCTURE FIELD default. Lean encodes a field default
// `(width : Nat := 5)` as the *constructor* carrying a parameter of type
// `optParam Nat 5`. Building the structure value without the field must insert
// the default and reduce the projection to 5.
// ===========================================================================

#[test]
fn test_imported_structure_field_default_inserted() {
    let mut env = base_env();

    // structure Cfg where mk :: (width : optParam Nat 5)
    //   => Cfg : Type, Cfg.mk : (width : optParam Nat 5) → Cfg
    let mk_ty = Expr::pi(BinderInfo::Default, opt_param_nat(nat(5)), const_("Cfg"));
    let ind = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Cfg"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Cfg.mk"),
                type_: mk_ty,
            }],
        }],
    };
    env.add_inductive(ind).expect("Cfg should declare");

    // `useCfg : Cfg := Cfg.mk` — omit the field, so `width` defaults to 5.
    elaborate_decls_into(&mut env, "def useCfg : Cfg := Cfg.mk");

    let value = env
        .get_const(&Name::from_string("useCfg"))
        .and_then(|i| i.value.clone())
        .expect("useCfg should be registered with a value");

    // Project the single field (`width`) and confirm it reduced to 5.
    let width = Expr::proj(Name::from_string("Cfg"), 0, value);
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&width, &nat(5)),
        "omitted structure-field default must insert 5; got head {:?}",
        whnf_head_const(&env, &width)
    );
    assert!(
        !tc.is_def_eq(&width, &nat(0)),
        "the field default must be 5, not 0"
    );
}

// ===========================================================================
// Diagnostic: surface (don't panic) that the bare-reference + applied uses both
// reach the kernel for the imported optParam declaration. Pins the failure mode
// so a regression on default insertion is caught with a clear message.
// ===========================================================================

#[test]
fn test_imported_optparam_use_elaborates_at_all() {
    let mut env = env_with_add_default();
    let result = try_elaborate_decls_into(
        &mut env,
        "def probeBare : Nat := addDefault\n\
         def probeApplied : Nat := addDefault Nat.zero",
    );
    assert!(
        result.is_ok(),
        "using an imported optParam decl (omitted AND supplied) should elaborate + kernel-check, got: {result:?}"
    );
}

// ===========================================================================
// FLIP-ON-FIX pin: `autoParam` (tactic-synthesised defaults). A real `.olean`
// encodes `(x : α := by tac)` as a parameter of type `autoParam α tac`, where
// the second slot is the tactic syntax to run. Inserting it requires the
// elaborator to *run* that tactic at application sites — which clean-elab does
// not yet do — so an omitted `autoParam` parameter is NOT filled and the use
// fails to kernel-check (an arity mismatch). This is ORTHOGONAL to `optParam`
// (a packaged value), which the other tests prove fixed. Pinned (NOT
// `#[ignore]`d) so the assertion flips to a failure the moment autoParam
// insertion lands, prompting an update to positive reduction assertions.
// ===========================================================================

#[test]
fn test_imported_autoparam_default_is_pending() {
    let mut env = base_env();

    // Synthesize a stand-in `autoParam.{u} (α : Sort u) (tac : Nat) : Sort u := α`.
    // The real prelude's second argument is `Lean.Syntax`; we use `Nat` here only
    // to avoid depending on the `Syntax` type — the elaborator distinguishes
    // `autoParam` from `optParam` by the head constant name, so the carrier of
    // the tactic slot is irrelevant to whether default insertion fires.
    let u = Name::from_string("u");
    let sort_u = Expr::sort(Level::param(u.clone()));
    let ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(BinderInfo::Default, const_("Nat"), sort_u.clone()),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::lam(BinderInfo::Default, const_("Nat"), Expr::bvar(1)),
    );
    // SOUNDNESS: test-only synthesis of the prelude-shaped `autoParam` constant
    // and a member whose parameter type is `autoParam Nat 0`. Kernel-checked.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("autoParam"),
        level_params: vec![u],
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("autoParam should kernel-check and declare");

    // withAuto (x : autoParam Nat 0) : Nat := x
    let op = Expr::const_(
        Name::from_string("autoParam"),
        vec![Level::succ(Level::zero())],
    );
    let auto_nat = Expr::app(Expr::app(op, const_("Nat")), const_("Nat.zero"));
    let with_ty = Expr::pi(BinderInfo::Default, auto_nat, const_("Nat"));
    let with_val = Expr::lam(BinderInfo::Default, const_("Nat"), Expr::bvar(0));
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("withAuto"),
        level_params: vec![],
        type_: with_ty,
        value: with_val,
        is_reducible: false,
    })
    .expect("withAuto should kernel-check and declare");

    // Omit the autoParam argument. Inserting it would require running the tactic
    // in the `autoParam` slot, which the elaborator does not yet do, so this must
    // currently FAIL to kernel-check.
    let result = try_elaborate_decls_into(&mut env, "def useAuto : Nat := withAuto");
    assert!(
        result.is_err(),
        "FLIP-ON-FIX: an omitted autoParam now elaborates — clean-elab gained \
         tactic-default synthesis at application sites. Replace this pin with a \
         positive assertion that `useAuto` reduces to the tactic-synthesised \
         value. Got: {result:?}"
    );
}

// ===========================================================================
// NATIVE control: a NATIVELY-elaborated decl with a plain explicit `Nat`
// parameter (no optParam) is byte-for-byte unaffected — supplying the argument
// works and an omitted required argument still errors. Confirms the optParam
// default-insertion path does not perturb ordinary explicit-argument handling.
// ===========================================================================

#[test]
fn test_native_plain_explicit_param_unaffected() {
    let mut env = base_env();

    // Native def with a REQUIRED explicit parameter (no optParam).
    elaborate_decls_into(&mut env, "def idNat (x : Nat) : Nat := x");

    // Supplying the argument works and reduces correctly.
    let mut env2 = env.clone();
    elaborate_decls_into(&mut env2, "def useId : Nat := idNat Nat.zero");
    let value = env2
        .get_const(&Name::from_string("useId"))
        .and_then(|i| i.value.clone())
        .expect("useId should register");
    let tc = TypeChecker::new(&env2);
    assert!(
        tc.is_def_eq(&value, &nat(0)),
        "idNat Nat.zero must reduce to 0 (plain explicit arg unaffected)"
    );

    // Omitting the REQUIRED argument must still fail — optParam insertion must
    // NOT fabricate a default for a non-optParam parameter.
    let mut env3 = env;
    let omitted = try_elaborate_decls_into(&mut env3, "def useIdBad : Nat := idNat");
    assert!(
        omitted.is_err(),
        "a required explicit parameter must NOT be auto-defaulted; got: {omitted:?}"
    );
}
