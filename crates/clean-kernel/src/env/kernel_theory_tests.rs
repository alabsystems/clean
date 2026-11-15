// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins for the kernel theory profiles (`kernel_theory.rs`).
//!
//! The kernel-level shape is exactly the one Lean's `Init/System/Platform.lean`
//! declares: `@[extern] opaque getIsWindows : Unit → Bool` and
//! `def isWindows : Bool := getIsWindows ()`. Ground truth (pinned Lean
//! v4.30.0-rc2, `leanchecker` on a `debug.skipKernelTC` forgery of
//! `isWindows = false := Eq.refl false`, 2026-09-24): `(kernel) declaration
//! type mismatch, ... has type Eq Bool.false Bool.false but it is expected to
//! have type Eq System.Platform.isWindows Bool.false`. `isWindows` is used rather
//! than `isOSX` because Clean's reducer answers `false` for it on every host.

use super::*;
use crate::env::{Declaration, EnvError};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::tc::{LocalContext, TcCaches, TypeChecker, TypeError};
use std::sync::Arc;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn bool_ty() -> Expr {
    Expr::const_(name("Bool"), vec![])
}

fn bool_false() -> Expr {
    Expr::const_(name("Bool.false"), vec![])
}

/// The prelude plus Lean's two platform declarations, spelled as Lean's
/// kernel holds them: an OPAQUE extern and a definition over it.
fn platform_env() -> Environment {
    let mut env = Environment::with_prelude();
    let unit = Expr::const_(name("Unit"), vec![]);
    env.add_decl(Declaration::Opaque {
        name: name("System.Platform.getIsWindows"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, unit.clone(), bool_ty()),
        value: Expr::lam(BinderInfo::Default, unit, bool_false()),
    })
    .expect("opaque getIsWindows is well-typed");
    env.add_decl(Declaration::Definition {
        name: name("System.Platform.isWindows"),
        level_params: vec![],
        type_: bool_ty(),
        value: Expr::app(
            Expr::const_(name("System.Platform.getIsWindows"), vec![]),
            Expr::const_(name("Unit.unit"), vec![]),
        ),
        is_reducible: false,
    })
    .expect("def isWindows is well-typed");
    env
}

/// `forged : @Eq Bool System.Platform.isWindows false := @Eq.refl Bool false`.
fn forged_not_windows() -> Declaration {
    let eq = |a: Expr, b: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(name("Eq"), vec![Level::succ(Level::zero())]),
                    bool_ty(),
                ),
                a,
            ),
            b,
        )
    };
    Declaration::Theorem {
        name: name("forged_not_windows"),
        level_params: vec![],
        type_: eq(
            Expr::const_(name("System.Platform.isWindows"), vec![]),
            bool_false(),
        ),
        value: Expr::app(
            Expr::app(
                Expr::const_(name("Eq.refl"), vec![Level::succ(Level::zero())]),
                bool_ty(),
            ),
            bool_false(),
        ),
    }
}

#[test]
fn test_kernel_theory_default_is_extended() {
    let env = Environment::new();
    assert_eq!(env.kernel_theory(), KernelTheory::Extended);
    let tc = TypeChecker::new(&env);
    assert_eq!(tc.kernel_theory(), KernelTheory::Extended);
}

/// RE-DECIDED 2026-09-26: this pinned the defect — the extended theory's
/// host-answering reducer decided a statement Lean's kernel cannot. Native-fold
/// authority (`native_fold_authority.rs`) closes it in EVERY theory: an
/// `opaque` extern has no definition a reducer could be justified by.
#[test]
fn test_extended_theory_rejects_forged_platform_boolean() {
    let env = platform_env();
    let err = env
        .check_decl_readonly(&forged_not_windows())
        .expect_err("no theory reduces the @[extern] opaque natively any more");
    assert!(
        matches!(err, EnvError::TypeCheckFailed { .. }),
        "the refusal is the kernel's own type mismatch, got {err:?}"
    );
}

/// The fix: under Lean's theory the opaque extern is stuck, exactly as in
/// Lean's kernel, so the forgery is a type mismatch.
#[test]
fn test_lean_theory_rejects_forged_platform_boolean() {
    let mut env = platform_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let err = env
        .check_decl_readonly(&forged_not_windows())
        .expect_err("Lean's kernel rejects `isWindows = false := rfl`");
    assert!(
        matches!(err, EnvError::TypeCheckFailed { .. }),
        "the refusal is the kernel's own type mismatch, got {err:?}"
    );
}

/// A reflexive statement about the stuck term still checks: the profile makes
/// the extern opaque, it does not make it ill-formed.
#[test]
fn test_lean_theory_accepts_reflexivity_on_stuck_platform_boolean() {
    let mut env = platform_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let is_windows = Expr::const_(name("System.Platform.isWindows"), vec![]);
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(name("Eq"), vec![Level::succ(Level::zero())]),
                bool_ty(),
            ),
            is_windows.clone(),
        ),
        is_windows.clone(),
    );
    let refl = Expr::app(
        Expr::app(
            Expr::const_(name("Eq.refl"), vec![Level::succ(Level::zero())]),
            bool_ty(),
        ),
        is_windows,
    );
    env.check_decl_readonly(&Declaration::Theorem {
        name: name("honest_windows_refl"),
        level_params: vec![],
        type_: eq_ty,
        value: refl,
    })
    .expect("`isWindows = isWindows := rfl` holds in Lean's theory");
}

/// A checker-level override wins over the environment's theory, in both
/// directions, so a lane can run Lean's theory against a borrowed env.
#[test]
fn test_type_checker_override_takes_precedence_over_environment_theory() {
    let env = platform_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(KernelTheory::Lean);
    assert_eq!(tc.kernel_theory(), KernelTheory::Lean);
    let is_windows = Expr::const_(name("System.Platform.isWindows"), vec![]);
    let reduced = tc.whnf(&is_windows);
    assert_ne!(
        reduced,
        bool_false(),
        "Lean-theory checker must leave `isWindows` stuck, got {reduced:?}"
    );

    // The override must still be DISCRIMINATING. The platform extern no longer
    // separates the theories (authority refuses it in both, 2026-09-26), so
    // use a canonical prelude head the Lean profile excludes and the extended
    // theory admits: `UInt8.decLt` (not in the differential list; a `fold`
    // row of `clean-prelude`). RE-DECIDED 2026-09-28: this used `UInt8.add`,
    // whose payload reducer the native-fold review never saw fire on a typed
    // input, so its row is no longer `fold` and neither theory admits it.
    let uint8_add = name("UInt8.decLt");
    assert!(
        tc.native_reducer_for(&uint8_add).is_none(),
        "Lean theory excludes UInt8.decLt"
    );
    let extended = TypeChecker::new(&env);
    assert_ne!(
        extended.whnf(&is_windows),
        bool_false(),
        "the extern is stuck in both theories"
    );
    assert!(
        extended.native_reducer_for(&uint8_add).is_some(),
        "the extended checker admits the canonical UInt8.decLt reducer"
    );
}

/// The THEORY-DISCRIMINATING environment for the cache-custody tests: the
/// `Coin` enumeration with its `casesOn` mirror FORGED (rules swapped), plus
/// `Eq`, `Bool` and `Nat`. The extended theory reduces `cases_on_heads()`
/// through the mirror to `Coin.heads`; Lean's theory declines the value-bearing
/// head and δ gives `Coin.tails` (`test_lean_theory_ignores_forged_cases_on_mirror`).
///
/// These tests used the platform boolean (`isWindows = false`) as the equation
/// only the extended theory accepted. Native-fold authority
/// (`native_fold_authority.rs`, 2026-09-26) refuses the reducer of an opaque
/// extern in EVERY theory, so that equation no longer separates them; the
/// forged mirror still does, which is what cache custody needs.
fn custody_env() -> Environment {
    let mut env = coin_env();
    env.init_eq().expect("Eq");
    env.init_bool().expect("Bool");
    env.init_nat().expect("Nat");
    let mirror = env
        .recursors
        .get_mut(&name("Coin.casesOn"))
        .expect("Clean mirrors casesOn into the recursor table");
    let first = mirror.rules[0].rhs.clone();
    mirror.rules[0].rhs = mirror.rules[1].rhs.clone();
    mirror.rules[1].rhs = first;
    env
}

/// The term the two theories reduce differently in [`custody_env`].
fn discriminated() -> Expr {
    cases_on_heads()
}

/// What the extended theory reduces [`discriminated`] to.
fn extended_answer() -> Expr {
    Expr::const_(name("Coin.heads"), vec![])
}

/// `forged_custody : @Eq Coin (casesOn … heads) Coin.heads := rfl` — accepted
/// by the extended theory through the forged mirror, refused by Lean's.
fn forged_custody() -> Declaration {
    let coin = Expr::const_(name("Coin"), vec![]);
    let one = Level::succ(Level::zero());
    Declaration::Theorem {
        name: name("forged_custody"),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(name("Eq"), vec![one.clone()]),
            [coin.clone(), discriminated(), extended_answer()],
        ),
        value: Expr::apps(
            Expr::const_(name("Eq.refl"), vec![one]),
            [coin, extended_answer()],
        ),
    }
}

/// A checker-local override is not the environment's policy. Transferring its
/// caches must not grant that override to a new checker which uses the same
/// immutable environment and exact local context, but the default Lean theory.
#[test]
fn test_cache_theory_custody_rejects_transferred_extended_proof() {
    let mut env = custody_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let ctx = Arc::new(LocalContext::new());
    let Declaration::Theorem { type_, value, .. } = forged_custody() else {
        panic!("fixture must provide the actual forged theorem");
    };

    let fresh = TypeChecker::with_context_and_caches(&env, ctx.clone(), TcCaches::default());
    let cold_error = fresh
        .check_type(&value, &type_)
        .expect_err("the cold Lean control must reject this exact proof and statement");
    assert!(
        matches!(cold_error, TypeError::TypeMismatch { .. }),
        "{cold_error:?}"
    );

    let mut warm = TypeChecker::with_context_and_caches(&env, ctx.clone(), TcCaches::default());
    // Obey the setter's contract: select the override before any reduction.
    warm.set_kernel_theory(KernelTheory::Extended);
    warm.check_type(&value, &type_)
        .expect("the Extended control accepts this exact platform equation");
    assert!(warm.def_eq_cache_entries() > 0);

    let transferred = TypeChecker::with_context_and_caches(&env, ctx, warm.take_caches());
    assert_eq!(transferred.kernel_theory(), KernelTheory::Lean);
    let error = transferred
        .check_type(&value, &type_)
        .expect_err("an Extended cached acceptance must not certify this proof in Lean theory");
    assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error:?}");
}

/// Exercise both reductions and equality directly, independently of inference
/// memoization or theorem registration. No environment/context mutation occurs.
#[test]
fn test_cache_theory_custody_rejects_transferred_extended_reduction() {
    let mut env = custody_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let ctx = Arc::new(LocalContext::new());
    let is_windows = discriminated();

    let fresh = TypeChecker::with_context_and_caches(&env, ctx.clone(), TcCaches::default());
    assert_ne!(fresh.whnf(&is_windows), extended_answer());
    assert!(!fresh.is_def_eq(&is_windows, &extended_answer()));

    let mut warm = TypeChecker::with_context_and_caches(&env, ctx.clone(), TcCaches::default());
    warm.set_kernel_theory(KernelTheory::Extended);
    assert_eq!(warm.whnf(&is_windows), extended_answer());
    assert!(warm.is_def_eq(&is_windows, &extended_answer()));
    assert!(warm.whnf_cache_entries() > 0);
    assert!(warm.def_eq_cache_entries() > 0);

    let transferred = TypeChecker::with_context_and_caches(&env, ctx, warm.take_caches());
    assert_eq!(transferred.kernel_theory(), KernelTheory::Lean);
    assert_ne!(
        transferred.whnf(&is_windows),
        extended_answer(),
        "the Lean checker must not reuse an Extended native reduction"
    );
    assert!(!transferred.is_def_eq(&is_windows, &extended_answer()));
}

/// A custody check must preserve actual cache hits when the policy agrees;
/// dropping every transfer is not the intended repair.
#[test]
fn test_cache_theory_custody_preserves_same_policy_warm_reduction() {
    for theory in [
        KernelTheory::Extended,
        KernelTheory::Lean,
        KernelTheory::LeanReference,
    ] {
        let mut env = platform_env();
        env.set_kernel_theory(theory);
        let ctx = Arc::new(LocalContext::new());
        let is_windows = Expr::const_(name("System.Platform.isWindows"), vec![]);
        let warm = TypeChecker::with_context_and_caches(&env, ctx.clone(), TcCaches::default());
        let reduced = warm.whnf(&is_windows);
        let entries = warm.whnf_cache_entries();
        assert!(entries > 0, "the control must populate a real cache");

        let transferred = TypeChecker::with_context_and_caches(&env, ctx, warm.take_caches());
        assert_eq!(transferred.kernel_theory(), theory);
        assert_eq!(transferred.whnf_cache_entries(), entries);
        let remaining = transferred.heartbeat_remaining();
        assert_eq!(transferred.whnf(&is_windows), reduced);
        assert_eq!(
            transferred.heartbeat_remaining(),
            remaining,
            "a same-policy warm WHNF hit must not redo reduction work"
        );
    }
}

#[test]
fn test_cache_theory_custody_preserves_same_override_warm_reduction() {
    let mut env = custody_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let ctx = Arc::new(LocalContext::new());
    let is_windows = discriminated();
    let mut warm = TypeChecker::with_context_and_caches(&env, ctx.clone(), TcCaches::default());
    warm.set_kernel_theory(KernelTheory::Extended);
    assert_eq!(warm.whnf(&is_windows), extended_answer());
    let entries = warm.whnf_cache_entries();
    assert!(entries > 0);

    let mut transferred = TypeChecker::with_context_and_caches(&env, ctx, warm.take_caches());
    assert_eq!(transferred.kernel_theory(), KernelTheory::Lean);
    // Restore the original override before any reduction. Constructor defaults
    // must not discard valid caches before the caller can finish this setup.
    transferred.set_kernel_theory(KernelTheory::Extended);
    assert_eq!(transferred.whnf_cache_entries(), entries);
    let remaining = transferred.heartbeat_remaining();
    assert_eq!(transferred.whnf(&is_windows), extended_answer());
    assert_eq!(transferred.heartbeat_remaining(), remaining);
}

#[test]
fn test_cache_theory_custody_rejects_untouched_reexport() {
    let mut env = custody_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let ctx = Arc::new(LocalContext::new());
    let Declaration::Theorem { type_, value, .. } = forged_custody() else {
        panic!("fixture must provide the actual forged theorem");
    };
    let mut warm = TypeChecker::with_context_and_caches(&env, ctx.clone(), TcCaches::default());
    warm.set_kernel_theory(KernelTheory::Extended);
    warm.check_type(&value, &type_)
        .expect("the source cache actually accepted the Extended equation");

    let intermediate = TypeChecker::with_context_and_caches(&env, ctx.clone(), warm.take_caches());
    assert_eq!(intermediate.kernel_theory(), KernelTheory::Lean);
    // No semantic operation in the intermediate checker: exporting alone must
    // not relabel Extended answers as Lean answers for the next consumer.
    let final_checker = TypeChecker::with_context_and_caches(&env, ctx, intermediate.take_caches());
    let error = final_checker
        .check_type(&value, &type_)
        .expect_err("an untouched transfer must not launder the cached acceptance");
    assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error:?}");
}

#[test]
fn test_cache_theory_custody_rejects_warm_checker_profile_change() {
    let env = custody_env();
    let Declaration::Theorem { type_, value, .. } = forged_custody() else {
        panic!("fixture must provide the actual forged theorem");
    };
    let mut checker = TypeChecker::new(&env);
    checker.enable_type_cache_pub();
    checker
        .check_type(&value, &type_)
        .expect("the warm checker must have accepted this exact equation");
    checker.set_kernel_theory(KernelTheory::Lean);
    let error = checker
        .check_type(&value, &type_)
        .expect_err("changing theory must invalidate this checker's cached acceptance too");
    assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error:?}");
}

fn extended_custody_caches(env: &Environment, ctx: Arc<LocalContext>) -> TcCaches {
    let is_windows = discriminated();
    let mut warm = TypeChecker::with_context_and_caches(env, ctx, TcCaches::default());
    warm.set_kernel_theory(KernelTheory::Extended);
    assert_eq!(warm.whnf(&is_windows), extended_answer());
    assert!(warm.is_def_eq(&is_windows, &extended_answer()));
    assert!(warm.whnf_cache_entries() > 0);
    assert!(warm.def_eq_cache_entries() > 0);
    warm.take_caches()
}

/// Certificate inference has its own public entry point. A Sort deliberately
/// needs no nested reduction: this pins that entry's barrier, not infer-only
/// validation of an application argument. Full proof rejection is checked next.
#[test]
fn test_cache_theory_custody_standalone_certificate_entry() {
    let mut env = custody_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let ctx = Arc::new(LocalContext::new());
    let caches = extended_custody_caches(&env, ctx.clone());
    let checker = TypeChecker::with_context_and_caches(&env, ctx, caches);
    let (ty, _) = checker
        .infer_type_with_cert(&Expr::prop())
        .expect("standalone certificate inference of Prop must still succeed");
    assert_eq!(ty, Expr::type_());
    assert_eq!(checker.whnf_cache_entries(), 0);
    assert_eq!(checker.def_eq_cache_entries(), 0);
    let Declaration::Theorem { type_, value, .. } = forged_custody() else {
        panic!("fixture must provide the actual forged theorem");
    };
    let error = checker
        .check_type(&value, &type_)
        .expect_err("certificate-entry cache custody must not retain the forged equality");
    assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error:?}");
}

#[test]
fn test_cache_theory_custody_proof_reduction_entry() {
    let mut env = custody_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let ctx = Arc::new(LocalContext::new());
    let is_windows = discriminated();
    // `Coin.rec (fun _ => Bool) false true <discriminated>`: Extended theory
    // reduces the major to `Coin.heads` (→ `false`), Lean theory to
    // `Coin.tails` (→ `true`).
    let mut case = Expr::const_(name("Coin.rec"), vec![Level::succ(Level::zero())]);
    for argument in [
        Expr::lam(
            BinderInfo::Default,
            Expr::const_(name("Coin"), vec![]),
            bool_ty(),
        ),
        bool_false(),
        Expr::const_(name("Bool.true"), vec![]),
        is_windows,
    ] {
        case = Expr::app(case, argument);
    }
    let fresh = TypeChecker::with_context_and_caches(&env, ctx.clone(), TcCaches::default());
    fresh
        .check_type(&case, &bool_ty())
        .expect("the Bool recursor must be well-typed even with a stuck major premise");
    let cold = fresh.whnf_with_proof(&case, &bool_ty(), Level::succ(Level::zero()));
    assert_ne!(cold.result, bool_false());

    let caches = extended_custody_caches(&env, ctx.clone());
    let checker = TypeChecker::with_context_and_caches(&env, ctx, caches);
    // First semantic call is the proof-producing API, which uses private WHNF
    // internally. Its recursor major must not see the old native Bool result.
    let transferred = checker.whnf_with_proof(&case, &bool_ty(), Level::succ(Level::zero()));
    assert_eq!(transferred.result, cold.result);
    assert_ne!(transferred.result, bool_false());
}

/// The native-reducer facade must reconcile custody even if its first input has
/// no reducer. The next supported reduction remains available under Lean theory.
#[test]
fn test_cache_theory_custody_native_reduction_entry() {
    let mut env = custody_env();
    env.set_kernel_theory(KernelTheory::Lean);
    let ctx = Arc::new(LocalContext::new());
    let caches = extended_custody_caches(&env, ctx.clone());
    let checker = TypeChecker::with_context_and_caches(&env, ctx, caches);
    assert!(checker.try_reduce_native(&Expr::prop()).is_none());
    assert_eq!(checker.whnf_cache_entries(), 0);
    assert_eq!(checker.def_eq_cache_entries(), 0);
    let add = Expr::app(
        Expr::app(Expr::const_(name("Nat.add"), vec![]), Expr::nat_lit(1)),
        Expr::nat_lit(2),
    );
    assert_eq!(checker.try_reduce_native(&add), Some(Expr::nat_lit(3)));
    let Declaration::Theorem { type_, value, .. } = forged_custody() else {
        panic!("fixture must provide the actual forged theorem");
    };
    let error = checker
        .check_type(&value, &type_)
        .expect_err("native-entry cache custody must not retain the forged equality");
    assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error:?}");
}

/// Every reducer the platform, `Float` and float→rational families register
/// is excluded, whatever the environment holds for its head constant.
#[test]
fn test_lean_theory_excludes_every_opaque_extern_family_reducer() {
    let mut families = Environment::default();
    families.init_platform_native_reducers();
    families.init_float_native_reducers();
    families.init_float_to_rat_native_reducers();
    let names: Vec<Name> = families
        .registered_native_reducer_names()
        .cloned()
        .collect();
    assert!(
        names.len() >= 30,
        "the three families register their reducers (got {})",
        names.len()
    );
    let env = Environment::new();
    for n in &names {
        assert_eq!(
            env.lean_theory_exclusion(n),
            Some(LeanTheoryExclusion::OpaqueExternFamily),
            "`{n}` must be excluded from Lean's theory"
        );
        assert!(env.native_reducer_in(n, KernelTheory::Lean).is_none());
        // `Environment::new()` declares none of these heads, and native-fold
        // authority refuses a head the environment does not hold canonically
        // in EVERY theory (2026-09-26; it used to fire by name here).
        assert!(env.native_reducer_in(n, KernelTheory::Extended).is_none());
    }
}

fn reduce_to_false(_args: &[&Expr]) -> Option<Expr> {
    Some(Expr::const_(Name::from_string("Bool.false"), vec![]))
}

/// Outside the named families the rule is structural: a reducer may only
/// accelerate a head constant that is a value-carrying `Definition` here.
#[test]
fn test_lean_theory_admits_reducer_only_for_definition_with_body() {
    let mut env = Environment::with_prelude();
    let unit_to_bool = Expr::pi(
        BinderInfo::Default,
        Expr::const_(name("Unit"), vec![]),
        bool_ty(),
    );
    env.add_decl(Declaration::Axiom {
        name: name("Probe.axiomHead"),
        level_params: vec![],
        type_: unit_to_bool.clone(),
    })
    .expect("axiom head");
    env.add_decl(Declaration::Definition {
        name: name("Probe.defHead"),
        level_params: vec![],
        type_: unit_to_bool.clone(),
        value: Expr::lam(
            BinderInfo::Default,
            Expr::const_(name("Unit"), vec![]),
            bool_false(),
        ),
        is_reducible: false,
    })
    .expect("definition head");
    for n in ["Probe.axiomHead", "Probe.defHead", "Probe.absentHead"] {
        env.register_native_reducer(name(n), reduce_to_false);
    }
    assert_eq!(
        env.lean_theory_structural_exclusion(&name("Probe.axiomHead")),
        Some(LeanTheoryExclusion::NoDefinitionBody)
    );
    assert_eq!(
        env.lean_theory_structural_exclusion(&name("Probe.absentHead")),
        Some(LeanTheoryExclusion::NoDefinitionBody)
    );
    assert_eq!(
        env.lean_theory_structural_exclusion(&name("Probe.defHead")),
        None
    );
    // Structurally computable is not enough: no battery covers the probe, so
    // rule 0 keeps it off (the next test pins that on its own).
    assert!(env
        .native_reducer_in(&name("Probe.defHead"), KernelTheory::Lean)
        .is_none());
}

/// Rule 0: a reducer whose head Lean's kernel could compute is still refused
/// unless the differential battery covers it. `String.drop` is the measured
/// case (a `String.Slice` in Lean 4.30, a `String` literal from Clean's
/// reducer), and neither it nor its siblings may ever be on the list.
#[test]
fn test_lean_theory_refuses_structurally_computable_reducer_without_differential() {
    let mut env = Environment::with_prelude();
    let unit = Expr::const_(name("Unit"), vec![]);
    env.add_decl(Declaration::Definition {
        name: name("Probe.computableHead"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, unit.clone(), bool_ty()),
        value: Expr::lam(BinderInfo::Default, unit, bool_false()),
        is_reducible: false,
    })
    .expect("definition head");
    env.register_native_reducer(name("Probe.computableHead"), reduce_to_false);
    let probe = name("Probe.computableHead");
    assert_eq!(env.lean_theory_structural_exclusion(&probe), None);
    assert_eq!(
        env.lean_theory_exclusion(&probe),
        Some(LeanTheoryExclusion::NotDifferentiallyChecked)
    );
    for head in [
        "String.drop",
        "String.take",
        "String.trimLeft",
        "String.trimRight",
        "String.toLower",
        "String.toUpper",
    ] {
        assert!(
            !LEAN_PROFILE_DIFFERENTIAL_REDUCERS.contains(&head),
            "`{head}` computes a different value or type than Lean's definition"
        );
        let n = name(head);
        if env.get_native_reducer(&n).is_some() {
            assert!(env.native_reducer_in(&n, KernelTheory::Lean).is_none());
        }
    }
}

/// The reference theory is Lean's kernel exactly: every `reduce_nat` head it
/// registers, and nothing else, whatever the environment or the allowlist says.
#[test]
fn test_lean_reference_theory_keeps_only_kernel_nat_extensions() {
    let env = Environment::with_prelude();
    let mut kept = 0usize;
    for n in env.registered_native_reducer_names() {
        let fires = env
            .native_reducer_in(n, KernelTheory::LeanReference)
            .is_some();
        // A kernel Nat extension fires only over a canonical definition
        // (`Nat.gcd` is absent from the prelude, so it does not).
        let nat = LEAN_KERNEL_NAT_EXTENSIONS.contains(&n.to_string().as_str())
            && env.native_fold_authorized(n);
        assert_eq!(fires, nat, "`{n}` under the reference theory");
        kept += usize::from(fires);
    }
    assert!(
        kept >= 10,
        "the Nat extensions are registered (kept {kept})"
    );
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(KernelTheory::LeanReference);
    for n in env.registered_native_reducer_names() {
        assert_eq!(
            tc.native_reducer_for(n).is_some(),
            env.native_reducer_in(n, KernelTheory::LeanReference)
                .is_some(),
            "`{n}` (checker vs environment gate)"
        );
    }
}

/// Rule 3, the shape of `Lean.Name.hash` (a definition whose body calls the
/// opaque `mixHash`) and of `isOSX` itself: the head is a value-carrying
/// definition, so rule 2 admits it, and only the δ-closure walk sees that
/// Lean's kernel is stuck on an opaque one step down.
#[test]
fn test_lean_theory_refuses_definition_stuck_on_opaque() {
    let mut env = Environment::with_prelude();
    let unit = Expr::const_(name("Unit"), vec![]);
    let unit_to_bool = Expr::pi(BinderInfo::Default, unit.clone(), bool_ty());
    env.add_decl(Declaration::Opaque {
        name: name("Probe.externHash"),
        level_params: vec![],
        type_: unit_to_bool.clone(),
        value: Expr::lam(BinderInfo::Default, unit.clone(), bool_false()),
    })
    .expect("opaque extern");
    env.add_decl(Declaration::Definition {
        name: name("Probe.stuckHash"),
        level_params: vec![],
        type_: unit_to_bool,
        value: Expr::lam(
            BinderInfo::Default,
            unit,
            Expr::app(
                Expr::const_(name("Probe.externHash"), vec![]),
                Expr::bvar(0),
            ),
        ),
        is_reducible: false,
    })
    .expect("definition over the extern");
    env.register_native_reducer(name("Probe.stuckHash"), reduce_to_false);
    assert_eq!(
        env.lean_theory_structural_exclusion(&name("Probe.stuckHash")),
        Some(LeanTheoryExclusion::OpaqueInClosure {
            opaque: name("Probe.externHash")
        })
    );
    assert!(env
        .native_reducer_in(&name("Probe.stuckHash"), KernelTheory::Lean)
        .is_none());
    // A user-declared head is not canonical, so authority refuses it in the
    // extended theory too (2026-09-26); rule 3 above is the Lean profile's own
    // finding and is pinned by the structural exclusion.
    assert!(env
        .native_reducer_in(&name("Probe.stuckHash"), KernelTheory::Extended)
        .is_none());
}

/// Lean's kernel computes these `Nat` heads natively (`reduce_nat`), so the
/// Lean profile must keep every one Clean registers, whatever its prelude
/// spells for the definition.
#[test]
fn test_lean_theory_keeps_every_kernel_nat_extension() {
    let env = Environment::with_prelude();
    let mut kept = 0;
    for head in LEAN_KERNEL_NAT_EXTENSIONS {
        let n = name(head);
        if env.get_native_reducer(&n).is_some() {
            assert_eq!(env.lean_theory_exclusion(&n), None, "`{head}` must stay");
            kept += 1;
        }
    }
    assert!(
        kept >= 10,
        "Clean registers the Nat extensions (kept {kept})"
    );
}

/// The checker's memoized gate agrees with the uncached environment gate on
/// every registered reducer, in both theories, and its memo is consulted on the
/// second lookup.
#[test]
fn test_type_checker_reducer_gate_matches_environment_gate() {
    let env = platform_env();
    let names: Vec<Name> = env.registered_native_reducer_names().cloned().collect();
    let mut lean = TypeChecker::new(&env);
    lean.set_kernel_theory(KernelTheory::Lean);
    let extended = TypeChecker::new(&env);
    let (mut admitted, mut refused) = (0usize, 0usize);
    for n in &names {
        let expect_lean = env.native_reducer_in(n, KernelTheory::Lean).is_some();
        assert_eq!(
            lean.native_reducer_for(n).is_some(),
            expect_lean,
            "`{n}` (Lean)"
        );
        assert_eq!(
            lean.native_reducer_for(n).is_some(),
            expect_lean,
            "`{n}` (memo)"
        );
        let expect_extended = env.native_reducer_in(n, KernelTheory::Extended).is_some();
        assert_eq!(
            extended.native_reducer_for(n).is_some(),
            expect_extended,
            "`{n}` (Extended)"
        );
        if expect_extended {
            admitted += 1;
        } else {
            refused += 1;
        }
    }
    // Non-vacuous: the prelude's canonical heads are admitted, and heads the
    // environment does not justify (absent, opaque, axiomatic) are refused.
    assert!(
        admitted > 0 && refused > 0,
        "admitted {admitted}, refused {refused}"
    );
}

/// The census under Clean's own prelude: nothing from the three opaque-extern
/// families survives, and every refusal names its reason.
#[test]
fn test_lean_theory_census_on_prelude_excludes_every_extern_family() {
    let env = Environment::with_prelude();
    let mut refused = Vec::new();
    let mut admitted = 0usize;
    for n in env.registered_native_reducer_names() {
        match env.lean_theory_exclusion(n) {
            None => admitted += 1,
            Some(why) => refused.push((n.to_string(), why)),
        }
    }
    let s = |x: &str| refused.iter().any(|(n, _)| n == x);
    for head in [
        "System.Platform.getIsOSX",
        "System.Platform.getIsWindows",
        "System.Platform.getIsEmscripten",
        "Float.add",
        "Float.ofScientific",
    ] {
        assert!(s(head), "`{head}` must be refused; census {refused:?}");
    }
    assert!(admitted > 0 && !refused.is_empty());
}

/// A two-constructor inductive `Coin` with `Coin.heads` / `Coin.tails`,
/// registered the way Clean registers every native inductive — which also
/// mirrors `Coin.casesOn` into the recursor table beside its definition.
fn coin_env() -> Environment {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};
    let mut env = Environment::new();
    let coin = Expr::const_(name("Coin"), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("Coin"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: name("Coin.heads"),
                    type_: coin.clone(),
                },
                Constructor {
                    name: name("Coin.tails"),
                    type_: coin,
                },
            ],
        }],
    })
    .expect("a two-constructor enumeration registers");
    env
}

/// `@Coin.casesOn.{1} (fun _ => Coin) Coin.heads Coin.tails Coin.heads`: the
/// heads case of a `casesOn` whose result type is `Coin` itself, so it reduces
/// to its FIRST minor, `Coin.tails`.
fn cases_on_heads() -> Expr {
    let coin = Expr::const_(name("Coin"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, coin.clone(), coin);
    Expr::apps(
        Expr::const_(name("Coin.casesOn"), vec![Level::succ(Level::zero())]),
        [
            motive,
            Expr::const_(name("Coin.heads"), vec![]),
            Expr::const_(name("Coin.tails"), vec![]),
            Expr::const_(name("Coin.heads"), vec![]),
        ],
    )
}

/// Clean mirrors a native inductive's value-bearing `casesOn` into the
/// recursor table; Lean has no such mirror, because `casesOn` is the
/// definition `mkCasesOn` builds and reduces by δ to its value. A FORGED
/// mirror — the two rules' right-hand sides swapped, as a Clean-written
/// .olean could carry — steers ι-reduction in the extended theory, and must
/// not under Lean's: there the ι step declines a value-bearing head and δ
/// unfolds the checked value to the real `Coin.rec`.
#[test]
fn test_lean_theory_ignores_forged_cases_on_mirror() {
    let mut env = coin_env();
    let cases = name("Coin.casesOn");
    assert!(
        env.get_const(&cases).is_some_and(|c| c.value.is_some()),
        "the test needs a value-bearing casesOn"
    );
    let honest = TypeChecker::new(&env).whnf(&cases_on_heads());
    assert_eq!(honest, Expr::const_(name("Coin.tails"), vec![]));

    let mirror = env
        .recursors
        .get_mut(&cases)
        .expect("Clean mirrors casesOn into the recursor table");
    assert_eq!(mirror.rules.len(), 2);
    let first = mirror.rules[0].rhs.clone();
    mirror.rules[0].rhs = mirror.rules[1].rhs.clone();
    mirror.rules[1].rhs = first;

    // The extended theory reduces through the mirror, forged or not: this is
    // the arm that shows the forgery is live and the Lean arm is not vacuous.
    let extended = TypeChecker::new(&env).whnf(&cases_on_heads());
    assert_eq!(extended, Expr::const_(name("Coin.heads"), vec![]));

    let mut lean = TypeChecker::new(&env);
    lean.set_kernel_theory(KernelTheory::Lean);
    assert_eq!(
        lean.whnf(&cases_on_heads()),
        Expr::const_(name("Coin.tails"), vec![]),
        "under Lean's theory casesOn must reduce by its checked value, never its mirror"
    );
}
