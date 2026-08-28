// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for the open-carrier instance grab — instance search
//! COMMITTING a global candidate against a goal whose input position is still
//! an unassigned metavariable, and thereby ASSIGNING that metavariable to
//! whatever the candidate's carrier happened to be.
//!
//! Issue: `docs/issues/2026-08-24-bare-default-picks-arbitrary-inhabited-instance.md`
//! (lane C6, measured at `8577574eb` on the pinned Mathlib source slice).
//!
//! ## What went wrong
//!
//! A bare `default` elaborates to `@Inhabited.default ?a ?inst`, and `[Inhabited ?a]`
//! was synthesized while `?a` was still open. Clean already refused the DIRECT
//! form of that grab: `resolve_instance_candidates`' phase-1
//! `postpone_undetermined_inputs` check rejects a candidate whose input argument
//! is RIGID against a still-open goal input. That guard was one hop deep and
//! covered four classes, and the grab LAUNDERS through a sub-goal:
//!
//! * a polymorphic bridge instance `{a} → [C a] → Inhabited a` has a BARE
//!   METAVARIABLE conclusion argument, so phase 1 passes it (flex/flex
//!   unification is legitimately deferred, not a wrong grab);
//! * its `[C ?a]` sub-goal is in class `C`, which the allowlist does not name,
//!   so THERE a concrete `C Decoy` candidate is committed and `?a := Decoy`.
//!
//! The elaborated `default` is then a term at `Decoy`, and the declaration
//! fails typechecking against the type the author actually wrote. It is
//! fail-OPEN and a wrong DIAGNOSIS — the kernel still refuses the term, so it
//! was never an unsound accept, but the reported cause points away from the
//! real one and the declaration is lost.
//!
//! ## The reproduction, and what it measured
//!
//! The three fixtures below are the whole mechanism in five declarations. At
//! `10961061f` — WITHOUT the fix — they produced, verbatim, the three error
//! signatures the issue records for `Mathlib/Logic/Unique.lean`:
//!
//! ```text
//! carrier from the expected type   TypeMismatch { expected: "FVar(FVarId(0))",
//!   (`x = default`)                  actual: "cannot unify expressions of different
//!                                    shape: Discriminant(3) vs Discriminant(1)" }
//! `default` fixes Eq's carrier     TypeMismatch { expected: "Const(Decoy, [])",
//!   (`default = x`)                  actual: "... Discriminant(1) vs Discriminant(3)" }
//! ascription (`(default : b)`)     TypeMismatch { expected: "FVar(FVarId(0))",
//!                                    actual: "Const(Decoy, []) (cannot unify ...
//!                                    Discriminant(3) vs Discriminant(1))" }
//! ```
//!
//! `Discriminant(3)` is `ExprKind::Const` and `Discriminant(1)` is
//! `ExprKind::FVar` (`crates/clean-kernel/src/expr/kind.rs`) — so those are, in
//! order, `Unique.{eq_default, forall_iff, exists_iff}` + `heq_const_of_unique`;
//! `Unique.default_eq` (the row that names the invented type outright); and
//! `uniqueElim` / `uniqueElim_default`. One cause, three shapes.
//!
//! ## The fix these pin
//!
//! `ElabCtx::resolve_instance` reads `is_input_only_postpone_class` on the
//! TOP-LEVEL goal and propagates the answer as `strict` to every SUB-goal the
//! search generates — which is what Lean gets for free from
//! `withNewMCtxDepth` (`Lean/Meta/SynthInstance.lean`: the whole search runs at
//! a deeper metavariable-context depth, so the caller's metavariables are not
//! assignable ANYWHERE inside it). One flag, one pass: a search rooted outside
//! those four classes is byte-identical to before at every depth, and pays
//! nothing. LOCAL instance binders are never guarded — see
//! `test_local_instance_binder_still_determines_the_carrier`.
//!
//! Second half, in `apply_implicit_to_expected_type`: when the expected type
//! HAS pinned every deferred instance goal and synthesis still fails, the eager
//! fallback used to `pop_scope` (discarding `?a := <expected>`) and re-run the
//! search with the carrier re-opened — which is where the invented carrier got
//! in. It now reports the synthesis failure honestly.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::env::KernelInstanceInfo;
use clean_kernel::{Environment, Expr, Name};
use clean_parser::parse_file;

/// Elaborate every declaration in `src`, returning the first error (as its
/// `Debug` rendering) or `None` when all of them registered.
fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// Elaborate `src`, panicking with `label` if anything fails.
fn elab_ok(env: &mut Environment, src: &str, label: &str) {
    if let Some(e) = elab(env, src) {
        panic!("{label} must elaborate and kernel-check, got: {e}");
    }
}

/// Register an already-elaborated constant as a global instance of `class`.
fn register_instance(env: &mut Environment, name: &str, class: &str, priority: u32) {
    let n = Name::from_string(name);
    let c = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("fixture constant `{name}` must be registered first"))
        .clone();
    env.register_instance(KernelInstanceInfo {
        name: n.clone(),
        class_name: Name::from_string(class),
        priority,
        type_: Some(c.type_),
        value: Some(Expr::const_(n, vec![])),
    });
}

/// The laundering environment: a class `MyU` with a CONCRETE-carrier global
/// instance, plus a POLYMORPHIC `Inhabited` bridge whose conclusion argument is
/// a bare metavariable. Nothing here is exotic — it is the shape of Mathlib's
/// `Unique`/`Inhabited` pair reduced to five declarations.
fn laundering_env() -> Environment {
    let mut env = Environment::with_prelude();
    elab_ok(&mut env, "inductive Decoy where\n  | mk\n", "Decoy");
    elab_ok(&mut env, "class MyU (a : Type) where\n  uniq : a\n", "MyU");
    elab_ok(
        &mut env,
        "def decoyU : MyU Decoy := MyU.mk Decoy.mk\n",
        "decoyU",
    );
    register_instance(&mut env, "decoyU", "MyU", 1000);
    elab_ok(
        &mut env,
        "def bridgeInhabited {a : Type} [inst : MyU a] : Inhabited a := \
         Inhabited.mk (MyU.uniq a)\n",
        "bridgeInhabited",
    );
    register_instance(&mut env, "bridgeInhabited", "Inhabited", 1000);
    env
}

/// A second, competing concrete carrier — so the goal is not merely
/// undetermined but genuinely AMBIGUOUS: two instances, nothing to choose
/// between them.
fn add_second_decoy(env: &mut Environment) {
    elab_ok(env, "inductive Decoy2 where\n  | mk\n", "Decoy2");
    elab_ok(
        env,
        "def decoyU2 : MyU Decoy2 := MyU.mk Decoy2.mk\n",
        "decoyU2",
    );
    register_instance(env, "decoyU2", "MyU", 1000);
}

/// Assert `err` is a synthesis failure that names NEITHER decoy carrier.
///
/// The carrier-naming half is the actual anti-regression: an error that quotes
/// `Decoy` is the search having committed one, whatever the error's kind.
fn assert_honest_synthesis_failure(err: &str, label: &str) {
    assert!(
        err.contains("FailedToSynthesize"),
        "{label}: synthesis must fail HONESTLY (FailedToSynthesize), got: {err}"
    );
    assert!(
        !err.contains("Decoy"),
        "{label}: the search committed a carrier instead of postponing — the error \
         names a decoy: {err}"
    );
}

/// `x = default`, with the carrier determined by the EXPECTED type and no
/// instance available at that carrier.
///
/// Pre-fix: `TypeMismatch { expected: "FVar(FVarId(0))", actual: "cannot unify
/// expressions of different shape: Discriminant(3) vs Discriminant(1)" }` —
/// i.e. `default` came back at `Decoy`. This is the signature of
/// `Unique.eq_default` / `forall_iff` / `exists_iff` / `heq_const_of_unique`.
#[test]
fn test_open_carrier_is_postponed_not_committed_expected_type_position() {
    let mut env = laundering_env();
    let err = elab(
        &mut env,
        "theorem probeEq {b : Type} (x : b) : x = default := sorry",
    )
    .expect("no instance exists at the expected carrier, so this must fail");
    assert_honest_synthesis_failure(&err, "x = default");
}

/// The same defect reached through an ASCRIPTION — `(default : b)`. The issue
/// singles this shape out because `?a := b` is available from the ascription
/// and still lost.
///
/// Pre-fix: `TypeMismatch { expected: "FVar(FVarId(0))", actual: "Const(Decoy, [])
/// (cannot unify expressions of different shape: Discriminant(3) vs
/// Discriminant(1))" }` — the signature of `uniqueElim` / `uniqueElim_default`.
#[test]
fn test_open_carrier_is_postponed_not_committed_ascription_position() {
    let mut env = laundering_env();
    let err = elab(
        &mut env,
        "def probeAscribe {b : Type} (f : b -> Nat) : Nat := f (default : b)",
    )
    .expect("no instance exists at the ascribed carrier, so this must fail");
    assert_honest_synthesis_failure(&err, "(default : b)");
}

/// A genuinely AMBIGUOUS goal: two registered carriers, nothing determining
/// which. The search must FAIL rather than pick — and in particular must not
/// pick the higher-priority or more-recently-registered one.
#[test]
fn test_ambiguous_open_carrier_fails_instead_of_picking() {
    let mut env = laundering_env();
    add_second_decoy(&mut env);
    let err = elab(
        &mut env,
        "def probeAmbiguous {b : Type} (f : b -> Nat) : Nat := f (default : b)",
    )
    .expect("an ambiguous carrier must not resolve");
    assert_honest_synthesis_failure(&err, "ambiguous carrier");
    assert!(
        !err.contains("Decoy2"),
        "ambiguous carrier: search picked the second decoy: {err}"
    );
}

/// The other direction of the same guard, and the reason it must NOT postpone
/// everything: a goal whose carrier IS determined has to resolve promptly, in
/// the same elaboration pass, with no retry from the caller.
///
/// Three ways the carrier can be determined are covered: by the declaration's
/// result type at the laundering carrier itself (`Decoy`, reached through the
/// polymorphic bridge and its `MyU` sub-goal), by a prelude carrier (`Nat`),
/// and by the ascription that the postponed cases above could not use.
#[test]
fn test_determined_carrier_still_resolves_promptly() {
    let mut env = laundering_env();
    elab_ok(&mut env, "def viaBridge : Decoy := default", "viaBridge");
    elab_ok(&mut env, "def viaPrelude : Nat := default", "viaPrelude");
    elab_ok(
        &mut env,
        "def viaAscription : Nat := (default : Nat)",
        "viaAscription",
    );
}

/// A LOCAL `[inst : C t]` binder is a hypothesis of the declaration being
/// elaborated, so matching it can only produce a carrier the author already
/// wrote down. It is deliberately NOT guarded, and this is load-bearing in two
/// ways: `[Inhabited a]` in scope must keep working, and — for the laundering
/// shape — a local `[MyU b]` binder is what lets the bridge's sub-goal pin the
/// carrier CORRECTLY instead of the fix merely refusing the declaration.
#[test]
fn test_local_instance_binder_still_determines_the_carrier() {
    let mut env = laundering_env();
    elab_ok(
        &mut env,
        "theorem localInhabitedLhs {a : Type} [Inhabited a] (x : a) : default = x := sorry",
        "localInhabitedLhs",
    );
    elab_ok(
        &mut env,
        "theorem localInhabitedRhs {a : Type} [Inhabited a] (x : a) : x = default := sorry",
        "localInhabitedRhs",
    );
    elab_ok(
        &mut env,
        "theorem localBridged {b : Type} [MyU b] (x : b) : x = default := sorry",
        "localBridged",
    );
}

/// The roots the guard deliberately leaves alone. `strict` is keyed on the
/// TOP-LEVEL goal's class, so a search rooted at `OfNat`/`HAdd`/`HMul` is
/// unchanged at every depth and numeric literals and heterogeneous arithmetic
/// keep resolving exactly as before; `Decidable`/`BEq` roots are strict and
/// must still resolve when their carrier is determined.
#[test]
fn test_arithmetic_and_decidable_goals_are_unaffected() {
    let mut env = laundering_env();
    elab_ok(
        &mut env,
        "def addsLiteral (n : Nat) : Nat := n + 5",
        "addsLiteral",
    );
    elab_ok(
        &mut env,
        "def beqLiteral (n : Nat) : Bool := n == 5",
        "beqLiteral",
    );
    elab_ok(
        &mut env,
        "def decidableGuard (n : Nat) : Nat := if n = 0 then 1 else 2",
        "decidableGuard",
    );
}
