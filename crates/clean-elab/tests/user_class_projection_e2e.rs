// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B06 — class projection application inserts
//! implicit + instance-implicit args** (`docs/plans/GAP_SWEEP_2026-07-09.md`).
//!
//! Root cause (three coupled gaps, all fixed here):
//!
//! 1. **Projection binder infos.** `elab_structure`'s projection generator
//!    emitted user-class projections with the params' DECLARED binder infos
//!    (explicit for `class C (α : Type)`) and an explicit `self`, so `C.f x`
//!    unified `x` against the `α : Type` binder ("expected Sort(Succ(Zero))
//!    … Discriminant(3) vs Discriminant(2)"). Lean makes ALL class params
//!    implicit and `self` instance-implicit — verified against Lean 4
//!    v4.30.0-rc2: `@MyMag.op : {α : Type} → [self : MyMag α] → α → α → α`.
//!    Ground truth: lean4 `src/Lean/Elab/Structure.lean` (`isClass` →
//!    `mkProjections`).
//!
//! 2. **Instance registry.** `register_elab_result` added a user `instance`
//!    only as a `Definition`; the kernel-side instance registry — which every
//!    subsequent declaration's `ElabCtx` rebuilds its `InstanceTable` from —
//!    never learned of it, so no later `C.f x` could resolve `[self]`.
//!    Ground truth: lean4 `src/Lean/Meta/Instances.lean` (`addInstance`).
//!
//! 3. **Ground-goal synthesis failure is LOUD.** An instance goal with no
//!    metavariables left that no instance inhabits now raises the typed
//!    `FailedToSynthesizeInstance` instead of leaking the metavariable into
//!    the declaration (kernel "contains free variables" — the wrong-reason
//!    reject of sweep row classes_instances/p17).
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{BinderInfo, ExprKind, Name};
use clean_parser::parse_file;

/// Drive the real file pipeline. Returns the environment and elaboration
/// results (one per surface decl) or the first error.
fn elaborate_file(source: &str) -> Result<(Environment, Vec<ElabResult>), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok((env, results))
}

fn expect_pass(source: &str) -> (Environment, Vec<ElabResult>) {
    elaborate_file(source).unwrap_or_else(|e| panic!("file must fully check, got: {e}\n{source}"))
}

fn expect_fail(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("file must be REJECTED, but it fully checked:\n{source}"),
        Err(e) => e,
    }
}

fn assert_empty_axiom_closure(env: &Environment, name: &str) {
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must be registered"));
    assert!(
        deps.is_empty(),
        "{name} must have an EMPTY axiom closure, got {deps:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Projection binder-info shape (the Lean 4 v4.30.0-rc2 ground truth)
// ═══════════════════════════════════════════════════════════════════════════

/// `@C.f : {α : Type} → [self : C α] → α → α → α` — params implicit,
/// `self` instance-implicit, field arrow explicit.
#[test]
fn b06_class_projection_binder_infos_match_lean() {
    let (env, _) = expect_pass("class MyMag (α : Type) where\n  op : α → α → α\n");
    let proj = env
        .get_const(&Name::from_string("MyMag.op"))
        .expect("MyMag.op projection must be registered");
    let ExprKind::Pi(param_bi, _, body) = proj.type_.kind() else {
        panic!(
            "MyMag.op must start with the class-param binder, got {:?}",
            proj.type_
        );
    };
    assert_eq!(
        param_bi.info,
        BinderInfo::Implicit,
        "class param binder must be IMPLICIT (Lean mkProjections)"
    );
    let ExprKind::Pi(self_bi, _, _) = body.kind() else {
        panic!("MyMag.op must have a `self` binder, got {body:?}");
    };
    assert_eq!(
        self_bi.info,
        BinderInfo::InstImplicit,
        "class `self` binder must be INSTANCE-IMPLICIT (Lean mkProjections)"
    );
}

/// Plain STRUCTURE projections keep an explicit `self` (unchanged lane).
#[test]
fn b06_structure_projection_self_stays_explicit() {
    let (env, _) = expect_pass("structure Point where\n  x : Nat\n  y : Nat\n");
    let proj = env
        .get_const(&Name::from_string("Point.x"))
        .expect("Point.x projection must be registered");
    let ExprKind::Pi(self_bi, _, _) = proj.type_.kind() else {
        panic!("Point.x must be a function, got {:?}", proj.type_);
    };
    assert_eq!(
        self_bi.info,
        BinderInfo::Default,
        "structure `self` binder must stay EXPLICIT"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Sweep rows flipped to MATCH_ACCEPT (value pins, kernel-certified)
// ═══════════════════════════════════════════════════════════════════════════

/// classes_instances/p01: `where`-instance + plain `C.f x` use.
#[test]
fn b06_p01_basic_class_where_pins() {
    let (env, _) = expect_pass(
        "class MyMag (α : Type) where\n  op : α → α → α\n\n\
         instance : MyMag Nat where\n  op := Nat.add\n\n\
         theorem p01_pin : MyMag.op 2 3 = 5 := rfl",
    );
    assert_empty_axiom_closure(&env, "p01_pin");
}

/// classes_instances/p02: NAMED instance.
#[test]
fn b06_p02_named_instance_pin() {
    expect_pass(
        "class Sz (α : Type) where\n  sz : α → Nat\n\n\
         instance natSz : Sz Nat where\n  sz n := n + 1\n\n\
         theorem p02_pin : Sz.sz (3 : Nat) = 4 := rfl",
    );
}

/// classes_instances/p03: `[inst]` binder in a def; projection on the local
/// instance; value certified through the global instance.
#[test]
fn b06_p03_inst_binder_def_pin() {
    let (env, _) = expect_pass(
        "class Dbl (α : Type) where\n  dbl : α → α\n\n\
         instance : Dbl Nat := ⟨fun n => n * 2⟩\n\n\
         def doubleIt {α : Type} [Dbl α] (a : α) : α := Dbl.dbl a\n\n\
         theorem p03_pin : doubleIt (4 : Nat) = 8 := rfl",
    );
    assert_empty_axiom_closure(&env, "p03_pin");
}

/// classes_instances/p07: `outParam` marker — β inferred from the instance.
#[test]
fn b06_p07_outparam_pin() {
    expect_pass(
        "class Conv (α : Type) (β : outParam Type) where\n  conv : α → β\n\n\
         instance : Conv Nat Int := ⟨Int.ofNat⟩\n\n\
         theorem p07_pin : Conv.conv (3 : Nat) = (3 : Int) := rfl",
    );
}

/// classes_instances/p08: section `variable {α} [Tagd α]` feeding a def.
#[test]
fn b06_p08_variable_instance_pin() {
    expect_pass(
        "class Tagd (α : Type) where\n  tag : α → Nat\n\n\
         variable {α : Type} [Tagd α]\n\n\
         def tagOf (a : α) : Nat := Tagd.tag a\n\n\
         instance : Tagd Nat := ⟨fun n => n + 5⟩\n\n\
         theorem p08_pin : tagOf (1 : Nat) = 6 := rfl",
    );
}

/// classes_instances/p10: structure-literal instance body.
#[test]
fn b06_p10_struct_syntax_instance_pin() {
    expect_pass(
        "class Cs (α : Type) where\n  v : α → Nat\n\n\
         instance : Cs Nat := { v := fun n => n * 3 }\n\n\
         theorem p10_pin : Cs.v (2 : Nat) = 6 := rfl",
    );
}

/// classes_instances/p12: derived instance chain `[Sho α] → Sho (Option α)`.
#[test]
fn b06_p12_derived_instance_chain_pin() {
    let (env, _) = expect_pass(
        "class Sho (α : Type) where\n  sho : α → Nat\n\n\
         instance : Sho Nat := ⟨fun _ => 1⟩\n\
         instance {α : Type} [Sho α] : Sho (Option α) := ⟨fun _ => 2⟩\n\n\
         theorem p12_pin : Sho.sho (some (0 : Nat)) = 2 := rfl",
    );
    assert_empty_axiom_closure(&env, "p12_pin");
}

/// classes_instances/p14: `attribute [instance]` on an existing def.
#[test]
fn b06_p14_attribute_instance_pin() {
    expect_pass(
        "class Ea (α : Type) where\n  v : α → Nat\n\n\
         def eNat : Ea Nat := ⟨fun n => n + 7⟩\n\n\
         attribute [instance] eNat\n\n\
         theorem p14_pin : Ea.v (1 : Nat) = 8 := rfl",
    );
}

/// classes_instances/p15: `local instance` in a section resolves in-section.
#[test]
fn b06_p15_local_instance_section_pin() {
    expect_pass(
        "class Fl (α : Type) where\n  v : α → Nat\n\n\
         section\n\
         local instance : Fl Nat := ⟨fun n => n + 2⟩\n\
         theorem p15_pin : Fl.v (1 : Nat) = 3 := rfl\n\
         end",
    );
}

/// classes_instances/p20: bare projection as a polymorphic ARGUMENT
/// (`some Zz.z`) gets implicit/instance insertion before unification.
#[test]
fn b06_p20_bare_projection_argument_pin() {
    let (env, _) = expect_pass(
        "class Zz (α : Type) where\n  z : α\n\n\
         instance : Zz Nat := ⟨0⟩\n\
         instance {α : Type} [Zz α] : Zz (Option α) := ⟨some Zz.z⟩\n\n\
         theorem p20_pin : (Zz.z : Option Nat) = some 0 := rfl",
    );
    assert_empty_axiom_closure(&env, "p20_pin");
}

// ═══════════════════════════════════════════════════════════════════════════
// Loud negatives
// ═══════════════════════════════════════════════════════════════════════════

/// classes_instances/p17: no `Hm Int` instance — the reject must be the
/// RIGHT-reason typed error, not a leaked-metavariable kernel rejection.
#[test]
fn b06_p17_missing_instance_rejects_with_synthesis_error() {
    let err = expect_fail(
        "class Hm (α : Type) where\n  v : α → Nat\n\n\
         def useH (a : Int) : Nat := Hm.v a",
    );
    assert!(
        err.contains("failed to synthesize"),
        "reject must name the unsynthesizable instance goal, got: {err}"
    );
    assert!(
        err.contains("Hm"),
        "reject must mention the class goal `Hm Int`, got: {err}"
    );
}

/// Wrong-value witnesses must be REJECTED (the pins above are not vacuous).
#[test]
fn b06_wrong_value_witnesses_rejected() {
    expect_fail(
        "class MyMag (α : Type) where\n  op : α → α → α\n\n\
         instance : MyMag Nat where\n  op := Nat.add\n\n\
         theorem bad : MyMag.op 2 3 = 6 := rfl",
    );
    expect_fail(
        "class Zz (α : Type) where\n  z : α\n\n\
         instance : Zz Nat := ⟨0⟩\n\
         instance {α : Type} [Zz α] : Zz (Option α) := ⟨some Zz.z⟩\n\n\
         theorem bad : (Zz.z : Option Nat) = some 1 := rfl",
    );
    expect_fail(
        "class Conv (α : Type) (β : outParam Type) where\n  conv : α → β\n\n\
         instance : Conv Nat Int := ⟨Int.ofNat⟩\n\n\
         theorem bad : Conv.conv (3 : Nat) = (4 : Int) := rfl",
    );
}

/// `attribute [instance]` on a def whose type is NOT a class application is a
/// LOUD error (Lean: "invalid 'instance' attribute").
#[test]
fn b06_attribute_instance_on_non_class_rejects() {
    expect_fail(
        "def notAnInstance : Nat := 3\n\n\
         attribute [instance] notAnInstance",
    );
}
