// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B12 — instance declaration machinery**
//! (`docs/plans/GAP_SWEEP_2026-07-09.md`), the four coupled sub-defects:
//!
//! 1. **Anonymous-instance name freshening.** A second anonymous
//!    `instance : C T` used to die `Duplicate declaration: instCT`; Lean
//!    freshens (`mkInstanceName` → `mkUnusedBaseName`, `instCT_1`, …).
//!    Rows `classes_instances/p05,p06,p16`.
//!
//! 2. **Later-wins ordering (a value bug).** For two EQUAL-priority instances
//!    Lean resolves the most-recently-declared one first (`Meta/Instances.lean`,
//!    `addInstance` prepends). Clean used to resolve the first-declared — a
//!    kernel-certified WRONG value (`Qw.v 0 = 1`, Lean says `2`). Row
//!    `classes_instances/p06`. Fixed in `clean-kernel` `register_instance`
//!    (prepend within a priority tier).
//!
//! 3. **Default class fields.** A defaulted method omitted by an instance is
//!    now materialized from `<Class>.<field>._default` (Lean StructInst);
//!    previously "missing field X". Rows `classes_instances/p04,p13`.
//!
//! 4. **`extends`-instances.** `instance : B where a1 := …; b1 := …` for
//!    `class B extends A` now assembles the parent subobject `toA`, instead of
//!    demanding the raw `toA` field. Row `classes_instances/p09` (rides B10's
//!    toParent embedding).
//!
//! These drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict. Every
//! accept is a `:= rfl` VALUE pin (kernel-certified) with an EMPTY domain-axiom
//! closure; every wrong-value witness must REJECT.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
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

/// A value pin is not vacuous only if its transitive axiom closure is empty —
/// the resolution + default materialization must bottom out in real
/// definitions, never in axioms or `sorry`.
fn assert_empty_axiom_closure(env: &Environment, name: &str) {
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must be registered"));
    assert!(
        deps.is_empty(),
        "{name} must have an EMPTY axiom closure, got {deps:?}"
    );
}

fn is_registered(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

// ═══════════════════════════════════════════════════════════════════════════
// (1) Anonymous-instance name freshening
// ═══════════════════════════════════════════════════════════════════════════

/// Two anonymous `instance : Qw Nat` no longer collide — the second freshens to
/// `instQwNat_1`, and BOTH register as constants + instances.
#[test]
fn b12_freshened_anonymous_instances_both_register() {
    let (env, _) = expect_pass(
        "class Qw (α : Type) where\n  v : α → Nat\n\n\
         instance : Qw Nat := ⟨fun _ => 1⟩\n\
         instance : Qw Nat := ⟨fun _ => 2⟩\n",
    );
    assert!(
        is_registered(&env, "instQwNat"),
        "first anonymous instance keeps the base name instQwNat"
    );
    assert!(
        is_registered(&env, "instQwNat_1"),
        "second anonymous instance must be freshened to instQwNat_1 (mkUnusedBaseName)"
    );
    assert!(env.is_instance(&Name::from_string("instQwNat")));
    assert!(env.is_instance(&Name::from_string("instQwNat_1")));
}

/// A THIRD anonymous instance freshens to `_2` — the suffix walk continues.
#[test]
fn b12_third_anonymous_instance_freshens_to_2() {
    let (env, _) = expect_pass(
        "class Qw (α : Type) where\n  v : α → Nat\n\n\
         instance : Qw Nat := ⟨fun _ => 1⟩\n\
         instance : Qw Nat := ⟨fun _ => 2⟩\n\
         instance : Qw Nat := ⟨fun _ => 3⟩\n",
    );
    for n in ["instQwNat", "instQwNat_1", "instQwNat_2"] {
        assert!(is_registered(&env, n), "{n} must be registered");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (2) Later-wins ordering — the VALUE pins (Lean's values)
// ═══════════════════════════════════════════════════════════════════════════

/// `classes_instances/p06`. Two equal-priority instances; the LATER one wins.
/// Lean value: `2`. (Clean used to certify `1` by rfl — the silent-wrong bug.)
#[test]
fn b12_p06_later_equal_priority_instance_wins_value_2() {
    let (env, _) = expect_pass(
        "class Qw (α : Type) where\n  v : α → Nat\n\n\
         instance : Qw Nat := ⟨fun _ => 1⟩\n\
         instance : Qw Nat := ⟨fun _ => 2⟩\n\n\
         theorem p06_pin : Qw.v (0 : Nat) = 2 := rfl",
    );
    assert_empty_axiom_closure(&env, "p06_pin");
}

/// The wrong-value witness (the OLD first-declared value) must now REJECT — the
/// pin above is not vacuous.
#[test]
fn b12_p06_first_declared_value_rejected() {
    expect_fail(
        "class Qw (α : Type) where\n  v : α → Nat\n\n\
         instance : Qw Nat := ⟨fun _ => 1⟩\n\
         instance : Qw Nat := ⟨fun _ => 2⟩\n\n\
         theorem bad : Qw.v (0 : Nat) = 1 := rfl",
    );
}

/// Symmetry check: swap the declaration order — now the value is `1` (the new
/// most-recent). Proves the pin tracks DECLARATION ORDER, not the literal.
#[test]
fn b12_p06_reversed_order_flips_winner() {
    let (env, _) = expect_pass(
        "class Qw (α : Type) where\n  v : α → Nat\n\n\
         instance : Qw Nat := ⟨fun _ => 2⟩\n\
         instance : Qw Nat := ⟨fun _ => 1⟩\n\n\
         theorem p06r_pin : Qw.v (0 : Nat) = 1 := rfl",
    );
    assert_empty_axiom_closure(&env, "p06r_pin");
}

/// `classes_instances/p05`. Priority DOMINATES declaration order: the
/// `(priority := high)` instance wins even though it is declared first (and the
/// later default-priority one would otherwise win under most-recent-first).
/// Lean value: `2`.
#[test]
fn b12_p05_higher_priority_wins_value_2() {
    let (env, _) = expect_pass(
        "class PrA (α : Type) where\n  v : α → Nat\n\n\
         instance (priority := high) : PrA Nat := ⟨fun _ => 2⟩\n\
         instance : PrA Nat := ⟨fun _ => 1⟩\n\n\
         theorem p05_pin : PrA.v (0 : Nat) = 2 := rfl",
    );
    assert_empty_axiom_closure(&env, "p05_pin");
}

/// `classes_instances/p16`. Numeric `(priority := 2000)` wins over the default.
/// Lean value: `2`.
#[test]
fn b12_p16_numeric_priority_wins_value_2() {
    let (env, _) = expect_pass(
        "class Gn (α : Type) where\n  v : α → Nat\n\n\
         instance (priority := 2000) : Gn Nat := ⟨fun _ => 2⟩\n\
         instance : Gn Nat := ⟨fun _ => 1⟩\n\n\
         theorem p16_pin : Gn.v (0 : Nat) = 2 := rfl",
    );
    assert_empty_axiom_closure(&env, "p16_pin");
}

/// A LOWER-priority instance declared LATER must NOT win — priority dominates
/// recency in both directions.
#[test]
fn b12_lower_priority_later_does_not_win() {
    let (env, _) = expect_pass(
        "class Gn (α : Type) where\n  v : α → Nat\n\n\
         instance (priority := 2000) : Gn Nat := ⟨fun _ => 2⟩\n\
         instance (priority := 100) : Gn Nat := ⟨fun _ => 1⟩\n\n\
         theorem prio_pin : Gn.v (0 : Nat) = 2 := rfl",
    );
    assert_empty_axiom_closure(&env, "prio_pin");
}

// ═══════════════════════════════════════════════════════════════════════════
// (3) Default class fields — both ways
// ═══════════════════════════════════════════════════════════════════════════

/// `classes_instances/p04`. A defaulted method (`greet := fun a => base a + 1`)
/// OMITTED by the instance is materialized from `Greet.greet._default`.
/// `greet 5 = base 5 + 1 = 5 + 1 = 6`.
#[test]
fn b12_p04_default_method_omitted_is_materialized() {
    let (env, _) = expect_pass(
        "class Greet (α : Type) where\n  base : α → Nat\n  greet : α → Nat := fun a => base a + 1\n\n\
         instance : Greet Nat where\n  base := fun n => n\n\n\
         theorem p04_pin : Greet.greet (5 : Nat) = 6 := rfl",
    );
    // The generated default fn is a real, kernel-checked definition.
    assert!(
        is_registered(&env, "Greet.greet._default"),
        "the dependent default must be emitted as Greet.greet._default"
    );
    assert_empty_axiom_closure(&env, "p04_pin");
}

/// `classes_instances/p13`. When the instance PROVIDES the defaulted field, the
/// provided value wins (the default is not used). `extra 5 = 15`.
#[test]
fn b12_p13_default_method_overridden_uses_provided() {
    let (env, _) = expect_pass(
        "class Dm (α : Type) where\n  base : α → Nat\n  extra : α → Nat := fun a => base a + 1\n\n\
         instance : Dm Nat where\n  base := fun n => n\n  extra := fun n => n + 10\n\n\
         theorem p13_pin : Dm.extra (5 : Nat) = 15 := rfl",
    );
    assert_empty_axiom_closure(&env, "p13_pin");
}

/// The default fill is a real fill, not an axiom: a WRONG value witness for the
/// materialized default must REJECT.
#[test]
fn b12_p04_default_wrong_value_rejected() {
    expect_fail(
        "class Greet (α : Type) where\n  base : α → Nat\n  greet : α → Nat := fun a => base a + 1\n\n\
         instance : Greet Nat where\n  base := fun n => n\n\n\
         theorem bad : Greet.greet (5 : Nat) = 7 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (4) extends-instances via `where`
// ═══════════════════════════════════════════════════════════════════════════

/// `classes_instances/p09`. `instance : B1 Nat where a1 := …; b1 := …` for a
/// `class B1 extends A1` (class-extends-CLASS) assembles the parent `toA1`
/// subobject from the flattened `a1` spelling.
///
/// **Closed by B24.** `elab_class` now records the `(toA1, A1)` subobject
/// metadata and synthesizes the derived inherited projection
/// `B1.a1 := fun {α} [self] => @A1.a1 α (@B1.toA1 α self)`, so the instance-
/// `where` groups the inline `a1` into `toA1` (via
/// `rewrite_parent_subobject_construction` +
/// `inherited_field_parent_proj`) and both projections compute. Full coverage in
/// `class_extends_instance_e2e.rs`.
#[test]
fn b24_p09_extends_instance_assembles_parent() {
    let (env, _) = expect_pass(
        "class A1 (α : Type) where\n  a1 : α → Nat\n\n\
         class B1 (α : Type) extends A1 α where\n  b1 : α → Nat\n\n\
         instance : B1 Nat where\n  a1 := fun n => n\n  b1 := fun n => n + 1\n\n\
         theorem p09b_pin : B1.b1 (3 : Nat) = 4 := rfl\n\
         theorem p09a_pin : B1.a1 (7 : Nat) = 7 := rfl",
    );
    assert_empty_axiom_closure(&env, "p09a_pin");
    assert_empty_axiom_closure(&env, "p09b_pin");
}

// ═══════════════════════════════════════════════════════════════════════════
// Loud negatives — genuine errors still reject (never silently accepted)
// ═══════════════════════════════════════════════════════════════════════════

/// A NON-defaulted field omitted by an instance is still a loud reject (the
/// missing-field routing to the structure-literal path reports it precisely,
/// it does not silently fill or accept).
#[test]
fn b12_genuinely_missing_field_rejects() {
    let err = expect_fail(
        "class Greet (α : Type) where\n  base : α → Nat\n  greet : α → Nat := fun a => base a + 1\n\n\
         instance : Greet Nat where\n  greet := fun _ => 0",
    );
    assert!(
        err.contains("base") || err.to_lowercase().contains("missing"),
        "reject must name the genuinely-missing non-defaulted field `base`, got: {err}"
    );
}
