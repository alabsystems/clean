// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B24 — class `extends` instance-`where` assembly**
//! of `docs/plans/GAP_SWEEP_2026-07-09.md` (row
//! `classes_instances/p09_class_extends`).
//!
//! B10 landed the `extends` SUBOBJECT layout for STRUCTURES (child embeds
//! `toParent : Parent`, `toParent` projection synthesized, inherited projections
//! composed through it). B24 closes the same story for CLASSES: a
//! `class B extends A` embeds the parent as a `toA` instance-field, and an
//! `instance : B T where <A's fields> <B's fields>` (providing the PARENT's
//! fields inline) assembles the parent A-instance subobject from those flattened
//! fields — mirroring how B10 assembles structure parents, adapted to the
//! class/instance path.
//!
//! Before B24, `elab_class` embedded the parent as a `toParent` field but
//! recorded NO parent subobject metadata and synthesized NO derived
//! parent-field projection, so:
//!   - `instance : B1 Nat where a1 := …; b1 := …` REJECTED loudly ("unknown /
//!     missing field `a1`/`toA1`") — the B12 right-reason descope, and
//!   - `b.a1` (inherited-field access) failed as `UnknownProjectionField`.
//! B24 records `(toA1, A1)` and synthesizes
//! `B1.a1 := fun {α} [self] => @A1.a1 α (@B1.toA1 α self)`, so the where-block
//! assembles the parent and the chain projects.
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict; every rfl
//! pin is re-checked by the real kernel (zero domain axioms).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Drive the real file pipeline. Returns the environment (post-registration)
/// plus the elaboration results, or the first error's message.
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

fn expect_pass(source: &str) -> Environment {
    elaborate_file(source)
        .unwrap_or_else(|e| panic!("file must fully check, got: {e}\n{source}"))
        .0
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

/// The canonical p09 shape: parameterized `class A1 (α)`, `class B1 (α) extends
/// A1 α`, own field `b1`.
const A1B1: &str = "class A1 (α : Type) where\n  a1 : α → Nat\n\n\
                    class B1 (α : Type) extends A1 α where\n  b1 : α → Nat\n\n";

// ═══════════════════════════════════════════════════════════════════════════
// Subobject metadata: the class records (toA1, A1) exactly like a structure
// ═══════════════════════════════════════════════════════════════════════════

/// `class B1 extends A1` embeds the parent as a `toA1` field and records the
/// `(toA1, A1)` subobject link — the same metadata B10 records for a structure
/// `extends`. And the derived projection `B1.a1` exists (composed through
/// `toA1`), so the inherited field is projectable.
#[test]
fn b24_class_records_parent_subobject_and_derived_projection() {
    let env = expect_pass(A1B1);
    let fields = env
        .get_structure_field_names(&Name::from_string("B1"))
        .expect("B1 has a field table");
    assert_eq!(
        fields,
        &[Name::from_string("toA1"), Name::from_string("b1")],
        "B1 embeds the parent as `toA1` then declares `b1` (subobject layout)"
    );
    let parents = env
        .get_structure_parents(&Name::from_string("B1"))
        .expect("B1 records its extends parents");
    assert_eq!(
        parents,
        &[(Name::from_string("toA1"), Name::from_string("A1"))],
        "B1 records the toA1→A1 subobject link"
    );
    assert!(
        env.get_const(&Name::from_string("B1.a1")).is_some(),
        "B1.a1 derived projection (through toA1) must be synthesized"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// p09 — instance-`where` assembles the parent from flattened inherited fields
// ═══════════════════════════════════════════════════════════════════════════

/// `instance : B1 Nat where a1 := …; b1 := …` assembles the `toA1` parent
/// subobject from the inline inherited `a1`, and both projections compute:
///   - `B1.b1` on the instance = `fun n => n + 1`, pinned at `3 ↦ 4`,
///   - `B1.a1` (inherited, through `toA1`) = `fun n => n`, pinned at `7 ↦ 7`.
#[test]
fn b24_p09_instance_where_assembles_parent_and_pins() {
    let src = format!(
        "{A1B1}instance : B1 Nat where\n  a1 := fun n => n\n  b1 := fun n => n + 1\n\n\
         theorem p09_b1 : B1.b1 (3 : Nat) = 4 := rfl\n\
         theorem p09_a1 : B1.a1 (7 : Nat) = 7 := rfl"
    );
    let env = expect_pass(&src);
    assert_empty_axiom_closure(&env, "p09_a1");
    assert_empty_axiom_closure(&env, "p09_b1");
}

/// Field access on a `B1`-typed VALUE goes through the chain: `b.a1` resolves
/// via `B1.a1 = A1.a1 ∘ B1.toA1`, `b.b1` via the direct class projection, and
/// `b.toA1` projects the assembled parent instance.
#[test]
fn b24_field_access_through_chain_on_value() {
    let src = format!(
        "{A1B1}def b : B1 Nat := {{ a1 := fun n => n + 10, b1 := fun n => n * 2 }}\n\
         theorem v_a1 : b.a1 5 = 15 := rfl\n\
         theorem v_b1 : b.b1 5 = 10 := rfl\n\
         theorem v_toA1_a1 : b.toA1.a1 5 = 15 := rfl"
    );
    let env = expect_pass(&src);
    assert_empty_axiom_closure(&env, "v_a1");
    assert_empty_axiom_closure(&env, "v_toA1_a1");
}

/// Order-independence: providing the own field before the inherited field still
/// assembles correctly (the where-block is grouped by parent, not by position).
#[test]
fn b24_instance_where_field_order_independent() {
    let src = format!(
        "{A1B1}instance : B1 Nat where\n  b1 := fun n => n + 5\n  a1 := fun n => n + 2\n\n\
         theorem o_a1 : B1.a1 (1 : Nat) = 3 := rfl\n\
         theorem o_b1 : B1.b1 (1 : Nat) = 6 := rfl"
    );
    expect_pass(&src);
}

// ═══════════════════════════════════════════════════════════════════════════
// Non-parameterized parent (plainest `class B extends A` shape)
// ═══════════════════════════════════════════════════════════════════════════

/// The simplest shape — a parameter-less parent whose fields are plain values:
/// `class A where a : Nat`, `class B extends A where b : Nat`. The instance
/// assembles `toA` from the flat `a`, and both project.
#[test]
fn b24_monomorphic_parentless_class_extends() {
    // `B.a` is the derived inherited projection (through `toA`); `B.b` the own
    // one. Accessing the parent field through the CHILD projection resolves
    // `[self : B]` directly against the registered `B` instance.
    let src = "class A where\n  a : Nat\n\n\
               class B extends A where\n  b : Nat\n\n\
               instance : B where\n  a := 10\n  b := 20\n\n\
               theorem m_a : (B.a : Nat) = 10 := rfl\n\
               theorem m_b : (B.b : Nat) = 20 := rfl";
    let env = expect_pass(src);
    assert_empty_axiom_closure(&env, "m_a");
    assert_empty_axiom_closure(&env, "m_b");
}

// ═══════════════════════════════════════════════════════════════════════════
// Empty closures
// ═══════════════════════════════════════════════════════════════════════════

/// A parent whose only field is defaulted is filled by an empty inherited
/// group: the child instance provides only its own field and the `toA` subobject
/// is assembled from the parent's default.
#[test]
fn b24_empty_inherited_group_uses_parent_default() {
    let src = "class A where\n  a : Nat := 3\n\n\
               class B extends A where\n  b : Nat\n\n\
               instance : B where\n  b := 9\n\n\
               theorem d_a : (B.a : Nat) = 3 := rfl\n\
               theorem d_b : (B.b : Nat) = 9 := rfl";
    expect_pass(src);
}

/// A field-less parent: the child instance provides only its own field and the
/// `toBlank` subobject assembles from the empty parent. (Named `Blank` to avoid
/// the prelude's built-in `Empty`.)
#[test]
fn b24_field_less_parent_class() {
    let src = "class Blank where\n\n\
               class Wrap extends Blank where\n  v : Nat\n\n\
               instance : Wrap where\n  v := 7\n\n\
               theorem w_v : (Wrap.v : Nat) = 7 := rfl";
    expect_pass(src);
}

// ═══════════════════════════════════════════════════════════════════════════
// Loud negatives — descopes and genuine errors reject, never silently accept
// ═══════════════════════════════════════════════════════════════════════════

/// A genuinely missing inherited field (parent field with no default, omitted by
/// the instance) is a LOUD reject naming the field — never silently filled.
#[test]
fn b24_missing_inherited_field_is_loud() {
    let err = expect_fail(&format!(
        "{A1B1}instance : B1 Nat where\n  b1 := fun n => n + 1\n"
    ));
    assert!(
        err.to_lowercase().contains("a1") || err.to_lowercase().contains("missing"),
        "omitted inherited field `a1` must reject loudly, got: {err}"
    );
}

/// An unknown field on the instance-`where` (neither own nor inherited) is a
/// LOUD reject, never silently dropped.
#[test]
fn b24_unknown_field_is_loud() {
    let err = expect_fail(&format!(
        "{A1B1}instance : B1 Nat where\n  a1 := fun n => n\n  b1 := fun n => n + 1\n  zzz := fun n => n\n"
    ));
    assert!(
        err.to_lowercase().contains("zzz")
            || err.to_lowercase().contains("unknown")
            || err.to_lowercase().contains("field"),
        "unknown field `zzz` must reject loudly, got: {err}"
    );
}

/// A wrong-value witness is rejected by the kernel: the instance sets
/// `a1 := fun n => n`, so `B1.a1 (7 : Nat) = 8` is FALSE and the `rfl` pin must
/// fail (no silently-accepted wrong value).
#[test]
fn b24_wrong_value_pin_rejects() {
    let err = expect_fail(&format!(
        "{A1B1}instance : B1 Nat where\n  a1 := fun n => n\n  b1 := fun n => n + 1\n\n\
         theorem wrong : B1.a1 (7 : Nat) = 8 := rfl"
    ));
    assert!(
        err.to_lowercase().contains("mismatch") || err.to_lowercase().contains("type"),
        "wrong inherited-field value pin must be a loud kernel reject, got: {err}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Descope: multi-level class extends (grandparent field) fails LOUD
// ═══════════════════════════════════════════════════════════════════════════

/// DESCOPE (loud, documented): a THREE-level chain `C extends B extends A`
/// re-exposes only the DIRECT parent's fields on each child. A grandparent field
/// accessed on the grandchild (or provided flat in the grandchild instance) is
/// NOT assembled — it fails LOUDLY (unknown/missing field), never silently
/// wrong. The direct-parent field still assembles.
#[test]
fn b24_multilevel_grandparent_field_descoped_loud() {
    // `gp` is A's field, reachable on B (B.gp derived), but NOT on C — C only
    // re-exposes B's direct field table [toA, mid], not the transitively
    // inherited `gp`. Providing `gp` flat in the C instance is a loud reject.
    let src = "class A where\n  gp : Nat\n\n\
               class B extends A where\n  mid : Nat\n\n\
               class C extends B where\n  lo : Nat\n\n\
               instance : C where\n  gp := 1\n  mid := 2\n  lo := 3\n";
    let err = expect_fail(src);
    assert!(
        err.to_lowercase().contains("gp")
            || err.to_lowercase().contains("unknown")
            || err.to_lowercase().contains("missing")
            || err.to_lowercase().contains("field"),
        "grandparent field `gp` on C must fail loudly (multi-level descope), got: {err}"
    );
}
