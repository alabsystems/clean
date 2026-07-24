// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B10 — `extends` parent-embedding representation +
//! toParent projections** of `docs/plans/GAP_SWEEP_2026-07-09.md`.
//!
//! Before B10, clean FLATTENED parents into the child constructor
//! (`B.mk : Nat → Nat → B`) and never synthesized `toA`, so the canonical
//! `B.mk (A.mk 1) 2` was rejected, `b.toA` was `UnknownProjectionField`, and
//! the surface layout diverged from the `.olean`-imported twin (an interop
//! hole). B10 switches the surface elaborator to Lean's subobject layout
//! (`src/Lean/Elab/Structure.lean` `withParents`/`mkToParentName`):
//!
//!   `structure B extends A where y : Nat`
//!     ⇝  ctor  `B.mk : A → Nat → B`      (parent embedded, NOT flattened)
//!        field table  `[toA, y]`         (matches the imported twin)
//!        `B.toA : B → A`                 (direct kernel projection)
//!        `B.x   : B → Nat := A.x ∘ B.toA` (derived, through the subobject)
//!
//! Covers sweep rows `structures/p07_extends_braces`,
//! `structures/sub_p07_true_repr`, `structures/p08_extends_anon_flatten`,
//! `structures/p18_multi_extends`, and `classes_instances/p09_class_extends`
//! (the class-`extends` instance-`where` assembly — was a B10/B12 right-reason
//! descope, now CLOSED by B24; full coverage in `class_extends_instance_e2e.rs`).
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

const AB: &str = "structure A where\n  x : Nat\n\nstructure B extends A where\n  y : Nat\n\n";

// ═══════════════════════════════════════════════════════════════════════════
// Representation: subobject layout matching the imported twin
// ═══════════════════════════════════════════════════════════════════════════

/// The child's registered constructor field table is `[toA, y]` (the embedded
/// parent subobject, then the own field) — NOT the old flattened `[x, y]`.
/// Byte-compatible with what `.olean` import recovers for the same structure.
#[test]
fn b10_field_table_is_subobject_not_flattened() {
    let env = expect_pass(AB);
    let fields = env
        .get_structure_field_names(&Name::from_string("B"))
        .expect("B has a field table");
    assert_eq!(
        fields,
        &[Name::from_string("toA"), Name::from_string("y")],
        "B embeds the parent as `toA` and declares `y` (subobject layout)"
    );
    // And the subobject metadata records `(toA, A)`.
    let parents = env
        .get_structure_parents(&Name::from_string("B"))
        .expect("B records its extends parents");
    assert_eq!(
        parents,
        &[(Name::from_string("toA"), Name::from_string("A"))],
        "B records the toA→A subobject link"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// sub_p07_true_repr — canonical constructor `B.mk (A.mk 1) 2`
// ═══════════════════════════════════════════════════════════════════════════

/// The canonical, Lean-faithful constructor application is accepted and its
/// field values pin by `rfl` (was a kernel `const mismatch: A vs Nat` before).
#[test]
fn b10_canonical_ctor_accepted_and_pins() {
    let src = format!(
        "{AB}def b : B := B.mk (A.mk 1) 2\n\
         theorem c_x : b.x = 1 := rfl\n\
         theorem c_y : b.y = 2 := rfl\n\
         theorem c_toA : b.toA = A.mk 1 := rfl"
    );
    expect_pass(&src);
}

/// The old flattened spelling `B.mk 1 2` is now REJECTED — the first argument
/// must be the parent subobject value, not a bare `Nat`.
#[test]
fn b10_flattened_ctor_spelling_rejected() {
    let src = format!("{AB}def b : B := B.mk 1 2");
    let err = expect_fail(&src);
    assert!(
        err.contains("mismatch") || err.contains("Mismatch") || err.contains("type"),
        "flattened `B.mk 1 2` must fail with a type error, got: {err}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// p07_extends_braces — brace-init + field access through the parent chain
// ═══════════════════════════════════════════════════════════════════════════

/// Base-less brace init assembles the parent subobject from flattened field
/// spellings, and inherited-field access resolves through `toA` (`b.x` reduces
/// to `A.x b.toA`). `b.toA` itself computes.
#[test]
fn b10_brace_init_and_chain_access() {
    let src = format!(
        "{AB}def b : B := {{ x := 1, y := 2 }}\n\
         theorem p07a : b.x = 1 := rfl\n\
         theorem p07b : b.y = 2 := rfl\n\
         theorem p07toA : b.toA = A.mk 1 := rfl\n\
         theorem p07toA_x : b.toA.x = 1 := rfl"
    );
    expect_pass(&src);
}

// ═══════════════════════════════════════════════════════════════════════════
// p08_extends_anon_flatten — anonymous constructor flattens across subobjects
// ═══════════════════════════════════════════════════════════════════════════

/// `⟨1, 2⟩ : B` flattens across the parent subobject to `B.mk (A.mk 1) 2`.
#[test]
fn b10_anon_ctor_flattens_across_subobject() {
    let src = format!(
        "{AB}def b : B := ⟨1, 2⟩\n\
         theorem p08a : b.x = 1 := rfl\n\
         theorem p08b : b.y = 2 := rfl"
    );
    expect_pass(&src);
}

/// A multi-field parent contributes multiple leaf slots to the flat
/// `⟨…⟩`: `A` has two fields, so `⟨1, 9, 2⟩ : B` builds `B.mk (A.mk 1 9) 2`.
#[test]
fn b10_anon_ctor_flattens_multi_field_parent() {
    let src = "structure A where\n  x : Nat\n  w : Nat\n\n\
               structure B extends A where\n  y : Nat\n\n\
               def b : B := ⟨1, 9, 2⟩\n\
               theorem a_x : b.x = 1 := rfl\n\
               theorem a_w : b.w = 9 := rfl\n\
               theorem a_y : b.y = 2 := rfl";
    expect_pass(src);
}

// ═══════════════════════════════════════════════════════════════════════════
// with-update through the parent subobject
// ═══════════════════════════════════════════════════════════════════════════

/// `{ b with x := 5 }` updates an inherited field through the parent subobject
/// (rewritten to `{ b with toA := { b.toA with x := 5 } }`) while preserving
/// the own field; and `{ b with y := 7 }` updates the own field, preserving the
/// inherited one.
#[test]
fn b10_with_update_through_parent() {
    let src = format!(
        "{AB}def b : B := {{ x := 1, y := 2 }}\n\
         def b2 : B := {{ b with x := 5 }}\n\
         theorem u_x : b2.x = 5 := rfl\n\
         theorem u_y : b2.y = 2 := rfl\n\
         def b3 : B := {{ b with y := 7 }}\n\
         theorem u3_x : b3.x = 1 := rfl\n\
         theorem u3_y : b3.y = 7 := rfl"
    );
    expect_pass(&src);
}

// ═══════════════════════════════════════════════════════════════════════════
// p18_multi_extends — two disjoint parents become two subobjects
// ═══════════════════════════════════════════════════════════════════════════

/// `C extends A, B` embeds both parents as subobjects (`toA`, `toB`); brace
/// init assembles both and all three flattened fields project.
#[test]
fn b10_multi_extends_two_subobjects() {
    let src = "structure A where\n  x : Nat\n\nstructure B where\n  y : Nat\n\n\
               structure C extends A, B where\n  z : Nat\n\n\
               def c : C := { x := 1, y := 2, z := 3 }\n\
               theorem m_x : c.x = 1 := rfl\n\
               theorem m_y : c.y = 2 := rfl\n\
               theorem m_z : c.z = 3 := rfl\n\
               theorem m_toA : c.toA = A.mk 1 := rfl\n\
               theorem m_toB : c.toB = B.mk 2 := rfl";
    let env = expect_pass(src);
    let fields = env
        .get_structure_field_names(&Name::from_string("C"))
        .expect("C has a field table");
    assert_eq!(
        fields,
        &[
            Name::from_string("toA"),
            Name::from_string("toB"),
            Name::from_string("z")
        ],
        "C embeds both parents as subobjects, then declares z"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Empty-closure brace init through a defaulted / field-less parent
// ═══════════════════════════════════════════════════════════════════════════

/// A parent with only defaulted fields is filled by the empty closure `{}` on
/// the child, threaded through the synthesized `toBase := {}`.
#[test]
fn b10_empty_closure_defaulted_parent() {
    let src = "structure Base where\n  n : Nat := 3\n\n\
               structure Ext extends Base where\n  m : Nat := 4\n\n\
               def e : Ext := {}\n\
               theorem e_n : e.n = 3 := rfl\n\
               theorem e_m : e.m = 4 := rfl";
    expect_pass(src);
}

/// A field-less parent: the child still constructs, and `toBlank` projects to
/// the parent's (unique) value. (The parent is named `Blank` rather than
/// `Empty` to avoid colliding with the prelude's built-in `Empty` type.)
#[test]
fn b10_empty_field_less_parent() {
    let src = "structure Blank where\n\nstructure Wrap extends Blank where\n  v : Nat\n\n\
               def w : Wrap := { v := 7 }\n\
               theorem w_v : w.v = 7 := rfl";
    expect_pass(src);
}

// ═══════════════════════════════════════════════════════════════════════════
// Loud negatives
// ═══════════════════════════════════════════════════════════════════════════

/// An unknown field is a LOUD typed error (with the own-field suggestion),
/// never silently dropped.
#[test]
fn b10_unknown_field_is_loud() {
    let err = expect_fail(&format!("{AB}def bad : B := {{ x := 1, y := 2, z := 3 }}"));
    assert!(
        err.contains("Unknown structure field") && err.contains('z'),
        "unknown field `z` must be a loud UnknownStructureField, got: {err}"
    );
}

/// An omitted inherited field (no default) is reported missing AGAINST THE
/// PARENT (`MissingStructureFields { A, [x] }`), matching Lean's flattened-view
/// "fields missing: `x`".
#[test]
fn b10_missing_inherited_field_is_loud() {
    let err = expect_fail(&format!("{AB}def bad : B := {{ y := 2 }}"));
    assert!(
        err.contains("Missing field") && err.contains('x'),
        "omitted inherited field `x` must be reported missing, got: {err}"
    );
}

/// B24 (was the B10/B12 descope): `class B1 extends A1 α` embeds the parent as
/// `toA1` AND assembling the parent from an instance-`where` block now works —
/// the inline inherited `a1` is grouped into the `toA1` subobject, and both the
/// own projection `B1.b1` and the derived inherited projection `B1.a1` (composed
/// through `toA1`) compute. Full class-extends-instance coverage lives in
/// `class_extends_instance_e2e.rs`; this pin guards the exact former-descope
/// shape and its value.
#[test]
fn b24_class_extends_instance_where_assembles_and_pins() {
    let src = "class A1 (a : Type) where\n  a1 : a → Nat\n\n\
               class B1 (a : Type) extends A1 a where\n  b1 : a → Nat\n\n\
               instance : B1 Nat where\n  a1 := fun n => n\n  b1 := fun n => n + 1\n\n\
               theorem c_a1 : B1.a1 (7 : Nat) = 7 := rfl\n\
               theorem c_b1 : B1.b1 (3 : Nat) = 4 := rfl";
    expect_pass(src);
}

/// Parameterized-parent `structure … extends P args` (the Mathlib base shape
/// `Unique (α : Sort u) extends Inhabited α`). Before this landed, the surface
/// structure elaborator FAILED CLOSED on any parent with parameters
/// ("parameterized parent `P` is not yet supported"), so the whole structure —
/// and every downstream theorem using its fields — was rejected. This gated
/// Mathlib's entire structure hierarchy (extends Inhabited/Monoid/Group/…).
/// Now the subobject field type is the applied `P args` and the inherited
/// projections specialize to the child's parameters, so the structure, its
/// `toP` subobject, the inherited field, and downstream uses all elaborate and
/// kernel-check. Uses a `Type` parameter (the universe-polymorphic `Sort u`
/// base is exercised by the real-Mathlib `Unique`/`Subtype` measurement).
#[test]
fn parameterized_parent_structure_extends_elaborates_and_kernel_checks() {
    // `expect_pass` fully elaborates AND kernel-checks every decl; the three
    // rfl theorems below exercise the derived inherited projection `mk2.val`,
    // the own field `mk2.extra`, and the subobject projection `mk2.toParent.val`
    // — so a pass proves the parameterized-parent subobject layout is correct
    // and kernel-accepted.
    let _env = expect_pass(
        "structure Parent (\u{3b1} : Type) where\n  val : \u{3b1}\n\n\
         structure Child (\u{3b1} : Type) extends Parent \u{3b1} where\n  extra : \u{3b1}\n\n\
         def mk2 : Child Nat := { val := 1, extra := 2 }\n\
         theorem child_val : mk2.val = 1 := rfl\n\
         theorem child_extra : mk2.extra = 2 := rfl\n\
         theorem child_toParent_val : mk2.toParent.val = 1 := rfl",
    );
}

/// `structure X extends Inhabited α` against the BUILT-IN prelude `Inhabited`
/// (not a locally-defined parent). Before Inhabited's structure field table was
/// registered in the kernel prelude (`init_inhabited`), the surface `extends`
/// path rejected it with `UnknownStruct { "Inhabited" }` even though it is a
/// single-field structure — blocking the Mathlib base shape
/// `Unique (α : Sort u) extends Inhabited α` and everything downstream. Combined
/// with parameterized-parent `extends`, `extends Inhabited α` now elaborates and
/// kernel-checks end-to-end (the derived inherited `default` projection included).
#[test]
fn extends_builtin_parameterized_inhabited() {
    let _env = expect_pass(
        "structure WithDefault (\u{3b1} : Type) extends Inhabited \u{3b1} where\n  tag : Nat\n\n\
         def wd : WithDefault Nat := { default := 7, tag := 1 }\n\
         theorem wd_tag : wd.tag = 1 := rfl\n\
         theorem wd_default : wd.default = 7 := rfl",
    );
}
