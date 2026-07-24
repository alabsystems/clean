// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B11 — dependent structure fields +
//! value-parameterized Prop classes** of `docs/plans/GAP_SWEEP_2026-07-09.md`.
//!
//! Before B11, a field whose TYPE mentioned an earlier field (or a value
//! parameter) could not even be parsed: the field-type sub-grammar
//! (`field_arrow_expr`/`field_app_expr`) only knew application and `→`, so
//! `h : n = n` parsed as just `n`, leaving `= n` as an error-recovery raw
//! declaration ("parser recovery produced raw declaration: Eq n"). The
//! truncated field `h : n` then had a non-`Sort` domain, and the kernel
//! rejected the constructor with `Expected sort, got Nat at codomain of Pi`
//! (`structures/p19_dependent_field`, `classes_instances/p11_prop_class_*`).
//!
//! B11 routes field types through the full operator grammar (`=`, `<`, `>`,
//! `≤`, `≠`, `∧`, …), bounded at the next field by a newline-leading `ident :`
//! (`in_field_type`). The elaborator already threaded prior fields / params
//! into scope, so with the parse fixed the constructor is the dependent
//! telescope `(f1 : T1) → (f2 : T2 f1) → … → S params` — Lean's field telescope
//! (`src/Lean/Elab/Structure.lean`). This unblocks Subtype-style certified
//! structures (`structure S where val : Nat; property : 0 < val`), ubiquitous
//! in Lean core / Mathlib.
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict; every rfl
//! pin is re-checked by the real kernel (zero domain axioms — the dependent
//! constructor is registered via a fully-checked `add_inductive`).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{ExprKind, Name};
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

const CERTIFIED: &str = "structure Certified where\n  n : Nat\n  h : n = n\n\n";

// ═══════════════════════════════════════════════════════════════════════════
// p19_dependent_field — a field whose type mentions an earlier field
// ═══════════════════════════════════════════════════════════════════════════

/// The Subtype-style structure declares (was a parse + kernel `ExpectedSort`
/// failure), a value constructs with the proof witness, and field access pins
/// by `rfl`. This is the canonical `structures/p19_dependent_field` probe.
#[test]
fn b11_dependent_field_declares_constructs_and_pins() {
    let src = format!(
        "{CERTIFIED}def s : Certified := ⟨3, rfl⟩\n\
         theorem p19a : s.n = 3 := rfl\n\
         theorem p19h : s.h = rfl := rfl"
    );
    expect_pass(&src);
}

/// The generated constructor is a genuine DEPENDENT telescope: after the first
/// field `n : Nat` (a closed domain), the second field's type `@Eq Nat n n`
/// references the bound `n` — a loose bvar under the first binder. A flattened
/// (non-dependent) ctor would have a closed second domain, so this is the
/// structural witness that prior fields are threaded into later field types.
#[test]
fn b11_constructor_is_dependent_telescope() {
    let env = expect_pass(CERTIFIED);
    let ctor = env
        .get_const(&Name::from_string("Certified.mk"))
        .expect("Certified.mk is registered");
    // `Certified.mk : (n : Nat) → (h : @Eq Nat n n) → Certified`
    let ExprKind::Pi(_, dom_n, body) = ctor.type_.kind() else {
        panic!("ctor type must start with a Pi, got {:?}", ctor.type_);
    };
    assert!(
        !dom_n.has_loose_bvars(),
        "first field `n : Nat` has a closed domain"
    );
    let ExprKind::Pi(_, dom_h, _) = body.kind() else {
        panic!("ctor must take a second field, got {body:?}");
    };
    assert!(
        dom_h.has_loose_bvars(),
        "second field type `n = n` must reference the first field (dependent telescope)"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Subtype-style certified structures — the load-bearing Mathlib idiom
// ═══════════════════════════════════════════════════════════════════════════

/// `property : 0 < val` — a `<` comparison in a field type (previously
/// unparseable). Constructs with a `by decide` witness and the value pins.
#[test]
fn b11_subtype_lt_field() {
    let src = "structure Pos where\n  val : Nat\n  property : 0 < val\n\n\
               def two : Pos := ⟨2, by decide⟩\n\
               theorem two_val : two.val = 2 := rfl";
    expect_pass(src);
}

/// `property : val > 0` — the `>` spelling the sweep's B11 entry calls out.
#[test]
fn b11_subtype_gt_field() {
    let src = "structure Pos2 where\n  val : Nat\n  property : val > 0\n\n\
               def three : Pos2 := ⟨3, by decide⟩\n\
               theorem three_val : three.val = 3 := rfl";
    expect_pass(src);
}

/// A structure PARAMETER threaded into a later field's type
/// (`structure Vecish (n : Nat) where len : Nat; matches : len = n`).
#[test]
fn b11_parameter_referenced_in_field_type() {
    let src = "structure Vecish (n : Nat) where\n  len : Nat\n  same : len = n\n\n\
               def v : Vecish 4 := ⟨4, rfl⟩\n\
               theorem v_len : v.len = 4 := rfl";
    expect_pass(src);
}

// ═══════════════════════════════════════════════════════════════════════════
// p11_prop_class_inferinstance — value-parameterized Prop class
// ═══════════════════════════════════════════════════════════════════════════

const IS_GOOD: &str = "class IsGood (n : Nat) : Prop where\n  good : n = n\n\n";

/// A `class` parameterized by a Nat VALUE (not a type), with a Prop-valued
/// field that mentions the value parameter, declares and its constructor
/// kernel-checks (was `add_inductive Structure … Expected sort, got Nat`).
/// The instance value `⟨rfl⟩ : IsGood 3` constructs, and the class field
/// projects both by dot notation and positionally, pinning by `rfl` — the
/// class projection carries B06's implicit-param / inst-implicit-`self` binder
/// infos, so `IsGood.good mk3` inserts `{n}` and unifies `[self]`.
#[test]
fn b11_value_parameterized_prop_class() {
    let src = format!(
        "{IS_GOOD}def mk3 : IsGood 3 := ⟨rfl⟩\n\
         theorem access_dot : mk3.good = rfl := rfl\n\
         theorem access_pos : IsGood.good mk3 = rfl := rfl"
    );
    expect_pass(&src);
}

// ═══════════════════════════════════════════════════════════════════════════
// Loud negatives — the fix must not silently certify a wrong witness
// ═══════════════════════════════════════════════════════════════════════════

/// A witness for a FALSE property (`0 < 0`) is rejected — the dependent field's
/// type is specialized to the constructed value and the proof must discharge
/// it. (Guards against a "field type dropped / not checked" silent accept.)
#[test]
fn b11_false_subtype_witness_rejected() {
    let src = "structure Pos where\n  val : Nat\n  property : 0 < val\n\n\
               def zero : Pos := ⟨0, by decide⟩";
    let err = expect_fail(src);
    assert!(
        err.contains("decide") || err.contains("false") || err.to_lowercase().contains("mismatch"),
        "a `0 < 0` witness must be loudly rejected, got: {err}"
    );
}

/// A Prop class whose field asserts `n = 0`, given a WRONG proof `rfl : 3 = 3`
/// where `3 = 0` is required, is rejected with a literal mismatch (3 vs 0) —
/// the field type is specialized to the instance's value parameter.
#[test]
fn b11_wrong_prop_class_proof_rejected() {
    let src = "class Holds (n : Nat) : Prop where\n  proof : n = 0\n\n\
               def bad : Holds 3 := ⟨rfl⟩";
    let err = expect_fail(src);
    assert!(
        err.contains("mismatch") || err.contains("Mismatch"),
        "a `3 = 0` witness must fail with a type mismatch, got: {err}"
    );
}

/// Constructing the dependent structure with too few fields still reports the
/// missing field loudly (the second, dependent field is a real ctor argument,
/// not silently defaulted).
#[test]
fn b11_missing_dependent_field_is_loud() {
    let src = format!("{CERTIFIED}def s : Certified := ⟨3⟩");
    let err = expect_fail(&src);
    assert!(
        !err.is_empty(),
        "an under-applied dependent constructor must be rejected"
    );
}
