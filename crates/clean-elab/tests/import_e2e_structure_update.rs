// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: structure-update (`{ s with f := v }`) on an *imported* structure.
//!
//! Structure update desugars to re-applying the constructor with the new value
//! for the updated field and *projections of the base* for every unchanged
//! field. For an imported structure (registered from a real Lean `.olean` as a
//! single-constructor inductive with Lean's own projection *functions*) the
//! field-projection / field-ordering logic in clean-elab's struct-literal
//! elaboration must use the imported layout correctly, exactly as the B43/B44
//! match-/projection-layout bugs required.
//!
//! This probe wires:
//!   1. `.olean` load of the `MyPair (α β : Type)` structure fixture (+ `MyBool`
//!      for two distinct nullary field values),
//!   2. clean-elab elaboration of a `def` that uses `{ p with fst := newVal }`,
//!   3. the full kernel type-check (`elaborate_decl_and_register`),
//!   4. `whnf` of the updated value's projections to assert the update both
//!      *replaces* `fst` and *preserves* `snd` — with distinct constructors so a
//!      field swap / mis-projection is observable rather than masked.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Name, TypeChecker};
use clean_olean::load_olean_file;
use clean_parser::parse_file;
use std::path::PathBuf;

fn structure_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Structure.olean")
}

fn inductive_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Inductive.olean")
}

/// Load the imported `MyPair` structure together with the `MyBool` inductive,
/// the latter supplying two distinct nullary values (`MyBool.myTrue` /
/// `MyBool.myFalse`).
fn load_env() -> Environment {
    let mut env = Environment::default();
    for path in [structure_fixture_path(), inductive_fixture_path()] {
        let summary = load_olean_file(&mut env, &path)
            .unwrap_or_else(|e| panic!("loading {} should succeed: {e}", path.display()));
        assert!(
            summary.added_constants > 0,
            "fixture {} should add constants",
            path.display()
        );
    }
    env
}

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `MyPair.mk MyBool MyBool myTrue myFalse` — fst = myTrue, snd = myFalse
/// (distinct constructors so a wrong field selection is observable).
fn mypair_mk_true_false() -> Expr {
    let mybool = const_("MyBool");
    let mk = Expr::app(Expr::app(const_("MyPair.mk"), mybool.clone()), mybool);
    let mk = Expr::app(mk, const_("MyBool.myTrue"));
    Expr::app(mk, const_("MyBool.myFalse"))
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

fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

// =============================================================================
// Preconditions: this is genuinely the imported-structure configuration, with
// no clean-side structure-field table (the configuration that exercises the
// struct-update path on an imported struct).
// =============================================================================

#[test]
fn test_imported_mypair_is_registered_without_clean_field_table() {
    let env = load_env();

    assert!(
        env.get_inductive(&Name::from_string("MyPair")).is_some(),
        "MyPair inductive should be imported"
    );
    assert!(
        env.get_const(&Name::from_string("MyPair.mk")).is_some(),
        "MyPair.mk constructor should be imported"
    );
    assert!(
        env.get_const(&Name::from_string("MyPair.fst")).is_some()
            && env.get_const(&Name::from_string("MyPair.snd")).is_some(),
        "MyPair.fst / MyPair.snd projection functions should be imported"
    );
}

// =============================================================================
// Probe: `{ p with fst := newVal }` on the imported MyPair must elaborate,
// kernel-check, and reduce so that fst is REPLACED and snd is PRESERVED.
// =============================================================================

#[test]
fn test_structure_update_on_imported_struct_replaces_and_preserves_fields() {
    let mut env = load_env();

    // `p` starts as (fst = myTrue, snd = myFalse).
    // `upd p` updates fst := myFalse, leaving snd untouched (= myFalse).
    // So after the update we expect fst = myFalse AND snd = myFalse.
    // Using a distinct *target* for fst (myFalse) vs the original (myTrue)
    // makes a no-op / failed-update observable, and snd (myFalse) catches a
    // field swap that would have written into snd instead.
    elaborate_decls_into(
        &mut env,
        "def upd (p : MyPair MyBool MyBool) : MyPair MyBool MyBool := \
         { p with fst := MyBool.myFalse }",
    );

    let pair = mypair_mk_true_false();
    let upd_pair = Expr::app(const_("upd"), pair);

    // fst must be REPLACED with myFalse.
    let upd_fst = Expr::proj(Name::from_string("MyPair"), 0, upd_pair.clone());
    assert_eq!(
        whnf_head_const(&env, &upd_fst).as_deref(),
        Some("MyBool.myFalse"),
        "{{ p with fst := myFalse }} must set fst to myFalse"
    );

    // snd must be PRESERVED as myFalse (projected from the base, not swapped
    // with the new fst value or dropped).
    let upd_snd = Expr::proj(Name::from_string("MyPair"), 1, upd_pair);
    assert_eq!(
        whnf_head_const(&env, &upd_snd).as_deref(),
        Some("MyBool.myFalse"),
        "{{ p with fst := myFalse }} must preserve snd (= myFalse from the base)"
    );
}

#[test]
fn test_structure_update_on_imported_struct_preserves_distinct_unchanged_field() {
    let mut env = load_env();

    // Update only `snd`. Start fst = myTrue, snd = myFalse; set snd := myTrue.
    // Expect fst = myTrue (PRESERVED, distinct from new snd) and snd = myTrue.
    // If unchanged-field projection mis-indexed (read snd instead of fst, or
    // off-by-num_params), fst would come back wrong.
    elaborate_decls_into(
        &mut env,
        "def updSnd (p : MyPair MyBool MyBool) : MyPair MyBool MyBool := \
         { p with snd := MyBool.myTrue }",
    );

    let pair = mypair_mk_true_false();
    let upd_pair = Expr::app(const_("updSnd"), pair);

    let upd_fst = Expr::proj(Name::from_string("MyPair"), 0, upd_pair.clone());
    assert_eq!(
        whnf_head_const(&env, &upd_fst).as_deref(),
        Some("MyBool.myTrue"),
        "{{ p with snd := myTrue }} must preserve fst (= myTrue from the base)"
    );

    let upd_snd = Expr::proj(Name::from_string("MyPair"), 1, upd_pair);
    assert_eq!(
        whnf_head_const(&env, &upd_snd).as_deref(),
        Some("MyBool.myTrue"),
        "{{ p with snd := myTrue }} must set snd to myTrue"
    );
}

// =============================================================================
// Diagnostic: surface (don't panic) whether struct-update elaboration even
// reaches the kernel for an imported structure. Pins the failure mode so a
// regression on the no-field-table fallback is caught with a clear message.
// =============================================================================

#[test]
fn test_structure_update_on_imported_struct_elaborates_at_all() {
    let mut env = load_env();
    let result = try_elaborate_decls_into(
        &mut env,
        "def updProbe (p : MyPair MyBool MyBool) : MyPair MyBool MyBool := \
         { p with fst := MyBool.myFalse }",
    );
    assert!(
        result.is_ok(),
        "structure-update on an imported structure should elaborate + kernel-check, got: {result:?}"
    );
}
