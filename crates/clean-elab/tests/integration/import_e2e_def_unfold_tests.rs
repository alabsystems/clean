// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end probe: an IMPORTED DEFINITION delta-unfolds and reduces correctly
//! when *used* by a freshly-elaborated declaration.
//!
//! The B43/B44 audits showed that native clean-elab paths register clean-side
//! metadata (recursor `arg_order`, `structure_fields`, …) and lower to kernel
//! primitives, whereas an *imported* `.olean` declaration is a plain Lean
//! function/constant. This probe checks the analogous concern for a plain
//! **definitional** constant: when `.olean` import registers a `def`, does it
//! import the def's *body* (so the kernel can delta-unfold it), or only the
//! type (leaving the constant opaque/stuck)?
//!
//! It exercises two checked-in Lean 4 v4.13.0 fixtures:
//!
//! * `Minimal.olean` — `def identity (α : Type) (x : α) : α := x`, a plain
//!   definitional constant whose body is the bound variable `x`. Delta-unfolding
//!   it must expose a `λ α x => x`, after which beta reduction selects the second
//!   argument.
//! * `Inductive.olean` — `def myNot : MyBool → MyBool | .myTrue => .myFalse
//!   | .myFalse => .myTrue`, a definitional constant whose body is a compiled
//!   match (recursor application).
//!
//! For each, the probe (a) asserts the importer registered the constant *with a
//! body* (`ConstantKind::Definition` + `value.is_some()`), (b) reduces a direct
//! application of the imported def via the kernel `whnf` and asserts the result,
//! and (c) elaborates a **new** clean-elab definition that *uses* the imported
//! def and asserts that the new def's saturated application reduces correctly —
//! i.e. the imported def delta-unfolds through a freshly-elaborated caller.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Name, TypeChecker};
use clean_olean::load_olean_file;
use clean_parser::parse_file;
use std::path::PathBuf;

/// Absolute path to the checked-in `Minimal` `.olean` fixture
/// (`def identity (α : Type) (x : α) : α := x`).
fn minimal_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Minimal.olean")
}

/// Absolute path to the checked-in `MyBool` inductive `.olean` fixture
/// (carries the Lean-compiled `def myNot`).
fn inductive_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Inductive.olean")
}

/// Load a fixture `.olean` into a fresh environment, asserting it added constants.
fn load_fixture(path: &PathBuf) -> Environment {
    let mut env = Environment::default();
    let summary = load_olean_file(&mut env, path)
        .unwrap_or_else(|e| panic!("loading {} should succeed: {e}", path.display()));
    assert!(
        summary.added_constants > 0,
        "fixture {} should add constants",
        path.display()
    );
    env
}

/// Elaborate and register a sequence of declarations from `source`, threading a
/// shared `FileContext`. `elaborate_decl_and_register` runs the full kernel
/// type check for each definition.
fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

/// Reduce `expr` to weak-head normal form and, if the head is a `Const`, return
/// its name.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

// =============================================================================
// Test 1: the importer records the imported `def` *with a body*, not opaquely.
// This is the precondition for delta-unfolding: a kernel whnf can only unfold a
// `Const` whose `ConstantInfo.value` is `Some`.
// =============================================================================

#[test]
fn test_imported_def_is_registered_with_unfoldable_body() {
    use clean_kernel::env::ConstantKind;

    let env = load_fixture(&minimal_fixture_path());
    let identity = env
        .get_const(&Name::from_string("identity"))
        .expect("identity should be imported from Minimal.olean");
    assert_eq!(
        identity.kind,
        ConstantKind::Definition,
        "identity is a plain definition, not an axiom/opaque"
    );
    assert!(
        identity.value.is_some(),
        "the importer must bring in identity's BODY (value), otherwise the kernel \
         cannot delta-unfold it and `identity α x` would stay stuck"
    );

    let bool_env = load_fixture(&inductive_fixture_path());
    let my_not = bool_env
        .get_const(&Name::from_string("myNot"))
        .expect("myNot should be imported from Inductive.olean");
    assert_eq!(my_not.kind, ConstantKind::Definition);
    assert!(
        my_not.value.is_some(),
        "myNot's body must be imported so it can delta-unfold"
    );
}

// =============================================================================
// Test 2: a direct application of the imported plain `def identity` delta-unfolds
// and beta-reduces to its argument under the kernel `whnf`.
// =============================================================================

#[test]
fn test_imported_identity_def_unfolds_and_reduces() {
    let env = load_fixture(&minimal_fixture_path());

    // `identity MyBoolStandIn` — we don't have an inductive here, so pick a value
    // whose whnf head is observable: `identity Type Nat` should reduce to `Nat`
    // (the second explicit argument), proving delta+beta fired through the
    // imported body `x`.
    let nat = const_("Nat");
    let app = Expr::app(Expr::app(const_("identity"), const_("Type")), nat);
    assert_eq!(
        whnf_head_const(&env, &app).as_deref(),
        Some("Nat"),
        "imported `identity Type Nat` must delta-unfold and beta-reduce to its \
         second argument (Nat); a stuck/opaque imported def would leave the head \
         as `identity`"
    );
}

// =============================================================================
// Test 3: the core scenario — a NEWLY elaborated clean-elab def that *uses* an
// imported def must reduce correctly. `quad`/`twice` style: build a new def that
// applies the imported `identity` twice, then assert the saturated call reduces
// through the imported body. This is the imported-def analogue of the B43/B44
// "elaborate a new decl over an imported decl" chain.
// =============================================================================

#[test]
fn test_new_def_using_imported_identity_reduces_through_imported_body() {
    let mut env = load_fixture(&minimal_fixture_path());

    // `def idid (α : Type) (x : α) : α := identity α (identity α x)`
    // elaborates against the imported `identity` and kernel-type-checks.
    elaborate_decls_into(
        &mut env,
        "def idid (α : Type) (x : α) : α := identity α (identity α x)",
    );

    // The new def's body must reference the imported constant (the chain is real,
    // not short-circuited by the elaborator).
    let info = env
        .get_const(&Name::from_string("idid"))
        .expect("idid should be registered after elaboration");
    let body = info
        .value
        .as_ref()
        .expect("idid is a definition with a body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("identity")),
        "idid's body must call the imported `identity`, got: {:?}",
        body.collect_constants()
    );

    // `idid Type Nat` must reduce to `Nat`: unfold `idid` -> beta -> unfold the
    // two imported `identity` calls -> beta -> `Nat`. A stuck imported `identity`
    // body would leave the head non-`Nat`.
    let app = Expr::app(Expr::app(const_("idid"), const_("Type")), const_("Nat"));
    assert_eq!(
        whnf_head_const(&env, &app).as_deref(),
        Some("Nat"),
        "idid Type Nat must reduce to Nat through the imported identity body"
    );
}

// =============================================================================
// Test 4: an imported def whose body is a *compiled match* (recursor) reduces
// correctly when used through a freshly-elaborated caller. `myNot` is the
// imported def; a new `applyNot p := myNot p` must reduce on each constructor.
// =============================================================================

#[test]
fn test_new_def_using_imported_match_def_reduces_correctly() {
    let mut env = load_fixture(&inductive_fixture_path());

    // Direct application of the imported `myNot` (body = compiled match).
    let direct_true = Expr::app(const_("myNot"), const_("MyBool.myTrue"));
    assert_eq!(
        whnf_head_const(&env, &direct_true).as_deref(),
        Some("MyBool.myFalse"),
        "imported myNot myTrue must reduce to myFalse (delta-unfold + iota)"
    );

    // A NEW clean-elab def that wraps the imported `myNot`.
    elaborate_decls_into(&mut env, "def applyNot (b : MyBool) : MyBool := myNot b");
    let info = env
        .get_const(&Name::from_string("applyNot"))
        .expect("applyNot should be registered after elaboration");
    let body = info
        .value
        .as_ref()
        .expect("applyNot is a definition with a body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("myNot")),
        "applyNot's body must call the imported myNot, got: {:?}",
        body.collect_constants()
    );

    // `applyNot myTrue` -> `myNot myTrue` -> delta-unfold myNot -> iota -> myFalse.
    let apply_true = Expr::app(const_("applyNot"), const_("MyBool.myTrue"));
    assert_eq!(
        whnf_head_const(&env, &apply_true).as_deref(),
        Some("MyBool.myFalse"),
        "applyNot myTrue must reduce to myFalse through the imported myNot body"
    );
    let apply_false = Expr::app(const_("applyNot"), const_("MyBool.myFalse"));
    assert_eq!(
        whnf_head_const(&env, &apply_false).as_deref(),
        Some("MyBool.myTrue"),
        "applyNot myFalse must reduce to myTrue through the imported myNot body"
    );
}
