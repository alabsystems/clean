// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end import -> elaborate -> kernel-verify validation.
//!
//! The individual pieces of the real-Mathlib import path exist but are never
//! exercised together in one test:
//!
//! 1. `.olean` loading (`clean_olean::load_olean_file`) registers an imported
//!    inductive, its constructors and its eliminators into an `Environment`.
//! 2. A *new* declaration that pattern-matches on the imported inductive is
//!    parsed and elaborated against that environment.
//! 3. The elaborated definition is kernel-type-checked (via
//!    `elaborate_decl_and_register`, which always runs the full kernel
//!    `add_decl` check for a definition).
//!
//! These tests wire that chain together against the checked-in `MyBool` fixture
//! (`tests/fixtures/olean/v4.13.0/custom/Inductive.olean`, compiled by Lean 4
//! v4.13.0). The fixture declares
//!
//! ```lean
//! inductive MyBool | myTrue | myFalse
//! def myNot : MyBool -> MyBool | .myTrue => .myFalse | .myFalse => .myTrue
//! ```
//!
//! and therefore imports `MyBool`, `MyBool.myTrue`, `MyBool.myFalse`,
//! `MyBool.rec`, `MyBool.casesOn`, and the Lean-compiled `myNot`.
//!
//! What this surfaced (a real correctness bug, now fixed — see
//! `test_match_on_imported_inductive_reduces_to_correct_constructor`): match
//! elaboration on a *natively-declared* inductive reduces correctly, and the
//! *Lean-compiled* `myNot` imported from the fixture reduces correctly, but a
//! *clean-elab-elaborated* match on the *imported* `MyBool` used to produce a
//! definition that type-checked yet reduced to the wrong constructor — because
//! the match lowering emitted the `casesOn` major premise last (the native
//! `MajorAfterMinors` layout) instead of right after the motive (Lean's
//! imported `MajorAfterMotive` `casesOn` layout). It now reduces correctly.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Name, TypeChecker};
use clean_olean::load_olean_file;
use clean_parser::parse_file;
use std::path::PathBuf;

/// Absolute path to the checked-in `MyBool` inductive `.olean` fixture.
fn inductive_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Inductive.olean")
}

/// Absolute path to the checked-in `MyPair` structure `.olean` fixture.
///
/// Compiled by Lean 4 v4.13.0 from:
///
/// ```lean
/// structure MyPair (α β : Type) where
///   fst : α
///   snd : β
/// def swap (p : MyPair α β) : MyPair β α := ⟨p.snd, p.fst⟩
/// ```
fn structure_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Structure.olean")
}

/// Load the `MyBool` fixture into a fresh environment.
fn load_mybool_env() -> Environment {
    let path = inductive_fixture_path();
    let mut env = Environment::default();
    let summary = load_olean_file(&mut env, &path)
        .unwrap_or_else(|e| panic!("loading {} should succeed: {e}", path.display()));
    assert!(
        summary.added_constants > 0,
        "fixture should add constants to the environment"
    );
    env
}

/// Load the `MyPair` structure fixture *and* the `MyBool` inductive fixture into
/// one environment. `MyBool` supplies two distinct nullary values
/// (`MyBool.myTrue` / `MyBool.myFalse`), letting projection tests instantiate
/// `MyPair MyBool MyBool` with genuinely different `fst`/`snd` values so a wrong
/// field index (an `fst`/`snd` swap) is observable in the reduced result.
fn load_mypair_over_mybool_env() -> Environment {
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

/// `MyPair.mk MyBool MyBool myTrue myFalse` — a `MyPair` value with `fst` and
/// `snd` set to *distinct* constructors so projection field selection is
/// observable.
fn mypair_mk_true_false() -> Expr {
    let mybool = const_("MyBool");
    let mk = Expr::app(Expr::app(const_("MyPair.mk"), mybool.clone()), mybool);
    let mk = Expr::app(mk, const_("MyBool.myTrue"));
    Expr::app(mk, const_("MyBool.myFalse"))
}

/// Elaborate and register a sequence of declarations from `source`, threading a
/// shared `FileContext`. Returns the populated environment.
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
/// its name. Used to observe which constructor a `casesOn` redex selects.
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
// Test 1: the load -> ctor/recursor resolution -> match-elaborate ->
// kernel-check chain succeeds end to end.
// =============================================================================

#[test]
fn test_import_then_match_def_elaborates_and_kernel_checks() {
    let mut env = load_mybool_env();

    // The importer must register the inductive, both constructors, and the
    // eliminators that match elaboration depends on.
    let mybool = Name::from_string("MyBool");
    let my_true = Name::from_string("MyBool.myTrue");
    let my_false = Name::from_string("MyBool.myFalse");

    let true_ctor = env
        .get_constructor(&my_true)
        .expect("MyBool.myTrue should resolve as an imported constructor");
    assert_eq!(
        true_ctor.inductive_name, mybool,
        "myTrue's parent inductive should be MyBool"
    );
    assert_eq!(
        true_ctor.num_fields, 0,
        "MyBool.myTrue is a nullary constructor"
    );

    let false_ctor = env
        .get_constructor(&my_false)
        .expect("MyBool.myFalse should resolve as an imported constructor");
    assert_eq!(false_ctor.inductive_name, mybool);
    assert_ne!(
        true_ctor.constructor_idx, false_ctor.constructor_idx,
        "the two constructors must have distinct indices"
    );

    let rec = env
        .get_recursor(&Name::from_string("MyBool.rec"))
        .expect("MyBool.rec should be imported alongside the inductive");
    assert_eq!(rec.inductive_name, mybool);
    assert_eq!(
        rec.num_minors, 2,
        "a two-constructor inductive has two minor premises"
    );
    assert!(
        env.get_const(&Name::from_string("MyBool.casesOn"))
            .is_some(),
        "MyBool.casesOn (the case eliminator match elaboration emits) must be imported"
    );

    // Now elaborate a *new* definition that pattern matches on the imported
    // inductive. `elaborate_decl_and_register` runs the full kernel type check
    // for the resulting definition; reaching here without panicking means the
    // body kernel-checked against the imported eliminator.
    elaborate_decls_into(
        &mut env,
        "def myNot2 : MyBool → MyBool\n  | MyBool.myTrue => MyBool.myFalse\n  | MyBool.myFalse => MyBool.myTrue",
    );

    let info = env
        .get_const(&Name::from_string("myNot2"))
        .expect("myNot2 should be registered after elaboration");
    let body = info
        .value
        .as_ref()
        .expect("myNot2 is a definition with a body");
    let referenced = body.collect_constants();

    // The elaborated body must compile through the *imported* eliminator and
    // reference the *imported* constructors — proving the chain is genuinely
    // wired rather than going through some unrelated path.
    assert!(
        referenced.contains(&Name::from_string("MyBool.casesOn")),
        "myNot2's body should be compiled against the imported MyBool.casesOn, got: {referenced:?}"
    );
    assert!(
        referenced.contains(&Name::from_string("MyBool.myTrue"))
            && referenced.contains(&Name::from_string("MyBool.myFalse")),
        "myNot2's body should reference both imported constructors, got: {referenced:?}"
    );
}

// =============================================================================
// Test 2: recursor reduction over the imported inductive works for the
// Lean-compiled definition shipped in the fixture.
// =============================================================================

#[test]
fn test_imported_lean_compiled_def_reduces_via_imported_recursor() {
    let env = load_mybool_env();

    // `myNot` was compiled by Lean 4 and imported. Reducing `myNot myTrue`
    // exercises the kernel's recursor reduction over the imported inductive.
    let my_not_true = Expr::app(const_("myNot"), const_("MyBool.myTrue"));
    assert_eq!(
        whnf_head_const(&env, &my_not_true).as_deref(),
        Some("MyBool.myFalse"),
        "imported myNot myTrue must reduce to myFalse"
    );

    let my_not_false = Expr::app(const_("myNot"), const_("MyBool.myFalse"));
    assert_eq!(
        whnf_head_const(&env, &my_not_false).as_deref(),
        Some("MyBool.myTrue"),
        "imported myNot myFalse must reduce to myTrue"
    );
}

// =============================================================================
// Test 3: control — match elaboration on a *natively* declared inductive
// reduces correctly. This isolates the gap in Test 4 to the import path.
// =============================================================================

#[test]
fn test_native_inductive_match_def_reduces_correctly() {
    let mut env = Environment::new();
    elaborate_decls_into(
        &mut env,
        "inductive Nb where\n  | nt : Nb\n  | nf : Nb\n\ndef nNot : Nb → Nb\n  | Nb.nt => Nb.nf\n  | Nb.nf => Nb.nt",
    );

    let nnot_nt = Expr::app(const_("nNot"), const_("Nb.nt"));
    assert_eq!(
        whnf_head_const(&env, &nnot_nt).as_deref(),
        Some("Nb.nf"),
        "nNot nt on a natively-declared inductive must reduce to nf"
    );
    let nnot_nf = Expr::app(const_("nNot"), const_("Nb.nf"));
    assert_eq!(
        whnf_head_const(&env, &nnot_nf).as_deref(),
        Some("Nb.nt"),
        "nNot nf on a natively-declared inductive must reduce to nt"
    );
}

// =============================================================================
// Test 4: documents the real gap surfaced by wiring the chain together.
// =============================================================================

/// FIXED (import -> match-elaborate -> reduce):
///
/// A clean-elab-elaborated `match` on an *imported* inductive type-checks **and
/// now reduces to the correct constructor**. `myNot2` is elaborated against the
/// imported `MyBool.casesOn`, whose Lean-compiled type is
///
/// ```text
/// (motive : MyBool → Sort u) → (t : MyBool) → motive .myTrue
///                                            → motive .myFalse → motive t
/// ```
///
/// i.e. the **major premise comes second** (right after the motive), with the
/// minor premises last — Lean's `MajorAfterMotive` `casesOn`/`recOn` layout.
/// Previously clean-elab emitted the major premise *last* (the native
/// `MyBool.rec` `MajorAfterMinors` layout), so `whnf` selected the wrong branch:
/// `myNot2 myTrue` reduced to `myTrue` instead of `myFalse`. The result still
/// type-checked because every argument here has type `MyBool`, masking the bug.
///
/// The fix (in `clean-elab` match lowering, `infer/elab_match/mod.rs`) detects
/// the eliminator's argument order: a *native* eliminator is a registered
/// recursor with a declared `arg_order`, while an *imported* `.casesOn` is a
/// plain definitional constant that follows Lean's `MajorAfterMotive`
/// convention. For the imported layout the scrutinee (and any indices) are now
/// emitted **before** the minor premises, so the application matches the
/// imported eliminator's binder layout and `whnf` selects the right branch.
///
/// Test 2 (Lean-compiled `myNot`) and Test 3 (native inductive) both reduce
/// correctly too, so the whole import -> elaborate -> reduce chain is sound.
#[test]
fn test_match_on_imported_inductive_reduces_to_correct_constructor() {
    let mut env = load_mybool_env();
    elaborate_decls_into(
        &mut env,
        "def myNot2 : MyBool → MyBool\n  | MyBool.myTrue => MyBool.myFalse\n  | MyBool.myFalse => MyBool.myTrue",
    );

    // Sanity: the Lean-compiled `myNot` in the *same* environment reduces
    // correctly, so the recursor-reduction machinery itself is sound here.
    let my_not_true = Expr::app(const_("myNot"), const_("MyBool.myTrue"));
    assert_eq!(
        whnf_head_const(&env, &my_not_true).as_deref(),
        Some("MyBool.myFalse"),
        "control: imported Lean-compiled myNot reduces correctly"
    );

    // The clean-elab-elaborated `myNot2` now reduces to the CORRECT branch under
    // Lean semantics: not(true) = false, not(false) = true.
    let my_not2_true = Expr::app(const_("myNot2"), const_("MyBool.myTrue"));
    assert_eq!(
        whnf_head_const(&env, &my_not2_true).as_deref(),
        Some("MyBool.myFalse"),
        "clean-elab match on imported MyBool must reduce myNot2 myTrue to myFalse \
         (the import-match casesOn argument-order bug is fixed)"
    );

    let my_not2_false = Expr::app(const_("myNot2"), const_("MyBool.myFalse"));
    assert_eq!(
        whnf_head_const(&env, &my_not2_false).as_deref(),
        Some("MyBool.myTrue"),
        "clean-elab match on imported MyBool must reduce myNot2 myFalse to myTrue"
    );
}

// =============================================================================
// Test 5: the analogous path for STRUCTURE PROJECTIONS. A clean-elab-elaborated
// `p.fst` / `p.snd` on an *imported* structure must reduce to the genuinely
// correct field value — not merely type-check. (B43-analogue audit.)
// =============================================================================

/// FIXED (import -> projection-elaborate -> reduce):
///
/// The `MyPair` structure imported from the Lean-compiled `Structure.olean`
/// fixture is registered as a two-parameter, single-constructor inductive
/// (`MyPair.mk : (α β : Type) → α → β → MyPair α β`) together with Lean's own
/// projection *functions* `MyPair.fst` / `MyPair.snd`, whose bodies are the
/// kernel projections `Proj("MyPair", 0, ·)` and `Proj("MyPair", 1, ·)`.
///
/// A real Lean `.olean` carries no clean-side `structure_fields` table, so
/// `Environment::get_structure_field_names("MyPair")` is `None`. clean-elab's
/// projection elaboration (`infer/elab_proj.rs::resolve_projection_target`)
/// therefore declines the kernel-`Proj` path and falls back to **dot notation**,
/// resolving `p.fst` to the imported function `MyPair.fst` applied to `p`.
///
/// The bug this surfaced: dot-notation lowering used to apply the receiver as
/// the *first explicit argument* (`MyPair.fst p`), which placed `p` where the
/// type parameter `α : Type` was expected. For an imported structure whose
/// projection binds explicit type parameters *before* the "self" argument, that
/// made `p.fst` fail to kernel-type-check entirely (`expected Type, got
/// MyPair MyBool MyBool`) — the imported-structure analogue of the B43 match
/// layout bug. (A *native* clean-elab structure registers `structure_fields`
/// and lowers `p.fst` to a kernel `Proj`, so it was unaffected; only the
/// import path hit this.)
///
/// The fix (`infer/elab_proj.rs::apply_dot_receiver`) follows Lean's rule:
/// insert the receiver at the first explicit parameter whose type head is the
/// namespace type `T`, solving the preceding explicit type parameters by
/// unifying the receiver's actual type into that slot. `p.fst` now elaborates
/// to `MyPair.fst MyBool MyBool p` (with `α`, `β` solved to `MyBool`), which
/// reduces through Lean's own `Proj("MyPair", 0/1, ·)` and the kernel's
/// projection reduction (`tc/whnf_proj.rs`, selecting argument `num_params +
/// idx`) to the *actual* `fst`/`snd` field values.
///
/// This test instantiates `MyPair MyBool MyBool` with `fst := MyBool.myTrue`,
/// `snd := MyBool.myFalse` (distinct constructors), so a wrong field index — an
/// `fst`/`snd` swap, or off-by-one against `num_params` — would surface as the
/// wrong constructor here rather than passing silently the way the B43 match bug
/// did. Both projections select the right field.
#[test]
fn test_projection_on_imported_struct_reduces_to_correct_field() {
    let mut env = load_mypair_over_mybool_env();

    // Precondition: a real Lean `.olean` registers the structure and its Lean
    // projection functions, but no clean-side structure-field table — this is the
    // exact configuration that routes `p.fst` through the dot-notation fallback.
    assert!(
        env.get_inductive(&Name::from_string("MyPair")).is_some(),
        "MyPair inductive should be imported"
    );
    assert!(
        env.get_const(&Name::from_string("MyPair.fst")).is_some()
            && env.get_const(&Name::from_string("MyPair.snd")).is_some(),
        "MyPair.fst / MyPair.snd projection functions should be imported"
    );

    // Elaborate clean-elab definitions that project the imported structure.
    // `elaborate_decl_and_register` runs the full kernel type check.
    elaborate_decls_into(
        &mut env,
        "def getFst (p : MyPair MyBool MyBool) : MyBool := p.fst\n\
         def getSnd (p : MyPair MyBool MyBool) : MyBool := p.snd",
    );

    let pair = mypair_mk_true_false();

    // getFst must select the FIRST field (myTrue), getSnd the SECOND (myFalse).
    // A field-index swap or off-by-`num_params` error would invert these.
    let get_fst = Expr::app(const_("getFst"), pair.clone());
    assert_eq!(
        whnf_head_const(&env, &get_fst).as_deref(),
        Some("MyBool.myTrue"),
        "getFst (MyPair.mk myTrue myFalse) must reduce to myTrue (the fst field)"
    );

    let get_snd = Expr::app(const_("getSnd"), pair);
    assert_eq!(
        whnf_head_const(&env, &get_snd).as_deref(),
        Some("MyBool.myFalse"),
        "getSnd (MyPair.mk myTrue myFalse) must reduce to myFalse (the snd field)"
    );
}

// =============================================================================
// Test 6: control — the kernel `Proj` node and the imported Lean projection
// *functions* agree on field order for the imported structure. This isolates
// any future regression to the elaborator (which picks one of these forms)
// rather than the kernel reduction or the importer's field layout.
// =============================================================================

#[test]
fn test_imported_struct_kernel_proj_and_proj_fn_agree_on_field_order() {
    let env = load_mypair_over_mybool_env();
    let pair = mypair_mk_true_false();

    // Direct kernel projections: idx 0 = fst, idx 1 = snd.
    let proj0 = Expr::proj(Name::from_string("MyPair"), 0, pair.clone());
    assert_eq!(
        whnf_head_const(&env, &proj0).as_deref(),
        Some("MyBool.myTrue"),
        "kernel Proj(MyPair, 0, mk myTrue myFalse) must reduce to the fst field (myTrue)"
    );
    let proj1 = Expr::proj(Name::from_string("MyPair"), 1, pair.clone());
    assert_eq!(
        whnf_head_const(&env, &proj1).as_deref(),
        Some("MyBool.myFalse"),
        "kernel Proj(MyPair, 1, mk myTrue myFalse) must reduce to the snd field (myFalse)"
    );

    // Imported Lean projection functions applied to the same value must agree.
    let mybool = const_("MyBool");
    let fst_fn = Expr::app(
        Expr::app(
            Expr::app(const_("MyPair.fst"), mybool.clone()),
            mybool.clone(),
        ),
        pair.clone(),
    );
    assert_eq!(
        whnf_head_const(&env, &fst_fn).as_deref(),
        Some("MyBool.myTrue"),
        "imported MyPair.fst must reduce to the fst field (myTrue)"
    );
    let snd_fn = Expr::app(
        Expr::app(Expr::app(const_("MyPair.snd"), mybool.clone()), mybool),
        pair,
    );
    assert_eq!(
        whnf_head_const(&env, &snd_fn).as_deref(),
        Some("MyBool.myFalse"),
        "imported MyPair.snd must reduce to the snd field (myFalse)"
    );
}
