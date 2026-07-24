// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: projections on an *imported* `Subtype` / `Sigma` value.
//!
//! This is the stdlib-shape analogue of the B44 `MyPair` dot-notation fix
//! (`infer/elab_proj.rs::apply_dot_receiver`). The B44 test
//! (`integration/import_elab_e2e_tests.rs`, test 5/6) covers an imported
//! structure (`MyPair`) whose projection functions bind their type parameters
//! *explicitly* before the "self" argument. `Subtype` and `Sigma` are different
//! in two ways that exercise additional code paths in dot-notation lowering:
//!
//! 1. Their type parameters are **implicit** (`{α : Sort u}`, `{p : α → Prop}` /
//!    `{β : α → Type v}`), so the receiver *is* the first explicit argument, but
//!    the leading implicit metavariables must still be solved by unifying the
//!    receiver's actual type into the self slot.
//! 2. Their second projection has a **dependent / `Prop`** result type:
//!    `Subtype.property : (self : Subtype p) → p self.val` and
//!    `Sigma.snd : (self : Sigma β) → β self.fst`.
//!
//! ## Synthesize-as-import
//!
//! A real Lean `.olean` registers `Subtype` / `Sigma` as a single-constructor
//! inductive together with Lean's own projection *functions* (`Subtype.val`,
//! `Subtype.property`, `Sigma.fst`, `Sigma.snd`) whose bodies are kernel
//! `Proj` nodes — but it carries **no** clean-side `structure_fields` table
//! (that table is only produced by clean's own structure elaborator / exporter,
//! per the B44 `MyPair` analysis). With no field table,
//! `Environment::get_structure_field_names` is `None`, so clean-elab's
//! projection elaboration declines the kernel-`Proj` path and falls back to
//! dot notation (`infer/elab_proj.rs`), resolving `s.val` to the imported
//! function `Subtype.val` applied to `s` via `apply_dot_receiver`.
//!
//! To reproduce that environment *faithfully and deterministically* (no shipped
//! `Subtype.olean` fixture exists), we build the canonical kernel declarations
//! with the kernel's own `init_subtype` / `init_sigma`, then copy the inductive
//! and its projection functions verbatim into a fresh "imported" environment
//! **without** calling `register_structure_fields`. The declarations are
//! therefore bit-identical to the native ones; the *only* difference is the
//! missing field table — exactly the import condition. We assert that
//! precondition explicitly so the test stays honest if the importer ever starts
//! shipping a field table.
//!
//! The native path (which *does* register `structure_fields`, lowering `s.val`
//! to a kernel `Proj`) is exercised as a control so any regression is isolated
//! to the elaborator's dot-notation lowering rather than kernel reduction.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{
    Constructor, Declaration, Expr, ExprKind, InductiveDecl, InductiveType, Name, TypeChecker,
};
use clean_parser::parse_file;

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Reduce `expr` to WHNF and return the head constant's name, if any.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Whether `expr` is definitionally equal to `reference`. Used where the result
/// normalizes to a kernel `Nat` literal (e.g. `Nat.succ Nat.zero` ⇝ `1`) rather
/// than a `Const`-headed term, so a head-name comparison would not suffice.
fn def_eq(env: &Environment, expr: &Expr, reference: &Expr) -> bool {
    let tc = TypeChecker::new(env);
    tc.is_def_eq(expr, reference)
}

/// Elaborate and register a sequence of declarations from `source`, threading a
/// shared `FileContext`. `elaborate_decl_and_register` runs the full kernel type
/// check for each definition, so reaching the end means every body kernel-checked.
fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

/// Copy a single-constructor inductive and one or more associated projection
/// *functions* from `src` into `dst`, mirroring what loading a real Lean
/// `.olean` does — but deliberately **without** registering a `structure_fields`
/// table, so projection elaboration on the result routes through the
/// dot-notation fallback exactly as it does for a real imported structure.
fn copy_as_imported(src: &Environment, dst: &mut Environment, ind_name: &str, proj_fns: &[&str]) {
    let ind = src
        .get_inductive(&Name::from_string(ind_name))
        .expect("source env should have the inductive");
    let ctor_name = ind
        .constructor_names
        .first()
        .expect("single-constructor inductive should have one constructor");
    let ctor = src
        .get_constructor(ctor_name)
        .expect("source env should have the constructor");

    dst.add_inductive(InductiveDecl {
        level_params: ind.level_params.clone(),
        num_params: ind.num_params,
        types: vec![InductiveType {
            name: ind.name.clone(),
            type_: ind.type_.clone(),
            constructors: vec![Constructor {
                name: ctor.name.clone(),
                type_: ctor.type_.clone(),
            }],
        }],
    })
    .expect("re-adding the imported inductive should succeed");

    for fn_name in proj_fns {
        let info = src
            .get_const(&Name::from_string(fn_name))
            .expect("source env should have the projection function");
        let value = info
            .value
            .clone()
            .expect("projection function should have a body");
        dst.add_decl(Declaration::Definition {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value,
            is_reducible: true,
        })
        .expect("re-adding the imported projection function should succeed");
    }
}

/// Build an environment that has `Nat`, `Subtype` and `Sigma` available the way
/// a real `.olean` import does: the inductives and their Lean projection
/// functions are present, but there is **no** clean-side `structure_fields`
/// table for `Subtype` / `Sigma`.
fn imported_env() -> Environment {
    // Canonical declarations, built by the kernel itself.
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native.init_true_false().expect("init_true_false");
    native.init_subtype().expect("init_subtype");
    native.init_sigma().expect("init_sigma");

    // Fresh env that imports them *without* the field table.
    let mut imported = Environment::new();
    imported.init_nat().expect("init_nat");
    imported.init_true_false().expect("init_true_false");
    copy_as_imported(
        &native,
        &mut imported,
        "Subtype",
        &["Subtype.val", "Subtype.property"],
    );
    copy_as_imported(&native, &mut imported, "Sigma", &["Sigma.fst", "Sigma.snd"]);
    imported
}

// =============================================================================
// Precondition: the synthesized environment matches the *import* configuration
// (inductive + projection functions present, no clean-side field table).
// =============================================================================

#[test]
fn test_imported_subtype_sigma_have_no_clean_field_table() {
    let env = imported_env();

    for ind in ["Subtype", "Sigma"] {
        assert!(
            env.get_inductive(&Name::from_string(ind)).is_some(),
            "{ind} inductive should be imported"
        );
        assert!(
            env.get_structure_field_names(&Name::from_string(ind))
                .is_none(),
            "an imported {ind} must NOT carry a clean-side structure_fields table — \
             this is the exact condition that routes `.val`/`.fst` through the \
             dot-notation fallback"
        );
    }

    for proj in ["Subtype.val", "Subtype.property", "Sigma.fst", "Sigma.snd"] {
        assert!(
            env.get_const(&Name::from_string(proj)).is_some(),
            "{proj} projection function should be imported"
        );
    }
}

// =============================================================================
// Subtype: `.val` on an imported Subtype value must project + reduce to the
// genuine witness. `.property` (a Prop / dependent field) must elaborate and
// kernel-check.
// =============================================================================

#[test]
fn test_imported_subtype_val_reduces_to_witness() {
    let mut env = imported_env();

    // A concrete predicate on Nat so we have a real `Subtype` to project.
    // `IsZero : Nat → Prop := fun _ => True`, and a witness
    // `s : Subtype IsZero := ⟨Nat.zero, True.intro⟩`.
    //
    // The witness is built with the fully explicit `@Subtype.mk Nat IsZero …`
    // form on purpose: inferring the *implicit* predicate `{p}` from the proof
    // argument (`p val =?= True`) is a higher-order unification that clean's
    // elaborator does not yet solve — an orthogonal gap that is not what this
    // probe tests. Pinning the type args explicitly isolates the test to the
    // *projection* (`.val`) lowering on the imported value.
    elaborate_decls_into(
        &mut env,
        "def IsZero (n : Nat) : Prop := True\n\
         def witness : Subtype IsZero := @Subtype.mk Nat IsZero Nat.zero True.intro\n\
         def getVal (s : Subtype IsZero) : Nat := s.val\n\
         def witnessVal : Nat := getVal witness",
    );

    // `s.val` must lower to the imported `Subtype.val` projection function (the
    // dot-notation fallback), proving we are genuinely on the import path.
    let get_val = env
        .get_const(&Name::from_string("getVal"))
        .expect("getVal should be registered");
    let body = get_val
        .value
        .as_ref()
        .expect("getVal is a definition with a body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Subtype.val")),
        "getVal's body must be compiled against the imported Subtype.val function, \
         got: {:?}",
        body.collect_constants()
    );

    // And it must REDUCE to the actual witness `Nat.zero`, not get stuck or
    // select the wrong slot.
    assert_eq!(
        whnf_head_const(&env, &const_("witnessVal")).as_deref(),
        Some("Nat.zero"),
        "getVal ⟨Nat.zero, True.intro⟩ must reduce to the val field (Nat.zero)"
    );

    // Direct projection on the literal value must agree.
    let direct = Expr::app(const_("getVal"), const_("witness"));
    assert_eq!(
        whnf_head_const(&env, &direct).as_deref(),
        Some("Nat.zero"),
        "getVal witness must reduce to Nat.zero"
    );
}

#[test]
fn test_imported_subtype_property_elaborates_and_kernel_checks() {
    let mut env = imported_env();

    // `.property` returns the (dependent, Prop-valued) proof `p s.val`. Here
    // `p = IsZero` and `IsZero n` unfolds to `True`, so the property has type
    // `True` once reduced. We elaborate a def that *uses* `s.property` and
    // relies on `elaborate_decl_and_register`'s full kernel check: reaching the
    // end means `s.property : IsZero s.val` kernel-checked, i.e. the dependent
    // Prop projection lowered correctly.
    elaborate_decls_into(
        &mut env,
        "def IsZero (n : Nat) : Prop := True\n\
         def getProp (s : Subtype IsZero) : IsZero s.val := s.property",
    );

    let get_prop = env
        .get_const(&Name::from_string("getProp"))
        .expect("getProp should be registered");
    let body = get_prop
        .value
        .as_ref()
        .expect("getProp is a definition with a body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Subtype.property")),
        "getProp's body must be compiled against the imported Subtype.property function, \
         got: {:?}",
        body.collect_constants()
    );
}

// =============================================================================
// Sigma: `.fst` and `.snd` (dependent second component) on an imported Sigma
// value must project + reduce to the correct components.
// =============================================================================

#[test]
fn test_imported_sigma_fst_snd_reduce_to_correct_components() {
    let mut env = imported_env();

    // A non-dependent Sigma over `Nat` whose two components are *distinct*
    // values, so a fst/snd swap or off-by-`num_params` slip is observable.
    //   β := fun _ => Nat
    //   p : Sigma β := ⟨Nat.zero, Nat.succ Nat.zero⟩   (fst = 0, snd = 1)
    //
    // As with the Subtype witness, the value is built with explicit `@Sigma.mk`
    // type args to side-step the unrelated higher-order-unification gap and keep
    // the focus on the `.fst` / `.snd` projection lowering.
    elaborate_decls_into(
        &mut env,
        "def constNat (n : Nat) : Type := Nat\n\
         def pair : Sigma constNat := @Sigma.mk Nat constNat Nat.zero (Nat.succ Nat.zero)\n\
         def getFst (s : Sigma constNat) : Nat := s.fst\n\
         def getSnd (s : Sigma constNat) : constNat s.fst := s.snd",
    );

    // Both projections must lower to the imported Sigma projection functions.
    for (def, expect_fn) in [("getFst", "Sigma.fst"), ("getSnd", "Sigma.snd")] {
        let info = env
            .get_const(&Name::from_string(def))
            .unwrap_or_else(|| panic!("{def} should be registered"));
        let body = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{def} is a definition with a body"));
        assert!(
            body.collect_constants()
                .contains(&Name::from_string(expect_fn)),
            "{def}'s body must be compiled against the imported {expect_fn}, got: {:?}",
            body.collect_constants()
        );
    }

    // fst selects the FIRST component (Nat.zero), snd the SECOND (Nat.succ 0).
    let get_fst = Expr::app(const_("getFst"), const_("pair"));
    assert_eq!(
        whnf_head_const(&env, &get_fst).as_deref(),
        Some("Nat.zero"),
        "getFst ⟨0, 1⟩ must reduce to the fst component (Nat.zero)"
    );

    // `Nat.succ Nat.zero` normalizes to the kernel `Nat` literal `1`, so compare
    // by definitional equality rather than head name. The reference `1` is
    // *distinct* from the fst component, so this still pins the fst/snd choice.
    let get_snd = Expr::app(const_("getSnd"), const_("pair"));
    let one = Expr::app(const_("Nat.succ"), const_("Nat.zero"));
    assert!(
        def_eq(&env, &get_snd, &one),
        "getSnd ⟨0, 1⟩ must reduce to the snd component (Nat.succ Nat.zero), got {:?}",
        TypeChecker::new(&env).whnf(&get_snd).kind()
    );
    // And it must NOT collapse to the fst component — guards against a fst/snd swap.
    assert!(
        !def_eq(&env, &get_snd, &const_("Nat.zero")),
        "getSnd must select the snd component, not the fst (Nat.zero)"
    );
}

// =============================================================================
// Control: the NATIVE path (init_subtype / init_sigma register a field table,
// so `.val`/`.fst` lower to a kernel `Proj`) reduces correctly too. This
// isolates any regression to the import-only dot-notation lowering rather than
// kernel projection reduction.
// =============================================================================

#[test]
fn test_native_subtype_sigma_projection_reduces_correctly() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env.init_subtype().expect("init_subtype");
    env.init_sigma().expect("init_sigma");

    // Native Subtype/Sigma DO have a clean-side field table.
    assert!(
        env.get_structure_field_names(&Name::from_string("Subtype"))
            .is_some(),
        "native Subtype should register a structure_fields table"
    );

    elaborate_decls_into(
        &mut env,
        "def IsZero (n : Nat) : Prop := True\n\
         def witness : Subtype IsZero := @Subtype.mk Nat IsZero Nat.zero True.intro\n\
         def getValN (s : Subtype IsZero) : Nat := s.val\n\
         def constNat (n : Nat) : Type := Nat\n\
         def pair : Sigma constNat := @Sigma.mk Nat constNat Nat.zero (Nat.succ Nat.zero)\n\
         def getFstN (s : Sigma constNat) : Nat := s.fst\n\
         def getSndN (s : Sigma constNat) : constNat s.fst := s.snd",
    );

    // Native `.val`/`.fst` lower to a kernel `Proj`, not the projection function.
    let get_val_n = env
        .get_const(&Name::from_string("getValN"))
        .and_then(|i| i.value.clone())
        .expect("getValN body");
    assert!(
        !get_val_n
            .collect_constants()
            .contains(&Name::from_string("Subtype.val")),
        "native getValN should lower s.val to a kernel Proj, not the Subtype.val function"
    );

    assert_eq!(
        whnf_head_const(&env, &Expr::app(const_("getValN"), const_("witness"))).as_deref(),
        Some("Nat.zero"),
        "native getValN witness must reduce to Nat.zero"
    );
    assert_eq!(
        whnf_head_const(&env, &Expr::app(const_("getFstN"), const_("pair"))).as_deref(),
        Some("Nat.zero"),
        "native getFstN ⟨0,1⟩ must reduce to Nat.zero"
    );
    let get_snd_n = Expr::app(const_("getSndN"), const_("pair"));
    let one = Expr::app(const_("Nat.succ"), const_("Nat.zero"));
    assert!(
        def_eq(&env, &get_snd_n, &one),
        "native getSndN ⟨0,1⟩ must reduce to Nat.succ Nat.zero"
    );
}
