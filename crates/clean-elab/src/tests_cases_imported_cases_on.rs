// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for the `cases` tactic on an `.olean`-IMPORTED
//! inductive — the `EnvironmentMissing TrustIr.BinOp.casesOn` blocker of the
//! trust-ir Lean↔Clean bridge (`by cases op <;> rfl` over the imported
//! `BinOp`).
//!
//! ## Root cause
//!
//! A NATIVE Clean inductive registers `T.casesOn` in the kernel recursor
//! registry (`build_cases_on`), but Lean 4 itself ships `T.casesOn` as an
//! auxiliary *definition* (`Lean/Meta/Constructions/CasesOn.lean`) — only
//! `T.rec` is a Recursor kernel object. An `.olean`-imported inductive
//! therefore arrives with `get_recursor("T.casesOn")` MISSING while
//! `get_const` finds the definitional constant. The `cases` tactic hard
//! required the recursor-registry entry, so it failed with
//! `EnvironmentMissing` on every imported inductive, even though the
//! term-level `match` elaborator already had the Definition fallback
//! (`elab_match/helpers.rs::eliminator_levels`).
//!
//! ## Fix
//!
//! `cases_core` mirrors the `elab_match` two-tier lookup: the only datum the
//! tactic needs from the registry is the eliminator's universe arity, and the
//! constant's declared `level_params` is authoritative for that either way.
//! The application layout (params → motive → major → minors) is the same
//! `MajorAfterMotive` convention in both worlds, and the assembled proof is
//! still kernel-rechecked, so the fallback cannot over-accept.
//!
//! These tests simulate the import shape natively (no `.olean` fixtures
//! needed): the inductive, constructors, and `.rec` are registered through the
//! same `TrustedEnvExt` entry points the `.olean` loader uses, while
//! `.casesOn` is present ONLY as a plain constant — exactly the imported
//! state.

use crate::elaborate_decl_and_register;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{ConstantInfo, Environment, Name};
use clean_parser::parse_file;

fn elaborate_all(env: &mut Environment, code: &str, label: &str) {
    let decls = parse_file(code).unwrap_or_else(|e| panic!("{label}: parse failed: {e:?}"));
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(env, decl);
        assert!(
            result.is_ok(),
            "{label}: decl {i} should elaborate, got: {result:?}"
        );
    }
}

/// Build an environment holding a 3-constructor enum `Trio` in the
/// `.olean`-import shape: inductive + constructors + `.rec` registered, but
/// `.casesOn` present ONLY as a plain constant (NOT in the recursor registry).
///
/// The Lean-shaped payloads are obtained by elaborating the inductive natively
/// in a donor environment and transplanting them through the same
/// `TrustedEnvExt` registration hooks the `.olean` loader uses.
fn build_import_shaped_env() -> Environment {
    let mut donor = Environment::with_prelude();
    elaborate_all(
        &mut donor,
        "inductive Trio where\n  | a\n  | b\n  | c",
        "donor Trio",
    );

    let trio = Name::from_string("Trio");
    let cases_on = Name::from_string("Trio.casesOn");

    let mut env = Environment::with_prelude();
    env.register_inductive(
        donor
            .get_inductive(&trio)
            .expect("donor should have the Trio inductive")
            .clone(),
    );
    for ctor in ["Trio.a", "Trio.b", "Trio.c"] {
        env.register_constructor(
            donor
                .get_constructor(&Name::from_string(ctor))
                .unwrap_or_else(|| panic!("donor should have constructor {ctor}"))
                .clone(),
        );
    }
    // `.rec` IS a Recursor kernel object in a real `.olean`; register it as one.
    env.register_recursor(
        donor
            .get_recursor(&Name::from_string("Trio.rec"))
            .expect("donor should have Trio.rec in the recursor registry")
            .clone(),
    );
    // `.casesOn` is a plain definitional constant in a real `.olean`: register
    // ONLY its `ConstantInfo` mirror (same shape `register_recursor` would
    // create for the constant map), never the recursor-registry entry.
    let donor_cases_on = donor
        .get_const(&cases_on)
        .expect("donor should have the Trio.casesOn constant")
        .clone();
    env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
        donor_cases_on.name.clone(),
        donor_cases_on.level_params.clone(),
        donor_cases_on.type_.clone(),
        None,
        false,
    )));

    // Sanity of the simulation: the import shape means `get_recursor` misses
    // while `get_const` hits.
    assert!(
        env.get_recursor(&cases_on).is_none(),
        "simulation must NOT have Trio.casesOn in the recursor registry"
    );
    assert!(
        env.get_const(&cases_on).is_some(),
        "simulation must have Trio.casesOn as a plain constant"
    );
    env
}

/// The bridge shape: `by cases t <;> rfl` over an inductive whose `casesOn`
/// is a plain imported Definition. Before the fix this failed with
/// `TacticFailed(EnvironmentMissing { constant: "Trio.casesOn" })`.
#[test]
fn test_cases_tactic_on_imported_cases_on_definition() {
    let mut env = build_import_shaped_env();
    elaborate_all(
        &mut env,
        "theorem trio_refl (t : Trio) : t = t := by cases t <;> rfl",
        "cases over imported casesOn",
    );
}

/// Control: the same theorem in the fully-native environment (registry-backed
/// `casesOn`) keeps working — the fallback is an addition, not a replacement.
#[test]
fn test_cases_tactic_native_registry_still_works() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "inductive Trio where\n  | a\n  | b\n  | c\n\n\
         theorem trio_refl (t : Trio) : t = t := by cases t <;> rfl",
        "cases over native casesOn",
    );
}

/// Fail-closed floor: when `casesOn` is absent from BOTH the recursor registry
/// and the constant map, the tactic must fail with a clean error (never panic,
/// never silently accept).
#[test]
fn test_cases_tactic_missing_cases_on_fails_closed() {
    let mut donor = Environment::with_prelude();
    elaborate_all(
        &mut donor,
        "inductive Trio where\n  | a\n  | b\n  | c",
        "donor Trio",
    );
    let trio = Name::from_string("Trio");
    let mut env = Environment::with_prelude();
    env.register_inductive(
        donor
            .get_inductive(&trio)
            .expect("donor should have the Trio inductive")
            .clone(),
    );
    for ctor in ["Trio.a", "Trio.b", "Trio.c"] {
        env.register_constructor(
            donor
                .get_constructor(&Name::from_string(ctor))
                .unwrap_or_else(|| panic!("donor should have constructor {ctor}"))
                .clone(),
        );
    }
    // Deliberately register NEITHER `.rec` nor `.casesOn`.
    let decls = parse_file("theorem trio_refl (t : Trio) : t = t := by cases t <;> rfl")
        .expect("parse should succeed");
    let result = elaborate_decl_and_register(&mut env, &decls[0]);
    assert!(
        result.is_err(),
        "cases with no casesOn constant at all must fail closed, got: {result:?}"
    );
}
