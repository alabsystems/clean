// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for `.olean` universe-parameter reconstruction and
//! order-independent (dependency-safe) constant loading.
//!
//! Background: the "Mathlib Anywhere" gap assessment flagged two suspected
//! blockers for real `.olean` constants kernel-type-checking at scale:
//!
//!   (a) constants loading in *isolation* / file order rather than dependency
//!       order, and
//!   (b) *universe parameters* not being reconstructed from the `.olean`
//!       constant header.
//!
//! These tests pin the *actual* behavior of the import pipeline against
//! round-tripped synthetic `.olean` files (built with [`OleanExporter`], so they
//! run fully offline with no Lean toolchain). They demonstrate that:
//!
//!   * universe-polymorphic constants reconstruct their level parameters
//!     faithfully — including level *arguments* embedded in a `Const` inside a
//!     definition's value — and then kernel-type-check (`infer_sort` /
//!     `add_decl`-equivalent full check);
//!   * a constant referenced by another loads and full-checks correctly
//!     regardless of the order the constants appear in the file, because the
//!     loader adds structurally-validated constants and the kernel check runs
//!     against the fully-assembled environment; and
//!   * a constant whose type references an *undeclared* level parameter is
//!     DECLINED (structural rejection), not mis-loaded with guessed params —
//!     the soundness guard.
//!
//! If a future refactor were to drop level params, switch loading to a checked
//! per-constant add that requires strict ordering, or weaken the
//! undeclared-param guard, one of these tests fails.

use clean_kernel::env::{ConstantInfo, ConstantKind, Environment, Reducibility, TrustedEnvExt};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_olean::verify_batch_full::typecheck_constants_full;
use clean_olean::{load_olean_file, parse_module, OleanExporter};
use std::collections::BTreeSet;
use std::fs;
use tempfile::tempdir;

const TEST_GIT_HASH: &str = "c0de000000000000000000000000000000000010";

/// `{α : Sort u} → α → α`, the canonical universe-polymorphic type.
fn poly_id_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    let inner = Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1));
    Expr::pi(BinderInfo::Implicit, sort_u, inner)
}

/// Round-trip `env` through an `.olean` file and load it into a fresh
/// environment, returning the loaded environment. Constants are written by the
/// exporter and re-parsed by the loader, exercising the full binary path.
fn roundtrip_env(env: &Environment, file_stem: &str) -> Environment {
    let bytes = OleanExporter::export_with_env(env, &[], &[], TEST_GIT_HASH)
        .expect("export_with_env should succeed");
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join(format!("{file_stem}.olean"));
    fs::write(&path, &bytes).expect("write temp .olean");

    let mut loaded = Environment::default();
    load_olean_file(&mut loaded, &path).expect("load_olean_file should succeed");
    loaded
}

// =============================================================================
// (b) Universe-parameter reconstruction
// =============================================================================

#[test]
fn test_universe_poly_axiom_reconstructs_and_kernel_checks() {
    let u = Name::from_string("u");
    let mut env = Environment::default();
    env.extend_constants_unchecked(std::iter::once(ConstantInfo {
        name: Name::from_string("PolyAx"),
        level_params: vec![u.clone()],
        type_: poly_id_type(&u),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Opaque,
        kind: ConstantKind::Axiom,
    }));

    let loaded = roundtrip_env(&env, "PolyAx");
    let ci = loaded
        .get_const(&Name::from_string("PolyAx"))
        .expect("PolyAx should be imported");

    // (b) the single declared level param `u` is reconstructed faithfully.
    assert_eq!(
        ci.level_params
            .iter()
            .map(|n| n.to_string())
            .collect::<Vec<_>>(),
        vec!["u".to_string()],
        "universe parameter `u` must reconstruct from the .olean header"
    );

    // The universe-polymorphic type kernel-type-checks (inhabits a Sort).
    let tc = TypeChecker::new(&loaded);
    let _sort = tc
        .infer_sort(&ci.type_)
        .expect("universe-polymorphic type must inhabit a Sort after import");
}

#[test]
fn test_universe_param_level_argument_in_value_reconstructs_and_full_checks() {
    // Realistic Mathlib shape: a definition whose VALUE applies another
    // universe-polymorphic constant at an explicit level argument
    // (`Const(PolyId, [Param v])`). The level argument must survive the
    // round-trip, and the `add_decl`-equivalent full check must pass.
    let u = Name::from_string("u");
    let v = Name::from_string("v");

    let mut env = Environment::default();
    let poly_id = ConstantInfo {
        name: Name::from_string("PolyId"),
        level_params: vec![u.clone()],
        type_: poly_id_type(&u),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Opaque,
        kind: ConstantKind::Axiom,
    };
    let poly_user = ConstantInfo {
        name: Name::from_string("PolyUser"),
        level_params: vec![v.clone()],
        // Same `{α : Sort v} → α → α` shape, instantiated at v.
        type_: poly_id_type(&v),
        // Value references PolyId at the explicit level argument `v`.
        value: Some(Expr::const_(
            Name::from_string("PolyId"),
            vec![Level::param(v.clone())],
        )),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Definition,
    };
    // NOTE: insertion order does not matter (HashMap-backed); the dependency-
    // order property is pinned explicitly in the (a) tests below.
    env.extend_constants_unchecked(vec![poly_id, poly_user].into_iter());

    let loaded = roundtrip_env(&env, "PolyUser");
    let user = loaded
        .get_const(&Name::from_string("PolyUser"))
        .expect("PolyUser should be imported");

    assert_eq!(
        user.level_params
            .iter()
            .map(|n| n.to_string())
            .collect::<Vec<_>>(),
        vec!["v".to_string()],
        "PolyUser's declared level param `v` must reconstruct"
    );

    // The level ARGUMENT inside the value's `Const` must reconstruct as `v`.
    match user.value.as_ref().map(Expr::kind) {
        Some(clean_kernel::expr::ExprKind::Const(name, levels)) => {
            assert_eq!(name.to_string(), "PolyId");
            assert_eq!(levels.len(), 1, "value Const must carry one level argument");
            assert_eq!(
                levels[0],
                Level::param(v.clone()),
                "value's level argument must reconstruct as the param `v`"
            );
        }
        other => panic!("expected PolyUser value to be Const(PolyId, [v]), got {other:?}"),
    }

    // Full `add_decl`-equivalent check (infer_sort on types + check_type on
    // values) passes for both constants.
    let targets: BTreeSet<String> = ["PolyId", "PolyUser"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    let (pass, fail, errs) =
        typecheck_constants_full(&loaded, &targets, clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT);
    assert_eq!(
        fail, 0,
        "no constant should fail full check, errors: {errs:?}"
    );
    assert_eq!(pass, 2, "both PolyId and PolyUser should pass full check");
}

// =============================================================================
// (a) Order-independent / dependency-safe loading
// =============================================================================

#[test]
fn test_constant_referencing_another_loads_regardless_of_order() {
    // `DepB`'s type references `DepA`. We export with `DepB` listed before
    // `DepA` to ensure the loader does not require the dependency to appear
    // first in the file. Both must load and `DepB`'s type must kernel-check.
    let dep_a = ConstantInfo {
        name: Name::from_string("DepA"),
        level_params: vec![],
        type_: Expr::prop(),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Opaque,
        kind: ConstantKind::Axiom,
    };
    let dep_b = ConstantInfo {
        name: Name::from_string("DepB"),
        level_params: vec![],
        // DepA -> Prop : references DepA in its type.
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("DepA"), Vec::<Level>::new()),
            Expr::prop(),
        ),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Opaque,
        kind: ConstantKind::Axiom,
    };
    // Build the .olean with DepB first, DepA second.
    let bytes = {
        let mut e = Environment::default();
        e.extend_constants_unchecked(vec![dep_b, dep_a].into_iter());
        OleanExporter::export_with_env(&e, &[], &[], TEST_GIT_HASH).expect("export")
    };

    // Sanity: the file genuinely lists both constants (order is exporter-defined).
    let module = parse_module(&bytes).expect("parse round-tripped module");
    let names: BTreeSet<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(names.contains("DepA") && names.contains("DepB"));

    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("Dep.olean");
    fs::write(&path, &bytes).expect("write temp .olean");

    let mut loaded = Environment::default();
    load_olean_file(&mut loaded, &path).expect("load should succeed");

    let dep_b_ci = loaded
        .get_const(&Name::from_string("DepB"))
        .expect("DepB should be imported even though its dependency followed it");
    assert!(
        loaded.get_const(&Name::from_string("DepA")).is_some(),
        "DepA dependency should also be imported"
    );

    // DepB's type (which references DepA) kernel-checks against the assembled env.
    let tc = TypeChecker::new(&loaded);
    let _sort = tc
        .infer_sort(&dep_b_ci.type_)
        .expect("DepB type must resolve DepA through the assembled environment");
}

#[test]
fn test_value_forward_reference_full_checks_independent_of_order() {
    // A definition whose VALUE references a constant that may be emitted later
    // in the file. The full `add_decl`-equivalent check runs against the fully
    // assembled environment, so it passes regardless of intra-file order.
    let mut env = Environment::default();
    let target = ConstantInfo {
        name: Name::from_string("FwdTarget"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Opaque,
        kind: ConstantKind::Axiom,
    };
    let user = ConstantInfo {
        name: Name::from_string("FwdUser"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
        value: Some(Expr::const_(
            Name::from_string("FwdTarget"),
            Vec::<Level>::new(),
        )),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Definition,
    };
    // Emit user before its target.
    env.extend_constants_unchecked(vec![user, target].into_iter());

    let loaded = roundtrip_env(&env, "Fwd");
    let targets: BTreeSet<String> = ["FwdTarget", "FwdUser"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    let (pass, fail, errs) =
        typecheck_constants_full(&loaded, &targets, clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT);
    assert_eq!(
        fail, 0,
        "forward value reference should full-check, errors: {errs:?}"
    );
    assert_eq!(pass, 2, "both constants should pass the full check");
}

// =============================================================================
// Soundness: decline (do not guess) unreconstructable universe headers
// =============================================================================

#[test]
fn test_undeclared_level_param_is_declined_not_misloaded() {
    // A constant whose TYPE references the level param `u` but which declares
    // NO level params is structurally invalid. The loader must DECLINE it
    // (record a skip with an UndefinedLevelParam reason) rather than silently
    // load it with the wrong/guessed universe signature.
    let mut env = Environment::default();
    env.extend_constants_unchecked(std::iter::once(ConstantInfo {
        name: Name::from_string("BadPoly"),
        level_params: vec![], // declares nothing...
        type_: Expr::sort(Level::param(Name::from_string("u"))), // ...but uses `u`
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Opaque,
        kind: ConstantKind::Axiom,
    }));

    let bytes = OleanExporter::export_with_env(&env, &[], &[], TEST_GIT_HASH)
        .expect("export should succeed");
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("BadPoly.olean");
    fs::write(&path, &bytes).expect("write temp .olean");

    let mut loaded = Environment::default();
    let summary = load_olean_file(&mut loaded, &path).expect("load call itself should not error");

    assert_eq!(
        summary.added_constants, 0,
        "the unreconstructable constant must not be added"
    );
    assert!(
        loaded.get_const(&Name::from_string("BadPoly")).is_none(),
        "declined constant must be absent from the environment (no guessed params)"
    );
    let skipped = summary
        .skipped_constants
        .iter()
        .find(|s| s.name == "BadPoly")
        .expect("BadPoly should be recorded as skipped");
    assert!(
        skipped.reason.contains("level parameter") || skipped.reason.contains("level param"),
        "decline reason should cite the undefined universe level parameter, got: {}",
        skipped.reason
    );
}
