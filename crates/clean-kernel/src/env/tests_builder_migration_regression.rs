// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for the EnvDeclBuilder migration (#1444).
//!
//! Each test initializes one domain module that was migrated from raw
//! `Expr::bvar` arithmetic to `EnvDeclBuilder`, then validates that every
//! declaration in that domain has no leaked FVars, MVars, loose BVars, or
//! undefined level parameters — the specific binder-safety guarantees that
//! EnvDeclBuilder provides.
//!
//! Full type-checking (infer_sort, check_type) is handled separately by
//! `tests_add_decl_audit.rs`. These tests focus on the #1444 root cause:
//! incorrect de Bruijn indices from manual arithmetic.
//!
//! Coverage: topology_basic, metric, order, order_basic, data,
//! euclidean_geometry, core.

use super::*;
use crate::name::Name;

/// Run a closure on a large stack to avoid overflows during type checking.
fn run_with_large_stack<F>(_name: &'static str, f: F)
where
    F: FnOnce() + Send + 'static,
{
    crate::test_utils::run_with_stack(crate::test_utils::LARGE_STACK, f);
}

/// Validate binder-safety for declarations matching `prefixes`: no leaked
/// FVars, MVars, loose BVars, or undefined level parameters.
///
/// Returns (passing_count, failure_details). Does NOT check type
/// well-formedness (infer_sort/check_type) — that is the job of
/// `tests_add_decl_audit.rs`.
fn audit_binder_safety_by_prefix(env: &Environment, prefixes: &[&str]) -> (usize, Vec<String>) {
    let mut passing = 0usize;
    let mut failures = Vec::new();

    let mut constants: Vec<_> = env.constants.iter().collect();
    constants.sort_by_key(|(name, _)| name.to_string());

    for (name, info) in &constants {
        let name_str = name.to_string();
        if !prefixes.iter().any(|p| name_str.starts_with(p)) {
            continue;
        }

        let mut has_failure = false;

        // Leaked FVars (the #1444 root cause).
        if info.type_.has_fvar_quick() {
            failures.push(format!("{name_str}: type has leaked FVar"));
            has_failure = true;
        }
        if let Some(value) = &info.value {
            if value.has_fvar_quick() {
                failures.push(format!("{name_str}: value has leaked FVar"));
                has_failure = true;
            }
        }

        // Leaked MVars.
        if info.type_.has_expr_mvar_quick() || info.type_.has_level_mvar_quick() {
            failures.push(format!("{name_str}: type has metavar"));
            has_failure = true;
        }
        if let Some(value) = &info.value {
            if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                failures.push(format!("{name_str}: value has metavar"));
                has_failure = true;
            }
        }

        // Loose BVars (the #1453 root cause).
        if info.type_.has_loose_bvars() {
            failures.push(format!("{name_str}: type has loose BVars"));
            has_failure = true;
        }
        if let Some(value) = &info.value {
            if value.has_loose_bvars() {
                failures.push(format!("{name_str}: value has loose BVars"));
                has_failure = true;
            }
        }

        // Level parameter scope.
        if let Some(undef) = find_undef_level_param(&info.type_, &info.level_params) {
            failures.push(format!("{name_str}: undef level `{undef}` in type"));
            has_failure = true;
        }
        if let Some(value) = &info.value {
            if let Some(undef) = find_undef_level_param(value, &info.level_params) {
                failures.push(format!("{name_str}: undef level `{undef}` in value"));
                has_failure = true;
            }
        }

        if !has_failure {
            passing += 1;
        }
    }

    (passing, failures)
}

// ---------------------------------------------------------------------------
// Gate 1: Regression tests per migrated domain
// ---------------------------------------------------------------------------

/// Regression: topology_basic declarations pass add_decl after EnvDeclBuilder migration.
///
/// Covers: TopologicalSpace, IsOpen, IsClosed, interior, closure, continuous,
/// continuous_comp, connected, compact, Hausdorff, homeomorphism, locally_compact.
#[test]
fn test_topology_basic_builder_migration_regression() {
    run_with_large_stack("builder_regression_topology_basic", || {
        let mut env = Environment::new();
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        env.init_topology_connected()
            .expect("init_topology_connected");
        env.init_topology_compact().expect("init_topology_compact");
        env.init_topology_hausdorff()
            .expect("init_topology_hausdorff");
        env.init_topology_homeomorphism()
            .expect("init_topology_homeomorphism");
        env.init_topology_locally_compact()
            .expect("init_topology_locally_compact");

        let prefixes = &[
            "TopologicalSpace",
            "Topology.IsOpen",
            "Topology.IsClosed",
            "Topology.interior",
            "Topology.closure",
            "Topology.continuous",
            "Topology.Continuous",
            "Topology.connected",
            "Topology.Connected",
            "Topology.compact",
            "Topology.Compact",
            "Topology.Hausdorff",
            "Topology.IsHausdorff",
            "Topology.Homeomorphism",
            "Topology.IsHomeomorphism",
            "Topology.locally_compact",
            "Topology.IsLocallyCompact",
        ];

        let (passing, failures) = audit_binder_safety_by_prefix(&env, prefixes);

        assert!(
            failures.is_empty(),
            "#1444 regression: topology_basic declarations have {} failures after \
             EnvDeclBuilder migration:\n{}",
            failures.len(),
            failures.join("\n")
        );
        assert!(
            passing >= 5,
            "Expected at least 5 topology_basic declarations to pass audit, got {passing}"
        );
    });
}

/// Regression: metric declarations pass add_decl after EnvDeclBuilder migration.
///
/// Covers: MetricSpace, distance, balls, continuous, Lipschitz, uniform continuity,
/// Cauchy sequences, completeness, boundedness, compactness.
#[test]
fn test_metric_builder_migration_regression() {
    run_with_large_stack("builder_regression_metric", || {
        let mut env = Environment::new();
        env.init_metric_space().expect("init_metric_space");

        let prefixes = &["MetricSpace", "Metric."];

        let (passing, failures) = audit_binder_safety_by_prefix(&env, prefixes);

        assert!(
            failures.is_empty(),
            "#1444 regression: metric declarations have {} failures after \
             EnvDeclBuilder migration:\n{}",
            failures.len(),
            failures.join("\n")
        );
        assert!(
            passing >= 3,
            "Expected at least 3 metric declarations to pass audit, got {passing}"
        );
    });
}

/// Regression: order_basic declarations pass add_decl after EnvDeclBuilder migration.
///
/// Covers: Nat ordering (Preorder, PartialOrder, LinearOrder, reflexive, irrefl,
/// asymm, trans, antisymm, StrictOrder, trichotomy, decidable ordering).
#[test]
fn test_order_basic_builder_migration_regression() {
    run_with_large_stack("builder_regression_order_basic", || {
        let mut env = Environment::new();
        env.init_nat_preorder().expect("init_nat_preorder");
        env.init_nat_partial_order()
            .expect("init_nat_partial_order");
        env.init_nat_linear_order().expect("init_nat_linear_order");
        env.init_nat_le_reflexive().expect("init_nat_le_reflexive");
        env.init_nat_lt_irrefl().expect("init_nat_lt_irrefl");
        env.init_nat_lt_asymm().expect("init_nat_lt_asymm");
        env.init_nat_lt_trans().expect("init_nat_lt_trans");
        env.init_nat_le_antisymm().expect("init_nat_le_antisymm");
        env.init_nat_le_trans().expect("init_nat_le_trans");
        env.init_strict_order().expect("init_strict_order");

        let prefixes = &[
            "Nat.Preorder",
            "Nat.PartialOrder",
            "Nat.LinearOrder",
            "Nat.le_refl",
            "Nat.lt_irrefl",
            "Nat.lt_asymm",
            "Nat.lt_trans",
            "Nat.le_antisymm",
            "Nat.le_trans",
            "StrictOrder",
            "Preorder",
            "PartialOrder",
            "LinearOrder",
        ];

        let (passing, failures) = audit_binder_safety_by_prefix(&env, prefixes);

        assert!(
            failures.is_empty(),
            "#1444 regression: order_basic declarations have {} failures after \
             EnvDeclBuilder migration:\n{}",
            failures.len(),
            failures.join("\n")
        );
        assert!(
            passing >= 3,
            "Expected at least 3 order_basic declarations to pass audit, got {passing}"
        );
    });
}

/// Regression: order declarations pass add_decl after EnvDeclBuilder migration.
///
/// Covers: LE, LT, GE, GT, Ordering, Int ordering.
#[test]
fn test_order_builder_migration_regression() {
    run_with_large_stack("builder_regression_order", || {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq"); // noConfusion declarations reference Eq
        env.init_le().expect("init_le");
        env.init_lt().expect("init_lt");
        env.init_ge().expect("init_ge");
        env.init_gt().expect("init_gt");
        env.init_ordering().expect("init_ordering");

        let prefixes = &["LE", "LT", "GE", "GT", "Ordering"];

        let (passing, failures) = audit_binder_safety_by_prefix(&env, prefixes);

        assert!(
            failures.is_empty(),
            "#1444 regression: order declarations have {} failures after \
             EnvDeclBuilder migration:\n{}",
            failures.len(),
            failures.join("\n")
        );
        assert!(
            passing >= 5,
            "Expected at least 5 order declarations to pass audit, got {passing}"
        );
    });
}

/// Regression: data declarations pass add_decl after EnvDeclBuilder migration.
///
/// Covers: Unit, PLift, Fin, Array, Option ops, List ops, Inhabited, BEq,
/// DecidableEq, Hashable, IO, StateT, StateM, Id.
#[test]
fn test_data_builder_migration_regression() {
    run_with_large_stack("builder_regression_data", || {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq"); // noConfusion declarations reference Eq
        env.init_unit().expect("init_unit");
        env.init_plift().expect("init_plift");
        env.init_fin().expect("init_fin");
        env.init_inhabited().expect("init_inhabited");

        let prefixes = &["Unit", "PUnit", "PLift", "Fin", "Inhabited"];

        let (passing, failures) = audit_binder_safety_by_prefix(&env, prefixes);

        assert!(
            failures.is_empty(),
            "#1444 regression: data declarations have {} failures after \
             EnvDeclBuilder migration:\n{}",
            failures.len(),
            failures.join("\n")
        );
        assert!(
            passing >= 3,
            "Expected at least 3 data declarations to pass audit, got {passing}"
        );
    });
}

/// Regression: euclidean_geometry declarations pass add_decl after EnvDeclBuilder migration.
///
/// Covers: EuclideanGeometry, Collinear, Concyclic, Sphere, InnerProduct, Angle.
#[test]
fn test_euclidean_geometry_builder_migration_regression() {
    run_with_large_stack("builder_regression_euclidean_geometry", || {
        let mut env = Environment::new();
        env.init_euclidean_geometry()
            .expect("init_euclidean_geometry");

        let prefixes = &["EuclideanGeometry", "Geometry."];

        let (passing, failures) = audit_binder_safety_by_prefix(&env, prefixes);

        assert!(
            failures.is_empty(),
            "#1444 regression: euclidean_geometry declarations have {} failures after \
             EnvDeclBuilder migration:\n{}",
            failures.len(),
            failures.join("\n")
        );
        assert!(
            passing >= 3,
            "Expected at least 3 euclidean_geometry declarations to pass audit, got {passing}"
        );
    });
}

/// Regression: core declarations pass add_decl after EnvDeclBuilder migration.
///
/// Covers: sorry, Eq, rfl, cast, Eq.rec, Eq.symm, Eq.trans, congr, congrArg.
/// This complements `test_core_declarations_pass_add_decl_validation` in
/// tests_add_decl_audit.rs by using the prefix-based audit pattern.
#[test]
fn test_core_builder_migration_regression() {
    run_with_large_stack("builder_regression_core", || {
        let mut env = Environment::new();
        env.init_sorry().expect("init_sorry");
        env.init_eq().expect("init_eq");

        let prefixes = &["sorry", "Eq", "rfl", "cast", "congr"];

        let (passing, failures) = audit_binder_safety_by_prefix(&env, prefixes);

        assert!(
            failures.is_empty(),
            "#1444 regression: core declarations have {} failures after \
             EnvDeclBuilder migration:\n{}",
            failures.len(),
            failures.join("\n")
        );
        assert!(
            passing >= 5,
            "Expected at least 5 core declarations to pass audit, got {passing}"
        );
    });
}

// ---------------------------------------------------------------------------
// Gate 3: continuous_comp migration verified
// ---------------------------------------------------------------------------

/// Regression guard for continuous_comp EnvDeclBuilder migration.
///
/// All three continuous_comp declarations (Topology.continuous_comp,
/// Metric.continuous_comp, Metric.uniform_continuous_comp) were migrated
/// from raw Expr::bvar to EnvDeclBuilder. This test validates they have
/// no loose bound variables — the specific failure mode of #1453.
#[test]
fn test_continuous_comp_no_loose_bvars_after_migration() {
    run_with_large_stack("builder_regression_continuous_comp", || {
        let mut env = Environment::new();
        env.init_topological_space()
            .expect("init_topological_space");
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        env.init_metric_space().expect("init_metric_space");
        env.init_metric_continuous()
            .expect("init_metric_continuous");
        env.init_metric_uniform_continuous()
            .expect("init_metric_uniform_continuous");

        let decl_names = [
            "Topology.continuous_comp",
            "Metric.continuous_comp",
            "Metric.uniform_continuous_comp",
        ];
        for decl_name in decl_names {
            let name = Name::from_string(decl_name);
            let info = env
                .get_const(&name)
                .expect("continuous_comp declaration should exist in environment");

            assert!(
                !info.type_.has_fvar_quick(),
                "{decl_name}: type has leaked FVar after EnvDeclBuilder migration"
            );
            assert!(
                !info.type_.has_loose_bvars(),
                "{decl_name}: type has loose BVars (#1453 regression)"
            );

            if let Some(value) = &info.value {
                assert!(
                    !value.has_fvar_quick(),
                    "{decl_name}: value has leaked FVar after EnvDeclBuilder migration"
                );
                assert!(
                    !value.has_loose_bvars(),
                    "{decl_name}: value has loose BVars (#1453 regression)"
                );
            }
        }
    });
}
