// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Audit tests for declarations inserted through unchecked init paths.
//!
//! These tests replay `add_decl` validation checks over already-loaded
//! constants to catch silent type errors introduced by `add_decl_unchecked`.

use super::*;
use crate::tc::TypeChecker;

/// Categorized failure for a declaration that would fail `add_decl`.
#[derive(Debug)]
enum AuditFailure {
    DuplicateLevelParam(String),
    TypeMetavar(String),
    ValueMetavar(String),
    TypeFreeVar(String),
    ValueFreeVar(String),
    UndefLevelInType(String),
    UndefLevelInValue(String),
    InferSortFailed(String, String),
    ValueCheckFailed(String, String),
}

impl AuditFailure {
    fn category(&self) -> &'static str {
        match self {
            AuditFailure::DuplicateLevelParam(_) => "duplicate_level_param",
            AuditFailure::TypeMetavar(_) => "type_metavar",
            AuditFailure::ValueMetavar(_) => "value_metavar",
            AuditFailure::TypeFreeVar(_) => "type_freevar",
            AuditFailure::ValueFreeVar(_) => "value_freevar",
            AuditFailure::UndefLevelInType(_) => "undef_level_type",
            AuditFailure::UndefLevelInValue(_) => "undef_level_value",
            AuditFailure::InferSortFailed(_, _) => "infer_sort_failed",
            AuditFailure::ValueCheckFailed(_, _) => "value_check_failed",
        }
    }

    fn name(&self) -> &str {
        match self {
            AuditFailure::DuplicateLevelParam(n)
            | AuditFailure::TypeMetavar(n)
            | AuditFailure::ValueMetavar(n)
            | AuditFailure::TypeFreeVar(n)
            | AuditFailure::ValueFreeVar(n)
            | AuditFailure::UndefLevelInType(n)
            | AuditFailure::UndefLevelInValue(n)
            | AuditFailure::InferSortFailed(n, _)
            | AuditFailure::ValueCheckFailed(n, _) => n,
        }
    }

    fn detail(&self) -> &str {
        match self {
            AuditFailure::InferSortFailed(_, d) | AuditFailure::ValueCheckFailed(_, d) => d,
            _ => "",
        }
    }
}

/// Audit result for an entire environment: lists failures and passing declarations.
struct AuditResult {
    failures: Vec<AuditFailure>,
    passing: Vec<String>,
    total: usize,
}

fn collect_add_decl_audit(env: &Environment) -> AuditResult {
    let tc = TypeChecker::with_mode(env, env.mode());
    let mut failures = Vec::new();
    let mut passing = Vec::new();

    let mut constants: Vec<_> = env.constants.iter().collect();
    constants.sort_by_key(|(name, _)| name.to_string());
    let total = constants.len();

    for (name, info) in &constants {
        let name_str = name.to_string();
        let mut has_failure = false;

        // Mirror add_decl duplicate universe parameter validation.
        for (i, param) in info.level_params.iter().enumerate() {
            if info.level_params[..i].contains(param) {
                failures.push(AuditFailure::DuplicateLevelParam(name_str.clone()));
                has_failure = true;
                break;
            }
        }

        // Mirror add_decl quick metadata checks.
        if info.type_.has_expr_mvar_quick() || info.type_.has_level_mvar_quick() {
            failures.push(AuditFailure::TypeMetavar(name_str.clone()));
            has_failure = true;
        }
        if info.type_.has_fvar_quick() {
            failures.push(AuditFailure::TypeFreeVar(name_str.clone()));
            has_failure = true;
        }
        if let Some(value) = &info.value {
            if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                failures.push(AuditFailure::ValueMetavar(name_str.clone()));
                has_failure = true;
            }
            if value.has_fvar_quick() {
                failures.push(AuditFailure::ValueFreeVar(name_str.clone()));
                has_failure = true;
            }
        }

        // Mirror add_decl level parameter scope checks.
        if let Some(_undef) = find_undef_level_param(&info.type_, &info.level_params) {
            failures.push(AuditFailure::UndefLevelInType(name_str.clone()));
            has_failure = true;
        }
        if let Some(value) = &info.value {
            if let Some(_undef) = find_undef_level_param(value, &info.level_params) {
                failures.push(AuditFailure::UndefLevelInValue(name_str.clone()));
                has_failure = true;
            }
        }

        // Mirror add_decl type well-formedness and value type checks.
        if let Err(err) = tc.infer_sort(&info.type_) {
            failures.push(AuditFailure::InferSortFailed(
                name_str.clone(),
                format!("{err:?}"),
            ));
            // Skip value check if type is already bad.
            continue;
        }

        if let Some(value) = &info.value {
            if let Err(err) = tc.check_type(value, &info.type_) {
                failures.push(AuditFailure::ValueCheckFailed(
                    name_str.clone(),
                    format!("{err:?}"),
                ));
                has_failure = true;
            }
        }

        if !has_failure {
            passing.push(name_str);
        }
    }

    AuditResult {
        failures,
        passing,
        total,
    }
}

/// Legacy wrapper for backward compat with existing test assertions.
fn collect_add_decl_validation_failures(env: &Environment) -> Vec<String> {
    let result = collect_add_decl_audit(env);
    result
        .failures
        .iter()
        .map(|f| format!("{}: {}", f.name(), f.category()))
        .collect()
}

/// Validate recursor/constructor metadata coherence for all recursors in `env`.
fn collect_recursor_metadata_failures(env: &Environment) -> Vec<String> {
    let mut names: Vec<String> = env.recursors().map(|rec| rec.name.to_string()).collect();
    names.sort();

    names
        .into_iter()
        .filter_map(|name| {
            let rec_name = Name::from_string(&name);
            env.validate_recursor_metadata(&rec_name)
                .err()
                .map(|err| format!("{name}: {err}"))
        })
        .collect()
}

fn summarize_failures(failures: &[String]) -> String {
    let mut message = failures
        .iter()
        .take(20)
        .cloned()
        .collect::<Vec<_>>()
        .join("\n");
    if failures.len() > 20 {
        message.push_str(&format!("\n... {} more", failures.len() - 20));
    }
    message
}

fn run_with_large_stack<F>(_name: &'static str, f: F)
where
    F: FnOnce() + Send + 'static,
{
    crate::test_utils::run_with_stack(crate::test_utils::LARGE_STACK, f);
}

/// Assert that an environment has zero add_decl audit failures (infer_sort + check_type).
fn assert_zero_audit_failures(label: &str, env: &Environment) {
    let result = collect_add_decl_audit(env);
    assert!(
        result.failures.is_empty(),
        "{label}: expected zero add_decl audit failures (infer_sort + check_type), \
         found {n}/{total}:\n{details}",
        n = result.failures.len(),
        total = result.total,
        details = result
            .failures
            .iter()
            .take(20)
            .map(|f| format!("  {} ({}): {}", f.name(), f.category(), f.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

#[test]
fn test_with_prelude_add_decl_audit_reports_failures() {
    run_with_large_stack("add_decl_audit_prelude", || {
        let env = Environment::with_prelude();
        let failures = collect_add_decl_validation_failures(&env);
        // After #1782 fix (index args in build_recursor_rule_rhs), Nat.le.rec
        // and Nat.le.recOn now pass type checking. Zero failures expected.
        assert!(
            failures.is_empty(),
            "Expected zero audit failures after #1782 fix, but found {}:\n{}",
            failures.len(),
            summarize_failures(&failures)
        );
    });
}

#[test]
fn test_topology_manifold_add_decl_audit_reports_failures() {
    run_with_large_stack("add_decl_audit_topology_manifold", || {
        let mut env = Environment::new();
        env.init_topology_manifold()
            .expect("init_topology_manifold should succeed before validation audit");
        let failures = collect_add_decl_validation_failures(&env);
        // After EnvDeclBuilder migration (#1444, #1632), all topology_manifold
        // declarations pass add_decl validation. AddCommGroup.casesOn is now
        // auto-generated by add_inductive, and AddGroup.neg uses add_decl.
        assert!(
            failures.is_empty(),
            "Expected zero audit failures after EnvDeclBuilder migration, \
             but found {}:\n{}",
            failures.len(),
            summarize_failures(&failures)
        );
    });
}

#[test]
fn test_nat_primes_and_fact_decls_are_level_closed() {
    run_with_large_stack("add_decl_audit_level_closed", || {
        let mut env = Environment::new();
        env.init_nat_card()
            .expect("init_nat_card should be infallible in a fresh environment");
        env.init_fact()
            .expect("init_fact should be infallible in a fresh environment");

        for name in ["Nat.Primes", "Fact.out", "Fact.mk"] {
            let info = env
                .get_const(&Name::from_string(name))
                .expect("missing expected declaration");
            assert!(
                find_undef_level_param(&info.type_, &info.level_params).is_none(),
                "{name} type has undefined level parameter with level_params={:?}",
                info.level_params
            );
            if let Some(value) = &info.value {
                assert!(
                    find_undef_level_param(value, &info.level_params).is_none(),
                    "{name} value has undefined level parameter with level_params={:?}",
                    info.level_params
                );
            }
        }
    });
}

/// Verify prelude audit produces zero categorized failures.
///
/// This test exercises the category-counting code path and asserts that
/// all prelude declarations pass the full add_decl audit pipeline.
#[test]
fn test_prelude_audit_categorized_summary() {
    run_with_large_stack("add_decl_audit_categorized", || {
        let env = Environment::with_prelude();
        let result = collect_add_decl_audit(&env);

        // Count failures by category.
        let mut category_counts: std::collections::BTreeMap<&str, Vec<&str>> =
            std::collections::BTreeMap::new();
        for f in &result.failures {
            category_counts
                .entry(f.category())
                .or_default()
                .push(f.name());
        }

        assert!(result.total > 0, "environment should have constants");
        assert!(
            result.failures.is_empty(),
            "prelude audit should have zero failures, got {} across {} categories: {:?}",
            result.failures.len(),
            category_counts.len(),
            category_counts
                .iter()
                .map(|(cat, names)| format!(
                    "{}: {} ({})",
                    cat,
                    names.len(),
                    names[..names.len().min(3)].join(", ")
                ))
                .collect::<Vec<_>>()
        );
    });
}

/// Regression test for core declarations: tracks known failures.
///
/// Known failing declarations have de Bruijn index errors or type construction bugs
/// in the recursor builder (add_inductive) or hand-crafted Eq derivatives (core.rs).
/// As these bugs are fixed, reduce KNOWN_FAILING_DECLS and add the fixed names to
/// MUST_PASS_DECLS. When all are fixed, this test becomes a zero-failure assertion.
#[test]
fn test_core_declarations_pass_add_decl_validation() {
    run_with_large_stack("add_decl_core_validation", || {
        // Build a minimal environment with just core.
        let mut env = Environment::new();
        env.init_sorry().expect("init_sorry");
        env.init_trusted_ay().expect("init_trusted_ay");
        env.init_eq().expect("init_eq");

        let result = collect_add_decl_audit(&env);

        // These declarations are known to pass and MUST continue to pass.
        let must_pass = [
            "sorry",
            "trustedAy",
            "Eq",
            "Eq.refl",
            "rfl",
            "cast",
            "Eq.ndrecOn",
            "Eq.rec",
            "Eq.casesOn",
            "Eq.recOn",
            "Eq.symm",
            "Eq.trans",
            "Eq.mp",
            "Eq.mpr",
            "Eq.subst",
            "Eq.ndrec",
            "congr",
            "congrArg",
            "congrFun",
            "congrFun'",
        ];
        for name in &must_pass {
            assert!(
                result.passing.iter().any(|p| p == name),
                "Core declaration `{name}` should pass add_decl validation but doesn't. \
                 Regression detected.",
            );
        }

        // #1394: add_decl validation is necessary but not sufficient.
        // Also enforce recursor/constructor metadata coherence to catch silent
        // semantic drift in reduction behavior.
        let metadata_failures = collect_recursor_metadata_failures(&env);
        assert!(
            metadata_failures.is_empty(),
            "Core metadata consistency failures:\n{}",
            metadata_failures.join("\n")
        );

        // Known failing count: 0 — all core declarations now pass add_decl validation.
        // Eq.noConfusion/noConfusionType are no longer generated for Prop-valued Eq
        // (matching Lean 4's isPropFormerType guard in NoConfusion.lean:359).
        let known_failing = 0usize;
        let actual_failing = result.total - result.passing.len();

        // Assert no NEW regressions (failure count must not increase).
        assert!(
            actual_failing <= known_failing,
            "Core declaration failures INCREASED from {} to {}. New regression detected: {:?}",
            known_failing,
            actual_failing,
            result
                .failures
                .iter()
                .map(|f| format!("{} ({})", f.name(), f.category()))
                .collect::<Vec<_>>(),
        );
    });
}

// Module-level add_decl audit tests (#1444, 9th directive).
// Each uses the full collect_add_decl_audit pipeline (infer_sort + check_type).

#[test]
fn test_topology_basic_add_decl_audit() {
    run_with_large_stack("add_decl_audit_topology_basic", || {
        let mut env = Environment::new();
        env.init_topology_continuous()
            .expect("init_topology_continuous");
        assert_zero_audit_failures("topology_basic", &env);
    });
}

#[test]
fn test_metric_add_decl_audit() {
    run_with_large_stack("add_decl_audit_metric", || {
        let mut env = Environment::new();
        env.init_metric_space().expect("init_metric_space");
        assert_zero_audit_failures("metric", &env);
    });
}

#[test]
fn test_order_basic_add_decl_audit() {
    run_with_large_stack("add_decl_audit_order_basic", || {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq");
        env.init_ge().expect("init_ge");
        assert_zero_audit_failures("order_basic", &env);
    });
}

#[test]
fn test_order_add_decl_audit() {
    run_with_large_stack("add_decl_audit_order", || {
        let mut env = Environment::new();
        env.init_fate_x_order_stubs()
            .expect("init_fate_x_order_stubs");
        assert_zero_audit_failures("order", &env);
    });
}

#[test]
fn test_data_add_decl_audit() {
    run_with_large_stack("add_decl_audit_data", || {
        let mut env = Environment::new();
        env.init_unit().expect("init_unit");
        env.init_fin().expect("init_fin");
        env.init_decidable_eq().expect("init_decidable_eq");
        env.init_io().expect("init_io");
        env.init_punit().expect("init_punit");
        env.init_prod().expect("init_prod");
        env.init_heq().expect("init_heq");
        env.init_state_t().expect("init_state_t");
        env.init_state_m().expect("init_state_m");
        assert_zero_audit_failures("data", &env);
    });
}

#[test]
fn test_euclidean_geometry_add_decl_audit() {
    run_with_large_stack("add_decl_audit_euclidean_geometry", || {
        let mut env = Environment::new();
        env.init_euclidean_geometry()
            .expect("init_euclidean_geometry");
        assert_zero_audit_failures("euclidean_geometry", &env);
    });
}
