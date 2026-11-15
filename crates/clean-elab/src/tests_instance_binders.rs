// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact pinned/current Lean controls for header instance annotations.

use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DriverOptions, EnvironmentSetup, ModuleReport, VerdictKind,
};
use clean_kernel::{Environment, Name};
use std::path::Path;

macro_rules! fixture {
    ($name:literal) => {
        include_str!(concat!(
            "../../../reports/instance-binders-2026-11-06/sources/",
            $name,
            ".lean"
        ))
    };
}

macro_rules! local_fixture {
    ($name:literal) => {
        include_str!(concat!(
            "../../../reports/local-function-headers-2026-11-06/sources/",
            $name,
            ".lean"
        ))
    };
}

fn check(source: &str) -> (ModuleReport, Environment) {
    let _lock = module_elaboration_lock();
    let path = Path::new("InstanceBinders.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("check environment");
    let _budget = DeclBudgetScope::enter(0);
    let parsed = parse_module(path, source).1.expect("fixture parses");
    let mut file_ctx = module_file_context(path);
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut file_ctx,
        DriverOptions::default(),
        &mut (),
    );
    (report, env)
}

fn accepted(source: &str) {
    let (report, env) = check(source);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{source}\n{:#?}",
        report.verdicts
    );
    let name = Name::from_string("probe");
    assert!(env.get_const(&name).is_some(), "probe registered: {source}");
    assert!(
        env.axiom_deps(&name).expect("probe closure").is_empty(),
        "no axioms: {source}"
    );
}

fn refused(source: &str, diagnostic: &str) {
    let (report, _) = check(source);
    assert!(
        report.verdicts.iter().any(|v| {
            v.kind != VerdictKind::Passed
                && v.detail
                    .as_deref()
                    .is_some_and(|text| text.contains(diagnostic))
        }),
        "{source}\n{:#?}",
        report.verdicts
    );
}

#[test]
fn nonclass_headers_are_refused_by_the_annotation_check() {
    for source in [
        fixture!("nonclass_true"),
        fixture!("nonclass_nat"),
        fixture!("forall_nonclass"),
        fixture!("section_nonclass"),
        fixture!("have_nonclass"),
        fixture!("structure_nonclass"),
        fixture!("structure_param_nonclass"),
        fixture!("inductive_nonclass"),
        fixture!("axiom_nonclass"),
    ] {
        refused(
            source,
            "invalid binder annotation, type is not a class instance",
        );
    }
}

#[test]
fn lambdas_and_local_let_instances_preserve_their_distinct_lean_boundary() {
    for source in [
        fixture!("lambda_nonclass"),
        fixture!("lambda_without_expected"),
        fixture!("lambda_bool"),
        fixture!("letI_nonclass"),
        fixture!("lambda_class"),
    ] {
        accepted(source);
    }
}

#[test]
fn class_headers_and_reducible_aliases_are_accepted() {
    for source in [
        fixture!("inhabited_class"),
        fixture!("nonempty_class"),
        fixture!("abbrev_class"),
        fixture!("reducible_class"),
        fixture!("forall_class"),
        fixture!("class_extends"),
    ] {
        accepted(source);
    }
    for source in [fixture!("def_class"), fixture!("irreducible_class")] {
        refused(
            source,
            "invalid binder annotation, type is not a class instance",
        );
    }
}

#[test]
fn parametric_local_instances_require_forward_dependencies() {
    accepted(fixture!("parametric_dependent"));
    accepted(fixture!("parametric_instance_unused"));
    refused(
        fixture!("parametric_unused"),
        "invalid parametric local instance",
    );
}

#[test]
fn annotation_option_disables_only_its_check_and_restores_after_scope() {
    for source in [
        fixture!("check_disabled_true"),
        fixture!("check_disabled_bool"),
        fixture!("check_disabled_scoped"),
    ] {
        accepted(source);
    }
    let (report, env) = check(fixture!("check_scope_restored"));
    let first = report
        .verdicts
        .iter()
        .find(|v| v.name == "localProbe")
        .expect("local theorem");
    assert_eq!(first.kind, VerdictKind::Passed);
    let second = report
        .verdicts
        .iter()
        .find(|v| v.name == "probe")
        .expect("outer theorem");
    assert_ne!(second.kind, VerdictKind::Passed);
    assert!(second
        .detail
        .as_deref()
        .expect("diagnostic")
        .contains("invalid binder annotation"));
    assert!(env.get_const(&Name::from_string("localProbe")).is_some());
    assert!(env.get_const(&Name::from_string("probe")).is_none());
}

/// Exercise the Q6 universe shape with real checked classes, independently
/// of the legacy Mathlib overlay's domain-specific axioms.
#[test]
fn q6_universe_shape_uses_genuine_checked_classes() {
    accepted(fixture!("q6_genuine_classes"));
}

#[test]
fn instance_where_headers_use_the_same_annotation_check() {
    refused(
        fixture!("instance_nonclass"),
        "invalid binder annotation, type is not a class instance",
    );
    refused(
        fixture!("instance_unused"),
        "invalid parametric local instance",
    );
    accepted(fixture!("instance_class"));
    accepted(fixture!("instance_disabled_true"));
}

#[test]
fn local_class_aliases_are_refused_before_tactic_let_reduction() {
    macro_rules! alias_fixture {
        ($name:literal) => {
            include_str!(concat!(
                "../../../reports/local-function-headers-2026-11-06/class-alias/",
                $name,
                ".lean"
            ))
        };
    }
    for source in [
        alias_fixture!("let_alias_tactic_have"),
        alias_fixture!("have_alias_tactic_have"),
        alias_fixture!("let_alias_forall"),
        alias_fixture!("have_alias_forall"),
        alias_fixture!("let_alias_nonclass"),
        alias_fixture!("transitive_let_alias"),
        alias_fixture!("semireducible_alias"),
    ] {
        refused(
            source,
            "invalid binder annotation, type is not a class instance",
        );
    }
    accepted(alias_fixture!("disabled_nonclass"));
}

#[test]
fn local_function_headers_validate_without_changing_explicit_lambdas() {
    for source in [
        local_fixture!("let_nonclass"),
        local_fixture!("let_typed_nonclass"),
        local_fixture!("have_nonclass"),
        local_fixture!("let_rec_nonclass"),
        local_fixture!("let_rec_equation_nonclass"),
        local_fixture!("where_unused_nonclass"),
        local_fixture!("where_used_nonclass"),
        local_fixture!("escaped_header_nonclass"),
        local_fixture!("expr_let_nonclass"),
    ] {
        refused(
            source,
            "invalid binder annotation, type is not a class instance",
        );
    }
    refused(
        local_fixture!("let_parametric_unused"),
        "invalid parametric local instance",
    );
    for source in [
        local_fixture!("let_class"),
        local_fixture!("let_parametric_dependent"),
        local_fixture!("have_class"),
        local_fixture!("have_plain_typed"),
        local_fixture!("have_plain_inferred"),
        local_fixture!("let_rec_class"),
        local_fixture!("where_class"),
        local_fixture!("expr_let_class"),
        local_fixture!("explicit_lambda_nonclass"),
        local_fixture!("explicit_lambda_bool"),
        local_fixture!("nested_lambda_shadow"),
        local_fixture!("escaped_lambda_nonclass"),
        local_fixture!("let_disabled_true"),
        local_fixture!("let_disabled_bool"),
        local_fixture!("have_disabled_true"),
        local_fixture!("have_disabled_bool"),
    ] {
        accepted(source);
    }
}

#[test]
fn do_function_headers_and_mutable_functions_preserve_the_local_boundary() {
    for source in [
        local_fixture!("do_let_nonclass_nat"),
        local_fixture!("do_have_nonclass_nat"),
        local_fixture!("do_let_rec_nonclass_nat"),
        local_fixture!("do_mut_nonclass"),
    ] {
        refused(
            source,
            "invalid binder annotation, type is not a class instance",
        );
    }
    for source in [
        local_fixture!("do_let_class_nat"),
        local_fixture!("do_have_class_nat"),
        local_fixture!("do_let_plain"),
        local_fixture!("do_explicit_lambda_nat"),
        local_fixture!("do_mut_function"),
    ] {
        accepted(source);
    }
}

#[test]
fn macro_and_notation_hygiene_preserve_header_origin_and_lambda_shadowing() {
    for source in [
        local_fixture!("macro_applied_nonclass"),
        local_fixture!("notation_optout_nonclass"),
    ] {
        refused(
            source,
            "invalid binder annotation, type is not a class instance",
        );
    }
    for source in [
        local_fixture!("macro_applied_nested_lambda"),
        local_fixture!("notation_optout_nested_lambda"),
    ] {
        accepted(source);
    }
}

/// These original oracle-accepted sources reach separate pre-existing gaps.
/// Keep them unchanged and make a future closure explicit, rather than count
/// a parsing repair or an applied-macro twin as their source admission.
#[test]
fn original_recursive_equation_and_nullary_macro_refusals_remain_open() {
    refused(
        local_fixture!("let_rec_equation_class"),
        "Unknown identifier: f",
    );
    refused(
        local_fixture!("macro_nested_lambda"),
        "Unknown identifier: goodLocalHeader",
    );
}
