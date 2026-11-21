// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_elab::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DriverOptions, EnvironmentSetup, FailureIsolation, ModuleReport, VerdictKind,
};
use clean_kernel::{Declaration, Environment, Expr, Name, TypeChecker};
use std::path::Path;

fn check(source: &str, isolation: FailureIsolation) -> (ModuleReport, Environment) {
    let _lock = module_elaboration_lock();
    let path = Path::new("CompilerEligibility.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("source environment");
    let parsed = parse_module(path, source).1.expect("source parses");
    assert!(parsed.diagnostics.is_empty(), "{:#?}", parsed.diagnostics);
    let mut context = module_file_context(path);
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut context,
        DriverOptions {
            lean_front_door: true,
            isolation,
            ..DriverOptions::default()
        },
        &mut (),
    );
    (report, env)
}

#[test]
fn compiler_error_retains_a_genuine_kernel_checked_declaration() {
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        for source in [
            include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/runtime-axiom.lean"),
            include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/noncomputable-dependency.lean"),
        ] {
            let (report, env) = check(source, isolation);
            let bad = report.verdicts.iter().find(|v| v.name == "bad").expect("bad verdict");
            assert_eq!(bad.kind, VerdictKind::SourceError, "{report:#?}");
            assert!(bad.detail.as_deref().is_some_and(|s| s.contains("noncomputable")));
            assert_eq!(report.verdicts.iter().filter(|v| v.kind.is_failure()).count(), 1,
                "the following #check must still see bad: {report:#?}");
            assert!(env.is_noncomputable(&Name::from_string("bad")));
            let declaration = env.get_const(&Name::from_string("bad")).expect("registered bad");
            let value = declaration.value.as_ref().expect("actual value, not an axiom substitute");
            TypeChecker::new(&env).check_type(value, &declaration.type_).expect("real kernel check");
        }
    }
}

#[test]
fn erased_values_and_foreign_code_remain_accepted() {
    for source in [
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/axiom-type-erased.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/proof-axiom-erased.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/erased-type-argument.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/erased-proof-argument.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/erased-proof-let.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/extern-axiom.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/foreign-definition.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/implemented-definition.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/fixtures/noncomputable-exemption.lean"),
    ] {
        let (report, _) = check(source, FailureIsolation::Keep);
        assert!(!report.verdicts.is_empty());
        assert!(report.verdicts.iter().all(|v| v.kind == VerdictKind::Passed), "{source}\n{report:#?}");
    }
}

#[test]
fn noncomputable_section_marks_real_dependencies_and_preserves_continuation() {
    let (report, env) = check(
        include_str!(
            "../../../reports/compiler-eligibility-2026-11-13/fixtures/noncomputable-section.lean"
        ),
        FailureIsolation::Keep,
    );
    assert!(env.is_noncomputable(&Name::from_string("marked")));
    assert_eq!(
        report
            .verdicts
            .iter()
            .filter(|v| v.kind.is_failure())
            .count(),
        1,
        "{report:#?}"
    );
    assert_eq!(
        report
            .verdicts
            .iter()
            .find(|v| v.name == "bad")
            .expect("bad")
            .kind,
        VerdictKind::SourceError
    );
    assert!(env.get_const(&Name::from_string("bad")).is_some());
}

#[test]
fn nested_source_error_keeps_its_own_line_and_all_registered_values() {
    let (report, env) = check(
        include_str!("../../../reports/compiler-eligibility-2026-11-13/more/nested.lean"),
        FailureIsolation::Rollback,
    );
    let bad = report
        .verdicts
        .iter()
        .find(|v| v.name == "T.bad")
        .expect("nested bad");
    assert_eq!(bad.kind, VerdictKind::SourceError);
    assert_eq!(bad.line, Some(3));
    assert_eq!(
        report
            .verdicts
            .iter()
            .filter(|v| v.kind.is_failure())
            .count(),
        1,
        "{report:#?}"
    );
    assert!(env.get_const(&Name::from_string("T.still_here")).is_some());
}

#[test]
fn matching_guard_consumes_the_source_error_and_keeps_the_declaration() {
    let (report, env) = check(
        include_str!("../../../reports/compiler-eligibility-2026-11-13/more/guard-expected.lean"),
        FailureIsolation::Keep,
    );
    assert!(
        report.verdicts.iter().all(|v| !v.kind.is_failure()),
        "{report:#?}"
    );
    assert!(report.verdicts.iter().any(|v| v.name == "bad"));
    let bad = env
        .get_const(&Name::from_string("bad"))
        .expect("guard declaration retained");
    TypeChecker::new(&env)
        .check_type(bad.value.as_ref().expect("real bad value"), &bad.type_)
        .expect("guard does not replace the value or skip its kernel check");
}

#[test]
fn failed_compilation_marks_callers_without_losing_their_values() {
    let (report, env) = check(
        include_str!(
            "../../../reports/compiler-eligibility-2026-11-13/more/failure-continuation.lean"
        ),
        FailureIsolation::Keep,
    );
    assert_eq!(
        report
            .verdicts
            .iter()
            .filter(|v| v.kind.is_failure())
            .count(),
        2,
        "{report:#?}"
    );
    for name in ["bad", "later"] {
        let name = Name::from_string(name);
        assert!(env.is_noncomputable(&name));
        let info = env.get_const(&name).expect("real declaration retained");
        TypeChecker::new(&env)
            .check_type(info.value.as_ref().expect("real value"), &info.type_)
            .expect("kernel checks the retained value");
    }
}

#[test]
fn mismatching_guard_keeps_registered_values_under_rollback_isolation() {
    let (report, env) = check(
        include_str!(
            "../../../reports/compiler-eligibility-2026-11-13/more/guard-mismatch-retains.lean"
        ),
        FailureIsolation::Rollback,
    );
    assert_eq!(
        report
            .verdicts
            .iter()
            .filter(|v| v.kind.is_failure())
            .count(),
        2,
        "{report:#?}"
    );
    assert!(env.get_const(&Name::from_string("bad")).is_some());
    assert!(report
        .verdicts
        .iter()
        .any(|v| v.name == "#guard_msgs" && v.kind == VerdictKind::SourceError));
}

#[test]
fn executable_placeholder_metadata_never_launders_sorry_debt_or_permits_evaluation() {
    let (report, env) = check(
        include_str!(
            "../../../reports/compiler-eligibility-2026-11-13/extras/sorry-definition.lean"
        ),
        FailureIsolation::Keep,
    );
    assert!(
        report.verdicts.iter().any(|v| matches!(
            v.kind,
            VerdictKind::TrustDebt(clean_elab::RegistrationWarningKind::ExplicitSorry)
        )),
        "{report:#?}"
    );
    assert!(
        !report.verdicts.iter().any(|v| v.kind.is_failure()),
        "{report:#?}"
    );
    assert!(env.get_const(&Name::from_string("placeholder")).is_some());

    let (report, _) = check(
        include_str!("../../../reports/compiler-eligibility-2026-11-13/extras/eval-sorry.lean"),
        FailureIsolation::Keep,
    );
    assert!(
        report.verdicts.iter().any(|v| v.kind.is_failure()
            && v.detail
                .as_deref()
                .is_some_and(|message| message.contains("depends on the 'sorry' axiom"))),
        "{report:#?}"
    );
}

#[test]
fn a_source_error_is_still_failure_when_the_value_also_has_sorry_debt() {
    let (report, env) = check(
        include_str!("../../../reports/compiler-eligibility-2026-11-13/special/mixed-debt.lean"),
        FailureIsolation::Keep,
    );
    let bad = report
        .verdicts
        .iter()
        .find(|v| v.name == "bad")
        .expect("bad verdict");
    assert_eq!(bad.kind, VerdictKind::SourceError, "{report:#?}");
    assert!(
        bad.kind.is_failure(),
        "allowing sorry must not consume a compiler error"
    );
    let warning =
        clean_elab::register::registration_warning_for_name(&env, &Name::from_string("bad"))
            .expect("sorry debt is preserved independently of source diagnostics");
    assert_eq!(
        warning.kind,
        clean_elab::RegistrationWarningKind::ExplicitSorry
    );
}

#[test]
fn ordinary_runtime_definitions_preserve_their_real_implementations() {
    for source in [
        include_str!("../../../reports/compiler-eligibility-2026-11-13/positive-runtime/float-add.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/positive-runtime/float-conversion.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/positive-runtime/word-add.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/positive-runtime/nat-conversion.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/positive-runtime/string-append.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/positive-runtime/io-print.lean"),
        include_str!("../../../reports/compiler-eligibility-2026-11-13/special/io-print-argument.lean"),
    ] {
        let (report, env) = check(source, FailureIsolation::Keep);
        assert_eq!(report.verdicts.len(), 1, "{report:#?}");
        assert_eq!(report.verdicts[0].kind, VerdictKind::Passed, "{source}\n{report:#?}");
        let declaration = env.get_const(&Name::from_string(&report.verdicts[0].name))
            .expect("real declaration");
        TypeChecker::new(&env).check_type(declaration.value.as_ref().expect("real value"), &declaration.type_)
            .expect("kernel checks the accepted definition");
    }
}

#[test]
fn an_unprovided_user_axiom_with_an_io_name_still_has_no_code() {
    let _lock = module_elaboration_lock();
    let path = Path::new("UserIoName.lean");
    let source = "def bad (s : String) : IO Unit := IO.println s\n";
    let mut env = Environment::with_prelude();
    // F3 keeps IO out of the default prelude. Provide only the logical type
    // for this counterexample, never the native IO operation provider.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("IO"),
        level_params: Vec::new(),
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .expect("explicit logical IO type without runtime code");
    assert!(!env.has_io_ops(), "the IO code provider is not installed");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("IO.println"),
        level_params: Vec::new(),
        type_: Expr::arrow(
            Expr::const_(Name::from_string("String"), Vec::new()),
            Expr::app(
                Expr::const_(Name::from_string("IO"), Vec::new()),
                Expr::const_(Name::from_string("Unit"), Vec::new()),
            ),
        ),
    })
    .expect("a logical axiom does not install runtime code");
    let parsed = parse_module(path, source).1.expect("source parses");
    assert!(parsed.diagnostics.is_empty());
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut module_file_context(path),
        DriverOptions {
            lean_front_door: true,
            ..DriverOptions::default()
        },
        &mut (),
    );
    assert_eq!(
        report
            .verdicts
            .iter()
            .find(|v| v.name == "bad")
            .expect("bad verdict")
            .kind,
        VerdictKind::SourceError,
        "{report:#?}"
    );
    assert!(
        !env.has_io_ops(),
        "a user axiom must not install runtime code"
    );
}

#[test]
fn sibling_binder_bodies_cannot_reuse_a_visited_temporary_address() {
    for source in [
        include_str!(
            "../../../reports/compiler-eligibility-2026-11-13/more/sibling-lambda-axiom.lean"
        ),
        include_str!(
            "../../../reports/compiler-eligibility-2026-11-13/more/sibling-let-axiom.lean"
        ),
    ] {
        for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
            let (report, env) = check(source, isolation);
            let bad = report
                .verdicts
                .iter()
                .find(|v| v.name == "bad")
                .expect("bad");
            assert_eq!(bad.kind, VerdictKind::SourceError, "{source}\n{report:#?}");
            assert!(bad
                .detail
                .as_deref()
                .is_some_and(|s| s.contains("`a`") || s.contains("'a'")));
            assert_eq!(
                report
                    .verdicts
                    .iter()
                    .filter(|v| v.kind.is_failure())
                    .count(),
                1,
                "the later #check retains the real declaration: {report:#?}"
            );
            let bad = env
                .get_const(&Name::from_string("bad"))
                .expect("registered bad");
            TypeChecker::new(&env)
                .check_type(bad.value.as_ref().expect("actual value"), &bad.type_)
                .expect("the compilation error does not replace the kernel value");
        }
    }
}

#[test]
fn csimp_compiler_heads_preserve_original_values_and_positive_acceptance() {
    for case in ["axiom", "noncomputable", "chain", "unused-cycle"] {
        let source = std::fs::read_to_string(format!(
            "{}/../../reports/compiler-eligibility-2026-11-13/review/csimp-{case}.lean",
            env!("CARGO_MANIFEST_DIR")
        ))
        .expect("fixture");
        let (report, env) = check(&source, FailureIsolation::Keep);
        assert!(
            report.verdicts.iter().all(|v| !v.kind.is_failure()),
            "{case}\n{report:#?}"
        );
        let consumer = env
            .get_const(&Name::from_string("consumer"))
            .expect("consumer");
        let value = consumer.value.as_ref().expect("logical value");
        TypeChecker::new(&env)
            .check_type(value, &consumer.type_)
            .expect("actual kernel value");
        if case != "unused-cycle" {
            let mut constants = std::collections::HashSet::new();
            value.collect_constants_into(&mut constants);
            assert!(
                constants.contains(&Name::from_string("source")),
                "compiler replacement must not rewrite the logical value"
            );
        }
    }
}

#[test]
fn csimp_does_not_hide_unavailable_targets_arguments_or_cycles() {
    for (case, dependency) in [
        ("target-noncomputable", "target"),
        ("runtime-argument", "missing"),
        ("cycle", "cycle"),
    ] {
        let source = std::fs::read_to_string(format!(
            "{}/../../reports/compiler-eligibility-2026-11-13/review/csimp-{case}.lean",
            env!("CARGO_MANIFEST_DIR")
        ))
        .expect("fixture");
        let (report, env) = check(&source, FailureIsolation::Rollback);
        let consumer = report
            .verdicts
            .iter()
            .find(|v| v.name == "consumer")
            .expect("consumer");
        assert_eq!(
            consumer.kind,
            VerdictKind::SourceError,
            "{case}\n{report:#?}"
        );
        assert!(
            consumer
                .detail
                .as_deref()
                .is_some_and(|s| s.contains(dependency)),
            "{report:#?}"
        );
        assert!(env.get_const(&Name::from_string("consumer")).is_some());
        assert_eq!(
            report
                .verdicts
                .iter()
                .filter(|v| v.kind.is_failure())
                .count(),
            1,
            "{report:#?}"
        );
    }
}

#[test]
fn csimp_cutoffs_and_local_visibility_do_not_retroactively_repair_a_body() {
    for (case, good, bad) in [("late", "late", "early"), ("local", "inside", "outside")] {
        let source = std::fs::read_to_string(format!(
            "{}/../../reports/compiler-eligibility-2026-11-13/review/csimp-{case}.lean",
            env!("CARGO_MANIFEST_DIR")
        ))
        .expect("fixture");
        let (report, env) = check(&source, FailureIsolation::Keep);
        assert_eq!(
            report
                .verdicts
                .iter()
                .find(|v| v.name == good)
                .expect("good")
                .kind,
            VerdictKind::Passed,
            "{report:#?}"
        );
        assert_eq!(
            report
                .verdicts
                .iter()
                .find(|v| v.name == bad)
                .expect("bad")
                .kind,
            VerdictKind::SourceError,
            "{report:#?}"
        );
        for (name, expected) in [(good, true), (bad, false)] {
            let rules = clean_kernel::env::csimp::rules_for(&env, Some(&Name::from_string(name)));
            assert_eq!(
                rules.iter().any(|r| r.from == Name::from_string("source")),
                expected,
                "{case}/{name}"
            );
        }
        assert_eq!(
            report
                .verdicts
                .iter()
                .filter(|v| v.kind.is_failure())
                .count(),
            1,
            "{report:#?}"
        );
    }
}

#[test]
fn source_init_retains_nat_recursor_compiler_replacement() {
    let choice = clean_olean::source_world_for_file(
        Path::new("CompilerEligibility.lean"),
        Some(clean_kernel::lean_world::LeanWorld::Lean435),
    )
    .expect("qualified Lean4.35 source world");
    let (env, _) = clean_elab::module_driver::module_environment_with_import_base_in_world(
        EnvironmentSetup::default(),
        &choice,
    )
    .expect("genuine Lean4.35 Init");
    let recursor = Name::from_string("Nat.rec");
    let replacement = clean_compiler::resolve_csimp_reference(&env, None, &recursor)
        .expect("valid imported compiler metadata");
    assert_ne!(replacement, recursor,
        "Lean accepts Nat.rec through its genuine Init CSimp replacement; source eligibility must retain that metadata");
    assert!(
        env.get_const(&replacement)
            .and_then(|c| c.value.as_ref())
            .is_some(),
        "the imported replacement must have a real body"
    );
}

#[test]
fn macro_inline_defers_unused_bodies_but_checks_real_runtime_calls() {
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        for (source, called) in [
            (include_str!("../../../reports/recursor-eligibility-2026-11-13/replacement-controls/deferred-axiom-unused.lean"), false),
            (include_str!("../../../reports/recursor-eligibility-2026-11-13/replacement-controls/deferred-axiom-called.lean"), true),
        ] {
            let (report, env) = check(source, isolation);
            let failures: Vec<_> = report.verdicts.iter().filter(|v| v.kind.is_failure()).collect();
            assert_eq!(failures.len(), usize::from(called), "{report:#?}");
            if called {
                assert_eq!(failures[0].name, "probe");
                assert_eq!(failures[0].kind, VerdictKind::SourceError);
                assert!(failures[0].detail.as_deref().is_some_and(|s| s.contains("missing")));
            }
            let helper = env.get_const(&Name::from_string("deferred")).expect("registered helper");
            let value = helper.value.as_ref().expect("original logical body");
            assert_eq!(value, &Expr::const_str("missing"));
            TypeChecker::new(&env).check_type(value, &helper.type_).expect("kernel value remains valid");
            assert!(!env.is_noncomputable(&Name::from_string("deferred")));
        }
    }
}

#[test]
fn macro_inline_nested_arguments_and_discarded_runtime_arguments_remain_accepted() {
    for source in [
        "@[macro_inline] def identity (n : Nat) : Nat := n\ndef probe : Nat := identity (identity 0)\n",
        "axiom missing : Nat\n@[macro_inline] def ignore (_ : Nat) : Nat := 0\ndef probe : Nat := ignore missing\n",
        "@[macro_inline] def inner (n : Nat) : Nat := n\n@[macro_inline] def outer (n : Nat) : Nat := inner n\ndef probe : Nat := outer (outer 0)\n",
    ] {
        let (report, env) = check(source, FailureIsolation::Keep);
        assert!(!report.verdicts.is_empty());
        assert!(report.verdicts.iter().all(|v| !v.kind.is_failure()), "{source}\n{report:#?}");
        let probe = env.get_const(&Name::from_string("probe")).expect("registered probe");
        TypeChecker::new(&env).check_type(probe.value.as_ref().expect("real body"), &probe.type_)
            .expect("temporary compiler expansion does not replace the kernel value");
    }
}

#[test]
fn macro_inline_partial_caller_functions_preserve_argument_context() {
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        for (source, unavailable) in [
            (include_str!("../../../reports/recursor-eligibility-2026-11-13/macro-partial-controls/partial-function-argument.lean"), false),
            (include_str!("../../../reports/recursor-eligibility-2026-11-13/macro-partial-controls/partial-function-discarded-axiom.lean"), false),
            (include_str!("../../../reports/recursor-eligibility-2026-11-13/macro-partial-controls/partial-function-used-axiom.lean"), true),
        ] {
            let (report, env) = check(source, isolation);
            let failures: Vec<_> = report.verdicts.iter().filter(|v| v.kind.is_failure()).collect();
            assert_eq!(failures.len(), usize::from(unavailable), "{source}\n{report:#?}");
            if unavailable {
                assert_eq!(failures[0].name, "probe", "{report:#?}");
                assert_eq!(failures[0].kind, VerdictKind::SourceError, "{report:#?}");
                assert!(failures[0].detail.as_deref().is_some_and(|message| message.contains("missing") && !message.contains("cyclic")), "{report:#?}");
            } else {
                let probe = env.get_const(&Name::from_string("probe")).expect("registered probe");
                TypeChecker::new(&env).check_type(probe.value.as_ref().expect("logical body"), &probe.type_)
                    .expect("compiler expansion preserves the checked logical value");
            }
        }
    }
}

#[test]
fn macro_inline_and_assumed_csimp_cycles_refuse_without_unbounded_expansion() {
    let source = "def base (n : Nat) : Nat := n\n@[macro_inline] def helper (n : Nat) : Nat := base (n + 1)\n@[csimp] axiom base_eq_helper : base = helper\ndef probe : Nat := helper 0\n";
    let (report, env) = check(source, FailureIsolation::Keep);
    let probe = report
        .verdicts
        .iter()
        .find(|v| v.name == "probe")
        .expect("probe verdict");
    assert_eq!(probe.kind, VerdictKind::SourceError, "{report:#?}");
    assert!(
        probe
            .detail
            .as_deref()
            .is_some_and(|s| s.contains("cyclic macro_inline")),
        "{report:#?}"
    );
    assert!(env
        .get_const(&Name::from_string("probe"))
        .and_then(|info| info.value.as_ref())
        .is_some());
}

#[test]
fn macro_inline_rejects_opaque_declarations_at_registration() {
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        for source in [
            "@[macro_inline] opaque hidden : Nat := 0\n",
            "opaque hidden : Nat := 0\nattribute [macro_inline] hidden\n",
        ] {
            let (report, _) = check(source, isolation);
            assert!(
                report.verdicts.iter().any(|v| v.kind.is_failure()
                    && v.kind != VerdictKind::Diverged
                    && v.detail
                        .as_deref()
                        .is_some_and(|message| message.contains("macro_inline"))),
                "opaque macro-inline must refuse: {source}\n{report:#?}"
            );
        }
    }
}

#[test]
fn macro_inline_manual_recursor_definition_remains_valid() {
    let source = include_str!("../../../reports/recursor-eligibility-2026-11-13/validation-controls/manual-recursor-helper.lean");
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        let (report, env) = check(source, isolation);
        assert!(!report.verdicts.is_empty());
        assert!(
            report
                .verdicts
                .iter()
                .all(|v| v.kind == VerdictKind::Passed),
            "{report:#?}"
        );
        assert!(env.is_macro_inline(&Name::from_string("manual")));
    }
}

#[test]
fn macro_inline_attribute_lists_preserve_written_order() {
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        for (source, macro_enabled) in [
            (include_str!("../../../reports/inline-source-order-2026-11-13/fixtures/list-macro-noinline.lean"), false),
            (include_str!("../../../reports/inline-source-order-2026-11-13/fixtures/list-noinline-macro.lean"), true),
        ] {
            let (report, env) = check(source, isolation);
            let probe = report.verdicts.iter().find(|v| v.name == "probe").expect("probe verdict");
            assert_eq!(probe.kind == VerdictKind::Passed, macro_enabled, "{source}\n{report:#?}");
            assert_eq!(env.is_macro_inline(&Name::from_string("ignore")), macro_enabled);
            assert_eq!(env.is_noinline(&Name::from_string("ignore")), !macro_enabled);
            assert!(report.verdicts.iter().all(|v| v.kind != VerdictKind::Diverged));
        }
    }
}

#[test]
fn macro_inline_caller_time_and_later_mode_override_remain_distinct() {
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        for (source, early_passes) in [
            (
                include_str!(
                    "../../../reports/inline-source-order-2026-11-13/fixtures/caller-time.lean"
                ),
                false,
            ),
            (
                include_str!(
                    "../../../reports/inline-source-order-2026-11-13/fixtures/mode-override.lean"
                ),
                true,
            ),
        ] {
            let (report, env) = check(source, isolation);
            for (name, passes) in [("early", early_passes), ("late", !early_passes)] {
                let verdict = report
                    .verdicts
                    .iter()
                    .find(|v| v.name == name)
                    .expect("caller verdict");
                assert_eq!(
                    verdict.kind == VerdictKind::Passed,
                    passes,
                    "{source}\n{report:#?}"
                );
                assert_eq!(
                    clean_kernel::env::csimp::inline_mode_at(
                        &env,
                        Some(&Name::from_string(name)),
                        &Name::from_string("ignore")
                    ) == Some(clean_kernel::env::csimp::InlineMode::MacroInline),
                    passes
                );
            }
            assert!(report
                .verdicts
                .iter()
                .all(|v| v.kind != VerdictKind::Diverged));
        }
    }
}

#[test]
fn macro_inline_enum_attributes_refuse_local_and_scoped_kinds() {
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        for source in [
            include_str!(
                "../../../reports/inline-source-order-2026-11-13/fixtures/local-macro.lean"
            ),
            include_str!(
                "../../../reports/inline-source-order-2026-11-13/fixtures/scoped-macro.lean"
            ),
            include_str!(
                "../../../reports/inline-source-order-2026-11-13/fixtures/local-noinline.lean"
            ),
        ] {
            let (report, env) = check(source, isolation);
            assert!(
                report.verdicts.iter().any(|v| v.kind.is_failure()
                    && v.kind != VerdictKind::Diverged
                    && v.detail
                        .as_deref()
                        .is_some_and(|message| message.contains("must be global"))),
                "{source}\n{report:#?}"
            );
            assert!(!env.is_macro_inline(&Name::from_string("ignore")));
            assert!(!env.is_macro_inline(&Name::from_string("N.ignore")));
        }
    }
}

#[test]
fn macro_inline_enum_attributes_refuse_declarations_of_another_source_run() {
    let _lock = module_elaboration_lock();
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        for attribute in [
            "inline",
            "noinline",
            "always_inline",
            "macro_inline",
            "inline_if_reduce",
        ] {
            let mut env =
                module_environment(EnvironmentSetup::default()).expect("source environment");
            let run = |env: &mut Environment, path: &Path, source: &str| {
                let parsed = parse_module(path, source).1.expect("source parses");
                assert!(parsed.diagnostics.is_empty());
                elaborate_decls(
                    env,
                    &parsed.decls,
                    source,
                    &mut module_file_context(path),
                    DriverOptions {
                        lean_front_door: true,
                        isolation,
                        ..DriverOptions::default()
                    },
                    &mut (),
                )
            };
            let library = run(
                &mut env,
                Path::new("InlineLib.lean"),
                include_str!(
                    "../../../reports/inline-source-order-2026-11-13/fixtures/InlineLib.lean"
                ),
            );
            assert!(
                library
                    .verdicts
                    .iter()
                    .all(|v| v.kind == VerdictKind::Passed),
                "{library:#?}"
            );
            let report = run(
                &mut env,
                Path::new("ImportedInline.lean"),
                &format!("attribute [{attribute}] InlineLib.ignore\n"),
            );
            assert!(
                report.verdicts.iter().any(|v| v.kind.is_failure()
                    && v.kind != VerdictKind::Diverged
                    && v.detail
                        .as_deref()
                        .is_some_and(|message| message.contains("imported module"))),
                "{attribute}: {report:#?}"
            );
            let name = Name::from_string("InlineLib.ignore");
            assert!(!env.is_inline(&name));
            assert!(!env.is_noinline(&name));
            assert!(!env.is_always_inline(&name));
            assert!(!env.is_macro_inline(&name));
            assert!(!env.is_inline_if_reduce(&name));
        }
    }
}
