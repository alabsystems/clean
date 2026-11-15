// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_elab::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DriverOptions, EnvironmentSetup, ModuleReport, VerdictKind,
};
use clean_kernel::{Environment, Name};
use std::path::Path;

fn check(source: &str) -> (Environment, ModuleReport) {
    let _lock = module_elaboration_lock();
    let path = Path::new("ArrowDomainFixture.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("environment");
    let _budget = DeclBudgetScope::enter(0);
    let parsed = parse_module(path, source).1.expect("fixture parses");
    let mut context = module_file_context(path);
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut context,
        DriverOptions::default(),
        &mut (),
    );
    (env, report)
}

#[test]
fn codomains_resolve_blocked_arrow_domains() {
    let (env, report) = check(include_str!(
        "fixtures/arrow_domain_inference/positive.lean"
    ));
    assert!(!report.verdicts.is_empty());
    for verdict in &report.verdicts {
        assert_eq!(verdict.kind, VerdictKind::Passed, "{verdict:#?}");
    }
    for name in ["emptyProof", "sameProof", "scopedProof", "rowProof"] {
        let name = Name::from_string(name);
        let constant = env.get_const(&name).expect("proof definition registered");
        assert!(
            constant.value.is_some(),
            "{name} must contain its proof term"
        );
        assert!(env.axiom_deps(&name).expect("axiom closure").is_empty());
    }
}

#[test]
fn unresolved_and_wrong_receivers_do_not_gain_acceptance() {
    for (name, source) in [
        (
            "BadDomain",
            include_str!("fixtures/arrow_domain_inference/not_a_type.lean"),
        ),
        (
            "WrongReceiver",
            include_str!("fixtures/arrow_domain_inference/wrong_receiver.lean"),
        ),
        (
            "unpinned",
            include_str!("fixtures/arrow_domain_inference/unpinned.lean"),
        ),
        (
            "futureShadow",
            include_str!("fixtures/arrow_domain_inference/future_shadow.lean"),
        ),
    ] {
        let (env, report) = check(source);
        let verdict = report
            .verdicts
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("{name} was not attempted: {report:#?}"));
        assert_eq!(verdict.kind, VerdictKind::ElaborationFailed, "{verdict:#?}");
        if name == "BadDomain" {
            assert!(
                verdict
                    .detail
                    .as_deref()
                    .is_some_and(|d| d.contains("opaque type variable")),
                "the failed retry must preserve the original receiver error: {verdict:#?}"
            );
        }
        assert!(
            verdict
                .detail
                .as_deref()
                .is_some_and(|d| d.contains("length")),
            "{verdict:#?}"
        );
        assert!(env.get_const(&Name::from_string(name)).is_none(), "{name}");
    }
}

#[test]
fn false_constructor_proof_is_still_refused() {
    let (env, report) = check(include_str!(
        "fixtures/arrow_domain_inference/false_proof.lean"
    ));
    assert!(env
        .get_constructor(&Name::from_string("EmptyList.intro"))
        .is_some());
    let verdict = report
        .verdicts
        .iter()
        .find(|v| v.name == "falseProof")
        .expect("false proof was attempted");
    assert_eq!(verdict.kind, VerdictKind::ElaborationFailed, "{verdict:#?}");
    assert!(env.get_const(&Name::from_string("falseProof")).is_none());
}
