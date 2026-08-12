// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_verify::test_utils::build_spec_with_stack;
use clean_verify::{ProofLibrary, ProofStatus};

// 2026-07-31: no test in this file currently asserts a `DerivedPending`
// provenance — every case here is on the `assert_proved_no_deps` side. Kept
// (not deleted) because the two helpers are the matched pair this file's
// contract is written against: a provenance test that lands on the pending
// side needs this exact assertion, and re-deriving it is how drift starts.
#[allow(dead_code)]
fn assert_pending_deps(
    report: &clean_verify::DependencyAuditReport,
    proof_name: &str,
    expected_deps: &[&str],
) {
    let result = report
        .results
        .get(proof_name)
        .unwrap_or_else(|| panic!("{proof_name} should have a dependency result"));

    assert_eq!(
        result.status,
        ProofStatus::DerivedPending,
        "{proof_name} should stay DerivedPending while it depends on helper axioms"
    );

    for dep in expected_deps {
        assert!(
            result.axiom_deps.contains(*dep),
            "{proof_name} should depend on {dep}, got: {:?}",
            result.axiom_deps
        );
    }

    assert!(
        result.error.is_none(),
        "{proof_name} should not have an audit error: {:?}",
        result.error
    );
}

fn assert_proved_no_deps(report: &clean_verify::DependencyAuditReport, proof_name: &str) {
    let result = report
        .results
        .get(proof_name)
        .unwrap_or_else(|| panic!("{proof_name} should have a dependency result"));

    assert_eq!(
        result.status,
        ProofStatus::DerivedProved,
        "{proof_name} should be DerivedProved with no helper-axiom closure, got deps: {:?}",
        result.axiom_deps
    );
    assert!(
        result.axiom_deps.is_empty(),
        "{proof_name} should have an empty helper-axiom closure, got: {:?}",
        result.axiom_deps
    );
    assert!(
        result.error.is_none(),
        "{proof_name} should not have an audit error: {:?}",
        result.error
    );
}

#[test]
fn test_audit_dependencies_definitional_extension_layers() {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    // The intro rules' former side-condition HelperAxioms were all DRAINED to
    // computable defs / the real algorithm (FreshDeclName in e7553776;
    // StrictlyPositiveCtorDecls + WellFormedCtorDecls in the faithful
    // positivity/wf drain), so the intro rules now audit clean.
    assert_proved_no_deps(&report, "constant_extension_intro");
    assert_proved_no_deps(&report, "inductive_extension_intro");

    // The soundness lemmas no longer rest on helper axioms: EnvSound is now a
    // faithful definition (DefinitionalExtension KEnv.empty env) and the two step
    // lemmas are derived from the FoundationalRule extension constructors, so the
    // whole soundness chain audits clean as DerivedProved with no helper-axiom
    // closure.
    assert_proved_no_deps(&report, "constant_extension_soundness");
    assert_proved_no_deps(&report, "inductive_extension_soundness");
    assert_proved_no_deps(&report, "definitional_extension_soundness");
}
