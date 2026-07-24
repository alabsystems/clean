// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// Intake-side rejections: missing kernel certificate, certificate mismatch, rejected-dependency policy, axiom-profile honesty.

// ---------------------------------------------------------------------------
// Negative: missing kernel certificate (theorem without proof value)
// ---------------------------------------------------------------------------

#[test]
fn test_graduate_without_kernel_certificate_rejected() {
    // Two ways a candidate can lack a kernel certificate, both fail-closed:
    //
    // 1. An axiom (no proof value at all) — rejected `not-a-theorem`.
    // 2. A theorem whose stored proof value does NOT re-check — the project
    //    claims a proof, but the fresh-environment `add_decl` replay rejects
    //    it. The bogus theorem enters the fixture env via
    //    `add_decl_structural` (test-only; this is precisely the laundering
    //    path the intake gate exists to close).
    let mut env = pilot_env();
    env.add_decl_structural(theorem(
        UNCHECKED,
        imp_self_type(),
        Expr::prop(), // Prop : Type — not a proof of `∀ p, p → p`
    ))
    .expect("structural bogus-theorem fixture");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[BAD_AXIOM, UNCHECKED]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    let axiom = entry(&record, BAD_AXIOM);
    assert!(!axiom.accepted);
    assert_eq!(axiom.kernel.verdict, KernelVerdict::Rejected);
    assert!(axiom
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.contains("not-a-theorem")));

    let bogus = entry(&record, UNCHECKED);
    assert!(!bogus.accepted);
    assert_eq!(bogus.kernel.verdict, KernelVerdict::Rejected);
    assert!(
        !bogus.kernel.value_typechecked,
        "a value the kernel rejected must never count as type-checked"
    );
    assert!(bogus
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.starts_with("kernel-rejected")));
    assert!(record.result.accepted.is_empty());
}

// ---------------------------------------------------------------------------
// Negative: certificate cross-check mismatch
// ---------------------------------------------------------------------------

#[test]
fn test_graduate_certificate_proof_hash_mismatch_rejected() {
    let env = pilot_env();
    let mut req = pilot_request();
    req.certificate_cross_checks = vec![CertificateCrossCheck {
        theorem: IMP_TRANS.to_string(),
        proof_hash: "blake3:not-the-real-proof-hash".to_string(),
    }];
    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[IMP_TRANS]),
        &req,
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");
    let rejected = entry(&record, IMP_TRANS);
    assert!(!rejected.accepted);
    assert!(rejected
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.starts_with("certificate-mismatch")));
}

// ---------------------------------------------------------------------------
// Dependency policy: external definition-valued deps are rejected
// ---------------------------------------------------------------------------

#[test]
fn test_graduate_rejects_dependent_of_rejected_candidate() {
    // bad_dependent is rejected with a NON-carryable defect (axiom-dependent
    // closure); a later candidate citing it must be rejected as
    // rejected-dependency — there is no kernel-clean object to put in the
    // shard. (Duplicate-POLICY rejections are the carryable exception: see
    // test_graduate_v31_dependent_of_duplicate_rejected_candidate_graduates.)
    let mut env = pilot_env();
    env.add_decl(theorem(
        "GradPilot.cites_bad_dependent",
        imp_self_type(),
        Expr::app(
            Expr::lam(bd(), bad_axiom_type(), imp_self_value()),
            Expr::const_str(BAD_DEPENDENT),
        ),
    ))
    .expect("cites_bad_dependent must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let baseline_dir = tmp.path().join("baseline");
    std::fs::create_dir_all(&baseline_dir).expect("baseline dir");
    let baseline = pilot_baseline(&baseline_dir);
    let record = graduate(
        &env,
        &names(&[BAD_DEPENDENT, "GradPilot.cites_bad_dependent"]),
        &pilot_request(),
        &baseline,
        &tmp.path().join("out"),
    )
    .expect("graduation runs");

    let rejected = entry(&record, BAD_DEPENDENT);
    assert!(!rejected.accepted);
    assert!(rejected
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.starts_with("axiom-dependent")));
    let dependent = entry(&record, "GradPilot.cites_bad_dependent");
    assert!(!dependent.accepted);
    assert!(dependent
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.starts_with("rejected-dependency")));
    assert!(
        record.carried_theorems.is_empty(),
        "an axiom-dependent rejected candidate must never be carried"
    );
}

// ---------------------------------------------------------------------------
// Profile honesty: NNVerify-prefixed names must not inherit heuristic bits
// ---------------------------------------------------------------------------

#[test]
fn test_graduate_nnverify_named_theorem_writes_empty_axiom_profile() {
    // `KernelShardBuilder::add_declaration` stamps name-heuristic content
    // bits (FLOAT_APPROX | NN_ABSTRACTION) on `NNVerify.*` names. A graduated
    // theorem's in-shard profile must instead carry the gate-derived facts
    // (foundational-only ⇒ NONE), or the produced shard fails the verb's own
    // cake gate (`NonEmptyAxiomProfile`). Regression for GRADUATION #1, where
    // 4 accepted `NNVerify.Nat.*` theorems made the CLI fail closed.
    const NN_NAME: &str = "NNVerify.GradPilot.imp_trans";
    let mut env = Environment::new();
    env.add_decl(theorem(NN_NAME, imp_trans_type(), imp_trans_value()))
        .expect("NNVerify-named imp_trans must kernel-check");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[NN_NAME]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");
    assert_eq!(record.result.accepted, vec![NN_NAME.to_string()]);

    let shard_path = out.join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read graduated shard");
    let (_idx, header) = reader
        .lookup_name(NN_NAME)
        .expect("NNVerify-named theorem must be in the graduated shard");
    assert_eq!(
        header.axiom_profile.0, 0,
        "graduated shard must carry the gate-derived (empty) axiom profile, \
         not add_declaration's name-heuristic bits"
    );

    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "NNVerify-named graduated shard must pass the cake gate; violations: {:?}",
        report.violations
    );
}
