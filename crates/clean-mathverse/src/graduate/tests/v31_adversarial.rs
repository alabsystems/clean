// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// v3.1 adversarial vectors for carried theorems: candidate-reference cycle
// (fail closed), pre-v3.1 schema honesty, coordinated forgery of an
// axiom-dependent carried theorem, single-file tamper evidence,
// serialization byte-invisibility.

/// Forged `carried_theorems` entry claiming the value-typechecked
/// KernelVerified verdict and a foundational-only closure, no matter what
/// the shard actually contains.
fn forged_carried_theorem_entry(
    name: &str,
    type_: &Expr,
    value: &Expr,
    required_by: &[&str],
) -> CarriedTheorem {
    CarriedTheorem {
        name: name.to_string(),
        decl_kind: "theorem".to_string(),
        statement_hash: expr_canonical_digest(type_).expect("hash type"),
        proof_hash: expr_canonical_digest(value).expect("hash value"),
        kernel: KernelFacts {
            verdict: KernelVerdict::KernelVerified, // the lie
            value_typechecked: true,
            family_checked: false,
            checker: "forged".to_string(),
        },
        axiom_closure: AxiomClosure {
            foundational_only: true, // the lie
            domain_axioms: Vec::new(),
            axiom_profile_bits: 0,
        },
        novelty: NoveltyFacts {
            method: "name+statement-hash".to_string(),
            verdict: NoveltyVerdict::New,
            matched_name: None,
            match_kind: None,
        },
        required_by: required_by.iter().map(|s| (*s).to_string()).collect(),
    }
}

#[test]
fn test_graduate_v31_carried_theorem_citing_candidate_cycle_fails_closed() {
    // ADVERSARIAL: a carried theorem whose proof references the CANDIDATE
    // being evaluated (a reference cycle, injectable only via the structural
    // test path) has no dependency order — it must be REJECTED with an
    // audited `dependency-cycle` reason, never looped on, never carried.
    const CYC_THM_A: &str = "GradPilot.cyc_thm_a";
    const CYC_THM_B: &str = "GradPilot.cyc_thm_b";

    let mut env = Environment::new();
    env.add_decl_structural(theorem(
        CYC_THM_A,
        imp_self_type(),
        imp_self_value_discarding(CYC_THM_B, imp_self_type()),
    ))
    .expect("structural cycle fixture a");
    env.add_decl_structural(theorem(
        CYC_THM_B,
        imp_self_type(),
        imp_self_value_discarding(CYC_THM_A, imp_self_type()),
    ))
    .expect("structural cycle fixture b");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[CYC_THM_A]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    assert!(record.carried_theorems.is_empty());
    let thm = entry(&record, CYC_THM_A);
    assert!(!thm.accepted);
    assert!(
        thm.reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("dependency-cycle")
                && r.contains(CYC_THM_A)
                && r.contains(CYC_THM_B)),
        "the candidate cycle must be rejected with both participants audited: {:?}",
        thm.reject_reason
    );

    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_cake_gate_rejects_pre_v31_schema_record_with_carried_theorems() {
    // Schema honesty: a coordinated forgery that lists carried_theorems
    // under a legacy v3 schema label must fail record consistency —
    // pre-v3.1 gates never carried theorems, so the claim is a lie about
    // provenance even when the content would replay.
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let helper_idx = builder
        .add_declaration(&theorem(HELPER_THM, imp_self_type(), imp_self_value()), &[])
        .expect("forged helper export");
    let user_idx = builder
        .add_declaration(
            &theorem(
                USES_HELPER,
                uses_helper_type(),
                uses_helper_value_citing(HELPER_THM),
            ),
            &[],
        )
        .expect("forged user export");
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION_V3);
    let mut user_entry =
        forged_accepted_entry(USES_HELPER, &uses_helper_type(), &imp_self_value(), &[]);
    user_entry.carried_theorems = vec![HELPER_THM.to_string()];
    record.theorems = vec![user_entry];
    record.carried_theorems = vec![forged_carried_theorem_entry(
        HELPER_THM,
        &imp_self_type(),
        &imp_self_value(),
        &[USES_HELPER],
    )];
    record.result.accepted = vec![USES_HELPER.to_string()];

    let shard_path = tmp.path().join("forged-graduated.mathverse");
    forge_bindings_and_write(
        &mut builder,
        &mut record,
        &[(helper_idx, HELPER_THM), (user_idx, USES_HELPER)],
        &shard_path,
    );

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            CakeGateViolation::RecordInconsistent { reason, .. }
                if reason.contains("pre-v3.1-schema record lists carried_theorems")
        )),
        "pre-v3.1 schema with carried_theorems must fail consistency: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_coordinated_forgery_of_axiom_dependent_carried_theorem() {
    // ADVERSARIAL: fully self-consistent v3.1 paperwork claiming a
    // foundational-only carried theorem whose proof actually cites a domain
    // axiom. The axiom cannot be in the shard (the gate admits only
    // theorems/definitions/family members), so the live kernel replay
    // fail-closes — paperwork can never launder the verdict.
    let tmp = tempfile::tempdir().expect("tempdir");
    let smuggler_value = Expr::const_str(BAD_AXIOM);
    let user_value = imp_self_value_discarding(SMUGGLER_THM, bad_axiom_type());

    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let smuggler_idx = builder
        .add_declaration(
            &theorem(SMUGGLER_THM, bad_axiom_type(), smuggler_value.clone()),
            &[],
        )
        .expect("forged smuggler export");
    let user_idx = builder
        .add_declaration(
            &theorem(USES_HELPER, imp_self_type(), user_value.clone()),
            &[],
        )
        .expect("forged user export");
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION);
    let mut user_entry = forged_accepted_entry(USES_HELPER, &imp_self_type(), &user_value, &[]);
    user_entry.carried_theorems = vec![SMUGGLER_THM.to_string()];
    record.theorems = vec![user_entry];
    record.carried_theorems = vec![forged_carried_theorem_entry(
        SMUGGLER_THM,
        &bad_axiom_type(),
        &smuggler_value,
        &[USES_HELPER],
    )];
    record.result.accepted = vec![USES_HELPER.to_string()];

    let shard_path = tmp.path().join("forged-graduated.mathverse");
    forge_bindings_and_write(
        &mut builder,
        &mut record,
        &[(smuggler_idx, SMUGGLER_THM), (user_idx, USES_HELPER)],
        &shard_path,
    );

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        !report.is_clean(),
        "an axiom-dependent carried theorem must fail the replay clause"
    );
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            CakeGateViolation::KernelRejected { name, .. } if name == SMUGGLER_THM
        )),
        "the kernel replay must reject the smuggled proof (its axiom is not \
         in the shard): {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_tampered_carried_theorem_record() {
    // Single-file tamper: editing a carried_theorems entry (here the proof
    // hash) must break the record's binding digest.
    let mut env = Environment::new();
    env.add_decl(theorem(HELPER_THM, imp_self_type(), imp_self_value()))
        .expect("helper lemma must kernel-check");
    env.add_decl(theorem(
        USES_HELPER,
        uses_helper_type(),
        uses_helper_value_citing(HELPER_THM),
    ))
    .expect("uses_helper must kernel-check");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_HELPER]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");
    let shard_path = out.join(&record.result.shard_filename);
    let record_path = graduation_record_path(&shard_path);

    let mut tampered = GraduationRecord::from_file(&record_path).expect("read record");
    tampered.carried_theorems[0].proof_hash = "blake3:forged".to_string();
    tampered
        .write_to_file(&record_path)
        .expect("write tampered record");

    let report = verify_cake_shard(&shard_path).expect("gate runs on tampered record");
    assert!(
        report
            .violations
            .iter()
            .any(|v| matches!(v, CakeGateViolation::MissingGraduationNote { .. })),
        "tampered carried_theorems entry must break the binding digest; violations: {:?}",
        report.violations
    );
}

#[test]
fn test_carried_theorems_empty_is_byte_invisible() {
    // v1/v2/v3 byte stability: empty `carried_theorems` must vanish from
    // both the record and the per-theorem serialization, so legacy binding
    // digests are reproduced byte-for-byte under the v3.1 serializer (the
    // committed-artifact gate tests pin the same property end-to-end).
    let record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION_V3);
    let json = serde_json::to_value(&record).expect("serialize record");
    assert!(
        json.get("carried_theorems").is_none(),
        "empty carried_theorems must be skipped: {json}"
    );
    let entry = forged_accepted_entry(IMP_SELF, &imp_self_type(), &imp_self_value(), &[]);
    let json = serde_json::to_value(&entry).expect("serialize entry");
    assert!(
        json.get("carried_theorems").is_none(),
        "empty per-theorem carried_theorems must be skipped: {json}"
    );
}
