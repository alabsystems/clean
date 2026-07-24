// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// Cake-gate unbypassability on genuine artifacts: tampered bytes/record, missing record, hand-rolled shard, tampered carried-definition entry.

// ---------------------------------------------------------------------------
// Gate unbypassability: tamper cases must FAIL
// ---------------------------------------------------------------------------

#[test]
fn test_cake_gate_rejects_tampered_shard_bytes() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let baseline_dir = tmp.path().join("baseline");
    std::fs::create_dir_all(&baseline_dir).expect("baseline dir");
    let record = run_pilot(&out, &baseline_dir);
    let shard_path = out.join(&record.result.shard_filename);

    let mut bytes = std::fs::read(&shard_path).expect("shard bytes");
    let mid = bytes.len() / 2;
    bytes[mid] ^= 0xFF;
    std::fs::write(&shard_path, &bytes).expect("write tampered shard");

    let err = verify_cake_shard(&shard_path).expect_err("tampered shard must fail the gate");
    assert!(
        matches!(err, CakeGateError::ShardDigestMismatch { .. }),
        "expected ShardDigestMismatch, got: {err}"
    );
}

#[test]
fn test_cake_gate_rejects_missing_graduation_record() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let baseline_dir = tmp.path().join("baseline");
    std::fs::create_dir_all(&baseline_dir).expect("baseline dir");
    let record = run_pilot(&out, &baseline_dir);
    let shard_path = out.join(&record.result.shard_filename);

    std::fs::remove_file(graduation_record_path(&shard_path)).expect("delete record");
    let err = verify_cake_shard(&shard_path).expect_err("recordless shard must fail the gate");
    assert!(
        matches!(err, CakeGateError::MissingGraduationRecord(_)),
        "expected MissingGraduationRecord, got: {err}"
    );
}

#[test]
fn test_cake_gate_rejects_tampered_record() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let baseline_dir = tmp.path().join("baseline");
    std::fs::create_dir_all(&baseline_dir).expect("baseline dir");
    let record = run_pilot(&out, &baseline_dir);
    let shard_path = out.join(&record.result.shard_filename);
    let record_path = graduation_record_path(&shard_path);

    // Edit a field the attacker would want to forge (the honesty label).
    let mut tampered = GraduationRecord::from_file(&record_path).expect("read record");
    tampered.provenance.residual_risk = "laundered".to_string();
    tampered
        .write_to_file(&record_path)
        .expect("write tampered record");

    let report = verify_cake_shard(&shard_path).expect("gate runs on tampered record");
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            crate::shard_verify::cake_gate::CakeGateViolation::MissingGraduationNote { .. }
        )),
        "tampered record must break the binding-digest note; violations: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_hand_rolled_cake_shard() {
    // A forger flips the source_system byte without going through intake.
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    builder
        .add_declaration(&theorem(IMP_SELF, imp_self_type(), imp_self_value()), &[])
        .expect("forged export");
    let shard_path = tmp.path().join("forged-graduated.mathverse");
    builder
        .write_to_file(&shard_path)
        .expect("write forged shard");

    let err = verify_cake_shard(&shard_path).expect_err("forged Cake shard must fail the gate");
    assert!(
        matches!(err, CakeGateError::MissingGraduationRecord(_)),
        "expected MissingGraduationRecord, got: {err}"
    );

    // ... and the directory sweep finds it by content, not by filename.
    let dir_err = crate::shard_verify::cake_gate::verify_cake_shard_dir(tmp.path())
        .expect_err("dir sweep must fail on the forged shard");
    assert!(matches!(dir_err, CakeGateError::MissingGraduationRecord(_)));
}

#[test]
fn test_cake_gate_rejects_tampered_carried_definition_record() {
    // Tampering with a carried-definition entry (here: the reducibility
    // hint the gate replays with) must break the record's binding digest.
    let mut env = Environment::new();
    env.add_decl(definition(PID_DEF, pid_type(), pid_value()))
        .expect("PId definition must kernel-check");
    env.add_decl(theorem(USES_PID, uses_pid_type(), uses_pid_value()))
        .expect("uses_pid must kernel-check");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_PID]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");
    let shard_path = out.join(&record.result.shard_filename);
    let record_path = graduation_record_path(&shard_path);

    let mut tampered = GraduationRecord::from_file(&record_path).expect("read record");
    tampered.carried_definitions[0].is_reducible = false;
    tampered
        .write_to_file(&record_path)
        .expect("write tampered record");

    let report = verify_cake_shard(&shard_path).expect("gate runs on tampered record");
    assert!(
        report
            .violations
            .iter()
            .any(|v| matches!(v, CakeGateViolation::MissingGraduationNote { .. })),
        "tampered carried-definition entry must break the binding digest; violations: {:?}",
        report.violations
    );
}

// ---------------------------------------------------------------------------
// ENV-FUSION: the in-process fast path (round-trip oracle against the primary
// gate's recheck env) must AGREE with full standalone replay on genuine
// artifacts, and must FAIL CLOSED when the primary env does not vouch.
// ---------------------------------------------------------------------------

/// Graduate the pilot env keeping the recheck environment (the ENV-FUSION
/// hook), returning `(shard_path, recheck_env)`.
fn run_pilot_keep_env(out: &Path, baseline_dir: &Path) -> (PathBuf, Environment) {
    std::fs::create_dir_all(baseline_dir).expect("baseline dir");
    let baseline = pilot_baseline(baseline_dir);
    let (record, recheck) = graduate_with_base_keep_env(
        &pilot_env(),
        &names(&[IMP_SELF, IMP_TRANS, BAD_DEPENDENT]),
        &pilot_request(),
        &baseline,
        out,
        RecheckBase::CleanPrelude,
    )
    .expect("graduation must not hit infrastructure errors");
    (out.join(&record.result.shard_filename), recheck)
}

/// Fusion changes the COST of clause 3, never its verdict: the fused report
/// must be identical to the full-replay report on a real graduated shard, and
/// both clean.
#[test]
fn test_env_fusion_matches_full_replay() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let baseline_dir = tmp.path().join("baseline");
    let (shard_path, mut recheck) = run_pilot_keep_env(&out, &baseline_dir);

    let full = verify_cake_shard(&shard_path).expect("full replay runs");
    let fused = verify_cake_shard_fused(&shard_path, &mut recheck).expect("fused runs");

    assert!(
        full.is_clean(),
        "full replay must be clean; violations: {:?}",
        full.violations
    );
    assert!(
        fused.is_clean(),
        "fused must be clean; violations: {:?}",
        fused.violations
    );
    assert_eq!(
        full, fused,
        "fused report must equal the full-replay report"
    );
}

/// The round-trip oracle fails closed: a primary env that does not contain the
/// shard's kernel-verified declarations (here a fresh, empty env) cannot vouch,
/// so the fused gate reports `FusedOracleMismatch` rather than a clean pass.
#[test]
fn test_env_fusion_oracle_fails_closed_on_empty_primary() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let baseline_dir = tmp.path().join("baseline");
    let (shard_path, _recheck) = run_pilot_keep_env(&out, &baseline_dir);

    let mut empty = Environment::new();
    let report = verify_cake_shard_fused(&shard_path, &mut empty).expect("fused runs");
    assert!(
        !report.is_clean(),
        "an empty primary env must not vouch for any shard constant"
    );
    assert!(
        report
            .violations
            .iter()
            .any(|v| matches!(v, CakeGateViolation::FusedOracleMismatch { .. })),
        "expected a FusedOracleMismatch; violations: {:?}",
        report.violations
    );
}
