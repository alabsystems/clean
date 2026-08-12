// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// Graduation record contract: full pilot contract + committed v1 artifact back-compat.

// ---------------------------------------------------------------------------
// Pilot: full contract
// ---------------------------------------------------------------------------

#[test]
fn test_graduate_pilot_full_contract() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let baseline_dir = tmp.path().join("baseline");
    std::fs::create_dir_all(&baseline_dir).expect("baseline dir");
    let record = run_pilot(&out, &baseline_dir);

    // (a) Schema + populated metadata.
    assert_eq!(record.schema, GRADUATION_SCHEMA_VERSION);
    assert_eq!(record.policy.min_trust, GRADUATION_MIN_TRUST);
    assert_eq!(record.project.name, "grad-pilot");
    assert_eq!(record.corpus_pin.mathverse_release, "fixture");
    assert!(record.corpus_pin.manifest_digest.starts_with("blake3:"));
    assert_eq!(record.provenance.attempt_id.as_deref(), Some("pilot-0001"));
    assert_eq!(record.provenance.residual_risk, "fixture");
    assert_eq!(record.theorems.len(), 3, "all candidates must be recorded");

    // (b) imp_trans accepted: kernel-verified, foundational-only, new.
    let trans = entry(&record, IMP_TRANS);
    assert!(trans.accepted, "imp_trans must graduate");
    assert_eq!(trans.kernel.verdict, KernelVerdict::KernelVerified);
    assert!(trans.kernel.value_typechecked);
    assert!(trans.axiom_closure.foundational_only);
    assert!(trans.axiom_closure.domain_axioms.is_empty());
    assert_eq!(trans.axiom_closure.axiom_profile_bits, 0);
    assert_eq!(trans.novelty.verdict, NoveltyVerdict::New);
    assert_eq!(
        trans.statement_hash,
        expr_canonical_digest(&imp_trans_type()).expect("hash imp_trans type"),
        "statement hash must be the canonical FlatExpr digest of the type"
    );

    // (c) imp_self rejected as duplicate of the baseline.
    let dup = entry(&record, IMP_SELF);
    assert!(!dup.accepted);
    assert_eq!(dup.novelty.verdict, NoveltyVerdict::Duplicate);
    assert_eq!(dup.novelty.matched_name.as_deref(), Some(IMP_SELF));
    assert!(dup.novelty.match_kind.is_some());
    assert!(
        dup.kernel.value_typechecked,
        "duplicate rejection must still record the honest kernel re-check"
    );
    assert!(dup
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.starts_with("duplicate")));

    // (d) bad_dependent rejected with the domain axiom named — and the
    // non-foundational closure can NOT claim kernel_verified.
    let bad = entry(&record, BAD_DEPENDENT);
    assert!(!bad.accepted);
    assert_eq!(bad.kernel.verdict, KernelVerdict::Rejected);
    assert!(!bad.axiom_closure.foundational_only);
    assert_eq!(bad.axiom_closure.domain_axioms, vec![BAD_AXIOM.to_string()]);
    assert!(bad
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.starts_with("axiom-dependent")));

    assert_eq!(record.result.accepted, vec![IMP_TRANS.to_string()]);
    assert_eq!(record.result.rejected.len(), 2);

    // (e) Shard round-trip: one Cake constant, KernelVerified, value-bearing,
    // empty profile, digest-bound provenance note.
    let shard_path = out.join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read graduated shard");
    assert_eq!(reader.header.constant_count, 1);
    let (_idx, header) = reader
        .lookup_name(IMP_TRANS)
        .expect("imp_trans must be in the graduated shard");
    assert_eq!(header.source_system, SourceSystem::Cake as u8);
    assert_eq!(
        header.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert!(header.has_value());
    assert_eq!(header.axiom_profile.0, 0);
    assert!(reader.lookup_name(IMP_SELF).is_none());
    assert!(reader.lookup_name(BAD_DEPENDENT).is_none());
    assert!(reader.lookup_name(BAD_AXIOM).is_none());

    let sidecar = ProvenanceSidecar::from_bytes(&reader.provenance)
        .expect("decode provenance sidecar");
    let prov = sidecar.get(header.provenance_idx).expect("prov record");
    let expected_note = record.provenance_note().expect("binding note");
    assert!(expected_note.starts_with(GRADUATION_NOTE_PREFIX));
    assert!(
        prov.notes.contains(&expected_note),
        "shard provenance must carry the record's binding digest"
    );
    assert_eq!(prov.module_path.as_deref(), Some("grad-pilot"));

    // Record/shard digests are mutually bound.
    let shard_bytes = std::fs::read(&shard_path).expect("shard bytes");
    assert_eq!(
        record.result.shard_digest,
        super::record::blake3_digest(&shard_bytes)
    );
    let reread =
        GraduationRecord::from_file(&graduation_record_path(&shard_path)).expect("reread record");
    assert_eq!(reread, record, "record JSON must round-trip");

    // (f) The cake gate passes on the genuine pair.
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "genuine graduated shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert_eq!(report.checked, 1);
}

#[test]
fn test_cake_gate_v1_committed_graduation_artifact_still_verifies() {
    // GRADUATION #1's committed `.mathverse` artifact was retired from the git
    // tree by the graduation-storage refactor (shards are no longer tracked —
    // see `tests/no_graduation_mathverse_tracked.rs`). The two properties that
    // artifact pinned are regenerated here in a tempdir, with no tracked binary
    // (`write_legacy_nonreplaying_graduation`, schema doc):
    //
    //   1. SCHEMA BACK-COMPAT — a v1-schema record (carried-dependency fields
    //      serde-default to empty and are skipped on re-serialization) parses
    //      under the current schema types and the cake gate accepts that
    //      schema.
    //   2. FAIL-CLOSED REPLAY — like the historical artifact (whose proof
    //      bytes predate the casesOn Lean-parity correction and no longer
    //      re-typecheck against the corrected prelude), a shard whose stored
    //      proof value does not typecheck must FAIL the gate's kernel replay
    //      — fail-closed, never silently accepted.
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_path = write_legacy_nonreplaying_graduation(
        tmp.path(),
        GRADUATION_SCHEMA_VERSION_V1,
        false,
    );

    let record = GraduationRecord::from_file(&graduation_record_path(&shard_path))
        .expect("regenerated v1 record must parse under the current schema types");
    assert_eq!(record.schema, GRADUATION_SCHEMA_VERSION_V1);
    assert!(record.carried_definitions.is_empty());

    let report = verify_cake_shard(&shard_path).expect("v1 artifact gate must run");
    assert!(
        !report.is_clean(),
        "a v1 shard whose stored proof value does not typecheck must NOT replay \
         clean — the gate must fail closed"
    );
    assert!(
        report.violations.iter().any(|v| {
            matches!(v, CakeGateViolation::KernelRejected { name, .. } if name == LEGACY_THM)
        }),
        "the fail-closed signal must be the kernel rejecting the mistyped proof: {:?}",
        report.violations
    );
}
