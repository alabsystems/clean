// Shard byte-reproducibility regression guard (Stage K, 2026-06-13).
//
// The auditable-mathematics-factory trust chain is content-addressed: corpus
// pins, the .mvix novelty index, graduation `shard_digest`s, and attestation
// replay all rest on "verify by digest". Stage J found two graduation runs of
// identical logical content produced different shard blake3 — the sole cause
// is the wall-clock decision time (`decided_at`) feeding per-record
// `import_timestamp` + the record `binding_digest` provenance note, amplified
// by zstd into the header `provenance_len`. The fix makes the decision time
// injectable (`GraduationRequest::decided_at_epoch_s`); pinning it must yield
// byte-identical shards. This test is the gate that would have caught Stage J.

use super::*;

const PINNED_DECISION: u64 = 1_700_000_000;

fn pinned_pilot_request() -> GraduationRequest {
    GraduationRequest {
        decided_at_epoch_s: Some(PINNED_DECISION),
        ..pilot_request()
    }
}

fn run_pilot_pinned(out: &Path, baseline_dir: &Path) -> GraduationRecord {
    let env = pilot_env();
    let baseline = pilot_baseline(baseline_dir);
    graduate(
        &env,
        &names(&[IMP_SELF, IMP_TRANS, BAD_DEPENDENT]),
        &pinned_pilot_request(),
        &baseline,
        out,
    )
    .expect("graduation must not hit infrastructure errors")
}

/// Two graduations of identical content with the SAME pinned decision time
/// MUST produce byte-identical shards and identical record `shard_digest`.
#[test]
fn test_shard_byte_reproducible_under_pinned_decision_time() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let base = tmp.path().join("baseline");
    std::fs::create_dir_all(&base).expect("baseline dir");

    let out_a = tmp.path().join("a");
    let out_b = tmp.path().join("b");
    let rec_a = run_pilot_pinned(&out_a, &base);
    let rec_b = run_pilot_pinned(&out_b, &base);

    let bytes_a = std::fs::read(out_a.join(&rec_a.result.shard_filename)).expect("read shard a");
    let bytes_b = std::fs::read(out_b.join(&rec_b.result.shard_filename)).expect("read shard b");

    assert_eq!(
        bytes_a,
        bytes_b,
        "pinned-decision-time graduations must be byte-identical shards \
         (Stage-K reproducibility guard); lens {} vs {}",
        bytes_a.len(),
        bytes_b.len()
    );
    assert_eq!(
        rec_a.result.shard_digest, rec_b.result.shard_digest,
        "identical shard bytes must yield identical recorded shard_digest"
    );
    // The decision time itself must round-trip into the record (so a verifier
    // can recover the pin needed to reproduce these exact bytes).
    assert_eq!(
        rec_a.gate.decided_at_epoch_s, PINNED_DECISION,
        "pinned decision time must be recorded for replay"
    );
}

/// Control: the SAME content with DIFFERENT pinned decision times differs only
/// through the provenance/decision channel — confirming the decision time is
/// the (sole) volatile input and that pinning is what closes it.
#[test]
fn test_shard_differs_only_via_decision_time_channel() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let base = tmp.path().join("baseline");
    std::fs::create_dir_all(&base).expect("baseline dir");

    let env = pilot_env();
    let baseline = pilot_baseline(&base);
    let cands = names(&[IMP_SELF, IMP_TRANS, BAD_DEPENDENT]);

    let out_a = tmp.path().join("a");
    let out_b = tmp.path().join("b");
    let req_a = GraduationRequest {
        decided_at_epoch_s: Some(PINNED_DECISION),
        ..pilot_request()
    };
    let req_b = GraduationRequest {
        decided_at_epoch_s: Some(PINNED_DECISION + 86_400),
        ..pilot_request()
    };
    let rec_a = graduate(&env, &cands, &req_a, &baseline, &out_a).expect("grad a");
    let rec_b = graduate(&env, &cands, &req_b, &baseline, &out_b).expect("grad b");

    // The mathematical outcome is invariant under decision time.
    let acc = |r: &GraduationRecord| {
        let mut v: Vec<_> = r
            .theorems
            .iter()
            .map(|t| (t.name.clone(), t.accepted))
            .collect();
        v.sort();
        v
    };
    assert_eq!(
        acc(&rec_a),
        acc(&rec_b),
        "per-theorem verdicts must be invariant under decision time"
    );
}
