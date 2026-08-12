// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Snapshot-resume equivalence gate for the standing re-import substrate
//! (`isabelle_pure_verify::snapshot`, P2.3 of
//! `designs/2026-07-07-isabelle-100pct-industrial-import.md`).
//!
//! The contract under test: replaying a corpus **prefix**, snapshotting, and
//! resuming over the **full** corpus must produce EXACTLY the verdicts of a
//! single full replay — same KernelVerified count, same rejection buckets,
//! same verified-name multiset — and a resumed run against a corpus whose
//! prefix bytes changed must be refused.
//!
//! Uses the committed 137-line foundational-closure fixture (the same corpus
//! `isabelle_closure_replay` gates on), split ~60/40.

use std::io::Write as _;
use std::path::PathBuf;
use std::sync::Mutex;

use clean_mathverse::hol::isabelle_pure_verify::{
    import_proven_theorems_parallel, import_proven_theorems_retry, import_proven_theorems_streaming,
};
use clean_mathverse::shard::ShardWriter;

const FIXTURE: &str = include_str!("fixtures/isabelle/hol_foundational_closure.jsonl");

/// A real single-line Isabelle export — `Int.power_int_def`, a polymorphic
/// instance-op definition whose body uses the built-in `HOL.If` def-const and
/// which KernelVerifies ONLY through the poly-inst handler once `HOL.If` is
/// registered AND `power_int` is in the poly-inst registry (see the
/// `kernel_verifies_polymorphic_instance_op_power_int_def` unit test). Used by
/// the retry-parity leg: withholding `HOL.If` makes both the def-const AND the
/// dependent registry entry absent, exactly reproducing a registration-altering
/// translator round.
const POWER_INT_DEF: &str = include_str!("fixtures/isabelle/power_int_def.json");
/// `Int.power_int_def`'s proof-term serial (see the ledger-retry fixtures).
const POWER_INT_SERIAL: i64 = 94308;
/// The kernel name of the built-in `HOL.If` def-const (see
/// `connectives::hol_if_def_name`). Withheld to simulate a pre-registration
/// translator build.
const HOL_IF_DEF_CONST: &str = "isabelle.def.HOL.If";

/// A plain `a = a` proved by `HOL.refl a` (serial 94305) — KV under BOTH arms
/// (needs no `HOL.If`); the accepted-prefix witness for the retry-checkpoint test.
const K_KV: &str = r#"{"name":"test.k_a_eq_a","serial":94305,"prop":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[{"k":"Type","n":"HOL.bool","a":[]},{"k":"Type","n":"prop","a":[]}]}},"a":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"HOL.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"HOL.bool","a":[]}]}]}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}},"proof":{"k":"appt","f":{"k":"axm","name":"HOL.refl"},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}}"#;

/// Build a dependent line asserting `Int.power_int_def`'s prop, proved by a bare
/// `PThm` reference to `dep_serial`. Chained (each depends on the previous) they
/// give the retry-checkpoint test several flippable reject lines: under the
/// withheld-`HOL.If` old arm the head (`power_int`) rejects and every dependent
/// then has an unresolved dep, so ALL reject; the retry (`HOL.If` restored) flips
/// the head, and each dependent's ref resolves against the growing KV closure and
/// flips too.
fn build_power_int_dependent(name: &str, serial: i64, dep_serial: i64) -> String {
    let pdef: serde_json::Value =
        serde_json::from_str(POWER_INT_DEF.trim()).expect("parse power_int_def");
    let prop = pdef.get("prop").expect("power_int_def has a prop").clone();
    let d = serde_json::json!({
        "name": name,
        "serial": serial,
        "prop": prop,
        "proof": {"k": "thm", "id": dep_serial, "thy": "Int"},
    });
    serde_json::to_string(&d).expect("serialize dependent")
}

/// Env-var choreography is process-global; every test in this binary that
/// touches `ISA_SNAPSHOT_*` / `ISA_WITHHOLD_DEF_CONSTS` serializes on this lock
/// so the parallel default test runner cannot interleave two runs' variables.
static ENV_LOCK: Mutex<()> = Mutex::new(());

fn write_lines(path: &PathBuf, lines: &[&str]) {
    let mut f = std::fs::File::create(path).expect("create corpus file");
    for l in lines {
        writeln!(f, "{l}").expect("write corpus line");
    }
}

/// Serialize-and-resume must equal a single full replay, verdict for verdict;
/// a tampered prefix must be refused. One `#[test]` so the env-var choreography
/// is single-threaded within this binary.
#[test]
fn snapshot_resume_matches_full_replay_and_refuses_tampered_prefix() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let dir = std::env::temp_dir().join(format!("isa_snapshot_test_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let full_path = dir.join("full.jsonl");
    let prefix_path = dir.join("prefix.jsonl");
    let snap_path = dir.join("state.snap");

    // The committed fixture is NOT serial-sorted (the closure_replay test uses
    // the batch driver, which topo-sorts); the streaming driver requires
    // serial-ascending order — sort here, exactly like the production corpus.
    let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
    lines.sort_by_key(|l| {
        l.strip_prefix("{\"serial\":")
            .and_then(|r| {
                r.chars()
                    .take_while(char::is_ascii_digit)
                    .collect::<String>()
                    .parse::<i64>()
                    .ok()
            })
            .unwrap_or(i64::MAX)
    });
    assert!(
        lines.len() > 40,
        "fixture unexpectedly small: {}",
        lines.len()
    );
    let split = lines.len() * 3 / 5;
    write_lines(&full_path, &lines);
    write_lines(&prefix_path, &lines[..split]);

    // Guard against ambient configuration leaking in.
    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_ELIDE_PROOFS",
        "ISA_TRANSLATE_NODE_BUDGET",
        "ISA_SNAPSHOT_SKIP_PREFIX_HASH",
        "ISA_SNAPSHOT_ALLOW_MISMATCH",
    ] {
        clean_mathverse::process_env::remove_persistent(var);
    }

    // 1) Reference: one full replay.
    let mut w = ShardWriter::new();
    let full = import_proven_theorems_streaming(&full_path, &mut w).expect("full replay");
    assert!(
        full.kernel_verified >= 129,
        "fixture gate: expected >=129 KV, got {}",
        full.kernel_verified
    );

    // 2) Prefix replay + snapshot save.
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &snap_path);
    let mut w = ShardWriter::new();
    let prefix = import_proven_theorems_streaming(&prefix_path, &mut w).expect("prefix replay");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    assert!(snap_path.exists(), "snapshot file must be written");
    assert!(
        prefix.kernel_verified < full.kernel_verified,
        "prefix must verify strictly fewer ({} vs {})",
        prefix.kernel_verified,
        full.kernel_verified
    );

    // 3) Resume over the full corpus — the prefix of `full.jsonl` is
    //    byte-identical to `prefix.jsonl` by construction.
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_IN", &snap_path);
    let mut w = ShardWriter::new();
    let resumed = import_proven_theorems_streaming(&full_path, &mut w).expect("resumed replay");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_IN");

    assert_eq!(
        resumed.kernel_verified, full.kernel_verified,
        "resumed KV must equal full-replay KV"
    );
    assert_eq!(
        resumed.rejected, full.rejected,
        "resumed reject count must equal full-replay reject count"
    );
    assert_eq!(
        resumed.rejection_reasons, full.rejection_reasons,
        "resumed rejection buckets must equal full-replay buckets"
    );
    let mut full_names = full.names.clone();
    let mut resumed_names = resumed.names.clone();
    full_names.sort();
    resumed_names.sort();
    assert_eq!(
        resumed_names, full_names,
        "resumed verified-name multiset must equal full replay's"
    );

    // 3b) PARALLEL full replay must equal the serial full replay (fixture-scale
    //     re-assertion of the grand-scale verdict-identity result).
    let mut w = ShardWriter::new();
    let par_full = import_proven_theorems_parallel(&full_path, &mut w, 4).expect("parallel full");
    assert_eq!(
        par_full.kernel_verified, full.kernel_verified,
        "parallel full-replay KV must equal serial"
    );
    assert_eq!(
        par_full.rejection_reasons, full.rejection_reasons,
        "parallel full-replay buckets must equal serial"
    );

    // 3c) PARALLEL resume from the SERIAL-written snapshot must equal full.
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_IN", &snap_path);
    let mut w = ShardWriter::new();
    let par_resumed =
        import_proven_theorems_parallel(&full_path, &mut w, 4).expect("parallel resumed");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_IN");
    assert_eq!(
        par_resumed.kernel_verified, full.kernel_verified,
        "parallel resumed KV must equal full"
    );
    assert_eq!(
        par_resumed.rejection_reasons, full.rejection_reasons,
        "parallel resumed buckets must equal full"
    );

    // 3d) Cross-direction: a PARALLEL prefix run writes a snapshot the SERIAL
    //     driver resumes from — same verdicts again.
    let par_snap_path = dir.join("state_par.snap");
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &par_snap_path);
    let mut w = ShardWriter::new();
    let _ = import_proven_theorems_parallel(&prefix_path, &mut w, 4).expect("parallel prefix");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    assert!(par_snap_path.exists(), "parallel snapshot must be written");
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_IN", &par_snap_path);
    let mut w = ShardWriter::new();
    let cross = import_proven_theorems_streaming(&full_path, &mut w).expect("serial cross-resume");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_IN");
    assert_eq!(
        cross.kernel_verified, full.kernel_verified,
        "serial resume from parallel snapshot must equal full"
    );
    assert_eq!(
        cross.rejection_reasons, full.rejection_reasons,
        "serial cross-resume buckets must equal full"
    );

    // 3e) The standing-pipeline verb end-to-end: raw per-theory files →
    //     assemble (sorted, deduped) → parallel replay → snapshot saved.
    //     Driven through the public CLI dispatch (`mathverse isabelle-import`).
    let raw_dir = dir.join("raw");
    std::fs::create_dir_all(&raw_dir).expect("mk raw dir");
    let third = lines.len() / 3;
    for (name, chunk) in [
        ("HOL.A.jsonl", &lines[..third]),
        ("HOL.B.jsonl", &lines[third..2 * third]),
        ("HOL.C.jsonl", &lines[2 * third..]),
    ] {
        write_lines(&raw_dir.join(name), chunk);
    }
    let verb_corpus = dir.join("verb_corpus.jsonl");
    let verb_snap = dir.join("verb.snap");
    let verb_shard = dir.join("verb.mathverse");
    clean_mathverse::cli::run(clean_mathverse::cli::MathverseArgs {
        command: clean_mathverse::cli::MathverseCommands::IsabelleImport(
            clean_mathverse::cli::IsabelleImportArgs {
                raw_dir: Some(raw_dir.clone()),
                corpus: verb_corpus.clone(),
                assemble_only: false,
                workers: 4,
                snapshot_in: None,
                retry_from: None,
                retry_ledger: false,
                retry_seed: None,
                corpus_diff: None,
                snapshot_out: Some(verb_snap.clone()),
                translate_budget: 8_000_000,
                mem_budget: 1 << 20,
                shard_out: Some(verb_shard.clone()),
            },
        ),
    })
    .expect("isabelle-import verb");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_IN");
    assert!(verb_snap.exists(), "verb must save the snapshot");
    // The published shard must read back with one KernelVerified header per
    // verified theorem, every header provenance-linked.
    let reader =
        clean_mathverse::shard::ShardReader::from_file(&verb_shard).expect("open published shard");
    assert_eq!(
        reader.constants.len(),
        full.kernel_verified,
        "shard must hold one constant per KernelVerified theorem"
    );
    assert!(
        reader.constants.iter().all(|c| c.sidecar_digest != 0),
        "every shard constant must be provenance-linked"
    );
    let verb_corpus_bytes = std::fs::read(&verb_corpus).expect("verb corpus");
    let full_bytes = std::fs::read(&full_path).expect("full corpus");
    assert_eq!(
        verb_corpus_bytes, full_bytes,
        "verb assembly must reproduce the serial-sorted corpus byte-for-byte"
    );

    // 3f) VERDICT-CACHE RETRY equivalence: a FULL replay that saves a v3
    //     snapshot (with the reject index), then a retry re-measure from that
    //     snapshot with the SAME translator, must reproduce the full replay's
    //     verdicts EXACTLY — every reject re-rejects identically, no former
    //     accept is touched. Both the serial (workers=0) and parallel
    //     (workers=4) retry drivers are asserted. This is the fixture-scale
    //     proof of the retry's equivalence guarantee.
    let full_snap = dir.join("full.snap");
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &full_snap);
    let mut w = ShardWriter::new();
    let full_for_retry =
        import_proven_theorems_streaming(&full_path, &mut w).expect("full replay for retry");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    assert!(full_snap.exists(), "full snapshot must be written");
    assert_eq!(
        full_for_retry.kernel_verified, full.kernel_verified,
        "control full replay must equal the reference full replay"
    );

    for retry_workers in [0usize, 4usize] {
        let mut w = ShardWriter::new();
        let retried = import_proven_theorems_retry(&full_path, &full_snap, &mut w, retry_workers)
            .unwrap_or_else(|e| panic!("retry (workers={retry_workers}) failed: {e}"));
        assert_eq!(
            retried.kernel_verified, full.kernel_verified,
            "retry (workers={retry_workers}) KV must equal full replay"
        );
        assert_eq!(
            retried.rejected, full.rejected,
            "retry (workers={retry_workers}) reject count must equal full replay"
        );
        assert_eq!(
            retried.rejection_reasons, full.rejection_reasons,
            "retry (workers={retry_workers}) rejection buckets must equal full replay"
        );
        let mut retried_names = retried.names.clone();
        let mut full_names2 = full.names.clone();
        retried_names.sort();
        full_names2.sort();
        assert_eq!(
            retried_names, full_names2,
            "retry (workers={retry_workers}) verified-name multiset must equal full replay"
        );
    }

    // 4) Tampered prefix: flip one byte inside the snapshotted range — the
    //    resume must be REFUSED (PrefixMismatch), not silently accepted.
    let tampered_path = dir.join("tampered.jsonl");
    let mut bytes = std::fs::read(&full_path).expect("read full corpus");
    let f = bytes
        .iter()
        .position(|b| *b == b':')
        .expect("some byte to flip");
    bytes[f] = b';';
    std::fs::write(&tampered_path, &bytes).expect("write tampered corpus");
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_IN", &snap_path);
    let mut w = ShardWriter::new();
    let refused = import_proven_theorems_streaming(&tampered_path, &mut w);
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_IN");
    assert!(
        refused.is_err(),
        "resume against a tampered prefix must be refused"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// LAYOUT GUARD (ITEM 2): the snapshot header carries a 32-byte ENV-LAYOUT
/// fingerprint (a deterministic canary encoding of the kernel/wire serde graph).
/// A snapshot written and re-read by the SAME binary loads cleanly; a snapshot
/// whose fingerprint no longer matches this binary — the exact effect of upstream
/// `Environment` serde churn — is refused up front with `SnapshotError::LayoutDrift`
/// BEFORE any payload decode, instead of a late opaque `Utf8Error`. We simulate
/// the drift by flipping one byte of the stored fingerprint (equivalent to the
/// current binary computing a different layout hash), and assert the payload is
/// otherwise untouched (its trailing digest still matches, so the refusal is the
/// fingerprint's doing, not corruption).
#[test]
fn snapshot_layout_guard_refuses_drifted_fingerprint() {
    use clean_mathverse::hol::isabelle_pure_verify::snapshot;

    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let dir = std::env::temp_dir().join(format!("isa_layout_guard_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let corpus = dir.join("power_int.jsonl");
    let snap = dir.join("layout.snap");

    write_lines(&corpus, &[POWER_INT_DEF.trim()]);
    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_WITHHOLD_DEF_CONSTS",
    ] {
        clean_mathverse::process_env::remove_persistent(var);
    }

    // Write a v6 snapshot with this binary's layout fingerprint.
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &snap);
    let mut w = ShardWriter::new();
    let _ = import_proven_theorems_streaming(&corpus, &mut w).expect("prefix replay");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    assert!(snap.exists(), "snapshot must be written");

    // 1) Same binary => matching fingerprint => loads cleanly.
    snapshot::load_snapshot(&snap).expect("matching-layout snapshot must load");

    // 2) Flip one byte of the stored fingerprint (header layout: magic[8] +
    //    version[4] + fingerprint[32] + ...), simulating a layout drift, and
    //    assert the loader refuses with LayoutDrift.
    let mut bytes = std::fs::read(&snap).expect("read snapshot");
    let fp_off = 8 + 4; // first fingerprint byte
    bytes[fp_off] ^= 0xff;
    std::fs::write(&snap, &bytes).expect("write drifted snapshot");

    match snapshot::load_snapshot(&snap) {
        Err(snapshot::SnapshotError::LayoutDrift { .. }) => {}
        Err(e) => panic!("drifted fingerprint must be refused with LayoutDrift, got: {e}"),
        Ok(_) => panic!("drifted fingerprint must be refused, but the load succeeded"),
    }
    // The retry loader shares the same header path, so it refuses identically.
    match snapshot::load_snapshot_retry(&snap) {
        Err(snapshot::SnapshotError::LayoutDrift { .. }) => {}
        Err(e) => panic!("retry loader must also refuse LayoutDrift, got: {e}"),
        Ok(_) => panic!("retry loader must refuse the drifted fingerprint, but it succeeded"),
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// RETRY PARITY (ITEM 1): a *registration-altering* translator round — one that
/// makes a NEW def-const (and the registry entry that depends on it) registrable
/// — must recover its dependent former-reject lines through `--retry-from`
/// EXACTLY as a fresh full replay does. Historically it reported `+0`: the retry
/// driver loaded the snapshot's FROZEN five PASS-1 registries and never refreshed
/// them, so a poly-inst entry (`power_int`) that only becomes registrable once
/// the new `HOL.If` def-const exists stayed absent, and the dependent `_def` line
/// re-rejected.
///
/// Reproduced deterministically in one binary via the `ISA_WITHHOLD_DEF_CONSTS`
/// seam: minting the prefix snapshot with `HOL.If` withheld is byte-for-byte the
/// state a pre-registration translator build would leave (no `HOL.If` def-const,
/// hence no `power_int` poly-inst registry entry, hence a rejected
/// `power_int_def`). The retry then runs with the def-const restored — the
/// "new binary" — and must flip the line.
#[test]
fn retry_parity_registration_altering_round_flips_dependent() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let dir = std::env::temp_dir().join(format!("isa_retry_parity_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let corpus = dir.join("power_int.jsonl");
    let snap = dir.join("withheld.snap");

    // Single-line corpus: `Int.power_int_def` (a self-contained poly-inst def,
    // no PThm deps). Serial-ascending by construction (one line).
    write_lines(&corpus, &[POWER_INT_DEF.trim()]);

    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_ELIDE_PROOFS",
        "ISA_WITHHOLD_DEF_CONSTS",
        "ISA_RETRY_REFRESH_REGISTRIES",
        "ISA_RETRY_SKIP_REGISTRY_REFRESH",
        "ISA_SNAPSHOT_SKIP_PREFIX_HASH",
        "ISA_SNAPSHOT_ALLOW_MISMATCH",
    ] {
        clean_mathverse::process_env::remove_persistent(var);
    }

    // 1) Reference: the "new binary" fresh full replay (HOL.If registered) — the
    //    dependent line KernelVerifies. This is the target the retry must match.
    let mut w = ShardWriter::new();
    let fresh = import_proven_theorems_streaming(&corpus, &mut w).expect("fresh replay");
    assert_eq!(
        fresh.kernel_verified, 1,
        "control: power_int_def must KV in a fresh replay (rejected={} reasons={:?})",
        fresh.rejected, fresh.rejection_reasons
    );

    // 2) The "old binary" prefix snapshot: HOL.If WITHHELD. Without the def-const
    //    the poly-inst pre-pass cannot register `power_int` (its `Definition`'s
    //    body references the absent `HOL.If`), so the line rejects and is written
    //    into the snapshot's reject index (v5).
    clean_mathverse::process_env::set_persistent("ISA_WITHHOLD_DEF_CONSTS", HOL_IF_DEF_CONST);
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &snap);
    let mut w = ShardWriter::new();
    let withheld =
        import_proven_theorems_streaming(&corpus, &mut w).expect("withheld prefix replay");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    clean_mathverse::process_env::remove_persistent("ISA_WITHHOLD_DEF_CONSTS");
    assert_eq!(
        withheld.kernel_verified, 0,
        "withholding HOL.If must make power_int_def reject (got KV={})",
        withheld.kernel_verified
    );
    assert_eq!(
        withheld.rejected, 1,
        "the withheld line must be recorded as exactly one reject"
    );
    assert!(snap.exists(), "withheld snapshot must be written");

    // 3) RETRY from the withheld snapshot as the "new binary" (HOL.If restored,
    //    withhold unset). The retry must refresh the frozen registries so that
    //    `power_int` becomes registrable and the dependent line flips to KV —
    //    matching the fresh replay's verdict EXACTLY. Both driver modes.
    for retry_workers in [0usize, 4usize] {
        let mut w = ShardWriter::new();
        let retried = import_proven_theorems_retry(&corpus, &snap, &mut w, retry_workers)
            .unwrap_or_else(|e| panic!("retry (workers={retry_workers}) failed: {e}"));
        assert_eq!(
            retried.kernel_verified,
            fresh.kernel_verified,
            "retry (workers={retry_workers}) must recover the dependent line to KV={} \
             (registration-altering parity); got KV={} rejected={} reasons={:?}",
            fresh.kernel_verified,
            retried.kernel_verified,
            retried.rejected,
            retried.rejection_reasons
        );
        assert_eq!(
            retried.rejected, fresh.rejected,
            "retry (workers={retry_workers}) reject count must equal the fresh replay's"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// **Periodic snapshot CHECKPOINT (crash/stall insurance).** A run with
/// `ISA_SNAPSHOT_EVERY=N` writes a `<ISA_SNAPSHOT_OUT>.ckpt` snapshot every N
/// lines, atomically, keeping only the latest. The contract: (a) the checkpoint
/// file (and its provenance sidecar) exist mid-run; (b) it is a NORMAL v6 prefix
/// snapshot at a positive multiple of N strictly before the end, carrying PARTIAL
/// verdicts; (c) enabling checkpoints never changes the run's own verdicts; and
/// (d) RESUMING from the mid-run checkpoint over the full corpus reproduces a
/// single full replay's verdicts EXACTLY — i.e. a killed run recovers its tail
/// from the last checkpoint with zero format changes (the same
/// `ISA_SNAPSHOT_IN` prefix-trust machinery). This is the resume-equivalence gate
/// (the same guarantee as the prefix-run resume above) applied to a checkpoint
/// minted DURING the run.
#[test]
fn periodic_checkpoint_is_written_partial_and_tail_resumes_to_full() {
    use clean_mathverse::hol::isabelle_pure_verify::snapshot;

    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let dir = std::env::temp_dir().join(format!("isa_ckpt_test_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let full_path = dir.join("full.jsonl");
    let out_snap = dir.join("state.snap");
    // The checkpoint path the driver derives: `<ISA_SNAPSHOT_OUT>.ckpt`.
    let ckpt = PathBuf::from(format!(
        "{}.ckpt",
        out_snap.to_str().expect("utf8 snapshot path")
    ));

    // Serial-sort the fixture exactly as production (the streaming driver requires
    // serial-ascending order).
    let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
    lines.sort_by_key(|l| {
        l.strip_prefix("{\"serial\":")
            .and_then(|r| {
                r.chars()
                    .take_while(char::is_ascii_digit)
                    .collect::<String>()
                    .parse::<i64>()
                    .ok()
            })
            .unwrap_or(i64::MAX)
    });
    let total = lines.len();
    assert!(total > 6, "fixture too small: {total}");
    write_lines(&full_path, &lines);
    // `every = total/3 + 1` guarantees ≥2 checkpoints, all strictly before the end
    // (never a checkpoint at the final line, so the latest ckpt is genuinely
    // partial regardless of the fixture's exact size).
    let every = total / 3 + 1;

    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_SNAPSHOT_EVERY",
        "ISA_ELIDE_PROOFS",
        "ISA_TRANSLATE_NODE_BUDGET",
        "ISA_PREMISE_STEP_BUDGET",
        "ISA_SNAPSHOT_SKIP_PREFIX_HASH",
        "ISA_SNAPSHOT_ALLOW_MISMATCH",
    ] {
        clean_mathverse::process_env::remove_persistent(var);
    }

    // 1) Reference: one full replay.
    let mut w = ShardWriter::new();
    let full = import_proven_theorems_streaming(&full_path, &mut w).expect("full replay");
    assert!(full.kernel_verified > 0, "fixture must verify something");

    // 2) Run WITH periodic checkpoints. The final snapshot still lands at
    //    `out_snap`; checkpoints land at `<out_snap>.ckpt` (latest kept).
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &out_snap);
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_EVERY", every.to_string());
    let mut w = ShardWriter::new();
    let run = import_proven_theorems_streaming(&full_path, &mut w).expect("checkpointed replay");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_EVERY");

    // (a) the checkpoint + its provenance sidecar exist.
    assert!(ckpt.exists(), "periodic checkpoint file must be written");
    let sidecar = snapshot::provenance_sidecar_path(&ckpt);
    assert!(
        sidecar.exists(),
        "the checkpoint's provenance sidecar must be written"
    );

    // (b) it is a partial v6 prefix snapshot at a positive multiple of `every`,
    //     strictly before the end, with fewer KV than the full run.
    let snap = snapshot::load_snapshot(&ckpt).expect("checkpoint must load as a v6 snapshot");
    assert!(snap.prefix_lines > 0, "checkpoint prefix must be non-empty");
    assert_eq!(
        snap.prefix_lines % every,
        0,
        "checkpoint prefix ({}) must be a multiple of the interval ({every})",
        snap.prefix_lines
    );
    assert!(
        snap.prefix_lines < total,
        "the latest checkpoint ({}) must be a MID-run partial prefix (< {total} total)",
        snap.prefix_lines
    );
    assert!(
        snap.out.kernel_verified < full.kernel_verified,
        "the mid-run checkpoint must carry PARTIAL verdicts ({} < {})",
        snap.out.kernel_verified,
        full.kernel_verified
    );

    // (c) checkpointing never changes the run's own verdicts.
    assert_eq!(
        run.kernel_verified, full.kernel_verified,
        "enabling checkpoints must not change the run's KV count"
    );
    assert_eq!(
        run.rejection_reasons, full.rejection_reasons,
        "enabling checkpoints must not change the run's reject buckets"
    );

    // (d) RESUME from the mid-run checkpoint over the FULL corpus == full replay.
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_IN", &ckpt);
    let mut w = ShardWriter::new();
    let resumed =
        import_proven_theorems_streaming(&full_path, &mut w).expect("resume from checkpoint");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_IN");
    assert_eq!(
        resumed.kernel_verified, full.kernel_verified,
        "tail-resume from the checkpoint must reach the full-replay KV count"
    );
    assert_eq!(
        resumed.rejected, full.rejected,
        "tail-resume reject count must equal the full replay's"
    );
    assert_eq!(
        resumed.rejection_reasons, full.rejection_reasons,
        "tail-resume rejection buckets must equal the full replay's"
    );
    let mut full_names = full.names.clone();
    let mut resumed_names = resumed.names.clone();
    full_names.sort();
    resumed_names.sort();
    assert_eq!(
        resumed_names, full_names,
        "tail-resume verified-name multiset must equal the full replay's"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// **Retry driver VISIBILITY PARITY (the v3.2 ledger-burn-down incident fix).**
/// The retry re-attempt pass re-verifies up to ~277k non-KV lines — a
/// near-grand-scale run — yet historically emitted NEITHER the streaming path's
/// `ISA_PROGRESS_EVERY` progress lines NOR its `ISA_SNAPSHOT_EVERY` resumable
/// `.ckpt` checkpoints, so a 24 h burn-down that had to be killed lost everything.
/// This gate asserts the retry now has the streaming path's checkpoint parity:
/// (a) a `<snapshot-out>.ckpt` (with its provenance sidecar) is written mid-retry;
/// (b) it loads as a v6 snapshot carrying PARTIAL flips (fewer KV than the
/// finished retry) at a positive multiple of the interval strictly before the end;
/// (c) enabling checkpoints does not change the retry's own verdicts; and (d)
/// RESUMING the retry from that mid-run checkpoint reaches the SAME final verdicts
/// as an uninterrupted retry — a killed retry recovers its tail from the last
/// checkpoint with zero format changes.
///
/// Scenario (both driver modes): a 4-line corpus K(KV) → power_int(94308) →
/// dep1(94309) → dep2(94310). Minting the OLD-arm snapshot with `HOL.If` WITHHELD
/// makes 94308's reflexive `_def` proof fail to close AND leaves both dependents
/// with an unresolved dep, so all three reject (K stays KV). The retry with
/// `HOL.If` restored flips all three in serial order (head → dependents cascade),
/// so `ISA_SNAPSHOT_EVERY=2` writes its last checkpoint after the 2nd flip — a
/// genuine partial (2 of 3 flips) — which then resumes to all three.
#[test]
fn retry_periodic_checkpoint_is_partial_and_resumes_to_full() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clean_mathverse::process_env::with_env_edits(retry_periodic_checkpoint_with_env);
}

fn retry_periodic_checkpoint_with_env(env: &mut clean_mathverse::process_env::EnvEditor) {
    use clean_mathverse::hol::isabelle_pure_verify::snapshot;

    let dir = std::env::temp_dir().join(format!("isa_retry_ckpt_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let corpus = dir.join("chain.jsonl");
    let old_snap = dir.join("old_arm.snap");

    // Serial-ascending: K(94305) power_int(94308) dep1(94309) dep2(94310).
    let dep1 = build_power_int_dependent("test.power_int_dep1", 94309, POWER_INT_SERIAL);
    let dep2 = build_power_int_dependent("test.power_int_dep2", 94310, 94309);
    write_lines(&corpus, &[K_KV, POWER_INT_DEF.trim(), &dep1, &dep2]);

    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_SNAPSHOT_EVERY",
        "ISA_PROGRESS_EVERY",
        "ISA_ELIDE_PROOFS",
        "ISA_WITHHOLD_DEF_CONSTS",
        "ISA_RETRY_SKIP_REGISTRY_REFRESH",
        "ISA_SNAPSHOT_SKIP_PREFIX_HASH",
        "ISA_SNAPSHOT_ALLOW_MISMATCH",
    ] {
        env.remove(var);
    }

    // 1) OLD-arm snapshot: HOL.If withheld ⇒ power_int + both dependents reject
    //    (recorded in the v6 reject index); only K is KV.
    env.set("ISA_WITHHOLD_DEF_CONSTS", HOL_IF_DEF_CONST);
    env.set("ISA_SNAPSHOT_OUT", &old_snap);
    let mut w = ShardWriter::new();
    let old = import_proven_theorems_streaming(&corpus, &mut w).expect("old-arm replay");
    env.remove("ISA_SNAPSHOT_OUT");
    env.remove("ISA_WITHHOLD_DEF_CONSTS");
    assert!(old_snap.exists(), "old-arm snapshot must be written");
    assert_eq!(old.kernel_verified, 1, "old arm: only K is KV");
    assert_eq!(
        old.rejected, 3,
        "old arm: power_int + dep1 + dep2 all reject (got {})",
        old.rejected
    );

    for retry_workers in [0usize, 4usize] {
        // 2) Reference: an UNINTERRUPTED retry (HOL.If restored) flips all three.
        let mut w = ShardWriter::new();
        let reference = import_proven_theorems_retry(&corpus, &old_snap, &mut w, retry_workers)
            .unwrap_or_else(|e| panic!("reference retry (workers={retry_workers}) failed: {e}"));
        assert_eq!(
            reference.kernel_verified, 4,
            "reference retry (workers={retry_workers}) must flip all three (K + 3 = 4 KV), got {}",
            reference.kernel_verified
        );

        // 3) CHECKPOINTED retry: ISA_SNAPSHOT_EVERY=2 writes `<new_snap>.ckpt` after
        //    the 2nd flip (partial), the last checkpoint kept.
        let new_snap = dir.join(format!("new_arm_{retry_workers}.snap"));
        let ckpt = PathBuf::from(format!(
            "{}.ckpt",
            new_snap.to_str().expect("utf8 snapshot path")
        ));
        env.set("ISA_SNAPSHOT_OUT", &new_snap);
        env.set("ISA_SNAPSHOT_EVERY", "2");
        let mut w = ShardWriter::new();
        let run = import_proven_theorems_retry(&corpus, &old_snap, &mut w, retry_workers)
            .unwrap_or_else(|e| panic!("checkpointed retry (workers={retry_workers}) failed: {e}"));
        env.remove("ISA_SNAPSHOT_OUT");
        env.remove("ISA_SNAPSHOT_EVERY");

        // (c) Checkpointing never changes the retry's own verdicts.
        assert_eq!(
            run.kernel_verified, reference.kernel_verified,
            "checkpointing must not change the retry's KV (workers={retry_workers})"
        );

        // (a) The checkpoint + its provenance sidecar exist.
        assert!(
            ckpt.exists(),
            "periodic retry checkpoint must be written (workers={retry_workers})"
        );
        assert!(
            snapshot::provenance_sidecar_path(&ckpt).exists(),
            "the retry checkpoint's provenance sidecar must be written (workers={retry_workers})"
        );

        // (b) It loads as a v6 snapshot carrying PARTIAL flips (fewer KV than the
        //     finished retry): 1 prefix KV + 2 of the 3 flips = 3.
        let snap = snapshot::load_snapshot(&ckpt).unwrap_or_else(|e| {
            panic!("checkpoint must load as v6 (workers={retry_workers}): {e}")
        });
        assert!(
            snap.out.kernel_verified < run.kernel_verified,
            "the mid-retry checkpoint must carry PARTIAL flips ({} < {}, workers={retry_workers})",
            snap.out.kernel_verified,
            run.kernel_verified
        );
        assert_eq!(
            snap.out.kernel_verified, 3,
            "checkpoint at re-attempt 2 must hold exactly 1 prefix KV + 2 flips (workers={retry_workers})"
        );

        // (d) RESUME the retry from the mid-run checkpoint ⇒ same final verdicts as
        //     the uninterrupted reference (the killed-run tail recovery).
        let mut w = ShardWriter::new();
        let resumed = import_proven_theorems_retry(&corpus, &ckpt, &mut w, retry_workers)
            .unwrap_or_else(|e| {
                panic!("resume-from-ckpt retry (workers={retry_workers}) failed: {e}")
            });
        assert_eq!(
            resumed.kernel_verified, reference.kernel_verified,
            "tail-resume from the retry checkpoint must reach the reference KV (workers={retry_workers})"
        );
        assert_eq!(
            resumed.rejected, reference.rejected,
            "tail-resume reject count must equal the reference retry (workers={retry_workers})"
        );
        assert_eq!(
            resumed.rejection_reasons, reference.rejection_reasons,
            "tail-resume rejection buckets must equal the reference retry (workers={retry_workers})"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
