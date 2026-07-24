// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Sharded-verify determinism gate** (`designs/2026-07-15-isabelle-shard-verify.md`).
//!
//! The load-bearing invariant of the sharded stream verify: the merge of `N`
//! shards' outputs is **byte-identical** to a single (`N == 1`) run over the same
//! corpus and binary — and both agree with the serial streaming driver on every
//! verdict field. This gate proves it at fixture scale on the committed 137-line
//! foundational-closure corpus (the same fixture `isabelle_snapshot_resume` uses),
//! entirely in-process, so it is fast and needs no external corpus.

use std::io::Write as _;
use std::path::PathBuf;
use std::sync::Mutex;

use clean_mathverse::hol::isabelle_pure_verify::{
    export_prepass_snapshot, import_proven_theorems_streaming,
    import_proven_theorems_streaming_shard, import_proven_theorems_streaming_shard_emit,
    import_proven_theorems_streaming_shard_prepass, merge_shard_mathverse, merge_shard_verdicts,
    ShardSpec,
};
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::shard_reconstruct::reconstruct_from_shard_with_level_lists;
use clean_mathverse::types::NO_VALUE;

const FIXTURE: &str = include_str!("fixtures/isabelle/hol_foundational_closure.jsonl");

/// The sharded runs share the process-global env + first-`OnceLock` config, so
/// serialize this test against the ambient-config mutation (matching the sibling
/// isabelle tests' discipline).
static ENV_LOCK: Mutex<()> = Mutex::new(());

/// Serial-sort the committed fixture (deps-before-uses) exactly as the production
/// corpus is ordered, and write it to `path`.
fn write_sorted_fixture(path: &PathBuf) {
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
    let mut f = std::fs::File::create(path).expect("create corpus file");
    for l in &lines {
        writeln!(f, "{l}").expect("write corpus line");
    }
}

/// One shard's declarations as a sorted, order-independent semantic fingerprint:
/// per constant, `(name, import_confidence, type-expr Debug, value-expr Debug)`.
/// Read entirely through the format's own public reader + reconstruction, so it
/// compares WHAT the shard declares (declaration-set + verdict + reconstructed
/// type/value), independent of arena layout.
fn shard_declarations(path: &std::path::Path) -> Vec<(String, u8, String, String)> {
    let reader = ShardReader::from_file(path).expect("open .mathverse shard");
    let recon = |idx: u32| -> String {
        if idx == NO_VALUE {
            return "<AXIOM>".to_string();
        }
        reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            idx,
        )
        .map(|e| format!("{e:?}"))
        .unwrap_or_else(|e| format!("<UNRECONSTRUCTABLE: {e}>"))
    };
    let mut decls: Vec<(String, u8, String, String)> = reader
        .constants
        .iter()
        .map(|c| {
            let name = reader
                .strings
                .get(c.name_idx as usize)
                .cloned()
                .unwrap_or_default();
            (
                name,
                c.import_confidence,
                recon(c.type_idx),
                recon(c.value_idx),
            )
        })
        .collect();
    decls.sort();
    decls
}

/// **Per-range `.mathverse` emission gate** (design note §8 follow-up). A sharded
/// run's per-range `.mathverse` shards, merged, declare exactly the same constants
/// (with the same `KernelVerified` verdicts + reconstructed type/value) as the
/// unsharded stream's single `.mathverse`. Proven at fixture scale via the format's
/// own reader (semantic equality — the merge re-flattens through
/// `reconstruct → lower`, so it is asserted declaration-set + verdict equal, not
/// byte-identical to the raw unsharded arena).
#[test]
fn merged_shard_mathverse_matches_unsharded() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_ELIDE_PROOFS",
        "ISA_TRANSLATE_NODE_BUDGET",
        "ISA_TRUSTED_LEDGER",
        "ISA_PROGRESS_EVERY",
    ] {
        clean_mathverse::process_env::remove_persistent(var);
    }

    let dir = std::env::temp_dir().join(format!("isa_shard_mv_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let corpus = dir.join("closure.serial_sorted.jsonl");
    write_sorted_fixture(&corpus);

    // Unsharded stream → the single production `.mathverse`.
    let mut w_full = ShardWriter::new();
    let full = import_proven_theorems_streaming(&corpus, &mut w_full).expect("serial full replay");
    let unsharded_mv = dir.join("unsharded.mathverse");
    w_full
        .write_to_file(&unsharded_mv)
        .expect("write unsharded .mathverse");

    // Four disjoint shards, each emitting ITS OWN range's `.mathverse`.
    let mut shard_paths = Vec::new();
    let mut kv_total = 0usize;
    for k in 1..=4 {
        let mut wk = ShardWriter::new();
        let shard_mv = dir.join(format!("shard_{k}.mathverse"));
        let verds = import_proven_theorems_streaming_shard_emit(
            &corpus,
            &mut wk,
            ShardSpec::new(k, 4).unwrap(),
            None,
            Some(&shard_mv),
        )
        .expect("shard k/4 emit");
        kv_total += verds.kernel_verified();
        shard_paths.push(shard_mv);
    }
    assert_eq!(
        kv_total, full.kernel_verified,
        "the four shard ranges' KV must sum to the unsharded KV"
    );

    // Merge the per-range shards (in serial order) into one `.mathverse`.
    let merged_mv = dir.join("merged.mathverse");
    let merged_count =
        merge_shard_mathverse(&shard_paths, &merged_mv).expect("merge shard .mathverse");
    assert_eq!(
        merged_count, full.kernel_verified,
        "merged .mathverse must carry exactly the unsharded KV constant count"
    );

    // Semantic equality via the format's own reader: same declaration set, same
    // verdicts, same reconstructed type/value — the load-bearing equivalence.
    let unsharded_decls = shard_declarations(&unsharded_mv);
    let merged_decls = shard_declarations(&merged_mv);
    assert!(
        !merged_decls.is_empty(),
        "fixture must yield real KernelVerified constants"
    );
    assert_eq!(
        unsharded_decls, merged_decls,
        "merged per-range shards' .mathverse must declare exactly the unsharded run's constants"
    );
    // Every merged constant is a genuine KernelVerified verdict (not a downgrade).
    let kv_confidence = clean_mathverse::types::ImportConfidence::KernelVerified as u8;
    assert!(
        merged_decls
            .iter()
            .all(|(_, conf, _, _)| *conf == kv_confidence),
        "every merged constant must stay KernelVerified"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn merged_shards_are_byte_identical_to_single_run() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    // Guard against ambient config leaking in and against the process-global
    // first-wins OnceLock caches diverging between the runs below.
    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_ELIDE_PROOFS",
        "ISA_TRANSLATE_NODE_BUDGET",
        "ISA_TRUSTED_LEDGER",
        "ISA_PROGRESS_EVERY",
    ] {
        clean_mathverse::process_env::remove_persistent(var);
    }

    let dir = std::env::temp_dir().join(format!("isa_shard_det_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let corpus = dir.join("closure.serial_sorted.jsonl");
    write_sorted_fixture(&corpus);

    // 1) N == 1: the whole run recorded by a single shard.
    let mut w = ShardWriter::new();
    let whole =
        import_proven_theorems_streaming_shard(&corpus, &mut w, ShardSpec::new(1, 1).unwrap())
            .expect("shard 1/1 verify");
    let merged_one = merge_shard_verdicts(std::slice::from_ref(&whole)).expect("merge 1/1");

    // 2) N == 4: four disjoint shards, merged.
    let mut parts = Vec::new();
    for k in 1..=4 {
        let mut wk = ShardWriter::new();
        let part =
            import_proven_theorems_streaming_shard(&corpus, &mut wk, ShardSpec::new(k, 4).unwrap())
                .expect("shard k/4 verify");
        parts.push(part);
    }
    let merged_four = merge_shard_verdicts(&parts).expect("merge 4 shards");

    // --- The invariant: merge(N=1) == merge(N=4), byte-for-byte. ---
    let bytes_one = serde_json::to_vec(&merged_one).expect("serialize merged_one");
    let bytes_four = serde_json::to_vec(&merged_four).expect("serialize merged_four");
    assert_eq!(
        merged_one, merged_four,
        "sharded merge diverged from the single run"
    );
    assert_eq!(
        bytes_one, bytes_four,
        "sharded merge is not byte-identical to the single run"
    );

    // The four shard ranges must exactly tile the corpus (disjoint + complete).
    let total = whole.total_lines;
    let mut frontier = 0;
    for p in &parts {
        assert_eq!(p.lo, frontier, "shard {}/4 gap/overlap", p.k);
        frontier = p.hi;
    }
    assert_eq!(frontier, total, "shards do not cover the whole corpus");
    let shard_kv: usize = parts.iter().map(|p| p.kv.len()).sum();
    assert_eq!(
        shard_kv,
        whole.kv.len(),
        "shard KV total must equal the single run's"
    );

    // 3) Cross-check the sharded path against the genuine serial driver — catches
    // any drift between the recorder path and the unsharded streaming driver.
    let mut wfull = ShardWriter::new();
    let full = import_proven_theorems_streaming(&corpus, &mut wfull).expect("serial full replay");
    assert!(
        merged_four.agrees_with_full(&full),
        "sharded merge disagrees with the serial driver: merged KV={} rej={}, serial KV={} rej={}",
        merged_four.kernel_verified,
        merged_four.rejected,
        full.kernel_verified,
        full.rejected,
    );

    // The fixture is a real foundational closure: it must produce genuine KV, and
    // the soundness invariant KV + rejected (+ tier-2 + ledger) == lines must hold.
    assert!(
        merged_four.kernel_verified > 0,
        "fixture should yield real KernelVerified constants"
    );
    assert_eq!(
        merged_four.kernel_verified
            + merged_four.rejected
            + merged_four.kernel_checked_ledger
            + merged_four.ledger_size,
        total,
        "every corpus line must be accounted for exactly once"
    );

    // 4) Pre-pass hand-off (`export_prepass_snapshot` +
    // `import_proven_theorems_streaming_shard_prepass`): a leader exports the
    // shared post-pre-pass state ONCE; each child loads it (skipping the O(T)
    // registry scan) and replays only its range. The merged result MUST stay
    // byte-identical to the plain sharded run and agree with the serial driver —
    // the hand-off changes the setup path, never a verdict.
    let prepass = dir.join("prepass.snap");
    export_prepass_snapshot(&corpus, &prepass).expect("export pre-pass snapshot");
    let mut pp_parts = Vec::new();
    for k in 1..=4 {
        let mut wk = ShardWriter::new();
        let part = import_proven_theorems_streaming_shard_prepass(
            &corpus,
            &mut wk,
            ShardSpec::new(k, 4).unwrap(),
            &prepass,
        )
        .expect("pre-pass shard k/4 verify");
        pp_parts.push(part);
    }
    let merged_prepass = merge_shard_verdicts(&pp_parts).expect("merge pre-pass shards");
    let bytes_prepass = serde_json::to_vec(&merged_prepass).expect("serialize merged_prepass");
    assert_eq!(
        merged_four, merged_prepass,
        "pre-pass hand-off diverged from the plain sharded run"
    );
    assert_eq!(
        bytes_four, bytes_prepass,
        "pre-pass hand-off is not byte-identical to the plain sharded run"
    );
    assert!(
        merged_prepass.agrees_with_full(&full),
        "pre-pass merge disagrees with the serial driver: prepass KV={} rej={}, serial KV={} rej={}",
        merged_prepass.kernel_verified,
        merged_prepass.rejected,
        full.kernel_verified,
        full.rejected,
    );

    let _ = std::fs::remove_dir_all(&dir);
}
