// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Shard-group orchestration E2E gate**
//! (`designs/2026-07-15-isabelle-shard-verify.md` §7 follow-up).
//!
//! The `N`-way shard group must run end-to-end on one machine and produce the
//! single verdict stream a serial run would — over BOTH the in-process (threads)
//! and the subprocess (child processes) runners. Proved at fixture scale on the
//! committed foundational-closure corpus so it stays fast and needs no external
//! data.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use clean_mathverse::hol::isabelle_pure_verify::{
    import_proven_theorems_streaming, import_proven_theorems_streaming_shard, merge_shard_verdicts,
    run_shard_group_in_process, run_shard_group_subprocess, ChildCommand, ShardGroupOpts,
    ShardSpec, ShardVerdicts,
};
use clean_mathverse::shard::ShardWriter;

const FIXTURE: &str = include_str!("fixtures/isabelle/hol_foundational_closure.jsonl");

/// Both tests mutate/read the process-global verify env; serialize them (this
/// binary runs its tests on threads) so their env expectations never interleave,
/// and so we do not run two heavy shard groups at once.
static ENV_LOCK: Mutex<()> = Mutex::new(());

fn write_sorted_fixture(path: &Path) {
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
    let mut f = std::fs::File::create(path).expect("create corpus file");
    for l in &lines {
        writeln!(f, "{l}").expect("write corpus line");
    }
}

/// Clear the KV-affecting env so the group and the serial cross-check see one
/// consistent configuration (mirrors the determinism gate's discipline). Also
/// clears `ISA_VERIFY_LOCK` so the leader genuinely OWNS the lock.
fn clear_verify_env() {
    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_ELIDE_PROOFS",
        "ISA_TRANSLATE_NODE_BUDGET",
        "ISA_TRUSTED_LEDGER",
        "ISA_PROGRESS_EVERY",
        "ISA_S3_MILLER",
        "ISA_REPROVE",
        "ISA_VERIFY_LOCK",
    ] {
        clean_mathverse::process_env::remove_persistent(var);
    }
}

/// A fresh, unique work dir for one test.
fn work_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("isa_shard_group_{}_{}", tag, std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk work dir");
    dir
}

#[test]
fn in_process_group_merges_byte_identical_to_serial() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_verify_env();

    let dir = work_dir("inproc");
    let corpus = dir.join("closure.serial_sorted.jsonl");
    write_sorted_fixture(&corpus);
    let work = dir.join("group");

    let mut opts = ShardGroupOpts::new(3, &work);
    opts.merged_out = Some(work.join("merged.json"));
    // Exercise the leader-lock acquisition path (owns or bypasses — either way the
    // run succeeds; the merge is what we assert).
    opts.acquire_lock = true;
    let merged = run_shard_group_in_process(&corpus, &opts).expect("in-process shard group");

    // The group's merge must reproduce a genuine serial run's verdict stream.
    let mut wfull = ShardWriter::new();
    let full = import_proven_theorems_streaming(&corpus, &mut wfull).expect("serial full replay");
    assert!(
        merged.agrees_with_full(&full),
        "in-process group disagrees with the serial driver: group KV={} rej={}, serial KV={} rej={}",
        merged.kernel_verified,
        merged.rejected,
        full.kernel_verified,
        full.rejected,
    );
    assert!(merged.kernel_verified > 0, "fixture must yield real KV");

    // Every per-shard artifact and the merged output were written.
    for k in 1..=3 {
        assert!(
            work.join(format!("shard_{k}.json")).exists(),
            "shard_{k}.json must be written"
        );
    }
    assert!(
        work.join("merged.json").exists(),
        "merged.json must be written"
    );

    // The written merged artifact round-trips to the same verdicts.
    let bytes = std::fs::read(work.join("merged.json")).expect("read merged.json");
    let reloaded: clean_mathverse::hol::isabelle_pure_verify::MergedVerdicts =
        serde_json::from_slice(&bytes).expect("decode merged.json");
    assert_eq!(reloaded, merged, "merged.json must round-trip");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn subprocess_group_spawns_children_and_merges() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_verify_env();

    let dir = work_dir("subproc");
    let corpus = dir.join("closure.serial_sorted.jsonl");
    write_sorted_fixture(&corpus);

    // Pre-compute the three shards' verdicts in-process and stash them; the child
    // processes below merely emit these to their injected ISA_SHARD_VERDICTS_OUT,
    // which exercises the driver's spawn / env-injection / wait / load / merge
    // plumbing with REAL child processes without paying a real verify per child.
    let precomp = dir.join("precomp");
    std::fs::create_dir_all(&precomp).expect("mk precomp dir");
    for k in 1..=3 {
        let mut w = ShardWriter::new();
        let verds =
            import_proven_theorems_streaming_shard(&corpus, &mut w, ShardSpec::new(k, 3).unwrap())
                .expect("precompute shard");
        verds
            .save(precomp.join(format!("shard_{k}.json")))
            .expect("save precomputed shard");
    }

    // Each child reads ISA_SHARD (k/N) the driver injects, and copies the matching
    // precomputed artifact to the ISA_SHARD_VERDICTS_OUT the driver also injects.
    let script = r#"k="${ISA_SHARD%%/*}"; cp "$PRECOMP/shard_${k}.json" "$ISA_SHARD_VERDICTS_OUT""#;
    let child = ChildCommand {
        program: "sh".to_string(),
        args: vec!["-c".to_string(), script.to_string()],
        envs: vec![("PRECOMP".to_string(), precomp.display().to_string())],
    };

    let work = dir.join("group");
    let mut opts = ShardGroupOpts::new(3, &work);
    opts.acquire_lock = true;
    let merged_sub = run_shard_group_subprocess(&corpus, &opts, &child)
        .expect("subprocess shard group runs children + merges");

    // The subprocess merge must equal the direct merge of the same three shards.
    let parts: Vec<ShardVerdicts> = (1..=3)
        .map(|k| ShardVerdicts::load(precomp.join(format!("shard_{k}.json"))).expect("load"))
        .collect();
    let expected = merge_shard_verdicts(&parts).expect("direct merge");
    assert_eq!(
        merged_sub, expected,
        "subprocess group merge diverged from the direct merge"
    );
    assert!(merged_sub.kernel_verified > 0, "fixture must yield real KV");

    // The children genuinely wrote their per-shard artifacts into the work dir.
    for k in 1..=3 {
        assert!(
            work.join(format!("shard_{k}.json")).exists(),
            "child {k} must have written its shard artifact"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
