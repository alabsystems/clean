// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Incremental-grand equivalence gate for the corpus-version diff substrate
//! (`hol::isabelle_corpus_diff` + the `--corpus-diff` retry integration,
//! `designs/2026-07-18-isabelle-incremental-grand.md`).
//!
//! The contract under test — the whole reason the feature exists — is:
//!
//! > **old corpus grand → snapshot → new corpus (append-only additions) → diff →
//! > `retry --corpus-diff` reproduces EXACTLY what a fresh grand on the new
//! > corpus produces**, both serial and parallel.
//!
//! Plus the soundness boundary: a corpus whose NEW version changes a line INSIDE
//! the old snapshot's trusted prefix must REFUSE incremental mode (loud error),
//! never silently trust the stale prefix.
//!
//! Uses the committed 137-line foundational-closure fixture, split ~60/40 so the
//! old corpus is a byte-exact prefix of the new (append-only), exactly the AFP
//! wave growth pattern.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use clean_mathverse::hol::isabelle_corpus_diff::{diff_corpora, load_diff, write_diff};
use clean_mathverse::hol::isabelle_index::{build_index, index_path, save_index};
use clean_mathverse::hol::isabelle_pure_verify::{
    import_proven_theorems_retry_with_diff, import_proven_theorems_streaming, StreamError,
};
use clean_mathverse::shard::ShardWriter;

const FIXTURE: &str = include_str!("fixtures/isabelle/hol_foundational_closure.jsonl");

/// Env-var choreography is process-global; serialize every test in this binary
/// that touches `ISA_SNAPSHOT_*` on one lock (the default runner is parallel).
static ENV_LOCK: Mutex<()> = Mutex::new(());

fn serial_of(line: &str) -> i64 {
    line.strip_prefix("{\"serial\":")
        .and_then(|r| {
            r.chars()
                .take_while(char::is_ascii_digit)
                .collect::<String>()
                .parse::<i64>()
                .ok()
        })
        .unwrap_or(i64::MAX)
}

/// Write `lines` (one per line, `\n`-joined + trailing `\n`) and build+save the
/// v2 `.idx` sidecar. Returns the corpus path.
fn write_corpus_indexed(path: &Path, lines: &[&str]) -> PathBuf {
    let mut f = std::fs::File::create(path).expect("create corpus");
    for l in lines {
        writeln!(f, "{l}").expect("write line");
    }
    f.flush().expect("flush");
    let index = build_index(path).expect("build index");
    save_index(&index_path(path), &index).expect("save index");
    path.to_path_buf()
}

fn clear_env() {
    for var in [
        "ISA_SNAPSHOT_IN",
        "ISA_SNAPSHOT_OUT",
        "ISA_ELIDE_PROOFS",
        "ISA_TRANSLATE_NODE_BUDGET",
        "ISA_SNAPSHOT_SKIP_PREFIX_HASH",
        "ISA_SNAPSHOT_ALLOW_MISMATCH",
        "ISA_RETRY_LEDGER",
        "ISA_TRUSTED_LEDGER",
        "ISA_RETRY_SKIP_REGISTRY_REFRESH",
    ] {
        clean_mathverse::process_env::remove_persistent(var);
    }
}

/// THE equivalence gate: an incremental retry over an append-only corpus bump
/// reproduces a fresh full grand on the new corpus, verdict for verdict — for
/// both the serial (workers=0) and parallel (workers=4) retry drivers.
#[test]
fn incremental_retry_matches_fresh_grand_on_append_only_growth() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_env();

    let dir = std::env::temp_dir().join(format!("isa_incr_grand_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");

    // Serial-ascending (the streaming driver's requirement); OLD = first 60%,
    // NEW = all — so OLD is a byte-exact prefix of NEW (append-only growth).
    let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
    lines.sort_by_key(|l| serial_of(l));
    let split = lines.len() * 3 / 5;
    assert!(split > 10 && split < lines.len(), "sane split: {split}");

    let old_corpus = write_corpus_indexed(&dir.join("old.jsonl"), &lines[..split]);
    let new_corpus = write_corpus_indexed(&dir.join("new.jsonl"), &lines);

    // OLD is a byte-exact prefix of NEW (the append-only invariant the diff and
    // the trusted-prefix boundary both rely on).
    let old_bytes = std::fs::read(&old_corpus).expect("read old");
    let new_bytes = std::fs::read(&new_corpus).expect("read new");
    assert_eq!(
        &new_bytes[..old_bytes.len()],
        &old_bytes[..],
        "old corpus must be a byte-exact prefix of the new corpus"
    );

    // 1) Reference: a fresh full grand on the NEW corpus.
    let mut w = ShardWriter::new();
    let fresh = import_proven_theorems_streaming(&new_corpus, &mut w).expect("fresh new grand");
    assert!(fresh.kernel_verified > 0, "fresh grand verifies something");

    // 2) OLD grand → snapshot (with reject index).
    let old_snap = dir.join("old.snap");
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &old_snap);
    let mut w = ShardWriter::new();
    let old_grand = import_proven_theorems_streaming(&old_corpus, &mut w).expect("old grand");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    assert!(old_snap.exists(), "old snapshot written");
    assert!(
        old_grand.kernel_verified < fresh.kernel_verified,
        "old prefix verifies strictly fewer than the full new corpus"
    );

    // 3) Diff OLD→NEW. Append-only ⇒ only NEW lines, no CHANGED/REMOVED.
    let diff = diff_corpora(&old_corpus, &new_corpus).expect("diff");
    assert!(diff.summary.append_only, "append-only growth");
    assert_eq!(diff.summary.changed, 0);
    assert_eq!(diff.summary.removed, 0);
    assert_eq!(
        diff.summary.new as usize,
        lines.len() - split,
        "every appended line is NEW"
    );
    let diff_path = dir.join("diff.json");
    write_diff(&diff_path, &diff).expect("write diff");
    // Round-trips.
    assert_eq!(load_diff(&diff_path).expect("load").summary, diff.summary);

    // 4) Incremental retry --corpus-diff, both serial and parallel, must equal
    //    the fresh new grand exactly.
    for workers in [0usize, 4usize] {
        let mut w = ShardWriter::new();
        let incr = import_proven_theorems_retry_with_diff(
            &new_corpus,
            &old_snap,
            &diff_path,
            &mut w,
            workers,
        )
        .unwrap_or_else(|e| panic!("incremental retry (workers={workers}) failed: {e}"));
        assert_eq!(
            incr.kernel_verified, fresh.kernel_verified,
            "incremental (workers={workers}) KV must equal the fresh new grand"
        );
        assert_eq!(
            incr.rejected, fresh.rejected,
            "incremental (workers={workers}) reject count must equal the fresh new grand"
        );
        assert_eq!(
            incr.rejection_reasons, fresh.rejection_reasons,
            "incremental (workers={workers}) rejection buckets must equal the fresh new grand"
        );
        let mut incr_names = incr.names.clone();
        let mut fresh_names = fresh.names.clone();
        incr_names.sort();
        fresh_names.sort();
        assert_eq!(
            incr_names, fresh_names,
            "incremental (workers={workers}) verified-name multiset must equal the fresh new grand"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// SOUNDNESS boundary: a NEW corpus that changes a line INSIDE the old
/// snapshot's trusted prefix must REFUSE incremental mode with a loud
/// [`StreamError::IncrementalRefused`] — never silently trust the stale prefix.
/// The byte-hash backstop (`validate_prefix`) is deliberately disabled
/// (`ISA_SNAPSHOT_SKIP_PREFIX_HASH=1`) so this asserts the *diff-based* refusal
/// specifically, which must hold even when the hash guard is off.
#[test]
fn incremental_retry_refuses_change_inside_trusted_prefix() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_env();

    let dir = std::env::temp_dir().join(format!("isa_incr_refuse_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");

    let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
    lines.sort_by_key(|l| serial_of(l));
    let split = lines.len() * 3 / 5;

    let old_corpus = write_corpus_indexed(&dir.join("old.jsonl"), &lines[..split]);

    // OLD grand → snapshot.
    let old_snap = dir.join("old.snap");
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &old_snap);
    let mut w = ShardWriter::new();
    let _ = import_proven_theorems_streaming(&old_corpus, &mut w).expect("old grand");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");

    // Build a TAMPERED new corpus: append the tail (append-only) BUT also mutate
    // one line inside the old prefix (append a harmless field to its JSON so its
    // content hash changes without breaking the leading serial). This makes the
    // old accepted prefix no longer byte-identical.
    let victim_idx = split / 2;
    let mut new_lines: Vec<String> = lines.iter().map(|s| s.to_string()).collect();
    let victim = &mut new_lines[victim_idx];
    assert!(victim.ends_with('}'), "line is a JSON object");
    victim.truncate(victim.len() - 1);
    victim.push_str(",\"_diff_probe\":1}");
    let new_refs: Vec<&str> = new_lines.iter().map(String::as_str).collect();
    let new_corpus = write_corpus_indexed(&dir.join("new_tampered.jsonl"), &new_refs);

    let diff = diff_corpora(&old_corpus, &new_corpus).expect("diff");
    assert!(
        diff.summary.changed >= 1,
        "the tampered prefix line shows up as CHANGED (got {} changed)",
        diff.summary.changed
    );
    let diff_path = dir.join("diff_tampered.json");
    write_diff(&diff_path, &diff).expect("write diff");

    // Disable the byte-hash backstop so ONLY the diff-based refusal can fire.
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_SKIP_PREFIX_HASH", "1");
    for workers in [0usize, 4usize] {
        let mut w = ShardWriter::new();
        let res = import_proven_theorems_retry_with_diff(
            &new_corpus,
            &old_snap,
            &diff_path,
            &mut w,
            workers,
        );
        match res {
            Err(StreamError::IncrementalRefused(msg)) => {
                assert!(
                    msg.contains("trusted") && msg.contains("prefix"),
                    "refusal must name the trusted-prefix boundary; got: {msg}"
                );
            }
            Err(e) => panic!("expected IncrementalRefused (workers={workers}), got {e}"),
            Ok(_) => panic!(
                "incremental retry (workers={workers}) must REFUSE a change inside the trusted \
                 prefix, but it succeeded"
            ),
        }
    }
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_SKIP_PREFIX_HASH");

    let _ = std::fs::remove_dir_all(&dir);
}

/// CLI WIRING: drive the public `clean mathverse` dispatch (`cli::run`) for the
/// new `isabelle-corpus-diff` verb and the `isabelle-import --corpus-diff`
/// incremental path — the exact code paths the binary takes — end to end, and
/// assert the artifacts land.
#[test]
fn cli_verbs_wire_corpus_diff_and_incremental_import() {
    use clean_mathverse::cli::{
        run, IsabelleCorpusDiffArgs, IsabelleImportArgs, MathverseArgs, MathverseCommands,
    };

    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_env();

    let dir = std::env::temp_dir().join(format!("isa_incr_cli_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");

    let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
    lines.sort_by_key(|l| serial_of(l));
    let split = lines.len() * 3 / 5;
    let old_corpus = write_corpus_indexed(&dir.join("old.jsonl"), &lines[..split]);
    let new_corpus = write_corpus_indexed(&dir.join("new.jsonl"), &lines);
    let old_snap = dir.join("old.snap");
    let new_snap = dir.join("new.snap");
    let diff_path = dir.join("diff.json");

    // OLD grand via the isabelle-import verb (writes the snapshot the incremental
    // path resumes from).
    run(MathverseArgs {
        command: MathverseCommands::IsabelleImport(IsabelleImportArgs {
            raw_dir: None,
            corpus: old_corpus.clone(),
            assemble_only: false,
            workers: 0,
            snapshot_in: None,
            retry_from: None,
            retry_ledger: false,
            retry_seed: None,
            corpus_diff: None,
            snapshot_out: Some(old_snap.clone()),
            translate_budget: 8_000_000,
            mem_budget: 1 << 20,
            shard_out: None,
        }),
    })
    .expect("old grand verb");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_IN");
    assert!(old_snap.exists(), "old snapshot written by the verb");

    // isabelle-corpus-diff verb -> diff.json.
    run(MathverseArgs {
        command: MathverseCommands::IsabelleCorpusDiff(IsabelleCorpusDiffArgs {
            old: old_corpus.clone(),
            new: new_corpus.clone(),
            out: diff_path.clone(),
        }),
    })
    .expect("corpus-diff verb");
    let diff = load_diff(&diff_path).expect("diff.json parses");
    assert!(diff.summary.append_only, "append-only bump");
    assert_eq!(diff.summary.new as usize, lines.len() - split);

    // isabelle-import --retry-from --corpus-diff (the incremental grand path).
    run(MathverseArgs {
        command: MathverseCommands::IsabelleImport(IsabelleImportArgs {
            raw_dir: None,
            corpus: new_corpus.clone(),
            assemble_only: false,
            workers: 0,
            snapshot_in: None,
            retry_from: Some(old_snap.clone()),
            retry_ledger: false,
            retry_seed: None,
            corpus_diff: Some(diff_path.clone()),
            snapshot_out: Some(new_snap.clone()),
            translate_budget: 8_000_000,
            mem_budget: 1 << 20,
            shard_out: None,
        }),
    })
    .expect("incremental import verb");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_IN");
    assert!(
        new_snap.exists(),
        "incremental import wrote the new snapshot"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
