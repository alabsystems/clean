// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-check unit tests for [`super`] (the `isabelle-doctor` ops preflight).
//! Every check is exercised in isolation with tempdir fixtures; the pure
//! evaluators are tested directly with synthetic inputs so no test depends on
//! the state of the host machine (git repo, running processes, real snapshots).

use std::path::{Path, PathBuf};

use super::super::isabelle_index;
use super::super::isabelle_pure_verify::snapshot::{
    self, SnapshotError, SnapshotHeaderInfo, SnapshotProvenance,
};
use super::artifacts::*;
use super::checks::*;
use super::skew::*;
use super::*;

fn tmpdir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("isa_doctor_{tag}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    dir
}

fn build_with(sha: &str, unix: Option<u64>) -> BuildIdentity {
    BuildIdentity::new(Some(sha.to_string()), unix)
}

// --- Check 1: binary freshness -------------------------------------------

#[test]
fn test_evaluate_binary_freshness_matching_head_passes() {
    let build = build_with("abc123def456", Some(1000));
    let check = evaluate_binary_freshness(&build, Some("abc123def456"), Some(500));
    assert_eq!(check.status, Status::Pass, "{}", check.summary);
}

#[test]
fn test_evaluate_binary_freshness_mismatched_head_warns() {
    let build = build_with("abc123def456", Some(1000));
    let check = evaluate_binary_freshness(&build, Some("ffffffffffff"), Some(500));
    assert_eq!(check.status, Status::Warn, "{}", check.summary);
    assert!(check.items.iter().any(|i| i.contains("repo HEAD")));
}

#[test]
fn test_evaluate_binary_freshness_unknown_identity_warns() {
    let check = evaluate_binary_freshness(&BuildIdentity::unknown(), Some("abc"), Some(1));
    assert_eq!(check.status, Status::Warn);
    assert!(check.summary.contains("NO embedded build identity"));
}

#[test]
fn test_evaluate_binary_freshness_older_than_crates_warns() {
    // SHA matches HEAD, but the binary predates the newest crates/ commit.
    let build = build_with("abc123def456", Some(100));
    let check = evaluate_binary_freshness(&build, Some("abc123def456"), Some(200));
    assert_eq!(check.status, Status::Warn, "{}", check.summary);
    assert!(check.items.iter().any(|i| i.contains("predates")));
}

#[test]
fn test_build_identity_new_normalizes_sentinels() {
    assert!(BuildIdentity::new(Some("unknown".into()), Some(0))
        .git_sha
        .is_none());
    assert!(BuildIdentity::new(Some(String::new()), None)
        .git_sha
        .is_none());
    assert_eq!(
        BuildIdentity::new(Some("deadbeef".into()), Some(7)).short_sha(),
        Some("deadbee".to_string())
    );
}

// --- Check 2: verify busy -------------------------------------------------

#[test]
fn test_evaluate_verify_busy_running_process_fails() {
    let procs = ["12345 isabelle_scale_run --grand".to_string()];
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Absent,
        &procs,
        None,
        None,
    );
    assert_eq!(check.status, Status::Fail);
    assert_eq!(check.items.len(), 1);
}

#[test]
fn test_evaluate_verify_busy_held_lock_fails() {
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Held,
        &[],
        None,
        None,
    );
    assert_eq!(check.status, Status::Fail);
    assert!(check.summary.contains("HELD"));
}

#[test]
fn test_evaluate_verify_busy_free_lock_passes() {
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Free,
        &[],
        None,
        None,
    );
    assert_eq!(check.status, Status::Pass);
}

#[test]
fn test_evaluate_verify_busy_absent_lock_passes() {
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Absent,
        &[],
        None,
        None,
    );
    assert_eq!(check.status, Status::Pass);
}

#[test]
fn test_evaluate_verify_busy_unknown_lock_warns() {
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Unknown,
        &[],
        None,
        None,
    );
    assert_eq!(check.status, Status::Warn);
}

#[test]
fn test_evaluate_verify_busy_held_reports_holder_metadata() {
    let holder = parse_lock_holder("pid=12345 started=1700000000 label=release grand");
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Held,
        &[],
        Some(&holder),
        None,
    );
    assert_eq!(check.status, Status::Fail);
    assert!(check.summary.contains("HELD"), "{}", check.summary);
    assert!(check.summary.contains("PID 12345"), "{}", check.summary);
    assert!(check.summary.contains("1700000000"), "{}", check.summary);
    assert!(check.summary.contains("release grand"), "{}", check.summary);
}

#[test]
fn test_evaluate_verify_busy_held_without_holder_names_generic_process() {
    // A legacy/empty lockfile parses to a blank holder -> fall back to a generic
    // phrase, still FAIL.
    let blank = parse_lock_holder("");
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Held,
        &[],
        Some(&blank),
        None,
    );
    assert_eq!(check.status, Status::Fail);
    assert!(
        check.summary.contains("another process"),
        "{}",
        check.summary
    );
}

#[test]
fn test_evaluate_verify_busy_running_process_appends_holder_item() {
    let holder = parse_lock_holder("pid=999 started=42 label=grand");
    let procs = ["999 isabelle_scale_run --grand".to_string()];
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Held,
        &procs,
        Some(&holder),
        None,
    );
    assert_eq!(check.status, Status::Fail);
    assert!(
        check
            .items
            .iter()
            .any(|i| i.contains("PID 999") && i.contains("grand")),
        "process branch should append the lock holder: {:?}",
        check.items
    );
}

#[test]
fn test_evaluate_verify_busy_reports_both_primary_and_side_holders() {
    // A primary grand HELD plus a bounded side lease alongside it: the check FAILs
    // on the held primary AND lists the side-lease holder metadata.
    let primary = parse_lock_holder("pid=111 started=1700000000 label=release grand");
    let side = parse_lock_holder("pid=222 started=1700000500 label=flip-gate check");
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Held,
        &[],
        Some(&primary),
        Some(&side),
    );
    assert_eq!(check.status, Status::Fail);
    assert!(check.summary.contains("PID 111"), "{}", check.summary);
    assert!(
        check.items.iter().any(|i| i.contains("side-verify lease")
            && i.contains("PID 222")
            && i.contains("flip-gate check")),
        "side lease holder must be reported: {:?}",
        check.items
    );
}

#[test]
fn test_evaluate_verify_busy_side_lease_only_warns() {
    // No primary/procs, but a live side lease: escalate the otherwise-Pass check to
    // WARN so a pre-grand operator sees the bounded verify competing for RAM.
    let side = parse_lock_holder("pid=555 started=1 label=verify-one");
    let check = evaluate_verify_busy(
        Path::new("/x/.clean_verify.lock"),
        LockState::Absent,
        &[],
        None,
        Some(&side),
    );
    assert_eq!(check.status, Status::Warn);
    assert!(
        check.summary.contains("SIDE-VERIFY LEASE"),
        "{}",
        check.summary
    );
    assert!(
        check
            .items
            .iter()
            .any(|i| i.contains("side-verify lease") && i.contains("PID 555")),
        "side lease holder item: {:?}",
        check.items
    );
}

#[test]
fn test_parse_lock_holder_full_record() {
    let h = parse_lock_holder("pid=12345 started=1700000000 label=release grand\n");
    assert_eq!(h.pid, Some(12345));
    assert_eq!(h.started_unix, Some(1_700_000_000));
    assert_eq!(h.label.as_deref(), Some("release grand"));
    assert!(!h.is_blank());
    assert_eq!(
        h.describe(),
        "held by PID 12345 since 1700000000 (unix) (release grand)"
    );
}

#[test]
fn test_parse_lock_holder_legacy_record_has_no_label() {
    // A pre-label lockfile (only pid + started) still parses its scalars.
    let h = parse_lock_holder("pid=99999 started=0\n");
    assert_eq!(h.pid, Some(99999));
    assert_eq!(h.started_unix, Some(0));
    assert_eq!(h.label, None);
    assert!(!h.is_blank());
}

#[test]
fn test_parse_lock_holder_empty_label_field_is_none() {
    let h = parse_lock_holder("pid=7 started=8 label=");
    assert_eq!(h.pid, Some(7));
    assert_eq!(h.label, None, "empty label field parses to None");
}

#[test]
fn test_parse_lock_holder_blank_and_garbled_degrade() {
    assert!(parse_lock_holder("").is_blank());
    assert!(parse_lock_holder("\n   \n").is_blank());
    // Non-record content: no recognisable keys -> blank, degrades to "unknown".
    assert!(parse_lock_holder("this is not a lock record").is_blank());
}

#[test]
fn test_lock_holder_describe_omits_missing_parts() {
    let only_label = parse_lock_holder("label=grand");
    assert_eq!(only_label.describe(), "held by an unknown process (grand)");
    let no_label = parse_lock_holder("pid=5 started=9");
    assert_eq!(no_label.describe(), "held by PID 5 since 9 (unix)");
}

#[test]
fn test_probe_verify_lock_absent_when_no_file() {
    let dir = tmpdir("lock_absent");
    let state = probe_verify_lock(&dir.join(".clean_verify.lock"));
    assert_eq!(state, LockState::Absent);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_probe_verify_lock_free_when_unheld() {
    let dir = tmpdir("lock_free");
    let lock = dir.join(".clean_verify.lock");
    std::fs::write(&lock, b"").expect("touch lock");
    // Nobody else holds it, so a non-blocking acquire succeeds.
    assert_eq!(probe_verify_lock(&lock), LockState::Free);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_collect_pgrep_hits_coalesces_embedded_newlines() {
    // One real process, then a monitoring command whose args contain literal
    // newlines — the continuation lines must fold onto the one PID entry.
    let out = "21939 target/release/deps/isabelle_scale_run-abc stream_run\n\
               23229 /bin/zsh -c eval 'R=x\n\
               last=\"\"\n\
               while true; do sleep 1800; done'";
    let mut hits = Vec::new();
    collect_pgrep_hits(out, 999_999, &mut hits);
    assert_eq!(
        hits.len(),
        2,
        "two processes, not newline fragments: {hits:?}"
    );
    assert!(hits[0].contains("isabelle_scale_run"));
}

#[test]
fn test_collect_pgrep_hits_filters_self_and_dedups() {
    let me = 4242;
    let out = format!("{me} clean mathverse isabelle-doctor\n100 verify-kernel --corpus c\n");
    let mut hits = Vec::new();
    collect_pgrep_hits(&out, me, &mut hits);
    // A second pattern hitting the same PID line must not double-count.
    collect_pgrep_hits("100 verify-kernel --corpus c\n", me, &mut hits);
    assert_eq!(
        hits.len(),
        1,
        "self filtered, duplicate coalesced: {hits:?}"
    );
    assert!(hits[0].starts_with("100 "));
}

#[test]
fn test_truncate_str_caps_long_lines() {
    let long = "x".repeat(500);
    let capped = truncate_str(&long, 180);
    assert_eq!(capped.chars().count(), 181, "180 chars + ellipsis");
    assert!(capped.ends_with('…'));
    assert_eq!(truncate_str("short", 180), "short");
}

// --- Check 3: dead script refs -------------------------------------------

#[test]
fn test_check_dead_script_refs_worktree_ref_fails() {
    let dir = tmpdir("dead_wt");
    let script = dir.join("run_grand.sh");
    std::fs::write(
        &script,
        "#!/bin/bash\nbash /Use\x72s/nobody/clean/.claude/worktrees/gone/launch.sh --go\n",
    )
    .expect("write script");
    let check = check_dead_script_refs(&dir);
    assert_eq!(check.status, Status::Fail, "{:?}", check);
    assert!(check.items.iter().any(|i| i.contains(".claude/worktrees")));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_dead_script_refs_all_present_passes() {
    let dir = tmpdir("dead_ok");
    let helper = dir.join("helper.sh");
    std::fs::write(&helper, "echo ok\n").expect("write helper");
    let script = dir.join("main.sh");
    std::fs::write(&script, format!("#!/bin/bash\nbash {}\n", helper.display()))
        .expect("write main");
    let check = check_dead_script_refs(&dir);
    assert_eq!(check.status, Status::Pass, "{:?}", check);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_dead_script_refs_missing_ops_dir_warns() {
    let dir = tmpdir("dead_missing");
    let ghost = dir.join("does-not-exist");
    let check = check_dead_script_refs(&ghost);
    assert_eq!(check.status, Status::Warn);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_extract_path_tokens_finds_users_home_and_tilde() {
    let text = "run /Use\x72s/x/a.sh and $HOME/b/c.jsonl plus ~/d/e.snap; skip /etc/passwd";
    let toks = extract_path_tokens(text);
    assert!(toks.iter().any(|t| t == "/Use\x72s/x/a.sh"), "{toks:?}");
    assert!(toks.iter().any(|t| t == "$HOME/b/c.jsonl"), "{toks:?}");
    assert!(toks.iter().any(|t| t == "~/d/e.snap"), "{toks:?}");
    // /etc is neither /Users nor $HOME nor ~, and has no matching prefix.
    assert!(!toks.iter().any(|t| t.contains("passwd")));
}

#[test]
fn test_extract_path_tokens_skips_directory_only_tokens() {
    // No extension on the final component -> not treated as a file reference.
    let toks = extract_path_tokens("out dir /Use\x72s/x/isabelle-work/output_dir end");
    assert!(toks.is_empty(), "{toks:?}");
}

#[test]
fn test_resolve_token_expands_home() {
    let resolved = resolve_token("$HOME/a/b.sh", Some("/home/me")).expect("resolves");
    assert_eq!(resolved, PathBuf::from("/home/me/a/b.sh"));
}

#[test]
fn test_resolve_token_skips_unresolved_var() {
    assert!(resolve_token("/Use\x72s/x/$RUN/b.sh", Some("/home/me")).is_none());
}

#[test]
fn test_check_dead_script_refs_skips_app_bundles() {
    // A vendored *.app bundle tree with a broken .sh launcher must NOT be
    // scanned (third-party content, not ops automation).
    let dir = tmpdir("dead_app");
    let app = dir.join("Isabelle2025-2.app/contrib/scripts");
    std::fs::create_dir_all(&app).expect("mk app tree");
    std::fs::write(
        app.join("vendored.sh"),
        "bash /Use\x72s/nobody/gone/launch.sh --go\n",
    )
    .expect("write vendored");
    let check = check_dead_script_refs(&dir);
    assert_eq!(
        check.status,
        Status::Pass,
        "*.app bundle scripts must be excluded: {check:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_dead_script_refs_ignores_self_created_redirect_output() {
    // release_grand.sh's own `> …main_v3_release.snap` is an OUTPUT, not a
    // missing dependency — it must not be flagged.
    let dir = tmpdir("dead_redirect");
    std::fs::write(
        dir.join("release_grand.sh"),
        "#!/bin/bash\nverify --corpus c > /Use\x72s/nobody/isabelle-work/main_v3_release.snap\n",
    )
    .expect("write script");
    let check = check_dead_script_refs(&dir);
    assert_eq!(check.status, Status::Pass, "{check:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_dead_script_refs_ignores_mkdir_output() {
    let dir = tmpdir("dead_mkdir");
    std::fs::write(
        dir.join("prep.sh"),
        "mkdir -p /Use\x72s/nobody/isabelle-work/build.out\n",
    )
    .expect("write script");
    let check = check_dead_script_refs(&dir);
    assert_eq!(check.status, Status::Pass, "{check:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_extract_referenced_tokens_excludes_created_paths() {
    let text = "cp /Use\x72s/x/in.jsonl dst\n\
                verify > /Use\x72s/x/out.snap\n\
                echo hi > \"/Use\x72s/x/quoted.log\"\n\
                mkdir -p /Use\x72s/x/build.out\n\
                mkdir -p /Use\x72s/x/made.d && bash /Use\x72s/x/dep.sh\n";
    let toks = extract_referenced_tokens(text);
    // Dependencies are kept…
    assert!(toks.iter().any(|t| t == "/Use\x72s/x/in.jsonl"), "{toks:?}");
    assert!(toks.iter().any(|t| t == "/Use\x72s/x/dep.sh"), "{toks:?}");
    // …outputs are dropped (plain + quoted redirects, mkdir args).
    assert!(!toks.iter().any(|t| t == "/Use\x72s/x/out.snap"), "{toks:?}");
    assert!(!toks.iter().any(|t| t == "/Use\x72s/x/quoted.log"), "{toks:?}");
    assert!(!toks.iter().any(|t| t == "/Use\x72s/x/build.out"), "{toks:?}");
    assert!(!toks.iter().any(|t| t == "/Use\x72s/x/made.d"), "{toks:?}");
}

// --- Check 4: corpus / index coherence -----------------------------------

fn write_corpus(dir: &Path) -> PathBuf {
    let corpus = dir.join("corpus.jsonl");
    let lines = [
        "{\"serial\":300,\"name\":\"HOL.refl\"}",
        "{\"serial\":305,\"name\":\"HOL.trans\"}",
        "{\"serial\":312,\"name\":\"HOL.sym\"}",
    ];
    std::fs::write(&corpus, lines.join("\n") + "\n").expect("write corpus");
    corpus
}

#[test]
fn test_check_corpus_index_coherent_passes() {
    let dir = tmpdir("corpus_ok");
    let corpus = write_corpus(&dir);
    let index = isabelle_index::build_index(&corpus).expect("build");
    isabelle_index::save_index(&isabelle_index::index_path(&corpus), &index).expect("save");
    let check = check_corpus_index(&corpus);
    assert_eq!(check.status, Status::Pass, "{}", check.summary);
    assert!(check.summary.contains("300..312"), "{}", check.summary);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_corpus_index_stale_fails() {
    let dir = tmpdir("corpus_stale");
    let corpus = write_corpus(&dir);
    let index = isabelle_index::build_index(&corpus).expect("build");
    isabelle_index::save_index(&isabelle_index::index_path(&corpus), &index).expect("save");
    // Append a line AFTER indexing -> stored corpus_len no longer matches.
    {
        use std::io::Write as _;
        let mut f = std::fs::OpenOptions::new()
            .append(true)
            .open(&corpus)
            .expect("open append");
        writeln!(f, "{{\"serial\":400,\"name\":\"Extra.x\"}}").expect("append");
    }
    let check = check_corpus_index(&corpus);
    assert_eq!(check.status, Status::Fail, "{}", check.summary);
    assert!(check.summary.contains("STALE"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_corpus_index_missing_idx_warns() {
    let dir = tmpdir("corpus_noidx");
    let corpus = write_corpus(&dir);
    let check = check_corpus_index(&corpus);
    assert_eq!(check.status, Status::Warn, "{}", check.summary);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_corpus_index_missing_corpus_fails() {
    let dir = tmpdir("corpus_gone");
    let check = check_corpus_index(&dir.join("nope.jsonl"));
    assert_eq!(check.status, Status::Fail);
    let _ = std::fs::remove_dir_all(&dir);
}

// --- Check 5: snapshot layout --------------------------------------------

fn hdr(has_fp: bool, matches: bool) -> SnapshotHeaderInfo {
    SnapshotHeaderInfo {
        version: 6,
        has_layout_fp: has_fp,
        layout_matches: matches,
        snapshot_fp_hex: "0011223344556677".to_string(),
        loader_fp_hex: "8899aabbccddeeff".to_string(),
    }
}

#[test]
fn test_classify_snapshot_header_layout_match_passes() {
    let check = classify_snapshot_header(Ok(hdr(true, true)), Path::new("/x/a.snap"));
    assert_eq!(check.status, Status::Pass, "{}", check.summary);
}

#[test]
fn test_classify_snapshot_header_drift_fails() {
    let check = classify_snapshot_header(Ok(hdr(true, false)), Path::new("/x/a.snap"));
    assert_eq!(check.status, Status::Fail, "{}", check.summary);
    assert!(check.summary.contains("ENV-LAYOUT DRIFT"));
}

#[test]
fn test_classify_snapshot_header_pre_v6_warns() {
    let mut h = hdr(false, true);
    h.version = 5;
    let check = classify_snapshot_header(Ok(h), Path::new("/x/a.snap"));
    assert_eq!(check.status, Status::Warn, "{}", check.summary);
}

#[test]
fn test_classify_snapshot_header_bad_header_fails() {
    let err = SnapshotError::Format("bad magic".to_string());
    let check = classify_snapshot_header(Err(err), Path::new("/x/a.snap"));
    assert_eq!(check.status, Status::Fail);
}

// --- Check 5b: snapshot ↔ binary provenance pairing ----------------------

fn prov_with(sha: &str) -> SnapshotProvenance {
    SnapshotProvenance {
        binary_git_sha: sha.to_string(),
        binary_path: "/opt/clean/bin/clean".to_string(),
        env_layout_fp: "ff".to_string(),
        corpus_fingerprint: "aa".to_string(),
        created_unix: 1,
    }
}

#[test]
fn test_snapshot_pairing_item_matching_sha_reports_match() {
    let build = build_with("abc123def456", None);
    let item = snapshot_pairing_item(Some(&prov_with("abc123def456")), &build);
    assert!(item.contains("MATCH"), "{item}");
    assert!(!item.contains("MISMATCH"), "{item}");
    assert!(item.contains("/opt/clean/bin/clean"), "{item}");
    assert!(item.contains("snapshot built by abc123d"), "{item}");
}

#[test]
fn test_snapshot_pairing_item_differing_sha_reports_mismatch() {
    let build = build_with("abc123def456", None);
    let item = snapshot_pairing_item(Some(&prov_with("ffffffffffff")), &build);
    assert!(item.contains("MISMATCH"), "{item}");
}

#[test]
fn test_snapshot_pairing_item_unknown_builder_sha_is_unverifiable() {
    let build = build_with("abc123def456", None);
    let item = snapshot_pairing_item(Some(&prov_with("unknown")), &build);
    assert!(item.contains("UNVERIFIABLE"), "{item}");
}

#[test]
fn test_snapshot_pairing_item_no_sidecar_degrades() {
    let build = build_with("abc123def456", None);
    let item = snapshot_pairing_item(None, &build);
    assert!(item.contains("no provenance sidecar"), "{item}");
}

#[test]
fn test_check_snapshot_layout_appends_sidecar_pairing() {
    let dir = tmpdir("snap_pairing");
    let snap = dir.join("x.snap");
    // A bad-magic snapshot fails the header parse (Status::Fail), but the pairing
    // item is appended regardless — that is the wiring under test.
    std::fs::write(&snap, b"GARBAGE!").expect("write garbage snapshot");
    snapshot::write_provenance_sidecar(&snap, &prov_with("abc123def456")).expect("write sidecar");

    let build = build_with("abc123def456", None);
    let check = check_snapshot_layout(&snap, &build);
    assert!(
        check
            .items
            .iter()
            .any(|i| i.contains("snapshot built by") && i.contains("MATCH")),
        "pairing item must be appended from the sidecar; items={:?}",
        check.items
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// --- Check 6: durability --------------------------------------------------

#[test]
fn test_is_under_tmp_detects_tmp_paths() {
    assert!(is_under_tmp(Path::new("/tmp/corpus.jsonl")));
    assert!(is_under_tmp(Path::new("/private/tmp/x/y.snap")));
    assert!(!is_under_tmp(Path::new(
        "/Use\x72s/me/isabelle-work/corpus.jsonl"
    )));
}

#[test]
fn test_check_durability_tmp_path_warns() {
    let cfg = DoctorConfig {
        ops_dir: PathBuf::from("/tmp/isabelle-work"),
        corpus: Some(PathBuf::from("/Use\x72s/me/durable/corpus.jsonl")),
        snapshot: None,
        afp_thys: None,
        isabelle_src: None,
        verify_lock: None,
        disk_threshold_gib: 100,
        strictness: Strictness::Advisory,
    };
    let check = check_durability(&cfg);
    assert_eq!(check.status, Status::Warn, "{:?}", check);
    assert!(check.items.iter().any(|i| i.contains("ops-dir")));
}

#[test]
fn test_check_durability_all_durable_passes() {
    let cfg = DoctorConfig {
        ops_dir: PathBuf::from("/Use\x72s/me/isabelle-work"),
        corpus: Some(PathBuf::from("/Use\x72s/me/isabelle-work/corpus.jsonl")),
        snapshot: Some(PathBuf::from("/Use\x72s/me/isabelle-work/x.snap")),
        afp_thys: None,
        isabelle_src: None,
        verify_lock: None,
        disk_threshold_gib: 100,
        strictness: Strictness::Advisory,
    };
    assert_eq!(check_durability(&cfg).status, Status::Pass);
}

// --- Check 7: disk headroom ----------------------------------------------

#[test]
fn test_parse_df_avail_kib_parses_posix_output() {
    let out = "Filesystem 1024-blocks     Used Available Capacity Mounted on\n\
               /dev/disk3s5 971350180 12345678 500000000      50% /\n";
    assert_eq!(parse_df_avail_kib(out), Some(500_000_000));
}

#[test]
fn test_parse_df_avail_kib_malformed_returns_none() {
    assert!(parse_df_avail_kib("garbage only header line\n").is_none());
    assert!(parse_df_avail_kib("").is_none());
}

#[test]
fn test_check_disk_headroom_zero_threshold_passes() {
    // Any real volume has >= 0 GiB free, so a zero threshold always passes.
    let check = check_disk_headroom(Path::new("."), 0);
    assert_eq!(check.status, Status::Pass, "{}", check.summary);
}

#[test]
fn test_check_disk_headroom_impossible_threshold_warns() {
    // No volume has this many GiB free -> low-headroom warning.
    let check = check_disk_headroom(Path::new("."), u64::MAX);
    assert_eq!(check.status, Status::Warn, "{}", check.summary);
}

#[test]
fn test_existing_ancestor_walks_up_to_existing() {
    let dir = tmpdir("anc");
    let deep = dir.join("a/b/c/never/made");
    assert_eq!(existing_ancestor(&deep), dir);
    let _ = std::fs::remove_dir_all(&dir);
}

// --- Check 8: AFP / Isabelle version skew --------------------------------

/// Build a fake AFP `thys` tree: one entry per `(name, root_body)` with a ROOT.
fn write_afp_thys(dir: &Path, entries: &[(&str, &str)]) -> PathBuf {
    let thys = dir.join("thys");
    for (name, body) in entries {
        let entry = thys.join(name);
        std::fs::create_dir_all(&entry).expect("mk afp entry");
        std::fs::write(entry.join("ROOT"), body).expect("write ROOT");
    }
    thys
}

/// Build a fake Isabelle `src` tree with the given `HOL/<subdir>/<theory>.thy`
/// files present.
fn write_isa_src(dir: &Path, theories: &[(&str, &str)]) -> PathBuf {
    let src = dir.join("src");
    for (subdir, theory) in theories {
        let sub = src.join("HOL").join(subdir);
        std::fs::create_dir_all(&sub).expect("mk src subdir");
        std::fs::write(sub.join(format!("{theory}.thy")), "theory stub\n").expect("write thy");
    }
    src
}

fn finding(entry: &str, qualifier: &str, theory: &str) -> AfpSkewFinding {
    AfpSkewFinding {
        entry: entry.to_string(),
        qualifier: qualifier.to_string(),
        theory: theory.to_string(),
        expected: PathBuf::from(format!("/src/HOL/{}/{theory}.thy", &qualifier[4..])),
    }
}

#[test]
fn test_session_subdir_strips_hol_prefix() {
    assert_eq!(session_subdir("HOL-Library").as_deref(), Some("Library"));
    assert_eq!(
        session_subdir("HOL-Data_Structures").as_deref(),
        Some("Data_Structures")
    );
    assert_eq!(
        session_subdir("HOL-Combinatorics").as_deref(),
        Some("Combinatorics")
    );
    // Bare `HOL` and non-distribution sessions are not mapped by this check.
    assert_eq!(session_subdir("HOL"), None);
    assert_eq!(session_subdir("HOL-"), None);
    assert_eq!(session_subdir("Foo-Bar"), None);
}

#[test]
fn test_extract_qualified_hol_theories_from_root() {
    let root = "session Foo (AFP) = \"HOL-Analysis\" +\n\
                  sessions\n    \"HOL-Library\"\n\
                  theories\n    \"HOL-Library.Multiset\"\n    \"HOL-Data_Structures.Trie\"\n\
                    Foo_Defs\n";
    let pairs = extract_qualified_hol_theories(root);
    assert!(
        pairs.contains(&("HOL-Library".to_string(), "Multiset".to_string())),
        "{pairs:?}"
    );
    assert!(
        pairs.contains(&("HOL-Data_Structures".to_string(), "Trie".to_string())),
        "{pairs:?}"
    );
    // Bare `HOL-Library` (a `sessions` entry, no dot) is NOT a qualified theory.
    assert!(
        !pairs
            .iter()
            .any(|(q, t)| q == "HOL-Library" && t == "Library"),
        "{pairs:?}"
    );
    // Local theory `Foo_Defs` (unqualified) is ignored.
    assert!(!pairs.iter().any(|(_, t)| t == "Foo_Defs"), "{pairs:?}");
}

#[test]
fn test_extract_qualified_hol_theories_dedups() {
    let root = "\"HOL-Library.Multiset\" \"HOL-Library.Multiset\" \"HOL-Library.FSet\"";
    let pairs = extract_qualified_hol_theories(root);
    let multiset = pairs.iter().filter(|(_, t)| t == "Multiset").count();
    assert_eq!(multiset, 1, "duplicate reference must collapse: {pairs:?}");
    assert_eq!(pairs.len(), 2);
}

#[test]
fn test_evaluate_afp_skew_no_findings_passes() {
    let check = evaluate_afp_skew(&[], 42);
    assert_eq!(check.status, Status::Pass, "{}", check.summary);
    assert!(
        check.summary.contains("42 AFP entries scanned"),
        "{}",
        check.summary
    );
}

#[test]
fn test_evaluate_afp_skew_findings_warn_with_counts() {
    let findings = [
        finding("EntryA", "HOL-Library", "Code_Target_Bit_Shifts"),
        finding("EntryB", "HOL-Library", "Code_Target_Bit_Shifts"),
        finding("EntryB", "HOL-Data_Structures", "Define_Time_Function"),
    ];
    let check = evaluate_afp_skew(&findings, 100);
    assert_eq!(check.status, Status::Warn, "{}", check.summary);
    // 2 distinct missing theories, referenced by 2 distinct entries.
    assert!(
        check.summary.contains("2 missing distribution theories"),
        "{}",
        check.summary
    );
    assert!(check.summary.contains("2 AFP entries"), "{}", check.summary);
    assert_eq!(
        check.items.len(),
        3,
        "one line per finding: {:?}",
        check.items
    );
}

#[test]
fn test_evaluate_afp_skew_caps_reported_findings() {
    let findings: Vec<AfpSkewFinding> = (0..50)
        .map(|i| finding(&format!("Entry{i}"), "HOL-Library", &format!("Gone{i}")))
        .collect();
    let check = evaluate_afp_skew(&findings, 900);
    assert_eq!(check.status, Status::Warn);
    // 20 detail lines + one "… and N more" line.
    assert_eq!(check.items.len(), 21, "{:?}", check.items);
    assert!(
        check.items.last().unwrap().contains("30 more"),
        "{:?}",
        check.items
    );
}

#[test]
fn test_check_afp_skew_finds_missing_theory_warns() {
    let dir = tmpdir("afp_skew");
    let afp = write_afp_thys(
        &dir,
        &[(
            "MyEntry",
            "session MyEntry (AFP) = HOL +\n  theories\n    \
             \"HOL-Library.Present_Theory\"\n    \"HOL-Library.Gone_Theory\"\n",
        )],
    );
    // src carries Present_Theory but NOT Gone_Theory (the skew).
    let src = write_isa_src(&dir, &[("Library", "Present_Theory")]);
    let check = check_afp_skew(Some(&afp), Some(&src));
    assert_eq!(check.status, Status::Warn, "{:?}", check);
    assert!(
        check.items.iter().any(|i| i.contains("Gone_Theory")),
        "{:?}",
        check.items
    );
    assert!(
        !check.items.iter().any(|i| i.contains("Present_Theory")),
        "present theory must not be flagged: {:?}",
        check.items
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_afp_skew_all_present_passes() {
    let dir = tmpdir("afp_ok");
    let afp = write_afp_thys(
        &dir,
        &[(
            "MyEntry",
            "  theories\n    \"HOL-Library.Multiset\"\n    \"HOL-Data_Structures.Trie\"\n",
        )],
    );
    let src = write_isa_src(
        &dir,
        &[("Library", "Multiset"), ("Data_Structures", "Trie")],
    );
    let check = check_afp_skew(Some(&afp), Some(&src));
    assert_eq!(check.status, Status::Pass, "{:?}", check);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_afp_skew_finds_nested_theory_via_recursion() {
    // A theory that lives one subdirectory deep under the session dir must be
    // resolved (not falsely reported as missing).
    let dir = tmpdir("afp_nested");
    let afp = write_afp_thys(&dir, &[("E", "theories\n    \"HOL-Library.Nested_Thy\"\n")]);
    let src = write_isa_src(&dir, &[("Library/Word", "Nested_Thy")]);
    let check = check_afp_skew(Some(&afp), Some(&src));
    assert_eq!(
        check.status,
        Status::Pass,
        "nested theory must resolve via recursion: {check:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_afp_skew_missing_afp_dir_warns_not_crash() {
    let dir = tmpdir("afp_gone");
    let src = write_isa_src(&dir, &[("Library", "Multiset")]);
    let check = check_afp_skew(Some(&dir.join("does-not-exist")), Some(&src));
    assert_eq!(check.status, Status::Warn, "{:?}", check);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_afp_skew_missing_src_dir_warns_not_crash() {
    let dir = tmpdir("afp_nosrc");
    let afp = write_afp_thys(&dir, &[("E", "theories\n    \"HOL-Library.Multiset\"\n")]);
    let check = check_afp_skew(Some(&afp), Some(&dir.join("no-src")));
    assert_eq!(check.status, Status::Warn, "{:?}", check);
    assert!(
        check.summary.contains("cannot resolve"),
        "{}",
        check.summary
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_check_afp_skew_one_sided_flag_warns() {
    let dir = tmpdir("afp_onesided");
    let afp = write_afp_thys(&dir, &[("E", "theories\n    \"HOL-Library.Multiset\"\n")]);
    // Only --afp-thys given, no --isabelle-src.
    let check = check_afp_skew(Some(&afp), None);
    assert_eq!(check.status, Status::Warn, "{:?}", check);
    assert!(check.summary.contains("needs BOTH"), "{}", check.summary);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_run_doctor_adds_afp_skew_when_flags_present() {
    let dir = tmpdir("afp_wired");
    let afp = write_afp_thys(&dir, &[("E", "theories\n    \"HOL-Library.Gone\"\n")]);
    let src = write_isa_src(&dir, &[("Library", "Present")]);
    let base = |strictness| DoctorConfig {
        ops_dir: dir.clone(),
        corpus: None,
        snapshot: None,
        afp_thys: Some(afp.clone()),
        isabelle_src: Some(src.clone()),
        verify_lock: None,
        disk_threshold_gib: 0,
        strictness,
    };
    let advisory = run_doctor(&base(Strictness::Advisory), &BuildIdentity::unknown());
    let strict = run_doctor(&base(Strictness::Strict), &BuildIdentity::unknown());
    let skew_status = |r: &DoctorReport| {
        r.checks
            .iter()
            .find(|c| c.id == "afp-skew")
            .map(|c| c.status)
            .expect("afp-skew check present when both flags set")
    };
    // The skew (Gone.thy absent) is an advisory WARN; --strict escalates it.
    assert_eq!(skew_status(&advisory), Status::Warn);
    assert_eq!(skew_status(&strict), Status::Fail);
    assert!(
        !strict.ok,
        "escalated afp-skew WARN must fail the strict gate"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// --- Orchestration --------------------------------------------------------

#[test]
fn test_run_doctor_assembles_expected_checks_and_verdict() {
    let dir = tmpdir("run_all");
    // A dead-worktree script forces a FAIL so ok=false is exercised.
    std::fs::write(
        dir.join("armed.sh"),
        "bash /Use\x72s/x/.claude/worktrees/gone/go.sh\n",
    )
    .expect("write");
    let cfg = DoctorConfig {
        ops_dir: dir.clone(),
        corpus: None,
        snapshot: None,
        afp_thys: None,
        isabelle_src: None,
        verify_lock: None,
        disk_threshold_gib: 0,
        strictness: Strictness::Advisory,
    };
    let report = run_doctor(&cfg, &BuildIdentity::unknown());
    // binary-identity, verify-busy, dead-script-refs, durability, disk-headroom.
    assert_eq!(report.checks.len(), 5, "{:#?}", report.checks);
    assert!(!report.ok, "the dead worktree ref must fail the gate");
    assert!(report.fail >= 1);
    // The human render must mention the verdict and every check id.
    let text = render_human(&report, &cfg, &BuildIdentity::unknown());
    assert!(text.contains("dead-script-refs"));
    assert!(text.contains("=>  FAIL"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_run_doctor_json_serializes() {
    let dir = tmpdir("run_json");
    let cfg = DoctorConfig {
        ops_dir: dir.clone(),
        corpus: None,
        snapshot: None,
        afp_thys: None,
        isabelle_src: None,
        verify_lock: None,
        disk_threshold_gib: 0,
        strictness: Strictness::Advisory,
    };
    let report = run_doctor(&cfg, &BuildIdentity::unknown());
    let json = serde_json::to_string(&report).expect("serialize report");
    assert!(json.contains("\"checks\""));
    assert!(json.contains("\"ok\""));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_default_ops_dir_ends_with_isabelle_work() {
    assert!(default_ops_dir().ends_with("isabelle-work"));
}

// --- --strict escalation --------------------------------------------------

#[test]
fn test_apply_strictness_escalates_listed_warn_to_fail() {
    for id in STRICT_ESCALATED_CHECKS {
        let warn = Check::new(id, Status::Warn, "advisory");
        let out = apply_strictness(warn, Strictness::Strict);
        assert_eq!(
            out.status,
            Status::Fail,
            "{id} WARN must escalate under strict"
        );
        assert!(out.summary.contains("--strict"), "{}", out.summary);
    }
}

#[test]
fn test_apply_strictness_advisory_is_noop() {
    let warn = Check::new("durability", Status::Warn, "advisory");
    let out = apply_strictness(warn, Strictness::Advisory);
    assert_eq!(out.status, Status::Warn, "advisory mode leaves WARN alone");
    assert!(!out.summary.contains("--strict"));
}

#[test]
fn test_apply_strictness_leaves_pass_and_unlisted_warn() {
    // A PASS is never escalated, even for a listed check.
    let pass = apply_strictness(
        Check::new("disk-headroom", Status::Pass, "ok"),
        Strictness::Strict,
    );
    assert_eq!(pass.status, Status::Pass);
    // A WARN on a check NOT in the escalation set (e.g. an unknown lock) stays WARN.
    let other = apply_strictness(
        Check::new("verify-busy", Status::Warn, "could not probe"),
        Strictness::Strict,
    );
    assert_eq!(
        other.status,
        Status::Warn,
        "only listed advisory checks escalate"
    );
}

#[test]
fn test_run_doctor_strict_escalates_unknown_binary_warn_to_fail() {
    let dir = tmpdir("strict_bin");
    // An unknown build identity is an advisory WARN for binary-identity; verify
    // it flips to FAIL under strict and stays WARN under advisory (robust to
    // whatever else the host reports).
    let base = |strictness| DoctorConfig {
        ops_dir: dir.clone(),
        corpus: None,
        snapshot: None,
        afp_thys: None,
        isabelle_src: None,
        verify_lock: None,
        disk_threshold_gib: 0,
        strictness,
    };
    let advisory = run_doctor(&base(Strictness::Advisory), &BuildIdentity::unknown());
    let strict = run_doctor(&base(Strictness::Strict), &BuildIdentity::unknown());
    let bin_status = |r: &DoctorReport| {
        r.checks
            .iter()
            .find(|c| c.id == "binary-identity")
            .map(|c| c.status)
            .expect("binary-identity check present")
    };
    assert_eq!(
        bin_status(&advisory),
        Status::Warn,
        "advisory keeps it a WARN"
    );
    assert_eq!(
        bin_status(&strict),
        Status::Fail,
        "strict escalates it to FAIL"
    );
    assert!(!strict.ok, "an escalated WARN must fail the gate");
    let _ = std::fs::remove_dir_all(&dir);
}
