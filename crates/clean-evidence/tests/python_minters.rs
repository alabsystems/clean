// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_evidence::envelope::python_minters::{read_record, InventoryError, RECORD_PATH};
use clean_evidence::envelope::{
    EvidenceEnvelope, FreshnessPolicy, FreshnessState, SchemaVersion, TreeState,
};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::Write,
    path::Path,
    process::{Command, Output, Stdio},
};
use tempfile::TempDir;

const REGISTRY_PATH: &str = "data/gate_registry.json";
const BASELINE_PATH: &str = "data/python_minters_baseline.json";
const REGISTRY: &[u8] = br#"{
  "schema": "clean.gate-registry/v1",
  "rows": [
    {"id": "first", "path": "scripts/shared.py", "implemented_by": "scripts/shared.py"},
    {"id": "second", "path": "scripts/shared.py"},
    {"id": "suite", "path": "", "implemented_by": "scripts/shared.py"},
    {"id": "other", "path": "scripts/file.py.txt", "implemented_by": "scripts/file.PY"}
  ]
}
"#;

fn git_command(root: &Path) -> Command {
    let mut command = Command::new("git");
    for (name, _) in std::env::vars_os() {
        if name
            .as_encoded_bytes()
            .get(..4)
            .is_some_and(|prefix| prefix.eq_ignore_ascii_case(b"GIT_"))
        {
            command.env_remove(name);
        }
    }
    command
        .current_dir(root)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", root.join("absent.gitconfig"));
    command
}

fn git(root: &Path, args: &[&str]) -> Vec<u8> {
    let output = git_command(root)
        .args(args)
        .output()
        .expect("run Git in the fixture");
    assert!(output.status.success(), "git {args:?}: {output:?}");
    output.stdout
}

fn git_id(root: &Path, args: &[&str]) -> String {
    String::from_utf8(git(root, args))
        .expect("Git object ID")
        .trim()
        .to_owned()
}

fn commit(root: &Path, message: &str) -> String {
    git(
        root,
        &[
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "--quiet",
            "-m",
            message,
        ],
    );
    git_id(root, &["rev-parse", "HEAD"])
}

fn write_index_entries(root: &Path, entries: &[u8]) {
    let mut writer = git_command(root)
        .args(["update-index", "-z", "--index-info"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("open raw Git index writer");
    writer
        .stdin
        .take()
        .expect("raw index stdin")
        .write_all(entries)
        .expect("write raw index entries");
    let written = writer.wait_with_output().expect("read raw index result");
    assert!(written.status.success(), "{written:?}");
}

fn write(root: &Path, relative: &str, bytes: &[u8]) {
    let file = root.join(relative);
    fs::create_dir_all(file.parent().expect("fixture parent")).expect("create fixture directory");
    fs::write(file, bytes).expect("write fixture");
}

fn fixture() -> TempDir {
    let repo = tempfile::tempdir().expect("new Git fixture");
    let root = repo.path();
    git(root, &["init", "--quiet"]);
    write(root, REGISTRY_PATH, REGISTRY);
    git(root, &["add", "--", REGISTRY_PATH]);
    repo
}

fn evidence_command(cwd: &Path, verb: &str, subject: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean-evidence"));
    command.current_dir(cwd).args([verb, subject]);
    command
}

fn inventory(cwd: &Path) -> Command {
    evidence_command(cwd, "inventory", "python-minters")
}

fn record(cwd: &Path) -> Command {
    evidence_command(cwd, "record", "python-minters")
}

fn run(root: &Path) -> Output {
    inventory(root)
        .output()
        .expect("run Python minter inventory")
}

fn membership(root: &Path) -> Output {
    evidence_command(root, "inventory", "python-minters-membership")
        .output()
        .expect("run Python minter membership inventory")
}

fn check(root: &Path) -> Output {
    evidence_command(root, "check", "python-minters")
        .output()
        .expect("run Python minter membership check")
}

fn expect_check_ok(root: &Path) {
    expect_check_output(check(root));
}

fn expect_check_output(output: Output) {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(output.stdout, b"PYTHON_MINTERS=ok\n", "{output:?}");
}

fn published(root: &Path, prior: &str) -> Output {
    evidence_command(root, "check", "python-minters")
        .args(["--published", prior])
        .output()
        .expect("run published Python membership check")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn fixture_baseline(paths: &[&[u8]]) -> Value {
    json!({
        "registry_implemented_by": [
            {"id": "first", "path": "scripts/shared.py"},
            {"id": "suite", "path": "scripts/shared.py"},
        ],
        "registry_path": [
            {"id": "first", "path": "scripts/shared.py"},
            {"id": "second", "path": "scripts/shared.py"},
        ],
        "schema": "clean.python_minters_baseline/v1",
        "tracked_scripts_hex": paths.iter().map(|path| hex(path)).collect::<Vec<_>>()
    })
}

fn write_baseline(root: &Path, baseline: &Value) {
    let mut bytes = serde_json::to_vec_pretty(baseline).expect("serialize test baseline");
    bytes.push(b'\n');
    write(root, BASELINE_PATH, &bytes);
}

fn stage_baseline(root: &Path, baseline: &Value) {
    write_baseline(root, baseline);
    git(root, &["add", "--", BASELINE_PATH]);
}

fn staged_script(root: &Path, path: &str) {
    write(root, path, b"fixture\n");
    git(root, &["add", "--", path]);
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn expect_inventory(output: Output, scripts: &[u8], registry: &[u8], counts: [usize; 3]) {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let [registry_path, registry_implemented_by, registry_rows] = counts;
    let tracked_scripts = scripts.iter().filter(|&&byte| byte == 0).count();
    let observed: Value =
        serde_json::from_slice(&output.stdout).expect("one inventory JSON object");
    assert_eq!(
        observed,
        json!({
            "figure": "tooling.python_minters",
            "tracked_scripts": tracked_scripts,
            "registry_path": registry_path,
            "registry_implemented_by": registry_implemented_by,
            "registry_rows": registry_rows,
            "tracked_scripts_sha256": sha256(scripts),
            "gate_registry_sha256": sha256(registry)
        })
    );
}

fn expect_record(output: Output, scripts: &[u8], registry: &[u8]) -> EvidenceEnvelope {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let envelope = EvidenceEnvelope::parse_canonical(&output.stdout)
        .expect("one canonical Python tooling evidence record");
    assert_eq!(envelope.schema, SchemaVersion::CURRENT);
    assert_eq!(envelope.figure, "tooling.python_minters");
    assert_eq!(envelope.freshness.policy, FreshnessPolicy::InputDigest);
    assert_eq!(envelope.freshness.state, FreshnessState::Fresh);
    let provenance = &envelope.provenance;
    assert!(!provenance.inputs_moved_during_run);
    assert_eq!(provenance.producer.id, "clean-evidence/python-minters");
    assert!(provenance.binary.is_none());
    assert!(envelope.rows_file.is_none());
    assert!(envelope.rows_sha256.is_none());
    assert!(envelope.denominator.is_none());
    assert!(!envelope.non_claims.is_empty());
    assert_eq!(envelope.gate_command, "scripts/local_gate.sh --fast");

    let paths_digest = sha256(scripts);
    let registry_digest = sha256(registry);
    let inputs = &provenance.inputs;
    assert_eq!(inputs.files.len(), 2);
    assert_eq!(inputs.files["data/gate_registry.json"], registry_digest);
    assert_eq!(inputs.files["git-index:scripts/**/*.py"], paths_digest);
    let framed = format!(
        "data/gate_registry.json\0{registry_digest}\ngit-index:scripts/**/*.py\0{paths_digest}\n"
    );
    assert_eq!(inputs.digest, sha256(framed.as_bytes()));
    envelope
}

fn expect_failure(output: Output, status: i32) {
    assert_eq!(output.status.code(), Some(status), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(!output.stderr.is_empty(), "{output:?}");
}

#[test]
fn saved_record_recomputes_freshness_from_both_inputs() {
    let repo = fixture();
    let root = repo.path();
    staged_script(root, "scripts/one.py");
    commit(root, "original script");
    let output = record(root).output().expect("record the fixture");
    let mut envelope = expect_record(output, b"scripts/one.py\0", REGISTRY);
    envelope.freshness.state = FreshnessState::Unknown;
    write(root, RECORD_PATH, &envelope.to_canonical_json().unwrap());
    assert!(read_record(root).unwrap().fresh);

    git(root, &["mv", "scripts/one.py", "scripts/two.py"]);
    envelope.freshness.state = FreshnessState::Fresh;
    write(root, RECORD_PATH, &envelope.to_canonical_json().unwrap());
    assert!(!read_record(root).unwrap().fresh);
    git(root, &["mv", "scripts/two.py", "scripts/one.py"]);

    let mut registry = REGISTRY.to_vec();
    registry.push(b' ');
    write(root, REGISTRY_PATH, &registry);
    assert!(!read_record(root).unwrap().fresh);
    fs::remove_file(root.join(REGISTRY_PATH)).unwrap();
    assert!(matches!(
        read_record(root),
        Err(InventoryError::Unavailable(_))
    ));
}

#[test]
fn saved_record_refuses_wrong_counts_and_inconsistent_digests() {
    let repo = fixture();
    let root = repo.path();
    commit(root, "original registry");
    let output = record(root).output().expect("record the fixture");
    let envelope = expect_record(output, b"", REGISTRY);

    let mut tampered = envelope.clone();
    tampered.value["tracked_scripts"] = json!(1);
    write(root, RECORD_PATH, &tampered.to_canonical_json().unwrap());
    let Err(InventoryError::Invalid(reason)) = read_record(root) else {
        panic!("unsubstantiated counts were accepted");
    };
    assert!(reason.contains("differ from derived counts"), "{reason}");

    let mut tampered = envelope.clone();
    tampered.value = json!([2, 2, 4, 0]);
    write(root, RECORD_PATH, &tampered.to_canonical_json().unwrap());
    let Err(InventoryError::Invalid(reason)) = read_record(root) else {
        panic!("positional counts were accepted");
    };
    assert!(reason.contains("expected an object"), "{reason}");

    let mut tampered = envelope;
    tampered.provenance.inputs.digest = "0".repeat(64);
    write(root, RECORD_PATH, &tampered.to_canonical_json().unwrap());
    let Err(InventoryError::Invalid(reason)) = read_record(root) else {
        panic!("inconsistent digest was accepted");
    };
    assert!(reason.contains("input aggregate digest"), "{reason}");
}

#[test]
fn inventory_follows_the_index_and_exact_worktree_registry() {
    let repo = fixture();
    let root = repo.path();
    let counts = [2, 2, 4];
    expect_inventory(run(root), b"", REGISTRY, counts);

    for path in [
        "scripts/root.py",
        "scripts/nested/two words.py",
        "scripts/ignored.PY",
        "scripts/ignored.py.txt",
        "other/outside.py",
    ] {
        write(root, path, b"fixture\n");
        git(root, &["add", "--", path]);
    }
    write(root, "scripts/untracked.py", b"fixture\n");
    let initial = b"scripts/nested/two words.py\0scripts/root.py\0";
    expect_inventory(run(root), initial, REGISTRY, counts);

    fs::remove_file(root.join("scripts/root.py")).expect("unstaged removal");
    expect_inventory(run(root), initial, REGISTRY, counts);
    git(
        root,
        &["rm", "--cached", "--quiet", "--", "scripts/root.py"],
    );
    expect_inventory(
        run(root),
        b"scripts/nested/two words.py\0",
        REGISTRY,
        counts,
    );

    git(root, &["add", "--", "scripts/untracked.py"]);
    let changed_registry = br#"{"schema":"clean.gate-registry/v1","rows":[
        {"path":"scripts/untracked.py"},
        {"path":"","implemented_by":"scripts/elsewhere.py"}
    ]} "#;
    write(root, REGISTRY_PATH, changed_registry);
    expect_inventory(
        run(root),
        b"scripts/nested/two words.py\0scripts/untracked.py\0",
        changed_registry,
        [1, 1, 2],
    );
}

#[test]
fn inventory_hashes_raw_paths_and_counts_conflicted_names_once() {
    let repo = fixture();
    let root = repo.path();
    let oid = git_id(root, &["rev-parse", ":data/gate_registry.json"]);
    let mut entries = format!("100644 {oid}\t").into_bytes();
    entries.extend_from_slice(b"scripts/raw-\xff.py\0");
    for stage in [1, 2, 3] {
        entries
            .extend_from_slice(format!("100644 {oid} {stage}\tscripts/conflicted.py\0").as_bytes());
    }
    write_index_entries(root, &entries);
    expect_inventory(
        run(root),
        b"scripts/conflicted.py\0scripts/raw-\xff.py\0",
        REGISTRY,
        [2, 2, 4],
    );
    let baseline = fixture_baseline(&[b"scripts/conflicted.py", b"scripts/raw-\xff.py"]);
    write_baseline(root, &baseline);
    let output = membership(root);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(
        output.stdout,
        fs::read(root.join(BASELINE_PATH)).expect("canonical fixture baseline"),
    );
    expect_check_ok(root);
}

#[test]
fn inventory_refuses_invalid_registry_documents() {
    let repo = fixture();
    let root = repo.path();
    for invalid in [
        b"{".as_slice(),
        br#"["clean.gate-registry/v1",[]]"#,
        br#"{"schema":"wrong","rows":[]}"#,
        br#"{"schema":"clean.gate-registry/v1","rows":[],"rows":[]}"#,
        br#"{"schema":"clean.gate-registry/v1","rows":[["scripts/x.py","scripts/y.py"]]}"#,
        br#"{"schema":"clean.gate-registry/v1","rows":[{"implemented_by":"scripts/test.py"}]}"#,
        br#"{"schema":"clean.gate-registry/v1","rows":[{"path":1}]}"#,
        br#"{"schema":"clean.gate-registry/v1","rows":[{"path":"","implemented_by":1}]}"#,
    ] {
        write(root, REGISTRY_PATH, invalid);
        expect_failure(run(root), 1);
    }
}

#[test]
fn inventory_uses_the_explicit_root_and_refuses_missing_inputs() {
    let repo = fixture();
    let root = repo.path();
    let outside = tempfile::tempdir().expect("unrelated working directory");
    let missing = outside.path().join("missing");
    let result = inventory(outside.path())
        .arg("--repo-root")
        .arg(root)
        .env("GIT_DIR", &missing)
        .env("GIT_WORK_TREE", &missing)
        .env("GIT_INDEX_FILE", &missing)
        .output()
        .expect("inventory from a different cwd");
    expect_inventory(result, b"", REGISTRY, [2, 2, 4]);

    expect_failure(run(outside.path()), 3);
    expect_failure(run(&root.join("data")), 3);
    fs::remove_file(root.join(REGISTRY_PATH)).expect("remove fixture registry");
    expect_failure(run(root), 3);
}

#[test]
fn inventory_refuses_incomplete_or_repeated_cli_options() {
    let repo = fixture();
    for args in [
        &["--repo-root"][..],
        &["--repo-root", ".", "--repo-root", "."],
        &["--unknown"],
    ] {
        let output = inventory(repo.path())
            .args(args)
            .output()
            .expect("run invalid inventory command");
        expect_failure(output, 2);
    }
}

#[test]
fn check_accepts_tracked_deletion_and_refuses_a_same_count_replacement() {
    let repo = fixture();
    let root = repo.path();
    let previous = "scripts/nested/previous.py";
    let replacement = "scripts/nested/replacement.py";
    write(root, previous, b"fixture\n");
    git(root, &["add", "--", previous]);
    write_baseline(root, &fixture_baseline(&[previous.as_bytes()]));
    expect_check_ok(root);

    write(root, replacement, b"fixture\n");
    expect_check_ok(root);
    git(root, &["rm", "--cached", "--quiet", "--", previous]);
    expect_check_ok(root);
    git(root, &["add", "--", replacement]);
    expect_inventory(
        run(root),
        b"scripts/nested/replacement.py\0",
        REGISTRY,
        [2, 2, 4],
    );
    expect_failure(check(root), 1);
}

#[test]
fn check_binds_registry_ids_and_columns_independently() {
    let repo = fixture();
    let root = repo.path();
    write_baseline(root, &fixture_baseline(&[]));
    expect_check_ok(root);

    let original: Value = serde_json::from_slice(REGISTRY).expect("decode fixture registry");
    let mut new_id = original.clone();
    new_id["rows"][1]["id"] = json!("new-path-row");
    let mut new_path = original.clone();
    new_path["rows"][1]["path"] = json!("scripts/replacement.py");
    let mut new_column = original.clone();
    new_column["rows"][1] = json!({
        "id": "second", "path": "", "implemented_by": "scripts/shared.py"
    });
    new_column["rows"][2] = json!({"id": "suite", "path": "scripts/shared.py"});
    for changed in [new_id, new_path, new_column] {
        let bytes = serde_json::to_vec(&changed).expect("encode one-for-one registry change");
        write(root, REGISTRY_PATH, &bytes);
        expect_inventory(run(root), b"", &bytes, [2, 2, 4]);
        expect_failure(check(root), 1);
    }

    let mut subset = original;
    subset["rows"]
        .as_array_mut()
        .expect("registry rows")
        .remove(1);
    let bytes = serde_json::to_vec(&subset).expect("encode registry row deletion");
    write(root, REGISTRY_PATH, &bytes);
    expect_check_ok(root);
}

#[test]
fn check_refuses_an_unavailable_or_noncanonical_baseline() {
    let repo = fixture();
    let root = repo.path();
    expect_failure(check(root), 3);
    let valid = fixture_baseline(&[b"scripts/a.py", b"scripts/b.py"]);
    write_baseline(root, &valid);
    expect_check_ok(root);

    write(root, BASELINE_PATH, b"{");
    expect_failure(check(root), 1);
    let compact = serde_json::to_vec(&valid).expect("encode compact baseline");
    write(root, BASELINE_PATH, &compact);
    expect_failure(check(root), 1);
    let mut wrong_schema = valid.clone();
    wrong_schema["schema"] = json!("clean.python_minters_baseline/v2");
    write_baseline(root, &wrong_schema);
    expect_failure(check(root), 1);

    for field in [
        "tracked_scripts_hex",
        "registry_path",
        "registry_implemented_by",
    ] {
        let mut reordered = valid.clone();
        reordered[field]
            .as_array_mut()
            .expect("baseline members")
            .reverse();
        write_baseline(root, &reordered);
        expect_failure(check(root), 1);

        let mut duplicate = valid.clone();
        let members = duplicate[field].as_array_mut().expect("baseline members");
        let repeated = members[0].clone();
        members.insert(1, repeated);
        write_baseline(root, &duplicate);
        expect_failure(check(root), 1);
    }
    for path in [hex(b"scripts/a.py").to_uppercase(), "not-hex".to_owned()] {
        let mut invalid_hex = valid.clone();
        invalid_hex["tracked_scripts_hex"][0] = json!(path);
        write_baseline(root, &invalid_hex);
        expect_failure(check(root), 1);
    }
}

#[test]
fn membership_commands_require_unique_nonempty_registry_ids() {
    let repo = fixture();
    let root = repo.path();
    write_baseline(root, &fixture_baseline(&[]));

    let original: Value = serde_json::from_slice(REGISTRY).expect("decode fixture registry");
    for invalid_row in [
        json!({"path": ""}),
        json!({"id": "", "path": ""}),
        json!({"id": 42, "path": ""}),
        json!({"id": "first", "path": ""}),
    ] {
        let mut invalid = original.clone();
        invalid["rows"][3] = invalid_row;
        let bytes = serde_json::to_vec(&invalid).expect("encode invalid registry ID");
        write(root, REGISTRY_PATH, &bytes);
        expect_failure(membership(root), 1);
        expect_failure(check(root), 1);
    }
}

#[test]
fn membership_commands_validate_explicit_roots_and_options() {
    let repo = fixture();
    let root = repo.path();
    write_baseline(root, &fixture_baseline(&[]));
    let unrelated = tempfile::tempdir().expect("unrelated directory");
    for (verb, subject) in [
        ("check", "python-minters"),
        ("inventory", "python-minters-membership"),
    ] {
        let command = || evidence_command(unrelated.path(), verb, subject);
        let output = command()
            .arg("--repo-root")
            .arg(root)
            .output()
            .expect("run against the explicit fixture root");
        assert!(output.status.success(), "{output:?}");
        expect_failure(command().output().expect("run outside a Git root"), 3);
        for args in [
            &["--repo-root"][..],
            &["--repo-root", ".", "--repo-root", "."],
            &["--unknown"],
        ] {
            let output = command().args(args).output().expect("run invalid options");
            expect_failure(output, 2);
        }
    }
}

#[test]
fn published_check_requires_exact_staged_membership_and_preserves_retirements() {
    let repo = fixture();
    let root = repo.path();
    let kept = "scripts/kept.py";
    let retired = "scripts/retired.py";
    staged_script(root, kept);
    staged_script(root, retired);
    let initial = fixture_baseline(&[kept.as_bytes(), retired.as_bytes()]);
    let smaller = fixture_baseline(&[kept.as_bytes()]);
    stage_baseline(root, &initial);
    let prior = commit(root, "publish initial membership");
    expect_check_output(published(root, &prior));

    stage_baseline(root, &smaller);
    expect_failure(published(root, &prior), 1);
    stage_baseline(root, &initial);
    git(root, &["rm", "--cached", "--quiet", "--", retired]);
    write_baseline(root, &smaller);
    expect_failure(published(root, &prior), 1);

    stage_baseline(root, &smaller);
    expect_check_output(published(root, &prior));
    let shrunken = commit(root, "publish retirement");
    expect_check_output(published(root, &shrunken));

    git(root, &["add", "--", retired]);
    stage_baseline(root, &initial);
    expect_check_ok(root);
    expect_failure(published(root, &shrunken), 1);
}

#[test]
fn published_check_refuses_self_approval_and_ignores_worktree_only_edits() {
    let repo = fixture();
    let root = repo.path();
    let incumbent = "scripts/old.py";
    let replacement = "scripts/new.py";
    staged_script(root, incumbent);
    let initial = fixture_baseline(&[incumbent.as_bytes()]);
    stage_baseline(root, &initial);
    let prior = commit(root, "publish original paths");

    git(root, &["rm", "--cached", "--quiet", "--", incumbent]);
    staged_script(root, replacement);
    stage_baseline(root, &fixture_baseline(&[replacement.as_bytes()]));
    expect_check_ok(root);
    expect_failure(published(root, &prior), 1);

    git(root, &["rm", "--cached", "--quiet", "--", replacement]);
    git(root, &["add", "--", incumbent]);
    let mut registry: Value = serde_json::from_slice(REGISTRY).expect("decode fixture registry");
    registry["rows"][1]["id"] = json!("replacement");
    let changed = serde_json::to_vec(&registry).expect("encode replacement row ID");
    write(root, REGISTRY_PATH, &changed);
    git(root, &["add", "--", REGISTRY_PATH]);
    let mut proposal = initial.clone();
    proposal["registry_path"][1]["id"] = json!("replacement");
    stage_baseline(root, &proposal);
    expect_check_ok(root);
    expect_failure(published(root, &prior), 1);

    write(root, REGISTRY_PATH, REGISTRY);
    write_baseline(root, &initial);
    expect_check_ok(root);
    expect_failure(published(root, &prior), 1);

    git(root, &["add", "--", REGISTRY_PATH, BASELINE_PATH]);
    write(root, REGISTRY_PATH, b"{");
    write(root, BASELINE_PATH, b"{");
    expect_check_output(published(root, &prior));
}

#[test]
fn published_check_uses_prior_live_membership_when_the_prior_baseline_is_stale() {
    let repo = fixture();
    let root = repo.path();
    let retired = "scripts/retired.py";
    staged_script(root, retired);
    stage_baseline(root, &fixture_baseline(&[retired.as_bytes()]));
    commit(root, "publish original member");
    git(root, &["rm", "--cached", "--quiet", "--", retired]);
    let stale = commit(root, "retire script without updating the old baseline");

    git(root, &["add", "--", retired]);
    expect_check_ok(root);
    expect_failure(published(root, &stale), 1);
}

#[test]
fn published_check_validates_commit_type_ancestry_and_git_context() {
    let repo = fixture();
    let root = repo.path();
    let missing_baseline = commit(root, "commit before any baseline");
    stage_baseline(root, &fixture_baseline(&[]));
    let prior = commit(root, "publish baseline");
    expect_failure(published(root, &missing_baseline), 3);
    expect_failure(published(root, &"0".repeat(prior.len())), 3);
    expect_failure(published(root, "HEAD"), 1);
    expect_failure(published(root, &"A".repeat(prior.len())), 1);

    let tree = git_id(root, &["rev-parse", "HEAD^{tree}"]);
    expect_failure(published(root, &tree), 1);
    let unrelated = git_id(
        root,
        &[
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit-tree",
            &tree,
            "-m",
            "unrelated root with the same files",
        ],
    );
    expect_failure(published(root, &unrelated), 1);

    let outside = tempfile::tempdir().expect("unrelated working directory");
    let bogus = outside.path().join("missing");
    let output = evidence_command(outside.path(), "check", "python-minters")
        .arg("--repo-root")
        .arg(root)
        .args(["--published", &prior])
        .env("GIT_DIR", &bogus)
        .env("GIT_WORK_TREE", &bogus)
        .env("GIT_INDEX_FILE", &bogus)
        .env("GIT_CONFIG_COUNT", "1")
        .env("GIT_CONFIG_KEY_0", "core.bare")
        .env("GIT_CONFIG_VALUE_0", "true")
        .output()
        .expect("check explicit root with inherited Git overrides");
    expect_check_output(output);

    for options in [
        &["--published"][..],
        &["--published", &prior, "--published", &prior],
    ] {
        let output = evidence_command(root, "check", "python-minters")
            .args(options)
            .output()
            .expect("check invalid publication arguments");
        expect_failure(output, 2);
    }

    let output = inventory(root)
        .args(["--published", &prior])
        .output()
        .expect("inventory with an unsupported publication argument");
    expect_failure(output, 2);
}

#[test]
fn published_check_refuses_conflicted_staged_baseline() {
    let repo = fixture();
    let root = repo.path();
    stage_baseline(root, &fixture_baseline(&[]));
    let prior = commit(root, "publish baseline");
    let oid = git_id(root, &["rev-parse", ":data/python_minters_baseline.json"]);
    git(root, &["rm", "--cached", "--quiet", "--", BASELINE_PATH]);
    let entries: String = [1, 2, 3]
        .into_iter()
        .map(|stage| format!("100644 {oid} {stage}\t{BASELINE_PATH}\0"))
        .collect();
    write_index_entries(root, entries.as_bytes());
    expect_failure(published(root, &prior), 1);
}

#[test]
fn record_renders_canonical_inventory_for_the_explicit_clean_root() {
    let repo = fixture();
    let root = repo.path();
    staged_script(root, "scripts/root.py");
    staged_script(root, "scripts/nested/two words.py");
    let head = commit(root, "record clean inventory");
    let outside = tempfile::tempdir().expect("unrelated working directory");
    let missing = outside.path().join("missing");
    let output = record(outside.path())
        .arg("--repo-root")
        .arg(root)
        .env("GIT_DIR", &missing)
        .env("GIT_INDEX_FILE", &missing)
        .env("GIT_CONFIG_COUNT", "1")
        .env("GIT_CONFIG_KEY_0", "core.worktree")
        .env("GIT_CONFIG_VALUE_0", &missing)
        .output()
        .expect("record in an explicit root with inherited Git overrides");
    let scripts = b"scripts/nested/two words.py\0scripts/root.py\0";
    let envelope = expect_record(output, scripts, REGISTRY);
    expect_inventory(run(root), scripts, REGISTRY, [2, 2, 4]);
    assert_eq!(
        envelope.value,
        json!({
            "tracked_scripts": 2,
            "registry_path": 2,
            "registry_implemented_by": 2,
            "registry_rows": 4
        })
    );
    assert_eq!(envelope.provenance.clean_commit, head);
    assert_eq!(envelope.provenance.tree_state, TreeState::Clean);
    assert_eq!(
        envelope.provenance.producer.argv,
        [
            "clean-evidence".to_owned(),
            "record".to_owned(),
            "python-minters".to_owned(),
            "--repo-root".to_owned(),
            root.to_string_lossy().into_owned(),
        ]
    );
    assert!(git(root, &["status", "--porcelain=v1", "-z"]).is_empty());
}

#[test]
fn record_binds_equal_count_changes_and_allows_observation_of_a_refused_proposal() {
    let repo = fixture();
    let root = repo.path();
    let old = "scripts/old.py";
    let new = "scripts/new.py";
    staged_script(root, old);
    stage_baseline(root, &fixture_baseline(&[old.as_bytes()]));
    let head = commit(root, "publish original paths");
    let initial = expect_record(
        record(root).output().expect("record initial inputs"),
        b"scripts/old.py\0",
        REGISTRY,
    );
    expect_check_output(published(root, &head));

    git(root, &["rm", "--cached", "--quiet", "--", old]);
    staged_script(root, new);
    stage_baseline(root, &fixture_baseline(&[new.as_bytes()]));
    let swapped = expect_record(
        record(root).output().expect("record staged replacement"),
        b"scripts/new.py\0",
        REGISTRY,
    );
    assert_eq!(swapped.provenance.clean_commit, head);
    assert_eq!(swapped.provenance.tree_state, TreeState::Dirty);
    assert_eq!(initial.value, swapped.value);
    assert_ne!(
        initial.provenance.inputs.digest,
        swapped.provenance.inputs.digest
    );
    expect_failure(published(root, &head), 1);

    let mut changed_registry = REGISTRY.to_vec();
    changed_registry.extend_from_slice(b" \t\n");
    write(root, REGISTRY_PATH, &changed_registry);
    let unstaged = expect_record(
        record(root)
            .output()
            .expect("record worktree registry bytes"),
        b"scripts/new.py\0",
        &changed_registry,
    );
    assert_eq!(swapped.value, unstaged.value);
    assert_eq!(
        swapped.provenance.inputs.files["git-index:scripts/**/*.py"],
        unstaged.provenance.inputs.files["git-index:scripts/**/*.py"]
    );
    assert_ne!(
        swapped.provenance.inputs.digest,
        unstaged.provenance.inputs.digest
    );
}

#[test]
fn record_refuses_unavailable_inputs_malformed_registry_and_publication_options() {
    let repo = fixture();
    let root = repo.path();
    expect_failure(record(root).output().expect("record before commit"), 3);
    let head = commit(root, "create observed revision");
    expect_failure(
        record(&root.join("data"))
            .output()
            .expect("record from a nested directory"),
        3,
    );
    expect_failure(
        record(root)
            .args(["--published", &head])
            .output()
            .expect("record with publication option"),
        2,
    );
    write(root, REGISTRY_PATH, b"{");
    expect_failure(record(root).output().expect("record malformed registry"), 1);
    fs::remove_file(root.join(REGISTRY_PATH)).expect("remove worktree registry");
    expect_failure(
        record(root)
            .output()
            .expect("record missing worktree registry"),
        3,
    );
}
