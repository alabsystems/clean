// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `isabelle-fetch`: the committed manifest, the real `curl` against
//! an HTTP server on 127.0.0.1, the real `git` against a local bare upstream,
//! and a recording fake that proves `--dry` starts nothing.

use std::cell::Cell;
use std::io::{Read as _, Write as _};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use sha2::{Digest as _, Sha256};

use super::fetch::{CheckoutState, Fetcher, Progress, SystemFetcher};
use super::manifest::{
    AfpPin, AfpReleaseNote, Distribution, NotFetched, PublicInputs, EMBEDDED_MANIFEST,
    MANIFEST_REL_PATH, MANIFEST_VERSION,
};
use super::{run_fetch, FetchError, FetchOptions, FetchReport, Mode, Outcome};
use crate::math_map::bundle::hex_lower;

const BODY: &[u8] = b"not an Isabelle archive, just bytes with a pinned sha256\n";
const FILE: &str = "fixture_macos.tar.gz";

fn sha256_hex(bytes: &[u8]) -> String {
    hex_lower(&Sha256::digest(bytes)[..])
}

fn quiet() -> SystemFetcher {
    SystemFetcher {
        progress: Progress::Hide,
    }
}

/// An HTTP server thread on 127.0.0.1 that answers every request with
/// `status` (e.g. `200 OK`) and `body`. Returns the URL and a counter of
/// accepted connections.
fn serve_status(status: &'static str, body: Vec<u8>) -> (String, Arc<AtomicUsize>) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind 127.0.0.1:0");
    let port = listener.local_addr().expect("local addr").port();
    let hits = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&hits);
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            counter.fetch_add(1, Ordering::SeqCst);
            let mut request = Vec::new();
            let mut chunk = [0u8; 1024];
            while !request.windows(4).any(|w| w == b"\r\n\r\n") {
                match stream.read(&mut chunk) {
                    Ok(0) | Err(_) => break,
                    Ok(n) => request.extend_from_slice(&chunk[..n]),
                }
            }
            let head = format!(
                "HTTP/1.1 {status}\r\nContent-Type: application/octet-stream\r\n\
                 Content-Length: {}\r\nConnection: close\r\n\r\n",
                body.len()
            );
            let _ = stream.write_all(head.as_bytes());
            let _ = stream.write_all(&body);
            let _ = stream.flush();
        }
    });
    (format!("http://127.0.0.1:{port}/{FILE}"), hits)
}

fn serve(body: Vec<u8>) -> (String, Arc<AtomicUsize>) {
    serve_status("200 OK", body)
}

fn dist(url: &str, body: &[u8], sha256: &str) -> Distribution {
    Distribution {
        id: "fixture".to_string(),
        file: FILE.to_string(),
        url: url.to_string(),
        bytes: body.len() as u64,
        sha256: sha256.to_string(),
        isabelle_id: "000000000000".to_string(),
        used_by: "the test".to_string(),
    }
}

fn afp_pin(repo: &str, rev: &str) -> AfpPin {
    AfpPin {
        id: "afp".to_string(),
        repo: repo.to_string(),
        rev: rev.to_string(),
        dir: "afp".to_string(),
        depth: 1,
        commit_date: "2026-11-15".to_string(),
        used_by: "the test".to_string(),
        matching_release_not_used: AfpReleaseNote {
            repo: "https://example.invalid/afp-next.git".to_string(),
            rev: "f".repeat(40),
            note: "information only".to_string(),
        },
    }
}

/// A manifest built in memory (not validated: the tests use `http://` and
/// local-path URLs the committed manifest is not allowed to carry).
fn inputs_with(distributions: Vec<Distribution>, afp: AfpPin) -> PublicInputs {
    PublicInputs {
        version: MANIFEST_VERSION,
        recorded: "2026-11-15".to_string(),
        distributions,
        afp,
        not_fetched: vec![NotFetched {
            what: "the capture-hook edit".to_string(),
            why: "not public".to_string(),
            how_to_get_it: "apply it by hand".to_string(),
        }],
        origin: "test manifest".to_string(),
    }
}

fn opts(ids: &[&str], work: &Path, mode: Mode) -> FetchOptions {
    FetchOptions {
        work_dir: work.to_path_buf(),
        only: ids.iter().map(|id| (*id).to_string()).collect(),
        mode,
    }
}

fn run(inputs: &PublicInputs, opts: &FetchOptions, fetcher: &dyn Fetcher) -> (FetchReport, String) {
    let mut out: Vec<u8> = Vec::new();
    let report = run_fetch(inputs, opts, fetcher, &mut out).expect("run_fetch");
    (report, String::from_utf8(out).expect("utf-8 report"))
}

fn sole_outcome(report: &FetchReport) -> &Outcome {
    assert_eq!(report.items.len(), 1, "exactly one input was selected");
    &report.items[0].outcome
}

// ---------------------------------------------------------------------------
// (1) The committed manifest.
// ---------------------------------------------------------------------------

fn is_lower_hex(s: &str, len: usize) -> bool {
    s.len() == len && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

#[test]
fn test_committed_manifest_parses_with_well_formed_pins() {
    let inputs = PublicInputs::embedded().expect("the committed manifest parses");
    assert_eq!(inputs.version, MANIFEST_VERSION);
    assert_eq!(inputs.ids(), vec!["Isabelle2025", "Isabelle2025-2", "afp"]);
    for d in &inputs.distributions {
        assert!(is_lower_hex(&d.sha256, 64), "{}: sha256 {}", d.id, d.sha256);
        assert!(d.bytes > 0, "{}: bytes must be > 0", d.id);
        assert!(d.url.starts_with("https://"), "{}: {}", d.id, d.url);
    }
    assert!(
        is_lower_hex(&inputs.afp.rev, 40),
        "afp rev {}",
        inputs.afp.rev
    );
    assert!(is_lower_hex(&inputs.afp.matching_release_not_used.rev, 40));
    assert_eq!(inputs.afp.depth, 1);
    assert!(!inputs.not_fetched.is_empty());
}

/// The values measured on 2026-11-15 from the archives in ~/isabelle-work
/// (`stat -f %z`, `shasum -a 256`), the AFP checkout (`git rev-parse HEAD`) and
/// upstream (`git ls-remote`). A change here must be a deliberate re-pin.
#[test]
fn test_committed_manifest_pins_the_measured_inputs() {
    fn pin<'a>(inputs: &'a PublicInputs, id: &str) -> (&'a str, u64, &'a str) {
        let d = inputs
            .distributions
            .iter()
            .find(|d| d.id == id)
            .expect("pinned distribution");
        (d.file.as_str(), d.bytes, d.sha256.as_str())
    }
    let inputs = PublicInputs::embedded().expect("the committed manifest parses");
    assert_eq!(
        pin(&inputs, "Isabelle2025"),
        (
            "Isabelle2025_macos.tar.gz",
            1_411_408_470,
            "ea5754c228857f5d9d3ae254ec9814797f2453ea290df20b2f6dcb2ef0e2e7f8"
        )
    );
    assert_eq!(
        pin(&inputs, "Isabelle2025-2"),
        (
            "Isabelle2025-2_macos.tar.gz",
            1_730_395_791,
            "8f187496e295f169952e944745af9e4ae00c9c1cd2ed4cadbcf7d898e444913e"
        )
    );
    assert_eq!(
        inputs.afp.repo,
        "https://github.com/isabelle-prover/mirror-afp-2025.git"
    );
    assert_eq!(inputs.afp.rev, "400ee45cf836394b0b35dde6d20ab5ecd2012ee3");
    assert_eq!(
        inputs.afp.matching_release_not_used.rev,
        "fa30b560ab754bfbb7a721ee45a921d4b3c04358"
    );
}

#[test]
fn test_committed_manifest_file_matches_the_built_in_copy() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(MANIFEST_REL_PATH);
    let loaded = PublicInputs::load(&path).expect("load the committed file");
    let built_in = PublicInputs::embedded().expect("the built-in copy parses");
    assert_eq!(loaded.recorded, built_in.recorded);
    assert_eq!(loaded.distributions, built_in.distributions);
    assert_eq!(loaded.afp, built_in.afp);
    assert_eq!(loaded.not_fetched, built_in.not_fetched);
}

#[test]
fn test_manifest_rejects_malformed_pins() {
    let sha = "ea5754c228857f5d9d3ae254ec9814797f2453ea290df20b2f6dcb2ef0e2e7f8";
    let cases = [
        (EMBEDDED_MANIFEST.replace(sha, "ea5754c2"), "sha256"),
        (
            EMBEDDED_MANIFEST.replace(sha, &sha.to_uppercase()),
            "sha256",
        ),
        (
            EMBEDDED_MANIFEST.replace(
                "\"Isabelle2025_macos.tar.gz\"",
                "\"../Isabelle2025_macos.tar.gz\"",
            ),
            "single file",
        ),
        (
            EMBEDDED_MANIFEST.replace(
                "\"https://isabelle.in.tum.de/website-Isabelle2025/",
                "\"http://isabelle.in.tum.de/website-Isabelle2025/",
            ),
            "https",
        ),
        (
            EMBEDDED_MANIFEST.replace("400ee45cf836394b0b35dde6d20ab5ecd2012ee3", "400ee45c"),
            "rev",
        ),
        (
            EMBEDDED_MANIFEST.replace("\"id\": \"Isabelle2025-2\"", "\"id\": \"Isabelle2025\""),
            "twice",
        ),
        (
            EMBEDDED_MANIFEST.replace("\"bytes\": 1411408470", "\"bytes\": 0"),
            "bytes",
        ),
    ];
    for (text, needle) in &cases {
        assert_ne!(
            text, EMBEDDED_MANIFEST,
            "case `{needle}` must change the text"
        );
        match PublicInputs::parse(text, "case") {
            Err(FetchError::ManifestInvalid { reason, .. }) => {
                assert!(reason.contains(needle), "`{needle}` not in: {reason}");
            }
            other => panic!("expected ManifestInvalid mentioning `{needle}`, got {other:?}"),
        }
    }
}

#[test]
fn test_manifest_rejects_unknown_fields() {
    let text = EMBEDDED_MANIFEST.replacen("\"version\": 1,", "\"version\": 1, \"extra\": true,", 1);
    assert_ne!(text, EMBEDDED_MANIFEST);
    assert!(matches!(
        PublicInputs::parse(&text, "case"),
        Err(FetchError::ManifestParse { .. })
    ));
}

// ---------------------------------------------------------------------------
// (2) Archives: the real curl against 127.0.0.1.
// ---------------------------------------------------------------------------

fn unused_afp() -> AfpPin {
    afp_pin("https://example.invalid/afp.git", &"0".repeat(40))
}

#[test]
fn test_download_with_matching_sha256_is_renamed_into_place() {
    let work = tempfile::tempdir().expect("tempdir");
    let (url, hits) = serve(BODY.to_vec());
    let inputs = inputs_with(vec![dist(&url, BODY, &sha256_hex(BODY))], unused_afp());
    let (report, text) = run(
        &inputs,
        &opts(&["fixture"], work.path(), Mode::Fetch),
        &quiet(),
    );
    assert!(matches!(sole_outcome(&report), Outcome::Fetched), "{text}");
    let target = work.path().join(FILE);
    assert_eq!(std::fs::read(target).expect("the fetched file"), BODY);
    assert!(
        !work.path().join(format!("{FILE}.part")).exists(),
        "no .part is left"
    );
    assert_eq!(hits.load(Ordering::SeqCst), 1);
    assert!(text.contains("Not fetched by this command"), "{text}");
    report.into_result().expect("every input verified");
}

#[test]
fn test_download_with_wrong_sha256_fails_and_leaves_no_file() {
    let work = tempfile::tempdir().expect("tempdir");
    let (url, hits) = serve(BODY.to_vec());
    let inputs = inputs_with(vec![dist(&url, BODY, &"0".repeat(64))], unused_afp());
    let (report, text) = run(
        &inputs,
        &opts(&["fixture"], work.path(), Mode::Fetch),
        &quiet(),
    );
    match sole_outcome(&report) {
        Outcome::Failed(FetchError::Mismatch { actual, .. }) => {
            assert_eq!(actual, &format!("sha256 {}", sha256_hex(BODY)));
        }
        other => panic!("expected a sha256 mismatch, got {other:?}\n{text}"),
    }
    assert!(
        !work.path().join(FILE).exists(),
        "no final file on a mismatch"
    );
    assert!(
        !work.path().join(format!("{FILE}.part")).exists(),
        "no .part is left"
    );
    assert_eq!(hits.load(Ordering::SeqCst), 1);
    assert!(matches!(
        report.into_result(),
        Err(FetchError::Unverified { count: 1, .. })
    ));
}

#[test]
fn test_present_verified_file_makes_no_request() {
    let work = tempfile::tempdir().expect("tempdir");
    std::fs::write(work.path().join(FILE), BODY).expect("seed the archive");
    let (url, hits) = serve(BODY.to_vec());
    let inputs = inputs_with(vec![dist(&url, BODY, &sha256_hex(BODY))], unused_afp());
    let (report, text) = run(
        &inputs,
        &opts(&["fixture"], work.path(), Mode::Fetch),
        &quiet(),
    );
    assert!(matches!(sole_outcome(&report), Outcome::Verified), "{text}");
    assert_eq!(
        hits.load(Ordering::SeqCst),
        0,
        "a verified file is not downloaded"
    );
}

#[test]
fn test_present_differing_file_is_replaced_after_the_check() {
    let work = tempfile::tempdir().expect("tempdir");
    std::fs::write(work.path().join(FILE), b"stale").expect("seed a stale archive");
    let (url, hits) = serve(BODY.to_vec());
    let inputs = inputs_with(vec![dist(&url, BODY, &sha256_hex(BODY))], unused_afp());
    let (report, text) = run(
        &inputs,
        &opts(&["fixture"], work.path(), Mode::Fetch),
        &quiet(),
    );
    assert!(matches!(sole_outcome(&report), Outcome::Fetched), "{text}");
    assert_eq!(
        std::fs::read(work.path().join(FILE)).expect("replaced"),
        BODY
    );
    assert_eq!(hits.load(Ordering::SeqCst), 1);
}

#[test]
fn test_failed_download_leaves_no_part() {
    let work = tempfile::tempdir().expect("tempdir");
    let (url, hits) = serve_status("404 Not Found", b"no such archive\n".to_vec());
    let inputs = inputs_with(vec![dist(&url, BODY, &sha256_hex(BODY))], unused_afp());
    let (report, text) = run(
        &inputs,
        &opts(&["fixture"], work.path(), Mode::Fetch),
        &quiet(),
    );
    assert!(
        matches!(
            sole_outcome(&report),
            Outcome::Failed(FetchError::Download { .. })
        ),
        "{text}"
    );
    assert_eq!(hits.load(Ordering::SeqCst), 1, "curl does not retry a 404");
    assert!(!work.path().join(FILE).exists());
    assert!(!work.path().join(format!("{FILE}.part")).exists());
}

// ---------------------------------------------------------------------------
// (3) The AFP: the real git against a local bare upstream.
// ---------------------------------------------------------------------------

fn git_cmd(dir: &Path) -> Command {
    let mut cmd = Command::new("git");
    for var in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_COMMON_DIR",
    ] {
        cmd.env_remove(var);
    }
    cmd.arg("-C").arg(dir).args([
        "-c",
        "user.email=test@example.invalid",
        "-c",
        "user.name=Test",
        "-c",
        "commit.gpgsign=false",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "init.defaultBranch=master",
    ]);
    cmd
}

fn git_out(dir: &Path, args: &[&str]) -> String {
    let out = git_cmd(dir).args(args).output().expect("spawn git");
    assert!(
        out.status.success(),
        "git {args:?} in {}: {}",
        dir.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

fn path_str(path: &Path) -> &str {
    path.to_str().expect("utf-8 temp path")
}

/// A bare upstream whose master has two commits. Returns the upstream path,
/// the first commit (the pin) and the second (the branch tip).
fn upstream_with_two_commits(root: &Path) -> (PathBuf, String, String) {
    let upstream = root.join("upstream.git");
    let working = root.join("working");
    git_out(root, &["init", "--quiet", "--bare", path_str(&upstream)]);
    // Fetching a commit by id: allowed by protocol v2 anyway; set explicitly so
    // the test does not depend on the local git's protocol default.
    git_out(
        &upstream,
        &["config", "uploadpack.allowAnySHA1InWant", "true"],
    );
    git_out(root, &["init", "--quiet", path_str(&working)]);
    std::fs::write(working.join("ROOTS"), "first\n").expect("write");
    git_out(&working, &["add", "ROOTS"]);
    git_out(&working, &["commit", "--quiet", "-m", "first"]);
    let first = git_out(&working, &["rev-parse", "HEAD"]);
    std::fs::write(working.join("ROOTS"), "first\nsecond\n").expect("write");
    git_out(&working, &["commit", "--quiet", "-am", "second"]);
    let second = git_out(&working, &["rev-parse", "HEAD"]);
    git_out(
        &working,
        &[
            "push",
            "--quiet",
            path_str(&upstream),
            "HEAD:refs/heads/master",
        ],
    );
    (upstream, first, second)
}

#[test]
fn test_afp_fetch_pins_the_revision_not_the_branch_tip() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (upstream, first, second) = upstream_with_two_commits(tmp.path());
    assert_ne!(first, second);
    let work = tmp.path().join("work");
    let inputs = inputs_with(Vec::new(), afp_pin(path_str(&upstream), &first));
    let (report, text) = run(&inputs, &opts(&["afp"], &work, Mode::Fetch), &quiet());
    assert!(matches!(sole_outcome(&report), Outcome::Fetched), "{text}");
    let afp = work.join("afp");
    assert_eq!(git_out(&afp, &["rev-parse", "HEAD"]), first);
    assert_eq!(
        std::fs::read_to_string(afp.join("ROOTS")).expect("checked-out file"),
        "first\n"
    );
    assert!(
        !work.join("afp.part").exists(),
        "the staging checkout was renamed"
    );
    report.into_result().expect("the AFP verified");

    // A second run finds the checkout at the pin and leaves it alone.
    let (again, text) = run(&inputs, &opts(&["afp"], &work, Mode::Fetch), &quiet());
    assert!(matches!(sole_outcome(&again), Outcome::Verified), "{text}");
}

#[test]
fn test_afp_checkout_at_another_revision_is_refused_untouched() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (upstream, first, second) = upstream_with_two_commits(tmp.path());
    let work = tmp.path().join("work");
    std::fs::create_dir_all(&work).expect("work dir");
    let afp = work.join("afp");
    git_out(
        tmp.path(),
        &["clone", "--quiet", path_str(&upstream), path_str(&afp)],
    );
    std::fs::write(afp.join("local-note.txt"), "keep me").expect("write");
    let inputs = inputs_with(Vec::new(), afp_pin(path_str(&upstream), &first));
    let (report, text) = run(&inputs, &opts(&["afp"], &work, Mode::Fetch), &quiet());
    match sole_outcome(&report) {
        Outcome::Refused(FetchError::AfpOtherRev { head, rev, .. }) => {
            assert_eq!(head, &second);
            assert_eq!(rev, &first);
        }
        other => panic!("expected AfpOtherRev, got {other:?}\n{text}"),
    }
    assert_eq!(
        git_out(&afp, &["rev-parse", "HEAD"]),
        second,
        "HEAD untouched"
    );
    assert_eq!(
        std::fs::read_to_string(afp.join("local-note.txt")).expect("still there"),
        "keep me"
    );
    assert!(!work.join("afp.part").exists());
    assert!(matches!(
        report.into_result(),
        Err(FetchError::Unverified { count: 1, .. })
    ));
}

#[test]
fn test_afp_checkout_with_modified_tracked_file_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (upstream, first, _second) = upstream_with_two_commits(tmp.path());
    let work = tmp.path().join("work");
    let afp = work.join("afp");
    std::fs::create_dir_all(&work).expect("work dir");
    git_out(
        tmp.path(),
        &["clone", "--quiet", path_str(&upstream), path_str(&afp)],
    );
    git_out(&afp, &["checkout", "--quiet", "--detach", first.as_str()]);
    std::fs::write(afp.join("ROOTS"), "edited\n").expect("edit a tracked file");
    let inputs = inputs_with(Vec::new(), afp_pin(path_str(&upstream), &first));
    let (report, text) = run(&inputs, &opts(&["afp"], &work, Mode::Fetch), &quiet());
    assert!(
        matches!(
            sole_outcome(&report),
            Outcome::Refused(FetchError::AfpModified { .. })
        ),
        "{text}"
    );
    assert_eq!(
        std::fs::read_to_string(afp.join("ROOTS")).expect("still edited"),
        "edited\n"
    );
}

#[test]
fn test_afp_directory_that_is_not_a_checkout_is_refused_untouched() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let work = tmp.path().join("work");
    let afp = work.join("afp");
    std::fs::create_dir_all(&afp).expect("afp dir");
    std::fs::write(afp.join("thys.txt"), "hand-made").expect("write");
    let inputs = inputs_with(
        Vec::new(),
        afp_pin("https://example.invalid/afp.git", &"1".repeat(40)),
    );
    let (report, text) = run(&inputs, &opts(&["afp"], &work, Mode::Fetch), &quiet());
    assert!(
        matches!(
            sole_outcome(&report),
            Outcome::Refused(FetchError::AfpNotACheckout { .. })
        ),
        "{text}"
    );
    assert_eq!(
        std::fs::read_to_string(afp.join("thys.txt")).expect("still there"),
        "hand-made"
    );
}

// ---------------------------------------------------------------------------
// (4) Dry runs and selection: a recording fake.
// ---------------------------------------------------------------------------

/// Counts every call; never touches the network or the disk.
#[derive(Default)]
struct RecordingFetcher {
    downloads: Cell<usize>,
    checkouts: Cell<usize>,
    inspects: Cell<usize>,
}

impl Fetcher for RecordingFetcher {
    fn download(&self, _url: &str, _dest: &Path) -> Result<(), FetchError> {
        self.downloads.set(self.downloads.get() + 1);
        Ok(())
    }

    fn checkout_rev(
        &self,
        _repo: &str,
        _rev: &str,
        _depth: u32,
        _dir: &Path,
    ) -> Result<(), FetchError> {
        self.checkouts.set(self.checkouts.get() + 1);
        Ok(())
    }

    fn inspect_checkout(&self, _dir: &Path) -> Result<CheckoutState, FetchError> {
        self.inspects.set(self.inspects.get() + 1);
        Ok(CheckoutState::NotACheckout)
    }
}

#[test]
fn test_dry_run_fetches_nothing_and_writes_nothing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let work = tmp.path().join("not-created");
    let inputs = inputs_with(
        vec![dist("http://127.0.0.1:9/never", BODY, &sha256_hex(BODY))],
        afp_pin("https://example.invalid/afp.git", &"1".repeat(40)),
    );
    let fake = RecordingFetcher::default();
    let (report, text) = run(&inputs, &opts(&[], &work, Mode::Dry), &fake);
    assert_eq!(report.items.len(), 2, "every input is in the plan");
    assert!(
        report
            .items
            .iter()
            .all(|item| matches!(item.outcome, Outcome::Planned(_))),
        "{text}"
    );
    assert_eq!((fake.downloads.get(), fake.checkouts.get()), (0, 0));
    assert!(!work.exists(), "a dry run does not create the work folder");
    assert!(text.contains("WOULD FETCH"), "{text}");
    assert!(text.contains("Not fetched by this command"), "{text}");
    report.into_result().expect("a plan is not a failure");
}

#[test]
fn test_dry_run_verifies_a_present_archive_by_checksum() {
    let work = tempfile::tempdir().expect("tempdir");
    std::fs::write(work.path().join(FILE), BODY).expect("seed the archive");
    let inputs = inputs_with(
        vec![dist("http://127.0.0.1:9/never", BODY, &sha256_hex(BODY))],
        unused_afp(),
    );
    let fake = RecordingFetcher::default();
    let (report, text) = run(&inputs, &opts(&["fixture"], work.path(), Mode::Dry), &fake);
    assert!(matches!(sole_outcome(&report), Outcome::Verified), "{text}");
    assert_eq!(fake.downloads.get(), 0);
}

#[test]
fn test_dry_run_reports_a_foreign_afp_directory_as_refused() {
    let work = tempfile::tempdir().expect("tempdir");
    std::fs::create_dir_all(work.path().join("afp")).expect("afp dir");
    let inputs = inputs_with(Vec::new(), unused_afp());
    let fake = RecordingFetcher::default();
    let (report, text) = run(&inputs, &opts(&["afp"], work.path(), Mode::Dry), &fake);
    assert!(
        matches!(
            sole_outcome(&report),
            Outcome::Refused(FetchError::AfpNotACheckout { .. })
        ),
        "{text}"
    );
    assert_eq!((fake.inspects.get(), fake.checkouts.get()), (1, 0));
    assert!(
        report.into_result().is_err(),
        "a real run would refuse it too"
    );
}

#[test]
fn test_unknown_only_id_is_rejected_before_any_work() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let work = tmp.path().join("not-created");
    let inputs = inputs_with(Vec::new(), unused_afp());
    let fake = RecordingFetcher::default();
    let err = run_fetch(
        &inputs,
        &opts(&["Isabelle2099"], &work, Mode::Fetch),
        &fake,
        &mut Vec::<u8>::new(),
    )
    .expect_err("an unknown id is an error");
    assert!(matches!(err, FetchError::UnknownId { .. }), "{err}");
    assert!(!work.exists(), "nothing is created for a bad selection");
}
