// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `saveEnvironment` writes its file whole or not at all (`handlers/save_file.rs`;
//! R36's open items, closed by R87). It wrote with
//! `fs::write`, which truncates the file and then writes it, so a write cut
//! short left the file torn, and a save whose request had answered the
//! timeout error still replaced the file. Its answer and its file agree: the
//! timeout error means the file is as it was, success that it was replaced
//! (review of 2026-10-18). The tests that order a save against its request's
//! timer pause the save at one of its steps (`save_file::seam`) and fire a
//! timer of their own ([`save_until`]).
//!
//! Every wait for something that must happen is a one-minute hang detector,
//! never a latency budget.

use super::temp_rooted_state;
use crate::dispatch::dispatch_request;
use crate::handlers::admin::save_until;
use crate::handlers::save_file::seam::{self, Step};
use crate::handlers::save_file::{save_file, Commit, SaveError, NAME_PREFIX_BYTES};
use crate::handlers::types::SaveEnvironmentParams;
use crate::handlers::*;
use crate::rpc::Response;
use clean_kernel::Environment;
use serde_json::{json, Value};
use std::path::Path;
use std::time::{Duration, Instant};
use tokio::sync::oneshot;

/// A wait for something that must happen.
const HANG: Duration = Duration::from_secs(60);

/// What the file holds before a save.
const OLD: &[u8] = b"the environment saved before\n";

/// Set (to anything) by the test that runs
/// [`a_save_cut_short_leaves_the_old_file_whole`] under a file-size limit.
const LIMITED: &str = "CLEAN_SERVER_SAVE_UNDER_A_FILE_SIZE_LIMIT";

/// Send `method` through the dispatcher; it must answer within the hang
/// detector.
async fn sent(state: &ServerState, method: &str, params: Value) -> Response {
    tokio::time::timeout(
        HANG,
        dispatch_request(method, Some(params), RequestId::Number(1), state, None),
    )
    .await
    .unwrap_or_else(|_| panic!("{method} was not answered within the hang detector"))
}

/// Wait until no work holds a slot: the abandoned work has ended.
async fn wait_until_idle(state: &ServerState) {
    let give_up = Instant::now() + HANG;
    while state.work.in_use() != 0 {
        assert!(Instant::now() < give_up, "the abandoned work never ended");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

fn save_params(path: &Path, timeout_ms: u64) -> Value {
    json!({ "path": path.to_string_lossy(), "timeout_ms": timeout_ms })
}

/// What saving `state`'s environment writes: the bytes a whole save leaves.
async fn whole(state: &ServerState) -> Vec<u8> {
    state
        .env
        .read()
        .await
        .to_bincode()
        .expect("encode the environment")
}

/// A save whose write is cut short leaves the old file whole: a reader sees
/// the old file or the whole new one, never a part. Run alone, nothing cuts
/// the save, and it replaces the file whole. Run by
/// `a_save_the_file_size_limit_cuts_short_leaves_the_old_file_whole`, under a
/// file-size limit far below the encoding, the write fails partway: the save
/// answers an error, and the file must be the old one. Before, `fs::write`
/// had truncated it and written up to the limit: a torn file.
///
/// The same for a save through a symbolic link that names nothing: cut short,
/// nothing is there afterwards, and the link still names nothing. Until
/// 2026-10-19 such a save went to `fs::write`, which created the file and left
/// it torn (review of 2026-10-19: 8 of 30 saves killed while they wrote).
#[tokio::test]
async fn a_save_cut_short_leaves_the_old_file_whole() {
    let limited = std::env::var_os(LIMITED).is_some();
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    let fresh = dir.path().join("fresh.bincode");
    let link = dir.path().join("link.bincode");
    link_to(&fresh, &link);

    let saved = sent(
        &state,
        "saveEnvironment",
        save_params(&path, HANG.as_millis() as u64),
    )
    .await;
    let through_link = sent(
        &state,
        "saveEnvironment",
        save_params(&link, HANG.as_millis() as u64),
    )
    .await;
    let after = std::fs::read(&path).expect("read the file back");
    let created = std::fs::read(&fresh).ok();
    let whole = whole(&state).await;
    let held = if after == OLD {
        "the old file"
    } else if after == whole {
        "the whole new file"
    } else {
        "neither: a torn file"
    };
    let held_through_link = match &created {
        None => "nothing",
        Some(bytes) if *bytes == whole => "the whole new file",
        Some(_) => "a torn file",
    };
    assert_eq!(
        (
            saved.error.is_some(),
            held,
            through_link.error.is_some(),
            held_through_link
        ),
        (
            limited,
            if limited {
                "the old file"
            } else {
                "the whole new file"
            },
            limited,
            if limited {
                "nothing"
            } else {
                "the whole new file"
            }
        ),
        "(the save failed, the path holds, the save through a link to nothing failed, the \
         linked path holds) with{} a file-size limit; the saves answered {:?} and {:?}; the \
         file has {} bytes, the linked one {:?}, the encoding {}",
        if limited { "" } else { "out" },
        saved.error,
        through_link.error,
        after.len(),
        created.as_ref().map(Vec::len),
        whole.len()
    );
    assert!(
        std::fs::symlink_metadata(&link)
            .expect("the link")
            .file_type()
            .is_symlink(),
        "the link was replaced by a file"
    );
    let mut left = left_beside(dir.path(), "saved.bincode");
    left.retain(|name| name != "link.bincode" && name != "fresh.bincode");
    assert!(left.is_empty(), "the saves left files behind: {left:?}");
}

/// A symbolic link at `link` to `target`.
fn link_to(target: &Path, link: &Path) {
    #[cfg(unix)]
    std::os::unix::fs::symlink(target, link).expect("make the link");
    #[cfg(windows)]
    std::os::windows::fs::symlink_file(target, link).expect("make the link");
}

/// Runs the test above in a process of its own under a file-size limit of
/// 64 blocks (32 or 64 KiB, the shell's unit), far below the prelude's
/// encoding, with `SIGXFSZ` ignored so a write past the limit fails with
/// `EFBIG` instead of killing the process. Its output goes to pipes, which no
/// file-size limit applies to.
#[cfg(unix)]
#[test]
fn a_save_the_file_size_limit_cuts_short_leaves_the_old_file_whole() {
    let this = std::env::current_exe().expect("this test binary");
    let test = "handlers::tests::save_file::a_save_cut_short_leaves_the_old_file_whole";
    let ran = std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg("trap '' XFSZ; ulimit -f 64 && exec \"$0\" --exact \"$1\" --test-threads=1")
        .arg(&this)
        .arg(test)
        .env(LIMITED, "1")
        .output()
        .expect("run the test under a file-size limit");
    let output = format!(
        "{}{}",
        String::from_utf8_lossy(&ran.stdout),
        String::from_utf8_lossy(&ran.stderr)
    );
    assert!(
        ran.status.success() && output.contains("1 passed"),
        "the save under a file-size limit ({}):\n{output}",
        ran.status
    );
}

/// A save whose request answered its timeout error went on to replace the
/// file (it read no deadline). It reads the deadline before it writes and
/// before it commits now, so the file stays as it was. A `timeout_ms` of 0
/// sends the save to the pool (a free slot and a free environment are taken
/// in the request's first poll) with its deadline already passed.
#[tokio::test]
async fn a_save_whose_request_timed_out_leaves_the_file_as_it_was() {
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");

    let saved = sent(&state, "saveEnvironment", save_params(&path, 0)).await;
    assert_eq!(saved.error.map(|e| e.code), Some(-32004));
    wait_until_idle(&state).await;
    assert_eq!(
        std::fs::read(&path).expect("read the file back"),
        OLD,
        "a save whose request timed out replaced the file"
    );
}

/// A save through a symbolic link that names nothing went to `fs::write`
/// before it read its deadline, and took no commit, so it answered the timeout
/// error and then created the file (review of 2026-10-19: 6 of 6 such saves).
/// It is a save of a new file at the path the link names now, and past its
/// deadline it creates nothing.
#[tokio::test]
async fn a_save_through_a_link_to_nothing_whose_request_timed_out_creates_nothing() {
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let fresh = dir.path().join("fresh.bincode");
    let link = dir.path().join("link.bincode");
    link_to(&fresh, &link);

    let saved = sent(&state, "saveEnvironment", save_params(&link, 0)).await;
    assert_eq!(saved.error.map(|e| e.code), Some(-32004));
    wait_until_idle(&state).await;
    assert!(
        !fresh.exists(),
        "a save whose request answered the timeout error created the file its link names"
    );
    assert_eq!(
        left_beside(dir.path(), "link.bincode"),
        Vec::<std::ffi::OsString>::new()
    );
}

/// A link to nothing, through a chain of links whose contents are relative
/// (each to its own link's directory, as the system reads them): the save
/// creates the file the last one names, whole, and every link stays a link.
#[cfg(unix)]
#[tokio::test]
async fn a_save_through_links_to_nothing_creates_the_file_they_name() {
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let sub = dir.path().join("sub");
    std::fs::create_dir(&sub).expect("make a directory");
    let first = dir.path().join("first.bincode");
    let second = sub.join("second.bincode");
    std::os::unix::fs::symlink("sub/second.bincode", &first).expect("link to the second link");
    std::os::unix::fs::symlink("fresh.bincode", &second).expect("link to nothing");

    let saved = sent(
        &state,
        "saveEnvironment",
        save_params(&first, HANG.as_millis() as u64),
    )
    .await;
    assert!(saved.error.is_none(), "{:?}", saved.error);
    let whole = whole(&state).await;
    assert_eq!(
        std::fs::read(sub.join("fresh.bincode")).expect("the file the links name"),
        whole
    );
    assert_eq!(
        saved.result.expect("a result")["file_size"],
        json!(whole.len())
    );
    for link in [&first, &second] {
        assert!(
            std::fs::symlink_metadata(link)
                .expect("the link")
                .file_type()
                .is_symlink(),
            "{} was replaced by a file",
            link.display()
        );
    }
    assert_eq!(
        left_beside(&sub, "second.bincode"),
        vec![std::ffi::OsString::from("fresh.bincode")]
    );
}

/// A long chain of relative links, each in a directory of its own with a long
/// name, that the system follows: the save replaces the file at its end, and
/// every link stays a link. Each link's contents are read from its directory's
/// real path; joined to the directory as written, every link lengthened the
/// path until the save was refused as `File name too long`, where the system,
/// which follows one link at a time, opens the chain (review of 2026-10-19).
/// Twenty-four links of 200-byte directories pass macOS's 1,024-byte and
/// Linux's 4,096-byte path limits that way, within both systems' link limits.
#[cfg(unix)]
#[tokio::test]
async fn a_save_through_a_long_chain_of_relative_links_replaces_the_file_at_its_end() {
    const LINKS: usize = 24;
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let names: Vec<String> = (0..=LINKS)
        .map(|i| format!("d{i:02}_{}", "x".repeat(196)))
        .collect();
    for name in &names {
        std::fs::create_dir(dir.path().join(name)).expect("make a directory");
    }
    let links: Vec<_> = (0..LINKS)
        .map(|i| dir.path().join(&names[i]).join("l"))
        .collect();
    for (i, link) in links.iter().enumerate() {
        let next = if i + 1 < LINKS { "l" } else { "file.bincode" };
        std::os::unix::fs::symlink(format!("../{}/{next}", names[i + 1]), link)
            .expect("make a link");
    }
    let file = dir.path().join(&names[LINKS]).join("file.bincode");
    std::fs::write(&file, OLD).expect("write the old file");
    // The premise: the system follows the chain.
    assert_eq!(
        std::fs::read(&links[0]).expect("the system opens the chain"),
        OLD
    );

    let saved = sent(
        &state,
        "saveEnvironment",
        save_params(&links[0], HANG.as_millis() as u64),
    )
    .await;
    assert!(saved.error.is_none(), "{:?}", saved.error);
    assert_eq!(
        std::fs::read(&file).expect("the file the chain names"),
        whole(&state).await
    );
    for link in &links {
        assert!(
            std::fs::symlink_metadata(link)
                .expect("the link")
                .file_type()
                .is_symlink(),
            "{} was replaced by a file",
            link.display()
        );
    }
    assert_eq!(
        left_beside(&dir.path().join(&names[LINKS]), "file.bincode"),
        Vec::<std::ffi::OsString>::new()
    );
}

/// Links that name each other name no file: the save is refused, as opening
/// the path is, and creates nothing.
#[cfg(unix)]
#[tokio::test]
async fn a_save_through_a_loop_of_links_is_refused() {
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let one = dir.path().join("one.bincode");
    let other = dir.path().join("other.bincode");
    std::os::unix::fs::symlink(&other, &one).expect("link one way");
    std::os::unix::fs::symlink(&one, &other).expect("link the other way");

    let saved = sent(
        &state,
        "saveEnvironment",
        save_params(&one, HANG.as_millis() as u64),
    )
    .await;
    let message = saved.error.map(|e| e.message).unwrap_or_default();
    assert!(message.contains("symbolic links"), "{message:?}");
    let mut left = left_beside(dir.path(), "one.bincode");
    left.retain(|name| name != "other.bincode");
    assert!(left.is_empty(), "the save left files behind: {left:?}");
}

/// A path that can name no new file (one that ends in a separator, `.` or
/// `..`, the empty path) is refused as `fs::write` refused it, and nothing is
/// written: a path ending in a separator wrote a whole temporary file before
/// its rename failed (review of 2026-10-19). The pause asks whether a save of
/// the file the slashed path spells got as far as its temporary file.
#[cfg(unix)]
#[tokio::test]
async fn a_save_of_a_path_that_names_no_new_file_writes_nothing() {
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    // Never kept waiting: only whether a save got there is asked.
    let (_reached, go) = seam::pause(&path, Step::Created);
    drop(go);

    let mut refusals = Vec::new();
    for spelled in [
        format!("{}/", path.display()),
        format!("{}/.", dir.path().display()),
        format!("{}/nowhere/..", dir.path().display()),
        String::new(),
    ] {
        let saved = sent(
            &state,
            "saveEnvironment",
            json!({ "path": spelled, "timeout_ms": HANG.as_millis() as u64 }),
        )
        .await;
        refusals.push((spelled, saved.error.map(|e| e.message)));
    }
    assert!(
        refusals.iter().all(|(_, refused)| refused.is_some()),
        "{refusals:?}"
    );
    assert!(
        seam::withdraw(&path, Step::Created),
        "a save of {:?} wrote a temporary file",
        refusals[0].0
    );
    assert_eq!(std::fs::read(&path).expect("read the file back"), OLD);
    assert_eq!(
        left_beside(dir.path(), "saved.bincode"),
        Vec::<std::ffi::OsString>::new()
    );
}

/// A save reads its deadline before it creates its new file: past it, it
/// creates and writes nothing, and its work's answer is dropped. The read
/// before the commit (below) would only remove the whole file written. Here
/// the deadline has passed when the save starts.
#[test]
fn a_save_past_its_deadline_creates_no_file() {
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    // Never kept waiting: only whether the save got there is asked.
    let (_reached, go) = seam::pause(&path, Step::Created);
    drop(go);
    let commit = Commit::default();

    let mut saved = None;
    let finished = clean_kernel::tc::run_until(Some(Instant::now()), || {
        saved = Some(save_file(&path, &[0u8; 1 << 16], &commit));
    });
    let created = !seam::withdraw(&path, Step::Created);
    assert_eq!(
        (
            finished.is_none(),
            matches!(saved, Some(Err(SaveError::Interrupted))),
            created
        ),
        (true, true, false),
        "(the deadline latched, the save answered that it passed, it created its new file); \
         it answered {saved:?}"
    );
    assert_eq!(std::fs::read(&path).expect("read the file back"), OLD);
    assert_eq!(
        left_beside(dir.path(), "saved.bincode"),
        Vec::<std::ffi::OsString>::new()
    );
    assert!(commit.abandon(), "a save past its deadline took its commit");
}

/// A save reads its deadline again once its new file is whole, before it
/// decides to commit: one whose deadline passed while it wrote never renames,
/// and answers the timeout error. Here the deadline passes as the save starts
/// writing (`seam::expire`) and nobody abandons the save, so the commit alone
/// would let it replace the file.
#[test]
fn a_save_whose_deadline_passed_while_it_wrote_never_commits() {
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    let _reached = seam::expire(&path, Step::Created);
    let commit = Commit::default();

    let saved = save_file(&path, b"the environment saved now\n", &commit);
    assert!(
        !seam::withdraw(&path, Step::Created),
        "the save never got to its new file: this test's premise"
    );
    assert!(matches!(saved, Err(SaveError::Interrupted)), "{saved:?}");
    assert_eq!(std::fs::read(&path).expect("read the file back"), OLD);
    assert_eq!(
        left_beside(dir.path(), "saved.bincode"),
        Vec::<std::ffi::OsString>::new()
    );
    assert!(commit.abandon(), "a save past its deadline took its commit");
}

/// The save replaces the file a symbolic link names and keeps the link, and
/// keeps the old file's permissions, as `fs::write` did.
#[cfg(unix)]
#[tokio::test]
async fn a_save_keeps_links_and_permissions() {
    use std::os::unix::fs::PermissionsExt;
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let target = dir.path().join("target.bincode");
    std::fs::write(&target, OLD).expect("write the old file");
    std::fs::set_permissions(&target, std::fs::Permissions::from_mode(0o640))
        .expect("set the old file's permissions");
    let link = dir.path().join("link.bincode");
    std::os::unix::fs::symlink(&target, &link).expect("link to the old file");

    let saved = sent(
        &state,
        "saveEnvironment",
        save_params(&link, HANG.as_millis() as u64),
    )
    .await;
    assert!(saved.error.is_none(), "{:?}", saved.error);
    assert!(
        std::fs::symlink_metadata(&link)
            .expect("the link")
            .file_type()
            .is_symlink(),
        "the link was replaced by a file"
    );
    assert_eq!(
        std::fs::read(&target).expect("read the target"),
        whole(&state).await
    );
    assert_eq!(
        std::fs::metadata(&target)
            .expect("the target")
            .permissions()
            .mode()
            & 0o777,
        0o640
    );
}

/// Wait for `what` to happen: one-minute hang detector.
async fn happened(what: &str, signal: oneshot::Receiver<()>) {
    tokio::time::timeout(HANG, signal)
        .await
        .unwrap_or_else(|_| panic!("{what} never happened"))
        .unwrap_or_else(|_| panic!("{what}: its sender went away"));
}

/// The files beside `kept` in `dir`: a save's leftovers.
fn left_beside(dir: &Path, kept: &str) -> Vec<std::ffi::OsString> {
    std::fs::read_dir(dir)
        .expect("list the directory")
        .map(|entry| entry.expect("an entry").file_name())
        .filter(|name| name != kept)
        .collect()
}

fn params_for(path: &Path) -> SaveEnvironmentParams {
    serde_json::from_value(save_params(path, HANG.as_millis() as u64)).expect("save params")
}

/// The save read the deadline before it renamed, but the request's timer was
/// its own: a save that read it just before it passed renamed after its
/// request had answered the timeout error (review of 2026-10-18: 12 of 186
/// saves near their deadline did). Here the save is paused after it has read
/// the deadline (an hour away) and before it decides to commit, and the
/// request's timer fires meanwhile: the request answers the timeout error, and
/// the save, let go, must never rename. Before, it renamed.
#[tokio::test]
async fn a_save_whose_request_stopped_waiting_before_it_committed_never_renames() {
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    let (reached, release) = seam::pause(&path, Step::BeforeCommit);
    let (fire, fired) = oneshot::channel::<()>();

    let (saved, ()) = tokio::join!(
        save_until(
            &state,
            RequestId::Number(1),
            params_for(&path),
            HANG,
            async move {
                let _ = fired.await;
            }
        ),
        async move {
            happened("the save reaching its commit", reached).await;
            let _ = fire.send(());
        }
    );
    assert_eq!(saved.error.map(|e| e.code), Some(-32004));
    let _ = release.send(());
    wait_until_idle(&state).await;
    assert_eq!(
        std::fs::read(&path).expect("read the file back"),
        OLD,
        "a save whose request answered the timeout error replaced the file"
    );
    assert_eq!(
        left_beside(dir.path(), "saved.bincode"),
        Vec::<std::ffi::OsString>::new()
    );
}

/// The other order: the save has begun replacing its file when its request's
/// timer fires. The request waits for it and answers what became of the file,
/// here success. Before, the request answered the timeout error, the file
/// replaced. The timer tells the test when the request has seen it fire, and
/// only then does the paused save go on.
#[tokio::test]
async fn a_save_that_began_replacing_its_file_is_answered_by_its_outcome() {
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    let (reached, release) = seam::pause(&path, Step::Committing);
    let (fire, fired) = oneshot::channel::<()>();
    let (seen, observed) = oneshot::channel::<()>();

    let (saved, ()) = tokio::join!(
        save_until(
            &state,
            RequestId::Number(1),
            params_for(&path),
            HANG,
            async move {
                let _ = fired.await;
                let _ = seen.send(());
            }
        ),
        async move {
            happened("the save taking its commit", reached).await;
            let _ = fire.send(());
            happened("the request seeing its timer fire", observed).await;
            let _ = release.send(());
        }
    );
    assert!(
        saved.error.is_none(),
        "a save that replaced its file answered {:?}",
        saved.error
    );
    assert_eq!(
        std::fs::read(&path).expect("read the file back"),
        whole(&state).await
    );
}

/// A file the server may not write: `fs::write` refused it at its open, and
/// the rename (which needs only the directory) replaced it (review of
/// 2026-10-18). The save asks the file first now: it does what opening the
/// file for writing says (refused, unless the tests run with a user that
/// writes any file), and a refused save leaves the file and its mode.
#[cfg(unix)]
#[tokio::test]
async fn a_save_refuses_a_file_the_server_may_not_write_as_fs_write_did() {
    use std::os::unix::fs::PermissionsExt;
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o444))
        .expect("make the old file read-only");
    let writable = std::fs::OpenOptions::new().write(true).open(&path).is_ok();

    let saved = sent(
        &state,
        "saveEnvironment",
        save_params(&path, HANG.as_millis() as u64),
    )
    .await;
    let whole = whole(&state).await;
    let after = std::fs::read(&path).expect("read the file back");
    let mode = std::fs::metadata(&path)
        .expect("the file")
        .permissions()
        .mode()
        & 0o777;
    assert_eq!(
        (saved.error.is_none(), after == whole, after == OLD, mode),
        (writable, writable, !writable, 0o444),
        "(saved, replaced, kept, mode) of a read-only file; opening it for writing {}; \
         the save answered {:?}",
        if writable { "succeeds" } else { "is refused" },
        saved.error
    );
}

/// A save writes a new file beside its target, so it needs the directory: a
/// writable file in a directory the server may not write is refused with the
/// reason (`fs::write` wrote such a file in place, torn when cut short), and
/// the file is as it was. Whether the directory refuses is asked of the file
/// system, as for the read-only file above.
#[cfg(unix)]
#[tokio::test]
async fn a_save_in_a_directory_it_may_not_write_is_refused_with_the_reason() {
    use std::os::unix::fs::PermissionsExt;
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let outer = tempfile::tempdir().expect("a scratch directory");
    let dir = outer.path().join("closed");
    std::fs::create_dir(&dir).expect("make the directory");
    let path = dir.join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o555))
        .expect("close the directory");
    let probe = dir.join("probe");
    let creatable = std::fs::File::create(&probe).is_ok();
    let _ = std::fs::remove_file(&probe);

    let saved = sent(
        &state,
        "saveEnvironment",
        save_params(&path, HANG.as_millis() as u64),
    )
    .await;
    let after = std::fs::read(&path).expect("read the file back");
    std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o755))
        .expect("open the directory again, for the clean-up");
    let message = saved.error.map(|e| e.message).unwrap_or_default();
    assert_eq!(
        (
            message.contains("the directory must be writable"),
            after == OLD,
            after == whole(&state).await
        ),
        (!creatable, !creatable, creatable),
        "(refused with the reason, kept, replaced); the directory {} a new file; the save \
         answered {message:?}",
        if creatable { "takes" } else { "refuses" },
    );
}

/// The temporary file's name repeated the target's whole name, so a target
/// whose name was near the file system's limit could not get one (review of
/// 2026-10-18: a 250-byte name answered "File name too long"). The name is cut
/// to [`NAME_PREFIX_BYTES`] now, on a character boundary. The limit is 255
/// bytes on most file systems and 255 characters on APFS, so the name here is
/// near both (252 bytes, 250 characters), and its cut falls inside a
/// three-byte character. A temporary name that repeated it whole is too long
/// here: checked first, so the test cannot pass on a file system that takes
/// it (review of 2026-10-19: one of 83 three-byte characters, 249 bytes, did).
#[tokio::test]
async fn a_save_of_a_name_at_the_limit_gets_a_temporary_file() {
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let name = format!("{}\u{20ac}{}", "a".repeat(31), "a".repeat(218));
    assert_eq!(
        (
            name.len(),
            name.chars().count(),
            name.is_char_boundary(NAME_PREFIX_BYTES)
        ),
        (252, 250, false),
        "this test's premise: a name near the limit, cut inside a character"
    );
    let whole_name = dir
        .path()
        .join(format!(".{name}.{}.0.saving", std::process::id()));
    let too_long = std::fs::File::create(&whole_name);
    assert!(
        too_long.is_err(),
        "this test's premise: a temporary name repeating the whole name is too long here"
    );
    let path = dir.path().join(&name);
    std::fs::write(&path, OLD).expect("write the old file");

    let saved = sent(
        &state,
        "saveEnvironment",
        save_params(&path, HANG.as_millis() as u64),
    )
    .await;
    assert!(saved.error.is_none(), "{:?}", saved.error);
    assert_eq!(
        std::fs::read(&path).expect("read the file back"),
        whole(&state).await
    );
    assert_eq!(
        left_beside(dir.path(), &name),
        Vec::<std::ffi::OsString>::new()
    );
}

/// The temporary file was created with the default mode and given the old
/// file's only once it was written, so while a save of an owner-only file
/// wrote, the new contents could be read by others (review of 2026-10-18).
/// Here the save is paused as soon as its temporary file exists, before
/// anything is written to it: it already has the old file's mode.
#[cfg(unix)]
#[tokio::test]
async fn a_save_creates_its_new_file_no_more_readable_than_the_old() {
    use std::os::unix::fs::PermissionsExt;
    let state = temp_rooted_state().with_env(Environment::with_prelude());
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("saved.bincode");
    std::fs::write(&path, OLD).expect("write the old file");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))
        .expect("make the old file owner-only");
    let (reached, release) = seam::pause(&path, Step::Created);
    let listing = dir.path().to_path_buf();

    let (saved, modes) = tokio::join!(
        sent(
            &state,
            "saveEnvironment",
            save_params(&path, HANG.as_millis() as u64),
        ),
        async move {
            happened("the save creating its temporary file", reached).await;
            let modes: Vec<u32> = left_beside(&listing, "saved.bincode")
                .into_iter()
                .map(|name| {
                    std::fs::metadata(listing.join(name))
                        .expect("the temporary file")
                        .permissions()
                        .mode()
                        & 0o777
                })
                .collect();
            let _ = release.send(());
            modes
        }
    );
    assert!(saved.error.is_none(), "{:?}", saved.error);
    assert_eq!(modes, vec![0o600], "the temporary file's mode, as created");
    assert_eq!(
        std::fs::metadata(&path)
            .expect("the saved file")
            .permissions()
            .mode()
            & 0o777,
        0o600
    );
}
