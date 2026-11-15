// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.3 harness: the FIRST launch of a freshly linked lane driver, kept out
//! of the timed vector runs. A child of `emit_trust_ir::tests::ws6_3`, so the
//! `trust-ir-backend-lib` gate leg (`-- emit_trust_ir`) runs its tests.
//!
//! macOS assesses an executable FILE the first time it is exec'd, before
//! `main` (measured 2026-09-28 under the landing lane's load: 17 s to 1582 s,
//! every second exec 0.00 s — see [`WS6_3_FIRST_LAUNCH_WALL`]). The WS6.3
//! vector wall ([`super::WS6_3_WALL`], 30 s) is about the ROOT, so each lane
//! driver is launched once here, bounded separately and checked, and
//! [`super::ws6_3_run`] refuses a vector on any driver that was not.

use super::*;

/// The bound on a freshly linked driver's FIRST launch, which is not a run of
/// the root. macOS assesses an executable FILE the first time it is exec'd,
/// before `main`: measured 2026-09-28 under the landing lane's load, a fresh
/// hello-world took 17 s and 47 s, a byte-identical COPY of an
/// already-launched binary at a new path 160 s, and every second exec
/// 0.00 s. Every test run links its drivers into a new tempdir, so without
/// a separate first launch that assessment landed inside the 30 s
/// [`WS6_3_WALL`] of the first vector and failed it as `Timeout` (the lane's
/// `trust-ir: mask 12 10` / `natMask 2^8 0` reds of 2026-09-28).
///
/// The bound is not a measurement, only a hang catch for a binary that is
/// broken before its argument check, so it is set well above the worst
/// assessment seen: at 21:15 that evening (`syspolicyd` backlogged) a fresh
/// two-line `/bin/sh` script's first exec took 1582 s with its file identity
/// unchanged, and the first cut of this bound (600 s) failed every lane
/// driver's first launch as `Timeout`.
pub(super) const WS6_3_FIRST_LAUNCH_WALL: std::time::Duration =
    std::time::Duration::from_secs(3600);

/// Every driver [`ws6_3_first_launch`] has launched and accepted: its path,
/// and the identity of the FILE that launch executed. A vector may only run
/// on a path whose file is still that one ([`ws6_3_require_first_launched`],
/// called by [`super::ws6_3_run`], enforces it), so "the wall measures the
/// root, never the first launch" is checked on every vector rather than
/// trusted to each builder. Keyed by path ALONE it would not be: the
/// assessment is per file, so a driver re-linked (or otherwise replaced) at an
/// already-launched path would pay it again inside the wall.
static WS6_3_LAUNCHED: std::sync::Mutex<BTreeMap<std::path::PathBuf, Ws63FileId>> =
    std::sync::Mutex::new(BTreeMap::new());

/// The identity of one executable file: which inode on which device, and its
/// length and modification time, so a replacement at the same path (a new
/// inode) and an in-place rewrite (same inode, new length or mtime) both read
/// as a different file.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Ws63FileId {
    dev: u64,
    ino: u64,
    len: u64,
    mtime_ns: i128,
}

/// The [`Ws63FileId`] of the file now at `bin` (symlinks followed, as `exec`
/// follows them).
fn ws6_3_file_id(bin: &std::path::Path) -> Result<Ws63FileId, String> {
    use std::os::unix::fs::MetadataExt;
    let m = std::fs::metadata(bin).map_err(|e| format!("stat {}: {e}", bin.display()))?;
    Ok(Ws63FileId {
        dev: m.dev(),
        ino: m.ino(),
        len: m.len(),
        mtime_ns: i128::from(m.mtime()) * 1_000_000_000 + i128::from(m.mtime_nsec()),
    })
}

/// Launch a freshly linked driver ONCE, with no arguments, before any timed
/// vector, bounded by `bound`. It must end exactly as the driver refuses a
/// wrong argument count (`exit 2`, before any root runs); anything else —
/// a success, another exit code, a signal, or still running at `bound` — is
/// refused, so the first launch cannot hide a broken binary or stand in for
/// a vector. The file must also be the same file after the launch as before
/// it; what is recorded is that file, never just the path.
pub(super) fn ws6_3_first_launch(
    bin: &std::path::Path,
    bound: std::time::Duration,
) -> Result<(), String> {
    let before = ws6_3_file_id(bin)?;
    match ws6_3_exec(bin, &[], bound) {
        Ws63Outcome::Exit(2) => {
            let after = ws6_3_file_id(bin)?;
            if after != before {
                return Err(format!(
                    "{} changed during its first launch ({before:?} -> {after:?})",
                    bin.display()
                ));
            }
            WS6_3_LAUNCHED
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .insert(bin.to_path_buf(), before);
            Ok(())
        }
        other => Err(format!(
            "first launch of {} with no arguments must be the driver's argument-count \
             refusal (exit 2) within {bound:?}, got {other:?}",
            bin.display()
        )),
    }
}

/// Panic unless the file now at `bin` is the one that passed
/// [`ws6_3_first_launch`] — called by [`super::ws6_3_run`] before every timed
/// vector. A path never launched, a file replaced or rewritten at a launched
/// path, and a launched path whose file is gone are all refused.
pub(super) fn ws6_3_require_first_launched(bin: &std::path::Path) {
    let launched = WS6_3_LAUNCHED
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(bin)
        .cloned();
    let Some(launched) = launched else {
        panic!(
            "{}: a timed vector on a driver that was never first-launched \
             (ws6_3_first_launch) would time the OS's first-launch assessment, not the root",
            bin.display()
        )
    };
    match ws6_3_file_id(bin) {
        Ok(now) if now == launched => {}
        now => panic!(
            "{}: the file at this path is not the one first-launched ({launched:?}, now \
             {now:?}) -- it was replaced since its first launch, so a timed vector would \
             time the OS's first-launch assessment of the new file, not the root",
            bin.display()
        ),
    }
}

/// A freshly linked [`WS6_3_DRIVER_MAIN`] driver, after its accepted first
/// launch ([`ws6_3_first_launch`]) — what both lane builders return, so every
/// vector [`super::ws6_3_run`] times runs on an already-launched binary. (The
/// reducer-agreement driver is linked by [`super::ws6_3_link`] too, but it is not a
/// `WS6_3_DRIVER_MAIN` driver and its run is not wall-bounded.)
pub(super) fn ws6_3_launched_driver(bin: std::path::PathBuf, label: &str) -> std::path::PathBuf {
    ws6_3_first_launch(&bin, WS6_3_FIRST_LAUNCH_WALL).unwrap_or_else(|e| panic!("{label}: {e}"));
    bin
}

/// An executable `/bin/sh` script `name` running `body`, in `dir`.
fn ws6_3_script(dir: &std::path::Path, name: &str, body: &str) -> std::path::PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = dir.join(name);
    std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write the script");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
        .expect("make the script executable");
    path
}

/// A second NAME for the file at `file`: a hard link, so the same inode (one
/// OS first-launch assessment for every name, where a fresh file per case
/// would pay one each — 1582 s apiece when `syspolicyd` is backlogged).
fn ws6_3_alias(file: &std::path::Path, name: &str) -> std::path::PathBuf {
    let path = file.with_file_name(name);
    std::fs::hard_link(file, &path).expect("hard-link the script");
    path
}

/// ONE script whose behavior is selected by the name it is run as (`$0`), so
/// every first-launch case below is a hard link to a single file.
const WS6_3_BY_NAME: &str = r#"case "${0##*/}" in
  refuses) exit 2 ;;
  succeeds) echo 9; exit 0 ;;
  exit0_silent) exit 0 ;;
  exit1) exit 1 ;;
  exit3) exit 3 ;;
  signal) kill -KILL $$ ;;
  hangs) exec sleep 600 ;;
esac
exit 99"#;

/// The first launch every lane driver gets ([`ws6_3_launched_driver`]) is a
/// CHECK, not a free pass: it accepts only the driver's argument-count
/// refusal (`exit 2`).
/// Negative twins: a binary that SUCCEEDS with no arguments (and prints a
/// plausible value), other exit codes, a signal, and a hang — the hang
/// refused AT its bound (killed), never waited out, so the separate
/// first-launch bound cannot turn a hanging driver into a slow pass.
#[test]
fn test_ws6_3_first_launch_accepts_only_the_argument_count_refusal() {
    let dir = tempfile::tempdir().expect("tempdir");
    let by_name = ws6_3_script(dir.path(), "by_name", WS6_3_BY_NAME);
    let refuses = ws6_3_alias(&by_name, "refuses");
    assert_eq!(
        ws6_3_first_launch(&refuses, WS6_3_FIRST_LAUNCH_WALL),
        Ok(())
    );
    // The dispatcher's own fall-through is not the refusal either.
    let unnamed = ws6_3_first_launch(&by_name, WS6_3_FIRST_LAUNCH_WALL);
    assert!(
        matches!(&unnamed, Err(e) if e.contains("Exit(99)")),
        "by_name: {unnamed:?}"
    );
    for (name, shown) in [
        ("succeeds", "Value(\"9\")"),
        ("exit0_silent", "Value(\"\")"),
        ("exit1", "Exit(1)"),
        ("exit3", "Exit(3)"),
        ("signal", "Signal(9)"),
    ] {
        let got = ws6_3_first_launch(&ws6_3_alias(&by_name, name), WS6_3_FIRST_LAUNCH_WALL);
        let Err(err) = got else {
            panic!("{name}: the first launch must refuse")
        };
        assert!(
            err.contains(shown),
            "{name}: the refusal names {shown}: {err}"
        );
    }
    // Only an ACCEPTED first launch admits the path to timed vectors.
    for name in [
        "by_name",
        "succeeds",
        "exit0_silent",
        "exit1",
        "exit3",
        "signal",
    ] {
        assert!(
            !WS6_3_LAUNCHED
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .contains_key(&dir.path().join(name)),
            "{name}: a refused first launch must not admit the driver"
        );
    }
    let hangs = ws6_3_alias(&by_name, "hangs");
    let bound = std::time::Duration::from_secs(2);
    let start = std::time::Instant::now();
    let got = ws6_3_first_launch(&hangs, bound);
    let took = start.elapsed();
    let err = got.expect_err("a hang must be refused");
    assert!(
        err.contains("Timeout"),
        "the hang is refused as Timeout: {err}"
    );
    assert!(
        took >= bound && took < std::time::Duration::from_secs(60),
        "the hang must be killed at its {bound:?} bound, took {took:?}"
    );
}

/// The vector runner REFUSES a driver that never passed its first launch
/// (so no builder can skip [`ws6_3_first_launch`] and silently put the OS's
/// first-launch assessment back inside [`WS6_3_WALL`]), and admits the same
/// path once its first launch is accepted.
#[test]
fn test_ws6_3_vector_run_requires_an_accepted_first_launch() {
    let dir = tempfile::tempdir().expect("tempdir");
    let driver = ws6_3_script(dir.path(), "driver", "exit 2");
    let unlaunched = std::panic::catch_unwind(|| {
        ws6_3_run(&driver, "mask", (12, 10), WS6_3_STACK_KIB, WS6_3_WALL)
    });
    let Err(payload) = unlaunched else {
        panic!("a vector on a never-launched driver must panic")
    };
    let msg = payload
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_default();
    assert!(
        msg.contains("never first-launched"),
        "the refusal names the missing first launch: {msg:?}"
    );
    assert_eq!(ws6_3_first_launch(&driver, WS6_3_FIRST_LAUNCH_WALL), Ok(()));
    assert_eq!(
        ws6_3_run(&driver, "mask", (12, 10), WS6_3_STACK_KIB, WS6_3_WALL),
        Ws63Outcome::Exit(2),
        "once launched, the same path runs its vectors"
    );
}

/// The first-launch record is about the FILE, not the path (negative twins of
/// [`test_ws6_3_vector_run_requires_an_accepted_first_launch`]): after an
/// accepted first launch, each way of putting a different file at the same
/// path makes the next timed vector panic instead of running — a replacement
/// (a new inode), an in-place rewrite (same inode, new length), a symlink
/// retargeted to another file, and the file removed. Positive twins: an
/// untouched launched path keeps running, and a fresh accepted first launch
/// of the replacement admits the path again. Two script files in all; every
/// other name is a link to one of them.
#[test]
fn test_ws6_3_vector_run_refuses_a_driver_changed_since_its_first_launch() {
    fn run_panics(bin: &std::path::Path) -> String {
        let got = std::panic::catch_unwind(|| {
            ws6_3_run(bin, "mask", (12, 10), WS6_3_STACK_KIB, WS6_3_WALL)
        });
        let Err(payload) = got else {
            panic!("{}: a vector on a changed driver must panic", bin.display())
        };
        payload
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_default()
    }
    let runs =
        |bin: &std::path::Path| ws6_3_run(bin, "mask", (12, 10), WS6_3_STACK_KIB, WS6_3_WALL);
    let launch = |bin: &std::path::Path| ws6_3_first_launch(bin, WS6_3_FIRST_LAUNCH_WALL);
    let dir = tempfile::tempdir().expect("tempdir");
    let d = dir.path();
    let file_a = ws6_3_script(d, "file_a", "exit 2");
    let file_b = ws6_3_script(d, "file_b", "exit 2");

    // Replaced: a different inode at the same path (what a re-link does).
    let replaced = ws6_3_alias(&file_a, "replaced");
    assert_eq!(launch(&replaced), Ok(()));
    assert_eq!(runs(&replaced), Ws63Outcome::Exit(2));
    std::fs::remove_file(&replaced).expect("remove the launched driver");
    std::fs::hard_link(&file_b, &replaced).expect("put another file at the path");
    let msg = run_panics(&replaced);
    assert!(
        msg.contains("replaced since its first launch"),
        "replaced: {msg:?}"
    );
    assert_eq!(
        launch(&replaced),
        Ok(()),
        "the replacement's own first launch"
    );
    assert_eq!(runs(&replaced), Ws63Outcome::Exit(2));

    // A symlink retargeted from the launched file to another one.
    let link = d.join("link");
    std::os::unix::fs::symlink(&file_a, &link).expect("symlink the driver");
    assert_eq!(launch(&link), Ok(()));
    std::fs::remove_file(&link).expect("unlink the symlink");
    std::os::unix::fs::symlink(&file_b, &link).expect("retarget the symlink");
    let msg = run_panics(&link);
    assert!(
        msg.contains("replaced since its first launch"),
        "retargeted: {msg:?}"
    );

    // Removed: the launched path has no file at all.
    let removed = ws6_3_alias(&file_a, "removed");
    assert_eq!(launch(&removed), Ok(()));
    std::fs::remove_file(&removed).expect("remove the launched driver");
    let msg = run_panics(&removed);
    assert!(
        msg.contains("replaced since its first launch"),
        "removed: {msg:?}"
    );

    // Rewritten in place: same inode, different length. Last, because it
    // rewrites file_a itself (and so every name linked to it).
    let untouched = ws6_3_alias(&file_b, "untouched");
    assert_eq!(launch(&untouched), Ok(()));
    let rewritten = ws6_3_alias(&file_a, "rewritten");
    assert_eq!(launch(&rewritten), Ok(()));
    std::fs::write(
        &rewritten,
        "#!/bin/sh\n# rewritten after its first launch\nexit 2\n",
    )
    .expect("rewrite the launched driver in place");
    let msg = run_panics(&rewritten);
    assert!(
        msg.contains("replaced since its first launch"),
        "rewritten: {msg:?}"
    );
    assert_eq!(
        runs(&untouched),
        Ws63Outcome::Exit(2),
        "a launched file nobody touched still runs"
    );
}
