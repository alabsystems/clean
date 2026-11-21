// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Default-feature CLI regression for dispatch_sync's run/compile stack.
//! `just ci` -> test-fast runs this without a backend feature or consumer.
//!
//! Lowering the process stack below 1.5 MiB overflows CLI startup before
//! dispatch, so a shell ulimit is not a control for the route. Instead a
//! test-only pthread interposer observes the explicitly sized worker while
//! the real CLI executes. No production switch or mock handler is involved.
#![cfg(any(target_os = "macos", target_os = "linux"))]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const INTERPOSER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#ifndef __APPLE__
#include <dlfcn.h>
#endif
static void observe(const char *name) {
    const char *path = getenv("X1_STACK_LOG");
    if (!path || (strcmp(name, "clean-run") && strcmp(name, "clean-compile"))) return;
    size_t bytes = 0;
#ifdef __APPLE__
    bytes = pthread_get_stacksize_np(pthread_self());
#else
    pthread_attr_t attr;
    if (pthread_getattr_np(pthread_self(), &attr)) _exit(95);
    if (pthread_attr_getstacksize(&attr, &bytes)) _exit(94);
    if (pthread_attr_destroy(&attr)) _exit(93);
#endif
    char msg[128];
    int len = snprintf(msg, sizeof(msg), "%s %zu\n", name, bytes);
    if (len < 0 || (size_t)len >= sizeof(msg)) _exit(92);
    int fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0600);
    if (fd < 0) _exit(97);
    if (write(fd, msg, (size_t)len) != len) _exit(98);
    if (close(fd)) _exit(99);
}
#ifdef __APPLE__
static int traced_setname(const char *name) {
    observe(name);
    return pthread_setname_np(name);
}
__attribute__((used)) static struct {
    const void *replacement;
    const void *original;
} interpose __attribute__((section("__DATA,__interpose"))) = {
    (const void *)traced_setname, (const void *)pthread_setname_np
};
#else
int pthread_setname_np(pthread_t thread, const char *name) {
    typedef int (*setname_fn)(pthread_t, const char *);
    setname_fn original = (setname_fn)dlsym(RTLD_NEXT, "pthread_setname_np");
    if (!original) _exit(96);
    if (pthread_equal(thread, pthread_self())) observe(name);
    return original(thread, name);
}
#endif
"#;

struct ObservedCli {
    _dir: tempfile::TempDir,
    library: PathBuf,
    log: PathBuf,
}

impl ObservedCli {
    fn new() -> Self {
        let dir = tempfile::tempdir().expect("interposer build dir");
        let source = dir.path().join("observe.c");
        let library = dir.path().join("observe.so");
        std::fs::write(&source, INTERPOSER).expect("interposer source");
        let mut cc = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
        #[cfg(target_os = "macos")]
        cc.arg("-dynamiclib");
        #[cfg(target_os = "linux")]
        cc.args(["-shared", "-fPIC"]);
        cc.arg("-pthread").arg(&source).arg("-o").arg(&library);
        #[cfg(target_os = "linux")]
        cc.arg("-ldl");
        let built = cc.output().expect("build pthread observer");
        assert!(
            built.status.success(),
            "{}",
            String::from_utf8_lossy(&built.stderr)
        );
        let log = dir.path().join("workers");
        Self {
            _dir: dir,
            library,
            log,
        }
    }

    fn run(&self, args: &[&str], expects_worker: bool) -> Output {
        std::fs::write(&self.log, "").expect("reset worker log");
        let mut command = Command::new(env!("CARGO_BIN_EXE_clean"));
        command
            .args(args)
            .env("X1_STACK_LOG", &self.log)
            // Other std/tokio threads must not mimic the explicit 1 GiB worker.
            .env("RUST_MIN_STACK", "2097152");
        #[cfg(target_os = "macos")]
        command.env("DYLD_INSERT_LIBRARIES", &self.library);
        #[cfg(target_os = "linux")]
        command.env("LD_PRELOAD", &self.library);
        let output = command.output().expect("run observed CLI");
        assert!(
            output.status.success(),
            "{args:?}: {:?}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let observed = std::fs::read_to_string(&self.log).expect("worker observation");
        if expects_worker {
            let prefix = format!("clean-{} ", args[0]);
            let bytes: usize = observed
                .strip_prefix(&prefix)
                .expect("the dispatched worker was named and observed")
                .trim()
                .parse()
                .expect("one stack-size observation");
            // macOS reports 12 KiB of pthread overhead above the requested
            // stack in the measured control; Linux reports the requested size.
            let requested = 1024 * 1024 * 1024;
            assert!(
                (requested..=requested + 64 * 1024).contains(&bytes),
                "{args:?}: the worker stack was {bytes}, requested {requested}"
            );
        } else {
            assert!(
                observed.is_empty(),
                "startup created a verb worker: {observed}"
            );
        }
        output
    }
}

#[test]
fn run_and_compile_dispatch_get_a_large_stack_by_default() {
    let cli = ObservedCli::new();
    // Startup is not evidence for either verb's dispatch route.
    cli.run(&["--version"], false);
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = root.join("tests/fixtures/advice_replay_checker");
    let source = fixture.join("programs/advice_replay.lean");
    let source = source.to_str().expect("source path");
    let run = cli.run(&["run", source, "--decl", "main"], true);
    assert!(
        run.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        run.stdout,
        std::fs::read(fixture.join("expected/advice_replay.stdout")).expect("Lean pin")
    );
    let dir = tempfile::tempdir().expect("compile output");
    let output = dir.path().join("checker.c");
    cli.run(
        &[
            "compile",
            source,
            "--decl",
            "main",
            "--emit",
            "c",
            "-o",
            output.to_str().expect("output path"),
        ],
        true,
    );
    let emitted = std::fs::read_to_string(output).expect("compile wrote C");
    assert!(
        emitted.contains("l_main"),
        "the selected declaration was emitted"
    );
}

/// Both failure stages must retain their cause at the production caller:
/// constant-to-LCNF lowering and the isolated IR pipeline probe. Selecting
/// the refusing dependency as root controls the original reason in each case.
#[test]
fn source_dependency_refusal_keeps_the_lowering_cause() {
    // Stage 1: constant-to-LCNF lowering refusal on a source dependency (`Application head: Let(`).
    let stage1_dir = tempfile::tempdir().expect("stage1 fixture dir");
    let stage1_src = stage1_dir.path().join("stage1_bad_app_head.lean");
    std::fs::write(
        &stage1_src,
        "def badHead (x : Nat) : Nat :=\n  (let f : Nat → Nat := Nat.succ; f) x\n\ndef main : IO Unit :=\n  IO.println (toString (badHead 1))\n",
    )
    .expect("write stage1 source");
    assert_source_refusal_at_path(
        &stage1_src,
        "badHead",
        "unsupported expression: Application head: Let(",
    );

    // Stage 2: isolated IR pipeline probe refusal on a source dependency (underapplied kernel recursor value).
    let stage2_dir = tempfile::tempdir().expect("stage2 fixture dir");
    let stage2_src = stage2_dir.path().join("stage2_valueless_recursor.lean");
    std::fs::write(
        &stage2_src,
        "def badRec : Nat → (Nat → Nat → Nat) → Nat → Nat :=\n  @Nat.rec (fun _ => Nat)\n\ndef main : IO Unit :=\n  IO.println (toString (badRec 0 (fun _ ih => ih) 0))\n",
    )
    .expect("write stage2 source");
    assert_source_refusal_at_path(
        &stage2_src,
        "badRec",
        "references kernel recursor `Nat.rec`",
    );
}

#[test]
fn closed_wide_nat_literal_dependency_runs_with_lean_pinned_bytes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = root.join("tests/fixtures/advice_replay_checker");
    let source = fixture.join("programs/c23_nat_literal_of_129_bits.lean");
    let source = source.to_str().expect("source");
    let pin = |ext: &str| {
        std::fs::read(fixture.join(format!("expected/c23_nat_literal_of_129_bits.{ext}")))
            .expect("Lean pin")
    };
    let dir = tempfile::tempdir().expect("output dir");
    let output = dir.path().join("root.c");
    let compile = Command::new(env!("CARGO_BIN_EXE_clean"))
        .args([
            "compile",
            source,
            "--decl",
            "two128",
            "--emit",
            "c",
            "-o",
            output.to_str().expect("output"),
        ])
        .output()
        .expect("compile the formerly refused wide Nat dependency");
    assert_eq!(
        compile.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let emitted = std::fs::read_to_string(&output).expect("compile wrote C");
    assert!(emitted.contains("l_two128"), "the root was emitted");
    let run = Command::new(env!("CARGO_BIN_EXE_clean"))
        .args(["run", source, "--decl", "main"])
        .output()
        .expect("run through closure walk");
    let lean_rc: i32 = String::from_utf8(pin("rc"))
        .expect("rc pin")
        .trim()
        .parse()
        .expect("rc pin");
    assert_eq!(
        run.status.code(),
        Some(lean_rc),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(run.stdout, pin("stdout"), "stdout differs from pinned Lean");
    assert_eq!(run.stderr, pin("stderr"), "stderr differs from pinned Lean");
}

/// The IR-probe refusal this file used to pin, c03's `Tm.isNormal` ("reference(s)
/// never released"), closed in the compiler's RC repair (see
/// `rc_repair_tests_nested.rs`). Pin the closure end to end, against the bytes
/// pinned Lean printed: the former refusing dependency compiles as root, and
/// `run` prints exactly Lean's stdout, stderr and exit code.
#[test]
fn closed_nested_pattern_dependency_runs_with_lean_pinned_bytes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = root.join("tests/fixtures/advice_replay_checker");
    let source = fixture.join("programs/c03_nested_overlapping_patterns.lean");
    let source = source.to_str().expect("source");
    let pin = |ext: &str| {
        std::fs::read(fixture.join(format!("expected/c03_nested_overlapping_patterns.{ext}")))
            .expect("Lean pin")
    };
    let dir = tempfile::tempdir().expect("output dir");
    let output = dir.path().join("root.c");
    let compile = Command::new(env!("CARGO_BIN_EXE_clean"))
        .args([
            "compile",
            source,
            "--decl",
            "Tm.isNormal",
            "--emit",
            "c",
            "-o",
            output.to_str().expect("output"),
        ])
        .output()
        .expect("compile the formerly refused dependency");
    assert_eq!(
        compile.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let emitted = std::fs::read_to_string(&output).expect("compile wrote C");
    assert!(emitted.contains("l_Tm_isNormal"), "the root was emitted");
    let run = Command::new(env!("CARGO_BIN_EXE_clean"))
        .args(["run", source, "--decl", "main"])
        .output()
        .expect("run through closure walk");
    let lean_rc: i32 = String::from_utf8(pin("rc"))
        .expect("rc pin")
        .trim()
        .parse()
        .expect("rc pin");
    assert_eq!(
        run.status.code(),
        Some(lean_rc),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(run.stdout, pin("stdout"), "stdout differs from pinned Lean");
    assert_eq!(run.stderr, pin("stderr"), "stderr differs from pinned Lean");
}

#[allow(dead_code)]
fn assert_source_refusal(name: &str, decl: &str, cause: &str) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let source = root.join(format!(
        "tests/fixtures/advice_replay_checker/programs/{name}.lean"
    ));
    assert_source_refusal_at_path(&source, decl, cause);
}

fn assert_source_refusal_at_path(source: &Path, decl: &str, cause: &str) {
    let name = source
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("<inline>");
    let dir = tempfile::tempdir().expect("output dir");
    let root_output = dir.path().join("root.c");
    let direct = Command::new(env!("CARGO_BIN_EXE_clean"))
        .args([
            "compile",
            source.to_str().expect("source"),
            "--decl",
            decl,
            "--emit",
            "c",
            "-o",
            root_output.to_str().expect("output"),
        ])
        .output()
        .expect("compile refusing dependency directly");
    assert_eq!(direct.status.code(), Some(1));
    let direct_err = String::from_utf8_lossy(&direct.stderr);
    assert!(direct_err.contains(cause), "{name}: {direct_err}");
    let run = Command::new(env!("CARGO_BIN_EXE_clean"))
        .args(["run", source.to_str().expect("source"), "--decl", "main"])
        .output()
        .expect("run through closure walk");
    assert_eq!(run.status.code(), Some(1));
    assert!(run.stdout.is_empty());
    let err = String::from_utf8_lossy(&run.stderr);
    assert!(
        err.contains(&format!("source dependency `{decl}`")),
        "{name}: {err}"
    );
    assert!(err.contains(cause), "{name}: {err}");
    assert!(!root_output.exists(), "refused compile wrote an output");
}
