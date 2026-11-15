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
    for (name, decl, cause) in [
        (
            "c28_r4_v_one_function_over_requests",
            "run",
            "unsupported expression: Expression form: Lam(",
        ),
        (
            "c03_nested_overlapping_patterns",
            "Tm.isNormal",
            "reference(s) never released",
        ),
    ] {
        assert_source_refusal(name, decl, cause);
    }
}

fn assert_source_refusal(name: &str, decl: &str, cause: &str) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let source = root.join(format!(
        "tests/fixtures/advice_replay_checker/programs/{name}.lean"
    ));
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
