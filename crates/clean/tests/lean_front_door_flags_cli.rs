// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lean`'s command line: every flag it honours, every flag it refuses,
//! and every usage error, by exit status and exact bytes.
//!
//! Where Lean's own bytes are reproducible they are pinned Lean's, measured on
//! `bin/lean` of each release (2026-10-16). Identity is Clean's by design
//! (decision R76), so the version line is asserted in Clean's shape.

#![cfg(unix)]

#[path = "support/lean_front_door.rs"]
mod front_door;

use front_door::{assert_run, lean, scratch, stderr, stdout, write, V4_30_0_RC2, V4_8_0};

fn version_line(release: &str) -> String {
    let profile = if cfg!(debug_assertions) {
        "Debug"
    } else {
        "Release"
    };
    let out = stdout(&lean(&scratch("version-probe"), release, &["--version"]));
    assert!(
        out.starts_with("Clean (version ")
            && out.ends_with(&format!(
                "`lean` front door for Lean {release}, {profile})\n"
            )),
        "{out}"
    );
    out.trim_end().to_owned()
}

#[test]
fn test_scratch_calls_with_the_same_label_preserve_each_others_files() {
    let first = scratch("same-label-regression");
    let sentinel = write(&first, "sentinel", "first directory remains intact");
    let second = scratch("same-label-regression");
    let distinct = first != second;
    let both_exist = first.is_dir() && second.is_dir();
    let contents = std::fs::read_to_string(&sentinel);

    // Clean up before asserting so the old, colliding implementation leaves no scratch.
    std::fs::remove_dir_all(&first).expect("remove first scratch directory");
    if distinct {
        std::fs::remove_dir_all(&second).expect("remove second scratch directory");
    }
    assert!(distinct, "each scratch call must own a distinct directory");
    assert!(both_exist, "both scratch directories must remain available");
    assert_eq!(
        contents.expect("the second scratch call must preserve the first sentinel"),
        "first directory remains intact"
    );
}

#[test]
fn test_version_flags_report_cleans_identity_never_a_lean_commit() {
    let dir = scratch("version");
    for release in [V4_8_0, V4_30_0_RC2] {
        let line = version_line(release);
        assert_run(&lean(&dir, release, &["-v"]), 0, &format!("{line}\n"), "");
        assert_run(
            &lean(&dir, release, &["--vers"]),
            0,
            &format!("{line}\n"),
            "",
        );
        // `--version` acts where it stands: a later bad option is not read.
        assert_run(
            &lean(&dir, release, &["--version", "--bogus"]),
            0,
            &format!("{line}\n"),
            "",
        );
        let githash = lean(&dir, release, &["-g"]);
        let sha = stdout(&githash);
        assert_eq!(githash.status.code(), Some(0), "{}", stderr(&githash));
        assert!(
            sha.len() == 41 && sha[..40].chars().all(|c| c.is_ascii_hexdigit()),
            "-g prints Clean's 40-hex commit: {sha:?}"
        );
        assert!(
            line.contains(sha.trim()),
            "the version line carries the same commit"
        );
    }
    // `-V` exists in 4.30.0-rc2 only, and prints Clean's version.
    let short = stdout(&lean(&dir, V4_30_0_RC2, &["-V"]));
    assert!(version_line(V4_30_0_RC2).contains(short.trim()), "{short}");
    let old = lean(&dir, V4_8_0, &["--short-version"]);
    assert_eq!(old.status.code(), Some(1));
    assert!(
        stderr(&old).starts_with(
            "lean: unrecognized option `--short-version'\nUnknown command line option\nClean (version "
        ),
        "{}",
        stderr(&old)
    );
}

#[test]
fn test_help_is_leans_option_list_under_cleans_header() {
    let dir = scratch("help");
    for (release, line) in [
        (
            V4_8_0,
            "  --json             report Lean output (e.g., messages) as JSON (one per line)\n",
        ),
        (
            V4_30_0_RC2,
            "  -E, --error=kind       report Lean messages of kind as errors\n",
        ),
    ] {
        let help = lean(&dir, release, &["--help"]);
        let text = stdout(&help);
        assert_eq!(help.status.code(), Some(0));
        assert_eq!(stderr(&help), "");
        assert!(
            text.starts_with(&format!("{}\nMiscellaneous", version_line(release))),
            "{text}"
        );
        assert!(text.contains(line), "{text}");
        assert!(
            text.ends_with("--deps-json, --print-prefix, --print-libdir, --profile, --stats.\n")
        );
    }
}

#[test]
fn test_usage_errors_use_each_releases_streams() {
    let dir = scratch("usage");
    write(&dir, "a.lean", "def a := 1\n");
    write(&dir, "b.lean", "def b := 1\n");
    // Lean 4.8.0: the message and the version line on stderr, the help body
    // on stdout. Lean 4.30.0-rc2: all of it on stderr.
    let old = lean(&dir, V4_8_0, &["a.lean", "b.lean"]);
    assert_eq!(old.status.code(), Some(1));
    assert_eq!(
        stderr(&old),
        format!("Expected exactly one file name\n{}\n", version_line(V4_8_0))
    );
    assert!(
        stdout(&old).starts_with("Miscellaneous:\n  --help -h"),
        "{}",
        stdout(&old)
    );
    let new = lean(&dir, V4_30_0_RC2, &[]);
    assert_eq!(new.status.code(), Some(1));
    assert_eq!(stdout(&new), "");
    assert!(stderr(&new).starts_with(&format!(
        "Expected exactly one file name\n{}\nMiscellaneous\n",
        version_line(V4_30_0_RC2)
    )));
    for (args, first) in [
        (
            &["--bogus", "a.lean"][..],
            "lean: unrecognized option `--bogus'\n",
        ),
        (&["-Z", "a.lean"][..], "lean: invalid option -- Z\n"),
        (
            &["a.lean", "-D"][..],
            "lean: option requires an argument -- D\n",
        ),
        (
            &["--root"][..],
            "lean: option `--root' requires an argument\n",
        ),
        (&["--s", "a.lean"][..], "lean: option `--s' is ambiguous\n"),
    ] {
        let run = lean(&dir, V4_30_0_RC2, args);
        assert_eq!(run.status.code(), Some(1), "{args:?}");
        assert!(
            stderr(&run).starts_with(&format!(
                "{first}Unknown command line option\nClean (version "
            )),
            "{args:?}: {}",
            stderr(&run)
        );
    }
}

#[test]
fn test_every_unsupported_flag_is_refused_by_name() {
    let dir = scratch("refused");
    write(&dir, "a.lean", "def a := 1\n");
    let cases: &[(&[&str], &str, &str)] = &[
        (
            &["-o", "a.olean", "a.lean"],
            "-o",
            "Clean does not write Lean-format `.olean` files",
        ),
        (
            &["--o=a.olean", "a.lean"],
            "--o",
            "Clean does not write Lean-format `.olean` files",
        ),
        (
            &["-i", "a.ilean", "a.lean"],
            "-i",
            "Clean does not write Lean `.ilean` files",
        ),
        (
            &["-c", "a.c", "a.lean"],
            "-c",
            "Clean does not emit Lean's C output",
        ),
        (
            &["-b", "a.bc", "a.lean"],
            "-b",
            "Clean emits no LLVM bitcode",
        ),
        (
            &["--plugin=x.so", "a.lean"],
            "--plugin",
            "Clean cannot load Lean shared-library plugins",
        ),
        (
            &["--load-dynlib=x.so", "a.lean"],
            "--load-dynlib",
            "Clean cannot load shared libraries",
        ),
        (
            &["--setup=s.json", "a.lean"],
            "--setup",
            "Clean does not read Lean's module-setup JSON",
        ),
        (
            &["--server"],
            "--server",
            "Clean's language server is `clean lsp`",
        ),
        (
            &["--worker"],
            "--worker",
            "Clean's language server is `clean lsp`",
        ),
        (
            &["-t", "0", "a.lean"],
            "-t",
            "Clean has no Lean trust levels",
        ),
        (
            &["-M", "100", "a.lean"],
            "-M",
            "Clean has no Lean memory limit",
        ),
        (
            &["-T", "10", "a.lean"],
            "-T",
            "Clean has no Lean allocation-count timeout",
        ),
        (
            &["-j", "2", "a.lean"],
            "-j",
            "Clean elaborates a file on one thread",
        ),
        (
            &["-s", "1024", "a.lean"],
            "-s",
            "Clean does not take a thread stack size",
        ),
        (
            &["--profile", "a.lean"],
            "--profile",
            "Clean prints no Lean profiler output",
        ),
        (
            &["--stats", "a.lean"],
            "--stats",
            "Clean prints no Lean environment statistics",
        ),
        (
            &["--features"],
            "--features",
            "Clean does not report Lean compiler features",
        ),
        (
            &["--print-prefix"],
            "--print-prefix",
            "Clean has no Lean installation prefix",
        ),
        (
            &["--print-libdir"],
            "--print-libdir",
            "Clean has no Lean library directory",
        ),
        (
            &["--deps-json", "a.lean"],
            "--deps-json",
            "Clean does not print Lean's JSON",
        ),
    ];
    for (args, flag, why) in cases {
        let run = lean(&dir, V4_30_0_RC2, args);
        let err = stderr(&run);
        assert_eq!(run.status.code(), Some(1), "{args:?}");
        assert_eq!(stdout(&run), "", "{args:?}");
        assert!(
            err.starts_with(&format!("clean: `lean {flag}` is not supported: {why}"))
                && err.ends_with('\n')
                && err.lines().count() == 1,
            "{args:?}: {err}"
        );
    }
}

#[test]
fn test_define_errors_are_each_releases_words() {
    let dir = scratch("define");
    write(&dir, "a.lean", "def a := 1\n");
    assert_run(
        &lean(&dir, V4_8_0, &["-Dbogus=1", "a.lean"]),
        1,
        "",
        "invalid -D parameter, unknown configuration option 'bogus'\n",
    );
    assert_run(
        &lean(&dir, V4_8_0, &["-D", "autoImplicit=0", "a.lean"]),
        1,
        "",
        "invalid -D parameter, invalid configuration option 'autoImplicit' value, it must be \
         true/false\n",
    );
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["-Dpp.all", "a.lean"]),
        1,
        "",
        "error: invalid -D parameter, argument must contain '='\n",
    );
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["-DautoImplicit=0", "a.lean"]),
        1,
        "",
        "error: invalid -D parameter, invalid configuration option '0' value, it must be \
         true/false\n",
    );
    // Lean's default is a no-op and says nothing; `printMessageEndPos` is the
    // front door's own option.
    assert_run(
        &lean(
            &dir,
            V4_30_0_RC2,
            &["-Dlinter.all=false", "-DprintMessageEndPos=true", "a.lean"],
        ),
        0,
        "",
        "",
    );
}

#[test]
fn test_missing_file_is_each_releases_message() {
    let dir = scratch("missing");
    assert_run(
        &lean(&dir, V4_8_0, &["nope.lean"]),
        1,
        "",
        "file 'nope.lean' not found\n",
    );
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["nope.lean"]),
        1,
        "",
        "no such file or directory (error code: 4294967294)\n  file: nope.lean\n",
    );
}

#[test]
fn test_deps_of_a_prelude_file() {
    let dir = scratch("deps");
    write(&dir, "p.lean", "prelude\n");
    assert_run(&lean(&dir, V4_30_0_RC2, &["--deps", "p.lean"]), 0, "", "");
    write(&dir, "q.lean", "prelude\nimport Nope.Mod\n");
    assert_run(
        &lean(&dir, V4_8_0, &["--deps", "q.lean"]),
        1,
        "",
        "unknown package 'Nope'\n",
    );
}

#[test]
fn test_unmodelled_toolchain_is_refused_by_name() {
    let dir = scratch("toolchain");
    write(&dir, "a.lean", "def a := 1\n");
    // Reader measurements must not silently promote a source dialect.
    for version in ["4.9.0", "4.36.0-rc2"] {
        let toolchain = format!("leanprover/lean4:v{version}");
        write(&dir, "lean-toolchain", &format!("{toolchain}\n"));
        let run = std::process::Command::new(front_door::clean_path())
            .args(["lean", "a.lean"])
            .current_dir(&dir)
            .env_remove("CLEAN_LEAN_VERSION")
            .output()
            .expect("spawn");
        assert_eq!(run.status.code(), Some(1), "{toolchain}");
        assert_eq!(stdout(&run), "", "{toolchain}");
        assert!(
            stderr(&run).contains(&format!(
                "names the toolchain `{toolchain}`, which Clean's \
                 `lean` front door does not model"
            )),
            "{}",
            stderr(&run)
        );
    }
    // The toolchain names a modelled release: it is that release.
    write(&dir, "lean-toolchain", "leanprover/lean4:v4.8.0\n");
    let run = std::process::Command::new(front_door::clean_path())
        .args(["lean", "--version"])
        .current_dir(&dir)
        .env_remove("CLEAN_LEAN_VERSION")
        .output()
        .expect("spawn");
    assert!(
        stdout(&run).contains("front door for Lean 4.8.0"),
        "{}",
        stdout(&run)
    );
}

/// `clean lean <args>` in `dir` with no `CLEAN_LEAN_VERSION`, so the nearest
/// `lean-toolchain` chooses the release.
fn lean_by_toolchain(dir: &std::path::Path, args: &[&str]) -> std::process::Output {
    std::process::Command::new(front_door::clean_path())
        .arg("lean")
        .args(args)
        .current_dir(dir)
        .env_remove("CLEAN_LEAN_VERSION")
        .env_remove("LEAN_PATH")
        .output()
        .expect("spawn clean lean")
}

/// A project `clean lake new` or `clean lake init` made speaks Clean's pin.
/// Its `lean-toolchain` reads `clean`, which the front door refused by name
/// (exit 1, before reading any option) until the scaffold's own name chose
/// the pin.
#[test]
fn test_lean_front_door_in_a_clean_scaffolded_project_speaks_the_pin() {
    let dir = scratch("scaffold");
    let new = std::process::Command::new(front_door::clean_path())
        .args(["lake", "new", "made_by_new", "--exe"])
        .current_dir(&dir)
        .env("PATH", "/usr/bin:/bin")
        .output()
        .expect("spawn clean lake new");
    assert!(new.status.success(), "clean lake new: {}", stderr(&new));
    let init_dir = dir.join("made_by_init");
    std::fs::create_dir(&init_dir).expect("create init dir");
    let init = std::process::Command::new(front_door::clean_path())
        .arg("lake")
        .arg("--dir")
        .arg(&init_dir)
        .args(["init", "made_by_init"])
        .current_dir(&dir)
        .env("PATH", "/usr/bin:/bin")
        .output()
        .expect("spawn clean lake init");
    assert!(init.status.success(), "clean lake init: {}", stderr(&init));

    for project in [dir.join("made_by_new"), init_dir] {
        let toolchain = std::fs::read_to_string(project.join("lean-toolchain"))
            .expect("the scaffold writes lean-toolchain");
        assert_eq!(toolchain, "clean\n", "{}", project.display());
        let pinned = lean(&project, V4_30_0_RC2, &["--version"]);
        assert!(
            stdout(&pinned).contains(&format!("`lean` front door for Lean {V4_30_0_RC2}, ")),
            "{}",
            stdout(&pinned)
        );
        // Exactly what naming the pin explicitly prints.
        assert_run(
            &lean_by_toolchain(&project, &["--version"]),
            0,
            &stdout(&pinned),
            "",
        );
    }
    // The scaffold's own `Main.lean` is accepted as `lean Main.lean` accepts
    // it: no message, exit 0.
    assert_run(
        &lean_by_toolchain(&dir.join("made_by_new"), &["Main.lean"]),
        0,
        "",
        "",
    );
}

#[test]
fn test_binary_invoked_as_lean_is_the_front_door() {
    let dir = scratch("argv0");
    let link = dir.join("lean");
    std::os::unix::fs::symlink(front_door::clean_path(), &link).expect("symlink");
    write(&dir, "a.lean", "theorem t : 1 = 1 := sorry\n");
    let run = std::process::Command::new(&link)
        .arg("a.lean")
        .current_dir(&dir)
        .env("CLEAN_LEAN_VERSION", V4_8_0)
        .output()
        .expect("spawn lean symlink");
    assert_run(
        &run,
        0,
        "a.lean:1:8: warning: declaration uses 'sorry'\n",
        "",
    );
}

#[test]
fn test_root_names_the_module_and_never_fails_the_run() {
    // Measured: pinned Lean exits 0 with a root that does not exist or does
    // not hold the file (its main module is then `_stdin`).
    let dir = scratch("root");
    std::fs::create_dir_all(dir.join("sub")).expect("sub dir");
    write(
        &dir,
        "sub/f.lean",
        "private def secret : Nat := 1\nexample : secret = 1 := rfl\n",
    );
    for root in ["sub", ".", "nonexistent", "-R"] {
        let args: Vec<&str> = if root == "-R" {
            vec!["-R", ".", "sub/f.lean"]
        } else {
            vec!["--root", root, "sub/f.lean"]
        };
        assert_run(&lean(&dir, V4_30_0_RC2, &args), 0, "", "");
    }
}

/// `--run` builds `main` with a C compiler, as `clean run` does: no compiler,
/// no verdict (the same fail-closed rule as `tostring_instances_cli.rs`).
fn require_cc() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_owned());
    let found = std::process::Command::new(cc)
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success());
    assert!(
        found,
        "`clean lean --run` needs a C compiler ($CC, else `cc`), and none was found"
    );
}

#[test]
fn test_run_prints_the_files_messages_then_runs_main_with_its_status() {
    require_cc();
    let dir = scratch("run");
    write(
        &dir,
        "r.lean",
        "def main (args : List String) : IO UInt32 := do\n  IO.println (toString args)\n  \
         return 3\n#eval 1\n",
    );
    // 4.30.0-rc2: everything after the file is the program's, flags included
    // (measured: pinned Lean prints `1`, then `[a, -x, --json]`, exit 3).
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["--run", "r.lean", "a", "-x", "--json"]),
        3,
        "1\n[a, -x, --json]\n",
        "",
    );
    // A file that logs an error is not run.
    write(
        &dir,
        "bad.lean",
        "def main : IO Unit := IO.println \"ran\"\nexample : 1 = 2 := rfl\n",
    );
    let run = lean(&dir, V4_30_0_RC2, &["--run", "bad.lean"]);
    assert_eq!(run.status.code(), Some(1));
    assert!(!stdout(&run).contains("ran"), "{}", stdout(&run));
}
