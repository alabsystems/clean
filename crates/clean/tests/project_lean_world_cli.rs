// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check` and `clean-native` resolve a run's imports in the Lean world
//! named by the `lean-toolchain` of the entry file's Lake package (decision
//! R111 in `docs/DECISIONS.md`; trust-ir gap G72).
//!
//! Before R111 every `import` resolved against the checkout's pin
//! (v4.30.0-rc2), whatever the project pinned. Each claim here is checked
//! against what pinned Lean does with the same files (measured 2026-10-22,
//! `lean` of each toolchain with no `LEAN_PATH`):
//!
//! | file (`import Init.Prelude` + one def) | Lean 4.8.0 | v4.30.0-rc2 |
//! |---|---|---|
//! | `Array.emptyWithCapacity 3` | refused (unknown constant) | accepted |
//! | `List.redLength l` | accepted | refused (unknown constant) |
//! | `Array.mkEmpty 3` | accepted | accepted |
//! | `@Lean.Syntax.setArg` | accepted | accepted |
//!
//! Lean 4.8.0 also refuses the first file when `LEAN_PATH` names
//! v4.30.0-rc2's library (`invalid header`), and `lake build` compiles every
//! package of a workspace, a dependency with its own `lean-toolchain`
//! included, with the root's toolchain.
//!
//! Lean also imports all of `Init` implicitly; Clean adds no implicit import
//! and reads `Init.Prelude` alone. Lean's `prelude` header, which turns that
//! implicit import off, is not used here: Clean does not parse it (`unknown
//! command`). The first three names are in `Init.Prelude` of each world that
//! has them, and Clean's own prelude has none of them, so Clean and Lean
//! agree on each in both worlds. (`Array.data` would not do: Lean 4.8.0's
//! name for `Array.toList`, it is absent from v4.30.0-rc2's `Init`, but
//! Clean's prelude declares it.) v4.30.0-rc2 moved `Lean.Syntax.setArg` out
//! of `Init.Prelude` (to `Init.Syntax`), so it is asserted only in Lean
//! 4.8.0's world.

use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TOOLCHAIN_4_8_0: &str = "leanprover/lean4:v4.8.0";
const ORACLE: &str = "leanprover/lean4:v4.30.0-rc2";

const EMPTY_WITH_CAPACITY: &str =
    "import Init.Prelude\n\ndef usesEmptyWithCapacity : Array Nat := Array.emptyWithCapacity 3\n";
const RED_LENGTH: &str =
    "import Init.Prelude\n\ndef usesRedLength (l : List Nat) : Nat := List.redLength l\n";
const MK_EMPTY: &str = "import Init.Prelude\n\ndef usesMkEmpty : Array Nat := Array.mkEmpty 3\n";
const SET_ARG: &str = "import Init.Prelude\n\ndef usesSetArg := @Lean.Syntax.setArg\n";

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// `clean check <file>` from `dir`, with every search-path variable removed
/// and then `env` set.
fn check_in(dir: &Path, file: &str, env: &[(&str, &Path)]) -> (Output, String) {
    check_args(dir, &["check", file], env)
}

/// `clean <args>` from `dir`, with every search-path variable removed and
/// then `env` set.
fn check_args(dir: &Path, args: &[&str], env: &[(&str, &Path)]) -> (Output, String) {
    let mut command = Command::new(clean_path());
    command
        .args(args)
        .current_dir(dir)
        .env_remove("LEAN_PATH")
        .env_remove("MATHLIB_PATH")
        .env_remove("LEAN_PACKAGES_PATH");
    for (key, value) in env {
        command.env(key, value);
    }
    let output = command.output().expect("run clean check");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output, text)
}

/// Write `files` (relative path, contents) under a fresh directory.
fn tree(files: &[(&str, &str)]) -> tempfile::TempDir {
    let root = tempfile::tempdir().expect("tempdir");
    for (rel, contents) in files {
        let path = root.path().join(rel);
        fs::create_dir_all(path.parent().expect("parent")).expect("dirs");
        fs::write(path, contents).expect("file");
    }
    root
}

/// `clean check Probe.lean` in a one-file project holding `source` and, when
/// given, `lean-toolchain` = `toolchain`.
fn check(toolchain: Option<&str>, source: &str, env: &[(&str, &Path)]) -> (Output, String) {
    let toolchain_line = toolchain.map(|t| format!("{t}\n"));
    let mut files = vec![("proj/Probe.lean", source)];
    if let Some(line) = toolchain_line.as_deref() {
        files.push(("proj/lean-toolchain", line));
    }
    let root = tree(&files);
    check_in(&root.path().join("proj"), "Probe.lean", env)
}

fn assert_passes(what: &str, (output, text): &(Output, String)) {
    assert!(output.status.success(), "{what} must pass:\n{text}");
}

fn assert_fails_naming(what: &str, (output, text): &(Output, String), needle: &str) {
    assert!(!output.status.success(), "{what} must fail:\n{text}");
    assert!(
        text.contains(needle),
        "{what} must name `{needle}`:\n{text}"
    );
}

/// The installed Lean 4.8.0 library, when there is one.
fn lean_4_8_0() -> Option<PathBuf> {
    clean_olean::installed_lean_lib_path(TOOLCHAIN_4_8_0)
}

/// With Lean 4.8.0 absent, the subject (checking in Lean 4.8.0's world)
/// cannot be measured. This returns what Clean says of a Lean 4.8.0 project
/// instead (its caller asserts the refusal by name) and reports the subject
/// unmeasured the way `crates/clean-olean/tests/support/installed_lean.rs`
/// does: a `<GATE>_GATE=skipped:<reason>` line that `scripts/verify_runner.py`
/// records as SKIPPED, never GREEN. `CLEAN_REQUIRE_LEAN_V4_8_0` makes it a
/// failure.
fn refusal_without_lean_4_8_0(test: &str) -> String {
    let (output, text) = check(Some(TOOLCHAIN_4_8_0), MK_EMPTY, &[]);
    assert!(!output.status.success(), "{test}: {text}");
    assert!(
        std::env::var_os("CLEAN_REQUIRE_LEAN_V4_8_0").is_none(),
        "{test}: Lean 4.8.0 is not installed and CLEAN_REQUIRE_LEAN_V4_8_0 demands a measurement"
    );
    let line = "\nPROJECT_LEAN_WORLD_GATE=skipped:lean-v4.8.0-not-installed\n";
    let mut stderr = std::io::stderr().lock();
    let _ = stderr.write_all(line.as_bytes());
    let _ = stderr.flush();
    text
}

fn oracle_lib() -> PathBuf {
    clean_olean::pinned_lean_lib_path().expect("the workspace's pinned Lean toolchain")
}

#[test]
fn test_a_lean_4_8_project_checks_against_lean_4_8s_init() {
    let project = Some(TOOLCHAIN_4_8_0);
    let Some(lib) = lean_4_8_0() else {
        let refusal =
            refusal_without_lean_4_8_0("test_a_lean_4_8_project_checks_against_lean_4_8s_init");
        assert!(refusal.contains("is not installed"), "{refusal}");
        return;
    };
    assert!(lib.join("Init/Prelude.olean").is_file());
    assert_fails_naming(
        "Array.emptyWithCapacity under Lean 4.8.0",
        &check(project, EMPTY_WITH_CAPACITY, &[]),
        "emptyWithCapacity",
    );
    assert_passes(
        "List.redLength under Lean 4.8.0",
        &check(project, RED_LENGTH, &[]),
    );
    assert_passes(
        "Lean.Syntax.setArg under Lean 4.8.0",
        &check(project, SET_ARG, &[]),
    );
    assert_passes(
        "Array.mkEmpty under Lean 4.8.0",
        &check(project, MK_EMPTY, &[]),
    );
    // Twins, in the Oracle's world, as pinned v4.30.0-rc2 has them.
    assert_passes(
        "Array.emptyWithCapacity in the Oracle's world",
        &check(None, EMPTY_WITH_CAPACITY, &[]),
    );
    assert_fails_naming(
        "List.redLength in the Oracle's world",
        &check(None, RED_LENGTH, &[]),
        "redLength",
    );
}

#[test]
fn test_lean_path_never_chooses_the_projects_world() {
    let Some(lib) = lean_4_8_0() else {
        let refusal = refusal_without_lean_4_8_0("test_lean_path_never_chooses_the_projects_world");
        assert!(refusal.contains("is not installed"), "{refusal}");
        return;
    };
    // A v4.8.0 project with the Oracle's library on LEAN_PATH: that library
    // is searched first, as `lean` searches LEAN_PATH before its sysroot,
    // and its parts are refused as a second world, as Lean 4.8.0 refuses
    // them ("invalid header"); never read as the project's.
    let oracle = oracle_lib();
    assert_fails_naming(
        "a v4.8.0 project with the Oracle's library on LEAN_PATH",
        &check(
            Some(TOOLCHAIN_4_8_0),
            EMPTY_WITH_CAPACITY,
            &[("LEAN_PATH", &oracle)],
        ),
        "mixed Lean worlds",
    );
    // Twin: the project's own library on LEAN_PATH is the project's world.
    assert_passes(
        "a v4.8.0 project with its own library on LEAN_PATH",
        &check(Some(TOOLCHAIN_4_8_0), MK_EMPTY, &[("LEAN_PATH", &lib)]),
    );
}

/// The root package's lakefile: one library whose roots are every module
/// the workspace tests use, so `lake build` from `ws/` builds them all.
const WS_LAKEFILE: &str = "name = \"ws\"\n\n[[lean_lib]]\nname = \"Ws\"\n\
     roots = [\"Main\", \"A\", \"Inner\", \"Std.Data.HashMap\"]\n";

/// A nested package's lakefile, building `Inner/Lib.lean` and `Inner/B.lean`.
const INNER_LAKEFILE: &str =
    "name = \"inner\"\n\n[[lean_lib]]\nname = \"Inner\"\nroots = [\"Lib\", \"B\"]\n";

/// A Lake workspace `ws/` whose root pins `root_toolchain`, with `Inner/`
/// pinned to `inner_toolchain` and, when `inner_package`, a lakefile of its
/// own (a package nested in the workspace). The root's library builds
/// `Inner/` either way, as pinned Lake does from `ws/`. `Main.lean` (`main`)
/// imports `Inner.Lib` (`lib`), whose source the run elaborates; `extra` adds
/// files.
fn workspace(
    root_toolchain: &str,
    inner_toolchain: &str,
    inner_package: bool,
    lib: &str,
    main: &str,
    extra: &[(&str, &str)],
) -> tempfile::TempDir {
    let root_line = format!("{root_toolchain}\n");
    let inner_line = format!("{inner_toolchain}\n");
    let mut files = vec![
        ("ws/lakefile.toml", WS_LAKEFILE),
        ("ws/lean-toolchain", root_line.as_str()),
        ("ws/Inner/lean-toolchain", inner_line.as_str()),
        ("ws/Inner/Lib.lean", lib),
        ("ws/Main.lean", main),
    ];
    if inner_package {
        files.push(("ws/Inner/lakefile.toml", INNER_LAKEFILE));
    }
    files.extend_from_slice(extra);
    tree(&files)
}

/// [`workspace`] with an Oracle-pinned `Inner/` package, where `Inner.Lib`
/// and `Main` both use `name`.
fn workspace_with_inner_project(root_toolchain: &str, name: &str) -> tempfile::TempDir {
    let lib = format!("import Init.Prelude\n\ndef Inner.e : Array Nat := {name} 3\n");
    let main = format!("import Inner.Lib\n\ndef Main.f : Array Nat := {name} 4\n");
    workspace(root_toolchain, ORACLE, true, &lib, &main, &[])
}

#[test]
fn test_one_world_per_run_the_root_projects() {
    let Some(_lib) = lean_4_8_0() else {
        let refusal = refusal_without_lean_4_8_0("test_one_world_per_run_the_root_projects");
        assert!(refusal.contains("is not installed"), "{refusal}");
        return;
    };
    // `Inner/`'s own package pins the Oracle; Lake builds it, as a package of
    // the workspace, with the root's Lean 4.8.0, which refuses
    // `Array.emptyWithCapacity`.
    let ws = workspace_with_inner_project(TOOLCHAIN_4_8_0, "Array.emptyWithCapacity");
    assert_fails_naming(
        "a v4.8.0 workspace whose inner project pins the Oracle",
        &check_in(&ws.path().join("ws"), "Main.lean", &[]),
        "emptyWithCapacity",
    );
    // The same under `--imports-prefer-olean` (no artifact for `Inner.Lib`).
    assert_fails_naming(
        "the same under --imports-prefer-olean",
        &check_args(
            &ws.path().join("ws"),
            &["check", "--imports-prefer-olean", "Main.lean"],
            &[],
        ),
        "emptyWithCapacity",
    );
    // Twin: the same layout with a name Lean 4.8.0 has passes.
    let ws = workspace_with_inner_project(TOOLCHAIN_4_8_0, "Array.mkEmpty");
    assert_passes(
        "a v4.8.0 workspace using Array.mkEmpty",
        &check_in(&ws.path().join("ws"), "Main.lean", &[]),
    );
}

/// The entry file's world is the one the tool that checks it reads (decision
/// R111). A module of the root package's library takes the root's
/// `lean-toolchain` whichever file is the entry, as `lake build Inner.Lib`,
/// `lake env lean Inner/Lib.lean` and `lean Inner/Lib.lean` run from the root
/// do (measured 2026-10-22: Lean 4.8.0, "unknown constant
/// 'Array.emptyWithCapacity'", though `Inner/lean-toolchain` names
/// v4.30.0-rc2). A file no package above it builds takes its own nearer
/// `lean-toolchain`, as `lean` in its directory does (`lake build proj.Probe`
/// from the package is "unknown target"). An `Inner/` with a lakefile of its
/// own builds with its own.
#[test]
fn test_an_entry_file_takes_its_lake_packages_world() {
    let Some(_lib) = lean_4_8_0() else {
        let refusal =
            refusal_without_lean_4_8_0("test_an_entry_file_takes_its_lake_packages_world");
        assert!(refusal.contains("is not installed"), "{refusal}");
        return;
    };
    let lib = "import Init.Prelude\n\ndef Inner.e : Array Nat := Array.emptyWithCapacity 3\n";
    let main = "import Inner.Lib\n\ndef Main.n : Nat := 2\n";
    let ws = workspace(TOOLCHAIN_4_8_0, ORACLE, false, lib, main, &[]);
    let dir = ws.path().join("ws");
    assert_fails_naming(
        "Inner/Lib.lean as the entry, in a directory of the v4.8.0 package",
        &check_in(&dir, "Inner/Lib.lean", &[]),
        "emptyWithCapacity",
    );
    assert_fails_naming(
        "the same file imported by the root's Main.lean",
        &check_in(&dir, "Main.lean", &[]),
        "emptyWithCapacity",
    );
    // Twin: `Inner/` with a lakefile of its own is a package of its own.
    let ws = workspace(TOOLCHAIN_4_8_0, ORACLE, true, lib, main, &[]);
    assert_passes(
        "Inner/Lib.lean as the entry of its own Oracle-pinned package",
        &check_in(&ws.path().join("ws"), "Inner/Lib.lean", &[]),
    );
    // A Lean 4.8.0 project under an Oracle-pinned package that does not
    // build it keeps its own world.
    let outer = |source: &str, lakefile: &str| {
        tree(&[
            ("outer/lakefile.toml", lakefile),
            ("outer/lean-toolchain", "leanprover/lean4:v4.30.0-rc2\n"),
            ("outer/proj/lean-toolchain", "leanprover/lean4:v4.8.0\n"),
            ("outer/proj/Probe.lean", source),
        ])
    };
    let only_outer = "name = \"outer\"\n\n[[lean_lib]]\nname = \"Outer\"\n";
    let layout = outer(EMPTY_WITH_CAPACITY, only_outer);
    assert_fails_naming(
        "a Lean 4.8.0 project the enclosing package does not build",
        &check_in(&layout.path().join("outer/proj"), "Probe.lean", &[]),
        "emptyWithCapacity",
    );
    let layout = outer(MK_EMPTY, only_outer);
    assert_passes(
        "its Array.mkEmpty twin",
        &check_in(&layout.path().join("outer/proj"), "Probe.lean", &[]),
    );
    // A lakefile that does not say plainly whether it builds the file, over
    // two toolchains: refused by name rather than chosen.
    let layout = outer(
        MK_EMPTY,
        "name = \"outer\"\n\n[[lean_lib]]\nname = \"Outer\"\nglobs = [\"Outer.+\"]\n",
    );
    assert_fails_naming(
        "a lakefile with globs over two toolchains",
        &check_in(&layout.path().join("outer/proj"), "Probe.lean", &[]),
        "does not say plainly",
    );
}

#[test]
fn test_a_refused_root_world_reads_no_lean_part() {
    // The root's world is refused; `Main`'s one import is satisfied from
    // source, by a package whose own lean-toolchain names the Oracle. Its
    // `import Init.Prelude` is refused in the run's world, not read in the
    // Oracle's.
    let ws = workspace_with_inner_project("leanprover/lean4:v4.99.0", "Array.mkEmpty");
    let refused = check_in(&ws.path().join("ws"), "Main.lean", &[]);
    assert_fails_naming("a v4.99.0 workspace", &refused, "leanprover/lean4:v4.99.0");
    assert_fails_naming("a v4.99.0 workspace", &refused, "is not a Lean world");
    // Twin: the same layout in the Oracle's world passes.
    let ws = workspace_with_inner_project(ORACLE, "Array.mkEmpty");
    assert_passes(
        "the same workspace pinned to the Oracle",
        &check_in(&ws.path().join("ws"), "Main.lean", &[]),
    );
}

/// A refused world refuses every import of a Lean module, never one the run
/// elaborated from the project's own source: a project whose imports are all
/// its own source reads no Lean part, so it is checked as the same code with
/// no imports is (pinned Lake builds such a project in any world).
#[test]
fn test_a_refused_world_still_checks_a_project_whose_imports_are_its_own_source() {
    let toolchain = "leanprover/lean4:v4.99.0\n";
    let project = tree(&[
        ("proj/lean-toolchain", toolchain),
        ("proj/Lib.lean", "def Lib.two : Nat := 2\n"),
        (
            "proj/Main.lean",
            "import Lib\n\ntheorem Main.t : Lib.two = 2 := rfl\n",
        ),
    ]);
    assert_passes(
        "a v4.99.0 project whose only import is its own source",
        &check_in(&project.path().join("proj"), "Main.lean", &[]),
    );
    // Twin: the same project importing a Lean module is refused by name.
    let project = tree(&[
        ("proj/lean-toolchain", toolchain),
        (
            "proj/Lib.lean",
            "import Init.Prelude\n\ndef Lib.two : Nat := 2\n",
        ),
        (
            "proj/Main.lean",
            "import Lib\n\ntheorem Main.t : Lib.two = 2 := rfl\n",
        ),
    ]);
    assert_fails_naming(
        "the same project when Lib imports Init.Prelude",
        &check_in(&project.path().join("proj"), "Main.lean", &[]),
        "leanprover/lean4:v4.99.0",
    );
}

#[test]
fn test_a_lake_dependency_is_checked_in_the_root_projects_world() {
    let Some(_lib) = lean_4_8_0() else {
        let refusal = refusal_without_lean_4_8_0(
            "test_a_lake_dependency_is_checked_in_the_root_projects_world",
        );
        assert!(refusal.contains("is not installed"), "{refusal}");
        return;
    };
    let oracle_line = format!("{ORACLE}\n");
    let root_line = format!("{TOOLCHAIN_4_8_0}\n");
    let layout = |name: &str| {
        let dep = format!("import Init.Prelude\n\ndef Dep.d : Array Nat := {name} 3\n");
        tree(&[
            ("ws/lakefile.toml", "name = \"ws\"\n"),
            ("ws/lean-toolchain", &root_line),
            ("ws/.lake/packages/Dep/lean-toolchain", &oracle_line),
            ("ws/.lake/packages/Dep/Dep.lean", &dep),
            (
                "ws/Probe.lean",
                "import Dep\n\ndef Probe.p : Array Nat := Dep.d\n",
            ),
        ])
    };
    let ws = layout("Array.emptyWithCapacity");
    assert_fails_naming(
        "a dependency pinned to the Oracle under a v4.8.0 root",
        &check_in(&ws.path().join("ws"), "Probe.lean", &[]),
        "emptyWithCapacity",
    );
    // The dependency checked on its own, from the workspace, takes the
    // root's world too.
    assert_fails_naming(
        "the dependency checked as the entry file",
        &check_in(&ws.path().join("ws"), ".lake/packages/Dep/Dep.lean", &[]),
        "emptyWithCapacity",
    );
    // Twin: a name Lean 4.8.0 has passes through the dependency.
    let ws = layout("Array.mkEmpty");
    assert_passes(
        "a dependency using Array.mkEmpty under a v4.8.0 root",
        &check_in(&ws.path().join("ws"), "Probe.lean", &[]),
    );
}

#[test]
fn test_a_project_in_a_world_clean_does_not_read_is_refused_by_name() {
    let refused = check(Some("leanprover/lean4:v4.99.0"), MK_EMPTY, &[]);
    assert_fails_naming("a v4.99.0 project", &refused, "leanprover/lean4:v4.99.0");
    assert_fails_naming("a v4.99.0 project", &refused, "is not a Lean world");
    // `--permissive-imports` does not continue past it.
    let root = tree(&[
        ("proj/lean-toolchain", "leanprover/lean4:v4.99.0\n"),
        ("proj/Probe.lean", MK_EMPTY),
    ]);
    assert_fails_naming(
        "a v4.99.0 project under --permissive-imports",
        &check_args(
            &root.path().join("proj"),
            &["check", "--permissive-imports", "Probe.lean"],
            &[],
        ),
        "leanprover/lean4:v4.99.0",
    );
    // Twin: a Clean toolchain (what `clean lake new` writes) is the pin's world.
    assert_passes(
        "a clean:stable project",
        &check(Some("clean:stable"), EMPTY_WITH_CAPACITY, &[]),
    );
}

#[test]
fn test_a_file_with_no_imports_is_checked_whatever_the_project_pins() {
    // The world decides imports only: a file with none checks in any project.
    let source = "def two : Nat := 2\n";
    assert_passes(
        "a refused-world project with no imports",
        &check(Some("leanprover/lean4:v4.99.0"), source, &[]),
    );
}

/// An Oracle-pinned workspace whose nested `Inner/` package pins Lean 4.8.0,
/// with `Inner.Lib` using `lib_def` and `Main` importing it.
fn oracle_root_with_a_lean_4_8_package(lib_def: &str) -> tempfile::TempDir {
    let lib = format!("import Init.Prelude\n\n{lib_def}\n");
    let main = "import Inner.Lib\n\ndef Main.n : Nat := 2\n";
    workspace(ORACLE, TOOLCHAIN_4_8_0, true, &lib, main, &[])
}

/// `clean-native` builds a program in one world, its entry file's
/// (`clean compile` here; `clean run`, `clean extract` and `lake build`'s
/// executable step share the walk). Lake builds the nested Lean 4.8.0
/// package with the root's v4.30.0-rc2, which refuses `List.redLength`
/// ("Unknown constant", measured 2026-10-22); a walk that let each file
/// select its own world accepted it.
#[test]
fn test_a_native_build_elaborates_every_file_in_its_entry_files_world() {
    let Some(_lib) = lean_4_8_0() else {
        let refusal = refusal_without_lean_4_8_0(
            "test_a_native_build_elaborates_every_file_in_its_entry_files_world",
        );
        assert!(refusal.contains("is not installed"), "{refusal}");
        return;
    };
    let compile = [
        "compile",
        "Main.lean",
        "--decl",
        "Main.n",
        "--emit",
        "l5cnf",
    ];
    let ws =
        oracle_root_with_a_lean_4_8_package("def Inner.r (l : List Nat) : Nat := List.redLength l");
    let dir = ws.path().join("ws");
    assert_fails_naming(
        "clean compile of an Oracle root over a Lean 4.8.0 package using List.redLength",
        &check_args(&dir, &compile, &[]),
        "redLength",
    );
    assert_fails_naming(
        "clean check of the same",
        &check_in(&dir, "Main.lean", &[]),
        "redLength",
    );
    // Twin: a name the Oracle's library has.
    let ws = oracle_root_with_a_lean_4_8_package("def Inner.e : Array Nat := Array.mkEmpty 3");
    let dir = ws.path().join("ws");
    assert_passes(
        "clean compile of the same layout using Array.mkEmpty",
        &check_args(&dir, &compile, &[]),
    );
    assert_passes(
        "clean check of the same layout using Array.mkEmpty",
        &check_in(&dir, "Main.lean", &[]),
    );
}

/// A file elaborated next to a module it does not import is re-elaborated
/// in its own import closure (the faithful environment); that run is in the
/// run's world too, so `Inner.B`, which Lean 4.8.0 accepts, does not diverge.
#[test]
fn test_the_faithful_re_elaboration_is_in_the_runs_world() {
    let Some(_lib) = lean_4_8_0() else {
        let refusal =
            refusal_without_lean_4_8_0("test_the_faithful_re_elaboration_is_in_the_runs_world");
        assert!(refusal.contains("is not installed"), "{refusal}");
        return;
    };
    let ws = workspace(
        TOOLCHAIN_4_8_0,
        ORACLE,
        true,
        "import Init.Prelude\n\ndef Inner.e : Nat := 1\n",
        "import A\nimport Inner.B\n\ndef Main.m : Nat := A.a\n",
        &[
            ("ws/A.lean", "import Init.Prelude\n\ndef A.a : Nat := 1\n"),
            (
                "ws/Inner/B.lean",
                "import Init.Prelude\n\ndef Inner.b (l : List Nat) : Nat := List.redLength l\n",
            ),
        ],
    );
    let checked = check_in(&ws.path().join("ws"), "Main.lean", &[]);
    assert!(
        !checked.1.contains("import_environment_divergence"),
        "Inner.B must not diverge in its own import closure:\n{}",
        checked.1
    );
    assert_passes("a v4.8.0 workspace importing A and Inner.B", &checked);
}

/// `--imports-prefer-olean` loads an import's artifact instead of its source
/// only when the run's world holds one. `Std/Data/HashMap.lean` is the root
/// package's own source under a name only v4.30.0-rc2's library also holds
/// (Lean 4.8.0's has no `Std`): in the run's Lean 4.8.0 world the source is
/// elaborated, where the Oracle-pinned `Inner/` package alone would take
/// v4.30.0-rc2's artifact. Pinned Lake 4.8.0 builds this workspace from `ws/`
/// (`lake build Main`, exit 0, measured 2026-10-22).
#[test]
fn test_the_prefer_olean_probe_asks_the_runs_world() {
    let Some(lib) = lean_4_8_0() else {
        let refusal = refusal_without_lean_4_8_0("test_the_prefer_olean_probe_asks_the_runs_world");
        assert!(refusal.contains("is not installed"), "{refusal}");
        return;
    };
    assert!(
        oracle_lib().join("Std/Data/HashMap.olean").is_file(),
        "the probe module must be in v4.30.0-rc2's library"
    );
    assert!(
        !lib.join("Std/Data/HashMap.olean").exists(),
        "the probe module must not be in Lean 4.8.0's library"
    );
    let ws = workspace(
        TOOLCHAIN_4_8_0,
        ORACLE,
        true,
        "import Init.Prelude\n\ndef Inner.e : Nat := 1\n",
        "import Inner.B\n\ndef Main.m : Nat := Inner.b\n",
        &[
            (
                "ws/Inner/B.lean",
                "import Std.Data.HashMap\n\ndef Inner.b : Nat := WorldGateLocal.x\n",
            ),
            (
                "ws/Std/Data/HashMap.lean",
                "def WorldGateLocal.x : Nat := 1\n",
            ),
        ],
    );
    let dir = ws.path().join("ws");
    assert_passes(
        "--imports-prefer-olean over a module only the Oracle's library holds",
        &check_args(&dir, &["check", "--imports-prefer-olean", "Main.lean"], &[]),
    );
    // Twin: without the flag the source is elaborated whatever the world.
    assert_passes(
        "the same without --imports-prefer-olean",
        &check_in(&dir, "Main.lean", &[]),
    );
}
