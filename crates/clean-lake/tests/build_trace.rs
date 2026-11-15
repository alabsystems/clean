// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake build` reuses a module's artifact only when this builder's
//! build trace for it matches (T7a2, module-trust 2026-09-26).
//!
//! Before: a module was skipped whenever its `.olean` was not older than its
//! source, and counted in `Build OK`. Each test below builds a GENUINE
//! project, then produces the on-disk state a stale cache or a buggy build tool
//! leaves (a leftover artifact next to a source it was not built from, a
//! dependency rebuilt under an unchanged dependent, a rewritten artifact, an
//! artifact with no trace), with the artifact's mtime at or after its
//! source's — exactly the state the timestamp test credited. Each asserts
//! the build now refuses (or rebuilds), and each was measured to pass the old
//! build.

use clean_lake::{BuildContext, BuildResult, Workspace};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

fn write_project(dir: &Path, files: &[(&str, &str)]) {
    fs::create_dir_all(dir).expect("project dir");
    let roots = files
        .iter()
        .map(|(m, _)| format!("\"{m}\""))
        .collect::<Vec<_>>()
        .join(", ");
    fs::write(
        dir.join("lakefile.toml"),
        format!("name = \"tr\"\n\n[[lean_lib]]\nname = \"Tr\"\nroots = [{roots}]\n"),
    )
    .expect("lakefile");
    for (module, source) in files {
        fs::write(dir.join(format!("{module}.lean")), source).expect("source");
    }
}

fn build(dir: &Path) -> BuildResult {
    BuildContext::new(Workspace::load(dir).expect("workspace"))
        .build_all()
        .expect("build runs")
}

fn parts(dir: &Path, module: &str) -> [PathBuf; 3] {
    let lib = dir.join(".lake/build/lib");
    [
        lib.join(format!("{module}.olean")),
        lib.join(format!("{module}.olean.server")),
        lib.join(format!("{module}.olean.private")),
    ]
}

/// Make every artifact file of `module` newer than every source in `dir`, so
/// the timestamp test calls the module up to date.
fn stamp_newer(dir: &Path, module: &str) {
    let later = SystemTime::now() + Duration::from_secs(3600);
    for part in parts(dir, module) {
        fs::File::options()
            .write(true)
            .open(&part)
            .expect("artifact part")
            .set_modified(later)
            .expect("set mtime");
    }
}

fn assert_ok(result: &BuildResult, what: &str) {
    assert!(result.failed.is_empty(), "{what}: {result:?}");
}

/// A source that no longer builds, next to the artifact of an earlier source
/// that did (the leftover a stale cache keeps): the build must come from the
/// source, not from the artifact.
#[test]
fn a_leftover_artifact_is_not_credited_for_a_source_that_does_not_build() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path();
    write_project(dir, &[("M", "theorem M.t : 1 = 1 := rfl\n")]);
    assert_ok(&build(dir), "genuine");
    fs::write(dir.join("M.lean"), "theorem M.t : 1 = 2 := rfl\n").expect("source");
    stamp_newer(dir, "M");

    let result = build(dir);
    assert!(result.skipped.is_empty(), "reused a leftover: {result:?}");
    assert_eq!(result.failed.len(), 1, "{result:?}");
    assert_eq!(result.failed[0].0, "M");
}

/// An artifact with no build trace (what an older builder, or any other
/// tool, leaves) is rebuilt, and the build counts it as built, not reused.
#[test]
fn an_artifact_without_a_trace_is_rebuilt_not_reused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path();
    write_project(dir, &[("M", "theorem M.t : 1 = 1 := rfl\n")]);
    assert_ok(&build(dir), "genuine");
    let trace = parts(dir, "M")[0].with_extension("clean-trace");
    assert!(trace.exists(), "a successful build writes a trace");
    fs::remove_file(&trace).expect("remove trace");
    stamp_newer(dir, "M");

    let result = build(dir);
    assert_ok(&result, "rebuild");
    assert_eq!(result.built, vec!["M".to_string()], "{result:?}");
    assert!(result.skipped.is_empty(), "{result:?}");
    assert!(trace.exists(), "the rebuild writes a trace again");
}

/// Control: an unchanged project is reused module for module (the
/// incremental build still works), and nothing is rebuilt.
#[test]
fn an_unchanged_project_is_reused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path();
    write_project(
        dir,
        &[
            ("Base", "def Base.v : Nat := 2\n"),
            ("Top", "import Base\n\ntheorem Top.t : Base.v = 2 := rfl\n"),
        ],
    );
    assert_ok(&build(dir), "genuine");
    let again = build(dir);
    assert_ok(&again, "again");
    assert!(again.built.is_empty(), "{again:?}");
    let mut skipped = again.skipped.clone();
    skipped.sort();
    assert_eq!(skipped, vec!["Base".to_string(), "Top".to_string()]);
}

/// A dependency is rebuilt with a new value while its dependent's source and
/// artifact stay untouched. The dependent's artifact proved `Base.v = 2` by
/// `rfl` against the OLD value; over the new one that statement is false.
#[test]
fn a_dependent_built_against_an_old_dependency_is_rebuilt() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path();
    write_project(
        dir,
        &[
            ("Base", "def Base.v : Nat := 2\n"),
            ("Top", "import Base\n\ntheorem Top.t : Base.v = 2 := rfl\n"),
        ],
    );
    assert_ok(&build(dir), "genuine");
    fs::write(dir.join("Base.lean"), "def Base.v : Nat := 1\n").expect("source");
    // Base's source is newer than its artifact (it rebuilds under either
    // rule); Top's artifact stays newer than Top's source.
    let later = SystemTime::now() + Duration::from_secs(7200);
    fs::File::options()
        .write(true)
        .open(dir.join("Base.lean"))
        .expect("src")
        .set_modified(later)
        .expect("mtime");
    for part in parts(dir, "Top") {
        fs::File::options()
            .write(true)
            .open(&part)
            .expect("part")
            .set_modified(later + Duration::from_secs(60))
            .expect("mtime");
    }

    let result = build(dir);
    assert!(
        !result.skipped.contains(&"Top".to_string()),
        "Top reused over a rebuilt dependency: {result:?}"
    );
    assert_eq!(result.failed.len(), 1, "{result:?}");
    assert_eq!(result.failed[0].0, "Top");
}

/// A dependency's artifact rewritten after its build (here: the artifact of
/// an earlier, different source copied over it) while its own source stays
/// the same. The dependent must not be built against the rewritten value: the
/// dependency is rebuilt from its source first.
#[test]
fn a_rewritten_dependency_artifact_is_rebuilt_from_source() {
    let tmp = tempfile::tempdir().expect("tmp");
    let donor = tmp.path().join("donor");
    write_project(&donor, &[("Base", "def Base.v : Nat := 2\n")]);
    assert_ok(&build(&donor), "donor");

    let dir = tmp.path().join("proj");
    write_project(
        &dir,
        &[
            ("Base", "def Base.v : Nat := 1\n"),
            ("Top", "import Base\n\ntheorem Top.t : Base.v = 1 := rfl\n"),
        ],
    );
    assert_ok(&build(&dir), "genuine");
    // The rewrite: Base's artifact now says `v := 2`, Top's source says
    // `Base.v = 2`.
    for (from, to) in parts(&donor, "Base").iter().zip(parts(&dir, "Base")) {
        fs::copy(from, to).expect("copy artifact");
    }
    stamp_newer(&dir, "Base");
    fs::write(
        dir.join("Top.lean"),
        "import Base\n\ntheorem Top.t : Base.v = 2 := rfl\n",
    )
    .expect("source");

    let result = build(&dir);
    assert!(
        result.built.contains(&"Base".to_string()),
        "Base reused although its artifact is not what this build wrote: {result:?}"
    );
    assert_eq!(result.failed.len(), 1, "{result:?}");
    assert_eq!(result.failed[0].0, "Top");
}

/// Control for the test above: with the same rewrite but a dependent that is
/// true of the SOURCE value, the project builds (so the refusal above is the
/// false statement, not the fixture).
#[test]
fn a_rewritten_dependency_artifact_is_replaced_and_a_true_dependent_builds() {
    let tmp = tempfile::tempdir().expect("tmp");
    let donor = tmp.path().join("donor");
    write_project(&donor, &[("Base", "def Base.v : Nat := 2\n")]);
    assert_ok(&build(&donor), "donor");
    let dir = tmp.path().join("proj");
    write_project(
        &dir,
        &[
            ("Base", "def Base.v : Nat := 1\n"),
            ("Top", "import Base\n\ntheorem Top.t : Base.v = 1 := rfl\n"),
        ],
    );
    assert_ok(&build(&dir), "genuine");
    let genuine = fs::read(&parts(&dir, "Base")[0]).expect("genuine artifact");
    for (from, to) in parts(&donor, "Base").iter().zip(parts(&dir, "Base")) {
        fs::copy(from, to).expect("copy artifact");
    }
    stamp_newer(&dir, "Base");

    let result = build(&dir);
    assert_ok(&result, "rebuild");
    assert!(result.built.contains(&"Base".to_string()), "{result:?}");
    assert_eq!(
        fs::read(&parts(&dir, "Base")[0]).expect("artifact"),
        genuine,
        "the rebuilt artifact is the source's own"
    );
}

/// A trace written by ANOTHER build of this same crate version is not this
/// builder's word (round-27 verification of `d0789d05f`): the identity was
/// the constant `.olean` format stamp plus the crate version, so a trace a
/// weaker or buggier build of `clean-lake 0.9.0` wrote over a sorry artifact
/// would have been reused by a fixed one — T7a2 one level up. The identity
/// now carries the running executable's digest; a trace naming only the old
/// constant identity rebuilds.
#[test]
fn a_trace_from_another_build_of_the_same_version_is_not_reused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path();
    write_project(dir, &[("M", "theorem M.t : 1 = 1 := rfl\n")]);
    assert_ok(&build(dir), "genuine");
    let trace = clean_lake::build_trace::trace_path(&parts(dir, "M")[0]);
    let mut recorded: serde_json::Value =
        serde_json::from_slice(&fs::read(&trace).expect("trace")).expect("json");
    let own = recorded["builder"].as_str().expect("builder").to_string();
    let version_only = format!(
        "{}+clean-lake-{}",
        clean_lake::CLEAN_OLEAN_GIT_HASH,
        env!("CARGO_PKG_VERSION")
    );
    assert!(
        own.starts_with(&version_only) && own != version_only,
        "the identity names more than the version: {own}"
    );
    // Control: this builder's own trace is reused.
    let again = build(dir);
    assert_eq!(again.skipped, vec!["M".to_string()], "{again:?}");
    recorded["builder"] = version_only.into();
    fs::write(&trace, serde_json::to_vec(&recorded).expect("json")).expect("write");
    let other = build(dir);
    assert_ok(&other, "rebuild");
    assert_eq!(other.built, vec!["M".to_string()], "{other:?}");
}
