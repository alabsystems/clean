// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check` against an imported artifact that is not the build of the
//! source next to it (module-trust round 27, `import_binding.rs`).
//!
//! Measured on `d0789d05f`: with an artifact whose `def K1Lib.v : Nat := 0`
//! was rewritten to `:= 1` (well-typed, so the imported-cone gate re-admits
//! it), `theorem : K1Lib.v = 1 := rfl` printed `1 passed`, exit 0, although
//! the library's source — in the same Lake workspace as the artifact — says
//! `0`. The same held for an artifact left behind after its source was edited.
//!
//! Layout: a consumer project `q` whose Lake dependency `.lake/packages/vlib`
//! (a package name source resolution does not map to `K1Lib`, so the import
//! can only resolve to the artifact) is the library's own workspace, built in
//! place by `clean lake build` with `buildDir = "build"` (the `build/lib`
//! layout the consumer's search paths discover).

use crate::check_import_gate::tests::{build_lib, consumer, payload, CITE_TRUE, LIB};
use crate::cmd_core::{collect_check_outcome, FileCheckOutcome};
use clean_kernel::cli::{PreludeMode, DEFAULT_DECL_BUDGET};
use clean_kernel::Name;
use clean_lake::{BuildContext, Workspace};
use clean_olean::payload::{encode_clean_payload, CleanPayload};
use std::fs;
use std::path::{Path, PathBuf};

pub(crate) const DEF_LIB: &str = "def K1Lib.v : Nat := 0\n";
/// FALSE in the library's source.
pub(crate) const CITE_V1: &str = "import K1Lib\n\ntheorem k1_v1 : K1Lib.v = 1 := rfl\n";
/// TRUE in the library's source.
pub(crate) const CITE_V0: &str = "import K1Lib\n\ntheorem k1_v0 : K1Lib.v = 0 := rfl\n";

/// The consumer project `root/tag` citing `cite`, with the library
/// `lib_source` as its Lake dependency, built in place. Returns the citing
/// file and the library's artifact.
pub(crate) fn sourced_dependency(
    root: &Path,
    tag: &str,
    lib_source: &str,
    cite: &str,
) -> (PathBuf, PathBuf) {
    let dir = root.join(tag);
    let pkg = dir.join(".lake/packages/vlib");
    fs::create_dir_all(&pkg).expect("package dir");
    fs::write(
        dir.join("lakefile.toml"),
        "name = \"q\"\n\n[[lean_lib]]\nname = \"Q\"\nroots = [\"Main\"]\n",
    )
    .expect("consumer lakefile");
    fs::write(
        pkg.join("lakefile.toml"),
        "name = \"vlib\"\nbuildDir = \"build\"\n\n[[lean_lib]]\nname = \"V\"\nroots = [\"K1Lib\"]\n",
    )
    .expect("library lakefile");
    fs::write(pkg.join("K1Lib.lean"), lib_source).expect("library source");
    // See `check_import_gate::tests::build_lib`: fixture builds bump the
    // process-wide trust counters a concurrent check/export reads.
    let _serialised = crate::cmd_core::check_file_lock();
    let built = BuildContext::new(Workspace::load(&pkg).expect("ws"))
        .build_all()
        .expect("build");
    assert!(built.failed.is_empty(), "{tag}: {built:?}");
    let main = dir.join("Main.lean");
    fs::write(&main, cite).expect("citing file");
    (main, pkg.join("build/lib/K1Lib.olean"))
}

/// Replace `artifact`'s payload by `edit` of it, in place (companions kept:
/// the payload is the file's trailer).
pub(crate) fn rewrite_payload(artifact: &Path, edit: impl FnOnce(&mut CleanPayload)) {
    let (bytes, mut p) = payload(artifact);
    edit(&mut p);
    let len = u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().expect("u64")) as usize;
    let trailer = len + clean_olean::payload::CLEAN_PAYLOAD_MAGIC.len() + 4 + 8;
    let mut out = bytes[..bytes.len() - trailer].to_vec();
    out.extend(encode_clean_payload(&p).expect("encode"));
    fs::write(artifact, out).expect("rewrite artifact");
}

/// `K1Lib.v`'s value taken from a genuine build of `def K1Lib.v : Nat := 1`:
/// a well-typed value swap.
pub(crate) fn value_one(root: &Path) -> clean_kernel::Expr {
    let donor = build_lib(root, "donor", "def K1Lib.v : Nat := 1\n");
    let n = Name::from_string("K1Lib.v");
    payload(&donor)
        .1
        .constants
        .into_iter()
        .find(|c| c.name == n)
        .and_then(|c| c.value)
        .expect("donor value")
}

pub(crate) fn set_v(p: &mut CleanPayload, value: clean_kernel::Expr) {
    let n = Name::from_string("K1Lib.v");
    p.constants
        .iter_mut()
        .find(|c| c.name == n)
        .expect("K1Lib.v in the payload")
        .value = Some(value);
}

fn check(path: &Path) -> FileCheckOutcome {
    collect_check_outcome(
        path,
        false,
        false,
        PreludeMode::Builtin,
        true,
        false,
        clean_elab::ImportPolicy::default(),
        DEFAULT_DECL_BUDGET,
        clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
        &[],
    )
    .expect("the check pipeline itself runs")
    .0
}

fn assert_not_checked_against(outcome: &FileCheckOutcome, why: &str, what: &str) {
    assert_eq!(outcome.success_count, 0, "{what}: {outcome:#?}");
    assert!(
        outcome
            .errors
            .iter()
            .any(|e| e.contains("is not the build of its source") && e.contains(why)),
        "{what}: {outcome:#?}"
    );
}

#[test]
fn a_bound_dependency_artifact_is_credited_with_no_disclosure() {
    let tmp = tempfile::tempdir().expect("tmp");
    let (main, _) = sourced_dependency(tmp.path(), "q", DEF_LIB, CITE_V0);
    let outcome = check(&main);
    assert_eq!(outcome.success_count, 1, "{outcome:#?}");
    assert!(outcome.errors.is_empty(), "{outcome:#?}");
    assert!(
        outcome.artifact_imports.is_empty(),
        "an artifact bound to its source is not a disclosure: {outcome:#?}"
    );
    // Control: the false statement is refused over the genuine artifact.
    let (main, _) = sourced_dependency(tmp.path(), "q1", DEF_LIB, CITE_V1);
    let outcome = check(&main);
    assert_eq!(outcome.success_count, 0, "{outcome:#?}");
}

#[test]
fn a_well_typed_value_swap_in_a_sourced_artifact_is_not_checked_against() {
    let tmp = tempfile::tempdir().expect("tmp");
    let one = value_one(tmp.path());
    let (main, artifact) = sourced_dependency(tmp.path(), "q", DEF_LIB, CITE_V1);
    rewrite_payload(&artifact, |p| set_v(p, one));
    let outcome = check(&main);
    assert_not_checked_against(
        &outcome,
        "artifact differs from what this builder wrote",
        "K1Lib.v = 1 over a rewritten value",
    );
}

#[test]
fn an_artifact_left_behind_after_its_source_changed_is_not_checked_against() {
    let tmp = tempfile::tempdir().expect("tmp");
    let (main, artifact) = sourced_dependency(tmp.path(), "q", DEF_LIB, CITE_V0);
    // The source now says `1`; the artifact still says `0`, so `K1Lib.v = 0`
    // is true of the artifact and false of the source.
    let source = artifact
        .parent()
        .and_then(Path::parent)
        .and_then(Path::parent)
        .expect("package root")
        .join("K1Lib.lean");
    fs::write(&source, "def K1Lib.v : Nat := 1\n").expect("edit source");
    let outcome = check(&main);
    assert_not_checked_against(&outcome, "source changed", "a stale artifact");
}

#[test]
fn an_artifact_with_no_source_is_credited_and_disclosed() {
    // No source anywhere near the artifact: nothing to compare it with. The
    // verdict stands, and says what it rests on.
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let main = consumer(tmp.path(), "use", &lib, CITE_TRUE, |_| {});
    let outcome = check(&main);
    assert_eq!(outcome.success_count, 1, "{outcome:#?}");
    assert!(
        outcome
            .artifact_imports
            .iter()
            .any(|row| row.starts_with("K1Lib: ") && row.contains("K1Lib.olean")),
        "{outcome:#?}"
    );
}

// ── a failed import: nothing is checked against the part that loaded ──────────

const STRUCT_LIB: &str = "structure K1Lib.P where\n  x : Nat\n  y : Nat\n";
/// FALSE in the library's source.
const CITE_PX1: &str = "import K1Lib\n\ntheorem k1_px : (K1Lib.P.mk 0 1).x = 1 := rfl\n";

fn check_with(path: &Path, policy: clean_elab::ImportPolicy) -> FileCheckOutcome {
    collect_check_outcome(
        path,
        false,
        false,
        PreludeMode::Builtin,
        true,
        false,
        policy,
        DEFAULT_DECL_BUDGET,
        clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
        &[],
    )
    .expect("the check pipeline itself runs")
    .0
}

/// `K1Lib.P.x`'s value replaced by `K1Lib.P.y`'s (well-typed), the field
/// table left honest: the loader refuses the import as inconsistent. Measured
/// on the first round-27 build, before this rule: the file went on being
/// checked against the half-loaded module and `k1_px` was counted `passed`
/// (`1 passed, 1 failed`, and under `--permissive-imports` `1 passed`, exit 0).
#[test]
fn nothing_is_checked_past_an_import_of_an_inconsistent_artifact() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", STRUCT_LIB);
    // Control: over the genuine artifact the false statement is refused by
    // elaboration and the import loads.
    let main = consumer(tmp.path(), "c", &lib, CITE_PX1, |_| {});
    let outcome = check_with(&main, clean_elab::ImportPolicy::FailClosed);
    assert_eq!(outcome.success_count, 0, "{outcome:#?}");
    assert!(
        !outcome
            .errors
            .iter()
            .any(|e| e.contains("inconsistent artifact")),
        "{outcome:#?}"
    );
    for (tag, policy) in [
        ("fc", clean_elab::ImportPolicy::FailClosed),
        ("perm", clean_elab::ImportPolicy::Permissive),
    ] {
        let main = consumer(tmp.path(), tag, &lib, CITE_PX1, |p| {
            let y = Name::from_string("K1Lib.P.y");
            let x = Name::from_string("K1Lib.P.x");
            let value = p
                .constants
                .iter()
                .find(|c| c.name == y)
                .and_then(|c| c.value.clone())
                .expect("P.y value");
            p.constants
                .iter_mut()
                .find(|c| c.name == x)
                .expect("P.x")
                .value = Some(value);
        });
        let outcome = check_with(&main, policy);
        assert_eq!(outcome.success_count, 0, "{tag}: {outcome:#?}");
        assert!(
            outcome
                .errors
                .iter()
                .any(|e| e.contains("inconsistent artifact")),
            "{tag}: {outcome:#?}"
        );
        assert!(
            outcome
                .errors
                .iter()
                .any(|e| e.contains("not checked — an import failed")),
            "{tag}: {outcome:#?}"
        );
    }
}

// ── a toolchain module is identified by its digest, not by a file name ───────

/// Put an EMPTY `Init/Prelude.olean` (and `Init/Core.olean`) beside `artifact`
/// — the marker that used to make its whole search root "a toolchain root".
fn plant_toolchain_marker(artifact: &Path) {
    let init = artifact.parent().expect("lib root").join("Init");
    fs::create_dir_all(&init).expect("Init dir");
    fs::write(init.join("Prelude.olean"), b"").expect("empty Prelude.olean");
    fs::write(init.join("Core.olean"), b"").expect("empty Core.olean");
}

/// Module-trust round 28, measured on `e3f696689`: with the marker planted
/// beside a rewritten `K1Lib.olean` in its own workspace, `K1Lib.v = 1`
/// passed `clean check` with `artifact_imports: []` (and `export-cert` wrote a
/// bundle `clean kernel cert verify` reported ALL PASSED).
#[test]
fn an_empty_prelude_beside_a_rewritten_artifact_does_not_exempt_it() {
    let tmp = tempfile::tempdir().expect("tmp");
    let one = value_one(tmp.path());
    let (main, artifact) = sourced_dependency(tmp.path(), "q", DEF_LIB, CITE_V1);
    rewrite_payload(&artifact, |p| set_v(p, one));
    plant_toolchain_marker(&artifact);
    let outcome = check(&main);
    assert_not_checked_against(
        &outcome,
        "artifact differs from what this builder wrote",
        "K1Lib.v = 1 over a rewritten value, marker planted",
    );
}

#[test]
fn an_empty_prelude_beside_a_stale_artifact_does_not_exempt_it() {
    let tmp = tempfile::tempdir().expect("tmp");
    let (main, artifact) = sourced_dependency(tmp.path(), "q", DEF_LIB, CITE_V0);
    let source = artifact
        .parent()
        .and_then(Path::parent)
        .and_then(Path::parent)
        .expect("package root")
        .join("K1Lib.lean");
    fs::write(&source, "def K1Lib.v : Nat := 1\n").expect("edit source");
    plant_toolchain_marker(&artifact);
    let outcome = check(&main);
    assert_not_checked_against(
        &outcome,
        "source changed",
        "a stale artifact, marker planted",
    );
}

#[test]
fn an_empty_prelude_beside_an_unsourced_artifact_does_not_hide_its_disclosure() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let main = consumer(tmp.path(), "use", &lib, CITE_TRUE, |_| {});
    plant_toolchain_marker(
        &main
            .parent()
            .expect("consumer root")
            .join(".lake/build/lib/lean/K1Lib.olean"),
    );
    let outcome = check(&main);
    assert_eq!(outcome.success_count, 1, "{outcome:#?}");
    assert!(
        outcome
            .artifact_imports
            .iter()
            .any(|row| row.starts_with("K1Lib: ") && row.contains("K1Lib.olean")),
        "{outcome:#?}"
    );
}
