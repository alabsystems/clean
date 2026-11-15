// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Controls for isolated setup and its bootstrap-artifact compatibility rule.
//! A Clean-payload closure retains program bootstrap while keeping independent
//! source-module validation active; genuine/mixed imports keep genuine Init.

use std::path::{Path, PathBuf};

use clean_olean::{CleanPayload, OleanExporter};

use super::{source_closure_needs_world_setup, SourceModuleSetup};

const GIT_HASH: &str = "0123456789abcdef0123456789abcdef01234567";

/// A Lake project root with `Main.lean` importing `Lib`, and its modern
/// artifact directory (`.lake/build/lib/lean`).
fn lake_project(dir: &Path) -> (PathBuf, PathBuf) {
    std::fs::write(dir.join("lakefile.lean"), "import Lake\n").expect("write lakefile");
    let lib = dir.join(".lake/build/lib/lean");
    std::fs::create_dir_all(&lib).expect("create lib dir");
    let main = dir.join("Main.lean");
    std::fs::write(&main, "import Lib\n\ntheorem t : True := trivial\n").expect("write main");
    (main, lib)
}

/// Write `<lib>/<module>.olean` recording `imports`; with a Clean payload
/// when `clean_built`, otherwise in the shape of a Lean-written artifact.
fn write_artifact(lib: &Path, module: &str, imports: &[&str], clean_built: bool) {
    let imports: Vec<(&str, bool)> = imports.iter().map(|name| (*name, false)).collect();
    let bytes = if clean_built {
        OleanExporter::export_with_payload(&imports, &[], &[], GIT_HASH, &CleanPayload::default())
    } else {
        OleanExporter::export_minimal(&imports, &[], &[], GIT_HASH)
    }
    .expect("export artifact");
    assert_eq!(
        clean_olean::decode_clean_payload(&bytes)
            .expect("decode payload")
            .is_some(),
        clean_built,
        "artifact {module} must carry a Clean payload exactly when Clean-built"
    );
    assert_eq!(
        clean_olean::parse_typed_imports(&bytes)
            .expect("artifact imports parse")
            .len(),
        imports.len(),
        "artifact {module} must record its imports"
    );
    std::fs::write(lib.join(format!("{module}.olean")), bytes).expect("write artifact");
}

#[test]
fn test_world_setup_clean_built_closure_keeps_bootstrap_route() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = lake_project(dir.path());
    write_artifact(&lib, "Dep", &[], true);
    write_artifact(&lib, "Lib", &["Dep"], true);
    assert!(
        source_closure_needs_world_setup(&main).expect("closure is readable"),
        "bootstrap compatibility must retain isolated source-module setup"
    );
    let decision = clean_olean::source_world_for_file(&main, None).expect("source world");
    let mut setup = SourceModuleSetup::for_program_file(&decision, &main)
        .expect("complete Clean-format program closure");
    let env = setup
        .initial_environment(&clean_parser::FileHeader::default())
        .expect("matching bootstrap snapshot");
    assert!(env
        .get_const(&clean_kernel::Name::from_string("instHAddNat"))
        .expect("bootstrap instance body remains available")
        .value
        .is_some());
    assert!(
        setup
            .environment()
            .get_const(&clean_kernel::Name::from_string("instHAddNat"))
            .is_none(),
        "citation base remains bare"
    );
    assert!(
        !setup.isolated().init_present,
        "source isolation remains active"
    );
}

#[test]
fn test_world_setup_clean_built_artifact_recording_init_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = lake_project(dir.path());
    write_artifact(&lib, "Lib", &["Init"], true);
    assert!(
        source_closure_needs_world_setup(&main).expect("closure is readable"),
        "a Clean-payload artifact recording an Init import must select genuine Init"
    );
}

#[test]
fn test_world_setup_transitive_init_import_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = lake_project(dir.path());
    write_artifact(&lib, "Dep", &["Init"], true);
    write_artifact(&lib, "Lib", &["Dep"], true);
    assert!(
        source_closure_needs_world_setup(&main).expect("closure is readable"),
        "an Init import recorded anywhere in the artifact closure selects genuine Init"
    );
}

#[test]
fn test_world_setup_lean_written_artifact_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = lake_project(dir.path());
    write_artifact(&lib, "Lib", &[], false);
    assert!(
        source_closure_needs_world_setup(&main).expect("closure is readable"),
        "an artifact without a Clean payload (Lean-written) must select genuine Init"
    );
}

#[test]
fn test_world_setup_lean_written_dependency_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = lake_project(dir.path());
    write_artifact(&lib, "Dep", &[], false);
    write_artifact(&lib, "Lib", &["Dep"], true);
    assert!(
        source_closure_needs_world_setup(&main).expect("closure is readable"),
        "a Clean-built artifact over a Lean-written one must select genuine Init"
    );
}

#[test]
fn test_world_setup_unresolved_artifact_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, _lib) = lake_project(dir.path());
    assert!(
        source_closure_needs_world_setup(&main).expect("closure is readable"),
        "an import that resolves to no artifact must select genuine Init"
    );
}
