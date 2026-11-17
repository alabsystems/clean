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

/// The implicit source world of `main`, as both production verbs select it.
fn world(main: &Path) -> clean_olean::SourceWorldDecision {
    clean_olean::source_world_for_file(main, None).expect("source world")
}

/// A Lake project whose `Main.lean` has `header` and no artifact directory
/// content: `(main, lib)`.
fn project_with_header(dir: &Path, header: &str) -> (PathBuf, PathBuf) {
    let (main, lib) = lake_project(dir);
    std::fs::write(&main, format!("{header}\ndef plain (n : Nat) : Nat := n\n"))
        .expect("write main");
    (main, lib)
}

#[test]
fn test_permissive_source_setup_ignores_only_absent_source_artifacts() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = project_with_header(dir.path(), "import MissingSourceArtifact");
    let decision = world(&main);
    assert_eq!(
        decision.world(),
        clean_kernel::lean_world::LeanWorld::ORACLE
    );
    assert!(decision.imports().is_ok());
    let setup = super::super::EnvironmentSetup::default();
    assert!(matches!(
        SourceModuleSetup::for_file(setup, &decision, &main),
        Err(super::SourceModuleError::Artifact { .. })
    ));
    let permissive = SourceModuleSetup::for_file_with_import_policy(
        setup,
        &decision,
        &main,
        crate::ImportPolicy::Permissive,
    )
    .expect("the ordinary importer handles an explicitly permissive missing source import");
    assert!(
        !permissive.bootstrap_snapshot,
        "an absent import cannot justify bootstrap semantics"
    );
    assert!(permissive.artifact_imports_permitted);
    assert!(permissive.init.is_none(), "genuine Init stays pending");

    std::fs::write(
        lib.join("MissingSourceArtifact.olean"),
        b"malformed artifact",
    )
    .expect("write malformed artifact");
    assert!(matches!(
        SourceModuleSetup::for_file_with_import_policy(
            setup,
            &decision,
            &main,
            crate::ImportPolicy::Permissive,
        ),
        Err(super::SourceModuleError::Artifact { .. })
    ));
}

#[test]
fn test_permissive_source_setup_requires_existing_artifact_dependencies() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = project_with_header(dir.path(), "import Lib\nimport MissingSourceArtifact");
    write_artifact(&lib, "Lib", &["MissingArtifactDependency"], true);
    let error = match SourceModuleSetup::for_file_with_import_policy(
        super::super::EnvironmentSetup::default(),
        &world(&main),
        &main,
        crate::ImportPolicy::Permissive,
    ) {
        Err(super::SourceModuleError::Artifact { reason, .. }) => reason,
        Err(other) => panic!("expected the recorded dependency's artifact error, got {other}"),
        Ok(_) => panic!("a recorded missing artifact dependency cannot select bootstrap"),
    };
    assert!(error.contains("MissingArtifactDependency"), "{error}");
}

/// A module Clean's hand-written prelude names verbatim, with no artifact
/// anywhere the importer searches, is served from that prelude, which is
/// built over the bootstrap prelude: it selects no world. Selecting genuine
/// Init for it registered the prelude's `HAdd` over Init's
/// ("init_hadd: Duplicate declaration: HAdd").
#[test]
fn test_world_setup_declared_prelude_without_artifact_keeps_bootstrap_route() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, _lib) = project_with_header(dir.path(), "import Mathlib.Data.Real.Basic");
    assert!(
        !source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
        "a declared-prelude import with no artifact is no artifact import"
    );
}

/// The same module with an artifact present is an artifact import.
#[test]
fn test_world_setup_declared_prelude_with_artifact_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = project_with_header(dir.path(), "import Mathlib.Data.Real.Basic");
    let real = lib.join("Mathlib/Data/Real");
    std::fs::create_dir_all(&real).expect("create module dir");
    write_artifact(&real, "Basic", &[], false);
    assert!(
        source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
        "an artifact for a declared-prelude module must select genuine Init"
    );
}

/// A declared-prelude import beside a real artifact import does not hide
/// the artifact import, in either order.
#[test]
fn test_world_setup_declared_prelude_beside_artifact_selects_genuine_init() {
    for header in [
        "import Mathlib.Data.Real.Basic\nimport Lib",
        "import Lib\nimport Mathlib.Data.Real.Basic",
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let (main, lib) = project_with_header(dir.path(), header);
        write_artifact(&lib, "Lib", &[], false);
        assert!(
            source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
            "{header}: the artifact import must select genuine Init"
        );
    }
}

/// A module no prelude names is never served by one: genuine Init, where the
/// importer refuses it by name.
#[test]
fn test_world_setup_undeclared_mathlib_module_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, _lib) = project_with_header(dir.path(), "import Mathlib.Utterly.Fake.Nonsense");
    assert!(
        source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
        "the Mathlib prefix wildcard is not a declared prelude"
    );
}

#[test]
fn test_world_setup_clean_built_closure_keeps_bootstrap_route() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = lake_project(dir.path());
    write_artifact(&lib, "Dep", &[], true);
    write_artifact(&lib, "Lib", &["Dep"], true);
    assert!(
        source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
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
        source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
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
        source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
        "an Init import recorded anywhere in the artifact closure selects genuine Init"
    );
}

#[test]
fn test_world_setup_lean_written_artifact_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, lib) = lake_project(dir.path());
    write_artifact(&lib, "Lib", &[], false);
    assert!(
        source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
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
        source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
        "a Clean-built artifact over a Lean-written one must select genuine Init"
    );
}

#[test]
fn test_world_setup_unresolved_artifact_selects_genuine_init() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (main, _lib) = lake_project(dir.path());
    assert!(
        source_closure_needs_world_setup(&main, &world(&main)).expect("closure is readable"),
        "an import that resolves to no artifact must select genuine Init"
    );
}
