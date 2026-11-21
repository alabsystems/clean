// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::lean_world::LeanWorld;
use clean_olean::{CleanPayload, OleanExporter};

fn project() -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("temporary Lake project");
    std::fs::write(dir.path().join("lakefile.toml"), "name = \"format_test\"\n")
        .expect("Lake root");
    std::fs::create_dir_all(dir.path().join(".lake/build/lib")).expect("artifact directory");
    std::fs::write(
        dir.path().join("Main.lean"),
        "import Library\ndef value : Nat := 1\n",
    )
    .expect("entry source");
    dir
}

fn artifact(dir: &Path, module: &str, imports: &[(&str, bool)], payload: bool) -> PathBuf {
    let bytes = if payload {
        OleanExporter::export_with_payload(
            imports,
            &[],
            &[],
            "0000000000000000000000000000000000000000",
            &CleanPayload::default(),
        )
    } else {
        OleanExporter::export_minimal(
            imports,
            &[],
            &[],
            "0000000000000000000000000000000000000000",
        )
    }
    .expect("valid format fixture");
    let path = dir.join(format!(".lake/build/lib/{module}.olean"));
    std::fs::write(&path, bytes).expect("artifact");
    path
}

fn choice(path: &Path) -> clean_olean::SourceWorldDecision {
    clean_olean::source_world_for_file(path, None).expect("default oracle source world")
}

#[test]
fn clean_format_closure_keeps_bootstrap_bodies_and_source_isolation() {
    let dir = project();
    let library = artifact(dir.path(), "Library", &[("Dependency", false)], true);
    artifact(dir.path(), "Dependency", &[], true);
    let mut previous = std::fs::read(&library).expect("base fixture");
    for suffix in ["olean.server", "olean.private"] {
        let bytes = OleanExporter::export_with_payload_after(
            &previous,
            &[("Dependency", false)],
            &[],
            &[],
            "0000000000000000000000000000000000000000",
            &CleanPayload::default(),
        )
        .expect("canonical companion placement");
        std::fs::write(library.with_extension(suffix), &bytes).expect("valid empty companion");
        previous = bytes;
    }
    let path = dir.path().join("Main.lean");
    assert!(source_closure_needs_world_setup(&path, &choice(&path)).expect("source walk"));
    assert!(clean_format_source_closure(&path, &choice(&path)).expect("strict format walk"));
    let mut setup = SourceModuleSetup::for_file(EnvironmentSetup::default(), &choice(&path), &path)
        .expect("Clean-format setup");
    let env = setup
        .initial_environment(&FileHeader::default())
        .expect("bootstrap snapshot");
    let instance = env
        .get_const(&Name::from_string("instHAddNat"))
        .expect("checked seed body");
    assert!(instance.value.is_some());
    assert!(
        setup
            .environment()
            .get_const(&Name::from_string("instHAddNat"))
            .is_none(),
        "the citation base remains bare"
    );
    assert!(
        !setup.isolated().init_present,
        "imported source still requires its own snapshot"
    );
}

#[test]
fn payloadless_transitive_dependency_requires_genuine_init() {
    let dir = project();
    artifact(dir.path(), "Library", &[("Dependency", false)], true);
    artifact(dir.path(), "Dependency", &[], false);
    let path = dir.path().join("Main.lean");
    assert!(!clean_format_source_closure(&path, &choice(&path)).expect("mixed format walk"));
    let setup = SourceModuleSetup::for_file(EnvironmentSetup::default(), &choice(&path), &path)
        .expect("genuine setup remains deferred");
    assert!(setup.init.is_none());
    assert!(!setup.bootstrap_snapshot);
}

#[test]
fn genuine_lean_artifact_never_selects_bootstrap() {
    let dir = project();
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Minimal.olean");
    std::fs::copy(fixture, dir.path().join(".lake/build/lib/Library.olean"))
        .expect("real Lean-format artifact");
    let path = dir.path().join("Main.lean");
    assert!(!clean_format_source_closure(&path, &choice(&path)).expect("genuine format"));
    let artifact = dir.path().join(".lake/build/lib/Library.olean");
    let mut bytes = std::fs::read(&artifact).expect("genuine fixture");
    bytes.extend(clean_olean::encode_clean_payload(&CleanPayload::default()).expect("payload"));
    std::fs::write(artifact, bytes).expect("foreign trailer fixture");
    assert!(
        clean_format_source_closure(&path, &choice(&path)).is_err(),
        "a forged payload on genuine Lean format must refuse"
    );
}

#[cfg(unix)]
#[test]
fn one_artifact_in_two_search_contexts_checks_both_transitive_resolutions() {
    let dir = project();
    std::fs::write(
        dir.path().join("Main.lean"),
        "import A.Left\nimport B.Right\n",
    )
    .expect("two source contexts");
    let shared = artifact(dir.path(), "Shared", &[("Dependency", false)], true);
    for (nested, module, clean) in [("A", "Left", true), ("B", "Right", false)] {
        let root = dir.path().join(nested);
        std::fs::create_dir_all(root.join(".lake/build/lib")).expect("nested artifact dir");
        std::fs::write(root.join("lakefile.toml"), "name = \"nested\"\n").expect("nested root");
        std::fs::write(root.join(format!("{module}.lean")), "import Shared\n")
            .expect("nested source");
        std::os::unix::fs::symlink(&shared, root.join(".lake/build/lib/Shared.olean"))
            .expect("same canonical artifact, different resolution contexts");
        artifact(&root, "Dependency", &[], clean);
    }
    let path = dir.path().join("Main.lean");
    assert!(!clean_format_source_closure(&path, &choice(&path)).expect("both contexts checked"));
}

#[cfg(unix)]
#[test]
fn source_aliases_preserve_lexical_parent_resolution_contexts() {
    let dir = project();
    artifact(dir.path(), "Library", &[], true);
    let shared = dir.path().join("Common.lean");
    std::fs::write(&shared, "import Dependency\n").expect("shared source");
    std::fs::write(
        dir.path().join("Main.lean"),
        "import B.Right\nimport A.Left\n",
    )
    .expect("source aliases");
    for (nested, module, body) in [
        ("A", "Left", "def a : Nat := 1\n"),
        ("B", "Right", "prelude\n"),
    ] {
        let parent = dir.path().join(nested);
        std::fs::create_dir_all(&parent).expect("alias parent");
        std::os::unix::fs::symlink(&shared, parent.join(format!("{module}.lean")))
            .expect("same canonical source");
        std::fs::write(parent.join("Dependency.lean"), body).expect("context-specific source");
    }
    let path = dir.path().join("Main.lean");
    assert!(source_closure_needs_world_setup(&path, &choice(&path))
        .expect("outer selector checks both contexts"));
    let setup = SourceModuleSetup::for_file(EnvironmentSetup::default(), &choice(&path), &path)
        .expect("prelude requires genuine setup");
    assert!(!setup.bootstrap_snapshot);
    std::fs::write(&shared, "import Dependency\nimport Library\n")
        .expect("add a valid artifact to the clean source context");
    assert!(!clean_format_source_closure(&path, &choice(&path)).expect("both source contexts"));
}

#[test]
fn missing_malformed_and_inconsistent_companions_never_select_bootstrap() {
    let dir = project();
    let path = dir.path().join("Main.lean");
    assert!(clean_format_source_closure(&path, &choice(&path)).is_err());
    let library = artifact(dir.path(), "Library", &[], true);
    std::fs::write(library.with_extension("olean.private"), b"malformed")
        .expect("malformed companion");
    assert!(clean_format_source_closure(&path, &choice(&path)).is_err());
    std::fs::remove_file(library.with_extension("olean.private"))
        .expect("remove malformed fixture");
    let mut bytes = std::fs::read(&library).expect("fixture bytes");
    let version = bytes.len() - 12;
    bytes[version..version + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    std::fs::write(&library, bytes).expect("unsupported payload version");
    assert!(clean_format_source_closure(&path, &choice(&path)).is_err());
}

#[test]
fn source_prelude_and_recent_world_never_select_bootstrap_snapshot() {
    let dir = project();
    artifact(dir.path(), "Library", &[], true);
    let path = dir.path().join("Main.lean");
    std::fs::write(dir.path().join("Library.lean"), "prelude\n")
        .expect("source takes precedence over artifact");
    assert!(!clean_format_source_closure(&path, &choice(&path)).expect("prelude source"));
    std::fs::remove_file(dir.path().join("Library.lean")).expect("restore artifact-only closure");
    for world in [
        LeanWorld::Lean435,
        LeanWorld::Lean436Rc2,
        LeanWorld::Lean436,
    ] {
        match clean_olean::source_world_for_file(&path, Some(world)) {
            Ok(decision) => {
                let setup =
                    SourceModuleSetup::for_file(EnvironmentSetup::default(), &decision, &path)
                        .expect("recent world setup");
                assert!(!setup.bootstrap_snapshot);
                assert!(
                    setup.init.is_none(),
                    "genuine Init remains the required deferred snapshot"
                );
            }
            Err(clean_olean::SourceWorldRefusal::Explicit {
                world: refused,
                reason,
            }) => {
                assert_eq!(refused, world);
                assert!(
                    !reason.is_empty(),
                    "unavailable SDK remains a named refusal"
                );
            }
            Err(error) => panic!("unexpected world decision: {error}"),
        }
    }
}

#[test]
fn quoted_parent_source_backedge_is_a_named_cycle_in_both_walkers() {
    // No Lake root: source lookup must retain the lexical parent rather than
    // resetting to a canonical project root at each import.
    let dir = tempfile::tempdir().expect("bare source directory");
    std::fs::create_dir(dir.path().join("Sub")).expect("real quoted-parent route");
    std::fs::write(dir.path().join("lean-toolchain"), "clean\n")
        .expect("checkout-pin source world");
    let path = dir.path().join("Main.lean");
    std::fs::write(&path, "import Sub.«..».Main\n").expect("real-file source cycle");
    let canonical = std::fs::canonicalize(&path).expect("canonical cycle fixture");
    let decision = choice(&path);
    decision
        .imports()
        .expect("fixture imports remain permitted");
    for result in [
        source_closure_needs_world_setup(&path, &decision),
        clean_format_source_closure(&path, &decision),
    ] {
        match result {
            Err(SourceModuleError::Header { path, reason }) => {
                assert_eq!(reason, "source import cycle detected");
                assert_eq!(
                    std::fs::canonicalize(path).expect("real backedge source"),
                    canonical,
                );
            }
            result => panic!("expected named source cycle, got {result:?}"),
        }
    }
}

#[test]
fn program_bootstrap_matches_producer_without_checker_extensions() {
    let dir = project();
    artifact(dir.path(), "Library", &[], true);
    let path = dir.path().join("Main.lean");
    let decision = choice(&path);
    let mut setup =
        SourceModuleSetup::for_program_file(&decision, &path).expect("program bootstrap setup");
    let actual = setup
        .initial_environment(&FileHeader::default())
        .expect("program snapshot");

    // Exact construction used by native compile and the Clean Lake producer.
    let mut producer = Environment::with_prelude();
    producer.init_io_ops().expect("producer IO operations");
    crate::prepare_session_environment(&mut producer);
    let actual_names: std::collections::BTreeSet<_> = actual
        .constants()
        .map(|constant| constant.name.clone())
        .collect();
    let producer_names: std::collections::BTreeSet<_> = producer
        .constants()
        .map(|constant| constant.name.clone())
        .collect();
    assert_eq!(actual_names, producer_names, "program declared vocabulary");
    for expected in producer.constants() {
        let found = actual
            .get_const(&expected.name)
            .expect("same declared names");
        assert_eq!(found.level_params, expected.level_params);
        assert_eq!(found.type_, expected.type_);
        assert_eq!(found.value, expected.value);
        assert_eq!(found.kind, expected.kind);
        assert_eq!(found.is_reducible, expected.is_reducible);
        assert_eq!(
            actual.get_constant_origin(&expected.name),
            producer.get_constant_origin(&expected.name),
        );
        assert_eq!(
            actual.is_instance(&expected.name),
            producer.is_instance(&expected.name)
        );
        assert_eq!(
            actual.instance_seq(&expected.name),
            producer.instance_seq(&expected.name)
        );
    }
    for name in ["instPureList", "instBindList", "instMonadList", "ULift"] {
        assert!(
            actual.get_const(&Name::from_string(name)).is_none(),
            "native program must not acquire checker extension {name}"
        );
    }
    assert!(actual.get_const(&Name::from_string("IO.println")).is_some());
    assert_eq!(
        actual.lean4_core_strict_monads(),
        producer.lean4_core_strict_monads()
    );
    assert_eq!(
        clean_olean::environment_world(&actual),
        decision.declared_world()
    );
    assert!(
        setup
            .environment()
            .get_const(&Name::from_string("instHAddNat"))
            .is_none(),
        "program citation base remains bare"
    );
    assert!(
        !setup.isolated().init_present,
        "program source isolation remains active"
    );
}

#[test]
fn checker_bootstrap_keeps_its_explicit_prelude_policy() {
    let dir = project();
    artifact(dir.path(), "Library", &[], true);
    let path = dir.path().join("Main.lean");
    let decision = choice(&path);
    for (prelude, has_list, strict) in [
        (crate::module_driver::PreludeFlavor::Builtin, true, false),
        (crate::module_driver::PreludeFlavor::Lean4Core, false, true),
    ] {
        let checker = EnvironmentSetup {
            prelude,
            imports: crate::module_driver::ImportArtifacts::Source,
        };
        let mut setup = SourceModuleSetup::for_file(checker, &decision, &path)
            .expect("checker bootstrap setup");
        let env = setup
            .initial_environment(&FileHeader::default())
            .expect("checker snapshot");
        for name in ["instPureList", "instBindList", "instMonadList"] {
            assert_eq!(
                env.get_const(&Name::from_string(name)).is_some(),
                has_list,
                "checker prelude controls {name}"
            );
        }
        assert!(env.get_const(&Name::from_string("ULift")).is_some());
        assert_eq!(env.lean4_core_strict_monads(), strict);
        assert!(setup
            .environment()
            .get_const(&Name::from_string("ULift"))
            .is_none());
    }
}

#[test]
fn clean_format_bootstrap_refuses_genuine_direct_replacement_at_actual_load() {
    for program in [false, true] {
        let dir = project();
        let library = artifact(dir.path(), "Library", &[], true);
        let path = dir.path().join("Main.lean");
        let decision = choice(&path);
        let mut setup = if program {
            SourceModuleSetup::for_program_file(&decision, &path)
        } else {
            SourceModuleSetup::for_file(EnvironmentSetup::default(), &decision, &path)
        }
        .expect("all-Clean bootstrap selected before replacement");
        assert!(setup.bootstrap_snapshot);
        let mut env = setup
            .initial_environment(&FileHeader::default())
            .expect("snapshot");
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean/v4.13.0/custom/Minimal.olean");
        std::fs::copy(fixture, &library).expect("genuine artifact replaces classified Clean bytes");
        let before = env.generation();
        let error = clean_olean::load_module_with_deps(
            &mut env,
            "Library",
            &[library.parent().expect("artifact parent").to_path_buf()],
        )
        .expect_err("classification cannot authorize later genuine content");
        assert!(error.is_inconsistent_artifact());
        assert!(
            matches!(error, clean_olean::ImportError::CleanPayloadRequired { module } if module == "Library")
        );
        assert_eq!(env.generation(), before);
        assert!(env.get_const(&Name::from_string("identity")).is_none());
    }
}

#[test]
fn clean_format_bootstrap_refuses_genuine_transitive_replacement_at_actual_load() {
    let dir = project();
    artifact(dir.path(), "Library", &[("Dependency", false)], true);
    let dependency = artifact(dir.path(), "Dependency", &[], true);
    let path = dir.path().join("Main.lean");
    let mut setup = SourceModuleSetup::for_program_file(&choice(&path), &path)
        .expect("all-Clean transitive closure selected");
    assert!(setup.bootstrap_snapshot);
    let mut env = setup
        .initial_environment(&FileHeader::default())
        .expect("snapshot");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Minimal.olean");
    std::fs::copy(fixture, &dependency).expect("genuine dependency after classification");
    let before = env.generation();
    let error = clean_olean::load_module_with_deps(
        &mut env,
        "Library",
        &[dependency.parent().expect("artifact parent").to_path_buf()],
    )
    .expect_err("transitive load must enforce the selected profile");
    assert!(error.is_inconsistent_artifact());
    assert!(
        matches!(error, clean_olean::ImportError::CleanPayloadRequired { module } if module == "Dependency")
    );
    assert_eq!(env.generation(), before);
    assert!(env.get_const(&Name::from_string("identity")).is_none());
}
