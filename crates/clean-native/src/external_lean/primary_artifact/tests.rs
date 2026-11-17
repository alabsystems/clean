//! Actual SDK captures exercise the public logical-only route. Private
//! corruption arms are labeled separately and grant no source/model rights.

use super::*;
use crate::external_lean::{ExternalLeanInput, ExternalLeanInspection};
use clean_kernel::{ExprKind, Literal};
use std::collections::BTreeSet;
use std::sync::Arc;

fn oracle_name(value: &serde_json::Value) -> Name {
    value
        .as_array()
        .unwrap()
        .iter()
        .fold(Name::anon(), |name, part| {
            match part["kind"].as_str().unwrap() {
                "str" => name.str(part["value"].as_str().unwrap()),
                "num" => name.num(part["value"].as_u64().unwrap()),
                other => panic!("actual SDK oracle Name component {other}"),
            }
        })
}

fn compare_actual_sdk_roster(label: &str, view: &PrimaryArtifactView<'_>) {
    // Use the capture's actual SDK and raw ModuleData fields, rather than a
    // Clean parse or a snapshot of the loaded Environment. The historical
    // DumpOlean helper was tried unchanged; its IO initializer cannot compile
    // on435, so this version-local fixture omits environment-mode machinery.
    let decision =
        clean_olean::source_world_for_file(view.source().sdk_argument_path(), Some(view.world()))
            .unwrap();
    let Ok(clean_olean::ImportWorld::Explicit { lib, .. }) = decision.imports() else {
        panic!("actual explicit SDK");
    };
    let sdk = lib.parent().unwrap().parent().unwrap().join("bin/lean");
    let oracle = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src/external_lean/primary_artifact/Inventory435.lean");
    let source = view.source();
    let parts: Vec<_> = source
        .output_parts()
        .take(3)
        .filter(|(_, observation)| observation.is_some())
        .map(|(path, _)| path)
        .collect();
    let output = std::process::Command::new(sdk)
        .env_clear()
        .arg("--run")
        .arg(oracle)
        .args(&parts)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "actual435 raw SDK oracle: {}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    if let Some(root) = std::env::var_os("CLEAN_PRIMARY_ARTIFACT_TEST_EVIDENCE") {
        let root = PathBuf::from(root).join(label);
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(root.join("raw-sdk.json"), &output.stdout).unwrap();
    }
    let index = match view.authoritative_part() {
        clean_olean::module::OLeanLevel::Exported => 0,
        clean_olean::module::OLeanLevel::Private => 2,
        other => panic!("unexpected authoritative level {other:?}"),
    };
    let part = &raw["parts"][index];
    let names: BTreeSet<_> = part["const_names"]
        .as_array()
        .unwrap()
        .iter()
        .map(oracle_name)
        .collect();
    let records: BTreeSet<_> = part["constants"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| oracle_name(&row["name"]))
        .collect();
    for row in part["constants"].as_array().unwrap() {
        let name = oracle_name(&row["name"]);
        let occurrence = view.declarations().find(|d| d.name() == &name).unwrap();
        if occurrence.captured_constant().is_some() {
            assert_eq!(
                view.program.env.is_unsafe(&name),
                row["is_unsafe"].as_bool().unwrap(),
                "actual SDK unsafe flag for resident {name:?}"
            );
            assert_eq!(
                view.program.env.is_partial(&name),
                row["is_partial"].as_bool().unwrap(),
                "actual SDK partial flag for resident {name:?}"
            );
        } else {
            // The existing loader deliberately excludes non-replayable
            // compiler auxiliaries. Missing membership is unavailable, never
            // an ordinary safe/nonpartial row, stub or replay permission.
            assert!(row["is_unsafe"].as_bool().unwrap() || row["is_partial"].as_bool().unwrap());
            assert!(view.program.inspect_owned_declaration(&name).is_err());
            assert!(view
                .program
                .replay_context(std::slice::from_ref(&name))
                .is_err());
            println!("actual SDK raw occurrence {name:?}: no captured constant; owned inspection and replay refuse PASS");
        }
    }
    assert_eq!(names.len(), part["const_names"].as_array().unwrap().len());
    assert_eq!(records.len(), part["constants"].as_array().unwrap().len());
    assert_eq!(names, records, "SDK name/record inventory");
    assert_eq!(
        view.declarations()
            .map(|d| d.name().clone())
            .collect::<BTreeSet<_>>(),
        records
    );
    assert!(view
        .declarations()
        .all(|d| d.origin() == ArtifactDeclarationOrigin::LeanRecord));
    println!(
        "actual435 upstream readModuleDataParts oracle: {} exact primary declarations PASS",
        records.len()
    );
}

const SIMPLE: &str =
    "prelude\n-- café λ\ninductive Token where | one\ndef query (x : Token) : Token := x\n";

fn n(text: &str) -> Name {
    Name::from_string(text)
}

fn export_view(label: &str, view: &PrimaryArtifactView<'_>) {
    let Some(root) = std::env::var_os("CLEAN_PRIMARY_ARTIFACT_TEST_EVIDENCE") else {
        return;
    };
    let root = PathBuf::from(root).join(label);
    std::fs::create_dir_all(&root).unwrap();
    let source = view.source();
    use sha2::{Digest, Sha256};
    let observation = |row: &InputObservation| {
        serde_json::json!({
            "path_display": row.path.display().to_string(),
            "path_encoded_bytes": row.path.as_os_str().as_encoded_bytes(),
            "bytes": row.bytes, "sha256": row.sha256,
        })
    };
    let bytes = std::fs::read(&source.owned_source_input().path).unwrap();
    assert_eq!(bytes.as_slice(), source.utf8().as_bytes());
    let digest: [u8; 32] = Sha256::digest(&bytes).into();
    assert_eq!(digest, source.owned_source_input().sha256);
    std::fs::write(root.join("captured-source.lean"), bytes).unwrap();
    let mut parts = Vec::new();
    for (index, (path, expected)) in source.output_parts().enumerate() {
        let archived = expected.map(|expected| {
            let bytes = std::fs::read(path).unwrap();
            let digest: [u8; 32] = Sha256::digest(&bytes).into();
            assert_eq!(digest, expected.sha256);
            assert_eq!(bytes.len() as u64, expected.bytes);
            let file = format!("output-{index}");
            std::fs::write(root.join(&file), bytes).unwrap();
            file
        });
        parts.push(
            serde_json::json!({"path_encoded_bytes":path.as_os_str().as_encoded_bytes(),
            "observation":expected.map(observation), "archive_file":archived}),
        );
    }
    let metadata = serde_json::json!({
        "module":view.module(), "world":format!("{:?}",view.world()),
        "authoritative_part":format!("{:?}",view.authoritative_part()),
        "declarations":view.declarations().map(|d| serde_json::json!({"name":d.name(),"origin":format!("{:?}",d.origin()),
            "captured_safety":d.captured_constant().map(|_| serde_json::json!({"is_unsafe":view.program.env.is_unsafe(d.name()),"is_partial":view.program.env.is_partial(d.name())}))})).collect::<Vec<_>>(),
        "original_input":observation(source.original_input()), "source_copy":observation(source.owned_source_input()),
        "original_canonical_encoded_bytes":source.original_canonical_path().as_os_str().as_encoded_bytes(),
        "sdk_argument_encoded_bytes":source.sdk_argument_path().as_os_str().as_encoded_bytes(),
        "sdk_canonical_encoded_bytes":source.sdk_canonical_path().as_os_str().as_encoded_bytes(),
        "all_capture_inputs":view.program.inputs().iter().map(observation).collect::<Vec<_>>(),
        "output_parts":parts,
        "global_delta_complete":view.program.source_capture().delta_complete,
        "global_capture_errors":view.program.source_capture().errors,
        "grants_source_native_model_authority":false,
    });
    std::fs::write(
        root.join("observations.json"),
        serde_json::to_vec_pretty(&metadata).unwrap(),
    )
    .unwrap();
}

fn capture(source: &str, imports: &[Name]) -> (tempfile::TempDir, ExternalLeanInspection) {
    capture_world(source, imports, LeanWorld::Lean435)
}

fn capture_world(
    source: &str,
    imports: &[Name],
    world: LeanWorld,
) -> (tempfile::TempDir, ExternalLeanInspection) {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("original-input.lean");
    std::fs::write(&file, source).unwrap();
    let program = ExternalLeanInspection::elaborate(ExternalLeanInput {
        file: &file,
        module: &n("PrimaryObservation"),
        imports,
        search_paths: &[],
        world,
    })
    .expect("actual selected435 SDK source capture");
    (directory, program)
}

#[test]
fn actual_primary_artifact_complete_roster_source_copy_utf8_and_context_affinity() {
    let (directory, program) = capture(SIMPLE, &[]);
    let view = program
        .primary_artifact(PrimaryArtifactLimits::default())
        .unwrap();
    compare_actual_sdk_roster("plain", &view);
    export_view("plain", &view);
    let source = view.source();
    assert_eq!(view.module(), &n("PrimaryObservation"));
    assert_eq!(view.world(), LeanWorld::Lean435);
    assert_eq!(source.utf8(), SIMPLE);
    assert_ne!(
        source.original_input().path,
        source.owned_source_input().path
    );
    assert_eq!(
        source.original_input().sha256,
        source.owned_source_input().sha256
    );
    assert_eq!(
        source.original_input().bytes,
        source.owned_source_input().bytes
    );
    assert_eq!(source.sdk_argument_path(), source.owned_source_input().path);
    assert_eq!(
        source.original_canonical_path(),
        std::fs::canonicalize(&source.original_input().path).unwrap()
    );
    source
        .require_producer_path(source.sdk_argument_path(), PrimaryArtifactLimits::default())
        .unwrap();
    source
        .require_producer_path(
            source.sdk_canonical_path(),
            PrimaryArtifactLimits::default(),
        )
        .unwrap();
    assert!(matches!(
        source.require_producer_path(
            &source.original_input().path,
            PrimaryArtifactLimits::default()
        ),
        Err(PrimaryArtifactError::ProducerPathMismatch)
    ));
    let start = SIMPLE.find('é').unwrap();
    assert_eq!(source.slice_utf8(start, start + 2).unwrap(), "é");
    for (a, b) in [
        (start, start + 1),
        (start + 1, start + 2),
        (5, 4),
        (0, SIMPLE.len() + 1),
    ] {
        assert!(matches!(
            source.slice_utf8(a, b),
            Err(PrimaryArtifactError::InvalidRange)
        ));
    }
    let parts: Vec<_> = source.output_parts().collect();
    assert_eq!(parts.len(), 5);
    let artifact_path = parts
        .iter()
        .find(|(path, _)| path.extension().is_some_and(|e| e == "olean"))
        .unwrap()
        .0;
    let artifact = clean_olean::read_artifact(
        "actual control",
        artifact_path,
        clean_olean::ArtifactDepth::Records,
    )
    .unwrap();
    let expected = artifact.inventory.unwrap().unwrap();
    let actual: BTreeSet<_> = view
        .declarations()
        .map(|d| (d.name().clone(), format!("{:?}", d.origin())))
        .collect();
    assert_eq!(
        actual,
        expected
            .declarations()
            .iter()
            .map(|d| (d.name().clone(), format!("{:?}", d.origin())))
            .collect()
    );
    assert!(actual.iter().any(|(name, _)| name == &n("query")));
    let context = program.replay_context(&[n("query")]).unwrap();
    view.require_context(&context).unwrap();
    let (_other_directory, other) = capture(SIMPLE, &[]);
    let foreign = other.replay_context(&[n("query")]).unwrap();
    assert!(matches!(
        view.require_context(&foreign),
        Err(PrimaryArtifactError::ForeignContext)
    ));
    let (_old_directory, old) = capture_world(SIMPLE, &[], LeanWorld::ORACLE);
    let old_context = old.replay_context(&[n("query")]).unwrap();
    assert!(matches!(
        view.require_context(&old_context),
        Err(PrimaryArtifactError::ForeignContext)
    ));
    // Original input liveness is not promised: only owned copies are rechecked.
    drop(directory);
    assert!(program
        .primary_artifact(PrimaryArtifactLimits::default())
        .is_ok());
    println!("actual435 default logical inspection: exact inventory, actual copy/output ledger, UTF8 ranges, same-context/foreign refusal and historical original observation PASS");
}

#[test]
fn actual_primary_artifact_full_init_keeps_flags_aliases_and_imported_identities() {
    let source = "def query (x : Nat) : Nat := x\nunsafe def unsafeLocal (x : Nat) : Nat := x\npartial def partialLocal (x : Nat) : Nat := partialLocal x\nprivate def hidden : Nat := 0\ndef alias : Nat := Nat.zero\n";
    let (_directory, program) = capture(source, &[n("Init")]);
    let view = program
        .primary_artifact(PrimaryArtifactLimits::default())
        .unwrap();
    compare_actual_sdk_roster("full-init-flags", &view);
    export_view("full-init-flags", &view);
    let names: BTreeSet<_> = view.declarations().map(|d| d.name().clone()).collect();
    for name in ["query", "unsafeLocal", "partialLocal", "alias"] {
        assert!(
            names.contains(&n(name)),
            "actual {name} must remain in complete roster"
        );
    }
    assert!(names.iter().any(|name| name.to_string().contains("hidden")));
    assert!(!names.contains(&n("Nat.zero")));
    assert!(program.program.env.is_unsafe(&n("unsafeLocal")));
    // Source `partial def` need not set DefinitionSafety.partial on its public
    // wrapper. Compare actual SDK record flags above, not source-keyword guesses.
    assert!(names.contains(&n("partialLocal._unsafe_rec")));
    let context = program.replay_context(&[n("alias")]).unwrap();
    assert!(context.declaration(&n("alias")).unwrap().is_source_owned());
    assert!(!context
        .declaration(&n("Nat.zero"))
        .unwrap()
        .is_source_owned());
    assert!(
        !program.source_capture().delta_complete,
        "known full-Init runtime-capture failure must remain disclosed"
    );
    assert!(!program.source_capture().errors.is_empty());
    println!("actual435 fullInit: unsafe/partial/private/alias records retained, imported Nat.zero stays imported, incomplete runtime capture retained PASS");
}

#[test]
fn actual_primary_artifact_module_private_authoritative_part_is_complete() {
    let source = "module\nprelude\npublic inductive Token where | one\npublic def query (x : Token) : Token := x\nprivate def hidden (x : Token) : Token := x\n";
    let (_directory, program) = capture(source, &[]);
    let view = program
        .primary_artifact(PrimaryArtifactLimits::default())
        .unwrap();
    assert_eq!(
        view.authoritative_part(),
        clean_olean::module::OLeanLevel::Private
    );
    assert!(view
        .declarations()
        .any(|d| d.name().to_string().contains("hidden")));
    assert!(view
        .source()
        .output_parts()
        .take(3)
        .all(|(_, observation)| observation.is_some()));
    compare_actual_sdk_roster("module-private", &view);
    export_view("module-private", &view);
}

#[test]
fn actual_primary_artifact_owned_changes_and_frozen_absence_refuse_atomically() {
    let (_directory, program) = capture(SIMPLE, &[]);
    let view = program
        .primary_artifact(PrimaryArtifactLimits::default())
        .unwrap();
    let source_path = view.source().owned_source_input().path.clone();
    let output = view
        .source()
        .output_parts()
        .find(|(_, observation)| observation.is_some())
        .unwrap()
        .0
        .to_path_buf();
    let absent = view
        .source()
        .output_parts()
        .find(|(_, observation)| observation.is_none())
        .map(|(path, _)| path.to_path_buf());
    std::fs::write(&source_path, SIMPLE.replace("café", "cafe")).unwrap();
    assert!(matches!(
        program.primary_artifact(PrimaryArtifactLimits::default()),
        Err(PrimaryArtifactError::ChangedOwnedInput)
    ));
    std::fs::write(&source_path, SIMPLE).unwrap();
    let original = std::fs::read(&output).unwrap();
    std::fs::write(&output, b"changed owned artifact").unwrap();
    assert!(matches!(
        program.primary_artifact(PrimaryArtifactLimits::default()),
        Err(PrimaryArtifactError::ChangedOwnedInput)
    ));
    std::fs::write(&output, original).unwrap();
    if let Some(path) = absent {
        std::fs::write(&path, b"appeared").unwrap();
        assert!(matches!(
            program.primary_artifact(PrimaryArtifactLimits::default()),
            Err(PrimaryArtifactError::ChangedOwnedInput)
        ));
        std::fs::remove_file(path).unwrap();
    } else {
        panic!("actual prelude fixture must retain at least one absent companion");
    }
    #[cfg(unix)]
    {
        let renamed = source_path.with_extension("moved-source");
        std::fs::rename(&source_path, &renamed).unwrap();
        std::os::unix::fs::symlink(&renamed, &source_path).unwrap();
        assert!(matches!(
            program.primary_artifact(PrimaryArtifactLimits::default()),
            Err(PrimaryArtifactError::ChangedOwnedInput)
        ));
        std::fs::remove_file(&source_path).unwrap();
        std::fs::rename(renamed, &source_path).unwrap();
    }
    assert!(program
        .primary_artifact(PrimaryArtifactLimits::default())
        .is_ok());
}

#[test]
fn actual_primary_artifact_positive_limits_bound_counts_structure_and_bytes() {
    let (_directory, program) = capture(SIMPLE, &[]);
    for limits in [(0, 1, 1), (1, 0, 1), (1, 1, 0)] {
        assert!(PrimaryArtifactLimits::new(limits.0, limits.1, limits.2).is_err());
    }
    assert!(matches!(
        program.primary_artifact(PrimaryArtifactLimits::new(1, 100_000, 64 * 1024 * 1024).unwrap()),
        Err(PrimaryArtifactError::Inventory(
            ArtifactInventoryError::DeclarationLimit
        ))
    ));
    assert!(matches!(
        program.primary_artifact(PrimaryArtifactLimits::new(100_000, 1, 64 * 1024 * 1024).unwrap()),
        Err(PrimaryArtifactError::Inventory(
            ArtifactInventoryError::StructuralLimit
        ))
    ));
    assert!(matches!(
        program.primary_artifact(PrimaryArtifactLimits::new(100_000, 100_000, 1).unwrap()),
        Err(PrimaryArtifactError::ByteLimit)
    ));
    let view = program
        .primary_artifact(PrimaryArtifactLimits::default())
        .unwrap();
    assert!(matches!(
        view.source().require_producer_path(
            view.source().sdk_argument_path(),
            PrimaryArtifactLimits::new(1, 1, 1).unwrap()
        ),
        Err(PrimaryArtifactError::StructuralLimit)
    ));
    assert!(program
        .primary_artifact(PrimaryArtifactLimits::default())
        .is_ok());
}

#[test]
fn actual_primary_artifact_empty_is_complete_and_private_corruption_never_succeeds() {
    let (_directory, mut program) = capture("prelude\n", &[]);
    assert_eq!(
        program
            .primary_artifact(PrimaryArtifactLimits::default())
            .unwrap()
            .declarations()
            .len(),
        0
    );
    // Fabricated private-record corruption control, not an SDK negative.
    let custody = Arc::get_mut(&mut program.program.custody).unwrap();
    custody.primary_artifact.as_mut().unwrap().copy = usize::MAX;
    assert!(matches!(
        program.primary_artifact(PrimaryArtifactLimits::default()),
        Err(PrimaryArtifactError::MissingAssociation)
    ));
}

#[test]
fn actual_primary_artifact_sdk_reported_file_path_is_the_recorded_owned_argument() {
    let source = "import Lean.Elab.Command\nopen Lean Elab Command in\nrun_cmd do\n  let file ← getFileName\n  elabCommand (← `(def $(mkIdent (Name.mkSimple \"actualProducerPath\")) : String := $(quote file)))\n";
    let (_directory, program) = capture(source, &[n("Init"), n("Lean.Elab.Command")]);
    let view = program
        .primary_artifact(PrimaryArtifactLimits::default())
        .unwrap();
    export_view("sdk-filename", &view);
    let record = view
        .declarations()
        .find(|d| d.name() == &n("actualProducerPath"))
        .unwrap();
    let value = record.captured_constant().unwrap().value.as_ref().unwrap();
    let ExprKind::Lit(Literal::String(path)) = value.kind() else {
        panic!("SDK command must retain actual filename string");
    };
    view.source()
        .require_producer_path(Path::new(path.as_ref()), PrimaryArtifactLimits::default())
        .unwrap();
    assert_ne!(
        Path::new(path.as_ref()),
        view.source().original_input().path
    );
    println!("actual435 SDK getFileName value matches actual recorded owned-copy path; original filename cannot substitute PASS");
}
