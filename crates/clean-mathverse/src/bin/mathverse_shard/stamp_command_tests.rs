// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Controls for P6 reader R1 (`mathverse_shard stamp`): every manifest this
//! build can read is refused, and the shard bytes are byte-identical after.

use super::*;

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_mathverse::shard::ShardWriter;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
};
use clean_mathverse::verify::incremental::verify_shard_incremental_with_env;
use clean_mathverse::verify::kernel_verified_manifest::{
    BaseEnvironment, BaseVariant, BuildIdentity, CheckSettings, DevelopmentRun, Elision, Imports,
    InductiveReplay,
};

/// A shard holding `Foo : Type 0 := Prop` at `Translated` confidence, which
/// the legacy corpus verifier accepts. Returns its bytes.
fn write_foo_shard(dir: &std::path::Path) -> Vec<u8> {
    let mut writer = ShardWriter::new();
    let name_idx = writer.add_string("Foo");
    let l_zero = writer.add_level(FlatLevel::zero());
    let l_one = writer.add_level(FlatLevel::succ(l_zero));
    let type_idx = writer.add_expr(FlatExpr::sort(l_one));
    let value_idx = writer.add_expr(FlatExpr::sort(l_zero));
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Translated as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut bytes = Vec::new();
    writer.write(&mut bytes).expect("encode shard");
    std::fs::write(dir.join("Foo.mathverse"), &bytes).expect("write shard");
    bytes
}

/// A genuine development manifest over the Foo shard: Foo is accepted.
fn write_development_manifest(dir: &std::path::Path, bytes: &[u8]) -> PathBuf {
    let reader = clean_mathverse::shard::ShardReader::from_bytes(bytes).expect("decode shard");
    let env = clean_kernel::Environment::try_with_prelude().expect("prelude");
    let run = DevelopmentRun::new(
        env.checker_settings(),
        BaseEnvironment::measure(&env, BaseVariant::Prelude),
        Imports::Replayed,
        CheckSettings {
            elision: Elision::None,
            inductive_replay: InductiveReplay::Generate,
            level_repair: false,
            heartbeat_limit: env.checker_settings().max_heartbeats,
            max_closure_modules: None,
        },
        BuildIdentity::current().expect("hash the test executable"),
    )
    .expect("a nameable development run");
    let report = verify_shard_incremental_with_env(&reader, env);
    assert_eq!(report.kernel_verified_names, ["Foo".to_string()]);
    let path = dir.join("kernel-verified.json");
    KernelVerifiedManifest::from_incremental_report(
        "test",
        &dir.display().to_string(),
        1,
        &report,
        run,
    )
    .write_to_file(&path)
    .expect("write manifest");
    path
}

fn opts(dir: &std::path::Path, manifest: PathBuf) -> StampOpts {
    StampOpts {
        shard_dir: dir.to_path_buf(),
        manifest,
        json: false,
    }
}

/// A valid development manifest naming an accepted constant is refused as
/// development tier, and the shard is byte-identical afterwards.
#[test]
fn test_stamp_refuses_development_manifest_and_leaves_bytes_unchanged() {
    let dir = tempfile::tempdir().expect("tempdir");
    let bytes = write_foo_shard(dir.path());
    let manifest = write_development_manifest(dir.path(), &bytes);
    let err = run_stamp(&opts(dir.path(), manifest)).expect_err("development manifest refused");
    assert!(err.contains("development-tier"), "{err}");
    assert_eq!(
        std::fs::read(dir.path().join("Foo.mathverse")).expect("re-read"),
        bytes,
        "the shard bytes are byte-identical after a refused stamp"
    );
}

/// A schema-1 manifest naming the constant (the shape the verb used to apply)
/// is refused by its own validation, and the shard is byte-identical.
#[test]
fn test_stamp_refuses_schema1_manifest_and_leaves_bytes_unchanged() {
    let dir = tempfile::tempdir().expect("tempdir");
    let bytes = write_foo_shard(dir.path());
    let manifest = dir.path().join("kernel-verified.json");
    std::fs::write(
        &manifest,
        r#"{"schema_version":1,"kernel_verified":1,"kernel_verified_names":["Foo"]}"#,
    )
    .expect("write schema-1 manifest");
    let err = run_stamp(&opts(dir.path(), manifest)).expect_err("schema-1 manifest refused");
    assert!(err.contains("schema_version 1"), "{err}");
    assert_eq!(
        std::fs::read(dir.path().join("Foo.mathverse")).expect("re-read"),
        bytes,
        "the shard bytes are byte-identical after a refused stamp"
    );
}
