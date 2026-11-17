// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
use std::path::{Path, PathBuf};
use std::sync::Arc;

use clean_kernel::{Environment, Name};

use super::*;
use crate::module_driver::EnvironmentSetup;

fn module(name: &str, source: &str) -> CapturedSourceModule {
    CapturedSourceModule {
        name: Name::from_string(name),
        path: format!("/never-open-captured-input/{name}.lean").into(),
        source: Arc::from(source),
    }
}

fn run(
    modules: Vec<CapturedSourceModule>,
    roots: &[&str],
) -> Result<SourceGraphOutput, SourceGraphError> {
    let names: std::collections::BTreeSet<_> =
        modules.iter().map(|module| module.name.clone()).collect();
    let graph = CapturedSourceGraph::new(modules)?;
    let decision = clean_olean::source_world_for_snapshot().expect("configured source world DATA");
    graph.elaborate(
        &roots
            .iter()
            .map(|name| Name::from_string(name))
            .collect::<Vec<_>>(),
        EnvironmentSetup::default(),
        &decision,
        &mut |from: &CapturedSourceModule, imported: &Name| {
            if names.contains(imported) {
                Ok(SourceImport::Captured(imported.clone()))
            } else if imported == &Name::from_string("Init.Prelude") {
                Ok(SourceImport::Artifact)
            } else {
                Err(SourceGraphError::Import {
                    module: from.name.clone(),
                    imported: imported.clone(),
                    reason: "unmounted source import in this test".into(),
                })
            }
        },
    )
}

#[test]
fn captured_bytes_sibling_imports_and_original_anonymous_terms() {
    let defs = module(
        "Defs",
        "prelude\nuniverse u\ndef ident (α : Sort u) (a : α) : α := a\n",
    );
    let use_defs = module("Use", "prelude\nimport Defs\nuniverse u\ndef useIdent (α : Sort u) (a : α) : α := ident α a\nexample (α : Sort u) (a : α) : α := ident α a\n");
    assert!(!defs.path.exists() && !use_defs.path.exists());
    let original = Arc::clone(&use_defs.source);
    let output =
        run(vec![use_defs, defs], &["Use"]).expect("source import in one canonical environment");
    assert_eq!(output.modules.len(), 2);
    assert!(output
        .environment
        .get_const(&Name::from_string("ident"))
        .is_some());
    assert!(output
        .environment
        .get_const(&Name::from_string("useIdent"))
        .is_some());
    let uses = &output.modules[&Name::from_string("Use")];
    assert_eq!(uses.checked_judgments.len(), 1);
    assert!(uses.introduced.contains(&Name::from_string("useIdent")));
    assert!(!uses.introduced.contains(&Name::from_string("ident")));
    assert_eq!(
        output
            .inputs
            .iter()
            .find(|input| input.name == Name::from_string("Use"))
            .unwrap()
            .source,
        original
    );
    let judgment = &uses.checked_judgments[0];
    let checker = clean_kernel::TypeChecker::new(&output.environment);
    checker
        .check_type(&judgment.value, &judgment.type_)
        .expect("actual original anonymous term");
}

#[test]
fn captured_import_cycles_unmounted_and_ill_typed_bodies_refuse() {
    let cycle = run(
        vec![
            module("A", "prelude\nimport B\n"),
            module("B", "prelude\nimport A\n"),
        ],
        &["A"],
    )
    .err()
    .expect("source cycle refused")
    .to_string();
    assert!(cycle.contains("cycle"), "{cycle}");
    let missing = run(vec![module("A", "prelude\nimport Missing\n")], &["A"])
        .err()
        .expect("unmounted import refused")
        .to_string();
    assert!(
        missing.contains("unmounted") && missing.contains("Missing"),
        "{missing}"
    );
    let bad = run(
        vec![module(
            "Bad",
            "prelude\nuniverse u\ndef bad (α : Sort u) (a : α) : α := α\n",
        )],
        &["Bad"],
    )
    .err()
    .expect("actual source type error refused")
    .to_string();
    assert!(bad.contains("bad") || bad.contains("Bad"), "{bad}");
}

#[test]
fn an_unimported_sibling_cannot_supply_a_source_body() {
    let result = run(vec![
        module("P", "prelude\nuniverse u\ndef hidden (α : Sort u) (a : α) : α := a\n"),
        module("Q", "prelude\nuniverse u\ndef dependsOnStranger (α : Sort u) (a : α) : α := hidden α a\n"),
        module("Main", "prelude\nimport P\nimport Q\n"),
    ], &["Main"]);
    let error = result
        .err()
        .expect("Q must fail in its own import closure")
        .to_string();
    assert!(error.contains("Q") && error.contains("hidden"), "{error}");
}

#[test]
fn captured_import_notation_is_seeded_without_reopening_a_path() {
    // Word aliases are an existing shared frontend limitation: the parser
    // skips identifier-led mixfix and imported FileContexts do not transport
    // same-file MacroCtx aliases. Preserve the exact refusal, not a pass.
    let inherited = run(vec![
        module("Defs", "prelude\nuniverse u\ndef ident (α : Sort u) (a : α) : α := a\nnotation \"capturedIdentity\" => ident\n"),
        module("Use", "prelude\nimport Defs\nuniverse u\ndef result (α : Sort u) (a : α) : α := capturedIdentity α a\n"),
    ], &["Use"]).err().expect("imported word alias remains refused").to_string();
    assert!(
        inherited.contains("Unknown identifier: capturedIdentity"),
        "{inherited}"
    );
    // This closed symbol-led notation uses the maintained parser expansion.
    let output = run(vec![
        module("Defs", "prelude\nuniverse u\ndef ident (α : Sort u) (a : α) : α := a\nnotation \"⌞\" α \", \" a \"⌟\" => ident α a\n"),
        module("Use", "prelude\nimport Defs\nuniverse u\ndef result (α : Sort u) (a : α) : α := ⌞α, a⌟\n"),
    ], &["Use"]).expect("captured closed mixfix reaches the maintained parser");
    assert!(output
        .environment
        .get_const(&Name::from_string("result"))
        .is_some());
}

#[test]
fn captured_inventory_and_frozen_resolution_are_fail_closed() {
    assert!(
        CapturedSourceGraph::new(vec![module("A", "prelude"), module("A", "prelude")]).is_err()
    );
    let mut other = module("B", "prelude");
    other.path = module("A", "prelude").path;
    assert!(CapturedSourceGraph::new(vec![module("A", "prelude"), other]).is_err());
    assert!(run(vec![module("A", "prelude"), module("B", "prelude")], &["A"]).is_err());
    let graph = CapturedSourceGraph::new(vec![
        module("A", "prelude\nimport B\n"),
        module("B", "prelude"),
    ])
    .unwrap();
    let decision = clean_olean::source_world_for_snapshot().unwrap();
    let error = graph
        .elaborate(
            &[Name::from_string("A")],
            EnvironmentSetup::default(),
            &decision,
            &mut |_from: &CapturedSourceModule, _import: &Name| Ok(SourceImport::Artifact),
        )
        .err()
        .expect("artifact cannot replace captured B")
        .to_string();
    assert!(error.contains("replace a captured"), "{error}");
}

#[test]
fn shared_effect_comparison_includes_failed_commands_and_environment_metadata() {
    let base = Environment::default();
    let plain = ModuleElaboration {
        effect: base.effect_since(&base),
        outcomes: vec![ElabOutcome::Refused],
    };
    let omitted_failure = ModuleElaboration {
        effect: base.effect_since(&base),
        outcomes: Vec::new(),
    };
    assert!(plain.disagreement(&omitted_failure, &base).is_some());
    let mut changed = base.clone();
    changed.set_option("sourceGraphControl".into(), Some("changed".into()));
    let own = ModuleElaboration {
        effect: base.effect_since(&base),
        outcomes: Vec::new(),
    };
    let shared = ModuleElaboration {
        effect: changed.effect_since(&base),
        outcomes: Vec::new(),
    };
    assert!(own.disagreement(&shared, &changed).is_some());
}

#[test]
fn shared_import_walk_preserves_order_diamond_dedup_and_backedge_refusal() {
    let mut graph = ImportGraph::default();
    let root = Path::new("Root");
    graph.enter(root, 256).unwrap().unwrap();
    for child in ["First", "Second"] {
        let path = Path::new(child);
        let before = graph.enter(path, 256).unwrap().unwrap();
        assert!(graph.enter(root, 256).unwrap_err().contains("cycle"));
        // Failed backedges add no frame. The original direct-import ledger
        // records the attempted edge; this unsuccessful walk is never completed.
        graph.import_frames.last_mut().unwrap().clear();
        let imports = graph.leave(path);
        graph.record_imports(path, imports, &before);
        graph.completed.insert(path.into());
    }
    let imports = graph.leave(root);
    assert_eq!(
        imports,
        vec![PathBuf::from("First"), PathBuf::from("Second")]
    );
    graph.completed.insert(PathBuf::from("First"));
    assert!(graph.enter(Path::new("First"), 256).unwrap().is_none());
}

#[test]
fn genuine_init_header_isolation_and_anonymous_source_fidelity_controls() {
    std::thread::Builder::new().stack_size(128 << 20).spawn(|| {
        let positive = run(vec![module("Genuine", "prelude\nimport Init.Prelude\ndef actualNat : Nat := 2\nexample : actualNat = 2 := rfl\n")], &["Genuine"])
            .expect("explicit genuine Init DATA and original source judgment");
        let observed = &positive.modules[&Name::from_string("Genuine")];
        assert_eq!(observed.checked_judgments.len(), 1);
        assert_eq!(observed.declarations[0].span.start, 0);
        assert_eq!(observed.declarations[0].span.end, "prelude".len());
        assert!(observed.declarations.iter().any(|event| event.primary_name == Some(Name::from_string("actualNat"))));

        let leaked = run(vec![
            module("Leaky", "prelude\ndef borrowedNat : Nat := 0\n"),
            module("Parent", "import Leaky\ndef parent : Nat := 0\n"),
        ], &["Parent"]).err().expect("prelude must not borrow ordinary parent's implicit Init").to_string();
        assert!(leaked.contains("Leaky") && leaked.contains("Nat"), "{leaked}");

        let changed_example = run(vec![
            module("Base", "prelude\nimport Init.Prelude\n"),
            module("P", "prelude\nimport Base\ninstance (priority := high) three : OfNat Nat 2 := ⟨3⟩\n"),
            module("Q", "prelude\nimport Base\nexample : (2 : Nat) = 2 := rfl\n"),
            module("Main", "prelude\nimport P\nimport Q\n"),
        ], &["Main"]).err().expect("canonical and own-closure examples must be the same judgments").to_string();
        assert!(changed_example.contains("anonymous judgments differ"), "{changed_example}");

        let decision = clean_olean::source_world_for_snapshot().unwrap();
        let collision = CapturedSourceGraph::new(vec![module("Init.Prelude", "prelude\n")]).unwrap()
            .elaborate(&[Name::from_string("Init.Prelude")], EnvironmentSetup::default(), &decision,
                &mut |_from: &CapturedSourceModule, _import: &Name| Ok(SourceImport::Artifact))
            .err().expect("captured source must not shadow the selected world's real artifact").to_string();
        assert!(collision.contains("collides with an artifact"), "{collision}");

        let missing_artifact = CapturedSourceGraph::new(vec![module("MissingArtifact", "prelude\nimport Init.SourceGraphFictionalModule\n")]).unwrap()
            .elaborate(&[Name::from_string("MissingArtifact")], EnvironmentSetup::default(), &decision,
                &mut |_from: &CapturedSourceModule, _import: &Name| Ok(SourceImport::Artifact))
            .err().expect("fictional Init module gets no provider fallback").to_string();
        assert!(missing_artifact.contains("Init.SourceGraphFictionalModule"), "{missing_artifact}");
    }).unwrap().join().unwrap();
}

#[test]
fn genuine_empty_prelude_only_and_import_only_modules_have_a_body_boundary() {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(|| {
            let output = run(
                vec![
                    module("Empty", ""),
                    module("PreludeOnly", "prelude\n"),
                    module("ImportOnly", "prelude\nimport PreludeOnly\n"),
                ],
                &["Empty", "PreludeOnly", "ImportOnly"],
            )
            .expect("actual empty and header-only mounted modules");
            assert_eq!(output.modules.len(), 3);
            for module in output.modules.values() {
                assert!(module.introduced.is_empty());
                assert!(module.checked_judgments.is_empty());
                assert!(module.report.verdicts.is_empty());
            }
            assert!(output.modules[&Name::from_string("Empty")]
                .declarations
                .is_empty());
            assert_eq!(
                output.modules[&Name::from_string("PreludeOnly")]
                    .declarations
                    .len(),
                1
            );
            assert_eq!(
                output.modules[&Name::from_string("ImportOnly")]
                    .declarations
                    .len(),
                2
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
