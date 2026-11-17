// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Static raw-check completeness with exact proof/meaning pins; no full C7 or authority claim.
#[path = "support/subject_export.rs"]
mod subject_export;
use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{ConstantKind, Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, ArtifactDepth,
    ClosedRecheckOptions,
};
#[path = "support/meaning_digest.rs"]
mod meaning_digest;
use meaning_digest::{MeaningDigests, Package};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

const MODULES: [&str; 1] = ["KCheckStaticComplete"];
#[test]
fn actual_raw_static_check_and_init_id_have_exact_proofs_and_meanings() {
    let package =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_static_complete");
    let descriptor: toml::Value = toml::from_str(
        &std::fs::read_to_string(package.join("lakefile.toml")).expect("package descriptor"),
    )
    .expect("descriptor TOML");
    let roots: Vec<&str> = descriptor["lean_lib"][0]["roots"]
        .as_array()
        .expect("library roots")
        .iter()
        .map(|root| root.as_str().expect("root name"))
        .collect();
    assert_eq!(
        roots, MODULES,
        "every actual module is an explicit library root"
    );
    let order: Vec<String> = std::fs::read_to_string(package.join("ORDER"))
        .expect("package order")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|stem| stem.replace('/', "."))
        .collect();
    assert_eq!(
        order, MODULES,
        "fixture compilation covers exactly the same modules"
    );
    let compiled = compiled_fixture_dir("kcheck_static_complete");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let leanchecker = lean.parent().expect("toolchain bin").join("leanchecker");
    let replay = Command::new(leanchecker)
        .arg("--fresh")
        .arg(MODULES[0])
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean paths"),
        )
        .output()
        .expect("independent actual closure replay");
    assert!(
        replay.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );
    let mut loaded = Environment::for_lean_replay();
    load_module_with_deps(&mut loaded, MODULES[0], &[compiled.clone(), lib])
        .expect("compiled original input");
    let mut targets = BTreeSet::new();
    for module in MODULES {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .expect("actual module declarations, including private names");
        for name in artifact.names {
            assert!(
                loaded.get_const(&name).is_some(),
                "stored target {name} is absent; no exclusion is authorized"
            );
            targets.insert(name);
        }
    }
    let base = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("fenced replay construction");
    assert!(
        base.report.passed() && base.entry_refusals.is_empty(),
        "{:?} {:?}",
        base.report,
        base.entry_refusals
    );
    let mut kernel = base.into_kernel().expect("genuine successful completion");
    let meaning_package = Package::of_fixture(
        &compiled,
        "kcheck_static_complete",
        &[
            "cic_l",
            "cic_l_model",
            "kcheck_spec",
            "kcheck_labelled",
            "cic_l_nat_literals",
            "kcheck_nat_acceptance",
            "kcheck_inference_complete",
            "kcheck_static_complete",
        ],
    );
    let full_pins: BTreeMap<Name, String> = {
        let digests = MeaningDigests::new(kernel.environment(), &meaning_package);
        let pins = targets
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    digests
                        .digest(name)
                        .expect("canonical full package meaning closure"),
                )
            })
            .collect();
        eprintln!(
            "{}",
            digests
                .describe(
                    &meaning_package,
                    &targets.iter().cloned().collect::<Vec<_>>()
                )
                .expect("complete meaning-closure inventory")
        );
        pins
    };
    let mut statements = BTreeMap::new();
    let mut meanings = BTreeMap::new();
    let mut closures = BTreeMap::new();
    for name in &targets {
        let c = loaded.get_const(name).expect("target exists");
        if c.kind != ConstantKind::Theorem {
            meanings.insert(name.to_string(), full_pins[name].clone());
            continue;
        }
        statements.insert(name.to_string(), full_pins[name].clone());
        let admitted = kernel.environment();
        let mut closure = admitted.axiom_deps(name).expect("admitted target");
        closure.extend(
            admitted
                .foundational_axiom_deps(name)
                .expect("foundational closure"),
        );
        assert!(
            closure.iter().all(clean_kernel::env::is_foundational_axiom),
            "{name} has a domain-specific or trust-marker dependency: {closure:?}"
        );
        closures.insert(
            name.to_string(),
            closure
                .iter()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>(),
        );
        let value = c.value.clone().expect("a theorem must carry a proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!(
                    "KCheckStaticComplete.Controls.positive{}",
                    statements.len()
                )),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .expect("same proof must first pass at its original statement");
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!(
                "KCheckStaticComplete.Controls.forged{}",
                statements.len()
            )),
            level_params: c.level_params.clone(),
            type_: Expr::const_(Name::from_string("False"), vec![]),
            value,
        });
        assert!(
            matches!(
                forged,
                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                }))
            ),
            "{name}: wrong statement must fail by type mismatch, got {forged:?}"
        );
    }
    assert_eq!(
        statements.len(),
        127,
        "exact theorem denominator; review every added/private theorem"
    );
    eprintln!(
        "static-check-completeness-statement-pins: {}",
        serde_json::to_string(&statements).expect("pins")
    );
    eprintln!(
        "static-check-completeness-meaning-pins: {}",
        serde_json::to_string(&meanings).expect("meanings")
    );

    eprintln!(
        "static-check-completeness-native-closure-pins: {}",
        serde_json::to_string(&closures).expect("complete native closure map")
    );
    subject_export::capture_if_requested(
        "CLEAN_STATIC_CHECK_EXPORT_PATH",
        "static-check-completeness-export",
        &loaded,
        &targets,
    );

    let expected: BTreeMap<String, String> = serde_json::from_str(
        &std::fs::read_to_string(package.join("statement_pins.json")).expect(
            "reviewed statement pins are required; a missing native qualification never passes",
        ),
    )
    .expect("pins JSON");
    let expected_meanings: BTreeMap<String, String> = serde_json::from_str(
        &std::fs::read_to_string(package.join("meaning_pins.json"))
            .expect("reviewed meaning pins are required"),
    )
    .expect("meaning JSON");
    assert_eq!(
        statements, expected,
        "canonical full-package statement meaning closures"
    );
    assert_eq!(
        meanings, expected_meanings,
        "canonical full-package non-theorem meaning closures"
    );
    let expected_closures: BTreeMap<String, BTreeSet<String>> = serde_json::from_str(
        &std::fs::read_to_string(package.join("native_foundational_closures.json"))
            .expect("reviewed exact native foundational closures"),
    )
    .expect("closure JSON");
    assert_eq!(
        closures, expected_closures,
        "no unreviewed axiom-closure growth"
    );
}
