// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent reference-proof and canonical-helper cross-check for D1 Revision 5.
//!
//! This adjunct imports the existing term syntax; it does not depend on the
//! false Revision 4 walk bridge or establish a checker soundness step. Pinned
//! Lean compiles the package, leanchecker replays its bytes independently, and
//! every declaration from its modules is re-admitted through the fenced Clean
//! reference entry. Every theorem statement and every declaration's observed
//! axiom closure is pinned, including compiler-generated and private names.
//!
//! A theorem's, contract's or dependency definition's pin is its meaning
//! digest (`support/meaning_digest.rs`) over the package of the fixture family
//! `kcheck_sort_bounds` (`cic_l`, `cic_l_model`, `kcheck_spec`,
//! `kcheck_sort_bounds`): the constant and every package definition,
//! inductive type, constructor and compiler auxiliary it reaches, down to
//! Init, a reached theorem by its statement. The two canonical helpers keep
//! their `::type-and-value` pins, which bind their proofs. Re-pin with
//! `CLEAN_REPIN_STATEMENT_PINS=1 scripts/heavy_gate.sh run 16 kcheck-sort-bounds-repin
//! -- "$(rustup run trust rustc --print sysroot)/bin/targo" --unverified test -p
//! clean-olean --locked --test kcheck_sort_bounds`: the run rewrites
//! `theories/kcheck_sort_bounds/statement_pins.json` and still fails, and the
//! next run without the variable, after a rebuild, confirms it.

#[path = "support/meaning_digest.rs"]
mod meaning_digest;

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{ConstantInfo, ConstantKind, Declaration, Environment};
use clean_kernel::{Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use meaning_digest::{MeaningDigests, Package};
use sha2::{Digest, Sha256};

const ROOT: &str = "KCheckSortBounds";
const CONTRACTS: &[(&str, &str)] = &[
    ("sortsWithin_inst", "inst"),
    ("sortsWithin_instLevels", "instLevels"),
    ("Contracts.canonicalInst", "inst"),
    ("Contracts.canonicalInstLevels", "instLevels"),
    ("inst_needs_argument", "needsArgument"),
    ("inst_needs_body", "needsBody"),
    ("instLevels_needs_transport", "needsTransport"),
    ("instLevels_missing_defaults", "missingDefaults"),
];
const FORGED_STATEMENTS: &[(&str, &str)] = &[
    ("sortsWithin_inst", "forgedInstArgument"),
    ("sortsWithin_inst", "forgedInstBody"),
    ("sortsWithin_instLevels", "forgedInstLevels"),
    ("Contracts.canonicalInst", "forgedInstArgument"),
    ("Contracts.canonicalInst", "forgedInstBody"),
    ("Contracts.canonicalInstLevels", "forgedInstLevels"),
];
const CANONICAL_HELPERS: &[&str] = &[
    "KCheckSpec.Term.sortsWithin_inst",
    "KCheckSpec.sortsWithin_instLevels",
];
const DEPENDENCY_DEFINITIONS: &[&str] = &[
    "KCheckSpec.Term.SortsWithin",
    "KCheckSpec.Term.inst",
    "KCheckSpec.Term.instLevels",
    "CICL.levelSubstitution",
    "KCheckSpec.pad",
];

// These public equation families were first emitted in the reference package
// before R5's canonical proofs began using them. Keep their current compiled
// declarations as explicit roots even when their origin moves into an import.
// Private generated declarations are selected by the exact own-module census;
// no equivalence between obsolete and current compiler-private names is assumed.
fn dependency_equation(subject: &Name) -> bool {
    let subject = subject.to_string();
    DEPENDENCY_DEFINITIONS.iter().any(|definition| {
        subject
            .strip_prefix(&format!("{definition}."))
            .is_some_and(|suffix| {
                suffix.starts_with("eq_") || suffix.starts_with("_sparseCasesOn_")
            })
    })
}

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn theorem_name(short: &str) -> Name {
    name(&format!("KCheckSortBounds.{short}"))
}

fn contract_name(short: &str) -> Name {
    name(&format!("KCheckSortBounds.Contracts.{short}"))
}

fn constant_digest(constant: &ConstantInfo) -> String {
    let mut hasher = Sha256::new();
    for part in std::iter::once(&constant.type_).chain(constant.value.as_ref()) {
        let bytes = bincode::serde::encode_to_vec(part, bincode::config::standard())
            .expect("serialize helper dependency definition");
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    }
    hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn source_modules(root: &Path, directory: &Path, modules: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(directory).expect("read helper package directory") {
        let entry = entry.expect("helper package directory entry");
        let path = entry.path();
        let filename = entry.file_name();
        if filename.to_string_lossy().starts_with('.') {
            continue;
        }
        if entry.file_type().expect("helper file type").is_dir() {
            source_modules(root, &path, modules);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lean")
            && filename != "lakefile.lean"
        {
            let stem = path
                .strip_prefix(root)
                .expect("helper source inside package")
                .with_extension("");
            let module = stem
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, ".");
            assert!(modules.insert(module), "duplicate source module");
        }
    }
}

fn is_type_mismatch<T>(result: &Result<T, ReferenceRefusal>) -> bool {
    matches!(
        result,
        Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }))
    )
}

#[test]
fn sort_bounds_helpers_recheck_with_pins_and_refutations() {
    let lib = require_pinned_lean_lib_path().expect("install repository-pinned Lean");
    let compiled = compiled_fixture_dir("kcheck_sort_bounds");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("pinned Lean bin directory");
    let mut binary_paths = vec![bin.to_path_buf()];
    binary_paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", ROOT])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("pinned Lean search path"),
        )
        .env(
            "PATH",
            std::env::join_paths(binary_paths).expect("pinned Lean binary path"),
        )
        .output()
        .expect("run independent pinned Lean kernel");
    assert!(
        independent.status.success(),
        "leanchecker --fresh {ROOT}: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );

    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_sort_bounds");
    let order: Vec<String> = include_str!("../../../theories/kcheck_sort_bounds/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.replace('/', "."))
        .collect();
    let modules: BTreeSet<String> = order.iter().cloned().collect();
    assert_eq!(modules.len(), order.len(), "duplicate helper ORDER entry");
    assert!(
        modules.contains(ROOT),
        "ORDER must include the package root"
    );
    let mut sources = BTreeSet::new();
    source_modules(&package, &package, &mut sources);
    assert_eq!(modules, sources, "ORDER equals all helper source modules");

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("load helper compiled bytes");
    let loaded_modules: BTreeSet<String> = summaries
        .iter()
        .filter_map(|summary| summary.module_name.as_ref())
        .filter(|module| modules.contains(*module))
        .cloned()
        .collect();
    assert_eq!(modules, loaded_modules, "every helper ORDER module loaded");
    for summary in summaries.iter().filter(|summary| {
        summary
            .module_name
            .as_ref()
            .is_some_and(|module| modules.contains(module))
    }) {
        assert!(
            summary.skipped_not_replayable.is_empty(),
            "helper module {:?} skipped declarations: {:?}",
            summary.module_name,
            summary.skipped_not_replayable
        );
    }
    let targets: BTreeSet<Name> = loaded
        .constants()
        .filter(|constant| {
            loaded
                .get_constant_origin(&constant.name)
                .and_then(|origin| origin.module_name())
                .is_some_and(|module| modules.contains(module))
        })
        .map(|constant| constant.name.clone())
        .collect();
    let added_targets: BTreeSet<Name> = summaries
        .iter()
        .filter(|summary| {
            summary
                .module_name
                .as_ref()
                .is_some_and(|module| modules.contains(module))
        })
        .flat_map(|summary| summary.added_names.iter().cloned())
        .collect();
    assert_eq!(targets, added_targets, "origin census equals loaded names");
    let mut artifact_targets = BTreeSet::new();
    for module in &modules {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read helper artifact {module}: {error}"));
        for subject in artifact.names {
            assert!(
                artifact_targets.insert(subject.clone()),
                "{subject} declared by two helper artifacts"
            );
        }
    }
    assert_eq!(
        targets, artifact_targets,
        "every declaration in the helper artifacts is resident and selected"
    );
    assert!(!targets.is_empty(), "nonempty helper declaration census");
    for subject in &targets {
        let constant = loaded
            .get_const(subject)
            .expect("resident helper declaration");
        assert_ne!(constant.kind, ConstantKind::Axiom, "helper axiom {subject}");
        assert!(
            !loaded.is_unsafe(subject) && !loaded.is_partial(subject),
            "unsafe or partial helper declaration {subject}"
        );
    }
    // Canonical theorems are explicit roots as well as dependencies of the
    // caller witnesses; this does not alter the own-module census denominator.
    let mut replay_targets = targets.clone();
    let dependency_equations: BTreeSet<Name> = loaded
        .constants()
        .map(|constant| &constant.name)
        .filter(|subject| dependency_equation(subject))
        .cloned()
        .collect();
    assert!(
        !dependency_equations.is_empty(),
        "dependency equation census"
    );
    let mut artifact_equations = BTreeSet::new();
    for module in modules.iter().map(String::as_str).chain([
        "CICL.CoreTyping",
        "KCheckSpec.TermData",
        "KCheckSpec.Term",
        "KCheckSpec.Env",
    ]) {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read equation artifact {module}: {error}"));
        artifact_equations.extend(artifact.names.into_iter().filter(dependency_equation));
    }
    assert_eq!(
        dependency_equations, artifact_equations,
        "public dependency equations equal their compiled artifact census"
    );
    replay_targets.extend(dependency_equations.iter().cloned());
    for canonical in CANONICAL_HELPERS {
        let subject = name(canonical);
        let constant = loaded
            .get_const(&subject)
            .expect("canonical helper resident");
        assert_eq!(
            constant.kind,
            ConstantKind::Theorem,
            "{canonical} is a theorem"
        );
        assert!(!loaded.is_unsafe(&subject) && !loaded.is_partial(&subject));
        assert!(constant.level_params.is_empty(), "monomorphic {canonical}");
        assert!(
            replay_targets.insert(subject),
            "canonical helper is external to adjunct"
        );
    }
    let checked = reference_base_closed(&loaded, &replay_targets, &ClosedRecheckOptions::default())
        .expect("dependency-closed fenced helper replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    eprintln!("fenced-helper-replay {}", checked.report.verdict_sentence());
    let mut kernel = checked.into_kernel().expect("all fenced admissions passed");
    let meaning_package = Package::of_fixture(
        &compiled,
        "kcheck_sort_bounds",
        &["cic_l", "cic_l_model", "kcheck_spec", "kcheck_sort_bounds"],
    );
    let digests = MeaningDigests::new(kernel.environment(), &meaning_package);
    let meaning = |subject: &Name| -> String {
        digests
            .digest(subject)
            .unwrap_or_else(|error| panic!("{subject}: {error}"))
    };

    let allowed: BTreeSet<String> = [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let mut observed_closures = BTreeMap::new();
    let mut observed_pins = BTreeMap::new();
    for subject in &replay_targets {
        let environment = kernel.environment();
        let mut closure = environment
            .axiom_deps(subject)
            .expect("helper axiom closure");
        closure.extend(
            environment
                .foundational_axiom_deps(subject)
                .expect("helper foundational closure"),
        );
        let closure: BTreeSet<String> = closure.iter().map(ToString::to_string).collect();
        assert!(closure.is_subset(&allowed), "{subject}: {closure:?}");
        observed_closures.insert(subject.to_string(), closure);
        let constant = loaded
            .get_const(subject)
            .expect("resident helper declaration");
        if constant.kind == ConstantKind::Theorem {
            observed_pins.insert(subject.to_string(), meaning(subject));
        }
    }
    let statement = |short: &str| -> Expr {
        loaded
            .get_const(&contract_name(short))
            .unwrap_or_else(|| panic!("missing helper contract {short}"))
            .value
            .clone()
            .unwrap_or_else(|| panic!("helper contract {short} has no value"))
    };
    let contract_names: BTreeSet<&str> = CONTRACTS
        .iter()
        .chain(FORGED_STATEMENTS)
        .map(|(_, pin)| *pin)
        .collect();
    assert_eq!(
        contract_names.len(),
        9,
        "all standalone and forged contracts retained"
    );
    for short in contract_names {
        assert!(
            observed_pins
                .insert(
                    contract_name(short).to_string(),
                    meaning(&contract_name(short))
                )
                .is_none(),
            "duplicate contract {short}"
        );
    }
    // The canonical proof values, not only their statement expressions, are
    // bound here. Their statement-only pins and closures were collected above.
    for dependency in DEPENDENCY_DEFINITIONS.iter().chain(CANONICAL_HELPERS) {
        let constant = loaded
            .get_const(&name(dependency))
            .unwrap_or_else(|| panic!("missing helper dependency {dependency}"));
        assert!(constant.value.is_some(), "{dependency} is a definition");
        assert!(
            observed_pins
                .insert(
                    if CANONICAL_HELPERS.contains(dependency) {
                        format!("{dependency}::type-and-value")
                    } else {
                        (*dependency).to_owned()
                    },
                    if CANONICAL_HELPERS.contains(dependency) {
                        constant_digest(constant)
                    } else {
                        meaning(&name(dependency))
                    },
                )
                .is_none(),
            "duplicate dependency pin {dependency}"
        );
    }
    for (subject, closure) in &observed_closures {
        let origin = loaded
            .get_constant_origin(&name(subject))
            .and_then(|origin| origin.module_name())
            .expect("replay subject has compiled module origin");
        eprintln!("origin-subject {subject} {origin}");
        eprintln!(
            "axiom-closure {subject} {}",
            serde_json::to_string(closure).expect("closure JSON")
        );
    }
    for (subject, pin) in &observed_pins {
        eprintln!("statement-pin {subject} {pin}");
    }
    let roots: Vec<Name> = replay_targets.iter().cloned().collect();
    eprintln!(
        "{}",
        digests
            .describe(&meaning_package, &roots)
            .unwrap_or_else(|error| panic!("{error}"))
    );
    drop(digests);
    let committed_closures: BTreeMap<String, BTreeSet<String>> = serde_json::from_str(
        include_str!("../../../theories/kcheck_sort_bounds/axiom_closures.json"),
    )
    .expect("committed helper closures");
    let committed_pins: BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../theories/kcheck_sort_bounds/statement_pins.json"
    ))
    .expect("committed helper statements");
    assert_eq!(
        observed_closures, committed_closures,
        "exact helper axiom census"
    );
    if let Err(failure) = meaning_digest::check_pins(
        &observed_pins,
        &committed_pins,
        "theories/kcheck_sort_bounds/statement_pins.json",
    ) {
        panic!("all helper theorem statements pinned: {failure}");
    }

    let mut control_names = BTreeSet::new();
    for (short, contract) in CONTRACTS {
        let control = format!("{}_at_{contract}", short.replace('.', "_"));
        assert!(
            control_names.insert(control.clone()),
            "duplicate proof/contract control"
        );
        let subject = theorem_name(short);
        assert!(
            targets.contains(&subject),
            "headline theorem {subject} is a subject"
        );
        let proof = loaded.get_const(&subject).expect("helper theorem");
        assert_eq!(proof.kind, ConstantKind::Theorem, "{subject} is a theorem");
        assert!(
            proof.level_params.is_empty(),
            "{subject} has no universe parameters"
        );
        let value = proof.value.clone().expect("helper theorem proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheckSortBounds.Recheck.{control}")),
                level_params: vec![],
                type_: statement(contract),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{subject} at {contract}: {refusal:?}"));
        let false_proof = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckSortBounds.Recheck.{control}_false")),
            level_params: vec![],
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&false_proof),
            "{subject} cannot prove False: {false_proof:?}"
        );
    }
    for (short, contract) in FORGED_STATEMENTS {
        let control = format!("{}_at_{contract}", short.replace('.', "_"));
        assert!(
            control_names.insert(control.clone()),
            "duplicate forged control"
        );
        let proof = loaded
            .get_const(&theorem_name(short))
            .expect("helper proof");
        let forged = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckSortBounds.Recheck.{control}")),
            level_params: vec![],
            type_: statement(contract),
            value: proof.value.clone().expect("helper theorem proof"),
        });
        assert!(
            is_type_mismatch(&forged),
            "{short} cannot prove forged {contract}: {forged:?}"
        );
    }
    eprintln!(
        "sort-bounds subjects {}, dependency equations {}, canonical roots {}, replay subjects {}, modules {}, proof/contract controls {}, forged controls {}",
        targets.len(),
        dependency_equations.len(),
        CANONICAL_HELPERS.len(),
        replay_targets.len(),
        modules.len(),
        CONTRACTS.len(),
        FORGED_STATEMENTS.len()
    );
}
