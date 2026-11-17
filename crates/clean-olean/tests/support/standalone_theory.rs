// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared full-ORDER qualification for the two fresh S2 proof packages.
//! Uses the maintained compiler, loader, meaning digest and fenced closed entry.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{ConstantInfo, ConstantKind, Declaration, Environment};
use clean_kernel::{
    Expr, ExprFolder, ExprKind, KernelEnvError, KernelTypeError, LevelVec, Name, ReferenceRefusal,
    TypeChecker,
};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use sha2::{Digest, Sha256};

#[path = "meaning_digest.rs"]
mod meaning_digest;
use meaning_digest::{MeaningDigests, Package as MeaningPackage};

pub enum Change {
    DeleteBinder(u32),
    // This shared helper is compiled separately for each standalone test;
    // the Eq-header package uses binder deletions only.
    #[allow(dead_code)]
    ReplaceConstant(&'static str, &'static str),
}

pub struct Mutation {
    pub proof: &'static str,
    pub literal: &'static str,
    pub change: Change,
}

pub struct Package {
    pub family: &'static str,
    pub source_root: &'static str,
    pub fixture_root: &'static str,
    pub theories: &'static [&'static str],
    pub fixture_modules: &'static [&'static str],
    pub module_count: usize,
    pub lake_includes_root: bool,
    pub root_imports_init: bool,
    pub mint_env: &'static str,
    pub contract_pairs: &'static str,
    pub contract_count: usize,
    pub data_pairs: &'static [(&'static str, &'static str)],
    pub mutations: &'static [Mutation],
    pub dependencies: &'static [&'static str],
}

fn name(text: &str) -> Name {
    Name::from_string(text)
}

// These are roster metadata, not the meaning of a kernel constant. Every
// semantic constant pin below uses the maintained MeaningDigests implementation.
fn metadata_digest<T: serde::Serialize>(value: &T) -> String {
    let bytes = bincode::serde::encode_to_vec(value, bincode::config::standard())
        .expect("serialize qualification pin");
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn closure(environment: &Environment, subject: &Name) -> BTreeSet<String> {
    let mut result = environment
        .axiom_deps(subject)
        .expect("subject axiom closure");
    result.extend(
        environment
            .foundational_axiom_deps(subject)
            .expect("subject foundational closure"),
    );
    result.iter().map(ToString::to_string).collect()
}

fn type_mismatch<T>(result: &Result<T, ReferenceRefusal>) -> bool {
    matches!(
        result,
        Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }))
    )
}

fn source_modules(root: &Path, directory: &Path, modules: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(directory).expect("read package source directory") {
        let entry = entry.expect("package source entry");
        if entry.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        let path = entry.path();
        let kind = entry.file_type().expect("package source file type");
        assert!(!kind.is_symlink(), "source symlink: {}", path.display());
        if kind.is_dir() {
            source_modules(root, &path, modules);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lean")
            && entry.file_name() != "lakefile.lean"
        {
            let module = path
                .strip_prefix(root)
                .expect("package source path")
                .with_extension("")
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, ".");
            assert!(modules.insert(module), "duplicate source module");
        }
    }
}

fn erase_binder(expression: &Expr, index: u32) -> Expr {
    let ExprKind::Pi(binder, domain, body) = expression.kind() else {
        panic!("mutation binder index exceeds original telescope")
    };
    if index == 0 {
        assert!(
            !body.has_loose_bvar(0),
            "deleted premise is used in the remaining type"
        );
        // The absent variable is substituted only to lower the outer indices.
        body.instantiate(&Expr::prop())
    } else {
        Expr::pi(*binder, (**domain).clone(), erase_binder(body, index - 1))
    }
}

struct ReplaceConstant<'a> {
    old: &'a Name,
    new: &'a Name,
}
impl ExprFolder for ReplaceConstant<'_> {
    fn fold_const(&mut self, constant: &Name, levels: &LevelVec) -> Expr {
        Expr::const_(
            if constant == self.old {
                self.new.clone()
            } else {
                constant.clone()
            },
            levels.clone(),
        )
    }
}

fn changed_type(proof: &ConstantInfo, change: &Change) -> Expr {
    match change {
        Change::DeleteBinder(index) => erase_binder(&proof.type_, *index),
        Change::ReplaceConstant(old, new) => {
            let (old, new) = (name(old), name(new));
            let changed = ReplaceConstant {
                old: &old,
                new: &new,
            }
            .fold_expr(&proof.type_);
            assert_ne!(
                changed, proof.type_,
                "declared constant mutation changes nothing"
            );
            changed
        }
    }
}

fn dependency_auxiliary(definition: &str, candidate: &ConstantInfo) -> bool {
    let text = candidate.name.to_string();
    let Some(suffix) = text.strip_prefix(&format!("{definition}.")) else {
        return false;
    };
    candidate.kind != ConstantKind::Theorem
        || ["eq_", "_eq_", "_proof_", "_match_", "match_"]
            .iter()
            .any(|prefix| suffix.starts_with(prefix))
}

/// The complete compiled graph of these mixed fixture families. The maintained
/// `of_fixture` intentionally accepts theory-only ORDERs; these also compile
/// independent literal modules, so validate the full recipe and use of_modules.
fn meaning_package(config: &Package, compiled: &Path) -> MeaningPackage {
    let fixture_order = clean_olean::test_support::fixture_root()
        .join(config.family)
        .join("ORDER");
    let fixture_text = std::fs::read_to_string(&fixture_order).expect("fixture ORDER");
    let observed: Vec<&str> = fixture_text
        .lines()
        .map(str::trim)
        .filter(|row| !row.is_empty() && !row.starts_with('#'))
        .collect();
    let expected: Vec<String> = config
        .theories
        .iter()
        .map(|theory| format!("theory {theory}"))
        .chain(
            config
                .fixture_modules
                .iter()
                .map(|module| (*module).to_owned()),
        )
        .collect();
    assert_eq!(
        observed,
        expected.iter().map(String::as_str).collect::<Vec<_>>(),
        "the complete meaning scope is the actual unchanged mixed fixture recipe"
    );
    assert_eq!(
        config.theories.last().copied(),
        Some(config.family),
        "the owned package is the final theory in the fixture graph"
    );
    let theories_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories");
    let mut modules = Vec::new();
    for theory in config.theories {
        let order = std::fs::read_to_string(theories_root.join(theory).join("ORDER"))
            .expect("meaning-scope theory ORDER");
        modules.extend(
            order
                .lines()
                .map(str::trim)
                .filter(|row| !row.is_empty() && !row.starts_with('#'))
                .map(|module| module.replace('/', ".")),
        );
        let aggregate = format!("CleanQualification.{theory}");
        let artifact = read_artifact(
            &aggregate,
            &compiled.join(format!("{}.olean", aggregate.replace('.', "/"))),
            ArtifactDepth::Records,
        )
        .unwrap_or_else(|error| panic!("read meaning-scope aggregate {aggregate}: {error}"));
        assert!(
            artifact.names.is_empty(),
            "meaning-scope aggregate {aggregate} declares names"
        );
        modules.push(aggregate);
    }
    modules.extend(
        config
            .fixture_modules
            .iter()
            .map(|module| module.replace('/', ".")),
    );
    let unique: BTreeSet<&String> = modules.iter().collect();
    assert_eq!(
        unique.len(),
        modules.len(),
        "duplicate meaning-scope module"
    );
    MeaningPackage::of_modules(compiled, modules)
}

pub fn qualify(config: &Package) {
    let package = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../theories")
        .join(config.family);
    let order: Vec<String> = std::fs::read_to_string(package.join("ORDER"))
        .expect("package ORDER")
        .lines()
        .map(str::trim)
        .filter(|row| !row.is_empty() && !row.starts_with('#'))
        .map(|row| row.replace('/', "."))
        .collect();
    assert_eq!(
        order.len(),
        config.module_count,
        "complete owned ORDER denominator"
    );
    let modules: BTreeSet<String> = order.iter().cloned().collect();
    assert_eq!(modules.len(), order.len(), "duplicate package ORDER module");
    let mut sources = BTreeSet::new();
    source_modules(&package, &package, &mut sources);
    let mut expected_sources = modules.clone();
    assert!(
        expected_sources.insert(config.source_root.to_owned()),
        "root already in ORDER"
    );
    assert_eq!(
        sources, expected_sources,
        "ORDER plus import-only root equals every package Lean source"
    );
    let lake: toml::Value = toml::from_str(
        &std::fs::read_to_string(package.join("lakefile.toml")).expect("package lakefile"),
    )
    .expect("parse package lakefile");
    let roots: Vec<String> = lake["lean_lib"][0]["roots"]
        .as_array()
        .expect("explicit Lake roots")
        .iter()
        .map(|value| value.as_str().expect("Lake module root").to_owned())
        .collect();
    let mut expected_roots = order.clone();
    if config.lake_includes_root {
        expected_roots.push(config.source_root.to_owned());
    }
    assert_eq!(roots, expected_roots, "exact Lake roots and owned ORDER");

    let lib = require_pinned_lean_lib_path().expect("install repository-pinned Lean toolchain");
    let compiled = compiled_fixture_dir(config.family);
    let meaning_package = meaning_package(config, &compiled);
    let aggregate = format!("CleanQualification.{}", config.family);
    for empty_root in [aggregate.as_str(), config.source_root, config.fixture_root] {
        let artifact = read_artifact(
            empty_root,
            &compiled.join(format!("{}.olean", empty_root.replace('.', "/"))),
            ArtifactDepth::Records,
        )
        .unwrap_or_else(|error| panic!("read import-only root {empty_root}: {error}"));
        assert!(
            artifact.names.is_empty(),
            "import-only root {empty_root} declares names"
        );
        if empty_root != config.fixture_root {
            let mut expected_imports = Vec::new();
            if empty_root == config.source_root && config.root_imports_init {
                expected_imports.extend(["Init".to_owned(), "Init".to_owned()]);
            }
            expected_imports.extend(order.iter().cloned());
            assert_eq!(
                artifact
                    .imports
                    .iter()
                    .map(|import| import.module_name.clone())
                    .collect::<Vec<_>>(),
                expected_imports,
                "{empty_root} imports the entire exact ORDER in order"
            );
        }
    }
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("pinned Lean bin directory");
    let mut binary_paths = vec![bin.to_path_buf()];
    binary_paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let fresh = Command::new(bin.join("leanchecker"))
        .args(["--fresh", config.fixture_root])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean path"),
        )
        .env(
            "PATH",
            std::env::join_paths(binary_paths).expect("pinned binary path"),
        )
        .output()
        .expect("independent fresh Lean replay");
    assert!(
        fresh.status.success(),
        "fresh {}: {}\n{}",
        config.fixture_root,
        String::from_utf8_lossy(&fresh.stdout),
        String::from_utf8_lossy(&fresh.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries =
        load_module_with_deps(&mut loaded, config.fixture_root, &[compiled.clone(), lib])
            .expect("load full fixture closure");
    let loaded_modules: BTreeSet<String> = summaries
        .iter()
        .filter_map(|summary| summary.module_name.as_ref())
        .filter(|module| modules.contains(*module))
        .cloned()
        .collect();
    assert_eq!(loaded_modules, modules, "every owned ORDER module loaded");
    let not_replayable: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let mut raw_owners = BTreeMap::new();
    let mut targets = BTreeSet::new();
    let mut compiler_copies = BTreeSet::new();
    for module in &order {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Records,
        )
        .unwrap_or_else(|error| panic!("read complete owned artifact {module}: {error}"));
        assert!(
            !artifact.names.is_empty(),
            "owned ORDER module {module} declares no names"
        );
        for subject in artifact.names {
            assert!(
                raw_owners
                    .insert(subject.to_string(), module.clone())
                    .is_none(),
                "duplicate owner {subject}"
            );
            if loaded.get_const(&subject).is_none() {
                let text = subject.to_string();
                assert!(
                    text.ends_with("._unsafe_rec") && not_replayable.contains(text.as_str()),
                    "absent declaration is not an artifact-marked compiler copy: {subject}"
                );
                compiler_copies.insert(text);
                continue;
            }
            assert!(
                !loaded.is_unsafe(&subject) && !loaded.is_partial(&subject),
                "unsafe/partial owned declaration {subject}"
            );
            assert_eq!(
                loaded
                    .get_constant_origin(&subject)
                    .and_then(|origin| origin.module_name()),
                Some(module.as_str()),
                "physical and loaded origin of {subject}"
            );
            assert!(targets.insert(subject), "owned declaration repeated");
        }
    }
    for copy in &compiler_copies {
        let original = copy
            .strip_suffix("._unsafe_rec")
            .expect("compiler-copy suffix");
        assert!(
            targets.contains(&name(original)),
            "compiler copy lacks owned safe original: {copy}"
        );
    }
    let reverse: BTreeSet<Name> = loaded
        .constants()
        .filter(|constant| {
            loaded
                .get_constant_origin(&constant.name)
                .and_then(|origin| origin.module_name())
                .is_some_and(|origin| modules.contains(origin))
        })
        .map(|constant| constant.name.clone())
        .collect();
    assert_eq!(
        reverse, targets,
        "every resident owned declaration has one physical owner"
    );
    assert!(!targets.is_empty(), "empty owned declaration census");
    let theorem_targets: BTreeSet<Name> = targets
        .iter()
        .filter(|subject| {
            loaded.get_const(subject).expect("owned declaration").kind == ConstantKind::Theorem
        })
        .cloned()
        .collect();

    let contracts: Vec<(String, String)> =
        serde_json::from_str(config.contract_pairs).expect("independent contract table");
    assert_eq!(
        contracts.len(),
        config.contract_count,
        "independent full-statement denominator"
    );
    let public_proofs: BTreeSet<Name> = contracts.iter().map(|(proof, _)| name(proof)).collect();
    assert_eq!(
        public_proofs.len(),
        contracts.len(),
        "duplicate public contract proof"
    );
    let public_proof_names: HashSet<Name> = public_proofs.iter().cloned().collect();
    assert!(
        public_proofs.is_subset(&theorem_targets),
        "every public proof is owned"
    );
    let mut replay_targets = targets.clone();
    let mut dependency_groups = BTreeMap::new();
    for definition in config.dependencies {
        let root = name(definition);
        assert!(
            loaded.get_const(&root).is_some(),
            "missing meaning dependency {definition}"
        );
        let mut group: Vec<Name> = loaded
            .constants()
            .filter(|candidate| {
                candidate.name == root || dependency_auxiliary(definition, candidate)
            })
            .filter(|candidate| {
                !loaded.is_unsafe(&candidate.name) && !loaded.is_partial(&candidate.name)
            })
            .map(|candidate| candidate.name.clone())
            .collect();
        group.sort();
        assert!(
            group.contains(&root),
            "unsafe/partial meaning dependency {definition}"
        );
        replay_targets.extend(group.iter().cloned());
        assert!(
            dependency_groups.insert(*definition, group).is_none(),
            "duplicate meaning group"
        );
    }
    for (_, literal) in &contracts {
        replay_targets.insert(name(literal));
    }
    for mutation in config.mutations {
        assert!(
            theorem_targets.contains(&name(mutation.proof)),
            "mutation proof must be owned"
        );
        replay_targets.insert(name(mutation.literal));
    }
    for (actual, literal) in config.data_pairs {
        assert!(targets.contains(&name(actual)), "actual data must be owned");
        replay_targets.insert(name(literal));
    }
    let checked = reference_base_closed(&loaded, &replay_targets, &ClosedRecheckOptions::default())
        .expect("dependency-closed fenced qualification replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    let mut kernel = checked.into_kernel().expect("all fenced admissions passed");
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
    for subject in &replay_targets {
        let row = closure(kernel.environment(), subject);
        assert!(
            row.is_subset(&allowed),
            "choice-free closure of {subject}: {row:?}"
        );
        observed_closures.insert(subject.to_string(), row);
    }
    let (mut observed_pins, meaning_description) = {
        let digests = MeaningDigests::new(kernel.environment(), &meaning_package);
        let mut pins = BTreeMap::new();
        for subject in &replay_targets {
            let pin = digests
                .digest(subject)
                .unwrap_or_else(|error| panic!("{error}"));
            assert!(
                pins.insert(subject.to_unambiguous_string(), pin).is_none(),
                "duplicate meaning pin"
            );
        }
        let roots: Vec<Name> = replay_targets.iter().cloned().collect();
        let described = digests
            .describe(&meaning_package, &roots)
            .unwrap_or_else(|error| panic!("{error}"));
        (pins, described)
    };
    assert!(
        observed_pins
            .insert(
                "::raw-module-ownership".to_owned(),
                metadata_digest(&raw_owners)
            )
            .is_none(),
        "ownership metadata key collides with a semantic pin"
    );
    assert!(
        observed_pins
            .insert(
                "::artifact-marked-compiler-copies".to_owned(),
                metadata_digest(&compiler_copies),
            )
            .is_none(),
        "compiler-copy metadata key collides with a semantic pin"
    );
    assert!(
        observed_pins
            .insert(
                "::meaning-package-modules".to_owned(),
                metadata_digest(&meaning_package.modules()),
            )
            .is_none(),
        "meaning-scope metadata key collides with a semantic pin"
    );
    for (definition, group) in dependency_groups {
        // Keep exactly the previous selected auxiliary population. Each member
        // already has a full transitive meaning pin above; this row binds the
        // selection itself, rather than reviving a shallow ConstantInfo digest.
        assert!(
            observed_pins
                .insert(
                    format!("{definition}::selected-meaning-roots"),
                    metadata_digest(&group),
                )
                .is_none(),
            "meaning-group metadata key collides with an existing pin"
        );
    }
    assert_eq!(
        observed_pins.len(),
        replay_targets.len() + 3 + config.dependencies.len(),
        "every semantic root and exact metadata roster must retain its pin"
    );
    eprintln!("{meaning_description}");

    for (index, subject) in theorem_targets.iter().enumerate() {
        let theorem = loaded.get_const(subject).expect("owned theorem");
        let body = theorem.value.clone().expect("original theorem body");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!(
                    "StandaloneQualification.{}.original_{index}",
                    config.family
                )),
                level_params: theorem.level_params.clone(),
                type_: theorem.type_.clone(),
                value: body.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{subject} original body: {refusal:?}"));
        let refused = kernel.add_checked(Declaration::Theorem {
            name: name(&format!(
                "StandaloneQualification.{}.false_{index}",
                config.family
            )),
            level_params: theorem.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value: body,
        });
        assert!(
            type_mismatch(&refused),
            "{subject} at False must fail by type mismatch: {refused:?}"
        );
    }
    for (index, (proof_name, literal_name)) in contracts.iter().enumerate() {
        let proof = loaded
            .get_const(&name(proof_name))
            .expect("public contract theorem");
        let literal = loaded
            .get_const(&name(literal_name))
            .expect("independent full proposition");
        assert_eq!(
            literal.kind,
            ConstantKind::Definition,
            "independent proposition definition"
        );
        assert!(
            TypeChecker::new(kernel.environment()).is_def_eq(&literal.type_, &Expr::prop()),
            "independent contract has type Prop"
        );
        assert_eq!(
            proof.level_params, literal.level_params,
            "complete contract LP {proof_name}"
        );
        let statement = literal.value.clone().expect("independent proposition body");
        let mut used = HashSet::new();
        statement.used_constants_dag(
            clean_kernel::expr::UsedConstants::WithProjectionStructures,
            &mut used,
        );
        assert!(
            used.is_disjoint(&public_proof_names),
            "literal uses implementation public proof"
        );
        assert!(
            TypeChecker::new(kernel.environment()).is_def_eq(&proof.type_, &statement),
            "full independent proposition {proof_name}"
        );
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!(
                    "StandaloneQualification.{}.literal_{index}",
                    config.family
                )),
                level_params: proof.level_params.clone(),
                type_: statement,
                value: proof.value.clone().expect("public proof body"),
            })
            .unwrap_or_else(|refusal| {
                panic!("{proof_name} at independent full literal: {refusal:?}")
            });
    }
    for (actual_name, literal_name) in config.data_pairs {
        let actual = loaded
            .get_const(&name(actual_name))
            .expect("actual data definition");
        let literal = loaded
            .get_const(&name(literal_name))
            .expect("independent rebuilt data definition");
        assert_eq!(
            actual.kind,
            ConstantKind::Definition,
            "actual data definition kind"
        );
        assert_eq!(
            literal.kind,
            ConstantKind::Definition,
            "literal data definition kind"
        );
        assert_eq!(
            actual.level_params, literal.level_params,
            "data LP {actual_name}"
        );
        let mut used = HashSet::new();
        literal
            .value
            .as_ref()
            .expect("literal data body")
            .used_constants_dag(
                clean_kernel::expr::UsedConstants::WithProjectionStructures,
                &mut used,
            );
        assert!(
            config
                .data_pairs
                .iter()
                .all(|(actual, _)| !used.contains(&name(actual)))
                && public_proofs.iter().all(|proof| !used.contains(proof)),
            "rebuilt data uses implementation subject"
        );
        let tc = TypeChecker::new(kernel.environment());
        assert!(
            tc.is_def_eq(&actual.type_, &literal.type_),
            "independent data type {actual_name}"
        );
        assert!(
            tc.is_def_eq(
                actual.value.as_ref().expect("actual data body"),
                literal.value.as_ref().expect("literal data body")
            ),
            "independent data value {actual_name}"
        );
    }
    for (index, mutation) in config.mutations.iter().enumerate() {
        let proof = loaded
            .get_const(&name(mutation.proof))
            .expect("exact control proof");
        let literal = loaded
            .get_const(&name(mutation.literal))
            .expect("exact mutation literal");
        assert_eq!(proof.level_params, literal.level_params, "mutation LP");
        let statement = literal
            .value
            .clone()
            .expect("complete mutation proposition");
        let changed = changed_type(proof, &mutation.change);
        assert!(
            TypeChecker::new(kernel.environment()).is_def_eq(&changed, &statement),
            "mutation changes only the declared binder/constant"
        );
        let refused = kernel.add_checked(Declaration::Theorem {
            name: name(&format!(
                "StandaloneQualification.{}.mutation_{index}",
                config.family
            )),
            level_params: proof.level_params.clone(),
            type_: statement,
            value: proof.value.clone().expect("original mutated proof body"),
        });
        assert!(
            type_mismatch(&refused),
            "{} exact mutation must fail by type mismatch: {refused:?}",
            mutation.proof
        );
    }
    // Mint only after every required positive and negative check completed.
    // Missing observations are an ordinary default failure, never an empty pin.
    if std::env::var_os(config.mint_env).is_some() {
        for (file, value) in [
            (
                "statement_pins.json",
                serde_json::to_value(&observed_pins).expect("pin JSON"),
            ),
            (
                "axiom_closures.json",
                serde_json::to_value(&observed_closures).expect("closure JSON"),
            ),
        ] {
            std::fs::write(
                package.join(file),
                serde_json::to_string_pretty(&value).expect("observed JSON") + "\n",
            )
            .expect("write actual observed qualification pins");
        }
    }
    let committed_pins: BTreeMap<String, String> = serde_json::from_str(
        &std::fs::read_to_string(package.join("statement_pins.json"))
            .expect("actual successful pin mint is required"),
    )
    .expect("committed statement/meaning pins");
    let committed_closures: BTreeMap<String, BTreeSet<String>> = serde_json::from_str(
        &std::fs::read_to_string(package.join("axiom_closures.json"))
            .expect("actual successful closure mint is required"),
    )
    .expect("committed axiom closures");
    assert_eq!(
        observed_pins, committed_pins,
        "complete exact statement/body/LP/meaning pins"
    );
    assert_eq!(
        observed_closures, committed_closures,
        "complete exact choice-free axiom census"
    );
    eprintln!("standalone {} modules {} raw {} safe_owned {} theorem_body_false {} compiler_copies {} full_literals {} data_literals {} exact_mutations {} replay_roots {}",
        config.family, modules.len(), raw_owners.len(), targets.len(), theorem_targets.len(),
        compiler_copies.len(), contracts.len(), config.data_pairs.len(), config.mutations.len(), replay_targets.len());
}
