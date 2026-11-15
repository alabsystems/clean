// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The set model (plan units M1 to M3): groundwork, one semantic lemma per
//! core rule, and `sound_N` with its witness, each re-entered at a pinned contract.
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{load_module_with_deps, reference_base_closed, require_pinned_lean_lib_path};

/// One semantic lemma per constructor of `CICL.CoreJudgmentIn` (plan unit M2):
/// `CICL.Model.CoreRules.<rule>` re-entered at `CICL.Model.Contracts.<contract>`.
/// The test requires this table to name every constructor exactly once.
const CORE_RULE_CONTRACTS: [(&str, &str); 25] = [
    ("sort", "ruleSort"),
    ("sortCong", "ruleSortCong"),
    ("bvar", "ruleBvar"),
    ("constant", "ruleConstant"),
    ("pi", "rulePi"),
    ("lam", "ruleLam"),
    ("app", "ruleApp"),
    ("letE", "ruleLetE"),
    ("mdata", "ruleMdata"),
    ("convert", "ruleConvert"),
    ("eqConvert", "ruleEqConvert"),
    ("refl", "ruleRefl"),
    ("symm", "ruleSymm"),
    ("trans", "ruleTrans"),
    ("beta", "ruleBeta"),
    ("zeta", "ruleZeta"),
    ("zetaLocal", "ruleZetaLocal"),
    ("delta", "ruleDelta"),
    ("metadata", "ruleMetadata"),
    ("proofIrrel", "ruleProofIrrel"),
    ("eta", "ruleEta"),
    ("piCong", "rulePiCong"),
    ("lamCong", "ruleLamCong"),
    ("appCong", "ruleAppCong"),
    ("letCong", "ruleLetCong"),
];

/// Plan units M1, M3 and M4, and M2's rule-level `Type : Type` refutation.
const CORE_MODEL_CONTRACTS: [(&str, &str); 49] = [
    ("KCheckSpec.Base.natRecDen_zero", "natRecursorZero"),
    ("KCheckSpec.Base.natRecDen_succ", "natRecursorSucc"),
    ("CICL.Model.Formula.falsity_false", "quotationFalse"),
    ("CICL.Model.Formula.identity_holds", "quotationImplication"),
    ("CICL.Model.Formula.equality_holds", "quotationEquality"),
    ("CICL.Model.Formula.universal_holds", "quotationUniversal"),
    ("CICL.Model.imaxValue_values", "imaxValues"),
    ("CICL.Model.imaxValue_eval", "imaxEvaluation"),
    ("CICL.Model.imaxValue_le", "imaxBound"),
    (
        "CICL.Model.SetValue.tracePi_congr",
        "tracePiDomainCongruence",
    ),
    (
        "CICL.Model.SetValue.traceLambda_congr",
        "traceLambdaDomainCongruence",
    ),
    ("CICL.Model.SetValue.sortValue_tracePi_mem", "sortProducts"),
    ("CICL.Model.CoreTower.closure", "coreTowerClosure"),
    (
        "CICL.Model.CoreRules.sort_bound_off_by_one_refuted",
        "sortBoundOffByOneRefuted",
    ),
    (
        "CICL.Model.RawEvaluation.statementMeaning_hasType",
        "statementTyping",
    ),
    (
        "CICL.Model.RawEvaluation.statementMeaning_defEq",
        "statementEquality",
    ),
    (
        "CICL.Model.RawEvaluation.LevelPolicy.within_sort",
        "boundedSortPolicy",
    ),
    (
        "CICL.Model.RawEvaluation.LevelPolicy.within_constant",
        "boundedConstantPolicy",
    ),
    ("CICL.Model.RawEvaluation.sound_N", "soundN"),
    (
        "CICL.Model.RawEvaluation.valid_assignment_exists",
        "validAssignmentExists",
    ),
    ("CICL.Model.RawEvaluation.consistent_N", "consistentN"),
    (
        "CICL.Model.RawEvaluation.WfSignatureWithin.no_axiom",
        "boundedSignatureNoAxiom",
    ),
    (
        "CICL.Model.Witness.witnessSignature_contents",
        "witnessSignatureContents",
    ),
    ("CICL.Model.Witness.witnessBound_values", "witnessBounds"),
    (
        "CICL.Model.Witness.badSignature_contents",
        "axiomSignatureContents",
    ),
    ("CICL.Model.Witness.witness_wf", "witnessWellFormed"),
    ("CICL.Model.Witness.witness_typed", "witnessTyped"),
    (
        "CICL.Model.Witness.witness_constant_typed",
        "witnessConstantTyped",
    ),
    ("CICL.Model.Witness.witness_proves", "witnessProves"),
    ("CICL.Model.Witness.witness_assignment", "witnessAssignment"),
    ("CICL.Model.Witness.witness_consistent", "witnessConsistent"),
    (
        "CICL.Model.Witness.witness_refuses_axiom",
        "witnessRefusesAxiom",
    ),
    (
        "CICL.Model.Witness.bad_signature_proves_falsity",
        "axiomSignatureProvesFalsity",
    ),
    (
        "CICL.Model.Witness.consistency_needs_noAxiom",
        "consistencyNeedsNoAxiom",
    ),
    ("CICL.Model.BaseInterpretation.typed", "baseTyped"),
    (
        "CICL.Model.BaseInterpretation.typed_index",
        "baseTypedIndex",
    ),
    ("CICL.Model.BaseWitness.base_signature_wf", "baseWellFormed"),
    (
        "CICL.Model.BaseWitness.base_signature_assignment",
        "baseAssignment",
    ),
    ("CICL.Model.BaseWitness.base_refl_typed", "baseReflTyped"),
    ("CICL.Model.BaseWitness.base_refl_proves", "baseReflProves"),
    (
        "CICL.Model.BaseWitness.base_signature_consistent",
        "baseConsistent",
    ),
    (
        "CICL.Model.BaseWitness.base_bound_of_wf",
        "baseBoundInherited",
    ),
    (
        "CICL.Model.BaseWitness.zero_nat_bound_refused",
        "baseZeroNatBoundRefused",
    ),
    (
        "CICL.Model.BaseWitness.base_signature_refuses_axiom",
        "baseRefusesAxiom",
    ),
    (
        "CICL.Model.BaseWitness.bad_signature_proves_falsity",
        "baseAxiomProvesFalsity",
    ),
    (
        "CICL.Model.BaseWitness.consistency_needs_axiom_refusal",
        "baseConsistencyNeedsAxiomRefusal",
    ),
    ("KCheckSpec.Base.eqRecDen_apply", "baseEqComputation"),
    ("KCheckSpec.Base.punitRecDen_apply", "basePUnitComputation"),
    ("KCheckSpec.Base.natRecDen_apply", "baseNatComputation"),
];

/// The hex SHA-256 of one model contract's proof value, for the untrusted pin
/// observations the contract test prints; the replay after them decides.
fn observed_value_digest(value: &Expr) -> String {
    let bytes = bincode::serde::encode_to_vec(value, bincode::config::standard())
        .expect("observed model proposition bytes");
    Sha256::digest(&bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

// Shared by the actual Model replay gate and the adversarial census controls.
// The default policy stays choice-free; the production caller supplies only
// the exact named exceptions already committed by plan decision 12.
fn model_axiom_census(env: &Environment, subject: &Name) -> Result<BTreeSet<String>, String> {
    model_axiom_census_with_exceptions(env, subject, &BTreeSet::new())
        .map(|names| names.iter().map(ToString::to_string).collect())
}

fn model_axiom_census_with_exceptions(
    env: &Environment,
    subject: &Name,
    choice_exceptions: &BTreeSet<Name>,
) -> Result<BTreeSet<Name>, String> {
    let info = env
        .get_const(subject)
        .ok_or_else(|| format!("missing model declaration: {subject}"))?;
    let axiom_root = info.kind == clean_kernel::env::ConstantKind::Axiom;
    // Dependency closure omits the subject itself: an unused axiom must not
    // disappear, even when no declaration refers to it.
    if axiom_root && !env.is_canonical_foundational_axiom(subject) {
        return Err(format!(
            "noncanonical model axiom root: {}",
            subject.to_unambiguous_string()
        ));
    }
    let domain = env
        .axiom_deps(subject)
        .ok_or_else(|| format!("missing model declaration: {subject}"))?;
    if !domain.is_empty() {
        return Err(format!(
            "{}: domain axioms {:?}",
            subject.to_unambiguous_string(),
            domain
                .iter()
                .map(Name::to_unambiguous_string)
                .collect::<BTreeSet<_>>()
        ));
    }
    let mut foundations = env
        .foundational_axiom_deps(subject)
        .ok_or_else(|| format!("missing axiom closure: {subject}"))?;
    if axiom_root {
        foundations.insert(subject.clone());
    }
    let mut allowed: BTreeSet<Name> = [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
    ]
    .into_iter()
    .map(Name::from_string)
    .collect();
    if choice_exceptions.contains(subject) {
        allowed.insert(Name::from_string("Classical.choice"));
    }
    if !foundations.iter().all(|name| allowed.contains(name)) {
        return Err(format!(
            "{}: disallowed foundations {:?}",
            subject.to_unambiguous_string(),
            foundations
                .iter()
                .map(Name::to_unambiguous_string)
                .collect::<BTreeSet<_>>()
        ));
    }
    Ok(foundations.into_iter().collect())
}

fn model_choice_exception_names(
    targets: &BTreeSet<Name>,
    declared: &[String],
) -> Result<BTreeSet<Name>, String> {
    let mut entries = BTreeSet::new();
    let mut exceptions = BTreeSet::new();
    for entry in declared {
        if !entries.insert(entry) {
            return Err(format!("duplicate choice exception: {entry}"));
        }
        // Match the injective disclosure form, then keep the actual Name.
        // Re-parsing Display would confuse numeric and string components of
        // private names, as well as quoted single-component public names.
        let mut matches = targets
            .iter()
            .filter(|name| name.to_unambiguous_string() == *entry)
            .cloned();
        let subject = matches
            .next()
            .ok_or_else(|| format!("choice exception is not a model target: {entry}"))?;
        if matches.next().is_some() {
            return Err(format!("ambiguous choice exception: {entry}"));
        }
        exceptions.insert(subject);
    }
    Ok(exceptions)
}

fn source_modules(root: &Path, directory: &Path, modules: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(directory).expect("model source directory") {
        let entry = entry.expect("model source entry");
        if entry.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        let path = entry.path();
        if entry.file_type().expect("source entry type").is_dir() {
            source_modules(root, &path, modules);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lean")
        {
            let relative = path
                .strip_prefix(root)
                .expect("relative model module")
                .with_extension("");
            modules.insert(
                relative
                    .components()
                    .map(|part| part.as_os_str().to_str().expect("UTF-8 module"))
                    .collect::<Vec<_>>()
                    .join("."),
            );
        }
    }
}

fn model_declaration_inventory(
    loaded: &Environment,
    targets: &BTreeSet<Name>,
) -> std::collections::BTreeMap<String, serde_json::Value> {
    let mut inventory = std::collections::BTreeMap::new();
    for subject in targets {
        let constant = loaded.get_const(subject).expect("model census declaration");
        let bytes = bincode::serde::encode_to_vec(&constant.type_, bincode::config::standard())
            .expect("model type bytes");
        let digest: String = Sha256::digest(&bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        let module = loaded
            .get_constant_origin(subject)
            .and_then(|origin| origin.module_name())
            .expect("model module origin");
        let mut row = serde_json::json!({
            "module": module, "kind": format!("{:?}", constant.kind), "type_sha256": digest
        });
        // Pin the meaning recursion and the migrated base semantics by body,
        // as well as type: changing either changes the model being claimed.
        if matches!(
            module,
            "CICLModel.Quotation"
                | "CICLModel.BaseRaw"
                | "CICLModel.BaseModel"
                | "CICLModel.BaseComputation"
                | "CICLModel.BaseTower"
                | "CICLModel.BaseSignature"
                | "CICLModel.BaseInterpretation"
                | "CICLModel.BaseWitness"
        ) {
            let bytes = bincode::serde::encode_to_vec(&constant.value, bincode::config::standard())
                .expect("model definition bytes");
            row["value_sha256"] = serde_json::json!(Sha256::digest(&bytes)
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>());
        }
        let previous = inventory.insert(subject.to_unambiguous_string(), row);
        assert!(
            previous.is_none(),
            "duplicate structural model inventory identity"
        );
    }
    assert_eq!(
        inventory.len(),
        targets.len(),
        "every structural target must have exactly one inventory row"
    );
    inventory
}

#[test]
fn model_contracts_recheck_with_named_axiom_exceptions() {
    let lib = require_pinned_lean_lib_path().expect("pinned Lean library");
    let compiled = compiled_fixture_dir("cic_l_model");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("Lean bin directory");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let binary_path = std::env::join_paths(paths).expect("binary path");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/cic_l_model");
    let package = Command::new(bin.join("lake"))
        .arg("build")
        .current_dir(&root)
        .env("PATH", &binary_path)
        .env_remove("LEAN_PATH")
        .output()
        .expect("model package build");
    assert!(
        package.status.success(),
        "model package build failed: {}\n{}",
        String::from_utf8_lossy(&package.stdout),
        String::from_utf8_lossy(&package.stderr)
    );
    // Loading through the package environment detects root collisions even
    // when lake considers every compiled module up to date.
    for (module, accepted) in [
        ("CICLModel.Contracts", true),
        ("CICL.Model.Contracts", false),
    ] {
        let mut probe = Command::new(bin.join("lake"))
            .args(["env", "lean", "--stdin"])
            .current_dir(&root)
            .env("PATH", &binary_path)
            .env_remove("LEAN_PATH")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("model package import probe");
        probe
            .stdin
            .take()
            .expect("probe stdin")
            .write_all(format!("prelude\nimport {module}\n").as_bytes())
            .expect("write model package import");
        let probe = probe
            .wait_with_output()
            .expect("model package import result");
        let output = format!(
            "{}\n{}",
            String::from_utf8_lossy(&probe.stdout),
            String::from_utf8_lossy(&probe.stderr)
        );
        assert_eq!(
            probe.status.success(),
            accepted,
            "model package import {module}: {output}"
        );
        if !accepted {
            assert!(
                output.contains(module) && output.contains("does not exist"),
                "old-root import must fail for the missing module: {output}"
            );
        }
        eprintln!("package-import {module} accepted={accepted}: {output}");
    }
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", "CICLModel.Contracts"])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean path"),
        )
        .env("PATH", &binary_path)
        .output()
        .expect("independent Lean kernel");
    assert!(
        independent.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );
    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, "CICLModel.Contracts", &[compiled, lib])
        .expect("load compiled model");
    let order: Vec<_> = include_str!("../../../theories/cic_l_model/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.replace('/', "."))
        .collect();
    let modules: BTreeSet<String> = order.iter().cloned().collect();
    assert_eq!(modules.len(), order.len(), "duplicate model ORDER entry");
    let mut sources = BTreeSet::new();
    source_modules(&root, &root, &mut sources);
    assert_eq!(
        modules, sources,
        "model ORDER must equal the source module inventory"
    );
    let loaded_modules: BTreeSet<_> = summaries
        .iter()
        .filter_map(|summary| summary.module_name.as_ref())
        .filter(|module| modules.contains(*module))
        .cloned()
        .collect();
    assert_eq!(
        modules, loaded_modules,
        "every model ORDER module must be loaded"
    );
    // Module provenance selects public and private declarations, irrespective of namespace.
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
    assert_eq!(
        targets, added_targets,
        "module-origin targets must equal the loader's added-name census"
    );
    let inventory = model_declaration_inventory(&loaded, &targets);
    eprintln!(
        "model-inventory {}",
        serde_json::to_string(&inventory).expect("model inventory JSON")
    );
    // Untrusted calibration output from the actual compiled propositions.
    // Emit it before the inventory comparison so a deliberate extension can
    // obtain its new pins without inserting invented placeholder digests.
    // Every inventory, denominator, proof replay and mutation gate below stays.
    for constant in loaded.constants().filter(|constant| {
        constant.type_.is_prop()
            && loaded
                .get_constant_origin(&constant.name)
                .and_then(|origin| origin.module_name())
                .is_some_and(|module| {
                    matches!(
                        module,
                        "CICLModel.Contracts"
                            | "CICLModel.CoreContracts"
                            | "CICLModel.PropFamilyContracts"
                            | "CICLModel.BaseContracts"
                            | "CICLModel.BaseComputation"
                    )
                })
    }) {
        if let Some(value) = &constant.value {
            eprintln!(
                "observed-model-contract {} {}",
                constant.name.to_unambiguous_string(),
                observed_value_digest(value)
            );
        }
    }
    // Validate the declared subject set before the full proof replay.
    let expected_inventory: std::collections::BTreeMap<String, serde_json::Value> =
        serde_json::from_str(include_str!(
            "../../../theories/cic_l_model/declaration_inventory.json"
        ))
        .expect("committed model declaration inventory");
    assert!(
        inventory == expected_inventory,
        "model declaration/type inventory changed; a new or altered declaration requires a reviewed pin decision"
    );
    assert!(!targets.is_empty());
    let checked = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("dependency-closed model replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    let mut kernel = checked.into_kernel().expect("fenced reference admissions");
    let choice_names: Vec<String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_model/named_choice_exceptions.json"
    ))
    .expect("named choice exceptions");
    let expected_choice = model_choice_exception_names(&targets, &choice_names)
        .expect("unique actual model names for choice exceptions");
    let mut observed_choice = BTreeSet::new();
    let choice = Name::from_string("Classical.choice");
    for subject in &targets {
        let closure =
            model_axiom_census_with_exceptions(kernel.environment(), subject, &expected_choice)
                .unwrap_or_else(|failure| panic!("{failure}"));
        eprintln!(
            "{}: {:?}",
            subject.to_unambiguous_string(),
            closure
                .iter()
                .map(Name::to_unambiguous_string)
                .collect::<BTreeSet<_>>()
        );
        if closure.contains(&choice) {
            observed_choice.insert(subject.clone());
        }
    }
    assert_eq!(
        observed_choice, expected_choice,
        "named choice closure changed"
    );
    let pins: std::collections::BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_model/model_statement_pins.json"
    ))
    .expect("committed model statement pins");
    assert_eq!(pins.len(), 253, "exact contract denominator");
    // Every constructor of the core judgment has exactly one semantic lemma
    // in the paired table below; a missing lemma fails at its lookup.
    let constructors: BTreeSet<Name> = kernel
        .environment()
        .get_inductive(&Name::from_string("CICL.CoreJudgmentIn"))
        .expect("core judgment was re-admitted with the model")
        .constructor_names
        .iter()
        .cloned()
        .collect();
    let ruled: BTreeSet<Name> = CORE_RULE_CONTRACTS
        .iter()
        .map(|(rule, _)| Name::from_string(&format!("CICL.CoreJudgmentIn.{rule}")))
        .collect();
    assert_eq!(
        constructors, ruled,
        "each core rule needs exactly one semantic lemma with a pinned contract"
    );
    let mut consumed = BTreeSet::new();
    let mut paired_count = 0;
    let mut mutation_count = 0;
    let groundwork = [
        ("ext", "extensionality"),
        ("no_self_member", "foundation"),
        ("member_union", "unions"),
        ("member_power", "powersets"),
        ("member_select", "separation"),
        ("orderedPair_injective", "orderedPairs"),
        ("member_product", "products"),
        ("member_functionSpace", "functions"),
        ("applyGraph_eq", "application"),
        ("maps_apply", "applicationTyping"),
        ("lambdaGraph_maps", "lambdas"),
        ("applyGraph_lambda", "beta"),
        ("lambdaGraph_apply", "eta"),
        ("maps_ext", "functionExt"),
        ("member_dependentFunctionSpace", "dependentProducts"),
        ("lambdaGraph_dependent", "dependentLambdas"),
        ("lift_injective", "liftEquality"),
        ("member_lift", "liftMembership"),
        ("member_lift_image", "liftImage"),
        ("member_smallUniverse", "universeMembers"),
        ("smallUniverse_transitive", "universeTransitive"),
        ("lift_power", "powerLift"),
        ("smallUniverse_power", "universePower"),
        ("smallUniverse_subset", "universeSubset"),
        ("smallUniverse_empty", "universeEmpty"),
        ("smallUniverse_pair", "universePair"),
        ("smallUniverse_union", "universeUnion"),
        ("subset_lift_image", "subsetLiftImage"),
        ("smallUniverse_select", "universeSeparation"),
        ("smallUniverse_product", "universeProducts"),
        ("smallUniverse_functionSpace", "universeFunctions"),
        (
            "smallUniverse_dependentFunctionSpace",
            "universeDependentProducts",
        ),
        ("lift_zero", "liftIdentity"),
        ("lift_lift", "liftComposition"),
        ("member_realizedRange", "realizedRanges"),
        ("member_realizedBound", "realizedBounds"),
        ("familyRealizer_subset", "familyBounds"),
        ("familyRealizer_small_bound", "smallFamilyBound"),
        ("realizedDependentProduct_small", "realizedProductSmall"),
        ("realizedDependentProduct_lambda", "realizedLambda"),
        ("smallUniverse_isUniverse", "universeClosure"),
        ("IsUniverse.lift", "liftedUniverseClosure"),
        (
            "IsUniverse.dependentFunctionSpace_mem",
            "dependentUniverseClosure",
        ),
        ("UniverseTower.extend_old", "towerOld"),
        ("UniverseTower.extend_top", "towerTop"),
        ("UniverseTower.level_ne", "towerStrict"),
        ("UniverseTower.level_subset", "towerCumulative"),
        ("UniverseTower.extend_closed", "towerClosure"),
        ("UniverseTower.extend_ascending", "towerAscending"),
        ("member_truth", "truthMembership"),
        ("truth_false_uninhabited", "falseUninhabited"),
        ("truth_in_propositions", "truthProposition"),
        ("proposition_proof_irrelevance", "proofIrrelevance"),
        ("proposition_as_truth", "propositionTruth"),
        ("propositions_in_universe", "propositionUniverse"),
        ("forallProposition_in_propositions", "impredicativity"),
        ("member_forallProposition", "universalProof"),
        ("forallProposition_elim", "universalElimination"),
        ("sortValue_member_succ", "sortSuccessor"),
        ("sortValue_not_self", "sortNotSelf"),
        ("sortValue_ne_succ", "sortStrict"),
        ("levelSort_member_succ", "levelSortSuccessor"),
        ("levelSort_semEq", "levelSortEquality"),
        ("levelSort_subst", "levelSortSubstitution"),
        ("member_traceLambda", "traceMembership"),
        ("trace_beta", "traceBeta"),
        ("trace_eta", "traceEta"),
        ("traceApply_empty", "traceEmptyApplication"),
        ("traceLambda_empty", "traceEmptyLambda"),
        ("member_tracePi", "traceProductMembership"),
        ("trace_lambda_typed", "traceLambdaTyping"),
        ("tracePi_proof_empty", "traceProofEmpty"),
        ("tracePi_impredicative", "traceImpredicativity"),
        ("tracePi_propositions", "tracePropositions"),
        ("IsUniverse.tracePi_mem", "traceUniverseClosure"),
        ("traceApply_not_applyGraph", "traceDistinctApplication"),
        ("ofRaw_orderedPair", "rawOrderedPair"),
        ("ofRaw_product", "rawProduct"),
        ("ofRaw_traceApply", "rawApplication"),
        ("ofRaw_outputBound", "rawBound"),
        ("ofRaw_traceLambda", "rawLambda"),
        ("ofRaw_tracePi", "rawPi"),
        ("member_raw_children", "rawChildren"),
        ("CICL.Model.RawEvaluation.eval_rename", "evaluationRenaming"),
        (
            "CICL.Model.RawEvaluation.eval_substitute",
            "evaluationSubstitution",
        ),
        (
            "CICL.Model.RawEvaluation.eval_instantiate",
            "evaluationInstantiation",
        ),
        ("CICL.Model.RawEvaluation.eval_zeta", "evaluationZeta"),
        (
            "CICL.Model.RawEvaluation.eval_metadata",
            "evaluationMetadata",
        ),
        ("CICL.Model.TowerRealizer.sorts_correct", "realizedSorts"),
        (
            "CICL.Model.RawEvaluation.Assignment.eval_sort_withTower",
            "evaluationSort",
        ),
        (
            "CICL.Model.RawEvaluation.lookupType_sound",
            "contextTypeLookup",
        ),
        (
            "CICL.Model.RawEvaluation.lookupValue_sound",
            "contextValueLookup",
        ),
        (
            "CICL.Model.RawSet.outputBound_related",
            "rawBoundCongruence",
        ),
        ("quotientFunction_congr", "quotientFunctionCongruence"),
        (
            "CICL.Model.RawSet.traceApply_related",
            "rawApplicationCongruence",
        ),
        (
            "CICL.Model.RawSet.traceLambda_related",
            "rawLambdaCongruence",
        ),
        ("CICL.Model.RawSet.tracePi_related", "rawPiCongruence"),
        ("raw_trace_beta", "rawBeta"),
        (
            "CICL.Model.RawEvaluation.eval_related",
            "evaluationExtensionality",
        ),
        (
            "CICL.Model.RawEvaluation.denote_ofEnvironment",
            "quotientEvaluation",
        ),
        (
            "CICL.Model.RawEvaluation.Assignment.eraseForeign_compatible",
            "foreignCompatibility",
        ),
        ("CICL.Model.RawEvaluation.bvar_meaning", "variableMeaning"),
        (
            "CICL.Model.RawEvaluation.local_definition_meaning",
            "localDefinitionMeaning",
        ),
        (
            "CICL.Model.RawEvaluation.metadata_meaning",
            "metadataMeaning",
        ),
        ("CICL.Model.RawEvaluation.zeta_meaning", "zetaMeaning"),
        ("CICL.Model.RawEvaluation.sort_meaning", "sortMeaning"),
        ("CICL.Model.RawEvaluation.beta_meaning", "betaMeaning"),
        (
            "CICL.Model.RawEvaluation.empty_context_has_valuation",
            "closedContextInhabited",
        ),
        (
            "CICL.Model.RawEvaluation.eval_mapLevels",
            "evaluationLevels",
        ),
        (
            "CICL.Model.RawEvaluation.eval_levelSubstitution",
            "argumentLevels",
        ),
        (
            "CICL.Model.RawEvaluation.eval_instantiateLevels",
            "instantiatedSchema",
        ),
        (
            "CICL.Model.RawEvaluation.eval_scope_congr",
            "scopedEvaluation",
        ),
        ("CICL.Model.RawEvaluation.eval_closed", "closedEvaluation"),
        ("CICL.Model.judgment_constantNames", "judgmentDependencies"),
        ("CICL.Model.typed_avoids_fresh", "freshDependency"),
        (
            "CICL.Model.admitted_type_avoids_fresh",
            "admittedTypeDependencies",
        ),
        (
            "CICL.Model.admitted_value_avoids_fresh",
            "admittedValueDependencies",
        ),
        (
            "CICL.Model.RawEvaluation.Assignment.withLevels_replaceConstant",
            "replacedConstantLevels",
        ),
        (
            "CICL.Model.RawEvaluation.eval_replaceConstant",
            "replacementEvaluation",
        ),
        (
            "CICL.Model.RawEvaluation.definedConstant_unfold",
            "definitionUnfolding",
        ),
        (
            "CICL.Model.RawEvaluation.admitted_definition_unfold",
            "admittedUnfolding",
        ),
        (
            "CICL.Model.RawEvaluation.admitted_type_preserved",
            "admittedTypePreservation",
        ),
        (
            "CICL.Model.RawEvaluation.definition_typing_step",
            "definitionTypingStep",
        ),
        (
            "CICL.Model.RawEvaluation.pushValuation_ofRaw",
            "semanticPush",
        ),
        (
            "CICL.Model.RawEvaluation.denote_instantiate",
            "semanticInstantiation",
        ),
        ("CICL.Model.RawEvaluation.denote_pi", "semanticPi"),
        ("CICL.Model.RawEvaluation.denote_lambda", "semanticLambda"),
        ("CICL.Model.RawEvaluation.denote_app", "semanticApplication"),
        (
            "CICL.Model.RawEvaluation.familyBound_contains",
            "computedFamilyBound",
        ),
        (
            "CICL.Model.RawEvaluation.valid_assumption",
            "semanticAssumptionContext",
        ),
        (
            "CICL.Model.RawEvaluation.valid_definition",
            "semanticDefinitionContext",
        ),
        ("traceLambda_bound_congr", "traceBoundIndependence"),
        (
            "CICL.Model.RawEvaluation.application_meaning",
            "applicationMeaning",
        ),
        ("CICL.Model.RawEvaluation.lambda_meaning", "lambdaMeaning"),
        ("CICL.Model.RawEvaluation.let_meaning", "letMeaning"),
        (
            "CICL.Model.RawEvaluation.denote_zero_sort",
            "zeroSortMeaning",
        ),
        (
            "CICL.Model.RawEvaluation.pi_proposition_meaning",
            "impredicativePiMeaning",
        ),
        ("smallUniverse_raw_image", "smallRawPreimage"),
        (
            "IsUniverse.indexedUnion_mem_smallUniverse",
            "indexedUnionSmallness",
        ),
        ("smallUniverse_indexedUnionClosed", "indexedClosureConcrete"),
        ("IndexedUnionClosed.lift", "indexedClosureLift"),
        (
            "UniverseTower.indexedUnionClosed_extend",
            "indexedClosureExtension",
        ),
        (
            "UniverseTower.indexedUnionClosed_empty",
            "indexedClosureEmpty",
        ),
        ("UniverseTower.indexedUnionClosed_two", "indexedClosureTwo"),
        (
            "UniverseTower.indexedUnionClosed_three",
            "indexedClosureThree",
        ),
        (
            "indexedUnion_requires_small_values",
            "indexedUnionPremiseNecessary",
        ),
        (
            "CICL.Model.RawEvaluation.familyBound_subset",
            "computedBoundLeast",
        ),
        (
            "CICL.Model.RawEvaluation.familyBound_small",
            "computedBoundSmall",
        ),
        (
            "CICL.Model.RawEvaluation.familyBound_smallUniverse",
            "computedBoundConcreteSmall",
        ),
        (
            "CICL.Model.RawEvaluation.pi_smallUniverse_meaning",
            "piConcreteSmallness",
        ),
        ("sortValue_subset_of_le", "sortCumulative"),
        ("sortValue_isUniverse", "dataSortUniverse"),
        ("sortValue_indexedUnionClosed", "dataSortIndexed"),
        ("sortValue_not_reverse_subset", "sortAntiCumulative"),
        ("sortValue_reverse_counterexample", "sortReverseWitness"),
        (
            "CICL.Model.RawEvaluation.denote_bounded_sort",
            "boundedSortDenotation",
        ),
        ("CICL.Model.RawEvaluation.pi_data_meaning", "dataPiMeaning"),
        ("CICL.Model.RawEvaluation.pi_meaning", "boundedPiMeaning"),
        // M4: the `Prop` half of the container lemma (off the route since D4) and its
        // large-elimination control. The direct base-family interpretation and
        // computation equations are paired in CORE_MODEL_CONTRACTS.
        ("CICL.Model.PropFamilies.family_intro", "propFamilyIntro"),
        (
            "CICL.Model.PropFamilies.family_proof_irrelevance",
            "propFamilyProofIrrelevance",
        ),
        (
            "CICL.Model.PropFamilies.family_induction",
            "propFamilyInduction",
        ),
        (
            "CICL.Model.PropFamilies.recursor_typed",
            "propFamilyEliminationTyped",
        ),
        (
            "CICL.Model.PropFamilies.recursor_computes",
            "propFamilyEliminationComputes",
        ),
        (
            "CICL.Model.PropFamilies.two_shapes_refute_elimination",
            "propFamilyTwoShapesRefuted",
        ),
        (
            "CICL.Model.PropFamilies.recursor_needs_subsingleton",
            "propFamilyEliminationNeedsSubsingleton",
        ),
        (
            "CICL.Model.PropFamilies.equality_family",
            "equalityContainerFamily",
        ),
        (
            "CICL.Model.PropFamilies.equality_recursor",
            "equalityContainerRecursor",
        ),
    ];
    let paired: Vec<_> = groundwork
        .iter()
        .map(|(proof, contract)| ((*proof).to_owned(), *contract))
        .chain(
            CORE_RULE_CONTRACTS
                .iter()
                .map(|(rule, contract)| (format!("CICL.Model.CoreRules.{rule}"), *contract)),
        )
        .chain(
            CORE_MODEL_CONTRACTS
                .iter()
                .map(|(proof, contract)| ((*proof).to_owned(), *contract)),
        )
        .collect();
    // Print the complete paired-contract observation before comparing pins,
    // as kcheck_spec does, so a deliberate extension needs one census run.
    for (_, contract) in &paired {
        let pin = loaded
            .get_const(&Name::from_string(&format!(
                "CICL.Model.Contracts.{contract}"
            )))
            .expect("independent contract");
        let bytes = bincode::serde::encode_to_vec(
            pin.value.as_ref().expect("contract proposition"),
            bincode::config::standard(),
        )
        .expect("contract bytes");
        eprintln!(
            "observed-statement-pin {contract} {}",
            Sha256::digest(&bytes)
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>()
        );
    }
    for (proof, contract) in paired {
        assert!(consumed.insert(contract), "duplicate contract: {contract}");
        let source = if proof.starts_with("CICL.") || proof.starts_with("KCheckSpec.") {
            Name::from_string(&proof)
        } else {
            Name::from_string(&format!("CICL.Model.SetValue.{proof}"))
        };
        let c = loaded.get_const(&source).expect("implementation proof");
        let pin = loaded
            .get_const(&Name::from_string(&format!(
                "CICL.Model.Contracts.{contract}"
            )))
            .expect("independent contract");
        let contract_type = pin
            .value
            .clone()
            .expect("contract is a proposition definition");
        let bytes = bincode::serde::encode_to_vec(&contract_type, bincode::config::standard())
            .expect("serialize independent statement");
        let digest = Sha256::digest(&bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        assert_eq!(
            pins.get(contract),
            Some(&digest),
            "statement changed: {contract}"
        );
        eprintln!("statement-pin {contract} {digest}");
        let value = c.value.clone().expect("real proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("CICL.Model.Controls.{contract}_positive")),
                level_params: c.level_params.clone(),
                type_: contract_type,
                value: value.clone(),
            })
            .expect("implementation proof at independent contract");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("CICL.Model.Controls.{contract}_false")),
            level_params: c.level_params.clone(),
            type_: Expr::const_(Name::from_string("False"), vec![]),
            value,
        });
        assert!(
            matches!(
                &bad,
                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                }))
            ),
            "false contract must fail with type mismatch: {bad:?}"
        );
        paired_count += 1;
    }
    for (proof, mutation) in [
        ("sortValue_member_succ", "typeInType"),
        ("sortValue_subset_of_le", "sortCumulativeReversed"),
        ("trace_beta", "traceWrongApplication"),
        (
            "IsUniverse.indexedUnion_mem_smallUniverse",
            "indexedUnionUnboundedValues",
        ),
        (
            "CICL.Model.RawEvaluation.eval_substitute",
            "evaluationWrongSubstitution",
        ),
        (
            "CICL.Model.RawEvaluation.eval_mapLevels",
            "evaluationWrongLevels",
        ),
        (
            "CICL.Model.RawEvaluation.definedConstant_unfold",
            "definitionWrongArguments",
        ),
        (
            "CICL.Model.RawEvaluation.denote_instantiate",
            "semanticWrongBinder",
        ),
        (
            "CICL.Model.RawEvaluation.application_meaning",
            "applicationWrongCodomain",
        ),
        ("CICL.Model.CoreRules.sort", "sortBoundOffByOne"),
        (
            "CICL.Model.PropFamilies.recursor_computes",
            "propFamilyEliminationWithoutSubsingleton",
        ),
        (
            "CICL.Model.BaseWitness.base_signature_wf",
            "baseUnderstatedBoundWellFormed",
        ),
    ] {
        assert!(consumed.insert(mutation), "duplicate mutation: {mutation}");
        let proof_name = if proof.starts_with("CICL.") || proof.starts_with("KCheckSpec.") {
            proof.to_owned()
        } else {
            format!("CICL.Model.SetValue.{proof}")
        };
        let source = loaded
            .get_const(&Name::from_string(&proof_name))
            .expect("positively re-entered proof");
        let wrong = loaded
            .get_const(&Name::from_string(&format!(
                "CICL.Model.Contracts.{mutation}"
            )))
            .expect("unproved mutation")
            .value
            .clone()
            .expect("mutation proposition");
        let bytes = bincode::serde::encode_to_vec(&wrong, bincode::config::standard())
            .expect("mutation bytes");
        let digest: String = Sha256::digest(&bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        assert_eq!(
            pins.get(mutation),
            Some(&digest),
            "mutation changed: {mutation}"
        );
        eprintln!("statement-pin {mutation} {digest}");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("CICL.Model.Controls.{mutation}_forged")),
            level_params: source.level_params.clone(),
            type_: wrong,
            value: source.value.clone().expect("same actual proof"),
        });
        assert!(
            matches!(
                &bad,
                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                }))
            ),
            "{mutation} must fail by type mismatch: {bad:?}"
        );
        mutation_count += 1;
    }
    assert_eq!(
        consumed,
        pins.keys().map(String::as_str).collect(),
        "every pinned statement must be checked exactly once"
    );
    eprintln!(
        "model targets {}, paired contracts {paired_count}, targeted mutations {mutation_count}",
        targets.len()
    );
}

// These environments are checked declaration fixtures for the census itself,
// not an assertion that a domain axiom passed the separate fenced reference
// admission. Every control calls the same helper as the complete Model owner.
fn census_alias(env: &mut Environment, dependency: &Name) -> Name {
    let info = env.get_const(dependency).expect("checked dependency");
    let subject = Name::from_string("CICL.Model.Census.subject");
    let declaration = Declaration::Definition {
        name: subject.clone(),
        level_params: info.level_params.clone(),
        type_: info.type_.clone(),
        value: Expr::const_(
            dependency.clone(),
            info.level_params
                .iter()
                .cloned()
                .map(clean_kernel::Level::param)
                .collect::<Vec<_>>(),
        ),
        is_reducible: true,
    };
    env.add_decl(declaration).expect("checked alias definition");
    subject
}

#[test]
fn axiom_census_refuses_unused_domain_axiom_root() {
    let mut env = Environment::new();
    let subject = Name::from_string("CICL.Model.Census.unused_domain_axiom");
    env.add_decl(Declaration::Axiom {
        name: subject.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("well-typed unused axiom fixture");
    assert!(env.axiom_deps(&subject).expect("closure").is_empty());
    assert!(
        model_axiom_census(&env, &subject).is_err(),
        "an unused domain axiom root must not pass the model census"
    );
}

#[test]
fn axiom_census_refuses_quoted_foundation_alias_dependency() {
    let mut env = Environment::new();
    let spoof = Name::anon().str("Quot.sound");
    let canonical = Name::from_string("Quot.sound");
    assert_ne!(spoof, canonical);
    assert_eq!(spoof.to_string(), canonical.to_string());
    env.add_decl(Declaration::Axiom {
        name: spoof.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("well-typed quoted-name axiom fixture");
    let subject = census_alias(&mut env, &spoof);
    assert!(env.axiom_deps(&subject).expect("closure").contains(&spoof));
    assert!(
        model_axiom_census(&env, &subject).is_err(),
        "display-equivalent domain dependency must remain a domain axiom"
    );
}

#[test]
fn axiom_census_accepts_canonical_foundation_dependency() {
    for foundation in ["propext", "Quot.sound"] {
        let mut env = Environment::with_prelude();
        let foundation = Name::from_string(foundation);
        assert!(env.is_canonical_foundational_axiom(&foundation));
        let subject = census_alias(&mut env, &foundation);
        let closure = model_axiom_census(&env, &subject).expect("allowed canonical foundation");
        assert!(closure.contains(&foundation.to_string()));
    }
}

#[test]
fn axiom_census_accepts_canonical_foundation_root() {
    let env = Environment::with_prelude();
    for foundation in [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
    ] {
        let foundation = Name::from_string(foundation);
        assert!(env.is_canonical_foundational_axiom(&foundation));
        model_axiom_census(&env, &foundation).expect("canonical no-choice foundation root");
    }
}

#[test]
fn axiom_census_refuses_choice_in_root_and_dependency() {
    let mut env = Environment::with_prelude();
    let choice = Name::from_string("Classical.choice");
    assert!(env.is_canonical_foundational_axiom(&choice));
    let subject = census_alias(&mut env, &choice);
    assert!(
        model_axiom_census(&env, &subject).is_err(),
        "choice dependency"
    );
    assert!(model_axiom_census(&env, &choice).is_err(), "choice root");
}

#[test]
fn axiom_census_accepts_checked_axiom_free_definition() {
    let mut env = Environment::new();
    let subject = Name::from_string("CICL.Model.Census.empty_proposition_type");
    env.add_decl(Declaration::Definition {
        name: subject.clone(),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero())),
        value: Expr::prop(),
        is_reducible: true,
    })
    .expect("checked axiom-free definition");
    assert!(model_axiom_census(&env, &subject)
        .expect("ordinary positive census")
        .is_empty());
}

#[test]
fn axiom_census_accepts_exact_named_choice_dependency() {
    let mut env = Environment::with_prelude();
    let choice = Name::from_string("Classical.choice");
    let subject = census_alias(&mut env, &choice);
    let targets = BTreeSet::from([subject.clone()]);
    let exceptions = model_choice_exception_names(&targets, &[subject.to_unambiguous_string()])
        .expect("exact named exception");
    let closure = model_axiom_census_with_exceptions(&env, &subject, &exceptions)
        .expect("named canonical choice dependency");
    assert!(closure.contains(&choice));
}

#[test]
fn axiom_census_refuses_same_display_named_choice_subject() {
    let mut env = Environment::with_prelude();
    let choice = Name::from_string("Classical.choice");
    let canonical = census_alias(&mut env, &choice);
    let alias = Name::anon().str(canonical.to_string());
    assert_ne!(alias, canonical);
    assert_eq!(alias.to_string(), canonical.to_string());
    let original = env.get_const(&canonical).expect("checked choice alias");
    let declaration = Declaration::Definition {
        name: alias.clone(),
        level_params: original.level_params.clone(),
        type_: original.type_.clone(),
        value: original.value.clone().expect("actual choice alias body"),
        is_reducible: true,
    };
    env.add_decl(declaration)
        .expect("well-typed same-display subject");
    let targets = BTreeSet::from([canonical.clone(), alias.clone()]);
    let exceptions = model_choice_exception_names(&targets, &[canonical.to_unambiguous_string()])
        .expect("only the actual canonical subject is named");
    assert!(model_axiom_census_with_exceptions(&env, &canonical, &exceptions).is_ok());
    assert!(
        model_axiom_census_with_exceptions(&env, &alias, &exceptions).is_err(),
        "same Display must not consume a structural subject's choice exception"
    );
}

#[test]
fn axiom_census_named_choice_preserves_private_numeric_components() {
    let prefix = Name::from_string("_private.CICLModel.Census");
    let numeric = prefix.clone().num(0).str("subject");
    let textual = prefix.str("0").str("subject");
    assert_ne!(numeric, textual);
    assert_eq!(numeric.to_string(), textual.to_string());
    assert_ne!(
        numeric.to_unambiguous_string(),
        textual.to_unambiguous_string()
    );
    let targets = BTreeSet::from([numeric.clone(), textual.clone()]);
    let numeric_exception =
        model_choice_exception_names(&targets, &[numeric.to_unambiguous_string()])
            .expect("numeric component retained");
    assert_eq!(numeric_exception, BTreeSet::from([numeric]));
    let textual_exception =
        model_choice_exception_names(&targets, &[textual.to_unambiguous_string()])
            .expect("text component retained");
    assert_eq!(textual_exception, BTreeSet::from([textual]));
}

// The real pinned Lean fixture has ten declarations, including two distinct
// Alias.value names with identical type/kind/module rows and different bodies.
// Reuse its complete loader/origin census and require fenced, axiom-free replay
// before exercising the same inventory builder used by the complete Model gate.
fn inventory_fixture() -> (Environment, BTreeSet<Name>, Name, Name) {
    let compiled = compiled_fixture_dir("typed_names");
    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, "TypedNames", &[compiled])
        .expect("real pinned Lean identity fixture");
    let targets: BTreeSet<_> = loaded
        .constants()
        .filter(|constant| {
            loaded
                .get_constant_origin(&constant.name)
                .and_then(|origin| origin.module_name())
                == Some("TypedNames")
        })
        .map(|constant| constant.name.clone())
        .collect();
    let added: BTreeSet<_> = summaries
        .iter()
        .filter(|summary| summary.module_name.as_deref() == Some("TypedNames"))
        .flat_map(|summary| summary.added_names.iter().cloned())
        .collect();
    assert_eq!(targets, added, "complete actual origin/added-name census");
    assert_eq!(targets.len(), 10, "unchanged real fixture denominator");
    let canonical = Name::anon().str("Alias").str("value");
    let quoted = Name::anon().str("Alias.value");
    assert_ne!(canonical, quoted);
    assert_eq!(canonical.to_string(), quoted.to_string());
    assert!(targets.contains(&canonical) && targets.contains(&quoted));
    let left = loaded.get_const(&canonical).expect("canonical declaration");
    let right = loaded.get_const(&quoted).expect("quoted declaration");
    assert_eq!(left.type_, right.type_);
    assert_eq!(left.kind, right.kind);
    assert_ne!(
        left.value, right.value,
        "actual different definition bodies"
    );
    assert_eq!(
        loaded.get_constant_origin(&canonical),
        loaded.get_constant_origin(&quoted)
    );
    let checked = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("dependency-closed identity fixture replay");
    assert!(checked.report.passed() && checked.entry_refusals.is_empty());
    let kernel = checked.into_kernel().expect("fenced fixture admissions");
    for target in &targets {
        assert!(model_axiom_census(kernel.environment(), target)
            .expect("unchanged no-choice fixture policy")
            .is_empty());
    }
    (loaded, targets, canonical, quoted)
}

#[test]
fn model_inventory_refuses_unlisted_same_display_declaration() {
    let (loaded, targets, _, quoted) = inventory_fixture();
    let mut pinned_targets = targets.clone();
    assert!(pinned_targets.remove(&quoted));
    assert_eq!(pinned_targets.len(), 9);
    let pinned = model_declaration_inventory(&loaded, &pinned_targets);
    let actual = model_declaration_inventory(&loaded, &targets);
    eprintln!(
        "inventory-omission actual-targets={} pinned-targets={} actual-rows={} pinned-rows={}",
        targets.len(),
        pinned_targets.len(),
        actual.len(),
        pinned.len()
    );
    assert_ne!(
        actual, pinned,
        "an unlisted structural declaration must change the pinned inventory"
    );
}

#[test]
fn model_inventory_refuses_same_display_declaration_replacement() {
    let (loaded, targets, canonical, quoted) = inventory_fixture();
    let mut pinned_targets = targets.clone();
    let mut substituted_targets = targets;
    assert!(pinned_targets.remove(&quoted));
    assert!(substituted_targets.remove(&canonical));
    assert_eq!(pinned_targets.len(), substituted_targets.len());
    let pinned = model_declaration_inventory(&loaded, &pinned_targets);
    let substituted = model_declaration_inventory(&loaded, &substituted_targets);
    assert_ne!(
        substituted, pinned,
        "same-count structural substitution must change the pinned inventory"
    );
}

#[test]
fn model_inventory_accepts_checked_canonical_declaration() {
    let (loaded, _, canonical, _) = inventory_fixture();
    let inventory = model_declaration_inventory(&loaded, &BTreeSet::from([canonical]));
    assert_eq!(inventory.len(), 1);
    let row = inventory
        .get("Alias.value")
        .expect("exact canonical identity");
    assert_eq!(row["module"], "TypedNames");
    assert_eq!(row["kind"], "Definition");
    assert_eq!(row["type_sha256"].as_str().expect("type hash").len(), 64);
}
