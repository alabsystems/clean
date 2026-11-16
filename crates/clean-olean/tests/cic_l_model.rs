// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The set model (plan units M1 to M5 and E6): groundwork, one semantic lemma per
//! core rule, interpreted primitives, quotation and negative controls, each
//! re-entered at a pinned contract.
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{ConstantKind, Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};

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
const CORE_MODEL_CONTRACTS: [(&str, &str); 70] = [
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
    ("CICL.Model.BaseMath.Eq.recursor_apply", "baseEqComputation"),
    (
        "CICL.Model.BaseMath.PUnit.recursor_apply",
        "basePUnitComputation",
    ),
    (
        "CICL.Model.BaseMath.Nat.natRecDen_apply",
        "baseNatComputation",
    ),
    (
        "CICL.Model.CongruenceControls.beta_without_argument_typing_refuted",
        "betaWithoutArgumentTypingRefuted",
    ),
    (
        "CICL.Model.CongruenceControls.piCong_refuted_of_tower",
        "piCongTowerControl",
    ),
    (
        "CICL.Model.CongruenceControls.lamCong_refuted_of_tower",
        "lamCongTowerControl",
    ),
    (
        "CICL.Model.CongruenceControls.appCong_refuted_of_tower",
        "appCongTowerControl",
    ),
    (
        "CICL.Model.CongruenceControls.letCong_refuted_of_tower",
        "letCongTowerControl",
    ),
    (
        "CICL.Model.CongruenceControls.piCong_control",
        "piCongControl",
    ),
    (
        "CICL.Model.CongruenceControls.lamCong_control",
        "lamCongControl",
    ),
    (
        "CICL.Model.CongruenceControls.appCong_control",
        "appCongControl",
    ),
    (
        "CICL.Model.CongruenceControls.letCong_control",
        "letCongControl",
    ),
    (
        "CICL.Model.QuotationSemantics.addFn_meaning",
        "quotationAddMeaning",
    ),
    (
        "CICL.Model.QuotationSemantics.mulFn_meaning",
        "quotationMulMeaning",
    ),
    (
        "CICL.Model.QuotationSemantics.arith_meaning",
        "quotationArithMeaning",
    ),
    (
        "CICL.Model.QuotationSemantics.formula_meaning",
        "quotationFormulaMeaning",
    ),
    (
        "CICL.Model.QuotationSemantics.quote_correct",
        "quotationCorrect",
    ),
    (
        "CICL.Model.QuotationSemantics.formula_quote_correct",
        "quotationFormulaSliceCorrect",
    ),
    (
        "CICL.Model.QuotationSemantics.valid_base_assignment_exists",
        "quotationValidBaseAssignment",
    ),
    (
        "CICL.Model.QuotationSemantics.quote_sound",
        "quotationSound",
    ),
    (
        "CICL.Model.QuotationSemantics.base_quote_sound",
        "quotationBaseSound",
    ),
    (
        "CICL.Model.QuotationSemantics.badAddFn_refuted",
        "quotationBadAddRefuted",
    ),
    (
        "CICL.Model.QuotationSemantics.badConj_refuted",
        "quotationBadConjRefuted",
    ),
    (
        "CICL.Model.QuotationSemantics.quotation_semantics_witness",
        "quotationWitness",
    ),
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
    let axiom_root = info.kind == ConstantKind::Axiom;
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
        let name_bytes = bincode::serde::encode_to_vec(subject, bincode::config::standard())
            .expect("model name bytes");
        let name_digest: String = Sha256::digest(&name_bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        let module = loaded
            .get_constant_origin(subject)
            .and_then(|origin| origin.module_name())
            .expect("model module origin");
        let mut row = serde_json::json!({
            "module": module,
            "kind": format!("{:?}", constant.kind), "type_sha256": digest,
            "name_sha256": name_digest,
            "level_params": constant.level_params.iter().map(Name::to_unambiguous_string).collect::<Vec<_>>()
        });
        // Bind every optional value, including theorem proofs, to this exact
        // declaration inventory. Statement and axiom checks alone permit a
        // different proof of the same statement; source lineage must detect it.
        let bytes = bincode::serde::encode_to_vec(&constant.value, bincode::config::standard())
            .expect("model optional value bytes");
        let digest: String = Sha256::digest(bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        row["value_sha256"] = serde_json::json!(digest);
        // Pin the full kernel meaning while retaining every theorem body hash.
        let meaning_payload = (
            constant,
            loaded.get_inductive(subject),
            loaded.get_constructor(subject),
            loaded.get_recursor(subject),
        );
        let bytes = bincode::serde::encode_to_vec(meaning_payload, bincode::config::standard())
            .expect("model full meaning bytes");
        row["meaning_sha256"] = serde_json::json!(Sha256::digest(&bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>());

        assert!(
            inventory
                .insert(subject.to_unambiguous_string(), row)
                .is_none(),
            "distinct model declarations must have distinct inventory keys"
        );
    }
    assert_eq!(
        inventory.len(),
        targets.len(),
        "every actual model name must be inventoried"
    );
    inventory
}

#[test]
fn model_artifact_headers_have_unique_owners() {
    let compiled = compiled_fixture_dir("cic_l_model");
    let mut owners = std::collections::BTreeMap::new();
    let mut counts = std::collections::BTreeMap::new();
    for module in include_str!("../../../theories/cic_l_model/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.replace('/', "."))
    {
        let artifact = read_artifact(
            &module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .expect("model artifact header");
        let mut local = BTreeSet::new();
        for subject in artifact.names {
            assert!(
                local.insert(subject.clone()),
                "repeated local artifact name: {module}: {}",
                subject.to_unambiguous_string()
            );
            if let Some(previous) = owners.insert(subject.clone(), module.clone()) {
                panic!(
                    "duplicate model artifact owner: {} first={previous} second={module}",
                    subject.to_unambiguous_string()
                );
            }
        }
        assert!(counts.insert(module, local.len()).is_none());
    }
    eprintln!(
        "model-raw-artifact-counts {}",
        serde_json::to_string(&counts).expect("artifact counts JSON")
    );
    let unsafe_rec_candidates: BTreeSet<_> = owners
        .keys()
        .filter(|name| name.to_string().ends_with("._unsafe_rec"))
        .map(Name::to_unambiguous_string)
        .collect();
    eprintln!(
        "model-raw-unsafe-rec-candidates {}",
        serde_json::to_string(&unsafe_rec_candidates).expect("raw candidate names JSON")
    );
    let canonical_equation = Name::from_string("CICL.BaseFamilies.Nat.term.eq_1");
    assert!(
        !owners.contains_key(&canonical_equation),
        "the Nat equation must be owned by its defining CICL module"
    );
    let defining_artifact = read_artifact(
        "CICL.BaseFamilies",
        &compiled.join("CICL/BaseFamilies.olean"),
        ArtifactDepth::Names,
    )
    .expect("canonical base-family artifact");
    assert_eq!(
        defining_artifact
            .names
            .iter()
            .filter(|name| **name == canonical_equation)
            .count(),
        1,
        "the canonical equation must remain present exactly once"
    );
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
    // Pin the primitive syntax to the actual sealed Lean declarations, including
    // binder annotations/names, block records, bounds and recursor rules.
    let mut pin_probe = Command::new(bin.join("lake"))
        .args(["env", "lean", "--stdin"])
        .current_dir(&root)
        .env("PATH", &binary_path)
        .env_remove("LEAN_PATH")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("canonical base-family pin probe");
    pin_probe
        .stdin
        .take()
        .expect("pin probe stdin")
        .write_all(include_str!("support/canonical_base_pins.lean").as_bytes())
        .expect("write canonical pin source");
    let pin_probe = pin_probe.wait_with_output().expect("canonical pin result");
    let pin_output = format!(
        "{}\n{}",
        String::from_utf8_lossy(&pin_probe.stdout),
        String::from_utf8_lossy(&pin_probe.stderr)
    );
    assert!(
        pin_probe.status.success(),
        "canonical base-family pin mismatch: {pin_output}"
    );
    for marker in [
        "CANONICAL_EQ_PIN Eq exact-type-and-payload=ok",
        "CANONICAL_EQ_PIN Eq.refl exact-type-and-payload=ok",
        "CANONICAL_EQ_PIN Eq.rec exact-type-and-payload=ok",
        "CANONICAL_EQ_FAMILY record-and-block=ok",
        "CANONICAL_EQ_COMPARATOR alpha-equal-binder-mutations-refused=ok",
        "CANONICAL_PUNIT_PIN PUnit exact-type-and-payload=ok",
        "CANONICAL_PUNIT_PIN PUnit.unit exact-type-and-payload=ok",
        "CANONICAL_PUNIT_PIN PUnit.rec exact-type-and-payload=ok",
        "CANONICAL_PUNIT_FAMILY record-and-block=ok",
        "CANONICAL_NAT_PIN Nat exact-type-and-payload=ok",
        "CANONICAL_NAT_PIN Nat.zero exact-type-and-payload=ok",
        "CANONICAL_NAT_PIN Nat.succ exact-type-and-payload=ok",
        "CANONICAL_NAT_PIN Nat.rec exact-type-and-payload=ok",
        "CANONICAL_NAT_FAMILY record-and-block=ok",
        "CANONICAL_NAT_COMPARATOR alpha-equal-binder-mutations-refused=ok",
        "CANONICAL_BASE_FAMILY_CENSUS count=3",
    ] {
        assert_eq!(
            pin_output.matches(marker).count(),
            1,
            "missing or duplicate canonical pin result: {pin_output}"
        );
    }
    eprintln!("canonical-base-pins {pin_output}");
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
    let summaries =
        load_module_with_deps(&mut loaded, "CICLModel.Contracts", &[compiled.clone(), lib])
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
    let skipped: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let mut observed_copies = BTreeSet::new();
    let mut artifact_targets = BTreeSet::new();
    for module in &modules {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .expect("model artifact name census");
        for subject in artifact.names {
            if loaded.get_const(&subject).is_none() {
                let display = subject.to_string();
                assert!(
                    display.ends_with("._unsafe_rec") && skipped.contains(display.as_str()),
                    "missing model declaration {subject}"
                );
                assert!(observed_copies.insert(subject.to_unambiguous_string()));
            } else {
                assert!(
                    artifact_targets.insert(subject),
                    "duplicate model artifact owner"
                );
            }
        }
    }
    let expected_copies: Vec<String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_model/compiler_copies.json"
    ))
    .expect("reviewed model compiler-copy roster");
    let expected_copy_set: BTreeSet<_> = expected_copies.iter().cloned().collect();
    assert_eq!(
        expected_copies.len(),
        expected_copy_set.len(),
        "duplicate expected compiler copy"
    );
    assert_eq!(
        observed_copies, expected_copy_set,
        "review unexpected model compiler-copy population"
    );
    for copy in &expected_copies {
        let definition = copy
            .strip_suffix("._unsafe_rec")
            .expect("compiler-copy suffix");
        let source = Name::from_string(definition);
        assert!(
            loaded.get_const(&source).is_some(),
            "compiler copy lacks source {copy}"
        );
        assert!(
            !loaded.is_unsafe(&source) && !loaded.is_partial(&source),
            "compiler copy must have a safe total source definition: {copy}"
        );
    }
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
    assert_eq!(
        targets, artifact_targets,
        "model module-origin and raw artifact name censuses must agree"
    );
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
    assert!(!targets.is_empty());
    let contract_replays: Vec<[String; 2]> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_model/contract_replays.json"
    ))
    .expect("reviewed model replay catalog");
    let mutant_replays: Vec<[String; 2]> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_model/mutant_replays.json"
    ))
    .expect("reviewed model replay catalog");
    // Print all observed schema identities before expensive dependency replay.
    // These are diagnostics: the independent comparisons below remain required.
    let mut observed_pins = std::collections::BTreeMap::new();
    for [_, contract] in contract_replays.iter().chain(&mutant_replays) {
        let declaration = loaded
            .get_const(&Name::from_string(&format!(
                "CICL.Model.Contracts.{contract}"
            )))
            .expect("compiled independent contract");
        let statement = declaration
            .value
            .as_ref()
            .expect("contract proposition definition");
        let bytes = bincode::serde::encode_to_vec(statement, bincode::config::standard())
            .expect("serialize observed contract");
        let digest: String = Sha256::digest(&bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        assert!(
            observed_pins.insert(contract.clone(), digest).is_none(),
            "duplicate observed contract: {contract}"
        );
    }
    eprintln!(
        "model-observed-statement-pins {}",
        serde_json::to_string(&observed_pins).expect("observed statement pins JSON")
    );
    assert!(
        inventory == expected_inventory,
        "model declaration/type/value inventory changed; a new or altered declaration requires a reviewed pin decision"
    );
    // A selected specification proof may have private proof helpers outside
    // model-origin targets. Replay its real dependency closure as well.
    let proof_roots: BTreeSet<Name> = contract_replays
        .iter()
        .chain(&mutant_replays)
        .map(|[proof, _]| {
            if proof.starts_with("CICL.") || proof.starts_with("KCheckSpec.") {
                Name::from_string(proof)
            } else {
                Name::from_string(&format!("CICL.Model.SetValue.{proof}"))
            }
        })
        .collect();
    let replay_roots: BTreeSet<Name> = targets.union(&proof_roots).cloned().collect();
    let checked = reference_base_closed(&loaded, &replay_roots, &ClosedRecheckOptions::default())
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
    for subject in &replay_roots {
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
    assert_eq!(pins.len(), 600, "exact contract denominator");
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
    for (rule, contract) in CORE_RULE_CONTRACTS {
        let proof = format!("CICL.Model.CoreRules.{rule}");
        assert!(
            contract_replays
                .iter()
                .any(|row| row[0] == proof && row[1] == contract),
            "missing core rule replay: {proof} at {contract}"
        );
    }
    for (proof, contract) in CORE_MODEL_CONTRACTS {
        assert!(
            contract_replays
                .iter()
                .any(|row| row[0] == proof && row[1] == contract),
            "missing core model replay: {proof} at {contract}"
        );
    }
    // Complete E6 / M3 negative-control census across CICL + CICLModel:
    // every constructor of `CICL.CoreJudgmentIn` must have a unique ground
    // `CICL.NegativeControls.Refutes` theorem admitted by the fenced kernel,
    // matching `data/cic_l_rule_inventory.json` with zero `"none"` exemptions.
    let rule_inventory: serde_json::Value =
        serde_json::from_str(include_str!("../../../data/cic_l_rule_inventory.json"))
            .expect("committed CIC_L rule inventory");
    let mut expected_controls: std::collections::BTreeMap<String, String> =
        std::collections::BTreeMap::new();
    let mut expected_model_controls: std::collections::BTreeMap<String, String> =
        std::collections::BTreeMap::new();
    for item in rule_inventory["rows"]
        .as_array()
        .expect("rule inventory rows")
        .iter()
        .filter_map(|row| row["cic_l"].as_array())
        .flatten()
    {
        let Some(ctor) = item["item"]
            .as_str()
            .and_then(|s| s.strip_prefix("CICL.CoreJudgmentIn."))
        else {
            continue;
        };
        assert!(
            item["control"]["none"].is_null(),
            "CoreJudgmentIn.{ctor} still records control.none instead of a Refutes theorem"
        );
        let theorem = item["control"]["theorem"]
            .as_str()
            .unwrap_or_else(|| panic!("CoreJudgmentIn.{ctor} lacks control.theorem"));
        let file = item["control"]["file"]
            .as_str()
            .unwrap_or_else(|| panic!("CoreJudgmentIn.{ctor} lacks control.file"));
        if let Some(prev) = expected_controls.insert(ctor.to_owned(), theorem.to_owned()) {
            assert_eq!(
                prev, theorem,
                "CoreJudgmentIn.{ctor} names conflicting controls"
            );
        }
        if file.starts_with("CICLModel/") {
            expected_model_controls.insert(ctor.to_owned(), theorem.to_owned());
        }
    }
    let expected_ctor_shorts: BTreeSet<String> = constructors
        .iter()
        .map(|n| n.to_string().rsplit('.').next().unwrap().to_owned())
        .collect();
    assert_eq!(
        expected_controls.keys().cloned().collect::<BTreeSet<_>>(),
        expected_ctor_shorts,
        "rule inventory controls must cover every CoreJudgmentIn constructor"
    );
    assert!(
        !expected_model_controls.is_empty(),
        "theories/cic_l_model must supply the semantic congruence Refutes controls"
    );
    let refutes_head = Name::from_string("CICL.NegativeControls.Refutes");
    let collect_refutes = |env: &Environment| {
        let mut map: std::collections::BTreeMap<String, BTreeSet<String>> =
            std::collections::BTreeMap::new();
        for c in env.constants() {
            if c.value.is_none() || !c.level_params.is_empty() {
                continue;
            }
            if !matches!(
                c.type_.get_app_fn().kind(),
                clean_kernel::ExprKind::Const(h, _) if h == &refutes_head
            ) {
                continue;
            }
            let rule_short = match c.type_.get_app_args().get(1).map(|r| r.kind()) {
                Some(clean_kernel::ExprKind::Const(r, _)) => {
                    r.to_string().rsplit('.').next().unwrap().to_owned()
                }
                other => panic!("unreadable rule argument in {}: {other:?}", c.name),
            };
            map.entry(rule_short)
                .or_default()
                .insert(c.name.to_string());
        }
        map
    };
    let loaded_controls = collect_refutes(&loaded);
    assert_eq!(
        loaded_controls.len(),
        constructors.len(),
        "ground Refutes census across loaded CICL + CICLModel must equal CoreJudgmentIn constructor count"
    );
    for (ctor, expected_thm) in &expected_controls {
        assert_eq!(
            loaded_controls.get(ctor),
            Some(&BTreeSet::from([expected_thm.clone()])),
            "loaded ground Refutes theorem mismatch for CoreJudgmentIn.{ctor}"
        );
    }
    let admitted_controls = collect_refutes(kernel.environment());
    assert_eq!(
        admitted_controls.len(),
        expected_model_controls.len(),
        "fenced CICLModel replay Refutes census must equal model-hosted control count"
    );
    for (ctor, expected_thm) in &expected_model_controls {
        assert_eq!(
            admitted_controls.get(ctor),
            Some(&BTreeSet::from([expected_thm.clone()])),
            "fenced ReferenceKernel Refutes theorem mismatch for CoreJudgmentIn.{ctor}"
        );
    }
    let mut consumed = BTreeSet::new();
    let mut paired_count = 0;
    let mut mutation_count = 0;
    for [proof, contract] in &contract_replays {
        let proof = proof.as_str();
        let contract = contract.as_str();
        assert!(
            consumed.insert(contract.to_owned()),
            "duplicate contract: {contract}"
        );
        let source = if proof.starts_with("CICL.") || proof.starts_with("KCheckSpec.") {
            Name::from_string(proof)
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
    for [proof, mutation] in &mutant_replays {
        let proof = proof.as_str();
        let mutation = mutation.as_str();
        assert!(
            consumed.insert(mutation.to_owned()),
            "duplicate mutation: {mutation}"
        );
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
        pins.keys().cloned().collect(),
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
    assert_eq!(
        row["meaning_sha256"]
            .as_str()
            .expect("full meaning hash")
            .len(),
        64
    );
}

#[test]
fn model_inventory_refuses_mutated_definition_body_and_level_params() {
    let (base_loaded, _, canonical, _) = inventory_fixture();
    let origin = base_loaded
        .get_constant_origin(&canonical)
        .expect("canonical origin")
        .clone();
    let mut env_a = Environment::for_lean_replay();
    let mut env_b = Environment::for_lean_replay();
    let mut env_c = Environment::for_lean_replay();
    let prop_sort = Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero()));
    for (env, level_name, body) in [
        (&mut env_a, "u", Expr::prop()),
        (
            &mut env_b,
            "u",
            Expr::pi(
                clean_kernel::BinderInfo::Default,
                Expr::prop(),
                Expr::prop(),
            ),
        ),
        (&mut env_c, "v", Expr::prop()),
    ] {
        env.add_decl(Declaration::Definition {
            name: canonical.clone(),
            level_params: vec![Name::from_string(level_name)],
            type_: prop_sort.clone(),
            value: body,
            is_reducible: true,
        })
        .expect("scratch model definition");
        assert!(env.set_constant_origin(canonical.clone(), origin.clone()));
    }
    let targets = BTreeSet::from([canonical]);
    let inv_a = model_declaration_inventory(&env_a, &targets);
    let inv_b = model_declaration_inventory(&env_b, &targets);
    let inv_c = model_declaration_inventory(&env_c, &targets);
    assert_eq!(
        inv_a["Alias.value"]["type_sha256"], inv_b["Alias.value"]["type_sha256"],
        "same level_params and type keep type_sha256 equal"
    );
    assert_ne!(
        inv_a["Alias.value"]["value_sha256"], inv_b["Alias.value"]["value_sha256"],
        "changing a non-theorem body anywhere in the model must change value_sha256"
    );
    // Preserve the expression-only type hash; bind universe names explicitly
    // and in the full kernel meaning hash.
    assert_eq!(
        inv_a["Alias.value"]["type_sha256"],
        inv_c["Alias.value"]["type_sha256"]
    );
    assert_ne!(
        inv_a["Alias.value"]["level_params"],
        inv_c["Alias.value"]["level_params"]
    );
    assert_ne!(
        inv_a["Alias.value"]["meaning_sha256"], inv_c["Alias.value"]["meaning_sha256"],
        "renaming level_params must change the pinned full meaning"
    );
}
