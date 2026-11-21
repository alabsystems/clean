// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Ph3 I.0: reproduce pinned Lean statements from the two original source modules.
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::Arc;

use clean_elab::module_driver::source_graph::{
    CapturedSourceGraph, CapturedSourceModule, SourceGraphError, SourceGraphOutput, SourceImport,
};
use clean_elab::module_driver::EnvironmentSetup;
use clean_kernel::expr::{ExprFolder, Literal};
use clean_kernel::lean_world::LeanWorld;
use clean_kernel::name::NameInner;
use clean_kernel::tc::TypeChecker;
use clean_kernel::{ConstantKind, Environment, Expr, ExprKind, Name, ReferenceKernel};
use clean_olean::meaning_digest::{MeaningDigests, Package, DOMAIN, FORMAT_VERSION};
use clean_olean::{
    load_module_with_deps, parse_module_file, pinned_lean_binary, read_artifact,
    reference_base_closed, reference_base_closed_with_source_wrappers, source_world_for_snapshot,
    ArtifactDepth, ClosedRecheckOptions, ConstantKind as StoredKind, DefinitionSafety, ImportWorld,
    ReferenceBase, SourceWorldDecision,
};
use serde::Serialize;
use sha2::{Digest, Sha256};

#[path = "self_proof_level_pin_reproduction/proof_transport.rs"]
mod proof_transport;

use proof_transport::{compare_monomorphic_proof_transport, proof_transport_seed_names};

const LEVEL: &str = "CICL.Level";
const CASES: &str = "CICL.LevelCases";
const LEVEL_TEXT: &str = include_str!("../../../theories/cic_l/CICL/Level.lean");
const CASES_TEXT: &str = include_str!("../../../theories/cic_l/CICL/LevelCases.lean");
const PIN: &str = include_str!("../../../lean-toolchain");
const PACKAGE_PIN: &str = include_str!("../../../theories/cic_l/lean-toolchain");
const COMMITTED_PINS: &str =
    include_str!("../../clean-olean/tests/cic_l_level/statement_pins.json");
const GITHASH: &str = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"; // Public Lean SHA. gitleaks:allow

struct Oracle {
    lean: PathBuf,
    lib: PathBuf,
    world: SourceWorldDecision,
}

impl Oracle {
    fn exact() -> Self {
        assert_eq!(PIN.trim(), PACKAGE_PIN.trim(), "I0 package toolchain drift");
        let world = source_world_for_snapshot().expect("I0 exact oracle world");
        assert_eq!(world.world(), LeanWorld::ORACLE);
        assert!(PIN.trim().ends_with(world.world().tag()));
        let ImportWorld::Explicit { lib, .. } = world.imports().expect("I0 oracle imports") else {
            panic!("I0 requires the declared artifact world");
        };
        let lib = lib.canonicalize().expect("I0 oracle library");
        let lean = pinned_lean_binary()
            .expect("I0 pinned Lean executable")
            .canonicalize()
            .expect("I0 pinned Lean executable identity");
        assert_eq!(
            lean.parent().and_then(Path::parent),
            lib.parent().and_then(Path::parent)
        );
        let version = Command::new(&lean)
            .arg("--githash")
            .output()
            .expect("Lean githash");
        assert_success(&version, "pinned Lean version");
        assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), GITHASH);
        Self { lean, lib, world }
    }

    fn command(&self, driver: &Path, root: &Path) -> Command {
        let mut command = Command::new(driver);
        let mut search = vec![self
            .lean
            .parent()
            .expect("I0 binary directory")
            .to_path_buf()];
        search.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        command
            .env(
                "PATH",
                std::env::join_paths(search).expect("I0 binary search path"),
            )
            .current_dir(root)
            .env(
                "LEAN_PATH",
                std::env::join_paths([root, &self.lib]).expect("I0 search path"),
            )
            .env_remove("LEAN_SRC_PATH");
        command
    }

    fn compile(&self, root: &Path, module: &str, text: &str) -> Output {
        let source = root.join(module_path(module, "lean"));
        let artifact = root.join(module_path(module, "olean"));
        fs::create_dir_all(source.parent().unwrap()).expect("I0 snapshot directory");
        fs::write(&source, text).expect("I0 exact source snapshot");
        self.command(&self.lean, root)
            .arg("-o")
            .arg(&artifact)
            .arg(&source)
            .output()
            .expect("I0 compile original source with pinned Lean")
    }
}

fn assert_success(output: &Output, purpose: &str) {
    assert!(
        output.status.success(),
        "{purpose}: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn module_path(module: &str, extension: &str) -> PathBuf {
    PathBuf::from(module.replace('.', "/")).with_extension(extension)
}

fn captured(module: &str, text: &str) -> CapturedSourceModule {
    CapturedSourceModule {
        name: Name::from_string(module),
        path: Path::new("theories/cic_l").join(module_path(module, "lean")),
        source: Arc::from(text),
    }
}

fn under_init(mut name: &Name) -> bool {
    let root = Name::from_string("Init");
    loop {
        if name == &root {
            return true;
        }
        name = match name.inner() {
            NameInner::Anon => return false,
            NameInner::Str(parent, _) | NameInner::Num(parent, _) => parent,
        };
    }
}

fn elaborate(
    oracle: &Oracle,
    modules: Vec<CapturedSourceModule>,
) -> Result<SourceGraphOutput, SourceGraphError> {
    let names: BTreeSet<_> = modules.iter().map(|module| module.name.clone()).collect();
    CapturedSourceGraph::new(modules)?.elaborate(
        &[Name::from_string(CASES)],
        EnvironmentSetup::default(),
        &oracle.world,
        &mut |from: &CapturedSourceModule, imported: &Name| {
            if names.contains(imported) {
                Ok(SourceImport::Captured(imported.clone()))
            } else if under_init(imported) {
                Ok(SourceImport::Artifact)
            } else {
                Err(SourceGraphError::Import {
                    module: from.name.clone(),
                    imported: imported.clone(),
                    reason: "unmounted I0 source import".into(),
                })
            }
        },
    )
}

fn pair(level: &str, cases: &str) -> Vec<CapturedSourceModule> {
    vec![captured(LEVEL, level), captured(CASES, cases)]
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

struct StoredModule {
    module: &'static str,
    names: BTreeSet<Name>,
    replayable: BTreeSet<Name>,
    theorems: BTreeSet<Name>,
}

fn read_module(root: &Path, module: &'static str, env: &Environment) -> StoredModule {
    let path = root.join(module_path(module, "olean"));
    let artifact =
        read_artifact(module, &path, ArtifactDepth::Records).expect("I0 actual artifact");
    assert!(
        !artifact.is_module,
        "I0 source header changed artifact layout: {module}"
    );
    let inventory = artifact
        .inventory
        .expect("Records inventory")
        .expect("I0 strict artifact inventory");
    let names: BTreeSet<_> = inventory
        .declarations()
        .iter()
        .map(|row| row.name().clone())
        .collect();
    assert_eq!(names.len(), artifact.names.len());
    assert_eq!(names, artifact.names.iter().cloned().collect());
    let parsed = parse_module_file(&path).expect("I0 authoritative records");
    assert_eq!(parsed.constants.len(), artifact.names.len());
    let mut replayable = BTreeSet::new();
    let mut theorems = BTreeSet::new();
    for (record, name) in parsed.constants.iter().zip(&artifact.names) {
        assert_eq!(record.name, name.to_string(), "I0 artifact record order");
        let compiler_copy = matches!(
            record.definition_safety,
            Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial)
        );
        if compiler_copy {
            assert_eq!(record.kind, StoredKind::Definition);
            let NameInner::Str(parent, suffix) = name.inner() else {
                panic!("I0 unexpected compiler copy name {name}");
            };
            assert_eq!(suffix.as_ref(), "_unsafe_rec");
            assert!(
                names.contains(parent.as_ref()),
                "I0 unowned compiler copy counterpart {parent}"
            );
            assert!(env
                .get_const(parent)
                .is_some_and(|info| info.kind == ConstantKind::Definition && info.value.is_some()));
            assert!(
                env.get_const(name).is_none(),
                "resident compiler copy {name}"
            );
        } else {
            let resident = env
                .get_const(name)
                .unwrap_or_else(|| panic!("I0 missing stored declaration {name}"));
            assert_eq!(
                record.kind == StoredKind::Theorem,
                resident.kind == ConstantKind::Theorem,
                "I0 theorem kind changed during import: {name}"
            );
            if record.kind == StoredKind::Theorem {
                assert!(theorems.insert(name.clone()));
            }
            assert!(replayable.insert(name.clone()));
        }
    }
    eprintln!(
        "I0_ARTIFACT {module} {}",
        sha(&fs::read(&path).expect("I0 artifact bytes"))
    );
    StoredModule {
        module,
        names,
        replayable,
        theorems,
    }
}

fn admitted(base: ReferenceBase) -> Result<ReferenceKernel, String> {
    if !base.report.passed() || !base.entry_refusals.is_empty() {
        return Err(format!("{:?} {:?}", base.report, base.entry_refusals));
    }
    base.into_kernel().map_err(|report| format!("{report:?}"))
}

fn check_original_body_agreement(pinned: &ReferenceKernel, source: &ReferenceKernel) {
    for dependency in ["CICL.Level.Scoped", "CICL.Level.eval", "CICL.Level.subst"] {
        let name = Name::from_string(dependency);
        let resident = pinned
            .environment()
            .get_const(&name)
            .expect("I0 pinned dependency");
        let captured = source
            .environment()
            .get_const(&name)
            .expect("I0 source dependency");
        assert!(resident.level_params.is_empty() && captured.level_params.is_empty());
        assert_eq!(resident.type_, captured.type_);
        let type_ = &resident.type_;
        let resident_value = resident.value.as_ref().expect("I0 pinned dependency body");
        let captured_value = captured.value.as_ref().expect("I0 source dependency body");
        let sort = TypeChecker::new(pinned.environment())
            .infer_type(type_)
            .expect("I0 dependency type has a sort");
        let ExprKind::Sort(level) = sort.kind() else {
            panic!("I0 dependency type did not infer to a sort: {dependency}");
        };
        let eq = Expr::const_(Name::from_string("Eq"), vec![level.clone()]);
        let refl = Expr::const_(Name::from_string("Eq.refl"), vec![level.clone()]);
        let original = Expr::apps(
            eq.clone(),
            [
                type_.clone(),
                resident_value.clone(),
                resident_value.clone(),
            ],
        );
        let proposed = Expr::apps(
            eq,
            [
                type_.clone(),
                resident_value.clone(),
                captured_value.clone(),
            ],
        );
        let proof = Expr::apps(refl, [type_.clone(), resident_value.clone()]);
        pinned
            .check_closed_term(&original, &proof)
            .expect("I0 reflexivity control in pinned world");
        let captured_in_pinned = pinned
            .check_closed_term(type_, captured_value)
            .map(|_| ())
            .map_err(|refusal| refusal.to_string());
        let resident_in_source = source
            .check_closed_term(type_, resident_value)
            .map(|_| ())
            .map_err(|refusal| refusal.to_string());
        let agreement = pinned
            .check_closed_term(&proposed, &proof)
            .map(|_| ())
            .map_err(|refusal| refusal.to_string());
        eprintln!(
            "I0_BODY_AGREEMENT {dependency} {}",
            serde_json::json!({
                "captured_body_checked_in_pinned_world": captured_in_pinned,
                "pinned_body_checked_in_source_world": resident_in_source,
                "reflexivity_checked_in_pinned_world": agreement,
                "pinned_body": resident_value,
                "captured_body": captured_value,
            })
        );
    }
}

fn check_constructor_helpers(
    pinned: &ReferenceKernel,
    source: &ReferenceKernel,
    package: &Package,
    actual: &SourceGraphOutput,
) {
    let guarded = MeaningDigests::new(source.environment(), package);
    let expected_meaning = MeaningDigests::new(pinned.environment(), package);
    for suffix in [
        "ctorIdx",
        "ctorElimType",
        "ctorElim",
        "noConfusionType",
        "noConfusion",
        "zero.elim",
        "succ.elim",
        "max.elim",
        "imax.elim",
        "param.elim",
        "succ.noConfusion",
        "max.noConfusion",
        "imax.noConfusion",
        "param.noConfusion",
    ] {
        let name = Name::from_string(&format!("{LEVEL}.{suffix}"));
        assert!(actual.modules[&Name::from_string(LEVEL)]
            .introduced
            .contains(&name));
        let expected = pinned
            .environment()
            .get_const(&name)
            .expect("pinned constructor helper");
        let observed = source
            .environment()
            .get_const(&name)
            .expect("source constructor helper");
        assert_eq!(observed, expected, "{name}");
        assert_eq!(
            guarded.digest(&name).unwrap(),
            expected_meaning.digest(&name).unwrap(),
            "{name}"
        );
    }
    let name = Name::from_string("CICL.Level.ctorIdx");
    assert!(actual.modules[&Name::from_string(LEVEL)]
        .introduced
        .contains(&name));
    assert!(actual.environment.is_protected(&name));
    let emitted = source
        .environment()
        .get_const(&name)
        .expect("checked index");
    assert!(emitted.level_params.is_empty());
    let stored_digest = expected_meaning
        .digest(&name)
        .expect("pinned index meaning");

    struct WrongIndex;
    impl ExprFolder for WrongIndex {
        fn fold_lit(&mut self, _: &Literal) -> Expr {
            Expr::nat_lit(42)
        }
    }
    let value = emitted.value.as_ref().expect("checked index body");
    let changed = WrongIndex.fold_expr(value);
    assert_ne!(&changed, value);
    pinned
        .check_closed_term(&emitted.type_, &changed)
        .expect("changed index remains well typed");
    let level = TypeChecker::new(pinned.environment())
        .infer_sort(&emitted.type_)
        .expect("index type sort");
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level.clone()]),
        [emitted.type_.clone(), value.clone()],
    );
    let conclusion = |other| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
            [emitted.type_.clone(), value.clone(), other],
        )
    };
    pinned
        .check_closed_term(&conclusion(value.clone()), &refl)
        .expect("unchanged index reflexivity");
    assert!(pinned
        .check_closed_term(&conclusion(changed), &refl)
        .is_err());
    eprintln!("I0_CONSTRUCTOR_INDEX {name} {stored_digest}; checked different index refused");
}

#[derive(Debug, Serialize)]
struct StatementRow {
    name: Name,
    pinned_level_params: Vec<Name>,
    actual_level_params: Option<Vec<Name>>,
    statement_equal: bool,
    pinned_digest: String,
    committed_digest: Option<String>,
    actual_digest: Result<String, String>,
}

impl StatementRow {
    fn matches(&self) -> bool {
        self.statement_equal && self.actual_digest.as_ref() == Ok(&self.pinned_digest)
    }

    fn constructor_injectivity(&self) -> bool {
        matches!(self.name.inner(), NameInner::Str(_, suffix) if matches!(suffix.as_ref(), "inj" | "injEq"))
    }
}

fn direct_meaning_differences(
    stored: &[StoredModule],
    pinned: &Environment,
    source: &Environment,
) -> BTreeSet<Name> {
    let mut different = BTreeSet::new();
    for module in stored {
        for name in module.replayable.difference(&module.theorems) {
            let (Some(expected), Some(actual)) = (pinned.get_const(name), source.get_const(name))
            else {
                continue;
            };
            // Isolate the canonical record by using a one-record package. The
            // actual statement pin below still uses its entire package closure.
            let record = Package::of_names(BTreeSet::from([name.clone()]));
            let expected_digest = MeaningDigests::new(pinned, &record)
                .digest(name)
                .expect("I0 resident pinned record");
            let actual_digest = MeaningDigests::new(source, &record)
                .digest(name)
                .expect("I0 resident source record");
            if expected_digest != actual_digest {
                different.insert(name.clone());
                eprintln!(
                    "I0_DEPENDENCY_RECORD {name} {}",
                    serde_json::json!({
                        "pinned_digest": expected_digest,
                        "actual_digest": actual_digest,
                        "kind_equal": expected.kind == actual.kind,
                        "universe_params_equal": expected.level_params == actual.level_params,
                        "type_equal": expected.type_ == actual.type_,
                        "value_equal": expected.value == actual.value,
                        "pinned_is_reducible": expected.is_reducible,
                        "actual_is_reducible": actual.is_reducible,
                        "pinned_reducibility": expected.reducibility,
                        "actual_reducibility": actual.reducibility,
                        "inductive_record_equal": pinned.get_inductive(name) == source.get_inductive(name),
                        "constructor_record_equal": pinned.get_constructor(name) == source.get_constructor(name),
                        "recursor_record_equal": pinned.get_recursor(name) == source.get_recursor(name),
                    })
                );
            }
        }
    }
    different
}

fn compare(
    stored: &[StoredModule],
    package: &Package,
    pinned: &Environment,
    actual: &SourceGraphOutput,
    measured_source: &Environment,
) -> (Vec<StatementRow>, BTreeSet<Name>) {
    let pins: BTreeMap<String, String> =
        serde_json::from_str(COMMITTED_PINS).expect("I0 committed CIC_L statement pins");
    let different = direct_meaning_differences(stored, pinned, measured_source);
    let pinned_digests = MeaningDigests::new(pinned, package);
    let source_digests = MeaningDigests::new(measured_source, package);
    let mut statements = Vec::new();
    let mut source_only_theorems = BTreeSet::new();
    for module in stored {
        let source = &actual.modules[&Name::from_string(module.module)].introduced;
        eprintln!(
            "I0_ROSTER {} {}",
            module.module,
            serde_json::json!({
                "stored": module.names,
                "stored_compiler_copies": module.names.difference(&module.replayable).collect::<Vec<_>>(),
                "source_introduced": source,
                "stored_only_replayable": module.replayable.difference(source).collect::<Vec<_>>(),
                "source_only": source.difference(&module.replayable).collect::<Vec<_>>(),
            })
        );
        for name in source.difference(&module.theorems) {
            let info = measured_source
                .get_const(name)
                .expect("I0 source-only declaration");
            if info.kind == ConstantKind::Theorem {
                eprintln!("I0_SOURCE_ONLY_THEOREM {name}: {}", info.type_);
                assert!(source_only_theorems.insert(name.clone()));
            }
        }
        for name in &module.theorems {
            let expected = pinned.get_const(name).expect("I0 owned oracle declaration");
            assert_eq!(expected.kind, ConstantKind::Theorem);
            assert!(
                expected.value.is_some(),
                "I0 pinned theorem without original proof {name}"
            );
            let observed = source.contains(name).then(|| {
                measured_source
                    .get_const(name)
                    .expect("I0 resident owned source declaration")
            });
            let statement_equal = observed.is_some_and(|constant| {
                constant.kind == ConstantKind::Theorem
                    && constant.value.is_some()
                    && constant.level_params == expected.level_params
                    && constant.type_ == expected.type_
            });
            let pinned_digest = pinned_digests
                .statement_digest(name, &expected.level_params, &expected.type_)
                .expect("I0 pinned statement closure");
            let actual_digest = match observed {
                Some(constant)
                    if constant.kind == ConstantKind::Theorem && constant.value.is_some() =>
                {
                    source_digests
                        .statement_digest(name, &constant.level_params, &constant.type_)
                        .map_err(|error| error.to_string())
                }
                _ => Err("source did not introduce a theorem with a proof at this name".into()),
            };
            if statement_equal
                && actual_digest
                    .as_ref()
                    .is_ok_and(|digest| digest != &pinned_digest)
            {
                let pinned_names = pinned_digests.closure(name).expect("I0 pinned closure");
                let source_names = source_digests.closure(name).expect("I0 source closure");
                let different_common_records: Vec<_> = pinned_names
                    .intersection(&source_names)
                    .filter(|dependency| different.contains(*dependency))
                    .map(ToString::to_string)
                    .collect();
                eprintln!(
                    "I0_MEANING_DIFFERENCE {name} {}",
                    serde_json::json!({
                        "different_common_records": different_common_records,
                        "pinned_only_dependencies": pinned_names.difference(&source_names).map(ToString::to_string).collect::<Vec<_>>(),
                        "source_only_dependencies": source_names.difference(&pinned_names).map(ToString::to_string).collect::<Vec<_>>(),
                    })
                );
            }
            if !statement_equal {
                eprintln!(
                    "I0_STATEMENT_DIFFERENCE {name}: pinned={} actual={}",
                    expected.type_,
                    observed.map_or_else(|| "absent".into(), |constant| constant.type_.to_string())
                );
            }
            let row = StatementRow {
                name: name.clone(),
                pinned_level_params: expected.level_params.clone(),
                actual_level_params: observed.map(|constant| constant.level_params.clone()),
                statement_equal,
                pinned_digest,
                committed_digest: pins.get(&name.to_string()).cloned(),
                actual_digest,
            };
            eprintln!(
                "I0_STATEMENT {}",
                serde_json::to_string(&row).expect("I0 comparison row")
            );
            statements.push(row);
        }
    }
    (statements, source_only_theorems)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Reproduction {
    Complete,
    ConstructorInjectivity,
    CourseOfValues,
    StructuralDefinitions,
}

fn check_original_and_controls(reproduction: Reproduction) {
    let oracle = Oracle::exact();
    let dir = tempfile::tempdir().expect("I0 local oracle artifacts");
    let root = dir.path();
    for (module, text) in [(LEVEL, LEVEL_TEXT), (CASES, CASES_TEXT)] {
        assert_success(&oracle.compile(root, module, text), module);
        eprintln!("I0_SOURCE {module} {}", sha(text.as_bytes()));
    }
    let leanchecker = oracle.lean.with_file_name("leanchecker");
    assert_success(
        &oracle
            .command(&leanchecker, root)
            .args(["--fresh", CASES])
            .output()
            .expect("I0 fresh independent Lean recheck"),
        "I0 fresh independent Lean recheck",
    );
    eprintln!("I0_ORACLE {GITHASH} {DOMAIN} v{FORMAT_VERSION}");

    let mut artifact_env = Environment::for_lean_replay();
    load_module_with_deps(
        &mut artifact_env,
        CASES,
        &[root.to_path_buf(), oracle.lib.clone()],
    )
    .expect("I0 import actual pinned-Lean artifacts");
    let stored = [
        read_module(root, LEVEL, &artifact_env),
        read_module(root, CASES, &artifact_env),
    ];
    let pinned_names: BTreeSet<_> = stored
        .iter()
        .flat_map(|row| row.replayable.iter().cloned())
        .collect();
    let options = ClosedRecheckOptions::default();
    let pinned = reference_base_closed(&artifact_env, &pinned_names, &options)
        .map_err(|error| error.to_string())
        .and_then(admitted)
        .expect("I0 fenced replay of pinned artifacts");
    let package = Package::of_module_names(
        stored
            .iter()
            .map(|row| (row.module.to_owned(), row.names.iter().cloned().collect())),
    );

    let actual =
        elaborate(&oracle, pair(LEVEL_TEXT, CASES_TEXT)).expect("I0 actual original source graph");
    let source_names = actual
        .modules
        .values()
        .flat_map(|row| row.introduced.iter().cloned())
        .collect();
    let source = reference_base_closed_with_source_wrappers(
        &actual.environment,
        &source_names,
        &source_names,
        &options,
    )
    .map_err(|error| error.to_string())
    .and_then(admitted);
    let measured_source = match &source {
        Ok(kernel) => {
            for wrapper in ["CICL.Level.casesOn", "CICL.Level.recOn"] {
                let name = Name::from_string(wrapper);
                let captured = actual
                    .environment
                    .get_const(&name)
                    .expect("I0 source wrapper");
                let checked = kernel
                    .environment()
                    .get_const(&name)
                    .expect("I0 checked wrapper");
                assert_eq!(checked.kind, ConstantKind::Definition);
                assert!(captured.value.is_some());
                assert_eq!(checked.value, captured.value);
                assert!(kernel.environment().get_recursor(&name).is_none());
            }
            eprintln!("I0_SOURCE_ENVIRONMENT fenced");
            check_original_body_agreement(&pinned, kernel);
            // A source proof can use authentic Init facts that none of the
            // original proof/type roots cite. Check those facts independently
            // before trying to transport that proof. The original statement
            // digest comparison still uses the original pinned cone above.
            let supplemental = proof_transport_seed_names(
                kernel.environment(),
                pinned.environment(),
                &artifact_env,
                &stored,
            );
            let transport = if supplemental.is_empty() {
                None
            } else {
                eprintln!("I0_PROOF_TRANSPORT_PINNED_INIT {:?}", supplemental);
                let targets = pinned_names.union(&supplemental).cloned().collect();
                Some(
                    reference_base_closed(&artifact_env, &targets, &options)
                        .map_err(|error| error.to_string())
                        .and_then(admitted)
                        .expect("I0 proof transport supplemental pinned Init fence"),
                )
            };
            compare_monomorphic_proof_transport(
                transport.as_ref().unwrap_or(&pinned),
                kernel,
                &stored,
            );
            kernel.environment()
        }
        Err(reason) => {
            eprintln!("I0_FENCED_REENTRY actual Clean owned declarations: {reason}");
            eprintln!("I0_SOURCE_ENVIRONMENT elaborated_diagnostic_only");
            &actual.environment
        }
    };
    let (statements, source_only_theorems) = compare(
        &stored,
        &package,
        pinned.environment(),
        &actual,
        measured_source,
    );
    assert!(
        !statements.is_empty(),
        "I0 cannot compare an empty theorem roster"
    );

    let unmounted = elaborate(&oracle, vec![captured(CASES, CASES_TEXT)])
        .err()
        .expect("missing module refusal");
    assert!(
        matches!(unmounted, SourceGraphError::Import { imported, .. } if imported == Name::from_string(LEVEL))
    );
    let fictional =
        LEVEL_TEXT.replacen("import Init.Data.Nat.MinMax", "import Init.I0Fictional", 1);
    assert_ne!(fictional, LEVEL_TEXT);
    let wrong_world = elaborate(&oracle, pair(&fictional, CASES_TEXT))
        .err()
        .expect("fictional Init refusal");
    assert!(wrong_world.to_string().contains("Init.I0Fictional"));
    eprintln!("I0_CONTROL unmounted-import refused; fictional-Init refused");

    let original = "theorem imax_positive : eval zeros (.imax one two) = 2 := rfl";
    assert_eq!(CASES_TEXT.matches(original).count(), 1);
    let invalid = CASES_TEXT.replacen(
        original,
        "theorem imax_positive : eval zeros (.imax one two) = 1 := rfl",
        1,
    );
    let lean_refusal = oracle.compile(root, CASES, &invalid);
    assert!(!lean_refusal.status.success());
    assert!(String::from_utf8_lossy(&lean_refusal.stdout).contains("rfl"));
    let clean_refusal = elaborate(&oracle, pair(LEVEL_TEXT, &invalid))
        .err()
        .expect("ill-typed source refusal");
    assert!(
        matches!(
            &clean_refusal,
            SourceGraphError::Module { module, reason, .. }
                if module == &Name::from_string(CASES)
                    && reason.starts_with("Type mismatch: expected CICL.Level.eval ")
                    && reason.contains(" = 1, got CICL.Level.eval ")
        ),
        "{clean_refusal}"
    );
    eprintln!("I0_CONTROL ill-typed-original-theorem refused by both elaborators");

    let valid = CASES_TEXT.replacen(
        original,
        "theorem imax_positive : eval zeros (.imax one three) = 3 := rfl",
        1,
    );
    assert_success(
        &oracle.compile(root, CASES, &valid),
        "I0 changed pinned statement",
    );
    let alternate =
        elaborate(&oracle, pair(LEVEL_TEXT, &valid)).expect("I0 well-typed source change");
    let target = Name::from_string("CICL.LevelCases.imax_positive");
    let module = Name::from_string(CASES);
    assert!(actual.modules[&module].introduced.contains(&target));
    assert!(alternate.modules[&module].introduced.contains(&target));
    let original = actual
        .environment
        .get_const(&target)
        .expect("I0 original theorem");
    let modified = alternate
        .environment
        .get_const(&target)
        .expect("I0 changed theorem");
    assert_eq!(original.kind, ConstantKind::Theorem);
    assert_eq!(modified.kind, ConstantKind::Theorem);
    assert!(original.value.is_some() && modified.value.is_some());
    assert_eq!(original.level_params, modified.level_params);
    assert_ne!(original.type_, modified.type_);
    assert_ne!(
        MeaningDigests::new(&actual.environment, &package)
            .statement_digest(&target, &original.level_params, &original.type_)
            .expect("I0 original source statement meaning"),
        MeaningDigests::new(&alternate.environment, &package)
            .statement_digest(&target, &modified.level_params, &modified.type_)
            .expect("I0 changed source statement meaning")
    );
    let pinned_statement = &pinned
        .environment()
        .get_const(&target)
        .expect("I0 pinned original theorem")
        .type_;
    pinned
        .check_closed_term(pinned_statement, original.value.as_ref().unwrap())
        .expect("I0 original proof at original pinned statement");
    assert!(
        pinned
            .check_closed_term(pinned_statement, modified.value.as_ref().unwrap())
            .is_err(),
        "I0 same-name changed proof must be refused at the original pinned statement"
    );
    eprintln!(
        "I0_CONTROL well-typed-original-theorem change accepted with a different digest and its proof refused at the pinned statement"
    );

    let mismatch: Vec<_> = statements
        .iter()
        .filter(|row| !row.matches())
        .map(|row| row.name.to_string())
        .collect();
    let committed_mismatch: Vec<_> = statements
        .iter()
        .filter(|row| row.committed_digest.as_ref() != Some(&row.pinned_digest))
        .map(|row| row.name.to_string())
        .collect();
    eprintln!(
        "I0_TOTAL statements={} mismatches={} source_only={} committed_mismatches={} fenced={}",
        statements.len(),
        mismatch.len(),
        source_only_theorems.len(),
        committed_mismatch.len(),
        source.is_ok()
    );
    if reproduction == Reproduction::StructuralDefinitions {
        assert!(source.is_ok() && source_only_theorems.is_empty() && committed_mismatch.is_empty());
        let matcher_equations: Vec<_> = statements
            .iter()
            .filter(|row| {
                row.name
                    .to_string()
                    .starts_with("_private.CICL.Level.0.CICL.Level.eval.match_")
            })
            .collect();
        assert_eq!(
            matcher_equations.len(),
            7,
            "I0 original private matcher equation count"
        );
        let recursion_equations: Vec<_> = statements
            .iter()
            .filter(|row| {
                let name = row.name.to_string();
                name.starts_with("CICL.Level.eval.eq_") || name.starts_with("CICL.Level.subst.eq_")
            })
            .collect();
        assert_eq!(
            recursion_equations.len(),
            12,
            "I0 original standalone recursion equation count"
        );
        let size_equations: Vec<_> = statements
            .iter()
            .filter(|row| row.name.to_string().ends_with(".sizeOf_spec"))
            .collect();
        assert_eq!(size_equations.len(), 5, "I0 original SizeOf equation count");
        let different_equations: Vec<_> = matcher_equations
            .iter()
            .chain(&recursion_equations)
            .chain(&size_equations)
            .filter(|row| {
                !row.statement_equal || row.actual_digest.as_ref() != Ok(&row.pinned_digest)
            })
            .map(|row| row.name.clone())
            .collect();
        eprintln!(
            "I0_GENERATED_EQUATIONS statements={} mismatches={}",
            matcher_equations.len() + recursion_equations.len() + size_equations.len(),
            different_equations.len()
        );
        for suffix in ["eval.match_1", "eval.match_3"] {
            let name = Name::from_string(&format!("{LEVEL}.{suffix}"));
            let expected = artifact_env
                .get_matcher_info(&name)
                .expect("matcher metadata from pinned Lean");
            assert_eq!(
                actual.environment.get_matcher_info(&name),
                Some(expected),
                "source-generated matcher metadata for {name}"
            );
        }
        check_recursive_definition_records(pinned.environment(), measured_source, &package);
        check_constructor_helpers(&pinned, source.as_ref().unwrap(), &package, &actual);
        for module in &stored {
            assert_eq!(
                actual.modules[&Name::from_string(module.module)].introduced,
                module.replayable,
                "{} safe source ownership",
                module.module
            );
        }
        assert!(
            different_equations.is_empty(),
            "I0 generated equation differences: {different_equations:?}"
        );
        return;
    }
    if reproduction == Reproduction::CourseOfValues {
        assert!(source.is_ok() && source_only_theorems.is_empty() && committed_mismatch.is_empty());
        let mut helper_mismatches = Vec::new();
        let pinned_meaning = MeaningDigests::new(pinned.environment(), &package);
        let source_meaning = MeaningDigests::new(measured_source, &package);
        for helper in ["below", "brecOn", "brecOn.go"] {
            let name = Name::from_string(&format!("{LEVEL}.{helper}"));
            let expected = pinned
                .environment()
                .get_const(&name)
                .expect("pinned helper");
            let actual = measured_source.get_const(&name);
            let same_type = actual.is_some_and(|info| {
                expected.level_params == info.level_params && expected.type_ == info.type_
            });
            let same_body = actual.is_some_and(|info| expected.value == info.value);
            let expected_digest = pinned_meaning.digest(&name).expect("pinned helper meaning");
            let actual_digest = source_meaning
                .digest(&name)
                .map_err(|error| error.to_string());
            eprintln!("I0_COURSE_OF_VALUES {name} type={same_type} body={same_body} pinned={expected_digest} actual={actual_digest:?}");
            if !same_type || !same_body || actual_digest.as_ref() != Ok(&expected_digest) {
                helper_mismatches.push(name);
            }
        }
        assert!(
            helper_mismatches.is_empty(),
            "I0 course-of-values helper mismatches: {helper_mismatches:?}"
        );
        assert!(
            !mismatch.iter().any(|name| name == "CICL.Level.brecOn.eq"),
            "I0 course-of-values equation mismatch"
        );
        return;
    }
    if reproduction == Reproduction::ConstructorInjectivity {
        let constructors: Vec<_> = statements
            .iter()
            .filter(|row| row.constructor_injectivity())
            .collect();
        let differing: Vec<_> = constructors
            .iter()
            .filter(|row| !row.matches())
            .map(|row| row.name.to_string())
            .collect();
        assert_eq!(
            constructors.len(),
            8,
            "I0 original constructor theorem count"
        );
        eprintln!(
            "I0_CONSTRUCTOR_TOTAL statements={} mismatches={}",
            constructors.len(),
            differing.len()
        );
        assert!(
            source.is_ok() && differing.is_empty() && source_only_theorems.is_empty() && committed_mismatch.is_empty(),
            "I0_CONSTRUCTOR_INJECTIVITY_DIFFERENCES constructors={differing:?} source_only={source_only_theorems:?} committed={committed_mismatch:?} fenced={}",
            source.is_ok()
        );
        return;
    }
    assert!(
        source.is_ok() && mismatch.is_empty() && source_only_theorems.is_empty() && committed_mismatch.is_empty(),
        "I0_STATEMENT_REPRODUCTION_DIFFERENCES pinned={mismatch:?} source_only={source_only_theorems:?} committed={committed_mismatch:?} fenced={}",
        source.is_ok()
    );
}

fn check_recursive_definition_records(
    pinned: &Environment,
    source: &Environment,
    package: &Package,
) {
    let pinned_meaning = MeaningDigests::new(pinned, package);
    let source_meaning = MeaningDigests::new(source, package);
    let mut differences = Vec::new();
    for name in [
        "_sizeOf_1",
        "_sizeOf_inst",
        "eval.match_1",
        "eval.match_3",
        "eval._f",
        "eval",
        "subst._f",
        "subst",
        "Scoped._f",
        "Scoped",
        "eval._sunfold",
        "subst._sunfold",
        "Scoped._sunfold",
    ]
    .into_iter()
    .map(|suffix| Name::from_string(&format!("{LEVEL}.{suffix}")))
    .chain(
        [
            "_private.CICL.Level.0.CICL.Level.eval.match_1.splitter",
            "_private.CICL.Level.0.CICL.Level.eval.match_3.splitter",
        ]
        .into_iter()
        .map(Name::from_string),
    ) {
        let expected = pinned
            .get_const(&name)
            .expect("I0 pinned recursive definition");
        let actual = source.get_const(&name);
        let same_header = actual.is_some_and(|actual| {
            expected.kind == actual.kind
                && expected.level_params == actual.level_params
                && expected.type_ == actual.type_
                && expected.reducibility == actual.reducibility
        });
        let same_body = actual.is_some_and(|actual| expected.value == actual.value);
        let expected_digest = pinned_meaning
            .digest(&name)
            .expect("I0 pinned recursive definition meaning");
        let actual_digest = source_meaning
            .digest(&name)
            .map_err(|error| error.to_string());
        eprintln!("I0_RECURSIVE_DEFINITION {name} header={same_header} body={same_body} pinned={expected_digest} actual={actual_digest:?}");
        if !same_header || !same_body || actual_digest.as_ref() != Ok(&expected_digest) {
            differences.push(name);
        }
    }
    assert!(
        differences.is_empty(),
        "I0 recursive definition differences: {differences:?}"
    );
}

fn run_original(reproduction: Reproduction) {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(move || check_original_and_controls(reproduction))
        .expect("I0 worker")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

#[test]
fn level_source_reproduces_pinned_lean_statements() {
    run_original(Reproduction::Complete);
}

#[test]
fn level_source_reproduces_constructor_injectivity() {
    run_original(Reproduction::ConstructorInjectivity);
}

#[test]
fn level_source_reproduces_course_of_values() {
    run_original(Reproduction::CourseOfValues);
}

#[test]
fn level_source_reproduces_recursive_definitions() {
    run_original(Reproduction::StructuralDefinitions);
}

#[test]
fn later_sibling_uses_the_source_generated_nat_matcher() {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(|| {
            let oracle = Oracle::exact();
            let (level, _) = LEVEL_TEXT
                .split_once("\ndef subst ")
                .expect("original Level.eval");
            let original = include_str!("../../../theories/cic_l/CICL/LevelDecide.lean");
            let (_, after_name) = original
                .split_once("theorem eval_imax_succ ")
                .expect("original theorem");
            let (statement, _) = after_name.split_once("\n\n").expect("theorem boundary");
            let sibling =
                format!("{level}\ntheorem eval_imax_succ {statement}\nend Level\nend CICL\n");
            let import = "prelude\nimport CICL.Level\n";
            let graph =
                elaborate(&oracle, pair(&sibling, import)).expect("same-module matcher selection");
            assert!(graph
                .environment
                .get_matcher_info(&Name::from_string("CICL.Level.eval.match_1"))
                .is_some());
            assert!(graph
                .environment
                .get_const(&Name::from_string("CICL.Level.eval_imax_succ"))
                .is_some());
            let changed = sibling.replace("(eval ρ v) := by", "(eval ρ v) + 1 := by");
            assert_ne!(sibling, changed);
            let error = elaborate(&oracle, pair(&changed, import))
                .err()
                .expect("different branch result refused");
            let SourceGraphError::Module { module, reason, .. } = error else {
                panic!("expected the changed theorem body to fail: {error}");
            };
            assert_eq!(module, Name::from_string(LEVEL));
            let start = changed.rfind("simp only").expect("changed theorem tactic");
            assert!(reason.contains("unsolved goal"), "{reason}");
            assert!(
                reason.contains(&format!(
                    "at source bytes {start}..{}",
                    start + "simp".len()
                )),
                "{reason}"
            );
        })
        .expect("source matcher worker")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}
