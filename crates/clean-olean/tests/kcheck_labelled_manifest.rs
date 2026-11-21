// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Additional W3 identities for the actual adopted checker. The legacy
//! expression/definition-bundle pins and their controls remain independent.
//! This is pinned-Lean artifact identity plus fenced native re-entry; it is
//! not Clean source elaboration, an island build, compiled lineage or authority.
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_kernel::name::NameInner;
use clean_kernel::{ConstantKind, Environment, Expr, ExprKind, Level, Name};
use clean_olean::meaning_digest::{MeaningDigests, Package, DOMAIN, FORMAT_VERSION, RECORD_DOMAIN};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, parse_module_file, read_artifact, reference_base_closed, ArtifactDepth,
    ClosedRecheckOptions, DefinitionSafety,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const MANIFEST: &str = "data/kcheck_labelled_canonical_manifest.json";
const EXPORT: &str = "CLEAN_KCHECK_LABELLED_MANIFEST_EXPORT";
const FAMILY: &str = "kcheck_labelled";
const ROOT: &str = "CleanQualification.kcheck_labelled";
const ROSTER: &str = "scripts/kcheck_labelled_manifest_roster.lean";
const LEGACY_PIN_COUNT: usize = 3_611;
const THEORIES: [(&str, usize); 4] = [
    ("cic_l", 68),
    ("cic_l_model", 162),
    ("kcheck_spec", 106),
    ("kcheck_labelled", 90),
];
const SELF_SOURCE: &[u8] = include_bytes!("kcheck_labelled_manifest.rs");
const ROSTER_SOURCE: &[u8] =
    include_bytes!("../../../scripts/kcheck_labelled_manifest_roster.lean");
const DIGEST_SOURCE: &[u8] = include_bytes!("../src/meaning_digest.rs");
const LEGACY_SOURCE: &[u8] = include_bytes!("kcheck_labelled.rs");

// Same 79 public definition roots as the legacy CHECKER table. A source check
// below enforces exact ordered agreement; its legacy hashing code is untouched.
const DEFINITIONS: &[&str] = &[
    "KCheck.readNat",
    "KCheck.decodeAt",
    "KCheck.Advice.start",
    "KCheck.Advice.read",
    "KCheck.Advice.exhausted",
    "KCheck.encodeNat",
    "KCheck.Token.encode",
    "KCheck.encode",
    "KCheck.encodeFrames",
    "KCheck.splitFrames",
    "KCheck.insertOffset",
    "KCheck.reportJoin",
    "KCheck.reportShift",
    "KCheck.reportOfLevel",
    "KCheck.reportAddLevel",
    "KCheck.reportInstantiate",
    "KCheck.reportStart",
    "KCheck.levelSame",
    "KCheck.levelsSame",
    "KCheck.Term.closeAt",
    "KCheck.Term.sameErasure",
    "KCheck.Term.getSpine",
    "KCheck.Term.getSpineAux",
    "KCheck.ProjectionPacket.termExact",
    "KCheck.ProjectionPacket.entryExact",
    "KCheck.ProjectionPacket.recognise",
    "KCheck.UnitFamilyPacket.ruleExact",
    "KCheck.UnitFamilyPacket.rulesExact",
    "KCheck.UnitFamilyPacket.familyExact",
    "KCheck.UnitFamilyPacket.lookupExact",
    "KCheck.UnitFamilyPacket.familyMember",
    "KCheck.UnitFamilyPacket.oldRecognise",
    "KCheck.UnitFamilyPacket.fresh",
    "KCheck.UnitFamilyPacket.scopedLevel",
    "KCheck.UnitFamilyPacket.sourceBlock",
    "KCheck.UnitFamilyPacket.extract",
    "KCheck.UnitFamilyPacket.reportsOf",
    "KCheck.UnitFamilyPacket.outputsExact",
    "KCheck.UnitFamilyFrames.parse",
    "KCheck.familyOfRecursor",
    "KCheck.findRule",
    "KCheck.leadingCount",
    "KCheck.recursorArity",
    "KCheck.matchesExpr",
    "KCheck.entryMatches",
    "KCheck.recogniseBlock",
    "KCheck.levelsEqv",
    "KCheck.next",
    "KCheck.lookupLocal",
    "KCheck.findEntry",
    "KCheck.unfoldHead",
    "KCheck.projectionGuard",
    "KCheck.projectionFieldType",
    "KCheck.projectionEta",
    "KCheck.redexAt",
    "KCheck.iotaReduct",
    "KCheck.instR",
    "KCheck.ctorStoredResult",
    "KCheck.ctorResultArgs",
    "KCheck.whnf",
    "KCheck.conv",
    "KCheck.inferAnn",
    "KCheck.check",
    "KCheck.walk",
    "KCheck.levelWithin",
    "KCheck.exprLevelsWithin",
    "KCheck.ordinaryParts",
    "KCheck.checkOrdinary",
    "KCheck.blockName",
    "KCheck.unitFormer",
    "KCheck.unitConstructor",
    "KCheck.unitRecursor",
    "KCheck.unitInstall",
    "KCheck.checkUnitFamily",
    "KCheck.kcheck",
    "KCheck.kcheckBytes",
    "KCheck.base",
    "KCheck.kcheckRun",
    "KCheck.checker",
];
const THEOREMS: [&str; 2] = ["KCheck.CompleteSound.c3Owes", "KCheck.checker_startsAtSeed"];
const MUTUAL: [&str; 5] = [
    "KCheck.whnf",
    "KCheck.conv",
    "KCheck.inferAnn",
    "KCheck.check",
    "KCheck.walk",
];

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
enum Component {
    Str(String),
    Num(u64),
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
struct StructuralName(Vec<Component>);

impl StructuralName {
    fn kernel(&self) -> Name {
        self.0.iter().fold(Name::anon(), |name, part| match part {
            Component::Str(s) => name.str(s),
            Component::Num(n) => name.num(*n),
        })
    }

    fn of(name: &Name) -> Self {
        fn visit(name: &Name, parts: &mut Vec<Component>) {
            match name.inner() {
                NameInner::Anon => {}
                NameInner::Str(parent, s) => {
                    visit(parent, parts);
                    parts.push(Component::Str(s.to_string()));
                }
                NameInner::Num(parent, n) => {
                    visit(parent, parts);
                    parts.push(Component::Num(*n));
                }
            }
        }
        let mut parts = Vec::new();
        visit(name, &mut parts);
        Self(parts)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct DeclarationRow {
    name: StructuralName,
    kind: String,
    safety: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeModule {
    path: PathBuf,
    declarations: Vec<DeclarationRow>,
    extra_names: Vec<StructuralName>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeRoster {
    schema: u32,
    modules: Vec<NativeModule>,
    regions_kept: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ModuleRoster {
    theory: String,
    module: String,
    declarations: Vec<DeclarationRow>,
    extra_names: Vec<StructuralName>,
    restatements: Vec<StructuralName>,
}

#[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CompilerCopy {
    module: String,
    name: StructuralName,
    safe_counterpart: StructuralName,
}

#[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct RootPin {
    name: StructuralName,
    kind: String,
    digest: String,
    meaning_closure: Vec<StructuralName>,
    axiom_closure: Vec<StructuralName>,
}

#[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: u32,
    state: String,
    lean_toolchain: String,
    lean_githash: String,
    meaning_domain: String,
    record_domain: String,
    meaning_format: u32,
    modules: Vec<ModuleRoster>,
    unique_package_names: usize,
    restated_declarations: usize,
    owned_resident_subjects: usize,
    owned_absent_compiler_copies: Vec<CompilerCopy>,
    legacy_pin_count: usize,
    roots: Vec<RootPin>,
}

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("workspace")
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn lines(text: &str) -> Vec<String> {
    text.lines()
        .map(str::trim)
        .filter(|s| !s.is_empty() && !s.starts_with('#'))
        .map(str::to_owned)
        .collect()
}

fn source_inputs(repo: &Path) -> BTreeMap<String, String> {
    fn walk(repo: &Path, dir: &Path, out: &mut BTreeMap<String, String>) {
        for entry in fs::read_dir(dir).expect("source directory") {
            let entry = entry.expect("source entry");
            if entry.file_name().to_string_lossy().starts_with('.') {
                continue;
            }
            let path = entry.path();
            let kind = entry.file_type().expect("source file type");
            assert!(!kind.is_symlink(), "W3_SOURCE_SYMLINK {}", path.display());
            if kind.is_dir() {
                walk(repo, &path, out);
            } else if kind.is_file() {
                let key = path
                    .strip_prefix(repo)
                    .expect("workspace source")
                    .to_str()
                    .expect("UTF-8");
                out.insert(
                    key.replace('\\', "/"),
                    sha(&fs::read(path).expect("source bytes")),
                );
            }
        }
    }
    let mut out = BTreeMap::new();
    for (theory, _) in THEORIES {
        walk(repo, &repo.join("theories").join(theory), &mut out);
    }
    // These two crates supply artifact conversion, declaration re-entry and
    // the kernel's structural serialization consumed by the canonical API.
    for crate_name in ["clean-kernel", "clean-olean"] {
        walk(
            repo,
            &repo.join("crates").join(crate_name).join("src"),
            &mut out,
        );
    }
    for path in [
        "lean-toolchain",
        "Cargo.toml",
        "Cargo.lock",
        "crates/clean-olean/Cargo.toml",
        "crates/clean-kernel/Cargo.toml",
        "crates/clean-olean/src/meaning_digest.rs",
        "crates/clean-olean/tests/kcheck_labelled.rs",
        "crates/clean-olean/tests/kcheck_labelled_manifest.rs",
        ROSTER,
        "scripts/qualify_kcheck_labelled_manifest.py",
        "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/kcheck_labelled/ORDER",
    ] {
        out.insert(
            path.to_owned(),
            sha(&fs::read(repo.join(path)).expect("declared source")),
        );
    }
    out
}

fn module_inventory(repo: &Path, sources: &BTreeMap<String, String>) -> Vec<(String, String)> {
    let family =
        repo.join("crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/kcheck_labelled/ORDER");
    assert_eq!(
        lines(&fs::read_to_string(family).expect("fixture ORDER")),
        THEORIES
            .iter()
            .map(|(t, _)| format!("theory {t}"))
            .collect::<Vec<_>>(),
        "W3_FIXTURE_THEORIES"
    );
    let pin = fs::read_to_string(repo.join("lean-toolchain")).expect("workspace Lean pin");
    let mut modules = Vec::new();
    for (theory, count) in THEORIES {
        let dir = repo.join("theories").join(theory);
        assert_eq!(
            fs::read_to_string(dir.join("lean-toolchain"))
                .expect("theory pin")
                .trim(),
            pin.trim(),
            "W3_THEORY_PIN {theory}"
        );
        let own = lines(&fs::read_to_string(dir.join("ORDER")).expect("theory ORDER"));
        assert_eq!(own.len(), count, "W3_MODULE_DENOMINATOR {theory}");
        let descriptor: toml::Value = toml::from_str(
            &fs::read_to_string(dir.join("lakefile.toml")).expect("theory descriptor"),
        )
        .expect("descriptor TOML");
        let roots = descriptor["lean_lib"][0]["roots"]
            .as_array()
            .expect("explicit roots")
            .iter()
            .map(|x| x.as_str().expect("root").to_owned())
            .collect::<Vec<_>>();
        assert_eq!(
            roots,
            own.iter().map(|s| s.replace('/', ".")).collect::<Vec<_>>(),
            "W3_LIBRARY_ORDER {theory}"
        );
        let prefix = format!("theories/{theory}/");
        let actual_sources: BTreeSet<String> = sources
            .keys()
            .filter_map(|path| path.strip_prefix(prefix.as_str()))
            .filter(|path| path.ends_with(".lean") && *path != "lakefile.lean")
            .map(str::to_owned)
            .collect();
        let mut expected_sources: BTreeSet<String> =
            own.iter().map(|stem| format!("{stem}.lean")).collect();
        if theory == FAMILY {
            expected_sources.insert("KCheckLabelledMain.lean".to_owned());
        }
        assert_eq!(
            actual_sources, expected_sources,
            "W3_UNLISTED_SOURCE_MODULE {theory}"
        );
        modules.extend(
            own.into_iter()
                .map(|s| (theory.to_owned(), s.replace('/', "."))),
        );
    }
    assert_eq!(modules.len(), 426, "W3_FULL_MODULE_DENOMINATOR");
    assert_eq!(
        modules
            .iter()
            .map(|(_, m)| m)
            .collect::<BTreeSet<_>>()
            .len(),
        modules.len(),
        "W3_DUPLICATE_MODULE"
    );
    modules
}

fn legacy_contract(repo: &Path) -> usize {
    let legacy = std::str::from_utf8(LEGACY_SOURCE).expect("legacy source UTF-8");
    let table = legacy
        .split("const CHECKER: &[&str] = &[")
        .nth(1)
        .expect("legacy CHECKER table")
        .split("];")
        .next()
        .expect("legacy table end");
    let ordered: Vec<&str> = table
        .lines()
        .map(str::trim)
        .filter(|s| s.starts_with('"'))
        .map(|s| s.trim_end_matches(',').trim_matches('"'))
        .collect();
    assert_eq!(ordered, DEFINITIONS, "W3_LEGACY_ROOTS_ORDER");
    assert_eq!(DEFINITIONS.len(), 79, "W3_LEGACY_DEFINITION_DENOMINATOR");
    let pins: BTreeMap<String, String> = serde_json::from_slice(
        &fs::read(repo.join("theories/kcheck_labelled/statement_pins.json")).expect("legacy pins"),
    )
    .expect("legacy pin JSON");
    assert_eq!(pins.len(), LEGACY_PIN_COUNT, "W3_LEGACY_PIN_DENOMINATOR");
    pins.len()
}

fn run(command: &mut Command, label: &str) -> Vec<u8> {
    let output = command.output().unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        output.status.success(),
        "{label}: {}\n{}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn kind_label(env: &Environment, name: &Name) -> &'static str {
    // Structured declarations reside in their own metadata tables; the
    // ordinary ConstantKind intentionally has only the four value kinds.
    if env.get_inductive(name).is_some() {
        "inductive"
    } else if env.get_constructor(name).is_some() {
        "constructor"
    } else if env.get_recursor(name).is_some() {
        "recursor"
    } else if env.get_quot(name).is_some() {
        "quotient"
    } else {
        match env.get_const(name).expect("resident constant kind").kind {
            ConstantKind::Axiom => "axiom",
            ConstantKind::Definition => "definition",
            ConstantKind::Theorem => "theorem",
            ConstantKind::Opaque => "opaque",
        }
    }
}

fn c3_and_base_guard(env: &Environment) {
    let name = |s: &str| Name::from_string(s);
    let c3 = env
        .get_const(&name(THEOREMS[0]))
        .expect("resident C3 theorem");
    assert_eq!(
        c3.level_params,
        vec![name("u")],
        "W3_C3_TYPE_GUARD universes"
    );
    let expected = Expr::app(
        Expr::const_(name("KCheckSpec.C3Owes"), vec![Level::param(name("u"))]),
        Expr::const_(name("KCheck.checker"), Vec::new()),
    );
    assert_eq!(
        c3.type_, expected,
        "W3_C3_TYPE_GUARD actual C3Owes checker statement"
    );
    let starts = env
        .get_const(&name(THEOREMS[1]))
        .expect("resident protected-seed theorem");
    assert!(
        starts.level_params.is_empty(),
        "W3_BASE_TYPE_GUARD universes"
    );
    assert_eq!(
        starts.type_,
        Expr::app(
            Expr::app(
                Expr::const_(name("KCheckSpec.Checker.StartsAt"), Vec::new()),
                Expr::const_(name("KCheck.checker"), Vec::new())
            ),
            Expr::const_(name("KCheckSpec.PSigmaSeed.seed"), Vec::new())
        ),
        "W3_BASE_TYPE_GUARD"
    );
    let base = env
        .get_const(&name("KCheck.base"))
        .expect("resident base definition");
    // Keep definitional equality here: the id-wrapped initializer mutation
    // must reach canonical body identity checking rather than fail this guard.
    let tc = clean_kernel::TypeChecker::new(env);
    let primitive = Expr::const_(name("KCheckSpec.Env.base"), Vec::new());
    let seed = Expr::const_(name("KCheckSpec.PSigmaSeed.seed"), Vec::new());
    assert!(
        tc.is_def_eq(base.value.as_ref().expect("base body"), &seed),
        "W3_BASE_BODY_GUARD"
    );
    let seed_info = env
        .get_const(&name("KCheckSpec.PSigmaSeed.seed"))
        .expect("resident protected initializer");
    assert_eq!(seed_info.kind, ConstantKind::Definition, "W3_SEED_KIND");
    assert!(seed_info.level_params.is_empty(), "W3_SEED_UNIVERSES");
    assert_eq!(
        seed_info.type_,
        Expr::const_(name("KCheckSpec.Env"), Vec::new()),
        "W3_SEED_TYPE"
    );
    let entry_type = Expr::const_(name("KCheckSpec.Entry"), Vec::new());
    let list = |head: Expr, tail: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(name("List.cons"), vec![Level::zero()]),
                    entry_type.clone(),
                ),
                head,
            ),
            tail,
        )
    };
    let pair = list(
        Expr::const_(name("KCheckSpec.PSigmaSeed.former"), Vec::new()),
        list(
            Expr::const_(name("KCheckSpec.PSigmaSeed.constructor"), Vec::new()),
            Expr::app(
                Expr::const_(name("List.nil"), vec![Level::zero()]),
                entry_type.clone(),
            ),
        ),
    );
    let entries = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(name("List.append"), vec![Level::zero()]),
                entry_type.clone(),
            ),
            Expr::proj(name("KCheckSpec.Env"), 0, primitive.clone()),
        ),
        pair,
    );
    let expected_seed = Expr::app(
        Expr::app(Expr::const_(name("KCheckSpec.Env.mk"), Vec::new()), entries),
        Expr::proj(name("KCheckSpec.Env"), 1, primitive),
    );
    assert!(
        tc.is_def_eq(seed_info.value.as_ref().expect("seed body"), &expected_seed),
        "W3_SEED_BODY_GUARD primitive entries then pair, primitive families"
    );
    let count = Expr::app(
        Expr::app(
            Expr::const_(name("List.length"), vec![Level::zero()]),
            entry_type,
        ),
        Expr::proj(name("KCheckSpec.Env"), 0, seed),
    );
    assert!(
        tc.is_def_eq(&count, &Expr::nat_lit(12)),
        "W3_SEED_ENTRY_DENOMINATOR"
    );
    let checker = env.get_const(&name("KCheck.checker")).expect("checker");
    let value = checker.value.as_ref().expect("checker record body");
    assert!(
        matches!(value.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name("KCheckSpec.Checker.mk")),
        "W3_CHECKER_RECORD_GUARD"
    );
    assert_eq!(value.get_app_num_args(), 9, "W3_CHECKER_FIELD_DENOMINATOR");
    // AppArgsIter runs from the last source argument to the first.
    assert!(
        matches!(value.get_app_args_iter().next().expect("checker base field").kind(),
        ExprKind::Const(n, ls) if n == &name("KCheck.base") && ls.is_empty()),
        "W3_CHECKER_BASE_FIELD_GUARD"
    );
}

fn axioms(env: &Environment, name: &Name) -> BTreeSet<Name> {
    let mut found: BTreeSet<Name> = env
        .axiom_deps(name)
        .expect("resident axiom closure")
        .into_iter()
        .collect();
    found.extend(
        env.foundational_axiom_deps(name)
            .expect("foundational closure"),
    );
    let allowed: BTreeSet<Name> = [
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
    assert!(
        found.is_subset(&allowed),
        "W3_OUTSIDE_CHECKER_AX0 {name}: {found:?}"
    );
    found
}

fn export_measured(path: &Path, repo: &Path, manifest: &Manifest) {
    let parent = path
        .parent()
        .expect("export parent")
        .canonicalize()
        .expect("existing export parent");
    let destination = parent.join(path.file_name().expect("export file name"));
    assert_ne!(
        destination,
        repo.join(MANIFEST),
        "W3_EXPORT_CANNOT_WRITE_EXPECTATIONS"
    );
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(destination)
        .expect("new measured-export file; refuse overwrite");
    serde_json::to_writer_pretty(&mut file, manifest).expect("measured manifest JSON");
    file.write_all(b"\n").expect("export newline");
}

#[test]
fn adopted_checker_has_canonical_manifest_from_pinned_lean_and_native_reentry() {
    let repo = workspace();
    let expected_bytes = fs::read(repo.join(MANIFEST)).expect("W3_MANIFEST_MISSING");
    let state: serde_json::Value = serde_json::from_slice(&expected_bytes).expect("manifest JSON");
    assert_eq!(state["schema"], 1, "W3_MANIFEST_SCHEMA");
    let export = std::env::var_os(EXPORT).map(PathBuf::from);
    let expected: Option<Manifest> = if state["state"] == "unminted" {
        assert!(
            export.is_some(),
            "W3_MANIFEST_UNMINTED: native bootstrap export required; no pins exist"
        );
        None
    } else {
        assert_eq!(state["state"], "measured", "W3_MANIFEST_STATE");
        Some(serde_json::from_slice(&expected_bytes).expect("complete expected manifest"))
    };
    for (path, bytes) in [
        (
            "crates/clean-olean/tests/kcheck_labelled_manifest.rs",
            SELF_SOURCE,
        ),
        (ROSTER, ROSTER_SOURCE),
        ("crates/clean-olean/src/meaning_digest.rs", DIGEST_SOURCE),
        ("crates/clean-olean/tests/kcheck_labelled.rs", LEGACY_SOURCE),
    ] {
        assert_eq!(
            fs::read(repo.join(path)).expect("compiled input"),
            bytes,
            "W3_COMPILED_SOURCE_DRIFT {path}"
        );
    }
    let sources = source_inputs(&repo);
    let modules = module_inventory(&repo, &sources);
    let legacy_pin_count = legacy_contract(&repo);
    let compiled = compiled_fixture_dir(FAMILY);
    for (theory, module) in &modules {
        let relative = format!("{}.lean", module.replace('.', "/"));
        assert_eq!(
            fs::read(compiled.join(&relative)).expect("staged source"),
            fs::read(repo.join("theories").join(theory).join(relative)).expect("actual source"),
            "W3_COMPILED_THEORY_SOURCE {module}"
        );
    }
    let lean = clean_olean::pinned_lean_binary().expect("exact pinned Lean");
    let lean_sha256 = sha(&fs::read(&lean).expect("pinned Lean binary before replay"));
    let leanchecker = lean.parent().expect("Lean bin").join("leanchecker");
    let leanchecker_sha256 =
        sha(&fs::read(&leanchecker).expect("pinned Lean checker before replay"));
    let lib = clean_olean::require_pinned_lean_lib_path().expect("exact Lean library pin");
    let mut search_path = vec![lean.parent().expect("Lean bin").to_path_buf()];
    search_path.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let search_path = std::env::join_paths(search_path).expect("pinned Lean executable path");
    let githash = String::from_utf8(run(Command::new(&lean).arg("--githash"), "W3_LEAN_GITHASH"))
        .expect("githash UTF-8")
        .trim()
        .to_owned();
    assert_eq!(
        githash, "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc",
        "W3_LEAN_GITHASH_PIN"
    );
    let mut artifact_modules: Vec<String> =
        modules.iter().map(|(_, module)| module.clone()).collect();
    artifact_modules.push(ROOT.to_owned());
    let paths: Vec<PathBuf> = artifact_modules
        .iter()
        .map(|module| compiled.join(format!("{}.olean", module.replace('.', "/"))))
        .collect();
    let aggregate_source_path = compiled.join(format!("{}.lean", ROOT.replace('.', "/")));
    let mut expected_aggregate_source = String::from("prelude\n");
    for (_, module) in modules.iter().filter(|(theory, _)| theory == FAMILY) {
        expected_aggregate_source.push_str(&format!("import {module}\n"));
    }
    let aggregate_source = fs::read(&aggregate_source_path).expect("generated aggregate source");
    assert_eq!(
        aggregate_source,
        expected_aggregate_source.as_bytes(),
        "W3_AGGREGATE_SOURCE exact checker ORDER imports"
    );
    let hash_artifacts = || -> BTreeMap<String, String> {
        artifact_modules
            .iter()
            .zip(&paths)
            .map(|(module, path)| {
                (
                    module.clone(),
                    sha(&fs::read(path).expect("actual artifact bytes")),
                )
            })
            .collect()
    };
    let artifact_sha256 = hash_artifacts();
    let artifact_paths: BTreeMap<String, PathBuf> = artifact_modules
        .iter()
        .zip(&paths)
        .map(|(module, path)| {
            (
                module.clone(),
                path.canonicalize().expect("actual artifact path"),
            )
        })
        .collect();
    let mut raw: NativeRoster = serde_json::from_slice(&run(
        Command::new(&lean)
            .arg("--run")
            .arg(repo.join(ROSTER))
            .args(&paths)
            .env("PATH", &search_path)
            .env_remove("LEAN_PATH")
            .env_remove("LEAN_SRC_PATH"),
        "W3_PINNED_LEAN_ROSTER",
    ))
    .expect("independent structural roster JSON");
    assert_eq!(raw.schema, 1, "W3_ROSTER_SCHEMA");
    assert_eq!(
        raw.regions_kept,
        modules.len() + 1,
        "W3_ROSTER_PART_DENOMINATOR"
    );
    assert_eq!(
        raw.modules.len(),
        modules.len() + 1,
        "W3_ROSTER_MODULE_DENOMINATOR"
    );
    // The generated aggregate is an observed input, not an additional owned
    // package module. Both readers must find no declarations or auxiliary names.
    let aggregate = raw.modules.pop().expect("aggregate roster");
    assert_eq!(
        &aggregate.path,
        paths.last().expect("aggregate input path"),
        "W3_AGGREGATE_ROSTER_PATH"
    );
    assert!(
        aggregate.declarations.is_empty() && aggregate.extra_names.is_empty(),
        "W3_AGGREGATE_DECLARES_SUBJECTS"
    );
    let aggregate_artifact = read_artifact(ROOT, &artifact_paths[ROOT], ArtifactDepth::Names)
        .expect("actual generated aggregate");
    assert!(
        aggregate_artifact.names.is_empty(),
        "W3_AGGREGATE_KERNEL_NAMES"
    );
    let aggregate_imports: Vec<String> = aggregate_artifact
        .imports
        .iter()
        .map(|import| import.module_name.clone())
        .collect();
    assert_eq!(
        aggregate_imports,
        modules
            .iter()
            .filter(|(theory, _)| theory == FAMILY)
            .map(|(_, module)| module.clone())
            .collect::<Vec<_>>(),
        "W3_AGGREGATE_IMPORTS exact checker ORDER"
    );
    let mut roster = Vec::new();
    let mut package_names = BTreeSet::new();
    let mut restated = 0;
    for (((theory, module), path), raw) in modules.iter().zip(&paths).zip(raw.modules) {
        assert_eq!(&raw.path, path, "W3_ROSTER_PATH_ORDER");
        let artifact =
            read_artifact(module, path, ArtifactDepth::Names).expect("actual artifact names");
        let independent: Vec<Name> = raw
            .declarations
            .iter()
            .map(|row| row.name.kernel())
            .collect();
        assert_eq!(
            artifact.names, independent,
            "W3_INDEPENDENT_ROSTER_MISMATCH {module}"
        );
        assert_eq!(
            independent.iter().collect::<BTreeSet<_>>().len(),
            independent.len(),
            "W3_DUPLICATE_WITHIN_MODULE {module}"
        );
        let mut repeats = Vec::new();
        for row in &raw.declarations {
            assert!(
                ["safe", "unsafe", "partial"].contains(&row.safety.as_str()),
                "W3_UNKNOWN_SAFETY"
            );
            if !package_names.insert(row.name.kernel()) {
                repeats.push(row.name.clone());
                restated += 1;
            }
        }
        roster.push(ModuleRoster {
            theory: theory.clone(),
            module: module.clone(),
            declarations: raw.declarations,
            extra_names: raw.extra_names,
            restatements: repeats,
        });
    }
    let package = Package::of_module_names(modules.iter().map(|(_, module)| module.clone()).map(
        |module| {
            let path = compiled.join(format!("{}.olean", module.replace('.', "/")));
            let artifact = read_artifact(&module, &path, ArtifactDepth::Names)
                .expect("actual owned module inventory");
            (module, artifact.names)
        },
    ));
    assert_eq!(package.names(), &package_names, "W3_FULL_PACKAGE_ROSTER");
    run(
        Command::new(&leanchecker)
            .args(["--fresh", ROOT])
            .current_dir(&compiled)
            .env("PATH", &search_path)
            .env(
                "LEAN_PATH",
                std::env::join_paths([&compiled, &lib]).expect("Lean path"),
            )
            .env_remove("LEAN_SRC_PATH"),
        "W3_FRESH_LEAN_REPLAY",
    );
    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("W3_ACTUAL_CHECKER_IMPORT");
    let skipped: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|s| s.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let mut targets = BTreeSet::new();
    let mut absent = Vec::new();
    for module in roster.iter().filter(|m| m.theory == FAMILY) {
        assert!(
            !module.declarations.is_empty(),
            "W3_EMPTY_OWN_MODULE {}",
            module.module
        );
        let mut parsed = None;
        for (ordinal, row) in module.declarations.iter().enumerate() {
            let name = row.name.kernel();
            if loaded.get_const(&name).is_some() {
                assert_eq!(
                    row.kind,
                    kind_label(&loaded, &name),
                    "W3_INDEPENDENT_KIND {name}"
                );
                assert_eq!(row.safety, "safe", "W3_OWN_UNSAFE_OR_PARTIAL {name}");
                assert!(
                    !loaded.is_unsafe(&name) && !loaded.is_partial(&name),
                    "W3_RESIDENT_SAFETY {name}"
                );
                assert!(targets.insert(name), "W3_DUPLICATE_OWN_DECLARATION");
            } else {
                let text = name.to_string();
                let safe = text
                    .strip_suffix("._unsafe_rec")
                    .expect("W3_ABSENT_NONCOMPILER_DECLARATION");
                let artifact = parsed.get_or_insert_with(|| {
                    let artifact = parse_module_file(&artifact_paths[&module.module])
                        .expect("W3_COPY_ARTIFACT_PARSE");
                    assert_eq!(
                        artifact.constants.len(),
                        module.declarations.len(),
                        "W3_COPY_ARTIFACT_DENOMINATOR"
                    );
                    for (constant, declaration) in
                        artifact.constants.iter().zip(&module.declarations)
                    {
                        assert_eq!(
                            constant.name,
                            declaration.name.kernel().to_string(),
                            "W3_COPY_ARTIFACT_ORDER"
                        );
                    }
                    artifact
                });
                let safety = artifact.constants[ordinal].definition_safety;
                let stored_label = match safety {
                    Some(DefinitionSafety::Unsafe) => "unsafe",
                    Some(DefinitionSafety::Partial) => "partial",
                    _ => panic!("W3_ABSENT_COPY_STORED_REPLAYABLE {text}"),
                };
                assert_eq!(
                    row.safety, stored_label,
                    "W3_ABSENT_COPY_SAFETY_MISMATCH {text}"
                );
                assert_eq!(row.kind, "definition", "W3_ABSENT_COPY_KIND");
                assert!(
                    skipped.contains(text.as_str()),
                    "W3_ABSENT_COPY_NOT_REPORTED {text}"
                );
                // Preserve structural parent identity; never rebuild it by parsing Display.
                let mut counterpart = row.name.clone();
                assert_eq!(
                    counterpart.0.pop(),
                    Some(Component::Str("_unsafe_rec".to_owned()))
                );
                assert_eq!(counterpart.kernel().to_string(), safe);
                absent.push(CompilerCopy {
                    module: module.module.clone(),
                    name: row.name.clone(),
                    safe_counterpart: counterpart,
                });
            }
        }
    }
    for copy in &absent {
        assert!(
            targets.contains(&copy.safe_counterpart.kernel()),
            "W3_COPY_WITHOUT_SAFE_COUNTERPART"
        );
    }
    let declared: usize = roster
        .iter()
        .filter(|m| m.theory == FAMILY)
        .map(|m| m.declarations.len())
        .sum();
    assert_eq!(targets.len() + absent.len(), declared, "W3_OWN_PARTITION");
    let reentry = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("W3_FENCED_NATIVE_REENTRY");
    assert!(
        reentry.report.passed() && reentry.entry_refusals.is_empty(),
        "W3_FENCED_NATIVE_REFUSED {:?} {:?}",
        reentry.report,
        reentry.entry_refusals
    );
    let kernel = reentry
        .into_kernel()
        .expect("successful complete native re-entry");
    let admitted = kernel.environment();
    for copy in &absent {
        let name = copy.safe_counterpart.kernel();
        let info = admitted
            .get_const(&name)
            .expect("W3_COPY_COUNTERPART_NOT_ADMITTED");
        assert_eq!(
            kind_label(admitted, &name),
            "definition",
            "W3_COPY_COUNTERPART_KIND"
        );
        assert!(info.value.is_some(), "W3_COPY_COUNTERPART_WITHOUT_BODY");
    }
    c3_and_base_guard(admitted);
    for target in &targets {
        let _ = axioms(admitted, target);
    }
    let imported_digests = MeaningDigests::new(&loaded, &package);
    let admitted_digests = MeaningDigests::new(admitted, &package);
    let mut roots = Vec::new();
    for (text, expected_kind) in DEFINITIONS
        .iter()
        .map(|s| (*s, "definition"))
        .chain(THEOREMS.into_iter().map(|s| (s, "theorem")))
    {
        let name = Name::from_string(text);
        assert!(targets.contains(&name), "W3_ROOT_NOT_OWN_RESIDENT {text}");
        let info = admitted.get_const(&name).expect("resident root");
        assert_eq!(
            kind_label(admitted, &name),
            expected_kind,
            "W3_ROOT_KIND {text}"
        );
        assert!(info.value.is_some(), "W3_ROOT_WITHOUT_VALUE {text}");
        let digest = imported_digests
            .digest(&name)
            .expect("pinned-Lean artifact meaning closure");
        assert_eq!(
            digest,
            admitted_digests
                .digest(&name)
                .expect("admitted meaning closure"),
            "W3_IMPORTED_ADMITTED_MEANING {text}"
        );
        let closure = imported_digests
            .closure(&name)
            .expect("complete explicit package closure");
        if MUTUAL.contains(&text) {
            assert!(
                closure.contains(&Name::from_string(&format!("{text}._f"))),
                "W3_MUTUAL_BODY_CLOSURE {text}"
            );
        }
        if text == THEOREMS[0] {
            for dependency in [
                "KCheckSpec.C3Owes",
                "KCheck.checker",
                "KCheck.kcheck",
                "KCheck.base",
                "KCheckSpec.PSigmaSeed.seed",
                "KCheckSpec.PSigmaSeed.former",
                "KCheckSpec.PSigmaSeed.constructor",
                "KCheckSpec.Env.base",
            ] {
                assert!(
                    closure.contains(&Name::from_string(dependency)),
                    "W3_C3_MEANING_CLOSURE {dependency}"
                );
            }
            for (theory, _) in THEORIES {
                assert!(
                    roster
                        .iter()
                        .filter(|module| module.theory == theory)
                        .flat_map(|module| module.declarations.iter())
                        .any(|row| closure.contains(&row.name.kernel())),
                    "W3_C3_REACHES_THEORY {theory}"
                );
            }
        }
        if text == THEOREMS[1] {
            for dependency in [
                "KCheckSpec.Checker.StartsAt",
                "KCheck.checker",
                "KCheck.base",
                "KCheckSpec.PSigmaSeed.seed",
                "KCheckSpec.Env.base",
            ] {
                assert!(
                    closure.contains(&Name::from_string(dependency)),
                    "W3_SEED_MEANING_CLOSURE {dependency}"
                );
            }
        }
        roots.push(RootPin {
            name: StructuralName::of(&name),
            kind: expected_kind.to_owned(),
            digest,
            meaning_closure: closure.iter().map(StructuralName::of).collect(),
            axiom_closure: axioms(admitted, &name)
                .iter()
                .map(StructuralName::of)
                .collect(),
        });
    }
    assert_eq!(roots.len(), 81, "W3_ROOT_DENOMINATOR");
    assert_eq!(
        sources,
        source_inputs(&repo),
        "W3_SOURCE_CHANGED_DURING_MINT"
    );
    assert_eq!(
        artifact_sha256,
        hash_artifacts(),
        "W3_ARTIFACT_CHANGED_DURING_MINT"
    );
    assert_eq!(
        aggregate_source,
        fs::read(&aggregate_source_path).expect("aggregate source after replay"),
        "W3_AGGREGATE_SOURCE_CHANGED_DURING_MINT"
    );
    assert_eq!(
        lean_sha256,
        sha(&fs::read(&lean).expect("pinned Lean binary after replay")),
        "W3_LEAN_CHANGED_DURING_MINT"
    );
    assert_eq!(
        leanchecker_sha256,
        sha(&fs::read(&leanchecker).expect("pinned Lean checker after replay")),
        "W3_LEANCHECKER_CHANGED_DURING_MINT"
    );
    let measured = Manifest {
        schema: 1,
        state: "measured".to_owned(),
        lean_toolchain: fs::read_to_string(repo.join("lean-toolchain"))
            .expect("pin")
            .trim()
            .to_owned(),
        lean_githash: githash,
        meaning_domain: DOMAIN.to_owned(),
        record_domain: RECORD_DOMAIN.to_owned(),
        meaning_format: FORMAT_VERSION,
        modules: roster,
        unique_package_names: package_names.len(),
        restated_declarations: restated,
        owned_resident_subjects: targets.len(),
        owned_absent_compiler_copies: absent,
        legacy_pin_count,
        roots,
    };
    if let Some(path) = export {
        export_measured(&path, &repo, &measured);
        // Source/artifact custody is a run receipt, not another meaning format.
        // In particular, an unrelated source edit cannot silently redefine a pin.
        let provenance_path = path.with_extension("provenance.json");
        let mut provenance = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&provenance_path)
            .expect("new source/artifact receipt; refuse overwrite");
        serde_json::to_writer_pretty(
            &mut provenance,
            &serde_json::json!({
                "schema": 1,
                "scope": "Untrusted mint input custody; not normative meaning identity",
                "source_sha256": sources,
                "artifact_sha256": artifact_sha256,
                "artifact_paths": artifact_paths,
                "aggregate_source_path": aggregate_source_path.canonicalize().expect("aggregate source path"),
                "aggregate_source_sha256": sha(&aggregate_source),
                "lean_binary_path": lean.canonicalize().expect("Lean binary path"),
                "lean_binary_sha256": lean_sha256,
                "leanchecker_binary_path": leanchecker.canonicalize().expect("Lean checker path"),
                "leanchecker_binary_sha256": leanchecker_sha256,
                "lean_githash": measured.lean_githash,
                "whole_w3_complete": false,
            }),
        )
        .expect("source/artifact receipt JSON");
        provenance.write_all(b"\n").expect("receipt newline");
    }
    let expected = expected.expect(
        "W3_MANIFEST_UNMINTED: complete native measurement exported; expectations remain unminted",
    );
    assert_eq!(measured.modules, expected.modules, "W3_OWNERSHIP_MISMATCH");
    assert_eq!(
        measured.roots, expected.roots,
        "W3_MEANING_OR_AXIOM_MISMATCH"
    );
    assert_eq!(measured, expected, "W3_MANIFEST_ACCOUNTING_MISMATCH");
    eprintln!(
        "W3_ADOPTED_MANIFEST_OK modules=426 roots=81 legacy-pins={legacy_pin_count}; no island or authority claim"
    );
}
