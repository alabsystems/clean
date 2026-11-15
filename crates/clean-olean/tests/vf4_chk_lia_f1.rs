// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VF4's accept line over the F1 corpus (`docs/DECISIONS.md` R162): every
//! obligation of a VF3-census F1 row is accepted by `Eq.refl` through kernel
//! evaluation of the VF4 checker, through the reference entry, and the
//! admission times give the p50 and p99 R162 publishes.
//!
//! The fixture family `tests/fixtures/lean/v4.30.0-rc2/chk_lia_f1/` compiles the
//! theory `theories/chk_lia` and the generated `ChkLIAF1.lean` (one theorem per
//! distinct certified obligation, `chk_LIA_cases [(case, certificate), …] = true
//! := rfl`); `corpus.tsv` names every harvested obligation and its outcome.
//!
//! * **Coverage.** Every F1 row of `corpus.tsv` is `certified` (its theorem is
//!   in the module) or `via-r1-sites` (proved by R1 caller propagation; its
//!   caller-site obligations are rows of their own, each certified). A census
//!   (non-F1) row may be anything, and is printed.
//! * **The entry.** The base is the theorems' cone, admitted from EMPTY through
//!   `reference_base_closed`; each theorem is then admitted through
//!   `ReferenceKernel::add_checked` under its own name, its closure ⊆ Ax0 in
//!   the entry's environment.
//! * **Kernel evaluation decides it.** Each theorem rebuilt with its own `true`
//!   under a fresh name is accepted (the positive control) and flipped to
//!   `false`, with the same `rfl`, refused as a type mismatch.
//! * **Timing.** Each certified theorem is admitted `REPEATS` more times under
//!   fresh names; p50 and p99 are printed per theorem and over the DISTINCT
//!   theorems' samples (a duplicate obligation reuses its theorem and adds no
//!   sample), for the F1 theorems, for those with a variable, and for all.
//! * **Census coverage** (`the_f1_corpus_covers_every_f1_row_of_the_vf3_census`).
//!   The VF3 census is vendored in the report directory, sha256-pinned; every F1
//!   row is in the hand-reviewed `census-f1-coverage.tsv` with its harvested
//!   obligation count, which `harvest.ndjson` and `corpus.tsv` must match.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{Expr, ExprKind, UsedConstants};
use clean_kernel::name::Name;
use clean_kernel::{KernelEnvError, KernelTypeError, ReferenceRefusal, TheoryId};
use clean_olean::load_module_with_deps;
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::reference_base_closed;
use clean_olean::test_support::{compiled_fixture_dir, fixture_root};

const PINNED: &str = "v4.30.0-rc2";
const FAMILY: &str = "chk_lia_f1";
const MODULE: &str = "ChkLIAF1";
const CASES_SOUND: &str = "ChkLIA.chk_LIA_cases_sound";
const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];
const QUOT_FORMERS: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];
/// Admissions per certified obligation beyond the first.
const REPEATS: usize = 20;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn pinned_lib() -> PathBuf {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this fixture is compiled by {PINNED}; the workspace pin moved"
    );
    let lib = clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (VF4 reads lean-{PINNED})"));
    let toolchain_dir = lib
        .parent()
        .and_then(Path::parent)
        .and_then(Path::file_name)
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    assert!(
        toolchain_dir.ends_with(&format!("---{PINNED}")),
        "the pinned toolchain is not {PINNED} ({toolchain_dir})"
    );
    lib
}

/// One row of `corpus.tsv`.
struct Row {
    index: String,
    theorem: String,
    corpus: String,
    test: String,
    function: String,
    source: String,
    kind: String,
    vars: String,
    outcome: String,
}

fn corpus() -> Vec<Row> {
    let path = fixture_root().join(FAMILY).join("corpus.tsv");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let rows: Vec<Row> = text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .map(|l| {
            let f: Vec<&str> = l.split('\t').collect();
            assert_eq!(f.len(), 14, "corpus.tsv row has 14 fields: {l}");
            Row {
                index: f[0].to_string(),
                theorem: f[1].to_string(),
                corpus: f[2].to_string(),
                test: f[3].to_string(),
                function: f[5].to_string(),
                source: f[6].to_string(),
                kind: f[7].to_string(),
                vars: f[10].to_string(),
                outcome: f[12].to_string(),
            }
        })
        .collect();
    assert!(!rows.is_empty(), "corpus.tsv lists the harvest");
    rows
}

fn closure(env: &Environment, name: &str) -> BTreeSet<String> {
    let name = n(name);
    let domain = env
        .axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name} is not in the environment"));
    let foundational = env
        .foundational_axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name} is not in the environment"));
    domain
        .into_iter()
        .chain(foundational)
        .map(|a| a.to_string())
        .collect()
}

fn assert_within_ax0(env: &Environment, name: &str, where_: &str) {
    let got = closure(env, name);
    let ax0: BTreeSet<String> = AX0
        .iter()
        .chain(QUOT_FORMERS.iter())
        .map(|s| (*s).to_string())
        .collect();
    assert!(
        got.is_subset(&ax0),
        "{where_}: {name}'s axiom closure {got:?} is not within Ax0 and the quotient formers"
    );
}

fn head(e: &Expr) -> Option<String> {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn theorem(env: &Environment, name: &str, as_name: &str, type_: Option<Expr>) -> Declaration {
    let c = env
        .get_const(&n(name))
        .unwrap_or_else(|| panic!("{name} is declared by the corpus module"));
    Declaration::Theorem {
        name: n(as_name),
        level_params: c.level_params.clone(),
        type_: type_.unwrap_or_else(|| c.type_.clone()),
        value: c
            .value
            .clone()
            .unwrap_or_else(|| panic!("{name} is a theorem with a proof")),
    }
}

/// `@Eq Bool (chk_LIA_cases …) b` rebuilt with `rhs := b`, after checking the
/// statement is exactly that shape with `b = Bool.true`.
fn with_rhs(env: &Environment, name: &str, b: &str) -> Expr {
    let ty = &env.get_const(&n(name)).expect("declared").type_;
    let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();
    assert!(
        head(ty).as_deref() == Some("Eq")
            && args.len() == 3
            && head(&args[0]).as_deref() == Some("Bool")
            && head(&args[1]).as_deref() == Some("ChkLIA.chk_LIA_cases")
            && head(&args[2]).as_deref() == Some("Bool.true"),
        "{name}: `@Eq Bool (chk_LIA_cases …) true`, got {ty}"
    );
    Expr::apps(
        ty.get_app_fn().clone(),
        [args[0].clone(), args[1].clone(), Expr::const_(n(b), vec![])],
    )
}

fn percentile(sorted: &[f64], p: f64) -> f64 {
    // Nearest rank.
    let rank = ((p / 100.0) * sorted.len() as f64).ceil() as usize;
    sorted[rank.clamp(1, sorted.len()) - 1]
}

#[test]
fn every_f1_obligation_is_accepted_by_kernel_evaluation_through_the_entry() {
    let rows = corpus();
    let theorems: BTreeSet<String> = rows
        .iter()
        .filter(|r| r.outcome == "certified")
        .map(|r| r.theorem.clone())
        .collect();

    // Coverage: every F1 obligation is certified, or proved through R1 sites
    // that are themselves certified rows of the same test.
    let mut f1 = 0usize;
    for r in rows.iter().filter(|r| r.corpus == "F1") {
        f1 += 1;
        match r.outcome.as_str() {
            "certified" | "duplicate" => {
                assert!(
                    theorems.contains(&r.theorem),
                    "F1 row {}: its theorem {} is certified",
                    r.index,
                    r.theorem
                );
            }
            "via-r1-sites" => {
                let sites: Vec<&Row> = rows
                    .iter()
                    .filter(|s| {
                        s.test == r.test && s.source == format!("r1-site:{}", r.function)
                    })
                    .collect();
                assert!(
                    !sites.is_empty()
                        && sites
                            .iter()
                            .all(|s| theorems.contains(&s.theorem)),
                    "F1 row {} ({} {}): proved by R1, so each of its caller sites is a certified row",
                    r.index,
                    r.function,
                    r.kind
                );
            }
            other => panic!(
                "F1 row {} ({} {} {}) is `{other}`: VF4's accept line needs every F1 obligation accepted",
                r.index, r.test, r.function, r.kind
            ),
        }
    }
    assert!(f1 > 0, "the corpus has F1 rows");
    for r in rows.iter().filter(|r| r.corpus != "F1") {
        eprintln!(
            "census\t{}\t{}\t{}\t{}",
            r.index, r.function, r.kind, r.outcome
        );
    }

    let lib = pinned_lib();
    let t = Instant::now();
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(&mut env, MODULE, &[compiled_fixture_dir(FAMILY), lib])
        .unwrap_or_else(|e| panic!("load {MODULE}: {e}"));
    eprintln!("load: {:.0} ms", t.elapsed().as_secs_f64() * 1e3);
    for th in &theorems {
        let full = format!("ChkLIAF1.{th}");
        assert!(
            env.get_const(&n(&full)).is_some(),
            "{full} is in the module"
        );
        assert_within_ax0(&env, &full, "loaded");
    }

    // The base: the theorems' cone (with `chk_LIA_cases_sound`, which turns each
    // into its meaning), admitted from EMPTY through the entry.
    let subjects: Vec<String> = theorems.iter().map(|t| format!("ChkLIAF1.{t}")).collect();
    let subject_names: HashSet<Name> = subjects.iter().map(|s| n(s)).collect();
    let mut used = HashSet::new();
    for s in subjects.iter().map(String::as_str).chain([CASES_SOUND]) {
        let c = env
            .get_const(&n(s))
            .unwrap_or_else(|| panic!("{s} missing"));
        c.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
        if let Some(v) = &c.value {
            v.used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
        }
    }
    used.insert(n(CASES_SOUND));
    let targets: BTreeSet<Name> = used
        .into_iter()
        .filter(|x| !subject_names.contains(x))
        .collect();
    let t = Instant::now();
    let built = reference_base_closed(&env, &targets, &ClosedRecheckOptions::default())
        .expect("the reference base starts");
    assert!(
        built.report.passed() && built.entry_refusals.is_empty(),
        "{}\n{:?}",
        built.report.verdict_sentence(),
        built.entry_refusals
    );
    eprintln!(
        "base: {} targets, {} admitted through the entry in {:.0} ms",
        targets.len(),
        built.admitted.len(),
        t.elapsed().as_secs_f64() * 1e3
    );
    assert!(built.admitted.contains(&n(CASES_SOUND)));
    let mut k = built.into_kernel().expect("a passing base");
    assert_within_ax0(k.environment(), CASES_SOUND, "entry");

    // Each theorem: admitted under its own name, rebuilt (accepted), flipped
    // (refused), then timed.
    let mut times: BTreeMap<String, Vec<f64>> = BTreeMap::new();
    for th in &theorems {
        let full = format!("ChkLIAF1.{th}");
        let t = Instant::now();
        let token = k
            .add_checked(theorem(&env, &full, &full, None))
            .unwrap_or_else(|e| panic!("{full} must be accepted through the entry: {e}"));
        let first = t.elapsed().as_secs_f64() * 1e3;
        assert_eq!(token.theory_id(), TheoryId::LeanReferenceV1, "{full}");
        assert_within_ax0(k.environment(), &full, "entry");
        k.add_checked(theorem(
            &env,
            &full,
            &format!("{full}.rebuilt"),
            Some(with_rhs(&env, &full, "Bool.true")),
        ))
        .unwrap_or_else(|e| panic!("{full}.rebuilt must be accepted: {e}"));
        let refusal = k.add_checked(theorem(
            &env,
            &full,
            &format!("{full}.forged"),
            Some(with_rhs(&env, &full, "Bool.false")),
        ));
        assert!(
            matches!(
                &refusal,
                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                }))
            ),
            "{full} forged to `= false` must be refused as a type mismatch, got {refusal:?}"
        );
        let mut samples = vec![first];
        for i in 0..REPEATS {
            let t = Instant::now();
            k.add_checked(theorem(&env, &full, &format!("{full}.timed{i}"), None))
                .unwrap_or_else(|e| panic!("{full}.timed{i}: {e}"));
            samples.push(t.elapsed().as_secs_f64() * 1e3);
        }
        let mut sorted = samples.clone();
        sorted.sort_by(f64::total_cmp);
        eprintln!(
            "theorem\t{full}\tfirst {first:.3} ms\tmedian {:.3} ms\tmax {:.3} ms",
            percentile(&sorted, 50.0),
            sorted[sorted.len() - 1]
        );
        times.insert(th.clone(), samples);
    }

    // p50 / p99 per distinct theorem, then over the distinct theorems' samples
    // (a duplicate obligation reuses its theorem, so it adds no sample), for the
    // F1 theorems, for those with a variable (ground formulas such as `0 ≤ -5 ∧ 0
    // ≤ 5` are decided without any linear arithmetic over unknowns), and for all.
    let vars_of = |th: &str| {
        rows.iter()
            .find(|r| r.outcome == "certified" && r.theorem == th)
            .map(|r| {
                r.vars
                    .parse::<usize>()
                    .unwrap_or_else(|e| panic!("{th} vars: {e}"))
            })
            .unwrap_or_else(|| panic!("{th} has a certified row"))
    };
    let corpus_of = |th: &str| {
        rows.iter()
            .find(|r| r.outcome == "certified" && r.theorem == th)
            .map(|r| r.corpus.clone())
            .expect("certified row")
    };
    for (th, samples) in &times {
        let mut sorted = samples.clone();
        sorted.sort_by(f64::total_cmp);
        let weight = rows
            .iter()
            .filter(|r| r.theorem == *th && matches!(r.outcome.as_str(), "certified" | "duplicate"))
            .count();
        eprintln!(
            "timing\ttheorem {th}\t{}\tvars {}\tobligations {weight}\tsamples {}\tp50 {:.3} ms\tp99 {:.3} ms",
            corpus_of(th),
            vars_of(th),
            sorted.len(),
            percentile(&sorted, 50.0),
            percentile(&sorted, 99.0),
        );
    }
    type Scope<'a> = &'a dyn Fn(&str) -> bool;
    let f1: Scope = &|th| corpus_of(th) == "F1";
    let f1_vars: Scope = &|th| corpus_of(th) == "F1" && vars_of(th) > 0;
    let all: Scope = &|_| true;
    for (label, scope) in [("F1", f1), ("F1 with variables", f1_vars), ("all", all)] {
        let distinct: Vec<&String> = times.keys().filter(|th| scope(th)).collect();
        let mut samples: Vec<f64> = distinct
            .iter()
            .flat_map(|th| times[*th].iter().copied())
            .collect();
        assert!(!samples.is_empty(), "{label}: timed samples");
        samples.sort_by(f64::total_cmp);
        eprintln!(
            "timing\t{label}\tdistinct theorems {}\tsamples {}\tp50 {:.3} ms\tp99 {:.3} ms\tmax {:.3} ms",
            distinct.len(),
            samples.len(),
            percentile(&samples, 50.0),
            percentile(&samples, 99.0),
            samples[samples.len() - 1]
        );
    }
}

/// The census's F1 rows, pinned by sha256 (Trust `6af3d62c55f`'s
/// `docs/trust-core/denominators/vf3-proved-census.tsv`, vendored byte for byte).
const CENSUS_SHA256: &str = "0b73645dd46bb1f7f444fde67e90a62a1ba855fc4bcf5f8e85e7ff247f407347";

fn report_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reports/2026-10-26-vf4-f1-corpus")
}

fn tsv_rows(path: &Path) -> Vec<Vec<String>> {
    std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .map(|l| l.split('\t').map(str::to_string).collect())
        .collect()
}

/// The corpus covers the census: every F1 row of the VF3 census is in the
/// hand-reviewed coverage table with the number of F1 obligations the harvest
/// kept for it, `harvest.ndjson` holds exactly those, every harvested obligation
/// belongs to a census row of the right corpus, and `corpus.tsv` (generated from
/// the harvest) lists as many. A row with no obligation has only contract
/// features (`ensures`/`requires`), the rows the harvest does not keep.
#[test]
fn the_f1_corpus_covers_every_f1_row_of_the_vf3_census() {
    use sha2::{Digest, Sha256};
    let dir = report_dir();
    let census_bytes = std::fs::read(dir.join("vf3-proved-census.tsv")).expect("vendored census");
    let digest: String = Sha256::digest(&census_bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(
        digest, CENSUS_SHA256,
        "the vendored census is Trust 6af3d62c55f's"
    );

    // The census rows: `row  test  revision  line  function  fragment  body-fragment  …  features`.
    let census = tsv_rows(&dir.join("vf3-proved-census.tsv"));
    let header = census
        .iter()
        .find(|r| r[0] == "kind" && r.get(1).map(String::as_str) == Some("test"))
        .expect("the census's row header");
    let col = |name: &str| {
        header
            .iter()
            .position(|h| h == name)
            .unwrap_or_else(|| panic!("census column {name}"))
    };
    let (c_test, c_rev, c_line, c_fn, c_frag, c_body, c_feat) = (
        col("test"),
        col("revision"),
        col("line"),
        col("function"),
        col("fragment"),
        col("body-fragment"),
        col("features"),
    );
    let mut census_rows: BTreeMap<(String, String, String), (bool, Vec<String>)> = BTreeMap::new();
    for r in census.iter().filter(|r| r[0] == "row") {
        let f1 = r[c_frag] == "F1" || r[c_body] == "F1";
        let key = (r[c_test].clone(), r[c_rev].clone(), r[c_line].clone());
        let fields = vec![
            r[c_test].clone(),
            r[c_rev].clone(),
            r[c_line].clone(),
            r[c_fn].clone(),
            r[c_frag].clone(),
            r[c_body].clone(),
            r[c_feat].clone(),
        ];
        assert!(
            census_rows.insert(key, (f1, fields)).is_none(),
            "census rows are unique"
        );
    }
    let census_f1: BTreeSet<_> = census_rows
        .iter()
        .filter(|(_, (f1, _))| *f1)
        .map(|(k, _)| k.clone())
        .collect();

    // The coverage table.
    let coverage = tsv_rows(&dir.join("census-f1-coverage.tsv"));
    assert_eq!(coverage[0][0], "test", "the coverage table's header");
    let mut covered: BTreeMap<(String, String, String), usize> = BTreeMap::new();
    for r in &coverage[1..] {
        assert_eq!(r.len(), 8, "coverage row: {r:?}");
        let key = (r[0].clone(), r[1].clone(), r[2].clone());
        let (_, fields) = census_rows
            .get(&key)
            .unwrap_or_else(|| panic!("coverage row {key:?} is a census row"));
        assert_eq!(
            &r[..7],
            &fields[..],
            "coverage row {key:?} restates its census row"
        );
        let obligations: usize = r[7].parse().expect("obligations");
        if obligations == 0 {
            assert!(
                r[6].split(',').all(|f| f == "ensures" || f == "requires"),
                "census row {key:?} has no harvested obligation, so its features must be contracts only, got {}",
                r[6]
            );
        }
        assert!(
            covered.insert(key, obligations).is_none(),
            "coverage rows are unique"
        );
    }
    assert_eq!(
        covered.keys().cloned().collect::<BTreeSet<_>>(),
        census_f1,
        "the coverage table lists exactly the census's F1 rows"
    );

    // The harvest holds exactly the covered obligations.
    let harvest_path = dir.join("harvest.ndjson");
    let harvest = std::fs::read_to_string(&harvest_path).expect("harvest.ndjson");
    let mut harvested: BTreeMap<(String, String, String), usize> = BTreeMap::new();
    let mut total = 0usize;
    for line in harvest.lines().filter(|l| !l.trim().is_empty()) {
        let v: serde_json::Value = serde_json::from_str(line).expect("harvest row is JSON");
        let s = |k: &str| {
            v[k].as_str()
                .unwrap_or_else(|| panic!("harvest {k}"))
                .to_string()
        };
        let key = (
            s("test"),
            s("revision"),
            v["census_line"].as_u64().expect("census_line").to_string(),
        );
        let (f1, _) = census_rows
            .get(&key)
            .unwrap_or_else(|| panic!("harvested obligation of {key:?} belongs to a census row"));
        assert_eq!(
            s("corpus") == "F1",
            *f1,
            "harvested obligation of {key:?}: its corpus is its census row's"
        );
        total += 1;
        if *f1 {
            *harvested.entry(key).or_default() += 1;
        }
    }
    for (key, want) in &covered {
        assert_eq!(
            harvested.get(key).copied().unwrap_or(0),
            *want,
            "census F1 row {key:?}: the harvest's obligations"
        );
    }
    let rows = corpus();
    assert_eq!(
        rows.len(),
        total,
        "corpus.tsv lists every harvested obligation"
    );
    assert_eq!(
        rows.iter().filter(|r| r.corpus == "F1").count(),
        covered.values().sum::<usize>(),
        "corpus.tsv's F1 rows are the covered obligations"
    );
    eprintln!(
        "coverage\t{} census F1 rows\t{} with obligations\t{} F1 obligations\t{} harvested in all",
        covered.len(),
        covered.values().filter(|n| **n > 0).count(),
        covered.values().sum::<usize>(),
        total
    );
}
