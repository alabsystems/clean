// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean cake` — the Layer-1 CAKE project lifecycle: **build → graduate →
//! verify**, driven by a single self-contained *cake-project* manifest so users
//! never hand-assemble the `--lake-project / --olean-module / --candidates /
//! --baseline / --out` flag soup.
//!
//! A cake project is an ordinary `clean-math-project` JSON manifest with an
//! added `"cake"` object declaring the operational fields:
//!
//! ```json
//! {
//!   "schema": "clean-math-project-v1",
//!   "project": "crown-proofs-invention-wave5",
//!   "cake": {
//!     "backend": "olean",
//!     "lake_project": "crown-proofs/lean",
//!     "modules": ["Crownproof.InventionWave5.Auto5"],
//!     "candidates": [
//!       "Crownproof.InventionWave5.auto5_isNilpotent_mul_swap",
//!       "Crownproof.InventionWave5.auto5_isNilpotent_mul_swap_iff"
//!     ],
//!     "baseline_index": "_mathverse-artifacts/mathverse-v1.2.0-v2.mvix",
//!     "baseline_release": "mathverse-v1.2.0",
//!     "out": "data/graduation/invention-wave5",
//!     "score": true
//!   }
//! }
//! ```
//!
//! - `clean cake build <project>`    — compile the project's modules (lake for
//!   the `olean` backend; the `native` backend builds nothing, the env is
//!   seeded internally).
//! - `clean cake graduate <project>` — run the full graduation gate over the
//!   declared candidates, reusing `clean mathverse graduate`'s engine.
//! - `clean cake verify <path>`      — run the FULL cake gate
//!   ([`verify_cake_shard`]) on an already-graduated shard or directory. (Note
//!   `clean mathverse verify` runs only the lighter structural check; this is
//!   the unbypassable trust gate.)

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context};
use clap::Subcommand;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use serde::Deserialize;

use clean_mathverse::cli::{
    run as mathverse_run, EvidenceClassArg, GraduateArgs, GraduateEnvKind, MathverseArgs,
    MathverseCommands, OnDuplicateArg,
};
use clean_mathverse::shard_verify::{verify_cake_shard, verify_cake_shard_dir};

const CAKE_DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Cake three-layer model",
    target: "designs/2026-06-09-cake-three-layer-model.md",
};

const CLI_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-cli",
    target: "clean-cli",
};

/// Feature descriptors surfaced by the `clean cake` verb tree.
///
/// One descriptor per leaf subcommand exposed by [`CakeCommands`]. Registered
/// in `crate::registry::all_features` via a single
/// `v.extend(crate::cmd_cake::FEATURES)` line and exercised by the drift gate
/// in `crates/clean-cli/tests/feature_coverage.rs`. `Stability::Building`
/// matches the sibling `audit cake` descriptor — the Layer-1 CAKE lifecycle is
/// still maturing.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["cake", "build"],
        summary: "Compile a cake project's declared modules",
        description: "\
Loads the cake-project manifest and compiles the modules its `cake` block \
declares. The `olean` backend shells out to `lake build` in the project's \
`lake_project` root; the `native` backend compiles nothing (its environment is \
seeded internally at graduation time). The first step of the build → graduate \
→ verify lifecycle.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean cake build crown-proofs.cake.json",
            what: "compile the modules declared by a cake project's manifest",
        }],
        see_also: &["cake graduate", "cake verify"],
        references: &[CAKE_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("cake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["cake", "graduate"],
        summary: "Graduate a cake project's candidate theorems through the full cake gate",
        description: "\
Runs the full graduation gate over the candidate theorems declared in the \
manifest's `cake` block, reusing `clean mathverse graduate`'s engine. Imports \
the declared module closure, novelty-checks each candidate against the pinned \
baseline index, and writes the graduated shard plus record to the manifest's \
`out` directory. Pass `--json` for the machine-readable summary.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean cake graduate crown-proofs.cake.json --json",
            what: "graduate the declared candidates and emit a JSON summary",
        }],
        see_also: &["cake build", "cake verify", "mathverse graduate"],
        references: &[CAKE_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("cake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["cake", "verify"],
        summary: "Re-run the FULL cake gate on an already-graduated shard or directory",
        description: "\
Runs the unbypassable cake trust gate (`verify_cake_shard`) over an existing \
`.mathverse` shard file or a directory of graduated shards, re-checking every \
constant through the full gate and reporting any violations. Unlike `clean \
mathverse verify` (which runs only the lighter structural check), this is the \
complete trust gate — it exits non-zero on any violation.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean cake verify data/graduation/invention-wave5",
            what: "re-check a directory of graduated shards through the full cake gate",
        }],
        see_also: &["cake graduate", "mathverse verify"],
        references: &[CAKE_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("cake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["cake", "status"],
        summary: "Report a cake project's configuration at a glance",
        description: "\
Prints a one-glance overview of a cake project's operational configuration — \
backend, modules, candidate set, novelty baseline, output directory, freshness \
and scoring policy — plus manifest sanity warnings. Pass `--json` for the \
machine-readable form. The proof-project manager's status report.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean cake status crown-proofs.cake.json",
            what: "show a cake project's backend/modules/candidates/baseline at a glance",
        }],
        see_also: &["cake build", "cake graduate", "cake verify"],
        references: &[CAKE_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("cake"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// `clean cake <verb>` — CAKE project lifecycle.
#[derive(Debug, Subcommand)]
pub(crate) enum CakeCommands {
    /// Compile a cake project's modules (lake for the `olean` backend).
    Build {
        /// Path to the cake-project manifest (`*.cake.json` / math-project JSON).
        project: PathBuf,
    },
    /// Graduate a cake project's candidate theorems through the full cake gate.
    Graduate {
        /// Path to the cake-project manifest.
        project: PathBuf,
        /// Emit JSON instead of the human-readable summary.
        #[arg(long)]
        json: bool,
    },
    /// Run the FULL cake gate on an already-graduated shard (file or directory).
    Verify {
        /// A `.mathverse` shard file, or a directory of graduated shards.
        path: PathBuf,
    },
    /// Report a cake project's configuration at a glance (backend, modules,
    /// candidates, baseline, freshness/scoring policy) — the proof-project
    /// manager's overview.
    Status {
        /// Path to the cake-project manifest (`*.cake.json` / math-project JSON).
        project: PathBuf,
        /// Emit machine-readable JSON instead of the human-readable overview.
        #[arg(long)]
        json: bool,
    },
}

/// The operational `"cake"` block of a cake-project manifest.
#[derive(Debug, Deserialize)]
struct CakeSpec {
    /// `"olean"` (lake-built Lean modules) or `"native"` (Clean's own pipeline).
    #[serde(default = "default_backend")]
    backend: String,
    /// Lake project root for the `olean` backend (auto-derives search paths).
    #[serde(default)]
    lake_project: Option<PathBuf>,
    /// Lean module names whose closure to import (`olean` backend).
    #[serde(default)]
    modules: Vec<String>,
    /// Candidate theorem names to graduate.
    #[serde(default)]
    candidates: Vec<String>,
    /// Graduate every theorem-kind constant (mutually exclusive with `candidates`).
    #[serde(default)]
    all: bool,
    /// Prebuilt `MVBIDX01` novelty index (takes precedence over `baseline`).
    #[serde(default)]
    baseline_index: Option<PathBuf>,
    /// Novelty baseline shard/dir (default `data/mathverse-shards`).
    #[serde(default)]
    baseline: Option<PathBuf>,
    /// Pinned baseline-release label.
    #[serde(default)]
    baseline_release: Option<String>,
    /// Output directory for the graduated shard + record.
    #[serde(default)]
    out: Option<PathBuf>,
    /// Compute + record each candidate's env-free semantic identity.
    #[serde(default)]
    score: bool,
    /// Also compute the (expensive) defeq Tier-1 identity. Implies `score`.
    #[serde(default)]
    score_defeq: bool,
    /// Fail closed if any declared module's `.olean` is stale vs its source.
    #[serde(default)]
    require_fresh: bool,
}

fn default_backend() -> String {
    "olean".to_string()
}

#[derive(Debug, Deserialize)]
struct CakeProjectFile {
    #[serde(default)]
    cake: Option<CakeSpec>,
}

fn load_spec(project: &Path) -> anyhow::Result<CakeSpec> {
    let text = std::fs::read_to_string(project)
        .with_context(|| format!("reading cake project manifest {}", project.display()))?;
    let parsed: CakeProjectFile = serde_json::from_str(&text)
        .with_context(|| format!("parsing cake project manifest {}", project.display()))?;
    parsed.cake.ok_or_else(|| {
        anyhow!(
            "{} has no `cake` block — add one declaring backend/modules/candidates/out \
             (see `clean cake --help`)",
            project.display()
        )
    })
}

fn parse_backend(spec: &CakeSpec) -> anyhow::Result<GraduateEnvKind> {
    match spec.backend.as_str() {
        "olean" => Ok(GraduateEnvKind::Olean),
        "native" => Ok(GraduateEnvKind::Native),
        other => bail!("unknown cake backend `{other}` (expected `olean` or `native`)"),
    }
}

pub(crate) fn handle_cake_command(command: CakeCommands) -> anyhow::Result<()> {
    match command {
        CakeCommands::Build { project } => cake_build(&project),
        CakeCommands::Graduate { project, json } => cake_graduate(&project, json),
        CakeCommands::Verify { path } => cake_verify(&path),
        CakeCommands::Status { project, json } => cake_status(&project, json),
    }
}

/// `clean cake status` — print a one-glance overview of the cake project, either
/// human-readable or (with `--json`) machine-readable for CI / tooling.
fn cake_status(project: &Path, json: bool) -> anyhow::Result<()> {
    let spec = load_spec(project)?;
    if json {
        println!("{}", cake_status_json(project, &spec));
    } else {
        println!("cake project: {}", project.display());
        println!("{}", cake_status_summary(&spec));
    }
    Ok(())
}

/// Machine-readable (`--json`) form of the cake project status — the same facts
/// as [`cake_status_summary`], shaped for programmatic consumption.
fn cake_status_json(project: &Path, spec: &CakeSpec) -> String {
    let candidates = if spec.all {
        serde_json::json!("all")
    } else {
        serde_json::json!(spec.candidates.len())
    };
    let scoring = if spec.score_defeq {
        "semantic+defeq"
    } else if spec.score {
        "semantic"
    } else {
        "off"
    };
    let report = serde_json::json!({
        "project": project.display().to_string(),
        "backend": spec.backend,
        "lake_project": spec.lake_project.as_ref().map(|p| p.display().to_string()),
        "modules": spec.modules,
        "candidates": candidates,
        "baseline_index": spec.baseline_index.as_ref().map(|p| p.display().to_string()),
        "baseline": spec.baseline.as_ref().map(|p| p.display().to_string()),
        "baseline_release": spec.baseline_release,
        "out": spec.out.as_ref().map(|p| p.display().to_string()),
        "require_fresh": spec.require_fresh,
        "scoring": scoring,
        "warnings": cake_status_warnings(spec),
    });
    serde_json::to_string_pretty(&report).unwrap_or_else(|_| "{}".to_string())
}

/// Render a cake project's operational configuration as a human-readable
/// overview (the proof-project manager's status report). Pure over [`CakeSpec`]
/// so it is directly testable.
fn cake_status_summary(spec: &CakeSpec) -> String {
    let mut lines = Vec::new();
    lines.push(format!("  backend: {}", spec.backend));
    if let Some(lp) = &spec.lake_project {
        lines.push(format!("  lake project: {}", lp.display()));
    }
    lines.push(format!("  modules: {}", spec.modules.len()));
    let candidates = if spec.all {
        "all theorem-kind constants".to_string()
    } else {
        format!("{} declared", spec.candidates.len())
    };
    lines.push(format!("  candidates: {candidates}"));
    if let Some(index) = &spec.baseline_index {
        lines.push(format!("  novelty index: {}", index.display()));
    }
    if let Some(baseline) = &spec.baseline {
        lines.push(format!("  novelty baseline: {}", baseline.display()));
    }
    if let Some(release) = &spec.baseline_release {
        lines.push(format!("  baseline release: {release}"));
    }
    if let Some(out) = &spec.out {
        lines.push(format!("  output dir: {}", out.display()));
    }
    lines.push(format!("  require fresh: {}", spec.require_fresh));
    let scoring = if spec.score_defeq {
        "semantic identity + defeq Tier-1"
    } else if spec.score {
        "semantic identity"
    } else {
        "off"
    };
    lines.push(format!("  scoring: {scoring}"));
    for warning in cake_status_warnings(spec) {
        lines.push(format!("  ⚠ warning: {warning}"));
    }
    lines.join("\n")
}

/// Manifest sanity checks for the proof-project manager: flag internally
/// inconsistent `cake` configuration so a user catches it before a build.
fn cake_status_warnings(spec: &CakeSpec) -> Vec<String> {
    let mut warnings = Vec::new();
    if spec.all && !spec.candidates.is_empty() {
        warnings.push(
            "both 'all' and 'candidates' are set; 'all' takes precedence and \
             'candidates' is ignored"
                .to_string(),
        );
    }
    if spec.backend == "olean" && spec.lake_project.is_none() && spec.modules.is_empty() {
        warnings.push(
            "'olean' backend with neither 'lake_project' nor 'modules' — there is \
             nothing to import"
                .to_string(),
        );
    }
    warnings
}

/// `clean cake build` — compile the project's modules.
fn cake_build(project: &Path) -> anyhow::Result<()> {
    let spec = load_spec(project)?;
    let backend = parse_backend(&spec)?;
    match backend {
        GraduateEnvKind::Native => {
            println!(
                "[cake build] native backend: nothing to compile (the native environment is \
                 seeded from Clean's own prelude at graduation time)"
            );
            Ok(())
        }
        GraduateEnvKind::Olean => {
            let root = spec.lake_project.clone().ok_or_else(|| {
                anyhow!("olean backend requires `lake_project` in the manifest's `cake` block")
            })?;
            if spec.modules.is_empty() {
                bail!("olean backend requires a non-empty `modules` list to build");
            }
            println!(
                "[cake build] lake build {} (in {})",
                spec.modules.join(" "),
                root.display()
            );
            let status = Command::new("lake")
                .arg("build")
                .args(&spec.modules)
                .current_dir(&root)
                .status()
                .with_context(|| {
                    format!(
                        "running `lake build` in {} (is lake on PATH?)",
                        root.display()
                    )
                })?;
            if !status.success() {
                bail!(
                    "`lake build` failed in {} (exit {:?})",
                    root.display(),
                    status.code()
                );
            }
            println!("[cake build] ok");
            Ok(())
        }
    }
}

/// `clean cake graduate` — run the graduation gate over the declared candidates.
fn cake_graduate(project: &Path, json: bool) -> anyhow::Result<()> {
    let spec = load_spec(project)?;
    let env = parse_backend(&spec)?;
    let out = spec
        .out
        .clone()
        .ok_or_else(|| anyhow!("manifest `cake` block must declare `out` (output directory)"))?;
    if spec.candidates.is_empty() && !spec.all {
        bail!("manifest `cake` block must declare `candidates` (or set `all: true`)");
    }

    let args = GraduateArgs {
        project: project.to_path_buf(),
        env,
        olean_module: spec.modules.clone(),
        olean_search_path: Vec::new(),
        lake_project: spec.lake_project.clone(),
        candidates: spec.candidates.clone(),
        all: spec.all,
        baseline: spec
            .baseline
            .clone()
            .unwrap_or_else(|| PathBuf::from("data/mathverse-shards")),
        baseline_index: spec.baseline_index.clone(),
        baseline_release: spec
            .baseline_release
            .clone()
            .unwrap_or_else(|| "local-shards".to_string()),
        out,
        on_duplicate: OnDuplicateArg::Reject,
        attempt_id: None,
        replay_sha256: None,
        engine: None,
        seed: None,
        evidence_class: EvidenceClassArg::AgentAttested,
        residual_risk: "unreviewed".to_string(),
        decided_at: None,
        // `lake_project` already defaults the source root inside the engine.
        olean_source_root: None,
        require_fresh: spec.require_fresh,
        score: spec.score || spec.score_defeq,
        score_defeq: spec.score_defeq,
        json,
    };

    mathverse_run(MathverseArgs {
        command: MathverseCommands::Graduate(args),
    })
    .map_err(|e| anyhow!("cake graduate: {e}"))
}

/// `clean cake verify` — run the FULL cake gate on an existing shard / directory.
fn cake_verify(path: &Path) -> anyhow::Result<()> {
    let report = if path.is_dir() {
        verify_cake_shard_dir(path).map_err(|e| anyhow!("cake verify: {e}"))?
    } else {
        verify_cake_shard(path).map_err(|e| anyhow!("cake verify: {e}"))?
    };
    if report.is_clean() {
        println!(
            "[cake verify] OK — {} constant(s) re-checked through the full cake gate, 0 violations: {}",
            report.checked,
            path.display()
        );
        Ok(())
    } else {
        eprintln!(
            "[cake verify] FAILED — {} violation(s) in {}:",
            report.violations.len(),
            path.display()
        );
        for v in &report.violations {
            eprintln!("  {}: {}", v.name(), v.reason());
        }
        bail!("cake gate rejected {}", path.display())
    }
}

#[cfg(test)]
mod tests {
    use super::{default_backend, parse_backend, CakeProjectFile};
    use clean_mathverse::cli::GraduateEnvKind;

    fn spec_from(json: &str) -> super::CakeSpec {
        serde_json::from_str::<CakeProjectFile>(json)
            .expect("parse")
            .cake
            .expect("cake block present")
    }

    #[test]
    fn test_cake_manifest_parses_operational_fields() {
        let spec = spec_from(
            r#"{
              "schema": "clean-math-project-v1",
              "project": "p",
              "cake": {
                "backend": "olean",
                "lake_project": "crown-proofs/lean",
                "modules": ["A.B"],
                "candidates": ["A.B.thm"],
                "baseline_index": "x.mvix",
                "baseline_release": "rel",
                "out": "out/dir",
                "score": true
              }
            }"#,
        );
        assert_eq!(spec.backend, "olean");
        assert_eq!(
            spec.lake_project.as_deref(),
            Some(std::path::Path::new("crown-proofs/lean"))
        );
        assert_eq!(spec.modules, vec!["A.B".to_string()]);
        assert_eq!(spec.candidates, vec!["A.B.thm".to_string()]);
        assert_eq!(
            spec.baseline_index.as_deref(),
            Some(std::path::Path::new("x.mvix"))
        );
        assert_eq!(spec.baseline_release.as_deref(), Some("rel"));
        assert_eq!(spec.out.as_deref(), Some(std::path::Path::new("out/dir")));
        assert!(spec.score);
        assert!(!spec.score_defeq);
        assert!(!spec.all);
    }

    #[test]
    fn test_cake_backend_defaults_to_olean_and_maps() {
        assert_eq!(default_backend(), "olean");
        let olean = spec_from(r#"{"cake": {"backend": "olean"}}"#);
        let native = spec_from(r#"{"cake": {"backend": "native"}}"#);
        let defaulted = spec_from(r#"{"cake": {}}"#);
        assert!(matches!(
            parse_backend(&olean).unwrap(),
            GraduateEnvKind::Olean
        ));
        assert!(matches!(
            parse_backend(&native).unwrap(),
            GraduateEnvKind::Native
        ));
        assert!(matches!(
            parse_backend(&defaulted).unwrap(),
            GraduateEnvKind::Olean
        ));
        let bad = spec_from(r#"{"cake": {"backend": "wat"}}"#);
        assert!(parse_backend(&bad).is_err());
    }

    #[test]
    fn test_cake_manifest_without_cake_block_is_none() {
        let parsed: CakeProjectFile =
            serde_json::from_str(r#"{"schema": "clean-math-project-v1", "project": "p"}"#).unwrap();
        assert!(parsed.cake.is_none());
    }

    #[test]
    fn test_cake_status_summary_reports_key_fields() {
        let spec = spec_from(
            r#"{"cake": {"backend": "native", "modules": ["A", "B"], "all": true,
                        "require_fresh": true, "score": true,
                        "baseline_release": "mathverse-v1.3.0"}}"#,
        );
        let s = super::cake_status_summary(&spec);
        assert!(s.contains("backend: native"), "got: {s}");
        assert!(s.contains("modules: 2"), "got: {s}");
        assert!(
            s.contains("candidates: all theorem-kind constants"),
            "got: {s}"
        );
        assert!(s.contains("require fresh: true"), "got: {s}");
        assert!(s.contains("scoring: semantic identity"), "got: {s}");
        assert!(s.contains("baseline release: mathverse-v1.3.0"), "got: {s}");
    }

    #[test]
    fn test_cake_status_summary_candidate_count_when_not_all() {
        let spec = spec_from(r#"{"cake": {"candidates": ["t1", "t2", "t3"]}}"#);
        let s = super::cake_status_summary(&spec);
        assert!(s.contains("candidates: 3 declared"), "got: {s}");
        assert!(s.contains("backend: olean"), "default backend; got: {s}");
        assert!(s.contains("scoring: off"), "got: {s}");
    }

    #[test]
    fn test_cake_status_json_is_valid_and_machine_readable() {
        let spec = spec_from(
            r#"{"cake": {"backend": "native", "modules": ["A", "B"], "all": true,
                        "require_fresh": true, "score_defeq": true}}"#,
        );
        let out = super::cake_status_json(std::path::Path::new("/tmp/p.cake.json"), &spec);
        let parsed: serde_json::Value =
            serde_json::from_str(&out).expect("`status --json` must emit valid JSON");
        assert_eq!(parsed["backend"], "native");
        assert_eq!(parsed["candidates"], "all");
        assert_eq!(parsed["modules"], serde_json::json!(["A", "B"]));
        assert_eq!(parsed["require_fresh"], true);
        assert_eq!(parsed["scoring"], "semantic+defeq");
    }

    #[test]
    fn test_cake_status_reports_index_and_out() {
        let spec = spec_from(
            r#"{"cake": {"baseline_index": "idx.mvbidx", "out": "build/out",
                        "candidates": ["t1"]}}"#,
        );
        let s = super::cake_status_summary(&spec);
        assert!(s.contains("novelty index: idx.mvbidx"), "got: {s}");
        assert!(s.contains("output dir: build/out"), "got: {s}");

        let out = super::cake_status_json(std::path::Path::new("/p"), &spec);
        let v: serde_json::Value = serde_json::from_str(&out).expect("valid JSON");
        assert_eq!(v["baseline_index"], "idx.mvbidx");
        assert_eq!(v["out"], "build/out");
    }

    #[test]
    fn test_cake_status_warns_on_all_plus_candidates() {
        // `native` backend isolates the all+candidates warning from the
        // olean-nothing-to-import one.
        let spec =
            spec_from(r#"{"cake": {"backend": "native", "all": true, "candidates": ["t1"]}}"#);
        let warnings = super::cake_status_warnings(&spec);
        assert!(
            warnings
                .iter()
                .any(|w| w.contains("'all'") && w.contains("'candidates'")),
            "should warn on the mutually-exclusive all+candidates; got {warnings:?}"
        );
        // And it surfaces in both renderings.
        assert!(super::cake_status_summary(&spec).contains("⚠ warning:"));
        let json = super::cake_status_json(std::path::Path::new("/p"), &spec);
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["warnings"].as_array().map(Vec::len), Some(1));
    }

    #[test]
    fn test_cake_status_warns_on_olean_with_nothing_to_import() {
        // Default backend is olean; no lake_project + no modules → nothing to import.
        let spec = spec_from(r#"{"cake": {"candidates": ["t1"]}}"#);
        let warnings = super::cake_status_warnings(&spec);
        assert!(
            warnings.iter().any(|w| w.contains("nothing to import")),
            "should warn on olean backend with no sources; got {warnings:?}"
        );
    }

    #[test]
    fn test_cake_status_clean_manifest_has_no_warnings() {
        let spec = spec_from(r#"{"cake": {"backend": "native", "all": true}}"#);
        assert!(
            super::cake_status_warnings(&spec).is_empty(),
            "a consistent native+all manifest should produce no warnings"
        );
    }
}
