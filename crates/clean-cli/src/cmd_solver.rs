// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean solver` — Phase-1 solver-results-cache tooling: build the `VCIDX01`
//! index, and report telemetry stats / weak areas / the VBS−SBS gap / NN
//! datasets over the captured solver-attempt stream.
//!
//! See `designs/2026-06-24-solver-results-cache-service.md` §5–§7. The producer
//! side (Phase 0, in `clean-auto`) captures one `solver-attempt-record-v1` row
//! per solving attempt to `$CLEAN_SOLVER_TELEMETRY_DIR/attempts.jsonl` and a
//! content-addressed proof cache to `$CLEAN_SOLVER_CACHE_DIR`. This verb tree is
//! the read/analysis side, mirroring how `clean mathverse` routes into the
//! library crate ([`clean_auto::solver_cache_service`]).
//!
//! Sub-verbs:
//! - `index-build <dirs...> -o solver.vcidx` — build a fail-closed, corpus-pinned
//!   `VCIDX01` index over the telemetry + cache dirs (µs lookups).
//! - `stats [--by solver|theory|strategy] [--json]` — aggregate attempts /
//!   solved / success-rate / PAR-2 / wall-time p50/p90/max / cache-hit rate.
//! - `weak [--by theory|solver|theory-solver] [--top N] [--json]` — worst classes
//!   by PAR-2 (the regression worklist).
//! - `vbs-gap [--json]` — the VBS − SBS gap (headroom a learned selector could
//!   capture; gate on building Phase 3).
//! - `export-dataset --out ds.jsonl [--engine ..] [--theory ..]` — NN training
//!   data (one row per attempt: features / strategy / labels / provenance).
//!
//! Everything here is **pure telemetry analysis** — zero kernel interaction,
//! zero soundness weight. The index is a lookup accelerator, never an arbiter.

use std::path::PathBuf;

use anyhow::{bail, Context};
use clap::Subcommand;
use clean_auto::solver_cache_service as svc;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const SOLVER_DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Solver-results cache + telemetry service",
    target: "designs/2026-06-24-solver-results-cache-service.md",
};

const CLI_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-cli",
    target: "clean-cli",
};

/// Feature descriptors surfaced by the `clean solver` verb tree.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["solver", "index-build"],
        summary: "Build a fail-closed VCIDX01 index over the solver cache + telemetry",
        description: "\
Folds the `solver-attempt-record-v1` telemetry rows plus the content-addressed \
proof-cache membership under the given directories into a binary, \
corpus-pinned, content-addressed `VCIDX01` index mapping `obligation_digest -> \
{cached?, attempt summary}`. The loader is fail-closed (magic + version + \
self-digest + section arithmetic + sortedness validated before any lookup) and \
lookups are µs binary searches over the full 256-bit obligation digest.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean solver index-build $CLEAN_SOLVER_TELEMETRY_DIR -o solver.vcidx",
            what: "build a VCIDX01 index over the telemetry directory",
        }],
        see_also: &["solver stats", "mathverse index-build"],
        references: &[SOLVER_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("solver"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["solver", "stats"],
        summary: "Aggregate solver telemetry: per-solver/theory/strategy success + PAR-2",
        description: "\
Reads the captured `attempts.jsonl` telemetry and aggregates per solver / per \
theory / per strategy: attempts, solved, success-rate, mean PAR-2 (the fused \
penalised-runtime score), wall-time distribution (p50/p90/max), and cache-hit \
rate. Prints a human table or, with `--json`, the machine-readable report.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean solver stats --by theory",
            what: "per-theory attempts / success / PAR-2 table",
        }],
        see_also: &["solver weak", "solver vbs-gap"],
        references: &[SOLVER_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("solver"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["solver", "weak"],
        summary: "Worst obligation classes by PAR-2 — the solver regression worklist",
        description: "\
Ranks obligation classes (by theory, solver, or theory×solver) worst-first by \
mean PAR-2, surfacing where the solver is weakest. The SATzilla/MachSMT-style \
per-class weak-area worklist.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean solver weak --by theory --top 20",
            what: "the 20 worst theory classes by PAR-2",
        }],
        see_also: &["solver stats", "solver vbs-gap"],
        references: &[SOLVER_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("solver"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["solver", "vbs-gap"],
        summary: "VBS − SBS gap: headroom a learned per-instance selector could capture",
        description: "\
Computes the virtual-best-solver (best engine picked per instance) versus \
single-best-solver (one engine with the lowest aggregate PAR-2) gap. A small \
gap means a learned strategy selector is not worth building; a large gap is the \
quantified headroom (Rice 1976 / SATzilla algorithm selection).",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean solver vbs-gap --json",
            what: "the VBS − SBS gap as a JSON report",
        }],
        see_also: &["solver stats", "solver export-dataset"],
        references: &[SOLVER_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("solver"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["solver", "export-dataset"],
        summary: "Export NN training data (features / strategy / labels / provenance)",
        description: "\
Emits one JSONL row per attempt — `(feature_vector, strategy_id, label_block, \
provenance)` — for a learned strategy/premise selector. Labels are \
Clean-engine-specific and non-transferable; the oracle engine's cost is flagged \
non-CPU; siblings share `obligation_digest` so VBS/SBS attempt sets reconstruct.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean solver export-dataset --out ds.jsonl --engine clean-smt",
            what: "export the clean-smt attempts as an NN dataset",
        }],
        see_also: &["solver stats", "solver vbs-gap"],
        references: &[SOLVER_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("solver"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// `clean solver <verb>` — solver-results-cache tooling.
#[derive(Debug, Subcommand)]
pub(crate) enum SolverCommands {
    /// Build a fail-closed, corpus-pinned `VCIDX01` index over the cache + telemetry.
    #[command(name = "index-build")]
    IndexBuild {
        /// Telemetry / cache directories to index (default: `$CLEAN_SOLVER_TELEMETRY_DIR`
        /// and `$CLEAN_SOLVER_CACHE_DIR` when set).
        dirs: Vec<PathBuf>,
        /// Output index path.
        #[arg(short, long)]
        out: PathBuf,
    },
    /// Aggregate telemetry: per-solver/theory/strategy success-rate + PAR-2.
    Stats {
        /// Telemetry directories to read (default: env-derived).
        dirs: Vec<PathBuf>,
        /// Slice to print: `solver` (default), `theory`, or `strategy`.
        #[arg(long, default_value = "solver")]
        by: String,
        /// PAR-2 timeout budget in ms (default: 5000).
        #[arg(long)]
        budget_ms: Option<u64>,
        /// Emit JSON instead of the human table.
        #[arg(long)]
        json: bool,
    },
    /// Worst obligation classes by PAR-2 — the regression worklist.
    Weak {
        /// Telemetry directories to read (default: env-derived).
        dirs: Vec<PathBuf>,
        /// Group by `theory` (default), `solver`, or `theory-solver`.
        #[arg(long, default_value = "theory")]
        by: String,
        /// Number of worst classes to show.
        #[arg(long, default_value_t = 20)]
        top: usize,
        /// PAR-2 timeout budget in ms (default: 5000).
        #[arg(long)]
        budget_ms: Option<u64>,
        /// Emit JSON instead of the human table.
        #[arg(long)]
        json: bool,
    },
    /// The VBS − SBS gap (learned-selector headroom).
    #[command(name = "vbs-gap")]
    VbsGap {
        /// Telemetry directories to read (default: env-derived).
        dirs: Vec<PathBuf>,
        /// PAR-2 timeout budget in ms (default: 5000).
        #[arg(long)]
        budget_ms: Option<u64>,
        /// Emit JSON instead of the human report.
        #[arg(long)]
        json: bool,
    },
    /// Export NN training data (one JSONL row per attempt).
    #[command(name = "export-dataset")]
    ExportDataset {
        /// Telemetry directories to read (default: env-derived).
        dirs: Vec<PathBuf>,
        /// Output dataset path (JSONL).
        #[arg(short, long)]
        out: PathBuf,
        /// Restrict to one engine (`clean-smt` / `clean-superposition` / `oracle`).
        #[arg(long)]
        engine: Option<String>,
        /// Restrict to one theory logic.
        #[arg(long)]
        theory: Option<String>,
        /// PAR-2 timeout budget in ms (default: 5000).
        #[arg(long)]
        budget_ms: Option<u64>,
    },
}

/// Resolve the directories to read: the explicit `dirs` if any, else the
/// telemetry + cache directories named by the producer-side env vars.
fn resolve_dirs(dirs: Vec<PathBuf>) -> anyhow::Result<Vec<PathBuf>> {
    if !dirs.is_empty() {
        return Ok(dirs);
    }
    let mut derived = Vec::new();
    for var in [svc::telemetry_dir_env(), svc::cache_dir_env()] {
        if let Some(v) = std::env::var_os(var) {
            if !v.is_empty() {
                derived.push(PathBuf::from(v));
            }
        }
    }
    if derived.is_empty() {
        bail!(
            "no telemetry/cache directories given and neither {} nor {} is set; \
             pass directories explicitly or set the env vars",
            svc::telemetry_dir_env(),
            svc::cache_dir_env()
        );
    }
    Ok(derived)
}

fn parse_weak_by(by: &str) -> anyhow::Result<svc::WeakArea> {
    match by {
        "theory" => Ok(svc::WeakArea::Theory),
        "solver" => Ok(svc::WeakArea::Solver),
        "theory-solver" => Ok(svc::WeakArea::TheorySolver),
        other => bail!("unknown --by `{other}` (expected theory|solver|theory-solver)"),
    }
}

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_solver_command(command: SolverCommands) -> anyhow::Result<()> {
    match command {
        SolverCommands::IndexBuild { dirs, out } => {
            let dirs = resolve_dirs(dirs)?;
            let summary = svc::build_index(&dirs, &out)
                .with_context(|| format!("building VCIDX01 index at {}", out.display()))?;
            println!(
                "VCIDX01 index written to {} ({} entries, {} attempts, {} cached, {} bytes)",
                out.display(),
                summary.entries,
                summary.attempts,
                summary.cached,
                summary.index_bytes
            );
            println!("corpus pin: {}", summary.corpus_digest);
            Ok(())
        }
        SolverCommands::Stats {
            dirs,
            by,
            budget_ms,
            json,
        } => {
            let dirs = resolve_dirs(dirs)?;
            let budget = budget_ms.unwrap_or_else(svc::default_budget_ms);
            let report = svc::stats(&dirs, budget).context("aggregating solver telemetry")?;
            if json {
                println!("{}", serde_json::to_string_pretty(&report)?);
            } else {
                print_stats_table(&report, &by);
            }
            Ok(())
        }
        SolverCommands::Weak {
            dirs,
            by,
            top,
            budget_ms,
            json,
        } => {
            let dirs = resolve_dirs(dirs)?;
            let budget = budget_ms.unwrap_or_else(svc::default_budget_ms);
            let axis = parse_weak_by(&by)?;
            let weak = svc::weak(&dirs, axis, budget, top).context("computing weak areas")?;
            if json {
                println!("{}", serde_json::to_string_pretty(&weak)?);
            } else {
                print_class_table(&format!("weak areas (worst PAR-2 first, by {by})"), &weak);
            }
            Ok(())
        }
        SolverCommands::VbsGap {
            dirs,
            budget_ms,
            json,
        } => {
            let dirs = resolve_dirs(dirs)?;
            let budget = budget_ms.unwrap_or_else(svc::default_budget_ms);
            let gap = svc::vbs_gap(&dirs, budget).context("computing VBS-SBS gap")?;
            if json {
                println!("{}", serde_json::to_string_pretty(&gap)?);
            } else {
                println!("VBS − SBS gap (PAR-2 budget {budget} ms)");
                println!("  VBS mean PAR-2 : {:.1}", gap.vbs_mean_par2);
                println!(
                    "  SBS ({})  mean PAR-2 : {:.1}",
                    gap.sbs_solver, gap.sbs_mean_par2
                );
                println!("  gap            : {:.1}", gap.gap);
                println!("  obligations    : {}", gap.obligations);
                if gap.gap < f64::EPSILON {
                    println!(
                        "  → gap is ~0: a learned per-instance selector is NOT worth building"
                    );
                }
            }
            Ok(())
        }
        SolverCommands::ExportDataset {
            dirs,
            out,
            engine,
            theory,
            budget_ms,
        } => {
            let dirs = resolve_dirs(dirs)?;
            let budget = budget_ms.unwrap_or_else(svc::default_budget_ms);
            let filter = svc::DatasetFilter { engine, theory };
            let n = svc::export_dataset(&dirs, &filter, budget, &out)
                .with_context(|| format!("exporting NN dataset to {}", out.display()))?;
            println!("wrote {n} dataset rows to {}", out.display());
            Ok(())
        }
    }
}

/// Print the per-class stats table for the requested slice.
fn print_stats_table(report: &svc::StatsReport, by: &str) {
    println!(
        "solver telemetry: {} attempts over {} obligations (PAR-2 budget {} ms)",
        report.total_attempts, report.distinct_obligations, report.budget_ms
    );
    let (label, classes): (&str, &[(String, svc::ClassReport)]) = match by {
        "theory" => ("theory", &report.by_theory),
        "strategy" => ("strategy", &report.by_strategy),
        _ => ("solver", &report.by_solver),
    };
    print_class_table(&format!("by {label}"), classes);
}

/// Render a `(name, ClassStats)` table with the aggregate columns.
fn print_class_table(title: &str, classes: &[(String, svc::ClassReport)]) {
    println!("\n{title}");
    println!(
        "{:<28} {:>8} {:>8} {:>8} {:>10} {:>8} {:>8} {:>8} {:>8}",
        "class", "attempts", "solved", "succ%", "mean_par2", "hit%", "p50ms", "p90ms", "maxms"
    );
    if classes.is_empty() {
        println!("  (no attempts recorded)");
        return;
    }
    for (name, s) in classes {
        println!(
            "{:<28} {:>8} {:>8} {:>7.1}% {:>10.1} {:>7.1}% {:>8} {:>8} {:>8}",
            truncate(name, 28),
            s.attempts,
            s.solved,
            s.success_rate * 100.0,
            s.mean_par2,
            s.cache_hit_rate * 100.0,
            opt(s.wall_p50),
            opt(s.wall_p90),
            opt(s.wall_max),
        );
    }
}

fn opt(v: Option<u64>) -> String {
    v.map(|n| n.to_string()).unwrap_or_else(|| "-".to_string())
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        s.to_string()
    } else {
        // Slice at a UTF-8 char boundary, never a raw byte index: class labels
        // (`theory_logic` / `solver.name` / `strategy`) come verbatim from
        // untrusted `attempts.jsonl` telemetry rows and may contain multibyte
        // chars. A bare `&s[..max-1]` would panic (abort, under release
        // `panic = "abort"`) when byte `max-1` lands inside a multibyte char.
        let want = max.saturating_sub(1);
        let end = s
            .char_indices()
            .map(|(i, _)| i)
            .take_while(|&i| i <= want)
            .last()
            .unwrap_or(0);
        format!("{}…", &s[..end])
    }
}

#[cfg(test)]
mod tests {
    use super::truncate;

    #[test]
    fn test_truncate_short_ascii_returns_verbatim() {
        // Correct path: `len <= max` is returned unchanged.
        assert_eq!(truncate("clean-smt", 28), "clean-smt");
        assert_eq!(truncate("", 28), "");
        // Exactly `max` bytes: still verbatim (boundary of the `<=` branch).
        let exactly = "a".repeat(28);
        assert_eq!(truncate(&exactly, 28), exactly);
    }

    #[test]
    fn test_truncate_long_ascii_slices_at_max_minus_one() {
        // Correct path unchanged: a long ASCII label is cut to `max-1` chars + '…'.
        let long = "a".repeat(40);
        assert_eq!(truncate(&long, 28), format!("{}…", "a".repeat(27)));
    }

    #[test]
    fn test_truncate_multibyte_on_boundary_does_not_panic() {
        // Regression: an untrusted class label whose multibyte char straddles
        // byte `max-1` (=27) used to panic with
        // "byte index 27 is not a char boundary" and abort the process.
        // 26 * 'a' (26 bytes) + '€' (3 bytes at indices 26,27,28) = 29 bytes.
        let name = format!("{}\u{20AC}", "a".repeat(26));
        assert_eq!(name.len(), 29);
        assert!(!name.is_char_boundary(27), "test fixture assumption");
        // Must not panic; truncates at the last valid boundary (<= 27), i.e. 26.
        let out = truncate(&name, 28);
        assert_eq!(out, format!("{}…", "a".repeat(26)));
    }

    #[test]
    fn test_truncate_all_multibyte_long_does_not_panic() {
        // A label made entirely of 4-byte chars, well over `max` bytes, must
        // also degrade cleanly at a char boundary rather than abort.
        let name = "\u{1F600}".repeat(20); // 20 * 4 = 80 bytes
        let out = truncate(&name, 28);
        // Result is valid UTF-8 and ends with the ellipsis; no panic occurred.
        assert!(out.ends_with('…'));
        assert!(out.len() <= 28 + '…'.len_utf8());
    }
}
