// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_swarm_worker` — the first autoprove swarm worker.
//!
//! Loops the in-repo `clean-auto` hammer over a stream of tier-1 (closed,
//! quantifier-free) AND tier-2 (`∀`-quantified, peeled + re-abstracted)
//! obligations and graduates every solved goal through the C1 kernel-recheck
//! trust gate
//! ([`clean_mathverse::graduate::recheck::recheck_and_classify`]). A goal is
//! counted `proved` only when the kernel itself re-checks the hammer's proof
//! term WITH its value to a foundational-only verdict — the worker never stamps
//! a verdict of its own.
//!
//! # Usage
//!
//! ```text
//! # Constructed demo goals (no corpus required):
//! mathverse_swarm_worker --demo
//!
//! # A corpus .mathverse shard directory:
//! mathverse_swarm_worker --shard-dir <dir> --limit 500 --timeout-ms 5000
//! ```

use std::process::ExitCode;
use std::time::Duration;

use clap::Parser;

use clean_mathverse::swarm_worker::{
    Attempt, DemoSource, Hierarchy, Miss, Obligation, ProverMode, ShardObligations, SwarmWorker,
    Tally, Tier, WorkerConfig,
};

/// CLI arguments for the swarm worker.
#[derive(Debug, Parser)]
#[command(
    name = "mathverse_swarm_worker",
    about = "Loop the clean-auto hammer over tier-1 + tier-2 obligations behind the C1 kernel-recheck gate"
)]
struct Args {
    /// Corpus `.mathverse` shard directory to draw obligations from.
    #[arg(long, value_name = "DIR", conflicts_with = "demo")]
    shard_dir: Option<String>,

    /// Use a small set of constructed tier-1 goals instead of a corpus.
    #[arg(long)]
    demo: bool,

    /// Stop after offering at most this many obligations.
    #[arg(long, value_name = "N")]
    limit: Option<u64>,

    /// Per-goal hammer timeout, in milliseconds.
    #[arg(long, default_value_t = 5000, value_name = "MS")]
    timeout_ms: u64,

    /// Seed the native lemma batches into the search environment.
    #[arg(long)]
    seed_native: bool,

    /// BASELINE control: run the bare hammer (no premises offered) instead of
    /// the premise-guided ATP. Same classifier, env, timeout, and C1 gate — only
    /// the premise channel is disabled, so an A/B against the default isolates
    /// the premise lift.
    #[arg(long)]
    bare: bool,

    /// Seed the in-repo algebra structure hierarchy (`Monoid`, `Group`, `Ring`,
    /// …) into the search + recheck environments (WALL 1). Required for real
    /// universe-polymorphic Mathlib algebra goals (`∀ {M} [Monoid M], …`) to
    /// type and graduate; the bare import prelude lacks the hierarchy.
    #[arg(long)]
    algebra_hierarchy: bool,
}

fn main() -> ExitCode {
    let args = Args::parse();
    match run(&args) {
        Ok(tally) => {
            print_summary(&tally);
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: &Args) -> Result<Tally, String> {
    let config = WorkerConfig {
        timeout: Duration::from_millis(args.timeout_ms),
        limit: args.limit,
        seed_native: args.seed_native,
        mode: if args.bare {
            ProverMode::Bare
        } else {
            ProverMode::PremiseGuided
        },
        hierarchy: if args.algebra_hierarchy {
            Hierarchy::Algebra
        } else {
            Hierarchy::Bare
        },
    };
    let mut worker = SwarmWorker::new(config).map_err(|e| e.to_string())?;
    eprintln!(
        "mode: {}  |  premise pool: {} lemmas",
        if args.bare {
            "BARE (baseline control)"
        } else {
            "PREMISE-GUIDED"
        },
        worker.premise_count()
    );

    let on_attempt = |obligation: &Obligation, attempt: &Attempt, tally: &Tally| {
        report_attempt(obligation, attempt);
        if tally.attempted.is_multiple_of(50) {
            eprintln!(
                "  …{} attempted | {} proved | {} missed | {} skipped",
                tally.attempted, tally.proved, tally.missed, tally.skipped
            );
        }
    };

    if args.demo {
        worker
            .run(DemoSource::default(), on_attempt)
            .map_err(|e| e.to_string())
    } else if let Some(dir) = &args.shard_dir {
        let source = ShardObligations::from_dir(dir)?;
        worker.run(source, on_attempt).map_err(|e| e.to_string())
    } else {
        Err("specify --demo or --shard-dir <dir>".to_string())
    }
}

/// One-line per-attempt trace (to stderr so stdout stays the final summary).
fn report_attempt(obligation: &Obligation, attempt: &Attempt) {
    let verdict = match attempt {
        Attempt::Proved(Tier::Tier1) => "PROVED/t1".to_string(),
        Attempt::Proved(Tier::Tier2) => "PROVED/t2".to_string(),
        Attempt::Missed(Miss::Skipped(outcome)) => format!("skip[{outcome:?}]"),
        Attempt::Missed(Miss::HammerNoProof) => "miss[no-proof]".to_string(),
        Attempt::Missed(Miss::GateRejected(reason)) => format!("miss[gate: {reason}]"),
        Attempt::Missed(Miss::AxiomDependent(axioms)) => {
            format!("miss[axiom-dependent: {}]", axioms.join(", "))
        }
    };
    eprintln!("  {verdict}  {}", obligation.name);
}

fn print_summary(tally: &Tally) {
    println!("swarm worker summary");
    println!("  attempted : {}", tally.attempted);
    println!("  kept      : {}", tally.kept);
    println!("  skipped   : {}", tally.skipped);
    println!(
        "  proved    : {} (kernel-verified, foundational-only)",
        tally.proved
    );
    println!("    of which tier-2 (∀-quantified): {}", tally.proved_tier2);
    println!("  missed    : {}", tally.missed);
}
