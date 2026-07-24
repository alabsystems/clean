// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI handler for the `promote` subcommand.
//!
//! Part of #3221: DerivedPending to DerivedProved promotion pipeline.

use anyhow::Result;
use clap::Subcommand;
use std::io::{self, Write};

/// Subcommands for `clean promote`.
#[derive(Subcommand)]
pub(crate) enum PromoteCommands {
    /// List all DerivedPending definitions and proof availability
    List {
        /// Show detailed information (type signatures, axiom deps)
        #[arg(short, long)]
        verbose: bool,
    },
    /// Run the full promotion pipeline on all DerivedPending definitions
    Run {
        /// Show per-definition results
        #[arg(short, long)]
        verbose: bool,
    },
    /// Check promotion status for a single definition
    Check {
        /// Definition name to check
        name: String,
        /// Show detailed information
        #[arg(short, long)]
        verbose: bool,
    },
    /// Show summary statistics (pending/proved/total counts)
    Count,
}

/// Dispatch a promote subcommand.
pub(crate) fn handle_promote_command(command: PromoteCommands) -> Result<()> {
    match command {
        PromoteCommands::List { verbose } => handle_promote_list(verbose),
        PromoteCommands::Run { verbose } => handle_promote_run(verbose),
        PromoteCommands::Check { name, verbose } => handle_promote_check(&name, verbose),
        PromoteCommands::Count => handle_promote_count(),
    }
}

/// Format a sorted list of axiom dependency names.
fn fmt_deps(deps: &std::collections::HashSet<String>) -> String {
    let mut sorted: Vec<_> = deps.iter().map(|s| s.as_str()).collect();
    sorted.sort();
    sorted.join(", ")
}

/// Handle `clean promote list`.
pub(crate) fn handle_promote_list(verbose: bool) -> Result<()> {
    use clean_verify::proofs::ProofLibrary;
    use clean_verify::spec::{AxiomCategory, ProofStatus, Specification};

    let spec = Specification::new().map_err(|e| anyhow::anyhow!("Failed to build spec: {e}"))?;
    let library = ProofLibrary::new();
    let out = &mut io::stdout().lock();

    let mut candidates: Vec<_> = spec
        .definitions()
        .values()
        .filter(|d| {
            d.category == AxiomCategory::DerivedLemma
                && d.proof_status == ProofStatus::DerivedPending
        })
        .collect();
    candidates.sort_by(|a, b| a.name.cmp(&b.name));

    writeln!(
        out,
        "DerivedPending definitions ({} total):\n",
        candidates.len()
    )?;
    for def in &candidates {
        let tag = if library.get(&def.name).is_some() {
            "[proof available]"
        } else {
            "[no proof]"
        };
        if verbose {
            writeln!(out, "  {} {} - {}", def.name, tag, def.description)?;
            writeln!(out, "    type: {}", def.type_src)?;
            if !def.axiom_deps.is_empty() {
                writeln!(out, "    axiom deps: {}", fmt_deps(&def.axiom_deps))?;
            }
            writeln!(out)?;
        } else {
            writeln!(out, "  {} {}", def.name, tag)?;
        }
    }

    let with_proof = candidates
        .iter()
        .filter(|d| library.get(&d.name).is_some())
        .count();
    writeln!(
        out,
        "\nSummary: {} DerivedPending, {} with proofs available",
        candidates.len(),
        with_proof
    )?;
    Ok(())
}

/// Handle `clean promote run`.
pub(crate) fn handle_promote_run(verbose: bool) -> Result<()> {
    use clean_verify::proofs::promote::run_promotion;
    use clean_verify::proofs::ProofLibrary;
    use clean_verify::spec::Specification;

    let mut spec =
        Specification::new().map_err(|e| anyhow::anyhow!("Failed to build spec: {e}"))?;
    let library = ProofLibrary::new();
    let out = &mut io::stdout().lock();

    writeln!(
        out,
        "Running DerivedPending -> DerivedProved promotion pipeline...\n"
    )?;
    let report = run_promotion(&mut spec, &library);
    writeln!(out, "{}", report.summary())?;

    if verbose {
        write_detailed_report(out, &report)?;
    }
    Ok(())
}

/// Write per-attempt details for a promotion report.
fn write_detailed_report(
    out: &mut impl Write,
    report: &clean_verify::proofs::promote::PromotionReport,
) -> Result<()> {
    writeln!(out, "\nDetailed results:\n")?;
    for a in &report.attempts {
        let change = if a.promoted {
            format!("{} -> {}", a.original_status, a.new_status)
        } else {
            format!("{} (unchanged)", a.original_status)
        };
        let sym = if a.promoted {
            "+"
        } else if a.error.is_some() {
            "!"
        } else {
            "-"
        };
        writeln!(out, "  [{sym}] {} : {change}", a.name)?;
        if let Some(err) = &a.error {
            writeln!(out, "      error: {err}")?;
        }
        if !a.axiom_deps.is_empty() {
            writeln!(out, "      axiom deps: {}", fmt_deps(&a.axiom_deps))?;
        }
    }
    Ok(())
}

/// Handle `clean promote check <name>`.
pub(crate) fn handle_promote_check(name: &str, verbose: bool) -> Result<()> {
    use clean_verify::proofs::promote::promote_single;
    use clean_verify::proofs::ProofLibrary;
    use clean_verify::spec::Specification;

    let mut spec =
        Specification::new().map_err(|e| anyhow::anyhow!("Failed to build spec: {e}"))?;
    let library = ProofLibrary::new();
    let out = &mut io::stdout().lock();

    writeln!(out, "Checking promotion for: {name}\n")?;
    match promote_single(&mut spec, &library, name) {
        Ok(a) => {
            if a.promoted {
                writeln!(out, "SUCCESS: {} promoted to DerivedProved", a.name)?;
            } else {
                writeln!(out, "NOT PROMOTED: {} remains {}", a.name, a.new_status)?;
                if !a.axiom_deps.is_empty() {
                    writeln!(out, "  Blocking axiom deps: {}", fmt_deps(&a.axiom_deps))?;
                }
            }
            if verbose {
                writeln!(out, "  Original status: {}", a.original_status)?;
                writeln!(out, "  New status: {}", a.new_status)?;
            }
        }
        Err(e) => writeln!(out, "Error: {e}")?,
    }
    Ok(())
}

/// Handle `clean promote count`.
pub(crate) fn handle_promote_count() -> Result<()> {
    use clean_verify::proofs::promote::count_definitions;
    use clean_verify::proofs::ProofLibrary;
    use clean_verify::spec::Specification;

    let spec = Specification::new().map_err(|e| anyhow::anyhow!("Failed to build spec: {e}"))?;
    let library = ProofLibrary::new();
    let out = &mut io::stdout().lock();

    let stats = count_definitions(&spec, &library);
    writeln!(out, "{}", stats.summary())?;
    Ok(())
}
