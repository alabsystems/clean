// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean discover` command dispatch.
//!
//! Ports the previous `clean-discover` orphan binary to live under the
//! unified `clean` CLI tree. The flag surface, defaults, and JSON
//! output shape are preserved byte-for-byte; only the entry point
//! moves.
//!
//! Part of #3449. Epic: #3436.

use std::io::Write;

use anyhow::{anyhow, Result};
use clean_discovery::cli::DiscoverArgs;
use clean_discovery::family::{CertSizeBoundConfig, TheoremFamily};
use clean_discovery::runner::{DiscoveryConfig, DiscoveryResults, DiscoveryRunner};

/// Run `clean discover` with the parsed CLI arguments.
pub(crate) fn handle_discover_command(args: DiscoverArgs) -> Result<()> {
    let family = parse_family(&args.family)?;
    if args.max_depth == 0 || args.max_width == 0 || args.max_c == 0 {
        return Err(anyhow!(
            "--max-depth, --max-width, and --max-c must be >= 1"
        ));
    }

    if !args.quiet {
        let threads = args.threads.map_or("auto".to_string(), |n| n.to_string());
        let _ = writeln!(
            std::io::stderr(),
            "Searching {family} family (max_depth={}, max_width={}, max_c={}, threads={threads})...",
            args.max_depth,
            args.max_width,
            args.max_c,
        );
    }

    let results = run_discovery(&args, family).map_err(|e| anyhow!("discovery failed: {e}"))?;

    let json_str = format_results_json(family, &results);

    if !args.quiet {
        let wall_ms = results.total_wall_time_ns / 1_000_000;
        let throughput = compute_throughput(&results);
        let _ = writeln!(
            std::io::stderr(),
            "Evaluated {} candidates in {wall_ms} ms ({throughput:.0}/sec)",
            results.total_evaluated,
        );
    }

    writeln!(std::io::stdout(), "{json_str}")?;
    write_output_file(&args, &json_str)?;
    Ok(())
}

/// Run the discovery pipeline from the parsed CLI args.
fn run_discovery(
    args: &DiscoverArgs,
    family: TheoremFamily,
) -> Result<DiscoveryResults, clean_discovery::DiscoveryError> {
    let config = DiscoveryConfig {
        families: vec![family],
        cert_size_config: CertSizeBoundConfig {
            max_depth: args.max_depth,
            max_width: args.max_width,
            max_c: args.max_c,
        },
        num_threads: args.threads,
        ..DiscoveryConfig::default()
    };
    let runner = DiscoveryRunner::new(config)?;
    runner.run()
}

/// Compute throughput in candidates per second from the results.
fn compute_throughput(results: &DiscoveryResults) -> f64 {
    let elapsed_secs = results.total_wall_time_ns as f64 / 1_000_000_000.0;
    if elapsed_secs > 0.0 {
        results.total_evaluated as f64 / elapsed_secs
    } else {
        0.0
    }
}

/// Format the discovery results as pretty-printed JSON matching the
/// legacy binary's output shape.
fn format_results_json(family: TheoremFamily, results: &DiscoveryResults) -> String {
    let mut verified_candidates = Vec::new();
    for (fam, ref search_result) in &results.family_results {
        for outcome in &search_result.outcomes {
            if outcome.verified {
                verified_candidates.push(serde_json::json!({
                    "family": fam.to_string(),
                    "candidate_id": outcome.candidate_id.0,
                    "time_ns": outcome.time_ns,
                }));
            }
        }
    }

    let acceptance_rate = if results.total_evaluated > 0 {
        results.total_verified as f64 / results.total_evaluated as f64
    } else {
        0.0
    };

    let output_json = serde_json::json!({
        "family": family.to_string(),
        "total_candidates": results.total_evaluated,
        "verified": results.total_verified,
        "acceptance_rate": acceptance_rate,
        "wall_time_ms": results.total_wall_time_ns / 1_000_000,
        "throughput_per_sec": compute_throughput(results),
        "verified_candidates": verified_candidates,
    });

    serde_json::to_string_pretty(&output_json)
        .expect("invariant: JSON serialization should not fail")
}

/// Write the JSON results to `--output` if specified.
fn write_output_file(args: &DiscoverArgs, json_str: &str) -> Result<()> {
    let Some(ref path) = args.output else {
        return Ok(());
    };
    std::fs::write(path, json_str).map_err(|e| anyhow!("error writing to {path}: {e}"))?;
    if !args.quiet {
        let _ = writeln!(std::io::stderr(), "Results written to {path}");
    }
    Ok(())
}

/// Parse a theorem family slug into the kernel enum.
fn parse_family(s: &str) -> Result<TheoremFamily> {
    match s {
        "cert_size_bound" | "CertSizeBound" => Ok(TheoremFamily::CertSizeBound),
        "domain_tightness" | "DomainTightness" => Ok(TheoremFamily::DomainTightness),
        "verification_complexity" | "VerificationComplexity" => {
            Ok(TheoremFamily::VerificationComplexity)
        }
        "new_abstract_domain" | "NewAbstractDomain" => Ok(TheoremFamily::NewAbstractDomain),
        _ => Err(anyhow!(
            "unknown family '{s}'; expected one of: cert_size_bound, domain_tightness, \
             verification_complexity, new_abstract_domain"
        )),
    }
}
