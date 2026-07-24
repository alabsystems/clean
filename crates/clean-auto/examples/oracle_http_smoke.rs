// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Smoke test for the HTTP oracle backend.
//!
//! Usage:
//!
//! ```bash
//! cargo run -p clean-auto --example oracle_http_smoke --features oracle-http -- \
//!   --endpoint http://127.0.0.1:8000/v1 \
//!   --model Goedel-Prover-V2-8B \
//!   --goal "∀ n : Nat, n = n"
//! ```
//!
//! This example exercises `HttpOracle::suggest_proof` against a caller-supplied
//! endpoint without requiring `clean-elab` or proof replay infrastructure.

use clean_auto::oracle::{HttpOracle, OracleConfig, OracleRequest, ProofOracle};
use std::time::Duration;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let endpoint =
        find_arg(&args, "--endpoint").unwrap_or_else(|| "http://127.0.0.1:8000/v1".to_string());
    let model = find_arg(&args, "--model").unwrap_or_else(|| "Goedel-Prover-V2-8B".to_string());
    let goal = find_arg(&args, "--goal").unwrap_or_else(|| "∀ n : Nat, n = n".to_string());
    let candidates: usize = find_arg(&args, "--candidates")
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);

    let config = OracleConfig {
        model_id: model.clone(),
        fallback_model_ids: Vec::new(),
        endpoint_url: Some(endpoint.clone()),
        api_key: None,
        max_tokens: 2048,
        num_candidates: candidates,
        temperature: 0.6,
        timeout: Duration::from_secs(30),
        use_cot: true,
    };

    let oracle = match HttpOracle::new(config) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("Failed to create HttpOracle: {e}");
            std::process::exit(1);
        }
    };

    println!("Oracle: {model}");
    println!("Endpoint: {endpoint}");
    println!("Goal: {goal}");
    println!();

    if !oracle.is_available() {
        eprintln!("Endpoint is not reachable. Is the server running?");
        std::process::exit(1);
    }
    println!("Endpoint is reachable.");

    let request = OracleRequest::new(&goal).with_candidates(candidates);
    println!("Requesting {candidates} candidate(s)...\n");

    match oracle.suggest_proof(&request) {
        Ok(results) => {
            println!("Received {} candidate(s):\n", results.len());
            for (i, candidate) in results.iter().enumerate() {
                println!(
                    "--- Candidate {} [{:.1}%] ---",
                    i + 1,
                    candidate.confidence * 100.0
                );
                println!("{}", candidate.tactic_text);
                if let Some(reasoning) = &candidate.reasoning {
                    println!("  Reasoning: {reasoning}");
                }
                println!();
            }
            if let Some(metrics) = oracle.last_metrics() {
                println!(
                    "Metrics: {} tokens, {}ms latency",
                    metrics.total_tokens, metrics.latency_ms
                );
            }
        }
        Err(e) => {
            eprintln!("Oracle error: {e}");
            std::process::exit(1);
        }
    }
}

fn find_arg(args: &[String], flag: &str) -> Option<String> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|i| args.get(i + 1))
        .cloned()
}
