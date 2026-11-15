// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Gamma-crown proof verification binary.
//!
//! Builds and classifies the gamma-crown conjecture environments, runs kernel type checking,
//! and produces a verification report in the requested format.
//!
//! # Usage
//!
//! ```bash
//! cargo run -p clean-kernel --features test-utils,math-overlays --bin verify_gamma_crown
//! cargo run -p clean-kernel --features test-utils,math-overlays --bin verify_gamma_crown -- --json
//! cargo run -p clean-kernel --features test-utils,math-overlays --bin verify_gamma_crown -- --csv
//! cargo run -p clean-kernel --features test-utils,math-overlays --bin verify_gamma_crown -- --latex
//! ```
//!
//! Exit code 0 only if ALL conjectures pass kernel verification.
//!
//! Part of #3380.

use clean_kernel::env::gamma_crown_verify::{
    format_csv_report, format_human_report, format_latex_report, verify_all_conjectures,
};

/// What `-h`/`--help` prints: the flags `main` reads, nothing more.
const USAGE: &str = "\
usage: verify_gamma_crown [--json | --csv | --latex]
  Verifies every gamma-crown conjecture in the kernel and prints the report on stdout
  (human-readable by default); per-conjecture progress goes to stderr. Given several
  formats, --json wins over --csv over --latex. Exit 0 only if every conjecture passes,
  1 when one fails, 2 on an unknown argument or a JSON serialization error.
";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    for arg in &args {
        match arg.as_str() {
            "--json" | "--csv" | "--latex" => {}
            "-h" | "--help" => {
                print!("{USAGE}");
                return;
            }
            other => {
                eprint!("verify_gamma_crown: unknown argument {other:?}\n{USAGE}");
                std::process::exit(2);
            }
        }
    }
    let json_mode = args.iter().any(|a| a == "--json");
    let csv_mode = args.iter().any(|a| a == "--csv");
    let latex_mode = args.iter().any(|a| a == "--latex");

    // Run verification once; print progress to stderr
    let report = verify_all_conjectures();
    for c in &report.conjectures {
        eprintln!(
            "  {} {} ({:.1}ms, {} axioms)",
            c.id,
            if c.tc_verified { "OK" } else { "FAILED" },
            c.verification_time_ms,
            c.domain_axioms,
        );
    }
    eprintln!();

    if json_mode {
        match serde_json::to_string_pretty(&report) {
            Ok(rendered) => println!("{rendered}"),
            Err(e) => {
                eprintln!("Error serializing JSON report: {e}");
                std::process::exit(2);
            }
        }
    } else if csv_mode {
        print!("{}", format_csv_report(&report));
    } else if latex_mode {
        print!("{}", format_latex_report(&report));
    } else {
        print!("{}", format_human_report(&report));
    }

    if report.conjectures_failed > 0 {
        std::process::exit(1);
    }
}
