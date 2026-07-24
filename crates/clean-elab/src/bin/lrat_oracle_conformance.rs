// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT oracle-conformance gate binary.
//!
//! Runs clean's native LRAT verifiers against an external oracle on a
//! maintained proof corpus. See `designs/2026-03-14-936-lrat-oracle-conformance-gate.md`.
//!
//! Usage:
//!   cargo run -p clean-elab --bin lrat_oracle_conformance -- [OPTIONS]
//!
//! Options:
//!   --ay-lrat-check <path>   Explicit path to ay-lrat-check binary
//!   --cake-lpr <path>        Explicit path to cake_lpr binary
//!   --update-report          Write report to reports/research/issue-936-lrat-oracle-current.md

use std::io::Write;
use std::path::PathBuf;
use std::process;

use clean_elab::tactic::drat::oracle_conformance::{
    discover_ay_lrat_check, discover_cake_lpr, render_report, run_harness, HarnessConfig,
    ResolvedOracle,
};

struct CliArgs {
    ay_lrat_check: Option<PathBuf>,
    cake_lpr: Option<PathBuf>,
    update_report: bool,
}

fn parse_args() -> CliArgs {
    let args: Vec<String> = std::env::args().collect();
    let mut cli = CliArgs {
        ay_lrat_check: None,
        cake_lpr: None,
        update_report: false,
    };

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--ay-lrat-check" => {
                i += 1;
                if i >= args.len() {
                    let _ = writeln!(
                        std::io::stderr(),
                        "error: --ay-lrat-check requires a path argument"
                    );
                    process::exit(2);
                }
                cli.ay_lrat_check = Some(PathBuf::from(&args[i]));
            }
            "--cake-lpr" => {
                i += 1;
                if i >= args.len() {
                    let _ = writeln!(
                        std::io::stderr(),
                        "error: --cake-lpr requires a path argument"
                    );
                    process::exit(2);
                }
                cli.cake_lpr = Some(PathBuf::from(&args[i]));
            }
            "--update-report" => cli.update_report = true,
            "--help" | "-h" => {
                print_usage();
                process::exit(0);
            }
            other => {
                let _ = writeln!(std::io::stderr(), "error: unknown argument: {}", other);
                print_usage();
                process::exit(2);
            }
        }
        i += 1;
    }
    cli
}

fn print_usage() {
    let mut err = std::io::stderr();
    let _ = writeln!(err, "Usage: lrat_oracle_conformance [OPTIONS]");
    let _ = writeln!(err);
    let _ = writeln!(err, "Options:");
    let _ = writeln!(
        err,
        "  --ay-lrat-check <path>   Explicit path to ay-lrat-check binary"
    );
    let _ = writeln!(
        err,
        "  --cake-lpr <path>        Explicit path to cake_lpr binary"
    );
    let _ = writeln!(
        err,
        "  --update-report          Write report to issue-936-lrat-oracle-current.md"
    );
    let _ = writeln!(err, "  --help                   Show this help message");
}

fn discover_oracles(cli: &CliArgs) -> Vec<ResolvedOracle> {
    let mut oracles = Vec::new();

    match discover_ay_lrat_check(cli.ay_lrat_check.as_deref()) {
        Some(oracle) => {
            let _ = writeln!(
                std::io::stderr(),
                "Found ay-lrat-check: {}",
                oracle.path.display()
            );
            oracles.push(oracle);
        }
        None => {
            let _ = writeln!(
                std::io::stderr(),
                "ay-lrat-check not found (searched ~/ay/target/ and PATH)"
            );
            if cli.ay_lrat_check.is_some() {
                let _ = writeln!(
                    std::io::stderr(),
                    "error: explicit --ay-lrat-check path does not exist"
                );
                process::exit(1);
            }
        }
    }

    if let Some(ref cake_path) = cli.cake_lpr {
        match discover_cake_lpr(Some(cake_path)) {
            Some(oracle) => {
                let _ = writeln!(
                    std::io::stderr(),
                    "Found cake_lpr: {}",
                    oracle.path.display()
                );
                oracles.push(oracle);
            }
            None => {
                let _ = writeln!(
                    std::io::stderr(),
                    "error: explicit --cake-lpr path does not exist"
                );
                process::exit(1);
            }
        }
    }

    oracles
}

fn current_date() -> String {
    process::Command::new("date")
        .arg("+%Y-%m-%d")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

fn find_report_path() -> PathBuf {
    let mut dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    loop {
        if dir.join(".git").exists() {
            return dir.join("reports/research/issue-936-lrat-oracle-current.md");
        }
        if !dir.pop() {
            break;
        }
    }
    PathBuf::from("reports/research/issue-936-lrat-oracle-current.md")
}

fn main() {
    let cli = parse_args();
    let oracles = discover_oracles(&cli);
    let report_path = find_report_path();

    let config = HarnessConfig {
        oracles,
        update_report: cli.update_report,
        report_path: report_path.clone(),
    };

    let (results, all_pass) = run_harness(&config);

    let command = std::env::args().collect::<Vec<_>>().join(" ");
    let report = render_report(&results, &config.oracles, &command, &current_date());

    let _ = writeln!(std::io::stdout(), "{}", report);

    if cli.update_report {
        if let Some(parent) = report_path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        match std::fs::write(&report_path, &report) {
            Ok(()) => {
                let _ = writeln!(
                    std::io::stderr(),
                    "Report written to {}",
                    report_path.display()
                );
            }
            Err(e) => {
                let _ = writeln!(std::io::stderr(), "Failed to write report: {}", e);
            }
        }
    }

    if !all_pass {
        let _ = writeln!(
            std::io::stderr(),
            "FAIL: mismatches or internal disagreements detected"
        );
        process::exit(1);
    }

    let _ = writeln!(std::io::stderr(), "PASS: all verifiers agree");
}
