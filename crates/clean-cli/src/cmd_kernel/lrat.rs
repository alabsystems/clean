// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean kernel lrat-conform` handler (#3443).
//!
//! In-process driver for the LRAT oracle-conformance harness. The underlying
//! discovery + harness live in `clean_elab::tactic::drat::oracle_conformance`
//! as a complete public API; this module forwards flags and handles report
//! persistence.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context};
use clean_elab::tactic::drat::oracle_conformance::{
    discover_ay_lrat_check, discover_cake_lpr, render_report, run_harness, HarnessConfig,
    ResolvedOracle,
};

pub(super) fn run(
    ay_lrat_check: Option<PathBuf>,
    cake_lpr: Option<PathBuf>,
    update_report: bool,
) -> anyhow::Result<()> {
    let oracles = discover_oracles(ay_lrat_check.as_deref(), cake_lpr.as_deref())?;
    let report_path = find_lrat_report_path();

    let config = HarnessConfig {
        oracles,
        update_report,
        report_path: report_path.clone(),
    };

    let (results, all_pass) = run_harness(&config);
    let command = std::env::args().collect::<Vec<_>>().join(" ");
    let report = render_report(&results, &config.oracles, &command, &current_date());
    println!("{report}");

    if update_report {
        if let Some(parent) = report_path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        std::fs::write(&report_path, &report).with_context(|| {
            format!(
                "Failed to persist LRAT oracle-conformance report to {}",
                report_path.display()
            )
        })?;
        eprintln!("Report written to {}", report_path.display());
    }

    if !all_pass {
        bail!("lrat-conform: mismatches or internal disagreements detected");
    }
    eprintln!("lrat-conform: all verifiers agree");
    Ok(())
}

fn discover_oracles(
    ay_lrat_check: Option<&Path>,
    cake_lpr: Option<&Path>,
) -> anyhow::Result<Vec<ResolvedOracle>> {
    let mut oracles = Vec::new();
    match discover_ay_lrat_check(ay_lrat_check) {
        Some(oracle) => {
            eprintln!("Found ay-lrat-check: {}", oracle.path.display());
            oracles.push(oracle);
        }
        None => {
            if ay_lrat_check.is_some() {
                bail!("explicit --ay-lrat-check path does not exist");
            }
            eprintln!("ay-lrat-check not found (searched ~/ay/target/ and PATH)");
        }
    }

    if let Some(explicit) = cake_lpr {
        match discover_cake_lpr(Some(explicit)) {
            Some(oracle) => {
                eprintln!("Found cake_lpr: {}", oracle.path.display());
                oracles.push(oracle);
            }
            None => bail!("explicit --cake-lpr path does not exist"),
        }
    }
    Ok(oracles)
}

fn find_lrat_report_path() -> PathBuf {
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

fn current_date() -> String {
    Command::new("date")
        .arg("+%Y-%m-%d")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}
