// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean kernel verify-gamma-crown` handler (#3446).
//!
//! In-process, feature-gated. The conjecture builders live behind the
//! `math-overlays` kernel feature, so this handler is gated on the
//! `math-overlays` feature exposed by the `clean-cli` crate. Without the
//! feature the handler emits an informative message and exits non-zero.

use anyhow::bail;

#[cfg(feature = "math-overlays")]
pub(super) fn run(json: bool, csv: bool, latex: bool) -> anyhow::Result<()> {
    use clean_kernel::env::gamma_crown_verify::{
        format_csv_report, format_human_report, format_latex_report, verify_all_conjectures,
    };

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

    if json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else if csv {
        print!("{}", format_csv_report(&report));
    } else if latex {
        print!("{}", format_latex_report(&report));
    } else {
        print!("{}", format_human_report(&report));
    }

    if report.conjectures_failed > 0 {
        bail!(
            "verify-gamma-crown: {} conjecture(s) failed",
            report.conjectures_failed
        );
    }
    Ok(())
}

#[cfg(not(feature = "math-overlays"))]
pub(super) fn run(_json: bool, _csv: bool, _latex: bool) -> anyhow::Result<()> {
    bail!(
        "clean kernel verify-gamma-crown requires the `math-overlays` feature. \
         Rebuild with `cargo build -p clean-cli --features math-overlays` \
         (or the equivalent feature on the `clean` package)."
    );
}
