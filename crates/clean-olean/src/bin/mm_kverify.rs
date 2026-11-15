// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-verify Metamath theorems from a `.mm` file — the SEQUENTIAL verifier,
//! and therefore the reference the two-pass pipeline's output is compared against.
//!
//! Usage: `mm_kverify <path.mm> [max_provables] [--exposure]`
//!
//! Parses the database, then has the Clean kernel certify each `$p` theorem
//! (reusing earlier theorems by proof inlining). Prints verified / failed /
//! skipped counts. `max_provables` bounds how many theorems are attempted (the
//! inlining strategy blows up on deeply-reused proofs in large databases).
//!
//! `--exposure` additionally answers the R1-MM exposure question for this
//! database prefix: does it contain a theorem the SEQUENTIAL verifier skips
//! because it may not reuse a dependency that IS itself verified? Every such pair
//! is a theorem the pre-fix two-pass export shipped as `KernelVerified` and the
//! fixed `mm_gate` now drops. See
//! `docs/issues/2026-08-23-r1-mm-two-pass-theorem.md` §3.3.

use std::process::ExitCode;
use std::time::Instant;

use clean_olean::metamath::{
    ground_reuse_exposure, kernel_verify_database_prefix_count_only, parse_database_file,
};

/// `--exposure` exit code when the prefix DOES exercise the R1-MM gap. Distinct
/// from 1 (an error) and 2 (a usage error) so a caller can tell "measured, and the
/// answer is yes" from "the run broke".
const EXIT_EXPOSED: u8 = 3;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let exposure = args.iter().any(|a| a == "--exposure");
    let positional: Vec<&String> = args
        .iter()
        .enumerate()
        .filter(|(i, a)| *i == 0 || !a.starts_with("--"))
        .map(|(_, a)| a)
        .collect();
    if positional.len() < 2 {
        eprintln!("usage: mm_kverify <path.mm> [max_provables] [--exposure]");
        return ExitCode::from(2);
    }
    let path = positional[1];
    let limit = positional
        .get(2)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(usize::MAX);

    let start = Instant::now();
    let db = match parse_database_file(std::path::Path::new(path)) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("parse error: {e}");
            return ExitCode::FAILURE;
        }
    };
    eprintln!(
        "parsed {} ({:.2}s, {} top-level statements)",
        path,
        start.elapsed().as_secs_f64(),
        db.statements.len()
    );

    let vstart = Instant::now();
    let report = match kernel_verify_database_prefix_count_only(&db, limit) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("verify error: {e}");
            return ExitCode::FAILURE;
        }
    };
    let elapsed = vstart.elapsed().as_secs_f64();

    let attempted = report.verified.len() + report.failed.len() + report.skipped.len();
    println!("=== kernel verification: {path} (limit={limit}) ===");
    println!("  attempted:  {attempted}");
    println!("  VERIFIED:   {}", report.verified.len());
    println!("  failed:     {}", report.failed.len());
    println!("  skipped:    {}", report.skipped.len());
    println!("  time:       {elapsed:.2}s");
    if !report.verified.is_empty() {
        let show: Vec<&String> = report.verified.iter().take(15).collect();
        println!("  first verified: {show:?}");
    }
    // Opt-in: dump EVERY verified label (one `V <label>` per line) so the
    // two-pass count-equivalence harness can diff this sequential set against
    // `mm_verify_range`'s set. Off by default to keep the normal summary terse.
    if std::env::var("CLEAN_MM_DUMP_VERIFIED").is_ok() {
        for label in &report.verified {
            println!("V {label}");
        }
    }
    for (label, reason) in report.failed.iter().take(8) {
        println!("    FAIL {label}: {reason}");
    }
    // Tally skip reasons.
    let mut compressed = 0;
    let mut oversized = 0;
    let mut dep = 0;
    let mut other = 0;
    for (_, r) in &report.skipped {
        if r.contains("compressed") {
            compressed += 1;
        } else if r.contains("size budget") {
            oversized += 1;
        } else if r.contains("did not verify") {
            dep += 1;
        } else {
            other += 1;
        }
    }
    if !report.skipped.is_empty() {
        println!(
            "  skip reasons: compressed={compressed}, oversized(inlining)={oversized}, dep-unverified={dep}, other={other}"
        );
        // Histogram of the "other" reasons (strip the trailing label/identifier).
        let mut hist: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for (_, r) in &report.skipped {
            if r.contains("compressed") || r.contains("size budget") || r.contains("did not verify")
            {
                continue;
            }
            // Key on the first 6 words to collapse per-theorem identifiers.
            let key: String = r.split_whitespace().take(6).collect::<Vec<_>>().join(" ");
            *hist.entry(key).or_insert(0) += 1;
        }
        let mut items: Vec<_> = hist.into_iter().collect();
        items.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
        for (k, n) in items.iter().take(8) {
            println!("    other[{n}]: {k}");
        }
    }

    if exposure {
        // R1-MM EXPOSURE. A pair here is a theorem the sequential verifier refuses
        // to build because it may not reuse `dep`, where `dep` nevertheless
        // VERIFIED — i.e. `dep` is verified-but-not-citable (the ground fallback).
        // The pre-fix two-pass export shipped every such dependent as
        // `KernelVerified`; the fixed gate drops them.
        let pairs = ground_reuse_exposure(&report);
        let ground: std::collections::HashSet<&str> =
            report.ground_only.iter().map(String::as_str).collect();
        println!("=== R1-MM exposure: {path} (limit={limit}) ===");
        println!("  verified:             {}", report.verified.len());
        println!("  verified ground-only: {}", report.ground_only.len());
        println!("  exposed dependents:   {}", pairs.len());
        for (dependent, dep) in &pairs {
            let how = if ground.contains(dep.as_str()) {
                "ground-only"
            } else {
                // Verified and cited but absent from the reuse cache for some other
                // reason. Report it rather than fold it into the ground-only story.
                "verified-but-uncached (NOT the ground fallback — investigate)"
            };
            println!("  EXPOSED {dependent} <- {dep} [{how}]");
        }
        if pairs.is_empty() {
            println!("  R1MM_EXPOSURE_VERDICT CLEAN (no verified-but-non-citable dependency is cited in this prefix)");
        } else {
            println!(
                "  R1MM_EXPOSURE_VERDICT EXPOSED ({} dependent(s) the pre-fix two-pass export shipped and the fixed gate drops)",
                pairs.len()
            );
            return ExitCode::from(EXIT_EXPOSED);
        }
    }
    ExitCode::SUCCESS
}
