// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-verify Metamath theorems from a `.mm` file.
//!
//! Usage: `mm_kverify <path.mm> [max_provables]`
//!
//! Parses the database, then has the Clean kernel certify each `$p` theorem
//! (reusing earlier theorems by proof inlining). Prints verified / failed /
//! skipped counts. `max_provables` bounds how many theorems are attempted (the
//! inlining strategy blows up on deeply-reused proofs in large databases).

use std::process::ExitCode;
use std::time::Instant;

use clean_olean::metamath::{kernel_verify_database_prefix_count_only, parse_database_file};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: mm_kverify <path.mm> [max_provables]");
        return ExitCode::FAILURE;
    }
    let path = &args[1];
    let limit = args
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
    ExitCode::SUCCESS
}
