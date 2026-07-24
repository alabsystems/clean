// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TWO-PASS PARALLEL Metamath range verifier (one worker of the parallel driver).
//!
//! Usage: `mm_verify_range <path.mm> <start> <end>`
//!
//! Verifies the PROOFS of the `$p` theorems whose 0-based provable ordinal lies
//! in `[start, end)`. Internally:
//!   PASS 1 registers EVERY `$p` theorem's schematic TYPE as an axiom (cheap, no
//!           proof check), building the dependency-type environment.
//!   PASS 2 re-verifies the proofs of the theorems in this range against that
//!           environment (the expensive, parallelizable work).
//!
//! Prints the verified count and one verified label per line (prefixed `V `) so
//! the driver (`scripts/mm_two_pass.sh`) can UNION the verified labels across
//! workers. `max_provables` is `end` — passes outside the range are still
//! traversed to build their axiom types, but only `[start, end)` is proof-checked.

use std::process::ExitCode;
use std::time::Instant;

use clean_olean::metamath::{kernel_verify_two_pass_range, parse_database_file};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 4 {
        eprintln!("usage: mm_verify_range <path.mm> <start> <end>");
        return ExitCode::FAILURE;
    }
    let path = &args[1];
    let start: usize = match args[2].parse() {
        Ok(n) => n,
        Err(_) => {
            eprintln!("error: <start> must be a non-negative integer");
            return ExitCode::FAILURE;
        }
    };
    let end: usize = match args[3].parse() {
        Ok(n) => n,
        Err(_) => {
            eprintln!("error: <end> must be a non-negative integer");
            return ExitCode::FAILURE;
        }
    };
    if start >= end {
        eprintln!("error: require start < end (got start={start}, end={end})");
        return ExitCode::FAILURE;
    }

    let t0 = Instant::now();
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
        t0.elapsed().as_secs_f64(),
        db.statements.len()
    );

    // `max_provables = end`: both passes traverse the prefix [0, end). Pass 1
    // registers types for all of [0, end); pass 2 proof-checks only [start, end).
    let tv = Instant::now();
    let report = match kernel_verify_two_pass_range(&db, start..end, end) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("verify error: {e}");
            return ExitCode::FAILURE;
        }
    };
    let elapsed = tv.elapsed().as_secs_f64();

    eprintln!(
        "=== two-pass range [{start},{end}) of {path}: VERIFIED={} failed={} skipped={} time={elapsed:.2}s ===",
        report.verified.len(),
        report.failed.len(),
        report.skipped.len()
    );
    // Any failure in a checked range is a soundness alarm — surface it loudly.
    for (label, reason) in report.failed.iter().take(20) {
        eprintln!("    FAIL {label}: {reason}");
    }

    // Machine-readable output for the driver: a count line then one label/line.
    println!("VERIFIED_COUNT {}", report.verified.len());
    for label in &report.verified {
        println!("V {label}");
    }
    ExitCode::SUCCESS
}
