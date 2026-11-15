// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `eval_ir_reuse_measure` — the explicit tool for the two expensive EvalIR
//! reuse procedures that must not sit in the test suite as ignored tests.
//!
//! ```text
//! targo --unverified run -p clean-verify --bin eval_ir_reuse_measure -- measure
//! targo --unverified run -p clean-verify --bin eval_ir_reuse_measure -- differential
//! targo --unverified run -p clean-verify --bin eval_ir_reuse_measure            # both
//! ```
//!
//! Exit status is the verdict: 0 when every requested procedure completed with
//! its invariants intact, 1 when one failed, 2 on a bad argument.

use clean_verify::eval_ir::reuse_measure::{
    measure_consecutive_byte_builds_and_clone, vocabulary_cached_byte_matches_fresh_constructor,
};
use std::process::ExitCode;

/// What `-h`/`--help` prints: the one mode word `main` reads, nothing more.
const USAGE: &str = "\
usage: eval_ir_reuse_measure [measure | differential | all]   (default: all)
  measure       time two consecutive byte-vocabulary builds and a clone, with RSS samples
  differential  check that the vocabulary-cached byte build matches a fresh constructor
  Exit 0 when every requested procedure completed with its invariants intact, 1 when one
  failed, 2 on an unknown mode.
";

fn main() -> ExitCode {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "all".to_owned());
    let (do_measure, do_differential) = match mode.as_str() {
        "measure" => (true, false),
        "differential" => (false, true),
        "all" => (true, true),
        "-h" | "--help" => {
            print!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        other => {
            eprint!("eval_ir_reuse_measure: unknown mode `{other}`\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let mut failed = false;
    if do_measure {
        match measure_consecutive_byte_builds_and_clone() {
            Ok(m) => {
                println!(
                    "byte-vocabulary-measure first_ms={} second_ms={} clone_ms={} definitions={} constants={}",
                    m.first_build.as_millis(),
                    m.second_build.as_millis(),
                    m.clone.as_millis(),
                    m.definitions,
                    m.constants
                );
                println!(
                    "byte-vocabulary-rss-kib before={:?} after_first={:?} with_copies={:?} after_owned_drop={:?}; process RSS includes allocator retention, not exact live-object size",
                    m.rss_kib_before,
                    m.rss_kib_after_first,
                    m.rss_kib_with_copies,
                    m.rss_kib_after_owned_drop
                );
            }
            Err(error) => {
                eprintln!("eval_ir_reuse_measure: measure FAILED: {error}");
                failed = true;
            }
        }
    }
    if do_differential {
        match vocabulary_cached_byte_matches_fresh_constructor() {
            Ok(compared) => {
                println!("byte-vocabulary-differential ok definitions_compared={compared}")
            }
            Err(error) => {
                eprintln!("eval_ir_reuse_measure: differential FAILED: {error}");
                failed = true;
            }
        }
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
