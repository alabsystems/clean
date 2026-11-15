// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `carcara-soundness`: run the rule-soundness battery and print a per-rule report.
//!
//! ```text
//! carcara-soundness [--mutants N] [--rounds N] [--seed N] [--threads N] [--rules a,b]
//!                   [--no-gen] [--models N] [--fuel N] [--examples N] [--tests DIR]
//!                   [--dialect upstream|clean|clean-bv-offset-spines-v1|clean-bv-reconstruct-v1]
//! carcara-soundness --fill DEFINITIONS PROOF
//! ```
//! `--dialect clean` parses every instance under `Config::clean_dialect()`, the configuration
//! `clean cert verify-external` checks with (third-party/carcara/DOWNSTREAM.md § Dialect).
//! Exit status is 1 when any accepted step has a counterexample. `--fill` prints a proof whose
//! first line is `; @@fill NAME` with `NAME` replaced by the term the checker expects there, which
//! is how the circuit regression tests in `carcara/tests/rules/bitvectors.rs` were produced.

use carcara_soundness::run::{render, run_battery, BatteryConfig};
use std::path::PathBuf;

fn main() {
    let mut cfg = BatteryConfig::default();
    let mut tests = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../carcara/tests/rules");
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut worker = false;
    let mut i = 0;
    while i < args.len() && args[i] != "--fill" {
        let val = |i: usize| args.get(i + 1).cloned().unwrap_or_default();
        match args[i].as_str() {
            "--mutants" => cfg.mutants_per_seed = val(i).parse().expect("--mutants N"),
            "--rounds" => cfg.max_rounds = val(i).parse().expect("--rounds N"),
            "--seed" => cfg.seed = val(i).parse().expect("--seed N"),
            "--threads" => cfg.threads = val(i).parse().expect("--threads N"),
            "--models" => cfg.oracle.random_models = val(i).parse().expect("--models N"),
            "--fuel" => cfg.oracle.fuel = val(i).parse().expect("--fuel N"),
            "--examples" => cfg.max_examples = val(i).parse().expect("--examples N"),
            "--rules" => cfg.rule_filter = Some(val(i).split(',').map(str::to_owned).collect()),
            "--tests" => tests = PathBuf::from(val(i)),
            "--dialect" => {
                cfg.oracle.dialect = carcara_soundness::oracle::Dialect::from_name(&val(i)).expect(
                    "--dialect upstream|clean|clean-bv-offset-spines-v1|clean-bv-reconstruct-v1",
                )
            }
            "--worker" => {
                worker = true;
                i += 1;
                continue;
            }
            "--no-gen" => {
                cfg.generators = false;
                i += 1;
                continue;
            }
            other => {
                eprintln!("unknown argument {}", other);
                std::process::exit(2);
            }
        }
        i += 2;
    }
    if args.first().map(String::as_str) == Some("--fill") {
        // carcara-soundness --fill <definitions file> <proof file whose first line is `; @@fill NAME`>
        let defs = std::fs::read_to_string(&args[1]).expect("definitions file");
        let proof = std::fs::read_to_string(&args[2]).expect("proof file");
        let inst = carcara_soundness::oracle::Instance { defs, proof };
        match carcara_soundness::oracle::fill_instance(&inst, cfg.oracle.dialect) {
            Ok(filled) => print!("{}", filled.proof),
            Err(o) => {
                eprintln!(
                    "fill failed: {:?} {:?} {:?}",
                    o.parse_error, o.panic, o.first_error
                );
                std::process::exit(1);
            }
        }
        return;
    }
    if worker {
        carcara_soundness::worker::serve(&cfg.oracle);
        return;
    }
    // Carcara panics on some malformed mutants; they are caught and counted, not printed.
    std::panic::set_hook(Box::new(|_| {}));
    let report = run_battery(&tests, &cfg);
    print!("{}", render(&report));
    let unsound: u64 = report.rules.values().map(|s| s.counterexamples).sum();
    std::process::exit(if unsound > 0 { 1 } else { 0 });
}
