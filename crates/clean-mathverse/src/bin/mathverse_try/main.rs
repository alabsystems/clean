// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_try` — fast proof-term sketchpad CLI (Part of #3551).
//!
//! Techlead-facing iteration tool. Lets a human or AI agent type a goal
//! (proposition) and a proof term and get pass/fail + axiom closure back
//! in ~seconds — WITHOUT editing a full `nn_verify_tier_a_*.rs` file and
//! rebuilding the clean-Native shard.
//!
//! # Example
//!
//! ```text
//! $ cargo run --locked -p clean-mathverse --bin mathverse_try -- \
//!       --env seed-native \
//!       --goal '(Eq^1 Rat (Rat.min Rat.zero Rat.zero) Rat.zero)' \
//!       --proof '(Rat.min_def Rat.zero Rat.zero (Rat.le_refl Rat.zero))'
//! PASS
//! axiom_closure (non-foundational): []
//! classification: CONSTRUCTIVE
//! ```
//!
//! # Expression DSL
//!
//! A minimal s-expression format, built specifically for the Tier A
//! `Const + App` proof idiom. This is intentionally thin — the goal is
//! to unblock fast iteration on shard-level proofs without wiring up
//! the full Lean 4 surface parser (which would require elaboration and
//! implicit-argument inference, neither of which this tool owns).
//!
//! | Surface                           | Parses to                                            |
//! |-----------------------------------|------------------------------------------------------|
//! | `Rat.zero`                        | `Const("Rat.zero", [])`                              |
//! | `Eq^1`                            | `Const("Eq", [Level::succ(Level::zero())])`          |
//! | `Foo^2`                           | `Const("Foo", [succ(succ(zero))])`                   |
//! | `(f x y z)`                       | `App(App(App(f, x), y), z)`                          |
//! | `Prop`                            | `Sort(Level::zero())`                                |
//! | `Type`                            | `Sort(Level::succ(Level::zero()))`                   |
//!
//! JSON fallback: if either `--goal` or `--proof` starts with `json:`,
//! the remainder is parsed via `serde_json` directly into `ExprKind` (so
//! the full expression language is available for advanced use).

use std::io::{self, Write};
use std::process::ExitCode;

use clap::Parser;

mod parse;
mod report;
mod run;

use report::Status;
use run::{run, Args};

fn main() -> ExitCode {
    let args = Args::parse();
    let report = run(&args);
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let _ = if args.json {
        writeln!(out, "{}", report.to_json())
    } else {
        write!(out, "{}", report.to_text())
    };
    match report.status {
        Status::Pass => ExitCode::SUCCESS,
        Status::Fail => ExitCode::FAILURE,
    }
}
