// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatcher for `clean tlaps …`.
//!
//! Routes the clap subcommand tree exported from `clean_tla::bench::cli`
//! into the runner/schema helpers that the legacy `tlaps-bench` binary
//! called directly. Part of Epic #3436 (Phase 3, #3448).

use std::path::Path;

use clean_tla::bench::cli::{BenchArgs, ShowArgs, TlapsArgs, TlapsCommands, ValidateArgs};
use clean_tla::bench::runner::{BenchmarkResult, BenchmarkRunner};
use clean_tla::bench::schema::BenchmarkObligation;

/// Handle every `clean tlaps` invocation.
pub(crate) fn handle_tlaps_command(args: TlapsArgs) -> anyhow::Result<()> {
    match args.command {
        TlapsCommands::Bench(a) => run_bench(a),
        TlapsCommands::Validate(a) => run_validate(a),
        TlapsCommands::Show(a) => run_show(a),
    }
}

fn run_bench(args: BenchArgs) -> anyhow::Result<()> {
    let BenchArgs {
        path,
        verbose,
        json,
        failures_only,
    } = args;
    let mut runner = BenchmarkRunner::new();

    if path.is_file() {
        let obligation = BenchmarkObligation::load(&path)
            .map_err(|e| anyhow::anyhow!("loading {}: {e}", path.display()))?;
        let result = runner.run_obligation(&obligation);
        if verbose || (!result.correct && failures_only) {
            print_result(&result);
        }
    } else {
        runner
            .run_directory(&path)
            .map_err(|e| anyhow::anyhow!("running benchmarks in {}: {e}", path.display()))?;

        if verbose {
            for result in runner.results() {
                if !failures_only || !result.correct {
                    print_result(result);
                }
            }
        }
    }

    if json {
        let summary = runner.summary();
        println!("{}", serde_json::to_string_pretty(&summary)?);
    } else {
        runner.print_summary();
        if failures_only {
            runner.print_failures();
        }
    }
    Ok(())
}

fn print_result(result: &BenchmarkResult) {
    let status = if result.proved {
        "\u{2713}"
    } else {
        "\u{2717}"
    };
    let expected = if result.expected {
        "\u{2713}"
    } else {
        "\u{2717}"
    };
    let correct = if result.correct { "" } else { " [INCORRECT]" };

    println!(
        "{} {} (expected: {}, took {}ms){}",
        status, result.id, expected, result.time_ms, correct
    );

    if !result.tactics_tried.is_empty() {
        println!("  Tactics: {:?}", result.tactics_tried);
    }
    if let Some(err) = result.error.as_ref() {
        println!("  Error: {err}");
    }
}

fn run_validate(args: ValidateArgs) -> anyhow::Result<()> {
    let path = args.path;
    let mut valid: u64 = 0;
    let mut invalid: u64 = 0;

    if path.is_file() {
        report_validation(&path, &mut valid, &mut invalid);
    } else {
        for entry in walkdir::WalkDir::new(&path)
            .into_iter()
            .filter_map(Result::ok)
        {
            let entry_path = entry.path();
            if entry_path.is_file()
                && entry_path.extension().and_then(|s| s.to_str()) == Some("json")
            {
                report_validation(entry_path, &mut valid, &mut invalid);
            }
        }
    }

    println!("\nValidation: {valid} valid, {invalid} invalid");
    if invalid > 0 {
        anyhow::bail!("{invalid} benchmark file(s) failed validation");
    }
    Ok(())
}

fn report_validation(entry: &Path, valid: &mut u64, invalid: &mut u64) {
    match BenchmarkObligation::load(entry) {
        Ok(obligation) => match obligation.to_tla_obligation() {
            Ok(_) => {
                println!("\u{2713} {}", entry.display());
                *valid += 1;
            }
            Err(e) => {
                println!("\u{2717} {} - Parse error: {e}", entry.display());
                *invalid += 1;
            }
        },
        Err(e) => {
            println!("\u{2717} {} - Load error: {e}", entry.display());
            *invalid += 1;
        }
    }
}

fn run_show(args: ShowArgs) -> anyhow::Result<()> {
    let path = args.path;
    let obligation = BenchmarkObligation::load(&path)
        .map_err(|e| anyhow::anyhow!("loading {}: {e}", path.display()))?;

    println!("ID: {}", obligation.id);
    println!("Module: {}", obligation.module);
    if let Some(line) = obligation.line {
        println!("Line: {line}");
    }
    println!(
        "Expected: {}",
        if obligation.expected_result {
            "provable"
        } else {
            "unprovable"
        }
    );
    println!("Difficulty: {}", obligation.difficulty);
    println!("Source: {}", obligation.source);
    println!("Tags: {:?}", obligation.tags);
    println!("Tactic hint: {:?}", obligation.tactic_hint);

    println!("\nDeclarations:");
    for decl in &obligation.declares {
        println!("  {} {} (arity {})", decl.decl_type, decl.name, decl.arity);
    }

    println!("\nHypotheses:");
    for hyp in &obligation.hypotheses {
        println!("  {}: {:?}", hyp.name, hyp.formula);
    }

    println!("\nGoal: {:?}", obligation.goal);

    match obligation.to_tla_obligation() {
        Ok(tla) => {
            println!("\nParsed TlaObligation:");
            println!("  Goal type: {:?}", std::mem::discriminant(&tla.goal));
            println!("  Temporal: {}", tla.is_temporal());
            println!("  Likely needs induction: {}", tla.likely_needs_induction());
        }
        Err(e) => {
            println!("\nParse error: {e}");
        }
    }
    Ok(())
}
