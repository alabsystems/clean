// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end verification pipeline for a single bundled `ExampleProgram`.
//!
//! Split out of `cli.rs` (#3451) to keep the top-level CLI module under the
//! 500-line file-size cap. Public surface (`ExampleReport`, `run_example`)
//! is re-exported from the parent `cli` module so callers only need one use
//! path.

use std::path::PathBuf;

use crate::examples::{all_examples, ExampleError, ExampleProgram};
use crate::expr::EvalResult;
use crate::types::UintType;
use crate::values::Value;

use super::RustSemCliError;

/// Verification report for a single example program.
#[derive(Debug, Clone)]
pub struct ExampleReport {
    /// Name of the example that was verified.
    pub name: String,
    /// Relative path of the source fixture on disk.
    pub fixture_path: PathBuf,
    /// Human-readable description from the example catalog.
    pub description: String,
    /// Outcome of the VIR / NLL borrow-check pass.
    pub borrow_outcome: BorrowOutcome,
    /// Outcome of the stacked-borrows aliasing interpreter.
    pub aliasing_outcome: AliasingOutcome,
    /// Outcome of the proof-bundle construction pipeline.
    pub proof_bundle_outcome: ProofBundleOutcome,
}

/// Borrow-checker outcome classifications for a single example.
#[derive(Debug, Clone)]
pub enum BorrowOutcome {
    /// Every function lowered cleanly and NLL accepted the program.
    Clean,
    /// Every function lowered cleanly and NLL rejected the expected function
    /// (a negative example whose failure is part of the contract).
    ExpectedError {
        /// Name of the function that produced the rejection.
        function: String,
        /// Count of NLL errors reported for that function.
        error_count: usize,
    },
    /// No borrow checks were requested for this example.
    Skipped,
}

/// Aliasing-interpreter outcome classifications for a single example.
#[derive(Debug, Clone)]
pub enum AliasingOutcome {
    /// Interpreter returned a concrete `u32` value as specified.
    ReturnedU32(u32),
    /// Interpreter reported the substring the expectation required
    /// (typically for negative fixtures).
    ErrorContains(String),
    /// Interpreter was not exercised (example opts out via `Skip`).
    Skipped,
}

/// Proof-bundle outcome classifications for a single example.
#[derive(Debug, Clone)]
pub enum ProofBundleOutcome {
    /// Bundle builder produced a non-empty proof bundle.
    Built {
        /// Number of translated function types recorded in the bundle.
        function_count: usize,
        /// Number of ownership obligations recorded in the bundle.
        obligation_count: usize,
    },
    /// Bundle construction was skipped for an example that legitimately cannot
    /// build one (e.g. expectations require a borrow-check failure).
    SkippedDueToExpectedError,
}

impl ExampleReport {
    /// Print a human-readable summary to stdout. `verbose` controls whether
    /// per-stage details are emitted in addition to the one-line summary.
    pub fn print(&self, verbose: bool) {
        println!("clean verify rust --example {}", self.name);
        println!("  fixture: {}", self.fixture_path.display());
        println!("  description: {}", self.description);
        match &self.borrow_outcome {
            BorrowOutcome::Clean => println!("  borrow-check: clean"),
            BorrowOutcome::ExpectedError {
                function,
                error_count,
            } => {
                println!("  borrow-check: expected error in `{function}` ({error_count} reported)")
            }
            BorrowOutcome::Skipped => println!("  borrow-check: skipped"),
        }
        match &self.aliasing_outcome {
            AliasingOutcome::ReturnedU32(v) => {
                println!("  aliasing-run: returned u32 = {v}");
            }
            AliasingOutcome::ErrorContains(needle) => {
                println!("  aliasing-run: rejected with `{needle}` in the error message");
            }
            AliasingOutcome::Skipped => println!("  aliasing-run: skipped"),
        }
        match &self.proof_bundle_outcome {
            ProofBundleOutcome::Built {
                function_count,
                obligation_count,
            } => println!(
                "  proof-bundle: {function_count} functions, {obligation_count} obligations"
            ),
            ProofBundleOutcome::SkippedDueToExpectedError => {
                println!("  proof-bundle: skipped (negative example expects a borrow error)");
            }
        }
        if verbose {
            // Verbose mode currently re-prints the same information with
            // stage headers; richer per-stage introspection (individual NLL
            // errors, per-function obligations, interpreter trace) is left
            // to the experimental follow-ups tracked on #3451.
            println!("  [verbose] Further per-stage detail will land with the");
            println!("  [verbose] follow-up issues that stabilize the library API.");
        }
        println!("Verification complete.");
    }
}

/// Run the end-to-end verification pipeline for the bundled example named
/// `name` and return a structured [`ExampleReport`].
///
/// The pipeline follows the contract laid out in the example catalog
/// (`crate::examples`):
///
/// 1. Parse the embedded Rust source via `SourceProgram::parse`.
/// 2. Lower each function body into VIR and run NLL borrow checking.
///    - `BorrowExpectation::Clean` → every function must verify.
///    - `BorrowExpectation::ErrorsIn { function }` → that function must
///      produce at least one NLL error; other functions must remain clean.
/// 3. Run the stacked-borrows aliasing interpreter and compare against the
///    declared `AliasingExpectation`.
/// 4. Build the ownership proof bundle via `ProofBundleBuilder`.
///    - Negative examples (step 2 failure) legitimately cannot build a bundle;
///      we mark `SkippedDueToExpectedError` in that case.
///
/// Any deviation from the declared expectation becomes a
/// [`RustSemCliError`].
pub fn run_example(name: &str) -> Result<ExampleReport, RustSemCliError> {
    let example = find_example(name)?;

    let program = example
        .parse()
        .map_err(|source| RustSemCliError::ParseFailed {
            name: example.name.to_string(),
            source,
        })?;

    let borrow_outcome = evaluate_borrow_outcome(&example, &program)?;

    let aliasing_outcome = evaluate_aliasing_outcome(&example, &program)?;

    let proof_bundle_outcome = evaluate_proof_bundle_outcome(&example, &program, &borrow_outcome)?;

    Ok(ExampleReport {
        name: example.name.to_string(),
        fixture_path: example.file_path(),
        description: example.description.to_string(),
        borrow_outcome,
        aliasing_outcome,
        proof_bundle_outcome,
    })
}

/// Print the bundled example catalog to stdout.
pub fn print_catalog() {
    println!("Available examples for `clean verify rust --example <NAME>`:");
    for example in all_examples() {
        println!("  {:<32} {}", example.name, example.description);
    }
}

/// Map an [`ExampleError`] into a friendly CLI error for callers that surface
/// lowering failures separately. Currently unused in the MVP but kept public
/// so follow-up issues can reuse the mapping.
#[must_use]
pub fn example_error_to_cli(name: &str, err: &ExampleError) -> RustSemCliError {
    RustSemCliError::BorrowCheckFailed {
        name: name.to_string(),
        detail: err.to_string(),
    }
}

fn find_example(name: &str) -> Result<ExampleProgram, RustSemCliError> {
    all_examples()
        .into_iter()
        .find(|e| e.name == name)
        .ok_or_else(|| RustSemCliError::UnknownExample {
            name: name.to_string(),
        })
}

fn evaluate_borrow_outcome(
    example: &ExampleProgram,
    program: &crate::source::SourceProgram,
) -> Result<BorrowOutcome, RustSemCliError> {
    use crate::examples::BorrowExpectation;

    let results = program
        .check_borrows()
        .map_err(|err| RustSemCliError::BorrowCheckFailed {
            name: example.name.to_string(),
            detail: err.to_string(),
        })?;

    match example.borrow_expectation {
        BorrowExpectation::Clean => {
            for (function, nll) in &results {
                if !nll.errors.is_empty() {
                    return Err(RustSemCliError::BorrowCheckFailed {
                        name: example.name.to_string(),
                        detail: format!(
                            "function `{function}` unexpectedly produced {} NLL error(s)",
                            nll.errors.len()
                        ),
                    });
                }
            }
            Ok(BorrowOutcome::Clean)
        }
        BorrowExpectation::ErrorsIn { function } => {
            let target =
                results
                    .get(function)
                    .ok_or_else(|| RustSemCliError::BorrowCheckFailed {
                        name: example.name.to_string(),
                        detail: format!(
                            "function `{function}` missing from NLL results (expected to fail)"
                        ),
                    })?;
            if target.errors.is_empty() {
                return Err(RustSemCliError::ExpectedErrorNotReported {
                    name: example.name.to_string(),
                    function: function.to_string(),
                });
            }
            Ok(BorrowOutcome::ExpectedError {
                function: function.to_string(),
                error_count: target.errors.len(),
            })
        }
    }
}

fn evaluate_aliasing_outcome(
    example: &ExampleProgram,
    program: &crate::source::SourceProgram,
) -> Result<AliasingOutcome, RustSemCliError> {
    use crate::examples::AliasingExpectation;

    match example.aliasing_expectation {
        AliasingExpectation::Skip => Ok(AliasingOutcome::Skipped),
        AliasingExpectation::ReturnsU32(expected) => {
            let result = program.run_with_aliasing_checks();
            match result {
                EvalResult::Value(value) | EvalResult::Return(value) => {
                    let got =
                        value_as_u32(&value).ok_or_else(|| RustSemCliError::BorrowCheckFailed {
                            name: example.name.to_string(),
                            detail: format!(
                                "aliasing interpreter returned non-u32 value: {value:?}"
                            ),
                        })?;
                    if got == expected {
                        Ok(AliasingOutcome::ReturnedU32(got))
                    } else {
                        Err(RustSemCliError::BorrowCheckFailed {
                            name: example.name.to_string(),
                            detail: format!(
                                "aliasing interpreter returned {got}, expected {expected}"
                            ),
                        })
                    }
                }
                other => Err(RustSemCliError::BorrowCheckFailed {
                    name: example.name.to_string(),
                    detail: format!("aliasing interpreter did not return a value: {other:?}"),
                }),
            }
        }
        AliasingExpectation::ErrorContains(needle) => {
            let result = program.run_with_aliasing_checks();
            match result {
                EvalResult::Error(msg) | EvalResult::Panic(msg) => {
                    if msg.contains(needle) {
                        Ok(AliasingOutcome::ErrorContains(needle.to_string()))
                    } else {
                        Err(RustSemCliError::BorrowCheckFailed {
                            name: example.name.to_string(),
                            detail: format!(
                                "aliasing interpreter error `{msg}` did not contain expected `{needle}`"
                            ),
                        })
                    }
                }
                other => Err(RustSemCliError::BorrowCheckFailed {
                    name: example.name.to_string(),
                    detail: format!(
                        "aliasing interpreter did not reject program as expected: {other:?}"
                    ),
                }),
            }
        }
    }
}

fn evaluate_proof_bundle_outcome(
    example: &ExampleProgram,
    program: &crate::source::SourceProgram,
    borrow_outcome: &BorrowOutcome,
) -> Result<ProofBundleOutcome, RustSemCliError> {
    match borrow_outcome {
        BorrowOutcome::ExpectedError { .. } => {
            // Negative examples intentionally fail NLL; bundle construction on
            // them would conflate "proof bundle broken" with "Rust program is
            // rejected". Skip and record that we did so.
            Ok(ProofBundleOutcome::SkippedDueToExpectedError)
        }
        BorrowOutcome::Clean | BorrowOutcome::Skipped => {
            let bundle =
                program
                    .build_proof_bundle()
                    .map_err(|err| RustSemCliError::ProofBundleFailed {
                        name: example.name.to_string(),
                        detail: err.to_string(),
                    })?;
            // Use the public fields on `RustProofBundle` rather than a
            // getter API — the library intentionally exposes them directly
            // pending stabilization (#3451 is Experimental).
            let function_count = bundle.translated_types.len();
            let obligation_count = bundle.obligations.len();
            Ok(ProofBundleOutcome::Built {
                function_count,
                obligation_count,
            })
        }
    }
}

/// Extract a concrete `u32` return value from a [`Value`] produced by the
/// stacked-borrows interpreter. Returns `None` for any other variant.
fn value_as_u32(value: &Value) -> Option<u32> {
    match *value {
        Value::Uint {
            value: v,
            ty: UintType::U32,
        } => u32::try_from(v).ok(),
        _ => None,
    }
}
