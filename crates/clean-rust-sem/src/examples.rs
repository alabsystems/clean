// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Worked Rust ownership examples for `clean-rust-sem`.
//!
//! The source fixtures live under `examples/ownership/` and `examples/negative/`
//! so they remain readable as standalone programs while the crate exposes a
//! typed catalog that can run them through source parsing, VIR lowering, NLL,
//! and stacked-borrows evaluation.

use crate::expr::EvalResult;
use crate::nll::NllResult;
use crate::proof_bundle::RustProofBundle;
use crate::source::{SourceError, SourceProgram};
use crate::vir_lowering::VirLoweringError;
use std::collections::BTreeMap;
use std::path::PathBuf;
use thiserror::Error;

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ExampleError {
    #[error(transparent)]
    Source(#[from] SourceError),

    #[error(transparent)]
    Lowering(#[from] VirLoweringError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BorrowExpectation {
    Clean,
    ErrorsIn { function: &'static str },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AliasingExpectation {
    Skip,
    ReturnsU32(u32),
    ErrorContains(&'static str),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExampleProgram {
    pub name: &'static str,
    pub description: &'static str,
    pub relative_path: &'static str,
    pub source: &'static str,
    pub borrow_expectation: BorrowExpectation,
    pub aliasing_expectation: AliasingExpectation,
}

impl ExampleProgram {
    #[must_use]
    pub fn file_path(self) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(self.relative_path)
    }

    pub fn parse(self) -> Result<SourceProgram, SourceError> {
        SourceProgram::parse(self.source)
    }

    pub fn from_file(self) -> Result<SourceProgram, SourceError> {
        SourceProgram::from_file(self.file_path())
    }

    pub fn check_borrows(self) -> Result<BTreeMap<String, NllResult>, ExampleError> {
        Ok(self.parse()?.check_borrows()?)
    }

    pub fn run_with_aliasing_checks(self) -> Result<EvalResult, SourceError> {
        Ok(self.parse()?.run_with_aliasing_checks())
    }

    pub fn build_proof_bundle(self) -> Result<RustProofBundle, ExampleError> {
        Ok(self.parse()?.build_proof_bundle()?)
    }
}

#[must_use]
pub fn inventory_restock_example() -> ExampleProgram {
    ExampleProgram {
        name: "inventory_restock",
        description: "Method-call two-phase borrowing over an inventory restock workflow.",
        relative_path: "examples/ownership/inventory_restock.rs",
        source: include_str!("../examples/ownership/inventory_restock.rs"),
        borrow_expectation: BorrowExpectation::Clean,
        aliasing_expectation: AliasingExpectation::ReturnsU32(9),
    }
}

#[must_use]
pub fn disjoint_field_scoreboard_example() -> ExampleProgram {
    ExampleProgram {
        name: "disjoint_field_scoreboard",
        description: "A shared borrow of one field survives a write to a disjoint field.",
        relative_path: "examples/ownership/disjoint_field_scoreboard.rs",
        source: include_str!("../examples/ownership/disjoint_field_scoreboard.rs"),
        borrow_expectation: BorrowExpectation::Clean,
        aliasing_expectation: AliasingExpectation::ReturnsU32(6),
    }
}

#[must_use]
pub fn stale_account_snapshot_example() -> ExampleProgram {
    ExampleProgram {
        name: "stale_account_snapshot",
        description: "A snapshot borrow becomes invalid after mutating the borrowed field.",
        relative_path: "examples/negative/stale_account_snapshot.rs",
        source: include_str!("../examples/negative/stale_account_snapshot.rs"),
        borrow_expectation: BorrowExpectation::ErrorsIn { function: "main" },
        aliasing_expectation: AliasingExpectation::Skip,
    }
}

#[must_use]
pub fn protected_receiver_raw_write_example() -> ExampleProgram {
    ExampleProgram {
        name: "protected_receiver_raw_write",
        description: "A shared receiver must reject a raw-pointer overwrite of the same referent.",
        relative_path: "examples/negative/protected_receiver_raw_write.rs",
        source: include_str!("../examples/negative/protected_receiver_raw_write.rs"),
        // rustc's borrow checker accepts this program: the `&mut session`
        // temporary's loan ends at the raw-pointer cast (drop-liveness — a
        // reference has no drop glue), and raw-pointer writes escape NLL.
        // The undefined behavior is caught by the Stacked Borrows aliasing
        // checker below, exactly as Miri (not rustc) rejects it.
        borrow_expectation: BorrowExpectation::Clean,
        aliasing_expectation: AliasingExpectation::ErrorContains("borrow error"),
    }
}

#[must_use]
pub fn enum_state_machine_example() -> ExampleProgram {
    ExampleProgram {
        name: "enum_state_machine",
        description: "Enum variants with data consumed by pattern-matching functions.",
        relative_path: "examples/ownership/enum_state_machine.rs",
        source: include_str!("../examples/ownership/enum_state_machine.rs"),
        borrow_expectation: BorrowExpectation::Clean,
        aliasing_expectation: AliasingExpectation::ReturnsU32(20),
    }
}

#[must_use]
pub fn overlapping_mut_borrows_example() -> ExampleProgram {
    ExampleProgram {
        name: "overlapping_mut_borrows",
        description: "Two live &mut borrows of the same struct must be rejected by NLL.",
        relative_path: "examples/negative/overlapping_mut_borrows.rs",
        source: include_str!("../examples/negative/overlapping_mut_borrows.rs"),
        borrow_expectation: BorrowExpectation::ErrorsIn { function: "main" },
        aliasing_expectation: AliasingExpectation::Skip,
    }
}

#[must_use]
pub fn raw_write_invalidates_reader_example() -> ExampleProgram {
    ExampleProgram {
        name: "raw_write_invalidates_reader",
        description: "A raw-pointer write must invalidate a co-existing shared reference.",
        relative_path: "examples/negative/raw_write_invalidates_reader.rs",
        source: include_str!("../examples/negative/raw_write_invalidates_reader.rs"),
        // rustc's borrow checker accepts this program: the `&mut` temporary's
        // loan ends at the raw-pointer cast (drop-liveness), and the later
        // write goes through a raw pointer, which NLL does not track. The
        // invalidation of `shared` is caught by the Stacked Borrows aliasing
        // checker below, exactly as Miri (not rustc) rejects it.
        borrow_expectation: BorrowExpectation::Clean,
        aliasing_expectation: AliasingExpectation::ErrorContains("borrow error"),
    }
}

#[must_use]
pub fn all_examples() -> [ExampleProgram; 7] {
    [
        inventory_restock_example(),
        disjoint_field_scoreboard_example(),
        stale_account_snapshot_example(),
        protected_receiver_raw_write_example(),
        enum_state_machine_example(),
        overlapping_mut_borrows_example(),
        raw_write_invalidates_reader_example(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::EvalResult;
    use crate::Value;

    #[test]
    fn test_all_examples_parse_from_embedded_source_and_files() {
        for example in all_examples() {
            let inline_program = example.parse().unwrap_or_else(|err| {
                panic!("{} should parse from embedded source: {err}", example.name)
            });
            let file_program = example.from_file().unwrap_or_else(|err| {
                panic!("{} should parse from file fixture: {err}", example.name)
            });
            let inline_items = serde_json::to_value(inline_program.items()).unwrap_or_else(|err| {
                panic!(
                    "{} inline AST should serialize for exact fixture comparison: {err}",
                    example.name
                )
            });
            let file_items = serde_json::to_value(file_program.items()).unwrap_or_else(|err| {
                panic!(
                    "{} file AST should serialize for exact fixture comparison: {err}",
                    example.name
                )
            });
            assert_eq!(
                inline_items, file_items,
                "{} should expose the exact same AST from source and file fixtures",
                example.name
            );
        }
    }

    #[test]
    fn test_examples_match_expected_borrow_outcomes() {
        for example in all_examples() {
            let analyses = example
                .check_borrows()
                .unwrap_or_else(|err| panic!("{} should lower and run NLL: {err}", example.name));

            match example.borrow_expectation {
                BorrowExpectation::Clean => {
                    let failing = analyses
                        .iter()
                        .filter(|(_, result)| !result.errors.is_empty())
                        .map(|(name, result)| (name.as_str(), &result.errors))
                        .collect::<Vec<_>>();
                    assert!(
                        failing.is_empty(),
                        "{} should stay borrow-clean, got {failing:?}",
                        example.name
                    );
                }
                BorrowExpectation::ErrorsIn { function } => {
                    let result = analyses.get(function).unwrap_or_else(|| {
                        panic!(
                            "{} should report a lowered function named `{function}`",
                            example.name
                        )
                    });
                    assert!(
                        !result.errors.is_empty(),
                        "{} should report borrow-check errors in `{function}`",
                        example.name
                    );
                    let unexpected = analyses
                        .iter()
                        .filter(|(name, result)| {
                            name.as_str() != function && !result.errors.is_empty()
                        })
                        .map(|(name, result)| (name.as_str(), &result.errors))
                        .collect::<Vec<_>>();
                    assert!(
                        unexpected.is_empty(),
                        "{} should only report borrow-check errors in `{function}`, got extra failures: {unexpected:?}",
                        example.name
                    );
                }
            }
        }
    }

    #[test]
    fn test_examples_match_expected_aliasing_outcomes() {
        for example in all_examples() {
            match example.aliasing_expectation {
                AliasingExpectation::Skip => {}
                AliasingExpectation::ReturnsU32(expected) => {
                    let result = example.run_with_aliasing_checks().unwrap_or_else(|err| {
                        panic!(
                            "{} should parse before aliasing execution: {err}",
                            example.name
                        )
                    });
                    let value = result.clone().value();
                    assert_eq!(
                        value,
                        Some(Value::u32(expected)),
                        "{} should evaluate to {expected} under aliasing checks, got {result:?}",
                        example.name
                    );
                }
                AliasingExpectation::ErrorContains(expected) => {
                    let result = example.run_with_aliasing_checks().unwrap_or_else(|err| {
                        panic!(
                            "{} should parse before aliasing execution: {err}",
                            example.name
                        )
                    });
                    assert!(
                        matches!(result, EvalResult::Error(ref err) if err.contains(expected)),
                        "{} should fail aliasing execution with `{expected}`, got {result:?}",
                        example.name
                    );
                }
            }
        }
    }
}
