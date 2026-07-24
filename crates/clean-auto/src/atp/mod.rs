// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ATP (Automated Theorem Proving) module for TPTP problem solving.
//!
//! Provides TPTP FOF/CNF parsing, clausification, and integration with
//! the existing superposition prover to solve first-order theorem proving
//! problems in TPTP format.
//!
//! # TPTP Format Support
//!
//! - **FOF** (First-Order Formula): Full first-order logic with quantifiers
//! - **CNF** (Clause Normal Form): Clauses as disjunctions of literals
//!
//! # SZS Status
//!
//! Output follows the TPTP/SZS ontology:
//! - `Theorem`: Problem proved (negated conjecture is unsatisfiable)
//! - `Unsatisfiable`: CNF clause set is unsatisfiable
//! - `CounterSatisfiable`: Found model for negated conjecture
//! - `Satisfiable`: CNF clause set is satisfiable
//! - `ResourceOut`: Resource limit reached
//! - `GaveUp`: Prover gave up

mod cnf_transform;
mod runner;
mod szs;
mod tptp_parser;
mod tptp_types;

pub use runner::{AtpConfig, AtpResult, AtpRunner};
pub use szs::SzsStatus;

#[cfg(test)]
mod tests;
