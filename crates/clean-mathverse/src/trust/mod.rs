// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust enforcement and self-verification proofs for the Mathverse import pipeline.

pub mod audit_report;
pub mod axiom_propagation;
pub mod gamma_crown;
pub mod graph_gate;
pub mod header_gate;
pub mod policy;
pub mod project_audit;
pub mod trust_enforcement;
pub mod verification;

pub use policy::*;

#[cfg(test)]
mod tests;
