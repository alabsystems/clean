// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection-aware semantic conversion and shape injectivity.
//!
//! Universe transport covers every CDP constructor. Actual confluence composes
//! semantic joins, and checked conversion preserves its real reduction paths.
//! Sort/Pi inversion retains semantic universe equality and component conversion.
//! The old acceptance judgments are unchanged; typing, admission and executing
//! Rust correspondence remain separate obligations.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod conversion;
mod injectivity;
mod join;
mod universe;

enum DeclarationInput {
    Inductive(&'static str),
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    universe::DECLARATIONS
        .iter()
        .chain(join::DECLARATIONS)
        .chain(conversion::DECLARATIONS)
        .chain(injectivity::DECLARATIONS)
}

impl Specification {
    /// Full bundle only, after the actual projection-confluence prerequisites.
    pub(super) fn add_projection_semantic(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Actual additive projection-aware relation carrier with checked eliminator; not an axiom or a replacement acceptance judgment.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Checked CDP universe transport, semantic conversion or shape inversion; no assumed output join, admission or source-execution claim.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent transport family or actual projection fixture, not an axiom or admission theorem.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
