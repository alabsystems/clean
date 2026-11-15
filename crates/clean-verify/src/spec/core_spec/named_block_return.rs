// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole listed-block return checking and selected-constructor consequences.
//! This does not prove Rust admission, positivity, source-table completeness,
//! or the correspondence between restored metadata and strict-time blocks.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod records;

enum DeclarationInput {
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    records::DECLARATIONS.iter()
}

impl Specification {
    /// Full only: consumes registered named/indexed guards and metadata.
    pub(super) fn add_named_block_return(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self, name, ty, body,
                    "Whole listed-block return guard reasoning; no Rust admission or output-typing premise.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent record-linked return checker or labeled synthetic model fixture.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
