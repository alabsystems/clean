// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordered shared-table installation and exact lookup preservation.
//! Cross-kind shadowing is retained. These facts do not establish source-list
//! completeness, admission, typing preservation, or Rust execution refinement.

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
    /// Full only: shared-table lookup facts and source-selected Eq callers.
    pub(super) fn add_ind_ctor_table(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self, name, ty, body,
                    "Computed shared-table lookup preservation, including cross-kind shadowing; no admission or desired-lookup premise.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent ordered table operation or finite source-selected Eq update stream.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
