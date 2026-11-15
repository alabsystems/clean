// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete raw-list metadata installation and a direct whole-return check.
//!
//! Raw input positions and flattened name uniqueness derive exact table
//! lookups. Direct raw whole-check success derives the installed NRB check,
//! and two input positions derive the selected constructor's return facts.
//! These computations do not establish external source completeness, strict
//! admission, positivity, transaction preservation or Rust execution refinement.
//! Metadata ctor-before-member order does not describe ConstantInfo insertion;
//! strict-time blocks are not identified with final nested-restored captures.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod family;
mod raw;
mod whole;

enum DeclarationInput {
    Inductive(&'static str),
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    raw::DECLARATIONS
        .iter()
        .chain(family::DECLARATIONS)
        .chain(whole::DECLARATIONS)
}

impl Specification {
    /// Full only, after exact shared-table insertion and lookup preservation.
    pub(super) fn add_raw_block_return(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Raw named source record carrier; no completeness, typing or admission evidence is stored.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Complete modeled raw-list installation, input-position lookup or direct raw whole-return implication; no assumed output lookup or Rust execution refinement.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent raw-list operation, lookup-free whole-return predicate or explicitly synthetic raw fixture.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
