// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructor return coherence within the existing modeled admission fragment.
//!
//! Successful return guards determine the exact ordered self-BVar parameter
//! spine; admitted declarations additionally establish the parameter-count bound.
//! The reflected monomorphic ProdType fixture constructs real model admission
//! and closes its self reference to the actual emitted signature. This finite
//! connection is not a general numeric-to-named environment representation,
//! indexed-family admission theorem, projection-expression typing rule, or
//! proof of executing Rust admission. Existing judgments remain unchanged.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod admission;
mod generic_closing;
mod prod_admission;
mod return_spine;

enum DeclarationInput {
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    admission::DECLARATIONS
        .iter()
        .chain(prod_admission::DECLARATIONS)
        .chain(return_spine::DECLARATIONS)
        .chain(generic_closing::DECLARATIONS)
}

impl Specification {
    /// Full bundle only, after the dependent projection typing prerequisites.
    pub(super) fn add_constructor_return_coherence(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Checked existing-fragment admission/return-spine derivation or finite reflected ProdType connection; no general source-admission or projection-typing claim.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent computed return/list function or explicit finite model fixture; numeric IDs are not source interning tags.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
