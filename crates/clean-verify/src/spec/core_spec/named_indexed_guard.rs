// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Named/indexed raw constructor-return checking and finite source-record evidence.
//!
//! Success determines an ordered parameter prefix and a block-free index suffix.
//! Caller prefix and former guards separately derive the parameter bound/index
//! count. The Eq consumer connects actual captured names, signatures and metadata.
//! Final stored blocks are not pre-restoration StrictCtx blocks; this does not
//! prove generic source admission, Rust execution refinement or new typing rules.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod evidence;
mod guard;

enum DeclarationInput {
    Inductive(&'static str),
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    guard::DECLARATIONS.iter().chain(evidence::DECLARATIONS)
}

impl Specification {
    /// Full only, after captured metadata and constructor-return prerequisites.
    pub(super) fn add_named_indexed_guard(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Actual Type-valued raw guard evidence with a checked eliminator; no assumed admission or typing judgment.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self, name, ty, body,
                    "Checked named/indexed guard reasoning or finite captured Eq record connection; no generic Rust/admission/StrictCtx correspondence claim.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent raw syntax computation or actual captured Eq data alias; not a theorem or an authored replacement source table.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
