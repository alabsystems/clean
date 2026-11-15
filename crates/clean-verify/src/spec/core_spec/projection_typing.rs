// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive CDP typing, dependent field domains, and typed constructor spines.
//!
//! Whole-typing generation and successful raw Pi-spine computations recover
//! argument typings and residual conversion; they do not assume those outputs.
//! The dependent DepPair fixture is model data, not a reflected or admitted
//! declaration. Its selected-field result starts from OLD whole typing and a
//! fixed-family resolver, not inference of an arbitrary observed subject type.
//! No projection-expression typing rule is added. Existing acceptance judgments
//! are unchanged; admission soundness and executing Rust correspondence remain
//! separate obligations.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod domain;
mod generation;
mod instantiation;
mod spine;
mod typing;

enum DeclarationInput {
    Inductive(&'static str),
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    domain::DECLARATIONS
        .iter()
        .chain(typing::DECLARATIONS)
        .chain(generation::DECLARATIONS)
        .chain(instantiation::DECLARATIONS)
        .chain(spine::DECLARATIONS)
}

impl Specification {
    /// Full bundle only, after additive projection-aware semantic conversion.
    pub(super) fn add_projection_typing(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Actual additive typing or generation/spine carrier with checked eliminator; no projection-expression typing or acceptance rule.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Checked dependent-domain, additive typing, generation, instantiation or whole-spine proof; no assumed output typing, admission or source-execution claim.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent typing family or explicit model fixture; DepPair data is not reflected or admitted source metadata.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
