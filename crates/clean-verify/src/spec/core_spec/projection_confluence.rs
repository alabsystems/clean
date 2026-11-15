// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit confluence of projection-extended raw reduction.
//!
//! The generic union theorem derives confluence from the two component
//! confluence proofs and genuine oriented one-step strong commutation. Concrete
//! old-CD/projection proofs discharge those premises, and both actual closure
//! inclusions transport the result to CDP-star. Environment conditions remain
//! explicit, with a checked instance for the finite reflected environment.
//! Acceptance migration, typing and executing Rust correspondence are separate.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod cdp_bindings;
mod composition;
mod iota;
mod mixed_roots;
mod mixed_strong;
mod projection_only;
mod relation_union;
mod union_sandwich;

enum DeclarationInput {
    Inductive(&'static str),
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    relation_union::DECLARATIONS
        .iter()
        .chain(cdp_bindings::DECLARATIONS)
        .chain(projection_only::DECLARATIONS)
        .chain(mixed_roots::DECLARATIONS)
        .chain(iota::DECLARATIONS)
        .chain(mixed_strong::DECLARATIONS)
        .chain(union_sandwich::DECLARATIONS)
        .chain(composition::DECLARATIONS)
}

impl Specification {
    /// Full bundle only; concrete projection prerequisites precede this unit.
    pub(super) fn add_projection_confluence(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Actual Type-valued relation carrier with checked eliminator; not an axiom or an acceptance judgment.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Checked relation composition with explicit colored residuals; no source-execution or environment-admission claim.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent relation abbreviation or raw computational fixture, not an axiom or admission theorem.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
