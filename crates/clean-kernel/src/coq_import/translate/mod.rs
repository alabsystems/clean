// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation from Coq `Constr` terms into clean kernel expressions.

mod context;
mod support;
mod translator;

use crate::inductive::InductiveDecl as KernelInductiveDecl;
use crate::Declaration;

pub use context::{InductiveMapping, TranslationContext};
pub use translator::{
    translate_constant_decl, translate_global_decl, translate_inductive_decl, translate_term,
    translate_term_with_context,
};

/// Result of translating one top-level Coq declaration.
#[derive(Debug, Clone)]
pub enum TranslatedGlobalDecl {
    Constant(Declaration),
    Inductive(KernelInductiveDecl),
}
