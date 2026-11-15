// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The declarations an [`ExportSource`](super::source::ExportSource) yields: every
//! name, level and expression already resolved to the kernel's own types.
//!
//! These mirror Lean's `ConstantInfo` records as lean4export 3.1.0 writes them
//! (`format_ndjson.md`), grouped the way the format groups an inductive block.
//! Nothing here is checked: the loader (`load.rs`) registers them in the
//! `.olean` loader's structural tier, and the replay decides them.

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

use crate::module::{DefinitionSafety, ParsedQuotKind, ReducibilityHintsData};

/// What every declaration states: its name, universe parameters and type.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ExportHeader {
    /// The declaration's name.
    pub name: Name,
    /// Its universe parameters, in order.
    pub level_params: Vec<Name>,
    /// Its type.
    pub type_: Expr,
}

/// One declaration of the export.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum ExportDeclaration {
    /// `axiom`.
    Axiom {
        /// Name, universe parameters, type.
        header: ExportHeader,
        /// `isUnsafe`.
        is_unsafe: bool,
    },
    /// `def`.
    Definition {
        /// Name, universe parameters, type.
        header: ExportHeader,
        /// Its value.
        value: Expr,
        /// Its reducibility hints.
        hints: ReducibilityHintsData,
        /// `safe`, `unsafe` or `partial`.
        safety: DefinitionSafety,
    },
    /// `thm`.
    Theorem {
        /// Name, universe parameters, type.
        header: ExportHeader,
        /// Its proof.
        value: Expr,
    },
    /// `opaque`.
    Opaque {
        /// Name, universe parameters, type.
        header: ExportHeader,
        /// Its value.
        value: Expr,
        /// `isUnsafe` (`false` when absent, as Lean's reader reads it).
        is_unsafe: bool,
    },
    /// `quot`: one of the four declarations Lean's `quotDecl` adds. Its stored
    /// type is data only: the quotient enters Clean's environment through
    /// `Environment::add_quot`, which builds the types itself.
    Quot {
        /// Name, universe parameters, type.
        header: ExportHeader,
        /// Which of the four.
        kind: ParsedQuotKind,
    },
    /// `inductive`: one block of types with their constructors and recursors.
    Inductive(ExportInductiveBlock),
}

impl ExportDeclaration {
    /// Every name this record declares.
    #[must_use]
    pub(crate) fn declared_names(&self) -> Vec<&Name> {
        match self {
            ExportDeclaration::Axiom { header, .. }
            | ExportDeclaration::Definition { header, .. }
            | ExportDeclaration::Theorem { header, .. }
            | ExportDeclaration::Opaque { header, .. }
            | ExportDeclaration::Quot { header, .. } => vec![&header.name],
            ExportDeclaration::Inductive(block) => block
                .types
                .iter()
                .map(|t| &t.header.name)
                .chain(block.ctors.iter().map(|c| &c.header.name))
                .chain(block.recs.iter().map(|r| &r.header.name))
                .collect(),
        }
    }
}

/// An `inductive` record: the format groups a (mutual) block's types, their
/// constructors and their recursors in one line.
#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct ExportInductiveBlock {
    /// `InductiveVal`s.
    pub types: Vec<ExportInductiveType>,
    /// `ConstructorVal`s.
    pub ctors: Vec<ExportConstructor>,
    /// `RecursorVal`s.
    pub recs: Vec<ExportRecursor>,
}

/// An `InductiveVal`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ExportInductiveType {
    /// Name, universe parameters, type.
    pub header: ExportHeader,
    /// `numParams`.
    pub num_params: u32,
    /// `numIndices`.
    pub num_indices: u32,
    /// `all`: the block's types.
    pub all: Vec<Name>,
    /// `ctors`: this type's constructors, in order.
    pub ctors: Vec<Name>,
    /// `numNested`.
    pub num_nested: u32,
    /// `isRec`.
    pub is_rec: bool,
    /// `isUnsafe`.
    pub is_unsafe: bool,
    /// `isReflexive`.
    pub is_reflexive: bool,
}

/// A `ConstructorVal`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ExportConstructor {
    /// Name, universe parameters, type.
    pub header: ExportHeader,
    /// `induct`: the type it constructs.
    pub induct: Name,
    /// `cidx`.
    pub cidx: u32,
    /// `numParams`.
    pub num_params: u32,
    /// `numFields`.
    pub num_fields: u32,
    /// `isUnsafe`.
    pub is_unsafe: bool,
}

/// A `RecursorVal`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ExportRecursor {
    /// Name, universe parameters, type.
    pub header: ExportHeader,
    /// `all`.
    pub all: Vec<Name>,
    /// `numParams`.
    pub num_params: u32,
    /// `numIndices`.
    pub num_indices: u32,
    /// `numMotives`.
    pub num_motives: u32,
    /// `numMinors`.
    pub num_minors: u32,
    /// `rules`.
    pub rules: Vec<ExportRecursorRule>,
    /// `k`.
    pub k: bool,
    /// `isUnsafe`.
    pub is_unsafe: bool,
}

/// A `RecursorRule`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ExportRecursorRule {
    /// `ctor`.
    pub ctor: Name,
    /// `nfields`.
    pub nfields: u32,
    /// `rhs`.
    pub rhs: Expr,
}
