// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Model units: the self-verification MODEL as real `.clean` files.
//!
//! Embed memo W1 (`designs/2026-08-28-embedding-the-kernel-model.md`, Step 1,
//! "Freeze the model"): the model used to live as Rust string literals handed
//! to `Specification::add_inductive` / `add_recursive_def`, which meant that
//! *no* scanner, gate or reader could see the model as Clean source — the
//! audit of 2026-09-10 (`trust/docs/audits/2026-09-10-prove-all-trust-audit.md`
//! §5.3) measured **zero** `.clean` files in the tree. This module is the
//! registration path that reads a unit from `crates/clean-verify/spec/<unit>.clean`
//! instead.
//!
//! ## What is preserved, and how it is checked
//!
//! The loader changes WHERE the source text lives and nothing else. Each
//! declaration chunk of a unit is handed to the SAME `add_inductive` /
//! `add_recursive_def` helpers the literal used (`declaration_registration.rs`),
//! so it is parsed by the same `parse_decl`, elaborated by the same
//! `elaborate_decl_and_register`, and recorded as the same `SpecDefinition`.
//! The doc comment (`/-- ... -/`) directly above a declaration is its
//! registered description, byte for byte. A declaration without one is refused,
//! with the fix.
//!
//! That "nothing else changed" claim is not asserted, it is measured: the
//! fidelity oracle in `model_units/tests.rs` registers every unit twice — from
//! the file and from the retained literal in `retained_literals.rs` — and
//! compares the two kernel environments constant by constant (type, value,
//! level params, reducibility, kind; inductive and recursor metadata including
//! every recursor rule) plus every `SpecDefinition` field, and the per
//! declaration axiom closure. A planted one-token edit in either the term or a
//! description turns it red (pinned by its own mutation arm).
//!
//! ## Source of the text
//!
//! The unit text is embedded with `include_str!` from
//! `crates/clean-verify/spec/*.clean` when the crate builds, so the `.clean`
//! file on disk IS the source of truth (cargo re-compiles when it changes) and
//! a shipped `clean` binary does not dereference a build-machine path at run
//! time. The oracle additionally reads each file from disk and asserts it is
//! byte-identical to the embedded copy.

use clean_parser::lexer::{Lexer, TokenKind};
use clean_parser::{Parser, SurfaceDecl, SurfaceName};

use super::{SpecError, Specification};

/// The foundation-agreement unit, checked against the model's own foundation —
/// the other half of the island check in `crates/clean-kernel/src/model_islands.rs`.
/// Test-only, like the oracle beside it: it builds specifications.
#[cfg(test)]
pub(crate) mod agreement;
#[cfg(test)]
pub(crate) mod retained_literals;
#[cfg(test)]
mod tests;

/// One `.clean` unit of the self-verification model.
///
/// Variants are listed in REGISTRATION order; `Self::ALL` is that order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ModelUnit {
    /// `spec/foundation_eq.clean` — `Eq`.
    FoundationEq,
    /// `spec/foundation_prod.clean` — `ProdType`.
    FoundationProd,
    /// `spec/foundation_nat.clean` — `Nat`, `Nat.add`, `Nat.pred`, `Nat.sub`.
    FoundationNat,
    /// `spec/foundation_order.clean` — `Lt`, `Le`.
    FoundationOrder,
    /// `spec/foundation_empty_and.clean` — `Empty`, `AndType`.
    FoundationEmptyAnd,
    /// `spec/foundation_agreement.clean` — the model's DEFINING EQUATIONS for the
    /// declarations it shares with any ambient environment (`Nat`, `Nat.add`,
    /// `Nat.pred`, `Nat.sub`, `Eq`, `Empty`) and for the ambient `Bool`, each held
    /// by `Eq.refl` so a kernel must decide it by computation.
    ///
    /// Registered into the LIVE specification so the independent Lean replay
    /// (`scripts/self_verify_crosscheck.sh`) re-checks it: the exporter roots at
    /// registered spec definitions, so a unit outside the spec is invisible to
    /// Lean. Also loaded as an island by `crates/clean-kernel/src/model_islands.rs`,
    /// where the SAME text is decided over the compiler prelude instead.
    ///
    /// BORN AS A FILE. Unlike the seven units W1 moved, this one never existed as
    /// a Rust string literal, so `retained_literals::of` has nothing to return for
    /// it and the W1 fidelity oracle has nothing to compare — see the fallback in
    /// `register_model_unit`.
    FoundationAgreement,
    /// `spec/expr_model_core.clean` — `Name`, `Level`, `ListType`, `KExpr` and
    /// the lift / instantiate layer.
    ExprModelCore,
    /// `spec/expr_model_spine.clean` — `kapp_fn`, `kapp_arg_count`,
    /// `is_const_app`.
    ExprModelSpine,
}

impl ModelUnit {
    /// Every unit, in registration order (the oracle walks it).
    #[cfg(test)]
    pub(crate) const ALL: &'static [ModelUnit] = &[
        ModelUnit::FoundationEq,
        ModelUnit::FoundationProd,
        ModelUnit::FoundationNat,
        ModelUnit::FoundationOrder,
        ModelUnit::FoundationEmptyAnd,
        ModelUnit::FoundationAgreement,
        ModelUnit::ExprModelCore,
        ModelUnit::ExprModelSpine,
    ];

    /// The unit's file name under `crates/clean-verify/spec/`.
    #[must_use]
    pub(crate) fn file_name(self) -> &'static str {
        match self {
            ModelUnit::FoundationEq => "foundation_eq.clean",
            ModelUnit::FoundationProd => "foundation_prod.clean",
            ModelUnit::FoundationNat => "foundation_nat.clean",
            ModelUnit::FoundationOrder => "foundation_order.clean",
            ModelUnit::FoundationEmptyAnd => "foundation_empty_and.clean",
            ModelUnit::ExprModelCore => "expr_model_core.clean",
            ModelUnit::ExprModelSpine => "expr_model_spine.clean",
            ModelUnit::FoundationAgreement => "foundation_agreement.clean",
        }
    }

    /// The unit's text, embedded from `crates/clean-verify/spec/<file>` at
    /// crate build time (see the module docs for why not a run-time read).
    #[must_use]
    pub(crate) fn embedded_source(self) -> &'static str {
        match self {
            ModelUnit::FoundationEq => include_str!("../../spec/foundation_eq.clean"),
            ModelUnit::FoundationProd => include_str!("../../spec/foundation_prod.clean"),
            ModelUnit::FoundationNat => include_str!("../../spec/foundation_nat.clean"),
            ModelUnit::FoundationOrder => include_str!("../../spec/foundation_order.clean"),
            ModelUnit::FoundationEmptyAnd => {
                include_str!("../../spec/foundation_empty_and.clean")
            }
            ModelUnit::ExprModelCore => include_str!("../../spec/expr_model_core.clean"),
            ModelUnit::ExprModelSpine => include_str!("../../spec/expr_model_spine.clean"),
            ModelUnit::FoundationAgreement => {
                include_str!("../../spec/foundation_agreement.clean")
            }
        }
    }
}

/// Which registration helper a model declaration goes through.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LiteralKind {
    /// `inductive ...` — registered by `Specification::add_inductive`.
    Inductive,
    /// `def ...` — registered by `Specification::add_recursive_def`.
    RecursiveDef,
}

/// A retained pre-move literal: exactly the `(source, description)` pair the
/// Rust registration code used to pass. Only the fidelity oracle reads these.
#[cfg(test)]
#[derive(Debug, Clone, Copy)]
pub(crate) struct RetainedLiteral {
    pub kind: LiteralKind,
    pub source: &'static str,
    pub description: &'static str,
}

/// One declaration read out of a unit: the exact text handed to the
/// registration helper, and the description taken from its doc comment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnitDeclaration {
    /// Which helper registers it.
    pub kind: LiteralKind,
    /// The declared name, as the surface parser read it.
    pub name: SurfaceName,
    /// The declaration text (the parser's span, whitespace-trimmed).
    pub source: String,
    /// The `/-- ... -/` text directly above the declaration.
    pub description: String,
}

/// Where `register_model_unit` takes a unit's declarations from.
#[derive(Debug, Clone, Default)]
pub(crate) enum ModelUnitSource {
    /// The `.clean` files — the ONLY production source.
    #[default]
    CleanFiles,
    /// The retained pre-move literals (`retained_literals.rs`). Oracle only.
    #[cfg(test)]
    RetainedLiterals,
    /// Unit texts supplied by a test (falls back to the `.clean` file for a
    /// unit not in the map). The oracle's mutation arms plant edits this way.
    #[cfg(test)]
    Planted(std::collections::HashMap<ModelUnit, String>),
}

/// Split a unit's text into its declarations, reading each doc comment as the
/// declaration's description. Fail-closed: every declaration must be an
/// `inductive` or a `def` and must carry a `/-- ... -/` doc comment.
///
/// # Errors
///
/// `SpecError::ParseError` naming the unit, the declaration and the fix.
pub(crate) fn declarations_of_source(
    unit_label: &str,
    text: &str,
) -> Result<Vec<UnitDeclaration>, SpecError> {
    let (decls, docs) = Parser::parse_file_with_docs(text).map_err(|e| {
        SpecError::ParseError(format!(
            "model unit {unit_label}: the unit does not parse as a Clean file: {e}"
        ))
    })?;
    // A declaration's text runs from its first token to its last token before
    // the next declaration starts. The surface span is NOT that: measured, the
    // `Inductive` span covers only the `inductive` keyword. Tokens are exact
    // because comments and doc comments are not tokens, so the `--` prose and
    // the next `/-- ... -/` between two declarations never leak into a chunk.
    let tokens = Lexer::tokenize(text);
    let starts: Vec<usize> = decls.iter().map(|d| d.span().start).collect();
    let mut out = Vec::with_capacity(decls.len());
    for (idx, decl) in decls.iter().enumerate() {
        let (kind, name) = match decl {
            SurfaceDecl::Inductive { name, .. } => (LiteralKind::Inductive, name.clone()),
            SurfaceDecl::Def { name, .. } => (LiteralKind::RecursiveDef, name.clone()),
            other => {
                return Err(SpecError::ParseError(format!(
                    "model unit {unit_label}: declaration #{} is a {} — a model unit may hold only \
                     `inductive` and `def` declarations (those are the two forms the literal path \
                     registered). Options: (1) move the declaration back to a Rust `SpecDefinition` \
                     in the registering module; (2) restate it as an `inductive` or a `def`; \
                     (3) extend `register_model_unit` with a new `LiteralKind` AND its oracle arm.",
                    idx + 1,
                    surface_decl_kind_name(other),
                )));
            }
        };
        let start = starts[idx];
        let next_start = starts.get(idx + 1).copied().unwrap_or(text.len());
        let end = tokens
            .iter()
            .filter(|t| t.kind != TokenKind::Eof && t.span.start >= start && t.span.start < next_start)
            .map(|t| t.span.end)
            .max()
            .ok_or_else(|| {
                SpecError::ParseError(format!(
                    "model unit {unit_label}: `{name}` has no tokens between byte {start} and {next_start}"
                ))
            })?;
        let source = text
            .get(start..end)
            .ok_or_else(|| {
                SpecError::ParseError(format!(
                    "model unit {unit_label}: token range {start}..{end} of `{name}` is outside the \
                     unit text ({} bytes)",
                    text.len()
                ))
            })?
            .trim()
            .to_string();
        let span = decl.span();
        let description = docs
            .iter()
            .find(|d| d.span == span)
            .map(|d| d.text.clone())
            .ok_or_else(|| {
                SpecError::ParseError(format!(
                    "model unit {unit_label}: `{name}` has no doc comment. Every model declaration \
                     must carry `/-- <description> -/` directly above it — that text is its \
                     registered description. Fix: add the doc comment (one line; the description \
                     the Rust literal used to pass, if this declaration was moved)."
                ))
            })?;
        out.push(UnitDeclaration {
            kind,
            name,
            source,
            description,
        });
    }
    Ok(out)
}

/// The declarations of a unit as read from its embedded `.clean` text.
///
/// # Errors
///
/// See [`declarations_of_source`].
pub(crate) fn unit_declarations(unit: ModelUnit) -> Result<Vec<UnitDeclaration>, SpecError> {
    declarations_of_source(unit.file_name(), unit.embedded_source())
}

fn surface_decl_kind_name(decl: &SurfaceDecl) -> &'static str {
    match decl {
        SurfaceDecl::Def { .. } => "def",
        SurfaceDecl::Theorem { .. } => "theorem",
        SurfaceDecl::Axiom { .. } => "axiom",
        SurfaceDecl::Opaque { .. } => "opaque",
        SurfaceDecl::Inductive { .. } => "inductive",
        SurfaceDecl::Structure { .. } => "structure",
        SurfaceDecl::Class { .. } => "class",
        SurfaceDecl::Instance { .. } => "instance",
        SurfaceDecl::Example { .. } => "example",
        SurfaceDecl::Namespace { .. } => "namespace",
        SurfaceDecl::Section { .. } => "section",
        SurfaceDecl::Open { .. } => "open",
        SurfaceDecl::Prelude { .. } => "prelude header",
        SurfaceDecl::RawDecl { .. } => "unparsed (parser recovery placeholder)",
        _ => "non-declaration command",
    }
}

impl Specification {
    /// Register every declaration of a model unit, in file order, through the
    /// same `add_inductive` / `add_recursive_def` path the literal used.
    ///
    /// # Errors
    ///
    /// Any parse, elaboration or kernel error of a declaration, prefixed with
    /// the unit and declaration it came from.
    pub(crate) fn register_model_unit(&mut self, unit: ModelUnit) -> Result<(), SpecError> {
        match &self.model_unit_source {
            ModelUnitSource::CleanFiles => {
                let decls = unit_declarations(unit)?;
                self.register_unit_declarations(unit, &decls)
            }
            #[cfg(test)]
            ModelUnitSource::RetainedLiterals => {
                let Some(lits) = retained_literals::of(unit) else {
                    // A unit BORN as a file has no pre-move Rust literal, so there
                    // is nothing for the W1 migration oracle to compare it against.
                    // Registering it from the file on both sides keeps the two
                    // environments identical, so the oracle still says exactly what
                    // it is for -- that the units W1 MOVED elaborate identically --
                    // and says nothing it cannot support about this one.
                    let decls = unit_declarations(unit)?;
                    return self.register_unit_declarations(unit, &decls);
                };
                for lit in lits {
                    self.register_unit_declaration(lit.kind, lit.source, lit.description)?;
                }
                Ok(())
            }
            #[cfg(test)]
            ModelUnitSource::Planted(map) => {
                let decls = match map.get(&unit) {
                    Some(text) => declarations_of_source(unit.file_name(), text)?,
                    None => unit_declarations(unit)?,
                };
                self.register_unit_declarations(unit, &decls)
            }
        }
    }

    fn register_unit_declarations(
        &mut self,
        unit: ModelUnit,
        decls: &[UnitDeclaration],
    ) -> Result<(), SpecError> {
        for decl in decls {
            self.register_unit_declaration(decl.kind, &decl.source, &decl.description)
                .map_err(|e| prefix_unit_error(unit, &decl.name, e))?;
        }
        Ok(())
    }

    fn register_unit_declaration(
        &mut self,
        kind: LiteralKind,
        source: &str,
        description: &str,
    ) -> Result<(), SpecError> {
        match kind {
            LiteralKind::Inductive => self.add_inductive(source, description),
            LiteralKind::RecursiveDef => self.add_recursive_def(source, description),
        }
    }

    /// Choose where model units are read from. Oracle and mutation arms only;
    /// production always reads the `.clean` files.
    #[cfg(test)]
    pub(crate) fn set_model_unit_source(&mut self, source: ModelUnitSource) {
        self.model_unit_source = source;
    }
}

fn prefix_unit_error(unit: ModelUnit, decl_name: &SurfaceName, error: SpecError) -> SpecError {
    let file = unit.file_name();
    match error {
        SpecError::ParseError(m) => SpecError::ParseError(format!("[{file} :: {decl_name}] {m}")),
        SpecError::ElabError(m) => SpecError::ElabError(format!("[{file} :: {decl_name}] {m}")),
        SpecError::TypeError(m) => SpecError::TypeError(format!("[{file} :: {decl_name}] {m}")),
        SpecError::EnvError(m) => SpecError::EnvError(format!("[{file} :: {decl_name}] {m}")),
        other => other,
    }
}
