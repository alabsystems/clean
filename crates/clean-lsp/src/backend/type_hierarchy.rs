// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type hierarchy support (`textDocument/prepareTypeHierarchy`,
//! `typeHierarchy/supertypes`, `typeHierarchy/subtypes`).
//!
//! # Clean type-relationship semantics
//!
//! Clean's LSP retains only a lightweight `Vec<ParsedCommand>` per document
//! (kind, span, name) — the surface AST's `extends` lists and instance class
//! types are not preserved past parsing. The type-relationship graph is
//! therefore reconstructed by re-lexing each declaration's *header* (the token
//! run before the body keyword `where`/`:=`), exactly mirroring how the call
//! hierarchy reconstructs callees from a definition's body extent.
//!
//! The participating nodes are `structure`, `class`, `inductive` and
//! `instance` declarations. Edges (child → parent) are:
//!
//! * **structure / class `extends P1, P2`** — each `Pi` head identifier is a
//!   *supertype* (parent) of the declared type. `extends Ring α` contributes
//!   the parent `Ring` (the applied arguments are not parents).
//! * **`instance [name] : C args`** — the class head `C` is a *supertype* of
//!   the instance; equivalently the instance is a *subtype* (implementor) of
//!   `C`.
//!
//! `supertypes(X)` returns the parents recorded for `X`; `subtypes(X)` returns
//! the reverse edges — every node that names `X` as a parent (structures /
//! classes extending `X`, and instances of class `X`). Only edges whose
//! endpoints are themselves indexed definitions are reported, so the panel
//! never surfaces unresolved names.

use super::{CleanBackend, DefinitionInfo};
use crate::document::CommandKind;
use clean_parser::lexer::{Lexer, TokenKind};
use std::collections::HashSet;
use tower_lsp::lsp_types::*;

impl CleanBackend {
    /// Whether `name` resolves to a declaration that participates in the type
    /// hierarchy: a `structure`, `class`, `inductive` or `instance`.
    pub(crate) fn is_type_hierarchy_node(&self, name: &str) -> bool {
        matches!(
            self.command_kind_for(name),
            Some(
                CommandKind::Structure
                    | CommandKind::Class
                    | CommandKind::Inductive
                    | CommandKind::Instance
            )
        )
    }

    /// Look up the [`CommandKind`] of the (first) parsed command declaring
    /// `name`, searching the document that indexes its definition.
    fn command_kind_for(&self, name: &str) -> Option<CommandKind> {
        let info = self.definitions.get(name)?;
        let doc = self.documents.get(&info.uri)?;
        let parsed = doc.parsed.as_ref()?;
        parsed
            .commands
            .iter()
            .find(|cmd| cmd.name.as_deref() == Some(name))
            .map(|cmd| cmd.kind.clone())
    }

    /// Build a [`TypeHierarchyItem`] from a definition record. Returns `None`
    /// if the owning document is no longer open.
    pub(crate) fn make_type_hierarchy_item(
        &self,
        name: &str,
        info: &DefinitionInfo,
    ) -> Option<TypeHierarchyItem> {
        let doc = self.documents.get(&info.uri)?;
        let kind = self.get_symbol_kind_for_definition(name);
        let range = Range {
            start: doc.offset_to_position(info.start),
            end: doc.offset_to_position(info.end),
        };
        let selection_range = Range {
            start: doc.offset_to_position(info.name_start),
            end: doc.offset_to_position(info.name_end),
        };
        Some(TypeHierarchyItem {
            name: name.to_string(),
            kind,
            tags: None,
            detail: None,
            uri: info.uri.clone(),
            range,
            selection_range,
            data: None,
        })
    }

    /// Supertypes (parents) of `name`: the head identifiers of the types it
    /// `extends` (structure / class) or the class it implements (instance).
    /// Only parents that are themselves indexed definitions are returned, with
    /// duplicates collapsed and a deterministic (sorted) order.
    pub(crate) fn type_supertypes(&self, name: &str) -> Vec<String> {
        let mut parents: Vec<String> = self
            .parents_of(name)
            .into_iter()
            .filter(|p| p != name && self.definitions.contains_key(p))
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        parents.sort();
        parents
    }

    /// Subtypes of `name`: every indexed node that records `name` as a parent
    /// (structures / classes extending `name`, instances of class `name`).
    /// Deterministically ordered with duplicates collapsed.
    pub(crate) fn type_subtypes(&self, name: &str) -> Vec<String> {
        let mut children: Vec<String> = self
            .definitions
            .iter()
            .filter(|entry| entry.key().as_str() != name)
            .filter(|entry| self.parents_of(entry.key()).iter().any(|p| p == name))
            .map(|entry| entry.key().clone())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        children.sort();
        children
    }

    /// Reconstruct the parent type head-identifiers declared by `name` by
    /// re-lexing its declaration header. Returns an empty vector for
    /// definitions that are absent, not a type-relationship node, or have no
    /// parents. The result may contain names that are not themselves indexed;
    /// callers filter as needed.
    fn parents_of(&self, name: &str) -> Vec<String> {
        let Some(info) = self.definitions.get(name) else {
            return Vec::new();
        };
        let Some(kind) = self.command_kind_for(name) else {
            return Vec::new();
        };
        let Some(doc) = self.documents.get(&info.uri) else {
            return Vec::new();
        };
        let text = doc.text();
        let body_end = self
            .next_definition_start(&info.uri, info.start)
            .unwrap_or(text.len());
        if info.start > text.len() || body_end > text.len() || info.start >= body_end {
            return Vec::new();
        }
        let header = &text[info.start..body_end];
        match kind {
            CommandKind::Structure | CommandKind::Class => extends_parents(header),
            CommandKind::Instance => instance_class_head(header).into_iter().collect(),
            // Inductive types are valid hierarchy nodes (they can be referenced
            // as a parent's subtype) but Clean carries no surface supertype
            // relation for them, so they contribute no parents of their own.
            _ => Vec::new(),
        }
    }
}

/// Extract the parent head identifiers from a `structure`/`class` header.
///
/// Scans for an `extends` keyword and collects the *first* identifier of each
/// comma-separated parent type, stopping at the body terminator (`where`,
/// `:=`, or a top-level `:` introducing the result type). For
/// `extends Applicative m, Foo β` this yields `["Applicative", "Foo"]`.
fn extends_parents(header: &str) -> Vec<String> {
    let mut parents = Vec::new();
    let mut tokens = Lexer::tokenize(header).into_iter().peekable();

    // Advance to the `extends` keyword; if absent there are no parents.
    let found_extends = tokens.by_ref().any(|t| t.kind == TokenKind::Extends);
    if !found_extends {
        return parents;
    }

    let mut expect_head = true;
    for token in tokens {
        match token.kind {
            // Body / signature terminators end the extends clause.
            TokenKind::Where | TokenKind::ColonEq | TokenKind::Colon => break,
            // A comma separates parents; the next identifier is a new head.
            TokenKind::Comma => expect_head = true,
            TokenKind::Ident(ref id) if expect_head => {
                parents.push(id.clone());
                expect_head = false;
            }
            // Any other token (applied args, binders, dots) is skipped; it is
            // not a fresh parent head.
            _ => {}
        }
    }
    parents
}

/// Extract the class head identifier instantiated by an `instance` header.
///
/// The class type follows the `:` separator: `instance [name] [binders] : C
/// args where ...`. Returns the first identifier after that colon, which is
/// the head of the class being implemented. Instance binders (`[Add α]`) and
/// any leading instance name precede the colon and are ignored.
fn instance_class_head(header: &str) -> Option<String> {
    let tokens = Lexer::tokenize(header);
    let mut after_colon = false;
    let mut depth: i32 = 0;
    for token in tokens {
        match token.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.saturating_sub(1)
            }
            // The class type is introduced by a top-level `:` (not one nested
            // inside binder brackets such as `[Add α]`).
            TokenKind::Colon if depth == 0 => after_colon = true,
            TokenKind::Where | TokenKind::ColonEq if depth == 0 => break,
            TokenKind::Ident(ref id) if after_colon && depth == 0 => return Some(id.clone()),
            _ => {}
        }
    }
    None
}
