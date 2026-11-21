// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The parser and term-elaborator registration tables in a Lean 4.36.0
//! base artifact. The tables name the declarations that provide grammar and
//! handlers. Their values and bodies have separate import policies.

use std::cell::Cell;
use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::{LeanWorld, Name};

use super::{invalid, Reader, MAX_TOTAL_ARRAY_ITEMS};
use crate::error::OleanResult;
use crate::header::OleanHeader;
use crate::region::{tags, CompactedRegion, TypedModuleLayout};
use crate::world::{lean_worlds, row_of_source_world, HeaderIdentity, WorldState};

#[cfg(test)]
mod tests;

/// Ordered exported records for the parser and term-elaborator extensions.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExportedTermSyntax {
    /// The parser extension's rows in persisted order, including categories
    /// other than `term` and registrations within a named scope.
    pub parser: Vec<ScopedSyntaxEntry<ParserRegistration>>,
    /// The term elaborator attribute's rows in persisted order. Lean adds
    /// later registrations for a kind ahead of its earlier registrations.
    pub term_elaborators: Vec<ScopedSyntaxEntry<TermElaboratorRegistration>>,
}

/// One row of a Lean `ScopedEnvExtension`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScopedSyntaxEntry<T> {
    /// A named scope, or `None` for a global row.
    pub scope: Option<Name>,
    /// The persisted payload.
    pub entry: T,
}

/// The constructors of `Lean.Parser.ParserExtension.OLeanEntry`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParserRegistration {
    /// Register the literal token with the lexer.
    Token(Arc<str>),
    /// Register a syntax node kind.
    Kind(Name),
    /// Declare a parser category.
    Category {
        /// Name of the new category.
        name: Name,
        /// Declaration that registered the category.
        declaration: Name,
        /// How identifier-leading parsers in this category compete.
        leading_ident: LeadingIdentBehavior,
    },
    /// Add a parser to a category. Its declaration can provide a
    /// `ParserDescr`, a trailing descriptor, or a compiled parser.
    Parser {
        /// Parser category, e.g. `term`.
        category: Name,
        /// Declaration supplying the parser.
        declaration: Name,
        /// The registration priority.
        priority: u64,
    },
}

/// Lean's `Parser.LeadingIdentBehavior`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeadingIdentBehavior {
    /// Try identifier parsers.
    Default,
    /// Prefer the literal token's parsers, when present.
    Symbol,
    /// Try both the literal token's and the identifier's parsers.
    Both,
}

/// A syntax kind's entry in `Lean.Elab.Term.termElabAttribute`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermElaboratorRegistration {
    /// The syntax node kind used for dispatch.
    pub kind: Name,
    /// Name of the declaration supplying the elaborator.
    pub declaration: Name,
}

/// Read registrations from the base `.olean` bytes supplied by an importer.
///
/// Use the base part of the same checked capture that supplies the
/// environment. The header identifies the expected format. The importer is
/// responsible for selecting the base part and admitting its provenance.
/// Named scopes and non-term parser categories are kept for the consumer.
///
/// # Errors
///
/// Refuses artifacts outside the registered Lean 4.36.0 build identity,
/// malformed rows, and unrecognized constructors in either table.
pub fn read_exported_term_syntax(bytes: &[u8]) -> OleanResult<ExportedTermSyntax> {
    let header = OleanHeader::parse(bytes)?;
    let stable = LeanWorld::Lean436;
    let identity = HeaderIdentity::of_header(&header);
    let row = row_of_source_world(lean_worlds(), stable);
    if !row.is_some_and(|row| {
        row.state != WorldState::Canary
            && row.identity == identity
            && row.lean_version == Some(stable.version())
            && header.lean_version.as_deref() == row.lean_version
    }) {
        return Err(invalid(format!(
            "parser registrations require registered Lean {} artifacts, found {} ({:?})",
            stable.version(),
            identity.describe(),
            header.lean_version,
        )));
    }

    let region = CompactedRegion::new(bytes, header.base_addr);
    let root = region.root_ptr()?;
    let layout = region.typed_module_layout_at(root)?;
    if layout != TypedModuleLayout::LeanV2 {
        return Err(invalid("parser registrations require v2 ModuleData"));
    }
    let root_offset = region.ptr_to_offset(root)?;
    let reader = Reader {
        region: &region,
        layout,
        legacy: false,
        remaining_items: Cell::new(MAX_TOTAL_ARRAY_ITEMS),
    };
    reader.boolean(root_offset + 48)?;
    let extensions = reader.array(reader.field(root_offset, 4)?)?;
    let parser_name = Name::anon()
        .str("Lean")
        .str("Parser")
        .str("parserExtension");
    let term_elab_name = Name::anon()
        .str("Lean")
        .str("Elab")
        .str("Term")
        .str("termElabAttribute");
    let (mut parser, mut term_elaborators) = (None, None);
    for pointer in extensions {
        let pair = reader.object(pointer, 0, 2, 0)?;
        let name = reader.name(reader.field(pair, 0)?)?;
        let table = reader.field(pair, 1)?;
        if name == parser_name {
            if parser.is_some() {
                return Err(invalid("duplicate Lean.Parser.parserExtension table"));
            }
            parser = Some(read_parser_rows(&reader, table, bytes.len())?);
        } else if name == term_elab_name {
            if term_elaborators.is_some() {
                return Err(invalid("duplicate Lean.Elab.Term.termElabAttribute table"));
            }
            term_elaborators = Some(read_term_elaborator_rows(&reader, table)?);
        }
    }
    Ok(ExportedTermSyntax {
        parser: parser.unwrap_or_default(),
        term_elaborators: term_elaborators.unwrap_or_default(),
    })
}

fn read_parser_rows(
    reader: &Reader<'_, '_>,
    table: u64,
    mut remaining_token_bytes: usize,
) -> OleanResult<Vec<ScopedSyntaxEntry<ParserRegistration>>> {
    let mut tokens = HashMap::<u64, Arc<str>>::new();
    reader
        .array(table)?
        .into_iter()
        .map(|row| {
            let (pointer, scope) = reader.scoped(row)?;
            let offset = reader.region.ptr_to_offset(pointer)?;
            let entry = match reader.region.read_header_at(offset)?.tag {
                0 => {
                    let offset = reader.object(pointer, 0, 1, 0)?;
                    let string = reader.field(offset, 0)?;
                    let token = match tokens.get(&string) {
                        Some(token) => Arc::clone(token),
                        None => {
                            let token = read_token(reader.region, string)?;
                            remaining_token_bytes =
                                remaining_token_bytes.checked_sub(token.len()).ok_or_else(
                                    || invalid("exported parser token byte budget exhausted"),
                                )?;
                            let token = Arc::<str>::from(token);
                            tokens.insert(string, Arc::clone(&token));
                            token
                        }
                    };
                    ParserRegistration::Token(token)
                }
                1 => {
                    let offset = reader.object(pointer, 1, 1, 0)?;
                    ParserRegistration::Kind(reader.name(reader.field(offset, 0)?)?)
                }
                2 => {
                    // Lean stores this three-constructor enumeration as one
                    // scalar byte after the two Name fields.
                    let offset = reader.object(pointer, 2, 2, 1)?;
                    let leading_ident = match reader.region.bytes_at(offset + 24, 1)?[0] {
                        0 => LeadingIdentBehavior::Default,
                        1 => LeadingIdentBehavior::Symbol,
                        2 => LeadingIdentBehavior::Both,
                        _ => return Err(invalid("unknown parser leading identifier behavior")),
                    };
                    ParserRegistration::Category {
                        name: reader.name(reader.field(offset, 0)?)?,
                        declaration: reader.name(reader.field(offset, 1)?)?,
                        leading_ident,
                    }
                }
                3 => {
                    let offset = reader.object(pointer, 3, 3, 0)?;
                    ParserRegistration::Parser {
                        category: reader.name(reader.field(offset, 0)?)?,
                        declaration: reader.name(reader.field(offset, 1)?)?,
                        priority: reader.nat(reader.field(offset, 2)?)?,
                    }
                }
                _ => return Err(invalid("unknown Lean.Parser.parserExtension constructor")),
            };
            Ok(ScopedSyntaxEntry { scope, entry })
        })
        .collect()
}

fn read_token<'a>(region: &CompactedRegion<'a>, pointer: u64) -> OleanResult<&'a str> {
    if pointer == 0 || !pointer.is_multiple_of(8) {
        return Err(invalid("parser token is not a compacted String pointer"));
    }
    let offset = region.ptr_to_offset(pointer)?;
    let header = region.read_header_at(offset)?;
    if (header.rc, header.tag, header.other) != (0, tags::STRING, 0) {
        return Err(invalid("invalid parser token String header"));
    }
    let size = region.read_usize_at(offset + 8, "parser token length")?;
    let capacity = region.read_usize_at(offset + 16, "parser token capacity")?;
    let characters = region.read_usize_at(offset + 24, "parser token character count")?;
    if size < 2 || capacity < size {
        return Err(invalid("invalid parser token length or capacity"));
    }
    let bytes = region.bytes_at(offset + 32, size)?;
    let token = bytes
        .strip_suffix(&[0])
        .ok_or_else(|| invalid("parser token String has no terminator"))?;
    let token =
        std::str::from_utf8(token).map_err(|_| invalid("parser token String is not UTF-8"))?;
    if token.chars().count() != characters {
        return Err(invalid("parser token String character count mismatch"));
    }
    Ok(token)
}

fn read_term_elaborator_rows(
    reader: &Reader<'_, '_>,
    table: u64,
) -> OleanResult<Vec<ScopedSyntaxEntry<TermElaboratorRegistration>>> {
    reader
        .array(table)?
        .into_iter()
        .map(|row| {
            let (pointer, scope) = reader.scoped(row)?;
            let pair = reader.object(pointer, 0, 2, 0)?;
            let kind = reader.name(reader.field(pair, 0)?)?;
            let declaration = reader.name(reader.field(pair, 1)?)?;
            Ok(ScopedSyntaxEntry {
                scope,
                entry: TermElaboratorRegistration { kind, declaration },
            })
        })
        .collect()
}
