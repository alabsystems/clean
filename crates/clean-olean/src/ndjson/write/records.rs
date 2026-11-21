// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The declaration records (`axiom`, `def`, `thm`, `opaque`, `quot`,
//! `inductive`), written from the [`ExportDeclaration`]s the reader yields.
//!
//! Each record is the inverse of its reading in `super::super::records`: the
//! same fields, under the same names, every one written. The one field with
//! no source is the `all` of a `def`, `thm` or `opaque` record (its mutual
//! block): neither the reader's declarations nor the kernel's keep it, and
//! Lean's kernel checks these declarations one by one and never reads it, so
//! it is written as the declaration alone.

use std::io::Write;

use clean_kernel::name::Name;

use super::error::ExportWriteError;
use super::json::Json;
use super::tables::{Emitter, Scope};
use crate::module::{DefinitionSafety, ParsedQuotKind, ReducibilityHintsData};
use crate::ndjson::decl::{ExportDeclaration, ExportHeader, ExportInductiveBlock};

type Fields = Vec<(&'static str, Json)>;

/// `name`, `levelParams`, `type`.
fn header<W: Write>(
    emitter: &mut Emitter<W>,
    scope: &Scope<'_>,
    header: &ExportHeader,
) -> Result<Fields, ExportWriteError> {
    let name = emitter.name(&header.name)?;
    let level_params = emitter.names(&header.level_params)?;
    let type_ = emitter.expr(scope, &header.type_)?;
    Ok(vec![
        ("name", Json::Nat(name)),
        ("levelParams", Json::nats(&level_params)),
        ("type", Json::Nat(type_)),
    ])
}

/// Write `decl`: the records of everything it mentions, then its own.
pub(super) fn write_declaration<W: Write>(
    emitter: &mut Emitter<W>,
    decl: &ExportDeclaration,
) -> Result<(), ExportWriteError> {
    let members: Vec<Name> = decl.declared_names().into_iter().cloned().collect();
    let label = members
        .first()
        .map(Name::to_unambiguous_string)
        .unwrap_or_default();
    let scope = Scope {
        label: &label,
        members: &members,
    };
    let (kind, fields) = match decl {
        ExportDeclaration::Axiom {
            header: h,
            is_unsafe,
        } => {
            let mut fields = header(emitter, &scope, h)?;
            fields.push(("isUnsafe", Json::Bool(*is_unsafe)));
            ("axiom", fields)
        }
        ExportDeclaration::Definition {
            header: h,
            value,
            hints,
            safety,
            all,
        } => {
            let mut fields = header(emitter, &scope, h)?;
            fields.push(("value", Json::Nat(emitter.expr(&scope, value)?)));
            fields.push((
                "hints",
                match hints {
                    ReducibilityHintsData::Opaque => Json::Str("opaque".to_owned()),
                    ReducibilityHintsData::Abbrev => Json::Str("abbrev".to_owned()),
                    ReducibilityHintsData::Regular(height) => {
                        Json::Object(vec![("regular", Json::Nat(u64::from(*height)))])
                    }
                },
            ));
            let safety = match safety {
                DefinitionSafety::Safe => "safe",
                DefinitionSafety::Unsafe => "unsafe",
                DefinitionSafety::Partial => "partial",
            };
            fields.push(("safety", Json::Str(safety.to_owned())));
            fields.push(("all", Json::nats(&emitter.names(all)?)));
            ("def", fields)
        }
        ExportDeclaration::Theorem {
            header: h,
            value,
            all,
        } => {
            let mut fields = header(emitter, &scope, h)?;
            fields.push(("value", Json::Nat(emitter.expr(&scope, value)?)));
            fields.push(("all", Json::nats(&emitter.names(all)?)));
            ("thm", fields)
        }
        ExportDeclaration::Opaque {
            header: h,
            value,
            is_unsafe,
            all,
        } => {
            let mut fields = header(emitter, &scope, h)?;
            fields.push(("value", Json::Nat(emitter.expr(&scope, value)?)));
            fields.push(("isUnsafe", Json::Bool(*is_unsafe)));
            fields.push(("all", Json::nats(&emitter.names(all)?)));
            ("opaque", fields)
        }
        ExportDeclaration::Quot { header: h, kind } => {
            let mut fields = header(emitter, &scope, h)?;
            let kind = match kind {
                ParsedQuotKind::Type => "type",
                ParsedQuotKind::Mk => "ctor",
                ParsedQuotKind::Lift => "lift",
                ParsedQuotKind::Ind => "ind",
                ParsedQuotKind::Sound => {
                    return Err(ExportWriteError::Unexportable {
                        declaration: label.clone(),
                        what: "a `quot` record of kind `sound`: Lean declares `Quot.sound` as an \
                               axiom, and the format has no such kind"
                            .to_owned(),
                    })
                }
            };
            fields.push(("kind", Json::Str(kind.to_owned())));
            ("quot", fields)
        }
        ExportDeclaration::Inductive(block) => ("inductive", inductive(emitter, &scope, block)?),
    };
    emitter.record(&Json::Object(vec![(kind, Json::Object(fields))]))?;
    emitter.declare(&members)
}

/// An `inductive` record's three arrays.
fn inductive<W: Write>(
    emitter: &mut Emitter<W>,
    scope: &Scope<'_>,
    block: &ExportInductiveBlock,
) -> Result<Fields, ExportWriteError> {
    let mut types = Vec::with_capacity(block.types.len());
    for t in &block.types {
        let mut fields = header(emitter, scope, &t.header)?;
        fields.extend([
            ("numParams", Json::Nat(u64::from(t.num_params))),
            ("numIndices", Json::Nat(u64::from(t.num_indices))),
            ("all", Json::nats(&emitter.names(&t.all)?)),
            ("ctors", Json::nats(&emitter.names(&t.ctors)?)),
            ("numNested", Json::Nat(u64::from(t.num_nested))),
            ("isRec", Json::Bool(t.is_rec)),
            ("isUnsafe", Json::Bool(t.is_unsafe)),
            ("isReflexive", Json::Bool(t.is_reflexive)),
        ]);
        types.push(Json::Object(fields));
    }
    let mut ctors = Vec::with_capacity(block.ctors.len());
    for c in &block.ctors {
        let mut fields = header(emitter, scope, &c.header)?;
        fields.extend([
            ("induct", Json::Nat(emitter.name(&c.induct)?)),
            ("cidx", Json::Nat(u64::from(c.cidx))),
            ("numParams", Json::Nat(u64::from(c.num_params))),
            ("numFields", Json::Nat(u64::from(c.num_fields))),
            ("isUnsafe", Json::Bool(c.is_unsafe)),
        ]);
        ctors.push(Json::Object(fields));
    }
    let mut recs = Vec::with_capacity(block.recs.len());
    for r in &block.recs {
        let mut fields = header(emitter, scope, &r.header)?;
        let all = emitter.names(&r.all)?;
        let mut rules = Vec::with_capacity(r.rules.len());
        for rule in &r.rules {
            rules.push(Json::Object(vec![
                ("ctor", Json::Nat(emitter.name(&rule.ctor)?)),
                ("nfields", Json::Nat(u64::from(rule.nfields))),
                ("rhs", Json::Nat(emitter.expr(scope, &rule.rhs)?)),
            ]));
        }
        fields.extend([
            ("all", Json::nats(&all)),
            ("numParams", Json::Nat(u64::from(r.num_params))),
            ("numIndices", Json::Nat(u64::from(r.num_indices))),
            ("numMotives", Json::Nat(u64::from(r.num_motives))),
            ("numMinors", Json::Nat(u64::from(r.num_minors))),
            ("rules", Json::Array(rules)),
            ("k", Json::Bool(r.k)),
            ("isUnsafe", Json::Bool(r.is_unsafe)),
        ]);
        recs.push(Json::Object(fields));
    }
    Ok(vec![
        ("types", Json::Array(types)),
        ("ctors", Json::Array(ctors)),
        ("recs", Json::Array(recs)),
    ])
}
