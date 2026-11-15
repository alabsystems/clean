// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The declaration records (`axiom`, `def`, `thm`, `opaque`, `quot`,
//! `inductive`), read against the tables into [`ExportDeclaration`]s.

use super::decl::{
    ExportConstructor, ExportDeclaration, ExportHeader, ExportInductiveBlock, ExportInductiveType,
    ExportRecursor, ExportRecursorRule,
};
use std::collections::HashSet;

use clean_kernel::expr::{ExprKind, UsedConstants};
use clean_kernel::name::Name;

use super::error::NdjsonError;
use super::fields::Fields;
use super::json::JsonValue;
use super::levels::LevelTaint;
use super::tables::Tables;
use crate::module::{DefinitionSafety, ParsedQuotKind, ReducibilityHintsData};

/// The first level Lean could tell from the built one (`levels.rs`) that a
/// declaration's stored data mentions: `path` of `member` at expression
/// `index`, unless an earlier path already marked it.
fn note_problem(
    tables: &Tables,
    taint: &mut Option<LevelTaint>,
    index: u64,
    member: &Name,
    path: &'static str,
) {
    if taint.is_none() {
        if let Some(problem) = tables.level_problem(index) {
            *taint = Some(LevelTaint {
                member: tables.shown(member),
                path,
                problem: Some(problem.clone()),
            });
        }
    }
}

/// `name`, `levelParams`, `type`; a level problem in the type marks `taint`.
fn header(
    tables: &Tables,
    line: u64,
    f: &mut Fields,
    taint: &mut Option<LevelTaint>,
) -> Result<ExportHeader, NdjsonError> {
    let (header, type_index) = header_at(tables, line, f)?;
    note_problem(tables, taint, type_index, &header.name, "type");
    Ok(header)
}

/// [`header`], and the expression index of the type.
fn header_at(
    tables: &Tables,
    line: u64,
    f: &mut Fields,
) -> Result<(ExportHeader, u64), NdjsonError> {
    let name = tables.name(line, f.nat("name")?)?;
    let level_params = tables.names_of(line, &f.nat_array("levelParams")?)?;
    let type_index = f.nat("type")?;
    let type_ = (*tables.expr(line, type_index)?).clone();
    Ok((
        ExportHeader {
            name,
            level_params,
            type_,
        },
        type_index,
    ))
}

/// `value`; a level problem in it marks `taint`.
fn value(
    tables: &Tables,
    line: u64,
    f: &mut Fields,
    member: &Name,
    taint: &mut Option<LevelTaint>,
) -> Result<clean_kernel::expr::Expr, NdjsonError> {
    let index = f.nat("value")?;
    note_problem(tables, taint, index, member, "value");
    Ok((*tables.expr(line, index)?).clone())
}

/// The `all` field of a `def`, `thm` or `opaque` record (its mutual block):
/// every index must be bound, as for any name the record carries, but the
/// list itself is not kept. Lean's kernel checks these declarations one by
/// one and never reads it (an inductive's `all` is kept: it names the block).
fn check_all(tables: &Tables, line: u64, f: &mut Fields) -> Result<(), NdjsonError> {
    all(tables, line, f)?;
    Ok(())
}

/// The `all` field: the names of a record's block, every index bound.
fn all(tables: &Tables, line: u64, f: &mut Fields) -> Result<Vec<Name>, NdjsonError> {
    tables.names_of(line, &f.nat_array("all")?)
}

/// One declaration record, `kind` its single key, and the first level its
/// stored data mentions that keeps the export from being accepted (R125).
pub(crate) fn declaration(
    tables: &Tables,
    line: u64,
    kind: &str,
    data: JsonValue,
) -> Result<(ExportDeclaration, Option<LevelTaint>), NdjsonError> {
    let mut taint = None;
    let decl = match kind {
        "axiom" => {
            let mut f = Fields::new(line, "axiom", data)?;
            let header = header(tables, line, &mut f, &mut taint)?;
            let is_unsafe = f.boolean("isUnsafe")?;
            f.finish()?;
            ExportDeclaration::Axiom { header, is_unsafe }
        }
        "def" => {
            let mut f = Fields::new(line, "def", data)?;
            let header = header(tables, line, &mut f, &mut taint)?;
            let value = value(tables, line, &mut f, &header.name, &mut taint)?;
            let hints = match f.take("hints")? {
                JsonValue::String(s) if s == "opaque" => ReducibilityHintsData::Opaque,
                JsonValue::String(s) if s == "abbrev" => ReducibilityHintsData::Abbrev,
                JsonValue::Object(entries) => {
                    let mut regular = Fields::new(line, "def.hints", JsonValue::Object(entries))?;
                    let height = regular.nat_u32("regular")?;
                    regular.finish()?;
                    ReducibilityHintsData::Regular(height)
                }
                other => {
                    return Err(f.error(
                        "hints",
                        format!(
                        "expected \"opaque\", \"abbrev\" or {{\"regular\": n}}, found {other:?}"
                    ),
                    ))
                }
            };
            let safety = match f.string("safety")?.as_str() {
                "safe" => DefinitionSafety::Safe,
                "unsafe" => DefinitionSafety::Unsafe,
                "partial" => DefinitionSafety::Partial,
                other => return Err(f.error("safety", format!("unknown safety {other:?}"))),
            };
            check_all(tables, line, &mut f)?;
            f.finish()?;
            ExportDeclaration::Definition {
                header,
                value,
                hints,
                safety,
            }
        }
        "thm" => {
            let mut f = Fields::new(line, "thm", data)?;
            let header = header(tables, line, &mut f, &mut taint)?;
            let value = value(tables, line, &mut f, &header.name, &mut taint)?;
            check_all(tables, line, &mut f)?;
            f.finish()?;
            ExportDeclaration::Theorem { header, value }
        }
        "opaque" => {
            let mut f = Fields::new(line, "opaque", data)?;
            let header = header(tables, line, &mut f, &mut taint)?;
            let value = value(tables, line, &mut f, &header.name, &mut taint)?;
            // Lean's reader defaults an absent `isUnsafe` to `false`, so the
            // value is checked in the safe context: the stricter reading.
            let is_unsafe = match f.take_opt("isUnsafe") {
                None => false,
                Some(JsonValue::Bool(b)) => b,
                Some(other) => {
                    return Err(f.error(
                        "isUnsafe",
                        format!("expected a boolean, found {}", other.type_name()),
                    ))
                }
            };
            check_all(tables, line, &mut f)?;
            f.finish()?;
            ExportDeclaration::Opaque {
                header,
                value,
                is_unsafe,
            }
        }
        "quot" => {
            let mut f = Fields::new(line, "quot", data)?;
            let header = header(tables, line, &mut f, &mut taint)?;
            let kind = match f.string("kind")?.as_str() {
                "type" => ParsedQuotKind::Type,
                "ctor" => ParsedQuotKind::Mk,
                "lift" => ParsedQuotKind::Lift,
                "ind" => ParsedQuotKind::Ind,
                other => return Err(f.error("kind", format!("unknown quot kind {other:?}"))),
            };
            f.finish()?;
            ExportDeclaration::Quot { header, kind }
        }
        "inductive" => {
            let (block, block_taint) = inductive(tables, line, data)?;
            taint = block_taint;
            ExportDeclaration::Inductive(block)
        }
        other => {
            return Err(NdjsonError::UnknownRecord {
                line,
                keys: vec![other.to_owned()],
            })
        }
    };
    Ok((decl, taint))
}

/// An inductive record, and the first member whose stored data mentions a
/// level Lean could tell from the built one or, failing that, a rewritten
/// level at all: Lean compares the block's constructors and recursors with
/// the ones it generates from the block as written, structurally, so a
/// rewrite on any path keeps the export from being accepted (R125).
fn inductive(
    tables: &Tables,
    line: u64,
    data: JsonValue,
) -> Result<(ExportInductiveBlock, Option<LevelTaint>), NdjsonError> {
    let mut f = Fields::new(line, "inductive", data)?;
    let types = f.array("types")?;
    let ctors = f.array("ctors")?;
    let recs = f.array("recs")?;
    f.finish()?;
    let mut block = ExportInductiveBlock::default();
    let mut problem: Option<LevelTaint> = None;
    let mut rewritten: Option<LevelTaint> = None;
    let mut note = |index: u64, member: &Name, path: &'static str| {
        note_problem(tables, &mut problem, index, member, path);
        if rewritten.is_none() && tables.mentions_rewritten_level(index) {
            rewritten = Some(LevelTaint {
                member: tables.shown(member),
                path,
                problem: None,
            });
        }
    };
    for item in types {
        let mut f = Fields::new(line, "InductiveVal", item)?;
        let (header, type_index) = header_at(tables, line, &mut f)?;
        note(type_index, &header.name, "inductive type's type");
        block.types.push(ExportInductiveType {
            header,
            num_params: f.nat_u32("numParams")?,
            num_indices: f.nat_u32("numIndices")?,
            all: all(tables, line, &mut f)?,
            ctors: tables.names_of(line, &f.nat_array("ctors")?)?,
            num_nested: f.nat_u32("numNested")?,
            is_rec: f.boolean("isRec")?,
            is_unsafe: f.boolean("isUnsafe")?,
            is_reflexive: f.boolean("isReflexive")?,
        });
        f.finish()?;
    }
    for item in ctors {
        let mut f = Fields::new(line, "ConstructorVal", item)?;
        let (header, type_index) = header_at(tables, line, &mut f)?;
        note(type_index, &header.name, "constructor type");
        block.ctors.push(ExportConstructor {
            header,
            induct: tables.name(line, f.nat("induct")?)?,
            cidx: f.nat_u32("cidx")?,
            num_params: f.nat_u32("numParams")?,
            num_fields: f.nat_u32("numFields")?,
            is_unsafe: f.boolean("isUnsafe")?,
        });
        f.finish()?;
    }
    for item in recs {
        let mut f = Fields::new(line, "RecursorVal", item)?;
        let (header, type_index) = header_at(tables, line, &mut f)?;
        note(type_index, &header.name, "recursor type");
        let all = all(tables, line, &mut f)?;
        let num_params = f.nat_u32("numParams")?;
        let num_indices = f.nat_u32("numIndices")?;
        let num_motives = f.nat_u32("numMotives")?;
        let num_minors = f.nat_u32("numMinors")?;
        let mut rules = Vec::new();
        for rule in f.array("rules")? {
            let mut r = Fields::new(line, "RecursorRule", rule)?;
            let ctor = tables.name(line, r.nat("ctor")?)?;
            let nfields = r.nat_u32("nfields")?;
            let rhs_index = r.nat("rhs")?;
            note(rhs_index, &header.name, "recursor rule's right-hand side");
            rules.push(ExportRecursorRule {
                ctor,
                nfields,
                rhs: (*tables.expr(line, rhs_index)?).clone(),
            });
            r.finish()?;
        }
        let k = f.boolean("k")?;
        let is_unsafe = f.boolean("isUnsafe")?;
        f.finish()?;
        block.recs.push(ExportRecursor {
            header,
            all,
            num_params,
            num_indices,
            num_motives,
            num_minors,
            rules,
            k,
            is_unsafe,
        });
    }
    check_block_shape(line, &block)?;
    check_block_flags(line, &block)?;
    Ok((block, problem.or(rewritten)))
}

fn rendered(names: &[Name]) -> String {
    let parts: Vec<String> = names.iter().map(Name::to_unambiguous_string).collect();
    format!("[{}]", parts.join(", "))
}

/// The record is one block, as lean4export writes it: every type's and every
/// recursor's `all` is the record's `types`, in order (Lean's replay builds
/// the block from `all`); every constructor's `induct` is the type whose
/// `ctors` list names it; and the types' `ctors` lists, in order, are the
/// record's `ctors`.
fn check_block_shape(line: u64, block: &ExportInductiveBlock) -> Result<(), NdjsonError> {
    let shape = |problem: String| Err(NdjsonError::InductiveBlockShape { line, problem });
    let types: Vec<Name> = block.types.iter().map(|t| t.header.name.clone()).collect();
    for t in &block.types {
        if t.all != types {
            return shape(format!(
                "type {}'s `all` is {}, not the record's types {}",
                t.header.name.to_unambiguous_string(),
                rendered(&t.all),
                rendered(&types)
            ));
        }
    }
    for r in &block.recs {
        if r.all != types {
            return shape(format!(
                "recursor {}'s `all` is {}, not the record's types {}",
                r.header.name.to_unambiguous_string(),
                rendered(&r.all),
                rendered(&types)
            ));
        }
    }
    let listed: Vec<(&Name, &Name)> = block
        .types
        .iter()
        .flat_map(|t| t.ctors.iter().map(move |c| (c, &t.header.name)))
        .collect();
    let stated: Vec<(&Name, &Name)> = block
        .ctors
        .iter()
        .map(|c| (&c.header.name, &c.induct))
        .collect();
    if listed != stated {
        return shape(format!(
            "the types' `ctors` lists, with their owners, are {:?}, but the record's \
             constructors and their `induct` are {:?}",
            listed
                .iter()
                .map(|(c, t)| format!(
                    "{} of {}",
                    c.to_unambiguous_string(),
                    t.to_unambiguous_string()
                ))
                .collect::<Vec<_>>(),
            stated
                .iter()
                .map(|(c, t)| format!(
                    "{} of {}",
                    c.to_unambiguous_string(),
                    t.to_unambiguous_string()
                ))
                .collect::<Vec<_>>()
        ));
    }
    Ok(())
}

/// Lean's kernel computes `isRec` and `isReflexive` per BLOCK
/// (`inductive.cpp`, `is_rec`/`is_reflexive`): recursive when some binder
/// domain of some constructor names a type of the block (a constant, not a
/// projection's structure name), reflexive when such a domain is itself a
/// function type. For a NESTED block (a domain whose head is not a type of
/// the block names one in its arguments: `List (Nat → T)`, `HBox T`) Lean
/// computes both over the auxiliary types nested elimination builds, whose
/// constructors the record does not carry: `isRec` is the same, but
/// `isReflexive` may be `true` with no function-typed domain here (the
/// auxiliary `List`'s `cons` takes `Nat → T`). For such a block the reader
/// refuses only a stored `false` beside a function-typed domain, and the
/// replay compares the stored flag with the kernel's, which regenerates the
/// auxiliary types (R112). Clean's kernel reads the stored `isRec`
/// (structure eta), so a lying one is refused here.
fn check_block_flags(line: u64, block: &ExportInductiveBlock) -> Result<(), NdjsonError> {
    let types: HashSet<&Name> = block.types.iter().map(|t| &t.header.name).collect();
    let mentions_block = |e: &clean_kernel::expr::Expr| {
        let mut used = HashSet::new();
        e.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
        used.iter().any(|n| types.contains(n))
    };
    let mut is_rec = false;
    let mut is_reflexive = false;
    let mut nested = false;
    for c in &block.ctors {
        let mut t = &c.header.type_;
        while let ExprKind::Pi(_, domain, body) = t.kind() {
            if mentions_block(domain.as_ref()) {
                is_rec = true;
                if matches!(domain.kind(), ExprKind::Pi(..)) {
                    is_reflexive = true;
                }
                // The domain's codomain, past its own binders: an occurrence
                // is nested unless its head is a type of the block.
                let mut codomain = domain.as_ref();
                while let ExprKind::Pi(_, _, inner) = codomain.kind() {
                    codomain = inner.as_ref();
                }
                let mut head = codomain;
                while let ExprKind::App(f, _) = head.kind() {
                    head = f.as_ref();
                }
                if !matches!(head.kind(), ExprKind::Const(n, _) if types.contains(n)) {
                    nested = true;
                }
            }
            t = body.as_ref();
        }
    }
    for t in &block.types {
        for (flag, stored, kernel) in [
            ("isRec", t.is_rec, is_rec),
            ("isReflexive", t.is_reflexive, is_reflexive),
        ] {
            let refused = if nested && flag == "isReflexive" {
                kernel && !stored
            } else {
                stored != kernel
            };
            if refused {
                return Err(NdjsonError::InductiveFlagMismatch {
                    line,
                    name: t.header.name.to_unambiguous_string(),
                    flag,
                    stored,
                    kernel,
                });
            }
        }
    }
    Ok(())
}
