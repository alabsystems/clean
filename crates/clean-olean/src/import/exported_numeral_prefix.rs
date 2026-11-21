// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exported term syntax described by a literal followed by a numeral.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use clean_kernel::{Expr, ExprKind, Level, Literal, Name};

use super::convert_expr_direct::{read_and_convert_expr_with_memo, RegionPtrCache};
use super::load_parse::{parse_load_module, LoadConstant, LoadModule};
use super::ExprInternCache;
use crate::lean_ir::exported_term_eval::evaluate_exported_numeral_parser_in_region;
use crate::module::{ConstantKind, DefinitionSafety};
use crate::{
    read_exported_term_syntax, ExportedTermSyntax, OleanError, OleanResult, ParserRegistration,
};

/// A term parser and handler registered globally by the same base artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportedNumeralPrefix {
    /// The syntax node's structural identity.
    pub kind: Name,
    /// Priority in the parser registration table.
    pub priority: u64,
    /// Binding power held by the descriptor's leading node.
    pub precedence: u64,
    /// Exact `ParserDescr.symbol` text, including surrounding ASCII whitespace.
    pub literal: Arc<str>,
    /// The declaration selected by the global term-elaborator attribute.
    pub handler: Name,
}

/// Decode supported numeral prefixes from the base bytes held by the importer.
/// Stable Lean exports some descriptors as kernel stubs with their executable
/// values in the same base part. Other descriptors, categories and scopes
/// remain unhandled.
///
/// # Errors
/// Refuses malformed parts or contradictory registrations for a supported
/// descriptor. The caller must separately establish the artifact's custody.
pub fn read_exported_numeral_prefixes(bytes: &[u8]) -> OleanResult<Vec<ExportedNumeralPrefix>> {
    let registrations = read_exported_term_syntax(bytes)?;
    if registrations.term_elaborators.is_empty() {
        return Ok(Vec::new());
    }
    let base = parse_load_module(bytes.to_vec())?;
    decode_prefixes(&base, &registrations)
}

pub(super) fn loaded_numeral_prefixes(
    base: &LoadModule,
) -> OleanResult<Vec<ExportedNumeralPrefix>> {
    let registrations = read_exported_term_syntax(&base.bytes)?;
    if registrations.term_elaborators.is_empty() {
        return Ok(Vec::new());
    }
    decode_prefixes(base, &registrations)
}

fn decode_prefixes(
    base: &LoadModule,
    registrations: &ExportedTermSyntax,
) -> OleanResult<Vec<ExportedNumeralPrefix>> {
    let term = Name::anon().str("term");
    let parsers: Vec<_> = registrations
        .parser
        .iter()
        .filter_map(|row| match (&row.scope, &row.entry) {
            (
                None,
                ParserRegistration::Parser {
                    category,
                    declaration,
                    priority,
                },
            ) if *category == term => Some((declaration, *priority)),
            _ => None,
        })
        .collect();
    let declarations: HashSet<_> = parsers.iter().map(|(name, _)| *name).collect();
    let constants = index_parser_constants(base, &declarations)?;
    let region = base.region();
    let root = region.root_ptr()?;
    let mut intern = ExprInternCache::default();
    let mut memo = RegionPtrCache::for_region();
    let mut kinds = HashSet::new();
    let mut tokens = HashSet::new();
    let mut prefixes = Vec::new();
    for (declaration, priority) in parsers {
        let Some(constant) = constants.get(declaration) else {
            continue;
        };
        if !matches!(
            constant.kind,
            ConstantKind::Definition | ConstantKind::Axiom
        ) || constant.definition_safety != Some(DefinitionSafety::Safe)
            || !constant.kernel_level_params.is_empty()
            || constant.type_ptr == 0
        {
            continue;
        }
        let mut read = |pointer| {
            read_and_convert_expr_with_memo(
                &region,
                pointer,
                &constant.name,
                &mut intern,
                &mut memo,
            )
            .map(|(expr, _)| expr)
            .map_err(|error| refusal(declaration, error))
        };
        if exact_app::<0>(&read(constant.type_ptr)?, "Lean.ParserDescr", &[]).is_none() {
            continue;
        }
        let descriptor = match (&constant.kind, constant.value_ptr) {
            (ConstantKind::Definition, pointer) if pointer != 0 => {
                kernel_descriptor(&read(pointer)?, declaration)?
            }
            (ConstantKind::Axiom, 0) if base.is_module => {
                evaluate_exported_numeral_parser_in_region(&region, root, declaration)?
            }
            _ => None,
        };
        let Some((kind, precedence, literal)) = descriptor else {
            continue;
        };
        let Some(handler) = global_handler(registrations, &kind)? else {
            continue;
        };
        let token = literal.trim_ascii();
        if !registered_literal_and_kind(registrations, token, &kind) {
            return Err(refusal(declaration, "missing global token or syntax kind"));
        }
        if !kinds.insert(kind.clone()) || !tokens.insert(token.to_owned()) {
            return Err(refusal(
                declaration,
                "competing numeral prefix registrations",
            ));
        }
        prefixes.push(ExportedNumeralPrefix {
            kind,
            priority,
            precedence,
            literal,
            handler: handler.clone(),
        });
    }
    Ok(prefixes)
}

fn kernel_descriptor(
    descriptor: &Expr,
    declaration: &Name,
) -> OleanResult<Option<(Name, u64, Arc<str>)>> {
    let Some((kind, precedence, literal)) = numeral_prefix_shape(descriptor) else {
        return Ok(None);
    };
    Ok(numeral_precedence(precedence, declaration)?
        .map(|precedence| (kind, precedence, Arc::clone(literal))))
}

fn index_parser_constants<'a>(
    base: &'a LoadModule,
    declarations: &HashSet<&Name>,
) -> OleanResult<HashMap<&'a Name, &'a LoadConstant>> {
    let mut constants = HashMap::new();
    for constant in &base.constants {
        let name = &constant.kernel_name;
        if declarations.contains(name) && constants.insert(name, constant).is_some() {
            return Err(refusal(
                name,
                "duplicate base declaration for registered parser",
            ));
        }
    }
    Ok(constants)
}

fn numeral_prefix_shape(expr: &Expr) -> Option<(Name, &Expr, &Arc<str>)> {
    let [node_kind, precedence, parser] = exact_app(expr, "Lean.ParserDescr.node", &[])?;
    let [namespace, kind] = exact_app(node_kind, "Lean.Name.mkStr2", &[])?;
    let kind = Name::anon()
        .str(string_literal(namespace)?)
        .str(string_literal(kind)?);
    let [combinator, symbol, numeral] = exact_app(parser, "Lean.ParserDescr.binary", &[])?;
    let [combinator] = exact_app(combinator, "Lean.Name.mkStr1", &[])?;
    if string_literal(combinator)?.as_ref() != "andthen" {
        return None;
    }
    let [literal] = exact_app(symbol, "Lean.ParserDescr.symbol", &[])?;
    let [numeral] = exact_app(numeral, "Lean.ParserDescr.const", &[])?;
    let [numeral] = exact_app(numeral, "Lean.Name.mkStr1", &[])?;
    let literal = string_literal(literal)?;
    if string_literal(numeral)?.as_ref() != "num" || literal.trim_ascii().is_empty() {
        return None;
    }
    Some((kind, precedence, literal))
}

fn numeral_precedence(expr: &Expr, declaration: &Name) -> OleanResult<Option<u64>> {
    let Some([ty, value, instance]) = exact_app(expr, "OfNat.ofNat", &[Level::zero()]) else {
        return Ok(None);
    };
    let Some([instance_value]) = exact_app(instance, "instOfNatNat", &[]) else {
        return Ok(None);
    };
    let ExprKind::Lit(Literal::Nat(nat)) = value.kind() else {
        return Ok(None);
    };
    if exact_app::<0>(ty, "Nat", &[]).is_none() || value != instance_value {
        return Err(refusal(
            declaration,
            "inconsistent numeral precedence instance",
        ));
    }
    Ok(nat.to_u64())
}

fn global_handler<'a>(
    registrations: &'a ExportedTermSyntax,
    kind: &Name,
) -> OleanResult<Option<&'a Name>> {
    let mut matching = registrations
        .term_elaborators
        .iter()
        .filter(|row| row.entry.kind == *kind);
    let Some(row) = matching.next() else {
        return Ok(None);
    };
    if row.scope.is_some() {
        if matching.any(|other| other.scope.is_none()) {
            return Err(refusal(
                kind,
                "competing global and scoped term elaborators",
            ));
        }
        return Ok(None);
    }
    if matching.next().is_some() {
        return Err(refusal(kind, "competing term elaborators"));
    }
    Ok(Some(&row.entry.declaration))
}

fn registered_literal_and_kind(
    registrations: &ExportedTermSyntax,
    token: &str,
    kind: &Name,
) -> bool {
    let mut globals = registrations
        .parser
        .iter()
        .filter(|row| row.scope.is_none());
    globals.clone().any(|row| {
        matches!(&row.entry, ParserRegistration::Token(registered) if registered.as_ref() == token)
    }) && globals.any(|row| {
        matches!(&row.entry, ParserRegistration::Kind(registered) if registered == kind)
    })
}

fn exact_app<'a, const N: usize>(
    expr: &'a Expr,
    constant: &str,
    levels: &[Level],
) -> Option<[&'a Expr; N]> {
    let mut head = expr;
    let mut args = [expr; N];
    for arg in args.iter_mut().rev() {
        let ExprKind::App(function, argument) = head.kind() else {
            return None;
        };
        head = function;
        *arg = argument;
    }
    matches!(head.kind(), ExprKind::Const(name, actual)
        if *name == Name::from_string(constant) && actual.as_slice() == levels)
    .then_some(args)
}

fn string_literal(expr: &Expr) -> Option<&Arc<str>> {
    match expr.kind() {
        ExprKind::Lit(Literal::String(string)) => Some(string),
        _ => None,
    }
}

fn refusal(declaration: &Name, detail: impl std::fmt::Display) -> OleanError {
    OleanError::Region(format!("exported numeral parser {declaration}: {detail}"))
}

#[cfg(test)]
mod tests;
