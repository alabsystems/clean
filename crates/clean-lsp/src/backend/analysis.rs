// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AST traversal helpers — identifier collection and location tracking.
//!
//! Warning detection (sorry, deprecated, unused variables) lives in `super::warnings`.

use std::collections::HashSet;

/// Parse text into a ParsedDocument (test-only)
#[cfg(test)]
#[must_use]
pub(crate) fn parse_lean_text(text: &str) -> crate::document::ParsedDocument {
    use super::CleanBackend;
    use crate::document::{ParseError, ParsedCommand, ParsedDocument};
    match clean_parser::parse_file_with_diagnostics(text) {
        Ok(report) => {
            let mut commands = Vec::new();

            for decl in &report.decls {
                let (kind, name, span) = CleanBackend::classify_decl(decl);
                let content_hash = CleanBackend::compute_content_hash(text, span.0, span.1);
                commands.push(ParsedCommand {
                    kind,
                    start: span.0,
                    end: span.1,
                    name,
                    content_hash,
                });
            }

            let errors = report
                .diagnostics
                .into_iter()
                .map(|diag| ParseError {
                    start: diag.recovery_start.byte,
                    end: diag.recovered_at.byte.max(diag.recovery_start.byte + 1),
                    message: diag.message,
                    related: Vec::new(),
                })
                .collect();

            ParsedDocument { errors, commands }
        }
        Err(e) => {
            let message = format!("{e}");
            ParsedDocument {
                errors: vec![ParseError {
                    start: 0,
                    end: 1,
                    message,
                    related: Vec::new(),
                }],
                commands: vec![],
            }
        }
    }
}

/// Collect all identifiers used in a surface expression
pub(crate) fn collect_used_idents(expr: &clean_parser::SurfaceExpr, used: &mut HashSet<String>) {
    use clean_parser::SurfaceExpr;

    match expr {
        SurfaceExpr::Ident(_, name) => {
            // Split qualified names and add the first component
            // e.g., "Nat.add" -> we care about "Nat", not local variable references
            let first_part = name.split('.').next().unwrap_or(name);
            used.insert(first_part.to_string());
        }
        SurfaceExpr::App(_, func, args) => {
            collect_used_idents(func, used);
            for arg in args {
                collect_used_idents(&arg.expr, used);
            }
        }
        SurfaceExpr::Lambda(_, binders, body)
        | SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            // Collect from binder types
            for binder in binders {
                if let Some(ty) = &binder.ty {
                    collect_used_idents(ty, used);
                }
                if let Some(default) = &binder.default {
                    collect_used_idents(default, used);
                }
            }
            collect_used_idents(body, used);
        }
        SurfaceExpr::Pi(_, binders, body) => {
            for binder in binders {
                if let Some(ty) = &binder.ty {
                    collect_used_idents(ty, used);
                }
                if let Some(default) = &binder.default {
                    collect_used_idents(default, used);
                }
            }
            collect_used_idents(body, used);
        }
        SurfaceExpr::Arrow(_, left, right) => {
            collect_used_idents(left, used);
            collect_used_idents(right, used);
        }
        SurfaceExpr::Let(_, binder, val, body) | SurfaceExpr::LetRec(_, binder, val, body) => {
            if let Some(ty) = &binder.ty {
                collect_used_idents(ty, used);
            }
            collect_used_idents(val, used);
            collect_used_idents(body, used);
        }
        SurfaceExpr::If(_, cond, then_branch, else_branch) => {
            collect_used_idents(cond, used);
            collect_used_idents(then_branch, used);
            collect_used_idents(else_branch, used);
        }
        SurfaceExpr::IfLet(_, _pat, scrutinee, then_branch, else_branch) => {
            collect_used_idents(scrutinee, used);
            collect_used_idents(then_branch, used);
            collect_used_idents(else_branch, used);
        }
        SurfaceExpr::IfDecidable(_, _, prop, then_branch, else_branch) => {
            collect_used_idents(prop, used);
            collect_used_idents(then_branch, used);
            collect_used_idents(else_branch, used);
        }
        SurfaceExpr::Match(_, _, scrutinee, arms) => {
            collect_used_idents(scrutinee, used);
            for arm in arms {
                collect_used_idents(&arm.body, used);
            }
        }
        SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::OutParam(_, inner)
        | SurfaceExpr::SemiOutParam(_, inner)
        | SurfaceExpr::Explicit(_, inner) => collect_used_idents(inner, used),
        SurfaceExpr::Ascription(_, expr, ty) => {
            collect_used_idents(expr, used);
            collect_used_idents(ty, used);
        }
        SurfaceExpr::Proj(_, expr, _)
        | SurfaceExpr::UniverseInst(_, expr, _)
        | SurfaceExpr::NamedArg(_, _, expr) => collect_used_idents(expr, used),
        // Qq quotations: recurse into inner expressions
        SurfaceExpr::QQuotation {
            inner, type_annot, ..
        } => {
            collect_used_idents(inner, used);
            if let Some(ty) = type_annot {
                collect_used_idents(ty, used);
            }
        }
        SurfaceExpr::QAntiquot { content, .. } => {
            use clean_parser::QAntiquotContent;
            match content {
                QAntiquotContent::Simple(name) => {
                    used.insert(name.clone());
                }
                QAntiquotContent::Expr(e) => {
                    collect_used_idents(e, used);
                }
                QAntiquotContent::Typed { name, ty } => {
                    used.insert(name.clone());
                    collect_used_idents(ty, used);
                }
                QAntiquotContent::Splice { name, .. } => {
                    used.insert(name.clone());
                }
            }
        }
        // Let-pattern: let q($pat) := scrutinee | fallback in body
        // Part of #23: Qq Phase 4 - let-pattern support
        SurfaceExpr::LetPattern(_, _pattern, scrutinee, fallback, body) => {
            collect_used_idents(scrutinee, used);
            collect_used_idents(fallback, used);
            collect_used_idents(body, used);
        }
        // Structure literal: { x := val, y := val2 }
        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            if let Some(ty) = struct_type {
                collect_used_idents(ty, used);
            }
            if let Some(b) = base {
                collect_used_idents(b, used);
            }
            for field in fields {
                collect_used_idents(&field.val, used);
            }
        }
        // Do notation: recurse into do-element sub-expressions
        SurfaceExpr::Do(_, elems) => {
            for elem in elems {
                collect_used_idents_do_elem(elem, used);
            }
        }
        // Nested action lift: recurse into inner expression
        SurfaceExpr::LiftMethod(_, inner) => collect_used_idents(inner, used),
        // Interpolated strings: recurse into expression parts
        SurfaceExpr::InterpolatedStr { parts, .. } => {
            for part in parts {
                if let clean_parser::InterpolationPart::Expr(inner) = part {
                    collect_used_idents(inner, used);
                }
            }
        }
        // ByTactic: tactics are opaque for identifier collection
        SurfaceExpr::ByTactic(_, _) => {}
        // CalcBlock: recurse into relation expressions and term justifications
        SurfaceExpr::CalcBlock(_, steps) => {
            for step in steps {
                collect_used_idents(&step.rel, used);
                if let clean_parser::SurfaceCalcJustification::Term(proof) = &step.proof {
                    collect_used_idents(proof, used);
                }
            }
        }
        // `open X in <term>`: the opened namespace heads are "used" (they gate
        // the sub-term's name resolution); recurse into the sub-term too.
        SurfaceExpr::OpenIn { paths, body, .. } => {
            for path in paths {
                if let Some(head) = path.path.first() {
                    used.insert(head.clone());
                }
            }
            collect_used_idents(body, used);
        }
        // Terminal expressions with no nested identifiers
        SurfaceExpr::Universe(_, _)
        | SurfaceExpr::Lit(_, _)
        | SurfaceExpr::Hole(_)
        | SurfaceExpr::NamedHole(_, _)
        | SurfaceExpr::SyntheticSorry(_)
        | SurfaceExpr::SyntaxQuote(_, _) => {}
    }
}

/// Recurse into a do-element to collect used identifiers
fn collect_used_idents_do_elem(elem: &clean_parser::DoElem, used: &mut HashSet<String>) {
    use clean_parser::DoElem;
    match elem {
        DoElem::Bind(_, _, action) | DoElem::Let(_, _, action) | DoElem::LetMut(_, _, action) => {
            collect_used_idents(action, used);
        }
        DoElem::LetRec(_, bindings) => {
            for (_, val) in bindings {
                collect_used_idents(val, used);
            }
        }
        DoElem::Return(_, expr) | DoElem::Expr(_, expr) => {
            collect_used_idents(expr, used);
        }
        DoElem::If(_, cond, then_branch, else_branch) => {
            collect_used_idents(cond, used);
            for elem in then_branch {
                collect_used_idents_do_elem(elem, used);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_used_idents_do_elem(elem, used);
                }
            }
        }
        DoElem::IfLet(_, _, scrutinee, then_branch, else_branch) => {
            collect_used_idents(scrutinee, used);
            for elem in then_branch {
                collect_used_idents_do_elem(elem, used);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_used_idents_do_elem(elem, used);
                }
            }
        }
        DoElem::IfDecidable(_, _, prop, then_branch, else_branch) => {
            collect_used_idents(prop, used);
            for elem in then_branch {
                collect_used_idents_do_elem(elem, used);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_used_idents_do_elem(elem, used);
                }
            }
        }
        DoElem::For(_, _, collection, body) => {
            collect_used_idents(collection, used);
            for elem in body {
                collect_used_idents_do_elem(elem, used);
            }
        }
        DoElem::Match(_, discrs, arms) => {
            for d in discrs {
                collect_used_idents(d, used);
            }
            for arm in arms {
                for elem in &arm.body {
                    collect_used_idents_do_elem(elem, used);
                }
            }
        }
        DoElem::TryCatch(_, try_body, catches, finally_body) => {
            for elem in try_body {
                collect_used_idents_do_elem(elem, used);
            }
            for catch in catches {
                if let Some(exc_ty) = &catch.exc_type {
                    collect_used_idents(exc_ty, used);
                }
                for elem in &catch.body {
                    collect_used_idents_do_elem(elem, used);
                }
            }
            if let Some(fin_elems) = finally_body {
                for elem in fin_elems {
                    collect_used_idents_do_elem(elem, used);
                }
            }
        }
        DoElem::LetElse(_, _, action, fallback) => {
            collect_used_idents(action, used);
            for elem in fallback {
                collect_used_idents_do_elem(elem, used);
            }
        }
        DoElem::LetExpr(_, _, val, _, fallback) => {
            collect_used_idents(val, used);
            for elem in fallback {
                collect_used_idents_do_elem(elem, used);
            }
        }
        DoElem::Repeat(_, body) => {
            for elem in body {
                collect_used_idents_do_elem(elem, used);
            }
        }
        DoElem::While(_, cond, body) => {
            collect_used_idents(cond, used);
            for elem in body {
                collect_used_idents_do_elem(elem, used);
            }
        }
        DoElem::DbgTrace(_, msg) => {
            collect_used_idents(msg, used);
        }
        DoElem::Break(_) | DoElem::Continue(_) => {}
        DoElem::Reassign(_, name, val) => {
            used.insert(name.clone());
            collect_used_idents(val, used);
        }
        DoElem::PatternReassign(_, pat, val) => {
            let mut names = Vec::new();
            pat.collect_var_names(&mut names);
            for name in names {
                used.insert(name);
            }
            collect_used_idents(val, used);
        }
    }
}

/// Location of an identifier in source
pub(crate) struct IdentLocation {
    pub(crate) name: String,
    pub(crate) start: usize,
    pub(crate) end: usize,
}

/// Collect all identifier occurrences (with spans) in an expression
pub(crate) fn collect_ident_locations(
    expr: &clean_parser::SurfaceExpr,
    locations: &mut Vec<IdentLocation>,
) {
    use clean_parser::SurfaceExpr;

    match expr {
        SurfaceExpr::Ident(span, name) => locations.push(IdentLocation {
            name: name.clone(),
            start: span.start,
            end: span.end,
        }),
        SurfaceExpr::App(_, func, args) => {
            collect_ident_locations(func, locations);
            for arg in args {
                collect_ident_locations(&arg.expr, locations);
            }
        }
        SurfaceExpr::Lambda(_, binders, body)
        | SurfaceExpr::PatternMatchLambda(_, binders, body)
        | SurfaceExpr::Pi(_, binders, body) => {
            collect_locations_from_binders(binders, locations);
            collect_ident_locations(body, locations);
        }
        SurfaceExpr::Arrow(_, left, right) => {
            collect_ident_locations(left, locations);
            collect_ident_locations(right, locations);
        }
        SurfaceExpr::Let(_, binder, val, body) | SurfaceExpr::LetRec(_, binder, val, body) => {
            collect_locations_from_binders(std::slice::from_ref(binder), locations);
            collect_ident_locations(val, locations);
            collect_ident_locations(body, locations);
        }
        SurfaceExpr::If(_, cond, then_branch, else_branch) => {
            collect_ident_locations(cond, locations);
            collect_ident_locations(then_branch, locations);
            collect_ident_locations(else_branch, locations);
        }
        SurfaceExpr::IfLet(_, _pat, scrutinee, then_branch, else_branch) => {
            collect_ident_locations(scrutinee, locations);
            collect_ident_locations(then_branch, locations);
            collect_ident_locations(else_branch, locations);
        }
        SurfaceExpr::IfDecidable(_, _, prop, then_branch, else_branch) => {
            collect_ident_locations(prop, locations);
            collect_ident_locations(then_branch, locations);
            collect_ident_locations(else_branch, locations);
        }
        SurfaceExpr::Match(_, _, scrutinee, arms) => {
            collect_ident_locations(scrutinee, locations);
            for arm in arms {
                collect_ident_locations(&arm.body, locations);
            }
        }
        // Single inner expression to recurse into
        SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::OutParam(_, inner)
        | SurfaceExpr::SemiOutParam(_, inner)
        | SurfaceExpr::Explicit(_, inner) => collect_ident_locations(inner, locations),
        SurfaceExpr::Ascription(_, expr, ty) => {
            collect_ident_locations(expr, locations);
            collect_ident_locations(ty, locations);
        }
        SurfaceExpr::Proj(_, expr, _)
        | SurfaceExpr::UniverseInst(_, expr, _)
        | SurfaceExpr::NamedArg(_, _, expr) => collect_ident_locations(expr, locations),
        // Qq quotations: recurse into inner expressions
        SurfaceExpr::QQuotation {
            inner, type_annot, ..
        } => {
            collect_ident_locations(inner, locations);
            if let Some(ty) = type_annot {
                collect_ident_locations(ty, locations);
            }
        }
        SurfaceExpr::QAntiquot { span, content } => {
            use clean_parser::QAntiquotContent;
            match content {
                QAntiquotContent::Simple(name) => {
                    locations.push(IdentLocation {
                        name: name.clone(),
                        start: span.start,
                        end: span.end,
                    });
                }
                QAntiquotContent::Expr(e) => {
                    collect_ident_locations(e, locations);
                }
                QAntiquotContent::Typed { name, ty } => {
                    locations.push(IdentLocation {
                        name: name.clone(),
                        start: span.start,
                        end: span.end,
                    });
                    collect_ident_locations(ty, locations);
                }
                QAntiquotContent::Splice { name, .. } => {
                    locations.push(IdentLocation {
                        name: name.clone(),
                        start: span.start,
                        end: span.end,
                    });
                }
            }
        }
        // Let-pattern: let q($pat) := scrutinee | fallback in body
        // Part of #23: Qq Phase 4 - let-pattern support
        SurfaceExpr::LetPattern(_, _pattern, scrutinee, fallback, body) => {
            collect_ident_locations(scrutinee, locations);
            collect_ident_locations(fallback, locations);
            collect_ident_locations(body, locations);
        }
        // Structure literal: { x := val, y := val2 }
        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            if let Some(ty) = struct_type {
                collect_ident_locations(ty, locations);
            }
            if let Some(b) = base {
                collect_ident_locations(b, locations);
            }
            for field in fields {
                collect_ident_locations(&field.val, locations);
            }
        }
        // Do notation: recurse into do-element sub-expressions
        SurfaceExpr::Do(_, elems) => {
            for elem in elems {
                collect_ident_locations_do_elem(elem, locations);
            }
        }
        // Nested action lift: recurse into inner expression
        SurfaceExpr::LiftMethod(_, inner) => collect_ident_locations(inner, locations),
        // Interpolated strings: recurse into expression parts
        SurfaceExpr::InterpolatedStr { parts, .. } => {
            for part in parts {
                if let clean_parser::InterpolationPart::Expr(inner) = part {
                    collect_ident_locations(inner, locations);
                }
            }
        }
        // ByTactic: tactics are opaque for identifier location collection
        SurfaceExpr::ByTactic(_, _) => {}
        // CalcBlock: recurse into relation expressions and term justifications
        SurfaceExpr::CalcBlock(_, steps) => {
            for step in steps {
                collect_ident_locations(&step.rel, locations);
                if let clean_parser::SurfaceCalcJustification::Term(proof) = &step.proof {
                    collect_ident_locations(proof, locations);
                }
            }
        }
        // `open X in <term>`: recurse into the sub-term for identifier spans.
        SurfaceExpr::OpenIn { body, .. } => collect_ident_locations(body, locations),
        // Terminal expressions with no nested identifiers
        SurfaceExpr::Universe(_, _)
        | SurfaceExpr::Lit(_, _)
        | SurfaceExpr::Hole(_)
        | SurfaceExpr::NamedHole(_, _)
        | SurfaceExpr::SyntheticSorry(_)
        | SurfaceExpr::SyntaxQuote(_, _) => {}
    }
}

/// Recurse into a do-element to collect identifier locations
fn collect_ident_locations_do_elem(
    elem: &clean_parser::DoElem,
    locations: &mut Vec<IdentLocation>,
) {
    use clean_parser::DoElem;
    match elem {
        DoElem::Bind(_, _, action) | DoElem::Let(_, _, action) | DoElem::LetMut(_, _, action) => {
            collect_ident_locations(action, locations);
        }
        DoElem::LetRec(_, bindings) => {
            for (_, val) in bindings {
                collect_ident_locations(val, locations);
            }
        }
        DoElem::Return(_, expr) | DoElem::Expr(_, expr) => {
            collect_ident_locations(expr, locations);
        }
        DoElem::If(_, cond, then_branch, else_branch) => {
            collect_ident_locations(cond, locations);
            for elem in then_branch {
                collect_ident_locations_do_elem(elem, locations);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_ident_locations_do_elem(elem, locations);
                }
            }
        }
        DoElem::IfLet(_, _, scrutinee, then_branch, else_branch) => {
            collect_ident_locations(scrutinee, locations);
            for elem in then_branch {
                collect_ident_locations_do_elem(elem, locations);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_ident_locations_do_elem(elem, locations);
                }
            }
        }
        DoElem::IfDecidable(_, _, prop, then_branch, else_branch) => {
            collect_ident_locations(prop, locations);
            for elem in then_branch {
                collect_ident_locations_do_elem(elem, locations);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_ident_locations_do_elem(elem, locations);
                }
            }
        }
        DoElem::For(_, _, collection, body) => {
            collect_ident_locations(collection, locations);
            for elem in body {
                collect_ident_locations_do_elem(elem, locations);
            }
        }
        DoElem::Match(_, discrs, arms) => {
            for d in discrs {
                collect_ident_locations(d, locations);
            }
            for arm in arms {
                for elem in &arm.body {
                    collect_ident_locations_do_elem(elem, locations);
                }
            }
        }
        DoElem::TryCatch(_, try_body, catches, finally_body) => {
            for elem in try_body {
                collect_ident_locations_do_elem(elem, locations);
            }
            for catch in catches {
                if let Some(exc_ty) = &catch.exc_type {
                    collect_ident_locations(exc_ty, locations);
                }
                for elem in &catch.body {
                    collect_ident_locations_do_elem(elem, locations);
                }
            }
            if let Some(fin_elems) = finally_body {
                for elem in fin_elems {
                    collect_ident_locations_do_elem(elem, locations);
                }
            }
        }
        DoElem::LetElse(_, _, action, fallback) => {
            collect_ident_locations(action, locations);
            for elem in fallback {
                collect_ident_locations_do_elem(elem, locations);
            }
        }
        DoElem::LetExpr(_, _, val, _, fallback) => {
            collect_ident_locations(val, locations);
            for elem in fallback {
                collect_ident_locations_do_elem(elem, locations);
            }
        }
        DoElem::Repeat(_, body) => {
            for elem in body {
                collect_ident_locations_do_elem(elem, locations);
            }
        }
        DoElem::While(_, cond, body) => {
            collect_ident_locations(cond, locations);
            for elem in body {
                collect_ident_locations_do_elem(elem, locations);
            }
        }
        DoElem::DbgTrace(_, msg) => {
            collect_ident_locations(msg, locations);
        }
        DoElem::Break(_) | DoElem::Continue(_) => {}
        DoElem::Reassign(_, _, val) => {
            collect_ident_locations(val, locations);
        }
        DoElem::PatternReassign(_, _, val) => {
            collect_ident_locations(val, locations);
        }
    }
}

/// Collect identifier occurrences from binders (types and defaults)
pub(crate) fn collect_locations_from_binders(
    binders: &[clean_parser::SurfaceBinder],
    locations: &mut Vec<IdentLocation>,
) {
    for binder in binders {
        if let Some(ty) = &binder.ty {
            collect_ident_locations(ty, locations);
        }
        if let Some(default) = &binder.default {
            collect_ident_locations(default, locations);
        }
    }
}
