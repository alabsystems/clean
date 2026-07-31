// Copyright 2026 Andrew Yates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Warning detection: sorry/admit usage, deprecated names, unused variables.

use super::analysis::{
    collect_ident_locations, collect_locations_from_binders, collect_used_idents, IdentLocation,
};
use crate::document::{Warning, WarningCode};
use std::collections::{HashMap, HashSet};

/// Binder information for unused-variable detection.
struct BinderInfo {
    name: String,
    start: usize,
    end: usize,
}

/// Collect all `sorry` and `admit` occurrences in an expression
pub(super) fn collect_sorry_usage(
    expr: &clean_parser::SurfaceExpr,
    locations: &mut Vec<IdentLocation>,
) {
    use clean_parser::SurfaceExpr;

    match expr {
        SurfaceExpr::Ident(span, name) => {
            // Check for sorry, admit, or native_decide (which can hide incomplete proofs)
            if name == "sorry" || name == "admit" {
                locations.push(IdentLocation {
                    name: name.clone(),
                    start: span.start,
                    end: span.end,
                });
            }
        }
        SurfaceExpr::App(_, func, args) => {
            collect_sorry_usage(func, locations);
            for arg in args {
                collect_sorry_usage(&arg.expr, locations);
            }
        }
        SurfaceExpr::Lambda(_, binders, body)
        | SurfaceExpr::PatternMatchLambda(_, binders, body)
        | SurfaceExpr::Pi(_, binders, body) => {
            for binder in binders {
                if let Some(ty) = &binder.ty {
                    collect_sorry_usage(ty, locations);
                }
                if let Some(default) = &binder.default {
                    collect_sorry_usage(default, locations);
                }
            }
            collect_sorry_usage(body, locations);
        }
        SurfaceExpr::Arrow(_, left, right) => {
            collect_sorry_usage(left, locations);
            collect_sorry_usage(right, locations);
        }
        SurfaceExpr::Let(_, binder, val, body) | SurfaceExpr::LetRec(_, binder, val, body) => {
            if let Some(ty) = &binder.ty {
                collect_sorry_usage(ty, locations);
            }
            collect_sorry_usage(val, locations);
            collect_sorry_usage(body, locations);
        }
        SurfaceExpr::If(_, cond, then_branch, else_branch) => {
            collect_sorry_usage(cond, locations);
            collect_sorry_usage(then_branch, locations);
            collect_sorry_usage(else_branch, locations);
        }
        SurfaceExpr::IfLet(_, _pat, scrutinee, then_branch, else_branch) => {
            collect_sorry_usage(scrutinee, locations);
            collect_sorry_usage(then_branch, locations);
            collect_sorry_usage(else_branch, locations);
        }
        SurfaceExpr::IfDecidable(_, _, prop, then_branch, else_branch) => {
            collect_sorry_usage(prop, locations);
            collect_sorry_usage(then_branch, locations);
            collect_sorry_usage(else_branch, locations);
        }
        SurfaceExpr::Match(_, _, scrutinee, arms) => {
            collect_sorry_usage(scrutinee, locations);
            for arm in arms {
                collect_sorry_usage(&arm.body, locations);
            }
        }
        SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::OutParam(_, inner)
        | SurfaceExpr::SemiOutParam(_, inner)
        | SurfaceExpr::Explicit(_, inner) => collect_sorry_usage(inner, locations),
        SurfaceExpr::Ascription(_, expr, ty) => {
            collect_sorry_usage(expr, locations);
            collect_sorry_usage(ty, locations);
        }
        SurfaceExpr::Proj(_, expr, _)
        | SurfaceExpr::UniverseInst(_, expr, _)
        | SurfaceExpr::NamedArg(_, _, expr) => collect_sorry_usage(expr, locations),
        SurfaceExpr::QQuotation {
            inner, type_annot, ..
        } => {
            collect_sorry_usage(inner, locations);
            if let Some(ty) = type_annot {
                collect_sorry_usage(ty, locations);
            }
        }
        SurfaceExpr::QAntiquot { content, .. } => {
            use clean_parser::QAntiquotContent;
            match content {
                QAntiquotContent::Simple(_) => {}
                QAntiquotContent::Expr(e) => {
                    collect_sorry_usage(e, locations);
                }
                QAntiquotContent::Typed { ty, .. } => {
                    collect_sorry_usage(ty, locations);
                }
                QAntiquotContent::Splice { .. } => {}
            }
        }
        SurfaceExpr::LetPattern(_, _pattern, scrutinee, fallback, body) => {
            collect_sorry_usage(scrutinee, locations);
            collect_sorry_usage(fallback, locations);
            collect_sorry_usage(body, locations);
        }
        // Structure literal: { x := val, y := val2 }
        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            if let Some(ty) = struct_type {
                collect_sorry_usage(ty, locations);
            }
            if let Some(b) = base {
                collect_sorry_usage(b, locations);
            }
            for field in fields {
                collect_sorry_usage(&field.val, locations);
            }
        }
        // Do notation: recurse into do-element sub-expressions
        SurfaceExpr::Do(_, elems) => {
            for elem in elems {
                collect_sorry_usage_do_elem(elem, locations);
            }
        }
        // Nested action lift: recurse into inner expression
        SurfaceExpr::LiftMethod(_, inner) => collect_sorry_usage(inner, locations),
        SurfaceExpr::InterpolatedStr { parts, .. } => parts.iter().for_each(|part| {
            if let clean_parser::InterpolationPart::Expr(e) = part {
                collect_sorry_usage(e, locations);
            }
        }),
        // ByTactic: tactics are opaque for sorry detection at surface level
        SurfaceExpr::ByTactic(_, _) => {}
        // CalcBlock: recurse into relation expressions and term justifications
        SurfaceExpr::CalcBlock(_, steps) => {
            for step in steps {
                collect_sorry_usage(&step.rel, locations);
                if let clean_parser::SurfaceCalcJustification::Term(proof) = &step.proof {
                    collect_sorry_usage(proof, locations);
                }
            }
        }
        // Synthetic sorry: the elaborator inserted this sorry, treat as sorry usage
        SurfaceExpr::SyntheticSorry(span) => {
            locations.push(IdentLocation {
                name: "sorry".to_string(),
                start: span.start,
                end: span.end,
            });
        }
        // `open X in <term>`: a `sorry` may hide in the sub-term; recurse.
        SurfaceExpr::OpenIn { body, .. } => collect_sorry_usage(body, locations),
        // Terminal expressions
        SurfaceExpr::Universe(_, _)
        | SurfaceExpr::Lit(_, _)
        | SurfaceExpr::Hole(_)
        | SurfaceExpr::NamedHole(_, _)
        | SurfaceExpr::SyntaxQuote(_, _) => {}
    }
}

/// Recurse into a do-element to collect sorry usage
pub(super) fn collect_sorry_usage_do_elem(
    elem: &clean_parser::DoElem,
    locations: &mut Vec<IdentLocation>,
) {
    use clean_parser::DoElem;
    match elem {
        DoElem::Bind(_, _, action) | DoElem::Let(_, _, action) | DoElem::LetMut(_, _, action) => {
            collect_sorry_usage(action, locations);
        }
        DoElem::LetRec(_, bindings) => {
            for (_, val) in bindings {
                collect_sorry_usage(val, locations);
            }
        }
        DoElem::Return(_, expr) | DoElem::Expr(_, expr) => {
            collect_sorry_usage(expr, locations);
        }
        DoElem::If(_, cond, then_branch, else_branch) => {
            collect_sorry_usage(cond, locations);
            for elem in then_branch {
                collect_sorry_usage_do_elem(elem, locations);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_sorry_usage_do_elem(elem, locations);
                }
            }
        }
        DoElem::IfLet(_, _, scrutinee, then_branch, else_branch) => {
            collect_sorry_usage(scrutinee, locations);
            for elem in then_branch {
                collect_sorry_usage_do_elem(elem, locations);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_sorry_usage_do_elem(elem, locations);
                }
            }
        }
        DoElem::IfDecidable(_, _, prop, then_branch, else_branch) => {
            collect_sorry_usage(prop, locations);
            for elem in then_branch {
                collect_sorry_usage_do_elem(elem, locations);
            }
            if let Some(else_elems) = else_branch {
                for elem in else_elems {
                    collect_sorry_usage_do_elem(elem, locations);
                }
            }
        }
        DoElem::For(_, _, collection, body) => {
            collect_sorry_usage(collection, locations);
            for elem in body {
                collect_sorry_usage_do_elem(elem, locations);
            }
        }
        DoElem::Match(_, discrs, arms) => {
            for d in discrs {
                collect_sorry_usage(d, locations);
            }
            for arm in arms {
                for elem in &arm.body {
                    collect_sorry_usage_do_elem(elem, locations);
                }
            }
        }
        DoElem::TryCatch(_, try_body, catches, finally_body) => {
            for elem in try_body {
                collect_sorry_usage_do_elem(elem, locations);
            }
            for catch in catches {
                if let Some(exc_ty) = &catch.exc_type {
                    collect_sorry_usage(exc_ty, locations);
                }
                for elem in &catch.body {
                    collect_sorry_usage_do_elem(elem, locations);
                }
            }
            if let Some(fin_elems) = finally_body {
                for elem in fin_elems {
                    collect_sorry_usage_do_elem(elem, locations);
                }
            }
        }
        DoElem::LetElse(_, _, action, fallback) => {
            collect_sorry_usage(action, locations);
            for elem in fallback {
                collect_sorry_usage_do_elem(elem, locations);
            }
        }
        DoElem::LetExpr(_, _, val, _, fallback) => {
            collect_sorry_usage(val, locations);
            for elem in fallback {
                collect_sorry_usage_do_elem(elem, locations);
            }
        }
        DoElem::Repeat(_, body) => {
            for elem in body {
                collect_sorry_usage_do_elem(elem, locations);
            }
        }
        DoElem::While(_, cond, body) => {
            collect_sorry_usage(cond, locations);
            for elem in body {
                collect_sorry_usage_do_elem(elem, locations);
            }
        }
        DoElem::DbgTrace(_, msg) => {
            collect_sorry_usage(msg, locations);
        }
        DoElem::Break(_) | DoElem::Continue(_) => {}
        DoElem::Reassign(_, _, val) => {
            collect_sorry_usage(val, locations);
        }
        DoElem::PatternReassign(_, _, val) => {
            collect_sorry_usage(val, locations);
        }
    }
}

/// Detect `sorry` usage in a declaration and return warnings
pub(crate) fn detect_sorry_warnings(decl: &clean_parser::SurfaceDecl) -> Vec<Warning> {
    use clean_parser::SurfaceDecl;

    let mut locations = Vec::new();

    // Extract expressions to check based on declaration type
    match decl {
        SurfaceDecl::Def { ty, val, .. } => {
            if let Some(ty) = ty {
                collect_sorry_usage(ty, &mut locations);
            }
            collect_sorry_usage(val, &mut locations);
        }
        SurfaceDecl::Theorem { ty, proof, .. } => {
            collect_sorry_usage(ty, &mut locations);
            collect_sorry_usage(proof, &mut locations);
        }
        _ => {}
    }

    // Convert to warnings
    locations
        .into_iter()
        .map(|loc| Warning {
            start: loc.start,
            end: loc.end,
            message: format!("declaration uses `{}` (incomplete proof)", loc.name),
            code: WarningCode::IncompleteProof,
            related: Vec::new(),
        })
        .collect()
}

/// Collect names marked as deprecated via `attribute [deprecated] ...`
pub(crate) fn collect_deprecated_names(decls: &[clean_parser::SurfaceDecl]) -> HashSet<String> {
    let mut deprecated = HashSet::new();

    for decl in decls {
        match decl {
            clean_parser::SurfaceDecl::Attribute { attrs, names, .. } => {
                let is_deprecated = attrs.iter().any(|attr| {
                    matches!(
                        attr,
                        clean_parser::AttributeCommandAttr::Add(
                            clean_parser::Attribute::Deprecated(_)
                        )
                    )
                });

                if is_deprecated {
                    for name in names {
                        deprecated.insert(name.clone());
                    }
                }
            }
            clean_parser::SurfaceDecl::Namespace { decls, .. }
            | clean_parser::SurfaceDecl::Section { decls, .. }
            | clean_parser::SurfaceDecl::Mutual { decls, .. } => {
                deprecated.extend(collect_deprecated_names(decls));
            }
            _ => {}
        }
    }

    deprecated
}

/// Convert identifier occurrences to deprecation warnings
pub(super) fn warnings_for_deprecated_usage(
    locations: Vec<IdentLocation>,
    deprecated_names: &HashSet<String>,
) -> Vec<Warning> {
    locations
        .into_iter()
        .filter(|loc| deprecated_names.contains(&loc.name))
        .map(|loc| Warning {
            start: loc.start,
            end: loc.end,
            message: format!("`{}` is deprecated", loc.name),
            code: WarningCode::DeprecatedFeature,
            related: Vec::new(),
        })
        .collect()
}

/// Detect usage of deprecated names within a declaration
pub(crate) fn detect_deprecated_usage(
    decl: &clean_parser::SurfaceDecl,
    deprecated_names: &HashSet<String>,
) -> Vec<Warning> {
    use clean_parser::SurfaceDecl;

    if deprecated_names.is_empty() {
        return Vec::new();
    }

    match decl {
        SurfaceDecl::Def {
            binders, ty, val, ..
        }
        | SurfaceDecl::Example {
            binders, ty, val, ..
        } => {
            let mut locations = Vec::new();
            collect_locations_from_binders(binders, &mut locations);
            if let Some(ty) = ty {
                collect_ident_locations(ty, &mut locations);
            }
            collect_ident_locations(val, &mut locations);
            warnings_for_deprecated_usage(locations, deprecated_names)
        }
        SurfaceDecl::Theorem {
            binders, ty, proof, ..
        } => {
            let mut locations = Vec::new();
            collect_locations_from_binders(binders, &mut locations);
            collect_ident_locations(ty, &mut locations);
            collect_ident_locations(proof, &mut locations);
            warnings_for_deprecated_usage(locations, deprecated_names)
        }
        SurfaceDecl::Axiom { binders, ty, .. } => {
            let mut locations = Vec::new();
            collect_locations_from_binders(binders, &mut locations);
            collect_ident_locations(ty, &mut locations);
            warnings_for_deprecated_usage(locations, deprecated_names)
        }
        SurfaceDecl::Inductive {
            binders, ty, ctors, ..
        } => {
            let mut locations = Vec::new();
            collect_locations_from_binders(binders, &mut locations);
            collect_ident_locations(ty, &mut locations);
            for ctor in ctors {
                collect_ident_locations(&ctor.ty, &mut locations);
            }
            warnings_for_deprecated_usage(locations, deprecated_names)
        }
        SurfaceDecl::Structure {
            binders,
            ty,
            fields,
            ..
        }
        | SurfaceDecl::Class {
            binders,
            ty,
            fields,
            ..
        } => {
            let mut locations = Vec::new();
            collect_locations_from_binders(binders, &mut locations);
            if let Some(ty) = ty {
                collect_ident_locations(ty, &mut locations);
            }
            for field in fields {
                collect_ident_locations(&field.ty, &mut locations);
                if let Some(default) = &field.default {
                    collect_ident_locations(default, &mut locations);
                }
            }
            warnings_for_deprecated_usage(locations, deprecated_names)
        }
        SurfaceDecl::Instance {
            binders,
            class_type,
            fields,
            ..
        } => {
            let mut locations = Vec::new();
            collect_locations_from_binders(binders, &mut locations);
            collect_ident_locations(class_type, &mut locations);
            for field in fields {
                collect_ident_locations(&field.val, &mut locations);
            }
            warnings_for_deprecated_usage(locations, deprecated_names)
        }
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => decls
            .iter()
            .flat_map(|d| detect_deprecated_usage(d, deprecated_names))
            .collect(),
        _ => Vec::new(),
    }
}

/// Merge surface `IncompleteProof` warnings with an optional registration report.
///
/// Policy:
/// - `None` report: return surface warnings unchanged
/// - `ExplicitSorry`: keep surface incomplete-proof warnings if they exist;
///   add one declaration-level warning only when no surface warning exists
/// - `SyntheticSorry`: remove surface incomplete-proof warnings and add one
///   declaration-level warning over the declaration span
///
/// Unrelated warnings (unused variable, deprecation, etc.) are always preserved.
pub(crate) fn merge_registration_sorry_warning(
    surface_warnings: Vec<Warning>,
    report: Option<&clean_elab::RegistrationWarning>,
    decl_name: &str,
    decl_span: (usize, usize),
) -> Vec<Warning> {
    let report = match report {
        Some(r) => r,
        None => return surface_warnings,
    };

    use clean_elab::RegistrationWarningKind;

    match report.kind {
        RegistrationWarningKind::ExplicitSorry => {
            let has_surface_incomplete = surface_warnings
                .iter()
                .any(|w| w.code == WarningCode::IncompleteProof);
            if has_surface_incomplete {
                // Surface warnings already have precise token ranges — keep them
                surface_warnings
            } else {
                // No surface warning exists; add one declaration-level fallback
                let mut out = surface_warnings;
                out.push(Warning {
                    start: decl_span.0,
                    end: decl_span.1,
                    message: format!("declaration `{decl_name}` uses explicit sorry"),
                    code: WarningCode::IncompleteProof,
                    related: Vec::new(),
                });
                out
            }
        }
        RegistrationWarningKind::SyntheticSorry => {
            // Remove surface incomplete-proof warnings; replace with one
            // declaration-level warning for the synthetic sorry
            let mut out: Vec<Warning> = surface_warnings
                .into_iter()
                .filter(|w| w.code != WarningCode::IncompleteProof)
                .collect();
            out.push(Warning {
                start: decl_span.0,
                end: decl_span.1,
                message: format!("declaration `{decl_name}` uses synthetic sorry"),
                code: WarningCode::IncompleteProof,
                related: Vec::new(),
            });
            out
        }
        // TrustedArith / TrustedAy are not sorry-class warnings for LSP
        RegistrationWarningKind::TrustedArith | RegistrationWarningKind::TrustedAy => {
            surface_warnings
        }
    }
}

/// Extract the leading binders and the body expressions to scan for a
/// declaration, or `None` for declaration kinds whose parameters are not
/// checked (inductives, structures, classes, instances — their parameters are
/// often present only for type inference).
fn binders_and_exprs(
    decl: &clean_parser::SurfaceDecl,
) -> Option<(Vec<BinderInfo>, Vec<&clean_parser::SurfaceExpr>)> {
    use clean_parser::SurfaceDecl;

    let collect_binders = |binders: &[clean_parser::SurfaceBinder]| -> Vec<BinderInfo> {
        binders
            .iter()
            .map(|b| BinderInfo {
                name: b.name.clone(),
                start: b.span.start,
                end: b.span.end,
            })
            .collect()
    };

    match decl {
        SurfaceDecl::Def {
            binders, ty, val, ..
        } => {
            let mut exprs: Vec<&clean_parser::SurfaceExpr> = vec![val.as_ref()];
            if let Some(ty) = ty {
                exprs.push(ty.as_ref());
            }
            Some((collect_binders(binders), exprs))
        }
        SurfaceDecl::Theorem {
            binders, ty, proof, ..
        } => Some((collect_binders(binders), vec![ty.as_ref(), proof.as_ref()])),
        SurfaceDecl::Axiom { binders, ty, .. } => {
            Some((collect_binders(binders), vec![ty.as_ref()]))
        }
        _ => None,
    }
}

/// Detect unused binders in a declaration and return warnings
pub(crate) fn detect_unused_variables(decl: &clean_parser::SurfaceDecl) -> Vec<Warning> {
    let mut warnings = Vec::new();

    let Some((binders, exprs)) = binders_and_exprs(decl) else {
        return warnings;
    };

    // Collect all used identifiers
    let mut used = HashSet::new();
    for expr in exprs {
        collect_used_idents(expr, &mut used);
    }

    // Check each binder
    for binder in binders {
        // Skip anonymous binders (names starting with _)
        if binder.name.starts_with('_') {
            continue;
        }

        // Check if the binder is used
        if !used.contains(&binder.name) {
            warnings.push(Warning {
                start: binder.start,
                end: binder.end,
                message: format!("unused variable `{}`", binder.name),
                code: WarningCode::UnusedVariable,
                related: Vec::new(),
            });
        }
    }

    warnings
}

/// Detect binders that reuse a name already bound earlier in the same
/// declaration's binder list, and return one warning per later occurrence.
///
/// The document model already records every binder span, so the warning can
/// point its `related` location at the *first* binder of the same name — a
/// genuine, model-tracked secondary location (never fabricated). This mirrors
/// the Lean 4 LSP behaviour of attaching `DiagnosticRelatedInformation` to a
/// duplicate-binder diagnostic that references the original binder site.
pub(crate) fn detect_duplicate_binders(decl: &clean_parser::SurfaceDecl) -> Vec<Warning> {
    let mut warnings = Vec::new();

    let Some((binders, _exprs)) = binders_and_exprs(decl) else {
        return warnings;
    };

    // Map each non-anonymous name to the span of its first occurrence.
    let mut first_seen: HashMap<String, (usize, usize)> = HashMap::new();
    for binder in &binders {
        // Anonymous binders (`_`-prefixed) are intentionally repeatable.
        if binder.name.starts_with('_') {
            continue;
        }
        match first_seen.get(&binder.name) {
            None => {
                first_seen.insert(binder.name.clone(), (binder.start, binder.end));
            }
            Some(&(first_start, first_end)) => {
                warnings.push(Warning {
                    start: binder.start,
                    end: binder.end,
                    message: format!("duplicate binder `{}`", binder.name),
                    code: WarningCode::Other,
                    related: vec![crate::document::RelatedLocation {
                        start: first_start,
                        end: first_end,
                        message: format!("first binding of `{}` is here", binder.name),
                    }],
                });
            }
        }
    }

    warnings
}
