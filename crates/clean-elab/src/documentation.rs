// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Markdown documentation validation at declaration attachment, after registration.
//!
//! The URL grammar and iterator movement follow Lean's `rewriteManualLinksCore`
//! (`src/Lean/DocString/Links.lean`, pinned v4.26.0 / v4.30.0-rc2 / v4.35.0).
//! In particular, code spans are scanned too, and the upstream end-of-input
//! boundary excludes the last character. This is a source diagnostic: an
//! invalid link does not undo the genuine declaration's registration.

use crate::source_diagnostics::SourceDiagnostic;
use crate::{ElabError, ElabResult};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_parser::surface::DocComment;
use clean_parser::{Span, SurfaceDecl};

const SCHEME: &str = "lean-manual://";

fn url_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || "-._~:/?#[]@!$&'*+,;=".contains(c)
}

fn path_error(path: &str) -> Option<String> {
    let mut items = path.split('/');
    let kind = items.next().unwrap_or_default();
    if path.is_empty() {
        return Some("Missing documentation type".into());
    }
    if !matches!(kind, "section" | "errorExplanation") {
        return Some(format!(
            "Unknown documentation type `{kind}`. Expected one of the following: `section`, `errorExplanation`"
        ));
    }
    let args: Vec<_> = items.collect();
    match args.as_slice() {
        [""] => Some(format!("Empty {kind} ID")),
        [_] => None,
        _ => Some(format!(
            "Expected one item after `{kind}`, but got [{}]",
            args.join(", ")
        )),
    }
}

/// Validate only an attached Markdown doc body. All offsets are original UTF-8
/// byte positions, including its leading whitespace, as in Lean's doc syntax.
fn diagnostics(doc: &DocComment) -> Vec<SourceDiagnostic> {
    let raw = &doc.raw_text;
    let mut errors = Vec::new();
    let mut outer = 0;
    while outer < raw.len() {
        let pre = outer;
        let Some(c) = raw[outer..].chars().next() else {
            break;
        };
        outer += c.len_utf8();
        let Some(tail) = raw[pre..].strip_prefix(SCHEME) else {
            continue;
        };
        let start = raw.len() - tail.len();
        let mut inner = start;
        while inner < raw.len() {
            let stop = inner;
            let Some(c) = raw[inner..].chars().next() else {
                break;
            };
            inner += c.len_utf8();
            if url_char(c) && inner < raw.len() {
                continue;
            }
            if let Some(message) = path_error(&raw[start..stop]) {
                errors.push(SourceDiagnostic {
                    error: ElabError::DocumentationLink { message },
                    span: Some(Span::new(
                        doc.comment_span.start + 3 + pre,
                        doc.comment_span.start + 3 + stop,
                    )),
                });
            } else {
                outer = inner;
            }
            break;
        }
    }
    errors
}

fn markdown_world(world: LeanWorld) -> bool {
    // 4.13's DocString/Extension.lean stores Markdown without validating manual links;
    // 4.26's Add.lean and later call validateDocComment before storage.
    matches!(
        world,
        LeanWorld::Lean426 | LeanWorld::Lean430Rc2 | LeanWorld::Lean435 | LeanWorld::Lean436Rc2
    )
}

/// Attach errors to the actual registered result. Never inspect inert command
/// quotations, ordinary comments, module docs, or the whole source file.
pub(crate) fn diagnose_registered(
    env: &Environment,
    result: ElabResult,
    decl: &SurfaceDecl,
    world: LeanWorld,
) -> ElabResult {
    let markdown = markdown_world(world);
    if let (SurfaceDecl::Mutual { decls, .. }, ElabResult::Multiple(_)) = (decl, &result) {
        // Registration follows dependencies, not source order. Read the doc
        // actually carried by each registered member; never zip the two orders.
        if let ElabResult::Multiple(results) = result {
            return ElabResult::Multiple(
                results
                    .into_iter()
                    .map(|result| {
                        let source = registered_documentation(&result).and_then(|doc| {
                            decls.iter().find(|decl| {
                                decl.documentation().is_some_and(|source| {
                                    source.comment_span == doc.comment_span
                                        && source.raw_text == doc.raw_text
                                })
                            })
                        });
                        match source {
                            Some(decl) => diagnose_registered(env, result, decl, world),
                            None => result,
                        }
                    })
                    .collect(),
            );
        }
    }
    let Some(leaf) = result.primary_leaf().and_then(ElabResult::primary_leaf) else {
        return result;
    };
    let Some(name) = leaf.declaration_name() else {
        return result;
    };
    if name.is_anon() || env.get_const(name).is_none() {
        return result;
    }
    let mut errors = Vec::new();
    if let (
        SurfaceDecl::Inductive { ctors, .. } | SurfaceDecl::Coinductive { ctors, .. },
        ElabResult::Inductive { constructors, .. },
    ) = (decl, leaf)
    {
        // Lean reports duplicates while constructing its member views, before
        // attaching the type's doc and each constructor's selected doc.
        for ctor in ctors {
            let constructor = crate::namespace::append_names(name, ctor.name.name());
            if ctor.duplicate_documentation.is_some()
                && constructors.iter().any(|(n, _)| *n == constructor)
                && env.get_const(&constructor).is_some()
            {
                if let Some(doc) = &ctor.documentation {
                    errors.push(SourceDiagnostic {
                        error: ElabError::DocumentationAttachment {
                            message: if markdown {
                                "Duplicate doc string"
                            } else {
                                "duplicate doc string"
                            }
                            .into(),
                        },
                        span: Some(doc.comment_span),
                    });
                }
            }
        }
    }
    if markdown {
        errors.extend(decl.documentation().map(diagnostics).unwrap_or_default());
    }
    match (decl, leaf) {
        (
            SurfaceDecl::Structure { fields, .. } | SurfaceDecl::Class { fields, .. },
            ElabResult::Structure { projections, .. },
        ) if markdown => {
            for field in fields {
                let projected = crate::namespace::append_names(name, field.name.name());
                if projections.iter().any(|(n, _, _)| *n == projected)
                    && env.get_const(&projected).is_some()
                {
                    if let Some(doc) = &field.documentation {
                        errors.extend(diagnostics(doc));
                    }
                }
            }
        }
        (
            SurfaceDecl::Inductive { ctors, .. } | SurfaceDecl::Coinductive { ctors, .. },
            ElabResult::Inductive { constructors, .. },
        ) if markdown => {
            for ctor in ctors {
                let constructor = crate::namespace::append_names(name, ctor.name.name());
                if constructors.iter().any(|(n, _)| *n == constructor)
                    && env.get_const(&constructor).is_some()
                {
                    if let Some(doc) = &ctor.documentation {
                        errors.extend(diagnostics(doc));
                    }
                }
            }
        }
        _ => {}
    }
    if errors.is_empty() {
        result
    } else {
        let target = name.clone();
        attach_errors(result, &target, &mut Some(errors))
    }
}

// A source declaration may lift helpers or have failed deriving siblings.
// Keep those leaves individually checkable: diagnose only its registered parent.
fn attach_errors(
    result: ElabResult,
    target: &Name,
    errors: &mut Option<Vec<SourceDiagnostic>>,
) -> ElabResult {
    match result {
        ElabResult::Multiple(results) => ElabResult::Multiple(
            results
                .into_iter()
                .map(|result| attach_errors(result, target, errors))
                .collect(),
        ),
        result if result.declaration_name() == Some(target) => {
            let Some(mut added) = errors.take() else {
                return result;
            };
            match result {
                ElabResult::Diagnosed {
                    result,
                    diagnostics,
                } => {
                    added.extend(diagnostics);
                    ElabResult::Diagnosed {
                        result,
                        diagnostics: added,
                    }
                }
                result => ElabResult::Diagnosed {
                    result: Box::new(result),
                    diagnostics: added,
                },
            }
        }
        result => result,
    }
}

// The elaborator copies the actual member modifiers into the registered result,
// including through dependency sorting and private-name generation.
fn registered_documentation(result: &ElabResult) -> Option<&DocComment> {
    match result.primary_leaf().and_then(ElabResult::primary_leaf)? {
        ElabResult::Definition { modifiers, .. }
        | ElabResult::Theorem { modifiers, .. }
        | ElabResult::Axiom { modifiers, .. }
        | ElabResult::Opaque { modifiers, .. }
        | ElabResult::Inductive { modifiers, .. }
        | ElabResult::Structure { modifiers, .. }
        | ElabResult::Instance { modifiers, .. }
        | ElabResult::MutualInductive { modifiers, .. } => modifiers.documentation.as_ref(),
        _ => None,
    }
}
