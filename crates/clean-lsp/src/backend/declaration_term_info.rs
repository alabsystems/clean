// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Declaration-name observations from actual normal elaboration results.

use clean_elab::term_info::{SourceInfo, TermContext};
use clean_elab::ElabResult;
use clean_kernel::{Expr, Level};
use clean_parser::lexer::{Lexer, TokenKind};
use clean_parser::{Span, SurfaceDecl};

use super::CleanBackend;

pub(super) fn observe(
    text: &str,
    decl: &SurfaceDecl,
    result: &ElabResult,
) -> Vec<(Span, TermContext)> {
    if let Some(term) = observe_leaf(text, decl, result) {
        return vec![term];
    }
    match (decl, result) {
        (
            SurfaceDecl::Namespace { decls, .. }
            | SurfaceDecl::Section { decls, .. }
            | SurfaceDecl::Mutual { decls, .. },
            ElabResult::Multiple(results),
        ) if decls.len() == results.len() => decls
            .iter()
            .zip(results)
            .flat_map(|(decl, result)| observe(text, decl, result))
            .collect(),
        _ => Vec::new(),
    }
}

fn observe_leaf(
    text: &str,
    decl: &SurfaceDecl,
    result: &ElabResult,
) -> Option<(Span, TermContext)> {
    let (name, universe_params, ty) = match result.primary_leaf()? {
        ElabResult::Definition {
            name,
            universe_params,
            ty,
            ..
        }
        | ElabResult::Theorem {
            name,
            universe_params,
            ty,
            ..
        }
        | ElabResult::Axiom {
            name,
            universe_params,
            ty,
            ..
        }
        | ElabResult::Opaque {
            name,
            universe_params,
            ty,
            ..
        } => (name, universe_params, ty),
        _ => return None,
    };
    let (_, source_name, (start, _)) = CleanBackend::classify_decl(decl);
    let source_name = source_name?;
    let mut lexer = Lexer::new(text.get(start..)?);
    loop {
        match lexer.next_token().kind {
            TokenKind::Private
            | TokenKind::Protected
            | TokenKind::Public
            | TokenKind::Noncomputable
            | TokenKind::Partial
            | TokenKind::Unsafe => {}
            TokenKind::Def
            | TokenKind::Abbrev
            | TokenKind::Theorem
            | TokenKind::Lemma
            | TokenKind::Axiom
            | TokenKind::Opaque
            | TokenKind::Codef => break,
            _ => return None,
        }
    }
    // Match the parsed name's actual tokens immediately after its command.
    // Do not search later comments, references, or another declaration.
    let mut name_span = None;
    for expected in Lexer::tokenize(&source_name) {
        if expected.kind == TokenKind::Eof {
            break;
        }
        if !matches!(expected.kind, TokenKind::Ident(_) | TokenKind::Dot) {
            return None;
        }
        let actual = lexer.next_token();
        if actual.kind != expected.kind {
            return None;
        }
        let span = name_span.get_or_insert(Span {
            start: start.checked_add(actual.span.start)?,
            end: start.checked_add(actual.span.end)?,
        });
        span.end = start.checked_add(actual.span.end)?;
    }
    let levels: Vec<_> = universe_params.iter().cloned().map(Level::param).collect();
    Some((
        name_span?,
        TermContext {
            expr: Expr::const_(name.clone(), levels),
            expected_type: None,
            unresolved_sort_goal: None,
            type_: ty.clone(),
            local_context: Vec::new(),
            is_binder: false,
        },
    ))
}

pub(super) fn append(infos: &mut Vec<SourceInfo>, declarations: Vec<(Span, TermContext)>) {
    let mut next_id = infos
        .iter()
        .map(|info| info.id)
        .max()
        .map_or(Some(0), |id| id.checked_add(1));
    for (span, term) in declarations {
        let Some(id) = next_id else {
            tracing::warn!("declaration term observation identifiers exhausted");
            break;
        };
        infos.push(SourceInfo {
            id,
            parent_id: None,
            span,
            application_head: None,
            is_variable: false,
            is_partial: false,
            term: Some(term),
        });
        next_id = id.checked_add(1);
    }
}
