// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Optional, untyped observations made by actual parser productions.
//!
//! This first foundation covers written identifiers, literals, holes, ordinary
//! parentheses and positional applications, plus def/theorem/axiom/opaque name
//! tokens. It deliberately does not infer origins for desugared notation,
//! projections, binders, tactics, named arguments or other unsupported syntax.
//! An unavailable root is not an origin reconstructed from a declaration span.
//! No endpoint or typed elaborator observation consumes this sidecar yet.
//!
//! Capture owns its source snapshot. IDs belong to that capture, survive an
//! immutable clone and are rejected by independent captures of identical text.
//! They are not semantic IDs, cache generations, serialized IDs or RPC IDs.
//! Capture errors invalidate observations only; parsing still returns its own
//! verdict and its unchanged surface AST.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::lexer::{Token, TokenKind};
use crate::{Span, SurfaceDecl, SurfaceExpr, SurfaceName};

// Public types and methods live at the crate root; these re-exports preserve
// the original origins:: paths for consumers of the optional sidecar.
use crate::OriginCore as Core;
pub use crate::{
    OriginAvailability, OriginCaptureError, OriginChildRole, OriginId, OriginKind, OriginNode,
    OriginRoot, ParsedWithOrigins, SourceOrigins,
};

pub(crate) fn agrees(nodes: &[OriginNode], root: usize, expr: &SurfaceExpr) -> bool {
    let mut pending = vec![(root, expr)];
    while let Some((index, expr)) = pending.pop() {
        let Some(node) = nodes.get(index) else {
            return false;
        };
        if node.ast_span != expr.span() {
            return false;
        }
        match (&node.core, expr) {
            (Core::Ident(a), SurfaceExpr::Ident(_, b))
            | (Core::NamedHole(a), SurfaceExpr::NamedHole(_, b))
                if a.same_origin_metadata(b) => {}
            (Core::Lit(a), SurfaceExpr::Lit(_, b)) if a == b => {}
            (Core::Hole, SurfaceExpr::Hole(_)) => {}
            (Core::Paren(inner), SurfaceExpr::Paren(_, expr)) => pending.push((*inner, expr)),
            (Core::App { head, args }, SurfaceExpr::App(_, f, xs)) if args.len() == xs.len() => {
                pending.push((*head, f));
                for ((span, child), arg) in args.iter().zip(xs) {
                    if arg.name.is_some() || *span != arg.span {
                        return false;
                    }
                    pending.push((*child, &arg.expr));
                }
            }
            _ => return false,
        }
    }
    true
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct OriginCheckpoint {
    nodes: usize,
    names: usize,
    roots: usize,
}

pub(crate) struct OriginBuilder {
    source: Arc<str>,
    owner: Arc<()>,
    nodes: Vec<OriginNode>,
    by_span: BTreeMap<(usize, usize), Vec<usize>>,
    names: Vec<(Span, usize)>,
    roots: Vec<OriginRoot>,
    failure: Option<OriginCaptureError>,
}

impl OriginBuilder {
    pub(crate) fn new(source: &str) -> Self {
        Self {
            source: Arc::from(source),
            owner: Arc::new(()),
            nodes: Vec::new(),
            by_span: BTreeMap::new(),
            names: Vec::new(),
            roots: Vec::new(),
            failure: None,
        }
    }

    pub(crate) fn invalidate(&mut self, reason: &'static str) {
        self.failure.get_or_insert(OriginCaptureError(reason));
    }

    pub(crate) fn checkpoint(&self) -> OriginCheckpoint {
        OriginCheckpoint {
            nodes: self.nodes.len(),
            names: self.names.len(),
            roots: self.roots.len(),
        }
    }

    pub(crate) fn rollback(&mut self, checkpoint: OriginCheckpoint) {
        self.nodes.truncate(checkpoint.nodes);
        self.names.truncate(checkpoint.names);
        self.roots.truncate(checkpoint.roots);
        self.by_span.retain(|_, ids| {
            ids.retain(|id| *id < checkpoint.nodes);
            !ids.is_empty()
        });
        // An invariant failure remains a failure, including in a discarded
        // attempt. It can never turn into a semantic parser error.
    }

    fn add(&mut self, span: Span, ast_span: Span, core: Core) -> Option<usize> {
        if self.failure.is_some() {
            return None;
        }
        if span.start >= span.end || self.source.get(span.start..span.end).is_none() {
            self.invalidate("invalid original-source span");
            return None;
        }
        let index = self.nodes.len();
        self.nodes.push(OriginNode {
            span,
            ast_span,
            core,
        });
        self.by_span
            .entry((ast_span.start, ast_span.end))
            .or_default()
            .push(index);
        Some(index)
    }

    fn find(&self, expr: &SurfaceExpr) -> Option<usize> {
        let span = expr.span();
        let ids = self.by_span.get(&(span.start, span.end))?;
        // Repeated successful attempts can describe the very same source
        // subtree. Requiring agreement with the whole graph excludes a leaf
        // sharing the deliberately narrow legacy application span.
        ids.iter()
            .rev()
            .copied()
            .find(|id| agrees(&self.nodes, *id, expr))
    }

    fn availability(&self, expr: Option<&SurfaceExpr>) -> OriginAvailability {
        match expr {
            None => OriginAvailability::NotPresent,
            Some(expr) => self
                .find(expr)
                .map_or(OriginAvailability::Unavailable, |index| {
                    OriginAvailability::Located(OriginId {
                        owner: self.owner.clone(),
                        index,
                    })
                }),
        }
    }

    pub(crate) fn atom(&mut self, expr: &SurfaceExpr, tokens: &[Token]) {
        let (Some(first), Some(last)) = (tokens.first(), tokens.last()) else {
            return;
        };
        let core = match (expr, &first.kind) {
            // A single actual identifier token, not ⊤/⊥/()/notation's
            // generated reference or a parser-reconstructed qualified head.
            (SurfaceExpr::Ident(_, name), TokenKind::Ident(text))
                if tokens.len() == 1
                    && name.same_syntax(&SurfaceName::component(text, first.ident_escaped))
                    && !name.is_global_reference() =>
            {
                Core::Ident(name.clone())
            }
            (
                SurfaceExpr::Lit(_, value),
                TokenKind::NatLit(_)
                | TokenKind::FloatLit(_)
                | TokenKind::CharLit(_)
                | TokenKind::StringLit(_),
            ) if tokens.len() == 1 => Core::Lit(value.clone()),
            (SurfaceExpr::Hole(_), TokenKind::Underscore) if tokens.len() == 1 => Core::Hole,
            (SurfaceExpr::Hole(_), TokenKind::Question) if tokens.len() <= 2 => Core::Hole,
            (SurfaceExpr::NamedHole(_, name), TokenKind::Question) if tokens.len() == 2 => {
                Core::NamedHole(name.clone())
            }
            (SurfaceExpr::Paren(_, inner), TokenKind::LParen)
                if matches!(last.kind, TokenKind::RParen) =>
            {
                let Some(child) = self.find(inner) else {
                    return;
                };
                let child_span = self.nodes[child].span;
                if first.span.end > child_span.start || child_span.end > last.span.start {
                    return;
                }
                Core::Paren(child)
            }
            _ => return,
        };
        self.add(first.span.merge(last.span), expr.span(), core);
    }

    pub(crate) fn application(&mut self, expr: &SurfaceExpr) {
        let SurfaceExpr::App(_, head, args) = expr else {
            return;
        };
        let Some(head) = self.find(head) else {
            return;
        };
        let start = self.nodes[head].span.start;
        let mut end = self.nodes[head].span.end;
        let mut children = Vec::with_capacity(args.len());
        for arg in args {
            if arg.name.is_some() {
                return;
            }
            let Some(child) = self.find(&arg.expr) else {
                return;
            };
            let child_span = self.nodes[child].span;
            if end > child_span.start {
                return;
            }
            end = child_span.end;
            children.push((arg.span, child));
        }
        if !children.is_empty() {
            self.add(
                Span::new(start, end),
                expr.span(),
                Core::App {
                    head,
                    args: children,
                },
            );
        }
    }

    pub(crate) fn declaration_name(
        &mut self,
        declaration_span: Span,
        span: Option<Span>,
        name: &SurfaceName,
    ) {
        let Some(span) = span else {
            self.invalidate("missing declaration-name token span");
            return;
        };
        if let Some(id) = self.add(span, span, Core::DeclarationName(name.clone())) {
            self.names.push((declaration_span, id));
        }
    }

    pub(crate) fn expression_root(&mut self, expr: &SurfaceExpr) {
        self.roots
            .push(OriginRoot::Expression(self.availability(Some(expr))));
    }

    pub(crate) fn declaration_root(&mut self, decl: &SurfaceDecl) {
        let (span, name, ty, value) = match decl {
            SurfaceDecl::Def {
                span,
                name,
                ty,
                val,
                ..
            } => (*span, name, ty.as_deref(), Some(val.as_ref())),
            SurfaceDecl::Theorem {
                span,
                name,
                ty,
                proof,
                ..
            } => (*span, name, Some(ty.as_ref()), Some(proof.as_ref())),
            SurfaceDecl::Axiom { span, name, ty, .. } => (*span, name, Some(ty.as_ref()), None),
            SurfaceDecl::Opaque {
                span,
                name,
                ty,
                val,
                ..
            } => (*span, name, Some(ty.as_ref()), val.as_deref()),
            _ => return,
        };
        let name = self.names.iter().rev().find_map(|(declaration, id)| {
            (*declaration == span
                && matches!(&self.nodes[*id].core,
                Core::DeclarationName(parsed) if parsed.same_origin_metadata(name)))
            .then_some(*id)
        });
        if let Some(index) = name {
            self.roots.push(OriginRoot::Declaration {
                name: OriginId {
                    owner: self.owner.clone(),
                    index,
                },
                ty: self.availability(ty),
                value: self.availability(value),
            });
        }
    }

    pub(crate) fn finish(self) -> Result<SourceOrigins, OriginCaptureError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        let mut reachable = BTreeSet::new();
        let mut pending = Vec::new();
        for root in &self.roots {
            match root {
                OriginRoot::Expression(availability) => push_available(availability, &mut pending),
                OriginRoot::Declaration { name, ty, value } => {
                    pending.push(name.index);
                    push_available(ty, &mut pending);
                    push_available(value, &mut pending);
                }
            }
        }
        while let Some(index) = pending.pop() {
            if !reachable.insert(index) {
                continue;
            }
            let Some(node) = self.nodes.get(index) else {
                return Err(OriginCaptureError("invalid origin edge"));
            };
            pending.extend(node.edges().into_iter().map(|(_, child)| child));
        }
        let remap: BTreeMap<_, _> = reachable
            .iter()
            .enumerate()
            .map(|(new, old)| (*old, new))
            .collect();
        let mapped = |old| {
            remap
                .get(&old)
                .copied()
                .ok_or(OriginCaptureError("unreachable origin edge"))
        };
        let mut nodes = Vec::with_capacity(reachable.len());
        for (index, mut node) in self.nodes.into_iter().enumerate() {
            if !reachable.contains(&index) {
                continue;
            }
            match &mut node.core {
                Core::Paren(inner) => *inner = mapped(*inner)?,
                Core::App { head, args } => {
                    *head = mapped(*head)?;
                    for (_, child) in args {
                        *child = mapped(*child)?;
                    }
                }
                _ => {}
            }
            nodes.push(node);
        }
        let mut roots = self.roots;
        for root in &mut roots {
            match root {
                OriginRoot::Expression(availability) => remap_available(availability, &mapped)?,
                OriginRoot::Declaration { name, ty, value } => {
                    name.index = mapped(name.index)?;
                    remap_available(ty, &mapped)?;
                    remap_available(value, &mapped)?;
                }
            }
        }
        Ok(SourceOrigins {
            source: self.source,
            owner: self.owner,
            nodes,
            roots,
        })
    }
}

fn push_available(availability: &OriginAvailability, pending: &mut Vec<usize>) {
    if let OriginAvailability::Located(id) = availability {
        pending.push(id.index);
    }
}

fn remap_available(
    availability: &mut OriginAvailability,
    mapped: &impl Fn(usize) -> Result<usize, OriginCaptureError>,
) -> Result<(), OriginCaptureError> {
    if let OriginAvailability::Located(id) = availability {
        id.index = mapped(id.index)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests;
