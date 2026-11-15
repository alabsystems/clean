// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conservative support for the existing certificate rebinder. Target-specific
//! queries stay call-local; exhaustively FVar-free summaries may be reused
//! through a weak-owned memo within the enclosing inference call.
//! This is a transformation identity check, never a certificate validity check.

use super::closed_memo::RebindClosedMemo;
use crate::cert::{ProofCert, ZFCSetCertKind};
use crate::expr::{stack_safe, Expr, ExprKind, FVarId, ZFCSetExpr};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Copy, Default)]
pub(super) struct Support {
    // The fixed target FVar in a certificate leaf or transformed Expr field.
    may_abstract_fvar: bool,
    // Unlike may_abstract_fvar, this includes every FVar, not only the current
    // target. A false value is exhaustive only when no positive short-circuit
    // occurred; every such short-circuit necessarily sets this flag true.
    has_any_fvar: bool,
    // These bounds are complete only when may_abstract_fvar is false. A known
    // target forces unchanged_at=false at EVERY depth, so positive support may
    // stop without inspecting the remaining children or metadata fields.
    // u64 preserves the range of even a malformed certificate BVar(u32::MAX).
    loose_range: u64,
    binder_height: u64,
}

impl Support {
    fn join(&mut self, other: Self) {
        self.may_abstract_fvar |= other.may_abstract_fvar;
        self.has_any_fvar |= other.has_any_fvar;
        self.loose_range = self.loose_range.max(other.loose_range);
        self.binder_height = self.binder_height.max(other.binder_height);
    }

    fn under_binder(mut self) -> Self {
        self.loose_range = self.loose_range.saturating_sub(1);
        self.binder_height = self.binder_height.saturating_add(1);
        self
    }

    pub(super) fn unchanged_at(self, depth: u32) -> bool {
        !self.may_abstract_fvar
            && self.loose_range <= u64::from(depth)
            && self.binder_height <= u64::from(u32::MAX - depth)
    }

    pub(super) fn fvar_free(self) -> bool {
        !self.has_any_fvar && !self.may_abstract_fvar
    }
}

/// Target-specific maps borrow input nodes that remain live for one conversion.
/// Their identities and answers never escape that call. Only exhaustive
/// FVar-free summaries may enter the separate, weak-owned inference-local memo;
/// those summaries apply to every target but retain their depth conditions.
///
/// SOUNDNESS: a missing target FVar alone is insufficient: existing BVars shift,
/// including those in type fields. `loose_range` follows exactly the rebinder's
/// child-depth schedule. An Expr field is unchanged only when the fixed target
/// is absent AND its loose-BVar range fits the current depth. The exact target
/// query follows every Expr child, independently of binder depth: FVar IDs are
/// not captured by binders. Unrelated FVars are retained, never substituted.
/// `binder_height` additionally preserves the rebinder's
/// checked depth additions, even for otherwise closed certificates. All cases
/// not proven unchanged continue through the original affected-node converter.
/// Once the fixed target is positively found, no range or height can authorize
/// reuse. Only that positive case short-circuits; the affected converter still
/// visits every field and preserves its original checked index/depth behavior.
pub(super) struct SupportContext<'a, 'memo> {
    target: FVarId,
    memo: HashMap<*const ProofCert, (&'a Arc<ProofCert>, Support)>,
    // Only live borrowed input nodes, including boxed metadata roots. This is
    // scoped to ONE target and conversion, with both positive and negative hits.
    expr_memo: HashMap<*const Expr, (&'a Expr, bool)>,
    // Optional structural summaries shared across binder exits, but not across
    // outer inference calls. The per-target borrowed maps above stay unchanged.
    closed: Option<(&'memo mut RebindClosedMemo, usize)>,
}

impl<'a, 'memo> SupportContext<'a, 'memo> {
    pub(super) fn new(target: FVarId) -> Self {
        Self::with_closed_memo(target, None)
    }

    pub(super) fn with_closed_memo(
        target: FVarId,
        closed: Option<(&'memo mut RebindClosedMemo, usize)>,
    ) -> Self {
        Self {
            target,
            memo: HashMap::new(),
            expr_memo: HashMap::new(),
            closed,
        }
    }

    fn expression(&mut self, out: &mut Support, expr: &'a Expr) {
        out.has_any_fvar |= expr.has_fvar_quick();
        out.may_abstract_fvar = out.may_abstract_fvar || self.contains_target(expr);
        out.loose_range = out.loose_range.max(u64::from(expr.loose_bvar_range()));
    }

    /// Iterative existential query: a positive child settles its ancestors
    /// without walking their remaining siblings. A negative answer still
    /// requires every FVar-bearing child. The single stack contains only the
    /// active path and its next-child cursors, never pending sibling subtrees.
    /// Shared metadata DAGs retain exact positive/negative memo entries, and
    /// closed subgraphs need only the existing O(1) metadata flag.
    fn contains_target(&mut self, expr: &'a Expr) -> bool {
        if !expr.has_fvar_quick() {
            return false;
        }
        let root = std::ptr::from_ref(expr);
        if let Some((_, found)) = self.expr_memo.get(&root) {
            return *found;
        }
        let mut pending = vec![(expr, 0)];
        while let Some((node, next_child)) = pending.pop() {
            // One unit per resumption of the walk (`crate::work_meter`).
            crate::work_meter::charge(crate::work_meter::Walk::Fold, 1);
            let key = std::ptr::from_ref(node);
            if !node.has_fvar_quick() {
                continue;
            }
            let found = if let Some((_, found)) = self.expr_memo.get(&key) {
                Some(*found)
            } else if let ExprKind::FVar(id) = node.kind() {
                let found = *id == self.target;
                self.expr_memo.insert(key, (node, found));
                Some(found)
            } else {
                None
            };
            if let Some(found) = found {
                if found {
                    // Every pending node is an actual ancestor of this
                    // witness. Unvisited siblings receive NO memo entry.
                    for (ancestor, _) in pending {
                        self.expr_memo
                            .insert(std::ptr::from_ref(ancestor), (ancestor, true));
                    }
                    return true;
                }
                continue;
            }
            let children = expression_children(node);
            if let Some((index, child)) = children
                .into_iter()
                .enumerate()
                .skip(next_child)
                .find_map(|(index, child)| {
                    child
                        .filter(|child| child.has_fvar_quick())
                        .map(|child| (index, child))
                })
            {
                pending.push((node, index + 1));
                pending.push((child, 0));
            } else {
                // Resumption reaches the end only after every relevant child
                // returned false. A missing entry never establishes absence.
                self.expr_memo.insert(key, (node, false));
            }
        }
        self.expr_memo.get(&root).is_none_or(|(_, found)| *found)
    }

    pub(super) fn arc(&mut self, cert: &'a Arc<ProofCert>) -> Support {
        let key = Arc::as_ptr(cert);
        if let Some((_, support)) = self.memo.get(&key) {
            return *support;
        }
        if let Some((closed, _)) = &mut self.closed {
            if let Some(support) = closed.get(cert) {
                return support;
            }
        }
        let support = self.cert(cert);
        self.memo.insert(key, (cert, support));
        if let Some((closed, cap)) = &mut self.closed {
            closed.insert(cert, support, *cap);
        }
        support
    }

    // Root values are borrowed but not pointer-memoized. Only their actual Arc
    // children enter the map, avoiding any temporary-root identity assumptions.
    pub(super) fn cert(&mut self, cert: &'a ProofCert) -> Support {
        stack_safe(|| self.cert_inner(cert))
    }

    fn cert_inner(&mut self, cert: &'a ProofCert) -> Support {
        // One unit per certificate node summarized (`crate::work_meter`).
        crate::work_meter::charge(crate::work_meter::Walk::Fold, 1);
        #[cfg(test)]
        if let Some((closed, _)) = &mut self.closed {
            closed.visits += 1;
        }
        let mut out = Support::default();
        macro_rules! child {
            ($cert:expr) => {{
                out.join(self.arc($cert));
                if out.may_abstract_fvar {
                    return out;
                }
            }};
        }
        macro_rules! bound {
            ($cert:expr) => {{
                out.join(self.arc($cert).under_binder());
                if out.may_abstract_fvar {
                    return out;
                }
            }};
        }
        macro_rules! field {
            ($expr:expr) => {{
                self.expression(&mut out, $expr);
                if out.may_abstract_fvar {
                    return out;
                }
            }};
        }
        match cert {
            ProofCert::Sort { .. }
            | ProofCert::CubicalInterval
            | ProofCert::CubicalEndpoint { .. }
            | ProofCert::SProp => {}
            ProofCert::FVar { id, type_ } => {
                out.has_any_fvar = true;
                if *id == self.target {
                    return Support {
                        may_abstract_fvar: true,
                        has_any_fvar: true,
                        ..Support::default()
                    };
                }
                field!(type_);
            }
            ProofCert::BVar { idx, expected_type } => {
                out.loose_range = u64::from(*idx) + 1;
                field!(expected_type);
            }
            ProofCert::Const { type_, .. } | ProofCert::Lit { type_, .. } => field!(type_),
            ProofCert::App {
                fn_cert,
                fn_type,
                arg_cert,
                result_type,
            } => {
                child!(fn_cert);
                child!(arg_cert);
                field!(fn_type);
                field!(result_type);
            }
            ProofCert::Lam {
                arg_type_cert,
                body_cert,
                result_type,
                ..
            } => {
                child!(arg_type_cert);
                bound!(body_cert);
                field!(result_type);
            }
            ProofCert::Pi {
                arg_type_cert,
                body_type_cert,
                ..
            } => {
                child!(arg_type_cert);
                bound!(body_type_cert);
            }
            ProofCert::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => {
                child!(type_cert);
                child!(value_cert);
                bound!(body_cert);
                field!(result_type);
            }
            ProofCert::DefEq {
                inner,
                expected_type,
                actual_type,
                ..
            } => {
                child!(inner);
                field!(expected_type);
                field!(actual_type);
            }
            ProofCert::MData {
                inner_cert,
                result_type,
                ..
            } => {
                child!(inner_cert);
                field!(result_type);
            }
            ProofCert::Proj {
                expr_cert,
                expr_type,
                field_type,
                ..
            } => {
                child!(expr_cert);
                field!(expr_type);
                field!(field_type);
            }
            ProofCert::CubicalPath {
                ty_cert,
                left_cert,
                right_cert,
                ..
            } => {
                child!(ty_cert);
                child!(left_cert);
                child!(right_cert);
            }
            ProofCert::CubicalPathLam {
                body_cert,
                body_type,
                result_type,
            } => {
                bound!(body_cert);
                // Both metadata fields stay at the current depth, not depth+1.
                field!(body_type);
                field!(result_type);
            }
            ProofCert::CubicalPathApp {
                path_cert,
                arg_cert,
                path_type,
                result_type,
            } => {
                child!(path_cert);
                child!(arg_cert);
                field!(path_type);
                field!(result_type);
            }
            ProofCert::CubicalHComp {
                ty_cert,
                phi_cert,
                u_cert,
                base_cert,
                result_type,
            } => {
                child!(ty_cert);
                child!(phi_cert);
                child!(u_cert);
                child!(base_cert);
                field!(result_type);
            }
            ProofCert::CubicalTransp {
                ty_cert,
                phi_cert,
                base_cert,
                result_type,
            } => {
                child!(ty_cert);
                child!(phi_cert);
                child!(base_cert);
                field!(result_type);
            }
            ProofCert::CubicalCoe {
                ty_cert,
                r_cert,
                s_cert,
                base_cert,
                result_type,
            } => {
                child!(ty_cert);
                child!(r_cert);
                child!(s_cert);
                child!(base_cert);
                field!(result_type);
            }
            ProofCert::ZFCSet { kind, result_type } => {
                field!(result_type);
                match kind {
                    ZFCSetCertKind::Empty | ZFCSetCertKind::Infinity => {}
                    ZFCSetCertKind::Singleton(c)
                    | ZFCSetCertKind::Union(c)
                    | ZFCSetCertKind::PowerSet(c)
                    | ZFCSetCertKind::Choice(c) => child!(c),
                    ZFCSetCertKind::Pair(a, b) => {
                        child!(a);
                        child!(b);
                    }
                    ZFCSetCertKind::Separation {
                        set_cert,
                        pred_cert,
                    }
                    | ZFCSetCertKind::Replacement {
                        set_cert,
                        func_cert: pred_cert,
                    } => {
                        child!(set_cert);
                        bound!(pred_cert);
                    }
                }
            }
            ProofCert::ZFCMem {
                elem_cert,
                set_cert,
            } => {
                child!(elem_cert);
                child!(set_cert);
            }
            ProofCert::ZFCComprehension {
                var_ty_cert,
                pred_cert,
                result_type,
            } => {
                child!(var_ty_cert);
                bound!(pred_cert);
                field!(result_type);
            }
            ProofCert::Squash { inner_cert } => child!(inner_cert),
        }
        out
    }
}

/// The complete structural child census, with no recursive calls or per-node
/// child allocation. Metadata values and universe levels contain no Expr/FVar.
/// Keep this exhaustive so new expression constructors cannot silently skip
/// their target occurrences. Binder offsets belong to loose_bvar_range, not
/// the depth-independent FVar query.
fn expression_children(expr: &Expr) -> [Option<&Expr>; 4] {
    match expr.kind() {
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => [None; 4],
        ExprKind::App(a, b)
        | ExprKind::Lam(_, a, b)
        | ExprKind::Pi(_, a, b)
        | ExprKind::CubicalPathApp { path: a, arg: b }
        | ExprKind::ZFCMem { element: a, set: b }
        | ExprKind::ZFCComprehension { domain: a, pred: b } => [Some(a), Some(b), None, None],
        ExprKind::Let(_, ty, value, body, _) => [Some(ty), Some(value), Some(body), None],
        ExprKind::Proj(_, _, inner)
        | ExprKind::MData(_, inner)
        | ExprKind::Squash(inner)
        | ExprKind::CubicalPathLam { body: inner } => [Some(inner), None, None, None],
        ExprKind::CubicalPath { ty, left, right } => [Some(ty), Some(left), Some(right), None],
        ExprKind::CubicalHComp { ty, phi, u, base } => [Some(ty), Some(phi), Some(u), Some(base)],
        ExprKind::CubicalTransp { ty, phi, base } => [Some(ty), Some(phi), Some(base), None],
        ExprKind::CubicalCoe { ty, r, s, base } => [Some(ty), Some(r), Some(s), Some(base)],
        ExprKind::ZFCSet(set) => match set {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => [None; 4],
            ZFCSetExpr::Singleton(e)
            | ZFCSetExpr::Union(e)
            | ZFCSetExpr::PowerSet(e)
            | ZFCSetExpr::Choice(e) => [Some(e), None, None, None],
            ZFCSetExpr::Pair(a, b)
            | ZFCSetExpr::Separation { set: a, pred: b }
            | ZFCSetExpr::Replacement { set: a, func: b } => [Some(a), Some(b), None, None],
        },
    }
}

#[cfg(test)]
#[path = "rebind_support_tests.rs"]
mod tests;
