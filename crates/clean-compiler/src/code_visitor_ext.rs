// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended code visitor/folder for L5IR bodies.
//!
//! - `IRBodyVisitor` / `IRBodyFolder` — walk/transform `IRBody` nodes
//! - `IRExprVisitor` — walk expressions within declarations
//! - `TraversalOrder` — top-down vs bottom-up traversal
//! - `ScopeTracker` — carry scope (variable bindings) through traversal
//! - `SelectiveFilter` — visit only specific node categories
//! - `VarCollector` — accumulating visitor collecting variable references
//! - `independent_subtrees` — extract subtrees for parallel processing
//! - `compose_visitors` — chain multiple visitors in sequence
//! - `walk_with_stats` / `VisitStats` — statistics on visited/skipped nodes
//!
//! Part of #3083 - Extensibility.

use crate::ir::{IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use std::collections::HashMap;

/// Whether to process children before or after the current node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TraversalOrder {
    TopDown,
    BottomUp,
}

/// Category of IR node, used by `SelectiveFilter` and `VisitStats`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum NodeCategory {
    VDecl,
    JDecl,
    Inc,
    Dec,
    Set,
    SetTag,
    USet,
    SSet,
    Case,
    Jmp,
    Ret,
    Unreachable,
}

impl NodeCategory {
    pub(crate) fn of_body(body: &IRBody) -> Self {
        match body {
            IRBody::VDecl { .. } => Self::VDecl,
            IRBody::JDecl { .. } => Self::JDecl,
            IRBody::Inc { .. } => Self::Inc,
            IRBody::Dec { .. } => Self::Dec,
            IRBody::Set { .. } => Self::Set,
            IRBody::SetTag { .. } => Self::SetTag,
            IRBody::USet { .. } => Self::USet,
            IRBody::SSet { .. } => Self::SSet,
            IRBody::Case { .. } => Self::Case,
            IRBody::Jmp { .. } => Self::Jmp,
            IRBody::Ret(_) => Self::Ret,
            IRBody::Unreachable => Self::Unreachable,
        }
    }
}

/// Statistics gathered during a visitor pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct VisitStats {
    pub(crate) visited: HashMap<NodeCategory, u32>,
    pub(crate) transformed: u32,
    pub(crate) skipped: u32,
}

impl VisitStats {
    pub(crate) fn record_visit(&mut self, cat: NodeCategory) {
        *self.visited.entry(cat).or_insert(0) += 1;
    }
    pub(crate) fn record_transform(&mut self) {
        self.transformed += 1;
    }
    pub(crate) fn record_skip(&mut self) {
        self.skipped += 1;
    }
    pub(crate) fn total_visited(&self) -> u32 {
        self.visited.values().sum()
    }
}

// -- IRBodyVisitor -----------------------------------------------------------

/// Walk an `IRBody` tree, accumulating a result without modification.
pub(crate) trait IRBodyVisitor {
    type Result: Default;
    fn combine(&self, a: Self::Result, b: Self::Result) -> Self::Result;

    fn visit_vdecl(
        &mut self,
        _var: VarId,
        _ty: &IRType,
        _val: &IRExpr,
        rest: &IRBody,
    ) -> Self::Result {
        self.visit_body(rest)
    }
    fn visit_jdecl(
        &mut self,
        _jp: JoinPointId,
        _p: &[(VarId, IRType)],
        body: &IRBody,
        rest: &IRBody,
    ) -> Self::Result {
        let a = self.visit_body(body);
        let b = self.visit_body(rest);
        self.combine(a, b)
    }
    fn visit_inc(&mut self, _var: VarId, _n: u32, rest: &IRBody) -> Self::Result {
        self.visit_body(rest)
    }
    fn visit_dec(&mut self, _var: VarId, rest: &IRBody) -> Self::Result {
        self.visit_body(rest)
    }
    fn visit_case(&mut self, _s: VarId, alts: &[IRAlt], def: Option<&IRBody>) -> Self::Result {
        let mut r = Self::Result::default();
        for alt in alts {
            let v = self.visit_body(&alt.body);
            r = self.combine(r, v);
        }
        if let Some(d) = def {
            let v = self.visit_body(d);
            r = self.combine(r, v);
        }
        r
    }
    fn visit_jmp(&mut self, _jp: JoinPointId, _args: &[IRArg]) -> Self::Result {
        Self::Result::default()
    }
    fn visit_ret(&mut self, _arg: &IRArg) -> Self::Result {
        Self::Result::default()
    }
    fn visit_unreachable(&mut self) -> Self::Result {
        Self::Result::default()
    }

    fn visit_body(&mut self, body: &IRBody) -> Self::Result {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => self.visit_vdecl(*var, ty, value, rest),
            IRBody::JDecl {
                jp,
                params,
                body: b,
                rest,
            } => self.visit_jdecl(*jp, params, b, rest),
            IRBody::Inc { var, n, rest } => self.visit_inc(*var, *n, rest),
            IRBody::Dec { var, rest } => self.visit_dec(*var, rest),
            IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => self.visit_body(rest),
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => self.visit_case(*scrutinee, alts, default.as_deref()),
            IRBody::Jmp { jp, args } => self.visit_jmp(*jp, args),
            IRBody::Ret(arg) => self.visit_ret(arg),
            IRBody::Unreachable => self.visit_unreachable(),
        }
    }
}

// -- IRBodyFolder ------------------------------------------------------------

/// Transform an `IRBody` tree by rewriting nodes.
pub(crate) trait IRBodyFolder {
    fn fold_vdecl(&mut self, var: VarId, ty: IRType, val: IRExpr, rest: IRBody) -> IRBody {
        IRBody::VDecl {
            var,
            ty,
            value: val,
            rest: Box::new(self.fold_body(&rest)),
        }
    }
    fn fold_jdecl(
        &mut self,
        jp: JoinPointId,
        params: Vec<(VarId, IRType)>,
        body: IRBody,
        rest: IRBody,
    ) -> IRBody {
        IRBody::JDecl {
            jp,
            params,
            body: Box::new(self.fold_body(&body)),
            rest: Box::new(self.fold_body(&rest)),
        }
    }
    fn fold_inc(&mut self, var: VarId, n: u32, rest: IRBody) -> IRBody {
        IRBody::Inc {
            var,
            n,
            rest: Box::new(self.fold_body(&rest)),
        }
    }
    fn fold_dec(&mut self, var: VarId, rest: IRBody) -> IRBody {
        IRBody::Dec {
            var,
            rest: Box::new(self.fold_body(&rest)),
        }
    }
    fn fold_case(
        &mut self,
        scrutinee: VarId,
        alts: Vec<IRAlt>,
        default: Option<Box<IRBody>>,
    ) -> IRBody {
        let new_alts = alts
            .into_iter()
            .map(|a| IRAlt {
                ctor: a.ctor,
                body: Box::new(self.fold_body(&a.body)),
            })
            .collect();
        IRBody::Case {
            scrutinee,
            alts: new_alts,
            default: default.map(|d| Box::new(self.fold_body(&d))),
        }
    }
    fn fold_ret(&mut self, arg: IRArg) -> IRBody {
        IRBody::Ret(arg)
    }
    fn fold_jmp(&mut self, jp: JoinPointId, args: Vec<IRArg>) -> IRBody {
        IRBody::Jmp { jp, args }
    }
    fn fold_unreachable(&mut self) -> IRBody {
        IRBody::Unreachable
    }

    fn fold_body(&mut self, body: &IRBody) -> IRBody {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => self.fold_vdecl(*var, ty.clone(), value.clone(), *rest.clone()),
            IRBody::JDecl {
                jp,
                params,
                body: b,
                rest,
            } => self.fold_jdecl(*jp, params.clone(), *b.clone(), *rest.clone()),
            IRBody::Inc { var, n, rest } => self.fold_inc(*var, *n, *rest.clone()),
            IRBody::Dec { var, rest } => self.fold_dec(*var, *rest.clone()),
            IRBody::Set {
                var,
                idx,
                value,
                rest,
            } => IRBody::Set {
                var: *var,
                idx: *idx,
                value: *value,
                rest: Box::new(self.fold_body(rest)),
            },
            IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
                var: *var,
                tag: *tag,
                rest: Box::new(self.fold_body(rest)),
            },
            IRBody::USet {
                var,
                idx,
                value,
                rest,
            } => IRBody::USet {
                var: *var,
                idx: *idx,
                value: *value,
                rest: Box::new(self.fold_body(rest)),
            },
            IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => IRBody::SSet {
                var: *var,
                n: *n,
                offset: *offset,
                value: *value,
                ty: ty.clone(),
                rest: Box::new(self.fold_body(rest)),
            },
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => self.fold_case(*scrutinee, alts.clone(), default.clone()),
            IRBody::Jmp { jp, args } => self.fold_jmp(*jp, args.clone()),
            IRBody::Ret(arg) => self.fold_ret(arg.clone()),
            IRBody::Unreachable => self.fold_unreachable(),
        }
    }
}

// -- IRExprVisitor -----------------------------------------------------------

/// Walk `IRExpr` nodes to collect information.
pub(crate) trait IRExprVisitor {
    type Result: Default;

    fn visit_ctor(&mut self, _args: &[IRArg]) -> Self::Result {
        Self::Result::default()
    }
    fn visit_proj(&mut self, _idx: u32, _ty: &IRType, _arg: &IRArg) -> Self::Result {
        Self::Result::default()
    }
    fn visit_apply(&mut self, _args: &[IRArg]) -> Self::Result {
        Self::Result::default()
    }
    fn visit_lit(&mut self) -> Self::Result {
        Self::Result::default()
    }
    fn visit_other(&mut self) -> Self::Result {
        Self::Result::default()
    }

    fn visit_expr(&mut self, expr: &IRExpr) -> Self::Result {
        match expr {
            IRExpr::Ctor { args, .. } => self.visit_ctor(args),
            IRExpr::Proj { idx, ty, arg } => self.visit_proj(*idx, ty, arg),
            IRExpr::Apply { args, .. } => self.visit_apply(args),
            IRExpr::Lit(_) | IRExpr::String(_) => self.visit_lit(),
            _ => self.visit_other(),
        }
    }
}

// -- ScopeTracker ------------------------------------------------------------

/// Tracks variable bindings in scope during an `IRBody` traversal.
#[derive(Debug, Clone, Default)]
pub(crate) struct ScopeTracker {
    pub(crate) bindings: HashMap<VarId, IRType>,
    pub(crate) join_points: HashMap<JoinPointId, Vec<(VarId, IRType)>>,
    pub(crate) depth: u32,
}

impl ScopeTracker {
    pub(crate) fn enter_vdecl(&mut self, var: VarId, ty: &IRType) {
        self.bindings.insert(var, ty.clone());
    }
    pub(crate) fn enter_jdecl(&mut self, jp: JoinPointId, params: &[(VarId, IRType)]) {
        self.join_points.insert(jp, params.to_vec());
        for (v, t) in params {
            self.bindings.insert(*v, t.clone());
        }
        self.depth += 1;
    }
    pub(crate) fn exit_jdecl(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }
    pub(crate) fn is_bound(&self, var: VarId) -> bool {
        self.bindings.contains_key(&var)
    }
    pub(crate) fn lookup(&self, var: VarId) -> Option<&IRType> {
        self.bindings.get(&var)
    }
}

// -- SelectiveFilter ---------------------------------------------------------

/// A filter that restricts which node categories are visited.
#[derive(Debug, Clone)]
pub(crate) struct SelectiveFilter {
    allowed: std::collections::HashSet<NodeCategory>,
}

impl SelectiveFilter {
    pub(crate) fn new(categories: &[NodeCategory]) -> Self {
        Self {
            allowed: categories.iter().copied().collect(),
        }
    }
    pub(crate) fn allows(&self, body: &IRBody) -> bool {
        self.allowed.contains(&NodeCategory::of_body(body))
    }
    pub(crate) fn all() -> Self {
        use NodeCategory::*;
        Self::new(&[
            VDecl,
            JDecl,
            Inc,
            Dec,
            Set,
            SetTag,
            USet,
            SSet,
            Case,
            Jmp,
            Ret,
            Unreachable,
        ])
    }
}

// -- VarCollector (accumulating visitor) -------------------------------------

/// Collects all `VarId`s referenced in an `IRBody`.
pub(crate) struct VarCollector {
    pub(crate) vars: Vec<VarId>,
}

impl VarCollector {
    pub(crate) fn new() -> Self {
        Self { vars: Vec::new() }
    }

    /// Collect all variable references from an `IRBody`.
    pub(crate) fn collect(body: &IRBody) -> Vec<VarId> {
        let mut c = Self::new();
        c.walk(body);
        c.vars
    }

    fn record_arg(&mut self, arg: &IRArg) {
        if let IRArg::Var(v) = arg {
            self.vars.push(*v);
        }
    }

    fn walk(&mut self, body: &IRBody) {
        match body {
            IRBody::VDecl {
                var, value, rest, ..
            } => {
                self.vars.push(*var);
                self.walk_expr(value);
                self.walk(rest);
            }
            IRBody::JDecl {
                params, body, rest, ..
            } => {
                for (v, _) in params {
                    self.vars.push(*v);
                }
                self.walk(body);
                self.walk(rest);
            }
            IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => {
                self.vars.push(*var);
                self.walk(rest);
            }
            IRBody::Set {
                var, value, rest, ..
            }
            | IRBody::USet {
                var, value, rest, ..
            }
            | IRBody::SSet {
                var, value, rest, ..
            } => {
                self.vars.push(*var);
                self.vars.push(*value);
                self.walk(rest);
            }
            IRBody::SetTag { var, rest, .. } => {
                self.vars.push(*var);
                self.walk(rest);
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                self.vars.push(*scrutinee);
                for alt in alts {
                    self.walk(&alt.body);
                }
                if let Some(d) = default {
                    self.walk(d);
                }
            }
            IRBody::Jmp { args, .. } => {
                for a in args {
                    self.record_arg(a);
                }
            }
            IRBody::Ret(arg) => self.record_arg(arg),
            IRBody::Unreachable => {}
        }
    }

    fn walk_expr(&mut self, expr: &IRExpr) {
        match expr {
            IRExpr::Ctor { args, .. }
            | IRExpr::Apply { args, .. }
            | IRExpr::PartialApply { args, .. }
            | IRExpr::ClosureApply { args, .. } => {
                for a in args {
                    self.record_arg(a);
                }
            }
            IRExpr::Proj { arg, .. }
            | IRExpr::Tag(arg)
            | IRExpr::Box { arg, .. }
            | IRExpr::Unbox { arg, .. } => self.record_arg(arg),
            IRExpr::UProj { var, .. }
            | IRExpr::SProj { var, .. }
            | IRExpr::IsShared(var)
            | IRExpr::Reset(var) => self.vars.push(*var),
            IRExpr::Reuse { var, args, .. } => {
                self.vars.push(*var);
                for a in args {
                    self.record_arg(a);
                }
            }
            IRExpr::Lit(_) | IRExpr::String(_) => {}
        }
    }
}

// -- Parallel subtree extraction ---------------------------------------------

/// Extract independent subtrees from an `IRBody` for parallel processing.
pub(crate) fn independent_subtrees(body: &IRBody) -> Vec<&IRBody> {
    match body {
        IRBody::Case { alts, default, .. } => {
            let mut t: Vec<&IRBody> = alts.iter().map(|a| a.body.as_ref()).collect();
            if let Some(d) = default {
                t.push(d.as_ref());
            }
            t
        }
        IRBody::JDecl { body, rest, .. } => vec![body.as_ref(), rest.as_ref()],
        _ => Vec::new(),
    }
}

// -- Composed visitors -------------------------------------------------------

/// Run two `IRBodyVisitor`s in sequence over the same body, returning both results.
pub(crate) fn compose_visitors<A, B>(a: &mut A, b: &mut B, body: &IRBody) -> (A::Result, B::Result)
where
    A: IRBodyVisitor,
    B: IRBodyVisitor,
{
    (a.visit_body(body), b.visit_body(body))
}

// -- walk_with_stats ---------------------------------------------------------

/// Walk an `IRBody` with configurable order, selective filter, and stats tracking.
pub(crate) fn walk_with_stats<F>(
    body: &IRBody,
    order: TraversalOrder,
    filter: &SelectiveFilter,
    stats: &mut VisitStats,
    visitor: &mut F,
) where
    F: FnMut(&IRBody),
{
    let allowed = filter.allows(body);
    if !allowed {
        stats.record_skip();
    }
    if allowed && order == TraversalOrder::TopDown {
        stats.record_visit(NodeCategory::of_body(body));
        visitor(body);
    }
    // Recurse into children.
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            walk_with_stats(rest, order, filter, stats, visitor);
        }
        IRBody::JDecl { body: b, rest, .. } => {
            walk_with_stats(b, order, filter, stats, visitor);
            walk_with_stats(rest, order, filter, stats, visitor);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                walk_with_stats(&alt.body, order, filter, stats, visitor);
            }
            if let Some(d) = default {
                walk_with_stats(d, order, filter, stats, visitor);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
    if allowed && order == TraversalOrder::BottomUp {
        stats.record_visit(NodeCategory::of_body(body));
        visitor(body);
    }
}

/// Walk all expressions within an `IRDecl`.
pub(crate) fn visit_decl_exprs<F>(decl: &IRDecl, visitor: &mut F)
where
    F: FnMut(&IRExpr),
{
    visit_body_exprs(&decl.body, visitor);
}

fn visit_body_exprs<F>(body: &IRBody, visitor: &mut F)
where
    F: FnMut(&IRExpr),
{
    match body {
        IRBody::VDecl { value, rest, .. } => {
            visitor(value);
            visit_body_exprs(rest, visitor);
        }
        IRBody::JDecl { body: b, rest, .. } => {
            visit_body_exprs(b, visitor);
            visit_body_exprs(rest, visitor);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => visit_body_exprs(rest, visitor),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                visit_body_exprs(&alt.body, visitor);
            }
            if let Some(d) = default {
                visit_body_exprs(d, visitor);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}
