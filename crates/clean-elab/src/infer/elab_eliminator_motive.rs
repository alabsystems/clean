// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lean KAbstract's all-occurrence motive abstraction for ordinary eliminators.

use super::*;
use clean_kernel::ExprFolderOpt;

fn head_num_args(mut expr: &Expr) -> usize {
    let mut count = 0;
    loop {
        match expr.kind() {
            ExprKind::App(function, _) => {
                count += 1;
                expr = function;
            }
            ExprKind::Let(_, _, _, body, _) | ExprKind::MData(_, body) => expr = body,
            _ => return count,
        }
    }
}

fn head_index(mut expr: Expr) -> Expr {
    // Usually the let value cannot affect the head key. Substitute only
    // when the cheap traversal reaches a bound variable, as Lean does.
    let mut quick = &expr;
    loop {
        match quick.kind() {
            ExprKind::App(function, _) | ExprKind::MData(_, function) => quick = function,
            ExprKind::Let(_, _, _, body, _) => quick = body,
            ExprKind::BVar(_) => break,
            _ => return quick.clone(),
        }
    }
    loop {
        expr = match expr.kind() {
            ExprKind::App(function, _) | ExprKind::MData(_, function) => function.as_ref().clone(),
            ExprKind::Let(_, _, value, body, _) => body.instantiate(value),
            _ => return expr,
        };
    }
}

fn same_head_index(left: &Expr, right: &Expr) -> bool {
    match (left.kind(), right.kind()) {
        (ExprKind::Const(a, _), ExprKind::Const(b, _)) => a == b,
        (ExprKind::FVar(a), ExprKind::FVar(b)) => a == b,
        (ExprKind::Proj(a, i, _), ExprKind::Proj(b, j, _)) => a == b && i == j,
        (ExprKind::Sort(_), ExprKind::Sort(_))
        | (ExprKind::Lam(..), ExprKind::Lam(..))
        | (ExprKind::Pi(..), ExprKind::Pi(..)) => true,
        _ => left == right,
    }
}

struct MotiveAbstraction<'ctx, 'env> {
    context: &'ctx ElabCtx<'env>,
    pattern: &'ctx Expr,
    head: Expr,
    num_args: usize,
    depth: u32,
}

impl ExprFolderOpt for MotiveAbstraction<'_, '_> {
    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !expr.has_loose_bvars()
            && head_num_args(expr) == self.num_args
            && same_head_index(&head_index(expr.clone()), &self.head)
        {
            let pending = self.context.pending_level_assigns.borrow().clone();
            if self.context.is_def_eq(expr, self.pattern) {
                if *self.context.pending_level_assigns.borrow() != pending {
                    self.context.tc_caches.replace(TcCaches::default());
                }
                return Some(Expr::bvar(self.depth));
            }
            // Failed def-eq probes cannot constrain another occurrence.
            self.context.pending_level_assigns.replace(pending);
            self.context.tc_caches.replace(TcCaches::default());
        }
        stack_safe(|| ExprFolderOpt::fold_expr_opt_inner(self, expr))
    }

    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        self.depth += 1;
        let result = self.fold_expr_opt(expr);
        self.depth -= 1;
        result
    }
}

impl ElabCtx<'_> {
    pub(super) fn abstract_eliminator_motive(&mut self, expected: &Expr, major: &Expr) -> Expr {
        let major = self
            .metas
            .instantiate_levels(&self.metas.instantiate(major));
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(expected));
        if let ExprKind::FVar(id) = major.kind() {
            if MetaState::from_fvar(*id).is_none() {
                return expected.abstract_fvar(*id);
            }
        }
        let body = expected.fold_opt_or_clone(&mut MotiveAbstraction {
            context: self,
            pattern: &major,
            head: head_index(major.clone()),
            num_args: head_num_args(&major),
            depth: 0,
        });
        self.commit_pending_level_assigns();
        self.metas
            .instantiate_levels(&self.metas.instantiate(&body))
    }
}
