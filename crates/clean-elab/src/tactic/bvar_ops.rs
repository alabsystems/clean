// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared BVar operations for tactic code.

use crate::stack_safe;
use clean_kernel::{Expr, ExprFolderOpt};

enum BVarMode<'a> {
    Lift { offset: i64, depth: u32 },
    HasLoose { idx: u32 },
    Instantiate { replacement: &'a Expr, depth: u32 },
    Abstract { target: &'a Expr, depth: u32 },
}

pub(crate) struct BVarFolder<'a> {
    mode: BVarMode<'a>,
    binder_depth: u32,
    found: bool,
}

impl<'a> BVarFolder<'a> {
    fn lift(offset: i64, depth: u32) -> Self {
        Self {
            mode: BVarMode::Lift { offset, depth },
            binder_depth: 0,
            found: false,
        }
    }

    fn has_loose(idx: u32) -> Self {
        Self {
            mode: BVarMode::HasLoose { idx },
            binder_depth: 0,
            found: false,
        }
    }

    fn instantiate(replacement: &'a Expr, depth: u32) -> Self {
        Self {
            mode: BVarMode::Instantiate { replacement, depth },
            binder_depth: 0,
            found: false,
        }
    }

    fn abstract_(target: &'a Expr, depth: u32) -> Self {
        Self {
            mode: BVarMode::Abstract { target, depth },
            binder_depth: 0,
            found: false,
        }
    }

    fn current_depth(&self, base_depth: u32) -> u32 {
        base_depth.saturating_add(self.binder_depth)
    }

    fn shift_idx(idx: u32, offset: i64) -> u32 {
        if offset >= 0 {
            let delta = u32::try_from(offset).unwrap_or(u32::MAX);
            idx.saturating_add(delta)
        } else {
            let delta = u32::try_from(offset.unsigned_abs()).unwrap_or(u32::MAX);
            debug_assert!(
                idx >= delta,
                "lift_bvar underflow: idx={idx}, offset={offset}"
            );
            idx.saturating_sub(delta)
        }
    }
}

impl ExprFolderOpt for BVarFolder<'_> {
    fn should_descend(&self, expr: &Expr) -> bool {
        match &self.mode {
            BVarMode::Lift { offset, depth } => {
                *offset != 0 && self.current_depth(*depth) < expr.loose_bvar_range()
            }
            BVarMode::HasLoose { idx } => {
                !self.found && idx.saturating_add(self.binder_depth) < expr.loose_bvar_range()
            }
            BVarMode::Instantiate { depth, .. } => {
                self.current_depth(*depth) < expr.loose_bvar_range()
            }
            BVarMode::Abstract { .. } => true,
        }
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if let BVarMode::Abstract { target, depth } = &self.mode {
            if expr == *target {
                return Some(Expr::bvar(self.current_depth(*depth)));
            }
        }
        if !self.should_descend(expr) {
            return None;
        }
        stack_safe(|| ExprFolderOpt::fold_expr_opt_inner(self, expr))
    }

    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        match &self.mode {
            BVarMode::Lift { offset, depth } => {
                let cutoff = self.current_depth(*depth);
                (idx >= cutoff).then(|| Expr::bvar(Self::shift_idx(idx, *offset)))
            }
            BVarMode::HasLoose { idx: target_idx } => {
                if idx == target_idx.saturating_add(self.binder_depth) {
                    self.found = true;
                }
                None
            }
            BVarMode::Instantiate { replacement, depth } => {
                let target = self.current_depth(*depth);
                if idx == target {
                    Some(replacement.lift(self.binder_depth))
                } else if idx > target {
                    Some(Expr::bvar(idx - 1))
                } else {
                    None
                }
            }
            BVarMode::Abstract { depth, .. } => {
                let cutoff = self.current_depth(*depth);
                (idx >= cutoff).then(|| Expr::bvar(idx.saturating_add(1)))
            }
        }
    }

    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        let saved = self.binder_depth;
        self.binder_depth = self.binder_depth.saturating_add(1);
        let result = self.fold_expr_opt(expr);
        self.binder_depth = saved;
        result
    }
}

pub(crate) fn lift_bvar(expr: &Expr, offset: i64, depth: u32) -> Expr {
    if offset == 0 {
        return expr.clone();
    }
    expr.fold_opt_or_clone(&mut BVarFolder::lift(offset, depth))
}

pub(crate) fn has_loose_bvar(expr: &Expr, idx: u32) -> bool {
    let mut folder = BVarFolder::has_loose(idx);
    folder.fold_expr_opt(expr);
    folder.found
}

pub(crate) fn instantiate_bvar(expr: &Expr, replacement: &Expr, depth: u32) -> Expr {
    expr.fold_opt_or_clone(&mut BVarFolder::instantiate(replacement, depth))
}

pub(crate) fn abstract_bvar(expr: &Expr, target: &Expr, depth: u32) -> Expr {
    expr.fold_opt_or_clone(&mut BVarFolder::abstract_(target, depth))
}

pub(crate) fn instantiate(body: &Expr, arg: &Expr) -> Expr {
    instantiate_bvar(body, arg, 0)
}

pub(crate) fn instantiate_at(body: &Expr, arg: &Expr, idx: u32) -> Expr {
    instantiate_bvar(body, arg, idx)
}

pub(crate) fn abstract_over(expr: &Expr, target: &Expr) -> Expr {
    abstract_bvar(expr, target, 0)
}

pub(crate) fn lift_bvars(expr: &Expr, amount: u32) -> Expr {
    lift_bvar(expr, i64::from(amount), 0)
}

pub(crate) fn lift_bvars_from(expr: &Expr, start: u32, amount: u32) -> Expr {
    lift_bvar(expr, i64::from(amount), start)
}

pub(crate) fn lower_bvars(expr: &Expr, amount: u32) -> Expr {
    lift_bvar(expr, -i64::from(amount), 0)
}

pub(crate) fn has_free_bvar(expr: &Expr, idx: u32) -> bool {
    has_loose_bvar(expr, idx)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::stack_safe;
    use clean_kernel::{BinderInfo, ExprKind, Name};

    fn legacy_substitute_bvar(expr: &Expr, idx: u32, replacement: &Expr) -> Expr {
        struct Folder<'a> {
            idx: u32,
            replacement: &'a Expr,
            depth: u32,
        }

        impl ExprFolderOpt for Folder<'_> {
            fn should_descend(&self, expr: &Expr) -> bool {
                self.idx.saturating_add(self.depth) < expr.loose_bvar_range()
            }

            fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
                let target = self.idx.saturating_add(self.depth);
                if idx == target {
                    Some(self.replacement.lift(self.depth))
                } else if idx > target {
                    Some(Expr::bvar(idx - 1))
                } else {
                    None
                }
            }

            fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
                let saved = self.depth;
                self.depth = self.depth.saturating_add(1);
                let result = self.fold_expr_opt(expr);
                self.depth = saved;
                result
            }
        }

        expr.fold_opt_or_clone(&mut Folder {
            idx,
            replacement,
            depth: 0,
        })
    }

    fn legacy_shift_expr(expr: &Expr, amount: i64, cutoff: u32) -> Expr {
        struct Folder {
            amount: i64,
            cutoff: u32,
        }

        impl ExprFolderOpt for Folder {
            fn should_descend(&self, expr: &Expr) -> bool {
                self.cutoff < expr.loose_bvar_range()
            }

            fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
                if idx < self.cutoff {
                    return None;
                }
                Some(Expr::bvar(BVarFolder::shift_idx(idx, self.amount)))
            }

            fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
                let saved = self.cutoff;
                self.cutoff = self.cutoff.saturating_add(1);
                let result = self.fold_expr_opt(expr);
                self.cutoff = saved;
                result
            }
        }

        expr.fold_opt_or_clone(&mut Folder { amount, cutoff })
    }

    fn legacy_contains_bvar(expr: &Expr, idx: u32) -> bool {
        struct Folder {
            idx: u32,
            depth: u32,
            found: bool,
        }

        impl ExprFolderOpt for Folder {
            fn should_descend(&self, expr: &Expr) -> bool {
                !self.found && self.idx.saturating_add(self.depth) < expr.loose_bvar_range()
            }

            fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
                if idx == self.idx.saturating_add(self.depth) {
                    self.found = true;
                }
                None
            }

            fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
                let saved = self.depth;
                self.depth = self.depth.saturating_add(1);
                let result = self.fold_expr_opt(expr);
                self.depth = saved;
                result
            }
        }

        let mut folder = Folder {
            idx,
            depth: 0,
            found: false,
        };
        folder.fold_expr_opt(expr);
        folder.found
    }

    fn legacy_abstract_over(expr: &Expr, target: &Expr, depth: u32) -> Expr {
        fn go(expr: &Expr, target: &Expr, depth: u32) -> Expr {
            stack_safe(|| {
                if expr == target {
                    return Expr::bvar(depth);
                }
                match expr.kind() {
                    ExprKind::App(f, a) => Expr::app(go(f, target, depth), go(a, target, depth)),
                    ExprKind::Lam(bi, ty, body) => {
                        Expr::lam(*bi, go(ty, target, depth), go(body, target, depth + 1))
                    }
                    ExprKind::Pi(bi, ty, body) => {
                        Expr::pi(*bi, go(ty, target, depth), go(body, target, depth + 1))
                    }
                    ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
                        name.clone(),
                        go(ty, target, depth),
                        go(val, target, depth),
                        go(body, target, depth + 1),
                        *non_dep,
                    ),
                    ExprKind::Proj(name, idx, inner) => {
                        Expr::proj(name.clone(), *idx, go(inner, target, depth))
                    }
                    ExprKind::MData(md, inner) => Expr::mdata(md.clone(), go(inner, target, depth)),
                    ExprKind::Squash(inner) => {
                        Expr::from_kind(ExprKind::Squash(Arc::new(go(inner, target, depth))))
                    }
                    ExprKind::BVar(i) => Expr::bvar((*i).saturating_add(u32::from(*i >= depth))),
                    _ => expr.clone(),
                }
            })
        }

        go(expr, target, depth)
    }

    #[test]
    fn instantiate_bvar_matches_legacy_substitute_bvar() {
        let arg = Expr::const_(Name::from_string("a"), vec![]);
        let body = Expr::proj(
            Name::from_string("Prod.fst"),
            0,
            Expr::mdata(
                vec![],
                Expr::lam(
                    BinderInfo::Default,
                    Expr::type_(),
                    Expr::app(Expr::bvar(2), Expr::app(Expr::bvar(1), Expr::bvar(0))),
                ),
            ),
        );

        assert_eq!(
            instantiate_bvar(&body, &arg, 0),
            legacy_substitute_bvar(&body, 0, &arg)
        );
        assert_eq!(
            instantiate_bvar(&body, &arg, 1),
            legacy_substitute_bvar(&body, 1, &arg)
        );
    }

    #[test]
    fn lift_bvar_matches_legacy_shift_expr() {
        let expr = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::app(
                Expr::proj(Name::from_string("Prod.snd"), 1, Expr::bvar(1)),
                Expr::mdata(vec![], Expr::bvar(2)),
            ),
        );

        assert_eq!(lift_bvar(&expr, 2, 0), legacy_shift_expr(&expr, 2, 0));
        assert_eq!(lift_bvar(&expr, -1, 0), legacy_shift_expr(&expr, -1, 0));
        assert_eq!(lift_bvar(&expr, 3, 1), legacy_shift_expr(&expr, 3, 1));
    }

    #[test]
    fn has_loose_bvar_matches_legacy_contains_bvar() {
        let expr = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::app(
                Expr::bvar(0),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::type_(),
                    Expr::app(Expr::bvar(2), Expr::bvar(0)),
                ),
            ),
        );

        assert_eq!(has_loose_bvar(&expr, 0), legacy_contains_bvar(&expr, 0));
        assert_eq!(has_loose_bvar(&expr, 1), legacy_contains_bvar(&expr, 1));
        assert_eq!(has_loose_bvar(&expr, 2), legacy_contains_bvar(&expr, 2));
    }

    #[test]
    fn abstract_bvar_matches_legacy_abstract_over() {
        let target = Expr::const_(Name::from_string("a"), vec![]);
        let expr = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::app(
                Expr::proj(
                    Name::from_string("Prod.fst"),
                    0,
                    Expr::mdata(vec![], target.clone()),
                ),
                Expr::from_kind(ExprKind::Squash(Arc::new(Expr::app(
                    target.clone(),
                    Expr::bvar(0),
                )))),
            ),
        );

        assert_eq!(
            abstract_bvar(&expr, &target, 0),
            legacy_abstract_over(&expr, &target, 0)
        );
        assert_eq!(
            abstract_bvar(&expr, &target, 1),
            legacy_abstract_over(&expr, &target, 1)
        );
    }
}
