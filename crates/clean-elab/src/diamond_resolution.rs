// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Diamond detection for type class hierarchies.
//!
//! A class hierarchy contains a diamond when a target class reaches the same
//! ancestor through two or more distinct superclass chains. That can make
//! instance resolution ambiguous unless every path yields the same instance
//! expression. This module enumerates those paths, records the known instance
//! expressions associated with the diamond class, and provides coherence checks
//! before resolution commits to one path.

use crate::stack_safe;
use clean_kernel::expr::{Expr, ExprKind};
use std::collections::{HashMap, HashSet, VecDeque};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DiamondPath {
    pub(crate) through: Vec<String>,
    pub(crate) instance_expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Diamond {
    pub(crate) class_name: String,
    pub(crate) instance_paths: Vec<DiamondPath>,
    pub(crate) resolved: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstanceEntry {
    pub(crate) name: String,
    pub(crate) class: String,
    pub(crate) type_args: Vec<Expr>,
    pub(crate) instance_expr: Expr,
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub(crate) enum DiamondError {
    #[error("incoherent instances for class `{class}` across {path_count} paths")]
    IncoherentInstances { class: String, path_count: usize },
    #[error("no superclass paths from `{from}` to `{to}`")]
    NoPaths { from: String, to: String },
    #[error("unknown class `{0}`")]
    UnknownClass(String),
}

#[derive(Debug, Default)]
pub(crate) struct DiamondDetector {
    pub(crate) class_hierarchy: HashMap<String, Vec<String>>,
    pub(crate) known_instances: HashMap<String, Vec<InstanceEntry>>,
}

impl DiamondDetector {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn register_superclass(&mut self, class: &str, superclass: &str) {
        let superclass = superclass.to_owned();
        let entry = self.class_hierarchy.entry(class.to_owned()).or_default();
        if !entry.iter().any(|existing| existing == &superclass) {
            entry.push(superclass.clone());
        }
        self.class_hierarchy.entry(superclass).or_default();
    }

    pub(crate) fn register_instance(&mut self, entry: InstanceEntry) {
        self.class_hierarchy.entry(entry.class.clone()).or_default();
        self.known_instances
            .entry(entry.class.clone())
            .or_default()
            .push(entry);
    }

    pub(crate) fn detect_diamonds(&self, target_class: &str) -> Vec<Diamond> {
        let mut ancestors: Vec<_> = self.all_ancestors(target_class).into_iter().collect();
        ancestors.sort();

        let mut diamonds = Vec::new();
        for ancestor in ancestors {
            let paths = self.find_all_paths(target_class, &ancestor);
            if paths.len() < 2 {
                continue;
            }

            diamonds.push(Diamond {
                class_name: ancestor.clone(),
                instance_paths: self.build_diamond_paths(&ancestor, paths),
                resolved: false,
            });
        }

        diamonds
    }

    pub(crate) fn check_diamond_coherence(&self, diamond: &Diamond) -> Result<(), DiamondError> {
        self.ensure_known_class(&diamond.class_name)?;
        let Some(first) = diamond.instance_paths.first() else {
            return Err(self.no_paths_error(diamond));
        };

        if diamond
            .instance_paths
            .iter()
            .skip(1)
            .all(|path| structural_expr_eq(&first.instance_expr, &path.instance_expr))
        {
            Ok(())
        } else {
            Err(DiamondError::IncoherentInstances {
                class: diamond.class_name.clone(),
                path_count: diamond.instance_paths.len(),
            })
        }
    }

    pub(crate) fn find_all_paths(&self, from: &str, to: &str) -> Vec<Vec<String>> {
        let mut paths = Vec::new();
        let mut current_path = vec![from.to_owned()];
        let mut visiting = HashSet::new();
        self.find_all_paths_dfs(from, to, &mut visiting, &mut current_path, &mut paths);
        paths.sort_by(|left, right| left.len().cmp(&right.len()).then_with(|| left.cmp(right)));
        paths
    }

    pub(crate) fn resolve_diamond(
        &self,
        diamond: &mut Diamond,
        unifier: &dyn Fn(&Expr, &Expr) -> bool,
    ) -> Result<(), DiamondError> {
        self.ensure_known_class(&diamond.class_name)?;
        let Some(first) = diamond.instance_paths.first() else {
            return Err(self.no_paths_error(diamond));
        };

        if diamond
            .instance_paths
            .iter()
            .skip(1)
            .all(|path| unifier(&first.instance_expr, &path.instance_expr))
        {
            diamond.resolved = true;
            Ok(())
        } else {
            Err(DiamondError::IncoherentInstances {
                class: diamond.class_name.clone(),
                path_count: diamond.instance_paths.len(),
            })
        }
    }

    pub(crate) fn superclasses(&self, class: &str) -> Vec<&str> {
        self.class_hierarchy
            .get(class)
            .map(|superclasses| superclasses.iter().map(String::as_str).collect())
            .unwrap_or_default()
    }

    pub(crate) fn all_ancestors(&self, class: &str) -> HashSet<String> {
        let mut ancestors = HashSet::new();
        let mut queue = VecDeque::new();

        for superclass in self.superclasses(class) {
            queue.push_back(superclass.to_owned());
        }

        while let Some(current) = queue.pop_front() {
            if !ancestors.insert(current.clone()) {
                continue;
            }
            for superclass in self.superclasses(&current) {
                if !ancestors.contains(superclass) {
                    queue.push_back(superclass.to_owned());
                }
            }
        }

        ancestors
    }

    fn build_diamond_paths(&self, class_name: &str, paths: Vec<Vec<String>>) -> Vec<DiamondPath> {
        let Some(entries) = self.known_instances.get(class_name) else {
            return Vec::new();
        };
        if entries.is_empty() {
            return Vec::new();
        }

        paths
            .into_iter()
            .enumerate()
            .map(|(index, through)| {
                let entry = &entries[index % entries.len()];
                DiamondPath {
                    through,
                    instance_expr: entry.instance_expr.clone(),
                }
            })
            .collect()
    }

    fn ensure_known_class(&self, class: &str) -> Result<(), DiamondError> {
        if self.class_hierarchy.contains_key(class) || self.known_instances.contains_key(class) {
            Ok(())
        } else {
            Err(DiamondError::UnknownClass(class.to_owned()))
        }
    }

    fn no_paths_error(&self, diamond: &Diamond) -> DiamondError {
        let from = diamond
            .instance_paths
            .first()
            .and_then(|path| path.through.first())
            .cloned()
            .unwrap_or_else(|| diamond.class_name.clone());
        DiamondError::NoPaths {
            from,
            to: diamond.class_name.clone(),
        }
    }

    fn find_all_paths_dfs(
        &self,
        current: &str,
        target: &str,
        visiting: &mut HashSet<String>,
        current_path: &mut Vec<String>,
        paths: &mut Vec<Vec<String>>,
    ) {
        if current == target {
            paths.push(current_path.clone());
            return;
        }
        if !visiting.insert(current.to_owned()) {
            return;
        }

        for superclass in self.superclasses(current) {
            if visiting.contains(superclass) {
                continue;
            }
            current_path.push(superclass.to_owned());
            self.find_all_paths_dfs(superclass, target, visiting, current_path, paths);
            current_path.pop();
        }

        visiting.remove(current);
    }
}

/// Conservative structural equality for expressions, with stack overflow protection.
fn structural_expr_eq(left: &Expr, right: &Expr) -> bool {
    stack_safe(|| structural_expr_eq_core(left.kind(), right.kind()))
}

/// Core DTT expression structural equality (BVar, FVar, Const, Sort, App, Lam, Pi, Let, Lit, Proj).
fn structural_expr_eq_core(left: &ExprKind, right: &ExprKind) -> bool {
    match (left, right) {
        (ExprKind::BVar(l), ExprKind::BVar(r)) => l == r,
        (ExprKind::FVar(l), ExprKind::FVar(r)) => l == r,
        (ExprKind::Const(ln, ll), ExprKind::Const(rn, rl)) => ln == rn && ll == rl,
        (ExprKind::Sort(l), ExprKind::Sort(r)) => l == r,
        (ExprKind::App(lf, la), ExprKind::App(rf, ra)) => {
            structural_expr_eq(lf, rf) && structural_expr_eq(la, ra)
        }
        (ExprKind::Lam(lb, lt, lbody), ExprKind::Lam(rb, rt, rbody))
        | (ExprKind::Pi(lb, lt, lbody), ExprKind::Pi(rb, rt, rbody)) => {
            lb == rb && structural_expr_eq(lt, rt) && structural_expr_eq(lbody, rbody)
        }
        (ExprKind::Let(_, lt, lv, lb, _), ExprKind::Let(_, rt, rv, rb, _)) => {
            structural_expr_eq(lt, rt) && structural_expr_eq(lv, rv) && structural_expr_eq(lb, rb)
        }
        (ExprKind::Lit(l), ExprKind::Lit(r)) => l == r,
        (ExprKind::Proj(ln, li, le), ExprKind::Proj(rn, ri, re)) => {
            ln == rn && li == ri && structural_expr_eq(le, re)
        }
        (ExprKind::MData(_, li), ExprKind::MData(_, ri))
        | (ExprKind::Squash(li), ExprKind::Squash(ri)) => structural_expr_eq(li, ri),
        (ExprKind::SProp, ExprKind::SProp) => true,
        _ => structural_expr_eq_ext(left, right),
    }
}

/// Extension cases: cubical type theory and ZFC set theory constructors.
fn structural_expr_eq_ext(left: &ExprKind, right: &ExprKind) -> bool {
    match (left, right) {
        (ExprKind::CubicalInterval, ExprKind::CubicalInterval)
        | (ExprKind::CubicalI0, ExprKind::CubicalI0)
        | (ExprKind::CubicalI1, ExprKind::CubicalI1) => true,
        (
            ExprKind::CubicalPath {
                ty: lt,
                left: ll,
                right: lr,
            },
            ExprKind::CubicalPath {
                ty: rt,
                left: rl,
                right: rr,
            },
        ) => structural_expr_eq(lt, rt) && structural_expr_eq(ll, rl) && structural_expr_eq(lr, rr),
        (ExprKind::CubicalPathLam { body: l }, ExprKind::CubicalPathLam { body: r }) => {
            structural_expr_eq(l, r)
        }
        (
            ExprKind::CubicalPathApp { path: lp, arg: la },
            ExprKind::CubicalPathApp { path: rp, arg: ra },
        ) => structural_expr_eq(lp, rp) && structural_expr_eq(la, ra),
        (
            ExprKind::CubicalHComp {
                ty: lt,
                phi: lp,
                u: lu,
                base: lb,
            },
            ExprKind::CubicalHComp {
                ty: rt,
                phi: rp,
                u: ru,
                base: rb,
            },
        ) => {
            structural_expr_eq(lt, rt)
                && structural_expr_eq(lp, rp)
                && structural_expr_eq(lu, ru)
                && structural_expr_eq(lb, rb)
        }
        (
            ExprKind::CubicalTransp {
                ty: lt,
                phi: lp,
                base: lb,
            },
            ExprKind::CubicalTransp {
                ty: rt,
                phi: rp,
                base: rb,
            },
        ) => structural_expr_eq(lt, rt) && structural_expr_eq(lp, rp) && structural_expr_eq(lb, rb),
        (ExprKind::ZFCSet(l), ExprKind::ZFCSet(r)) => structural_zfc_eq(l, r),
        (
            ExprKind::ZFCMem {
                element: le,
                set: ls,
            },
            ExprKind::ZFCMem {
                element: re,
                set: rs,
            },
        ) => structural_expr_eq(le, re) && structural_expr_eq(ls, rs),
        (
            ExprKind::ZFCComprehension {
                domain: ld,
                pred: lp,
            },
            ExprKind::ZFCComprehension {
                domain: rd,
                pred: rp,
            },
        ) => structural_expr_eq(ld, rd) && structural_expr_eq(lp, rp),
        _ => false,
    }
}

fn structural_zfc_eq(
    left: &clean_kernel::expr::ZFCSetExpr,
    right: &clean_kernel::expr::ZFCSetExpr,
) -> bool {
    match (left, right) {
        (clean_kernel::expr::ZFCSetExpr::Empty, clean_kernel::expr::ZFCSetExpr::Empty)
        | (clean_kernel::expr::ZFCSetExpr::Infinity, clean_kernel::expr::ZFCSetExpr::Infinity) => {
            true
        }
        (
            clean_kernel::expr::ZFCSetExpr::Singleton(lhs),
            clean_kernel::expr::ZFCSetExpr::Singleton(rhs),
        )
        | (
            clean_kernel::expr::ZFCSetExpr::Union(lhs),
            clean_kernel::expr::ZFCSetExpr::Union(rhs),
        )
        | (
            clean_kernel::expr::ZFCSetExpr::PowerSet(lhs),
            clean_kernel::expr::ZFCSetExpr::PowerSet(rhs),
        )
        | (
            clean_kernel::expr::ZFCSetExpr::Choice(lhs),
            clean_kernel::expr::ZFCSetExpr::Choice(rhs),
        ) => structural_expr_eq(lhs, rhs),
        (
            clean_kernel::expr::ZFCSetExpr::Pair(lhs_left, lhs_right),
            clean_kernel::expr::ZFCSetExpr::Pair(rhs_left, rhs_right),
        ) => structural_expr_eq(lhs_left, rhs_left) && structural_expr_eq(lhs_right, rhs_right),
        (
            clean_kernel::expr::ZFCSetExpr::Separation {
                set: lhs_set,
                pred: lhs_pred,
            },
            clean_kernel::expr::ZFCSetExpr::Separation {
                set: rhs_set,
                pred: rhs_pred,
            },
        ) => structural_expr_eq(lhs_set, rhs_set) && structural_expr_eq(lhs_pred, rhs_pred),
        (
            clean_kernel::expr::ZFCSetExpr::Replacement {
                set: lhs_set,
                func: lhs_func,
            },
            clean_kernel::expr::ZFCSetExpr::Replacement {
                set: rhs_set,
                func: rhs_func,
            },
        ) => structural_expr_eq(lhs_set, rhs_set) && structural_expr_eq(lhs_func, rhs_func),
        _ => false,
    }
}
