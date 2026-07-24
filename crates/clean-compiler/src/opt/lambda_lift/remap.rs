// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FVar Remapping
//!
//! Substitutes FVarIds throughout LCNF code and expressions according to a
//! remapping table. Used by lambda lifting to rename captured variables to
//! fresh parameters in lifted function bodies.

use crate::lcnf::{Arg, Cases, Code, FunDecl, LetDecl, LetValue, Param};
use crate::CodeFolder;
use clean_kernel::expr::{ExprKind, ZFCSetExpr};
use clean_kernel::{Expr, FVarId};
use std::collections::HashMap;
use std::sync::Arc;

/// Remap FVarIds in code according to a substitution map.
pub(super) fn remap_fvars_in_code(code: &Code, remap: &HashMap<FVarId, FVarId>) -> Code {
    RemapFolder { remap }.fold_code(code)
}

/// CodeFolder implementation for FVar remapping.
struct RemapFolder<'a> {
    remap: &'a HashMap<FVarId, FVarId>,
}

impl CodeFolder for RemapFolder<'_> {
    fn fold_return(&mut self, fvar: FVarId) -> Code {
        Code::Return(self.remap.get(&fvar).copied().unwrap_or(fvar))
    }

    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        let new_decl = LetDecl {
            fvar_id: decl.fvar_id,
            name: decl.name,
            ty: remap_fvars_in_expr(&decl.ty, self.remap),
            value: remap_fvars_in_value(&decl.value, self.remap),
        };
        Code::Let(new_decl, Box::new(self.fold_code(&body)))
    }

    fn fold_fun(&mut self, decl: FunDecl, body: Code) -> Code {
        let new_decl = FunDecl {
            fvar_id: decl.fvar_id,
            name: decl.name,
            params: remap_fvars_in_params(&decl.params, self.remap),
            ty: remap_fvars_in_expr(&decl.ty, self.remap),
            body: Box::new(self.fold_code(&decl.body)),
        };
        Code::Fun(new_decl, Box::new(self.fold_code(&body)))
    }

    fn fold_join_point(&mut self, decl: FunDecl, body: Code) -> Code {
        let new_decl = FunDecl {
            fvar_id: decl.fvar_id,
            name: decl.name,
            params: remap_fvars_in_params(&decl.params, self.remap),
            ty: remap_fvars_in_expr(&decl.ty, self.remap),
            body: Box::new(self.fold_code(&decl.body)),
        };
        Code::JoinPoint(new_decl, Box::new(self.fold_code(&body)))
    }

    fn fold_cases(&mut self, cases: Cases) -> Code {
        let Cases {
            type_name,
            result_type,
            scrutinee,
            alts,
        } = cases;
        let new_scrutinee = self.remap.get(&scrutinee).copied().unwrap_or(scrutinee);
        let new_alts = alts.into_iter().map(|alt| self.fold_alt(alt)).collect();
        Code::Cases(Cases {
            type_name,
            result_type: remap_fvars_in_expr(&result_type, self.remap),
            scrutinee: new_scrutinee,
            alts: new_alts,
        })
    }

    fn fold_jmp(&mut self, jp: FVarId, args: Vec<Arg>) -> Code {
        Code::Jmp {
            jp: self.remap.get(&jp).copied().unwrap_or(jp),
            args: args
                .iter()
                .map(|arg| remap_fvars_in_arg(arg, self.remap))
                .collect(),
        }
    }

    // fold_unreachable: default (identity) — remap doesn't touch Unreachable.
    // Unreachable code is never executed, and the expression is typically a
    // type/error message, not runtime code.
}

fn remap_fvars_in_value(value: &LetValue, remap: &HashMap<FVarId, FVarId>) -> LetValue {
    match value {
        LetValue::Lit(_) | LetValue::Erased => value.clone(),

        LetValue::Const { name, levels, args } => LetValue::Const {
            name: name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| remap_fvars_in_arg(a, remap)).collect(),
        },

        LetValue::Ctor { name, levels, args } => LetValue::Ctor {
            name: name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| remap_fvars_in_arg(a, remap)).collect(),
        },

        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => LetValue::Proj {
            type_name: type_name.clone(),
            idx: *idx,
            structure: remap.get(structure).copied().unwrap_or(*structure),
        },

        LetValue::FVar { fvar, args } => LetValue::FVar {
            fvar: remap.get(fvar).copied().unwrap_or(*fvar),
            args: args.iter().map(|a| remap_fvars_in_arg(a, remap)).collect(),
        },

        LetValue::Reuse {
            slot,
            ctor_name,
            levels,
            args,
        } => LetValue::Reuse {
            slot: remap.get(slot).copied().unwrap_or(*slot),
            ctor_name: ctor_name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| remap_fvars_in_arg(a, remap)).collect(),
        },
    }
}

fn remap_fvars_in_arg(arg: &Arg, remap: &HashMap<FVarId, FVarId>) -> Arg {
    match arg {
        Arg::FVar(fvar) => Arg::FVar(remap.get(fvar).copied().unwrap_or(*fvar)),
        Arg::Type(expr) => Arg::Type(remap_fvars_in_expr(expr, remap)),
        Arg::Erased | Arg::Index(_) => arg.clone(),
    }
}

fn remap_zfc_set_expr(set_expr: &ZFCSetExpr, remap: &HashMap<FVarId, FVarId>) -> ZFCSetExpr {
    match set_expr {
        ZFCSetExpr::Empty => ZFCSetExpr::Empty,
        ZFCSetExpr::Infinity => ZFCSetExpr::Infinity,
        ZFCSetExpr::Singleton(inner) => {
            ZFCSetExpr::Singleton(Arc::new(remap_fvars_in_expr(inner, remap)))
        }
        ZFCSetExpr::Pair(left, right) => ZFCSetExpr::Pair(
            Arc::new(remap_fvars_in_expr(left, remap)),
            Arc::new(remap_fvars_in_expr(right, remap)),
        ),
        ZFCSetExpr::Union(inner) => ZFCSetExpr::Union(Arc::new(remap_fvars_in_expr(inner, remap))),
        ZFCSetExpr::PowerSet(inner) => {
            ZFCSetExpr::PowerSet(Arc::new(remap_fvars_in_expr(inner, remap)))
        }
        ZFCSetExpr::Separation { set, pred } => ZFCSetExpr::Separation {
            set: Arc::new(remap_fvars_in_expr(set, remap)),
            pred: Arc::new(remap_fvars_in_expr(pred, remap)),
        },
        ZFCSetExpr::Replacement { set, func } => ZFCSetExpr::Replacement {
            set: Arc::new(remap_fvars_in_expr(set, remap)),
            func: Arc::new(remap_fvars_in_expr(func, remap)),
        },
        ZFCSetExpr::Choice(inner) => {
            ZFCSetExpr::Choice(Arc::new(remap_fvars_in_expr(inner, remap)))
        }
    }
}

/// Remap FVarIds in an expression according to a substitution map.
pub(super) fn remap_fvars_in_expr(expr: &Expr, remap: &HashMap<FVarId, FVarId>) -> Expr {
    if remap.is_empty() {
        return expr.clone();
    }
    match expr.kind() {
        ExprKind::FVar(fvar) => {
            if let Some(&new_id) = remap.get(fvar) {
                Expr::fvar(new_id)
            } else {
                expr.clone()
            }
        }
        ExprKind::App(f, arg) => Expr::app(
            remap_fvars_in_expr(f, remap),
            remap_fvars_in_expr(arg, remap),
        ),
        ExprKind::Lam(bi, ty, body) => Expr::lam(
            *bi,
            remap_fvars_in_expr(ty, remap),
            remap_fvars_in_expr(body, remap),
        ),
        ExprKind::Pi(bi, ty, body) => Expr::pi(
            *bi,
            remap_fvars_in_expr(ty, remap),
            remap_fvars_in_expr(body, remap),
        ),
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            remap_fvars_in_expr(ty, remap),
            remap_fvars_in_expr(val, remap),
            remap_fvars_in_expr(body, remap),
            *non_dep,
        ),
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), remap_fvars_in_expr(inner, remap)),
        ExprKind::Proj(name, idx, inner) => {
            Expr::proj(name.clone(), *idx, remap_fvars_in_expr(inner, remap))
        }
        ExprKind::Squash(inner) => Expr::from_kind(ExprKind::Squash(Arc::new(
            remap_fvars_in_expr(inner, remap),
        ))),
        ExprKind::CubicalPath { ty, left, right } => Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(remap_fvars_in_expr(ty, remap)),
            left: Arc::new(remap_fvars_in_expr(left, remap)),
            right: Arc::new(remap_fvars_in_expr(right, remap)),
        }),
        ExprKind::CubicalPathLam { body } => Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(remap_fvars_in_expr(body, remap)),
        }),
        ExprKind::CubicalPathApp { path, arg } => Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(remap_fvars_in_expr(path, remap)),
            arg: Arc::new(remap_fvars_in_expr(arg, remap)),
        }),
        ExprKind::CubicalHComp { ty, phi, u, base } => Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(remap_fvars_in_expr(ty, remap)),
            phi: Arc::new(remap_fvars_in_expr(phi, remap)),
            u: Arc::new(remap_fvars_in_expr(u, remap)),
            base: Arc::new(remap_fvars_in_expr(base, remap)),
        }),
        ExprKind::CubicalTransp { ty, phi, base } => Expr::from_kind(ExprKind::CubicalTransp {
            ty: Arc::new(remap_fvars_in_expr(ty, remap)),
            phi: Arc::new(remap_fvars_in_expr(phi, remap)),
            base: Arc::new(remap_fvars_in_expr(base, remap)),
        }),
        ExprKind::ZFCSet(set_expr) => {
            Expr::from_kind(ExprKind::ZFCSet(remap_zfc_set_expr(set_expr, remap)))
        }
        ExprKind::ZFCMem { element, set } => Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(remap_fvars_in_expr(element, remap)),
            set: Arc::new(remap_fvars_in_expr(set, remap)),
        }),
        ExprKind::ZFCComprehension { domain, pred } => {
            Expr::from_kind(ExprKind::ZFCComprehension {
                domain: Arc::new(remap_fvars_in_expr(domain, remap)),
                pred: Arc::new(remap_fvars_in_expr(pred, remap)),
            })
        }
        // Leaf variants: BVar, Sort, Const, Lit, SProp, CubicalInterval, CubicalI0, CubicalI1
        _ => expr.clone(),
    }
}

/// Remap FVarIds in parameter type annotations.
pub(super) fn remap_fvars_in_params(
    params: &[Param],
    remap: &HashMap<FVarId, FVarId>,
) -> Vec<Param> {
    params
        .iter()
        .map(|p| Param {
            fvar_id: p.fvar_id,
            name: p.name.clone(),
            ty: remap_fvars_in_expr(&p.ty, remap),
            borrow: p.borrow,
        })
        .collect()
}
