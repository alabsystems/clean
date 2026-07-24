// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CSE substitution helpers — apply FVar remapping to LCNF values, args,
//! params, and kernel expressions.

use super::CseContext;
use crate::lcnf::{Arg, LetValue, Param};
use clean_kernel::{Expr, ExprFolderOpt, FVarId};

/// Apply substitutions to a let-value.
pub(super) fn apply_subst_to_value(value: &LetValue, ctx: &CseContext) -> LetValue {
    match value {
        LetValue::Lit(lit) => LetValue::Lit(lit.clone()),
        LetValue::Erased => LetValue::Erased,
        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => LetValue::Proj {
            type_name: type_name.clone(),
            idx: *idx,
            structure: ctx.canonical(*structure),
        },
        LetValue::Const { name, levels, args } => LetValue::Const {
            name: name.clone(),
            levels: levels.clone(),
            args: apply_subst_to_args(args, ctx),
        },
        LetValue::FVar { fvar, args } => LetValue::FVar {
            fvar: ctx.canonical(*fvar),
            args: apply_subst_to_args(args, ctx),
        },
        LetValue::Ctor { name, levels, args } => LetValue::Ctor {
            name: name.clone(),
            levels: levels.clone(),
            args: apply_subst_to_args(args, ctx),
        },
        LetValue::Reuse {
            slot,
            ctor_name,
            levels,
            args,
        } => LetValue::Reuse {
            slot: ctx.canonical(*slot),
            ctor_name: ctor_name.clone(),
            levels: levels.clone(),
            args: apply_subst_to_args(args, ctx),
        },
    }
}

/// Apply substitutions to arguments.
pub(super) fn apply_subst_to_args(args: &[Arg], ctx: &CseContext) -> Vec<Arg> {
    args.iter()
        .map(|arg| match arg {
            Arg::FVar(fvar) => Arg::FVar(ctx.canonical(*fvar)),
            Arg::Erased => Arg::Erased,
            Arg::Type(ty) => Arg::Type(apply_subst_to_expr(ty, ctx)),
            Arg::Index(idx) => Arg::Index(*idx),
        })
        .collect()
}

/// Apply substitutions to parameter types.
pub(super) fn apply_subst_to_params(params: &[Param], ctx: &CseContext) -> Vec<Param> {
    params
        .iter()
        .map(|param| Param {
            fvar_id: param.fvar_id,
            name: param.name.clone(),
            ty: apply_subst_to_expr(&param.ty, ctx),
            borrow: param.borrow,
        })
        .collect()
}

/// Apply substitutions to kernel expressions.
///
/// Uses a single-pass FVar remapping via ExprFolderOpt instead of
/// iterating all substitutions (O(S * E) → O(E)).
pub(super) fn apply_subst_to_expr(expr: &Expr, ctx: &CseContext) -> Expr {
    if ctx.subst.is_empty() {
        return expr.clone();
    }

    struct BulkFVarSubst<'a> {
        ctx: &'a CseContext,
    }

    impl ExprFolderOpt for BulkFVarSubst<'_> {
        fn should_descend(&self, expr: &Expr) -> bool {
            expr.has_fvar_quick()
        }

        fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
            let canonical = self.ctx.canonical(id);
            if canonical != id {
                Some(Expr::fvar(canonical))
            } else {
                None
            }
        }
    }

    let mut folder = BulkFVarSubst { ctx };
    expr.fold_opt_or_clone(&mut folder)
}
