// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Prepare checked Int instance projections and concrete numerals for SMT.
//!
//! The environment-free translator must not guess a dictionary's operation
//! from its carrier or a numeral's value from its literal index. Reduce those
//! actual projections here, at the caller that owns the kernel environment.

use crate::tactic::op_projection::{
    reduce_op_projection_head_instances, reduce_structure_projection_head_instances,
};
use crate::tactic::smt_translate::TranslateError;
use crate::tactic::{Goal, ProofState};
use clean_kernel::expr::{ExprFolder, Literal};
use clean_kernel::{Expr, ExprKind, Name};

pub(super) fn prepare_smt_integer_expr(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
) -> Result<Expr, TranslateError> {
    let prepared = IntegerInputFolder { state, goal }.fold_expr(expr);
    if prepared == *expr {
        return Ok(prepared);
    }
    // Both sides must be actual well-typed terms, and the conversion must hold
    // in the entire expression's binder context. The original goal remains
    // the target of the downstream proof validation and close_goal checks.
    let original_ty = state.infer_type_strict(goal, expr).map_err(|error| {
        TranslateError::UnsupportedExpr(format!("ill-typed integer SMT input: {error}"))
    })?;
    let prepared_ty = state.infer_type_strict(goal, &prepared).map_err(|error| {
        TranslateError::UnsupportedExpr(format!("ill-typed prepared integer SMT input: {error}"))
    })?;
    if !state.is_def_eq(goal, &original_ty, &prepared_ty) || !state.is_def_eq(goal, expr, &prepared)
    {
        return Err(TranslateError::UnsupportedExpr(
            "integer SMT preparation failed kernel conversion".to_string(),
        ));
    }
    Ok(prepared)
}

struct IntegerInputFolder<'a> {
    state: &'a ProofState,
    goal: &'a Goal,
}

impl ExprFolder for IntegerInputFolder<'_> {
    fn fold_app(&mut self, function: &Expr, argument: &Expr) -> Expr {
        let expr = Expr::app(self.fold_expr(function), self.fold_expr(argument));
        let ExprKind::Const(name, _) = expr.get_app_fn().kind() else {
            return expr;
        };
        let rendered = name.to_string();
        if *name != Name::from_string(&rendered) {
            return expr;
        }
        let args = expr.get_app_args();
        let expected_operation = match (rendered.as_str(), args.as_slice()) {
            ("HDiv.hDiv", [a, b, c, _, _, _]) if [a, b, c].into_iter().all(|a| is_int(a)) => {
                Some("Int.ediv")
            }
            ("HMod.hMod", [a, b, c, _, _, _]) if [a, b, c].into_iter().all(|a| is_int(a)) => {
                Some("Int.emod")
            }
            ("Div.div", [a, _, _, _]) if is_int(a) => Some("Int.ediv"),
            ("Mod.mod", [a, _, _, _]) if is_int(a) => Some("Int.emod"),
            ("OfNat.ofNat", [carrier, _, _]) if is_int(carrier) || is_nat(carrier) => {
                let reduced = self.state.whnf_instances(self.goal, &expr);
                return if is_concrete_numeral(&reduced, is_int(carrier)) {
                    reduced
                } else {
                    expr.clone()
                };
            }
            _ => None,
        };
        if let Some(expected_operation) = expected_operation {
            // Select the actual stored field without unfolding the operation
            // itself. Instance WHNF has its existing hard reduction budget;
            // custom fields stay unsupported rather than receiving an
            // interpretation based on the Int carrier.
            let reduced = reduce_op_projection_head_instances(self.state, self.goal, &expr)
                .unwrap_or_else(|| {
                    reduce_structure_projection_head_instances(self.state, self.goal, &expr)
                });
            if matches!(reduced.get_app_fn().kind(), ExprKind::Const(head, _) if *head == Name::from_string(expected_operation))
                && reduced.get_app_args().len() == 2
            {
                return reduced;
            }
        }
        expr.clone()
    }
}

fn is_int(expr: &Expr) -> bool {
    matches!(expr.strip_mdata().kind(), ExprKind::Const(name, _) if *name == Name::from_string("Int"))
}

fn is_nat(expr: &Expr) -> bool {
    matches!(expr.strip_mdata().kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat"))
}

fn is_concrete_numeral(expr: &Expr, integer: bool) -> bool {
    if !integer {
        return matches!(expr.strip_mdata().kind(), ExprKind::Lit(Literal::Nat(_)));
    }
    let args = expr.get_app_args();
    matches!(expr.get_app_fn().kind(), ExprKind::Const(name, _) if *name == Name::from_string("Int.ofNat") || *name == Name::from_string("Int.negSucc"))
        && matches!(args.as_slice(), [argument] if matches!(argument.strip_mdata().kind(), ExprKind::Lit(Literal::Nat(_))))
}
