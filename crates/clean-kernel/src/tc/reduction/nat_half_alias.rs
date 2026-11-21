// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Refold the one-step iterator behind an already authenticated right shift.
//! The alias name is read from the actual definitions, never assumed by name.
//! A universal reflexivity proof validates the rewrite in the current checker.
//! Numeric evaluation still uses only the existing guarded shift reducer.

use super::names;
use crate::env::ConstantKind;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn nat() -> Expr {
    Expr::const_(names::NAT.clone(), vec![])
}

fn lambda(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

fn iterator_value(alias: &Name) -> Expr {
    let function = Expr::arrow(nat(), nat());
    let motive = lambda(nat(), function.clone());
    let base = lambda(nat(), Expr::bvar(0));
    let apply_alias = Expr::app(Expr::const_(alias.clone(), vec![]), Expr::bvar(0));
    let step = lambda(
        nat(),
        lambda(
            function,
            lambda(nat(), Expr::app(Expr::bvar(1), apply_alias)),
        ),
    );
    lambda(
        nat(),
        Expr::apps(
            Expr::const_(names::NAT_REC.clone(), vec![Level::succ(Level::zero())]),
            [motive, base, step, Expr::bvar(0)],
        ),
    )
}

fn default_lambda_body(e: &Expr) -> Option<&Expr> {
    match e.kind() {
        ExprKind::Lam(binder, _, body) if *binder == BinderInfo::Default.into() => Some(body),
        _ => None,
    }
}

impl<'env> TypeChecker<'env> {
    /// A bounded, purely syntactic hint. It grants no reduction authority.
    fn derive_unary_shift_alias(&self) -> Option<Name> {
        let shift = self.env.get_const(&names::NAT_SHIFT_RIGHT)?;
        if shift.kind != ConstantKind::Definition || !shift.level_params.is_empty() {
            return None;
        }
        let value = shift.value.as_ref()?;
        let body = default_lambda_body(default_lambda_body(value)?)?;
        let ExprKind::Const(iterator, levels) = body.get_app_fn().kind() else {
            return None;
        };
        if !levels.is_empty() {
            return None;
        }
        let expected = lambda(
            nat(),
            lambda(
                nat(),
                Expr::apps(
                    Expr::const_(iterator.clone(), vec![]),
                    [Expr::bvar(0), Expr::bvar(1)],
                ),
            ),
        );
        if *value != expected {
            return None;
        }
        let iterator = self.env.get_const(iterator)?;
        if iterator.kind != ConstantKind::Definition
            || !iterator.is_reducible
            || !iterator.level_params.is_empty()
        {
            return None;
        }
        let value = iterator.value.as_ref()?;
        let recursion = default_lambda_body(value)?;
        let args = recursion.get_app_args();
        if args.len() != 4 {
            return None;
        }
        let step = default_lambda_body(default_lambda_body(default_lambda_body(args[2])?)?)?;
        let ExprKind::App(_, application) = step.kind() else {
            return None;
        };
        let ExprKind::App(function, _) = application.kind() else {
            return None;
        };
        let ExprKind::Const(alias, levels) = function.kind() else {
            return None;
        };
        if !levels.is_empty() || *value != iterator_value(alias) {
            return None;
        }
        Some(alias.clone())
    }

    /// Check the complete closed equation using this checker's existing budget.
    /// Its open argument cannot use the closed-argument optimization below, so
    /// this proof cannot justify itself through the rewrite being admitted.
    fn check_unary_shift_alias(&self, alias: &Name) -> bool {
        let input = Expr::bvar(0);
        let lhs = Expr::app(Expr::const_(alias.clone(), vec![]), input.clone());
        let rhs = Expr::apps(
            Expr::const_(names::NAT_SHIFT_RIGHT.clone(), vec![]),
            [input, Expr::nat_lit(1)],
        );
        let universe = vec![Level::succ(Level::zero())];
        let claim = Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), universe.clone()),
                [nat(), lhs.clone(), rhs],
            ),
        );
        let proof = lambda(
            nat(),
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), universe),
                [nat(), lhs],
            ),
        );
        self.check_type(&proof, &claim).is_ok()
    }

    pub(in crate::tc) fn reduce_unary_shift_alias(&self, e: &Expr) -> Option<Expr> {
        let ExprKind::App(function, input) = e.kind() else {
            return None;
        };
        let ExprKind::Const(name, levels) = function.kind() else {
            return None;
        };
        if !levels.is_empty()
            || input.has_loose_bvars()
            || input.has_fvar_quick()
            || input.has_expr_mvar_quick()
            || input.has_level_mvar_quick()
            || *name == *names::NAT_SUCC
            || *name == *names::NAT_PRED
        {
            return None;
        }
        let alias = self
            .unary_shift_alias
            .get_or_init(|| self.derive_unary_shift_alias())
            .as_ref()?;
        // A syntactic hint cannot authorize arithmetic: the actual destination
        // must retain its existing complete native-fold admission.
        if name != alias || !self.hardwired_fold_admitted(&names::NAT_SHIFT_RIGHT) {
            return None;
        }
        if !self.unary_shift_alias_verified.get() {
            if !self.check_unary_shift_alias(alias) {
                return None;
            }
            self.unary_shift_alias_verified.set(true);
        }
        let shifted = Expr::apps(
            Expr::const_(names::NAT_SHIFT_RIGHT.clone(), vec![]),
            [input.as_ref().clone(), Expr::nat_lit(1)],
        );
        self.reduce_nat(&shifted)
    }
}

#[cfg(test)]
#[path = "nat_half_alias_tests.rs"]
mod tests;
