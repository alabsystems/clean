// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for ay_backend translation tests.

use super::*;
use clean_kernel::Expr;

/// Helper: build `Eq T lhs rhs` as an Expr (3-arg Eq application)
pub(super) fn build_eq_expr(lhs: Expr, rhs: Expr) -> Expr {
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![Level::zero()]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::app(Expr::app(Expr::app(eq_const, nat_ty), lhs), rhs)
}

/// Helper: build a binary Nat operation application `op(a, b)`
pub(super) fn build_nat_binop(op_name: &str, a: u64, b: u64) -> Expr {
    use clean_kernel::name::Name;
    let a_expr = Expr::nat_lit(a);
    let b_expr = Expr::nat_lit(b);
    let op = Expr::const_(Name::from_string(op_name), vec![]);
    Expr::app(Expr::app(op, a_expr), b_expr)
}

/// Helper: build an FVar-headed application `fvar(arg1, arg2, ...)`
pub(super) fn build_fvar_app(fvar_id: FVarId, args: &[Expr]) -> Expr {
    let mut result = Expr::fvar(fvar_id);
    for arg in args {
        result = Expr::app(result, arg.clone());
    }
    result
}

/// Helper: build `Iff a b` as an Expr
pub(super) fn build_iff_expr(a: Expr, b: Expr) -> Expr {
    use clean_kernel::name::Name;
    let iff = Expr::const_(Name::from_string("Iff"), vec![]);
    Expr::app(Expr::app(iff, a), b)
}

/// Helper: build `@Exists Nat (fun n : Nat => body)` as an Expr
pub(super) fn build_exists_nat(body: Expr) -> Expr {
    use clean_kernel::name::Name;
    use clean_kernel::BinderInfo;
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let predicate = Expr::lam(BinderInfo::Default, nat_ty.clone(), body);
    let exists = Expr::const_(Name::from_string("Exists"), vec![]);
    Expr::app(Expr::app(exists, nat_ty), predicate)
}

/// Helper: build a 6-arg H-op typeclass application `@HOp.hOp α β γ inst a b`
///
/// This is how Lean 4 elaborates `a op b` for typeclass-dispatched operators.
/// For Nat: `@HSub.hSub Nat Nat Nat instHSubNat a b`.
pub(super) fn build_h_binop(op_name: &str, ty_name: &str, a: Expr, b: Expr) -> Expr {
    use clean_kernel::name::Name;
    let ty = Expr::const_(Name::from_string(ty_name), vec![]);
    let inst = Expr::const_(
        Name::from_string(&format!("inst{}{}", op_name, ty_name)),
        vec![],
    );
    let op = Expr::const_(Name::from_string(op_name), vec![]);
    // 6-arg form: op α β γ inst a b
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(op, ty.clone()), ty.clone()), ty),
                inst,
            ),
            a,
        ),
        b,
    )
}
