// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

use super::wrappers::to_fin_view;
use super::{build_ne_body, mk_eq_expr, mk_noconfusion_app, NoConfusionCtx};

pub(super) fn build_fin_ne_body(
    env: &Environment,
    ctx: &NoConfusionCtx,
    eq_ty: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    eq_level: &Level,
    depth: usize,
) -> Option<Expr> {
    let lhs_view = to_fin_view(lhs)?;
    let rhs_view = to_fin_view(rhs)?;
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_eq_level = Level::succ(Level::zero());
    // Under the v4.30 heterogeneous convention
    // (designs/2026-07-03-noconfusion-ctoridx-convention.md §3) the faithful
    // `Fin.mk : {n} → (val : Nat) → (isLt : Nat.lt val n) → Fin n` diagonal
    // chain has exactly ONE hypothesis: `val = val'` stays an `Eq` (`Nat` is
    // fully concrete — mentions no param and no earlier field), and the
    // Prop-valued `isLt` witness is skipped by proof irrelevance. The
    // recursive Nat sub-proof therefore IS the continuation: its binder type
    // `@Eq.{1} Nat val val'` matches the chain hypothesis exactly.
    let val_proof = build_ne_body(
        env,
        &nat_ty,
        &lhs_view.field,
        &rhs_view.field,
        &nat_eq_level,
        depth + 1,
    )?;
    let eq_app = mk_eq_expr(eq_ty, &lhs_view.form, &rhs_view.form, eq_level);
    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    let nc_app = mk_noconfusion_app(
        ctx,
        &false_expr,
        &lhs_view.form,
        &rhs_view.form,
        eq_ty,
        eq_level,
    );
    Some(Expr::lam(
        clean_kernel::BinderInfo::Default,
        eq_app,
        Expr::app(nc_app, val_proof),
    ))
}
