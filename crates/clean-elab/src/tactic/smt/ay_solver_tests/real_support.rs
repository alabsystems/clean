// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Expr, Level, Name};

pub(super) fn real_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

pub(super) fn real_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), lhs),
        rhs,
    )
}

pub(super) fn real_eq(lhs: Expr, rhs: Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                real_ty,
            ),
            lhs,
        ),
        rhs,
    )
}

pub(super) fn int_le(lhs: Expr, rhs: Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let inst = Expr::const_(Name::from_string("instLEInt"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LE.le"), vec![]), int_ty),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

pub(super) fn real_lt(lhs: Expr, rhs: Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let inst = Expr::const_(Name::from_string("instLTReal"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LT.lt"), vec![]), real_ty),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}
