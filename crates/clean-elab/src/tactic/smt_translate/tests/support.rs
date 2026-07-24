// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers reused across multiple test-family leaves.

use super::*;

pub(crate) fn real_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

/// Build `@HSub.hSub ty ty ty inst lhs rhs` (6 args: 3 type + 1 instance + 2 operands).
pub(crate) fn make_hsub(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    let inst = Expr::const_(Name::from_string("instHSubNat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("HSub.hSub"), vec![]),
                            ty.clone(),
                        ),
                        ty.clone(),
                    ),
                    ty,
                ),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build `@HDiv.hDiv ty ty ty inst lhs rhs`.
pub(crate) fn make_hdiv(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    let inst = Expr::const_(Name::from_string("instHDivNat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("HDiv.hDiv"), vec![]),
                            ty.clone(),
                        ),
                        ty.clone(),
                    ),
                    ty,
                ),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build `@HMod.hMod ty ty ty inst lhs rhs`.
pub(crate) fn make_hmod(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    let inst = Expr::const_(Name::from_string("instHModNat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("HMod.hMod"), vec![]),
                            ty.clone(),
                        ),
                        ty.clone(),
                    ),
                    ty,
                ),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}
