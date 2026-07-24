// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Expr, ExprKind};

fn nat_const_value(expr: &Expr) -> Option<u64> {
    let mut current = expr;
    let mut succs = 0_u64;

    loop {
        match current.kind() {
            ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => {
                return n.to_u64()?.checked_add(succs);
            }
            ExprKind::Const(name, _) => {
                let name = name.to_string();
                return match name.as_str() {
                    "Nat.zero" => Some(succs),
                    "Nat.one" | "1" => succs.checked_add(1),
                    _ => None,
                };
            }
            ExprKind::App(f, arg) => match f.kind() {
                ExprKind::Const(name, _) if name.to_string() == "Nat.succ" => {
                    succs = succs.checked_add(1)?;
                    current = arg;
                }
                _ => return None,
            },
            _ => return None,
        }
    }
}

pub(crate) fn nonnegative_ring_const_value(expr: &Expr) -> Option<u64> {
    nat_const_value(expr).or_else(|| match expr.kind() {
        ExprKind::Const(name, _) => {
            let name = name.to_string();
            match name.as_str() {
                "Int.zero" | "Rat.zero" => Some(0),
                "Int.one" | "Rat.one" => Some(1),
                _ => None,
            }
        }
        ExprKind::App(f, arg) => match f.kind() {
            ExprKind::Const(name, _) if name.to_string() == "Int.ofNat" => nat_const_value(arg),
            _ => None,
        },
        _ => None,
    })
}
