// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::{to_nat_view, NatView};

pub(super) struct NatFieldView {
    pub(super) form: Expr,
    pub(super) field: Expr,
}

pub(super) struct FinView {
    pub(super) form: Expr,
    pub(super) field: Expr,
}

pub(super) enum IntView {
    OfNat(NatFieldView),
    NegSucc(NatFieldView),
}

impl IntView {
    pub(super) fn form(&self) -> &Expr {
        match self {
            Self::OfNat(view) | Self::NegSucc(view) => &view.form,
        }
    }

    pub(super) fn field(&self) -> &Expr {
        match self {
            Self::OfNat(view) | Self::NegSucc(view) => &view.field,
        }
    }
}

pub(super) fn to_char_view(expr: &Expr) -> Option<NatFieldView> {
    // Under the genuine v4.30 Char (`Char.mk (val : UInt32) (valid : …)`), the
    // constructor's first field is a `UInt32` chain, NOT a bare `Nat`, so only
    // the `Char.ofNat <nat>` literal spelling carries a bare-`Nat` field here.
    to_nat_field_view(expr, &["Char.ofNat"])
}

pub(super) fn to_uint_view(expr: &Expr, type_name: &str) -> Option<NatFieldView> {
    to_nat_field_view(expr, &[&format!("{type_name}.mk")])
}

pub(super) fn to_fin_view(expr: &Expr) -> Option<FinView> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    match head.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Fin.mk" && args.len() == 3 => {
            // args[2] (the `isLt` proof witness) is not captured: under the
            // v4.30 noConfusion convention the Prop-valued witness field is
            // skipped in the diagonal chain (proof irrelevance), so the Fin
            // arm never needs it.
            Some(FinView {
                form: expr.clone(),
                field: args[1].clone(),
            })
        }
        _ => None,
    }
}

pub(super) fn to_int_view(expr: &Expr) -> Option<IntView> {
    match expr.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Int.zero" => {
            let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            Some(IntView::OfNat(NatFieldView {
                form: Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    zero.clone(),
                ),
                field: zero,
            }))
        }
        ExprKind::App(f, arg) => match f.kind() {
            ExprKind::Const(name, _) => match name.to_string().as_str() {
                "Int.ofNat" => Some(IntView::OfNat(NatFieldView {
                    form: expr.clone(),
                    field: arg.as_ref().clone(),
                })),
                "Int.negSucc" => Some(IntView::NegSucc(NatFieldView {
                    form: expr.clone(),
                    field: arg.as_ref().clone(),
                })),
                "Int.negOfNat" => match to_nat_view(arg)? {
                    NatView::Zero => {
                        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
                        Some(IntView::OfNat(NatFieldView {
                            form: Expr::app(
                                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                                zero.clone(),
                            ),
                            field: zero,
                        }))
                    }
                    NatView::Succ(pred) => Some(IntView::NegSucc(NatFieldView {
                        form: Expr::app(
                            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
                            pred.clone(),
                        ),
                        field: pred,
                    })),
                },
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn eq_level_for_type(ty: &Expr) -> Option<Level> {
    match ty.get_app_fn().kind() {
        ExprKind::Const(name, levels) => match name.to_string().as_str() {
            "Nat" | "Bool" | "Char" | "String" | "Int" | "Fin" | "UInt8" | "UInt16" | "UInt32"
            | "UInt64" | "Unit" | "Empty" => Some(Level::succ(Level::zero())),
            // `List α : Type u` and `Option α : Type u` for `α : Type u`, so the
            // Eq carrier lives at `Sort (u+1)`.
            "List" | "Option" => levels.first().cloned().map(Level::succ),
            // `Prod α β : Type (max u v)` and `Sum α β : Type (max u v)`, so the
            // Eq carrier lives at `Sort (max u v + 1)` in both cases.
            "Prod" | "Sum" => match (levels.first(), levels.get(1)) {
                (Some(u), Some(v)) => Some(Level::succ(Level::max(u.clone(), v.clone()))),
                _ => None,
            },
            _ => None,
        },
        ExprKind::Sort(level) => Some(Level::succ(level.clone())),
        _ => None,
    }
}

pub(super) fn char_type() -> Expr {
    Expr::const_(Name::from_string("Char"), vec![])
}

pub(super) fn list_type(elem_ty: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        elem_ty,
    )
}

fn to_nat_field_view(expr: &Expr, ctor_names: &[&str]) -> Option<NatFieldView> {
    match expr.kind() {
        ExprKind::App(f, arg) => match f.kind() {
            ExprKind::Const(name, _) if ctor_names.iter().any(|ctor| name.to_string() == *ctor) => {
                Some(NatFieldView {
                    form: expr.clone(),
                    field: arg.as_ref().clone(),
                })
            }
            _ => None,
        },
        _ => None,
    }
}
