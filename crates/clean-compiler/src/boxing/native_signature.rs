// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Original checked source signatures for native UInt arithmetic/comparisons.

use crate::ir::IRType;
use clean_kernel::{
    ConstantKind, DeclarationVerification, Environment, Expr, ExprKind, Level, Name,
};

/// Both the existing native-operation table and the exact source declaration
/// must agree. No inference from a displayed method name supplies an ABI.
/// Returns the operand and result scalar types. Arithmetic has an exact
/// nondependent UInt result; comparisons permit only the existing Decidable
/// proof erasure with the exact canonical decision proposition. No universes
/// or additional computational binders are silently removed.
pub(super) fn checked_uint_signature(env: &Environment, name: &Name) -> Option<(IRType, IRType)> {
    let text = name.to_string();
    if *name != Name::from_string(&text) {
        return None;
    }
    let arithmetic = crate::to_ir::code::uint_arith_scalar_ty(name);
    #[cfg(feature = "trust-ir-backend")]
    let comparison = match crate::carrier_prims::carrier_prim(name, false) {
        Some(crate::carrier_prims::CarrierPrim::Cmp(_, width)) => Some(width.ir_type()),
        _ => None,
    };
    #[cfg(not(feature = "trust-ir-backend"))]
    let comparison: Option<IRType> = None;
    let primitive = arithmetic.clone().or(comparison.clone())?;
    let info = env.get_const(name)?;
    if !info.level_params.is_empty()
        || info.kind != ConstantKind::Definition
        || env.declaration_verification(name) != Some(DeclarationVerification::FullKernelCheck)
    {
        return None;
    }
    let expected = Expr::const_str(text.rsplit_once('.')?.0);
    let ExprKind::Pi(_, first, rest) = info.type_.strip_mdata().kind() else {
        return None;
    };
    let ExprKind::Pi(_, second, result) = rest.strip_mdata().kind() else {
        return None;
    };
    if first.strip_mdata() != &expected || second.strip_mdata() != &expected {
        return None;
    }
    let result_type = if arithmetic.is_some() {
        if result.strip_mdata() != &expected {
            return None;
        }
        primitive.clone()
    } else {
        // Only the existing proof-erasure representation of a genuine
        // Decidable result supplies Bool. Arbitrary dependent scalar results
        // and a fabricated Bool signature are not repaired into this ABI.
        let result = result.strip_mdata();
        if !matches!(result.get_app_fn().kind(), ExprKind::Const(n, levels)
            if *n == Name::from_string("Decidable") && levels.is_empty())
            || result.get_app_args().len() != 1
            || crate::to_mono::to_mono_type(result) != Expr::const_str("Bool")
        {
            return None;
        }
        let (carrier, operation) = text.rsplit_once('.')?;
        let proposition = match operation {
            "decEq" => Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [expected.clone(), Expr::bvar(1), Expr::bvar(0)],
            ),
            "decLt" | "decLe" => {
                let class = if operation == "decLt" { "LT" } else { "LE" };
                Expr::apps(
                    Expr::const_(
                        Name::from_string(&format!(
                            "{class}.{}",
                            if class == "LT" { "lt" } else { "le" }
                        )),
                        vec![Level::zero()],
                    ),
                    [
                        expected.clone(),
                        Expr::const_str(&format!("inst{class}{carrier}")),
                        Expr::bvar(1),
                        Expr::bvar(0),
                    ],
                )
            }
            _ => return None,
        };
        if result != &Expr::app(Expr::const_str("Decidable"), proposition) {
            return None;
        }
        IRType::Bool
    };
    let actual = crate::to_ir::expr_to_ir_type(first).ok()?;
    (actual == primitive).then_some((actual, result_type))
}
