// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sort inference and unsound-domain guard helpers for the Ay backend.
//!
//! Moved from `mod.rs` as part of the root surface split (#2867).
//! Re-exported `pub(crate)` from the parent module for sibling access.

use ay::Sort;
use clean_kernel::expr::BigNat;
use clean_kernel::{Expr, ExprKind};
use num_bigint::BigInt;

use super::surface::{AyError, AyResult};

pub(crate) fn bignat_to_bigint(value: &BigNat) -> BigInt {
    match value {
        BigNat::Small(v) => BigInt::from(*v),
        BigNat::Big(limbs) => {
            let mut acc = BigInt::from(0u64);
            for &limb in limbs.iter().rev() {
                acc = (acc << 64) + BigInt::from(limb);
            }
            acc
        }
    }
}

/// Known Lean types whose SMT encoding is semantically wrong (#2849).
///
/// `UInt*`/`USize` use modular arithmetic (not unbounded Int), `Float` uses IEEE 754
/// (not exact Real). These must be rejected, not silently widened.
const UNSOUND_DOMAIN_TYPES: &[&str] = &["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"];

/// Infer ay Sort from a Lean type expression (checked).
///
/// Maps Lean types to SMT sorts:
/// - `Nat`, `Int` → `Sort::Int`
/// - `Real`, `Rat` → `Sort::Real` (SMT-LIB Real models the rationals)
/// - `Bool` → `Sort::Bool`
/// - `String` → `Sort::String`
/// - `Sort 0` (Prop) → `Sort::Bool`
/// - `UInt*`, `USize`, `Float` → `Err(UnsupportedExpr)` (#2849, #2852)
/// - Unknown types → `Sort::Uninterpreted` (#2260)
pub(crate) fn infer_sort_from_lean_type(lean_type: &Expr) -> AyResult<Sort> {
    // Strip MData so metadata-wrapped types are recognized (#2261)
    let lean_type = lean_type.strip_mdata();
    match lean_type.kind() {
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            reject_unsound_domain(&name_str)?;
            match name_str.as_str() {
                "Nat" | "Int" => Ok(Sort::Int),
                "Real" | "Rat" => Ok(Sort::Real),
                "Bool" => Ok(Sort::Bool),
                "String" => Ok(Sort::String),
                other => Ok(Sort::Uninterpreted(other.to_string())),
            }
        }
        ExprKind::Sort(_) => Ok(Sort::Bool), // Prop (Sort 0) → Bool is correct
        ExprKind::App(_, _) => {
            // Strip MData from head — get_app_fn only peels App nodes (#2261)
            let head = lean_type.get_app_fn().strip_mdata();
            if let ExprKind::Const(name, _) = head.kind() {
                let name_str = name.to_string();
                reject_unsound_domain(&name_str)?;
                match name_str.as_str() {
                    "Nat" | "Int" => Ok(Sort::Int),
                    "Real" | "Rat" => Ok(Sort::Real),
                    other => Ok(Sort::Uninterpreted(format!("App_{other}"))),
                }
            } else {
                Ok(Sort::Uninterpreted("unknown_app".to_string()))
            }
        }
        _ => Ok(Sort::Uninterpreted("unknown_expr".to_string())),
    }
}

/// Reject Lean types whose SMT encoding is semantically wrong (#2849).
fn reject_unsound_domain(name: &str) -> AyResult<()> {
    if UNSOUND_DOMAIN_TYPES.contains(&name) {
        Err(AyError::UnsupportedExpr(format!(
            "{name} cannot be mapped to SMT Int/Real — modular/IEEE semantics mismatch"
        )))
    } else {
        Ok(())
    }
}

/// Defense-in-depth: reject unsound domain types from a Lean type expression (#2852).
///
/// Checks the `ty` field of arithmetic and comparison `LogicalForm` variants.
/// The primary guard is `register_fvar_from_lean_type` in sort inference, but this
/// catches any path that bypasses FVar registration (e.g. direct expression translation).
pub(crate) fn reject_unsound_domain_ty(ty: &Expr) -> AyResult<()> {
    let ty = ty.strip_mdata();
    let head = match ty.kind() {
        ExprKind::Const(name, _) => name.to_string(),
        ExprKind::App(_, _) => {
            let head = ty.get_app_fn().strip_mdata();
            if let ExprKind::Const(name, _) = head.kind() {
                name.to_string()
            } else {
                return Ok(());
            }
        }
        _ => return Ok(()),
    };
    reject_unsound_domain(&head)
}
