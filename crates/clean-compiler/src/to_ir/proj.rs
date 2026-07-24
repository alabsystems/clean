// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Projection field resolution for IR conversion.
//!
//! Resolves field types and runtime indices from the kernel `Environment`
//! for structure projections. Single Pi-chain walk prevents divergence
//! between type and index lookups.

use crate::ir::IRType;
use clean_kernel::{Environment, ExprKind, Name};

use super::expr_to_ir_type;

/// Resolve both the IRType and runtime index of a projected field.
///
/// Uses the Environment to look up the inductive type by `type_name`,
/// find the (sole) constructor, decompose its Pi-type, and for field `idx`:
/// - Returns the field's IRType
/// - Computes the runtime index: obj_idx for object fields, byte offset
///   for scalar fields (#1982)
///
/// Single Pi-chain walk prevents divergence between type and index lookups.
///
/// Returns `(IRType::Object, idx)` as fallback when:
/// - The type is not found in the environment
/// - The type is not a structure (has != 1 constructor)
/// - The constructor is not found
/// - The index is out of range
pub(crate) fn get_proj_field_info(type_name: &Name, idx: u32, env: &Environment) -> (IRType, u32) {
    let ind = match env.get_inductive(type_name) {
        Some(ind) => ind,
        None => return (IRType::Object, idx),
    };
    if ind.constructor_names.len() != 1 {
        return (IRType::Object, idx);
    }
    let ctor_name = &ind.constructor_names[0];
    let ctor_val = match env.get_constructor(ctor_name) {
        Some(cv) => cv,
        None => return (IRType::Object, idx),
    };
    let mut current = ctor_val.type_.clone();
    let mut arg_idx = 0u32;
    let mut obj_idx = 0u32;
    let mut scalar_byte_off = 0u32;

    while let ExprKind::Pi(_, domain, codomain) = current.kind() {
        if arg_idx >= ctor_val.num_params {
            let field_idx = arg_idx - ctor_val.num_params;
            let field_ty = expr_to_ir_type(domain);
            if field_idx == idx {
                let runtime_idx = if field_ty.is_scalar() {
                    scalar_byte_off
                } else {
                    obj_idx
                };
                return (field_ty, runtime_idx);
            }
            if field_ty.is_scalar() {
                scalar_byte_off += field_ty.scalar_byte_size();
            } else {
                obj_idx += 1;
            }
        }
        current = (**codomain).clone();
        arg_idx += 1;
    }
    (IRType::Object, idx)
}
