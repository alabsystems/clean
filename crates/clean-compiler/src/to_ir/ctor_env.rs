// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructor environment building for IR lowering.
//!
//! Extracts constructor metadata (tag, field types, scalar/object counts)
//! from kernel `ConstructorVal` data for use during IR conversion.

use super::state::CtorMeta;
use super::types::expr_to_ir_type;
use crate::error::CompilerError;
use crate::ir::IRType;
use clean_kernel::{ConstructorVal, Expr, ExprKind};
use std::collections::HashMap;

use clean_kernel::Name;

/// Extract field types from a constructor's type expression.
///
/// A constructor type is a Pi chain, e.g., `{A : Type} → A → List A → List A`
/// for `List.cons`. The first `num_params` Pi binders are type parameters
/// (skipped). The remaining domains are the field types.
fn extract_field_ir_types(ctor_type: &Expr, num_params: u32) -> Result<Vec<IRType>, CompilerError> {
    let mut types = Vec::new();
    let mut current = ctor_type.clone();
    let mut arg_idx = 0u32;

    while let ExprKind::Pi(_, domain, codomain) = current.kind() {
        if arg_idx >= num_params {
            types.push(expr_to_ir_type(domain)?);
        }
        arg_idx += 1;
        current = (**codomain).clone();
    }

    Ok(types)
}

/// Count the number of leading Pi binders in a type expression.
fn count_pi_arity(ty: &Expr) -> u16 {
    let mut arity: u16 = 0;
    let mut current = ty.clone();
    while let ExprKind::Pi(_, _domain, codomain) = current.kind() {
        arity = arity.saturating_add(1);
        current = (**codomain).clone();
    }
    arity
}

/// Whether a type's final codomain (after stripping the Pi-telescope) is a
/// `Sort` — i.e. the constant is a TYPE FORMER (`IO : Type → Type`, `Nat : Type`,
/// a `Prop`), not a runtime function.
///
/// SOUNDNESS: type formers emit no callable `l_X` runtime function, so they MUST
/// be excluded from the runtime-function arity map. Assigning one would make an
/// *unapplied* reference — e.g. `IO`, which is ubiquitous in any `IO Unit`
/// program — lower to `clean_alloc_closure((void*)l_IO, 1, 0)` over an undeclared
/// symbol, breaking codegen. Genuine runtime functions (`Nat.add`, constructors,
/// `HAdd.hAdd`) have a non-`Sort` codomain and are correctly included.
fn returns_sort(ty: &Expr) -> bool {
    let mut current = ty.clone();
    while let ExprKind::Pi(_, _domain, codomain) = current.kind() {
        current = (**codomain).clone();
    }
    matches!(current.kind(), ExprKind::Sort(_))
}

/// Build an arity map for every *runtime-function* constant in the environment
/// (Pi-telescope length). Type formers (final codomain `Sort`) are excluded — see
/// [`returns_sort`].
pub(crate) fn build_external_arities(env: &clean_kernel::Environment) -> HashMap<Name, u16> {
    env.constants()
        .filter(|c| !returns_sort(&c.type_))
        .map(|c| (c.name.clone(), count_pi_arity(&c.type_)))
        .collect()
}

/// Build constructor and inductive environments from kernel `ConstructorVal` data.
///
/// Returns two maps:
/// 1. **ctor_env**: constructor name → `CtorMeta` (for `LetValue::Ctor`)
/// 2. **inductive_env**: inductive type name → `CtorMeta` (for `LetValue::Proj`)
///
/// For each constructor, computes:
/// - `tag` from `constructor_idx`
/// - `field_types` by analyzing the constructor's Pi-chain type
/// - `num_scalars`/`num_objects` from the field type classification
///
/// The inductive_env maps from the constructor's `inductive_name` (e.g., `Prod`)
/// so that `Proj { type_name, idx, .. }` can look up field types. For multi-
/// constructor inductives, only the first constructor is stored (projections are
/// only valid on single-constructor types/structures in Lean 4).
///
/// Part of #1953, #1941.
pub fn build_ctor_env(
    ctors: &[&ConstructorVal],
) -> Result<(HashMap<Name, CtorMeta>, HashMap<Name, CtorMeta>), CompilerError> {
    let mut ctor_env = HashMap::with_capacity(ctors.len());
    let mut inductive_env = HashMap::with_capacity(ctors.len());
    for ctor in ctors {
        let field_types = extract_field_ir_types(&ctor.type_, ctor.num_params)?;
        let num_scalars = field_types.iter().filter(|t| t.is_scalar()).count() as u32;
        let num_objects = field_types.iter().filter(|t| t.is_rc_type()).count() as u32;
        let meta = CtorMeta {
            tag: ctor.constructor_idx,
            num_params: ctor.num_params,
            field_types,
            num_scalars,
            num_objects,
        };
        // Inductive env: only store first constructor (tag 0) per type.
        // Projections are only valid on single-constructor types (structures).
        if ctor.constructor_idx == 0 {
            inductive_env.insert(ctor.inductive_name.clone(), meta.clone());
        }
        ctor_env.insert(ctor.name.clone(), meta);
    }
    Ok((ctor_env, inductive_env))
}
