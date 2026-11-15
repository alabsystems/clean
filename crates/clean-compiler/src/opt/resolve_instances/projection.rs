// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared value-based structure projection reading. The ordinary optimized
//! pipeline and the Rust-ABI carrier pipeline use the same delta/iota rule;
//! neither guesses an instance's field from the instance or method name.

use crate::lcnf::{Arg, LetValue};
use clean_kernel::env::ConstantKind;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name};
use std::collections::HashMap;

/// A projection function read from its kernel value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClassProjection {
    pub(crate) class: Name,
    pub(crate) field: u32,
    pub(crate) inst_pos: usize,
}

/// `lambda p... self, self.i`, with `self : C p...`, for a one-constructor,
/// index-free, non-recursive structure. Runtime substitutions refuse reading
/// the kernel value. Class registration is irrelevant to this iota rule:
/// the prelude's `OfNat` is not registered as a class.
pub(crate) fn structure_projection(env: &Environment, method: &Name) -> Option<ClassProjection> {
    if env.has_implemented_by(method) || env.is_extern(method) || env.is_noncomputable(method) {
        return None;
    }
    let info = env.get_const(method)?;
    if info.kind != ConstantKind::Definition {
        return None;
    }
    let mut body = info.value.as_ref()?;
    let mut lambdas = 0usize;
    let mut self_ty: Option<&Expr> = None;
    while let ExprKind::Lam(_, ty, inner) = body.kind() {
        self_ty = Some(ty);
        body = inner;
        lambdas += 1;
    }
    let ExprKind::Proj(class, field, target) = body.kind() else {
        return None;
    };
    if lambdas == 0 || !matches!(target.kind(), ExprKind::BVar(0)) {
        return None;
    }
    let inductive = env.get_inductive(class)?;
    let n_params = lambdas - 1;
    if inductive.constructor_names.len() != 1
        || inductive.num_indices != 0
        || inductive.is_recursive
        || inductive.num_params as usize != n_params
    {
        return None;
    }
    let self_ty = self_ty?;
    if !matches!(self_ty.get_app_fn().kind(), ExprKind::Const(c, _) if c == class) {
        return None;
    }
    let params = self_ty.get_app_args();
    if params.len() != n_params
        || params
            .iter()
            .enumerate()
            .any(|(k, p)| !matches!(p.kind(), ExprKind::BVar(i) if *i as usize + k + 1 == n_params))
    {
        return None;
    }
    let ctor = env.get_constructor(&inductive.constructor_names[0])?;
    if *field >= ctor.num_fields {
        return None;
    }
    Some(ClassProjection {
        class: class.clone(),
        field: *field,
        inst_pos: n_params,
    })
}

/// The nullary-instance/method-call rule additionally requires a registered
/// class, preserving that rule's existing boundary.
pub(crate) fn class_projection(env: &Environment, method: &Name) -> Option<ClassProjection> {
    let proj = structure_projection(env, method)?;
    env.is_class(&proj.class).then_some(proj)
}

/// `Some(j)` iff a registered, unsubstituted instance's value is exactly
/// `lambda y..., C.mk p... f...`, with the selected field the bound variable
/// `y_j`. Only a full instance application is read. This is the existing
/// carrier projection rule, shared without admitting any new reflected op.
pub(crate) fn instance_field_is_argument(
    env: &Environment,
    instance: &Name,
    class: &Name,
    field: u32,
    arity: usize,
) -> Option<usize> {
    if !env.is_instance(instance)
        || env.has_implemented_by(instance)
        || env.is_extern(instance)
        || env.is_noncomputable(instance)
    {
        return None;
    }
    let info = env.get_const(instance)?;
    if info.kind != ConstantKind::Definition {
        return None;
    }
    let mut body = info.value.as_ref()?;
    let mut k = 0usize;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        k += 1;
        body = inner;
    }
    if k != arity {
        return None;
    }
    let ExprKind::Const(ctor_name, _) = body.get_app_fn().kind() else {
        return None;
    };
    let ctor = env.get_constructor(ctor_name)?;
    if ctor.inductive_name != *class || field >= ctor.num_fields {
        return None;
    }
    let args = body.get_app_args();
    if args.len() != ctor.num_params.checked_add(ctor.num_fields)? as usize {
        return None;
    }
    let ExprKind::BVar(i) = args
        .get(ctor.num_params.checked_add(field)? as usize)?
        .kind()
    else {
        return None;
    };
    let i = *i as usize;
    (i < k).then(|| k - 1 - i)
}

/// A saturated projection of an in-scope instance application whose field
/// is its own argument becomes that argument. In particular, the value of
/// `OfNat.ofNat Nat n (I n m)` comes from I's selected field, never a guess
/// that the numeral index n is the result. Parameters/erased fields and
/// nontrivial computations outside the exact rule remain unchanged.
pub(crate) fn project_instance_argument(
    env: &Environment,
    method: &Name,
    args: &[Arg],
    apps: &HashMap<FVarId, (Name, Vec<Arg>)>,
) -> Option<LetValue> {
    let proj = structure_projection(env, method)?;
    if args.len() != proj.inst_pos + 1 {
        return None;
    }
    let Some(Arg::FVar(inst)) = args.get(proj.inst_pos) else {
        return None;
    };
    let (instance, inst_args) = apps.get(inst)?;
    let j = instance_field_is_argument(env, instance, &proj.class, proj.field, inst_args.len())?;
    let Some(Arg::FVar(source)) = inst_args.get(j) else {
        return None;
    };
    Some(LetValue::FVar {
        fvar: *source,
        args: vec![],
    })
}
