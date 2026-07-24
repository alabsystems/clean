// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Argument transformation for monomorphization.

use crate::lcnf::{Arg, LetValue, Param};
use clean_kernel::{Expr, ExprKind, Name};

use super::{is_erased, is_type_former_type, to_mono_type, ToMonoState, MAX_TO_MONO_STACK_DEPTH};

/// Transform an argument to monomorphic form.
pub fn arg_to_mono(arg: &Arg, state: &ToMonoState) -> Arg {
    match arg {
        // Type arguments always become erased
        Arg::Type(_) => Arg::Erased,
        Arg::Erased => Arg::Erased,
        // FVar depends on whether it was bound to a type-former
        Arg::FVar(fvar_id) => {
            if state.is_type_param(*fvar_id) {
                Arg::Erased
            } else {
                arg.clone()
            }
        }
        // Index literals pass through unchanged
        Arg::Index(_) => arg.clone(),
    }
}

/// Transform arguments to monomorphic form.
pub fn args_to_mono(args: &[Arg], state: &ToMonoState) -> Vec<Arg> {
    args.iter().map(|a| arg_to_mono(a, state)).collect()
}

/// Transform arguments to monomorphic form using function type information.
///
/// Uses the function's type signature to determine which arguments should be erased.
/// Based on Lean 4's `argsToMonoWithFnType` in `ToMono.lean`.
///
/// For each forall binder in the type:
/// - If the binder domain is erased (`lcErased`), the argument is erased
/// - If the binder domain is a type-former (Sort), the argument is erased
/// - Otherwise, the argument is transformed via arg_to_mono
///
/// This is more precise than simple arg_to_mono because it uses the actual function
/// signature (after mono transformation) rather than just tracked type parameters.
///
/// # Arguments
/// * `args` - The arguments to transform
/// * `fn_type` - The type of the function being applied
/// * `state` - ToMono state for tracked type parameters
pub fn args_to_mono_with_fn_type(args: &[Arg], fn_type: &Expr, state: &ToMonoState) -> Vec<Arg> {
    args_to_mono_with_fn_type_impl(args, fn_type, state, 0)
}

fn args_to_mono_with_fn_type_impl(
    args: &[Arg],
    fn_type: &Expr,
    state: &ToMonoState,
    depth: usize,
) -> Vec<Arg> {
    // Stack protection
    if depth > MAX_TO_MONO_STACK_DEPTH {
        return args_to_mono(args, state);
    }

    let mut result = Vec::with_capacity(args.len());
    let mut remaining_type: Option<&Expr> = Some(fn_type);

    for arg in args {
        let mono_arg = if let Some(rt) = remaining_type {
            if let ExprKind::Pi(_, domain, body) = rt.kind() {
                remaining_type = Some(body);

                // Check if domain is erased (lcErased marker or Sort type)
                // Lean 4 checks d.isErased which means the domain equals lcErased
                if is_erased(domain) || matches!(domain.kind(), ExprKind::Sort(_)) {
                    // Erased parameter: replace argument with erased
                    Arg::Erased
                } else {
                    // Non-erased parameter: transform normally
                    arg_to_mono(arg, state)
                }
            } else {
                // No more type info: fall back to simple arg_to_mono
                remaining_type = None;
                arg_to_mono(arg, state)
            }
        } else {
            // No more type info: fall back to simple arg_to_mono
            remaining_type = None;
            arg_to_mono(arg, state)
        };

        result.push(mono_arg);
    }

    result
}

/// Transform arguments for reduced-argument (_redArg) function calls.
///
/// Used when a function has a specialized _redArg version that takes fewer arguments.
/// The `red_args` array contains the subset of arguments the _redArg version expects,
/// mapping back to the original parameter positions.
///
/// # Arguments
/// * `args` - Original arguments to the function
/// * `params` - Original function parameters
/// * `red_args` - The reduced argument pattern from the _redArg function
/// * `state` - ToMono state for tracked type parameters
///
/// # Returns
/// Arguments for the _redArg call, with type params erased
pub fn args_to_mono_red_arg(
    args: &[Arg],
    params: &[Param],
    red_args: &[Arg],
    state: &ToMonoState,
) -> Vec<Arg> {
    let mut result = Vec::with_capacity(red_args.len());
    let mut arg_idx = 0usize;

    for red_arg in red_args {
        match red_arg {
            Arg::FVar(fvar_id) => {
                // Find the matching parameter index
                while arg_idx < params.len() && params[arg_idx].fvar_id != *fvar_id {
                    arg_idx += 1;
                }
                if arg_idx < args.len() {
                    result.push(arg_to_mono(&args[arg_idx], state));
                    arg_idx += 1;
                }
            }
            // Erased, Type, and Index args in red_args pattern are skipped
            Arg::Erased | Arg::Type(_) | Arg::Index(_) => {}
        }
    }

    // Add remaining args after params.len() position
    for arg in args.iter().skip(params.len()) {
        result.push(arg_to_mono(arg, state));
    }

    result
}

/// Transform a constructor application to monomorphic form.
///
/// Erases the first `num_params` arguments (type parameters) and transforms
/// the remaining field arguments using arg_to_mono.
///
/// # Arguments
/// * `ctor_name` - Name of the constructor
/// * `args` - Arguments to the constructor
/// * `num_params` - Number of type parameters to erase
/// * `state` - ToMono state for tracked type parameters
///
/// # Returns
/// A LetValue::Const with erased type params and transformed field args
pub fn ctor_app_to_mono(
    ctor_name: &Name,
    args: &[Arg],
    num_params: usize,
    state: &ToMonoState,
) -> LetValue {
    let mut mono_args = Vec::with_capacity(args.len());

    // First num_params args are type params - replace with Erased
    for _ in 0..num_params.min(args.len()) {
        mono_args.push(Arg::Erased);
    }

    // Remaining args are fields - transform normally
    for arg in args.iter().skip(num_params) {
        mono_args.push(arg_to_mono(arg, state));
    }

    LetValue::Const {
        name: ctor_name.clone(),
        levels: vec![],
        args: mono_args,
    }
}

/// Transform a parameter to monomorphic form.
pub fn param_to_mono(param: &Param, state: &mut ToMonoState) -> Param {
    let ty = to_mono_type(&param.ty);

    // If param type is a type-former, track it for arg erasure
    if is_type_former_type(&param.ty) {
        state.add_type_param(param.fvar_id);
    }

    Param {
        fvar_id: param.fvar_id,
        name: param.name.clone(),
        ty,
        borrow: param.borrow,
    }
}
