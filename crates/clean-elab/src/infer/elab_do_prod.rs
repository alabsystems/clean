// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Product tuple helpers for mutable variable accumulator threading (#1818).
//!
//! Implements sigma-type (product type) construction, value packing, and
//! destructuring for the `StateT σ` layer and for-loop accumulators.
//!
//! Lean 4 equivalents:
//! - `build_sigma_type` ← `mkProdN` from `Lean/Meta/ProdN.lean`
//! - `build_sigma_value` ← `mkProdMkN` from `Lean/Meta/ProdN.lean:41-57`
//! - `destructure_sigma` ← `bindMutVarsFromTuple` from `Do/Basic.lean:445-462`
//!
//! Reference: ~/lean4-ref/src/Lean/Meta/ProdN.lean
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/Basic.lean

use super::{ElabCtx, ElabError};
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

#[derive(Clone)]
struct ProductTail {
    ty: Expr,
    level: Level,
}

/// Return the universe parameter `u` required by `Prod.{u, _}` for `ty`.
///
/// `infer_sort(ty)` returns the level of the sort inhabited by `ty`, while
/// `Prod`'s parameter is one predecessor lower (`ty : Type u` means
/// `ty : Sort (u + 1)`).  Do not guess this level: mutable state may contain
/// values from arbitrary universes.
pub(crate) fn type_universe(ctx: &ElabCtx<'_>, ty: &Expr) -> Result<Level, ElabError> {
    // `Prop` is cumulative into `Type 0`, so a proposition-valued component is
    // valid in `Prod`/`Option` at universe parameter zero.  `SProp` is a
    // distinct strict sort in Clean's impredicative mode and is deliberately
    // not treated as Type-cumulative here.
    let inferred = ctx.whnf(&ctx.infer_type(ty)?);
    if matches!(inferred.kind(), clean_kernel::ExprKind::SProp) {
        return Err(ElabError::TypeMismatch {
            expected: "Type-cumulative product/option component".to_string(),
            actual: format!("{ty:?} inhabits SProp"),
        });
    }
    match ctx.infer_sort(ty)?.normalize() {
        Level::Zero => Ok(Level::Zero),
        Level::Succ(level) => Ok(level.as_ref().clone()),
        actual => Err(ElabError::TypeMismatch {
            expected: "Type-valued mutable-state component".to_string(),
            actual: format!("{ty:?} inhabits Sort {actual:?}"),
        }),
    }
}

fn mk_prod_type(left: Expr, left_level: Level, right: Expr, right_level: Level) -> Expr {
    let prod = Expr::const_(Name::from_string("Prod"), vec![left_level, right_level]);
    Expr::app(Expr::app(prod, left), right)
}

/// Build every suffix of a right-nested product once. Entry `i` is the exact
/// type and `Prod` universe parameter for components `i..`.
fn product_tail_plan(
    ctx: &ElabCtx<'_>,
    component_types: &[Expr],
) -> Result<Vec<ProductTail>, ElabError> {
    let Some(last_ty) = component_types.last() else {
        return Ok(Vec::new());
    };
    let last_level = type_universe(ctx, last_ty)?;
    let mut reversed = Vec::with_capacity(component_types.len());
    reversed.push(ProductTail {
        ty: last_ty.clone(),
        level: last_level,
    });

    for left_ty in component_types.iter().rev().skip(1) {
        let left_level = type_universe(ctx, left_ty)?;
        let right = reversed
            .last()
            .expect("product tail plan contains the final component");
        let level = Level::max(left_level.clone(), right.level.clone());
        reversed.push(ProductTail {
            ty: mk_prod_type(
                left_ty.clone(),
                left_level,
                right.ty.clone(),
                right.level.clone(),
            ),
            level,
        });
    }
    reversed.reverse();
    Ok(reversed)
}

/// Build an exact binary `Prod` type from two validated component types.
pub(crate) fn build_prod_type(
    ctx: &ElabCtx<'_>,
    left_ty: &Expr,
    right_ty: &Expr,
) -> Result<Expr, ElabError> {
    let left_level = type_universe(ctx, left_ty)?;
    let right_level = type_universe(ctx, right_ty)?;
    Ok(mk_prod_type(
        left_ty.clone(),
        left_level,
        right_ty.clone(),
        right_level,
    ))
}

/// Build an exact `Prod.mk` application from validated component types.
pub(crate) fn build_prod_value(
    ctx: &ElabCtx<'_>,
    left_ty: &Expr,
    right_ty: &Expr,
    left: Expr,
    right: Expr,
) -> Result<Expr, ElabError> {
    let left_level = type_universe(ctx, left_ty)?;
    let right_level = type_universe(ctx, right_ty)?;
    let prod_mk = Expr::const_(Name::from_string("Prod.mk"), vec![left_level, right_level]);
    Ok(Expr::apps(
        prod_mk,
        [left_ty.clone(), right_ty.clone(), left, right],
    ))
}

/// Project one component of an exact binary `Prod` type.
pub(crate) fn project_prod(
    ctx: &ElabCtx<'_>,
    left_ty: &Expr,
    right_ty: &Expr,
    pair: Expr,
    first: bool,
) -> Result<Expr, ElabError> {
    let left_level = type_universe(ctx, left_ty)?;
    let right_level = type_universe(ctx, right_ty)?;
    let projection = Expr::const_(
        Name::from_string(if first { "Prod.fst" } else { "Prod.snd" }),
        vec![left_level, right_level],
    );
    Ok(Expr::apps(
        projection,
        [left_ty.clone(), right_ty.clone(), pair],
    ))
}

/// Build the sigma type (product of mutable variable types).
///
/// For a single variable, sigma is just its type.
/// For multiple variables, sigma is a nested `Prod`:
/// `Prod T1 (Prod T2 (Prod T3 ...))` (right-nested).
pub(crate) fn build_sigma_type(
    ctx: &ElabCtx<'_>,
    mut_var_types: &[(String, Expr)],
) -> Result<Expr, ElabError> {
    match mut_var_types.len() {
        0 => Ok(Expr::const_(Name::from_string("Unit"), vec![])),
        _ => {
            let component_types: Vec<Expr> =
                mut_var_types.iter().map(|(_, ty)| ty.clone()).collect();
            let plan = product_tail_plan(ctx, &component_types)?;
            Ok(plan
                .first()
                .expect("non-empty component list has a product tail")
                .ty
                .clone())
        }
    }
}

/// Build a sigma value (product of mutable variable values).
///
/// Mirrors `build_sigma_type` but for values instead of types.
/// Equivalent to Lean 4's `mkProdMkN` from `Lean/Meta/ProdN.lean:41-57`.
///
/// For 1 variable: just the value expression
/// For 2+ variables: right-nested `Prod.mk v1 (Prod.mk v2 v3)`
///
/// The entries provide the type of each value for the `Prod.mk`
/// type arguments. Each entry is `(name, value_expr, type_expr)`.
/// An empty mutable-state tuple is a caller invariant violation; callers that
/// genuinely need an empty accumulator must construct its chosen unit value
/// explicitly instead of passing a dummy value that is ignored for non-empty
/// tuples.
pub(crate) fn build_sigma_value(
    ctx: &ElabCtx<'_>,
    vars: &[(String, Expr, Expr)],
) -> Result<Expr, ElabError> {
    match vars.len() {
        0 => Err(ElabError::InternalInvariant(
            "cannot build an empty mutable-state product value".to_string(),
        )),
        1 => {
            let _ = type_universe(ctx, &vars[0].2)?;
            Ok(vars[0].1.clone())
        }
        _ => {
            let component_types: Vec<Expr> = vars.iter().map(|(_, _, ty)| ty.clone()).collect();
            let plan = product_tail_plan(ctx, &component_types)?;
            let mut val = vars
                .last()
                .expect("invariant: non-empty when len > 1")
                .1
                .clone();
            for i in (0..vars.len() - 1).rev() {
                let (_, value, left_ty) = &vars[i];
                let right = &plan[i + 1];
                let left_level = type_universe(ctx, left_ty)?;
                let prod_mk = Expr::const_(
                    Name::from_string("Prod.mk"),
                    vec![left_level, right.level.clone()],
                );
                val = Expr::apps(
                    prod_mk,
                    [left_ty.clone(), right.ty.clone(), value.clone(), val],
                );
            }
            Ok(val)
        }
    }
}

/// Destructure a sigma value (product tuple) into individual let-bindings.
///
/// Equivalent to Lean 4's `bindMutVarsFromTuple` from `Do/Basic.lean:445-462`.
///
/// For 1 variable: returns `[(name, tuple_fvar)]` -- the tuple IS the variable.
/// For 2+ variables: returns projections using `Prod.fst` and `Prod.snd`:
///   `[(name1, Prod.fst tuple), (name2, Prod.fst (Prod.snd tuple)), ...]`
///
/// Returns a vec of `(var_name, projection_expr)` pairs that the caller should
/// bind as local variables.
pub(crate) fn destructure_sigma(
    ctx: &ElabCtx<'_>,
    vars: &[(String, Expr)],
    tuple_expr: Expr,
) -> Result<Vec<(String, Expr)>, ElabError> {
    match vars.len() {
        0 => Ok(vec![]),
        1 => {
            let _ = type_universe(ctx, &vars[0].1)?;
            Ok(vec![(vars[0].0.clone(), tuple_expr)])
        }
        _ => {
            let component_types: Vec<Expr> = vars.iter().map(|(_, ty)| ty.clone()).collect();
            let plan = product_tail_plan(ctx, &component_types)?;
            let mut result = Vec::with_capacity(vars.len());
            let mut current = tuple_expr;
            for (i, (name, left_ty)) in vars.iter().enumerate() {
                if i == vars.len() - 1 {
                    // Last element: use the remaining expression directly
                    result.push((name.clone(), current));
                    break;
                }
                let right = &plan[i + 1];
                let proj = project_prod(ctx, left_ty, &right.ty, current.clone(), true)?;
                result.push((name.clone(), proj));
                current = project_prod(ctx, left_ty, &right.ty, current, false)?;
            }
            Ok(result)
        }
    }
}
