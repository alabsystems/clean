// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bound preprocessing before constructing, hashing or checking candidates.
//! Shared levels are charged by expanded occurrence: kernel level hashing is
//! not DAG-memoized, so counting only distinct allocations would not bound it.

use clean_kernel::expr::{BigNat, MDataValue};
use clean_kernel::name::NameInner;
use clean_kernel::{ConstantInfo, Expr, ExprKind, Level, Literal, Multiplicity, Name};

use super::{ReplayContextError, ReplayedLeanContext};

fn spend(remaining: &mut usize, units: usize) -> Result<(), ReplayContextError> {
    *remaining = remaining
        .checked_sub(units)
        .ok_or(ReplayContextError::NodeLimit)?;
    Ok(())
}

fn name(mut current: &Name, remaining: &mut usize) -> Result<(), ReplayContextError> {
    loop {
        spend(remaining, 1)?;
        match current.inner() {
            NameInner::Anon => return Ok(()),
            NameInner::Str(parent, text) => {
                spend(remaining, text.len())?;
                current = parent;
            }
            NameInner::Num(parent, _) => current = parent,
        }
    }
}

fn level(root: &Level, remaining: &mut usize) -> Result<(), ReplayContextError> {
    let mut pending = vec![root];
    while let Some(current) = pending.pop() {
        spend(remaining, 1)?;
        match current {
            Level::Zero => {}
            Level::Succ(inner) => pending.push(inner),
            Level::Max(left, right) | Level::IMax(left, right) => {
                pending.extend([left.as_ref(), right.as_ref()])
            }
            Level::Param(_) => return Err(ReplayContextError::OpenExpression),
        }
    }
    Ok(())
}

fn arity(info: &ConstantInfo, levels: &[Level]) -> Result<(), ReplayContextError> {
    if info.level_params.len() != levels.len() {
        return Err(ReplayContextError::UniverseArity {
            expected: info.level_params.len(),
            actual: levels.len(),
        });
    }
    Ok(())
}

pub(super) fn declaration_term(
    context: &ReplayedLeanContext<'_>,
    info: &ConstantInfo,
    levels: &[Level],
    remaining: &mut usize,
) -> Result<Expr, ReplayContextError> {
    // Arity is O(1), before copying or hashing any caller-provided levels.
    arity(info, levels)?;
    spend(remaining, 1)?;
    name(&info.name, remaining)?;
    context.require_member(&info.name)?;
    for argument in levels {
        level(argument, remaining)?;
    }
    Ok(Expr::const_(info.name.clone(), levels.to_vec()))
}

pub(super) fn expression(
    context: &ReplayedLeanContext<'_>,
    root: &Expr,
    remaining: &mut usize,
) -> Result<(), ReplayContextError> {
    if root.has_fvar_quick()
        || root.has_expr_mvar_quick()
        || root.has_level_mvar_quick()
        || root.has_level_param_quick()
        || root.has_loose_bvars_quick()
    {
        return Err(ReplayContextError::OpenExpression);
    }
    let mut pending = vec![root];
    while let Some(current) = pending.pop() {
        spend(remaining, 1)?;
        match current.kind() {
            ExprKind::Const(declaration, levels) => {
                name(declaration, remaining)?;
                let info = context.declaration(declaration)?;
                arity(info.constant(), levels)?;
                for argument in levels {
                    level(argument, remaining)?;
                }
            }
            ExprKind::App(left, right) => pending.extend([left.as_ref(), right.as_ref()]),
            ExprKind::Lam(binder, left, right) | ExprKind::Pi(binder, left, right) => {
                if binder.mult != Multiplicity::Many {
                    return Err(ReplayContextError::ExtendedExpression);
                }
                pending.extend([left.as_ref(), right.as_ref()]);
            }
            ExprKind::Let(binder, ty, value, body, _) => {
                name(binder, remaining)?;
                pending.extend([ty.as_ref(), value.as_ref(), body.as_ref()]);
            }
            ExprKind::Proj(structure, _, inner) => {
                name(structure, remaining)?;
                context.require_member(structure)?;
                pending.push(inner);
            }
            ExprKind::MData(entries, inner) => {
                spend(remaining, entries.len())?;
                for (key, value) in entries {
                    name(key, remaining)?;
                    match value {
                        MDataValue::Bool(_) | MDataValue::Nat(_) => spend(remaining, 1)?,
                        MDataValue::String(text) => spend(remaining, text.len())?,
                        MDataValue::Name(value) => name(value, remaining)?,
                    }
                }
                pending.push(inner);
            }
            ExprKind::Lit(Literal::Nat(value)) => {
                match value {
                    BigNat::Small(_) => spend(remaining, 1)?,
                    BigNat::Big(limbs) => spend(remaining, limbs.len())?,
                }
                context.require_member(&Name::from_string("Nat"))?;
            }
            ExprKind::Lit(Literal::String(text)) => {
                spend(remaining, text.len())?;
                context.require_member(&Name::from_string("String"))?;
            }
            ExprKind::Sort(value) => level(value, remaining)?,
            ExprKind::BVar(_) => {}
            ExprKind::FVar(_) => return Err(ReplayContextError::OpenExpression),
            ExprKind::SProp
            | ExprKind::Squash(_)
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. }
            | ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. } => {
                return Err(ReplayContextError::ExtendedExpression)
            }
        }
    }
    Ok(())
}
