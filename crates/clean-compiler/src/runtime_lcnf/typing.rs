// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{RuntimeContext, RuntimeLimits, RuntimeLowerError as Error};
use clean_kernel::{Expr, ExprKind, FVarId, Level, Literal, Multiplicity, Name};
use clean_olean::import::runtime::RuntimeBody;
use clean_olean::module::{ConstantKind, DefinitionSafety};
use std::collections::{BTreeMap, BTreeSet};

pub(super) struct Budget {
    remaining: usize,
    depth: usize,
}
impl Budget {
    pub(crate) fn new(limits: RuntimeLimits) -> Self {
        Self {
            remaining: limits.steps,
            depth: limits.depth,
        }
    }
    pub(crate) fn step(&mut self, depth: usize) -> Result<(), Error> {
        if depth > self.depth {
            return Err(Error::Resource("expression depth"));
        }
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or(Error::Resource("typing/lowering steps"))?;
        Ok(())
    }
}

/// A diagnostic local typer, conditional on captured headers. It has no kernel
/// Environment and cannot produce DeclarationVerification or an admission token.
pub(super) struct Typing<'a, 'b> {
    pub context: &'a RuntimeContext,
    pub budget: &'b mut Budget,
    pub locals: BTreeMap<FVarId, Expr>,
    next: u64,
    levels: BTreeSet<Name>,
}

impl<'a, 'b> Typing<'a, 'b> {
    pub(crate) fn new(
        context: &'a RuntimeContext,
        levels: &[Name],
        budget: &'b mut Budget,
    ) -> Result<Self, Error> {
        let unique: BTreeSet<_> = levels.iter().cloned().collect();
        if unique.len() != levels.len() {
            return Err(Error::Unsupported("duplicate universe binders"));
        }
        Ok(Self {
            context,
            budget,
            locals: BTreeMap::new(),
            next: 0,
            levels: unique,
        })
    }

    pub(crate) fn fresh(&mut self, ty: Expr) -> Result<FVarId, Error> {
        let id = FVarId::new(self.next);
        self.next = self
            .next
            .checked_add(1)
            .ok_or(Error::Resource("local identity"))?;
        self.locals.insert(id, ty);
        Ok(id)
    }

    pub(crate) fn seed_locals(&mut self, locals: &BTreeMap<FVarId, Expr>) -> Result<(), Error> {
        self.next = locals
            .keys()
            .map(|id| id.as_u64())
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(Error::Resource("local identity"))?;
        self.locals = locals.clone();
        Ok(())
    }

    pub(crate) fn closed_source(
        &mut self,
        expr: &Expr,
        binders: u32,
        depth: usize,
    ) -> Result<(), Error> {
        self.budget.step(depth)?;
        match expr.kind() {
            ExprKind::BVar(index) if *index < binders => Ok(()),
            ExprKind::BVar(_) | ExprKind::FVar(_) => Err(Error::UnboundVariable),
            ExprKind::Const(_, levels) => {
                for level in levels.iter() {
                    self.level(level, depth + 1)?;
                }
                Ok(())
            }
            ExprKind::Sort(level) => self.level(level, depth + 1),
            ExprKind::Lit(_) => Ok(()),
            ExprKind::App(a, b) => {
                self.closed_source(a, binders, depth + 1)?;
                self.closed_source(b, binders, depth + 1)
            }
            ExprKind::Lam(binder, domain, body) | ExprKind::Pi(binder, domain, body) => {
                if binder.mult != Multiplicity::Many {
                    return Err(Error::Unsupported("runtime binder multiplicity"));
                }
                self.closed_source(domain, binders, depth + 1)?;
                self.closed_source(
                    body,
                    binders
                        .checked_add(1)
                        .ok_or(Error::Resource("binder depth"))?,
                    depth + 1,
                )
            }
            ExprKind::Let(_, ty, value, body, _) => {
                self.closed_source(ty, binders, depth + 1)?;
                self.closed_source(value, binders, depth + 1)?;
                self.closed_source(
                    body,
                    binders
                        .checked_add(1)
                        .ok_or(Error::Resource("binder depth"))?,
                    depth + 1,
                )
            }
            _ => Err(Error::Unsupported(
                "source expression outside the exact runtime core",
            )),
        }
    }

    fn level(&mut self, level: &Level, depth: usize) -> Result<(), Error> {
        self.budget.step(depth)?;
        match level {
            Level::Zero => Ok(()),
            Level::Param(name) if self.levels.contains(name) => Ok(()),
            Level::Param(name) => Err(Error::UniverseParameter(name.clone())),
            Level::Succ(inner) => self.level(inner, depth + 1),
            Level::Max(a, b) | Level::IMax(a, b) => {
                self.level(a, depth + 1)?;
                self.level(b, depth + 1)
            }
        }
    }

    pub(crate) fn constant_type(&mut self, name: &Name, levels: &[Level]) -> Result<Expr, Error> {
        let row = self.context.declaration(name)?;
        if row.level_params.len() != levels.len() {
            return Err(Error::UniverseArity {
                name: name.clone(),
                expected: row.level_params.len(),
                found: levels.len(),
            });
        }
        for level in levels {
            self.level(level, 0)?;
        }
        let ty = row.type_.as_ref().map_err(|error| Error::Incomplete {
            name: name.clone(),
            detail: error.clone(),
        })?;
        Ok(ty.instantiate_level_params_direct(&row.level_params, levels))
    }

    pub(crate) fn infer(&mut self, expr: &Expr, depth: usize) -> Result<Expr, Error> {
        self.budget.step(depth)?;
        match expr.kind() {
            ExprKind::Sort(level) => {
                self.level(level, depth + 1)?;
                Ok(Expr::sort(Level::succ(level.clone())))
            }
            ExprKind::Const(name, levels) => self.constant_type(name, levels),
            ExprKind::FVar(id) => self.locals.get(id).cloned().ok_or(Error::UnboundVariable),
            ExprKind::BVar(_) => Err(Error::UnboundVariable),
            ExprKind::App(function, argument) => {
                let inferred = self.infer(function, depth + 1)?;
                let ty = self.whnf(&inferred, depth + 1)?;
                let ExprKind::Pi(_, domain, body) = ty.kind() else {
                    return Err(Error::ExpectedFunction(ty));
                };
                self.check(argument, domain, depth + 1)?;
                Ok(body.instantiate(argument))
            }
            ExprKind::Lam(binder, domain, body) => {
                let _ = self.sort_of(domain, depth + 1)?;
                let local = self.fresh(domain.as_ref().clone())?;
                let result = self.infer(&body.instantiate(&Expr::fvar(local)), depth + 1);
                self.locals.remove(&local);
                Ok(Expr::pi(
                    *binder,
                    domain.as_ref().clone(),
                    result?.abstract_fvar(local),
                ))
            }
            ExprKind::Pi(_, domain, body) => {
                let domain_level = self.sort_of(domain, depth + 1)?;
                let local = self.fresh(domain.as_ref().clone())?;
                let result = self.sort_of(&body.instantiate(&Expr::fvar(local)), depth + 1);
                self.locals.remove(&local);
                Ok(Expr::sort(Level::imax(domain_level, result?)))
            }
            ExprKind::Let(_, ty, value, body, _) => {
                let _ = self.sort_of(ty, depth + 1)?;
                self.check(value, ty, depth + 1)?;
                self.infer(&body.instantiate(value), depth + 1)
            }
            ExprKind::Lit(value) => {
                let name = Name::from_string(match value {
                    Literal::Nat(_) => "Nat",
                    Literal::String(_) => "String",
                });
                let _ = self.constant_type(&name, &[])?;
                Ok(Expr::const_(name, vec![]))
            }
            ExprKind::MData(_, _) => Err(Error::Unsupported("unmeasured metadata payload")),
            ExprKind::Proj(_, _, _) => Err(Error::Unsupported("runtime projection typing")),
            _ => Err(Error::Unsupported("non-core runtime expression")),
        }
    }

    pub(crate) fn sort_of(&mut self, expr: &Expr, depth: usize) -> Result<Level, Error> {
        let inferred = self.infer(expr, depth + 1)?;
        let inferred = self.whnf(&inferred, depth + 1)?;
        match inferred.kind() {
            ExprKind::Sort(level) => Ok(level.clone()),
            _ => Err(Error::ExpectedSort(inferred)),
        }
    }

    pub(crate) fn check(
        &mut self,
        value: &Expr,
        expected: &Expr,
        depth: usize,
    ) -> Result<(), Error> {
        let found = self.infer(value, depth + 1)?;
        if self.equal(&found, expected, depth + 1)? {
            Ok(())
        } else {
            Err(Error::TypeMismatch {
                expected: expected.clone(),
                found,
            })
        }
    }

    /// Only beta/let and captured SAFE type-definition delta reduction. Runtime
    /// function bodies, partial recursion, opaque constants and family rules are
    /// never unfolded to convince this local type comparison.
    pub(crate) fn whnf(&mut self, expr: &Expr, depth: usize) -> Result<Expr, Error> {
        let mut current = expr.clone();
        loop {
            self.budget.step(depth)?;
            match current.kind() {
                ExprKind::Let(_, _, value, body, _) => current = body.instantiate(value),
                ExprKind::App(function, argument) => {
                    let head = self.whnf(function, depth + 1)?;
                    if let ExprKind::Lam(_, _, body) = head.kind() {
                        current = body.instantiate(argument);
                    } else {
                        return Ok(Expr::app(head, argument.as_ref().clone()));
                    }
                }
                ExprKind::Const(name, levels) => {
                    let row = self.context.declaration(name)?;
                    let _ = self.constant_type(name, levels)?;
                    let mut result_type =
                        row.type_.as_ref().map_err(|error| Error::Incomplete {
                            name: name.clone(),
                            detail: error.clone(),
                        })?;
                    while let ExprKind::Pi(_, _, body) = result_type.kind() {
                        result_type = body;
                    }
                    if row.kind == ConstantKind::Definition
                        && row.declaration_safety == Some(DefinitionSafety::Safe)
                        && matches!(result_type.kind(), ExprKind::Sort(_))
                    {
                        let RuntimeBody::Stored(Ok(body)) = &row.body else {
                            return Err(Error::MissingBody(name.clone()));
                        };
                        current = body.instantiate_level_params_direct(&row.level_params, levels);
                    } else {
                        return Ok(current);
                    }
                }
                _ => return Ok(current),
            }
        }
    }

    pub(crate) fn equal(&mut self, left: &Expr, right: &Expr, depth: usize) -> Result<bool, Error> {
        self.budget.step(depth)?;
        if left == right {
            return Ok(true);
        }
        let left = self.whnf(left, depth + 1)?;
        let right = self.whnf(right, depth + 1)?;
        if left == right {
            return Ok(true);
        }
        match (left.kind(), right.kind()) {
            (ExprKind::Sort(a), ExprKind::Sort(b)) => Ok(a.normalize() == b.normalize()),
            (ExprKind::Const(a, la), ExprKind::Const(b, lb)) => Ok(a == b
                && la.len() == lb.len()
                && la
                    .iter()
                    .zip(lb)
                    .all(|(a, b)| a.normalize() == b.normalize())),
            (ExprKind::App(f, a), ExprKind::App(g, b)) => {
                Ok(self.equal(f, g, depth + 1)? && self.equal(a, b, depth + 1)?)
            }
            (ExprKind::Pi(_, a, b), ExprKind::Pi(_, c, d))
            | (ExprKind::Lam(_, a, b), ExprKind::Lam(_, c, d)) => {
                if !self.equal(a, c, depth + 1)? {
                    return Ok(false);
                }
                let id = self.fresh(a.as_ref().clone())?;
                let result = self.equal(
                    &b.instantiate(&Expr::fvar(id)),
                    &d.instantiate(&Expr::fvar(id)),
                    depth + 1,
                );
                self.locals.remove(&id);
                result
            }
            _ => Ok(false),
        }
    }
}
