// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::typing::{Budget, Typing};
use super::{
    RuntimeContext, RuntimeLcnfOutput, RuntimeLimits, RuntimeLowerError as Error, RuntimeRowOrigin,
};
use crate::lcnf::{Arg, Code, Decl, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, ExprKind, FVarId, Name};
use clean_olean::import::runtime::{RuntimeBody, RuntimeFamily};
use clean_olean::module::ConstantKind;
use std::collections::BTreeSet;

pub(super) fn lower_definition(
    context: &RuntimeContext,
    name: &Name,
    dependencies: Vec<RuntimeRowOrigin>,
    limits: RuntimeLimits,
) -> Result<RuntimeLcnfOutput, Error> {
    let mut budget = Budget::new(limits);
    // Check every represented header/body/rule in the exact reachable capture.
    // This is local consistency under those headers, never fresh kernel replay.
    for origin in &dependencies {
        let row = context.declaration(&origin.name)?;
        let mut typing = Typing::new(context, &row.level_params, &mut budget)?;
        let ty = row.type_.as_ref().map_err(|error| Error::Incomplete {
            name: row.name.clone(),
            detail: error.clone(),
        })?;
        typing.closed_source(ty, 0, 0)?;
        let _ = typing.sort_of(ty, 0)?;
        if let RuntimeBody::Stored(body) = &row.body {
            let body = body.as_ref().map_err(|error| Error::Incomplete {
                name: row.name.clone(),
                detail: error.clone(),
            })?;
            typing.closed_source(body, 0, 0)?;
            typing.check(body, ty, 0)?;
        }
        if let RuntimeFamily::Recursor { rules, .. } = &row.family {
            for rule in rules {
                let rhs = rule.rhs.as_ref().map_err(|error| Error::Incomplete {
                    name: row.name.clone(),
                    detail: error.clone(),
                })?;
                typing.closed_source(rhs, 0, 0)?;
                let _ = typing.infer(rhs, 0)?;
            }
        }
    }
    let row = context.declaration(name)?;
    if row.kind != ConstantKind::Definition {
        return Err(Error::Unsupported(
            "runtime root is not a stored definition",
        ));
    }
    let RuntimeBody::Stored(Ok(body)) = &row.body else {
        return Err(Error::MissingBody(name.clone()));
    };
    let ty = row.type_.as_ref().map_err(|error| Error::Incomplete {
        name: name.clone(),
        detail: error.clone(),
    })?;
    let mut typing = Typing::new(context, &row.level_params, &mut budget)?;
    let (params, result_type, code) = lower_function(&mut typing, body, ty, 0)?;
    let recursive = recursive_body_dependency(context, name, typing.budget)?;
    Ok(RuntimeLcnfOutput {
        declaration: Decl::new(
            name.clone(),
            row.level_params.clone(),
            result_type,
            params,
            code,
            recursive,
        ),
        origin: context.origin(name)?,
        dependencies,
    })
}

enum Pending {
    Let(LetDecl),
    Fun(FunDecl),
}

fn finish(pending: Vec<Pending>, result: FVarId) -> Code {
    pending
        .into_iter()
        .rev()
        .fold(Code::Return(result), |rest, entry| match entry {
            Pending::Let(value) => Code::Let(value, Box::new(rest)),
            Pending::Fun(value) => Code::Fun(value, Box::new(rest)),
        })
}

fn lower_function(
    typing: &mut Typing<'_, '_>,
    body: &Expr,
    ty: &Expr,
    depth: usize,
) -> Result<(Vec<Param>, Expr, Code), Error> {
    typing.budget.step(depth)?;
    let mut term = body.clone();
    let mut result_type = ty.clone();
    let mut params = Vec::new();
    while let ExprKind::Lam(_, domain, body) = term.kind() {
        typing.budget.step(depth)?;
        let signature = typing.whnf(&result_type, depth + 1)?;
        let ExprKind::Pi(_, expected, codomain) = signature.kind() else {
            return Err(Error::ExpectedFunction(signature));
        };
        if !typing.equal(domain, expected, depth + 1)? {
            return Err(Error::TypeMismatch {
                expected: expected.as_ref().clone(),
                found: domain.as_ref().clone(),
            });
        }
        let id = typing.fresh(domain.as_ref().clone())?;
        params.push(Param::new(id, Name::anon(), domain.as_ref().clone()));
        term = body.instantiate(&Expr::fvar(id));
        result_type = codomain.instantiate(&Expr::fvar(id));
    }
    typing.check(&term, &result_type, depth + 1)?;
    let mut pending = Vec::new();
    let result = lower_value(typing, &term, &mut pending, depth + 1)?;
    for param in &params {
        typing.locals.remove(&param.fvar_id);
    }
    Ok((params, result_type, finish(pending, result)))
}

fn bind(
    typing: &mut Typing<'_, '_>,
    pending: &mut Vec<Pending>,
    ty: Expr,
    value: LetValue,
) -> Result<FVarId, Error> {
    let id = typing.fresh(ty.clone())?;
    pending.push(Pending::Let(LetDecl::new(id, Name::anon(), ty, value)));
    Ok(id)
}

fn lower_arg(
    typing: &mut Typing<'_, '_>,
    expr: &Expr,
    pending: &mut Vec<Pending>,
    depth: usize,
) -> Result<Arg, Error> {
    let inferred = typing.infer(expr, depth + 1)?;
    // A function returning a type is type-level too. Preserve the original
    // expression as Arg::Type; no runtime body is replaced with a fake value.
    let mut result = inferred.clone();
    while let ExprKind::Pi(_, _, body) = result.kind() {
        result = body.as_ref().clone();
    }
    if matches!(result.kind(), ExprKind::Sort(_)) {
        return Ok(Arg::Type(expr.clone()));
    }
    Ok(Arg::FVar(lower_value(typing, expr, pending, depth + 1)?))
}

fn lower_value(
    typing: &mut Typing<'_, '_>,
    expr: &Expr,
    pending: &mut Vec<Pending>,
    depth: usize,
) -> Result<FVarId, Error> {
    typing.budget.step(depth)?;
    let ty = typing.infer(expr, depth + 1)?;
    match expr.kind() {
        ExprKind::FVar(id) => Ok(*id),
        ExprKind::Let(_, declared, value, body, _) => {
            typing.check(value, declared, depth + 1)?;
            let local = lower_value(typing, value, pending, depth + 1)?;
            lower_value(
                typing,
                &body.instantiate(&Expr::fvar(local)),
                pending,
                depth + 1,
            )
        }
        ExprKind::Lam(_, _, _) => {
            let id = typing.fresh(ty.clone())?;
            let (params, result, body) = lower_function(typing, expr, &ty, depth + 1)?;
            pending.push(Pending::Fun(FunDecl::new(
                id,
                Name::anon(),
                params,
                result,
                body,
            )));
            Ok(id)
        }
        ExprKind::Lit(value) => bind(typing, pending, ty, LetValue::Lit(value.clone())),
        ExprKind::Const(_, _) | ExprKind::App(_, _) => {
            let mut head = expr;
            let mut arguments = Vec::new();
            while let ExprKind::App(function, argument) = head.kind() {
                typing.budget.step(depth)?;
                arguments.push(argument.as_ref());
                head = function;
            }
            arguments.reverse();
            let mut args = Vec::with_capacity(arguments.len());
            for argument in arguments {
                args.push(lower_arg(typing, argument, pending, depth + 1)?);
            }
            let value = match head.kind() {
                ExprKind::Const(name, levels) => {
                    if let RuntimeFamily::Constructor {
                        num_params,
                        num_fields,
                        ..
                    } = &typing.context.declaration(name)?.family
                    {
                        let arity = num_params
                            .checked_add(*num_fields)
                            .ok_or(Error::Resource("constructor arity"))?
                            as usize;
                        if args.len() < arity {
                            return eta_constructor(
                                typing,
                                pending,
                                name,
                                levels,
                                args,
                                ty,
                                arity,
                                depth + 1,
                            );
                        }
                        if args.len() != arity {
                            return Err(Error::Unsupported("constructor application arity"));
                        }
                        LetValue::Ctor {
                            name: name.clone(),
                            levels: levels.to_vec(),
                            args,
                        }
                    } else {
                        LetValue::Const {
                            name: name.clone(),
                            levels: levels.to_vec(),
                            args,
                        }
                    }
                }
                ExprKind::FVar(fvar) => LetValue::FVar { fvar: *fvar, args },
                ExprKind::Lam(_, _, _) | ExprKind::Let(_, _, _, _, _) => {
                    let fvar = lower_value(typing, head, pending, depth + 1)?;
                    LetValue::FVar { fvar, args }
                }
                _ => return Err(Error::Unsupported("application head outside runtime core")),
            };
            bind(typing, pending, ty, value)
        }
        _ => Err(Error::Unsupported(
            "runtime value outside the exact LCNF fragment",
        )),
    }
}

/// A constructor value is a closure until fully saturated, not an allocation
/// with missing fields. Already supplied arguments stay ANF-bound outside the
/// new function, so eta expansion does not delay or duplicate their evaluation.
fn eta_constructor(
    typing: &mut Typing<'_, '_>,
    pending: &mut Vec<Pending>,
    name: &Name,
    levels: &[clean_kernel::Level],
    mut args: Vec<Arg>,
    ty: Expr,
    arity: usize,
    depth: usize,
) -> Result<FVarId, Error> {
    let id = typing.fresh(ty.clone())?;
    let mut result_type = ty;
    let mut params = Vec::new();
    while args.len() < arity {
        typing.budget.step(depth)?;
        let signature = typing.whnf(&result_type, depth + 1)?;
        let ExprKind::Pi(_, domain, body) = signature.kind() else {
            return Err(Error::ExpectedFunction(signature));
        };
        let local = typing.fresh(domain.as_ref().clone())?;
        params.push(Param::new(local, Name::anon(), domain.as_ref().clone()));
        args.push(lower_arg(
            typing,
            &Expr::fvar(local),
            &mut Vec::new(),
            depth + 1,
        )?);
        result_type = body.instantiate(&Expr::fvar(local));
    }
    let mut inner = Vec::new();
    let value = bind(
        typing,
        &mut inner,
        result_type.clone(),
        LetValue::Ctor {
            name: name.clone(),
            levels: levels.to_vec(),
            args,
        },
    )?;
    for param in &params {
        typing.locals.remove(&param.fvar_id);
    }
    pending.push(Pending::Fun(FunDecl::new(
        id,
        Name::anon(),
        params,
        result_type,
        finish(inner, value),
    )));
    Ok(id)
}

/// Conservative executable-body dependency recursion, including mutual calls
/// and recursor RHSs. It is not a termination claim. Type annotations and family
/// membership alone do not make every constructor use look recursive.
fn recursive_body_dependency(
    context: &RuntimeContext,
    root: &Name,
    budget: &mut Budget,
) -> Result<bool, Error> {
    fn references(
        expr: &Expr,
        out: &mut BTreeSet<Name>,
        budget: &mut Budget,
        depth: usize,
    ) -> Result<(), Error> {
        budget.step(depth)?;
        match expr.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.clone());
            }
            ExprKind::App(a, b) => {
                references(a, out, budget, depth + 1)?;
                references(b, out, budget, depth + 1)?;
            }
            ExprKind::Lam(_, _, body) => references(body, out, budget, depth + 1)?,
            ExprKind::Let(_, _, value, body, _) => {
                references(value, out, budget, depth + 1)?;
                references(body, out, budget, depth + 1)?;
            }
            _ => {}
        }
        Ok(())
    }
    let mut queue = vec![root.clone()];
    let mut seen = BTreeSet::new();
    while let Some(name) = queue.pop() {
        budget.step(0)?;
        if !seen.insert(name.clone()) {
            continue;
        }
        let row = context.declaration(&name)?;
        let mut targets = BTreeSet::new();
        if let RuntimeBody::Stored(Ok(body)) = &row.body {
            references(body, &mut targets, budget, 0)?;
        }
        if let RuntimeFamily::Recursor { rules, .. } = &row.family {
            for rule in rules {
                if let Ok(rhs) = &rule.rhs {
                    references(rhs, &mut targets, budget, 0)?;
                }
            }
        }
        if targets.contains(root) {
            return Ok(true);
        }
        queue.extend(targets);
    }
    Ok(false)
}
