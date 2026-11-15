// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded, structural unary-family matcher specialization. All three layers
//! (matcher, wrapper, recursor rules) are read from the captured source context.
//! No spelling, suffix, default tag, missing RHS or kernel origin substitutes for
//! these equations. Generic eliminators remain outside this diagnostic slice.

use super::typing::Budget;
use super::{RuntimeContext, RuntimeLowerError as Error, RuntimeRowOrigin};
use clean_kernel::{Expr, ExprKind, FVarId, Level, Multiplicity, Name};
use clean_olean::import::runtime::{RuntimeBody, RuntimeFamily};
use clean_olean::module::{ConstantKind, DefinitionSafety};

pub(super) struct Plan {
    pub source: RuntimeRowOrigin,
    pub wrapper: RuntimeRowOrigin,
    pub recursor: RuntimeRowOrigin,
    pub family: RuntimeRowOrigin,
    pub zero: Name,
    pub succ: Name,
    pub unit: Name,
    pub motive: Expr,
    pub levels: Vec<Level>,
}
fn peel(
    body: &Expr,
    n: usize,
    budget: &mut Budget,
) -> Result<Option<(Vec<(FVarId, Expr)>, Expr)>, Error> {
    let mut body = body.clone();
    let mut params = Vec::new();
    for i in 0..n {
        budget.step(0)?;
        let ExprKind::Lam(binder, domain, inner) = body.kind() else {
            return Ok(None);
        };
        if binder.mult != Multiplicity::Many {
            return Ok(None);
        }
        let id = FVarId::new(10_000 + i as u64);
        params.push((id, domain.as_ref().clone()));
        body = inner.instantiate(&Expr::fvar(id));
    }
    Ok(Some((params, body)))
}
fn spine(expr: &Expr, budget: &mut Budget) -> Result<(Expr, Vec<Expr>), Error> {
    let mut head = expr;
    let mut args = Vec::new();
    while let ExprKind::App(f, a) = head.kind() {
        budget.step(0)?;
        args.push(a.as_ref().clone());
        head = f;
    }
    args.reverse();
    Ok((head.clone(), args))
}
fn stored(context: &RuntimeContext, name: &Name, levels: &[Level]) -> Result<Option<Expr>, Error> {
    let row = context.declaration(name)?;
    if row.kind != ConstantKind::Definition
        || row.declaration_safety != Some(DefinitionSafety::Safe)
        || levels.len() != row.level_params.len()
    {
        return Ok(None);
    }
    let RuntimeBody::Stored(Ok(body)) = &row.body else {
        return Ok(None);
    };
    Ok(Some(body.instantiate_level_params_direct(
        &row.level_params,
        levels,
    )))
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

pub(super) fn derive(
    context: &RuntimeContext,
    name: &Name,
    levels: &[Level],
    motive: &Expr,
    budget: &mut Budget,
) -> Result<Option<Plan>, Error> {
    let Some(body) = stored(context, name, levels)? else {
        return Ok(None);
    };
    let Some((p, body)) = peel(&body, 4, budget)? else {
        return Ok(None);
    };
    let ExprKind::Const(data, data_levels) = p[1].1.kind() else {
        return Ok(None);
    };
    if !data_levels.is_empty() {
        return Ok(None);
    }
    let data_expr = Expr::const_(data.clone(), vec![]);
    let row = context.declaration(data)?;
    let RuntimeFamily::Inductive {
        constructors,
        num_params: 0,
        num_indices: 0,
        num_nested: Some(0),
        is_nested: false,
        is_unsafe: false,
        ..
    } = &row.family
    else {
        return Ok(None);
    };
    if constructors.len() != 2 {
        return Ok(None);
    }
    let zero = constructors[0].clone();
    let succ = constructors[1].clone();
    let z = context.declaration(&zero)?;
    let s = context.declaration(&succ)?;
    if !matches!(&z.family,RuntimeFamily::Constructor{inductive,index:0,num_params:0,num_fields:0,is_unsafe:false} if inductive==data)
        || !matches!(&s.family,RuntimeFamily::Constructor{inductive,index:1,num_params:0,num_fields:1,is_unsafe:false} if inductive==data)
        || z.type_.as_ref().ok() != Some(&data_expr)
    {
        return Ok(None);
    }
    let Ok(succ_ty) = &s.type_ else {
        return Ok(None);
    };
    let ExprKind::Pi(binder, domain, result) = succ_ty.kind() else {
        return Ok(None);
    };
    if binder.mult != Multiplicity::Many
        || domain.as_ref() != &data_expr
        || result.as_ref() != &data_expr
    {
        return Ok(None);
    }
    // Initial specialization requires a nondependent, closed data motive. The
    // IR adapter independently classifies this exact result type, never Any.
    let ExprKind::Lam(binder, domain, result) = motive.kind() else {
        return Ok(None);
    };
    if binder.mult != Multiplicity::Many
        || domain.as_ref() != &data_expr
        || !matches!(result.kind(), ExprKind::Const(_, _))
    {
        return Ok(None);
    }
    let (case, arguments) = spine(&body, budget)?;
    let ExprKind::Const(case_name, case_levels) = case.kind() else {
        return Ok(None);
    };
    if arguments.len() != 4 || arguments[1] != Expr::fvar(p[1].0) {
        return Ok(None);
    }
    let ExprKind::Lam(_, domain, body) = arguments[0].kind() else {
        return Ok(None);
    };
    if domain.as_ref() != &data_expr
        || body.as_ref() != &Expr::app(Expr::fvar(p[0].0), Expr::bvar(0))
    {
        return Ok(None);
    }
    let ExprKind::App(zero_fn, unit) = arguments[2].kind() else {
        return Ok(None);
    };
    let ExprKind::Const(unit_name, unit_levels) = unit.kind() else {
        return Ok(None);
    };
    if zero_fn.as_ref() != &Expr::fvar(p[2].0) || !unit_levels.is_empty() {
        return Ok(None);
    }
    let ExprKind::Lam(_, domain, body) = arguments[3].kind() else {
        return Ok(None);
    };
    if domain.as_ref() != &data_expr
        || body.as_ref() != &Expr::app(Expr::fvar(p[3].0), Expr::bvar(0))
    {
        return Ok(None);
    }
    let Some(case_body) = stored(context, case_name, case_levels)? else {
        return Ok(None);
    };
    let Some((q, case_body)) = peel(&case_body, 4, budget)? else {
        return Ok(None);
    };
    if q[1].1 != data_expr {
        return Ok(None);
    }
    let (rec, arguments) = spine(&case_body, budget)?;
    let ExprKind::Const(rec_name, rec_levels) = rec.kind() else {
        return Ok(None);
    };
    if arguments.len() != 4
        || arguments[0] != Expr::fvar(q[0].0)
        || arguments[1] != Expr::fvar(q[2].0)
        || arguments[3] != Expr::fvar(q[1].0)
    {
        return Ok(None);
    }
    let ExprKind::Lam(_, domain, ih) = arguments[2].kind() else {
        return Ok(None);
    };
    if domain.as_ref() != &data_expr {
        return Ok(None);
    }
    let ExprKind::Lam(_, ih_type, body) = ih.kind() else {
        return Ok(None);
    };
    if ih_type.as_ref() != &Expr::app(Expr::fvar(q[0].0), Expr::bvar(0))
        || body.as_ref() != &Expr::app(Expr::fvar(q[3].0), Expr::bvar(1))
    {
        return Ok(None);
    }
    let rec_row = context.declaration(rec_name)?;
    let RuntimeFamily::Recursor {
        all,
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 2,
        k: false,
        is_unsafe: false,
        rules,
    } = &rec_row.family
    else {
        return Ok(None);
    };
    if all != std::slice::from_ref(data)
        || rules.len() != 2
        || rec_levels.len() != rec_row.level_params.len()
        || rules[0].constructor != zero
        || rules[0].num_fields != 0
        || rules[1].constructor != succ
        || rules[1].num_fields != 1
    {
        return Ok(None);
    }
    for (i, rule) in rules.iter().enumerate() {
        let Ok(rhs) = &rule.rhs else { return Ok(None) };
        let rhs = rhs.instantiate_level_params_direct(&rec_row.level_params, rec_levels);
        let Some((r, body)) = peel(&rhs, 3 + i, budget)? else {
            return Ok(None);
        };
        let Ok(header) = &rec_row.type_ else {
            return Ok(None);
        };
        let mut header = header.instantiate_level_params_direct(&rec_row.level_params, rec_levels);
        for (id, actual_domain) in r.iter().take(3) {
            let ExprKind::Pi(_, domain, codomain) = header.kind() else {
                return Ok(None);
            };
            if domain.as_ref() != actual_domain {
                return Ok(None);
            }
            header = codomain.instantiate(&Expr::fvar(*id));
        }
        let ExprKind::Pi(_, major_domain, _) = header.kind() else {
            return Ok(None);
        };
        if major_domain.as_ref() != &data_expr {
            return Ok(None);
        }
        if i == 0 {
            if body != Expr::fvar(r[1].0) {
                return Ok(None);
            }
        } else {
            if r[3].1 != data_expr {
                return Ok(None);
            }
            let recursive = app(
                Expr::const_(rec_name.clone(), rec_levels.to_vec()),
                r.iter().map(|(id, _)| Expr::fvar(*id)),
            );
            let expected = app(Expr::fvar(r[2].0), [Expr::fvar(r[3].0), recursive]);
            if body != expected {
                return Ok(None);
            }
        }
    }
    Ok(Some(Plan {
        source: context.origin(name)?,
        wrapper: context.origin(case_name)?,
        recursor: context.origin(rec_name)?,
        family: context.origin(data)?,
        zero,
        succ,
        unit: unit_name.clone(),
        motive: motive.clone(),
        levels: levels.to_vec(),
    }))
}
