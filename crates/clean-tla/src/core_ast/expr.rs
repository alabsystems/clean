// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::formula::formula_from_core;
use super::shared::{callee_name, module_target_name, single_named_domain};
use crate::encoding::{TlaArithOp, TlaCmpOp, TlaExceptPath, TlaExceptSpec, TlaExpr};
use crate::tla_core::ast as core_ast;
use crate::tla_core::Spanned;
use crate::TlaError;
use std::convert::TryFrom;

pub(super) fn expr_from_core(expr: &Spanned<core_ast::Expr>) -> Result<TlaExpr, TlaError> {
    if let Some(converted) = convert_atomic_expr(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_operator_expr(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_set_expr(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_function_expr(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_structural_expr(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_control_expr(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_arith_expr(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_action_expr(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_temporal_value_expr(expr)? {
        return Ok(converted);
    }
    unsupported_value_expr(&expr.node)
}

fn convert_action_expr(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        // `e'` — next-state value of `e`. Encoded as a dedicated `Prime` node so
        // the successor-state value is never conflated with the current state.
        core_ast::Expr::Prime(inner) => Ok(Some(TlaExpr::Prime(Box::new(expr_from_core(inner)?)))),
        _ => Ok(None),
    }
}

/// Temporal operators (`[]`, `<>`, `~>`, `WF`/`SF`, `ENABLED`, `UNCHANGED`)
/// occurring in *value* position.
///
/// TLA+ is untyped, so a temporal formula can be the body of an operator
/// definition (`Liveness == []<>P`) or otherwise appear where a value
/// expression is expected. Such a node has no native [`TlaExpr`] variant — the
/// temporal layer lives on [`TlaFormula`] — so it is converted through
/// [`formula_from_core`] (which recurses into nested temporal sub-formulas,
/// preserving e.g. `[]<>P` = infinitely often and `<>[]P` = eventually always)
/// and wrapped in [`TlaExpr::TemporalFormula`]. The expression translator
/// re-enters the formula translator for that wrapper, so the standard temporal
/// semantics are kept end-to-end.
fn convert_temporal_value_expr(
    expr: &Spanned<core_ast::Expr>,
) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        core_ast::Expr::Always(_)
        | core_ast::Expr::Eventually(_)
        | core_ast::Expr::LeadsTo(_, _)
        | core_ast::Expr::WeakFair(_, _)
        | core_ast::Expr::StrongFair(_, _)
        | core_ast::Expr::Enabled(_)
        | core_ast::Expr::Unchanged(_) => Ok(Some(TlaExpr::TemporalFormula(Box::new(
            formula_from_core(expr)?,
        )))),
        _ => Ok(None),
    }
}

fn convert_atomic_expr(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        core_ast::Expr::Bool(value) => Ok(Some(if *value {
            TlaExpr::True
        } else {
            TlaExpr::False
        })),
        core_ast::Expr::Int(value) => {
            let value = i64::try_from(value).map_err(|_| {
                TlaError::UnsupportedCoreAst(format!(
                    "integer literal exceeds clean-tla i64 range: {value}"
                ))
            })?;
            Ok(Some(TlaExpr::Int(value)))
        }
        core_ast::Expr::String(value) => Ok(Some(TlaExpr::Str(value.clone()))),
        core_ast::Expr::Ident(name, _) | core_ast::Expr::StateVar(name, _, _) => {
            Ok(Some(TlaExpr::Var(name.clone())))
        }
        core_ast::Expr::OpRef(name) => Ok(Some(TlaExpr::Const(name.clone()))),
        core_ast::Expr::Label(label) => expr_from_core(label.body.as_ref()).map(Some),
        _ => Ok(None),
    }
}

fn convert_operator_expr(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        core_ast::Expr::Apply(callee, args) => {
            let name = callee_name(callee).ok_or_else(|| {
                TlaError::UnsupportedCoreAst(format!(
                    "operator application with non-name callee: {:?}",
                    callee.node
                ))
            })?;
            Ok(Some(TlaExpr::OpApply(
                name,
                args.iter()
                    .map(expr_from_core)
                    .collect::<Result<Vec<_>, _>>()?,
            )))
        }
        core_ast::Expr::ModuleRef(target, name, args) => Ok(Some(TlaExpr::OpApply(
            format!("{}!{}", module_target_name(target), name),
            args.iter()
                .map(expr_from_core)
                .collect::<Result<Vec<_>, _>>()?,
        ))),
        _ => Ok(None),
    }
}

fn convert_set_expr(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        core_ast::Expr::SetEnum(elems) => Ok(Some(TlaExpr::SetEnum(
            elems
                .iter()
                .map(expr_from_core)
                .collect::<Result<Vec<_>, _>>()?,
        ))),
        core_ast::Expr::SetBuilder(template, bounds) => {
            let (name, domain) = single_named_domain(bounds, "set builder")?;
            Ok(Some(TlaExpr::SetMap(
                Box::new(expr_from_core(template)?),
                name,
                Box::new(expr_from_core(domain)?),
                None,
            )))
        }
        core_ast::Expr::SetFilter(bound, predicate) => {
            let name = super::shared::bound_name(bound, "set filter")?;
            let domain = bound.domain.as_deref().ok_or_else(|| {
                TlaError::UnsupportedCoreAst(
                    "set filter without domain cannot map to clean-tla".to_string(),
                )
            })?;
            Ok(Some(TlaExpr::SetOf(
                Box::new(expr_from_core(domain)?),
                name,
                Box::new(formula_from_core(predicate)?),
            )))
        }
        core_ast::Expr::In(elem, set) => Ok(Some(TlaExpr::Mem(
            Box::new(expr_from_core(elem)?),
            Box::new(expr_from_core(set)?),
        ))),
        core_ast::Expr::Subseteq(lhs, rhs) => Ok(Some(TlaExpr::Subset(
            Box::new(expr_from_core(lhs)?),
            Box::new(expr_from_core(rhs)?),
        ))),
        core_ast::Expr::Union(lhs, rhs) => binary_expr(TlaExpr::Union, lhs, rhs).map(Some),
        core_ast::Expr::Intersect(lhs, rhs) => binary_expr(TlaExpr::Inter, lhs, rhs).map(Some),
        core_ast::Expr::SetMinus(lhs, rhs) => binary_expr(TlaExpr::Diff, lhs, rhs).map(Some),
        core_ast::Expr::Powerset(set) => {
            Ok(Some(TlaExpr::PowerSet(Box::new(expr_from_core(set)?))))
        }
        core_ast::Expr::BigUnion(set) => {
            Ok(Some(TlaExpr::BigUnion(Box::new(expr_from_core(set)?))))
        }
        _ => Ok(None),
    }
}

fn convert_function_expr(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        core_ast::Expr::FuncDef(bounds, body) => {
            let (name, domain) = single_named_domain(bounds, "function definition")?;
            Ok(Some(TlaExpr::Func(
                name,
                Box::new(expr_from_core(domain)?),
                Box::new(expr_from_core(body)?),
            )))
        }
        core_ast::Expr::FuncApply(func, arg) => Ok(Some(TlaExpr::Apply(
            Box::new(expr_from_core(func)?),
            Box::new(expr_from_core(arg)?),
        ))),
        core_ast::Expr::Domain(func) => Ok(Some(TlaExpr::Domain(Box::new(expr_from_core(func)?)))),
        // `[S -> T]` — the set of total functions from `S` into `T`.
        core_ast::Expr::FuncSet(domain, codomain) => Ok(Some(TlaExpr::FuncSet(
            Box::new(expr_from_core(domain)?),
            Box::new(expr_from_core(codomain)?),
        ))),
        // `[f EXCEPT !p1 = v1, ...]` — function/record update. Each spec carries
        // a path of index (`![e]`) and field (`!.name`) selectors plus the
        // replacement value; both are translated structurally so deep updates
        // round-trip exactly.
        core_ast::Expr::Except(func, specs) => Ok(Some(TlaExpr::Except(
            Box::new(expr_from_core(func)?),
            specs
                .iter()
                .map(except_spec_from_core)
                .collect::<Result<Vec<_>, _>>()?,
        ))),
        _ => Ok(None),
    }
}

fn except_spec_from_core(spec: &core_ast::ExceptSpec) -> Result<TlaExceptSpec, TlaError> {
    Ok(TlaExceptSpec {
        path: spec
            .path
            .iter()
            .map(except_path_from_core)
            .collect::<Result<Vec<_>, _>>()?,
        value: expr_from_core(&spec.value)?,
    })
}

fn except_path_from_core(element: &core_ast::ExceptPathElement) -> Result<TlaExceptPath, TlaError> {
    match element {
        core_ast::ExceptPathElement::Index(key) => Ok(TlaExceptPath::Index(expr_from_core(key)?)),
        core_ast::ExceptPathElement::Field(field) => {
            Ok(TlaExceptPath::Field(field.name.node.clone()))
        }
    }
}

fn convert_structural_expr(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        core_ast::Expr::Record(fields) => Ok(Some(TlaExpr::Record(
            fields
                .iter()
                .map(|(name, value)| Ok((name.node.clone(), expr_from_core(value)?)))
                .collect::<Result<Vec<_>, TlaError>>()?,
        ))),
        core_ast::Expr::RecordAccess(record, field) => Ok(Some(TlaExpr::Field(
            Box::new(expr_from_core(record)?),
            field.name.node.clone(),
        ))),
        // `[f1: S1, f2: S2, ...]` — record type / set constructor: the set of
        // all records whose `f_i` field ranges over the set `S_i`. Field names
        // are kept in order; each set is translated structurally, mirroring the
        // `Record` value constructor above.
        core_ast::Expr::RecordSet(fields) => Ok(Some(TlaExpr::RecordSet(
            fields
                .iter()
                .map(|(name, set)| Ok((name.node.clone(), expr_from_core(set)?)))
                .collect::<Result<Vec<_>, TlaError>>()?,
        ))),
        core_ast::Expr::Tuple(values) => Ok(Some(TlaExpr::Tuple(
            values
                .iter()
                .map(expr_from_core)
                .collect::<Result<Vec<_>, _>>()?,
        ))),
        // `S \X T \X ...` — Cartesian product. Factors are converted in order
        // and folded left-associatively at encoding time over `TLA.times`.
        core_ast::Expr::Times(factors) => Ok(Some(TlaExpr::Times(
            factors
                .iter()
                .map(expr_from_core)
                .collect::<Result<Vec<_>, _>>()?,
        ))),
        _ => Ok(None),
    }
}

fn convert_control_expr(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        // CHOOSE x ∈ S : P(x) — Hilbert's epsilon over the domain `S`.
        //
        // Only the *bounded* form is representable: `TlaExpr::Choose` (and its
        // `TLA.choose S (λx. P)` encoding) is defined relative to an explicit
        // domain set. The unbounded form `CHOOSE x : P(x)` ranges over the
        // entire TLA+ universe, which has no domain expression to supply; we
        // reject it rather than fabricate a domain, since choosing from a
        // concrete `S` is not semantically equal to choosing from the universe.
        core_ast::Expr::Choose(bound, predicate) => {
            let name = super::shared::bound_name(bound, "CHOOSE")?;
            let domain = bound.domain.as_deref().ok_or_else(|| {
                TlaError::UnsupportedCoreAst(
                    "unbounded CHOOSE (CHOOSE x : P) cannot map to clean-tla: \
                     no domain to range over"
                        .to_string(),
                )
            })?;
            Ok(Some(TlaExpr::Choose(
                name,
                Box::new(expr_from_core(domain)?),
                Box::new(formula_from_core(predicate)?),
            )))
        }
        core_ast::Expr::If(cond, then_branch, else_branch) => Ok(Some(TlaExpr::IfThenElse(
            Box::new(formula_from_core(cond)?),
            Box::new(expr_from_core(then_branch)?),
            Box::new(expr_from_core(else_branch)?),
        ))),
        core_ast::Expr::Case(arms, default) => Ok(Some(TlaExpr::Case(
            arms.iter()
                .map(|arm| Ok((formula_from_core(&arm.guard)?, expr_from_core(&arm.body)?)))
                .collect::<Result<Vec<_>, TlaError>>()?,
            default
                .as_ref()
                .map(|expr| expr_from_core(expr).map(Box::new))
                .transpose()?,
        ))),
        core_ast::Expr::Let(defs, body) => convert_let_expr(defs, body).map(Some),
        _ => Ok(None),
    }
}

fn convert_arith_expr(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaExpr>, TlaError> {
    match &expr.node {
        core_ast::Expr::Add(lhs, rhs) => binary_arith(TlaArithOp::Add, lhs, rhs).map(Some),
        core_ast::Expr::Sub(lhs, rhs) => binary_arith(TlaArithOp::Sub, lhs, rhs).map(Some),
        core_ast::Expr::Mul(lhs, rhs) => binary_arith(TlaArithOp::Mul, lhs, rhs).map(Some),
        core_ast::Expr::Div(lhs, rhs) | core_ast::Expr::IntDiv(lhs, rhs) => {
            binary_arith(TlaArithOp::Div, lhs, rhs).map(Some)
        }
        core_ast::Expr::Mod(lhs, rhs) => binary_arith(TlaArithOp::Mod, lhs, rhs).map(Some),
        // `b ^ e` — TLA+ exponentiation (the `Naturals` module's `^` operator).
        core_ast::Expr::Pow(base, exp) => binary_arith(TlaArithOp::Pow, base, exp).map(Some),
        core_ast::Expr::Neg(value) => Ok(Some(TlaExpr::Neg(Box::new(expr_from_core(value)?)))),
        core_ast::Expr::Range(lhs, rhs) => Ok(Some(TlaExpr::Range(
            Box::new(expr_from_core(lhs)?),
            Box::new(expr_from_core(rhs)?),
        ))),
        core_ast::Expr::Lt(lhs, rhs) => binary_cmp(TlaCmpOp::Lt, lhs, rhs).map(Some),
        core_ast::Expr::Leq(lhs, rhs) => binary_cmp(TlaCmpOp::Le, lhs, rhs).map(Some),
        core_ast::Expr::Gt(lhs, rhs) => binary_cmp(TlaCmpOp::Gt, lhs, rhs).map(Some),
        core_ast::Expr::Geq(lhs, rhs) => binary_cmp(TlaCmpOp::Ge, lhs, rhs).map(Some),
        _ => Ok(None),
    }
}

/// Lower a `LET d_1 == e_1  ...  d_n == e_n IN body` into clean-tla's
/// single-binding [`TlaExpr::Let`].
///
/// # Why multi-definition LET is not a trivial desugaring
///
/// In TLA+ the definitions of a single `LET` are **simultaneously** in scope:
/// every `e_i` and `body` may reference every `d_j` (including forward and
/// mutual/recursive references). clean-tla's only LET node binds **one** name
/// whose value is evaluated in the *enclosing* scope (it lowers to
/// `(λname. body) value`), so it cannot represent simultaneous binding
/// directly.
///
/// A right- or left-nested chain of single-binding LETs only reproduces the
/// TLA+ meaning for the **subset that has no forward / self / mutual
/// references**. Concretely, lowering the defs left-to-right as
/// `LET d_1 == e_1 IN (LET d_2 == e_2 IN (... IN body))` makes `e_i` able to
/// see `d_1 .. d_{i-1}` (the earlier siblings) but *not* `d_i .. d_n` (itself
/// and the later siblings). That nesting is provably equivalent to the
/// simultaneous form exactly when no `e_i` references its own name or any name
/// bound at or after it. Any LET that does have such a reference would change
/// meaning under the nesting, so it is rejected with a precise message rather
/// than silently mis-scoped (exactness-or-reject — clean-tla is a faithful
/// encoding surface).
///
/// Self-recursive definitions (`OperatorDef::is_recursive`) and parameterized
/// definitions are likewise rejected: neither is expressible by the
/// single-binding node.
fn convert_let_expr(
    defs: &[core_ast::OperatorDef],
    body: &Spanned<core_ast::Expr>,
) -> Result<TlaExpr, TlaError> {
    if defs.is_empty() {
        return Err(TlaError::UnsupportedCoreAst(
            "LET with no definitions cannot map to clean-tla".to_string(),
        ));
    }

    // Each definition must be a plain (non-parameterized, non-recursive) value
    // binding to be representable by the single-binding LET node.
    for def in defs {
        if !def.params.is_empty() {
            return Err(TlaError::UnsupportedCoreAst(
                "parameterized LET definitions cannot map to clean-tla".to_string(),
            ));
        }
        if def.is_recursive {
            return Err(TlaError::UnsupportedCoreAst(
                "recursive LET definitions cannot map to clean-tla".to_string(),
            ));
        }
    }

    // Reject forward / self / mutual references: definition `i` may only refer
    // to earlier siblings (`d_0 .. d_{i-1}`). If `e_i` mentions its own name or
    // any later sibling's name, the left-nested single-binding lowering would
    // change the binding (TLA+ scopes all siblings simultaneously), so the LET
    // is not faithfully representable.
    for (i, def) in defs.iter().enumerate() {
        let forbidden = &defs[i..];
        if let Some(referenced) = first_referenced_name(&def.body, forbidden) {
            return Err(TlaError::UnsupportedCoreAst(format!(
                "LET definition `{}` references `{}`, which is bound at or after it \
                 (forward/self/mutual references are not representable in clean-tla)",
                def.name.node, referenced
            )));
        }
    }

    // Left-nest: d_0 is the outermost binding so each later e_i sees it.
    //   LET d_0 == e_0  d_1 == e_1 IN body
    //     => Let(d_0, e_0, Let(d_1, e_1, body))
    let mut acc = expr_from_core(body)?;
    for def in defs.iter().rev() {
        acc = TlaExpr::Let(
            def.name.node.clone(),
            Box::new(expr_from_core(&def.body)?),
            Box::new(acc),
        );
    }
    Ok(acc)
}

/// Return the first name from `forbidden` that occurs anywhere in `expr`, or
/// `None` if none do.
///
/// This is a deliberately conservative *syntactic* scan: it treats any textual
/// occurrence of a forbidden name (as an identifier, state variable, operator
/// reference, or applied/module-referenced operator) as a reference, even if an
/// inner binder would shadow it. Over-detection only causes extra rejections of
/// otherwise-faithful LETs; it can never miss a real reference, so the
/// soundness direction (never mis-scope) is preserved. Unknown future `Expr`
/// shapes fall through to a conservative "referenced" result for the same
/// reason.
fn first_referenced_name<'a>(
    expr: &Spanned<core_ast::Expr>,
    forbidden: &'a [core_ast::OperatorDef],
) -> Option<&'a str> {
    forbidden
        .iter()
        .map(|def| def.name.node.as_str())
        .find(|name| expr_references_name(expr, name))
}

/// Whether `name` occurs free-or-shadowed anywhere in `expr` (conservative;
/// see [`first_referenced_name`]).
fn expr_references_name(expr: &Spanned<core_ast::Expr>, name: &str) -> bool {
    use core_ast::Expr;
    let any = |es: &[Spanned<Expr>]| es.iter().any(|e| expr_references_name(e, name));
    match &expr.node {
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => false,
        Expr::Ident(n, _) | Expr::StateVar(n, _, _) | Expr::OpRef(n) => n == name,
        Expr::Apply(callee, args) => expr_references_name(callee, name) || any(args),
        Expr::ModuleRef(target, op, args) => {
            op == name || module_target_references_name(target, name) || any(args)
        }
        Expr::InstanceExpr(_, subs) => subs.iter().any(|s| expr_references_name(&s.to, name)),
        Expr::Lambda(_, body) => expr_references_name(body, name),
        Expr::Label(label) => expr_references_name(&label.body, name),
        Expr::And(l, r)
        | Expr::Or(l, r)
        | Expr::Implies(l, r)
        | Expr::Equiv(l, r)
        | Expr::In(l, r)
        | Expr::NotIn(l, r)
        | Expr::Subseteq(l, r)
        | Expr::Union(l, r)
        | Expr::Intersect(l, r)
        | Expr::SetMinus(l, r)
        | Expr::FuncApply(l, r)
        | Expr::FuncSet(l, r)
        | Expr::LeadsTo(l, r)
        | Expr::WeakFair(l, r)
        | Expr::StrongFair(l, r)
        | Expr::Eq(l, r)
        | Expr::Neq(l, r)
        | Expr::Lt(l, r)
        | Expr::Leq(l, r)
        | Expr::Gt(l, r)
        | Expr::Geq(l, r)
        | Expr::Add(l, r)
        | Expr::Sub(l, r)
        | Expr::Mul(l, r)
        | Expr::Div(l, r)
        | Expr::IntDiv(l, r)
        | Expr::Mod(l, r)
        | Expr::Pow(l, r)
        | Expr::Range(l, r) => expr_references_name(l, name) || expr_references_name(r, name),
        Expr::Not(inner)
        | Expr::Powerset(inner)
        | Expr::BigUnion(inner)
        | Expr::Domain(inner)
        | Expr::Prime(inner)
        | Expr::Always(inner)
        | Expr::Eventually(inner)
        | Expr::Enabled(inner)
        | Expr::Unchanged(inner)
        | Expr::Neg(inner) => expr_references_name(inner, name),
        Expr::Forall(bounds, body)
        | Expr::Exists(bounds, body)
        | Expr::SetBuilder(body, bounds)
        | Expr::FuncDef(bounds, body) => {
            bounds.iter().any(|b| bound_var_references_name(b, name))
                || expr_references_name(body, name)
        }
        Expr::Choose(bound, body) | Expr::SetFilter(bound, body) => {
            bound_var_references_name(bound, name) || expr_references_name(body, name)
        }
        Expr::SetEnum(es) | Expr::Tuple(es) | Expr::Times(es) => any(es),
        Expr::Except(base, specs) => {
            expr_references_name(base, name)
                || specs
                    .iter()
                    .any(|spec| except_spec_references_name(spec, name))
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            fields.iter().any(|(_, e)| expr_references_name(e, name))
        }
        Expr::RecordAccess(base, _) => expr_references_name(base, name),
        Expr::If(c, t, e) => {
            expr_references_name(c, name)
                || expr_references_name(t, name)
                || expr_references_name(e, name)
        }
        Expr::Case(arms, default) => {
            arms.iter().any(|arm| {
                expr_references_name(&arm.guard, name) || expr_references_name(&arm.body, name)
            }) || default
                .as_ref()
                .is_some_and(|d| expr_references_name(d, name))
        }
        Expr::Let(inner_defs, inner_body) => {
            inner_defs
                .iter()
                .any(|d| expr_references_name(&d.body, name))
                || expr_references_name(inner_body, name)
        }
        Expr::SubstIn(subs, inner) => {
            subs.iter().any(|s| expr_references_name(&s.to, name))
                || expr_references_name(inner, name)
        }
        // Any variant not enumerated above is treated as referencing the name:
        // a conservative default that errs toward rejection rather than risking
        // an unsound mis-scoped lowering.
        #[allow(unreachable_patterns)]
        _ => true,
    }
}

fn bound_var_references_name(bound: &core_ast::BoundVar, name: &str) -> bool {
    bound
        .domain
        .as_ref()
        .is_some_and(|d| expr_references_name(d, name))
}

fn except_spec_references_name(spec: &core_ast::ExceptSpec, name: &str) -> bool {
    expr_references_name(&spec.value, name)
        || spec.path.iter().any(|elem| match elem {
            core_ast::ExceptPathElement::Index(e) => expr_references_name(e, name),
            core_ast::ExceptPathElement::Field(_) => false,
        })
}

fn module_target_references_name(target: &core_ast::ModuleTarget, name: &str) -> bool {
    match target {
        core_ast::ModuleTarget::Named(_) => false,
        core_ast::ModuleTarget::Parameterized(_, args) => {
            args.iter().any(|e| expr_references_name(e, name))
        }
        core_ast::ModuleTarget::Chained(base) => expr_references_name(base, name),
    }
}

fn binary_expr(
    constructor: fn(Box<TlaExpr>, Box<TlaExpr>) -> TlaExpr,
    lhs: &Spanned<core_ast::Expr>,
    rhs: &Spanned<core_ast::Expr>,
) -> Result<TlaExpr, TlaError> {
    Ok(constructor(
        Box::new(expr_from_core(lhs)?),
        Box::new(expr_from_core(rhs)?),
    ))
}

fn binary_arith(
    op: TlaArithOp,
    lhs: &Spanned<core_ast::Expr>,
    rhs: &Spanned<core_ast::Expr>,
) -> Result<TlaExpr, TlaError> {
    Ok(TlaExpr::Arith(
        op,
        Box::new(expr_from_core(lhs)?),
        Box::new(expr_from_core(rhs)?),
    ))
}

fn binary_cmp(
    op: TlaCmpOp,
    lhs: &Spanned<core_ast::Expr>,
    rhs: &Spanned<core_ast::Expr>,
) -> Result<TlaExpr, TlaError> {
    Ok(TlaExpr::Cmp(
        op,
        Box::new(expr_from_core(lhs)?),
        Box::new(expr_from_core(rhs)?),
    ))
}

fn unsupported_value_expr(expr: &core_ast::Expr) -> Result<TlaExpr, TlaError> {
    Err(TlaError::UnsupportedCoreAst(format!(
        "tla-core expression variant not representable as clean-tla value expr: {:?}",
        expr
    )))
}
