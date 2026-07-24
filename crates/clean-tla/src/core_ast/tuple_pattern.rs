// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful desugaring of tuple-pattern quantifier binders.
//!
//! TLA+ allows a bounded quantifier to destructure each element of its domain
//! with a tuple pattern:
//!
//! ```tla
//! \E <<x, y>> \in S : P(x, y)
//! \A <<x, y>> \in S : P(x, y)
//! ```
//!
//! Here `S` is a set of pairs (tuples); the pattern binds `x` to the first
//! component and `y` to the second component of each element. clean-tla's
//! quantifier nodes ([`TlaFormula::ForallIn`] / [`TlaFormula::ExistsIn`]) bind a
//! **single** name ranging over a domain, so a tuple pattern has no direct
//! target.
//!
//! # Faithful encoding (exactness-or-reject)
//!
//! The standard meaning-preserving rewrite introduces one fresh element name
//! `t` (not occurring anywhere in the binder's domain or the quantifier body)
//! and replaces each pattern component `x_i` with the projection `t[i]`:
//!
//! ```tla
//! \E <<x, y>> \in S : P(x, y)   ==   \E t \in S : P(t[1], t[2])
//! ```
//!
//! In TLA+ a tuple `<<a, b>>` is the function `(1 :> a) @@ (2 :> b)`, so
//! `t[1]` / `t[2]` are exactly its components and the rewrite is an equality,
//! not an approximation. The projection `t[i]` is built as
//! `FuncApply(t, Int(i))`, which downstream encodes to `TLA.apply t i` — the
//! same encoding TLA+ tuple indexing already uses.
//!
//! ## Why a *globally* fresh name
//!
//! The replacement `t[i]` mentions `t`. To guarantee no inner binder inside the
//! body can capture it, `t` is chosen distinct from **every** name appearing in
//! the body and domain (free or bound), not merely the free ones. Combined with
//! shadow-aware substitution (a nested binder that re-binds `x_i` stops the
//! `x_i` substitution within its scope), this makes the rewrite capture-free.
//!
//! ## What is rejected
//!
//! An *unbounded* tuple pattern (`\E <<x, y>> : P`, no domain) has no set to
//! range over and no element to project, so it is rejected with a precise
//! [`TlaError::UnsupportedCoreAst`] rather than fabricating a domain.

use crate::tla_core::ast as core_ast;
use crate::tla_core::Spanned;
use crate::TlaError;
use std::collections::{HashMap, HashSet};

/// Rewrite every tuple-pattern binder in a quantifier's bound list into a
/// fresh single-name binder, returning the rewritten bounds together with the
/// rewritten body.
///
/// Binders are processed left-to-right. The substitution introduced by an
/// earlier binder is applied to the *domains* of later binders (a later
/// binder's domain is evaluated in the scope of the earlier ones) and finally
/// to the body, exactly mirroring TLA+ scoping. Non-tuple binders are returned
/// unchanged (their domains are still rewritten so they see earlier siblings'
/// substitutions).
///
/// Returns `Ok(None)` when no binder uses a tuple pattern, so callers can keep
/// the original (already-`Spanned`) nodes on the common path.
pub(super) fn desugar_quantifier_bounds(
    bounds: &[core_ast::BoundVar],
    body: &Spanned<core_ast::Expr>,
    context: &str,
) -> Result<Option<(Vec<core_ast::BoundVar>, Spanned<core_ast::Expr>)>, TlaError> {
    if !bounds
        .iter()
        .any(|b| matches!(b.pattern, Some(core_ast::BoundPattern::Tuple(_))))
    {
        return Ok(None);
    }

    // Names that the fresh element variable must avoid: everything mentioned in
    // any binder domain and in the body. Collecting bound names too (not just
    // free ones) guarantees the fresh `t` cannot be captured by an inner binder.
    let mut used = HashSet::new();
    for bound in bounds {
        if let Some(domain) = bound.domain.as_deref() {
            collect_names(domain, &mut used);
        }
        // Pattern-introduced names are also "in use" for the surrounding scope.
        match &bound.pattern {
            Some(core_ast::BoundPattern::Tuple(names)) => {
                used.extend(names.iter().map(|n| n.node.clone()));
            }
            Some(core_ast::BoundPattern::Var(name)) => {
                used.insert(name.node.clone());
            }
            None => {
                used.insert(bound.name.node.clone());
            }
        }
    }
    collect_names(body, &mut used);

    let mut subst: HashMap<String, core_ast::Expr> = HashMap::new();
    let mut fresh_counter = 0usize;
    let mut new_bounds = Vec::with_capacity(bounds.len());

    for bound in bounds {
        // A later binder's domain lives in the scope of earlier binders, so it
        // must reflect substitutions accumulated so far.
        let domain = bound
            .domain
            .as_ref()
            .map(|d| Box::new(substitute(d, &subst)));

        match &bound.pattern {
            Some(core_ast::BoundPattern::Tuple(components)) => {
                let domain = domain.ok_or_else(|| {
                    TlaError::UnsupportedCoreAst(format!(
                        "{context} tuple pattern without an explicit domain cannot map to \
                         clean-tla: no set to range over"
                    ))
                })?;
                let fresh = fresh_name(&used, &mut fresh_counter);
                used.insert(fresh.clone());

                // Map each component `x_i` to the projection `fresh[i]`
                // (1-based, matching TLA+ tuple indexing).
                for (idx, component) in components.iter().enumerate() {
                    let projection = core_ast::Expr::FuncApply(
                        Box::new(Spanned::dummy(core_ast::Expr::Ident(
                            fresh.clone(),
                            crate::tla_core::intern_name(&fresh),
                        ))),
                        Box::new(Spanned::dummy(core_ast::Expr::Int(
                            ((idx + 1) as i64).into(),
                        ))),
                    );
                    subst.insert(component.node.clone(), projection);
                }

                new_bounds.push(core_ast::BoundVar {
                    name: Spanned::dummy(fresh.clone()),
                    domain: Some(domain),
                    pattern: None,
                });
            }
            _ => {
                new_bounds.push(core_ast::BoundVar {
                    name: bound.name.clone(),
                    domain,
                    pattern: bound.pattern.clone(),
                });
            }
        }
    }

    let new_body = substitute(body, &subst);
    Ok(Some((new_bounds, new_body)))
}

/// Pick a name of the form `__tla_tuple_N` not present in `used`.
fn fresh_name(used: &HashSet<String>, counter: &mut usize) -> String {
    loop {
        let candidate = format!("__tla_tuple_{counter}");
        *counter += 1;
        if !used.contains(&candidate) {
            return candidate;
        }
    }
}

/// Capture-avoiding, shadow-aware substitution of identifiers/operator/state
/// references by replacement expressions.
///
/// `subst` maps a *source name* to its replacement. A binder that re-binds one
/// of those names shadows the substitution inside its own scope: the rebound
/// names are dropped from the active map while recursing into the body (but the
/// binder's domain, which is evaluated in the outer scope, still uses the full
/// map). Because every replacement mentions only a globally-fresh name (see
/// [`desugar_quantifier_bounds`]), no inner binder can capture it.
fn substitute(
    expr: &Spanned<core_ast::Expr>,
    subst: &HashMap<String, core_ast::Expr>,
) -> Spanned<core_ast::Expr> {
    use core_ast::Expr;

    if subst.is_empty() {
        return expr.clone();
    }

    let rebox = |e: &Spanned<Expr>| Box::new(substitute(e, subst));
    let revec = |es: &[Spanned<Expr>]| es.iter().map(|e| substitute(e, subst)).collect::<Vec<_>>();

    let node = match &expr.node {
        Expr::Ident(name, id) => match subst.get(name) {
            Some(replacement) => replacement.clone(),
            None => Expr::Ident(name.clone(), *id),
        },
        Expr::OpRef(name) => match subst.get(name) {
            Some(replacement) => replacement.clone(),
            None => Expr::OpRef(name.clone()),
        },
        Expr::StateVar(name, slot, id) => match subst.get(name) {
            Some(replacement) => replacement.clone(),
            None => Expr::StateVar(name.clone(), *slot, *id),
        },
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => expr.node.clone(),

        Expr::Apply(callee, args) => Expr::Apply(rebox(callee), revec(args)),
        Expr::ModuleRef(target, op, args) => Expr::ModuleRef(
            substitute_module_target(target, subst),
            op.clone(),
            revec(args),
        ),
        Expr::InstanceExpr(name, subs) => {
            Expr::InstanceExpr(name.clone(), substitute_subs(subs, subst))
        }
        Expr::Label(label) => Expr::Label(core_ast::ExprLabel {
            name: label.name.clone(),
            body: rebox(&label.body),
        }),

        Expr::And(l, r) => Expr::And(rebox(l), rebox(r)),
        Expr::Or(l, r) => Expr::Or(rebox(l), rebox(r)),
        Expr::Not(e) => Expr::Not(rebox(e)),
        Expr::Implies(l, r) => Expr::Implies(rebox(l), rebox(r)),
        Expr::Equiv(l, r) => Expr::Equiv(rebox(l), rebox(r)),

        Expr::Forall(bounds, body) => {
            let (bounds, body) = substitute_binders(bounds, body, subst);
            Expr::Forall(bounds, Box::new(body))
        }
        Expr::Exists(bounds, body) => {
            let (bounds, body) = substitute_binders(bounds, body, subst);
            Expr::Exists(bounds, Box::new(body))
        }
        Expr::SetBuilder(template, bounds) => {
            // The template is in the scope of the binders, so it shares their
            // shadowing; reuse the same binder logic with template as "body".
            let (bounds, template) = substitute_binders(bounds, template, subst);
            Expr::SetBuilder(Box::new(template), bounds)
        }
        Expr::FuncDef(bounds, body) => {
            let (bounds, body) = substitute_binders(bounds, body, subst);
            Expr::FuncDef(bounds, Box::new(body))
        }
        Expr::Choose(bound, body) => {
            let (bound, body) = substitute_single_binder(bound, body, subst);
            Expr::Choose(bound, Box::new(body))
        }
        Expr::SetFilter(bound, body) => {
            let (bound, body) = substitute_single_binder(bound, body, subst);
            Expr::SetFilter(bound, Box::new(body))
        }

        Expr::SetEnum(es) => Expr::SetEnum(revec(es)),
        Expr::In(l, r) => Expr::In(rebox(l), rebox(r)),
        Expr::NotIn(l, r) => Expr::NotIn(rebox(l), rebox(r)),
        Expr::Subseteq(l, r) => Expr::Subseteq(rebox(l), rebox(r)),
        Expr::Union(l, r) => Expr::Union(rebox(l), rebox(r)),
        Expr::Intersect(l, r) => Expr::Intersect(rebox(l), rebox(r)),
        Expr::SetMinus(l, r) => Expr::SetMinus(rebox(l), rebox(r)),
        Expr::Powerset(e) => Expr::Powerset(rebox(e)),
        Expr::BigUnion(e) => Expr::BigUnion(rebox(e)),

        Expr::FuncApply(f, x) => Expr::FuncApply(rebox(f), rebox(x)),
        Expr::Domain(e) => Expr::Domain(rebox(e)),
        Expr::Except(base, specs) => Expr::Except(
            rebox(base),
            specs
                .iter()
                .map(|spec| core_ast::ExceptSpec {
                    path: spec
                        .path
                        .iter()
                        .map(|elem| match elem {
                            core_ast::ExceptPathElement::Index(e) => {
                                core_ast::ExceptPathElement::Index(substitute(e, subst))
                            }
                            core_ast::ExceptPathElement::Field(f) => {
                                core_ast::ExceptPathElement::Field(f.clone())
                            }
                        })
                        .collect(),
                    value: substitute(&spec.value, subst),
                })
                .collect(),
        ),
        Expr::FuncSet(l, r) => Expr::FuncSet(rebox(l), rebox(r)),

        Expr::Record(fields) => Expr::Record(
            fields
                .iter()
                .map(|(n, e)| (n.clone(), substitute(e, subst)))
                .collect(),
        ),
        Expr::RecordAccess(base, field) => Expr::RecordAccess(rebox(base), field.clone()),
        Expr::RecordSet(fields) => Expr::RecordSet(
            fields
                .iter()
                .map(|(n, e)| (n.clone(), substitute(e, subst)))
                .collect(),
        ),

        Expr::Tuple(es) => Expr::Tuple(revec(es)),
        Expr::Times(es) => Expr::Times(revec(es)),

        Expr::Prime(e) => Expr::Prime(rebox(e)),
        Expr::Always(e) => Expr::Always(rebox(e)),
        Expr::Eventually(e) => Expr::Eventually(rebox(e)),
        Expr::LeadsTo(l, r) => Expr::LeadsTo(rebox(l), rebox(r)),
        Expr::WeakFair(l, r) => Expr::WeakFair(rebox(l), rebox(r)),
        Expr::StrongFair(l, r) => Expr::StrongFair(rebox(l), rebox(r)),
        Expr::Enabled(e) => Expr::Enabled(rebox(e)),
        Expr::Unchanged(e) => Expr::Unchanged(rebox(e)),

        Expr::If(c, t, e) => Expr::If(rebox(c), rebox(t), rebox(e)),
        Expr::Case(arms, default) => Expr::Case(
            arms.iter()
                .map(|arm| core_ast::CaseArm {
                    guard: substitute(&arm.guard, subst),
                    body: substitute(&arm.body, subst),
                })
                .collect(),
            default.as_ref().map(|d| rebox(d)),
        ),

        Expr::Eq(l, r) => Expr::Eq(rebox(l), rebox(r)),
        Expr::Neq(l, r) => Expr::Neq(rebox(l), rebox(r)),
        Expr::Lt(l, r) => Expr::Lt(rebox(l), rebox(r)),
        Expr::Leq(l, r) => Expr::Leq(rebox(l), rebox(r)),
        Expr::Gt(l, r) => Expr::Gt(rebox(l), rebox(r)),
        Expr::Geq(l, r) => Expr::Geq(rebox(l), rebox(r)),

        Expr::Add(l, r) => Expr::Add(rebox(l), rebox(r)),
        Expr::Sub(l, r) => Expr::Sub(rebox(l), rebox(r)),
        Expr::Mul(l, r) => Expr::Mul(rebox(l), rebox(r)),
        Expr::Div(l, r) => Expr::Div(rebox(l), rebox(r)),
        Expr::IntDiv(l, r) => Expr::IntDiv(rebox(l), rebox(r)),
        Expr::Mod(l, r) => Expr::Mod(rebox(l), rebox(r)),
        Expr::Pow(l, r) => Expr::Pow(rebox(l), rebox(r)),
        Expr::Neg(e) => Expr::Neg(rebox(e)),
        Expr::Range(l, r) => Expr::Range(rebox(l), rebox(r)),

        // `Lambda` / `Let` / `SubstIn` introduce their own binders that this
        // pass does not currently rewrite. They are never produced by the
        // tuple-pattern desugaring path (which only substitutes projections of
        // a fresh element variable into a quantifier body); a quantifier body
        // that contains one of these is left untouched here and will be handled
        // — or rejected — by the main conversion. Cloning preserves it exactly.
        Expr::Lambda(_, _) | Expr::Let(_, _) | Expr::SubstIn(_, _) => expr.node.clone(),
    };

    Spanned::new(node, expr.span)
}

/// Substitute under a multi-binder construct, dropping shadowed names for the
/// body while keeping them for the (outer-scope) domains.
fn substitute_binders(
    bounds: &[core_ast::BoundVar],
    body: &Spanned<core_ast::Expr>,
    subst: &HashMap<String, core_ast::Expr>,
) -> (Vec<core_ast::BoundVar>, Spanned<core_ast::Expr>) {
    let mut inner = subst.clone();
    let new_bounds = bounds
        .iter()
        .map(|bound| {
            // Domain is evaluated before this binder takes effect, in the scope
            // accumulated so far.
            let domain = bound
                .domain
                .as_ref()
                .map(|d| Box::new(substitute(d, &inner)));
            for name in bound_introduced_names(bound) {
                inner.remove(&name);
            }
            core_ast::BoundVar {
                name: bound.name.clone(),
                domain,
                pattern: bound.pattern.clone(),
            }
        })
        .collect();
    let new_body = substitute(body, &inner);
    (new_bounds, new_body)
}

/// Substitute under a single-binder construct (CHOOSE / set filter).
fn substitute_single_binder(
    bound: &core_ast::BoundVar,
    body: &Spanned<core_ast::Expr>,
    subst: &HashMap<String, core_ast::Expr>,
) -> (core_ast::BoundVar, Spanned<core_ast::Expr>) {
    let domain = bound
        .domain
        .as_ref()
        .map(|d| Box::new(substitute(d, subst)));
    let mut inner = subst.clone();
    for name in bound_introduced_names(bound) {
        inner.remove(&name);
    }
    let new_bound = core_ast::BoundVar {
        name: bound.name.clone(),
        domain,
        pattern: bound.pattern.clone(),
    };
    (new_bound, substitute(body, &inner))
}

/// Names a binder brings into scope (its variable, or each tuple component).
fn bound_introduced_names(bound: &core_ast::BoundVar) -> Vec<String> {
    match &bound.pattern {
        Some(core_ast::BoundPattern::Tuple(names)) => {
            names.iter().map(|n| n.node.clone()).collect()
        }
        Some(core_ast::BoundPattern::Var(name)) => vec![name.node.clone()],
        None => vec![bound.name.node.clone()],
    }
}

fn substitute_module_target(
    target: &core_ast::ModuleTarget,
    subst: &HashMap<String, core_ast::Expr>,
) -> core_ast::ModuleTarget {
    match target {
        core_ast::ModuleTarget::Named(n) => core_ast::ModuleTarget::Named(n.clone()),
        core_ast::ModuleTarget::Parameterized(n, args) => core_ast::ModuleTarget::Parameterized(
            n.clone(),
            args.iter().map(|e| substitute(e, subst)).collect(),
        ),
        core_ast::ModuleTarget::Chained(base) => {
            core_ast::ModuleTarget::Chained(Box::new(substitute(base, subst)))
        }
    }
}

fn substitute_subs(
    subs: &[core_ast::Substitution],
    subst: &HashMap<String, core_ast::Expr>,
) -> Vec<core_ast::Substitution> {
    subs.iter()
        .map(|s| core_ast::Substitution {
            from: s.from.clone(),
            to: substitute(&s.to, subst),
        })
        .collect()
}

/// Collect every identifier-like name appearing anywhere in `expr` (free or
/// bound), used to choose a fresh element variable that cannot be captured.
fn collect_names(expr: &Spanned<core_ast::Expr>, out: &mut HashSet<String>) {
    use core_ast::Expr;
    let mut recur = |e: &Spanned<Expr>, out: &mut HashSet<String>| collect_names(e, out);
    let each = |es: &[Spanned<Expr>], out: &mut HashSet<String>| {
        for e in es {
            collect_names(e, out);
        }
    };

    match &expr.node {
        Expr::Ident(n, _) | Expr::OpRef(n) | Expr::StateVar(n, _, _) => {
            out.insert(n.clone());
        }
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => {}
        Expr::Apply(callee, args) => {
            recur(callee, out);
            each(args, out);
        }
        Expr::ModuleRef(target, op, args) => {
            out.insert(op.clone());
            match target {
                core_ast::ModuleTarget::Named(n) | core_ast::ModuleTarget::Parameterized(n, _) => {
                    out.insert(n.clone());
                }
                core_ast::ModuleTarget::Chained(base) => recur(base, out),
            }
            if let core_ast::ModuleTarget::Parameterized(_, ts) = target {
                each(ts, out);
            }
            each(args, out);
        }
        Expr::InstanceExpr(n, subs) => {
            out.insert(n.clone());
            for s in subs {
                out.insert(s.from.node.clone());
                recur(&s.to, out);
            }
        }
        Expr::Lambda(params, body) => {
            for p in params {
                out.insert(p.node.clone());
            }
            recur(body, out);
        }
        Expr::Label(label) => {
            out.insert(label.name.node.clone());
            recur(&label.body, out);
        }
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
        | Expr::Range(l, r) => {
            recur(l, out);
            recur(r, out);
        }
        Expr::Not(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Domain(e)
        | Expr::Prime(e)
        | Expr::Always(e)
        | Expr::Eventually(e)
        | Expr::Enabled(e)
        | Expr::Unchanged(e)
        | Expr::Neg(e) => recur(e, out),
        Expr::Forall(bounds, body)
        | Expr::Exists(bounds, body)
        | Expr::SetBuilder(body, bounds)
        | Expr::FuncDef(bounds, body) => {
            for b in bounds {
                collect_bound_names(b, out);
            }
            recur(body, out);
        }
        Expr::Choose(bound, body) | Expr::SetFilter(bound, body) => {
            collect_bound_names(bound, out);
            recur(body, out);
        }
        Expr::SetEnum(es) | Expr::Tuple(es) | Expr::Times(es) => each(es, out),
        Expr::Except(base, specs) => {
            recur(base, out);
            for spec in specs {
                for elem in &spec.path {
                    if let core_ast::ExceptPathElement::Index(e) = elem {
                        recur(e, out);
                    }
                }
                recur(&spec.value, out);
            }
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (n, e) in fields {
                out.insert(n.node.clone());
                recur(e, out);
            }
        }
        Expr::RecordAccess(base, field) => {
            out.insert(field.name.node.clone());
            recur(base, out);
        }
        Expr::If(c, t, e) => {
            recur(c, out);
            recur(t, out);
            recur(e, out);
        }
        Expr::Case(arms, default) => {
            for arm in arms {
                recur(&arm.guard, out);
                recur(&arm.body, out);
            }
            if let Some(d) = default {
                recur(d, out);
            }
        }
        Expr::Let(defs, body) => {
            for d in defs {
                out.insert(d.name.node.clone());
                recur(&d.body, out);
            }
            recur(body, out);
        }
        Expr::SubstIn(subs, inner) => {
            for s in subs {
                out.insert(s.from.node.clone());
                recur(&s.to, out);
            }
            recur(inner, out);
        }
    }
}

fn collect_bound_names(bound: &core_ast::BoundVar, out: &mut HashSet<String>) {
    for name in bound_introduced_names(bound) {
        out.insert(name);
    }
    if let Some(domain) = bound.domain.as_deref() {
        collect_names(domain, out);
    }
}
