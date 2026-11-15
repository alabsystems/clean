// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Optional, proof-checked normalization of an ORIGINAL conditional decision.
//! A proposition's syntax selects at most four UInt proposals; only an exact
//! closed kernel value equality can authorize replacement. Compiled runtime
//! overrides are a separate meaning and conservatively decline this shortcut.

use super::LcnfContext;
use crate::implemented_by::CodeMeaning;
use clean_kernel::{tc::TypeChecker, BinderInfo, Environment, Expr, ExprKind, Level, Name};
use std::collections::HashSet;

const MAX_BINDERS: usize = 64;
const MAX_NODES: usize = 262_144;
const MAX_DECLARATIONS: usize = 4096;
const MAX_CHECK_HEARTBEATS: u32 = 200_000;

fn args_of<'a>(
    term: &'a Expr,
    name: &str,
    levels: &[Level],
    count: usize,
) -> Option<Vec<&'a Expr>> {
    let term = term.strip_mdata();
    let ExprKind::Const(actual, actual_levels) = term.get_app_fn().kind() else {
        return None;
    };
    if actual != &Name::from_string(name) || actual_levels.as_slice() != levels {
        return None;
    }
    let args = term.get_app_args();
    (args.len() == count).then(|| args.into_vec())
}

fn operands(proposition: &Expr) -> Option<(u32, Expr, Expr)> {
    for width in [8, 16, 32, 64] {
        let uint = Expr::const_str(&format!("UInt{width}"));
        for method in ["LT.lt", "LE.le"] {
            if let Some(args) = args_of(proposition, method, &[Level::zero()], 4) {
                if args[0] == &uint {
                    // Keep the actual dictionary in the equality's p. The
                    // matcher does NOT assume the semantics of its field.
                    return Some((width, args[2].clone(), args[3].clone()));
                }
            }
        }
        for relation in ["lt", "le"] {
            if let Some(args) = args_of(proposition, &format!("UInt{width}.{relation}"), &[], 2) {
                return Some((width, args[0].clone(), args[1].clone()));
            }
        }
    }
    None
}

/// Close BOTH sides, their exact expected type, and their equality under every
/// active typed binder. Cached types for popped locals are never resurrected.
struct Judgment {
    original: Expr,
    candidate: Expr,
    expected: Expr,
    goal: Expr,
    proof: Expr,
}

fn close(ctx: &LcnfContext<'_>, p: &Expr, original: &Expr, candidate: &Expr) -> Option<Judgment> {
    if ctx.bvar_stack.len() > MAX_BINDERS {
        return None;
    }
    let p = ctx.resolve_local_type(p);
    let mut original = ctx.resolve_local_type(original);
    let mut candidate = ctx.resolve_local_type(candidate);
    let mut expected = Expr::app(Expr::const_str("Decidable"), p);
    let mut goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [expected.clone(), original.clone(), candidate.clone()],
    );
    let mut proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [expected.clone(), original.clone()],
    );
    let mut seen = HashSet::new();
    for id in ctx.bvar_stack.iter().rev() {
        if !seen.insert(*id) {
            return None;
        }
        // local_type already opens a dependent domain to stable outer ids.
        let ty = ctx.local_type(*id)?;
        goal = Expr::pi(BinderInfo::Default, ty.clone(), goal.abstract_fvar(*id));
        expected = Expr::pi(BinderInfo::Default, ty.clone(), expected.abstract_fvar(*id));
        proof = Expr::lam(BinderInfo::Default, ty.clone(), proof.abstract_fvar(*id));
        original = Expr::lam(BinderInfo::Default, ty.clone(), original.abstract_fvar(*id));
        candidate = Expr::lam(
            BinderInfo::Default,
            ty.clone(),
            candidate.abstract_fvar(*id),
        );
    }
    for term in [&original, &candidate, &expected, &goal, &proof] {
        if term.has_fvar_quick()
            || term.has_loose_bvars()
            || term.has_expr_mvar_quick()
            || term.has_level_mvar_quick()
            || term.has_level_param_quick()
        {
            return None;
        }
    }
    Some(Judgment {
        original,
        candidate,
        expected,
        goal,
        proof,
    })
}

/// Bounded DAG/closure walk, including type/value dependencies, projection
/// structures, mutual inductives, constructors and recursor rule bodies. An
/// unknown declaration or non-Lean expression form declines optimization.
/// The roots include the original instance, candidate, proposition and scope
/// domains through the closed judgment; no compiled override is erased merely
/// because its kernel value happens to be definitionally equal.
fn closure_safe<'a>(
    env: &'a Environment,
    roots: &[&'a Expr],
    compiled: bool,
    locals: Option<&LcnfContext<'_>>,
) -> bool {
    let mut nodes = roots.to_vec();
    let mut names = Vec::new();
    let mut seen_nodes = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut remaining = MAX_NODES;
    loop {
        while let Some(expr) = nodes.pop() {
            if !seen_nodes.insert(std::ptr::from_ref(expr) as usize) {
                continue;
            }
            let Some(rest) = remaining.checked_sub(1) else {
                return false;
            };
            remaining = rest;
            match expr.kind() {
                ExprKind::Const(name, _) => names.push(name.clone()),
                ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
                ExprKind::FVar(id) => {
                    // In the OPEN compiled preflight, used local functions or
                    // opaque values have unknown runtime meaning. For example
                    // kernel beta reduction could discard an effectful local
                    // callback application. Only known first-order data locals
                    // can pass; all other cases retain the original lowering.
                    let Some(ctx) = locals else {
                        return false;
                    };
                    if !ctx.bvar_stack.contains(id) {
                        return false;
                    }
                    let Some(ty) = ctx.local_type(*id) else {
                        return false;
                    };
                    let ExprKind::Const(name, levels) = ty.kind() else {
                        return false;
                    };
                    if !levels.is_empty()
                        || !["UInt8", "UInt16", "UInt32", "UInt64", "Nat", "Bool"]
                            .iter()
                            .any(|text| *name == Name::from_string(text))
                    {
                        return false;
                    }
                }
                ExprKind::App(f, a) => {
                    nodes.push(f);
                    nodes.push(a);
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    nodes.push(ty);
                    nodes.push(body);
                }
                ExprKind::Let(_, ty, value, body, _) => {
                    nodes.push(ty);
                    nodes.push(value);
                    nodes.push(body);
                }
                ExprKind::Proj(structure, _, inner) => {
                    names.push(structure.clone());
                    nodes.push(inner);
                }
                ExprKind::MData(_, inner) => nodes.push(inner),
                _ => return false,
            }
        }
        let Some(name) = names.pop() else {
            return true;
        };
        if !seen_names.insert(name.clone()) {
            continue;
        }
        if seen_names.len() > MAX_DECLARATIONS {
            return false;
        }
        if compiled && (env.get_implemented_by(&name).is_some() || env.get_extern(&name).is_some())
        {
            return false;
        }
        let mut known = false;
        if let Some(info) = env.get_const(&name) {
            if compiled && info.kind == clean_kernel::ConstantKind::Opaque {
                return false;
            }
            if compiled
                && info.value.is_none()
                && info.kind == clean_kernel::ConstantKind::Definition
                && env.get_inductive(&name).is_none()
                && env.get_constructor(&name).is_none()
                && env.get_recursor(&name).is_none()
                && env.get_quot(&name).is_none()
            {
                return false;
            }
            known = true;
            nodes.push(&info.type_);
            if let Some(value) = &info.value {
                nodes.push(value);
            }
        }
        if let Some(inductive) = env.get_inductive(&name) {
            known = true;
            nodes.push(&inductive.type_);
            let Some(edges) = inductive
                .all_names
                .len()
                .checked_add(inductive.constructor_names.len())
            else {
                return false;
            };
            let Some(rest) = remaining.checked_sub(edges) else {
                return false;
            };
            remaining = rest;
            names.extend(inductive.all_names.iter().cloned());
            names.extend(inductive.constructor_names.iter().cloned());
        }
        if let Some(constructor) = env.get_constructor(&name) {
            known = true;
            nodes.push(&constructor.type_);
            names.push(constructor.inductive_name.clone());
        }
        if let Some(recursor) = env.get_recursor(&name) {
            known = true;
            nodes.push(&recursor.type_);
            names.push(recursor.inductive_name.clone());
            let Some(rest) = remaining.checked_sub(recursor.rules.len()) else {
                return false;
            };
            remaining = rest;
            for rule in &recursor.rules {
                names.push(rule.constructor_name.clone());
                nodes.push(&rule.rhs);
            }
        }
        if let Some(quotient) = env.get_quot(&name) {
            known = true;
            nodes.push(&quotient.type_);
        }
        if !known {
            return false;
        }
    }
}

fn accepted(ctx: &LcnfContext<'_>, p: &Expr, original: &Expr, candidate: &Expr) -> bool {
    let Some(judgment) = close(ctx, p, original, candidate) else {
        return false;
    };
    let compiled = ctx.meaning == CodeMeaning::LeanCompiled;
    if compiled {
        let opened = [
            ctx.resolve_local_type(p),
            ctx.resolve_local_type(original),
            ctx.resolve_local_type(candidate),
        ];
        if !closure_safe(
            ctx.env,
            &[&opened[0], &opened[1], &opened[2]],
            true,
            Some(ctx),
        ) {
            return false;
        }
    }
    if !closure_safe(ctx.env, &[&judgment.goal, &judgment.proof], compiled, None) {
        return false;
    }
    // Resource options change only on this private checker view. Do not refill
    // or suspend the kernel's ambient declaration budget. A smaller configured
    // nonzero limit wins; absent/invalid/unlimited options receive a finite cap.
    let limit = ctx
        .env
        .get_option("maxHeartbeats")
        .and_then(|v| v.as_ref())
        .and_then(|v| v.parse::<u32>().ok())
        .filter(|n| *n != 0)
        .map_or(MAX_CHECK_HEARTBEATS, |n| n.min(MAX_CHECK_HEARTBEATS));
    let mut checking = ctx.env.clone();
    checking.set_option("maxHeartbeats".to_owned(), Some(limit.to_string()));
    let mut tc = TypeChecker::with_mode(&checking, checking.mode());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(limit);
    if tc
        .check_type(&judgment.original, &judgment.expected)
        .is_err()
        || tc
            .check_type(&judgment.candidate, &judgment.expected)
            .is_err()
        || tc.heartbeat_spent()
    {
        return false;
    }
    // Strict audit rechecks the EXACT closed equality and dependency closure.
    // Inference alone, a primitive name, and structural admission grant nothing.
    checking
        .audit_certification(&judgment.goal, &judgment.proof)
        .is_certified()
}

/// Return the candidate in the ORIGINAL BVar scope, not the opened proof scope.
/// No match, missing scope/type, changed compiled meaning, or checker/budget
/// rejection returns None so lower_dite_ite lowers its original instance.
pub(super) fn normalize(ctx: &LcnfContext<'_>, p: &Expr, original: &Expr) -> Option<Expr> {
    let (width, a, b) = operands(p)?;
    for operation in ["decLt", "decLe"] {
        for swapped in [false, true] {
            let args = if swapped {
                [b.clone(), a.clone()]
            } else {
                [a.clone(), b.clone()]
            };
            let name = Name::from_string(&format!("UInt{width}.{operation}"));
            let Some(info) = ctx.env.get_const(&name) else {
                continue;
            };
            if !info.level_params.is_empty()
                || info.kind != clean_kernel::ConstantKind::Definition
                || info.value.is_none()
            {
                continue;
            }
            let candidate = Expr::apps(Expr::const_(name, vec![]), args);
            if accepted(ctx, p, original, &candidate) {
                return Some(candidate);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests;
