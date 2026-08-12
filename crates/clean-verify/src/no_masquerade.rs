// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conservative MASQUERADE lint scaffolding for proof-promotion gates.
//!
//! This module intentionally lives in `clean-verify`, not the kernel theorem
//! builders. It consumes already-built kernel [`Expr`] and declaration metadata
//! and reports suspicious proof/declaration shapes that should block promotion
//! until reviewed.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{
    ConstantInfo, ConstantKind, Environment, Expr, ExprKind, FVarId, Name, Reducibility,
};
use std::collections::{HashMap, HashSet};

const REFL_NAMES: &[&str] = &["Eq.refl", "rfl", "HEq.refl"];

const PEELABLE_PROOF_COMBINATORS: &[&str] = &[
    "Eq.symm",
    "Eq.trans",
    "Eq.subst",
    "Eq.substType",
    "Eq.mpr",
    "Eq.mp",
    "congrArg",
    "congrFun",
    "congr",
    "id",
];

/// Read-only declaration lookup used by the lint.
///
/// Implemented for the real kernel [`Environment`] and for synthetic
/// `HashMap<Name, ConstantInfo>` fixtures used by tests and future importers.
pub trait ConstLookup {
    /// Return kernel metadata for `name`, if available.
    fn get_const_info(&self, name: &Name) -> Option<&ConstantInfo>;
}

impl ConstLookup for Environment {
    fn get_const_info(&self, name: &Name) -> Option<&ConstantInfo> {
        self.get_const(name)
    }
}

impl ConstLookup for HashMap<Name, ConstantInfo> {
    fn get_const_info(&self, name: &Name) -> Option<&ConstantInfo> {
        self.get(name)
    }
}

/// Optional knobs for the conservative no-masquerade lint.
#[derive(Clone, Debug)]
pub struct NoMasqueradeConfig {
    /// Symbols that must occur in the proof body.
    pub required_symbols: Vec<RequiredSymbol>,
    /// Named theorems allowed to use root `Eq.refl` without a finding.
    pub allowed_refl_theorems: HashSet<Name>,
    /// Check reducible definitions referenced by each theorem type.
    pub scan_theorem_type_carriers: bool,
    /// Also scan every reducible definition in the lookup source.
    ///
    /// The generic [`ConstLookup`] trait cannot enumerate declarations, so this
    /// knob is used only by [`lint_environment`].
    pub scan_all_reducible_definitions: bool,
}

impl Default for NoMasqueradeConfig {
    fn default() -> Self {
        Self {
            required_symbols: Vec::new(),
            allowed_refl_theorems: HashSet::new(),
            scan_theorem_type_carriers: true,
            scan_all_reducible_definitions: false,
        }
    }
}

/// A proof symbol whose occurrence is required by a promotion policy.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RequiredSymbol {
    /// A named constant must occur somewhere in the proof expression.
    Const(Name),
    /// A free variable id must occur somewhere in the proof expression.
    FVar(FVarId),
    /// A theorem outer lambda binder must occur in the lambda-peeled proof
    /// body.
    ///
    /// `arg_index` is in declaration order, so `0` names the outermost theorem
    /// argument.
    TheoremArg {
        /// Human-readable label shown in findings.
        label: String,
        /// Argument index in theorem declaration order.
        arg_index: usize,
    },
    /// A bound variable must occur in the lambda-peeled proof body.
    ///
    /// `index` uses the body-local de Bruijn index after peeling all outer
    /// lambdas, so `0` is usually the innermost peeled binder, e.g. an `ih`.
    BodyBVar {
        /// Human-readable label shown in findings.
        label: String,
        /// Body-local de Bruijn index.
        index: u32,
    },
}

impl RequiredSymbol {
    /// Build a required constant symbol from a dotted Lean name.
    pub fn const_str(name: &str) -> Self {
        Self::Const(Name::from_string(name))
    }

    /// Build a required theorem-argument symbol in declaration order.
    pub fn theorem_arg(label: impl Into<String>, arg_index: usize) -> Self {
        Self::TheoremArg {
            label: label.into(),
            arg_index,
        }
    }

    /// Build a required body-bound-variable symbol, typically `"ih"` at `0`.
    pub fn body_bvar(label: impl Into<String>, index: u32) -> Self {
        Self::BodyBVar {
            label: label.into(),
            index,
        }
    }
}

/// Description of a suspicious reducible-definition carrier.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CarrierShape {
    /// `fun x1 ... xn => xi`, including the one-argument identity carrier.
    IdentityOnArgument {
        /// Number of peeled lambda binders.
        lambda_arity: usize,
        /// Returned argument index in declaration order.
        returned_arg: usize,
    },
    /// `fun x1 ... xn => K`, where no peeled binder occurs in `K`.
    ConstantBody {
        /// Number of peeled lambda binders.
        lambda_arity: usize,
    },
    /// Some, but not all, peeled binders occur in the body.
    DiscardsArguments {
        /// Number of peeled lambda binders.
        lambda_arity: usize,
        /// Used argument indices in declaration order.
        used_args: Vec<usize>,
        /// Discarded argument indices in declaration order.
        discarded_args: Vec<usize>,
    },
}

/// Where a carrier finding was observed.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CarrierContext {
    /// The definition itself was scanned directly.
    Definition,
    /// The carrier was referenced by a theorem type.
    TheoremType {
        /// The theorem whose type referenced the carrier.
        theorem: Name,
    },
}

/// One conservative no-masquerade lint finding.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum NoMasqueradeFinding {
    /// The theorem proof is directly headed by an axiom after peeling outer
    /// lambdas and standard proof combinators.
    DirectAxiomWrapper {
        /// Theorem being linted.
        theorem: Name,
        /// Axiom referenced by the proof root.
        axiom: Name,
        /// Number of proof wrappers peeled before the axiom root was found.
        peel_depth: usize,
    },
    /// The theorem proof is rooted at `Eq.refl`/`rfl`/`HEq.refl`, and the
    /// theorem type is a named equality whose sides are not syntactically equal.
    ReflRootOnNamedTheorem {
        /// Theorem being linted.
        theorem: Name,
        /// Number of proof wrappers peeled before `Eq.refl` was found.
        peel_depth: usize,
    },
    /// A supplied required proof symbol was absent.
    MissingRequiredSymbol {
        /// Theorem being linted.
        theorem: Name,
        /// Required symbol that was not referenced.
        symbol: RequiredSymbol,
    },
    /// A reducible definition looks like a constant or argument-discarding
    /// carrier.
    ArgumentDiscardingCarrier {
        /// Carrier definition name.
        carrier: Name,
        /// Classified suspicious shape.
        shape: CarrierShape,
        /// Where this carrier was found.
        context: CarrierContext,
    },
}

/// Aggregate lint report.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NoMasqueradeReport {
    /// Findings in discovery order.
    pub findings: Vec<NoMasqueradeFinding>,
}

impl NoMasqueradeReport {
    /// Return `true` iff no findings were emitted.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    fn push(&mut self, finding: NoMasqueradeFinding) {
        self.findings.push(finding);
    }

    fn extend(&mut self, other: NoMasqueradeReport) {
        self.findings.extend(other.findings);
    }
}

/// Lint a theorem-shaped constant using an arbitrary declaration lookup.
pub fn lint_constant<L: ConstLookup>(
    lookup: &L,
    info: &ConstantInfo,
    config: &NoMasqueradeConfig,
) -> NoMasqueradeReport {
    let mut report = NoMasqueradeReport::default();

    if info.kind == ConstantKind::Definition && info.is_reducible {
        if let Some(shape) = classify_argument_discarding_carrier(info) {
            report.push(NoMasqueradeFinding::ArgumentDiscardingCarrier {
                carrier: info.name.clone(),
                shape,
                context: CarrierContext::Definition,
            });
        }
    }

    if info.kind != ConstantKind::Theorem {
        return report;
    }

    let Some(proof) = info.value.as_ref() else {
        return report;
    };

    report.extend(lint_theorem_exprs(
        lookup,
        &info.name,
        &info.type_,
        proof,
        config,
    ));
    report
}

/// Lint one theorem proof/type pair using an arbitrary declaration lookup.
pub fn lint_theorem_exprs<L: ConstLookup>(
    lookup: &L,
    theorem: &Name,
    type_: &Expr,
    proof: &Expr,
    config: &NoMasqueradeConfig,
) -> NoMasqueradeReport {
    let mut report = NoMasqueradeReport::default();

    if let Some((root, peel_depth)) = peeled_proof_root(proof) {
        if let Some(info) = lookup.get_const_info(&root) {
            if info.kind == ConstantKind::Axiom {
                report.push(NoMasqueradeFinding::DirectAxiomWrapper {
                    theorem: theorem.clone(),
                    axiom: root.clone(),
                    peel_depth,
                });
            }
        }

        if is_refl_name(&root)
            && !config.allowed_refl_theorems.contains(theorem)
            && is_nontrivial_named_eq(type_)
        {
            report.push(NoMasqueradeFinding::ReflRootOnNamedTheorem {
                theorem: theorem.clone(),
                peel_depth,
            });
        }
    }

    for symbol in &config.required_symbols {
        if !required_symbol_occurs(proof, symbol) {
            report.push(NoMasqueradeFinding::MissingRequiredSymbol {
                theorem: theorem.clone(),
                symbol: symbol.clone(),
            });
        }
    }

    if config.scan_theorem_type_carriers {
        let mut seen = HashSet::new();
        for name in consts_in_expr(type_) {
            if !seen.insert(name.clone()) {
                continue;
            }
            let Some(carrier) = lookup.get_const_info(&name) else {
                continue;
            };
            if carrier.kind != ConstantKind::Definition || !carrier.is_reducible {
                continue;
            }
            if let Some(shape) = classify_argument_discarding_carrier(carrier) {
                report.push(NoMasqueradeFinding::ArgumentDiscardingCarrier {
                    carrier: name,
                    shape,
                    context: CarrierContext::TheoremType {
                        theorem: theorem.clone(),
                    },
                });
            }
        }
    }

    report
}

/// Lint all constants in a kernel environment.
pub fn lint_environment(env: &Environment, config: &NoMasqueradeConfig) -> NoMasqueradeReport {
    let mut report = NoMasqueradeReport::default();
    for info in env.constants() {
        if info.kind == ConstantKind::Definition && !config.scan_all_reducible_definitions {
            continue;
        }
        report.extend(lint_constant(env, info, config));
    }
    report
}

/// Classify a reducible definition body as a suspicious carrier shape.
pub fn classify_argument_discarding_carrier(info: &ConstantInfo) -> Option<CarrierShape> {
    if info.kind != ConstantKind::Definition || !info.is_reducible {
        return None;
    }
    classify_argument_discarding_value(info.value.as_ref()?)
}

/// Classify a raw expression value as a suspicious lambda-carrier shape.
pub fn classify_argument_discarding_value(value: &Expr) -> Option<CarrierShape> {
    let (body, lambda_arity) = peel_lambdas(value);
    if lambda_arity == 0 {
        return None;
    }

    if let ExprKind::BVar(idx) = body.kind() {
        let idx = *idx as usize;
        if idx < lambda_arity {
            return Some(CarrierShape::IdentityOnArgument {
                lambda_arity,
                returned_arg: lambda_arity - 1 - idx,
            });
        }
    }

    let used_args = used_lambda_args(body, lambda_arity);
    if used_args.is_empty() {
        return Some(CarrierShape::ConstantBody { lambda_arity });
    }
    if used_args.len() < lambda_arity {
        let used_set: HashSet<usize> = used_args.iter().copied().collect();
        let discarded_args = (0..lambda_arity)
            .filter(|idx| !used_set.contains(idx))
            .collect();
        return Some(CarrierShape::DiscardsArguments {
            lambda_arity,
            used_args,
            discarded_args,
        });
    }
    None
}

fn is_refl_name(name: &Name) -> bool {
    let name = name.to_string();
    REFL_NAMES.iter().any(|candidate| name == *candidate)
}

fn is_peelable_proof_combinator(name: &Name) -> bool {
    let name = name.to_string();
    PEELABLE_PROOF_COMBINATORS
        .iter()
        .any(|candidate| name == *candidate)
}

fn peeled_proof_root(proof: &Expr) -> Option<(Name, usize)> {
    let mut current = proof;
    let mut peel_depth = 0usize;

    loop {
        let (peeled, lam_depth) = peel_lambdas(current);
        current = peeled;
        peel_depth += lam_depth;

        let (head, args) = collect_app_args(current);
        let head_name = head_const(head)?.clone();
        if !is_peelable_proof_combinator(&head_name) || args.is_empty() {
            return Some((head_name, peel_depth));
        }

        current = args[args.len() - 1];
        peel_depth += 1;
    }
}

fn required_symbol_occurs(proof: &Expr, symbol: &RequiredSymbol) -> bool {
    match symbol {
        RequiredSymbol::Const(name) => expr_contains_const(proof, name),
        RequiredSymbol::FVar(id) => expr_contains_fvar(proof, *id),
        RequiredSymbol::TheoremArg { arg_index, .. } => theorem_arg_occurs(proof, *arg_index),
        RequiredSymbol::BodyBVar { index, .. } => {
            let (body, _) = peel_lambdas(proof);
            expr_uses_bvar(body, *index)
        }
    }
}

fn theorem_arg_occurs(proof: &Expr, arg_index: usize) -> bool {
    let (body, lambda_arity) = peel_lambdas(proof);
    let Some(body_bvar_idx) = theorem_arg_body_bvar_index(lambda_arity, arg_index) else {
        return false;
    };
    expr_uses_bvar(body, body_bvar_idx)
}

fn theorem_arg_body_bvar_index(lambda_arity: usize, arg_index: usize) -> Option<u32> {
    if arg_index >= lambda_arity {
        return None;
    }
    Some((lambda_arity - 1 - arg_index) as u32)
}

fn is_nontrivial_named_eq(type_: &Expr) -> bool {
    let Some((lhs, rhs)) = outer_eq_sides(type_) else {
        return false;
    };
    lhs != rhs
}

fn outer_eq_sides(type_: &Expr) -> Option<(&Expr, &Expr)> {
    let mut current = type_;
    loop {
        match current.kind() {
            ExprKind::Pi(_, _, body) => current = body,
            ExprKind::MData(_, inner) => current = inner,
            _ => break,
        }
    }

    let (head, args) = collect_app_args(current);
    let head_name = head_const(head)?.to_string();
    if head_name != "Eq" && head_name != "HEq" {
        return None;
    }
    if args.len() < 2 {
        return None;
    }
    Some((args[args.len() - 2], args[args.len() - 1]))
}

fn collect_app_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut current = expr;
    loop {
        match current.kind() {
            ExprKind::App(f, a) => {
                args.push(a.as_ref());
                current = f;
            }
            ExprKind::MData(_, inner) => current = inner,
            _ => {
                args.reverse();
                return (current, args);
            }
        }
    }
}

fn head_const(expr: &Expr) -> Option<&Name> {
    let mut current = expr;
    loop {
        match current.kind() {
            ExprKind::App(f, _) => current = f,
            ExprKind::MData(_, inner) => current = inner,
            ExprKind::Const(name, _) => return Some(name),
            _ => return None,
        }
    }
}

fn peel_lambdas(expr: &Expr) -> (&Expr, usize) {
    let mut depth = 0usize;
    let mut current = expr;
    loop {
        match current.kind() {
            ExprKind::Lam(_, _, body) => {
                current = body;
                depth += 1;
            }
            ExprKind::MData(_, inner) => current = inner,
            _ => return (current, depth),
        }
    }
}

fn used_lambda_args(body: &Expr, lambda_arity: usize) -> Vec<usize> {
    let mut used_args = Vec::new();
    for bvar_idx in 0..lambda_arity {
        if expr_uses_bvar(body, bvar_idx as u32) {
            used_args.push(lambda_arity - 1 - bvar_idx);
        }
    }
    used_args.sort_unstable();
    used_args
}

fn expr_uses_bvar(expr: &Expr, target: u32) -> bool {
    let mut stack = vec![(expr, target)];
    while let Some((expr, shifted_target)) = stack.pop() {
        match expr.kind() {
            ExprKind::BVar(idx) => {
                if *idx == shifted_target {
                    return true;
                }
            }
            kind => push_children_for_bvar(kind, shifted_target, &mut stack),
        }
    }
    false
}

fn expr_contains_const(expr: &Expr, required: &Name) -> bool {
    let mut stack = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr.kind() {
            ExprKind::Const(name, _) if name == required => return true,
            kind => push_children(kind, &mut stack),
        }
    }
    false
}

fn expr_contains_fvar(expr: &Expr, required: FVarId) -> bool {
    let mut stack = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr.kind() {
            ExprKind::FVar(id) if *id == required => return true,
            kind => push_children(kind, &mut stack),
        }
    }
    false
}

fn consts_in_expr(expr: &Expr) -> Vec<Name> {
    let mut out = Vec::new();
    let mut stack = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr.kind() {
            ExprKind::Const(name, _) => out.push(name.clone()),
            kind => push_children(kind, &mut stack),
        }
    }
    out
}

fn push_children<'a>(kind: &'a ExprKind, stack: &mut Vec<&'a Expr>) {
    match kind {
        ExprKind::App(f, a) => {
            stack.push(f);
            stack.push(a);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            stack.push(ty);
            stack.push(body);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            stack.push(ty);
            stack.push(val);
            stack.push(body);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            stack.push(inner);
        }
        ExprKind::CubicalPath { ty, left, right } => {
            stack.push(ty);
            stack.push(left);
            stack.push(right);
        }
        ExprKind::CubicalPathLam { body } => stack.push(body),
        ExprKind::CubicalPathApp { path, arg } => {
            stack.push(path);
            stack.push(arg);
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            stack.push(ty);
            stack.push(phi);
            stack.push(u);
            stack.push(base);
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            stack.push(ty);
            stack.push(phi);
            stack.push(base);
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            stack.push(ty);
            stack.push(r);
            stack.push(s);
            stack.push(base);
        }
        ExprKind::ZFCSet(set) => push_zfc_children(set, stack),
        ExprKind::ZFCMem { element, set } => {
            stack.push(element);
            stack.push(set);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            stack.push(domain);
            stack.push(pred);
        }
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => {}
    }
}

fn push_children_for_bvar<'a>(
    kind: &'a ExprKind,
    shifted_target: u32,
    stack: &mut Vec<(&'a Expr, u32)>,
) {
    match kind {
        ExprKind::App(f, a) => {
            stack.push((f, shifted_target));
            stack.push((a, shifted_target));
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            stack.push((ty, shifted_target));
            stack.push((body, shifted_target + 1));
        }
        ExprKind::Let(_, ty, val, body, _) => {
            stack.push((ty, shifted_target));
            stack.push((val, shifted_target));
            stack.push((body, shifted_target + 1));
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            stack.push((inner, shifted_target));
        }
        ExprKind::CubicalPath { ty, left, right } => {
            stack.push((ty, shifted_target));
            stack.push((left, shifted_target));
            stack.push((right, shifted_target));
        }
        ExprKind::CubicalPathLam { body } => stack.push((body, shifted_target + 1)),
        ExprKind::CubicalPathApp { path, arg } => {
            stack.push((path, shifted_target));
            stack.push((arg, shifted_target));
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            stack.push((ty, shifted_target));
            stack.push((phi, shifted_target));
            stack.push((u, shifted_target));
            stack.push((base, shifted_target));
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            stack.push((ty, shifted_target));
            stack.push((phi, shifted_target));
            stack.push((base, shifted_target));
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            stack.push((ty, shifted_target));
            stack.push((r, shifted_target));
            stack.push((s, shifted_target));
            stack.push((base, shifted_target));
        }
        ExprKind::ZFCSet(set) => push_zfc_children_for_bvar(set, shifted_target, stack),
        ExprKind::ZFCMem { element, set } => {
            stack.push((element, shifted_target));
            stack.push((set, shifted_target));
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            stack.push((domain, shifted_target));
            stack.push((pred, shifted_target + 1));
        }
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => {}
    }
}

fn push_zfc_children<'a>(set: &'a ZFCSetExpr, stack: &mut Vec<&'a Expr>) {
    match set {
        ZFCSetExpr::Singleton(expr)
        | ZFCSetExpr::Union(expr)
        | ZFCSetExpr::PowerSet(expr)
        | ZFCSetExpr::Choice(expr) => stack.push(expr),
        ZFCSetExpr::Pair(left, right) => {
            stack.push(left);
            stack.push(right);
        }
        ZFCSetExpr::Separation { set, pred } => {
            stack.push(set);
            stack.push(pred);
        }
        ZFCSetExpr::Replacement { set, func } => {
            stack.push(set);
            stack.push(func);
        }
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
    }
}

fn push_zfc_children_for_bvar<'a>(
    set: &'a ZFCSetExpr,
    shifted_target: u32,
    stack: &mut Vec<(&'a Expr, u32)>,
) {
    match set {
        ZFCSetExpr::Singleton(expr)
        | ZFCSetExpr::Union(expr)
        | ZFCSetExpr::PowerSet(expr)
        | ZFCSetExpr::Choice(expr) => stack.push((expr, shifted_target)),
        ZFCSetExpr::Pair(left, right) => {
            stack.push((left, shifted_target));
            stack.push((right, shifted_target));
        }
        ZFCSetExpr::Separation { set, pred } => {
            stack.push((set, shifted_target));
            stack.push((pred, shifted_target + 1));
        }
        ZFCSetExpr::Replacement { set, func } => {
            stack.push((set, shifted_target));
            stack.push((func, shifted_target + 1));
        }
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
    }
}

fn synthetic_const(
    name: &str,
    kind: ConstantKind,
    type_: Expr,
    value: Option<Expr>,
    is_reducible: bool,
) -> ConstantInfo {
    ConstantInfo::new_with_reducibility(
        Name::from_string(name),
        Vec::new(),
        type_,
        value,
        if is_reducible {
            Reducibility::Reducible
        } else {
            Reducibility::Opaque
        },
        kind,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Level};

    fn name(s: &str) -> Name {
        Name::from_string(s)
    }

    fn c(s: &str) -> Expr {
        Expr::const_(name(s), Vec::<Level>::new())
    }

    fn app(func: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(func, args)
    }

    fn eq_type(lhs: Expr, rhs: Expr) -> Expr {
        app(c("Eq"), [c("Nat"), lhs, rhs])
    }

    fn theorem(name: &str, type_: Expr, proof: Expr) -> ConstantInfo {
        synthetic_const(name, ConstantKind::Theorem, type_, Some(proof), false)
    }

    fn axiom(name: &str, type_: Expr) -> ConstantInfo {
        synthetic_const(name, ConstantKind::Axiom, type_, None, false)
    }

    fn reducible_def(name: &str, value: Expr) -> ConstantInfo {
        synthetic_const(name, ConstantKind::Definition, c("Nat"), Some(value), true)
    }

    #[test]
    fn reports_direct_axiom_wrapper_root() {
        let type_ = eq_type(c("lhs"), c("rhs"));
        let proof = c("Existing.axiom");
        let theorem = theorem("Wrapped.theorem", type_.clone(), proof);
        let mut lookup = HashMap::new();
        lookup.insert(theorem.name.clone(), theorem.clone());
        lookup.insert(
            name("Existing.axiom"),
            axiom("Existing.axiom", type_.clone()),
        );

        let report = lint_constant(&lookup, &theorem, &NoMasqueradeConfig::default());

        assert!(matches!(
            report.findings.as_slice(),
            [NoMasqueradeFinding::DirectAxiomWrapper { theorem, axiom, peel_depth }]
                if theorem.to_string() == "Wrapped.theorem"
                    && axiom.to_string() == "Existing.axiom"
                    && *peel_depth == 0
        ));
    }

    #[test]
    fn reports_refl_root_on_nontrivial_named_eq() {
        let type_ = eq_type(c("lhs"), c("rhs"));
        let proof = app(c("Eq.refl"), [c("Nat"), c("lhs")]);
        let theorem = theorem("Suspicious.refl", type_, proof);
        let lookup = HashMap::from([(theorem.name.clone(), theorem.clone())]);

        let report = lint_constant(&lookup, &theorem, &NoMasqueradeConfig::default());

        assert!(report.findings.iter().any(|finding| matches!(
            finding,
            NoMasqueradeFinding::ReflRootOnNamedTheorem { theorem, peel_depth }
                if theorem.to_string() == "Suspicious.refl" && *peel_depth == 0
        )));
    }

    #[test]
    fn does_not_report_refl_root_on_syntactic_identity_eq() {
        let type_ = eq_type(c("lhs"), c("lhs"));
        let proof = app(c("Eq.refl"), [c("Nat"), c("lhs")]);
        let theorem = theorem("Trivial.refl", type_, proof);
        let lookup = HashMap::from([(theorem.name.clone(), theorem.clone())]);

        let report = lint_constant(&lookup, &theorem, &NoMasqueradeConfig::default());

        assert!(!report
            .findings
            .iter()
            .any(|finding| matches!(finding, NoMasqueradeFinding::ReflRootOnNamedTheorem { .. })));
    }

    #[test]
    fn reports_missing_required_body_bvar_for_ignored_ih() {
        let body = Expr::app(c("Nat.succ"), Expr::bvar(1));
        let proof = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("IH"), body),
        );
        let theorem = theorem("Induction.step", eq_type(c("lhs"), c("rhs")), proof);
        let lookup = HashMap::from([(theorem.name.clone(), theorem.clone())]);
        let config = NoMasqueradeConfig {
            required_symbols: vec![RequiredSymbol::body_bvar("ih", 0)],
            ..NoMasqueradeConfig::default()
        };

        let report = lint_constant(&lookup, &theorem, &config);

        assert!(report.findings.iter().any(|finding| matches!(
            finding,
            NoMasqueradeFinding::MissingRequiredSymbol {
                theorem,
                symbol: RequiredSymbol::BodyBVar { label, index }
            } if theorem.to_string() == "Induction.step" && label == "ih" && *index == 0
        )));
    }

    #[test]
    fn reports_missing_required_theorem_arg_for_ignored_ih() {
        let body = Expr::app(c("Nat.succ"), Expr::bvar(1));
        let proof = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("IH"), body),
        );
        let theorem = theorem("Induction.step", eq_type(c("lhs"), c("rhs")), proof);
        let lookup = HashMap::from([(theorem.name.clone(), theorem.clone())]);
        let config = NoMasqueradeConfig {
            required_symbols: vec![RequiredSymbol::theorem_arg("ih", 1)],
            ..NoMasqueradeConfig::default()
        };

        let report = lint_constant(&lookup, &theorem, &config);

        assert!(report.findings.iter().any(|finding| matches!(
            finding,
            NoMasqueradeFinding::MissingRequiredSymbol {
                theorem,
                symbol: RequiredSymbol::TheoremArg { label, arg_index }
            } if theorem.to_string() == "Induction.step" && label == "ih" && *arg_index == 1
        )));
    }

    #[test]
    fn required_body_bvar_passes_when_ih_is_used() {
        let body = Expr::app(c("useIH"), Expr::bvar(0));
        let proof = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("IH"), body),
        );
        let theorem = theorem("Induction.step", eq_type(c("lhs"), c("rhs")), proof);
        let lookup = HashMap::from([(theorem.name.clone(), theorem.clone())]);
        let config = NoMasqueradeConfig {
            required_symbols: vec![RequiredSymbol::body_bvar("ih", 0)],
            ..NoMasqueradeConfig::default()
        };

        let report = lint_constant(&lookup, &theorem, &config);

        assert!(!report
            .findings
            .iter()
            .any(|finding| matches!(finding, NoMasqueradeFinding::MissingRequiredSymbol { .. })));
    }

    #[test]
    fn required_theorem_arg_passes_when_ih_is_used() {
        let body = Expr::app(c("useIH"), Expr::bvar(0));
        let proof = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("IH"), body),
        );
        let theorem = theorem("Induction.step", eq_type(c("lhs"), c("rhs")), proof);
        let lookup = HashMap::from([(theorem.name.clone(), theorem.clone())]);
        let config = NoMasqueradeConfig {
            required_symbols: vec![RequiredSymbol::theorem_arg("ih", 1)],
            ..NoMasqueradeConfig::default()
        };

        let report = lint_constant(&lookup, &theorem, &config);

        assert!(!report
            .findings
            .iter()
            .any(|finding| matches!(finding, NoMasqueradeFinding::MissingRequiredSymbol { .. })));
    }

    #[test]
    fn required_theorem_arg_maps_declaration_order_across_three_binders() {
        let body = Expr::app(c("useOuter"), Expr::bvar(2));
        let proof = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(
                BinderInfo::Default,
                c("IH"),
                Expr::lam(BinderInfo::Default, c("Step"), body),
            ),
        );
        let theorem = theorem("Induction.step3", eq_type(c("lhs"), c("rhs")), proof);
        let lookup = HashMap::from([(theorem.name.clone(), theorem.clone())]);
        let config = NoMasqueradeConfig {
            required_symbols: vec![RequiredSymbol::theorem_arg("major", 0)],
            ..NoMasqueradeConfig::default()
        };

        let report = lint_constant(&lookup, &theorem, &config);

        assert!(!report
            .findings
            .iter()
            .any(|finding| matches!(finding, NoMasqueradeFinding::MissingRequiredSymbol { .. })));
    }

    #[test]
    fn required_theorem_arg_survives_nested_lam_and_let_shifts() {
        let body = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::let_named(
                Name::anon(),
                c("Nat"),
                c("zero"),
                app(c("useIH"), [Expr::bvar(2), Expr::bvar(0)]),
                false,
            ),
        );
        let proof = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("IH"), body),
        );
        let theorem = theorem("Induction.shifted", eq_type(c("lhs"), c("rhs")), proof);
        let lookup = HashMap::from([(theorem.name.clone(), theorem.clone())]);
        let config = NoMasqueradeConfig {
            required_symbols: vec![RequiredSymbol::theorem_arg("ih", 1)],
            ..NoMasqueradeConfig::default()
        };

        let report = lint_constant(&lookup, &theorem, &config);

        assert!(!report
            .findings
            .iter()
            .any(|finding| matches!(finding, NoMasqueradeFinding::MissingRequiredSymbol { .. })));
    }

    #[test]
    fn classifies_constant_carrier_definition() {
        let value = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("Nat"), c("zero")),
        );
        let carrier = reducible_def("Carrier.const", value);

        assert_eq!(
            classify_argument_discarding_carrier(&carrier),
            Some(CarrierShape::ConstantBody { lambda_arity: 2 })
        );
    }

    #[test]
    fn classifies_identity_carrier_definition() {
        let value = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("Nat"), Expr::bvar(1)),
        );
        let carrier = reducible_def("Carrier.identity", value);

        assert_eq!(
            classify_argument_discarding_carrier(&carrier),
            Some(CarrierShape::IdentityOnArgument {
                lambda_arity: 2,
                returned_arg: 0,
            })
        );
    }

    #[test]
    fn reports_argument_discarding_carrier_referenced_by_theorem_type() {
        let value = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                Expr::app(c("Nat.succ"), Expr::bvar(1)),
            ),
        );
        let carrier = reducible_def("Carrier.partial", value);
        let theorem = theorem(
            "Uses.carrier",
            eq_type(Expr::app(c("Carrier.partial"), c("x")), c("rhs")),
            app(c("Eq.refl"), [c("Nat"), c("rhs")]),
        );
        let lookup = HashMap::from([
            (carrier.name.clone(), carrier),
            (theorem.name.clone(), theorem.clone()),
        ]);

        let report = lint_constant(&lookup, &theorem, &NoMasqueradeConfig::default());

        assert!(report.findings.iter().any(|finding| matches!(
            finding,
            NoMasqueradeFinding::ArgumentDiscardingCarrier {
                carrier,
                shape: CarrierShape::DiscardsArguments {
                    lambda_arity,
                    used_args,
                    discarded_args,
                },
                context: CarrierContext::TheoremType { theorem }
            } if carrier.to_string() == "Carrier.partial"
                && *lambda_arity == 2
                && used_args == &vec![0]
                && discarded_args == &vec![1]
                && theorem.to_string() == "Uses.carrier"
        )));
    }
}
