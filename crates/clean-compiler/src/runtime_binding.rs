// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit, conservative runtime binding-order reachability. No source or
//! binary authority: default compiler entries retain their global refusals.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use clean_kernel::expr::UsedConstants;
use clean_kernel::{ConstantInfo, Environment, Expr, ExprKind, Name};

use crate::error::CompilerError;
use crate::ir::{IRBody, IRDecl, IRExpr};
use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, FunDecl, LetValue, Param};

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub(crate) struct Attributes {
    implementation: Option<Name>,
    csimp_rules: Vec<clean_kernel::env::csimp::Rule>,
    external: Option<String>,
    noncomputable: bool,
    unsafe_: bool,
    partial: bool,
}

/// A checked over-approximation of selected logical and runtime dependencies.
/// Private fields; no caller-provided favorable hashes or member lists. The
/// full Environment remains intact and is rechecked at each scoped consumer.
/// This is compiler-policy evidence, not source or binary proof authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeBindingClosure {
    roots: BTreeSet<Name>,
    digests: BTreeMap<Name, [u8; 32]>,
    attributes: BTreeMap<Name, Attributes>,
}

/// An opaque discovery of the actual runtime binding dependencies and their
/// compiler attributes, without encoding or digesting kernel records.
///
/// This is a member-population plan, not resource admission, a source snapshot,
/// or a checked compiler closure. A caller must bound and bind the represented
/// rows and these attributes from the same immutable environment before calling
/// [`Self::finish`]. No constructor accepts a favorable member list or digest.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct RuntimeBindingPlan {
    roots: BTreeSet<Name>,
    attributes: BTreeMap<Name, Attributes>,
    max_members: usize,
}

impl RuntimeBindingPlan {
    /// Discover the ordinary logical/runtime fixpoint without calling
    /// `Environment::closure_digest`. Refuse when its unique member population
    /// would exceed `max_members`; zero never means unlimited.
    pub fn discover(
        env: &Environment,
        roots: &[Name],
        max_members: usize,
    ) -> Result<Self, CompilerError> {
        discover(env, roots, max_members, |_| Ok(()))
    }

    /// Exact requested roots, independent of their diagnostic display names.
    pub fn roots(&self) -> impl ExactSizeIterator<Item = &Name> {
        self.roots.iter()
    }

    /// Every discovered logical/runtime member, including family metadata and
    /// implementation or selected compiler-simplification dependencies.
    pub fn members(&self) -> impl ExactSizeIterator<Item = &Name> {
        self.attributes.keys()
    }

    #[cfg(feature = "runtime-lcnf")]
    pub(crate) fn attribute_rows(&self) -> &BTreeMap<Name, Attributes> {
        &self.attributes
    }

    /// Recheck the same bounded discovery and compiler attributes without
    /// encoding kernel record digests. Observations must reject stale plans.
    pub fn recheck_discovery(&self, env: &Environment) -> Result<(), CompilerError> {
        let roots: Vec<_> = self.roots.iter().cloned().collect();
        if Self::discover(env, &roots, self.max_members)? != *self {
            return Err(refusal(
                "runtime binding plan members or compiler attributes changed",
            ));
        }
        Ok(())
    }

    /// Mint the ordinary checked closure after independently rediscovering the
    /// bounded population and attributes in the supplied environment.
    ///
    /// This method does not enforce row/byte budgets or authenticate an external
    /// snapshot. Those are the caller's responsibility before calling it on the
    /// same immutable environment. Ordinary closure record digests and all
    /// downstream rechecks remain unchanged.
    pub fn finish(&self, env: &Environment) -> Result<RuntimeBindingClosure, CompilerError> {
        let roots: Vec<_> = self.roots.iter().cloned().collect();
        self.recheck_discovery(env)?;
        let closure = RuntimeBindingClosure::check(env, &roots)?;
        if closure.roots != self.roots || closure.attributes != self.attributes {
            return Err(refusal(
                "runtime binding plan members or compiler attributes changed",
            ));
        }
        Ok(closure)
    }
}

/// The shared walk preserves the ordinary check's digest callback position:
/// after discovering each kernel cone and before processing its attributes.
/// Plan discovery uses the identical walk with no record-digest callback.
fn discover(
    env: &Environment,
    requested_roots: &[Name],
    max_members: usize,
    mut visit_closure: impl FnMut(&Name) -> Result<(), CompilerError>,
) -> Result<RuntimeBindingPlan, CompilerError> {
    let mut roots = BTreeSet::new();
    for root in requested_roots {
        if !roots.contains(root) && roots.len() == max_members {
            return Err(refusal("runtime binding member population bound exceeded"));
        }
        roots.insert(root.clone());
    }
    if roots.is_empty() {
        return Err(refusal("runtime closure requires a root"));
    }
    let mut pending: Vec<Name> = roots.iter().cloned().collect();
    let mut visited_roots = BTreeSet::new();
    let mut attributes = BTreeMap::new();
    while let Some(root) = pending.pop() {
        if visited_roots.contains(&root) {
            continue;
        }
        let closure = env
            .dependency_closure(&root)
            .map_err(|e| refusal(e.to_string()))?;
        visit_closure(&root)?;
        visited_roots.insert(root);
        for name in closure {
            if attributes.contains_key(&name) {
                continue;
            }
            if attributes.len() == max_members {
                return Err(refusal("runtime binding member population bound exceeded"));
            }
            let csimp_rules = clean_kernel::env::csimp::rules_for(env, Some(&name));
            if let Some(value) = env.get_const(&name).and_then(|c| c.value.as_ref()) {
                let mut references = HashSet::new();
                value.used_constants_dag(UsedConstants::WithProjectionStructures, &mut references);
                // Include every selected chain link and its theorem in the
                // checked closure, even when later erasure drops a reference.
                let mut changed = true;
                while changed {
                    changed = false;
                    let current: Vec<_> = references.iter().cloned().collect();
                    for from in current {
                        if let Some(rule) = csimp_rules.iter().rev().find(|r| r.from == from) {
                            crate::csimp::runtime_name(
                                env,
                                &csimp_rules,
                                &from,
                                crate::CodeMeaning::LeanCompiled,
                            )?;
                            if references.insert(rule.to.clone()) {
                                changed = true;
                            }
                            pending.push(rule.to.clone());
                            pending.push(rule.theorem.clone());
                        }
                    }
                }
            }
            let implementation = env.get_implemented_by(&name).cloned();
            if let Some(target) = &implementation {
                // Same link-type/unsafe/cycle semantics as actual lowering.
                crate::implemented_by::runtime_const_name(env, &name)?;
                pending.push(target.clone());
            }
            attributes.insert(
                name.clone(),
                Attributes {
                    implementation,
                    csimp_rules,
                    external: env.get_extern(&name).cloned(),
                    noncomputable: env.is_noncomputable(&name),
                    unsafe_: env.is_unsafe(&name),
                    partial: env.is_partial(&name),
                },
            );
        }
    }
    if let Some(record) = crate::implemented_by::order(env) {
        if let Some((referrer, why)) = record
            .iter()
            .filter(|(name, why)| {
                attributes.contains_key(*name)
                    || attributes.contains_key(&why.rebound)
                    || attributes.contains_key(&why.via)
            })
            .min_by_key(|(name, _)| (*name).clone())
        {
            return Err(CompilerError::RuntimeBindingOrder {
                referrer: referrer.clone(),
                rebound: why.rebound.clone(),
                via: why.via.clone(),
            });
        }
    }
    Ok(RuntimeBindingPlan {
        roots,
        attributes,
        max_members,
    })
}

impl RuntimeBindingClosure {
    /// Follow the actual kernel closures and every runtime implementation
    /// target to a fixpoint. Refuse any reached order referrer OR rebound,
    /// including intermediate targets and logical bodies that may be erased.
    pub fn check(env: &Environment, roots: &[Name]) -> Result<Self, CompilerError> {
        let mut digests = BTreeMap::new();
        let plan = discover(env, roots, usize::MAX, |root| {
            digests.insert(
                root.clone(),
                env.closure_digest(root)
                    .map_err(|error| refusal(error.to_string()))?,
            );
            Ok(())
        })?;
        Ok(Self {
            roots: plan.roots,
            digests,
            attributes: plan.attributes,
        })
    }

    fn recheck(&self, env: &Environment) -> Result<(), CompilerError> {
        let actual = Self::check(env, &self.roots.iter().cloned().collect::<Vec<_>>())?;
        if &actual != self {
            return Err(refusal(
                "runtime closure declarations or compiler attributes changed",
            ));
        }
        Ok(())
    }

    fn references(
        &self,
        env: &Environment,
        names: BTreeSet<Name>,
        transformed: bool,
    ) -> Result<(), CompilerError> {
        for name in names {
            if self.attributes.contains_key(&name) {
                continue;
            }
            // Only compiler-owned stage outputs may introduce synthetic names.
            // A resident declaration, any compiler binding, or an order-record
            // participant is never such a name, even if a fresh helper collides.
            let declared = env.get_const(&name).is_some()
                || env.get_inductive(&name).is_some()
                || env.get_constructor(&name).is_some()
                || env.get_recursor(&name).is_some()
                || env.get_quot(&name).is_some();
            let order_participant = crate::implemented_by::order(env).is_some_and(|record| {
                record.iter().any(|(referrer, why)| {
                    referrer == &name || why.rebound == name || why.via == name
                })
            });
            if transformed
                && !declared
                && env.get_implemented_by(&name).is_none()
                && env.get_extern(&name).is_none()
                && !env.is_noncomputable(&name)
                && !env.is_unsafe(&name)
                && !env.is_partial(&name)
                && !order_participant
            {
                continue;
            }
            return Err(refusal(format!(
                "{name:?} is outside the checked runtime closure"
            )));
        }
        Ok(())
    }

    pub(crate) fn constant(
        &self,
        env: &Environment,
        info: &ConstantInfo,
    ) -> Result<(), CompilerError> {
        self.recheck(env)?;
        let mut names = Names::new(env);
        names.found.insert(info.name.clone());
        names.kernel_expression(&info.type_);
        if let Some(value) = &info.value {
            names.kernel_expression(value);
        }
        self.references(env, names.found, false)
    }

    pub(crate) fn declarations(
        &self,
        env: &Environment,
        decls: &[Decl],
    ) -> Result<(), CompilerError> {
        self.recheck(env)?;
        self.lcnf_references(env, decls, false)
    }

    pub(crate) fn transformed_declarations(
        &self,
        env: &Environment,
        decls: &[Decl],
    ) -> Result<(), CompilerError> {
        self.lcnf_references(env, decls, true)
    }

    fn lcnf_references(
        &self,
        env: &Environment,
        decls: &[Decl],
        transformed: bool,
    ) -> Result<(), CompilerError> {
        let mut names = Names::new(env);
        if transformed {
            // This private consumer runs only on the actual outputs of the
            // maintained Base/Mono/Impure passes. Its annotation grammar is
            // monomorphic compiler IR, not original CIC syntax.
            names.annotation_origin = AnnotationOrigin::CompilerMono;
        }
        for decl in decls {
            names.found.insert(decl.name.clone());
            names.expression(&decl.ty);
            names.params(&decl.params);
            if let DeclValue::Code(code) = &decl.body {
                names.code(code);
            }
        }
        self.references(env, names.found, transformed)
    }

    pub(crate) fn ir_declarations(
        &self,
        env: &Environment,
        decls: &[IRDecl],
    ) -> Result<(), CompilerError> {
        let mut names = BTreeSet::new();
        for decl in decls {
            names.insert(decl.name.clone());
            let mut pending = vec![&decl.body];
            while let Some(body) = pending.pop() {
                match body {
                    IRBody::VDecl { value, rest, .. } => {
                        match value {
                            IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } => {
                                names.insert(fn_id.0.clone());
                            }
                            IRExpr::Ctor { info, .. } | IRExpr::Reuse { ctor: info, .. } => {
                                names.insert(info.name.clone());
                            }
                            IRExpr::Proj { .. }
                            | IRExpr::Tag(_)
                            | IRExpr::Box { .. }
                            | IRExpr::Unbox { .. }
                            | IRExpr::Lit(_)
                            | IRExpr::ClosureApply { .. }
                            | IRExpr::UProj { .. }
                            | IRExpr::SProj { .. }
                            | IRExpr::IsShared(_)
                            | IRExpr::String(_)
                            | IRExpr::Reset(_) => {}
                        }
                        pending.push(rest);
                    }
                    IRBody::JDecl { body, rest, .. } => {
                        pending.push(body);
                        pending.push(rest);
                    }
                    IRBody::Inc { rest, .. }
                    | IRBody::Dec { rest, .. }
                    | IRBody::Set { rest, .. }
                    | IRBody::SetTag { rest, .. }
                    | IRBody::USet { rest, .. }
                    | IRBody::SSet { rest, .. } => pending.push(rest),
                    IRBody::Case { alts, default, .. } => {
                        for alt in alts {
                            names.insert(alt.ctor.name.clone());
                            pending.push(&alt.body);
                        }
                        if let Some(body) = default {
                            pending.push(body);
                        }
                    }
                    IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
                }
            }
        }
        self.references(env, names, true)
    }
}

struct Names<'a> {
    env: &'a Environment,
    found: BTreeSet<Name>,
    annotation_origin: AnnotationOrigin,
}

#[derive(Clone, Copy)]
enum AnnotationOrigin {
    Source,
    CompilerMono,
}
impl<'a> Names<'a> {
    fn new(env: &'a Environment) -> Self {
        Self {
            env,
            found: BTreeSet::new(),
            annotation_origin: AnnotationOrigin::Source,
        }
    }
    fn kernel_expression(&mut self, expr: &Expr) {
        let mut names = HashSet::new();
        expr.used_constants_dag(UsedConstants::WithProjectionStructures, &mut names);
        self.found.extend(names);
    }

    fn expression(&mut self, expr: &Expr) {
        if matches!(self.annotation_origin, AnnotationOrigin::CompilerMono) {
            self.mono_annotation(expr);
            return;
        }
        self.source_annotation(expr);
    }

    fn source_annotation(&mut self, expr: &Expr) {
        let mut names = HashSet::new();
        expr.used_constants_dag(UsedConstants::WithProjectionStructures, &mut names);
        for name in names {
            // Only an unbound TYPE placeholder is special; runtime Const
            // references are inserted directly and never use this exemption.
            if name == Name::from_string("_") && self.env.get_const(&name).is_none() {
                continue;
            }
            self.found.insert(name);
        }
    }

    fn mono_annotation(&mut self, expr: &Expr) {
        let mut pending = vec![expr];
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(std::ptr::from_ref(ty) as usize) {
                continue;
            }
            // Exact zero-universe constructors emitted by to_mono, only in
            // compiler-stage TYPE slots. Genuine Init declares these names as
            // compiler axioms: they remain forbidden in source/kernel terms.
            // No runtime/header name or applied/dependent term is filtered.
            if ty == &crate::to_mono::any_expr() || ty == &crate::to_mono::erased_expr() {
                continue;
            }
            match ty.kind() {
                ExprKind::Pi(_, domain, codomain) => {
                    pending.push(domain);
                    pending.push(codomain);
                }
                ExprKind::MData(_, inner) => pending.push(inner),
                _ => self.source_annotation(ty),
            }
        }
    }
    fn params(&mut self, params: &[Param]) {
        for p in params {
            self.expression(&p.ty);
        }
    }
    fn args(&mut self, args: &[Arg]) {
        for arg in args {
            if let Arg::Type(expr) = arg {
                self.expression(expr);
            }
        }
    }
    fn function(&mut self, f: &FunDecl) {
        self.params(&f.params);
        self.expression(&f.ty);
        self.code(&f.body);
    }
    fn code(&mut self, code: &Code) {
        match code {
            Code::Let(decl, body) => {
                self.expression(&decl.ty);
                match &decl.value {
                    LetValue::Const { name, args, .. } | LetValue::Ctor { name, args, .. } => {
                        self.found.insert(name.clone());
                        self.args(args);
                    }
                    LetValue::Reuse {
                        ctor_name, args, ..
                    } => {
                        self.found.insert(ctor_name.clone());
                        self.args(args);
                    }
                    LetValue::Proj { type_name, .. } => {
                        self.found.insert(type_name.clone());
                    }
                    LetValue::FVar { args, .. } => self.args(args),
                    LetValue::Lit(_) | LetValue::Erased => {}
                }
                self.code(body);
            }
            Code::Fun(f, body) | Code::JoinPoint(f, body) => {
                self.function(f);
                self.code(body);
            }
            Code::Cases(cases) => {
                self.found.insert(cases.type_name.clone());
                self.expression(&cases.result_type);
                for alt in &cases.alts {
                    if let Alt::Ctor {
                        ctor_name, params, ..
                    } = alt
                    {
                        self.found.insert(ctor_name.clone());
                        self.params(params);
                    }
                    self.code(alt.body());
                }
            }
            Code::Jmp { args, .. } => self.args(args),
            Code::Unreachable(ty) => self.expression(ty),
            Code::Return(_) => {}
        }
    }
}

fn refusal(detail: impl Into<String>) -> CompilerError {
    CompilerError::RuntimeBindingClosure {
        detail: detail.into(),
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "runtime_binding/scoped_tests.rs"]
mod scoped_tests;
