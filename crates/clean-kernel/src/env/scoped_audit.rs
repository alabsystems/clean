// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete scoped judgments using the existing local-context kernel rules.

use super::*;
use crate::expr::{ExprFolderOpt, FVarId};
use crate::tc::{LocalContext, TypeChecker};

fn rejection(error: impl Into<String>) -> CertificationIssue {
    CertificationIssue::TermRejected {
        error: error.into(),
    }
}
fn rejection_debug(arguments: std::fmt::Arguments<'_>) -> CertificationIssue {
    rejection(bounded_diagnostic(arguments))
}
fn finish(
    audit: CertificationAudit,
    mut work: ScopedAuditWork,
    visits: usize,
) -> (CertificationAudit, ScopedAuditWork) {
    work.reference_visits = visits;
    work.total = crate::tc::declaration_budget_used();
    (audit, work)
}

struct ScopeReferences {
    allowed: HashSet<FVarId>,
    visited: HashSet<usize>,
    visits: usize,
    limit: usize,
    depth: usize,
    error: Option<CertificationIssue>,
}
struct ScopeStack<'a>(&'a mut ScopeReferences);
impl ExprFolderOpt for ScopeStack<'_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expression)
    }
}
impl ScopeReferences {
    fn scan(&mut self, expression: &Expr) -> Result<(), CertificationIssue> {
        if expression.has_loose_bvars_quick() {
            return Err(rejection("loose index in scoped judgment"));
        }
        self.fold_expr_opt(expression);
        self.error.clone().map_or(Ok(()), Err)
    }
}
impl ExprFolderOpt for ScopeReferences {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        if self.error.is_some() {
            return None;
        }
        if self.visits >= self.limit || self.depth >= 16_384 {
            self.error = Some(rejection("scoped judgment reference budget exceeded"));
            return None;
        }
        self.visits += 1;
        if !expression.has_fvar_quick() || !self.visited.insert(expression as *const Expr as usize)
        {
            return None;
        }
        self.depth += 1;
        ScopeStack(self).fold_expr_opt(expression);
        self.depth -= 1;
        None
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        if !self.allowed.contains(&id) {
            self.error = Some(rejection_debug(format_args!(
                "forward or untracked scoped local {id:?}"
            )));
        }
        None
    }
}

impl Environment {
    /// Replay every original declaration and the complete body. Parameters may
    /// occur only in the outer telescope and must match the frozen closed
    /// claim's successive Pi domains; later entries must have checked values.
    /// Every value is checked before insertion into one live local context.
    /// The existing checker options and any ambient budget are never reset.
    #[must_use]
    pub fn audit_scoped_certification(
        &self,
        context: &LocalContext,
        outer_count: usize,
        external_claim: &Expr,
        goal: &Expr,
        term: &Expr,
        reference_limit: usize,
    ) -> (CertificationAudit, ScopedAuditWork) {
        let mut audit = CertificationAudit::default();
        let mut work = ScopedAuditWork {
            ambient_limit: crate::tc::declaration_budget_limit(),
            ..ScopedAuditWork::default()
        };
        let mut refs = ScopeReferences {
            allowed: HashSet::new(),
            visited: HashSet::new(),
            visits: 0,
            limit: reference_limit,
            depth: 0,
            error: None,
        };
        if crate::env::mm_axiom_only()
            || reference_limit == 0
            || outer_count > context.len()
            || external_claim.has_fvar_quick()
            || external_claim.has_loose_bvars_quick()
        {
            audit.issues.push(rejection(
                "invalid original scoped claim or telescope boundary",
            ));
            return finish(audit, work, refs.visits);
        }
        let mut floor = 0;
        for (index, declaration) in context.iter().enumerate() {
            if declaration.id.as_u64() >= (1u64 << 63)
                || refs.allowed.contains(&declaration.id)
                || (index >= outer_count && declaration.value.is_none())
            {
                audit.issues.push(rejection(
                    "duplicate/reserved local or new component assumption",
                ));
                return finish(audit, work, refs.visits);
            }
            if let Err(error) = refs.scan(&declaration.type_).and_then(|()| {
                declaration
                    .value
                    .as_ref()
                    .map_or(Ok(()), |value| refs.scan(value))
            }) {
                audit.issues.push(error);
                return finish(audit, work, refs.visits);
            }
            refs.allowed.insert(declaration.id);
            floor = floor.max(declaration.id.as_u64() + 1);
        }
        if let Err(error) = refs.scan(goal).and_then(|()| refs.scan(term)) {
            audit.issues.push(error);
            return finish(audit, work, refs.visits);
        }
        let mut reserved = LocalContext::new();
        reserved.reserve_fvar_floor(floor);
        let mut checker = TypeChecker::with_context(self, reserved);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        if let Some(Some(value)) = self.get_option("maxHeartbeats") {
            if let Ok(limit) = value.parse::<u32>() {
                checker.set_heartbeat_limit(limit);
            }
        }
        if let Some(Some(value)) = self.get_option("tcMaxCacheEntries") {
            if let Ok(limit) = value.parse::<usize>() {
                checker.set_max_cache_entries(limit);
            }
        }
        let result = (|| -> Result<(), CertificationIssue> {
            for (index, declaration) in context.iter().enumerate() {
                let before = crate::tc::declaration_budget_used();
                let checked_type = checker.infer_sort(&declaration.type_);
                let after_type = crate::tc::declaration_budget_used();
                work.declarations.push(ScopedDeclarationWork {
                    id: declaration.id,
                    before,
                    after_type,
                    after_value: None,
                    installed: false,
                });
                let _sort = checked_type.map_err(|error| {
                    rejection_debug(format_args!(
                        "scoped declaration {index} {:?} type: {error:?}",
                        declaration.id
                    ))
                })?;
                if let Some(value) = &declaration.value {
                    let checked_value = checker.check_type(value, &declaration.type_);
                    if let Some(row) = work.declarations.last_mut() {
                        row.after_value = Some(crate::tc::declaration_budget_used());
                    }
                    checked_value.map_err(|error| {
                        rejection_debug(format_args!(
                            "scoped declaration {index} {:?} value: {error:?}",
                            declaration.id
                        ))
                    })?;
                    checker.ctx_mut().push_let_with_id(
                        declaration.id,
                        declaration.name.clone(),
                        declaration.type_.clone(),
                        value.clone(),
                    );
                } else {
                    checker.ctx_mut().push_with_id(
                        declaration.id,
                        declaration.name.clone(),
                        declaration.type_.clone(),
                        declaration.bi,
                    );
                }
                if let Some(row) = work.declarations.last_mut() {
                    row.installed = true;
                }
            }
            work.after_declarations = Some(crate::tc::declaration_budget_used());
            match checker.infer_sort(external_claim) {
                Ok(sort) if sort.is_zero() => {}
                result => {
                    return Err(rejection_debug(format_args!(
                        "original external claim is not a proposition: {result:?}"
                    )));
                }
            }
            work.after_external_type = Some(crate::tc::declaration_budget_used());
            // Keep the unconsumed body intact. Applying one substitution after
            // all outer binders avoids replaying its complete suffix at every
            // Pi/LET. Prefix LET values are themselves opened in their exact
            // earlier environment; no equation or parameter is discarded.
            let mut current = external_claim.clone();
            let mut arguments = Vec::new();
            let instantiate = |expression: &Expr, values: &[Expr]| {
                checker
                    .metered_scoped_operation(|| expression.instantiate_rev(values))
                    .map_err(|error| {
                        rejection_debug(format_args!("scoped claim substitution: {error:?}"))
                    })
            };
            for (index, declaration) in context.iter().take(outer_count).enumerate() {
                if let Some(value) = &declaration.value {
                    if let ExprKind::Let(name, ty, candidate, body, _) = current.kind() {
                        let replacements: Vec<_> = arguments.iter().rev().cloned().collect();
                        let ty = instantiate(ty, &replacements)?;
                        let candidate = instantiate(candidate, &replacements)?;
                        let matches = checker
                            .metered_scoped_operation(|| {
                                *name == declaration.name
                                    && ty == declaration.type_
                                    && candidate == *value
                            })
                            .map_err(|error| {
                                rejection_debug(format_args!(
                                    "scoped claim definition comparison: {error:?}"
                                ))
                            })?;
                        if matches {
                            let body = body.as_ref().clone();
                            arguments.push(Expr::fvar(declaration.id));
                            current = body;
                            work.matched_claim_bindings += 1;
                        }
                    }
                    continue;
                }
                while let ExprKind::Let(_, _, value, body, _) = current.kind() {
                    let replacements: Vec<_> = arguments.iter().rev().cloned().collect();
                    let value = instantiate(value, &replacements)?;
                    let body = body.as_ref().clone();
                    arguments.push(value);
                    current = body;
                    work.inlined_claim_lets += 1;
                }
                if !matches!(current.kind(), ExprKind::Pi(..)) {
                    let replacements: Vec<_> = arguments.iter().rev().cloned().collect();
                    current = checker.whnf(&instantiate(&current, &replacements)?);
                    arguments.clear();
                }
                let ExprKind::Pi(data, domain, body) = current.kind() else {
                    return Err(rejection_debug(format_args!(
                        "original external claim lacks telescope parameter {index}"
                    )));
                };
                let replacements: Vec<_> = arguments.iter().rev().cloned().collect();
                let domain = instantiate(domain, &replacements)?;
                if *data != declaration.bi || !checker.is_def_eq(&domain, &declaration.type_) {
                    return Err(rejection_debug(format_args!(
                        "original external claim parameter {index} type differs"
                    )));
                }
                let body = body.as_ref().clone();
                arguments.push(Expr::fvar(declaration.id));
                current = body;
                work.matched_claim_bindings += 1;
            }
            work.after_parameters = Some(crate::tc::declaration_budget_used());
            let replacements: Vec<_> = arguments.iter().rev().cloned().collect();
            let opened = instantiate(&current, &replacements)?;
            if !checker.is_def_eq(&opened, goal) {
                return Err(rejection(
                    "scoped goal differs from the complete original external claim",
                ));
            }
            match checker.infer_sort(goal) {
                Ok(sort) if sort.is_zero() => {}
                result => {
                    return Err(rejection_debug(format_args!(
                        "scoped goal is not a proposition: {result:?}"
                    )));
                }
            }
            work.after_claim = Some(crate::tc::declaration_budget_used());
            checker.check_type(term, goal).map_err(|error| {
                rejection_debug(format_args!("complete scoped root body: {error:?}"))
            })?;
            work.after_body = Some(crate::tc::declaration_budget_used());
            Ok(())
        })();
        drop(checker);
        if let Err(error) = result {
            audit.issues.push(error);
            return finish(audit, work, refs.visits);
        }
        let mut roots = HashSet::new();
        for expression in [external_claim, goal, term] {
            collect_const_refs(expression, &mut roots);
        }
        for declaration in context.iter() {
            collect_const_refs(&declaration.type_, &mut roots);
            if let Some(value) = &declaration.value {
                collect_const_refs(value, &mut roots);
            }
        }
        audit = self.audit_certification_dependencies(audit, roots);
        work.after_dependencies = Some(crate::tc::declaration_budget_used());
        finish(audit, work, refs.visits)
    }
}

#[cfg(test)]
#[path = "scoped_audit_tests.rs"]
mod tests;
