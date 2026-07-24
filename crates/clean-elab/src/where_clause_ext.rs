// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Extended where-clause elaboration with recursive bindings, type inference,
//! pattern matching, guards, and generalized syntax.

use std::collections::{HashMap, HashSet};

use clean_parser::{
    Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceMatchArm, SurfacePattern,
};

use crate::where_desugar::WhereClause;
use crate::where_desugar_ext::{analyze_where_deps, collect_free_idents, WhereDesugarError};

#[derive(Debug, Clone)]
pub(crate) struct WhereClauseExtConfig {
    pub(crate) allow_recursive_bindings: bool,
    pub(crate) allow_type_inference: bool,
    pub(crate) allow_pattern_bindings: bool,
    pub(crate) allow_guards: bool,
    pub(crate) max_binding_depth: usize,
    pub(crate) max_bindings: usize,
}

impl Default for WhereClauseExtConfig {
    fn default() -> Self {
        Self {
            allow_recursive_bindings: true,
            allow_type_inference: true,
            allow_pattern_bindings: true,
            allow_guards: true,
            max_binding_depth: 64,
            max_bindings: 256,
        }
    }
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum WhereBindingKind {
    Simple,
    Recursive {
        deps: Vec<String>,
    },
    Pattern {
        pattern: SurfacePattern,
        scrutinee: SurfaceExpr,
    },
    Guarded {
        condition: SurfaceExpr,
    },
}

#[derive(Debug, Clone)]
pub(crate) struct ExtWhereBinding {
    pub(crate) name: String,
    pub(crate) kind: WhereBindingKind,
    pub(crate) params: Vec<SurfaceBinder>,
    pub(crate) return_type: Option<SurfaceExpr>,
    pub(crate) body: SurfaceExpr,
    pub(crate) inferred_type: Option<SurfaceExpr>,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum WhereClauseExtError {
    #[error("cyclic extended where-clause dependency: {}", names.join(" -> "))]
    DependencyCycle { names: Vec<String>, span: Span },
    #[error("where clause has {count} bindings, exceeds max {max}")]
    ExceededMaxBindings {
        count: usize,
        max: usize,
        span: Span,
    },
    #[error("where binding depth {depth} exceeds max {max}")]
    ExceededMaxDepth {
        depth: usize,
        max: usize,
        span: Span,
    },
    #[error("pattern binding `{name}` is not allowed here")]
    PatternBindingNotAllowed { name: String, span: Span },
    #[error("guarded binding `{name}` is not allowed here")]
    GuardNotAllowed { name: String, span: Span },
    #[error("recursive binding `{name}` is not allowed here")]
    RecursiveBindingNotAllowed { name: String, span: Span },
    #[error("type inference for binding `{name}` is not allowed here")]
    TypeInferenceNotAllowed { name: String, span: Span },
    #[error("duplicate where binding `{name}`")]
    DuplicateBinding { name: String, span: Span },
    #[error("binding `{name}` depends on unresolved sibling `{dep}`")]
    UnresolvedDependency {
        name: String,
        dep: String,
        span: Span,
    },
}

#[derive(Debug, Clone, Default)]
pub(crate) struct WhereClauseExtResult {
    pub(crate) bindings: Vec<ExtWhereBinding>,
    pub(crate) recursive_groups: Vec<Vec<usize>>,
    pub(crate) inferred_types: HashMap<String, SurfaceExpr>,
}

#[must_use]
pub(crate) fn classify_binding(
    clause: &WhereClause,
    all_names: &HashSet<String>,
) -> WhereBindingKind {
    let locals: HashSet<&str> = clause
        .params
        .iter()
        .map(|b| b.name.as_str())
        .filter(|n| *n != "_")
        .collect();
    let mut deps: Vec<String> = collect_free_idents(&clause.body)
        .into_iter()
        .filter(|n| n != &clause.name && !locals.contains(n.as_str()) && all_names.contains(n))
        .collect();
    deps.sort_unstable();
    deps.dedup();
    if deps.is_empty() {
        WhereBindingKind::Simple
    } else {
        WhereBindingKind::Recursive { deps }
    }
}

#[must_use]
pub(crate) fn classify_bindings(clauses: &[WhereClause]) -> Vec<(usize, WhereBindingKind)> {
    let all_names: HashSet<String> = clauses.iter().map(|c| c.name.clone()).collect();
    clauses
        .iter()
        .enumerate()
        .map(|(i, c)| (i, classify_binding(c, &all_names)))
        .collect()
}

#[must_use]
pub(crate) fn infer_omitted_type(binding: &ExtWhereBinding) -> Option<SurfaceExpr> {
    if binding.return_type.is_some() {
        return None;
    }
    match &binding.body {
        SurfaceExpr::Lambda(..)
        | SurfaceExpr::PatternMatchLambda(..)
        | SurfaceExpr::Ident(..)
        | SurfaceExpr::SyntheticSorry(..)
        | SurfaceExpr::Universe(..)
        | SurfaceExpr::Lit(..)
        | SurfaceExpr::Hole(_)
        | SurfaceExpr::StructLit { .. } => Some(SurfaceExpr::Hole(binding.span)),
        _ if !binding.params.is_empty() => Some(SurfaceExpr::Hole(binding.span)),
        _ => None,
    }
}

pub(crate) fn validate_bindings(
    bindings: &[ExtWhereBinding],
    config: &WhereClauseExtConfig,
) -> Result<(), WhereClauseExtError> {
    if bindings.len() > config.max_bindings {
        return Err(WhereClauseExtError::ExceededMaxBindings {
            count: bindings.len(),
            max: config.max_bindings,
            span: bindings.first().map_or_else(Span::dummy, |b| b.span),
        });
    }
    let mut seen = HashSet::new();
    for binding in bindings {
        if !seen.insert(binding.name.clone()) {
            return Err(WhereClauseExtError::DuplicateBinding {
                name: binding.name.clone(),
                span: binding.span,
            });
        }
        if matches!(binding.kind, WhereBindingKind::Pattern { .. })
            && !config.allow_pattern_bindings
        {
            return Err(WhereClauseExtError::PatternBindingNotAllowed {
                name: binding.name.clone(),
                span: binding.span,
            });
        }
        if matches!(binding.kind, WhereBindingKind::Guarded { .. }) && !config.allow_guards {
            return Err(WhereClauseExtError::GuardNotAllowed {
                name: binding.name.clone(),
                span: binding.span,
            });
        }
        if (matches!(binding.kind, WhereBindingKind::Recursive { .. }) || self_recursive(binding))
            && !config.allow_recursive_bindings
        {
            return Err(WhereClauseExtError::RecursiveBindingNotAllowed {
                name: binding.name.clone(),
                span: binding.span,
            });
        }
        if !config.allow_type_inference
            && binding.return_type.is_none()
            && infer_omitted_type(binding).is_some()
        {
            return Err(WhereClauseExtError::TypeInferenceNotAllowed {
                name: binding.name.clone(),
                span: binding.span,
            });
        }
        let depth = binding_depth(binding);
        if depth > config.max_binding_depth {
            return Err(WhereClauseExtError::ExceededMaxDepth {
                depth,
                max: config.max_binding_depth,
                span: binding.span,
            });
        }
    }
    Ok(())
}

pub(crate) fn order_bindings(
    bindings: &[ExtWhereBinding],
) -> Result<Vec<usize>, WhereClauseExtError> {
    let mut name_to_idx = HashMap::with_capacity(bindings.len());
    for (idx, binding) in bindings.iter().enumerate() {
        if name_to_idx.insert(binding.name.clone(), idx).is_some() {
            return Err(WhereClauseExtError::DuplicateBinding {
                name: binding.name.clone(),
                span: binding.span,
            });
        }
    }
    let all_names: HashSet<String> = name_to_idx.keys().cloned().collect();
    let mut edges = vec![Vec::<usize>::new(); bindings.len()];
    let mut in_degree = vec![0usize; bindings.len()];
    for (idx, binding) in bindings.iter().enumerate() {
        for dep in binding_deps(binding, &all_names)? {
            if let Some(dep_idx) = name_to_idx.get(dep.as_str()).copied() {
                if dep_idx != idx && !edges[dep_idx].contains(&idx) {
                    edges[dep_idx].push(idx);
                    in_degree[idx] += 1;
                }
            } else {
                return Err(WhereClauseExtError::UnresolvedDependency {
                    name: binding.name.clone(),
                    dep,
                    span: binding.span,
                });
            }
        }
    }
    let mut queue: Vec<usize> = in_degree
        .iter()
        .enumerate()
        .filter_map(|(i, d)| (*d == 0).then_some(i))
        .collect();
    queue.sort_unstable_by(|a, b| b.cmp(a));
    let mut ordered = Vec::with_capacity(bindings.len());
    while let Some(idx) = queue.pop() {
        ordered.push(idx);
        for next in &edges[idx] {
            in_degree[*next] = in_degree[*next].saturating_sub(1);
            if in_degree[*next] == 0 {
                queue.push(*next);
                queue.sort_unstable_by(|a, b| b.cmp(a));
            }
        }
    }
    if ordered.len() == bindings.len() {
        Ok(ordered)
    } else {
        let names = in_degree
            .iter()
            .enumerate()
            .filter_map(|(i, d)| (*d > 0).then_some(bindings[i].name.clone()))
            .collect();
        let span = in_degree
            .iter()
            .position(|d| *d > 0)
            .and_then(|i| bindings.get(i))
            .map_or_else(Span::dummy, |b| b.span);
        Err(WhereClauseExtError::DependencyCycle { names, span })
    }
}

pub(crate) fn build_ext_where_bindings(
    clauses: &[WhereClause],
    config: &WhereClauseExtConfig,
) -> Result<WhereClauseExtResult, WhereClauseExtError> {
    if clauses.is_empty() {
        return Ok(WhereClauseExtResult::default());
    }
    let analysis = analyze_where_deps(clauses).map_err(map_dep_error)?;
    let mut bindings: Vec<ExtWhereBinding> = classify_bindings(clauses)
        .into_iter()
        .filter_map(|(i, kind)| {
            clauses.get(i).map(|c| ExtWhereBinding {
                name: c.name.clone(),
                kind,
                params: c.params.clone(),
                return_type: c.return_type.clone(),
                body: c.body.clone(),
                inferred_type: None,
                span: c.span,
            })
        })
        .collect();
    validate_bindings(&bindings, config)?;
    for binding in &mut bindings {
        binding.inferred_type = infer_omitted_type(binding);
    }
    let ordered_indices = if analysis.mutual_groups.is_empty() {
        order_bindings(&bindings)?
    } else {
        analysis.sorted_indices.clone()
    };
    let positions: HashMap<usize, usize> = ordered_indices
        .iter()
        .enumerate()
        .map(|(pos, idx)| (*idx, pos))
        .collect();
    let ordered_bindings: Vec<ExtWhereBinding> = ordered_indices
        .iter()
        .filter_map(|idx| bindings.get(*idx).cloned())
        .collect();
    let recursive_groups = analysis
        .mutual_groups
        .iter()
        .filter_map(|group| {
            let mut mapped: Vec<usize> = group
                .iter()
                .filter_map(|idx| positions.get(idx).copied())
                .collect();
            mapped.sort_unstable();
            (!mapped.is_empty()).then_some(mapped)
        })
        .collect();
    let inferred_types = ordered_bindings
        .iter()
        .filter_map(|b| b.inferred_type.clone().map(|ty| (b.name.clone(), ty)))
        .collect();
    Ok(WhereClauseExtResult {
        bindings: ordered_bindings,
        recursive_groups,
        inferred_types,
    })
}

#[must_use]
pub(crate) fn desugar_ext_where(body: SurfaceExpr, result: &WhereClauseExtResult) -> SurfaceExpr {
    let groups_by_end: HashMap<usize, Vec<usize>> = result
        .recursive_groups
        .iter()
        .filter_map(|group| {
            let mut group = group.clone();
            group.sort_unstable();
            group.last().copied().map(|end| (end, group))
        })
        .collect();
    let mut inner = body;
    let mut next = result.bindings.len();
    while next > 0 {
        let idx = next - 1;
        if let Some(group) = groups_by_end.get(&idx) {
            inner = group
                .iter()
                .rev()
                .filter_map(|pos| result.bindings.get(*pos))
                .fold(inner, |acc, b| let_rec(b, acc));
            next = group.first().copied().unwrap_or(0);
        } else {
            if let Some(binding) = result.bindings.get(idx) {
                inner = let_rec(binding, inner);
            }
            next -= 1;
        }
    }
    inner
}

pub(crate) fn process_where_clause_ext(
    body: SurfaceExpr,
    clauses: &[WhereClause],
    config: &WhereClauseExtConfig,
) -> Result<SurfaceExpr, WhereClauseExtError> {
    build_ext_where_bindings(clauses, config).map(|result| desugar_ext_where(body, &result))
}

fn map_dep_error(err: WhereDesugarError) -> WhereClauseExtError {
    match err {
        WhereDesugarError::CyclicDependency { names, span } => {
            WhereClauseExtError::DependencyCycle { names, span }
        }
        WhereDesugarError::DuplicateName { name, span } => {
            WhereClauseExtError::DuplicateBinding { name, span }
        }
    }
}

#[must_use]
fn let_rec(binding: &ExtWhereBinding, inner_body: SurfaceExpr) -> SurfaceExpr {
    let hole = SurfaceExpr::Hole(binding.span);
    let wrapped = match &binding.kind {
        WhereBindingKind::Simple | WhereBindingKind::Recursive { .. } => binding.body.clone(),
        WhereBindingKind::Pattern { pattern, scrutinee } => SurfaceExpr::Match(
            binding.span,
            None,
            Box::new(scrutinee.clone()),
            vec![
                SurfaceMatchArm {
                    span: binding.span,
                    pattern: pattern.clone(),
                    body: binding.body.clone(),
                },
                SurfaceMatchArm {
                    span: binding.span,
                    pattern: SurfacePattern::Wildcard,
                    body: hole.clone(),
                },
            ],
        ),
        WhereBindingKind::Guarded { condition } => SurfaceExpr::If(
            binding.span,
            Box::new(condition.clone()),
            Box::new(binding.body.clone()),
            Box::new(hole.clone()),
        ),
    };
    let value = if binding.params.is_empty() {
        wrapped
    } else {
        SurfaceExpr::Lambda(binding.span, binding.params.clone(), Box::new(wrapped))
    };
    let codomain = binding
        .return_type
        .clone()
        .or_else(|| binding.inferred_type.clone())
        .unwrap_or(hole);
    let binder_ty = if binding.params.is_empty() {
        codomain
    } else {
        SurfaceExpr::Pi(binding.span, binding.params.clone(), Box::new(codomain))
    };
    let binder = SurfaceBinder {
        span: binding.span,
        name: binding.name.clone(),
        ty: Some(Box::new(binder_ty)),
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };
    SurfaceExpr::LetRec(binding.span, binder, Box::new(value), Box::new(inner_body))
}

fn binding_deps(
    binding: &ExtWhereBinding,
    all_names: &HashSet<String>,
) -> Result<Vec<String>, WhereClauseExtError> {
    let mut locals: HashSet<String> = binding
        .params
        .iter()
        .map(|b| b.name.clone())
        .filter(|n| n != "_")
        .collect();
    if let WhereBindingKind::Pattern { pattern, .. } = &binding.kind {
        let mut names = Vec::new();
        pattern.collect_var_names(&mut names);
        locals.extend(names.into_iter().filter(|n| n != "_"));
    }
    let mut free = collect_free_idents(&binding.body);
    for expr in binding.params.iter().filter_map(|b| b.ty.as_deref()) {
        free.extend(collect_free_idents(expr));
    }
    for expr in binding.params.iter().filter_map(|b| b.default.as_deref()) {
        free.extend(collect_free_idents(expr));
    }
    if let Some(expr) = &binding.return_type {
        free.extend(collect_free_idents(expr));
    }
    if let Some(expr) = &binding.inferred_type {
        free.extend(collect_free_idents(expr));
    }
    match &binding.kind {
        WhereBindingKind::Pattern { scrutinee, .. } => free.extend(collect_free_idents(scrutinee)),
        WhereBindingKind::Guarded { condition } => free.extend(collect_free_idents(condition)),
        WhereBindingKind::Recursive { deps } => free.extend(deps.iter().cloned()),
        WhereBindingKind::Simple => {}
    }
    let mut deps: Vec<String> = free
        .into_iter()
        .filter(|n| n != &binding.name && !locals.contains(n) && all_names.contains(n))
        .collect();
    if let WhereBindingKind::Recursive { deps: explicit } = &binding.kind {
        for dep in explicit {
            if dep == &binding.name || locals.contains(dep) {
                continue;
            }
            if !all_names.contains(dep) {
                return Err(WhereClauseExtError::UnresolvedDependency {
                    name: binding.name.clone(),
                    dep: dep.clone(),
                    span: binding.span,
                });
            }
            deps.push(dep.clone());
        }
    }
    deps.sort_unstable();
    deps.dedup();
    Ok(deps)
}

#[must_use]
fn self_recursive(binding: &ExtWhereBinding) -> bool {
    collect_free_idents(&binding.body).contains(&binding.name)
        || binding
            .return_type
            .as_ref()
            .is_some_and(|e| collect_free_idents(e).contains(&binding.name))
        || matches!(&binding.kind, WhereBindingKind::Recursive { deps } if deps.iter().any(|dep| dep == &binding.name))
}

#[must_use]
fn binding_depth(binding: &ExtWhereBinding) -> usize {
    let kind_depth = match &binding.kind {
        WhereBindingKind::Simple | WhereBindingKind::Recursive { .. } => 0,
        WhereBindingKind::Pattern { scrutinee, .. } => expr_depth(scrutinee),
        WhereBindingKind::Guarded { condition } => expr_depth(condition),
    };
    binding
        .params
        .iter()
        .map(binder_depth)
        .chain([expr_depth(&binding.body), kind_depth])
        .chain(binding.return_type.iter().map(expr_depth))
        .chain(binding.inferred_type.iter().map(expr_depth))
        .max()
        .unwrap_or(0)
}

#[must_use]
fn binder_depth(binder: &SurfaceBinder) -> usize {
    binder
        .ty
        .as_deref()
        .map(expr_depth)
        .into_iter()
        .chain(binder.default.as_deref().map(expr_depth))
        .max()
        .unwrap_or(0)
}

#[must_use]
fn expr_depth(expr: &SurfaceExpr) -> usize {
    1 + match expr {
        SurfaceExpr::App(_, f, args) => args
            .iter()
            .map(|a| expr_depth(&a.expr))
            .fold(expr_depth(f), usize::max),
        SurfaceExpr::Lambda(_, bs, body)
        | SurfaceExpr::PatternMatchLambda(_, bs, body)
        | SurfaceExpr::Pi(_, bs, body) => bs
            .iter()
            .map(binder_depth)
            .fold(expr_depth(body), usize::max),
        SurfaceExpr::Let(_, b, v, body) | SurfaceExpr::LetRec(_, b, v, body) => {
            binder_depth(b).max(expr_depth(v)).max(expr_depth(body))
        }
        SurfaceExpr::Arrow(_, l, r) | SurfaceExpr::Ascription(_, l, r) => {
            expr_depth(l).max(expr_depth(r))
        }
        SurfaceExpr::If(_, c, t, e) | SurfaceExpr::IfLet(_, _, c, t, e) => {
            expr_depth(c).max(expr_depth(t)).max(expr_depth(e))
        }
        SurfaceExpr::IfDecidable(_, _, p, t, e) => {
            expr_depth(p).max(expr_depth(t)).max(expr_depth(e))
        }
        SurfaceExpr::Match(_, _, scrutinee, arms) => arms
            .iter()
            .map(|arm| expr_depth(&arm.body))
            .fold(expr_depth(scrutinee), usize::max),
        SurfaceExpr::Paren(_, e)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::NamedArg(_, _, e)
        | SurfaceExpr::Proj(_, e, _)
        | SurfaceExpr::LiftMethod(_, e)
        | SurfaceExpr::UniverseInst(_, e, _) => expr_depth(e),
        _ => 0,
    }
}
