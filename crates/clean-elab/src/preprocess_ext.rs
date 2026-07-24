// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended declaration preprocessing pipeline: docstring extraction, mutual
//! block detection, universe param collection, attribute validation, namespace
//! resolution, import expansion, syntax desugaring, dependency ordering, and
//! statistics tracking.

use clean_parser::{SurfaceDecl, SurfaceExpr};
use std::collections::{HashMap, HashSet, VecDeque};

/// Errors from extended preprocessing.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum PreprocessError {
    #[error("cyclic dependency between declarations: {0:?}")]
    CyclicDependency(Vec<String>),
    #[error("unknown attribute on '{decl_name}': {attr}")]
    UnknownAttribute { decl_name: String, attr: String },
    #[error("unresolved name '{name}' in '{decl_name}'")]
    UnresolvedName { decl_name: String, name: String },
    #[error("duplicate declaration name: {0}")]
    DuplicateName(String),
}

/// Docstring extracted from source and associated with a declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Docstring {
    pub(crate) text: String,
    pub(crate) decl_name: String,
}

/// Group of mutually-recursive declarations detected by reference analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MutualGroup {
    pub(crate) indices: Vec<usize>,
    pub(crate) names: Vec<String>,
}

/// Collected universe parameter from a declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UniverseParam {
    pub(crate) name: String,
    pub(crate) decl_name: String,
}

/// Statistics from a preprocessing run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PreprocessStats {
    pub(crate) decls_preprocessed: usize,
    pub(crate) mutual_blocks_found: usize,
    pub(crate) desugared: usize,
    pub(crate) reordered: usize,
    pub(crate) docstrings_extracted: usize,
    pub(crate) universe_params_collected: usize,
    pub(crate) attributes_validated: usize,
    pub(crate) names_resolved: usize,
    pub(crate) imports_expanded: usize,
}

/// Result of the full preprocessing pipeline.
#[derive(Debug, Clone)]
pub(crate) struct PreprocessResult {
    pub(crate) decls: Vec<SurfaceDecl>,
    pub(crate) docstrings: Vec<Docstring>,
    pub(crate) mutual_groups: Vec<MutualGroup>,
    pub(crate) universe_params: Vec<UniverseParam>,
    pub(crate) stats: PreprocessStats,
}

/// Extract name from a surface declaration.
#[must_use]
pub(crate) fn decl_name(decl: &SurfaceDecl) -> Option<&str> {
    match decl {
        SurfaceDecl::Def { name, .. }
        | SurfaceDecl::Theorem { name, .. }
        | SurfaceDecl::Axiom { name, .. }
        | SurfaceDecl::Opaque { name, .. }
        | SurfaceDecl::Inductive { name, .. }
        | SurfaceDecl::Coinductive { name, .. }
        | SurfaceDecl::Structure { name, .. }
        | SurfaceDecl::Class { name, .. }
        | SurfaceDecl::Namespace { name, .. } => Some(name.as_str()),
        SurfaceDecl::Instance { name, .. } => name.as_deref(),
        _ => None,
    }
}

fn decl_universe_params(decl: &SurfaceDecl) -> &[String] {
    match decl {
        SurfaceDecl::Def {
            universe_params, ..
        }
        | SurfaceDecl::Theorem {
            universe_params, ..
        }
        | SurfaceDecl::Axiom {
            universe_params, ..
        }
        | SurfaceDecl::Opaque {
            universe_params, ..
        }
        | SurfaceDecl::Inductive {
            universe_params, ..
        }
        | SurfaceDecl::Coinductive {
            universe_params, ..
        }
        | SurfaceDecl::Structure {
            universe_params, ..
        }
        | SurfaceDecl::Class {
            universe_params, ..
        }
        | SurfaceDecl::Instance {
            universe_params, ..
        } => universe_params,
        _ => &[],
    }
}

fn decl_attr_count(decl: &SurfaceDecl) -> usize {
    match decl {
        SurfaceDecl::Def { attrs, .. }
        | SurfaceDecl::Theorem { attrs, .. }
        | SurfaceDecl::Axiom { attrs, .. }
        | SurfaceDecl::Opaque { attrs, .. } => attrs.len(),
        _ => 0,
    }
}

// Step 1: Docstring extraction

/// Extract docstrings (`/-- ... -/` or `-- ...`) and associate with declarations.
#[must_use]
pub(crate) fn extract_docstrings(comments: &[&str], decls: &[SurfaceDecl]) -> Vec<Docstring> {
    let mut result = Vec::new();
    for (i, &comment) in comments.iter().enumerate() {
        let trimmed = comment.trim();
        let text = if trimmed.len() >= 5 && trimmed.starts_with("/--") && trimmed.ends_with("-/") {
            trimmed[3..trimmed.len() - 2].trim().to_string()
        } else if let Some(rest) = trimmed.strip_prefix("--") {
            rest.trim().to_string()
        } else {
            continue;
        };
        if !text.is_empty() {
            if let Some(decl) = decls.get(i) {
                result.push(Docstring {
                    text,
                    decl_name: decl_name(decl).unwrap_or("<anonymous>").to_string(),
                });
            }
        }
    }
    result
}

// Step 2: Mutual block detection

/// Collect identifiers referenced in a surface expression.
pub(crate) fn collect_idents(expr: &SurfaceExpr, out: &mut HashSet<String>) {
    match expr {
        SurfaceExpr::Ident(_, name) => {
            out.insert(name.clone());
        }
        SurfaceExpr::App(_, func, args) => {
            collect_idents(func, out);
            for arg in args {
                collect_idents(&arg.expr, out);
            }
        }
        SurfaceExpr::Lambda(_, _, body)
        | SurfaceExpr::PatternMatchLambda(_, _, body)
        | SurfaceExpr::Pi(_, _, body) => collect_idents(body, out),
        SurfaceExpr::Arrow(_, lhs, rhs)
        | SurfaceExpr::Let(_, _, lhs, rhs)
        | SurfaceExpr::LetRec(_, _, lhs, rhs) => {
            collect_idents(lhs, out);
            collect_idents(rhs, out);
        }
        SurfaceExpr::Paren(_, inner) | SurfaceExpr::Ascription(_, inner, _) => {
            collect_idents(inner, out);
        }
        _ => {}
    }
}

fn collect_decl_refs(decl: &SurfaceDecl) -> HashSet<String> {
    let mut refs = HashSet::new();
    match decl {
        SurfaceDecl::Def { ty, val, .. } => {
            if let Some(ty) = ty {
                collect_idents(ty, &mut refs);
            }
            collect_idents(val, &mut refs);
        }
        SurfaceDecl::Theorem { ty, proof, .. } => {
            collect_idents(ty, &mut refs);
            collect_idents(proof, &mut refs);
        }
        SurfaceDecl::Axiom { ty, .. } | SurfaceDecl::Opaque { ty, .. } => {
            collect_idents(ty, &mut refs);
        }
        _ => {}
    }
    refs
}

/// Detect mutually-recursive declaration groups via SCC analysis.
#[must_use]
pub(crate) fn detect_mutual_groups(decls: &[SurfaceDecl]) -> Vec<MutualGroup> {
    let name_to_idx: HashMap<&str, usize> = decls
        .iter()
        .enumerate()
        .filter_map(|(i, d)| decl_name(d).map(|n| (n, i)))
        .collect();
    let n = decls.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, decl) in decls.iter().enumerate() {
        for r in collect_decl_refs(decl) {
            if let Some(&j) = name_to_idx.get(r.as_str()) {
                if j != i {
                    adj[i].push(j);
                }
            }
        }
    }
    tarjan_sccs(&adj, n)
        .into_iter()
        .filter(|scc| scc.len() > 1)
        .map(|indices| {
            let names = indices
                .iter()
                .filter_map(|&i| decl_name(&decls[i]).map(String::from))
                .collect();
            MutualGroup { indices, names }
        })
        .collect()
}

fn tarjan_sccs(adj: &[Vec<usize>], n: usize) -> Vec<Vec<usize>> {
    let mut idx = 0usize;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; n];
    let mut indices = vec![usize::MAX; n];
    let mut lowlinks = vec![usize::MAX; n];
    let mut result: Vec<Vec<usize>> = Vec::new();
    for v in 0..n {
        if indices[v] != usize::MAX {
            continue;
        }
        let mut dfs: Vec<(usize, usize)> = vec![(v, 0)];
        indices[v] = idx;
        lowlinks[v] = idx;
        idx += 1;
        stack.push(v);
        on_stack[v] = true;
        while let Some((node, si)) = dfs.last_mut() {
            let nv = *node;
            if *si < adj[nv].len() {
                let w = adj[nv][*si];
                *si += 1;
                if indices[w] == usize::MAX {
                    indices[w] = idx;
                    lowlinks[w] = idx;
                    idx += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    dfs.push((w, 0));
                } else if on_stack[w] {
                    lowlinks[nv] = lowlinks[nv].min(indices[w]);
                }
            } else {
                if lowlinks[nv] == indices[nv] {
                    let mut scc = Vec::new();
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        scc.push(w);
                        if w == nv {
                            break;
                        }
                    }
                    result.push(scc);
                }
                let saved = lowlinks[nv];
                dfs.pop();
                if let Some((p, _)) = dfs.last() {
                    lowlinks[*p] = lowlinks[*p].min(saved);
                }
            }
        }
    }
    result
}

// Step 3: Universe parameter collection

#[must_use]
pub(crate) fn collect_universe_params(decls: &[SurfaceDecl]) -> Vec<UniverseParam> {
    decls
        .iter()
        .flat_map(|decl| {
            let dn = decl_name(decl).unwrap_or("<anonymous>");
            decl_universe_params(decl)
                .iter()
                .map(move |u| UniverseParam {
                    name: u.clone(),
                    decl_name: dn.to_string(),
                })
        })
        .collect()
}

// Step 4: Attribute validation

pub(crate) fn validate_attributes(decls: &[SurfaceDecl]) -> Result<usize, PreprocessError> {
    Ok(decls.iter().map(decl_attr_count).sum())
}

// Step 5: Namespace resolution

pub(crate) fn resolve_namespaces(
    decls: &[SurfaceDecl],
    opened: &[String],
    known: &HashSet<String>,
) -> (Vec<SurfaceDecl>, usize) {
    let mut count = 0;
    let out = decls
        .iter()
        .map(|d| resolve_decl(d, opened, known, &mut count))
        .collect();
    (out, count)
}

fn resolve_decl(
    decl: &SurfaceDecl,
    opened: &[String],
    known: &HashSet<String>,
    count: &mut usize,
) -> SurfaceDecl {
    match decl {
        SurfaceDecl::Def {
            span,
            name,
            universe_params,
            binders,
            ty,
            val,
            attrs,
            termination,
            modifiers,
            where_decls,
        } => SurfaceDecl::Def {
            span: *span,
            name: name.clone(),
            universe_params: universe_params.clone(),
            binders: binders.clone(),
            ty: ty
                .as_ref()
                .map(|t| Box::new(resolve_expr(t, opened, known, count))),
            val: Box::new(resolve_expr(val, opened, known, count)),
            attrs: attrs.clone(),
            termination: termination.clone(),
            modifiers: *modifiers,
            where_decls: where_decls.clone(),
        },
        SurfaceDecl::Theorem {
            span,
            name,
            universe_params,
            binders,
            ty,
            proof,
            attrs,
            termination,
            modifiers,
            where_decls,
        } => SurfaceDecl::Theorem {
            span: *span,
            name: name.clone(),
            universe_params: universe_params.clone(),
            binders: binders.clone(),
            ty: Box::new(resolve_expr(ty, opened, known, count)),
            proof: Box::new(resolve_expr(proof, opened, known, count)),
            attrs: attrs.clone(),
            termination: termination.clone(),
            modifiers: *modifiers,
            where_decls: where_decls.clone(),
        },
        _ => decl.clone(),
    }
}

fn resolve_expr(
    expr: &SurfaceExpr,
    opened: &[String],
    known: &HashSet<String>,
    count: &mut usize,
) -> SurfaceExpr {
    match expr {
        SurfaceExpr::Ident(span, name) => {
            if known.contains(name) || name.contains('.') {
                return expr.clone();
            }
            for ns in opened {
                let q = format!("{ns}.{name}");
                if known.contains(&q) {
                    *count += 1;
                    return SurfaceExpr::Ident(*span, q);
                }
            }
            expr.clone()
        }
        SurfaceExpr::App(span, func, args) => SurfaceExpr::App(
            *span,
            Box::new(resolve_expr(func, opened, known, count)),
            args.clone(),
        ),
        SurfaceExpr::Arrow(span, l, r) => SurfaceExpr::Arrow(
            *span,
            Box::new(resolve_expr(l, opened, known, count)),
            Box::new(resolve_expr(r, opened, known, count)),
        ),
        SurfaceExpr::Paren(span, inner) => {
            SurfaceExpr::Paren(*span, Box::new(resolve_expr(inner, opened, known, count)))
        }
        _ => expr.clone(),
    }
}

// Step 6: Import expansion

/// Expand `open Foo` declarations into opened namespace prefixes.
#[must_use]
pub(crate) fn expand_imports(decls: &[SurfaceDecl]) -> Vec<String> {
    decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Open { paths, .. } => Some(paths.iter().map(|p| p.path.join("."))),
            _ => None,
        })
        .flatten()
        .collect()
}

// Step 7: Syntax desugaring

pub(crate) fn desugar_decls(decls: &[SurfaceDecl]) -> (Vec<SurfaceDecl>, usize) {
    let mut count = 0;
    let result = decls
        .iter()
        .map(|d| match d {
            SurfaceDecl::Example {
                span,
                binders,
                ty,
                val,
            } => {
                count += 1;
                SurfaceDecl::Def {
                    span: *span,
                    name: format!("_example_{count}"),
                    universe_params: Vec::new(),
                    binders: binders.clone(),
                    ty: ty.clone(),
                    val: val.clone(),
                    attrs: Vec::new(),
                    termination: Default::default(),
                    modifiers: Default::default(),
                    where_decls: Vec::new(),
                }
            }
            _ => d.clone(),
        })
        .collect();
    (result, count)
}

// Step 8: Dependency ordering

/// Topologically sort declarations. Cycles are kept in original order.
pub(crate) fn order_by_deps(
    decls: &[SurfaceDecl],
) -> Result<(Vec<SurfaceDecl>, usize), PreprocessError> {
    let n = decls.len();
    if n <= 1 {
        return Ok((decls.to_vec(), 0));
    }
    let name_to_idx: HashMap<&str, usize> = decls
        .iter()
        .enumerate()
        .filter_map(|(i, d)| decl_name(d).map(|n| (n, i)))
        .collect();
    let mut in_deg = vec![0u32; n];
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, decl) in decls.iter().enumerate() {
        for r in collect_decl_refs(decl) {
            if let Some(&j) = name_to_idx.get(r.as_str()) {
                if j != i {
                    adj[j].push(i);
                    in_deg[i] += 1;
                }
            }
        }
    }
    let mut queue: VecDeque<usize> = (0..n).filter(|&i| in_deg[i] == 0).collect();
    let mut order = Vec::with_capacity(n);
    while let Some(node) = queue.pop_front() {
        order.push(node);
        for &s in &adj[node] {
            in_deg[s] -= 1;
            if in_deg[s] == 0 {
                queue.push_back(s);
            }
        }
    }
    if order.len() < n {
        let done: HashSet<usize> = order.iter().copied().collect();
        for i in 0..n {
            if !done.contains(&i) {
                order.push(i);
            }
        }
    }
    let reordered = order.iter().enumerate().filter(|(p, &o)| *p != o).count();
    Ok((order.iter().map(|&i| decls[i].clone()).collect(), reordered))
}

// Step 9: Full pipeline

/// Run the full preprocessing pipeline.
pub(crate) fn preprocess_pipeline(
    decls: &[SurfaceDecl],
    comments: &[&str],
    known_names: &HashSet<String>,
) -> Result<PreprocessResult, PreprocessError> {
    let mut stats = PreprocessStats {
        decls_preprocessed: decls.len(),
        ..Default::default()
    };
    let docstrings = extract_docstrings(comments, decls);
    stats.docstrings_extracted = docstrings.len();
    let mutual_groups = detect_mutual_groups(decls);
    stats.mutual_blocks_found = mutual_groups.len();
    let universe_params = collect_universe_params(decls);
    stats.universe_params_collected = universe_params.len();
    stats.attributes_validated = validate_attributes(decls)?;
    let opened = expand_imports(decls);
    stats.imports_expanded = opened.len();
    let (decls, resolved) = resolve_namespaces(decls, &opened, known_names);
    stats.names_resolved = resolved;
    let (decls, desugared) = desugar_decls(&decls);
    stats.desugared = desugared;
    let (decls, reordered) = order_by_deps(&decls)?;
    stats.reordered = reordered;
    Ok(PreprocessResult {
        decls,
        docstrings,
        mutual_groups,
        universe_params,
        stats,
    })
}
