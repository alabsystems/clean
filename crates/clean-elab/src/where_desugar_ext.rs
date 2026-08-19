// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended where-clause desugaring with dependency ordering and cycle detection.
//!
//! Extends [`crate::where_desugar`] with: free-ident collection, dependency
//! graph construction, topological sorting, cycle detection, and mutual
//! recursion grouping (SCCs). [`desugar_where_from_parsed_ordered`] is the
//! production entry point for `def`/`theorem` `where` blocks
//! (`infer/elab_decl_value.rs`).
//!
//! Reference: Lean 4 `src/Lean/Parser/Term.lean:701-703` (`whereDecls`),
//! `src/Lean/Elab/Binders.lean:472-476` (`expandWhereDecls` — `where` becomes
//! a leading `let rec` group), `src/Lean/Elab/LetRec.lean:87/110/140`
//! (mutually visible group members, lifted to auxiliary definitions),
//! `src/Lean/Elab/MutualDef.lean:332-397`.

use std::collections::{HashMap, HashSet, VecDeque};

use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, WhereLocalDef};

use crate::where_desugar::WhereClause;

/// Errors arising from where-clause dependency analysis.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum WhereDesugarError {
    /// A cycle exists among where-clause definitions that cannot be resolved
    /// as mutual recursion.
    #[error(
        "cyclic dependency among where-clause definitions: {}",
        names.join(" -> ")
    )]
    CyclicDependency {
        /// Names forming the cycle, in dependency order.
        names: Vec<String>,
        /// Span of the first clause in the cycle, for error reporting.
        span: Span,
    },

    /// Duplicate where-clause name.
    #[error("duplicate where-clause definition: `{name}`")]
    DuplicateName {
        /// The duplicated name.
        name: String,
        /// Span of the second (duplicate) definition.
        span: Span,
    },
}

/// Collect free identifier names from a `SurfaceExpr` (excluding locally bound names).
/// Conservative approximation — caller intersects with where-clause name set.
#[must_use]
pub(crate) fn collect_free_idents(expr: &SurfaceExpr) -> HashSet<String> {
    collect_free_idents_checked(expr).0
}

/// Whether [`collect_free_idents`] could analyze `expr` COMPLETELY.
///
/// The traversal's final arm silently ignores constructs it does not model, so
/// an identifier occurring only inside one is never reported. Undercounting is
/// sound for dependency analysis; it is NOT sound for `used_section_binders`,
/// where a missed identifier drops a section `variable` and the declaration
/// registers with the WRONG ARITY (measured: `p` used only as a `Proj`
/// receiver, `TooManyArguments` on every later application — r90's
/// `sectvar_transitive_incl`).
///
/// Callers that need completeness consult this and fall back to including
/// everything.
#[must_use]
pub(crate) fn free_idents_are_complete(expr: &SurfaceExpr) -> bool {
    collect_free_idents_checked(expr).1
}

/// The single traversal: free identifiers, plus whether it saw everything.
///
/// ONE match, deliberately. Completeness used to be computed by a second,
/// parallel match that had to be kept in step by hand — and a drift in either
/// direction is silent: teach only the collector and the fallback still fires
/// (losing the Lean-parity win); teach only the predicate and the arity bug
/// returns. Adding a variant here now updates both by construction.
#[must_use]
pub(crate) fn collect_free_idents_checked(expr: &SurfaceExpr) -> (HashSet<String>, bool) {
    let mut free = HashSet::new();
    let mut bound: Vec<HashSet<String>> = vec![HashSet::new()];
    let mut complete = true;
    collect_free_idents_inner(expr, &mut free, &mut bound, &mut complete);
    (free, complete)
}

fn collect_free_idents_inner(
    expr: &SurfaceExpr,
    free: &mut HashSet<String>,
    bound: &mut Vec<HashSet<String>>,
    complete: &mut bool,
) {
    match expr {
        SurfaceExpr::Ident(_, name) => {
            let is_bound = bound.iter().any(|scope| scope.contains(name.as_str()));
            if !is_bound {
                free.insert(name.clone());
            }
        }

        SurfaceExpr::Lambda(_, binders, body)
        | SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            // Collect from binder types before pushing scope
            for b in binders {
                if let Some(ty) = &b.ty {
                    collect_free_idents_inner(ty, free, bound, complete);
                }
                if let Some(def) = &b.default {
                    collect_free_idents_inner(def, free, bound, complete);
                }
            }
            let mut scope = HashSet::new();
            for b in binders {
                if b.name != "_" {
                    scope.insert(b.name.clone());
                }
            }
            bound.push(scope);
            collect_free_idents_inner(body, free, bound, complete);
            bound.pop();
        }

        SurfaceExpr::Pi(_, binders, body) => {
            for b in binders {
                if let Some(ty) = &b.ty {
                    collect_free_idents_inner(ty, free, bound, complete);
                }
            }
            let mut scope = HashSet::new();
            for b in binders {
                if b.name != "_" {
                    scope.insert(b.name.clone());
                }
            }
            bound.push(scope);
            collect_free_idents_inner(body, free, bound, complete);
            bound.pop();
        }

        SurfaceExpr::Let(_, binder, val, body) => {
            if let Some(ty) = &binder.ty {
                collect_free_idents_inner(ty, free, bound, complete);
            }
            collect_free_idents_inner(val, free, bound, complete);
            let mut scope = HashSet::new();
            if binder.name != "_" {
                scope.insert(binder.name.clone());
            }
            bound.push(scope);
            collect_free_idents_inner(body, free, bound, complete);
            bound.pop();
        }

        SurfaceExpr::LetRec(_, binder, val, body) => {
            // In let rec, the name is in scope in both val and body.
            let mut scope = HashSet::new();
            if binder.name != "_" {
                scope.insert(binder.name.clone());
            }
            bound.push(scope);
            if let Some(ty) = &binder.ty {
                collect_free_idents_inner(ty, free, bound, complete);
            }
            collect_free_idents_inner(val, free, bound, complete);
            collect_free_idents_inner(body, free, bound, complete);
            bound.pop();
        }

        SurfaceExpr::App(_, func, args) => {
            collect_free_idents_inner(func, free, bound, complete);
            for arg in args {
                collect_free_idents_inner(&arg.expr, free, bound, complete);
            }
        }

        SurfaceExpr::Arrow(_, lhs, rhs) => {
            collect_free_idents_inner(lhs, free, bound, complete);
            collect_free_idents_inner(rhs, free, bound, complete);
        }

        SurfaceExpr::Ascription(_, e, ty) => {
            collect_free_idents_inner(e, free, bound, complete);
            collect_free_idents_inner(ty, free, bound, complete);
        }

        SurfaceExpr::If(_, cond, then_br, else_br) => {
            collect_free_idents_inner(cond, free, bound, complete);
            collect_free_idents_inner(then_br, free, bound, complete);
            collect_free_idents_inner(else_br, free, bound, complete);
        }

        SurfaceExpr::Match(_, hyp, scrutinee, arms) => {
            collect_free_idents_inner(scrutinee, free, bound, complete);
            for arm in arms {
                let mut scope = HashSet::new();
                // The annotated discriminant (`match h : e with`) binds `h`
                // inside every arm body.
                if let Some(h) = hyp {
                    scope.insert(h.clone());
                }
                collect_pattern_bound_names(&arm.pattern, &mut scope);
                bound.push(scope);
                collect_free_idents_inner(&arm.body, free, bound, complete);
                bound.pop();
            }
        }

        SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::OutParam(_, inner)
        | SurfaceExpr::SemiOutParam(_, inner) => {
            collect_free_idents_inner(inner, free, bound, complete);
        }

        // Leaves: no sub-expressions to traverse
        SurfaceExpr::Hole(_)
        | SurfaceExpr::Lit(_, _)
        | SurfaceExpr::Universe(_, _)
        | SurfaceExpr::SyntheticSorry(_) => {}

        // Transparent wrappers: the identifiers are in the sub-term.
        //
        // `Proj` is the one that mattered. `p.2` is `Proj(_, p, _)`, and leaving
        // it to the catch-all meant `p` was never seen — which dropped the
        // section variable and gave the declaration the wrong arity (r90's
        // `sectvar_transitive_incl`, `TooManyArguments`). The others here are
        // the same shape: a boxed sub-term whose free identifiers are the
        // node's.
        SurfaceExpr::Proj(_, inner, _)
        | SurfaceExpr::Explicit(_, inner)
        | SurfaceExpr::UniverseInst(_, inner, _) => {
            collect_free_idents_inner(inner, free, bound, complete);
        }
        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            if let Some(t) = struct_type {
                collect_free_idents_inner(t, free, bound, complete);
            }
            if let Some(b) = base {
                collect_free_idents_inner(b, free, bound, complete);
            }
            for f in fields {
                collect_free_idents_inner(&f.val, free, bound, complete);
            }
        }
        SurfaceExpr::OpenIn { body, .. } => {
            collect_free_idents_inner(body, free, bound, complete);
        }
        // Everything still unmodelled (`Do`, `ByTactic`, `CalcBlock`,
        // `IfLet`, `LetPattern`, quotations, `InterpolatedStr`, ...) is
        // reported as INCOMPLETE rather than silently undercounted. Callers
        // that need completeness fall back; callers doing dependency analysis
        // ignore the flag, exactly as before.
        _ => *complete = false,
    }
}

/// Collect the names bound by a match pattern into `scope`.
///
/// `Wildcard`/`Ellipsis`/`Lit` bind nothing; `Inaccessible`/`QPattern` hold
/// expressions, not binders. `_` is never recorded.
fn collect_pattern_bound_names(
    pattern: &clean_parser::SurfacePattern,
    scope: &mut HashSet<String>,
) {
    use clean_parser::SurfacePattern;
    match pattern {
        SurfacePattern::Var(name) => {
            if name != "_" {
                scope.insert(name.clone());
            }
        }
        SurfacePattern::Ctor(_, args) => {
            for arg in args {
                collect_pattern_bound_names(arg, scope);
            }
        }
        SurfacePattern::NumeralAdd(inner, _) => collect_pattern_bound_names(inner, scope),
        SurfacePattern::As(name, inner) => {
            if name != "_" {
                scope.insert(name.clone());
            }
            collect_pattern_bound_names(inner, scope);
        }
        SurfacePattern::Or(lhs, rhs) => {
            collect_pattern_bound_names(lhs, scope);
            collect_pattern_bound_names(rhs, scope);
        }
        SurfacePattern::Wildcard
        | SurfacePattern::Inaccessible(_)
        | SurfacePattern::Lit(_)
        | SurfacePattern::QPattern(_)
        | SurfacePattern::Ellipsis => {}
    }
}

/// Collect free identifiers from a where-clause's body and type annotation,
/// excluding parameters bound by the clause itself.
#[must_use]
fn clause_free_idents(clause: &WhereClause) -> HashSet<String> {
    let mut free = HashSet::new();
    let mut bound: Vec<HashSet<String>> = vec![HashSet::new()];

    // This walk feeds WHERE-CLAUSE DEPENDENCY analysis, which the collector's
    // contract explicitly serves: missing an identifier can only drop a
    // dependency edge, never invent one. Completeness is discarded here on
    // purpose — unlike `used_section_binders`, where an undercount silently
    // changes a declaration's arity.
    let mut dep_analysis_tolerates_undercount = true;

    // Parameters are bound in the body and return type
    let mut param_scope = HashSet::new();
    for b in &clause.params {
        if b.name != "_" {
            param_scope.insert(b.name.clone());
        }
        // But parameter types can reference other clauses
        if let Some(ty) = &b.ty {
            collect_free_idents_inner(
                ty,
                &mut free,
                &mut bound,
                &mut dep_analysis_tolerates_undercount,
            );
        }
    }

    bound.push(param_scope);

    // Collect from body
    collect_free_idents_inner(
        &clause.body,
        &mut free,
        &mut bound,
        &mut dep_analysis_tolerates_undercount,
    );

    // Collect from return type
    if let Some(ret) = &clause.return_type {
        collect_free_idents_inner(
            ret,
            &mut free,
            &mut bound,
            &mut dep_analysis_tolerates_undercount,
        );
    }

    bound.pop();
    free
}

/// Result of dependency analysis on where-clauses.
#[derive(Debug)]
pub(crate) struct WhereDepAnalysis {
    /// Indices into the original clause list, in dependency-sorted order.
    /// Dependencies appear before their dependents.
    pub(crate) sorted_indices: Vec<usize>,

    /// Groups of mutually recursive clause indices (SCCs with size > 1).
    /// Each group should be desugared as a single `let rec` block.
    pub(crate) mutual_groups: Vec<Vec<usize>>,
}

/// Analyze dependencies among where-clauses and produce a topological ordering.
/// Returns `DuplicateName` on duplicate clause names. Mutual recursion groups
/// are detected via SCC and returned in `mutual_groups`.
pub(crate) fn analyze_where_deps(
    clauses: &[WhereClause],
) -> Result<WhereDepAnalysis, WhereDesugarError> {
    if clauses.is_empty() {
        return Ok(WhereDepAnalysis {
            sorted_indices: Vec::new(),
            mutual_groups: Vec::new(),
        });
    }

    // Check for duplicate names
    let mut seen_names: HashMap<&str, usize> = HashMap::new();
    for (i, clause) in clauses.iter().enumerate() {
        if let Some(&prev_idx) = seen_names.get(clause.name.as_str()) {
            let _ = prev_idx; // suppress unused warning
            return Err(WhereDesugarError::DuplicateName {
                name: clause.name.clone(),
                span: clause.span,
            });
        }
        seen_names.insert(&clause.name, i);
    }

    // Build name → index mapping
    let name_to_idx: HashMap<&str, usize> = clauses
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.as_str(), i))
        .collect();

    let num_nodes = clauses.len();

    // Build adjacency list: edges[i] = set of clause indices that clause i depends on
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); num_nodes];
    for (i, clause) in clauses.iter().enumerate() {
        let free = clause_free_idents(clause);
        for ident in &free {
            if let Some(&dep_idx) = name_to_idx.get(ident.as_str()) {
                if dep_idx != i {
                    edges[i].push(dep_idx);
                }
            }
        }
        // Deduplicate
        edges[i].sort_unstable();
        edges[i].dedup();
    }

    // Compute SCCs using iterative Tarjan's
    let sccs = tarjan_sccs(&edges, num_nodes);
    let mutual_groups: Vec<Vec<usize>> = sccs.iter().filter(|scc| scc.len() > 1).cloned().collect();

    // Topological sort on the SCC-condensed DAG
    // Map each node to its SCC index
    let mut node_to_scc = vec![0usize; num_nodes];
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for &node in scc {
            node_to_scc[node] = scc_idx;
        }
    }

    let num_sccs = sccs.len();
    let mut scc_edges: Vec<HashSet<usize>> = vec![HashSet::new(); num_sccs];
    for (from, deps) in edges.iter().enumerate() {
        let from_scc = node_to_scc[from];
        for &to in deps {
            let to_scc = node_to_scc[to];
            if from_scc != to_scc {
                scc_edges[to_scc].insert(from_scc);
            }
        }
    }

    // Kahn's algorithm on the condensed DAG
    let mut in_degree = vec![0u32; num_sccs];
    for deps in &scc_edges {
        for &to in deps {
            in_degree[to] += 1;
        }
    }

    let mut queue: VecDeque<usize> = (0..num_sccs).filter(|&i| in_degree[i] == 0).collect();
    let mut scc_order = Vec::with_capacity(num_sccs);

    while let Some(scc_idx) = queue.pop_front() {
        scc_order.push(scc_idx);
        for &dep_scc in &scc_edges[scc_idx] {
            in_degree[dep_scc] -= 1;
            if in_degree[dep_scc] == 0 {
                queue.push_back(dep_scc);
            }
        }
    }

    // Expand SCC order back to node indices
    let mut sorted_indices = Vec::with_capacity(num_nodes);
    for &scc_idx in &scc_order {
        let mut scc_nodes = sccs[scc_idx].clone();
        // Within an SCC, preserve original order for stability
        scc_nodes.sort_unstable();
        sorted_indices.extend(scc_nodes);
    }

    Ok(WhereDepAnalysis {
        sorted_indices,
        mutual_groups,
    })
}

/// Iterative Tarjan's SCC algorithm. Returns SCCs in reverse topological order.
fn tarjan_sccs(adj: &[Vec<usize>], num_nodes: usize) -> Vec<Vec<usize>> {
    let mut index_counter: usize = 0;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; num_nodes];
    let mut indices = vec![usize::MAX; num_nodes];
    let mut lowlinks = vec![usize::MAX; num_nodes];
    let mut result: Vec<Vec<usize>> = Vec::new();

    for v in 0..num_nodes {
        if indices[v] != usize::MAX {
            continue;
        }

        let mut dfs_stack: Vec<(usize, usize)> = vec![(v, 0)];
        indices[v] = index_counter;
        lowlinks[v] = index_counter;
        index_counter += 1;
        stack.push(v);
        on_stack[v] = true;

        while let Some(&mut (node, ref mut succ_idx)) = dfs_stack.last_mut() {
            if *succ_idx < adj[node].len() {
                let w = adj[node][*succ_idx];
                *succ_idx += 1;

                if indices[w] == usize::MAX {
                    indices[w] = index_counter;
                    lowlinks[w] = index_counter;
                    index_counter += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    dfs_stack.push((w, 0));
                } else if on_stack[w] {
                    lowlinks[node] = lowlinks[node].min(indices[w]);
                }
            } else {
                if lowlinks[node] == indices[node] {
                    let mut scc = Vec::new();
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        scc.push(w);
                        if w == node {
                            break;
                        }
                    }
                    result.push(scc);
                }

                dfs_stack.pop();
                if let Some(&mut (parent, _)) = dfs_stack.last_mut() {
                    lowlinks[parent] = lowlinks[parent].min(lowlinks[node]);
                }
            }
        }
    }

    result
}

/// Desugar where-clauses with dependency-aware ordering.
///
/// Validates, topologically sorts, and wraps clauses as nested `let rec`.
/// Returns `WhereDesugarError` on duplicate names or cycles.
///
/// Topological ordering gives Lean-equivalent scoping for acyclic groups: in
/// Lean, all `where` decls form ONE `let rec` group whose names are mutually
/// visible (`Lean/Elab/Binders.lean:475` emits `let rec $decls,*`;
/// `Lean/Elab/LetRec.lean:87 withAuxLocalDecls` puts every group member in
/// scope for every value). Clean nests one `LetRec` per clause, so a clause
/// only sees the clauses wrapped outside it — reordering dependencies outward
/// reproduces Lean's visibility whenever the dependency graph is acyclic.
/// Genuinely mutual groups (cycles) cannot be expressed by nesting and are
/// REJECTED LOUD via [`WhereDesugarError::CyclicDependency`] — never lowered
/// to a shape that would elaborate wrong or land on a placeholder.
pub(crate) fn desugar_where_ordered(
    body: SurfaceExpr,
    clauses: &[WhereClause],
) -> Result<SurfaceExpr, WhereDesugarError> {
    if clauses.is_empty() {
        return Ok(body);
    }

    let analysis = analyze_where_deps(clauses)?;

    // Mutual recursion across where-clauses is descoped: fail loud. (A
    // clause referencing only ITSELF is not in any mutual group; single
    // self-recursion is handled downstream by the `let rec` structural lift.)
    if let Some(group) = analysis.mutual_groups.first() {
        let mut names: Vec<String> = group.iter().map(|&i| clauses[i].name.clone()).collect();
        let span = group.first().map_or_else(Span::dummy, |&i| clauses[i].span);
        if let Some(first) = names.first().cloned() {
            names.push(first); // display as `a -> b -> a`
        }
        return Err(WhereDesugarError::CyclicDependency { names, span });
    }

    // Reorder clauses according to topological sort
    let reordered: Vec<&WhereClause> = analysis
        .sorted_indices
        .iter()
        .map(|&i| &clauses[i])
        .collect();

    // Wrap from last (innermost) to first (outermost)
    let result = reordered
        .iter()
        .rev()
        .fold(body, |inner, clause| build_let_rec(clause, inner));

    Ok(result)
}

/// Desugar parsed where-definitions with dependency ordering.
///
/// Entry point for the elaborator. Converts parser `WhereLocalDef` types
/// and delegates to [`desugar_where_ordered`].
///
/// # Errors
///
/// Returns `WhereDesugarError` on duplicate names or cycles.
pub(crate) fn desugar_where_from_parsed_ordered(
    body: &SurfaceExpr,
    where_defs: &[WhereLocalDef],
) -> Result<SurfaceExpr, WhereDesugarError> {
    if where_defs.is_empty() {
        return Ok(body.clone());
    }

    let clauses: Vec<WhereClause> = where_defs
        .iter()
        .map(|def| WhereClause {
            name: def.name.clone(),
            params: def.binders.clone(),
            return_type: def.ret_ty.as_deref().cloned(),
            body: def.body.clone(),
            span: def.span,
        })
        .collect();

    desugar_where_ordered(body.clone(), &clauses)
}

/// Build a `LetRec` node from a single where-clause wrapping an inner body.
///
/// Shape contract with `elab_let_rec` (`infer/elab_core.rs`):
/// - `val` is `fun params => (body : ret_ty)` — the return-type annotation
///   rides INSIDE the lambda as an ascription, because the recursive lift
///   (`try_elab_let_rec_lifted`) peels the lambda binders and reads the
///   helper's return type from that ascription. Putting only the full
///   `params → ret_ty` Pi on the binder made the lift mistake the FULL
///   function type for the RETURN type (the pre-fix `where`-recursion bug).
/// - `binder.ty` is the full `params → ret_ty` Pi when a return type is
///   ascribed (used by the plain-`let` lowering of non-recursive helpers),
///   and `None` when the clause has no annotation, so both lowerings infer.
///
/// This mirrors Lean, where a `where` decl is a `letRecDecl` whose optional
/// type ascription is attached per-decl (`Lean/Parser/Term.lean:701-703
/// whereDecls`, `Lean/Elab/Binders.lean:472-476 expandWhereDecls`).
pub(crate) fn build_let_rec(clause: &WhereClause, inner_body: SurfaceExpr) -> SurfaceExpr {
    let span = clause.span;

    let ascribed_body = match &clause.return_type {
        Some(ret) => {
            SurfaceExpr::Ascription(span, Box::new(clause.body.clone()), Box::new(ret.clone()))
        }
        None => clause.body.clone(),
    };

    let val = if clause.params.is_empty() {
        ascribed_body
    } else {
        SurfaceExpr::Lambda(span, clause.params.clone(), Box::new(ascribed_body))
    };

    let binder_ty = clause.return_type.as_ref().map(|ret| {
        if clause.params.is_empty() {
            Box::new(ret.clone())
        } else {
            Box::new(SurfaceExpr::Pi(
                span,
                clause.params.clone(),
                Box::new(ret.clone()),
            ))
        }
    });

    let binder = SurfaceBinder {
        span,
        name: clause.name.clone(),
        ty: binder_ty,
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };

    SurfaceExpr::LetRec(span, binder, Box::new(val), Box::new(inner_body))
}

#[cfg(test)]
#[path = "where_desugar_ext_tests.rs"]
mod tests;
