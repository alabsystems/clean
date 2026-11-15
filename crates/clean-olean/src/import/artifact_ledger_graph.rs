// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The dependency graph rule 3 of the artifact ledger walks
//! (`artifact_ledger.rs`): the constants a declaration refers to, and the
//! first strongly connected component that is a cycle through a safe
//! declaration.

use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use hashbrown::HashSet;

/// The constants a registered declaration refers to: its type and, for a
/// definition, theorem or opaque, its value. A recursor's ι-rules are not
/// followed: they refer to the recursor itself by construction. `shared`
/// holds the sub-terms already walked for this declaration: imported terms
/// are hash-consed DAGs, and a tree walk of one can be exponential.
pub(super) fn references(
    env: &Environment,
    name: &Name,
    shared: &mut HashSet<*const Expr>,
    out: &mut std::collections::HashSet<Name>,
) {
    out.clear();
    if let Some(info) = env.get_const(name) {
        // A sub-term walked for an earlier declaration may hold a constant
        // this one refers to as well, so the memo is per declaration.
        shared.clear();
        walk_constants(&info.type_, shared, out);
        if let Some(value) = &info.value {
            walk_constants(value, shared, out);
        }
    }
}

/// Every constant under `root`, each shared sub-term visited once.
pub(super) fn walk_constants(
    root: &Expr,
    seen: &mut HashSet<*const Expr>,
    out: &mut std::collections::HashSet<Name>,
) {
    let mut stack: Vec<&Expr> = vec![root];
    while let Some(e) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(e)) {
            continue;
        }
        match e.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.clone());
            }
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
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
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            // The extension kinds: the kernel's own complete walk.
            _ => e.collect_constants_into(out),
        }
    }
}

/// A strongly connected component with a safe member that depends on
/// itself: two or more members, or one with an edge to itself. Iterative
/// Tarjan, so a long dependency chain cannot exhaust the stack.
pub(super) fn first_cycle(
    env: &Environment,
    nodes: &[Name],
    edges: &[Vec<usize>],
) -> Option<Vec<Name>> {
    const UNVISITED: usize = usize::MAX;
    let n = nodes.len();
    let mut index = vec![UNVISITED; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next = 0usize;
    for root in 0..n {
        if index[root] != UNVISITED {
            continue;
        }
        // (node, next child to visit)
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(top) = work.len().checked_sub(1) {
            let (v, child) = work[top];
            if let Some(&w) = edges[v].get(child) {
                work[top].1 += 1;
                if index[w] == UNVISITED {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == index[v] {
                // Pop the component: everything above `v`, and `v` itself
                // (Tarjan's stack holds `v` while `low[v] == index[v]`).
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                let cyclic = component.len() > 1 || edges[v].contains(&v);
                // Lean admits a cycle of `unsafe` declarations (and only
                // those): a safe declaration may not even mention one.
                if cyclic && component.iter().any(|&m| !env.is_unsafe(&nodes[m])) {
                    let mut names: Vec<Name> =
                        component.iter().map(|&m| nodes[m].clone()).collect();
                    names.sort_by_key(ToString::to_string);
                    return Some(names);
                }
            }
        }
    }
    None
}
