// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Lane-agnostic blocking-weight frontier arithmetic** — the reusable core of
//! the Isabelle cascade-weight targeter, extracted so every import lane (Coq,
//! Lean, …) can rank its REJECTED items by how much downstream cascade each one
//! transitively gates.
//!
//! # What this computes
//!
//! Given a set of REJECTED items in a *topological order* (every rejected
//! dependency of an item appears before it) and a raw dependency lookup, over
//! the reject subgraph (rejected nodes; an edge `x → d` for every dep `d` of `x`
//! that is itself rejected):
//!
//! - A rejected item is a **PRIMARY** (a frontier gatekeeper) iff it has no
//!   rejected dependency — the sinks of the reject subgraph, the items a round
//!   can actually attack because everything they need already verifies.
//! - Each rejected item's **frontier set** is the set of primaries reachable
//!   from it through rejected-only edges — the primaries it *waits on*. A
//!   primary's own frontier set is exactly itself.
//! - **blocked(p)** = number of rejected items whose frontier set contains `p`
//!   (`p` included) — `p`'s cascade weight (the optimistic ceiling).
//! - **exclusive(p)** = number of rejected items whose frontier set is *exactly*
//!   `{p}` (`p` included) — `p`'s SOLE-blocked dependents, the guaranteed release
//!   when `p` is fixed.
//!
//! `exclusive(p) ≤ blocked(p)`, both count `p` itself.
//!
//! # Why generic
//!
//! The arithmetic is pure graph math over an opaque item id (`Id: Eq + Hash +
//! Clone`): Isabelle keys items by an `i64` proof-term serial; Coq keys them by
//! fully-qualified constant `String`. The Isabelle targeter
//! (`hol::isabelle_targets`) is the first adapter and delegates its inner loop
//! here with byte-identical results; the Coq adapter (`replay_infra::coq_targets`)
//! is the second.
//!
//! # Topological-order contract (forward-edge handling)
//!
//! The frontier pass builds each item's set from its dependencies' sets in one
//! ascending pass, so a dependency must be *fully built* before the item that
//! needs it — i.e. `order` must list rejected deps before their dependents. Any
//! edge `x → d` whose `d` appears at position `≥ x` (a forward reference or a
//! back-edge of a cycle) is DROPPED from the reject subgraph and tallied in
//! `forward_edges`, exactly as the Isabelle DAG-order pass drops `dep_serial ≥
//! referrer_serial`. Callers whose ids are not naturally topo-sortable can build
//! a suitable order with [`topo_order`].

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// A fixed-width bitset over the `P` primaries (word = 64 bits).
#[derive(Clone)]
struct PrimaryBits {
    words: Vec<u64>,
}

impl PrimaryBits {
    fn new(primaries: usize) -> Self {
        PrimaryBits {
            words: vec![0u64; primaries.div_ceil(64)],
        }
    }
    fn set(&mut self, idx: usize) {
        self.words[idx >> 6] |= 1u64 << (idx & 63);
    }
    fn or_from(&mut self, other: &PrimaryBits) {
        for (a, b) in self.words.iter_mut().zip(other.words.iter()) {
            *a |= *b;
        }
    }
    /// The single set bit's index iff exactly one bit is set.
    fn single(&self) -> Option<usize> {
        let mut found: Option<usize> = None;
        for (wi, &w) in self.words.iter().enumerate() {
            if w == 0 {
                continue;
            }
            if w.count_ones() != 1 || found.is_some() {
                return None;
            }
            found = Some((wi << 6) + w.trailing_zeros() as usize);
        }
        found
    }
    fn for_each_set<F: FnMut(usize)>(&self, mut f: F) {
        for (wi, &w) in self.words.iter().enumerate() {
            let mut bits = w;
            while bits != 0 {
                let b = bits.trailing_zeros() as usize;
                f((wi << 6) + b);
                bits &= bits - 1;
            }
        }
    }
}

/// One gatekeeper (primary) row: how much cascade it gates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrontierRow<Id> {
    /// The primary's id.
    pub id: Id,
    /// Cascade weight: rejected items whose frontier set includes this primary
    /// (this primary counted).
    pub blocked: usize,
    /// Sole-blocked dependents: rejected items whose frontier set is exactly
    /// this primary (this primary counted) — the guaranteed release.
    pub exclusive: usize,
}

/// The blocking-weight result over a reject subgraph. `rows` are in *bit order*
/// (each primary's order of first appearance in the input `order`), NOT ranked —
/// adapters rank by their own tie-break policy.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FrontierReport<Id> {
    /// Rejected items considered (`order.len()`).
    pub rejected: usize,
    /// Frontier primaries (rejected items with no rejected dependency).
    pub primaries: usize,
    /// Gated cascade (`rejected - primaries`).
    pub cascade: usize,
    /// Edges dropped as forward/back references (dep at position `≥` referrer).
    pub forward_edges: usize,
    /// Per-primary `(id, blocked, exclusive)` rows, in bit order.
    pub rows: Vec<FrontierRow<Id>>,
}

/// Compute the blocking-weight frontier report over the reject subgraph.
///
/// `order` lists every rejected item's id in a topological order (each rejected
/// dependency before its dependents; see the module-level contract). `raw_deps`
/// maps an id to its raw dependency ids — a superset that may include accepted,
/// absent, duplicated, or forward-referenced ids; the function filters to the
/// in-`order` rejected deps and drops forward references.
///
/// Ids in `order` are assumed distinct; a duplicated id keeps its FIRST position
/// (`HashMap` insertion), matching the Isabelle serial-dedup behavior.
#[must_use]
pub fn frontier_weights<'a, Id, D>(order: &[Id], raw_deps: D) -> FrontierReport<Id>
where
    Id: Eq + Hash + Clone + 'a,
    D: Fn(&Id) -> &'a [Id],
{
    // Position index of each rejected id. First occurrence wins (dedup).
    let mut rej_idx: HashMap<&Id, usize> = HashMap::with_capacity(order.len());
    for (i, s) in order.iter().enumerate() {
        rej_idx.entry(s).or_insert(i);
    }

    // Reject-subgraph edges (deduped, filtered) + primary flags. A dep at
    // position ≥ the referrer is a forward/back edge: dropped and tallied.
    let mut rej_deps: Vec<Vec<usize>> = vec![Vec::new(); order.len()];
    let mut is_primary: Vec<bool> = vec![true; order.len()];
    let mut forward_edges = 0usize;
    for (i, s) in order.iter().enumerate() {
        let mut seen: HashSet<usize> = HashSet::new();
        for d in raw_deps(s) {
            let Some(&di) = rej_idx.get(d) else {
                continue; // dep accepted or absent — does not gate.
            };
            if di >= i {
                forward_edges += 1;
                continue; // forward ref / cycle back-edge: not a predecessor.
            }
            if seen.insert(di) {
                rej_deps[i].push(di);
                is_primary[i] = false;
            }
        }
    }

    // Assign each primary a bit index (bit order = ascending position).
    let mut primary_bit: Vec<Option<usize>> = vec![None; order.len()];
    let mut primaries: Vec<usize> = Vec::new();
    for (i, &prim) in is_primary.iter().enumerate() {
        if prim {
            primary_bit[i] = Some(primaries.len());
            primaries.push(i);
        }
    }
    let p = primaries.len();

    // Ascending pass: frontier set = union of rejected deps' sets, plus self
    // when primary. Deps are at lower positions, hence already built.
    let mut blocked: Vec<usize> = vec![0; p];
    let mut exclusive: Vec<usize> = vec![0; p];
    let mut sets: Vec<PrimaryBits> = Vec::with_capacity(order.len());
    for i in 0..order.len() {
        let mut bits = PrimaryBits::new(p);
        if let Some(pb) = primary_bit[i] {
            bits.set(pb);
        } else {
            for &di in &rej_deps[i] {
                bits.or_from(&sets[di]);
            }
        }
        bits.for_each_set(|pb| blocked[pb] += 1);
        if let Some(pb) = bits.single() {
            exclusive[pb] += 1;
        }
        sets.push(bits);
    }

    let rows: Vec<FrontierRow<Id>> = primaries
        .iter()
        .enumerate()
        .map(|(bit, &ri)| FrontierRow {
            id: order[ri].clone(),
            blocked: blocked[bit],
            exclusive: exclusive[bit],
        })
        .collect();

    FrontierReport {
        rejected: order.len(),
        primaries: p,
        cascade: order.len() - p,
        forward_edges,
        rows,
    }
}

/// Build a topological order (dependencies before dependents) over `items`
/// using their `raw_deps`, so [`frontier_weights`] can consume ids whose natural
/// ordering is not itself a topo order (e.g. Coq's string names).
///
/// Only edges to ids that are also in `items` are followed. Cycles are tolerated:
/// a node on a cycle is emitted after the acyclic part of its dependencies, and
/// the residual back-edge is then dropped by [`frontier_weights`]'s position
/// check (and tallied there as a forward edge). Iterative DFS post-order; the
/// input `items` order breaks ties deterministically.
#[must_use]
pub fn topo_order<'a, Id, D>(items: &[Id], raw_deps: D) -> Vec<Id>
where
    Id: Eq + Hash + Clone + 'a,
    D: Fn(&Id) -> &'a [Id],
{
    let in_set: HashSet<&Id> = items.iter().collect();
    let mut visited: HashSet<Id> = HashSet::with_capacity(items.len());
    let mut on_stack: HashSet<Id> = HashSet::new();
    let mut out: Vec<Id> = Vec::with_capacity(items.len());

    // Iterative DFS: stack of (node, next-dep-cursor).
    for root in items {
        if visited.contains(root) {
            continue;
        }
        let mut stack: Vec<(Id, usize)> = vec![(root.clone(), 0)];
        on_stack.insert(root.clone());
        while let Some((node, cursor)) = stack.last().cloned() {
            let deps = raw_deps(&node);
            let mut advanced = false;
            let mut idx = cursor;
            while idx < deps.len() {
                let d = &deps[idx];
                idx += 1;
                if in_set.contains(d) && !visited.contains(d) && !on_stack.contains(d) {
                    // Descend into the unvisited dependency.
                    if let Some(top) = stack.last_mut() {
                        top.1 = idx;
                    }
                    stack.push((d.clone(), 0));
                    on_stack.insert(d.clone());
                    advanced = true;
                    break;
                }
            }
            if !advanced {
                // All deps explored (or on-stack cycle back-edges) — emit.
                stack.pop();
                on_stack.remove(&node);
                if visited.insert(node.clone()) {
                    out.push(node);
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn deps_fn<'m>(map: &'m HashMap<i64, Vec<i64>>) -> impl Fn(&i64) -> &'m [i64] + 'm {
        move |id| map.get(id).map(Vec::as_slice).unwrap_or(&[])
    }

    /// The canonical hand graph from the Isabelle targeter's own gate:
    /// rejected order 10,15,20,30,40 with deps A=10(→acc), E=15(→acc),
    /// B=20(→10), C=30(→20), D=40(→10,15). Frontier sets: A→{A}, E→{E}, B→{A},
    /// C→{A}, D→{A,E}. blocked(A)=4 excl(A)=3; blocked(E)=2 excl(E)=1.
    #[test]
    fn test_frontier_weights_canonical() {
        let mut deps: HashMap<i64, Vec<i64>> = HashMap::new();
        deps.insert(10, vec![1, 2]); // accepted deps → primary
        deps.insert(15, vec![1]);
        deps.insert(20, vec![10]);
        deps.insert(30, vec![20]);
        deps.insert(40, vec![10, 15]);
        let order = vec![10, 15, 20, 30, 40];
        let r = frontier_weights(&order, deps_fn(&deps));
        assert_eq!(r.rejected, 5);
        assert_eq!(r.primaries, 2);
        assert_eq!(r.cascade, 3);
        let a = r.rows.iter().find(|x| x.id == 10).expect("A");
        assert_eq!((a.blocked, a.exclusive), (4, 3));
        let e = r.rows.iter().find(|x| x.id == 15).expect("E");
        assert_eq!((e.blocked, e.exclusive), (2, 1));
    }

    /// A forward reference (dep at position ≥ referrer) is dropped + tallied.
    #[test]
    fn test_frontier_weights_forward_ref_dropped() {
        let mut deps: HashMap<i64, Vec<i64>> = HashMap::new();
        deps.insert(10, vec![1, 20]); // 20 is a forward ref in this order
        deps.insert(20, vec![1]);
        let order = vec![10, 20];
        let r = frontier_weights(&order, deps_fn(&deps));
        assert_eq!(r.forward_edges, 1);
        assert_eq!(
            r.primaries, 2,
            "both 10 and 20 are primaries once forward dropped"
        );
        let ten = r.rows.iter().find(|x| x.id == 10).expect("10");
        assert_eq!((ten.blocked, ten.exclusive), (1, 1));
    }

    /// `topo_order` puts a dependency before its dependent even when the id sort
    /// order would not, so `frontier_weights` sees zero forward edges.
    #[test]
    fn test_topo_order_string_ids() {
        // "a" depends on "z"; the natural sort would place "a" first (wrong).
        let mut deps: HashMap<String, Vec<String>> = HashMap::new();
        deps.insert("a".into(), vec!["z".into()]);
        deps.insert("z".into(), vec![]);
        let items = vec!["a".to_string(), "z".to_string()];
        let dfn = |id: &String| deps.get(id).map(Vec::as_slice).unwrap_or(&[]);
        let order = topo_order(&items, dfn);
        let za = order.iter().position(|x| x == "z").unwrap();
        let aa = order.iter().position(|x| x == "a").unwrap();
        assert!(za < aa, "dependency z must precede dependent a: {order:?}");

        let r = frontier_weights(&order, dfn);
        assert_eq!(r.forward_edges, 0, "topo order eliminates forward edges");
        assert_eq!(r.primaries, 1, "only z is a primary (a depends on z)");
        let z = r.rows.iter().find(|x| x.id == "z").expect("z");
        assert_eq!((z.blocked, z.exclusive), (2, 2), "z solely gates {{z, a}}");
    }

    /// A cycle is tolerated: one back-edge is dropped, no panic.
    #[test]
    fn test_topo_order_cycle_tolerated() {
        let mut deps: HashMap<String, Vec<String>> = HashMap::new();
        deps.insert("p".into(), vec!["q".into()]);
        deps.insert("q".into(), vec!["p".into()]);
        let items = vec!["p".to_string(), "q".to_string()];
        let dfn = |id: &String| deps.get(id).map(Vec::as_slice).unwrap_or(&[]);
        let order = topo_order(&items, dfn);
        assert_eq!(order.len(), 2, "both nodes emitted exactly once");
        let r = frontier_weights(&order, dfn);
        assert_eq!(r.forward_edges, 1, "one back-edge dropped");
        assert_eq!(r.rejected, 2);
    }
}
