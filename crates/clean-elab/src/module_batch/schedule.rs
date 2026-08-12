// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 5 — classifying what could not be scheduled.
//!
//! Two graphs, because a signature cycle and a body cycle are different
//! failures:
//!
//! * **`G_sig`** — edges from the constants a staged header's TYPE mentions. A
//!   cycle here is always vicious: types cannot legitimately depend on each
//!   other at the declaration level. The one exception, a mutual inductive
//!   family, is a SINGLE atomic node, so it is not a cycle in this graph at all.
//! * **`G_body`** — edges from the constants an elaborated type-and-value
//!   mentions, minus the node's own introduced names (self-recursion is not an
//!   inter-node edge).
//!
//! Detection is Tarjan over the union, one pass, O(V+E), producing the strongly
//! connected components directly. Only genuinely cyclic components are reported
//! (size ≥ 2, or a self-edge), and the witness rendered is the SHORTEST cycle
//! found by breadth-first search from an arbitrary member back to itself — so
//! the message reads `a -> b -> a` rather than dumping a forty-member component.
//!
//! # What counts as a SUPPORTED mutual group
//!
//! Exactly one thing: the members of a single syntactic `mutual … end` block
//! that is a parameterless `mutual inductive`, which routes to one atomic
//! `add_inductive` where the kernel re-checks positivity and builds the mutual
//! recursors. Because [`super::plan`] keeps a `mutual` block as ONE node, such a
//! group is never a cycle here in the first place.
//!
//! Everything else is vicious, and each kind gets its own diagnosis:
//!
//! * every member a `theorem` → [`BatchRejection::ProofCycle`]. There is no
//!   supported mutual-theorem form and there cannot be one: `theorem a : False
//!   := b` and `theorem b : False := a` is the shape staging exists to refuse.
//! * a cycle among staged signatures → [`BatchRejection::SignatureCycle`].
//! * anything else → [`BatchRejection::UnsupportedScc`], whose diagnostic names
//!   the ways forward in order of preference.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use clean_kernel::Name;

use super::plan::Plan;
use super::{BatchRejection, HeaderKind, Site};

/// Options offered when a dependency cycle is not a supported mutual group.
pub(super) const UNSUPPORTED_SCC_OPTIONS: &[&str] = &[
    "put every member of the cycle inside ONE `mutual ... end` block — that is \
     the only mutual form Clean checks atomically, and only for a parameterless \
     `mutual inductive`",
    "break the recursion so the members no longer need each other: give one of \
     them an explicit result type that does not mention the others, or inline \
     the shared part into a third declaration both can depend on",
    "state one member as an `axiom`, which is disclosed BY NAME in the \
     certification closure and never silently trusted — a proof depending on it \
     reports `NonFoundationalAxiom`, not `Certified`",
];

/// Options offered when the cycle is among proofs.
pub(super) const PROOF_CYCLE_OPTIONS: &[&str] = &[
    "prove one member outright, without reference to the others",
    "state one member as an `axiom` and accept the disclosure: it appears by \
     name in the certification closure of everything that uses it",
];

/// Classify every node that could not be scheduled.
///
/// `blocked` maps a node index to the staged names its elaborated term still
/// mentioned; `errors` carries the last elaboration failure for a node that
/// never produced a term at all.
pub(super) fn classify(
    plan: &Plan,
    blocked: &HashMap<usize, BTreeSet<Name>>,
    errors: &HashMap<usize, Box<crate::ElabError>>,
    pending: &[usize],
) -> Vec<BatchRejection> {
    // Which node introduces which name. Only staged/registered names matter:
    // an edge to something outside the batch is not a scheduling problem.
    let mut owner: HashMap<Name, usize> = HashMap::new();
    for (index, node) in plan.nodes.iter().enumerate() {
        if let Some(name) = &node.name {
            owner.insert(name.clone(), index);
        }
        for name in &node.introduces {
            owner.insert(name.clone(), index);
        }
    }

    let pending_set: HashSet<usize> = pending.iter().copied().collect();
    let mut edges: HashMap<usize, BTreeSet<usize>> = HashMap::new();
    for &index in pending {
        let mut targets = BTreeSet::new();
        // G_body: what the elaborated term still needs.
        if let Some(names) = blocked.get(&index) {
            for name in names {
                if let Some(&target) = owner.get(name) {
                    if target != index && pending_set.contains(&target) {
                        targets.insert(target);
                    }
                }
            }
        }
        // G_sig: what this node's own staged signature mentions.
        if let Some(header) = &plan.nodes[index].header {
            let mut in_type = HashSet::new();
            header.ty.collect_constants_into(&mut in_type);
            for name in in_type {
                if let Some(&target) = owner.get(&name) {
                    if target != index && pending_set.contains(&target) {
                        targets.insert(target);
                    }
                }
            }
        }
        edges.insert(index, targets);
    }

    let mut rejections = Vec::new();
    let mut reported: HashSet<usize> = HashSet::new();

    for component in tarjan(pending, &edges) {
        let cyclic = component.len() > 1
            || edges
                .get(&component[0])
                .is_some_and(|targets| targets.contains(&component[0]));
        if !cyclic {
            continue;
        }
        reported.extend(component.iter().copied());
        let witness_indices = shortest_cycle(&component, &edges);
        let witness: Vec<Site> = witness_indices
            .iter()
            .map(|&i| plan.nodes[i].site())
            .collect();
        let names: Vec<Name> = witness_indices
            .iter()
            .map(|&i| {
                plan.nodes[i]
                    .name
                    .clone()
                    .unwrap_or_else(|| Name::from_string(&plan.nodes[i].display_name()))
            })
            .collect();

        let all_theorems = component.iter().all(|&i| {
            plan.nodes[i]
                .header
                .as_ref()
                .is_some_and(|h| h.kind == HeaderKind::Theorem)
        });
        let signature_only = component
            .iter()
            .all(|&i| plan.nodes[i].header.is_some() && !blocked.contains_key(&i));

        rejections.push(if all_theorems {
            BatchRejection::ProofCycle { witness, names }
        } else if signature_only {
            BatchRejection::SignatureCycle { witness, names }
        } else {
            BatchRejection::UnsupportedScc {
                witness,
                names,
                options: UNSUPPORTED_SCC_OPTIONS,
            }
        });
    }

    // Whatever is left made no progress for its own reason, not a cycle's.
    for &index in pending {
        if reported.contains(&index) {
            continue;
        }
        let node = &plan.nodes[index];
        if let Some(error) = errors.get(&index) {
            rejections.push(BatchRejection::Elaboration {
                name: node.name.clone(),
                site: node.site(),
                error: error.clone(),
            });
        } else if let Some(staged) = blocked.get(&index) {
            rejections.push(BatchRejection::StagedReference {
                subject: node
                    .name
                    .clone()
                    .unwrap_or_else(|| Name::from_string(&node.display_name())),
                staged: staged.iter().cloned().collect(),
                site: node.site(),
            });
        }
    }

    rejections
}

/// Tarjan's strongly-connected-components, iterative so a deep dependency chain
/// cannot overflow the stack.
fn tarjan(nodes: &[usize], edges: &HashMap<usize, BTreeSet<usize>>) -> Vec<Vec<usize>> {
    #[derive(Default, Clone, Copy)]
    struct Info {
        index: Option<usize>,
        lowlink: usize,
        on_stack: bool,
    }

    let mut info: HashMap<usize, Info> = nodes.iter().map(|&n| (n, Info::default())).collect();
    let mut counter = 0usize;
    let mut stack: Vec<usize> = Vec::new();
    let mut components = Vec::new();
    let empty = BTreeSet::new();

    for &root in nodes {
        if info[&root].index.is_some() {
            continue;
        }
        // (node, index of the next successor to visit)
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        while let Some((node, child)) = work.pop() {
            if child == 0 {
                let entry = info.entry(node).or_default();
                entry.index = Some(counter);
                entry.lowlink = counter;
                entry.on_stack = true;
                counter += 1;
                stack.push(node);
            }
            let successors: Vec<usize> =
                edges.get(&node).unwrap_or(&empty).iter().copied().collect();
            let mut recursed = false;
            for (offset, &next) in successors.iter().enumerate().skip(child) {
                let next_info = info.get(&next).copied().unwrap_or_default();
                if next_info.index.is_none() {
                    work.push((node, offset + 1));
                    work.push((next, 0));
                    recursed = true;
                    break;
                } else if next_info.on_stack {
                    let current = info.get(&node).copied().unwrap_or_default();
                    let low = current.lowlink.min(next_info.index.unwrap_or(usize::MAX));
                    info.entry(node).or_default().lowlink = low;
                }
            }
            if recursed {
                continue;
            }
            let current = info.get(&node).copied().unwrap_or_default();
            if current.lowlink == current.index.unwrap_or(usize::MAX) {
                let mut component = Vec::new();
                while let Some(top) = stack.pop() {
                    info.entry(top).or_default().on_stack = false;
                    component.push(top);
                    if top == node {
                        break;
                    }
                }
                component.sort_unstable();
                components.push(component);
            }
            if let Some(&(parent, _)) = work.last() {
                let child_low = info.get(&node).copied().unwrap_or_default().lowlink;
                let entry = info.entry(parent).or_default();
                entry.lowlink = entry.lowlink.min(child_low);
            }
        }
    }
    components
}

/// The shortest cycle through some member of `component`, as a node list that
/// starts and ends at the same node.
fn shortest_cycle(component: &[usize], edges: &HashMap<usize, BTreeSet<usize>>) -> Vec<usize> {
    let members: HashSet<usize> = component.iter().copied().collect();
    let mut best: Option<Vec<usize>> = None;
    let empty = BTreeSet::new();
    for &start in component {
        let mut previous: HashMap<usize, usize> = HashMap::new();
        let mut queue = VecDeque::from([start]);
        let mut seen: HashSet<usize> = HashSet::from([start]);
        'search: while let Some(node) = queue.pop_front() {
            for &next in edges.get(&node).unwrap_or(&empty) {
                if !members.contains(&next) {
                    continue;
                }
                if next == start {
                    let mut path = vec![start];
                    let mut cursor = node;
                    while cursor != start {
                        path.push(cursor);
                        let Some(&back) = previous.get(&cursor) else {
                            break;
                        };
                        cursor = back;
                    }
                    path.reverse();
                    path.push(start);
                    if best.as_ref().is_none_or(|b| path.len() < b.len()) {
                        best = Some(path);
                    }
                    break 'search;
                }
                if seen.insert(next) {
                    previous.insert(next, node);
                    queue.push_back(next);
                }
            }
        }
    }
    best.unwrap_or_else(|| {
        let mut path = component.to_vec();
        if let Some(&first) = path.first() {
            path.push(first);
        }
        path
    })
}
