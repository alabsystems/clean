// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared BFS skeleton for shortest proof-chain search.

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

pub(super) fn bfs_chain_search<K, E, R>(
    source: K,
    target: K,
    adjacency: &HashMap<K, Vec<(K, E)>>,
    fold_path: impl FnOnce(&[E]) -> Option<R>,
) -> Option<R>
where
    K: Eq + Hash + Clone,
    E: Clone,
{
    let starts = adjacency.get(&source)?.iter().cloned();
    bfs_chain_search_from_starts(
        [source],
        starts,
        adjacency,
        |node| *node == target,
        fold_path,
    )
}

pub(super) fn bfs_chain_search_from_starts<K, E, R>(
    blocked: impl IntoIterator<Item = K>,
    starts: impl IntoIterator<Item = (K, E)>,
    adjacency: &HashMap<K, Vec<(K, E)>>,
    is_target: impl Fn(&K) -> bool,
    fold_path: impl FnOnce(&[E]) -> Option<R>,
) -> Option<R>
where
    K: Eq + Hash + Clone,
    E: Clone,
{
    let mut seen: HashSet<K> = blocked.into_iter().collect();
    let mut parent: HashMap<K, (Option<K>, E)> = HashMap::new();
    let mut queue = VecDeque::new();

    for (node, edge) in starts {
        if seen.insert(node.clone()) {
            parent.insert(node.clone(), (None, edge));
            queue.push_back(node);
        }
    }

    while let Some(current) = queue.pop_front() {
        if is_target(&current) {
            let mut path = Vec::new();
            let mut node = current.clone();
            loop {
                let (prev, edge) = parent.get(&node)?;
                path.push(edge.clone());
                let Some(prev) = prev else {
                    break;
                };
                node = prev.clone();
            }
            path.reverse();
            return fold_path(&path);
        }

        if let Some(neighbors) = adjacency.get(&current) {
            for (neighbor, edge) in neighbors {
                if seen.insert(neighbor.clone()) {
                    parent.insert(neighbor.clone(), (Some(current.clone()), edge.clone()));
                    queue.push_back(neighbor.clone());
                }
            }
        }
    }

    None
}
