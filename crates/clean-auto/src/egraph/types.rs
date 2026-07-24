// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core E-graph data types: e-class IDs, symbols, e-nodes, and union-find.

use std::sync::Arc;

/// An e-class ID (equivalence class identifier)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EClassId(u32);

impl EClassId {
    /// Create a new e-class ID
    #[inline]
    pub fn new(id: u32) -> Self {
        EClassId(id)
    }

    /// Get the raw ID value
    #[inline]
    pub fn id(self) -> u32 {
        self.0
    }
}

/// A symbol (function name or constant name)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Symbol(Arc<str>);

impl Symbol {
    /// Create a new symbol
    pub fn new(name: impl AsRef<str>) -> Self {
        Symbol(Arc::from(name.as_ref()))
    }

    /// Get the symbol name
    pub fn name(&self) -> &str {
        &self.0
    }

    #[cfg(test)]
    pub(super) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol::new(s)
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Self {
        Symbol(Arc::from(s.into_boxed_str()))
    }
}

impl From<&String> for Symbol {
    fn from(s: &String) -> Self {
        Symbol::new(s)
    }
}

/// An e-node represents a function application.
/// The children are e-class IDs, not direct terms.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ENode {
    /// The function symbol (or constant name if no children)
    pub symbol: Symbol,
    /// Child e-class IDs (empty for constants)
    pub children: Vec<EClassId>,
}

/// Reason why two e-classes were merged
#[derive(Clone, Debug)]
pub enum MergeReason {
    /// Direct union call (external assertion)
    External,
    /// Congruence: two function applications became equal
    /// because their arguments became equal
    Congruence {
        /// The function symbol
        func: Symbol,
        /// The original children of the first e-node (before canonicalization)
        children1: Vec<EClassId>,
        /// The original children of the second e-node (before canonicalization)
        children2: Vec<EClassId>,
    },
}

/// Record of a merge operation in the E-graph
#[derive(Clone, Debug)]
pub struct MergeRecord {
    /// First e-class (before merge)
    pub ec1: EClassId,
    /// Second e-class (before merge)
    pub ec2: EClassId,
    /// Reason for the merge
    pub reason: MergeReason,
}

impl ENode {
    /// Create a constant (no children)
    pub fn constant(symbol: impl Into<Symbol>) -> Self {
        ENode {
            symbol: symbol.into(),
            children: Vec::new(),
        }
    }

    /// Create a function application
    pub fn app(symbol: impl Into<Symbol>, children: Vec<EClassId>) -> Self {
        ENode {
            symbol: symbol.into(),
            children,
        }
    }

    /// Check if this is a constant (no children)
    pub fn is_constant(&self) -> bool {
        self.children.is_empty()
    }

    /// Get the arity (number of children)
    pub fn arity(&self) -> usize {
        self.children.len()
    }

    /// Create a canonical version of this e-node using the given function
    /// to map e-class IDs to their canonical representatives
    #[must_use]
    pub fn canonicalize(&self, mut find: impl FnMut(EClassId) -> EClassId) -> Self {
        ENode {
            symbol: self.symbol.clone(),
            children: self.children.iter().map(|&id| find(id)).collect(),
        }
    }

    /// Returns `true` if all children are already canonical (i.e., `find(id) == id`
    /// for every child). When true, `canonicalize` would return a structurally
    /// identical node, so the caller can skip the allocation and clone `self`.
    pub fn is_canonical(&self, mut find: impl FnMut(EClassId) -> EClassId) -> bool {
        self.children.iter().all(|&id| find(id) == id)
    }
}

/// An equivalence class containing e-nodes
#[derive(Clone, Debug)]
pub struct EClass {
    /// The canonical ID of this e-class
    pub id: EClassId,
    /// All e-nodes in this e-class
    pub nodes: Vec<ENode>,
    /// Parent e-nodes that reference this e-class
    /// (used for upward merging during congruence closure)
    pub parents: Vec<(ENode, EClassId)>,
}

impl EClass {
    /// Create a new e-class with a single node
    pub(super) fn new(id: EClassId, node: ENode) -> Self {
        EClass {
            id,
            nodes: vec![node],
            parents: Vec::new(),
        }
    }
}

/// Union-Find data structure for efficient equivalence class operations
#[derive(Clone, Debug)]
pub(super) struct UnionFind {
    /// Parent pointers (id -> parent id).
    /// If `parent[i] == i`, then `i` is a root.
    parent: Vec<u32>,
    /// Rank for union by rank optimization
    rank: Vec<u32>,
}

impl UnionFind {
    /// Create a new empty union-find
    pub(super) fn new() -> Self {
        UnionFind {
            parent: Vec::new(),
            rank: Vec::new(),
        }
    }

    /// Make a new singleton set and return its ID
    pub(super) fn make_set(&mut self) -> EClassId {
        let id = u32::try_from(self.parent.len()).expect("invariant: e-class count fits in u32");
        self.parent.push(id);
        self.rank.push(0);
        EClassId(id)
    }

    /// Find the canonical representative of an e-class (with path compression)
    pub(super) fn find(&mut self, id: EClassId) -> EClassId {
        let idx = id.0 as usize;
        if self.parent[idx] != id.0 {
            // Path compression
            let root = self.find(EClassId(self.parent[idx]));
            self.parent[idx] = root.0;
        }
        EClassId(self.parent[idx])
    }

    /// Find without mutation (for use in contexts where we can't mutate)
    pub(super) fn find_const(&self, id: EClassId) -> EClassId {
        let mut current = id.0;
        while self.parent[current as usize] != current {
            current = self.parent[current as usize];
        }
        EClassId(current)
    }

    /// Union two e-classes, returns the new root
    /// Returns (new_root, merged_root) - merged_root is now pointing to new_root
    pub(super) fn union(&mut self, a: EClassId, b: EClassId) -> (EClassId, EClassId) {
        let a_root = self.find(a);
        let b_root = self.find(b);

        if a_root == b_root {
            return (a_root, a_root);
        }

        let a_idx = a_root.0 as usize;
        let b_idx = b_root.0 as usize;

        // Union by rank
        if self.rank[a_idx] < self.rank[b_idx] {
            self.parent[a_idx] = b_root.0;
            (b_root, a_root)
        } else if self.rank[a_idx] > self.rank[b_idx] {
            self.parent[b_idx] = a_root.0;
            (a_root, b_root)
        } else {
            self.parent[b_idx] = a_root.0;
            self.rank[a_idx] += 1;
            (a_root, b_root)
        }
    }
}
