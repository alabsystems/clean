// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! EGraph: congruence closure data structure with hashconsing and proof recording.

use super::{EClass, EClassId, ENode, MergeReason, MergeRecord, Symbol, Term, UnionFind};
use std::collections::{HashMap, HashSet, VecDeque};

/// Reusable buffer for congruence detection during `do_union`.
///
/// Avoids allocating a fresh `HashMap` on every union call. The buffer is
/// cleared at the start of each `do_union` invocation and reused across calls.
#[derive(Clone, Debug, Default)]
struct CongruenceBuf {
    /// Maps canonical e-nodes to (original_node_index, parent_id) pairs.
    /// Indices refer into a temporary snapshot of the combined parent list.
    canonical_groups: HashMap<ENode, Vec<(usize, EClassId)>>,
}

/// The E-graph data structure
#[derive(Clone, Debug)]
pub struct EGraph {
    /// Union-find for e-class membership
    uf: UnionFind,
    /// E-classes indexed by their canonical ID
    pub(super) classes: HashMap<EClassId, EClass>,
    /// Hashcons: maps canonical e-nodes to their e-class
    pub(super) hashcons: HashMap<ENode, EClassId>,
    /// Pending merges for congruence closure (includes reason)
    pending: VecDeque<(EClassId, EClassId, MergeReason)>,
    /// Whether the egraph needs rebuilding (after unions)
    dirty: bool,
    /// History of merge operations (for proof reconstruction)
    pub(super) merge_history: Vec<MergeRecord>,
    /// Reusable buffer for congruence detection (avoids HashMap alloc per union).
    congruence_buf: CongruenceBuf,
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl EGraph {
    /// Create a new empty e-graph.
    ///
    /// # Contracts
    ///
    /// **ENSURES:**
    /// - Returns empty e-graph with no e-classes
    /// - No pending congruence closure work
    pub fn new() -> Self {
        EGraph {
            uf: UnionFind::new(),
            classes: HashMap::new(),
            hashcons: HashMap::new(),
            pending: VecDeque::new(),
            dirty: false,
            merge_history: Vec::new(),
            congruence_buf: CongruenceBuf::default(),
        }
    }

    /// Get the canonical representative of an e-class ID.
    ///
    /// # Contracts
    ///
    /// **REQUIRES:** `id` was returned by `add_const`, `add_app`, or `union`.
    ///
    /// **ENSURES:**
    /// - Returns canonical representative of `id`'s equivalence class
    /// - `find(find(x)) == find(x)` (idempotent)
    /// - `find(x) == find(y)` iff `x` and `y` are in same class
    pub fn find(&mut self, id: EClassId) -> EClassId {
        self.uf.find(id)
    }

    /// Get the canonical representative without mutation
    pub fn find_const(&self, id: EClassId) -> EClassId {
        self.uf.find_const(id)
    }

    /// Check if two e-class IDs are in the same equivalence class
    pub fn are_equal(&mut self, a: EClassId, b: EClassId) -> bool {
        self.find(a) == self.find(b)
    }

    /// Add a constant to the e-graph.
    ///
    /// # Contracts
    ///
    /// **ENSURES:**
    /// - Returns e-class ID for the constant
    /// - Hashconsed: multiple calls with same name return same canonical e-class
    /// - Constant is leaf node (no children)
    pub fn add_const(&mut self, name: impl Into<Symbol>) -> EClassId {
        let node = ENode::constant(name);
        self.add_node(node)
    }

    /// Add a function application to the e-graph.
    ///
    /// # Contracts
    ///
    /// **REQUIRES:** All `children` are valid e-class IDs.
    ///
    /// **ENSURES:**
    /// - Returns e-class ID for `symbol(children...)`
    /// - Hashconsed: structurally equal nodes map to same e-class
    /// - Children are canonicalized before lookup
    pub fn add_app(&mut self, symbol: impl Into<Symbol>, children: Vec<EClassId>) -> EClassId {
        // Canonicalize children first
        let canonical_children: Vec<EClassId> = children.iter().map(|&id| self.find(id)).collect();
        let node = ENode::app(symbol, canonical_children);
        self.add_node(node)
    }

    /// Add an e-node to the e-graph
    fn add_node(&mut self, node: ENode) -> EClassId {
        // Canonicalize the node
        let canonical = node.canonicalize(|id| self.find(id));

        // Check if we already have this e-node (hashconsing)
        if let Some(&id) = self.hashcons.get(&canonical) {
            return self.find(id);
        }

        // Create a new e-class
        let id = self.uf.make_set();
        let eclass = EClass::new(id, canonical.clone());

        // Register this e-class as a parent of its children
        for &child_id in &canonical.children {
            let child_canonical = self.find(child_id);
            if let Some(child_class) = self.classes.get_mut(&child_canonical) {
                child_class.parents.push((canonical.clone(), id));
            }
        }

        self.hashcons.insert(canonical, id);
        self.classes.insert(id, eclass);

        id
    }

    /// Merge two e-classes (assert they are equal).
    ///
    /// # Contracts
    ///
    /// **REQUIRES:** Both `a` and `b` are valid e-class IDs.
    ///
    /// **ENSURES:**
    /// - `find(a) == find(b)` after call
    /// - Triggers congruence closure
    /// - Returns canonical representative of merged class
    pub fn union(&mut self, a: EClassId, b: EClassId) -> EClassId {
        self.union_with_reason(a, b, MergeReason::External)
    }

    /// Merge two e-classes with a specified reason
    pub fn union_with_reason(&mut self, a: EClassId, b: EClassId, reason: MergeReason) -> EClassId {
        let a = self.find(a);
        let b = self.find(b);

        if a == b {
            return a;
        }

        self.pending.push_back((a, b, reason));
        self.dirty = true;

        // Process all pending merges (congruence closure)
        self.rebuild();

        self.find(a)
    }

    /// Rebuild the e-graph after unions (congruence closure)
    fn rebuild(&mut self) {
        while let Some((a, b, reason)) = self.pending.pop_front() {
            self.do_union(a, b, reason);
        }
        self.dirty = false;
    }

    /// Perform the actual union and propagate congruences
    fn do_union(&mut self, a: EClassId, b: EClassId, reason: MergeReason) {
        let a = self.uf.find(a);
        let b = self.uf.find(b);

        if a == b {
            return;
        }

        self.merge_history.push(MergeRecord {
            ec1: a,
            ec2: b,
            reason,
        });

        let (new_root, merged_root) = self.uf.union(a, b);

        let merged_class = self
            .classes
            .remove(&merged_root)
            .expect("invariant: merged e-class exists after union");
        let mut root_class = self
            .classes
            .remove(&new_root)
            .expect("invariant: root e-class exists after union");

        root_class.nodes.extend(merged_class.nodes);

        let congruence_merges = self.detect_congruences(&root_class.parents, &merged_class.parents);

        root_class.parents.extend(merged_class.parents);
        self.classes.insert(new_root, root_class);
        self.pending.extend(congruence_merges);
    }

    /// Detect congruent parents across two parent lists. Updates `hashcons`
    /// with re-canonicalized entries and returns pending congruence merges.
    /// Reuses `congruence_buf` to avoid per-call HashMap allocation.
    fn detect_congruences(
        &mut self,
        root_parents: &[(ENode, EClassId)],
        merged_parents: &[(ENode, EClassId)],
    ) -> Vec<(EClassId, EClassId, MergeReason)> {
        self.congruence_buf.canonical_groups.clear();

        let all_parents: Vec<(&ENode, EClassId)> = root_parents
            .iter()
            .chain(merged_parents.iter())
            .map(|(node, id)| (node, *id))
            .collect();

        for (idx, &(node, parent_id)) in all_parents.iter().enumerate() {
            let canonical = node.canonicalize(|id| self.uf.find_const(id));
            let parent_canonical = self.uf.find_const(parent_id);
            self.hashcons.remove(node);
            self.hashcons.insert(canonical.clone(), parent_canonical);
            self.congruence_buf
                .canonical_groups
                .entry(canonical)
                .or_default()
                .push((idx, parent_id));
        }

        let mut merges = Vec::new();
        for (canonical, group) in &self.congruence_buf.canonical_groups {
            if group.len() < 2 {
                continue;
            }
            let &(first_idx, first_id) = &group[0];
            let first_canonical = self.uf.find_const(first_id);
            let first_node = all_parents[first_idx].0;

            for &(idx, parent_id) in group.iter().skip(1) {
                let parent_canonical = self.uf.find_const(parent_id);
                if first_canonical != parent_canonical {
                    let node = all_parents[idx].0;
                    merges.push((
                        first_canonical,
                        parent_canonical,
                        MergeReason::Congruence {
                            func: canonical.symbol.clone(),
                            children1: first_node.children.clone(),
                            children2: node.children.clone(),
                        },
                    ));
                }
            }
        }
        for group in self.congruence_buf.canonical_groups.values_mut() {
            group.clear();
        }
        merges
    }

    /// Get an e-class by ID (returns the canonical class)
    pub fn get_class(&mut self, id: EClassId) -> Option<&EClass> {
        let canonical = self.find(id);
        self.classes.get(&canonical)
    }

    /// Get the number of e-classes
    pub fn num_classes(&self) -> usize {
        self.classes
            .keys()
            .filter(|&&id| self.uf.find_const(id) == id)
            .count()
    }

    /// Get the total number of e-nodes
    pub fn num_nodes(&self) -> usize {
        self.classes
            .values()
            .filter(|c| self.uf.find_const(c.id) == c.id)
            .map(|c| c.nodes.len())
            .sum()
    }

    /// Get all canonical e-class IDs
    pub fn classes(&self) -> impl Iterator<Item = EClassId> + '_ {
        self.classes
            .keys()
            .copied()
            .filter(move |&id| self.uf.find_const(id) == id)
    }

    /// Check if the e-graph contains an e-node
    pub fn contains(&self, node: &ENode) -> bool {
        let canonical = node.canonicalize(|id| self.uf.find_const(id));
        self.hashcons.contains_key(&canonical)
    }

    /// Lookup an e-node in the e-graph
    pub fn lookup(&mut self, node: &ENode) -> Option<EClassId> {
        let canonical = node.canonicalize(|id| self.uf.find(id));
        if let Some(&id) = self.hashcons.get(&canonical) {
            Some(self.find(id))
        } else {
            None
        }
    }

    /// Get all e-nodes in an e-class
    pub fn get_nodes(&mut self, id: EClassId) -> Vec<ENode> {
        let canonical = self.find(id);
        self.classes
            .get(&canonical)
            .map(|c| c.nodes.clone())
            .unwrap_or_default()
    }

    /// Extract a representative term from an e-class (smallest by default)
    pub fn extract(&mut self, id: EClassId) -> Option<Term> {
        let mut visited = HashSet::new();
        self.extract_with_visited(id, &mut visited)
    }

    fn extract_with_visited(
        &mut self,
        id: EClassId,
        visited: &mut HashSet<EClassId>,
    ) -> Option<Term> {
        let canonical = self.find(id);

        if !visited.insert(canonical) {
            return None;
        }

        let nodes: Vec<ENode> = self.classes.get(&canonical)?.nodes.clone();

        let mut best: Option<(usize, Term)> = None;

        for node in &nodes {
            if let Some(term) = self.extract_term_with_visited(node, visited) {
                let size = term.size();
                match &best {
                    None => best = Some((size, term)),
                    Some((best_size, _)) if size < *best_size => best = Some((size, term)),
                    _ => {}
                }
            }
        }

        visited.remove(&canonical);
        best.map(|(_, t)| t)
    }

    fn extract_term_with_visited(
        &mut self,
        node: &ENode,
        visited: &mut HashSet<EClassId>,
    ) -> Option<Term> {
        if node.is_constant() {
            return Some(Term::Const(node.symbol.name().to_string()));
        }

        let children_ids: Vec<EClassId> = node.children.clone();
        let mut children = Vec::new();
        for child_id in children_ids {
            children.push(self.extract_with_visited(child_id, visited)?);
        }

        Some(Term::App(node.symbol.name().to_string(), children))
    }

    /// Clear the e-graph
    pub fn clear(&mut self) {
        self.uf = UnionFind::new();
        self.classes.clear();
        self.hashcons.clear();
        self.pending.clear();
        self.dirty = false;
        self.merge_history.clear();
        self.congruence_buf.canonical_groups.clear();
    }

    /// Get the merge history for proof reconstruction
    pub fn merge_history(&self) -> &[MergeRecord] {
        &self.merge_history
    }

    /// Clear the merge history (useful after extracting for proofs)
    pub fn clear_merge_history(&mut self) {
        self.merge_history.clear();
    }
}
