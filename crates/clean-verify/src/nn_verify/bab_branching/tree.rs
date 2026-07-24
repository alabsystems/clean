// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BaB tree formalization: nodes, tree structure, and metrics.
//!
//! A branch-and-bound (BaB) tree for neural network verification represents
//! the search space explored by splitting on ReLU neurons. Each internal node
//! corresponds to a neuron split, with children representing the two cases
//! (neuron forced active vs. forced inactive). Leaf nodes hold verification
//! results.
//!
//! ## Design
//!
//! The tree uses arena-based allocation with `NodeId` indices into a flat
//! `Vec<BabNode>`. This avoids recursive ownership issues and enables O(1)
//! node access. The root is always at index 0.

/// Unique identifier for a node in the BaB tree (index into the arena).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(pub(crate) usize);

impl NodeId {
    /// Return the raw index value.
    #[must_use]
    pub fn index(self) -> usize {
        self.0
    }
}

/// Direction of a neuron split in the BaB tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SplitDirection {
    /// Neuron forced active (pre-activation >= 0, ReLU = identity).
    Active,
    /// Neuron forced inactive (pre-activation <= 0, ReLU = zero).
    Inactive,
}

/// Verification result at a BaB tree leaf node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VerificationResult {
    /// The subproblem is verified safe (property holds on this branch).
    Safe,
    /// A counterexample was found (property violated on this branch).
    Unsafe,
    /// Verification is incomplete (e.g., timeout or bound too loose).
    Unknown,
}

/// A single node in the BaB search tree.
///
/// Internal nodes have a `neuron_split` and two children. Leaf nodes
/// have `neuron_split == None` and a `result`.
#[derive(Debug, Clone)]
pub struct BabNode {
    /// Which neuron was split at this node.
    /// `None` for leaf nodes (no further splitting).
    pub neuron_split: Option<NeuronId>,

    /// Direction from parent (how this node was reached).
    /// `None` for the root node.
    pub direction: Option<SplitDirection>,

    /// Child when the neuron is forced active.
    pub active_child: Option<NodeId>,

    /// Child when the neuron is forced inactive.
    pub inactive_child: Option<NodeId>,

    /// Parent node. `None` for the root.
    pub parent: Option<NodeId>,

    /// Verification result (only meaningful at leaf nodes).
    pub result: Option<VerificationResult>,

    /// Depth of this node in the tree (root = 0).
    pub depth: u32,

    /// Lower bound on the verification objective at this node.
    /// Used for pruning: if lower_bound proves safety, no need to split.
    pub lower_bound: f64,
}

/// Identifier for a neuron in the network.
///
/// Neurons are identified by their layer index and position within the layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NeuronId {
    /// Layer index (0-based from input).
    pub layer: u32,
    /// Neuron position within the layer.
    pub index: u32,
}

impl NeuronId {
    /// Create a new neuron identifier.
    #[must_use]
    pub fn new(layer: u32, index: u32) -> Self {
        Self { layer, index }
    }
}

/// A complete branch-and-bound search tree.
///
/// Stores nodes in a flat arena for cache-friendly access. The root is
/// always at index 0 (if the tree is non-empty).
#[derive(Debug, Clone)]
pub struct BabTree {
    /// Arena of all nodes in the tree.
    nodes: Vec<BabNode>,
}

impl BabTree {
    /// Create a new BaB tree with a single root leaf node.
    #[must_use]
    pub fn new() -> Self {
        let root = BabNode {
            neuron_split: None,
            direction: None,
            active_child: None,
            inactive_child: None,
            parent: None,
            result: None,
            depth: 0,
            lower_bound: f64::NEG_INFINITY,
        };
        Self { nodes: vec![root] }
    }

    /// Return the root node ID.
    #[must_use]
    pub fn root(&self) -> NodeId {
        NodeId(0)
    }

    /// Return the number of nodes in the tree.
    #[must_use]
    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    /// Return the node at the given ID.
    ///
    /// Returns `None` if the ID is out of bounds.
    #[must_use]
    pub fn get(&self, id: NodeId) -> Option<&BabNode> {
        self.nodes.get(id.0)
    }

    /// Return the maximum depth of the tree.
    ///
    /// Returns 0 for a single-node tree.
    #[must_use]
    pub fn max_depth(&self) -> u32 {
        self.nodes.iter().map(|n| n.depth).max().unwrap_or(0)
    }

    /// Count the number of leaf nodes (nodes with no children).
    #[must_use]
    pub fn leaf_count(&self) -> usize {
        self.nodes
            .iter()
            .filter(|n| n.active_child.is_none() && n.inactive_child.is_none())
            .count()
    }

    /// Count the number of internal (non-leaf) nodes.
    #[must_use]
    pub fn internal_count(&self) -> usize {
        self.size() - self.leaf_count()
    }

    /// Check whether the tree is complete: every leaf has a verification result.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.nodes.iter().all(|n| {
            let is_leaf = n.active_child.is_none() && n.inactive_child.is_none();
            !is_leaf || n.result.is_some()
        })
    }

    /// Check whether the entire verification is resolved.
    ///
    /// Returns `Some(Safe)` if all leaves are `Safe`, `Some(Unsafe)` if any
    /// leaf is `Unsafe`, and `None` if there are unresolved leaves.
    #[must_use]
    pub fn overall_result(&self) -> Option<VerificationResult> {
        let leaves: Vec<_> = self
            .nodes
            .iter()
            .filter(|n| n.active_child.is_none() && n.inactive_child.is_none())
            .collect();

        if leaves.is_empty() {
            return None;
        }

        // Any Unsafe leaf means the property is violated.
        if leaves
            .iter()
            .any(|n| n.result == Some(VerificationResult::Unsafe))
        {
            return Some(VerificationResult::Unsafe);
        }

        // All leaves must be Safe for overall safety.
        if leaves
            .iter()
            .all(|n| n.result == Some(VerificationResult::Safe))
        {
            return Some(VerificationResult::Safe);
        }

        None
    }

    /// Split a leaf node on a given neuron, creating two child leaves.
    ///
    /// Returns the IDs of the (active_child, inactive_child) pair, or `None`
    /// if the node is not a valid leaf (already has children or ID out of bounds).
    pub fn split_node(&mut self, node_id: NodeId, neuron: NeuronId) -> Option<(NodeId, NodeId)> {
        // Validate: node exists and is a leaf.
        let depth = {
            let node = self.nodes.get(node_id.0)?;
            if node.active_child.is_some() || node.inactive_child.is_some() {
                return None;
            }
            node.depth
        };

        // Create active child.
        let active_id = NodeId(self.nodes.len());
        self.nodes.push(BabNode {
            neuron_split: None,
            direction: Some(SplitDirection::Active),
            active_child: None,
            inactive_child: None,
            parent: Some(node_id),
            result: None,
            depth: depth + 1,
            lower_bound: f64::NEG_INFINITY,
        });

        // Create inactive child.
        let inactive_id = NodeId(self.nodes.len());
        self.nodes.push(BabNode {
            neuron_split: None,
            direction: Some(SplitDirection::Inactive),
            active_child: None,
            inactive_child: None,
            parent: Some(node_id),
            result: None,
            depth: depth + 1,
            lower_bound: f64::NEG_INFINITY,
        });

        // Update parent to record split.
        let node = &mut self.nodes[node_id.0];
        node.neuron_split = Some(neuron);
        node.active_child = Some(active_id);
        node.inactive_child = Some(inactive_id);
        // Clear any previous result since this is now an internal node.
        node.result = None;

        Some((active_id, inactive_id))
    }

    /// Set the verification result for a leaf node.
    ///
    /// Returns `false` if the node is not a leaf or ID is out of bounds.
    pub fn set_result(&mut self, node_id: NodeId, result: VerificationResult) -> bool {
        if let Some(node) = self.nodes.get_mut(node_id.0) {
            if node.active_child.is_some() || node.inactive_child.is_some() {
                return false; // Not a leaf.
            }
            node.result = Some(result);
            true
        } else {
            false
        }
    }

    /// Set the lower bound for a node.
    pub fn set_lower_bound(&mut self, node_id: NodeId, bound: f64) -> bool {
        if let Some(node) = self.nodes.get_mut(node_id.0) {
            node.lower_bound = bound;
            true
        } else {
            false
        }
    }

    /// Return all leaf node IDs that have no verification result yet.
    #[must_use]
    pub fn open_leaves(&self) -> Vec<NodeId> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| {
                n.active_child.is_none() && n.inactive_child.is_none() && n.result.is_none()
            })
            .map(|(i, _)| NodeId(i))
            .collect()
    }

    /// Collect the neuron splits along the path from root to the given node.
    ///
    /// Returns a list of `(NeuronId, SplitDirection)` pairs from root to node.
    #[must_use]
    pub fn path_to_node(&self, node_id: NodeId) -> Vec<(NeuronId, SplitDirection)> {
        let mut path = Vec::new();
        let mut current = node_id;

        while let Some(node) = self.nodes.get(current.0) {
            if let (Some(parent_id), Some(direction)) = (node.parent, node.direction) {
                if let Some(parent) = self.nodes.get(parent_id.0) {
                    if let Some(neuron) = parent.neuron_split {
                        path.push((neuron, direction));
                    }
                }
                current = parent_id;
            } else {
                break;
            }
        }

        path.reverse();
        path
    }
}

impl Default for BabTree {
    fn default() -> Self {
        Self::new()
    }
}
