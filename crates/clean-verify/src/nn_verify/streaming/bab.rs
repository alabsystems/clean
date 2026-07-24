// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Branch-and-Bound (BaB) tree certificate verification.
//!
//! A BaB verifier recursively splits the input region along chosen dimensions.
//! Each leaf node either verifies the property for its subregion or reports
//! a counterexample. A complete BaB tree with all leaves verified constitutes
//! a proof for the root region (T82).
//!
//! ## Tree Structure
//!
//! ```text
//!              [root: R]
//!             /          \
//!     [R_left]            [R_right]
//!    /        \           (leaf: verified)
//! (leaf)    (leaf)
//! ```
//!
//! Interior nodes carry the split dimension and split value.
//! Leaf nodes carry a [`PartialCert`].

use thiserror::Error;

use super::partial_cert::{PartialCert, RegionBounds};

/// Errors from BaB tree verification.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum BabTreeError {
    /// A leaf node's certificate is not verified.
    #[error("leaf at depth {depth} has unverified certificate (cert_id={cert_id})")]
    UnverifiedLeaf { depth: usize, cert_id: u64 },

    /// A leaf node's certificate region does not match the expected region.
    #[error("leaf region mismatch at depth {depth}: expected {expected}, got {actual}")]
    RegionMismatch {
        depth: usize,
        expected: String,
        actual: String,
    },

    /// An interior node's children do not partition the parent region correctly.
    #[error("split error at depth {depth}, dim {dim}: {reason}")]
    SplitError {
        depth: usize,
        dim: usize,
        reason: String,
    },

    /// Split dimension is out of bounds for the region dimensionality.
    #[error("split dimension {dim} out of bounds for {ndim}-dimensional region at depth {depth}")]
    SplitDimOutOfBounds {
        depth: usize,
        dim: usize,
        ndim: usize,
    },

    /// The tree is empty (no root node).
    #[error("empty BaB tree")]
    EmptyTree,
}

/// Split dimension specification for a BaB interior node.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BabSplitDim {
    /// Which input dimension to split on (0-indexed).
    pub dim: usize,
    /// The value at which to split: left child gets `[lo, split_val]`,
    /// right child gets `[split_val, hi]`.
    pub split_val: f64,
}

/// A node in the Branch-and-Bound verification tree.
///
/// Either a leaf holding a [`PartialCert`] or an interior node that splits
/// the region along one dimension.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum BabNode {
    /// Leaf node with a partial certificate for a subregion.
    Leaf {
        /// The partial certificate for this subregion.
        cert: PartialCert,
    },
    /// Interior node that splits the region into two children.
    Interior {
        /// The region this node covers.
        region: RegionBounds,
        /// How the region is split.
        split: BabSplitDim,
        /// Left child (covers region with upper bound = split_val on split dim).
        left: Box<BabNode>,
        /// Right child (covers region with lower bound = split_val on split dim).
        right: Box<BabNode>,
    },
}

impl BabNode {
    /// Get the region covered by this node.
    #[must_use]
    pub fn region(&self) -> &RegionBounds {
        match self {
            Self::Leaf { cert } => &cert.region,
            Self::Interior { region, .. } => region,
        }
    }

    /// Count the total number of leaf nodes.
    #[must_use]
    pub fn leaf_count(&self) -> usize {
        match self {
            Self::Leaf { .. } => 1,
            Self::Interior { left, right, .. } => left.leaf_count() + right.leaf_count(),
        }
    }

    /// Maximum depth of the tree (0 for a leaf).
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            Self::Leaf { .. } => 0,
            Self::Interior { left, right, .. } => 1 + left.depth().max(right.depth()),
        }
    }

    /// Check if all leaves are verified.
    #[must_use]
    pub fn all_verified(&self) -> bool {
        match self {
            Self::Leaf { cert } => cert.verified,
            Self::Interior { left, right, .. } => left.all_verified() && right.all_verified(),
        }
    }
}

/// Tolerance for floating-point bound comparisons.
const EPSILON: f64 = 1e-9;

/// Verify a complete BaB tree certificate.
///
/// Checks that:
/// 1. The tree's root region matches the expected `root_region`.
/// 2. Every interior node correctly partitions its region along its split dimension.
/// 3. Every leaf node has a verified partial certificate whose region matches.
///
/// This implements the T82 theorem: if all leaves are verified, the entire
/// root region is verified.
///
/// # Errors
///
/// Returns [`BabTreeError`] describing the first structural or verification
/// failure found during traversal.
pub fn verify_bab_tree(tree: &BabNode, root_region: &RegionBounds) -> Result<(), BabTreeError> {
    verify_node(tree, root_region, 0)
}

/// Recursive verification of a single BaB node.
fn verify_node(
    node: &BabNode,
    expected_region: &RegionBounds,
    depth: usize,
) -> Result<(), BabTreeError> {
    match node {
        BabNode::Leaf { cert } => {
            // Check that the leaf's certificate region matches the expected region.
            if !regions_match(&cert.region, expected_region) {
                return Err(BabTreeError::RegionMismatch {
                    depth,
                    expected: expected_region.to_string(),
                    actual: cert.region.to_string(),
                });
            }

            // Check that the certificate is verified.
            if !cert.verified {
                return Err(BabTreeError::UnverifiedLeaf {
                    depth,
                    cert_id: cert.cert_id,
                });
            }

            Ok(())
        }
        BabNode::Interior {
            region,
            split,
            left,
            right,
        } => {
            // Check that the interior node's region matches expected.
            if !regions_match(region, expected_region) {
                return Err(BabTreeError::RegionMismatch {
                    depth,
                    expected: expected_region.to_string(),
                    actual: region.to_string(),
                });
            }

            // Validate split dimension.
            if split.dim >= region.ndim() {
                return Err(BabTreeError::SplitDimOutOfBounds {
                    depth,
                    dim: split.dim,
                    ndim: region.ndim(),
                });
            }

            // Validate split value is within the region's bounds on that dimension.
            let (lo, hi) = region.bounds()[split.dim];
            if split.split_val < lo - EPSILON || split.split_val > hi + EPSILON {
                return Err(BabTreeError::SplitError {
                    depth,
                    dim: split.dim,
                    reason: format!(
                        "split_val {} outside region bounds [{}, {}]",
                        split.split_val, lo, hi
                    ),
                });
            }

            // Compute expected child regions.
            let left_region = region.restrict_upper(split.dim, split.split_val);
            let right_region = region.restrict_lower(split.dim, split.split_val);

            // Recursively verify children.
            verify_node(left, &left_region, depth + 1)?;
            verify_node(right, &right_region, depth + 1)?;

            Ok(())
        }
    }
}

/// Check if two regions match within floating-point tolerance.
fn regions_match(a: &RegionBounds, b: &RegionBounds) -> bool {
    if a.ndim() != b.ndim() {
        return false;
    }
    a.bounds()
        .iter()
        .zip(b.bounds().iter())
        .all(|(&(a_lo, a_hi), &(b_lo, b_hi))| {
            (a_lo - b_lo).abs() <= EPSILON && (a_hi - b_hi).abs() <= EPSILON
        })
}
