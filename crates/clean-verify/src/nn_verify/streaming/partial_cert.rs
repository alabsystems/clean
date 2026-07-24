// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Partial certificates for subregions of the input space.
//!
//! A [`PartialCert`] attests that a neural network satisfies a
//! [`VerifiedProperty`] for all inputs within a bounded [`RegionBounds`].
//! Two adjacent partial certs can be merged via [`merge_certificates`]
//! when their regions partition a larger region along a split dimension.

use std::fmt;

use thiserror::Error;

use super::super::certificate::ChainTrustLevel;

/// Tolerance for floating-point bound comparisons.
const EPSILON: f64 = 1e-9;

/// Errors from certificate merge operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MergeError {
    /// The two certificates verify different properties.
    #[error("property mismatch: left={left}, right={right}")]
    PropertyMismatch { left: String, right: String },

    /// The two certificates have regions with different dimensionality.
    #[error("dimension mismatch: left={left}, right={right}")]
    DimensionMismatch { left: usize, right: usize },

    /// The split dimension is out of bounds.
    #[error("split dimension {dim} out of bounds for {ndim}-dimensional region")]
    SplitDimOutOfBounds { dim: usize, ndim: usize },

    /// The two regions do not share matching bounds on all non-split dimensions.
    #[error("non-split dimension {dim} bounds mismatch: left=[{left_lo}, {left_hi}], right=[{right_lo}, {right_hi}]")]
    NonSplitBoundsMismatch {
        dim: usize,
        left_lo: f64,
        left_hi: f64,
        right_lo: f64,
        right_hi: f64,
    },

    /// The split point does not match the boundary between the two regions.
    #[error("split point mismatch on dimension {dim}: left upper={left_hi}, right lower={right_lo}, expected split at {split_val}")]
    SplitPointMismatch {
        dim: usize,
        left_hi: f64,
        right_lo: f64,
        split_val: f64,
    },

    /// One or both certificates are not verified.
    #[error("unverified certificate: left_verified={left}, right_verified={right}")]
    UnverifiedCertificate { left: bool, right: bool },
}

/// Axis-aligned bounding box for a region of the input space.
///
/// Each dimension has a `[lower, upper]` interval. A point is contained
/// in the region iff it lies within every dimension's interval.
#[derive(Debug, Clone, PartialEq)]
pub struct RegionBounds {
    /// Per-dimension bounds as (lower, upper) pairs.
    bounds: Vec<(f64, f64)>,
}

impl RegionBounds {
    /// Create region bounds from per-dimension `(lower, upper)` pairs.
    ///
    /// # Panics
    ///
    /// Panics if any lower bound exceeds its upper bound.
    #[must_use]
    pub fn new(bounds: Vec<(f64, f64)>) -> Self {
        for (i, &(lo, hi)) in bounds.iter().enumerate() {
            assert!(
                lo <= hi + EPSILON,
                "dimension {i}: lower bound {lo} exceeds upper bound {hi}"
            );
        }
        Self { bounds }
    }

    /// Number of dimensions.
    #[must_use]
    pub fn ndim(&self) -> usize {
        self.bounds.len()
    }

    /// Per-dimension bounds as (lower, upper) pairs.
    #[must_use]
    pub fn bounds(&self) -> &[(f64, f64)] {
        &self.bounds
    }

    /// Check if a point is contained in this region.
    #[must_use]
    pub fn contains(&self, point: &[f64]) -> bool {
        if point.len() != self.bounds.len() {
            return false;
        }
        self.bounds
            .iter()
            .zip(point.iter())
            .all(|(&(lo, hi), &x)| lo - EPSILON <= x && x <= hi + EPSILON)
    }

    /// Create a restricted region where dimension `dim` has upper bound
    /// clamped to `split_val`.
    #[must_use]
    pub fn restrict_upper(&self, dim: usize, split_val: f64) -> Self {
        let mut bounds = self.bounds.clone();
        if dim < bounds.len() {
            bounds[dim].1 = split_val;
        }
        Self { bounds }
    }

    /// Create a restricted region where dimension `dim` has lower bound
    /// raised to `split_val`.
    #[must_use]
    pub fn restrict_lower(&self, dim: usize, split_val: f64) -> Self {
        let mut bounds = self.bounds.clone();
        if dim < bounds.len() {
            bounds[dim].0 = split_val;
        }
        Self { bounds }
    }

    /// Check if two regions are adjacent along `dim` with a shared split point.
    ///
    /// Returns `Ok(split_val)` if the regions match on all non-split dimensions
    /// and share a boundary on the split dimension, `Err` otherwise.
    pub(crate) fn check_adjacency(&self, other: &Self, dim: usize) -> Result<f64, MergeError> {
        if self.ndim() != other.ndim() {
            return Err(MergeError::DimensionMismatch {
                left: self.ndim(),
                right: other.ndim(),
            });
        }
        if dim >= self.ndim() {
            return Err(MergeError::SplitDimOutOfBounds {
                dim,
                ndim: self.ndim(),
            });
        }

        // Non-split dimensions must match.
        for (i, (&(l_lo, l_hi), &(r_lo, r_hi))) in
            self.bounds.iter().zip(other.bounds.iter()).enumerate()
        {
            if i == dim {
                continue;
            }
            if (l_lo - r_lo).abs() > EPSILON || (l_hi - r_hi).abs() > EPSILON {
                return Err(MergeError::NonSplitBoundsMismatch {
                    dim: i,
                    left_lo: l_lo,
                    left_hi: l_hi,
                    right_lo: r_lo,
                    right_hi: r_hi,
                });
            }
        }

        // Split dimension: left upper must match right lower.
        let split_val = self.bounds[dim].1;
        if (split_val - other.bounds[dim].0).abs() > EPSILON {
            return Err(MergeError::SplitPointMismatch {
                dim,
                left_hi: self.bounds[dim].1,
                right_lo: other.bounds[dim].0,
                split_val,
            });
        }

        Ok(split_val)
    }

    /// Merge two adjacent regions into one encompassing region.
    ///
    /// Assumes adjacency has been verified.
    pub(crate) fn merge_along(&self, other: &Self, dim: usize) -> Self {
        let mut bounds = self.bounds.clone();
        // Take the min lower and max upper on the split dimension.
        bounds[dim].0 = self.bounds[dim].0.min(other.bounds[dim].0);
        bounds[dim].1 = self.bounds[dim].1.max(other.bounds[dim].1);
        Self { bounds }
    }
}

impl fmt::Display for RegionBounds {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, &(lo, hi)) in self.bounds.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "[{lo:.4}, {hi:.4}]")?;
        }
        write!(f, "]")
    }
}

/// Property being verified by a partial certificate.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VerifiedProperty {
    /// Output bounds: network(x) lies within given bounds for all x in region.
    OutputBounds {
        /// Per-dimension output bounds as (lower, upper) pairs.
        output_bounds: Vec<(i64, i64)>,
    },
    /// Safety property: output class != adversarial_class for all x in region.
    RobustnessAgainst {
        /// The adversarial class index.
        adversarial_class: usize,
        /// The true class index.
        true_class: usize,
    },
    /// Generic labeled property.
    Custom {
        /// Human-readable property description.
        label: String,
    },
}

impl fmt::Display for VerifiedProperty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutputBounds { output_bounds } => {
                write!(f, "output_bounds({} dims)", output_bounds.len())
            }
            Self::RobustnessAgainst {
                adversarial_class,
                true_class,
            } => {
                write!(f, "robust(true={true_class}, adv={adversarial_class})")
            }
            Self::Custom { label } => write!(f, "custom({label})"),
        }
    }
}

/// A partial verification certificate for a bounded subregion of the input space.
///
/// Attests that all inputs within `region` satisfy `property`, as verified
/// by a particular method at a given trust level.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PartialCert {
    /// The subregion this certificate covers.
    pub region: RegionBounds,
    /// The property verified for this subregion.
    pub property: VerifiedProperty,
    /// Whether verification succeeded for this subregion.
    pub verified: bool,
    /// Trust level of the verification method.
    pub trust_level: ChainTrustLevel,
    /// Unique identifier for this partial certificate.
    pub cert_id: u64,
    /// Per-dimension output bounds computed by the verifier (if applicable).
    pub computed_output_bounds: Option<Vec<(f64, f64)>>,
}

/// Merge two adjacent partial certificates into one covering the combined region.
///
/// The two certificates must:
/// - Verify the same property
/// - Both be verified (verified == true)
/// - Have adjacent regions along `split_dim`
///
/// The merged certificate inherits the minimum trust level of the two inputs
/// (conservative composition, matching T72 axiom profile semantics).
///
/// # Errors
///
/// Returns [`MergeError`] if the certificates cannot be merged.
pub fn merge_certificates(
    left: &PartialCert,
    right: &PartialCert,
    split_dim: usize,
) -> Result<PartialCert, MergeError> {
    // Both must be verified.
    if !left.verified || !right.verified {
        return Err(MergeError::UnverifiedCertificate {
            left: left.verified,
            right: right.verified,
        });
    }

    // Must verify the same property.
    if left.property != right.property {
        return Err(MergeError::PropertyMismatch {
            left: left.property.to_string(),
            right: right.property.to_string(),
        });
    }

    // Check adjacency and get the split value.
    let _split_val = left.region.check_adjacency(&right.region, split_dim)?;

    // Merge regions.
    let merged_region = left.region.merge_along(&right.region, split_dim);

    // Conservative trust: minimum of the two.
    let merged_trust = left.trust_level.min(right.trust_level);

    // Merge output bounds if both present.
    let merged_output_bounds = match (&left.computed_output_bounds, &right.computed_output_bounds) {
        (Some(l), Some(r)) if l.len() == r.len() => {
            let merged: Vec<(f64, f64)> = l
                .iter()
                .zip(r.iter())
                .map(|(&(l_lo, l_hi), &(r_lo, r_hi))| (l_lo.min(r_lo), l_hi.max(r_hi)))
                .collect();
            Some(merged)
        }
        _ => None,
    };

    // Use a deterministic combined ID.
    let merged_id =
        left.cert_id ^ right.cert_id ^ (split_dim as u64).wrapping_mul(0x9E3779B97F4A7C15);

    Ok(PartialCert {
        region: merged_region,
        property: left.property.clone(),
        verified: true,
        trust_level: merged_trust,
        cert_id: merged_id,
        computed_output_bounds: merged_output_bounds,
    })
}
