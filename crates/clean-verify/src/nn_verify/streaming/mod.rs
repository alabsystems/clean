// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Streaming verification certificates for incremental Branch-and-Bound (BaB)
//! proofs (C007: T80-T83).
//!
//! Branch-and-bound neural network verifiers produce results incrementally:
//! each split of the input space refines bounds and can produce a partial
//! verification certificate. This module formalizes how partial certificates
//! are combined into a complete proof.
//!
//! ## Architecture
//!
//! - [`PartialCert`]: Certificate for a single subregion of the input space
//! - [`CertificateStream`]: Ordered sequence of partial certs covering the
//!   full input space
//! - [`merge_certificates`]: Combine two adjacent partial certs whose regions
//!   together cover a larger region
//! - [`BabNode`]: A node in the BaB tree with bounds, split info, and children
//! - [`verify_bab_tree`]: Verify a complete BaB tree certificate
//!
//! ## Soundness Argument
//!
//! T80 (partial_cert_sound): A partial certificate for subregion R proves
//! that all inputs in R satisfy the property.
//!
//! T81 (merge_certs_sound): If partial certs cover adjacent subregions R1, R2
//! that together form R, then the merged certificate proves the property for R.
//!
//! T82 (bab_tree_sound): A complete BaB tree whose leaves all have valid
//! partial certificates proves the property for the root region.
//!
//! T83 (stream_completeness): A certificate stream covering the entire input
//! space (verified via region partitioning) constitutes a complete proof.

pub(crate) mod bab;
pub(crate) mod partial_cert;
pub(crate) mod stream;

#[cfg(test)]
mod tests;

pub use bab::{verify_bab_tree, BabNode, BabSplitDim, BabTreeError};
pub use partial_cert::{
    merge_certificates, MergeError, PartialCert, RegionBounds, VerifiedProperty,
};
pub use stream::{CertificateStream, StreamError, StreamStatus};

use crate::spec::ProofStatus;

/// T80: partial_cert_sound
///
/// A partial certificate for subregion R proves that all inputs x in R
/// satisfy the verified property P.
///
/// ```text
/// theorem partial_cert_sound (cert : PartialCert) (R : RegionBounds d)
///   (h_region : cert.region = R) (h_valid : cert.verified = true) :
///   forall x, R.contains x -> P x
/// ```
pub const T80_PARTIAL_CERT_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T81: merge_certs_sound
///
/// If two partial certificates cover adjacent subregions R1 and R2 that
/// partition a larger region R along a split dimension, then the merged
/// certificate proves the property for all of R.
///
/// ```text
/// theorem merge_certs_sound (c1 c2 : PartialCert) (R : RegionBounds d)
///   (dim : Fin d) (split_val : Rat)
///   (h1 : c1.region = R.restrict_upper dim split_val)
///   (h2 : c2.region = R.restrict_lower dim split_val)
///   (h_v1 : c1.verified) (h_v2 : c2.verified) :
///   forall x, R.contains x -> P x
/// ```
///
/// Proof: case split on whether x[dim] <= split_val or x[dim] > split_val.
/// In the first case, x is in R1, so c1 applies. In the second, x is in R2,
/// so c2 applies.
pub const T81_MERGE_CERTS_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T82: bab_tree_sound
///
/// A complete BaB tree whose leaf nodes all hold valid partial certificates
/// proves the property for the root region.
///
/// ```text
/// theorem bab_tree_sound (tree : BabNode) (R : RegionBounds d)
///   (h_root : tree.region = R)
///   (h_leaves : forall leaf in tree.leaves, leaf.cert.verified) :
///   forall x, R.contains x -> P x
/// ```
///
/// Proof: structural induction on the BaB tree. Base case: leaf node with
/// valid cert (by T80). Inductive case: interior node with two children
/// whose regions partition the parent (by T81 applied recursively).
pub const T82_BAB_TREE_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T83: stream_completeness
///
/// A certificate stream whose partial certs collectively cover the entire
/// input region constitutes a complete verification proof.
///
/// ```text
/// theorem stream_completeness (stream : CertificateStream)
///   (R : RegionBounds d)
///   (h_covers : stream.covers R)
///   (h_all_valid : forall cert in stream.certs, cert.verified) :
///   forall x, R.contains x -> P x
/// ```
///
/// Proof: for any x in R, by h_covers there exists a cert in stream.certs
/// whose region contains x. By h_all_valid that cert is verified, so by
/// T80 the property holds for x.
pub const T83_STREAM_COMPLETENESS: ProofStatus = ProofStatus::DerivedPending;

#[cfg(test)]
mod spec_tests {
    use super::*;

    #[test]
    fn test_streaming_proof_status_tracking() {
        assert!(matches!(
            T80_PARTIAL_CERT_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(T81_MERGE_CERTS_SOUND, ProofStatus::DerivedPending));
        assert!(matches!(T82_BAB_TREE_SOUND, ProofStatus::DerivedPending));
        assert!(matches!(
            T83_STREAM_COMPLETENESS,
            ProofStatus::DerivedPending
        ));
    }
}
