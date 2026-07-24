// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for streaming verification certificates.

use super::super::certificate::ChainTrustLevel;
use super::bab::{verify_bab_tree, BabNode, BabSplitDim};
use super::partial_cert::{
    merge_certificates, MergeError, PartialCert, RegionBounds, VerifiedProperty,
};
use super::stream::{CertificateStream, StreamError, StreamStatus};

// ---------------------------------------------------------------------------
// Helper constructors
// ---------------------------------------------------------------------------

fn make_region(bounds: Vec<(f64, f64)>) -> RegionBounds {
    RegionBounds::new(bounds)
}

fn make_cert(region: RegionBounds, verified: bool, cert_id: u64) -> PartialCert {
    PartialCert {
        region,
        property: VerifiedProperty::RobustnessAgainst {
            adversarial_class: 1,
            true_class: 0,
        },
        verified,
        trust_level: ChainTrustLevel::Numerical,
        cert_id,
        computed_output_bounds: None,
    }
}

fn make_cert_with_trust(region: RegionBounds, trust: ChainTrustLevel, cert_id: u64) -> PartialCert {
    PartialCert {
        region,
        property: VerifiedProperty::RobustnessAgainst {
            adversarial_class: 1,
            true_class: 0,
        },
        verified: true,
        trust_level: trust,
        cert_id,
        computed_output_bounds: None,
    }
}

fn make_cert_with_output_bounds(
    region: RegionBounds,
    output_bounds: Vec<(f64, f64)>,
    cert_id: u64,
) -> PartialCert {
    // Use a fixed property so both sides match for merge testing.
    // The actual per-subregion output bounds go into computed_output_bounds.
    PartialCert {
        region,
        property: VerifiedProperty::OutputBounds {
            output_bounds: vec![(0, 10)],
        },
        verified: true,
        trust_level: ChainTrustLevel::Formal,
        cert_id,
        computed_output_bounds: Some(output_bounds),
    }
}

// ---------------------------------------------------------------------------
// RegionBounds tests
// ---------------------------------------------------------------------------

#[test]
fn test_region_bounds_contains_interior_point() {
    let r = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    assert!(r.contains(&[0.5, 0.5]));
}

#[test]
fn test_region_bounds_contains_boundary_point() {
    let r = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    assert!(r.contains(&[0.0, 1.0]));
    assert!(r.contains(&[1.0, 0.0]));
}

#[test]
fn test_region_bounds_excludes_exterior_point() {
    let r = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    assert!(!r.contains(&[1.5, 0.5]));
    assert!(!r.contains(&[-0.5, 0.5]));
}

#[test]
fn test_region_bounds_wrong_dimension() {
    let r = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    assert!(!r.contains(&[0.5]));
    assert!(!r.contains(&[0.5, 0.5, 0.5]));
}

#[test]
fn test_region_restrict_upper() {
    let r = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let restricted = r.restrict_upper(0, 0.5);
    assert!(restricted.contains(&[0.3, 0.5]));
    assert!(!restricted.contains(&[0.7, 0.5]));
}

#[test]
fn test_region_restrict_lower() {
    let r = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let restricted = r.restrict_lower(0, 0.5);
    assert!(restricted.contains(&[0.7, 0.5]));
    assert!(!restricted.contains(&[0.3, 0.5]));
}

#[test]
fn test_region_adjacency_valid() {
    let left = make_region(vec![(0.0, 0.5), (0.0, 1.0)]);
    let right = make_region(vec![(0.5, 1.0), (0.0, 1.0)]);
    let split = left.check_adjacency(&right, 0);
    assert!(split.is_ok());
    let split_val = split.expect("adjacency should succeed");
    assert!((split_val - 0.5).abs() < 1e-9);
}

#[test]
fn test_region_adjacency_dimension_mismatch() {
    let left = make_region(vec![(0.0, 0.5)]);
    let right = make_region(vec![(0.5, 1.0), (0.0, 1.0)]);
    let err = left.check_adjacency(&right, 0).expect_err("should fail");
    assert!(matches!(err, MergeError::DimensionMismatch { .. }));
}

#[test]
fn test_region_adjacency_non_split_mismatch() {
    let left = make_region(vec![(0.0, 0.5), (0.0, 1.0)]);
    let right = make_region(vec![(0.5, 1.0), (0.0, 0.8)]); // dim 1 mismatch
    let err = left.check_adjacency(&right, 0).expect_err("should fail");
    assert!(matches!(err, MergeError::NonSplitBoundsMismatch { .. }));
}

#[test]
fn test_region_adjacency_gap() {
    let left = make_region(vec![(0.0, 0.4), (0.0, 1.0)]);
    let right = make_region(vec![(0.6, 1.0), (0.0, 1.0)]);
    let err = left.check_adjacency(&right, 0).expect_err("should fail");
    assert!(matches!(err, MergeError::SplitPointMismatch { .. }));
}

#[test]
fn test_region_merge_along() {
    let left = make_region(vec![(0.0, 0.5), (0.0, 1.0)]);
    let right = make_region(vec![(0.5, 1.0), (0.0, 1.0)]);
    let merged = left.merge_along(&right, 0);
    assert_eq!(merged.ndim(), 2);
    let bounds = merged.bounds();
    assert!((bounds[0].0 - 0.0).abs() < 1e-9);
    assert!((bounds[0].1 - 1.0).abs() < 1e-9);
    assert!((bounds[1].0 - 0.0).abs() < 1e-9);
    assert!((bounds[1].1 - 1.0).abs() < 1e-9);
}

// ---------------------------------------------------------------------------
// PartialCert merge tests
// ---------------------------------------------------------------------------

#[test]
fn test_merge_certificates_valid() {
    let left = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), true, 1);
    let right = make_cert(make_region(vec![(0.5, 1.0), (0.0, 1.0)]), true, 2);

    let merged = merge_certificates(&left, &right, 0).expect("merge should succeed");
    assert!(merged.verified);
    let bounds = merged.region.bounds();
    assert!((bounds[0].0 - 0.0).abs() < 1e-9);
    assert!((bounds[0].1 - 1.0).abs() < 1e-9);
}

#[test]
fn test_merge_certificates_unverified_left() {
    let left = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), false, 1);
    let right = make_cert(make_region(vec![(0.5, 1.0), (0.0, 1.0)]), true, 2);

    let err = merge_certificates(&left, &right, 0).expect_err("should fail");
    assert!(matches!(err, MergeError::UnverifiedCertificate { .. }));
}

#[test]
fn test_merge_certificates_unverified_right() {
    let left = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), true, 1);
    let right = make_cert(make_region(vec![(0.5, 1.0), (0.0, 1.0)]), false, 2);

    let err = merge_certificates(&left, &right, 0).expect_err("should fail");
    assert!(matches!(err, MergeError::UnverifiedCertificate { .. }));
}

#[test]
fn test_merge_certificates_property_mismatch() {
    let mut left = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), true, 1);
    let right = make_cert(make_region(vec![(0.5, 1.0), (0.0, 1.0)]), true, 2);

    left.property = VerifiedProperty::Custom {
        label: "different".to_owned(),
    };

    let err = merge_certificates(&left, &right, 0).expect_err("should fail");
    assert!(matches!(err, MergeError::PropertyMismatch { .. }));
}

#[test]
fn test_merge_certificates_conservative_trust() {
    let left = make_cert_with_trust(
        make_region(vec![(0.0, 0.5), (0.0, 1.0)]),
        ChainTrustLevel::Formal,
        1,
    );
    let right = make_cert_with_trust(
        make_region(vec![(0.5, 1.0), (0.0, 1.0)]),
        ChainTrustLevel::Heuristic,
        2,
    );

    let merged = merge_certificates(&left, &right, 0).expect("merge should succeed");
    assert_eq!(merged.trust_level, ChainTrustLevel::Heuristic);
}

#[test]
fn test_merge_certificates_output_bounds_merged() {
    let left = make_cert_with_output_bounds(make_region(vec![(0.0, 0.5)]), vec![(1.0, 3.0)], 1);
    let right = make_cert_with_output_bounds(make_region(vec![(0.5, 1.0)]), vec![(2.0, 5.0)], 2);

    let merged = merge_certificates(&left, &right, 0).expect("merge should succeed");
    let out = merged
        .computed_output_bounds
        .expect("should have merged output bounds");
    assert!((out[0].0 - 1.0).abs() < 1e-9); // min(1.0, 2.0)
    assert!((out[0].1 - 5.0).abs() < 1e-9); // max(3.0, 5.0)
}

// ---------------------------------------------------------------------------
// BaB tree tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_bab_tree_single_leaf() {
    let root_region = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let tree = BabNode::Leaf {
        cert: make_cert(root_region.clone(), true, 1),
    };

    verify_bab_tree(&tree, &root_region).expect("single verified leaf should pass");
}

#[test]
fn test_verify_bab_tree_unverified_leaf() {
    let root_region = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let tree = BabNode::Leaf {
        cert: make_cert(root_region.clone(), false, 1),
    };

    let err = verify_bab_tree(&tree, &root_region).expect_err("should fail");
    assert!(matches!(
        err,
        super::bab::BabTreeError::UnverifiedLeaf { .. }
    ));
}

#[test]
fn test_verify_bab_tree_one_split() {
    let root_region = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let left_region = root_region.restrict_upper(0, 0.5);
    let right_region = root_region.restrict_lower(0, 0.5);

    let tree = BabNode::Interior {
        region: root_region.clone(),
        split: BabSplitDim {
            dim: 0,
            split_val: 0.5,
        },
        left: Box::new(BabNode::Leaf {
            cert: make_cert(left_region, true, 1),
        }),
        right: Box::new(BabNode::Leaf {
            cert: make_cert(right_region, true, 2),
        }),
    };

    verify_bab_tree(&tree, &root_region).expect("valid single-split tree should pass");
}

#[test]
fn test_verify_bab_tree_two_levels() {
    let root_region = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let left_region = root_region.restrict_upper(0, 0.5);
    let right_region = root_region.restrict_lower(0, 0.5);

    // Further split left along dim 1
    let left_left = left_region.restrict_upper(1, 0.5);
    let left_right = left_region.restrict_lower(1, 0.5);

    let tree = BabNode::Interior {
        region: root_region.clone(),
        split: BabSplitDim {
            dim: 0,
            split_val: 0.5,
        },
        left: Box::new(BabNode::Interior {
            region: left_region,
            split: BabSplitDim {
                dim: 1,
                split_val: 0.5,
            },
            left: Box::new(BabNode::Leaf {
                cert: make_cert(left_left, true, 1),
            }),
            right: Box::new(BabNode::Leaf {
                cert: make_cert(left_right, true, 2),
            }),
        }),
        right: Box::new(BabNode::Leaf {
            cert: make_cert(right_region, true, 3),
        }),
    };

    verify_bab_tree(&tree, &root_region).expect("valid two-level tree should pass");
    assert_eq!(tree.leaf_count(), 3);
    assert_eq!(tree.depth(), 2);
    assert!(tree.all_verified());
}

#[test]
fn test_verify_bab_tree_region_mismatch() {
    let root_region = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let wrong_region = make_region(vec![(0.0, 2.0), (0.0, 1.0)]); // wrong!

    let tree = BabNode::Leaf {
        cert: make_cert(wrong_region, true, 1),
    };

    let err = verify_bab_tree(&tree, &root_region).expect_err("should fail");
    assert!(matches!(
        err,
        super::bab::BabTreeError::RegionMismatch { .. }
    ));
}

#[test]
fn test_verify_bab_tree_split_dim_out_of_bounds() {
    let root_region = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);

    let tree = BabNode::Interior {
        region: root_region.clone(),
        split: BabSplitDim {
            dim: 5, // out of bounds for 2D region
            split_val: 0.5,
        },
        left: Box::new(BabNode::Leaf {
            cert: make_cert(root_region.clone(), true, 1),
        }),
        right: Box::new(BabNode::Leaf {
            cert: make_cert(root_region.clone(), true, 2),
        }),
    };

    let err = verify_bab_tree(&tree, &root_region).expect_err("should fail");
    assert!(matches!(
        err,
        super::bab::BabTreeError::SplitDimOutOfBounds { .. }
    ));
}

#[test]
fn test_verify_bab_tree_split_val_out_of_region() {
    let root_region = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);

    let tree = BabNode::Interior {
        region: root_region.clone(),
        split: BabSplitDim {
            dim: 0,
            split_val: 5.0, // outside [0,1]
        },
        left: Box::new(BabNode::Leaf {
            cert: make_cert(root_region.clone(), true, 1),
        }),
        right: Box::new(BabNode::Leaf {
            cert: make_cert(root_region.clone(), true, 2),
        }),
    };

    let err = verify_bab_tree(&tree, &root_region).expect_err("should fail");
    assert!(matches!(err, super::bab::BabTreeError::SplitError { .. }));
}

#[test]
fn test_bab_node_leaf_count_and_depth() {
    let leaf = BabNode::Leaf {
        cert: make_cert(make_region(vec![(0.0, 1.0)]), true, 1),
    };
    assert_eq!(leaf.leaf_count(), 1);
    assert_eq!(leaf.depth(), 0);
}

// ---------------------------------------------------------------------------
// CertificateStream tests
// ---------------------------------------------------------------------------

#[test]
fn test_stream_empty_status() {
    let target = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let stream = CertificateStream::new(target, "net1");
    assert!(stream.is_empty());
    assert_eq!(stream.len(), 0);
    assert!(matches!(stream.status(), StreamStatus::Empty));
}

#[test]
fn test_stream_append_verified() {
    let target = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let mut stream = CertificateStream::new(target.clone(), "net1");

    let cert = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), true, 1);
    stream.append(cert).expect("append should succeed");
    assert_eq!(stream.len(), 1);
}

#[test]
fn test_stream_reject_unverified() {
    let target = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let mut stream = CertificateStream::new(target, "net1");

    let cert = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), false, 1);
    let err = stream.append(cert).expect_err("should reject unverified");
    assert!(matches!(err, StreamError::UnverifiedCertificate { .. }));
}

#[test]
fn test_stream_reject_out_of_bounds() {
    let target = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let mut stream = CertificateStream::new(target, "net1");

    let cert = make_cert(
        make_region(vec![(0.0, 2.0), (0.0, 1.0)]), // exceeds target
        true,
        1,
    );
    let err = stream
        .append(cert)
        .expect_err("should reject out of bounds");
    assert!(matches!(err, StreamError::RegionOutOfBounds { .. }));
}

#[test]
fn test_stream_partial_coverage() {
    let target = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let mut stream = CertificateStream::new(target, "net1");

    // Only cover half the region.
    let cert = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), true, 1);
    stream.append(cert).expect("append should succeed");

    assert!(matches!(
        stream.status(),
        StreamStatus::Partial { verified_count: 1 }
    ));
}

#[test]
fn test_stream_complete_coverage_two_halves() {
    let target = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let mut stream = CertificateStream::new(target, "net1");

    let left = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), true, 1);
    let right = make_cert(make_region(vec![(0.5, 1.0), (0.0, 1.0)]), true, 2);

    stream.append(left).expect("left append should succeed");
    stream.append(right).expect("right append should succeed");

    assert!(matches!(
        stream.status(),
        StreamStatus::Complete { total_certs: 2 }
    ));
}

#[test]
fn test_stream_complete_coverage_four_quadrants() {
    let target = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let mut stream = CertificateStream::new(target, "net1");

    // Four quadrants: split dim 0 at 0.5, then dim 1 at 0.5.
    let q1 = make_cert(make_region(vec![(0.0, 0.5), (0.0, 0.5)]), true, 1);
    let q2 = make_cert(make_region(vec![(0.0, 0.5), (0.5, 1.0)]), true, 2);
    let q3 = make_cert(make_region(vec![(0.5, 1.0), (0.0, 0.5)]), true, 3);
    let q4 = make_cert(make_region(vec![(0.5, 1.0), (0.5, 1.0)]), true, 4);

    stream.append(q1).expect("q1 append should succeed");
    stream.append(q2).expect("q2 append should succeed");
    stream.append(q3).expect("q3 append should succeed");
    stream.append(q4).expect("q4 append should succeed");

    assert!(matches!(
        stream.status(),
        StreamStatus::Complete { total_certs: 4 }
    ));
}

#[test]
fn test_stream_try_merge_all_two_halves() {
    let target = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let mut stream = CertificateStream::new(target.clone(), "net1");

    let left = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), true, 1);
    let right = make_cert(make_region(vec![(0.5, 1.0), (0.0, 1.0)]), true, 2);

    stream.append(left).expect("left append should succeed");
    stream.append(right).expect("right append should succeed");

    let merged = stream.try_merge_all().expect("merge should succeed");
    assert!(merged.verified);
    let bounds = merged.region.bounds();
    assert!((bounds[0].0 - 0.0).abs() < 1e-9);
    assert!((bounds[0].1 - 1.0).abs() < 1e-9);
    assert!((bounds[1].0 - 0.0).abs() < 1e-9);
    assert!((bounds[1].1 - 1.0).abs() < 1e-9);
}

#[test]
fn test_stream_network_id() {
    let target = make_region(vec![(0.0, 1.0)]);
    let stream = CertificateStream::new(target, "my_network");
    assert_eq!(stream.network_id(), "my_network");
}

#[test]
fn test_stream_status_display() {
    assert_eq!(StreamStatus::Empty.to_string(), "empty");
    assert_eq!(
        StreamStatus::Partial { verified_count: 3 }.to_string(),
        "partial(3 certs)"
    );
    assert_eq!(
        StreamStatus::Complete { total_certs: 5 }.to_string(),
        "complete(5 certs)"
    );
}

// ---------------------------------------------------------------------------
// VerifiedProperty tests
// ---------------------------------------------------------------------------

#[test]
fn test_verified_property_display() {
    let ob = VerifiedProperty::OutputBounds {
        output_bounds: vec![(0, 10), (0, 10)],
    };
    assert!(ob.to_string().contains("2 dims"));

    let rob = VerifiedProperty::RobustnessAgainst {
        adversarial_class: 3,
        true_class: 7,
    };
    assert!(rob.to_string().contains("true=7"));
    assert!(rob.to_string().contains("adv=3"));

    let custom = VerifiedProperty::Custom {
        label: "my_prop".to_owned(),
    };
    assert!(custom.to_string().contains("my_prop"));
}

// ---------------------------------------------------------------------------
// Integration: BaB tree -> stream conversion
// ---------------------------------------------------------------------------

#[test]
fn test_bab_tree_leaves_feed_stream() {
    // Build a BaB tree with 4 leaves (2 splits).
    let root_region = make_region(vec![(0.0, 1.0), (0.0, 1.0)]);
    let left_region = root_region.restrict_upper(0, 0.5);
    let right_region = root_region.restrict_lower(0, 0.5);
    let ll = left_region.restrict_upper(1, 0.5);
    let lr = left_region.restrict_lower(1, 0.5);

    let c1 = make_cert(ll.clone(), true, 1);
    let c2 = make_cert(lr.clone(), true, 2);
    let c3 = make_cert(right_region.clone(), true, 3);

    let tree = BabNode::Interior {
        region: root_region.clone(),
        split: BabSplitDim {
            dim: 0,
            split_val: 0.5,
        },
        left: Box::new(BabNode::Interior {
            region: left_region.clone(),
            split: BabSplitDim {
                dim: 1,
                split_val: 0.5,
            },
            left: Box::new(BabNode::Leaf { cert: c1.clone() }),
            right: Box::new(BabNode::Leaf { cert: c2.clone() }),
        }),
        right: Box::new(BabNode::Leaf { cert: c3.clone() }),
    };

    // Verify the tree.
    verify_bab_tree(&tree, &root_region).expect("tree should verify");

    // Feed leaf certs into a stream.
    let mut stream = CertificateStream::new(root_region, "test_net");
    // Merge left two leaves first, then merge with right.
    let left_merged = merge_certificates(&c1, &c2, 1).expect("left merge should succeed");
    stream
        .append(left_merged)
        .expect("append merged left should succeed");
    stream.append(c3).expect("append right should succeed");

    assert!(matches!(
        stream.status(),
        StreamStatus::Complete { total_certs: 2 }
    ));
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_merge_1d_region() {
    let left = make_cert(make_region(vec![(0.0, 0.5)]), true, 1);
    let right = make_cert(make_region(vec![(0.5, 1.0)]), true, 2);

    let merged = merge_certificates(&left, &right, 0).expect("1D merge should succeed");
    assert!(merged.verified);
    let bounds = merged.region.bounds();
    assert!((bounds[0].0 - 0.0).abs() < 1e-9);
    assert!((bounds[0].1 - 1.0).abs() < 1e-9);
}

#[test]
fn test_merge_3d_region() {
    let left = make_cert(
        make_region(vec![(0.0, 0.5), (0.0, 1.0), (-1.0, 1.0)]),
        true,
        1,
    );
    let right = make_cert(
        make_region(vec![(0.5, 1.0), (0.0, 1.0), (-1.0, 1.0)]),
        true,
        2,
    );

    let merged = merge_certificates(&left, &right, 0).expect("3D merge should succeed");
    assert_eq!(merged.region.ndim(), 3);
}

#[test]
fn test_split_dim_out_of_bounds_for_merge() {
    let left = make_cert(make_region(vec![(0.0, 0.5), (0.0, 1.0)]), true, 1);
    let right = make_cert(make_region(vec![(0.5, 1.0), (0.0, 1.0)]), true, 2);

    let err = merge_certificates(&left, &right, 5).expect_err("should fail");
    assert!(matches!(err, MergeError::SplitDimOutOfBounds { .. }));
}

#[test]
fn test_region_display() {
    let r = make_region(vec![(0.0, 1.0), (2.0, 3.0)]);
    let s = r.to_string();
    assert!(s.contains("[0.0000, 1.0000]"));
    assert!(s.contains("[2.0000, 3.0000]"));
}
