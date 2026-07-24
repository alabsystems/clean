// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate stream: an ordered, incrementally-extendable sequence of
//! partial certificates.
//!
//! A [`CertificateStream`] collects partial certs as they arrive from a
//! BaB verifier. Once all subregions are covered, the stream constitutes
//! a complete proof (T83).

use std::fmt;

use thiserror::Error;

use super::partial_cert::{merge_certificates, MergeError, PartialCert, RegionBounds};

/// Errors from certificate stream operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum StreamError {
    /// The appended certificate does not match the stream's target region.
    #[error("certificate region is not a subregion of the target: cert={cert_region}, target={target_region}")]
    RegionOutOfBounds {
        cert_region: String,
        target_region: String,
    },

    /// The appended certificate is not verified.
    #[error("cannot append unverified certificate (cert_id={cert_id})")]
    UnverifiedCertificate { cert_id: u64 },

    /// Merge of adjacent certificates failed.
    #[error("merge failed: {0}")]
    MergeFailed(#[from] MergeError),
}

/// Status of a certificate stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum StreamStatus {
    /// No certificates have been added yet.
    Empty,
    /// Some subregions are covered but the target is not fully covered.
    Partial {
        /// Number of verified partial certificates.
        verified_count: usize,
    },
    /// The entire target region is covered by verified certificates.
    Complete {
        /// Total number of partial certificates that cover the region.
        total_certs: usize,
    },
}

impl fmt::Display for StreamStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "empty"),
            Self::Partial { verified_count } => write!(f, "partial({verified_count} certs)"),
            Self::Complete { total_certs } => write!(f, "complete({total_certs} certs)"),
        }
    }
}

/// Tolerance for floating-point bound comparisons.
const EPSILON: f64 = 1e-9;

/// An incrementally-extendable sequence of partial verification certificates.
///
/// Certificates are appended as the BaB verifier completes subregions.
/// The stream tracks coverage of the target region and reports when the
/// proof is complete.
#[derive(Debug, Clone)]
pub struct CertificateStream {
    /// The full region we aim to cover.
    target_region: RegionBounds,
    /// Accumulated partial certificates (in arrival order).
    certs: Vec<PartialCert>,
    /// Network identifier.
    network_id: String,
}

impl CertificateStream {
    /// Create a new empty certificate stream for a target region.
    #[must_use]
    pub fn new(target_region: RegionBounds, network_id: &str) -> Self {
        Self {
            target_region,
            certs: Vec::new(),
            network_id: network_id.to_owned(),
        }
    }

    /// The target region this stream aims to cover.
    #[must_use]
    pub fn target_region(&self) -> &RegionBounds {
        &self.target_region
    }

    /// The network identifier.
    #[must_use]
    pub fn network_id(&self) -> &str {
        &self.network_id
    }

    /// The currently accumulated certificates.
    #[must_use]
    pub fn certs(&self) -> &[PartialCert] {
        &self.certs
    }

    /// Number of certificates in the stream.
    #[must_use]
    pub fn len(&self) -> usize {
        self.certs.len()
    }

    /// Whether the stream has no certificates.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.certs.is_empty()
    }

    /// Append a verified partial certificate to the stream.
    ///
    /// The certificate must be verified and its region must be a subregion
    /// of the target.
    ///
    /// # Errors
    ///
    /// Returns [`StreamError`] if the certificate is invalid for this stream.
    pub fn append(&mut self, cert: PartialCert) -> Result<(), StreamError> {
        if !cert.verified {
            return Err(StreamError::UnverifiedCertificate {
                cert_id: cert.cert_id,
            });
        }

        if !is_subregion(&cert.region, &self.target_region) {
            return Err(StreamError::RegionOutOfBounds {
                cert_region: cert.region.to_string(),
                target_region: self.target_region.to_string(),
            });
        }

        self.certs.push(cert);
        Ok(())
    }

    /// Current status of the stream.
    ///
    /// Checks whether the accumulated certificates collectively cover
    /// the target region. Coverage is checked by attempting to merge
    /// all certificates along each dimension.
    #[must_use]
    pub fn status(&self) -> StreamStatus {
        if self.certs.is_empty() {
            return StreamStatus::Empty;
        }

        if self.check_coverage() {
            StreamStatus::Complete {
                total_certs: self.certs.len(),
            }
        } else {
            StreamStatus::Partial {
                verified_count: self.certs.len(),
            }
        }
    }

    /// Attempt to merge all certificates into a single certificate covering
    /// the target region.
    ///
    /// Tries successive merges along each dimension. Returns the merged
    /// certificate if successful.
    ///
    /// # Errors
    ///
    /// Returns [`StreamError::MergeFailed`] if the certificates cannot be
    /// merged into a single covering certificate.
    pub fn try_merge_all(&self) -> Result<PartialCert, StreamError> {
        if self.certs.is_empty() {
            return Err(StreamError::MergeFailed(MergeError::DimensionMismatch {
                left: 0,
                right: 0,
            }));
        }

        let mut working = self.certs.clone();

        // Iteratively try to merge adjacent pairs along each dimension.
        let ndim = self.target_region.ndim();
        let mut made_progress = true;

        while working.len() > 1 && made_progress {
            made_progress = false;
            for dim in 0..ndim {
                let merged_round = try_merge_pass(&working, dim);
                if merged_round.len() < working.len() {
                    working = merged_round;
                    made_progress = true;
                }
            }
        }

        if working.len() == 1 {
            Ok(working.into_iter().next().expect("invariant: len == 1"))
        } else {
            Err(StreamError::MergeFailed(MergeError::DimensionMismatch {
                left: working.len(),
                right: 1,
            }))
        }
    }

    /// Check if accumulated certs cover the target region.
    ///
    /// Structurally merges all certs and verifies the merged region matches
    /// the target. A single cert that only covers part of the target will not
    /// pass the final region check even if `try_merge_all` returns it.
    fn check_coverage(&self) -> bool {
        match self.try_merge_all() {
            Ok(merged) => regions_match(&merged.region, &self.target_region),
            Err(_) => false,
        }
    }
}

/// Try one pass of merging adjacent certificates along `dim`.
///
/// Walks the list, attempting to merge each consecutive pair. Merged pairs
/// are replaced by their merged result; unmerged certs pass through.
fn try_merge_pass(certs: &[PartialCert], dim: usize) -> Vec<PartialCert> {
    let mut result = Vec::with_capacity(certs.len());
    let mut i = 0;

    while i < certs.len() {
        if i + 1 < certs.len() {
            // Try merging certs[i] with certs[i+1].
            if let Ok(merged) = merge_certificates(&certs[i], &certs[i + 1], dim) {
                result.push(merged);
                i += 2;
                continue;
            }
        }
        result.push(certs[i].clone());
        i += 1;
    }

    result
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

/// Check if `inner` is a subregion of `outer` (all bounds contained).
fn is_subregion(inner: &RegionBounds, outer: &RegionBounds) -> bool {
    if inner.ndim() != outer.ndim() {
        return false;
    }
    inner
        .bounds()
        .iter()
        .zip(outer.bounds().iter())
        .all(|(&(i_lo, i_hi), &(o_lo, o_hi))| i_lo >= o_lo - EPSILON && i_hi <= o_hi + EPSILON)
}
