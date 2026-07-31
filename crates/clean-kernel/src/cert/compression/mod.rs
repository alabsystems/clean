// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate Compression
//!
//! This module provides compression utilities for proof certificates:
//! - Structure sharing (hash-consing) for deduplication
//! - LZ4 compression for byte-level compression
//! - Zstd compression with configurable levels
//! - Dictionary-based Zstd compression for domain-specific patterns
//! - Streaming compression for large certificate archives

pub mod compress;
mod compress_hash;
pub mod decompress;
pub mod dict;
pub(crate) mod limits;
pub mod lz4;
pub mod streaming;
pub mod types;
#[path = "zstd_backend.rs"]
pub mod zstd_backend;

use serde::{Deserialize, Serialize};

use super::ProofCert;

// Re-export types
pub use types::{
    CertIdx, CompressedCert, CompressedCertNode, CompressedCertSchema, CompressedExpr,
    CompressedLevel, CompressionStats, ExprIdx, LevelIdx,
};

// Re-export compression/decompression core
pub use compress::{compress_cert, compress_cert_with_stats, CompressError};
pub use decompress::{decompress_cert, DecompressError};

// Re-export LZ4 backend
pub use lz4::{
    archive_cert, archive_cert_with_stats, lz4_compress, lz4_decompress, unarchive_cert,
    ArchiveStats, ByteCompressError, CertArchive,
};

// Re-export Zstd backend
pub use zstd_backend::{
    zstd_archive_cert, zstd_archive_cert_level, zstd_archive_cert_with_stats,
    zstd_archive_cert_with_stats_level, zstd_compress, zstd_compress_level, zstd_decompress,
    zstd_unarchive_cert, ZstdArchiveStats, ZstdCertArchive, ZstdCompressError,
};

// Re-export dictionary backend
pub use dict::{
    zstd_archive_cert_with_dict, zstd_archive_cert_with_dict_level,
    zstd_archive_cert_with_dict_stats, zstd_archive_cert_with_dict_stats_level,
    zstd_compress_with_dict, zstd_compress_with_dict_level, zstd_decompress_with_dict,
    zstd_unarchive_cert_with_dict, CertDictionary, DictArchiveStats, DictCertArchive,
    DictCompressError, DictTrainError,
};

// Re-export streaming API
pub use streaming::{
    stream_certs_from_file, stream_certs_to_file, CompressionAlgorithm, StreamingArchiveHeader,
    StreamingCertReader, StreamingCertWriter, StreamingError, StreamingProgressCallback,
    StreamingStats,
};

// ============================================================================
// Algorithm Dispatch (Unified API)
// ============================================================================

/// Unified error type for certificate archiving across algorithms.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CertArchiveError {
    /// Error from LZ4-based archiving
    #[error("LZ4 archive error: {0}")]
    Lz4(#[from] ByteCompressError),
    /// Error from zstd-based archiving
    #[error("Zstd archive error: {0}")]
    Zstd(#[from] ZstdCompressError),
}

/// Statistics for any compression algorithm.
#[derive(Debug, Clone)]
pub enum ArchiveVariantStats {
    /// Statistics for LZ4 archives
    Lz4(ArchiveStats),
    /// Statistics for zstd archives
    Zstd(ZstdArchiveStats),
}

impl ArchiveVariantStats {
    /// Get the compression algorithm used.
    pub fn algorithm(&self) -> CompressionAlgorithm {
        match self {
            ArchiveVariantStats::Lz4(_) => CompressionAlgorithm::Lz4,
            ArchiveVariantStats::Zstd(stats) => {
                CompressionAlgorithm::from_zstd_level(stats.compression_level)
            }
        }
    }

    /// Get the total compression ratio (original / archive).
    pub fn total_ratio(&self) -> f64 {
        match self {
            ArchiveVariantStats::Lz4(stats) => stats.total_ratio,
            ArchiveVariantStats::Zstd(stats) => stats.total_ratio,
        }
    }

    /// Get the structure sharing ratio (original / structure_shared).
    pub fn structure_ratio(&self) -> f64 {
        match self {
            ArchiveVariantStats::Lz4(stats) => stats.structure_ratio,
            ArchiveVariantStats::Zstd(stats) => stats.structure_ratio,
        }
    }
}

impl std::fmt::Display for ArchiveVariantStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArchiveVariantStats::Lz4(stats) => {
                write!(f, "ArchiveVariantStats {{ algo: LZ4, {stats} }}")
            }
            ArchiveVariantStats::Zstd(stats) => {
                write!(f, "ArchiveVariantStats {{ algo: Zstd, {stats} }}")
            }
        }
    }
}

/// Envelope that records which compression algorithm produced the archive.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CertArchiveEnvelope {
    /// LZ4-compressed archive
    Lz4(CertArchive),
    /// Zstd-compressed archive
    Zstd(ZstdCertArchive),
}

impl CertArchiveEnvelope {
    /// Compression algorithm used for this archive.
    pub fn algorithm(&self) -> CompressionAlgorithm {
        match self {
            CertArchiveEnvelope::Lz4(_) => CompressionAlgorithm::Lz4,
            CertArchiveEnvelope::Zstd(archive) => {
                CompressionAlgorithm::from_zstd_level(archive.compression_level)
            }
        }
    }

    /// Size of the compressed payload in bytes.
    pub fn compressed_len(&self) -> usize {
        match self {
            CertArchiveEnvelope::Lz4(archive) => archive.compressed_data.len(),
            CertArchiveEnvelope::Zstd(archive) => archive.compressed_data.len(),
        }
    }

    /// Uncompressed size hint stored alongside the archive.
    pub fn uncompressed_size(&self) -> u32 {
        match self {
            CertArchiveEnvelope::Lz4(archive) => archive.uncompressed_size,
            CertArchiveEnvelope::Zstd(archive) => archive.uncompressed_size,
        }
    }
}

/// Archive a certificate using the selected compression algorithm.
pub fn archive_cert_with_algorithm(
    cert: &ProofCert,
    algorithm: CompressionAlgorithm,
) -> Result<CertArchiveEnvelope, CertArchiveError> {
    match algorithm {
        CompressionAlgorithm::Lz4 => archive_cert(cert)
            .map(CertArchiveEnvelope::Lz4)
            .map_err(CertArchiveError::from),
        CompressionAlgorithm::ZstdDefault
        | CompressionAlgorithm::ZstdHigh
        | CompressionAlgorithm::ZstdMax => {
            let level = algorithm
                .zstd_level()
                .unwrap_or(ZstdCertArchive::DEFAULT_LEVEL);
            zstd_archive_cert_level(cert, level)
                .map(CertArchiveEnvelope::Zstd)
                .map_err(CertArchiveError::from)
        }
    }
}

/// Archive a certificate with statistics for the selected algorithm.
pub fn archive_cert_with_algorithm_stats(
    cert: &ProofCert,
    algorithm: CompressionAlgorithm,
) -> Result<(CertArchiveEnvelope, ArchiveVariantStats), CertArchiveError> {
    match algorithm {
        CompressionAlgorithm::Lz4 => archive_cert_with_stats(cert)
            .map(|(archive, stats)| {
                (
                    CertArchiveEnvelope::Lz4(archive),
                    ArchiveVariantStats::Lz4(stats),
                )
            })
            .map_err(CertArchiveError::from),
        CompressionAlgorithm::ZstdDefault
        | CompressionAlgorithm::ZstdHigh
        | CompressionAlgorithm::ZstdMax => {
            let level = algorithm
                .zstd_level()
                .unwrap_or(ZstdCertArchive::DEFAULT_LEVEL);
            zstd_archive_cert_with_stats_level(cert, level)
                .map(|(archive, stats)| {
                    (
                        CertArchiveEnvelope::Zstd(archive),
                        ArchiveVariantStats::Zstd(stats),
                    )
                })
                .map_err(CertArchiveError::from)
        }
    }
}

/// Restore a certificate from any archive envelope.
pub fn unarchive_cert_envelope(
    archive: &CertArchiveEnvelope,
) -> Result<ProofCert, CertArchiveError> {
    match archive {
        CertArchiveEnvelope::Lz4(archive) => {
            unarchive_cert(archive).map_err(CertArchiveError::from)
        }
        CertArchiveEnvelope::Zstd(archive) => {
            zstd_unarchive_cert(archive).map_err(CertArchiveError::from)
        }
    }
}
