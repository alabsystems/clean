// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LZ4 byte-level compression for proof certificates.
//!
//! Combines structure sharing (hash-consing) with LZ4 compression for
//! fast archiving with moderate compression ratios.

use serde::{Deserialize, Serialize};

use super::super::ProofCert;
use super::compress::compress_cert;
use super::decompress::decompress_cert;
use super::limits::{
    decode_certificate_bincode_limited, MAX_COMPRESSED_ARCHIVE_BYTES,
    MAX_UNCOMPRESSED_ARCHIVE_BYTES,
};
use super::types::CompressedCert;

/// Error during byte-level compression/decompression
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ByteCompressError {
    /// Failed to serialize to bincode
    #[error("Serialization error: {0}")]
    SerializeError(String),
    /// Failed to compress with LZ4
    #[error("LZ4 compression error: {0}")]
    CompressError(String),
    /// Failed to decompress with LZ4
    #[error("LZ4 decompression error: {0}")]
    DecompressError(String),
    /// Failed to deserialize from bincode
    #[error("Deserialization error: {0}")]
    DeserializeError(String),
    /// Data exceeds an archive resource limit.
    #[error("Data size {size} exceeds maximum {max} bytes")]
    SizeOverflow {
        /// Actual data size in bytes
        size: usize,
        /// Maximum allowed size in bytes
        max: u32,
    },
    /// Archive format version is unsupported.
    #[error("Unsupported archive version {found}; expected {expected}")]
    UnsupportedVersion {
        /// Version found in the archive.
        found: u8,
        /// Version supported by this decoder.
        expected: u8,
    },
}

/// Convert a usize to u32, returning an error if it would overflow.
#[inline]
fn usize_to_u32(size: usize) -> Result<u32, ByteCompressError> {
    u32::try_from(size).map_err(|_| ByteCompressError::SizeOverflow {
        size,
        max: u32::MAX,
    })
}

fn ensure_size(size: usize, max: usize) -> Result<(), ByteCompressError> {
    if size <= max {
        Ok(())
    } else {
        Err(ByteCompressError::SizeOverflow {
            size,
            max: max as u32,
        })
    }
}

/// A certificate archive with byte-level LZ4 compression.
///
/// Combines structure sharing (hash-consing) via `CompressedCert`
/// with LZ4 byte-level compression. Ideal for archiving proofs to
/// disk or network transmission.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertArchive {
    /// LZ4-compressed bincode serialization of `CompressedCert`
    pub compressed_data: Vec<u8>,
    /// Uncompressed size for allocation hint
    pub uncompressed_size: u32,
    /// Archive format version
    pub version: u8,
}

impl CertArchive {
    /// Archive format version
    ///
    /// Version 2 preserves binder multiplicity and let-binding metadata in
    /// compressed expressions. Version 1 is rejected rather than decoded
    /// lossily.
    pub const VERSION: u8 = 2;
}

/// Statistics about archive compression
#[derive(Debug, Clone)]
pub struct ArchiveStats {
    /// Original certificate size (bincode)
    pub original_cert_bytes: usize,
    /// After structure sharing (bincode `CompressedCert`)
    pub structure_shared_bytes: usize,
    /// After LZ4 compression
    pub archive_bytes: usize,
    /// Structure sharing ratio (`original` / `structure_shared`)
    pub structure_ratio: f64,
    /// LZ4 ratio (`structure_shared` / `archive`)
    pub lz4_ratio: f64,
    /// Total ratio (original / archive)
    pub total_ratio: f64,
}

impl std::fmt::Display for ArchiveStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ArchiveStats {{ {} -> {} -> {} bytes (struct: {:.1}x, lz4: {:.1}x, total: {:.1}x) }}",
            self.original_cert_bytes,
            self.structure_shared_bytes,
            self.archive_bytes,
            self.structure_ratio,
            self.lz4_ratio,
            self.total_ratio
        )
    }
}

/// Create a certificate archive with maximum compression.
///
/// Combines structure sharing (hash-consing) with LZ4 byte-level compression.
pub fn archive_cert(cert: &ProofCert) -> Result<CertArchive, ByteCompressError> {
    let compressed =
        compress_cert(cert).map_err(|e| ByteCompressError::CompressError(e.to_string()))?;

    let bincode_bytes = bincode::serde::encode_to_vec(&compressed, bincode::config::standard())
        .map_err(|e| ByteCompressError::SerializeError(e.to_string()))?;
    ensure_size(bincode_bytes.len(), MAX_UNCOMPRESSED_ARCHIVE_BYTES)?;

    let uncompressed_size = usize_to_u32(bincode_bytes.len())?;

    let lz4_bytes = lz4_flex::compress_prepend_size(&bincode_bytes);
    ensure_size(lz4_bytes.len(), MAX_COMPRESSED_ARCHIVE_BYTES)?;

    Ok(CertArchive {
        compressed_data: lz4_bytes,
        uncompressed_size,
        version: CertArchive::VERSION,
    })
}

/// Restore a certificate from an archive.
pub fn unarchive_cert(archive: &CertArchive) -> Result<ProofCert, ByteCompressError> {
    if archive.version != CertArchive::VERSION {
        return Err(ByteCompressError::UnsupportedVersion {
            found: archive.version,
            expected: CertArchive::VERSION,
        });
    }
    ensure_size(archive.compressed_data.len(), MAX_COMPRESSED_ARCHIVE_BYTES)?;
    let prefix = archive
        .compressed_data
        .get(..4)
        .ok_or_else(|| ByteCompressError::DecompressError("missing LZ4 size prefix".to_string()))?;
    let encoded_size = u32::from_le_bytes(prefix.try_into().expect("four-byte LZ4 size prefix"));
    if encoded_size != archive.uncompressed_size {
        return Err(ByteCompressError::DecompressError(format!(
            "declared size {} does not match LZ4 size prefix {encoded_size}",
            archive.uncompressed_size
        )));
    }
    ensure_size(encoded_size as usize, MAX_UNCOMPRESSED_ARCHIVE_BYTES)?;

    let bincode_bytes = decompress_canonical_lz4(&archive.compressed_data)?;

    let compressed: CompressedCert = decode_certificate_bincode_limited(&bincode_bytes)
        .map_err(ByteCompressError::DeserializeError)?;

    decompress_cert(&compressed).map_err(|e| ByteCompressError::DeserializeError(e.to_string()))
}

/// Archive a certificate and return compression statistics.
pub fn archive_cert_with_stats(
    cert: &ProofCert,
) -> Result<(CertArchive, ArchiveStats), ByteCompressError> {
    let original_bytes = bincode::serde::encode_to_vec(cert, bincode::config::standard())
        .map_err(|e| ByteCompressError::SerializeError(e.to_string()))?;
    let original_cert_bytes = original_bytes.len();

    let compressed =
        compress_cert(cert).map_err(|e| ByteCompressError::CompressError(e.to_string()))?;
    let structure_bytes = bincode::serde::encode_to_vec(&compressed, bincode::config::standard())
        .map_err(|e| ByteCompressError::SerializeError(e.to_string()))?;
    ensure_size(structure_bytes.len(), MAX_UNCOMPRESSED_ARCHIVE_BYTES)?;
    let structure_shared_bytes = structure_bytes.len();

    let lz4_bytes = lz4_flex::compress_prepend_size(&structure_bytes);
    ensure_size(lz4_bytes.len(), MAX_COMPRESSED_ARCHIVE_BYTES)?;
    let archive_bytes = lz4_bytes.len();

    let archive = CertArchive {
        compressed_data: lz4_bytes,
        uncompressed_size: usize_to_u32(structure_shared_bytes)?,
        version: CertArchive::VERSION,
    };

    let structure_ratio = if structure_shared_bytes > 0 {
        original_cert_bytes as f64 / structure_shared_bytes as f64
    } else {
        1.0
    };

    let lz4_ratio = if archive_bytes > 0 {
        structure_shared_bytes as f64 / archive_bytes as f64
    } else {
        1.0
    };

    let total_ratio = if archive_bytes > 0 {
        original_cert_bytes as f64 / archive_bytes as f64
    } else {
        1.0
    };

    let stats = ArchiveStats {
        original_cert_bytes,
        structure_shared_bytes,
        archive_bytes,
        structure_ratio,
        lz4_ratio,
        total_ratio,
    };

    Ok((archive, stats))
}

/// Compress raw bytes with LZ4 (low-level utility).
pub fn lz4_compress(data: &[u8]) -> Vec<u8> {
    lz4_flex::compress_prepend_size(data)
}

/// Decompress LZ4-compressed bytes (low-level utility).
pub fn lz4_decompress(data: &[u8]) -> Result<Vec<u8>, ByteCompressError> {
    ensure_size(data.len(), MAX_COMPRESSED_ARCHIVE_BYTES)?;
    let prefix = data
        .get(..4)
        .ok_or_else(|| ByteCompressError::DecompressError("missing LZ4 size prefix".to_string()))?;
    let encoded_size = u32::from_le_bytes(prefix.try_into().expect("four-byte LZ4 size prefix"));
    ensure_size(encoded_size as usize, MAX_UNCOMPRESSED_ARCHIVE_BYTES)?;
    decompress_canonical_lz4(data)
}

fn decompress_canonical_lz4(data: &[u8]) -> Result<Vec<u8>, ByteCompressError> {
    let output = lz4_flex::decompress_size_prepended(data)
        .map_err(|e| ByteCompressError::DecompressError(e.to_string()))?;
    // The block API does not report consumed input.  This carrier is produced
    // by `compress_prepend_size`, so require its deterministic canonical form
    // to reject appended or alternate trailing block bytes.
    if lz4_flex::compress_prepend_size(&output) != data {
        return Err(ByteCompressError::DecompressError(
            "non-canonical or trailing LZ4 block bytes".to_string(),
        ));
    }
    Ok(output)
}
