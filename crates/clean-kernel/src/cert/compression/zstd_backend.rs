// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zstd byte-level compression for proof certificates.
//!
//! Provides higher compression ratio than LZ4 at the cost of slower
//! compression/decompression speed. Ideal when storage size matters
//! more than latency.

use std::io::Read;

use serde::{Deserialize, Serialize};

use super::super::ProofCert;
use super::compress::compress_cert;
use super::decompress::decompress_cert;
use super::limits::{
    decode_certificate_bincode_limited, read_declared_bounded, read_unknown_bounded,
    MAX_COMPRESSED_ARCHIVE_BYTES, MAX_UNCOMPRESSED_ARCHIVE_BYTES,
};
use super::types::CompressedCert;

/// Error during zstd compression/decompression
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ZstdCompressError {
    /// Failed to serialize to bincode
    #[error("Serialization error: {0}")]
    SerializeError(String),
    /// Failed to compress with zstd
    #[error("Zstd compression error: {0}")]
    CompressError(String),
    /// Failed to decompress with zstd
    #[error("Zstd decompression error: {0}")]
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

/// Convert a usize to u32 for zstd archive format, returning an error if it would overflow.
#[inline]
fn usize_to_u32_zstd(size: usize) -> Result<u32, ZstdCompressError> {
    u32::try_from(size).map_err(|_| ZstdCompressError::SizeOverflow {
        size,
        max: u32::MAX,
    })
}

fn ensure_size(size: usize, max: usize) -> Result<(), ZstdCompressError> {
    if size <= max {
        Ok(())
    } else {
        Err(ZstdCompressError::SizeOverflow {
            size,
            max: max as u32,
        })
    }
}

/// A certificate archive with byte-level zstd compression.
///
/// Higher compression ratio than LZ4 at the cost of slower speed.
/// Combines structure sharing (hash-consing) with zstd byte-level compression.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZstdCertArchive {
    /// Zstd-compressed bincode serialization of `CompressedCert`
    pub compressed_data: Vec<u8>,
    /// Uncompressed size for allocation hint
    pub uncompressed_size: u32,
    /// Archive format version
    pub version: u8,
    /// Zstd compression level used (1-22, default 3)
    pub compression_level: i32,
}

impl ZstdCertArchive {
    /// Archive format version
    ///
    /// Version 2 preserves binder multiplicity and let-binding metadata in
    /// compressed expressions. Version 1 is rejected rather than decoded
    /// lossily.
    pub const VERSION: u8 = 2;
    /// Default compression level (balanced speed/ratio)
    pub const DEFAULT_LEVEL: i32 = 3;
    /// High compression level (better ratio, slower)
    pub const HIGH_LEVEL: i32 = 19;
    /// Maximum compression level
    pub const MAX_LEVEL: i32 = 22;
}

/// Statistics about zstd archive compression
#[derive(Debug, Clone)]
pub struct ZstdArchiveStats {
    /// Original certificate size (bincode)
    pub original_cert_bytes: usize,
    /// After structure sharing (bincode `CompressedCert`)
    pub structure_shared_bytes: usize,
    /// After zstd compression
    pub archive_bytes: usize,
    /// Structure sharing ratio (`original` / `structure_shared`)
    pub structure_ratio: f64,
    /// Zstd ratio (`structure_shared` / `archive`)
    pub zstd_ratio: f64,
    /// Total ratio (original / archive)
    pub total_ratio: f64,
    /// Compression level used
    pub compression_level: i32,
}

impl std::fmt::Display for ZstdArchiveStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ZstdArchiveStats {{ {} -> {} -> {} bytes (struct: {:.1}x, zstd[{}]: {:.1}x, total: {:.1}x) }}",
            self.original_cert_bytes,
            self.structure_shared_bytes,
            self.archive_bytes,
            self.structure_ratio,
            self.compression_level,
            self.zstd_ratio,
            self.total_ratio
        )
    }
}

/// Create a certificate archive with zstd compression (default level).
pub fn zstd_archive_cert(cert: &ProofCert) -> Result<ZstdCertArchive, ZstdCompressError> {
    zstd_archive_cert_level(cert, ZstdCertArchive::DEFAULT_LEVEL)
}

/// Create a certificate archive with zstd compression at a specific level.
pub fn zstd_archive_cert_level(
    cert: &ProofCert,
    level: i32,
) -> Result<ZstdCertArchive, ZstdCompressError> {
    let compressed =
        compress_cert(cert).map_err(|e| ZstdCompressError::CompressError(e.to_string()))?;

    let bincode_bytes = bincode::serde::encode_to_vec(&compressed, bincode::config::standard())
        .map_err(|e| ZstdCompressError::SerializeError(e.to_string()))?;
    ensure_size(bincode_bytes.len(), MAX_UNCOMPRESSED_ARCHIVE_BYTES)?;

    let uncompressed_size = usize_to_u32_zstd(bincode_bytes.len())?;

    let zstd_bytes = zstd::encode_all(bincode_bytes.as_slice(), level)
        .map_err(|e| ZstdCompressError::CompressError(e.to_string()))?;
    ensure_size(zstd_bytes.len(), MAX_COMPRESSED_ARCHIVE_BYTES)?;

    Ok(ZstdCertArchive {
        compressed_data: zstd_bytes,
        uncompressed_size,
        version: ZstdCertArchive::VERSION,
        compression_level: level,
    })
}

/// Restore a certificate from a zstd archive.
pub fn zstd_unarchive_cert(archive: &ZstdCertArchive) -> Result<ProofCert, ZstdCompressError> {
    if archive.version != ZstdCertArchive::VERSION {
        return Err(ZstdCompressError::UnsupportedVersion {
            found: archive.version,
            expected: ZstdCertArchive::VERSION,
        });
    }
    ensure_size(archive.compressed_data.len(), MAX_COMPRESSED_ARCHIVE_BYTES)?;
    let mut decoder = zstd::stream::Decoder::new(std::io::Cursor::new(&archive.compressed_data))
        .map_err(|e| ZstdCompressError::DecompressError(e.to_string()))?;
    decoder = decoder.single_frame();
    let bincode_bytes = read_declared_bounded(
        &mut decoder,
        archive.uncompressed_size as usize,
        MAX_UNCOMPRESSED_ARCHIVE_BYTES,
        "zstd certificate archive",
    )
    .map_err(ZstdCompressError::DecompressError)?;
    reject_trailing_zstd_input(&mut decoder)?;

    let compressed: CompressedCert = decode_certificate_bincode_limited(&bincode_bytes)
        .map_err(ZstdCompressError::DeserializeError)?;

    decompress_cert(&compressed).map_err(|e| ZstdCompressError::DeserializeError(e.to_string()))
}

/// Archive a certificate with zstd and return compression statistics.
pub fn zstd_archive_cert_with_stats(
    cert: &ProofCert,
) -> Result<(ZstdCertArchive, ZstdArchiveStats), ZstdCompressError> {
    zstd_archive_cert_with_stats_level(cert, ZstdCertArchive::DEFAULT_LEVEL)
}

/// Archive a certificate with zstd at a specific level and return statistics.
pub fn zstd_archive_cert_with_stats_level(
    cert: &ProofCert,
    level: i32,
) -> Result<(ZstdCertArchive, ZstdArchiveStats), ZstdCompressError> {
    let original_bytes = bincode::serde::encode_to_vec(cert, bincode::config::standard())
        .map_err(|e| ZstdCompressError::SerializeError(e.to_string()))?;
    let original_cert_bytes = original_bytes.len();

    let compressed =
        compress_cert(cert).map_err(|e| ZstdCompressError::CompressError(e.to_string()))?;
    let structure_bytes = bincode::serde::encode_to_vec(&compressed, bincode::config::standard())
        .map_err(|e| ZstdCompressError::SerializeError(e.to_string()))?;
    ensure_size(structure_bytes.len(), MAX_UNCOMPRESSED_ARCHIVE_BYTES)?;
    let structure_shared_bytes = structure_bytes.len();

    let zstd_bytes = zstd::encode_all(structure_bytes.as_slice(), level)
        .map_err(|e| ZstdCompressError::CompressError(e.to_string()))?;
    ensure_size(zstd_bytes.len(), MAX_COMPRESSED_ARCHIVE_BYTES)?;
    let archive_bytes = zstd_bytes.len();

    let archive = ZstdCertArchive {
        compressed_data: zstd_bytes,
        uncompressed_size: usize_to_u32_zstd(structure_shared_bytes)?,
        version: ZstdCertArchive::VERSION,
        compression_level: level,
    };

    let structure_ratio = if structure_shared_bytes > 0 {
        original_cert_bytes as f64 / structure_shared_bytes as f64
    } else {
        1.0
    };

    let zstd_ratio = if archive_bytes > 0 {
        structure_shared_bytes as f64 / archive_bytes as f64
    } else {
        1.0
    };

    let total_ratio = if archive_bytes > 0 {
        original_cert_bytes as f64 / archive_bytes as f64
    } else {
        1.0
    };

    let stats = ZstdArchiveStats {
        original_cert_bytes,
        structure_shared_bytes,
        archive_bytes,
        structure_ratio,
        zstd_ratio,
        total_ratio,
        compression_level: level,
    };

    Ok((archive, stats))
}

/// Compress raw bytes with zstd (low-level utility).
pub fn zstd_compress(data: &[u8]) -> Result<Vec<u8>, ZstdCompressError> {
    zstd_compress_level(data, ZstdCertArchive::DEFAULT_LEVEL)
}

/// Compress raw bytes with zstd at a specific level.
pub fn zstd_compress_level(data: &[u8], level: i32) -> Result<Vec<u8>, ZstdCompressError> {
    zstd::encode_all(data, level).map_err(|e| ZstdCompressError::CompressError(e.to_string()))
}

/// Decompress zstd-compressed bytes (low-level utility).
pub fn zstd_decompress(data: &[u8]) -> Result<Vec<u8>, ZstdCompressError> {
    ensure_size(data.len(), MAX_COMPRESSED_ARCHIVE_BYTES)?;
    let mut decoder = zstd::stream::Decoder::new(std::io::Cursor::new(data))
        .map_err(|e| ZstdCompressError::DecompressError(e.to_string()))?;
    decoder = decoder.single_frame();
    let output = read_unknown_bounded(&mut decoder, MAX_UNCOMPRESSED_ARCHIVE_BYTES, "zstd payload")
        .map_err(ZstdCompressError::DecompressError)?;
    reject_trailing_zstd_input(&mut decoder)?;
    Ok(output)
}

fn reject_trailing_zstd_input<R: Read>(
    decoder: &mut zstd::stream::Decoder<'_, std::io::BufReader<R>>,
) -> Result<(), ZstdCompressError> {
    let mut trailing = [0_u8; 1];
    if decoder
        .get_mut()
        .read(&mut trailing)
        .map_err(|error| ZstdCompressError::DecompressError(error.to_string()))?
        != 0
    {
        return Err(ZstdCompressError::DecompressError(
            "trailing bytes after zstd frame".to_string(),
        ));
    }
    Ok(())
}
