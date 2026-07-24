// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dictionary-based Zstd compression for proof certificates.
//!
//! Trained dictionaries improve compression ratios for small, similar data.
//! For proof certificates, training on a representative corpus can significantly
//! improve compression, especially for small proofs.

use serde::{Deserialize, Serialize};

use super::super::ProofCert;
use super::compress::compress_cert;
use super::decompress::decompress_cert;
use super::types::CompressedCert;

/// A trained dictionary for certificate compression.
///
/// Dictionaries improve compression ratios for small, similar data. For proof
/// certificates, training a dictionary on a corpus of representative certificates
/// can significantly improve compression, especially for small proofs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertDictionary {
    /// The raw dictionary bytes
    pub data: Vec<u8>,
    /// Dictionary ID for validation (hash of data)
    pub dict_id: u32,
    /// Number of samples used for training
    pub sample_count: usize,
    /// Target compression level this dictionary was trained for
    pub target_level: i32,
    /// Version for format compatibility
    pub version: u8,
}

impl CertDictionary {
    /// Current dictionary format version
    pub const VERSION: u8 = 1;

    /// Default dictionary size (32KB - good balance of size vs effectiveness)
    pub const DEFAULT_SIZE: usize = 32 * 1024;

    /// Minimum samples needed for effective training
    pub const MIN_SAMPLES: usize = 5;

    /// Create a dictionary from raw bytes.
    pub fn from_bytes(data: Vec<u8>, target_level: i32) -> Self {
        let dict_id = Self::compute_id(&data);
        CertDictionary {
            data,
            dict_id,
            sample_count: 0,
            target_level,
            version: Self::VERSION,
        }
    }

    /// Train a dictionary from a collection of proof certificates.
    pub fn train(
        samples: &[ProofCert],
        max_size: usize,
        level: i32,
    ) -> Result<Self, DictTrainError> {
        if samples.len() < Self::MIN_SAMPLES {
            return Err(DictTrainError::NotEnoughSamples {
                provided: samples.len(),
                minimum: Self::MIN_SAMPLES,
            });
        }

        let sample_bytes: Vec<Vec<u8>> = samples
            .iter()
            .map(|cert| {
                let compressed = compress_cert(cert).map_err(|e| {
                    DictTrainError::SerializeError(format!("Failed to compress sample: {e}"))
                })?;
                bincode::serde::encode_to_vec(&compressed, bincode::config::standard()).map_err(
                    |e| DictTrainError::SerializeError(format!("Failed to serialize sample: {e}")),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        let dict_data = zstd::dict::from_samples(&sample_bytes, max_size)
            .map_err(|e| DictTrainError::TrainError(e.to_string()))?;

        let dict_id = Self::compute_id(&dict_data);

        Ok(CertDictionary {
            data: dict_data,
            dict_id,
            sample_count: samples.len(),
            target_level: level,
            version: Self::VERSION,
        })
    }

    /// Train a dictionary from raw byte samples.
    pub fn train_from_bytes(
        samples: &[Vec<u8>],
        max_size: usize,
        level: i32,
    ) -> Result<Self, DictTrainError> {
        if samples.len() < Self::MIN_SAMPLES {
            return Err(DictTrainError::NotEnoughSamples {
                provided: samples.len(),
                minimum: Self::MIN_SAMPLES,
            });
        }

        let dict_data = zstd::dict::from_samples(samples, max_size)
            .map_err(|e| DictTrainError::TrainError(e.to_string()))?;

        let dict_id = Self::compute_id(&dict_data);

        Ok(CertDictionary {
            data: dict_data,
            dict_id,
            sample_count: samples.len(),
            target_level: level,
            version: Self::VERSION,
        })
    }

    /// Compute a dictionary ID from its data (simple hash for validation).
    fn compute_id(data: &[u8]) -> u32 {
        let mut hash: u32 = 2_166_136_261;
        for byte in data {
            hash ^= u32::from(*byte);
            hash = hash.wrapping_mul(16_777_619);
        }
        hash
    }

    /// Get the dictionary size in bytes.
    pub fn size(&self) -> usize {
        self.data.len()
    }

    /// Check if this dictionary was trained for a compatible level.
    pub fn is_compatible_level(&self, level: i32) -> bool {
        // `abs_diff` computes |target_level - level| as a u32 without overflow.
        // The naive `(self.target_level - level).abs()` overflows i32 when the
        // difference exceeds i32 range (e.g. `level == i32::MIN`), and
        // `i32::MIN.abs()` itself overflows — a real panic the Trust verifier flags.
        self.target_level.abs_diff(level) <= 5
    }
}

/// Errors during dictionary training.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum DictTrainError {
    /// Not enough samples for training
    #[error("Not enough samples for dictionary training: {provided} provided, {minimum} minimum")]
    NotEnoughSamples {
        /// Number of samples provided
        provided: usize,
        /// Minimum samples required
        minimum: usize,
    },
    /// Failed to serialize sample
    #[error("Serialization error: {0}")]
    SerializeError(String),
    /// Zstd training failed
    #[error("Dictionary training error: {0}")]
    TrainError(String),
}

/// A certificate archive compressed with a trained dictionary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DictCertArchive {
    /// Dictionary-compressed bincode serialization of CompressedCert
    pub compressed_data: Vec<u8>,
    /// Uncompressed size for allocation hint
    pub uncompressed_size: u32,
    /// Archive format version
    pub version: u8,
    /// Zstd compression level used
    pub compression_level: i32,
    /// Dictionary ID used for compression (for validation)
    pub dict_id: u32,
}

impl DictCertArchive {
    /// Archive format version
    pub const VERSION: u8 = 1;
}

/// Statistics about dictionary-compressed archive.
#[derive(Debug, Clone)]
pub struct DictArchiveStats {
    /// Original certificate size (bincode)
    pub original_cert_bytes: usize,
    /// After structure sharing (bincode CompressedCert)
    pub structure_shared_bytes: usize,
    /// After dictionary compression
    pub archive_bytes: usize,
    /// Structure sharing ratio (original / structure_shared)
    pub structure_ratio: f64,
    /// Dictionary compression ratio (structure_shared / archive)
    pub dict_ratio: f64,
    /// Total ratio (original / archive)
    pub total_ratio: f64,
    /// Compression level used
    pub compression_level: i32,
    /// Dictionary ID used
    pub dict_id: u32,
}

impl std::fmt::Display for DictArchiveStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "DictArchiveStats {{ {} -> {} -> {} bytes (struct: {:.1}x, dict[{}]: {:.1}x, total: {:.1}x) }}",
            self.original_cert_bytes,
            self.structure_shared_bytes,
            self.archive_bytes,
            self.structure_ratio,
            self.compression_level,
            self.dict_ratio,
            self.total_ratio
        )
    }
}

/// Error during dictionary compression/decompression.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum DictCompressError {
    /// Failed to serialize
    #[error("Serialization error: {0}")]
    SerializeError(String),
    /// Failed to compress
    #[error("Dict compression error: {0}")]
    CompressError(String),
    /// Failed to decompress
    #[error("Dict decompression error: {0}")]
    DecompressError(String),
    /// Failed to deserialize
    #[error("Deserialization error: {0}")]
    DeserializeError(String),
    /// Dictionary mismatch
    #[error("Dictionary ID mismatch: expected {expected:#x}, found {found:#x}")]
    DictMismatch {
        /// Expected dictionary ID
        expected: u32,
        /// Found dictionary ID
        found: u32,
    },
    /// Data too large to store in archive format (>4GB uncompressed)
    #[error("Data size {size} exceeds maximum {max} bytes")]
    SizeOverflow {
        /// Actual data size in bytes
        size: usize,
        /// Maximum allowed size in bytes
        max: u32,
    },
}

/// Convert a usize to u32 for dict archive format, returning an error if it would overflow.
#[inline]
fn usize_to_u32_dict(size: usize) -> Result<u32, DictCompressError> {
    u32::try_from(size).map_err(|_| DictCompressError::SizeOverflow {
        size,
        max: u32::MAX,
    })
}

/// Archive a certificate using dictionary compression.
pub fn zstd_archive_cert_with_dict(
    cert: &ProofCert,
    dict: &CertDictionary,
) -> Result<DictCertArchive, DictCompressError> {
    zstd_archive_cert_with_dict_level(cert, dict, dict.target_level)
}

/// Archive a certificate using dictionary compression at a specific level.
pub fn zstd_archive_cert_with_dict_level(
    cert: &ProofCert,
    dict: &CertDictionary,
    level: i32,
) -> Result<DictCertArchive, DictCompressError> {
    let compressed =
        compress_cert(cert).map_err(|e| DictCompressError::CompressError(e.to_string()))?;

    let bincode_bytes = bincode::serde::encode_to_vec(&compressed, bincode::config::standard())
        .map_err(|e| DictCompressError::SerializeError(e.to_string()))?;

    let uncompressed_size = usize_to_u32_dict(bincode_bytes.len())?;

    let mut output = Vec::new();
    {
        let mut encoder = zstd::stream::Encoder::with_dictionary(&mut output, level, &dict.data)
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
        std::io::Write::write_all(&mut encoder, &bincode_bytes)
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
        encoder
            .finish()
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
    }

    Ok(DictCertArchive {
        compressed_data: output,
        uncompressed_size,
        version: DictCertArchive::VERSION,
        compression_level: level,
        dict_id: dict.dict_id,
    })
}

/// Restore a certificate from a dictionary-compressed archive.
pub fn zstd_unarchive_cert_with_dict(
    archive: &DictCertArchive,
    dict: &CertDictionary,
) -> Result<ProofCert, DictCompressError> {
    if archive.dict_id != dict.dict_id {
        return Err(DictCompressError::DictMismatch {
            expected: archive.dict_id,
            found: dict.dict_id,
        });
    }

    let mut decompressed = Vec::with_capacity(archive.uncompressed_size as usize);
    {
        let mut decoder = zstd::stream::Decoder::with_dictionary(
            std::io::Cursor::new(&archive.compressed_data),
            &dict.data,
        )
        .map_err(|e| DictCompressError::DecompressError(e.to_string()))?;
        std::io::Read::read_to_end(&mut decoder, &mut decompressed)
            .map_err(|e| DictCompressError::DecompressError(e.to_string()))?;
    }

    let compressed_cert: CompressedCert =
        bincode::serde::decode_from_slice(&decompressed, bincode::config::standard())
            .map(|(__v, _)| __v)
            .map_err(|e| DictCompressError::DeserializeError(e.to_string()))?;

    decompress_cert(&compressed_cert)
        .map_err(|e| DictCompressError::DeserializeError(format!("Structure decompress: {e}")))
}

/// Archive a certificate with dictionary and return compression statistics.
pub fn zstd_archive_cert_with_dict_stats(
    cert: &ProofCert,
    dict: &CertDictionary,
) -> Result<(DictCertArchive, DictArchiveStats), DictCompressError> {
    zstd_archive_cert_with_dict_stats_level(cert, dict, dict.target_level)
}

/// Archive a certificate with dictionary at a specific level and return statistics.
pub fn zstd_archive_cert_with_dict_stats_level(
    cert: &ProofCert,
    dict: &CertDictionary,
    level: i32,
) -> Result<(DictCertArchive, DictArchiveStats), DictCompressError> {
    let original_bytes = bincode::serde::encode_to_vec(cert, bincode::config::standard())
        .map_err(|e| DictCompressError::SerializeError(e.to_string()))?;
    let original_cert_bytes = original_bytes.len();

    let compressed =
        compress_cert(cert).map_err(|e| DictCompressError::CompressError(e.to_string()))?;
    let structure_bytes = bincode::serde::encode_to_vec(&compressed, bincode::config::standard())
        .map_err(|e| DictCompressError::SerializeError(e.to_string()))?;
    let structure_shared_bytes = structure_bytes.len();

    let mut output = Vec::new();
    {
        let mut encoder = zstd::stream::Encoder::with_dictionary(&mut output, level, &dict.data)
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
        std::io::Write::write_all(&mut encoder, &structure_bytes)
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
        encoder
            .finish()
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
    }
    let archive_bytes = output.len();

    let archive = DictCertArchive {
        compressed_data: output,
        uncompressed_size: usize_to_u32_dict(structure_shared_bytes)?,
        version: DictCertArchive::VERSION,
        compression_level: level,
        dict_id: dict.dict_id,
    };

    let structure_ratio = if structure_shared_bytes > 0 {
        original_cert_bytes as f64 / structure_shared_bytes as f64
    } else {
        1.0
    };

    let dict_ratio = if archive_bytes > 0 {
        structure_shared_bytes as f64 / archive_bytes as f64
    } else {
        1.0
    };

    let total_ratio = if archive_bytes > 0 {
        original_cert_bytes as f64 / archive_bytes as f64
    } else {
        1.0
    };

    let stats = DictArchiveStats {
        original_cert_bytes,
        structure_shared_bytes,
        archive_bytes,
        structure_ratio,
        dict_ratio,
        total_ratio,
        compression_level: level,
        dict_id: dict.dict_id,
    };

    Ok((archive, stats))
}

/// Compress raw bytes with a dictionary.
pub fn zstd_compress_with_dict(
    data: &[u8],
    dict: &CertDictionary,
) -> Result<Vec<u8>, DictCompressError> {
    zstd_compress_with_dict_level(data, dict, dict.target_level)
}

/// Compress raw bytes with a dictionary at a specific level.
pub fn zstd_compress_with_dict_level(
    data: &[u8],
    dict: &CertDictionary,
    level: i32,
) -> Result<Vec<u8>, DictCompressError> {
    let mut output = Vec::new();
    {
        let mut encoder = zstd::stream::Encoder::with_dictionary(&mut output, level, &dict.data)
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
        std::io::Write::write_all(&mut encoder, data)
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
        encoder
            .finish()
            .map_err(|e| DictCompressError::CompressError(e.to_string()))?;
    }
    Ok(output)
}

/// Decompress bytes that were compressed with a dictionary.
pub fn zstd_decompress_with_dict(
    data: &[u8],
    dict: &CertDictionary,
) -> Result<Vec<u8>, DictCompressError> {
    let mut decompressed = Vec::new();
    {
        let mut decoder =
            zstd::stream::Decoder::with_dictionary(std::io::Cursor::new(data), &dict.data)
                .map_err(|e| DictCompressError::DecompressError(e.to_string()))?;
        std::io::Read::read_to_end(&mut decoder, &mut decompressed)
            .map_err(|e| DictCompressError::DecompressError(e.to_string()))?;
    }
    Ok(decompressed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_compatible_level_no_overflow_at_boundaries() {
        // Regression: `(target_level - level).abs()` overflowed i32 when the
        // difference left i32 range (e.g. `level == i32::MIN`), and
        // `i32::MIN.abs()` overflowed — a real debug panic. `abs_diff` is total.
        let dict = CertDictionary::from_bytes(Vec::new(), 0);
        assert!(!dict.is_compatible_level(i32::MIN)); // |0 - MIN| ≫ 5, no panic
        assert!(!dict.is_compatible_level(i32::MAX));
    }

    #[test]
    fn test_is_compatible_level_window() {
        let dict = CertDictionary::from_bytes(Vec::new(), 10);
        assert!(dict.is_compatible_level(10)); // diff 0
        assert!(dict.is_compatible_level(15)); // diff 5 (inclusive boundary)
        assert!(dict.is_compatible_level(5)); // diff 5
        assert!(!dict.is_compatible_level(16)); // diff 6
        assert!(!dict.is_compatible_level(4)); // diff 6
    }
}
