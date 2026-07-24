// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Streaming compression API for proof certificate archives.
//!
//! Provides streaming read/write for large certificate collections,
//! reducing memory usage and enabling progress reporting.

use serde::{Deserialize, Serialize};

use super::super::ProofCert;
use super::zstd_backend::ZstdCertArchive;

/// Compression algorithm choice for certificate archiving.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompressionAlgorithm {
    /// LZ4: Very fast compression/decompression, moderate ratio
    Lz4,
    /// Zstd default (level 3): Balanced speed and ratio
    ZstdDefault,
    /// Zstd high (level 19): Better ratio, slower
    ZstdHigh,
    /// Zstd max (level 22): Best ratio, slowest
    ZstdMax,
}

impl CompressionAlgorithm {
    /// Get descriptive name for the algorithm
    pub fn name(&self) -> &'static str {
        match self {
            CompressionAlgorithm::Lz4 => "LZ4",
            CompressionAlgorithm::ZstdDefault => "Zstd (level 3)",
            CompressionAlgorithm::ZstdHigh => "Zstd (level 19)",
            CompressionAlgorithm::ZstdMax => "Zstd (level 22)",
        }
    }

    /// Get the zstd compression level for this algorithm, if applicable.
    pub fn zstd_level(&self) -> Option<i32> {
        match self {
            CompressionAlgorithm::Lz4 => None,
            CompressionAlgorithm::ZstdDefault => Some(ZstdCertArchive::DEFAULT_LEVEL),
            CompressionAlgorithm::ZstdHigh => Some(ZstdCertArchive::HIGH_LEVEL),
            CompressionAlgorithm::ZstdMax => Some(ZstdCertArchive::MAX_LEVEL),
        }
    }

    /// Derive a CompressionAlgorithm from a zstd level.
    pub fn from_zstd_level(level: i32) -> CompressionAlgorithm {
        if level >= ZstdCertArchive::MAX_LEVEL {
            CompressionAlgorithm::ZstdMax
        } else if level >= ZstdCertArchive::HIGH_LEVEL {
            CompressionAlgorithm::ZstdHigh
        } else {
            CompressionAlgorithm::ZstdDefault
        }
    }
}

/// Progress callback type for streaming operations.
/// Called with (bytes_processed, total_bytes_if_known).
pub type StreamingProgressCallback = Box<dyn FnMut(u64, Option<u64>) + Send>;

/// Error type for streaming compression operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum StreamingError {
    /// I/O error during streaming
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// Serialization error
    #[error("Serialization error: {0}")]
    Serialize(String),
    /// Decompression error
    #[error("Decompression error: {0}")]
    Decompress(String),
    /// Invalid header or format
    #[error("Invalid format: {0}")]
    InvalidFormat(String),
    /// Data too large to store in streaming format (>4GB per item)
    #[error("Data size {size} exceeds maximum {max} bytes")]
    SizeOverflow {
        /// Actual data size in bytes
        size: usize,
        /// Maximum allowed size in bytes
        max: u32,
    },
}

/// Convert a usize to u32 for streaming format, returning an error if it would overflow.
#[inline]
fn usize_to_u32_streaming(size: usize) -> Result<u32, StreamingError> {
    u32::try_from(size).map_err(|_| StreamingError::SizeOverflow {
        size,
        max: u32::MAX,
    })
}

/// Streaming header written at the start of a streaming archive.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StreamingArchiveHeader {
    /// Magic bytes for format identification
    pub magic: [u8; 4],
    /// Version of the streaming format
    pub version: u8,
    /// Compression algorithm used
    pub algorithm: u8, // 0 = LZ4, 1 = Zstd
    /// Zstd compression level (0 if LZ4)
    pub compression_level: i32,
    /// Total uncompressed size (0 if unknown)
    pub uncompressed_size: u64,
    /// Number of certificates in stream (0 if unknown)
    pub cert_count: u64,
}

impl StreamingArchiveHeader {
    /// Magic bytes for streaming certificate archives
    pub const MAGIC: [u8; 4] = *b"L5CS";
    /// Current format version
    pub const VERSION: u8 = 1;

    /// Create a new header for LZ4 streaming
    pub fn new_lz4() -> Self {
        StreamingArchiveHeader {
            magic: Self::MAGIC,
            version: Self::VERSION,
            algorithm: 0,
            compression_level: 0,
            uncompressed_size: 0,
            cert_count: 0,
        }
    }

    /// Create a new header for Zstd streaming
    pub fn new_zstd(level: i32) -> Self {
        StreamingArchiveHeader {
            magic: Self::MAGIC,
            version: Self::VERSION,
            algorithm: 1,
            compression_level: level,
            uncompressed_size: 0,
            cert_count: 0,
        }
    }

    /// Get the compression algorithm
    pub fn algorithm(&self) -> CompressionAlgorithm {
        if self.algorithm == 0 {
            CompressionAlgorithm::Lz4
        } else {
            CompressionAlgorithm::from_zstd_level(self.compression_level)
        }
    }

    /// Validate the header
    pub fn validate(&self) -> Result<(), StreamingError> {
        if self.magic != Self::MAGIC {
            return Err(StreamingError::InvalidFormat(format!(
                "Invalid magic bytes: expected {:?}, got {:?}",
                Self::MAGIC,
                self.magic
            )));
        }
        if self.version > Self::VERSION {
            return Err(StreamingError::InvalidFormat(format!(
                "Unsupported version: {} (max supported: {})",
                self.version,
                Self::VERSION
            )));
        }
        if self.algorithm > 1 {
            return Err(StreamingError::InvalidFormat(format!(
                "Unknown algorithm: {}",
                self.algorithm
            )));
        }
        Ok(())
    }
}

/// A streaming certificate writer that compresses certificates as they are written.
pub struct StreamingCertWriter<W: std::io::Write> {
    /// Inner Zstd encoder (wraps the output writer)
    encoder: zstd::stream::Encoder<'static, W>,
    /// Number of certificates written
    cert_count: u64,
    /// Total uncompressed bytes written
    uncompressed_bytes: u64,
    /// Progress callback
    progress: Option<StreamingProgressCallback>,
    /// Header (kept for finalization)
    header: StreamingArchiveHeader,
}

impl<W: std::io::Write> StreamingCertWriter<W> {
    /// Create a new streaming writer with Zstd compression.
    pub fn new_zstd(mut writer: W, level: i32) -> Result<Self, StreamingError> {
        let header = StreamingArchiveHeader::new_zstd(level);

        let header_bytes = bincode::serde::encode_to_vec(&header, bincode::config::standard())
            .map_err(|e| StreamingError::Serialize(e.to_string()))?;

        let len_bytes = usize_to_u32_streaming(header_bytes.len())?.to_le_bytes();
        writer.write_all(&len_bytes)?;
        writer.write_all(&header_bytes)?;

        let encoder = zstd::stream::Encoder::new(writer, level)?;

        Ok(StreamingCertWriter {
            encoder,
            cert_count: 0,
            uncompressed_bytes: 0,
            progress: None,
            header,
        })
    }

    /// Set a progress callback for monitoring compression.
    #[must_use]
    pub fn with_progress(mut self, callback: StreamingProgressCallback) -> Self {
        self.progress = Some(callback);
        self
    }

    /// Write a certificate to the stream.
    pub fn write_cert(&mut self, cert: &ProofCert) -> Result<(), StreamingError> {
        use std::io::Write;

        let cert_bytes = bincode::serde::encode_to_vec(cert, bincode::config::standard())
            .map_err(|e| StreamingError::Serialize(e.to_string()))?;

        let cert_len = usize_to_u32_streaming(cert_bytes.len())?;
        let len_bytes = cert_len.to_le_bytes();
        self.encoder.write_all(&len_bytes)?;
        self.encoder.write_all(&cert_bytes)?;

        self.cert_count += 1;
        self.uncompressed_bytes += 4 + u64::from(cert_len);

        if let Some(ref mut callback) = self.progress {
            callback(self.uncompressed_bytes, None);
        }

        Ok(())
    }

    /// Write multiple certificates to the stream.
    pub fn write_certs(&mut self, certs: &[ProofCert]) -> Result<(), StreamingError> {
        for cert in certs {
            self.write_cert(cert)?;
        }
        Ok(())
    }

    /// Get the number of certificates written so far.
    pub fn cert_count(&self) -> u64 {
        self.cert_count
    }

    /// Get the total uncompressed bytes written so far.
    pub fn uncompressed_bytes(&self) -> u64 {
        self.uncompressed_bytes
    }

    /// Get the compression algorithm used.
    pub fn algorithm(&self) -> CompressionAlgorithm {
        self.header.algorithm()
    }

    /// Finish writing and return the underlying writer.
    pub fn finish(self) -> Result<W, StreamingError> {
        let writer = self.encoder.finish()?;
        Ok(writer)
    }
}

/// A streaming certificate reader that decompresses certificates as they are read.
pub struct StreamingCertReader<R: std::io::Read> {
    /// Inner Zstd decoder (wraps the input reader)
    decoder: zstd::stream::Decoder<'static, std::io::BufReader<R>>,
    /// The header read from the stream
    header: StreamingArchiveHeader,
    /// Number of certificates read
    certs_read: u64,
    /// Total uncompressed bytes read
    uncompressed_bytes: u64,
    /// Progress callback
    progress: Option<StreamingProgressCallback>,
}

impl<R: std::io::Read> StreamingCertReader<R> {
    /// Create a new streaming reader.
    pub fn new(mut reader: R) -> Result<Self, StreamingError> {
        let mut len_bytes = [0u8; 4];
        reader.read_exact(&mut len_bytes)?;
        let header_len = u32::from_le_bytes(len_bytes) as usize;

        // Guard against corrupt/malicious header length. 1 MB is generous for metadata.
        const MAX_HEADER_BYTES: usize = 1024 * 1024;
        if header_len > MAX_HEADER_BYTES {
            return Err(StreamingError::InvalidFormat(format!(
                "header size {header_len} exceeds maximum {MAX_HEADER_BYTES}"
            )));
        }

        let mut header_bytes = vec![0u8; header_len];
        reader.read_exact(&mut header_bytes)?;

        let header: StreamingArchiveHeader =
            bincode::serde::decode_from_slice(&header_bytes, bincode::config::standard())
                .map(|(__v, _)| __v)
                .map_err(|e| StreamingError::InvalidFormat(e.to_string()))?;

        header.validate()?;

        if header.algorithm != 1 {
            return Err(StreamingError::InvalidFormat(
                "Streaming only supports Zstd algorithm".to_string(),
            ));
        }

        let decoder = zstd::stream::Decoder::new(reader)?;

        Ok(StreamingCertReader {
            decoder,
            header,
            certs_read: 0,
            uncompressed_bytes: 0,
            progress: None,
        })
    }

    /// Set a progress callback for monitoring decompression.
    #[must_use]
    pub fn with_progress(mut self, callback: StreamingProgressCallback) -> Self {
        self.progress = Some(callback);
        self
    }

    /// Get the header information.
    pub fn header(&self) -> &StreamingArchiveHeader {
        &self.header
    }

    /// Read the next certificate from the stream.
    ///
    /// Returns `None` when the stream is exhausted.
    pub fn read_cert(&mut self) -> Result<Option<ProofCert>, StreamingError> {
        use std::io::Read;

        let mut len_bytes = [0u8; 4];
        match self.decoder.read_exact(&mut len_bytes) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(StreamingError::Io(e)),
        }

        let cert_len = u32::from_le_bytes(len_bytes) as usize;

        // Guard against malicious/corrupt archives requesting extreme allocations.
        // 256 MB is generous for any single serialized certificate.
        const MAX_CERT_BYTES: usize = 256 * 1024 * 1024;
        if cert_len > MAX_CERT_BYTES {
            return Err(StreamingError::Decompress(format!(
                "certificate size {cert_len} exceeds maximum {MAX_CERT_BYTES}"
            )));
        }

        let mut cert_bytes = vec![0u8; cert_len];
        self.decoder.read_exact(&mut cert_bytes)?;

        let cert: ProofCert =
            bincode::serde::decode_from_slice(&cert_bytes, bincode::config::standard())
                .map(|(__v, _)| __v)
                .map_err(|e| StreamingError::Decompress(e.to_string()))?;

        self.certs_read += 1;
        self.uncompressed_bytes += 4 + cert_len as u64;

        if let Some(ref mut callback) = self.progress {
            let total = if self.header.cert_count > 0 {
                Some(self.header.cert_count)
            } else {
                None
            };
            callback(self.certs_read, total);
        }

        Ok(Some(cert))
    }

    /// Read all remaining certificates from the stream.
    pub fn read_all(&mut self) -> Result<Vec<ProofCert>, StreamingError> {
        let mut certs = Vec::new();
        while let Some(cert) = self.read_cert()? {
            certs.push(cert);
        }
        Ok(certs)
    }

    /// Get the number of certificates read so far.
    pub fn certs_read(&self) -> u64 {
        self.certs_read
    }

    /// Get the total uncompressed bytes read so far.
    pub fn uncompressed_bytes(&self) -> u64 {
        self.uncompressed_bytes
    }
}

/// Streaming archive statistics.
#[derive(Debug, Clone)]
pub struct StreamingStats {
    /// Number of certificates processed
    pub cert_count: u64,
    /// Total uncompressed size in bytes
    pub uncompressed_bytes: u64,
    /// Total compressed size in bytes
    pub compressed_bytes: u64,
    /// Compression algorithm used
    pub algorithm: CompressionAlgorithm,
}

impl StreamingStats {
    /// Calculate compression ratio (uncompressed / compressed).
    pub fn ratio(&self) -> f64 {
        if self.compressed_bytes == 0 {
            0.0
        } else {
            self.uncompressed_bytes as f64 / self.compressed_bytes as f64
        }
    }
}

impl std::fmt::Display for StreamingStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "StreamingStats {{ certs: {}, uncompressed: {} bytes, compressed: {} bytes, ratio: {:.2}x, algo: {} }}",
            self.cert_count,
            self.uncompressed_bytes,
            self.compressed_bytes,
            self.ratio(),
            self.algorithm.name()
        )
    }
}

/// Write certificates to a file using streaming compression.
pub fn stream_certs_to_file(
    path: &std::path::Path,
    certs: &[ProofCert],
    level: i32,
) -> Result<StreamingStats, StreamingError> {
    let file = std::fs::File::create(path)?;
    let mut writer = StreamingCertWriter::new_zstd(file, level)?;

    for cert in certs {
        writer.write_cert(cert)?;
    }

    let uncompressed = writer.uncompressed_bytes();
    let count = writer.cert_count();
    let _file = writer.finish()?;

    let compressed = std::fs::metadata(path)?.len();

    Ok(StreamingStats {
        cert_count: count,
        uncompressed_bytes: uncompressed,
        compressed_bytes: compressed,
        algorithm: CompressionAlgorithm::from_zstd_level(level),
    })
}

/// Read certificates from a file using streaming decompression.
pub fn stream_certs_from_file(
    path: &std::path::Path,
) -> Result<(Vec<ProofCert>, StreamingStats), StreamingError> {
    let compressed_size = std::fs::metadata(path)?.len();
    let file = std::fs::File::open(path)?;
    let mut reader = StreamingCertReader::new(file)?;

    let algorithm = reader.header().algorithm();
    let certs = reader.read_all()?;
    let cert_count = certs.len() as u64;

    Ok((
        certs,
        StreamingStats {
            cert_count,
            uncompressed_bytes: reader.uncompressed_bytes(),
            compressed_bytes: compressed_size,
            algorithm,
        },
    ))
}
