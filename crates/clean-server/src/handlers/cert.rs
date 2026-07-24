// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate verification, compression, and archival handlers.
//!
//! This module contains all handlers related to proof certificate operations:
//! - Single and batch certificate verification
//! - Structure-sharing compression/decompression
//! - Archive/unarchive (LZ4 and Zstd)
//! - Dictionary-based compression

use super::helpers::format_expr;
use super::state::ServerState;
use super::types::ns_from_us;
use crate::progress::ProgressSender;
use crate::rpc::{RequestId, Response, RpcError};
use clean_kernel::cert::{
    archive_cert_with_algorithm_stats, batch_verify_with_stats_progress, compress_cert,
    compress_cert_with_stats, decompress_cert, unarchive_cert_envelope,
    zstd_archive_cert_with_dict, zstd_archive_cert_with_dict_level,
    zstd_archive_cert_with_dict_stats_level, zstd_unarchive_cert_with_dict, BatchVerifyInput,
    BatchVerifyResult, BatchVerifyStats, CertArchiveEnvelope, CertDictionary, CertError,
    CertVerifier, CompressedCert, CompressionAlgorithm, CompressionStats, DictCertArchive,
    ProofCert,
};
use clean_kernel::Expr;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::time::{Duration, Instant};
use tracing::instrument;

// ============================================================================
// Batch Certificate Verification Types
// ============================================================================

/// Batch verify certificates request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchVerifyCertParams {
    /// List of certificates to verify
    pub items: Vec<BatchVerifyCertItem>,
    /// Number of threads to use (0 = auto, default)
    #[serde(default)]
    pub threads: usize,
    /// Optional timeout for entire batch in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Single item in batch certificate verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchVerifyCertItem {
    /// Unique identifier for this item
    pub id: String,
    /// The proof certificate (JSON-encoded ProofCert)
    pub cert: ProofCert,
    /// The expression the certificate should verify
    pub expr: Expr,
}

/// Verify archived certificate request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyCertArchiveParams {
    /// Archived proof certificate
    pub archive: CertArchiveEnvelope,
    /// The expression the certificate should verify
    pub expr: Expr,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Batch verify archived certificates request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchVerifyCertArchiveParams {
    /// List of archived certificates to verify
    pub items: Vec<BatchVerifyCertArchiveItem>,
    /// Number of threads to use (0 = auto, default)
    #[serde(default)]
    pub threads: usize,
    /// Optional timeout for entire batch in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Single item in batch archived certificate verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchVerifyCertArchiveItem {
    /// Unique identifier for this item
    pub id: String,
    /// Archived proof certificate
    pub archive: CertArchiveEnvelope,
    /// The expression the certificate should verify
    pub expr: Expr,
}

/// Batch verify certificates response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchVerifyCertResult {
    /// Results for each item (in same order)
    pub results: Vec<BatchVerifyCertItemResult>,
    /// Aggregate statistics
    pub stats: BatchVerifyCertStats,
    /// Total time in milliseconds
    pub time_ms: u64,
    /// Total time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Result for single batch certificate item
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchVerifyCertItemResult {
    /// Item ID (same as request)
    pub id: String,
    /// Whether verification succeeded
    pub success: bool,
    /// Verified type as string (if successful)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verified_type: Option<String>,
    /// Error message (if failed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    /// Verification time in microseconds
    pub time_us: u64,
    /// Verification time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Aggregate statistics for batch certificate verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchVerifyCertStats {
    /// Total number of inputs
    pub total: usize,
    /// Number of successful verifications
    pub successful: usize,
    /// Number of failed verifications
    pub failed: usize,
    /// Total wall-clock time in microseconds
    pub wall_time_us: u64,
    /// Total wall-clock time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub wall_time_ns: Option<u64>,
    /// Sum of individual verification times (useful for parallelism analysis)
    pub sum_verify_time_us: u64,
    /// Sum of individual verification times in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sum_verify_time_ns: Option<u64>,
    /// Minimum verification time
    pub min_time_us: u64,
    /// Minimum verification time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub min_time_ns: Option<u64>,
    /// Maximum verification time
    pub max_time_us: u64,
    /// Maximum verification time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_time_ns: Option<u64>,
    /// Effective speedup (sum_verify_time / wall_time)
    pub speedup: f64,
}

impl From<BatchVerifyStats> for BatchVerifyCertStats {
    fn from(s: BatchVerifyStats) -> Self {
        Self {
            total: s.total,
            successful: s.successful,
            failed: s.failed,
            wall_time_us: s.wall_time_us,
            wall_time_ns: Some(ns_from_us(s.wall_time_us)),
            sum_verify_time_us: s.sum_verify_time_us,
            sum_verify_time_ns: Some(ns_from_us(s.sum_verify_time_us)),
            min_time_us: s.min_time_us,
            min_time_ns: Some(ns_from_us(s.min_time_us)),
            max_time_us: s.max_time_us,
            max_time_ns: Some(ns_from_us(s.max_time_us)),
            speedup: s.speedup,
        }
    }
}

// ============================================================================
// Single Certificate Verification Types
// ============================================================================

/// Verify single certificate request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyCertParams {
    /// The proof certificate to verify
    pub cert: ProofCert,
    /// The expression the certificate should verify
    pub expr: Expr,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Verify single certificate response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyCertResult {
    /// Whether verification succeeded
    pub success: bool,
    /// Verified type as string (if successful)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verified_type: Option<String>,
    /// Error message (if failed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    /// Verification time in microseconds
    pub time_us: u64,
    /// Verification time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

// ============================================================================
// Certificate Compression Types
// ============================================================================

/// Compress certificate request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompressCertParams {
    /// The proof certificate to compress
    pub cert: ProofCert,
    /// Whether to include compression statistics
    #[serde(default)]
    pub include_stats: bool,
}

/// Compress certificate response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompressCertResult {
    /// The compressed certificate
    pub compressed: CompressedCert,
    /// Compression statistics (if requested)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stats: Option<CompressCertStats>,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Compression statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompressCertStats {
    /// Number of unique expressions after sharing
    pub unique_exprs: usize,
    /// Number of unique levels after sharing
    pub unique_levels: usize,
    /// Number of unique certificates after sharing
    pub unique_certs: usize,
    /// Original size in bytes
    pub original_bytes: usize,
    /// Compressed size in bytes
    pub compressed_bytes: usize,
    /// Compression ratio
    pub ratio: f64,
}

impl From<CompressionStats> for CompressCertStats {
    fn from(s: CompressionStats) -> Self {
        Self {
            unique_exprs: s.unique_exprs,
            unique_levels: s.unique_levels,
            unique_certs: s.unique_certs,
            original_bytes: s.original_bytes,
            compressed_bytes: s.compressed_bytes,
            ratio: s.ratio,
        }
    }
}

/// Decompress certificate request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecompressCertParams {
    /// The compressed certificate to decompress
    pub compressed: CompressedCert,
}

/// Decompress certificate response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecompressCertResult {
    /// The decompressed proof certificate
    pub cert: ProofCert,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Archive certificate request parameters (byte-level compression)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArchiveCertParams {
    /// The proof certificate to archive
    pub cert: ProofCert,
    /// Compression algorithm: "lz4" (default, fast) or "zstd" (better ratio)
    #[serde(default)]
    pub algorithm: Option<String>,
    /// Zstd compression level (1-22, default 3). Only used for "zstd" algorithm.
    #[serde(default)]
    pub level: Option<i32>,
    /// Whether to include compression statistics
    #[serde(default)]
    pub include_stats: bool,
}

/// Archive certificate response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArchiveCertResult {
    /// The archived certificate as base64-encoded bytes
    pub archive: String,
    /// Compression algorithm used
    pub algorithm: String,
    /// Original size in bytes (before compression)
    pub original_size: usize,
    /// Compressed size in bytes
    pub compressed_size: usize,
    /// Compression ratio
    pub compression_ratio: f64,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Unarchive certificate request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnarchiveCertParams {
    /// The archived certificate as base64-encoded bytes
    pub archive: String,
}

/// Unarchive certificate response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnarchiveCertResult {
    /// The restored proof certificate
    pub cert: ProofCert,
    /// Compression algorithm that was used
    pub algorithm: String,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

// ============================================================================
// Dictionary Compression Types
// ============================================================================

/// Train dictionary request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainDictParams {
    /// Sample certificates to train the dictionary from (minimum 5)
    pub samples: Vec<ProofCert>,
    /// Maximum dictionary size in bytes (default 32KB)
    #[serde(default)]
    pub max_size: Option<usize>,
    /// Target compression level (default 3)
    #[serde(default)]
    pub level: Option<i32>,
}

/// Train dictionary response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainDictResult {
    /// The trained dictionary as base64-encoded bytes
    pub dictionary: String,
    /// Dictionary ID for validation
    pub dict_id: u32,
    /// Number of samples used for training
    pub sample_count: usize,
    /// Dictionary size in bytes
    pub size: usize,
    /// Target compression level
    pub target_level: i32,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Archive certificate with dictionary request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArchiveCertWithDictParams {
    /// The proof certificate to archive
    pub cert: ProofCert,
    /// The dictionary as base64-encoded bytes (from trainDict)
    pub dictionary: String,
    /// Compression level (optional, uses dictionary's target level by default)
    #[serde(default)]
    pub level: Option<i32>,
    /// Whether to include compression statistics
    #[serde(default)]
    pub include_stats: bool,
}

/// Archive certificate with dictionary response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArchiveCertWithDictResult {
    /// The archived certificate as base64-encoded bytes
    pub archive: String,
    /// Dictionary ID used for compression
    pub dict_id: u32,
    /// Original size in bytes (before any compression)
    pub original_size: usize,
    /// After structure sharing (intermediate)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub structure_shared_size: Option<usize>,
    /// Final compressed size in bytes
    pub compressed_size: usize,
    /// Total compression ratio (original / compressed)
    pub compression_ratio: f64,
    /// Compression level used
    pub compression_level: i32,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Unarchive certificate with dictionary request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnarchiveCertWithDictParams {
    /// The archived certificate as base64-encoded bytes
    pub archive: String,
    /// The dictionary as base64-encoded bytes (must match the one used for compression)
    pub dictionary: String,
}

/// Unarchive certificate with dictionary response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnarchiveCertWithDictResult {
    /// The restored proof certificate
    pub cert: ProofCert,
    /// Dictionary ID that was used
    pub dict_id: u32,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

// ============================================================================
// Handler Implementations
// ============================================================================

/// Handle the "batchVerifyCert" method
///
/// Verifies multiple proof certificates in parallel using rayon.
/// This is the high-throughput API for validating pre-computed proof certificates.
#[instrument(skip(state))]
pub async fn handle_batch_verify_cert(
    state: &ServerState,
    id: RequestId,
    params: BatchVerifyCertParams,
    progress: Option<ProgressSender>,
) -> Response {
    let start = Instant::now();
    let cert_count = params.items.len() as u64;
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms * 10));

    let result = tokio::time::timeout(timeout, async {
        batch_verify_cert_impl(state, &params, progress.clone()).await
    })
    .await;

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok(mut verify_result)) => {
            verify_result.time_ms = elapsed_ms;
            verify_result.time_ns = Some(ns_from_us(elapsed_us));
            let all_success = verify_result.results.iter().all(|r| r.success);
            state
                .metrics
                .record_request("batchVerifyCert", all_success, elapsed_us);
            state.metrics.record_batch_items(cert_count);
            state.metrics.record_certs_verified(cert_count);
            state.metrics.record_cert_verify_time(elapsed_us);
            Response::success_typed(id.clone(), &verify_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state
                .metrics
                .record_request("batchVerifyCert", false, elapsed_us);
            Response::error(id, e)
        }
        Err(_) => {
            state
                .metrics
                .record_request("batchVerifyCert", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

/// Handle the "batchVerifyCertArchive" method
///
/// Verifies a batch of archived proof certificates against expressions.
#[instrument(skip(state))]
pub async fn handle_batch_verify_cert_archive(
    state: &ServerState,
    id: RequestId,
    params: BatchVerifyCertArchiveParams,
    progress: Option<ProgressSender>,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms * 10));

    let result = tokio::time::timeout(timeout, async {
        batch_verify_cert_archive_impl(state, &params, progress.clone()).await
    })
    .await;

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok(mut verify_result)) => {
            verify_result.time_ms = elapsed_ms;
            verify_result.time_ns = Some(ns_from_us(elapsed_us));
            let all_success = verify_result.results.iter().all(|r| r.success);
            let cert_count = verify_result.results.len() as u64;
            state
                .metrics
                .record_request("batchVerifyCertArchive", all_success, elapsed_us);
            state.metrics.record_batch_items(cert_count);
            state.metrics.record_certs_verified(cert_count);
            state.metrics.record_cert_verify_time(elapsed_us);
            Response::success_typed(id.clone(), &verify_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state
                .metrics
                .record_request("batchVerifyCertArchive", false, elapsed_us);
            Response::error(id, e)
        }
        Err(_) => {
            state
                .metrics
                .record_request("batchVerifyCertArchive", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

async fn batch_verify_cert_impl(
    state: &ServerState,
    params: &BatchVerifyCertParams,
    progress: Option<ProgressSender>,
) -> Result<BatchVerifyCertResult, RpcError> {
    let total = params.items.len();

    if let Some(ref progress) = progress {
        progress
            .notify(
                format!("Batch verify started ({total} certs)"),
                Some(0),
                None,
            )
            .await;
    }

    // Convert to kernel BatchVerifyInput
    let inputs: Vec<BatchVerifyInput> = params
        .items
        .iter()
        .map(|item| BatchVerifyInput::new(item.id.clone(), item.cert.clone(), item.expr.clone()))
        .collect();

    let env = state.env.read().await;

    // Determine thread count: request param > server config > auto (0)
    let num_threads = if params.threads > 0 {
        params.threads
    } else {
        state.worker_threads
    };

    // Forward per-item completions over an unbounded channel when progress is requested
    let (progress_tx, progress_rx) = if progress.is_some() {
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<BatchVerifyResult>();
        (Some(tx), Some(rx))
    } else {
        (None, None)
    };

    // Stream progress notifications as results arrive
    // Adaptive frequency: for large batches, only send progress every N items
    let progress_interval = if total <= 100 {
        1 // Every item
    } else if total <= 500 {
        total / 50 // ~50 updates
    } else if total <= 2000 {
        total / 100 // ~100 updates
    } else {
        total / 200 // ~200 updates max
    };

    let progress_forwarder = if let (Some(progress), Some(mut rx)) = (progress.clone(), progress_rx)
    {
        Some(tokio::spawn(async move {
            let mut completed = 0usize;
            while let Some(result) = rx.recv().await {
                completed += 1;
                // Only send progress on interval boundaries, first item, or last item
                let should_report =
                    completed % progress_interval == 0 || completed == total || completed == 1;
                if should_report {
                    let percentage = (completed * 100)
                        .checked_div(total)
                        .map_or(100, |p| p.min(100) as u8);

                    let details = json!({
                        "id": result.id,
                        "success": result.success,
                        "verified_type": result.verified_type.as_ref().map(format_expr),
                        "error": result.error,
                        "time_us": result.time_us,
                    });

                    progress
                        .notify(
                            format!("Verified {}/{} ({})", completed, total, result.id),
                            Some(percentage),
                            Some(details),
                        )
                        .await;
                }
            }
        }))
    } else {
        None
    };

    // Use tokio spawn_blocking to run the CPU-bound parallel verification
    let env_clone = env.clone();
    let progress_callback = progress_tx.map(|tx| {
        move |result: &BatchVerifyResult| {
            let _ = tx.send(result.clone());
        }
    });
    let threads = num_threads;
    let (results, stats) = tokio::task::spawn_blocking(move || match progress_callback {
        Some(cb) => batch_verify_with_stats_progress(&env_clone, inputs, threads, cb),
        None => batch_verify_with_stats_progress(&env_clone, inputs, threads, |_| {}),
    })
    .await
    .map_err(|e| RpcError::internal_error(format!("Task join error: {e}")))?;

    if let Some(task) = progress_forwarder {
        let _ = task.await;
    }

    // Convert results to API types
    let api_results: Vec<BatchVerifyCertItemResult> = results
        .into_iter()
        .map(|r| {
            let time_ns = Some(ns_from_us(r.time_us));
            BatchVerifyCertItemResult {
                id: r.id,
                success: r.success,
                verified_type: r.verified_type.map(|t| format_expr(&t)),
                error: r.error,
                time_us: r.time_us,
                time_ns,
            }
        })
        .collect();

    if let Some(ref progress) = progress {
        progress
            .notify(
                format!(
                    "Batch verify complete: {}/{} succeeded",
                    stats.successful, stats.total
                ),
                Some(100),
                Some(json!({
                    "total": stats.total,
                    "successful": stats.successful,
                    "failed": stats.failed,
                    "speedup": stats.speedup,
                })),
            )
            .await;
    }

    Ok(BatchVerifyCertResult {
        results: api_results,
        stats: stats.into(),
        time_ms: 0,
        time_ns: None,
    })
}

fn compute_batch_verify_stats(
    results: &[BatchVerifyResult],
    wall_time_us: u64,
) -> BatchVerifyStats {
    let total = results.len();
    let mut successful = 0usize;
    let mut failed = 0usize;
    let mut sum_verify_time_us = 0u64;
    let mut min_time_us = u64::MAX;
    let mut max_time_us = 0u64;

    for r in results {
        sum_verify_time_us = sum_verify_time_us.saturating_add(r.time_us);
        min_time_us = min_time_us.min(r.time_us);
        max_time_us = max_time_us.max(r.time_us);

        if r.success {
            successful += 1;
        } else {
            failed += 1;
        }
    }

    if total == 0 {
        min_time_us = 0;
    }

    let speedup = if wall_time_us > 0 {
        sum_verify_time_us as f64 / wall_time_us as f64
    } else {
        1.0
    };

    BatchVerifyStats {
        total,
        successful,
        failed,
        wall_time_us,
        sum_verify_time_us,
        min_time_us,
        max_time_us,
        speedup,
    }
}

async fn batch_verify_cert_archive_impl(
    state: &ServerState,
    params: &BatchVerifyCertArchiveParams,
    progress: Option<ProgressSender>,
) -> Result<BatchVerifyCertResult, RpcError> {
    let total = params.items.len();
    let wall_start = Instant::now();

    if let Some(ref progress) = progress {
        progress
            .notify(
                format!("Batch verify started ({total} archived certs)"),
                Some(0),
                None,
            )
            .await;
    }

    let (progress_tx, progress_rx) = if progress.is_some() {
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<BatchVerifyResult>();
        (Some(tx), Some(rx))
    } else {
        (None, None)
    };

    let progress_interval = if total <= 100 {
        1
    } else if total <= 500 {
        total / 50
    } else if total <= 2000 {
        total / 100
    } else {
        total / 200
    };

    let progress_forwarder = if let (Some(progress), Some(mut rx)) = (progress.clone(), progress_rx)
    {
        Some(tokio::spawn(async move {
            let mut completed = 0usize;
            while let Some(result) = rx.recv().await {
                completed += 1;
                let should_report =
                    completed % progress_interval == 0 || completed == total || completed == 1;
                if should_report {
                    let percentage = (completed * 100)
                        .checked_div(total)
                        .map_or(100, |p| p.min(100) as u8);

                    let details = json!({
                        "id": result.id,
                        "success": result.success,
                        "verified_type": result.verified_type.as_ref().map(format_expr),
                        "error": result.error,
                        "time_us": result.time_us,
                    });

                    progress
                        .notify(
                            format!("Verified {}/{} ({})", completed, total, result.id),
                            Some(percentage),
                            Some(details),
                        )
                        .await;
                }
            }
        }))
    } else {
        None
    };

    let mut inputs = Vec::new();
    let mut input_indices = Vec::new();
    let mut results: Vec<Option<BatchVerifyResult>> = vec![None; total];

    for (idx, item) in params.items.iter().enumerate() {
        match unarchive_cert_envelope(&item.archive) {
            Ok(cert) => {
                inputs.push(BatchVerifyInput::new(
                    item.id.clone(),
                    cert,
                    item.expr.clone(),
                ));
                input_indices.push(idx);
            }
            Err(e) => {
                let failure = BatchVerifyResult {
                    id: item.id.clone(),
                    success: false,
                    verified_type: None,
                    error: Some(format!("Archive error: {e}")),
                    time_us: 0,
                };
                results[idx] = Some(failure.clone());
                if let Some(ref tx) = progress_tx {
                    let _ = tx.send(failure);
                }
            }
        }
    }

    let env = state.env.read().await;

    let num_threads = if params.threads > 0 {
        params.threads
    } else {
        state.worker_threads
    };

    let env_clone = env.clone();
    let progress_callback = progress_tx.map(|tx| {
        move |result: &BatchVerifyResult| {
            let _ = tx.send(result.clone());
        }
    });
    let threads = num_threads;
    let verified_results = tokio::task::spawn_blocking(move || {
        if inputs.is_empty() {
            Vec::new()
        } else {
            match progress_callback {
                Some(cb) => batch_verify_with_stats_progress(&env_clone, inputs, threads, cb).0,
                None => batch_verify_with_stats_progress(&env_clone, inputs, threads, |_| {}).0,
            }
        }
    })
    .await
    .map_err(|e| RpcError::internal_error(format!("Task join error: {e}")))?;

    for (result, idx) in verified_results.into_iter().zip(input_indices) {
        results[idx] = Some(result);
    }

    if let Some(task) = progress_forwarder {
        let _ = task.await;
    }

    let mut combined = Vec::with_capacity(total);
    for (idx, item) in params.items.iter().enumerate() {
        let result = results[idx].clone().unwrap_or_else(|| BatchVerifyResult {
            id: item.id.clone(),
            success: false,
            verified_type: None,
            error: Some("Missing verification result".to_string()),
            time_us: 0,
        });
        combined.push(result);
    }

    let wall_time_us = wall_start.elapsed().as_micros() as u64;
    let stats = compute_batch_verify_stats(&combined, wall_time_us);

    let api_results: Vec<BatchVerifyCertItemResult> = combined
        .into_iter()
        .map(|r| {
            let time_ns = Some(ns_from_us(r.time_us));
            BatchVerifyCertItemResult {
                id: r.id,
                success: r.success,
                verified_type: r.verified_type.map(|t| format_expr(&t)),
                error: r.error,
                time_us: r.time_us,
                time_ns,
            }
        })
        .collect();

    if let Some(ref progress) = progress {
        progress
            .notify(
                format!(
                    "Batch verify complete: {} success / {} failed",
                    stats.successful, stats.failed
                ),
                Some(100),
                Some(json!({
                    "total": stats.total,
                    "successful": stats.successful,
                    "failed": stats.failed,
                    "speedup": stats.speedup,
                })),
            )
            .await;
    }

    Ok(BatchVerifyCertResult {
        results: api_results,
        stats: stats.into(),
        time_ms: 0,
        time_ns: None,
    })
}

/// Handle the "verifyCert" method
///
/// Verifies a single proof certificate against an expression.
/// This is the lightweight API for verifying individual certificates,
/// as opposed to batchVerifyCert which is optimized for high-throughput parallel verification.
#[instrument(skip(state))]
pub async fn handle_verify_cert(
    state: &ServerState,
    id: RequestId,
    params: VerifyCertParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    let result = tokio::time::timeout(timeout, async {
        let env = state.env.read().await;
        let mut verifier = CertVerifier::with_mode(&env, env.mode());
        verifier.verify(&params.cert, &params.expr)
    })
    .await;

    let time_us = start.elapsed().as_micros() as u64;

    match result {
        Ok(Ok(verified_type)) => {
            state.metrics.record_request("verifyCert", true, time_us);
            state.metrics.record_certs_verified(1);
            state.metrics.record_cert_verify_time(time_us);
            let result = VerifyCertResult {
                success: true,
                verified_type: Some(format_expr(&verified_type)),
                error: None,
                time_us,
                time_ns: Some(ns_from_us(time_us)),
            };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state.metrics.record_request("verifyCert", false, time_us);
            let result = VerifyCertResult {
                success: false,
                verified_type: None,
                error: Some(format!("{e:?}")),
                time_us,
                time_ns: Some(ns_from_us(time_us)),
            };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(_) => {
            state.metrics.record_request("verifyCert", false, time_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

/// Handle the "verifyCertArchive" method
///
/// Verifies a single archived proof certificate against an expression.
#[instrument(skip(state))]
pub async fn handle_verify_cert_archive(
    state: &ServerState,
    id: RequestId,
    params: VerifyCertArchiveParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    let result = tokio::time::timeout(timeout, async {
        let env = state.env.read().await;
        let cert = match unarchive_cert_envelope(&params.archive) {
            Ok(cert) => cert,
            Err(e) => return Err(CertError::InvalidCert(format!("Archive error: {e}"))),
        };
        let mut verifier = CertVerifier::with_mode(&env, env.mode());
        verifier.verify(&cert, &params.expr)
    })
    .await;

    let time_us = start.elapsed().as_micros() as u64;

    match result {
        Ok(Ok(verified_type)) => {
            state
                .metrics
                .record_request("verifyCertArchive", true, time_us);
            state.metrics.record_certs_verified(1);
            state.metrics.record_cert_verify_time(time_us);
            let result = VerifyCertResult {
                success: true,
                verified_type: Some(format_expr(&verified_type)),
                error: None,
                time_us,
                time_ns: Some(ns_from_us(time_us)),
            };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state
                .metrics
                .record_request("verifyCertArchive", false, time_us);
            let result = VerifyCertResult {
                success: false,
                verified_type: None,
                error: Some(format!("{e:?}")),
                time_us,
                time_ns: Some(ns_from_us(time_us)),
            };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(_) => {
            state
                .metrics
                .record_request("verifyCertArchive", false, time_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

/// Handle the "compressCert" method
///
/// Compresses a proof certificate using structure-sharing compression.
/// This is an in-memory compression that exploits shared subexpressions.
#[instrument(skip(_state))]
pub async fn handle_compress_cert(
    _state: &ServerState,
    id: RequestId,
    params: CompressCertParams,
) -> Response {
    let start = Instant::now();

    let result = if params.include_stats {
        match compress_cert_with_stats(&params.cert) {
            Ok((compressed, stats)) => {
                let elapsed_us = start.elapsed().as_micros() as u64;
                CompressCertResult {
                    compressed,
                    stats: Some(stats.into()),
                    time_us: elapsed_us,
                    time_ns: Some(ns_from_us(elapsed_us)),
                }
            }
            Err(e) => {
                return Response::error(
                    id,
                    RpcError::internal_error(format!("Compression failed: {e}")),
                );
            }
        }
    } else {
        match compress_cert(&params.cert) {
            Ok(compressed) => {
                let elapsed_us = start.elapsed().as_micros() as u64;
                CompressCertResult {
                    compressed,
                    stats: None,
                    time_us: elapsed_us,
                    time_ns: Some(ns_from_us(elapsed_us)),
                }
            }
            Err(e) => {
                return Response::error(
                    id,
                    RpcError::internal_error(format!("Compression failed: {e}")),
                );
            }
        }
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle the "decompressCert" method
///
/// Decompresses a structure-sharing compressed certificate back to ProofCert.
#[instrument(skip(_state))]
pub async fn handle_decompress_cert(
    _state: &ServerState,
    id: RequestId,
    params: DecompressCertParams,
) -> Response {
    let start = Instant::now();

    match decompress_cert(&params.compressed) {
        Ok(cert) => {
            let elapsed_us = start.elapsed().as_micros() as u64;
            let result = DecompressCertResult {
                cert,
                time_us: elapsed_us,
                time_ns: Some(ns_from_us(elapsed_us)),
            };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => Response::error(
            id,
            RpcError::internal_error(format!("Decompression failed: {e:?}")),
        ),
    }
}

/// Handle the "archiveCert" method
///
/// Archives a proof certificate to a portable byte format using LZ4 or Zstd compression.
/// The result is a base64-encoded string suitable for storage or transmission.
#[instrument(skip(_state))]
pub async fn handle_archive_cert(
    _state: &ServerState,
    id: RequestId,
    params: ArchiveCertParams,
) -> Response {
    use base64::{engine::general_purpose::STANDARD, Engine};
    use clean_kernel::cert::ArchiveVariantStats;

    let start = Instant::now();

    // Parse algorithm
    let algorithm = match params.algorithm.as_deref().unwrap_or("lz4") {
        "lz4" => CompressionAlgorithm::Lz4,
        "zstd" | "zstd_default" => CompressionAlgorithm::ZstdDefault,
        "zstd_high" => CompressionAlgorithm::ZstdHigh,
        "zstd_max" => CompressionAlgorithm::ZstdMax,
        other => {
            return Response::error(
                id,
                RpcError::invalid_params(format!(
                    "Unknown algorithm '{other}'. Use 'lz4', 'zstd', 'zstd_high', or 'zstd_max'."
                )),
            );
        }
    };

    // Archive with stats
    let result = archive_cert_with_algorithm_stats(&params.cert, algorithm);

    match result {
        Ok((envelope, stats)) => {
            // Serialize envelope to bytes
            let envelope_bytes =
                match bincode::serde::encode_to_vec(&envelope, bincode::config::standard()) {
                    Ok(bytes) => bytes,
                    Err(e) => {
                        return Response::error(
                            id,
                            RpcError::internal_error(format!("Envelope serialization failed: {e}")),
                        );
                    }
                };

            let archive_base64 = STANDARD.encode(&envelope_bytes);

            // Extract stats based on variant
            let (original_size, compressed_size, compression_ratio, algo_name) = match stats {
                ArchiveVariantStats::Lz4(s) => (
                    s.original_cert_bytes,
                    s.archive_bytes,
                    s.total_ratio,
                    "lz4".to_string(),
                ),
                ArchiveVariantStats::Zstd(s) => (
                    s.original_cert_bytes,
                    s.archive_bytes,
                    s.total_ratio,
                    "zstd".to_string(),
                ),
            };

            let elapsed_us = start.elapsed().as_micros() as u64;
            let api_result = ArchiveCertResult {
                archive: archive_base64,
                algorithm: algo_name,
                original_size,
                compressed_size,
                compression_ratio,
                time_us: elapsed_us,
                time_ns: Some(ns_from_us(elapsed_us)),
            };

            Response::success_typed(id.clone(), &api_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => Response::error(
            id,
            RpcError::internal_error(format!("Archive failed: {e:?}")),
        ),
    }
}

/// Handle the "unarchiveCert" method
///
/// Restores a proof certificate from a base64-encoded archive.
#[instrument(skip(_state))]
pub async fn handle_unarchive_cert(
    _state: &ServerState,
    id: RequestId,
    params: UnarchiveCertParams,
) -> Response {
    use base64::{engine::general_purpose::STANDARD, Engine};

    let start = Instant::now();

    // Decode base64
    let envelope_bytes = match STANDARD.decode(&params.archive) {
        Ok(bytes) => bytes,
        Err(e) => {
            return Response::error(id, RpcError::invalid_params(format!("Invalid base64: {e}")));
        }
    };

    // Deserialize envelope
    let envelope: CertArchiveEnvelope =
        match bincode::serde::decode_from_slice(&envelope_bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
        {
            Ok(env) => env,
            Err(e) => {
                return Response::error(
                    id,
                    RpcError::invalid_params(format!("Invalid archive format: {e}")),
                );
            }
        };

    // Determine algorithm from envelope
    let algorithm = match &envelope {
        CertArchiveEnvelope::Lz4(_) => "lz4".to_string(),
        CertArchiveEnvelope::Zstd(_) => "zstd".to_string(),
    };

    // Unarchive
    match unarchive_cert_envelope(&envelope) {
        Ok(cert) => {
            let elapsed_us = start.elapsed().as_micros() as u64;
            let result = UnarchiveCertResult {
                cert,
                algorithm,
                time_us: elapsed_us,
                time_ns: Some(ns_from_us(elapsed_us)),
            };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => Response::error(
            id,
            RpcError::internal_error(format!("Unarchive failed: {e:?}")),
        ),
    }
}

// ============================================================================
// Dictionary Compression Handlers
// ============================================================================

/// Handle the "trainDict" method
///
/// Trains a compression dictionary from sample certificates.
/// The dictionary can then be used with archiveCertWithDict for improved compression.
#[instrument(skip(_state))]
pub async fn handle_train_dict(
    _state: &ServerState,
    id: RequestId,
    params: TrainDictParams,
) -> Response {
    use base64::{engine::general_purpose::STANDARD, Engine};

    let start = Instant::now();

    let max_size = params.max_size.unwrap_or(CertDictionary::DEFAULT_SIZE);
    let level = params.level.unwrap_or(3);

    // Train the dictionary
    match CertDictionary::train(&params.samples, max_size, level) {
        Ok(dict) => {
            // Serialize dictionary for transport
            let dict_bytes = match bincode::serde::encode_to_vec(&dict, bincode::config::standard())
            {
                Ok(bytes) => bytes,
                Err(e) => {
                    return Response::error(
                        id,
                        RpcError::internal_error(format!("Failed to serialize dictionary: {e}")),
                    );
                }
            };

            let elapsed_us = start.elapsed().as_micros() as u64;
            let result = TrainDictResult {
                dictionary: STANDARD.encode(&dict_bytes),
                dict_id: dict.dict_id,
                sample_count: dict.sample_count,
                size: dict.size(),
                target_level: dict.target_level,
                time_us: elapsed_us,
                time_ns: Some(ns_from_us(elapsed_us)),
            };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => Response::error(
            id,
            RpcError::invalid_params(format!("Dictionary training failed: {e}")),
        ),
    }
}

/// Handle the "archiveCertWithDict" method
///
/// Archives a certificate using dictionary-based Zstd compression.
/// The dictionary must have been created with trainDict.
#[instrument(skip(_state))]
pub async fn handle_archive_cert_with_dict(
    _state: &ServerState,
    id: RequestId,
    params: ArchiveCertWithDictParams,
) -> Response {
    use base64::{engine::general_purpose::STANDARD, Engine};

    let start = Instant::now();

    // Decode and deserialize dictionary
    let dict_bytes = match STANDARD.decode(&params.dictionary) {
        Ok(bytes) => bytes,
        Err(e) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("Invalid dictionary base64: {e}")),
            );
        }
    };

    let dict: CertDictionary =
        match bincode::serde::decode_from_slice(&dict_bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
        {
            Ok(d) => d,
            Err(e) => {
                return Response::error(
                    id,
                    RpcError::invalid_params(format!("Invalid dictionary format: {e}")),
                );
            }
        };

    // Get original size for stats
    let original_bytes =
        match bincode::serde::encode_to_vec(&params.cert, bincode::config::standard()) {
            Ok(b) => b,
            Err(e) => {
                return Response::error(
                    id,
                    RpcError::internal_error(format!("Failed to measure cert size: {e}")),
                );
            }
        };
    let original_size = original_bytes.len();

    // Archive with dictionary
    if params.include_stats {
        let level = params.level.unwrap_or(dict.target_level);
        match zstd_archive_cert_with_dict_stats_level(&params.cert, &dict, level) {
            Ok((archive, stats)) => {
                // Serialize archive for transport
                let archive_bytes =
                    match bincode::serde::encode_to_vec(&archive, bincode::config::standard()) {
                        Ok(bytes) => bytes,
                        Err(e) => {
                            return Response::error(
                                id,
                                RpcError::internal_error(format!(
                                    "Failed to serialize archive: {e}"
                                )),
                            );
                        }
                    };

                let elapsed_us = start.elapsed().as_micros() as u64;
                let result = ArchiveCertWithDictResult {
                    archive: STANDARD.encode(&archive_bytes),
                    dict_id: archive.dict_id,
                    original_size: stats.original_cert_bytes,
                    structure_shared_size: Some(stats.structure_shared_bytes),
                    compressed_size: stats.archive_bytes,
                    compression_ratio: stats.total_ratio,
                    compression_level: stats.compression_level,
                    time_us: elapsed_us,
                    time_ns: Some(ns_from_us(elapsed_us)),
                };
                Response::success_typed(id.clone(), &result).unwrap_or_else(|e| {
                    Response::error(id, RpcError::internal_error(e.to_string()))
                })
            }
            Err(e) => Response::error(
                id,
                RpcError::internal_error(format!("Dictionary archive failed: {e}")),
            ),
        }
    } else {
        let archive_result = if let Some(level) = params.level {
            zstd_archive_cert_with_dict_level(&params.cert, &dict, level)
        } else {
            zstd_archive_cert_with_dict(&params.cert, &dict)
        };

        match archive_result {
            Ok(archive) => {
                // Serialize archive for transport
                let archive_bytes =
                    match bincode::serde::encode_to_vec(&archive, bincode::config::standard()) {
                        Ok(bytes) => bytes,
                        Err(e) => {
                            return Response::error(
                                id,
                                RpcError::internal_error(format!(
                                    "Failed to serialize archive: {e}"
                                )),
                            );
                        }
                    };

                let compressed_size = archive_bytes.len();
                let compression_ratio = if compressed_size > 0 {
                    original_size as f64 / compressed_size as f64
                } else {
                    0.0
                };

                let elapsed_us = start.elapsed().as_micros() as u64;
                let result = ArchiveCertWithDictResult {
                    archive: STANDARD.encode(&archive_bytes),
                    dict_id: archive.dict_id,
                    original_size,
                    structure_shared_size: None,
                    compressed_size,
                    compression_ratio,
                    compression_level: archive.compression_level,
                    time_us: elapsed_us,
                    time_ns: Some(ns_from_us(elapsed_us)),
                };
                Response::success_typed(id.clone(), &result).unwrap_or_else(|e| {
                    Response::error(id, RpcError::internal_error(e.to_string()))
                })
            }
            Err(e) => Response::error(
                id,
                RpcError::internal_error(format!("Dictionary archive failed: {e}")),
            ),
        }
    }
}

/// Handle the "unarchiveCertWithDict" method
///
/// Restores a certificate from a dictionary-compressed archive.
/// The same dictionary used for compression must be provided.
#[instrument(skip(_state))]
pub async fn handle_unarchive_cert_with_dict(
    _state: &ServerState,
    id: RequestId,
    params: UnarchiveCertWithDictParams,
) -> Response {
    use base64::{engine::general_purpose::STANDARD, Engine};

    let start = Instant::now();

    // Decode and deserialize dictionary
    let dict_bytes = match STANDARD.decode(&params.dictionary) {
        Ok(bytes) => bytes,
        Err(e) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("Invalid dictionary base64: {e}")),
            );
        }
    };

    let dict: CertDictionary =
        match bincode::serde::decode_from_slice(&dict_bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
        {
            Ok(d) => d,
            Err(e) => {
                return Response::error(
                    id,
                    RpcError::invalid_params(format!("Invalid dictionary format: {e}")),
                );
            }
        };

    // Decode and deserialize archive
    let archive_bytes = match STANDARD.decode(&params.archive) {
        Ok(bytes) => bytes,
        Err(e) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("Invalid archive base64: {e}")),
            );
        }
    };

    let archive: DictCertArchive =
        match bincode::serde::decode_from_slice(&archive_bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
        {
            Ok(a) => a,
            Err(e) => {
                return Response::error(
                    id,
                    RpcError::invalid_params(format!("Invalid archive format: {e}")),
                );
            }
        };

    // Unarchive with dictionary
    match zstd_unarchive_cert_with_dict(&archive, &dict) {
        Ok(cert) => {
            let elapsed_us = start.elapsed().as_micros() as u64;
            let result = UnarchiveCertWithDictResult {
                cert,
                dict_id: dict.dict_id,
                time_us: elapsed_us,
                time_ns: Some(ns_from_us(elapsed_us)),
            };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => Response::error(
            id,
            RpcError::internal_error(format!("Dictionary unarchive failed: {e}")),
        ),
    }
}
