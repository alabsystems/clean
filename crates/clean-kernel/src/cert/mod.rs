// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof Certificates for clean
//!
//! This module implements proof certificates that witness type-correctness.
//! A proof certificate is a compact representation of a typing derivation
//! that can be verified much faster than re-running type inference.
//!
//! ## Design Goals
//!
//! 1. **Verifiable**: Certificates can be checked by a simple checker
//! 2. **Compact**: Certificates are smaller than full derivation trees
//! 3. **Deterministic**: Same input produces same certificate
//! 4. **Self-contained**: Certificate + expression is sufficient for verification
//!
//! ## Certificate Structure
//!
//! Each certificate node corresponds to a typing rule from CIC:
//!
//! ```text
//! Sort:    Sort(l) : Sort(succ(l))
//! Pi:      (x : A) → B : Sort(imax(l1, l2))
//! Lam:     λ (x : A). b : (x : A) → B
//! App:     f a : B[a/x] when f : (x : A) → B
//! Let:     let x : A := v in b : B[v/x]
//! ```
//!
//! ## Usage
//!
//! ```text
//! // Generate certificate during type checking
//! let (ty, cert) = checker.infer_type_with_cert(&expr)?;
//!
//! // Verify certificate independently
//! let verified_ty = cert.verify(&env, &expr)?;
//! assert_eq!(ty, verified_ty);
//! ```

// Core submodules
pub mod bundle;
mod cross_project;
mod def_eq;
mod expr_eq;
#[cfg(test)]
pub(crate) mod failed_eq_cache;
mod gamma_crown_import;
mod metadata;
mod nat_reduce;
mod reduction;
mod types;
mod verifier;

// Existing submodules
mod batch;
pub mod builder;
pub mod builder_pool;
mod compression;
mod replay;
pub mod trace;

// Re-export bundle types
pub use bundle::{
    BundleInspectEntry, BundleInspectIssue, BundleInspectReport, BundleVerifyResult, CertBundle,
    CertBundleEntry, CertBundleError, CertBundleManifest,
};

// Re-export core types
pub use cross_project::{
    CrossProjectCert, CrossProjectDependency, CrossProjectVerifyError, ProverInfo, ProverSystem,
};
pub use gamma_crown_import::{
    import_gamma_crown_cert, import_gamma_crown_cert_json, GammaCrownBoundType, GammaCrownCert,
    GammaCrownImportError,
};
pub use metadata::{
    ArchiveDependency, ArchiveFormat, DistributionInfo, MetadataValidationError,
    ProofArchiveMetadata, TrustLevel, VerificationChain, VerificationStep,
};
pub use types::{CertError, DefEqStep, ProofCert, ZFCSetCertKind};
pub use verifier::CertVerifier;

// Re-export helper functions (used by tests)
#[cfg(test)]
pub(crate) use types::{cert_name, expr_name};

// Re-export batch verification API
pub use batch::{
    // Function API (backward compatibility)
    batch_build_verify,
    batch_build_verify_sequential,
    batch_build_verify_sequential_with_stats,
    batch_build_verify_with_stats,
    batch_build_verify_with_stats_progress,
    batch_build_verify_with_stats_threads,
    batch_build_verify_with_threads,
    batch_verify,
    batch_verify_sequential,
    batch_verify_sequential_with_stats,
    batch_verify_with_stats,
    batch_verify_with_stats_progress,
    batch_verify_with_stats_threads,
    batch_verify_with_threads,
    // Types
    BatchBuildInput,
    BatchBuildResult,
    BatchBuildStats,
    // Builder pattern API (preferred)
    BatchBuildVerifier,
    BatchVerifier,
    BatchVerifyInput,
    BatchVerifyResult,
    BatchVerifyStats,
    BuilderFn,
};

// Re-export compression API
pub use compression::{
    archive_cert, archive_cert_with_algorithm, archive_cert_with_algorithm_stats,
    archive_cert_with_stats, compress_cert, compress_cert_with_stats, decompress_cert,
    lz4_compress, lz4_decompress, stream_certs_from_file, stream_certs_to_file, unarchive_cert,
    unarchive_cert_envelope, zstd_archive_cert, zstd_archive_cert_level,
    zstd_archive_cert_with_dict, zstd_archive_cert_with_dict_level,
    zstd_archive_cert_with_dict_stats, zstd_archive_cert_with_dict_stats_level,
    zstd_archive_cert_with_stats, zstd_archive_cert_with_stats_level, zstd_compress,
    zstd_compress_level, zstd_compress_with_dict, zstd_compress_with_dict_level, zstd_decompress,
    zstd_decompress_with_dict, zstd_unarchive_cert, zstd_unarchive_cert_with_dict, ArchiveStats,
    ArchiveVariantStats, ByteCompressError, CertArchive, CertArchiveEnvelope, CertArchiveError,
    CertDictionary, CertIdx, CompressError, CompressedCert, CompressedCertNode,
    CompressedCertSchema, CompressedExpr, CompressedLevel, CompressionAlgorithm, CompressionStats,
    DecompressError, DictArchiveStats, DictCertArchive, DictCompressError, DictTrainError, ExprIdx,
    LevelIdx, StreamingArchiveHeader, StreamingCertReader, StreamingCertWriter, StreamingError,
    StreamingProgressCallback, StreamingStats, ZstdArchiveStats, ZstdCertArchive,
    ZstdCompressError,
};

// Re-export replay API
pub use replay::replay_cert;

// Re-export builder API
pub use builder::{BuildResult, CertBuilder, NodeId, WhnfCache};

// Re-export builder pool API
pub use builder_pool::{BuilderPool, BuilderResources, PoolStats, PooledBuilder};

// Re-export trace API
pub use trace::{
    DeclKind, NullCollector, ReductionStep, SharedTraceCollector, ThreadedCollector,
    TraceCollector, TraceDefEqStep, TraceEntry,
};

#[cfg(feature = "geometry-tools")]
pub mod benchmark;
#[cfg(feature = "geometry-tools")]
pub mod derivation;
#[cfg(feature = "geometry-tools")]
pub mod geometry;
#[cfg(feature = "geometry-tools")]
pub mod problem;

#[cfg(test)]
mod tests;
