// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error types for the Mathverse Library.

use std::fmt;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum MathverseError {
    #[error("invalid shard magic: expected {expected:#010x}, got {got:#010x}")]
    InvalidMagic { expected: u32, got: u32 },

    #[error("unsupported shard version: {0}")]
    UnsupportedVersion(u32),

    #[error(
        "shard checksum mismatch: expected {expected}, got {got} — file content does not \
         match the blake3 footer written at build time (truncated or corrupted copy); \
         re-download the release archive (`clean mathverse download`) or rebuild the shard \
         (`cargo run -p clean-mathverse --release --bin mathverse_convert`)"
    )]
    ChecksumMismatch { expected: String, got: String },

    #[error("constant index {idx} out of range (count: {count})")]
    ConstantOutOfRange { idx: u32, count: u32 },

    #[error("expression index {idx} out of range (count: {count})")]
    ExprOutOfRange { idx: u32, count: u32 },

    #[error("string index {idx} out of range (count: {count})")]
    StringOutOfRange { idx: u32, count: u32 },

    #[error("unknown source system: {0}")]
    UnknownSourceSystem(u8),

    #[error("shard truncated: expected {expected} bytes, got {got}")]
    Truncated { expected: usize, got: usize },

    #[error("duplicate constant: {0}")]
    DuplicateConstant(String),

    #[error("axiom profile cycle detected at constant {0}")]
    AxiomProfileCycle(u32),

    #[error("trust violation: {0}")]
    TrustViolation(String),

    #[error("import failed for {system}: {reason}")]
    ImportFailed { system: String, reason: String },

    #[error("provenance conflict for `{name}`: existing source `{existing_source}` vs new `{new_source}`")]
    ProvenanceConflict {
        name: String,
        existing_source: String,
        new_source: String,
    },

    #[error("unsupported Coq feature `{feature}` in module `{module}`")]
    UnsupportedCoqFeature { feature: String, module: String },

    #[error("depth limit exceeded for `{constant}`: depth {depth} > limit {limit}")]
    DepthLimitExceeded {
        constant: String,
        depth: usize,
        limit: usize,
    },

    #[error("invalid axiom profile bits {bits:#018x}: {reason}")]
    InvalidAxiomProfile { bits: u64, reason: String },

    #[error("unknown expression tag {tag} at index {idx} during shard remapping")]
    UnknownExprTag { tag: u8, idx: u32 },

    #[error("unknown level tag {tag} at index {idx} during shard remapping")]
    UnknownLevelTag { tag: u8, idx: u32 },

    #[error("shard corrupt at `{path}`: {reason}")]
    ShardCorrupt { path: String, reason: String },

    #[error(
        "cannot read shard file `{path}`: {source}; `.mathverse` shards ship in release \
         archives, not in the git tree — fetch a release with `clean mathverse download` \
         (or `clean artifacts get`), or build shards locally with \
         `cargo run -p clean-mathverse --release --bin mathverse_convert -- all <out-dir>`"
    )]
    ShardFileUnreadable {
        path: String,
        #[source]
        source: std::io::Error,
    },

    #[error("baseline index invalid at `{path}`: {reason}")]
    BaselineIndexCorrupt { path: String, reason: String },

    #[error(
        "kernel-verified stamp count mismatch: manifest lists {manifest} verified names, \
         but {stored} constants carry KernelVerified in the shard bytes under `{shard_dir}`"
    )]
    KernelVerifiedStampMismatch {
        shard_dir: String,
        manifest: usize,
        stored: usize,
    },

    #[error("io: {0}")]
    Io(#[from] std::io::Error),

    #[error("json: {0}")]
    Json(#[from] serde_json::Error),

    #[error("kernel: {0}")]
    Kernel(String),

    #[error("{inner} (context: {context})")]
    WithContext {
        inner: Box<MathverseError>,
        context: String,
    },

    #[error("{inner} (constant: {constant_name})")]
    ForConstant {
        inner: Box<MathverseError>,
        constant_name: String,
    },
}

impl MathverseError {
    /// Wrap this error with additional context.
    #[must_use]
    pub fn with_context(self, ctx: &str) -> Self {
        MathverseError::WithContext {
            inner: Box::new(self),
            context: ctx.to_string(),
        }
    }

    /// Attach a constant name to this error for diagnostics.
    #[must_use]
    pub fn constant_name(self, name: &str) -> Self {
        MathverseError::ForConstant {
            inner: Box::new(self),
            constant_name: name.to_string(),
        }
    }
}

pub type MathverseResult<T> = Result<T, MathverseError>;

/// Extension trait for `MathverseResult` providing context-chaining helpers.
pub trait MathverseResultExt<T> {
    /// Attach a context string to the error side of this result.
    fn map_err_context(self, ctx: &str) -> MathverseResult<T>;
}

impl<T> MathverseResultExt<T> for MathverseResult<T> {
    fn map_err_context(self, ctx: &str) -> MathverseResult<T> {
        self.map_err(|e| e.with_context(ctx))
    }
}

/// Wrapper for displaying an `MathverseError` with its full context chain.
pub struct ErrorChain<'a>(pub &'a MathverseError);

impl fmt::Display for ErrorChain<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut current = self.0;
        write!(f, "{current}")?;
        while let MathverseError::WithContext { inner, .. }
        | MathverseError::ForConstant { inner, .. } = current
        {
            current = inner;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_with_context_display() {
        let err = MathverseError::DuplicateConstant("Nat.add".to_string());
        let wrapped = err.with_context("during batch import");
        let msg = wrapped.to_string();
        assert!(msg.contains("duplicate constant: Nat.add"));
        assert!(msg.contains("during batch import"));
    }

    #[test]
    fn test_constant_name_display() {
        let err = MathverseError::Kernel("type mismatch".to_string());
        let wrapped = err.constant_name("List.map");
        let msg = wrapped.to_string();
        assert!(msg.contains("type mismatch"));
        assert!(msg.contains("List.map"));
    }

    #[test]
    fn test_chained_context() {
        let err = MathverseError::Kernel("bad".to_string())
            .constant_name("Foo.bar")
            .with_context("phase 2");
        let msg = err.to_string();
        assert!(msg.contains("bad"));
        assert!(msg.contains("Foo.bar"));
        assert!(msg.contains("phase 2"));
    }

    #[test]
    fn test_provenance_conflict_display() {
        let err = MathverseError::ProvenanceConflict {
            name: "Nat.add_comm".to_string(),
            existing_source: "Lean4".to_string(),
            new_source: "Coq".to_string(),
        };
        let msg = err.to_string();
        assert!(msg.contains("Nat.add_comm"));
        assert!(msg.contains("Lean4"));
        assert!(msg.contains("Coq"));
    }

    #[test]
    fn test_unsupported_coq_feature_display() {
        let err = MathverseError::UnsupportedCoqFeature {
            feature: "SProp".to_string(),
            module: "Coq.Init.Logic".to_string(),
        };
        let msg = err.to_string();
        assert!(msg.contains("SProp"));
        assert!(msg.contains("Coq.Init.Logic"));
    }

    #[test]
    fn test_depth_limit_exceeded_display() {
        let err = MathverseError::DepthLimitExceeded {
            constant: "huge_term".to_string(),
            depth: 500,
            limit: 256,
        };
        let msg = err.to_string();
        assert!(msg.contains("huge_term"));
        assert!(msg.contains("500"));
        assert!(msg.contains("256"));
    }

    #[test]
    fn test_invalid_axiom_profile_display() {
        let err = MathverseError::InvalidAxiomProfile {
            bits: 0xDEAD,
            reason: "reserved bits set".to_string(),
        };
        let msg = err.to_string();
        assert!(msg.contains("0x000000000000dead"));
        assert!(msg.contains("reserved bits set"));
    }

    #[test]
    fn test_shard_corrupt_display() {
        let err = MathverseError::ShardCorrupt {
            path: "/tmp/test.mathverse".to_string(),
            reason: "truncated header".to_string(),
        };
        let msg = err.to_string();
        assert!(msg.contains("/tmp/test.mathverse"));
        assert!(msg.contains("truncated header"));
    }

    #[test]
    fn test_shard_file_unreadable_answers_four_questions() {
        let err = MathverseError::ShardFileUnreadable {
            path: "/tmp/base/Init.mathverse".to_string(),
            source: std::io::Error::new(std::io::ErrorKind::NotFound, "No such file"),
        };
        let msg = err.to_string();
        // WHAT failed (the object), WHY (the io cause), WHAT NOW (the commands).
        assert!(msg.contains("/tmp/base/Init.mathverse"));
        assert!(msg.contains("No such file"));
        assert!(msg.contains("clean mathverse download"));
        assert!(msg.contains("mathverse_convert"));
    }

    #[test]
    fn test_checksum_mismatch_states_cause_and_remediation() {
        let err = MathverseError::ChecksumMismatch {
            expected: "aa".repeat(32),
            got: "bb".repeat(32),
        };
        let msg = err.to_string();
        assert!(msg.contains(&"aa".repeat(32)) && msg.contains(&"bb".repeat(32)));
        assert!(msg.contains("blake3 footer"), "cause missing: {msg}");
        assert!(
            msg.contains("clean mathverse download"),
            "remediation missing: {msg}"
        );
    }

    #[test]
    fn test_map_err_context_ok() {
        let res: MathverseResult<i32> = Ok(42);
        let mapped = res.map_err_context("should not appear");
        assert_eq!(mapped.unwrap(), 42);
    }

    #[test]
    fn test_map_err_context_err() {
        let res: MathverseResult<i32> = Err(MathverseError::Kernel("fail".to_string()));
        let mapped = res.map_err_context("during import");
        let msg = mapped.unwrap_err().to_string();
        assert!(msg.contains("fail"));
        assert!(msg.contains("during import"));
    }

    #[test]
    fn test_duplicate_constant_variant_unchanged() {
        let err = MathverseError::DuplicateConstant("x".to_string());
        assert!(err.to_string().contains("duplicate constant: x"));
    }

    #[test]
    fn test_error_chain_display() {
        let err = MathverseError::Kernel("root".to_string())
            .with_context("ctx1")
            .with_context("ctx2");
        let chain = ErrorChain(&err);
        let msg = chain.to_string();
        assert!(msg.contains("root"));
        assert!(msg.contains("ctx1"));
        assert!(msg.contains("ctx2"));
    }
}
