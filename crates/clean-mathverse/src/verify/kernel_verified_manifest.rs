// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-verified manifest — records which constants Clean's own kernel
//! re-verified across a corpus run (`verify-kernel --corpus --emit-verified`).
//!
//! This is a NON-DESTRUCTIVE sidecar: the shards themselves are not rewritten.
//! It lists, by name, every constant the kernel accepted during a global
//! dependency-closed re-verification ([`verify_corpus_incremental`]), so the
//! corpus is marked with what Clean verified and tools/loaders can upgrade
//! `ImportConfidence` to `KernelVerified` at load time. Names (not shard-local
//! indices) are stored so the manifest survives shard re-splitting and matches
//! the library's global `name_to_idx`.
//!
//! [`verify_corpus_incremental`]: crate::verify::incremental::verify_corpus_incremental

use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::error::{MathverseError, MathverseResult};
use crate::verify::incremental::IncrementalVerifyReport;

/// Reproducibility fingerprint for a `stamp-verified` run: the verification-env
/// knobs REQUESTED via CLI flags / env vars (distinct from the proof-attempt
/// [`crate::env_fingerprint::EnvFingerprint`], which pins solver/dep revisions).
/// A `KernelVerified` verdict is only reproducible against a matching fingerprint
/// — these are the knobs that can otherwise let two runs disagree on which
/// constants verify. NOTE: these are the *requested* values; the *applied* policy
/// can be weaker (e.g. closure elision is not applied on the prelude-only or
/// non-single-pass paths). Pure recorded metadata: nothing in the verify/stamp
/// path reads it back, so it can never raise or lower a verdict.
#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
pub struct StampEnvFingerprint {
    /// clean-kernel crate version (`clean_kernel::VERSION`).
    pub kernel_version: String,
    /// rustc/toolchain string the binary was built with, captured from the
    /// `CLEAN_MATHVERSE_TOOLCHAIN_VERSION` build env (populated by
    /// `clean-mathverse`'s `build.rs`, which queries `rustc --version` at
    /// compile time), else `"unknown"` if the build-time query failed. A
    /// toolchain bump changes this and re-keys the incremental cache.
    pub toolchain: String,
    /// `CLEAN_KERNEL_HEARTBEAT` in effect: `"default"` if unset, else the raw
    /// value (`"0"` = unlimited).
    pub heartbeat: String,
    /// Proof-value elision policy: `"none"` | `"opaque"` | `"opaque-and-theorem"`.
    pub elision_policy: String,
    /// `CLEAN_MAX_CLOSURE_MODULES` ceiling actually used (default 1500).
    pub max_closure_modules: usize,
    /// Trusted-context variant: `"closure-root"` (import closure seeded) or
    /// `"prelude-only"` (bare prelude).
    pub prelude_variant: String,
}

impl StampEnvFingerprint {
    /// A stable, single-line key folding every field that can change a verdict.
    /// Used as the incremental-cache's per-module closure-hash prefix: any change
    /// here re-keys every module, forcing an honest full re-verify.
    pub fn cache_key(&self) -> String {
        format!(
            "kv={};tc={};hb={};el={};mcm={};pv={}",
            self.kernel_version,
            self.toolchain,
            self.heartbeat,
            self.elision_policy,
            self.max_closure_modules,
            self.prelude_variant,
        )
    }
}

/// Sidecar manifest of the constants Clean's kernel re-verified.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KernelVerifiedManifest {
    /// Manifest schema version.
    pub schema_version: u32,
    /// Tool that produced this manifest.
    pub tool: String,
    /// clean-mathverse crate version.
    pub clean_version: String,
    /// ISO-8601 creation timestamp.
    pub created_at: String,
    /// Shard directory that was re-verified.
    pub shard_dir: String,
    /// Number of shards merged into the corpus library.
    pub shards_loaded: usize,
    /// Total constants considered by the verification run.
    pub total_constants: usize,
    /// Count of constants the kernel genuinely proof-checked
    /// (`== kernel_verified_names.len()`). Excludes axioms and axiom fallbacks.
    pub kernel_verified: usize,
    /// `NO_VALUE` constants accepted as well-formed axioms (not proof-checked).
    pub axiom_accepted: usize,
    /// Value-bearing Lean `unsafe def`s accepted TYPE-ONLY in trusted context
    /// (Lean structurally bars unsafe consts from proofs, so they can never be
    /// proof-checked). Excluded from `kernel_verified`; not failures.
    /// `#[serde(default)]` so legacy sidecars (written before this field)
    /// still deserialize (to 0).
    #[serde(default)]
    pub unsafe_accepted: usize,
    /// Value-bearing constants that fell back to an axiom registration (their
    /// value failed to typecheck, or no value was present); not proof-checked.
    pub axiom_fallback: usize,
    /// Constants whose kernel type-check failed.
    pub failed: usize,
    /// Constants skipped due to dependency cycles.
    pub cycle_skipped: usize,
    /// Constants skipped because FlatExpr reconstruction failed.
    pub reconstruct_failed: usize,
    /// Wall-clock seconds elapsed.
    pub elapsed_secs: f64,
    /// The load-bearing payload: names of every kernel-verified constant.
    pub kernel_verified_names: Vec<String>,
    /// Reproducibility fingerprint of the verification environment. Optional and
    /// `#[serde(default)]` so legacy manifests (written before this field) still
    /// deserialize (to `None`); populated via [`with_env_fingerprint`] by callers
    /// that know the env (the `stamp-verified` dispatch).
    ///
    /// [`with_env_fingerprint`]: Self::with_env_fingerprint
    #[serde(default)]
    pub env_fingerprint: Option<StampEnvFingerprint>,
}

impl KernelVerifiedManifest {
    /// Build a manifest from a corpus verification report.
    #[must_use]
    pub fn from_report(
        shard_dir: &str,
        shards_loaded: usize,
        report: &IncrementalVerifyReport,
    ) -> Self {
        Self {
            schema_version: 1,
            tool: "mathverse_shard verify-kernel --corpus".to_string(),
            clean_version: env!("CARGO_PKG_VERSION").to_string(),
            created_at: crate::release::now_iso8601(),
            shard_dir: shard_dir.to_string(),
            shards_loaded,
            total_constants: report.total,
            kernel_verified: report.kernel_verified,
            axiom_accepted: report.axiom_accepted,
            unsafe_accepted: report.unsafe_accepted,
            axiom_fallback: report.axiom_fallback,
            failed: report.failed,
            cycle_skipped: report.cycle_skipped,
            reconstruct_failed: report.reconstruct_failed,
            elapsed_secs: report.elapsed_secs,
            kernel_verified_names: report.kernel_verified_names.clone(),
            env_fingerprint: None,
        }
    }

    /// Attach a reproducibility [`StampEnvFingerprint`] (builder; caller opts in).
    #[must_use]
    pub fn with_env_fingerprint(mut self, fp: StampEnvFingerprint) -> Self {
        self.env_fingerprint = Some(fp);
        self
    }

    /// Build a manifest from a single subprocess worker's verification of one
    /// module's OWN constants (the sharded/streaming Lane-A path).
    ///
    /// Unlike [`from_report`](Self::from_report), this does not require an
    /// [`IncrementalVerifyReport`]: the sharded worker re-checks `.olean`
    /// constants already loaded into a kernel `Environment` via
    /// `kernel_verify_const`, so it tracks its own count buckets and the set of
    /// kernel-verified names directly. `shard_dir` carries the module name for
    /// per-shard sidecars.
    ///
    /// Invariant (mirrors the corpus path): `kernel_verified_names.len() ==
    /// kernel_verified`.
    #[must_use]
    pub fn from_worker_parts(
        shard_dir: &str,
        total_constants: usize,
        axiom_accepted: usize,
        failed: usize,
        elapsed_secs: f64,
        kernel_verified_names: Vec<String>,
    ) -> Self {
        Self {
            schema_version: 1,
            tool: "mathverse_shard verify-kernel --module".to_string(),
            clean_version: env!("CARGO_PKG_VERSION").to_string(),
            created_at: crate::release::now_iso8601(),
            shard_dir: shard_dir.to_string(),
            shards_loaded: 1,
            total_constants,
            kernel_verified: kernel_verified_names.len(),
            axiom_accepted,
            unsafe_accepted: 0,
            axiom_fallback: 0,
            failed,
            cycle_skipped: 0,
            reconstruct_failed: 0,
            elapsed_secs,
            kernel_verified_names,
            env_fingerprint: None,
        }
    }

    /// Merge a set of per-module sidecar manifests into one consolidated
    /// manifest (the driver's reduce step).
    ///
    /// The `kernel_verified_names` are set-UNIONed (dedup by fully qualified
    /// name); every count bucket is summed. The result is idempotent under
    /// re-merging because the name union is set-based. `shard_dir` records the
    /// driver's output directory; `shards_loaded` becomes the number of merged
    /// sidecars.
    ///
    /// `total_constants` is summed across sidecars: each worker reports its own
    /// module's OWN constants, which are disjoint across modules (a constant is
    /// declared by exactly one module), so the sum is the true corpus total
    /// with no double-counting.
    #[must_use]
    pub fn merge(shard_dir: &str, sidecars: &[KernelVerifiedManifest]) -> Self {
        use std::collections::BTreeSet;

        let mut verified: BTreeSet<String> = BTreeSet::new();
        let mut total_constants = 0usize;
        let mut axiom_accepted = 0usize;
        let mut unsafe_accepted = 0usize;
        let mut axiom_fallback = 0usize;
        let mut failed = 0usize;
        let mut cycle_skipped = 0usize;
        let mut reconstruct_failed = 0usize;
        let mut elapsed_secs = 0.0f64;

        for m in sidecars {
            for name in &m.kernel_verified_names {
                verified.insert(name.clone());
            }
            total_constants += m.total_constants;
            axiom_accepted += m.axiom_accepted;
            unsafe_accepted += m.unsafe_accepted;
            axiom_fallback += m.axiom_fallback;
            failed += m.failed;
            cycle_skipped += m.cycle_skipped;
            reconstruct_failed += m.reconstruct_failed;
            elapsed_secs += m.elapsed_secs;
        }

        let kernel_verified_names: Vec<String> = verified.into_iter().collect();
        Self {
            schema_version: 1,
            tool: "mathverse_shard verify-kernel --corpus-sharded".to_string(),
            clean_version: env!("CARGO_PKG_VERSION").to_string(),
            created_at: crate::release::now_iso8601(),
            shard_dir: shard_dir.to_string(),
            shards_loaded: sidecars.len(),
            total_constants,
            kernel_verified: kernel_verified_names.len(),
            axiom_accepted,
            unsafe_accepted,
            axiom_fallback,
            failed,
            cycle_skipped,
            reconstruct_failed,
            elapsed_secs,
            kernel_verified_names,
            env_fingerprint: None,
        }
    }

    /// Serialize to pretty JSON.
    ///
    /// # Errors
    /// Returns an error if serialization fails.
    pub fn to_json(&self) -> MathverseResult<String> {
        serde_json::to_string_pretty(self).map_err(MathverseError::from)
    }

    /// Write the manifest to `path` as pretty JSON.
    ///
    /// # Errors
    /// Returns an error if serialization or the file write fails.
    pub fn write_to_file(&self, path: &Path) -> MathverseResult<()> {
        std::fs::write(path, self.to_json()?)?;
        Ok(())
    }

    /// Read a manifest from `path`.
    ///
    /// # Errors
    /// Returns an error if the file cannot be read or parsed.
    pub fn from_file(path: &Path) -> MathverseResult<Self> {
        let data = std::fs::read_to_string(path)?;
        serde_json::from_str(&data).map_err(MathverseError::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_report() -> IncrementalVerifyReport {
        IncrementalVerifyReport {
            total: 6,
            kernel_verified: 2,
            axiom_accepted: 2,
            unsafe_accepted: 0,
            axiom_fallback: 1,
            axiom_fallback_names: vec![(
                "masked".to_string(),
                "value did not typecheck".to_string(),
            )],
            family_standins: Vec::new(),
            standin_blocked_fallbacks: Vec::new(),
            failed: 1,
            cycle_skipped: 0,
            reconstruct_failed: 0,
            inductive_registered: 0,
            seeded_checked: 0,
            seeded_unchecked: 0,
            failures: vec![("bad".to_string(), "boom".to_string())],
            kernel_verified_names: vec!["foo".to_string(), "bar".to_string()],
            discharged_axiom_names: vec!["foo".to_string()],
            elapsed_secs: 0.5,
            heartbeat_escalated_recovered: 0,
        }
    }

    #[test]
    fn test_manifest_from_report_and_roundtrip() {
        let report = sample_report();
        let m = KernelVerifiedManifest::from_report("data/mathverse-shards", 4, &report);

        // The genuine verdict set is carried verbatim, and its length matches
        // the count — axioms and fallbacks are NOT folded into it.
        assert_eq!(m.kernel_verified, 2);
        assert_eq!(m.kernel_verified_names.len(), m.kernel_verified);
        assert_eq!(m.axiom_accepted, 2);
        assert_eq!(m.axiom_fallback, 1);
        assert_eq!(m.shards_loaded, 4);
        assert_eq!(m.total_constants, 6);

        let json = m.to_json().expect("serialize");
        let back: KernelVerifiedManifest = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back.kernel_verified_names, m.kernel_verified_names);
        assert_eq!(back.axiom_accepted, 2);
        assert_eq!(back.axiom_fallback, 1);
        assert_eq!(back.failed, 1);
        assert_eq!(back.schema_version, 1);
    }

    #[test]
    fn test_from_worker_parts_count_matches_names() {
        let m = KernelVerifiedManifest::from_worker_parts(
            "Mathlib.Order.Basic",
            10,
            3,
            1,
            0.25,
            vec!["a".to_string(), "b".to_string(), "c".to_string()],
        );
        assert_eq!(m.shards_loaded, 1);
        assert_eq!(m.total_constants, 10);
        assert_eq!(m.kernel_verified, 3);
        assert_eq!(m.kernel_verified_names.len(), m.kernel_verified);
        assert_eq!(m.axiom_accepted, 3);
        assert_eq!(m.failed, 1);
        assert_eq!(m.axiom_fallback, 0);
    }

    #[test]
    fn test_merge_unions_names_and_sums_buckets() {
        let a = KernelVerifiedManifest::from_worker_parts(
            "Mathlib.A",
            4,
            1,
            0,
            0.1,
            vec!["x".to_string(), "y".to_string()],
        );
        // Overlapping name "y" must dedup; counts sum.
        let b = KernelVerifiedManifest::from_worker_parts(
            "Mathlib.B",
            5,
            2,
            1,
            0.2,
            vec!["y".to_string(), "z".to_string()],
        );

        let merged = KernelVerifiedManifest::merge("out-dir", &[a, b]);
        assert_eq!(merged.shards_loaded, 2);
        assert_eq!(merged.total_constants, 9);
        assert_eq!(merged.axiom_accepted, 3);
        assert_eq!(merged.failed, 1);
        // Union of {x,y} and {y,z} = {x,y,z}; "y" dedups.
        assert_eq!(merged.kernel_verified, 3);
        assert_eq!(merged.kernel_verified_names, vec!["x", "y", "z"]);
        assert_eq!(merged.kernel_verified_names.len(), merged.kernel_verified);
        assert!((merged.elapsed_secs - 0.3).abs() < 1e-9);
    }

    #[test]
    fn test_merge_idempotent_under_remerge() {
        let a = KernelVerifiedManifest::from_worker_parts(
            "Mathlib.A",
            4,
            1,
            0,
            0.1,
            vec!["x".to_string(), "y".to_string()],
        );
        let merged_once = KernelVerifiedManifest::merge("out", std::slice::from_ref(&a));
        // Re-merging the already-merged manifest yields the same name set.
        let merged_twice = KernelVerifiedManifest::merge("out", std::slice::from_ref(&merged_once));
        assert_eq!(
            merged_once.kernel_verified_names,
            merged_twice.kernel_verified_names
        );
        assert_eq!(merged_once.kernel_verified, merged_twice.kernel_verified);
    }

    #[test]
    fn test_env_fingerprint_roundtrips() {
        let fp = StampEnvFingerprint {
            kernel_version: "1.2.3".into(),
            toolchain: "rustc 1.90.0".into(),
            heartbeat: "50000000".into(),
            elision_policy: "opaque-and-theorem".into(),
            max_closure_modules: 9000,
            prelude_variant: "closure-root".into(),
        };
        let m = KernelVerifiedManifest::from_report("d", 1, &sample_report())
            .with_env_fingerprint(fp.clone());
        let json = m.to_json().expect("serialize");
        let back: KernelVerifiedManifest = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back.env_fingerprint, Some(fp));
        assert_eq!(back.schema_version, 1); // additive — schema version unchanged
    }

    #[test]
    fn test_legacy_manifest_without_fingerprint_deserializes_to_none() {
        // A manifest JSON written before `env_fingerprint` existed (key absent)
        // must still deserialize, defaulting the new field to None.
        let legacy = r#"{
            "schema_version": 1, "tool": "t", "clean_version": "0",
            "created_at": "2026-01-01", "shard_dir": "d", "shards_loaded": 1,
            "total_constants": 2, "kernel_verified": 1, "axiom_accepted": 0,
            "axiom_fallback": 0, "failed": 0, "cycle_skipped": 0,
            "reconstruct_failed": 0, "elapsed_secs": 0.0,
            "kernel_verified_names": ["x"]
        }"#;
        let m: KernelVerifiedManifest =
            serde_json::from_str(legacy).expect("legacy manifest must still deserialize");
        assert_eq!(m.env_fingerprint, None);
        assert_eq!(m.kernel_verified_names, vec!["x".to_string()]);
    }
}
