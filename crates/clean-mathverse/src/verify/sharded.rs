// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sharded/streaming kernel-verification core (Lane A scale path).
//!
//! The whole-corpus `verify_corpus_incremental` path OOMs at ~24 GiB because it
//! merges every shard into one library, clones all arenas, and retains every
//! proof-term VALUE forever. Per-leaf / sub-closure passes are fine and
//! sub-second. This module provides the SUBPROCESS-SHARDING primitives that turn
//! that into actual `KernelVerified` rows at scale WITHOUT touching the kernel:
//!
//! - one WORKER process verifies ONE module's OWN constants against a fresh
//!   prelude env loaded with that module's full transitive dependency closure
//!   (types + values), then EXITS so the OS reclaims its memory;
//! - a DRIVER process spawns workers (re-execing itself), bounded to N
//!   concurrent children, and merges the per-module sidecars into one
//!   consolidated `kernel-verified.json` (set-union of names, summed buckets).
//!
//! # Why this is sound with zero kernel change
//!
//! A constant's kernel check needs its transitive deps' TYPES always plus the
//! VALUES of any definition it δ-reduces. A worker loads the module's FULL
//! transitive closure (`load_module_with_deps` registers types AND values), so
//! every dependency a constant could δ-reduce is present — exactly why per-leaf
//! already passes at ~99.9%. Subprocessing is the whole point: no value-eviction
//! is performed (eviction of definition values a dependent δ-reduces would
//! cause false negatives — `clean-kernel/src/env/unfold.rs:165`), and each
//! process's footprint is one module's closure, not the whole corpus.
//!
//! This module is pure (no process spawning): the WORKER body lives in
//! [`verify_module`], path/enumeration helpers are below, and the DRIVER's
//! process orchestration lives in the `mathverse_shard` binary.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::env::Environment;
use clean_olean::{load_module_with_deps, parse_module_file};
use thiserror::Error;

use crate::verify::classify::{classify_const, ConstKind};
use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

/// How many OWN names per class to retain as an audit sample in the result.
const CLASS_SAMPLE_CAP: usize = 25;

/// Errors raised by the sharded worker.
#[derive(Debug, Error)]
pub enum ShardedVerifyError {
    /// The kernel prelude environment could not be constructed.
    #[error("failed to build prelude environment: {0}")]
    Prelude(String),
    /// The target module's `.olean` could not be located under any search path.
    #[error("module `{module}` not found under any olean root (tried {tried} path(s))")]
    ModuleNotFound { module: String, tried: usize },
    /// The target module's `.olean` failed to parse (needed for its OWN
    /// constant names).
    #[error("failed to parse module `{module}` at {path}: {reason}")]
    ParseModule {
        module: String,
        path: String,
        reason: String,
    },
    /// Loading the module + its transitive dependency closure failed.
    #[error("failed to load module `{module}` with deps: {reason}")]
    LoadDeps { module: String, reason: String },
}

/// Per-constant verdict bucket for a single module's OWN constants.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ModuleVerifyCounts {
    /// Total OWN constants of the module that were attempted.
    pub total: usize,
    /// Constants the kernel genuinely proof-checked (value type-checked, or a
    /// well-formed `Theorem` Prop type). `== kernel_verified_names.len()`.
    pub kernel_verified: usize,
    /// `Axiom`/`Opaque` constants accepted as well-formed but NOT proof-checked.
    pub axiom_accepted: usize,
    /// Constants the kernel REJECTED (type-check / value-check failure).
    pub failed: usize,
    /// Constants named by the module but absent from the loaded environment
    /// (e.g. compiler-internal names not registered by the importer).
    pub not_found: usize,
}

/// Verdict buckets for ONE class (MATH or GENERATED) of a module's OWN
/// constants. Records the same verdicts as [`ModuleVerifyCounts`] but split by
/// the [`ConstKind`] classification, so the TRUE Lane-A yield (MATH-only
/// kernel-verify rate) can be read off directly.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ClassCounts {
    /// Constants of this class that resolved in the env (excludes `not_found`).
    pub resolved: usize,
    /// Genuinely proof-checked.
    pub kernel_verified: usize,
    /// `Axiom`/`Opaque` accepted as well-formed, not proof-checked.
    pub axiom_accepted: usize,
    /// Kernel-REJECTED.
    pub failed: usize,
    /// Named by the module but absent from the loaded env.
    pub not_found: usize,
}

impl ClassCounts {
    /// Kernel-verify rate over RESOLVED constants of this class
    /// (`kernel_verified / (kernel_verified + axiom_accepted + failed)`).
    /// Returns `None` when no constant of this class resolved.
    #[must_use]
    pub fn verified_rate(&self) -> Option<f64> {
        let denom = self.kernel_verified + self.axiom_accepted + self.failed;
        if denom == 0 {
            None
        } else {
            Some(self.kernel_verified as f64 / denom as f64 * 100.0)
        }
    }
}

/// Result of verifying ONE module's OWN constants in a worker.
#[derive(Clone, Debug)]
pub struct ModuleVerifyResult {
    /// Dot-separated module name (e.g. `Mathlib.Order.Basic`).
    pub module: String,
    /// Verdict buckets (all classes combined; the historical aggregate).
    pub counts: ModuleVerifyCounts,
    /// MATH-only verdict buckets (human-authored named results).
    pub math: ClassCounts,
    /// GENERATED-only verdict buckets (compiler-emitted internals).
    pub generated: ClassCounts,
    /// Number of constants in the loaded transitive closure (env size). Useful
    /// for the memory/scale narrative — this is what one worker holds resident.
    pub closure_constants: usize,
    /// Fully qualified names the kernel verified.
    pub kernel_verified_names: Vec<String>,
    /// `(name, reason)` for each rejected OWN constant (capped by the caller).
    pub failures: Vec<(String, String)>,
    /// `(name, reason)` for each rejected MATH constant (capped). These are the
    /// failures that actually cost Lane-A coverage; kept separately so they are
    /// not lost among the GENERATED noise.
    pub math_failures: Vec<(String, String)>,
    /// A small sample of OWN constant names in each class, for auditing the
    /// classification (so a human can confirm no real theorem was mislabeled).
    pub math_sample: Vec<String>,
    /// A small sample of GENERATED OWN constant names.
    pub generated_sample: Vec<String>,
    /// Wall-clock seconds for load + verify.
    pub elapsed_secs: f64,
}

impl ModuleVerifyResult {
    /// Verification rate over OWN constants that resolved (excludes `not_found`).
    #[must_use]
    pub fn verified_rate(&self) -> f64 {
        let denom = self.counts.kernel_verified + self.counts.axiom_accepted + self.counts.failed;
        if denom == 0 {
            0.0
        } else {
            self.counts.kernel_verified as f64 / denom as f64 * 100.0
        }
    }

    /// Build the non-destructive per-shard sidecar manifest for this module.
    #[must_use]
    pub fn to_manifest(&self) -> KernelVerifiedManifest {
        KernelVerifiedManifest::from_worker_parts(
            &self.module,
            self.counts.total,
            self.counts.axiom_accepted,
            self.counts.failed,
            self.elapsed_secs,
            self.kernel_verified_names.clone(),
        )
    }
}

/// Map a dot-separated module name to its relative `.olean` path.
///
/// `Mathlib.Order.Basic` → `Mathlib/Order/Basic.olean`. Returns `None` for an
/// empty name or one with empty `.`-separated components.
#[must_use]
pub fn module_rel_path(module: &str) -> Option<PathBuf> {
    let trimmed = module.trim_matches('.');
    if trimmed.is_empty() {
        return None;
    }
    let mut path = PathBuf::new();
    for part in trimmed.split('.') {
        if part.is_empty() {
            return None;
        }
        path.push(part);
    }
    path.set_extension("olean");
    Some(path)
}

/// Resolve a module name to its `.olean` file under the first matching search
/// path.
#[must_use]
pub fn resolve_module_olean(module: &str, search_paths: &[PathBuf]) -> Option<PathBuf> {
    let rel = module_rel_path(module)?;
    search_paths
        .iter()
        .map(|base| base.join(&rel))
        .find(|candidate| candidate.exists())
}

/// Recursively enumerate every module name reachable under `root` by its
/// directory tree (one entry per `.olean` file). Returns sorted, deduplicated
/// dot-separated names.
///
/// Skips Lean's compiler-internal sibling artifacts (`*.olean.private`,
/// `*.olean.server`) — only files whose extension is exactly `olean` count.
#[must_use]
pub fn enumerate_modules(root: &Path) -> Vec<String> {
    let mut names = BTreeSet::new();
    enumerate_modules_into(root, root, &mut names);
    names.into_iter().collect()
}

fn enumerate_modules_into(root: &Path, dir: &Path, out: &mut BTreeSet<String>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            enumerate_modules_into(root, &path, out);
        } else if path.extension().is_some_and(|ext| ext == "olean") {
            if let Some(name) = module_name_from_rel(root, &path) {
                out.insert(name);
            }
        }
    }
}

fn module_name_from_rel(root: &Path, path: &Path) -> Option<String> {
    let rel = path.strip_prefix(root).unwrap_or(path).with_extension("");
    let parts: Vec<String> = rel
        .components()
        .filter_map(|c| match c {
            std::path::Component::Normal(s) => {
                let s = s.to_string_lossy();
                if s.is_empty() {
                    None
                } else {
                    Some(s.to_string())
                }
            }
            _ => None,
        })
        .collect();
    if parts.is_empty() {
        None
    } else {
        Some(parts.join("."))
    }
}

/// WORKER: verify ONE module's OWN constants against a fresh prelude env loaded
/// with that module's full transitive dependency closure.
///
/// Steps (each cheap; the whole point is per-process memory is one module's
/// closure, never the whole corpus):
/// 1. fresh `Environment::try_with_prelude_for_import` (suppresses the lossy
///    `extends`-structure stubs so the genuine olean structures register with
///    their full field telescope — see the call site for the rationale);
/// 2. `parse_module_file` the module's `.olean` to read its OWN `const_names`
///    (the constants this module DECLARES — not the whole closure);
/// 3. `load_module_with_deps` to register the module + transitive deps (types
///    AND values) into the env;
/// 4. `kernel_verify_const` each OWN name; bucket the verdict.
///
/// `max_failures` caps how many `(name, reason)` pairs are retained for the
/// report (counts are always exact).
///
/// # Errors
/// Returns [`ShardedVerifyError`] if the prelude cannot be built, the module's
/// `.olean` cannot be located/parsed, or the dependency-closure load fails. A
/// per-constant kernel rejection is NOT an error — it is bucketed into
/// `failed`.
pub fn verify_module(
    module: &str,
    search_paths: &[PathBuf],
    max_failures: usize,
) -> Result<ModuleVerifyResult, ShardedVerifyError> {
    let start = Instant::now();

    let olean_path = resolve_module_olean(module, search_paths).ok_or_else(|| {
        ShardedVerifyError::ModuleNotFound {
            module: module.to_string(),
            tried: search_paths.len(),
        }
    })?;

    // The module's OWN declared constants (NOT the whole transitive closure).
    let parsed = parse_module_file(&olean_path).map_err(|e| ShardedVerifyError::ParseModule {
        module: module.to_string(),
        path: olean_path.display().to_string(),
        reason: format!("{e}"),
    })?;
    let own_names: Vec<String> = {
        let mut set: BTreeSet<String> = BTreeSet::new();
        set.extend(parsed.const_names.iter().cloned());
        set.extend(parsed.extra_const_names.iter().cloned());
        set.into_iter().collect()
    };

    // Use the IMPORT prelude, which suppresses the kernel's hand-rolled,
    // non-Lean-faithful `extends`-structure stubs (`Semigroup`/`Monoid`/`Group`/
    // `Preorder`/…). Those stubs carry a FLATTENED, trailing-field-dropping
    // constructor (e.g. the stub `Monoid.mk` has 5 fields `[mul, assoc, one,
    // one_mul, mul_one]` versus Lean's genuine 7 `[toSemigroup, toOne, one_mul,
    // mul_one, npow, npow_zero, npow_succ]`). Because `load_module_with_deps`
    // dedups inductives by name, a stub shadows the real Mathlib structure on
    // import, so every parent projection `Monoid.toSemigroup = self.0` lands on
    // the WRONG flattened field and fails `check_type` with a spurious
    // TypeMismatch. Suppressing the stubs lets the genuine structures register
    // through the checked import path with their FULL field telescope, so the
    // typeclass-inheritance projections kernel-verify. This is strictly more
    // faithful (no kernel/TCB change): we stop seeding a wrong structure rather
    // than accepting any new term.
    let mut env = Environment::try_with_prelude_for_import()
        .map_err(|e| ShardedVerifyError::Prelude(format!("{e}")))?;

    load_module_with_deps(&mut env, module, search_paths).map_err(|e| {
        ShardedVerifyError::LoadDeps {
            module: module.to_string(),
            reason: format!("{e}"),
        }
    })?;

    let closure_constants = env.num_constants();

    // Heartbeat budget for this worker's kernel checks. `CLEAN_KERNEL_HEARTBEAT`
    // overrides the kernel's `DEFAULT_HEARTBEAT_LIMIT` (0 = unlimited), so the
    // heavy-tail modules (`CategoryTheory.Limits.*`, `Tactic.Ring.*`) whose WHNF
    // reduction exceeds the default budget can run to completion. SOUNDNESS-
    // NEUTRAL: the heartbeat is a resource ceiling, not an acceptance criterion —
    // a larger budget only lets MORE valid proofs finish, never accepts an
    // invalid one. `None` keeps the kernel default unchanged.
    let heartbeat = crate::lean4::kernel_verify::heartbeat_from_env();

    let mut counts = ModuleVerifyCounts {
        total: own_names.len(),
        ..ModuleVerifyCounts::default()
    };
    let mut math = ClassCounts::default();
    let mut generated = ClassCounts::default();
    let mut kernel_verified_names = Vec::new();
    let mut failures = Vec::new();
    let mut math_failures = Vec::new();
    let mut math_sample = Vec::new();
    let mut generated_sample = Vec::new();

    for name in &own_names {
        let kind = classify_const(name);
        let class = match kind {
            ConstKind::Math => &mut math,
            ConstKind::Generated => &mut generated,
        };
        match kind {
            ConstKind::Math if math_sample.len() < CLASS_SAMPLE_CAP => {
                math_sample.push(name.clone());
            }
            ConstKind::Generated if generated_sample.len() < CLASS_SAMPLE_CAP => {
                generated_sample.push(name.clone());
            }
            _ => {}
        }

        match crate::lean4::kernel_verify::kernel_verify_const_with_heartbeat(&env, name, heartbeat)
        {
            Ok(ok) => {
                class.resolved += 1;
                if ok.confidence == crate::types::ImportConfidence::KernelVerified {
                    counts.kernel_verified += 1;
                    class.kernel_verified += 1;
                    kernel_verified_names.push(name.clone());
                } else {
                    // Axiom/Opaque: structurally accepted, not proof-checked.
                    counts.axiom_accepted += 1;
                    class.axiom_accepted += 1;
                }
            }
            Err(crate::lean4::kernel_verify::KernelVerifyError::NotFound(_)) => {
                counts.not_found += 1;
                class.not_found += 1;
            }
            Err(e) => {
                counts.failed += 1;
                class.resolved += 1;
                class.failed += 1;
                let reason = format!("{e}");
                if failures.len() < max_failures {
                    failures.push((name.clone(), reason.clone()));
                }
                if kind == ConstKind::Math && math_failures.len() < max_failures {
                    math_failures.push((name.clone(), reason));
                }
            }
        }
    }

    Ok(ModuleVerifyResult {
        module: module.to_string(),
        counts,
        math,
        generated,
        closure_constants,
        kernel_verified_names,
        failures,
        math_failures,
        math_sample,
        generated_sample,
        elapsed_secs: start.elapsed().as_secs_f64(),
    })
}

#[cfg(test)]
#[path = "sharded_tests.rs"]
mod tests;
