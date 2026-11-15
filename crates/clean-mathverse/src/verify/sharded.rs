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
use clean_kernel::Name;
use clean_olean::replay_order::{
    resident_refs, ReplayGraph, ReplayRefusal, ReplaySchedule, ReplayVerdicts,
};
use clean_olean::{
    load_module_with_deps_replaying_module, parse_module_file, ImportError, LoadSummary,
    OleanImportPolicy,
};
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
    /// The loader's module-trust rules refused an artifact of the module's
    /// closure (`clean_olean::ImportError::is_inconsistent_artifact`), naming
    /// the declarations in `names`: an IMPORT whose declaration depends on
    /// itself, refers forward or redeclares another import's name (the worker
    /// only trusts its imports, it never replays them), or an inconsistency of
    /// the module's own artifact the replay cannot take over. Nothing of the
    /// module is verified.
    #[error(
        "the import of module `{module}` is refused, naming {}: {reason}",
        names.join(", ")
    )]
    ImportRefused {
        /// The module whose closure was being loaded.
        module: String,
        /// The declarations the refusal is about
        /// (`clean_olean::ImportError::declaration_names`).
        names: Vec<String>,
        /// The loader's refusal.
        reason: String,
    },
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
/// 1. fresh `Environment::for_lean_replay` (no declaration beyond the closure
///    loaded next, as `leanchecker` replays into the module's imports — see the
///    call site for the rationale);
/// 2. `parse_module_file` the module's `.olean` to read its OWN `const_names`
///    (the constants this module DECLARES — not the whole closure), joined
///    after the load by every name its `.olean.server`/`.olean.private` parts
///    registered (a `module`'s private declarations live there alone);
/// 3. `load_module_with_deps_replaying_module` to register the module +
///    transitive deps (types AND values) into the env (see the call site);
/// 4. `kernel_verify_const` each OWN name in Lean's replay order; bucket the
///    verdict.
///
/// `max_failures` caps how many `(name, reason)` pairs are retained for the
/// report (counts are always exact).
///
/// # Errors
/// Returns [`ShardedVerifyError`] if the prelude cannot be built, the module's
/// `.olean` cannot be located/parsed, or the dependency-closure load fails
/// ([`ShardedVerifyError::ImportRefused`] when the loader's module-trust rules
/// refuse an artifact, naming the declarations). A per-constant kernel
/// rejection is NOT an error — it is bucketed into `failed`.
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

    // The module's OWN declared constants (NOT the whole transitive closure):
    // what its `.olean` states here, and what its other parts add after the
    // load (below).
    let parsed = parse_module_file(&olean_path).map_err(|e| ShardedVerifyError::ParseModule {
        module: module.to_string(),
        path: olean_path.display().to_string(),
        reason: format!("{e}"),
    })?;
    let mut own_set: BTreeSet<String> = BTreeSet::new();
    own_set.extend(parsed.const_names.iter().cloned());
    own_set.extend(parsed.extra_const_names.iter().cloned());

    // The IMPORT prelude used to be seeded here: it suppressed the kernel's
    // hand-rolled, non-Lean-faithful `extends`-structure stubs (`Semigroup`/
    // `Monoid`/`Group`/`Preorder`/…) that shadowed the real Mathlib structures
    // on import, because `load_module_with_deps` dedups by name.
    //
    // Lean's replay environment replaces it (`Environment::for_lean_replay`):
    // the module and its `.olean` closure, and nothing else. The import prelude
    // also seeded `sorry`/`trustedArith`/`trustedAy` and hand-written
    // declarations that shadowed same-named Lean constants, and a reference to
    // one type-checked here where `leanchecker` reports an unknown constant.
    let mut env = Environment::for_lean_replay();

    // `leanchecker <module>` replays the module's own declarations and refuses
    // a self-dependent declaration, a use of one, or a redeclaration of an
    // import's name PER DECLARATION, never at load. So does `ModuleReplay`
    // below (the replay order, and `already_declared`), so the module's OWN
    // parts load with the loader's module-trust rules 1 and 3 left to it
    // (`load_module_with_deps_replaying_module`): under the default load such a
    // module was refused whole, as a load error. Whatever an IMPORT gets wrong
    // still refuses the import: this worker only trusts its imports, and its
    // verdicts are merged over a corpus with no cross-module pass
    // (`mathverse_shard sharded --corpus-sharded`), so an import whose
    // declaration depends on itself is refused at load rather than trusted as
    // `leanchecker` trusts it (`ShardedVerifyError::ImportRefused`).
    let summaries = load_module_with_deps_replaying_module(
        &mut env,
        module,
        search_paths,
        // Its imports refuse a refused completion of their own stubs (R131),
        // as they refuse every other inconsistency; the module's own parts,
        // loaded with their rules left to the replay below, record it.
        OleanImportPolicy::default().refusing_refused_completions(),
    )
    .map_err(|e| load_error(module, &e))?;
    // This module's declarations the loader dropped because an import already
    // held the name: Lean's `addDecl` refuses them as already declared.
    let already_declared: std::collections::BTreeMap<Name, String> = summaries
        .iter()
        .filter(|s| is_own_part(s, module))
        .flat_map(|s| s.shadowed_declarations.iter().cloned())
        .collect();
    // This module's family records the loader REFUSED (a recursor, constructor
    // or inductive record the kernel does not derive from the stored family,
    // clean-kernel `env/imported_family.rs`): never resident, so they are
    // failures with the loader's reason, not `not_found`.
    let refused_at_load: std::collections::BTreeMap<String, String> = summaries
        .iter()
        .filter(|s| is_own_part(s, module))
        .flat_map(|s| s.skipped_constants.iter())
        .filter(|sk| sk.reason.contains("imported family record"))
        .map(|sk| (sk.name.clone(), sk.reason.clone()))
        .collect();
    // Every declaration the module's parts registered, or dropped as another
    // module's name, is the module's own and is replayed. A `module`-system
    // artifact's private declarations live in its `.olean.private` alone, and
    // `leanchecker` (a consumer that is not itself a `module`) reads the
    // artifact through that part and replays them with the rest (`clean olean
    // replay` takes its targets from the same summaries). Measured 2026-09-29:
    // with the replay set the `.olean`'s names alone, a private declaration was
    // never replayed, and the relaxed load above registered
    // `ReplayForgedPriv`'s private `priv_self : False := priv_self` as stored,
    // so `priv_user : False := priv_self` was verified.
    for summary in summaries.iter().filter(|s| is_own_part(s, module)) {
        own_set.extend(summary.added_names.iter().map(ToString::to_string));
        own_set.extend(
            summary
                .shadowed_declarations
                .iter()
                .map(|(name, _)| name.to_string()),
        );
    }
    own_set.extend(refused_at_load.keys().cloned());
    // This module's declarations its authoritative part states with a value
    // the load did not make resident with it (R131's kernel-refused
    // completions, and R142's invariant: a value that did not convert, a name
    // an import holds, `LoadSummary::refused_completions`). Lean reads the
    // declaration with the value: each is a failure with the loader's reason,
    // never an accepted axiom, and every use of one is refused by the replay's
    // admission gate. Before R131 and R142 the stub was checked as the axiom it
    // was left as (`axiom_accepted`) and its user verified.
    let refused_completions: std::collections::BTreeMap<Name, String> = summaries
        .iter()
        .filter(|s| is_own_part(s, module))
        .flat_map(|s| s.refused_completions.iter().cloned())
        .collect();
    let own_names: Vec<String> = own_set.into_iter().collect();
    // The trusted closure is loaded; every check from here re-checks a Lean
    // `.olean` module, so it runs in Lean's kernel theory (reducers Lean's
    // kernel has, Lean's safe context), `clean_kernel::env::kernel_theory`.
    env.set_kernel_theory(clean_kernel::env::KernelTheory::Lean);

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

    // Lean's replay order (`clean_olean::replay_order`, porting
    // `Lean/Replay.lean`): the module's own constants are all resident, so
    // without it a value could lean on itself or on a module-mate that leans
    // back on it. Each constant is checked only after every module-local
    // constant it uses was admitted; unsafe/partial ones are never admitted.
    let replay = ModuleReplay::new(&env, &own_names, &already_declared);
    let mut verdicts = ReplayVerdicts::new();

    for name in &replay.order {
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

        let key = Name::from_string(name);
        if let Some(reason) = refused_completions.get(&key) {
            counts.failed += 1;
            class.resolved += 1;
            class.failed += 1;
            let reason = format!(
                "the module's authoritative part states it with a value the load did not make \
                 resident: {reason}"
            );
            if failures.len() < max_failures {
                failures.push((name.clone(), reason.clone()));
            }
            if kind == ConstKind::Math && math_failures.len() < max_failures {
                math_failures.push((name.clone(), reason.clone()));
            }
            verdicts.insert(
                key.clone(),
                Err(ReplayRefusal::KernelRejected {
                    name: key,
                    message: reason,
                }),
            );
            continue;
        }
        let admitted = if replay.scheduled.contains(&key) {
            replay
                .schedule
                .admission_gate(&key, &verdicts)
                .and_then(|()| replay.families.get(&key).cloned().map_or(Ok(()), Err))
        } else {
            Ok(())
        };
        if let Err(refusal) = admitted {
            // The constant itself unsafe/partial: never admitted, never a
            // failure (Lean's replay skips it) — accepted as context, as the
            // sequential lane's `UnsafeAccepted` is.
            if matches!(refusal, ReplayRefusal::NotReplayable { name: ref n, .. } if *n == key) {
                counts.axiom_accepted += 1;
                class.resolved += 1;
                class.axiom_accepted += 1;
            } else {
                counts.failed += 1;
                class.resolved += 1;
                class.failed += 1;
                let reason = refusal.to_string();
                if failures.len() < max_failures {
                    failures.push((name.clone(), reason.clone()));
                }
                if kind == ConstKind::Math && math_failures.len() < max_failures {
                    math_failures.push((name.clone(), reason));
                }
            }
            verdicts.insert(key, Err(refusal));
            continue;
        }
        let verdict =
            crate::lean4::kernel_verify::kernel_verify_const_with_heartbeat(&env, name, heartbeat);
        verdicts.insert(
            key.clone(),
            match &verdict {
                Ok(_) => Ok(()),
                Err(e) => Err(ReplayRefusal::KernelRejected {
                    name: key,
                    message: e.to_string(),
                }),
            },
        );
        match verdict {
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
            Err(crate::lean4::kernel_verify::KernelVerifyError::NotFound(_))
                if !refused_at_load.contains_key(name) =>
            {
                counts.not_found += 1;
                class.not_found += 1;
            }
            Err(crate::lean4::kernel_verify::KernelVerifyError::NotFound(_)) => {
                counts.failed += 1;
                class.resolved += 1;
                class.failed += 1;
                let reason = refused_at_load.get(name).cloned().unwrap_or_default();
                if failures.len() < max_failures {
                    failures.push((name.clone(), reason.clone()));
                }
                if kind == ConstKind::Math && math_failures.len() < max_failures {
                    math_failures.push((name.clone(), reason));
                }
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

/// A closure load that failed, as the worker reports it: a module-trust
/// refusal that names declarations is [`ShardedVerifyError::ImportRefused`],
/// anything else [`ShardedVerifyError::LoadDeps`].
fn load_error(module: &str, error: &ImportError) -> ShardedVerifyError {
    let names: Vec<String> = error
        .declaration_names()
        .into_iter()
        .map(str::to_owned)
        .collect();
    if error.is_inconsistent_artifact() && !names.is_empty() {
        ShardedVerifyError::ImportRefused {
            module: module.to_owned(),
            names,
            reason: error.to_string(),
        }
    } else {
        ShardedVerifyError::LoadDeps {
            module: module.to_owned(),
            reason: error.to_string(),
        }
    }
}

/// Whether `summary` is one of `module`'s own parts (its `.olean`,
/// `.olean.server` or `.olean.private`), not an import's.
fn is_own_part(summary: &LoadSummary, module: &str) -> bool {
    summary.module_name.as_deref().is_some_and(|label| {
        label
            .strip_suffix("._server")
            .or_else(|| label.strip_suffix("._private"))
            .unwrap_or(label)
            == module
    })
}

/// One module's own constants scheduled in Lean's replay order.
struct ModuleReplay {
    schedule: ReplaySchedule,
    /// The own names the environment holds (the schedule's nodes).
    scheduled: BTreeSet<Name>,
    /// Every own name: the scheduled ones in replay order, then the ones the
    /// environment does not hold (they report `not_found`, as before).
    order: Vec<String>,
    /// Inductive-family members Lean's replay would not admit
    /// (`clean_olean::replay_families`): every stored constructor and recursor
    /// must be what the kernel generates from the block's stored types.
    families: std::collections::BTreeMap<Name, ReplayRefusal>,
}

impl ModuleReplay {
    fn new(
        env: &Environment,
        own_names: &[String],
        already_declared: &std::collections::BTreeMap<Name, String>,
    ) -> Self {
        let resident = |n: &Name| {
            env.get_const(n).is_some()
                || env.get_inductive(n).is_some()
                || env.get_constructor(n).is_some()
                || env.get_recursor(n).is_some()
        };
        let mut graph = ReplayGraph::new();
        let mut spelled: std::collections::BTreeMap<Name, String> = Default::default();
        let mut absent = Vec::new();
        for name in own_names {
            let key = Name::from_string(name);
            if !resident(&key) {
                absent.push(name.clone());
                continue;
            }
            graph.insert(key.clone(), resident_refs(env, &key));
            let safety = if env.is_unsafe(&key) {
                Some("unsafe")
            } else if env.is_partial(&key) {
                Some("partial")
            } else {
                None
            };
            if let Some(safety) = safety {
                graph.refuse(
                    key.clone(),
                    ReplayRefusal::NotReplayable {
                        name: key.clone(),
                        safety,
                    },
                );
            }
            if let Some(held_by) = already_declared.get(&key) {
                graph.refuse(
                    key.clone(),
                    ReplayRefusal::AlreadyDeclared {
                        name: key.clone(),
                        reason: held_by.clone(),
                    },
                );
            }
            spelled.insert(key, name.clone());
        }
        let schedule = graph.schedule();
        // Absent own names too: a family record the loader refused still names
        // a member of its block, which the replay then refuses whole.
        let local: BTreeSet<Name> = spelled
            .keys()
            .cloned()
            .chain(absent.iter().map(|name| Name::from_string(name)))
            .collect();
        let families = clean_olean::replay_families::inductive_block_refusals(env, &local, &local);
        let mut order: Vec<String> = schedule
            .order()
            .iter()
            .filter_map(|k| spelled.get(k).cloned())
            .collect();
        order.extend(absent);
        let scheduled = spelled.into_keys().collect();
        Self {
            schedule,
            scheduled,
            order,
            families,
        }
    }
}

#[cfg(test)]
#[path = "sharded_tests.rs"]
mod tests;
