// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PER-CONSTANT streaming closure loader (`clean mathverse per-constant-verify`).
//!
//! The MODULE-closure driver ([`crate::cli::closure_load::load_targets_closure`])
//! eager-loads a target module's WHOLE transitive IMPORT closure — every module
//! it transitively imports, and EVERY constant of each — into a shared kernel
//! [`Environment`], reconstructing 250k–429k `Expr`s before a single lemma is
//! checked. For a single leaf lemma that is a ~100–400x over-approximation: the
//! measured transitive CONSTANT closure of `taylor_mean_remainder_lagrange` is
//! 3,238 constants (vs 429,100), and a reals lemma ~768.
//!
//! This loader instead demand-walks ONLY the target constant's transitive
//! constant closure (the Rust analog of Lean's `getUsedConstants` fold, via
//! [`clean_kernel::expr::Expr::collect_constants_into`]):
//!
//! 1. **name -> .olean index (header-only).** Scan every module in the target's
//!    import closure for its declared `constNames` via
//!    [`clean_olean::parse_imports_and_const_names_only`] — a `Name`-array walk
//!    that reconstructs NO `Expr`. This maps every referenced name to the
//!    `.olean` that defines it, cheaply.
//! 2. **demand walk.** Seed a worklist from the TARGET constant's own type+value
//!    `Const` refs. For each referenced name, resolve it to its `.olean`, load
//!    ONLY that constant's [`ConstantInfo`] (definitional kinds) — or, for an
//!    inductive-family member, register that ONE module's inductive families via
//!    the same trusted path the eager loader uses — into the SHARED env,
//!    `collect_constants` on it, and recurse until the closure is complete. Only
//!    modules that DEFINE a used constant are ever parsed; only used constants
//!    become resident.
//!
//!    Trusted-dependency modules are parsed **TYPES-ONLY**
//!    ([`crate::lean4::olean::olean_bridge::parse_dep_module_types_only`]): the
//!    kernel never δ-unfolds a `Theorem`/`Opaque` value, so a dependency's proof
//!    body is never reconstructed. This eliminates the peak-RSS cost — hundreds of
//!    analysis-module proof `Expr`s — that OOMs the full-value path (MVT, Taylor),
//!    and prunes the walk itself: with theorem values elided the walk never
//!    descends into proof bodies, so the closure shrinks to the statement-level
//!    dependencies the kernel actually consults. Only the TARGET module is parsed
//!    with proofs, since only its target constant is `check_type`'d.
//! 3. **verify.** Feed the target name(s) to
//!    [`clean_olean::verify_batch_full::typecheck_constants_full`] UNCHANGED.
//!
//! SOUNDNESS is IDENTICAL to the module-closure path: the closure constants are
//! TRUSTED IMPORTS (registered through the same `extend_constants_structural` /
//! inductive-family path, NOT re-checked), and ONLY the TARGET flows through the
//! kernel's `infer_sort(type) + check_type(value)` gauntlet to earn a verdict.
//! Narrowing WHICH trusted constants are resident cannot admit a false proof —
//! a missing dependency can only make the target's own `check_type`
//! conservatively FAIL, never falsely pass.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

use serde::Serialize;

use clean_kernel::env::{
    is_foundational_axiom, ConstantInfo, ConstantKind, Declaration, Environment, ProofElisionStats,
    ProofValueElision, TrustedEnvExt,
};
use clean_kernel::expr::Expr;
use clean_kernel::Name;

use crate::verify::fingerprint::decl_content_fingerprint;
use clean_olean::verify_batch::module_name_from_path;
use clean_olean::ConstantKind as OleanKind;
use clean_olean::{
    load_parsed_module_with_import_policy, parse_imports_and_const_names_only, ImportKinds,
    OleanImportPolicy, ParsedConstant, ParsedExpr, ParsedModule,
};

use crate::cli::closure_load::{
    build_closure_search_paths, resolve_module_olean, verify_one_closure_shard,
};
use crate::cli::kv_cache::{self, FingerprintMode, KvCache};
use crate::cli::{MathverseCliError, PerConstantVerifyArgs};
use crate::closure_source::{walk_refs_from_reader, ShardConstantSource};
use crate::lean4::olean::olean_bridge::{
    parse_dep_module_types_only, parse_target_module_with_proofs,
};

/// Content-addressed verdict-cache report for the JSON/human summary.
#[derive(Debug, Serialize)]
struct CacheReport {
    /// Whether `--kv-cache` was supplied AND the executable could be
    /// fingerprinted (else the cache is disabled and every target re-verifies).
    enabled: bool,
    /// Targets served from the cache (kernel re-check skipped) this run.
    hits: usize,
    /// Targets that missed and were freshly kernel-verified + recorded.
    misses: usize,
    /// The executable fingerprint the cache is bound to (`size:mtime` metadata,
    /// or `exe-blake3:…` content hash under `--kv-cache-content-hash`).
    #[serde(skip_serializing_if = "Option::is_none")]
    kernel_fingerprint: Option<String>,
    /// The deterministic digest of the demand-walked trusted closure the
    /// target(s) were checked against — the cache's per-run reproducibility
    /// witness. Emitted whenever digests are computed (cache on, or
    /// `--print-digests`). Two runs on the same (target, tree, binary) MUST
    /// print the same value; a change means the resident closure changed.
    #[serde(skip_serializing_if = "Option::is_none")]
    closure_digest: Option<String>,
    /// Per-target content digest (type + value + attributes). Same
    /// reproducibility contract as `closure_digest`.
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    target_digests: BTreeMap<String, String>,
}

/// Machine-readable summary emitted by `clean mathverse per-constant-verify`.
#[derive(Debug, Serialize)]
struct PerConstantSummary {
    ok: bool,
    generated_by: &'static str,
    target_module: String,
    targets: Vec<String>,
    /// Constants the kernel genuinely proof-checked (`infer_sort` + `check_type`).
    /// Includes targets served from the verdict cache (a cache hit is a replay
    /// of a prior kernel pass on byte-identical content — see `cache`).
    kernel_verified: usize,
    failed: usize,
    /// Targets carrying a proof VALUE (so `check_type` ran on a real proof term).
    /// If this is < `targets.len()`, the KV count for those is `infer_sort`-only.
    target_values_present: usize,
    /// The demand-walked transitive constant closure size (distinct names).
    closure_names: usize,
    /// Constants resident in the trusted env (closure + prelude) — the memory
    /// win: ~10^3, not the ~10^5 of the whole module-import closure.
    constants_resident: usize,
    modules_indexed: usize,
    modules_parsed: usize,
    /// Cap-induced re-parses under `CLEAN_MAX_PARSED_MODULES` (0 = cap unset
    /// or never exceeded — the legacy fully-resident walk).
    modules_reparsed: usize,
    inductive_modules_loaded: usize,
    /// TARGET proof values freed by `--stream-elide` after their own passing
    /// `check_type` (0 under `none` — the eager, fully-resident behavior).
    values_elided: usize,
    /// Closure names served lazily from the `--closure-shards` cache (0 =
    /// lane off/unused — the fully-eager legacy walk).
    lazy_served: usize,
    /// Shards passing / failing on-first-touch verification under the lane.
    lazy_shards_verified: usize,
    lazy_shards_failed: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    missing: Vec<String>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    errors: BTreeMap<String, String>,
    cache: CacheReport,
    index_millis: u128,
    walk_millis: u128,
    verify_millis: u128,
}

/// `clean mathverse per-constant-verify` entry point.
pub(crate) fn cmd_per_constant_verify(
    args: PerConstantVerifyArgs,
) -> Result<(), MathverseCliError> {
    let fingerprint_mode = if args.kv_cache_content_hash {
        FingerprintMode::Content
    } else {
        FingerprintMode::Metadata
    };
    let want_receipt = args.receipt.is_some() || args.receipt_leaves.is_some();
    if args.constant.is_empty() && !args.all_declared {
        return Err(MathverseCliError::StampNoInput(
            "pass at least one --constant, or --all-declared".to_string(),
        ));
    }
    // The lazy closure lane skips resident dep conversion, but the receipt
    // path's full-value axiom walk + leaf fingerprints are specified against
    // the eager env — keep receipts on the proven eager lane, loudly.
    let closure_shards = if want_receipt && args.closure_shards.is_some() {
        eprintln!(
            "per-constant-verify: --closure-shards disabled for this run — \
             --receipt/--receipt-leaves runs on the eager closure lane; running eager"
        );
        None
    } else {
        args.closure_shards.clone()
    };
    // Streaming elision frees target proof values as chunks pass, but the
    // receipt path reads them back AFTER verification (leaf fingerprints via
    // `constant_info_to_declaration` + the full-value axiom walk) — force the
    // eager policy there, loudly, rather than emit a silently-shrunk receipt.
    let stream_elide = if want_receipt && args.stream_elide != crate::cli::ClosureElide::None {
        eprintln!(
            "per-constant-verify: --stream-elide {:?} disabled for this run — \
             --receipt/--receipt-leaves needs resident proof values (leaf \
             fingerprints + axiom walk); running eager",
            args.stream_elide
        );
        crate::cli::ClosureElide::None
    } else {
        args.stream_elide
    };
    let result = per_constant_verify(
        &args.target,
        &args.closure_root,
        &args.constant,
        args.heartbeat,
        args.kv_cache.as_deref(),
        fingerprint_mode,
        args.print_digests || args.kv_cache.is_some(),
        want_receipt,
        args.all_declared,
        stream_elide.to_kernel(),
        args.stream_elide_chunk,
        closure_shards.as_deref(),
    )?;

    // P4 — emit a trust receipt over the kernel-verified target(s), if requested.
    // A commitment to what the kernel accepted (root over `(name, content-hash)`
    // leaves + the computed foundational axiom basis), independently re-derivable
    // — never a verify shortcut.
    if want_receipt {
        emit_trust_receipt(
            &result.verified_leaves,
            &result.axiom_closure,
            result.axiom_basis_complete,
            args.source_id.clone(),
            args.receipt.as_deref(),
            args.receipt_leaves.as_deref(),
            args.json,
        )?;
    }

    let summary = PerConstantSummary {
        ok: result.failed == 0 && result.missing.is_empty(),
        generated_by: "clean mathverse per-constant-verify",
        target_module: module_name_from_path(&args.target, &args.closure_root),
        targets: result.targets,
        kernel_verified: result.kernel_verified,
        failed: result.failed,
        target_values_present: result.target_values_present,
        closure_names: result.closure_names,
        constants_resident: result.constants_resident,
        modules_indexed: result.modules_indexed,
        modules_parsed: result.modules_parsed,
        modules_reparsed: result.modules_reparsed,
        inductive_modules_loaded: result.inductive_modules_loaded,
        values_elided: result.values_elided,
        lazy_served: result.lazy_served,
        lazy_shards_verified: result.lazy_shards_verified,
        lazy_shards_failed: result.lazy_shards_failed,
        missing: result.missing,
        errors: result.errors,
        cache: CacheReport {
            enabled: result.cache_enabled,
            hits: result.cache_hits,
            misses: result.cache_misses,
            kernel_fingerprint: result.cache_fingerprint,
            closure_digest: result.closure_digest,
            target_digests: result.target_digests,
        },
        index_millis: result.index_millis,
        walk_millis: result.walk_millis,
        verify_millis: result.verify_millis,
    };

    // DIAGNOSTIC: dump per-constant kernel errors to stderr so a fidelity fail's
    // divergence is visible without the slow full-base diag replay. Verdict-
    // neutral (stderr only); the errors map is already computed.
    if std::env::var("CLEAN_PRINT_ERRORS").is_ok() {
        for (name, err) in &summary.errors {
            eprintln!("=== ERROR {name} ===\n{err}\n");
        }
    }

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    if args.json {
        serde_json::to_writer_pretty(&mut out, &summary)?;
        writeln!(out)?;
    } else {
        writeln!(
            out,
            "per-constant-verify: {} kernel_verified={} (values_checked={}) failed={} closure={} resident={}{}{} \
             (modules: indexed={} parsed={}{} inductive={}){} \
             [index={}ms walk={}ms verify={}ms]{}",
            summary.targets.join(","),
            summary.kernel_verified,
            summary.target_values_present,
            summary.failed,
            summary.closure_names,
            summary.constants_resident,
            if summary.values_elided > 0 {
                format!(" elided={}", summary.values_elided)
            } else {
                String::new()
            },
            if summary.lazy_served + summary.lazy_shards_verified + summary.lazy_shards_failed > 0 {
                format!(
                    " lazy={} shards[ok={} fail={}]",
                    summary.lazy_served, summary.lazy_shards_verified, summary.lazy_shards_failed
                )
            } else {
                String::new()
            },
            summary.modules_indexed,
            summary.modules_parsed,
            if summary.modules_reparsed > 0 {
                format!(" reparsed={}", summary.modules_reparsed)
            } else {
                String::new()
            },
            summary.inductive_modules_loaded,
            if summary.cache.enabled {
                format!(
                    " cache[hit={} miss={}]",
                    summary.cache.hits, summary.cache.misses
                )
            } else {
                String::new()
            },
            summary.index_millis,
            summary.walk_millis,
            summary.verify_millis,
            if summary.missing.is_empty() {
                String::new()
            } else {
                format!(" MISSING={}", summary.missing.len())
            },
        )?;
        if let Some(cd) = &summary.cache.closure_digest {
            writeln!(out, "  closure_digest: {cd}")?;
        }
    }
    Ok(())
}

/// Outcome of a per-constant kernel-verification run.
#[derive(Debug)]
pub(crate) struct PerConstantResult {
    /// The target constant name(s) fed to `check_type`.
    pub(crate) targets: Vec<String>,
    /// Constants the kernel genuinely proof-checked (`infer_sort` + `check_type`
    /// passed). This is the `kernel_verified` count.
    pub(crate) kernel_verified: usize,
    /// Targets whose type or value the kernel REJECTED.
    pub(crate) failed: usize,
    /// Per-target error messages (empty on a clean pass).
    pub(crate) errors: BTreeMap<String, String>,
    /// How many targets carried a proof VALUE (so `check_type` genuinely ran on
    /// a proof term, not just `infer_sort` on its type). An honesty guard: a
    /// value-less target would be counted a "pass" by `infer_sort` alone.
    pub(crate) target_values_present: usize,
    /// Distinct modules whose HEADERS were scanned to build the name index.
    pub(crate) modules_indexed: usize,
    /// Distinct modules actually PARSED (with proofs) to materialize a used
    /// constant — the modules that DEFINE something in the closure.
    pub(crate) modules_parsed: usize,
    /// Cap-induced RE-parses (see `CLEAN_MAX_PARSED_MODULES`): evicted modules
    /// parsed again on a later access. 0 when the cap is unset/never exceeded.
    pub(crate) modules_reparsed: usize,
    /// Modules whose inductive families were registered (trusted).
    pub(crate) inductive_modules_loaded: usize,
    /// Constants resident in the trusted env after the walk (closure size + the
    /// prelude). The whole point: this is ~10^3, not ~10^5.
    pub(crate) constants_resident: usize,
    /// Distinct constant names in the demand-walked closure (visited set).
    pub(crate) closure_names: usize,
    /// Referenced names that resolved to NO indexed `.olean` and were not in the
    /// prelude (a coverage hole — the target may fail to verify).
    pub(crate) missing: Vec<String>,
    /// Whether the content-addressed verdict cache was active this run.
    pub(crate) cache_enabled: bool,
    /// Targets served from the cache (kernel re-check skipped).
    pub(crate) cache_hits: usize,
    /// Targets that missed the cache and were freshly verified + recorded.
    pub(crate) cache_misses: usize,
    /// The executable fingerprint the cache is bound to, if enabled.
    pub(crate) cache_fingerprint: Option<String>,
    /// The deterministic closure digest, if digests were computed (cache on or
    /// `--print-digests`). The per-run reproducibility witness.
    pub(crate) closure_digest: Option<String>,
    /// Per-target content digest, if digests were computed.
    pub(crate) target_digests: BTreeMap<String, String>,
    /// `(name, content_hash)` leaf for every KERNEL-VERIFIED target — the P4
    /// trust-receipt leaves.
    pub(crate) verified_leaves: Vec<(String, [u8; 32])>,
    /// Sorted NON-foundational axioms (domain axioms + `sorry`/trust markers) the
    /// verified set's proofs transitively reach — empty ⇒ rests only on the
    /// 3-axiom TCB. Computed by the full-value [`compute_axiom_closure`] walk.
    pub(crate) axiom_closure: Vec<String>,
    /// Whether the axiom walk resolved the ENTIRE value closure (so the closure
    /// is sound + complete). `false` if unrequested or a dependency was
    /// unresolvable (then no TCB claim is published).
    pub(crate) axiom_basis_complete: bool,
    /// Wall time (ms) building the name->olean header index.
    pub(crate) index_millis: u128,
    /// Wall time (ms) demand-walking + loading the constant closure.
    pub(crate) walk_millis: u128,
    /// Wall time (ms) running the `check_type` gauntlet on the target(s).
    pub(crate) verify_millis: u128,
    /// TARGET proof values freed by the `--stream-elide` policy after their own
    /// passing `check_type` (0 under `none`, or when nothing elidable passed).
    pub(crate) values_elided: usize,
    /// Closure names promised to the lazy shard source (skipped eager
    /// conversion; kernel materializes on demand). 0 = lane off/unused.
    pub(crate) lazy_served: usize,
    /// Shards that PASSED on-first-touch content-binding verification.
    pub(crate) lazy_shards_verified: usize,
    /// Shards that FAILED a verification gate (their names fell back eager).
    pub(crate) lazy_shards_failed: usize,
}

/// A name-array-only index from constant name -> the `.olean` that declares it,
/// built by scanning module HEADERS (no `Expr` reconstruction).
struct NameOleanIndex {
    /// Distinct `.olean` paths, de-duplicated; `by_name` stores indices into it.
    oleans: Vec<PathBuf>,
    /// name -> index into `oleans`. First declarer wins (import-order stable).
    by_name: HashMap<Name, u32>,
}

impl NameOleanIndex {
    fn olean_for(&self, name: &Name) -> Option<&Path> {
        self.by_name
            .get(name)
            .and_then(|&i| self.oleans.get(i as usize))
            .map(PathBuf::as_path)
    }
}

/// Build the `name -> .olean` index by BFS-ing the target module's transitive
/// IMPORT closure and reading each module's `constNames`/`extraConstNames`
/// header array ONLY — never a constant's `Expr`. Returns the index plus the
/// module count scanned.
fn build_name_index(
    target_olean: &Path,
    root: &Path,
    search_paths: &[PathBuf],
) -> Result<NameOleanIndex, MathverseCliError> {
    let mut oleans: Vec<PathBuf> = Vec::new();
    let mut by_name: HashMap<Name, u32> = HashMap::new();
    let mut visited: HashSet<String> = HashSet::new();
    let mut queue: VecDeque<String> = VecDeque::new();

    // Seed with the target module itself so sibling constants (same module) are
    // resolvable, then fan out over its imports.
    let target_module = module_name_from_path(target_olean, root);
    queue.push_back(target_module);

    while let Some(module) = queue.pop_front() {
        if !visited.insert(module.clone()) {
            continue;
        }
        let Some(olean) = resolve_module_olean(&module, search_paths) else {
            // A module we cannot resolve contributes no names; the coverage gate
            // at verify time is the backstop.
            continue;
        };
        let Ok(bytes) = std::fs::read(&olean) else {
            continue;
        };
        let (imports, names) = match parse_imports_and_const_names_only(&bytes) {
            Ok(v) => v,
            Err(_) => continue,
        };
        let olean_idx = oleans.len() as u32;
        let mut used_this_olean = false;
        for n in names {
            if n.is_empty() {
                continue;
            }
            // First declarer wins (matches the eager loader's insert-only model).
            by_name.entry(Name::from_string(&n)).or_insert_with(|| {
                used_this_olean = true;
                olean_idx
            });
        }
        if used_this_olean {
            oleans.push(olean);
        }
        for import in imports {
            let nm = import.module_name.trim().to_string();
            if !nm.is_empty() && !visited.contains(&nm) {
                queue.push_back(nm);
            }
        }
    }

    Ok(NameOleanIndex { oleans, by_name })
}

/// The per-constant LAZY CLOSURE LANE (design:
/// `designs/2026-07-09-lazy-closure-lane-per-constant-verify.md`, Stage 2).
///
/// Wraps a [`ShardConstantSource`] with ON-FIRST-TOUCH per-shard verification:
/// before doing any eager olean work for a closure constant, the demand walk
/// asks [`LazyLane::try_serve`]; the first touch of a shard runs the SAME
/// content-binding gates the stamp-verified lazy path runs whole-dir
/// ([`verify_one_closure_shard`]: source-olean digest + namespace subset +
/// per-constant arena `recon_digest`), amortizing gate cost to the modules a
/// run actually reaches — mandatory at whole-tree union-cache scale. A name is
/// promised only when its shard PASSED; `get()`'s per-entry serve gate then
/// honors exactly that promise at kernel resolution time. Every gate failure
/// falls back PER NAME to the eager olean walker — the same fail-closed
/// trust posture as `insert_or_upgrade`'s (closure constants are context-only;
/// a bad shard can at worst FAIL the target's check, never mint a verdict).
struct LazyLane {
    source: ShardConstantSource,
    /// The shard-cache directory (for per-shard stamp sidecars).
    shards_dir: PathBuf,
    /// Per-shard on-first-touch verification verdicts (`None` = untouched).
    /// Never retried in-process: a failed shard costs exactly one check.
    touched: Vec<Option<bool>>,
    /// Closure names promised to the lazy source (skipped eager conversion).
    served: usize,
    shards_verified: usize,
    shards_failed: usize,
}

/// A digest-bound verification stamp: records that the shard bytes with
/// `shard_blake3` passed the full structural gates against the olean bytes
/// with `olean_blake3`. Both digests are RECOMPUTED on every touch; the stamp
/// only licenses skipping the deterministic structural replay.
#[derive(serde::Serialize, serde::Deserialize)]
struct ShardVerifyStamp {
    shard_blake3: String,
    shard_len: u64,
    olean_blake3: String,
    olean_len: u64,
}

/// blake3 + length of one file.
fn file_digest(path: &Path) -> std::io::Result<([u8; 32], u64)> {
    let bytes = std::fs::read(path)?;
    Ok((*blake3::hash(&bytes).as_bytes(), bytes.len() as u64))
}

fn hex32(bytes: &[u8; 32]) -> String {
    blake3::Hash::from(*bytes).to_hex().to_string()
}

fn vstamp_path(shard_path: &Path) -> PathBuf {
    let mut s = shard_path.as_os_str().to_owned();
    s.push(".vstamp");
    PathBuf::from(s)
}

fn read_vstamp(path: &Path) -> Option<ShardVerifyStamp> {
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

/// Atomic (tmp+rename), best-effort: a failed stamp write only means the next
/// process re-runs the full gates.
fn write_vstamp(path: &Path, stamp: &ShardVerifyStamp) {
    let Ok(json) = serde_json::to_vec(stamp) else {
        return;
    };
    let tmp = path.with_extension("vstamp.tmp");
    if std::fs::write(&tmp, json).is_ok() {
        let _ = std::fs::rename(&tmp, path);
    }
}

impl LazyLane {
    fn new(source: ShardConstantSource, shards_dir: PathBuf) -> Self {
        let n = source.shard_count();
        Self {
            source,
            shards_dir,
            touched: vec![None; n],
            served: 0,
            shards_verified: 0,
            shards_failed: 0,
        }
    }

    /// Whether `name` WILL be lazily served: indexed by a shard that passes
    /// on-first-touch verification. Fail-closed: `false` sends the caller down
    /// the eager olean path for this name.
    fn try_serve(&mut self, name: &Name, search_paths: &[PathBuf]) -> bool {
        let Some(shard) = self.source.shard_of(name) else {
            return false;
        };
        let idx = shard as usize;
        match self.touched.get(idx).copied().flatten() {
            Some(verdict) => verdict,
            None => {
                let verdict = self.stamped_or_verify(idx, search_paths);
                if let Some(slot) = self.touched.get_mut(idx) {
                    *slot = Some(verdict);
                }
                if verdict {
                    self.shards_verified += 1;
                } else {
                    self.shards_failed += 1;
                }
                verdict
            }
        }
    }

    /// On-first-touch verification with a DIGEST-BOUND STAMP CACHE.
    ///
    /// The full structural gates ([`verify_one_closure_shard`]: parse the
    /// olean with proofs for the namespace-subset check + re-materialize every
    /// servable constant for the arena `recon_digest` binding) are expensive —
    /// on heavy modules they cost as much as the eager work the lane displaces.
    /// They are also DETERMINISTIC in the shard bytes and the olean bytes. So
    /// after a shard passes them once, record `(shard blake3+len, olean
    /// blake3+len)` in a `<shard>.vstamp` sidecar; a later touch recomputes
    /// BOTH digests (cheap: two file hashes — accidental corruption, staleness,
    /// or a swapped file is therefore still caught on EVERY touch) and skips
    /// only the deterministic structural replay on a full match.
    ///
    /// SOUNDNESS: byte-identical inputs make the structural gates' verdict
    /// deterministic, so skipping their replay cannot change an outcome; any
    /// byte difference misses the stamp and runs the full gates. A forged
    /// stamp requires write access to the shard dir — the same access that
    /// could swap the shard bytes themselves, which the certificate's
    /// fully-malicious-bytes carve-out already places out of scope (no signing
    /// key). Stamp writes are atomic (tmp+rename) and idempotent, so
    /// concurrent sweep processes race benignly.
    fn stamped_or_verify(&mut self, shard: usize, search_paths: &[PathBuf]) -> bool {
        // Resolve the shard file + its olean's identities. Any resolution
        // failure just means "no stamp lane" — run the full gates.
        let identities = self
            .source
            .shard_module(shard)
            .map(str::to_owned)
            .map(|module| {
                let shard_path = self.shards_dir.join(format!("{module}.mathverse"));
                let olean_digest = resolve_module_olean(&module, search_paths)
                    .and_then(|olean| crate::cli::closure_load::source_olean_digest(&olean).ok());
                (shard_path, olean_digest)
            });

        if let Some((shard_path, Some((olean_b3, olean_len)))) = &identities {
            if let Ok((shard_b3, shard_len)) = file_digest(shard_path) {
                let stamp_path = vstamp_path(shard_path);
                if let Some(stamp) = read_vstamp(&stamp_path) {
                    if stamp.shard_blake3 == hex32(&shard_b3)
                        && stamp.shard_len == shard_len
                        && stamp.olean_blake3 == hex32(olean_b3)
                        && stamp.olean_len == *olean_len
                    {
                        // Byte-identical to a prior full pass: deterministic
                        // replay skipped, serve gate flipped.
                        self.source.mark_shard_verified(shard);
                        return true;
                    }
                }
                // No/stale stamp: run the full gates; stamp on success.
                let verdict = matches!(
                    verify_one_closure_shard(&mut self.source, shard, search_paths),
                    Some(true)
                );
                if verdict {
                    write_vstamp(
                        &stamp_path,
                        &ShardVerifyStamp {
                            shard_blake3: hex32(&shard_b3),
                            shard_len,
                            olean_blake3: hex32(olean_b3),
                            olean_len: *olean_len,
                        },
                    );
                }
                return verdict;
            }
        }
        matches!(
            verify_one_closure_shard(&mut self.source, shard, search_paths),
            Some(true)
        )
    }

    /// TRANSIENTLY reconstruct `name`'s walk references from its verified
    /// shard: TYPE refs always, VALUE refs only for a DEFINITION — the exact
    /// discipline of the eager types-only dep loader
    /// (`parse_dep_module_types_only` skips Theorem/Opaque proof bodies, so
    /// the eager walk never expands their references either). This keeps the
    /// lazy walk's transitive closure EQUAL to the eager walk's (not a
    /// proof-value superset) and never materializes a theorem proof term
    /// during the walk. Deliberately bypasses `get()`'s append-only cache
    /// ([`walk_refs_from_reader`] directly), so the walk holds at most ONE
    /// reconstructed constant at a time — the kernel's verify-time cache then
    /// accumulates only the subset checking actually resolves. Mirrors
    /// `get()`'s name-binding refusal; `None` ⇒ eager fallback for this name.
    fn refs_of(&self, name: &Name) -> Option<(Expr, Option<Expr>)> {
        let (shard, idx) = self.source.shard_entry_of(name)?;
        if !self.source.is_shard_verified(shard) {
            return None;
        }
        let reader = self.source.reader(shard as usize)?;
        let (rc_name, ty, val) = walk_refs_from_reader(reader, idx)?;
        if rc_name != *name {
            return None;
        }
        Some((ty, val))
    }
}

/// The demand-walk loader state: the parsed-module cache + a name->(olean,idx)
/// map that also covers PRIVATE proof helpers (which are absent from base
/// `constNames`, so the header index cannot see them, but appear once their
/// declaring module is parsed WITH PROOFS).
struct Walker<'a> {
    root: &'a Path,
    index: &'a NameOleanIndex,
    /// olean -> its parsed-with-proofs module (cached; dropped after the walk).
    parsed: HashMap<PathBuf, ParsedModule>,
    /// name -> (olean, constant index) for every constant of a parsed module,
    /// including private helpers appended by the proof merge.
    located: HashMap<Name, (PathBuf, usize)>,
    /// oleans whose inductive families we have already registered.
    inductive_loaded: HashSet<PathBuf>,
    modules_parsed: usize,
    inductive_modules_loaded: usize,
    /// Resident parsed-module cap (`CLEAN_MAX_PARSED_MODULES`; `None` =
    /// unlimited, the legacy behavior). When exceeded, the least-recently-used
    /// TYPES-ONLY module is dropped from `parsed`; a later access re-parses it
    /// on demand (see [`Walker::parsed_constant`]). Bounds the walk's dominant
    /// transient — `parsed` holding every dependency's full `ParsedExpr` trees
    /// simultaneously — which is what OOM'd 24 GB machines on heavy
    /// AlgebraicGeometry closures.
    max_resident: Option<usize>,
    /// Monotonic LRU clock + per-module last-touch stamps.
    tick: u64,
    last_used: HashMap<PathBuf, u64>,
    /// Modules parsed WITH PROOFS (the target): PINNED, never evicted — a
    /// types-only re-parse would silently drop the proof values `check_type`
    /// needs and turn genuine verifications VACUOUS.
    full_parsed: HashSet<PathBuf>,
    /// Every olean ever parsed, so `modules_parsed` stays a DISTINCT-module
    /// count and cap-induced re-parses are surfaced separately.
    ever_parsed: HashSet<PathBuf>,
    modules_reparsed: usize,
}

impl<'a> Walker<'a> {
    /// Ensure `olean` is parsed and its constants located. `types_only` selects
    /// the TRUSTED-dependency loader ([`parse_dep_module_types_only`], which skips
    /// every `Theorem`/`Opaque` proof body); `false` selects the full
    /// proof-carrying loader ([`parse_target_module_with_proofs`]) used ONLY for
    /// the target module, whose target constant is `check_type`'d and so needs its
    /// value. Returns a reference-free success flag (the parsed module lives in
    /// `self.parsed`). A module already parsed FULL (the target) is never
    /// re-parsed type-only — the cache short-circuits — so the target keeps its
    /// value even if a later dependency walk touches its module.
    fn ensure_parsed(&mut self, olean: &Path, types_only: bool) -> bool {
        if self.parsed.contains_key(olean) {
            self.touch(olean);
            return true;
        }
        let parsed = if types_only {
            parse_dep_module_types_only(olean)
        } else {
            parse_target_module_with_proofs(olean)
        };
        let module = match parsed {
            Ok(m) => m,
            Err(_) => return false,
        };
        for (i, c) in module.constants.iter().enumerate() {
            self.located
                .entry(Name::from_string(&c.name))
                .or_insert_with(|| (olean.to_path_buf(), i));
        }
        self.parsed.insert(olean.to_path_buf(), module);
        if !types_only {
            self.full_parsed.insert(olean.to_path_buf());
        }
        if self.ever_parsed.insert(olean.to_path_buf()) {
            self.modules_parsed += 1;
        } else {
            self.modules_reparsed += 1;
        }
        self.touch(olean);
        self.evict_over_cap(olean);
        true
    }

    /// LRU bookkeeping: stamp `olean` as most-recently-used.
    fn touch(&mut self, olean: &Path) {
        self.tick += 1;
        self.last_used.insert(olean.to_path_buf(), self.tick);
    }

    /// Evict least-recently-used TYPES-ONLY modules until `parsed` is within
    /// `max_resident`. PURE CACHE POLICY — can never change a verdict:
    /// `located` keeps every `(olean, idx)` forever, deterministic parsing
    /// keeps indices stable, and [`Walker::parsed_constant`] re-parses on miss
    /// (fail-closed to `missing` if the re-parse fails, exactly as a
    /// first-parse failure would). Full-parse (target) modules and `protect`
    /// (the module just ensured, whose reference the caller may be about to
    /// take) are never victims.
    fn evict_over_cap(&mut self, protect: &Path) {
        let Some(cap) = self.max_resident else { return };
        let cap = cap.max(1);
        while self.parsed.len() > cap {
            let victim = self
                .parsed
                .keys()
                .filter(|p| !self.full_parsed.contains(*p) && p.as_path() != protect)
                .min_by_key(|p| self.last_used.get(*p).copied().unwrap_or(0))
                .cloned();
            let Some(v) = victim else { break };
            self.parsed.remove(&v);
            self.last_used.remove(&v);
        }
    }

    /// Locate the parsed `ParsedConstant` for `name`, parsing its owning module
    /// (private-aware, TYPES-ONLY — a demand-loaded dependency is trusted) on
    /// demand. Returns `(olean, constant index)`.
    fn locate(&mut self, name: &Name) -> Option<(PathBuf, usize)> {
        if let Some(loc) = self.located.get(name) {
            return Some(loc.clone());
        }
        let olean = self.index.olean_for(name)?.to_path_buf();
        if !self.ensure_parsed(&olean, true) {
            return None;
        }
        self.located.get(name).cloned()
    }

    /// Fetch the parsed constant at `(olean, idx)`, RE-PARSING the module
    /// (types-only trusted-dependency loader) if the LRU cap evicted it.
    /// Parsing is deterministic, so `(olean, idx)` from `located` resolves to
    /// the same constant across re-parses. Returns `None` (callers fail closed
    /// to `missing`) only if the re-parse itself fails — the same contract as
    /// a first-parse failure.
    fn parsed_constant(&mut self, olean: &Path, idx: usize) -> Option<&ParsedConstant> {
        if !self.parsed.contains_key(olean) && !self.ensure_parsed(olean, true) {
            return None;
        }
        self.touch(olean);
        self.parsed.get(olean)?.constants.get(idx)
    }

    /// Register `olean`'s inductive families into `env` (trusted), once. Uses the
    /// SAME `load_parsed_module` path the eager loader uses under
    /// `InductiveFamiliesOnly`, so recursor reduction rules + `is_large_elim`
    /// fixups are installed exactly as in the module-closure loader.
    fn load_inductive_families(&mut self, env: &mut Environment, olean: &Path) {
        if self.inductive_loaded.contains(olean) {
            return;
        }
        // Types-only is sufficient: inductive/constructor/recursor reconstruction
        // reads types + recursor rules, never a Theorem/Opaque proof body.
        if !self.ensure_parsed(olean, true) {
            self.inductive_loaded.insert(olean.to_path_buf());
            return;
        }
        let module = self.parsed.get(olean).expect("just ensured parsed");
        let module_name = Some(module_name_from_path(olean, self.root));
        let policy =
            OleanImportPolicy::default().with_import_kinds(ImportKinds::InductiveFamiliesOnly);
        // Best-effort: a single out-of-context module load can fail its policy
        // check; a failure just leaves the family unregistered (coverage gate
        // catches it). Never a wrong verdict.
        let _ = load_parsed_module_with_import_policy(env, module, module_name, policy);
        self.inductive_loaded.insert(olean.to_path_buf());
        self.inductive_modules_loaded += 1;
    }
}

/// Push every `Const` reference in `ty` (+ optional `val`) onto `work`, reusing
/// `scratch` so we allocate one set, not one per term.
///
/// DETERMINISM: the refs are pushed in SORTED `Name` order, not `HashSet`
/// iteration order. The demand walk pops `work` as a LIFO stack, so the push
/// order fixes the traversal order, and thus the `visited`/`missing` sets the
/// content-addressed KV cache digests over ([`crate::cli::kv_cache`]). `Name`'s
/// `Ord` is Lean's structural `cmp_core` (by string components, NOT interned
/// id), so this order is stable across processes — a given (target, olean tree,
/// binary) always walks the same closure and yields the same closure digest.
/// Without this, `HashSet` iteration order could reclassify a name as
/// resolved-vs-missing run-to-run (observed as a wobbling `MISSING` count),
/// perturbing the digest and causing spurious cache misses.
fn push_refs(ty: &Expr, val: Option<&Expr>, scratch: &mut HashSet<Name>, work: &mut Vec<Name>) {
    scratch.clear();
    ty.collect_constants_into(scratch);
    if let Some(v) = val {
        v.collect_constants_into(scratch);
    }
    let mut refs: Vec<Name> = scratch.iter().cloned().collect();
    refs.sort_unstable();
    work.extend(refs);
}

/// Kernel-verify `target_names` (constants defined in `target_olean`) by
/// demand-loading ONLY their transitive constant closure from `root`'s `.olean`
/// tree. See the module docs for the soundness argument.
pub(crate) fn per_constant_verify(
    target_olean: &Path,
    root: &Path,
    target_names_in: &[String],
    max_heartbeats: u32,
    kv_cache_path: Option<&Path>,
    fingerprint_mode: FingerprintMode,
    compute_digests: bool,
    compute_axioms: bool,
    all_declared: bool,
    stream_elide: ProofValueElision,
    stream_elide_chunk: usize,
    closure_shards: Option<&Path>,
) -> Result<PerConstantResult, MathverseCliError> {
    let search_paths = build_closure_search_paths(root);

    // LAZY CLOSURE LANE (opt-in via --closure-shards): open the shard cache up
    // front. An unusable dir is LOUD but non-fatal — the run stays fully eager
    // (sound, just slower), preserving the byte-identical default lane.
    let mut lazy: Option<LazyLane> = match closure_shards {
        None => None,
        Some(dir) => match ShardConstantSource::from_dir(dir) {
            Ok(src) => Some(LazyLane::new(src, dir.to_path_buf())),
            Err(e) => {
                eprintln!(
                    "per-constant-verify: --closure-shards `{}` unusable ({e}) — \
                     running fully eager",
                    dir.display()
                );
                None
            }
        },
    };

    // (1) name -> .olean header index (no Expr reconstruction).
    let idx_start = Instant::now();
    let index = build_name_index(target_olean, root, &search_paths)?;
    let index_millis = idx_start.elapsed().as_millis();
    let modules_indexed = index.oleans.len();

    // (2) Prelude-seeded shared env (same import-verification prelude the module
    // path uses) + demand walk.
    let mut env = Environment::try_with_prelude_for_import()
        .map_err(|e| MathverseCliError::StampPrelude(e.to_string()))?;

    let walk_start = Instant::now();
    // CLEAN_MAX_PARSED_MODULES bounds the resident parsed-module cache (LRU,
    // types-only modules only; the target is pinned). Unset/0 = unlimited
    // (legacy). Memory/perf knob only — eviction is a pure cache policy and
    // cannot change any verdict (see `Walker::evict_over_cap`).
    let max_parsed_resident: Option<usize> = std::env::var("CLEAN_MAX_PARSED_MODULES")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0);
    let mut walker = Walker {
        root,
        index: &index,
        parsed: HashMap::new(),
        located: HashMap::new(),
        inductive_loaded: HashSet::new(),
        modules_parsed: 0,
        inductive_modules_loaded: 0,
        max_resident: max_parsed_resident,
        tick: 0,
        last_used: HashMap::new(),
        full_parsed: HashSet::new(),
        ever_parsed: HashSet::new(),
        modules_reparsed: 0,
    };
    // ONE intern cache for the whole demand walk (#2383 cross-constant
    // hash-consing): every converted closure constant shares structurally
    // equal subterms instead of duplicating Mathlib's repeated type/instance
    // spines per constant. Verdict-neutral (interning is full structural
    // equality); this attacks the converted-constants env that dominates peak
    // RSS on heavy modules (see HANDOFF fix #3 measurement).
    let mut convert_session = clean_olean::ConstantConvertSession::default();

    // Seed the worklist from each target constant's own type+value refs, and
    // insert the target itself as an ordinary (trusted) constant so
    // `typecheck_constants_full` finds it in `env.constants()` and re-checks it.
    let mut work: Vec<Name> = Vec::new();
    let mut scratch: HashSet<Name> = HashSet::new();
    let mut resolved_targets: Vec<String> = Vec::new();
    let mut target_values_present = 0usize;
    {
        // The TARGET module is parsed FULL (with proofs): its target constant is
        // fed to `check_type` and so needs its real proof value. Every OTHER
        // module reached by the demand walk is a trusted dependency and comes in
        // TYPES-ONLY (see `Walker::ensure_parsed`).
        if !walker.ensure_parsed(target_olean, false) {
            return Err(MathverseCliError::StampClosure {
                module: target_olean.display().to_string(),
                reason: "failed to parse target module (with proofs)".to_string(),
            });
        }

        // The effective target list. `--all-declared` selects every value-bearing
        // (`Definition`/`Theorem`/`Opaque`) constant the target module declares —
        // a whole-module receipt — UNIONed with any explicit `--constant`s.
        // Explicit names error if absent/non-checkable; `--all-declared` names are
        // SKIPPED (a module legitimately declares inductive families/axioms).
        let mut effective: Vec<(String, bool)> =
            target_names_in.iter().map(|t| (t.clone(), true)).collect();
        if all_declared {
            let mut seen: HashSet<String> = target_names_in.iter().cloned().collect();
            if let Some(module) = walker.parsed.get(target_olean) {
                for c in &module.constants {
                    if matches!(
                        c.kind,
                        OleanKind::Definition | OleanKind::Theorem | OleanKind::Opaque
                    ) && seen.insert(c.name.clone())
                    {
                        effective.push((c.name.clone(), false));
                    }
                }
            }
        }

        for (tname, explicit) in &effective {
            let name = Name::from_string(tname);
            let Some((olean, i)) = walker.located.get(&name).cloned() else {
                if *explicit {
                    return Err(MathverseCliError::StampClosure {
                        module: target_olean.display().to_string(),
                        reason: format!("target constant `{tname}` not declared by this module"),
                    });
                }
                continue;
            };
            let Some(pc) = walker.parsed_constant(&olean, i) else {
                continue;
            };
            match convert_session.const_info(pc) {
                Ok(Some(ci)) => {
                    if ci.value.is_some() {
                        target_values_present += 1;
                    }
                    push_refs(&ci.type_, ci.value.as_ref(), &mut scratch, &mut work);
                    // Insert as trusted; it is ALSO in target_names, so it earns a
                    // verdict via check_type below (only the target does).
                    insert_or_upgrade(&mut env, ci);
                    resolved_targets.push(tname.clone());
                }
                Ok(None) => {
                    if *explicit {
                        return Err(MathverseCliError::StampClosure {
                            module: target_olean.display().to_string(),
                            reason: format!(
                                "target `{tname}` is an inductive-family member, not a checkable value"
                            ),
                        });
                    }
                    continue;
                }
                Err(e) => {
                    if *explicit {
                        return Err(MathverseCliError::StampClosure {
                            module: target_olean.display().to_string(),
                            reason: format!("target `{tname}` failed to convert: {e}"),
                        });
                    }
                    continue;
                }
            }
        }
    }
    if std::env::var("CLEAN_DIAG_ENUM").is_ok() {
        // DIAGNOSTIC: how many value-bearing constants did the target module declare
        // vs how many resolved? Distinguishes "vacuous (0 declared)" from a
        // conversion/location tool-gap. Verdict-neutral (stderr).
        let declared_vb = walker
            .parsed
            .get(target_olean)
            .map(|m| {
                m.constants
                    .iter()
                    .filter(|c| {
                        matches!(
                            c.kind,
                            OleanKind::Definition | OleanKind::Theorem | OleanKind::Opaque
                        )
                    })
                    .count()
            })
            .unwrap_or(usize::MAX);
        eprintln!(
            "CLEAN_DIAG_ENUM: target declares {declared_vb} value-bearing constants (D/T/O in its olean table); resolved_targets={}",
            resolved_targets.len()
        );
    }
    if resolved_targets.is_empty() {
        return Err(MathverseCliError::StampNoInput(
            "no checkable target constants".to_string(),
        ));
    }

    // Demand-walk the transitive constant closure.
    let mut visited: HashSet<Name> = HashSet::new();
    let mut missing: BTreeSet<Name> = BTreeSet::new();
    while let Some(name) = work.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }

        // Already present as an inductive-family member (prelude or a prior
        // load): expand its type's refs and move on.
        if let Some(t) = inductive_family_type(&env, &name) {
            push_refs(&t, None, &mut scratch, &mut work);
            continue;
        }

        // LAZY LANE: a name a verified shard serves needs NO eager conversion —
        // the kernel materializes it on demand at verify time (`get_const`
        // falls through to the installed source on an eager-map miss, and the
        // eager map keeps priority so targets/prelude legitimately shadow).
        // Walk its refs from a TRANSIENT materialization (never cached) so the
        // walk itself stays lazy. Fail-closed: any miss (unverified shard,
        // name-binding refusal, materialization failure) falls through to the
        // eager olean path below — per NAME, exactly as the design specifies.
        if let Some(lz) = lazy.as_mut() {
            if lz.try_serve(&name, &search_paths) {
                if let Some((ty, val)) = lz.refs_of(&name) {
                    push_refs(&ty, val.as_ref(), &mut scratch, &mut work);
                    lz.served += 1;
                    continue;
                }
            }
        }

        // Resolve the declaring module's parsed constant (private-aware).
        let Some((olean, i)) = walker.locate(&name) else {
            // Not in any indexed olean: rely on whatever the prelude provides.
            if let Some(ci) = env.get_const(&name) {
                let (ty, val) = (ci.type_.clone(), ci.value.clone());
                push_refs(&ty, val.as_ref(), &mut scratch, &mut work);
            } else {
                missing.insert(name);
            }
            continue;
        };
        let kind = match walker.parsed_constant(&olean, i) {
            Some(pc) => pc.kind.clone(),
            None => {
                missing.insert(name);
                continue;
            }
        };

        match kind {
            OleanKind::Inductive | OleanKind::Constructor | OleanKind::Recursor => {
                walker.load_inductive_families(&mut env, &olean);
                if let Some(t) = inductive_family_type(&env, &name) {
                    push_refs(&t, None, &mut scratch, &mut work);
                } else if let Some(ci) = env.get_const(&name) {
                    // A family aux (e.g. `.rec`) that registered as a constant.
                    let (ty, val) = (ci.type_.clone(), ci.value.clone());
                    push_refs(&ty, val.as_ref(), &mut scratch, &mut work);
                } else {
                    missing.insert(name);
                }
            }
            _ => {
                // Definitional / quotient kind: convert JUST this constant.
                // (Under CLEAN_MAX_PARSED_MODULES the module may have been
                // evicted and its re-parse can fail — fail closed to missing,
                // the same as a first-parse failure.)
                let Some(pc) = walker.parsed_constant(&olean, i) else {
                    missing.insert(name);
                    continue;
                };
                match convert_session.const_info(pc) {
                    Ok(Some(ci)) => {
                        let (ty, val) = (ci.type_.clone(), ci.value.clone());
                        insert_or_upgrade(&mut env, ci);
                        push_refs(&ty, val.as_ref(), &mut scratch, &mut work);
                    }
                    // Convert says "inductive family" or errored: fall back to the
                    // prelude, then to a VALUE-LESS trusted stub, else record the miss.
                    Ok(None) | Err(_) => {
                        if let Some(ci) = env.get_const(&name) {
                            let (ty, val) = (ci.type_.clone(), ci.value.clone());
                            push_refs(&ty, val.as_ref(), &mut scratch, &mut work);
                        } else if let Ok(Some(stub)) = convert_session.type_stub(pc) {
                            // A value-less `Theorem`/`Opaque` (types-only skipped its
                            // proof body) that the full converter rejects with
                            // `MissingValue`. These are Lean's compiler-generated
                            // private proof helpers (`_private.…._proof_N`, `._simp_N`,
                            // …), referenced only by other trusted values — the kernel
                            // never δ-unfolds them checking the target. Register a
                            // value-less stub from the TYPE so the closure is complete
                            // rather than spuriously reporting them missing. SOUND: a
                            // value-less trusted stub adds only a type; it cannot make
                            // an ill-typed target pass (see the fn's soundness note).
                            let ty = stub.type_.clone();
                            insert_or_upgrade(&mut env, stub);
                            push_refs(&ty, None, &mut scratch, &mut work);
                        } else {
                            missing.insert(name);
                        }
                    }
                }
            }
        }
    }
    let closure_names = visited.len();
    let modules_parsed = walker.modules_parsed;
    let modules_reparsed = walker.modules_reparsed;
    let inductive_modules_loaded = walker.inductive_modules_loaded;
    // Release the parsed-module cache (the heavy transient) before verifying.
    drop(walker);
    // The intern cache holds only Arc clones shared with env constants —
    // dropping it frees map overhead; the shared expression data lives on.
    drop(convert_session);

    // LAZY LANE INSTALL: hand the source to the env so verify-time `get_const`
    // resolves the promised names on demand (eager map first, source on miss).
    let (mut lazy_served, mut lazy_shards_verified, mut lazy_shards_failed) =
        (0usize, 0usize, 0usize);
    if let Some(lz) = lazy.take() {
        lazy_served = lz.served;
        lazy_shards_verified = lz.shards_verified;
        lazy_shards_failed = lz.shards_failed;
        if lz.served > 0 {
            // PRELUDE-STUB OVERRIDE (verdict parity — the exact mirror of
            // `load_targets_closure_mmap`): the prelude registers value-less
            // AXIOM STUBS for some library names; the fully-eager walk
            // OVERWRITES them with the real `.olean` definition via
            // `insert_or_upgrade`, but a lazily-served name skips that insert,
            // so the stub would survive in the eager map and — eager-first —
            // shadow the faithful shard. Mirror the eager overwrite: drop each
            // value-LESS Axiom stub whose name the source serves value-BEARING.
            // Narrow by construction (genuine inductive members are value-less
            // too but never shard-served; targets are value-bearing).
            {
                use clean_kernel::env::ConstantSource;
                let to_drop: Vec<Name> = env
                    .constants()
                    .filter(|ci| ci.value.is_none() && ci.kind == ConstantKind::Axiom)
                    .map(|ci| ci.name.clone())
                    .filter(|name| {
                        ConstantSource::get(&lz.source, name).is_some_and(|ci| ci.value.is_some())
                    })
                    .collect();
                for name in to_drop {
                    env.forget_decl(&name);
                }
            }
            env.set_constant_source(std::sync::Arc::new(lz.source));
        }
    }
    let walk_millis = walk_start.elapsed().as_millis();
    let constants_resident = env.constants().count();

    // (3) Kernel re-check the target(s) against the trusted closure env — but
    // consult the content-addressed verdict cache first, if enabled. The cache
    // key binds each target's content digest, the shared closure digest, and the
    // executable fingerprint; a hit replays a prior kernel pass on byte-identical
    // inputs, so skipping the re-check is sound (see the `kv_cache` module docs).
    let verify_start = Instant::now();

    let mut cache = kv_cache_path.and_then(|p| KvCache::open(p, fingerprint_mode));
    let cache_fingerprint = cache.as_ref().map(|c| c.fingerprint().to_string());
    let cache_enabled = cache.is_some();

    // Digests every target shares its closure key from. `visited` IS the
    // transitive constant closure — exactly the decls the kernel can consult, and
    // it is walked in a deterministic order (see `push_refs`), so this digest is
    // reproducible for a given (target, olean tree, binary). Computed when the
    // cache is active OR `--print-digests` was requested; otherwise the
    // flat-encode + blake3 pass is pure overhead and is skipped.
    let want_digests = cache_enabled || compute_digests;
    let closure_dig: Option<String> = if want_digests {
        Some(kv_cache::closure_digest(&env, visited.iter()))
    } else {
        None
    };
    let target_digests: BTreeMap<String, Option<String>> = if want_digests {
        resolved_targets
            .iter()
            .map(|t| {
                let d = env
                    .get_const(&Name::from_string(t))
                    .and_then(kv_cache::constant_content_digest);
                (t.clone(), d)
            })
            .collect()
    } else {
        BTreeMap::new()
    };

    // Partition targets into cache hits (skip the kernel) and misses (re-check).
    // A target whose digest could not be computed cannot be safely cached, so it
    // always misses and re-verifies.
    let mut cache_hits = 0usize;
    let mut to_verify: BTreeSet<String> = BTreeSet::new();
    match (cache.as_ref(), closure_dig.as_ref()) {
        (Some(c), Some(cd)) => {
            for t in &resolved_targets {
                match target_digests.get(t).and_then(|d| d.as_ref()) {
                    Some(td) if c.lookup(t, td, cd) => cache_hits += 1,
                    _ => {
                        to_verify.insert(t.clone());
                    }
                }
            }
        }
        _ => {
            to_verify = resolved_targets.iter().cloned().collect();
        }
    }

    // Kernel-check only the misses (the hits are already-earned verdicts).
    //
    // CLEAN_REDUCTION_STATS=<top-N>: dump the kernel's per-name reduction
    // statistics (unfold_by_name / iota_by_rec / whnf_miss_by_head /
    // def-eq head pairs) to stderr after the check. Diagnostic-only: the
    // report is empty unless clean-kernel was built with the
    // `reduction-stats` feature, and the counters never influence
    // verification verdicts.
    let reduction_stats_top: Option<usize> = std::env::var("CLEAN_REDUCTION_STATS")
        .ok()
        .and_then(|v| v.parse().ok().or(Some(30)));
    if reduction_stats_top.is_some() {
        clean_kernel::reduction_stats_reset();
    }
    // DIAGNOSTIC: dump the reducibility/value of specified constants from the
    // reconstructed env (CLEAN_DUMP_CONSTS=a,b,c) — reveals whether a
    // projection like `SemigroupAction.toSMul` is reducible + value-bearing
    // (so def-eq CAN unfold it) or opaque (stuck). Verdict-neutral.
    if let Ok(names) = std::env::var("CLEAN_DUMP_CONSTS") {
        for n in names.split(',').filter(|s| !s.is_empty()) {
            match env.get_const(&Name::from_string(n.trim())) {
                Some(ci) => {
                    let vhead = ci.value.as_ref().map(|v| {
                        let mut h = v;
                        while let clean_kernel::expr::ExprKind::App(f, _) = h.kind() {
                            h = f;
                        }
                        format!("{:?}", h.kind())
                    });
                    eprintln!(
                        "=== DUMP {n} === reducibility={:?} is_reducible={} has_value={} value_head={:?} levels={:?}",
                        ci.reducibility,
                        ci.is_reducible,
                        ci.value.is_some(),
                        vhead,
                        ci.level_params
                    );
                }
                None => eprintln!("=== DUMP {n} === NOT IN ENV"),
            }
        }
    }
    // DEFENSE-IN-DEPTH: the cmd wrapper already forces `None` for receipt runs;
    // re-assert here because `verified_leaves` and `compute_axiom_closure`
    // below read resident target values for the receipt path.
    let effective_elide = if compute_axioms {
        ProofValueElision::None
    } else {
        stream_elide
    };
    let (pass, fail, errors, elision_stats) = if to_verify.is_empty() {
        (
            0usize,
            0usize,
            BTreeMap::new(),
            ProofElisionStats::default(),
        )
    } else {
        clean_olean::verify_batch_full::typecheck_constants_full_streaming(
            &mut env,
            &to_verify,
            max_heartbeats,
            effective_elide,
            Some(stream_elide_chunk),
        )
    };
    if let Some(top) = reduction_stats_top {
        eprintln!("{}", clean_kernel::reduction_stats_report(top));
    }

    // Record every fresh pass (a miss target with no error entry passed cleanly),
    // then persist. Failures are never cached — only a genuine kernel pass on the
    // exact content is remembered.
    if let (Some(c), Some(cd)) = (cache.as_mut(), closure_dig.as_ref()) {
        for t in &to_verify {
            if !errors.contains_key(t) {
                if let Some(Some(td)) = target_digests.get(t) {
                    c.record(t, td.clone(), cd.clone(), closure_names);
                }
            }
        }
        c.save();
    }
    let verify_millis = verify_start.elapsed().as_millis();

    let cache_misses = to_verify.len();

    // (4) TRUST-RECEIPT leaves (P4): for every KERNEL-VERIFIED target (a resolved
    // target with no error entry — whether freshly checked or a cache hit),
    // compute a name-independent content hash from its resident `ConstantInfo`
    // (the SAME `decl_content_fingerprint` recipe the vh machinery uses).
    let verified_targets: Vec<String> = resolved_targets
        .iter()
        .filter(|t| !errors.contains_key(*t))
        .cloned()
        .collect();
    let verified_leaves: Vec<(String, [u8; 32])> = verified_targets
        .iter()
        .filter_map(|t| {
            let ci = env.get_const(&Name::from_string(t))?;
            let decl = constant_info_to_declaration(ci)?;
            let h = decl_content_fingerprint(&decl).ok()?;
            Some((t.clone(), h))
        })
        .collect();
    // The FOUNDATIONAL AXIOM BASIS. The types-only verify env cannot see axioms
    // hidden inside an elided dependency proof, so we compute the closure with a
    // dedicated, bounded, FULL-VALUE streaming walk over the verified targets
    // (`compute_axiom_closure`): every non-foundational axiom (domain axiom, or a
    // `sorry`/`sorryAx`/`trusted*` trust marker) the proof terms transitively
    // reach. Empty ⇒ the verified set rests only on the 3-axiom TCB.
    let (axiom_closure, axiom_basis_complete) = if compute_axioms && !verified_targets.is_empty() {
        compute_axiom_closure(&verified_targets, &index, &search_paths, &env)
    } else {
        (Vec::new(), false)
    };

    // Surface the digests (present iff they were computed). Drop the per-target
    // `None`s — a target whose type/value failed to flatten simply has no digest.
    let target_digests_out: BTreeMap<String, String> = target_digests
        .into_iter()
        .filter_map(|(k, v)| v.map(|d| (k, d)))
        .collect();

    Ok(PerConstantResult {
        targets: resolved_targets,
        kernel_verified: pass + cache_hits,
        failed: fail,
        errors,
        target_values_present,
        modules_indexed,
        modules_parsed,
        inductive_modules_loaded,
        constants_resident,
        closure_names,
        missing: missing.into_iter().map(|n| n.to_string()).collect(),
        cache_enabled,
        cache_hits,
        cache_misses,
        cache_fingerprint,
        closure_digest: closure_dig,
        target_digests: target_digests_out,
        verified_leaves,
        axiom_closure,
        axiom_basis_complete,
        index_millis,
        walk_millis,
        verify_millis,
        values_elided: elision_stats.total_elided(),
        modules_reparsed,
        lazy_served,
        lazy_shards_verified,
        lazy_shards_failed,
    })
}

/// Build a kernel [`Declaration`] from a resident [`ConstantInfo`] so its
/// name-independent content hash can be taken with the shared
/// [`decl_content_fingerprint`] recipe. Returns `None` for a value-less
/// non-axiom stub (a Theorem/Opaque whose proof body was elided — no checkable
/// content to commit to as a verified leaf).
fn constant_info_to_declaration(ci: &ConstantInfo) -> Option<Declaration> {
    let name = ci.name.clone();
    let level_params = ci.level_params.clone();
    let type_ = ci.type_.clone();
    match ci.kind {
        ConstantKind::Axiom => Some(Declaration::Axiom {
            name,
            level_params,
            type_,
        }),
        ConstantKind::Definition => ci.value.clone().map(|value| Declaration::Definition {
            name,
            level_params,
            type_,
            value,
            is_reducible: ci.is_reducible,
        }),
        ConstantKind::Theorem => ci.value.clone().map(|value| Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
        }),
        ConstantKind::Opaque => ci.value.clone().map(|value| Declaration::Opaque {
            name,
            level_params,
            type_,
            value,
        }),
    }
}

/// The compact per-constant fact the axiom walk needs: is it a (non-foundational)
/// axiom, and which constants does it reference. Just names + a flag — the heavy
/// `Expr`s are dropped after extraction, keeping the walk's peak memory bounded
/// to one module's proofs at a time even over a whole-corpus value closure.
struct ConstFacts {
    is_axiom: bool,
    refs: Vec<Name>,
}

/// Compute the SOUND, COMPLETE foundational-axiom basis of `verified_targets`: the
/// set of NON-foundational axioms (domain axioms + `sorry`/`sorryAx`/`trusted*`
/// trust markers) their proof terms transitively reach. Empty ⇒ the verified set
/// rests only on the 3-axiom TCB (`propext`, `Quot.sound`, `Classical.choice`).
///
/// Unlike the verify env (types-only trusted deps, so a `sorry` hidden in a
/// dependency's elided proof is invisible), this walks the FULL VALUE closure —
/// it re-parses each declaring module WITH proofs, extracts every constant's
/// `(is_axiom, refs)` into `facts`, and DROPS the reconstructed `Expr`s before
/// moving on. Peak memory is therefore one module's proof `Expr`s plus the
/// name-only `facts` map — bounded even across all of Mathlib, so it stays sound
/// where the memory-elided verify path cannot.
///
/// Returns `(sorted_non_foundational_axioms, complete)`. `complete` is `false`
/// if any referenced constant could not be resolved (then the caller must not
/// publish a within-TCB claim — an unresolved dep could hide an axiom).
fn compute_axiom_closure(
    verified_targets: &[String],
    index: &NameOleanIndex,
    search_paths: &[PathBuf],
    prelude_env: &Environment,
) -> (Vec<String>, bool) {
    let mut facts: HashMap<Name, ConstFacts> = HashMap::new();
    let mut parsed_oleans: HashSet<PathBuf> = HashSet::new();
    let mut scratch: HashSet<Name> = HashSet::new();

    // Populate `facts` for every constant of `name`'s declaring module (parsed
    // WITH proofs, then dropped). Returns false if the module can't be resolved
    // or parsed. Constants already present (from the prelude or a prior parse)
    // are left untouched.
    let mut ensure_module = |name: &Name, facts: &mut HashMap<Name, ConstFacts>| -> bool {
        if facts.contains_key(name) {
            return true;
        }
        // The base-`constNames` index maps PUBLIC names. A Lean compiler-generated
        // `_private.<Mod>.<n>.…` name (referenced cross-module in real Mathlib
        // proofs) is not indexed — derive its declaring module from the mangled
        // name so its `.olean` (with the private companion) still gets parsed;
        // otherwise the walk would spuriously mark the basis incomplete.
        let olean = match index.olean_for(name).map(Path::to_path_buf) {
            Some(o) => o,
            None => match private_prefix_module(&name.to_string())
                .and_then(|m| resolve_module_olean(&m, search_paths))
            {
                Some(o) => o,
                None => return false,
            },
        };
        if parsed_oleans.contains(&olean) {
            // Module already parsed but this name wasn't among its constants.
            return facts.contains_key(name);
        }
        let Ok(module) = parse_target_module_with_proofs(&olean) else {
            return false;
        };
        for pc in &module.constants {
            let cname = Name::from_string(&pc.name);
            if facts.contains_key(&cname) {
                continue;
            }
            // Collect const refs directly from the RAW parsed type+value — no
            // kernel `Expr` reconstruction — so EVERY kind (incl. inductive
            // families, whose `ConstantInfo` conversion returns `None`) is handled
            // uniformly and the walk never spuriously marks a family member
            // unresolved. `is_axiom` is the declared olean kind.
            let mut names: HashSet<Name> = HashSet::new();
            if let Some(t) = &pc.type_ {
                collect_parsed_consts(t, &mut names);
            }
            if let Some(v) = &pc.value {
                collect_parsed_consts(v, &mut names);
            }
            let mut refs: Vec<Name> = names.into_iter().collect();
            refs.sort_unstable();
            refs.dedup();
            facts.insert(
                cname,
                ConstFacts {
                    is_axiom: pc.kind == OleanKind::Axiom,
                    refs,
                },
            );
        }
        parsed_oleans.insert(olean);
        // `module` (and all its proof `Expr`s) drops here — bounded peak.
        facts.contains_key(name)
    };

    // Seed `facts` from the prelude for any name the prelude defines (foundational
    // axioms, quotient primitives, …) so the walk doesn't mark them unresolved.
    let record_from_env =
        |name: &Name, facts: &mut HashMap<Name, ConstFacts>, scratch: &mut HashSet<Name>| -> bool {
            let Some(ci) = prelude_env.get_const(name) else {
                return false;
            };
            scratch.clear();
            ci.type_.collect_constants_into(scratch);
            if let Some(v) = &ci.value {
                v.collect_constants_into(scratch);
            }
            let mut refs: Vec<Name> = scratch.iter().cloned().collect();
            refs.sort_unstable();
            refs.dedup();
            facts.insert(
                name.clone(),
                ConstFacts {
                    is_axiom: ci.kind == ConstantKind::Axiom,
                    refs,
                },
            );
            true
        };

    let mut visited: HashSet<Name> = HashSet::new();
    let mut work: Vec<Name> = verified_targets
        .iter()
        .map(|t| Name::from_string(t))
        .collect();
    let mut axioms: BTreeSet<String> = BTreeSet::new();
    let mut complete = true;

    while let Some(name) = work.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        // Resolve this constant's facts: an indexed olean first, then the prelude.
        if !facts.contains_key(&name)
            && !ensure_module(&name, &mut facts)
            && !record_from_env(&name, &mut facts, &mut scratch)
        {
            // Unresolved reference — could hide an axiom, so the basis is not
            // provably complete. (Foundational quotient/eq helpers the prelude
            // lacks are still safe: they are never non-foundational axioms.)
            complete = false;
            continue;
        }
        let Some(f) = facts.get(&name) else {
            complete = false;
            continue;
        };
        if f.is_axiom && !is_foundational_axiom(&name) {
            axioms.insert(name.to_string());
        }
        for r in f.refs.clone() {
            if !visited.contains(&r) {
                work.push(r);
            }
        }
    }

    (axioms.into_iter().collect(), complete)
}

/// If `s` is Lean's mangled `private` name `_private.<Mod.Path>.<macroScopeId>.…`,
/// return `<Mod.Path>` — the module whose `.olean.private` companion declares it.
/// The module is the run of components between the `_private.` prefix and the
/// first all-digit component. `None` for any non-`_private.` name.
fn private_prefix_module(s: &str) -> Option<String> {
    let rest = s.strip_prefix("_private.")?;
    let parts: Vec<&str> = rest.split('.').collect();
    let scope = parts
        .iter()
        .position(|c| !c.is_empty() && c.bytes().all(|b| b.is_ascii_digit()))?;
    if scope == 0 {
        return None;
    }
    Some(parts[..scope].join("."))
}

/// Collect every `Const` name referenced in a raw [`ParsedExpr`] tree into `out`.
/// Walks the whole term (types AND proof values) so no reference is missed. No
/// kernel `Expr` reconstruction — cheap, and uniform across every constant kind.
fn collect_parsed_consts(e: &ParsedExpr, out: &mut HashSet<Name>) {
    match e {
        ParsedExpr::Const(name, _) => {
            out.insert(Name::from_string(name));
        }
        ParsedExpr::App(f, a) => {
            collect_parsed_consts(f, out);
            collect_parsed_consts(a, out);
        }
        ParsedExpr::Lam(_, ty, body, _) | ParsedExpr::ForallE(_, ty, body, _) => {
            collect_parsed_consts(ty, out);
            collect_parsed_consts(body, out);
        }
        ParsedExpr::LetE(_, ty, val, body, _) => {
            collect_parsed_consts(ty, out);
            collect_parsed_consts(val, out);
            collect_parsed_consts(body, out);
        }
        ParsedExpr::MData(inner) | ParsedExpr::Proj(_, _, inner) => {
            collect_parsed_consts(inner, out);
        }
        ParsedExpr::BVar(_)
        | ParsedExpr::FVar(_)
        | ParsedExpr::MVar(_)
        | ParsedExpr::Sort(_)
        | ParsedExpr::Lit(_) => {}
        // `ParsedExpr` is `#[non_exhaustive]`; any leaf-like future variant
        // carries no `Const` and is safely a no-op for ref collection.
        _ => {}
    }
}

/// The type of `name` if it is a registered inductive-family member (inductive,
/// constructor, or recursor), else `None`.
fn inductive_family_type(env: &Environment, name: &Name) -> Option<Expr> {
    if let Some(iv) = env.get_inductive(name) {
        return Some(iv.type_.clone());
    }
    if let Some(cv) = env.get_constructor(name) {
        return Some(cv.type_.clone());
    }
    if let Some(rv) = env.get_recursor(name) {
        return Some(rv.type_.clone());
    }
    None
}

/// Insert a trusted constant, upgrading a value-less prelude axiom stub of the
/// same name in place when the loaded constant carries a real value (mirrors the
/// eager loader's `.olean` definition overwriting the import-prelude stub).
fn insert_or_upgrade(env: &mut Environment, ci: ConstantInfo) {
    match env.get_const(&ci.name) {
        // A real (value-bearing) constant is already resident: keep it.
        Some(existing) if existing.value.is_some() => {}
        // A value-less stub is resident and we now have a real value: upgrade.
        Some(existing)
            if existing.value.is_none()
                && existing.kind == ConstantKind::Axiom
                && ci.value.is_some() =>
        {
            let name = ci.name.clone();
            if env.upgrade_axiom_stubs(std::iter::once(ci)) == 0 {
                // Stub was not an upgradeable axiom: replace outright.
                env.forget_decl(&name);
            }
        }
        // A value-less non-upgradeable entry, or nothing: (re)insert fresh.
        Some(_) => {
            let name = ci.name.clone();
            env.forget_decl(&name);
            // SOUNDNESS: demand-loaded CLOSURE CONTEXT only (ratcheted in
            // data/unchecked_decl_ratchet.json, #4). The per-constant-verify
            // design trusts the imported constant closure exactly like
            // `stamp-verified --closure-root` trusts the eager import closure:
            // closure constants are never stamped, certified, or receipted —
            // only the named TARGET(s) run the kernel `check_type` gauntlet,
            // and only kernel-accepted targets enter a receipt. A corrupt
            // closure byte can at worst make the target's check fail, never
            // mint a false KernelVerified.
            let _ = env.extend_constants_structural(std::iter::once(ci));
        }
        None => {
            // SOUNDNESS: same trusted-closure-context justification as the
            // re-insert arm above (ratcheted in data/unchecked_decl_ratchet.json).
            let _ = env.extend_constants_structural(std::iter::once(ci));
        }
    }
}

/// Build a P4 trust receipt over `verified_leaves` and write it (and/or the
/// companion leaves manifest) to disk, printing a one-line summary unless `json`.
fn emit_trust_receipt(
    verified_leaves: &[(String, [u8; 32])],
    axiom_closure: &[String],
    axiom_basis_complete: bool,
    source_id: Option<String>,
    receipt_path: Option<&Path>,
    leaves_path: Option<&Path>,
    json: bool,
) -> Result<(), MathverseCliError> {
    use crate::verify::trust_receipt::{LeavesManifest, TrustReceipt};

    let clean_version = env!("CARGO_PKG_VERSION");
    // `axiom_closure` is the SOUND, COMPLETE set of non-foundational axioms the
    // verified proofs transitively reach (from `compute_axiom_closure`'s full-value
    // walk). Empty + complete ⇒ within_tcb=true (rests only on the 3-axiom TCB).
    let (receipt, _ordered) = TrustReceipt::build(
        verified_leaves,
        axiom_closure,
        axiom_basis_complete,
        source_id.clone(),
        clean_version,
    );

    if let Some(p) = receipt_path {
        let bytes = serde_json::to_vec_pretty(&receipt)?;
        std::fs::write(p, bytes)?;
    }
    if let Some(p) = leaves_path {
        let manifest = LeavesManifest::new(
            verified_leaves,
            axiom_closure,
            axiom_basis_complete,
            source_id,
        );
        let bytes = serde_json::to_vec_pretty(&manifest)?;
        std::fs::write(p, bytes)?;
    }
    if !json {
        let stdout = std::io::stdout();
        let mut out = stdout.lock();
        let tcb = match receipt.within_tcb {
            Some(true) => "yes",
            Some(false) => "NO",
            None => "incomplete",
        };
        writeln!(
            out,
            "trust-receipt: root={} leaves={} non_foundational_axioms={} within_tcb={}",
            receipt.merkle_root,
            receipt.leaf_count,
            receipt.axiom_closure.len(),
            tcb,
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::private_prefix_module;

    #[test]
    fn private_prefix_module_derives_declaring_module() {
        // Real cross-module `_private.*` refs the axiom walk must resolve.
        assert_eq!(
            private_prefix_module(
                "_private.Mathlib.Algebra.Order.Floor.Defs.1.FloorRing.ofBounded._proof_1"
            )
            .as_deref(),
            Some("Mathlib.Algebra.Order.Floor.Defs")
        );
        assert_eq!(
            private_prefix_module("_private.Init.Data.Nat.Gcd.1.Nat.gcd._unary._proof_1")
                .as_deref(),
            Some("Init.Data.Nat.Gcd")
        );
    }

    #[test]
    fn private_prefix_module_ignores_ordinary_and_malformed() {
        assert_eq!(private_prefix_module("Nat.add_comm"), None);
        assert_eq!(private_prefix_module("taylor_mean_remainder"), None);
        // `_private.` with no numeric macro-scope component is not a valid mangle.
        assert_eq!(private_prefix_module("_private.Foo.Bar"), None);
    }
}
