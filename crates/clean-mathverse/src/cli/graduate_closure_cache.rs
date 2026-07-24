// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Content-addressed cached closure loader for `clean mathverse graduate --env olean`.
//!
//! `graduate --env olean` builds its source [`Environment`] by reconstructing the
//! transitive `.olean` import closure of the declared modules from scratch
//! ([`clean_olean::load_modules_with_deps`]) — the dominant cost of a real-Mathlib
//! graduation (proof-term conversion of the whole closure). This module layers a
//! CONTENT-ADDRESSED, OPT-IN, FAIL-CLOSED cache over that load:
//!
//! - **KEY** — a single blake3 *union digest* over the EXACT `.olean` set of the
//!   declared modules' transitive closure (each resolved `.olean`++`.private`++
//!   `.server`, via [`source_olean_digest`], folded with a [`CACHE_FORMAT_VERSION`]
//!   recipe tag and [`SHARD_VERSION`]). The cache directory is opt-in via the
//!   `$CLEAN_CLOSURE_CACHE_DIR` env var; UNSET means the cache is fully bypassed and
//!   behavior is byte-for-byte the legacy eager load (zero default behavior change).
//!
//! - **SUBSTRATE** — the existing v3 fail-closed `.mathverse` closure shards
//!   ([`build_closure_shards_for_targets`]): a kernel-faithful, source-olean-bound,
//!   per-constant-recon-digest-stamped flat-expr arena. We do NOT invent a new
//!   format. Inductive families (Inductive/Constructor/Recursor/Quot) stay
//!   EAGER-from-olean (the shard format cannot losslessly carry recursor reduction
//!   rules — a confirmed false-accept hole, roadmap Phase-2/L2); the definitional
//!   kinds (Definition/Theorem/Axiom/Opaque) are reconstructed from the cached
//!   shards, skipping the expensive proof-term re-conversion. (Auto-generated
//!   `*.noConfusion` eliminators are Definition-kind but neither eager-regenerated
//!   nor shard-served — see the FAITHFULNESS BOUNDARY below.)
//!
//! - **WARM LOAD** (cache HIT) — eager-load the closure's inductive families from
//!   `.olean` ([`ImportKinds::InductiveFamiliesOnly`]), then materialize every
//!   cached definitional constant into the SAME env via the trusted-import
//!   [`TrustedEnvExt::extend_constants_structural`] hook (the byte-identical path
//!   the eager `.olean` importer uses for these constants). The result is a fully
//!   populated, ENUMERABLE env (so `--all` theorem enumeration over
//!   `env.constants()` is faithful) whose constant set is a faithful SUBSET of the
//!   eager load's (see the FAITHFULNESS BOUNDARY below).
//!
//! - **COLD LOAD** (cache MISS) — the caller reconstructs eagerly as today, then we
//!   best-effort populate the cache (build the shards + write a manifest). A
//!   cache-write failure never fails the graduation.
//!
//! SOUNDNESS BOUNDARY (load-bearing): the cached closure is the *source env* for
//! graduation; the kernel RE-CHECKS every candidate from scratch downstream
//! (`graduate_with_base_keep_env` → `add_decl`'s `check_type`). The cache is a LOAD
//! ACCELERATOR, **NOT** in the TCB — a stale/corrupt/forged cache cannot mint a
//! `KernelVerified`: a candidate that depends on a cache-corrupted constant fails
//! type-checking. Defense in depth on top of that:
//!   1. CONTENT-ADDRESSED — the entry directory is named by, and the manifest
//!      records, the union digest of the exact live `.olean` set; a digest mismatch
//!      => MISS => reconstruct.
//!   2. PER-SHARD BINDING — each served shard's `source_olean_blake3` is recomputed
//!      against the live on-disk `.olean` for its declaring module; a mismatch
//!      leaves the shard unverified (its `get()`s return `None`) => coverage miss.
//!   3. COVERAGE — every module in the closure must have a verified, source-bound
//!      shard; any gap => MISS => reconstruct. (Conservative: a purely-inductive
//!      module without a shard also forces the cold path.)
//! On ANY of these failing, [`decide`] returns [`CacheDecision::Miss`] /
//! [`fast_load`] returns `None`, and the caller falls back to the trusted eager
//! reconstruction — never a silently-wrong closure.
//!
//! FAITHFULNESS BOUNDARY (measured): the warm env is a faithful *subset* of the
//! cold eager env — `warm ⊆ cold`, never the reverse. On a real Mathlib closure
//! (`Mathlib.Init`, 1126 modules) the warm env carries 117,873 of the cold load's
//! 119,618 constants (98.54%); every constant it DOES carry is structurally
//! identical to eager (kind / level-params / type / value — pinned by
//! `graduate_closure_cache_tests::test_warm_load_is_faithful_to_cold`). The entire
//! 1,745-constant residual is auto-generated `*.noConfusion` constructor
//! eliminators: these are `Definition`-kind, so the [`ImportKinds::InductiveFamiliesOnly`]
//! eager leg skips them, and they are not serialized into the definitional shards,
//! so the warm reconstruction omits them. This is a COMPLETENESS gap, NOT a
//! soundness one: because `warm ⊆ cold`, the cache can only ever OMIT a constant,
//! never ADD or ALTER one — so it can never make a candidate type-check that
//! wouldn't under the eager env (no forged `KernelVerified`). A candidate whose
//! proof term references an omitted `noConfusion` simply fails its kernel re-check
//! (`ConstNotFound`) under a warm env and is REJECTED — a false negative that the
//! caller can always resolve by clearing `$CLEAN_CLOSURE_CACHE_DIR` to force the
//! eager path. Closing the gap (regenerating `noConfusion` in the warm leg) is
//! tracked as future work; the cache stays opt-in until then.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::{Path, PathBuf};

use clean_kernel::env::{ConstantInfo, ConstantSource, ProofValueElision, TrustedEnvExt};
use clean_kernel::{Environment, Name};
use clean_olean::{
    load_module_with_deps_bounded_shared_with_policy, parse_imports_only, ImportKinds,
    OleanImportPolicy,
};

use crate::cli::closure_load::{
    build_closure_shards_for_targets_with_search_paths, max_closure_modules, source_olean_digest,
};
use crate::closure_source::ShardConstantSource;
use crate::shard::SHARD_VERSION;

/// Cache-recipe version. Bump to invalidate every previously-written entry when the
/// reconstruction recipe (what we serialize / how we warm-load) changes in a way
/// that the `.olean`-set digest alone would not capture. Folded into the union
/// digest, so a bump simply re-keys every entry (old entries become unreachable —
/// cold reconstruct + repopulate under the new key).
pub(crate) const CACHE_FORMAT_VERSION: u32 = 1;

/// Opt-in env var naming the cache root. Unset/empty => the cache is bypassed and
/// the eager load runs unchanged (zero default behavior change).
pub(crate) const CACHE_DIR_ENV: &str = "CLEAN_CLOSURE_CACHE_DIR";

/// Manifest file written into each per-digest entry directory.
const MANIFEST_FILE: &str = "manifest.json";

/// Everything [`decide`] resolved about a single graduate closure load: enough for
/// a warm fast-load AND for a cold-miss populate, computed once.
#[derive(Debug, Clone)]
pub(crate) struct CachePlan {
    /// The olean search paths graduate resolves the closure against (authoritative).
    search_paths: Vec<PathBuf>,
    /// Root passed to the campaign shard builder (`--lake-project` if given, else
    /// the first search path).
    root: PathBuf,
    /// The declared top-level modules' resolved `.olean` files (shard-build targets).
    target_oleans: Vec<PathBuf>,
    /// Every module in the transitive closure (resolvable under `search_paths`),
    /// including the declared targets.
    closure_modules: BTreeSet<String>,
    /// `module -> resolved .olean`, for the union digest and the per-shard binding.
    closure_oleans: BTreeMap<String, PathBuf>,
    /// Lowercase-hex union digest over the closure's `.olean` set + recipe tag.
    union_digest_hex: String,
    /// `<cache_root>/<union_digest_hex>` — the content-addressed entry directory.
    entry_dir: PathBuf,
}

/// Outcome of consulting the cache for a graduate closure load.
pub(crate) enum CacheDecision {
    /// `$CLEAN_CLOSURE_CACHE_DIR` is unset, or the closure could not be resolved for
    /// keying. The caller cold-loads exactly as before; no populate.
    Disabled,
    /// Cache miss. The caller cold-loads, then calls [`populate`] with this plan.
    Miss(CachePlan),
    /// Cache hit: a fully-populated, faithful, enumerable env.
    Hit(Box<Environment>),
}

/// Consult the content-addressed cache for the closure of `modules`.
///
/// `lake_project` is `--lake-project` (used only to pick the shard-builder root).
pub(crate) fn decide(
    modules: &[String],
    search_paths: &[PathBuf],
    lake_project: Option<&Path>,
) -> CacheDecision {
    let Some(cache_root) = cache_root_from_env() else {
        return CacheDecision::Disabled;
    };
    // Resolve the declared modules to their .olean files (shard-build targets). If
    // any cannot be resolved under graduate's own search paths, we cannot key the
    // cache; bypass and let the eager loader speak for the failure.
    let mut target_oleans = Vec::with_capacity(modules.len());
    for m in modules {
        match resolve_module_olean(m, search_paths) {
            Some(p) => target_oleans.push(p),
            None => return CacheDecision::Disabled,
        }
    }

    let (closure_modules, closure_oleans) = closure_bfs(modules, search_paths);
    let Some(union_digest_hex) = compute_union_digest(&closure_oleans) else {
        return CacheDecision::Disabled;
    };

    // SHARD-BUILDER ROOT (load-bearing): `build_closure_shards_for_targets` derives
    // BOTH the module NAMES (`module_name_from_path(target, root)`) AND its own olean
    // search paths (`build_closure_search_paths(root)`, which walks ancestors for the
    // `.lake/packages` dir) relative to THIS root, so it must be the LIB dir
    // (`<proj>/.lake/build/lib/lean`) — NOT the bare `--lake-project` dir. The eager
    // loader's resolved search paths put that lib dir FIRST (see
    // `lake_project_search_paths`), so `search_paths.first()` is exactly it. Passing
    // the lake-project root instead would name the target `.lake.build.lib.lean.<M>`
    // and try to resolve every `<Pkg>.*` olean under a nonexistent `<proj>/<Pkg>/...`,
    // leaving the populated closure covering ONLY the toolchain-core modules — so
    // `fully_covered` is never reached and the warm load MISSES forever on any real
    // lake project. Prefer the lib dir; fall back to the raw project dir then `.`.
    let root = search_paths
        .first()
        .cloned()
        .or_else(|| lake_project.map(Path::to_path_buf))
        .unwrap_or_else(|| PathBuf::from("."));
    let entry_dir = cache_root.join(&union_digest_hex);

    let plan = CachePlan {
        search_paths: search_paths.to_vec(),
        root,
        target_oleans,
        closure_modules,
        closure_oleans,
        union_digest_hex,
        entry_dir,
    };

    match fast_load(&plan) {
        Some(env) => CacheDecision::Hit(Box::new(env)),
        None => CacheDecision::Miss(plan),
    }
}

/// The cache root from `$CLEAN_CLOSURE_CACHE_DIR`, or `None` when unset/empty.
fn cache_root_from_env() -> Option<PathBuf> {
    let v = std::env::var_os(CACHE_DIR_ENV)?;
    if v.is_empty() {
        return None;
    }
    Some(PathBuf::from(v))
}

/// Resolve a dotted Lean module NAME (`Mathlib.Logic.Basic`) to its `.olean` file,
/// trying each search path in order — the same resolution the campaign loader uses.
fn resolve_module_olean(module: &str, search_paths: &[PathBuf]) -> Option<PathBuf> {
    let rel: PathBuf = module
        .split('.')
        .collect::<PathBuf>()
        .with_extension("olean");
    search_paths
        .iter()
        .map(|p| p.join(&rel))
        .find(|c| c.is_file())
}

/// BFS the transitive import closure of `modules` over `search_paths`, returning the
/// set of resolvable closure modules (including the targets) and their `.olean`
/// paths. Imports that do not resolve under `search_paths` are skipped — exactly as
/// the eager load would also fail to find them (so warm and cold agree on coverage).
fn closure_bfs(
    modules: &[String],
    search_paths: &[PathBuf],
) -> (BTreeSet<String>, BTreeMap<String, PathBuf>) {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut oleans: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut queue: VecDeque<String> = modules.iter().cloned().collect();

    while let Some(module) = queue.pop_front() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let Some(olean) = resolve_module_olean(&module, search_paths) else {
            // Unresolved import: not in the keyed closure (cold load also lacks it).
            seen.remove(&module);
            continue;
        };
        let Ok(bytes) = std::fs::read(&olean) else {
            seen.remove(&module);
            continue;
        };
        oleans.insert(module.clone(), olean);
        if let Ok(imports) = parse_imports_only(&bytes) {
            for import in imports {
                let nm = import.module_name.trim().to_string();
                if !nm.is_empty() && !seen.contains(&nm) {
                    queue.push_back(nm);
                }
            }
        }
    }
    (seen, oleans)
}

/// The union digest over the closure's `.olean` set, lowercase hex, or `None` on any
/// read error (=> the cache is bypassed for this load). Order-independent: modules
/// are folded in sorted (`BTreeMap`) order, each as
/// `len(module)||module || source_olean_digest.hash || source_olean_digest.len`,
/// after a domain-separation tag and the recipe/shard version tags.
fn compute_union_digest(closure_oleans: &BTreeMap<String, PathBuf>) -> Option<String> {
    if closure_oleans.is_empty() {
        return None;
    }
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"clean-closure-cache\0");
    hasher.update(&CACHE_FORMAT_VERSION.to_le_bytes());
    hasher.update(&SHARD_VERSION.to_le_bytes());
    for (module, olean) in closure_oleans {
        let (hash, len) = source_olean_digest(olean).ok()?;
        hasher.update(&(module.len() as u64).to_le_bytes());
        hasher.update(module.as_bytes());
        hasher.update(&hash);
        hasher.update(&len.to_le_bytes());
    }
    Some(hasher.finalize().to_hex().to_string())
}

/// Attempt a faithful WARM load from the cache entry. Returns `None` on ANY
/// fail-closed condition (missing/foreign/stale manifest, partial coverage, a
/// per-shard source-olean binding mismatch, a decode/extend failure) so the caller
/// hard-falls-back to the trusted eager reconstruction.
fn fast_load(plan: &CachePlan) -> Option<Environment> {
    // Opt-in diagnostics (off by default; zero noise). Set `CLEAN_CLOSURE_CACHE_DEBUG`
    // to log the exact fail-closed gate that forced a cold fallback.
    let dbg = std::env::var_os("CLEAN_CLOSURE_CACHE_DEBUG").is_some();
    macro_rules! miss {
        ($($a:tt)*) => {{
            if dbg { eprintln!("[closure-cache] MISS: {}", format_args!($($a)*)); }
            return None;
        }};
    }

    let Some(manifest) = Manifest::read(&plan.entry_dir.join(MANIFEST_FILE)) else {
        miss!("no/unreadable manifest at {}", plan.entry_dir.display());
    };
    // Content-address + recipe gates (defense in depth over the entry-dir name).
    if manifest.union_digest != plan.union_digest_hex {
        miss!("union digest mismatch");
    }
    if manifest.cache_format_version != CACHE_FORMAT_VERSION
        || manifest.shard_version != SHARD_VERSION
    {
        miss!(
            "recipe/shard version mismatch (cache_fmt {} vs {}, shard {} vs {})",
            manifest.cache_format_version,
            CACHE_FORMAT_VERSION,
            manifest.shard_version,
            SHARD_VERSION
        );
    }
    if !manifest.fully_covered {
        miss!("manifest fully_covered=false");
    }

    // Open the shard source and re-bind each shard to its live on-disk .olean. Only
    // a shard whose recomputed source digest matches its header is marked verified
    // (and can therefore serve); an unverified shard's get() returns None.
    let mut source = match ShardConstantSource::from_dir(&plan.entry_dir) {
        Ok(s) => s,
        Err(e) => miss!("ShardConstantSource::from_dir failed: {e}"),
    };
    let mut verified_modules: BTreeSet<String> = BTreeSet::new();
    let mut unreadable = 0usize;
    let mut unstamped = 0usize;
    let mut unresolved = 0usize;
    let mut digest_mismatch = 0usize;
    for shard in 0..source.shard_count() {
        let bound = {
            let Some(reader) = source.reader(shard) else {
                unreadable += 1;
                continue;
            };
            if reader.header.source_olean_blake3 == [0u8; 32]
                || reader.header.fail_closed_verified != 1
            {
                None
            } else {
                reader.source_module.clone().map(|module| {
                    (
                        module,
                        reader.header.source_olean_blake3,
                        reader.header.source_olean_len,
                    )
                })
            }
        };
        let Some((module, hdr_hash, hdr_len)) = bound else {
            unstamped += 1;
            continue;
        };
        let Some(olean) = plan
            .closure_oleans
            .get(&module)
            .cloned()
            .or_else(|| resolve_module_olean(&module, &plan.search_paths))
        else {
            unresolved += 1;
            continue;
        };
        let Ok((live_hash, live_len)) = source_olean_digest(&olean) else {
            unresolved += 1;
            continue;
        };
        if live_hash == hdr_hash && live_len == hdr_len {
            source.mark_shard_verified(shard);
            verified_modules.insert(module);
        } else {
            digest_mismatch += 1;
        }
    }
    if dbg {
        eprintln!(
            "[closure-cache] shards={} verified={} unreadable={} unstamped={} unresolved={} digest_mismatch={}",
            source.shard_count(),
            verified_modules.len(),
            unreadable,
            unstamped,
            unresolved,
            digest_mismatch
        );
    }

    // COVERAGE: every closure module must have a verified, source-bound shard. A gap
    // (missing/unverified shard, e.g. a purely-inductive module or a swapped olean)
    // forces the trusted cold path — conservative, never a wrong-but-fast closure.
    let missing: Vec<&String> = plan
        .closure_modules
        .iter()
        .filter(|m| !verified_modules.contains(*m))
        .collect();
    if !missing.is_empty() {
        miss!(
            "coverage gap: {}/{} closure modules unverified, e.g. {:?}",
            missing.len(),
            plan.closure_modules.len(),
            missing.iter().take(8).collect::<Vec<_>>()
        );
    }

    // EAGER LEG: inductive families (+ regenerated noConfusion) from .olean, exactly
    // as the eager importer registers them — the shard format cannot carry recursor
    // rules losslessly. Definitional kinds are skipped here (served from shards).
    let mut env = Environment::default();
    let policy = OleanImportPolicy::default()
        .with_proof_elision(ProofValueElision::None)
        .with_import_kinds(ImportKinds::InductiveFamiliesOnly);
    let mut visited: hashbrown::HashSet<String> = hashbrown::HashSet::new();
    let max = max_closure_modules();
    for module in plan.closure_oleans.keys() {
        // Drive the import by the resolved closure module names (targets included),
        // threading one visited set so each module loads once.
        if let Err(e) = load_module_with_deps_bounded_shared_with_policy(
            &mut env,
            module,
            &plan.search_paths,
            max,
            &mut visited,
            policy,
        ) {
            miss!("eager inductive-families load of `{module}` failed: {e}");
        }
    }

    // LAZY-DEFINITIONAL LEG, materialized EAGERLY for enumerability: pull every
    // served definitional constant out of the verified shards and register it via
    // the trusted-import structural bulk-add.
    //
    // SOUNDNESS: these are the SAME constants, from the SAME .olean set, that the
    // eager importer registers via this exact `extend_constants_structural` hook
    // (crates/clean-olean/src/import/load_register.rs) — the cache only changes the
    // SOURCE OF THE BYTES (a content-addressed, digest-bound, per-constant-recon-
    // digest-stamped shard) not the trust boundary. Constants are stored Unverified
    // (imported context), and every graduation candidate is re-type-checked from
    // scratch downstream, so a wrong byte here cannot mint a KernelVerified — it can
    // only fail a candidate's recheck. Ratcheted in data/unchecked_decl_ratchet.json
    // (extend_constants block, #4). A structural rejection => fall back to eager.
    let names = ConstantSource::names(&source);
    let mut infos: Vec<ConstantInfo> = Vec::with_capacity(names.len());
    for name in &names {
        match ConstantSource::get(&source, name) {
            Some(ci) => infos.push(ci.clone()),
            // A verified-shard name that will not materialize is a corruption
            // tripwire (recon_digest / name-binding gate) => fail closed.
            None => miss!("served name `{name}` did not materialize"),
        }
    }
    let served = infos.len();
    let rejected = env.extend_constants_structural(infos.into_iter());
    if !rejected.is_empty() {
        miss!(
            "{} of {} served constants structurally rejected",
            rejected.len(),
            served
        );
    }

    if dbg {
        eprintln!(
            "[closure-cache] HIT: env total {} (served {} definitional + eager inductives)",
            env.constants().count(),
            served
        );
    }
    Some(env)
}

/// Best-effort populate of the cache entry after a cold reconstruction. Builds the
/// v3 fail-closed closure shards for the target modules' union closure into the
/// per-digest entry directory and writes the manifest. Any error is logged and
/// swallowed — a cache-write failure must never fail the graduation.
pub(crate) fn populate(plan: &CachePlan) {
    if let Err(e) = std::fs::create_dir_all(&plan.entry_dir) {
        eprintln!(
            "[graduate cache] populate skipped (mkdir {} failed: {e})",
            plan.entry_dir.display()
        );
        return;
    }
    // exclude_targets = false: the declared modules' OWN definitional decls must be
    // served too (graduate enumerates/needs them), unlike stamp-verified's re-mint.
    //
    // Resolve+stamp against `plan.search_paths` — the EXACT toolchain-pinned paths
    // the eager/warm loader uses (closure_bfs / the eager inductive leg / fast_load's
    // binding all key off them). Re-deriving paths from `root` instead would let a
    // core module bind to a different installed toolchain's `.olean`, mismatching the
    // live digest at warm time and forcing a permanent (spurious) MISS.
    let build = match build_closure_shards_for_targets_with_search_paths(
        &plan.target_oleans,
        &plan.root,
        &plan.search_paths,
        &plan.entry_dir,
        false,
    ) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("[graduate cache] populate skipped (shard build failed: {e})");
            return;
        }
    };

    // Coverage is "full" only when every closure module the warm gate will require
    // is backed by a shard: no skipped module AND no per-constant drop. Anything
    // less means the warm load would (correctly) fall back, so record it honestly.
    let fully_covered = build.skipped_modules.is_empty() && build.dropped_const_modules.is_empty();
    let manifest = Manifest {
        schema: MANIFEST_SCHEMA.to_string(),
        cache_format_version: CACHE_FORMAT_VERSION,
        shard_version: SHARD_VERSION,
        union_digest: plan.union_digest_hex.clone(),
        modules: plan.closure_modules.iter().cloned().collect(),
        converted: build.converted,
        skipped_modules: build.skipped_modules,
        dropped_consts: build.dropped_const_modules.len(),
        fully_covered,
    };
    if let Err(e) = manifest.write(&plan.entry_dir.join(MANIFEST_FILE)) {
        eprintln!("[graduate cache] manifest write failed (entry left unusable): {e}");
    }
}

const MANIFEST_SCHEMA: &str = "clean-closure-cache-v1";

/// The per-entry manifest. The union digest is the content-address; the version
/// fields gate the recipe; `fully_covered` gates whether a warm load may proceed.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct Manifest {
    schema: String,
    cache_format_version: u32,
    shard_version: u32,
    union_digest: String,
    modules: Vec<String>,
    converted: usize,
    skipped_modules: Vec<String>,
    dropped_consts: usize,
    fully_covered: bool,
}

impl Manifest {
    fn read(path: &Path) -> Option<Self> {
        let bytes = std::fs::read(path).ok()?;
        let m: Manifest = serde_json::from_slice(&bytes).ok()?;
        if m.schema != MANIFEST_SCHEMA {
            return None;
        }
        Some(m)
    }

    fn write(&self, path: &Path) -> std::io::Result<()> {
        let bytes = serde_json::to_vec_pretty(self)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        std::fs::write(path, bytes)
    }
}

#[cfg(test)]
#[path = "graduate_closure_cache_tests.rs"]
mod tests;
