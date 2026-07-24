// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Incremental **content-addressed** verdict cache for per-constant
//! kernel-verification (`clean mathverse per-constant-verify --kv-cache`).
//!
//! # What it caches
//!
//! Repeatedly reloading the same Mathlib slice into Clean re-runs the kernel's
//! `check_type` gauntlet on the *same* proof terms every time — the dominant
//! cost of iterating on anything else. This cache lets an unchanged constant
//! skip that re-check by remembering "the kernel already accepted this exact
//! content against this exact trusted closure, under this exact checker."
//!
//! # Why it is sound
//!
//! The kernel verdict for a target is a deterministic function of THREE inputs:
//!
//! 1. the target constant's own content (its type + proof value),
//! 2. the trusted environment it is `check_type`'d against (its transitive
//!    constant closure — the only decls the checker can consult), and
//! 3. the checker code itself (reduction, def-eq, recursor iota).
//!
//! The cache key binds all three:
//!
//! - **`target_digest`** — a blake3 over `(name, kind, reducibility, universe
//!   params, type, value)`, where type/value go through the existing
//!   [`expr_canonical_digest`] (a de Bruijn structural digest: alpha-equivalent
//!   terms match, but definitionally-equal-yet-structurally-different terms do
//!   NOT). Structural (not defeq) is exactly right for a proof cache: any change
//!   the kernel would actually see as a different term forces a re-verify.
//! - **`closure_digest`** — a blake3 over the *sorted* content digests of every
//!   constant/inductive family reached by the demand walk, i.e. the exact
//!   trusted env the target was checked against. Change any dependency's
//!   declared type and the closure digest changes → cache miss → re-verify.
//! - **`kernel_fingerprint`** — a metadata stamp of the running executable
//!   (its byte length + mtime), so ANY rebuild of the kernel — which rewrites
//!   the `clean` binary with a fresh size/mtime — invalidates the whole cache.
//!   It is a stat, not a 300 MB content hash: hashing the binary on every
//!   invocation would cost more than the kernel re-check it saves for all but
//!   the heaviest lemmas, and a rebuild always changes the metadata. (This is
//!   the standard build-staleness check; a content-hash mode, amortized once
//!   per process, is the natural upgrade for the batch/corpus path.)
//!
//! A hit skips ONLY [`crate::cli::per_constant_load`]'s final
//! `typecheck_constants_full` call — the demand walk still runs and RECOMPUTES
//! every digest, so a hit is a proof that the content is byte-for-byte what was
//! verified before. The cache therefore cannot mask a changed proof: a changed
//! term yields a different digest yields a miss. The cache also never stores a
//! FAILED verdict (a failure may be environmental), so it can only ever let the
//! kernel be *re-run*, never let a rejection masquerade as an acceptance.
//!
//! This preserves the per-constant loader's trust boundary unchanged: closure
//! constants remain trusted imports; only the target ever earns a verdict.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use serde::{Deserialize, Serialize};

use clean_kernel::env::{ConstantInfo, Environment};
use clean_kernel::Name;

use crate::graduate::record::expr_canonical_digest;

/// On-disk cache format version. Bump on any change to how a key is derived, so
/// an older manifest is treated as stale rather than mis-hit.
const CACHE_FORMAT: u32 = 1;

/// How the running executable is fingerprinted to bind cached verdicts to the
/// exact checker that produced them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FingerprintMode {
    /// `size:mtime` of the binary — a `stat`, paid every process, effectively
    /// free. A rebuild always rewrites `clean` with a new size/mtime, so this
    /// catches every rebuild. The default: it is a build-staleness check, and
    /// build staleness is precisely what invalidates a verdict.
    Metadata,
    /// blake3 of the binary's *bytes* — a cryptographic content hash, ~300 MB
    /// read+hash amortized ONCE per process via a `OnceLock`. Stronger than
    /// `Metadata` in the corner cases metadata cannot see: two builds that land
    /// the same size at the same mtime (e.g. a restored-from-backup or
    /// content-addressed-store binary, or a filesystem with coarse mtime
    /// granularity). Opt in with `--kv-cache-content-hash` for the batch/corpus
    /// path where the one-time hash cost is dwarfed by thousands of re-checks.
    Content,
}

/// A fingerprint of the running executable under `mode`, memoized per mode.
/// `None` if the executable cannot be located or read/`stat`'d — in which case
/// the cache is disabled (fail-safe: we simply re-verify, never trust an
/// unattributable verdict). Any rebuild of `clean` changes the fingerprint
/// under either mode, invalidating every prior verdict. The `Metadata`/`Content`
/// prefixes also make the two modes' fingerprints disjoint strings, so a
/// manifest written under one mode never hits under the other (its
/// `kernel_fingerprint` field simply mismatches and the manifest resets).
pub(crate) fn kernel_fingerprint(mode: FingerprintMode) -> Option<String> {
    match mode {
        FingerprintMode::Metadata => {
            static META_FP: OnceLock<Option<String>> = OnceLock::new();
            META_FP
                .get_or_init(|| {
                    let exe = std::env::current_exe().ok()?;
                    let meta = std::fs::metadata(&exe).ok()?;
                    let len = meta.len();
                    let mtime_nanos = meta
                        .modified()
                        .ok()
                        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                        .map(|d| d.as_nanos())
                        .unwrap_or(0);
                    Some(format!("exe-meta:{len}:{mtime_nanos}"))
                })
                .clone()
        }
        FingerprintMode::Content => {
            static CONTENT_FP: OnceLock<Option<String>> = OnceLock::new();
            CONTENT_FP
                .get_or_init(|| {
                    let exe = std::env::current_exe().ok()?;
                    let bytes = std::fs::read(&exe).ok()?;
                    Some(format!("exe-blake3:{}", blake3::hash(&bytes).to_hex()))
                })
                .clone()
        }
    }
}

/// Stable one-byte tag for a [`clean_kernel::env::ConstantKind`]. Included in the
/// content digest because the kernel treats the kinds differently (e.g. a
/// Theorem/Opaque value is never δ-unfolded), so kind affects the verdict.
fn kind_tag(kind: clean_kernel::env::ConstantKind) -> u8 {
    use clean_kernel::env::ConstantKind::*;
    match kind {
        Definition => 0,
        Theorem => 1,
        Opaque => 2,
        Axiom => 3,
    }
}

/// Stable tag + height for a [`clean_kernel::env::Reducibility`]. Reducibility
/// drives delta-unfolding order and whether a def unfolds at all, so it can
/// change a def-eq outcome and therefore belongs in the digest.
fn reduc_tag(r: clean_kernel::env::Reducibility) -> (u8, u32) {
    use clean_kernel::env::Reducibility::*;
    match r {
        Reducible => (0, 0),
        Regular(h) => (1, h),
        Irreducible => (2, 0),
        Opaque => (3, 0),
    }
}

/// Content digest of a single constant — binds everything the kernel's verdict
/// can depend on. Returns `None` if either sub-expression fails to flatten (in
/// which case the caller degrades to a normal, uncached verify).
pub(crate) fn constant_content_digest(ci: &ConstantInfo) -> Option<String> {
    let mut h = blake3::Hasher::new();
    h.update(b"clean.kv.const.v1\0");
    h.update(ci.name.to_string().as_bytes());
    h.update(b"\0");
    h.update(&[kind_tag(ci.kind)]);
    let (rt, rh) = reduc_tag(ci.reducibility);
    h.update(&[rt]);
    h.update(&rh.to_le_bytes());
    // Universe parameters (order-significant).
    h.update(&(ci.level_params.len() as u32).to_le_bytes());
    for lp in &ci.level_params {
        h.update(lp.to_string().as_bytes());
        h.update(b"\0");
    }
    // Type is always present; value is present only for value-bearing kinds (and
    // for types-only-loaded trusted deps, deliberately absent — which is exactly
    // what the kernel sees, so the digest matches the kernel's view).
    h.update(expr_canonical_digest(&ci.type_).ok()?.as_bytes());
    match &ci.value {
        Some(v) => {
            h.update(b"V");
            h.update(expr_canonical_digest(v).ok()?.as_bytes());
        }
        None => {
            h.update(b"N");
        }
    }
    Some(format!("blake3:{}", h.finalize().to_hex()))
}

/// Content digest of an inductive-family member (inductive / constructor /
/// recursor). Its reduction behaviour is regenerated deterministically from its
/// declaration by the (fingerprinted) kernel, so binding name + kind-tag + type
/// pins it given a fixed `kernel_fingerprint`.
fn inductive_member_digest(name: &Name, ty: &clean_kernel::Expr, tag: u8) -> Option<String> {
    let mut h = blake3::Hasher::new();
    h.update(b"clean.kv.ind.v1\0");
    h.update(name.to_string().as_bytes());
    h.update(b"\0");
    h.update(&[tag]);
    h.update(expr_canonical_digest(ty).ok()?.as_bytes());
    Some(format!("blake3:{}", h.finalize().to_hex()))
}

/// The per-name content digest, whichever family the name belongs to. A name
/// that resolves to nothing resident becomes a stable `missing:` marker so a
/// coverage hole still perturbs the closure key (and such a target would not be
/// cached anyway, since it would fail to verify).
fn member_digest(env: &Environment, name: &Name) -> String {
    if let Some(ci) = env.get_const(name) {
        if let Some(d) = constant_content_digest(ci) {
            return d;
        }
    }
    if let Some(iv) = env.get_inductive(name) {
        if let Some(d) = inductive_member_digest(name, &iv.type_, 0) {
            return d;
        }
    }
    if let Some(cv) = env.get_constructor(name) {
        if let Some(d) = inductive_member_digest(name, &cv.type_, 1) {
            return d;
        }
    }
    if let Some(rv) = env.get_recursor(name) {
        if let Some(d) = inductive_member_digest(name, &rv.type_, 2) {
            return d;
        }
    }
    format!("missing:{name}")
}

/// Digest of the trusted closure the target(s) were checked against: a blake3
/// over the SORTED per-member digests of `closure` (a deterministic key
/// independent of walk order). `closure` should be the demand-walk `visited`
/// set — every constant the kernel could consult.
pub(crate) fn closure_digest<'a>(
    env: &Environment,
    closure: impl Iterator<Item = &'a Name>,
) -> String {
    let mut members: Vec<String> = closure.map(|n| member_digest(env, n)).collect();
    members.sort_unstable();
    let mut h = blake3::Hasher::new();
    h.update(b"clean.kv.closure.v1\0");
    h.update(&(members.len() as u64).to_le_bytes());
    for m in &members {
        h.update(m.as_bytes());
        h.update(b"\0");
    }
    format!("blake3:{}", h.finalize().to_hex())
}

/// A single cached verdict for one target constant.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct CacheEntry {
    /// Content digest of the target constant (type + value + attributes).
    target_digest: String,
    /// Digest of the trusted closure it was checked against.
    closure_digest: String,
    /// Closure size at record time (informational; not part of the key).
    #[serde(default)]
    closure_names: usize,
    /// Always `"KernelVerified"` — failures are never stored.
    verdict: String,
}

/// The on-disk manifest: a fingerprint plus a map from target name to its cached
/// verdict. Entries are valid ONLY under the stored `kernel_fingerprint`.
#[derive(Debug, Serialize, Deserialize)]
struct CacheManifest {
    generated_by: String,
    cache_format: u32,
    /// The executable fingerprint these entries were produced under. On a
    /// mismatch the whole manifest is reset (a new binary invalidates every
    /// verdict).
    kernel_fingerprint: String,
    entries: BTreeMap<String, CacheEntry>,
}

/// Loaded, mutable view of the cache bound to its backing path.
pub(crate) struct KvCache {
    path: PathBuf,
    fingerprint: String,
    manifest: CacheManifest,
    /// Whether any entry was added/changed since load (drives whether `save`
    /// bothers writing).
    dirty: bool,
}

impl KvCache {
    /// Open the cache at `path`, binding it to the executable fingerprint under
    /// `mode`. Returns `None` (cache disabled) if the fingerprint cannot be
    /// computed. A missing or corrupt manifest, or one written under a different
    /// fingerprint/format (including a different `mode`, whose prefix differs),
    /// yields a fresh empty cache bound to the current fingerprint — never an
    /// error, and never a stale hit.
    pub(crate) fn open(path: &Path, mode: FingerprintMode) -> Option<Self> {
        let fingerprint = kernel_fingerprint(mode)?;
        let manifest = std::fs::read(path)
            .ok()
            .and_then(|b| serde_json::from_slice::<CacheManifest>(&b).ok())
            .filter(|m| m.cache_format == CACHE_FORMAT && m.kernel_fingerprint == fingerprint)
            .unwrap_or_else(|| CacheManifest {
                generated_by: "clean mathverse per-constant-verify (kv-cache v1)".to_string(),
                cache_format: CACHE_FORMAT,
                kernel_fingerprint: fingerprint.clone(),
                entries: BTreeMap::new(),
            });
        Some(KvCache {
            path: path.to_path_buf(),
            fingerprint,
            manifest,
            dirty: false,
        })
    }

    /// The fingerprint this cache is bound to (for reporting).
    pub(crate) fn fingerprint(&self) -> &str {
        &self.fingerprint
    }

    /// A HIT iff a stored `KernelVerified` entry for `target_name` matches BOTH
    /// the recomputed target and closure digests. Any mismatch is a miss.
    pub(crate) fn lookup(
        &self,
        target_name: &str,
        target_digest: &str,
        closure_digest: &str,
    ) -> bool {
        self.manifest.entries.get(target_name).is_some_and(|e| {
            e.verdict == "KernelVerified"
                && e.target_digest == target_digest
                && e.closure_digest == closure_digest
        })
    }

    /// Record a fresh `KernelVerified` verdict, overwriting any prior entry for
    /// this target. Only call after the kernel genuinely accepted the target.
    pub(crate) fn record(
        &mut self,
        target_name: &str,
        target_digest: String,
        closure_digest: String,
        closure_names: usize,
    ) {
        self.manifest.entries.insert(
            target_name.to_string(),
            CacheEntry {
                target_digest,
                closure_digest,
                closure_names,
                verdict: "KernelVerified".to_string(),
            },
        );
        self.dirty = true;
    }

    /// Persist the manifest atomically (temp file + rename) if anything changed.
    /// Best-effort: an IO error is swallowed (the cache is an optimization, not a
    /// source of truth).
    pub(crate) fn save(&self) {
        if !self.dirty {
            return;
        }
        if let Some(parent) = self.path.parent() {
            if !parent.as_os_str().is_empty() {
                let _ = std::fs::create_dir_all(parent);
            }
        }
        let Ok(bytes) = serde_json::to_vec_pretty(&self.manifest) else {
            return;
        };
        let tmp = self.path.with_extension("json.tmp");
        if std::fs::write(&tmp, &bytes).is_ok() {
            let _ = std::fs::rename(&tmp, &self.path);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("clean_kv_cache_test_{name}.json"))
    }

    use FingerprintMode::{Content, Metadata};

    #[test]
    fn fingerprint_is_present_and_stable() {
        let a = kernel_fingerprint(Metadata);
        let b = kernel_fingerprint(Metadata);
        assert!(a.is_some(), "the test binary must be fingerprintable");
        assert_eq!(a, b, "fingerprint must be stable within a process");
    }

    #[test]
    fn content_and_metadata_fingerprints_differ_and_are_stable() {
        let m = kernel_fingerprint(Metadata).expect("metadata fingerprintable");
        let c = kernel_fingerprint(Content).expect("content fingerprintable");
        assert!(m.starts_with("exe-meta:"), "metadata mode is prefixed");
        assert!(c.starts_with("exe-blake3:"), "content mode is prefixed");
        assert_ne!(m, c, "the two modes must produce disjoint fingerprints");
        // Both memoized: repeated calls are stable.
        assert_eq!(c, kernel_fingerprint(Content).unwrap());
    }

    #[test]
    fn hit_requires_exact_target_and_closure_digests() {
        let path = tmp("exact");
        let _ = std::fs::remove_file(&path);
        let mut c = KvCache::open(&path, Metadata).expect("fingerprintable");
        assert!(!c.lookup("T", "td", "cd"), "empty cache is a miss");
        c.record("T", "td".into(), "cd".into(), 3);
        assert!(
            c.lookup("T", "td", "cd"),
            "exact (target,closure) match hits"
        );
        // The soundness contract: ANY digest change is a miss → forces re-verify.
        assert!(!c.lookup("T", "td2", "cd"), "changed target digest misses");
        assert!(!c.lookup("T", "td", "cd2"), "changed closure digest misses");
        assert!(!c.lookup("Other", "td", "cd"), "different name misses");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn recorded_verdict_persists_across_reopen() {
        let path = tmp("persist");
        let _ = std::fs::remove_file(&path);
        {
            let mut c = KvCache::open(&path, Metadata).expect("fingerprintable");
            c.record("T", "td".into(), "cd".into(), 7);
            c.save();
        }
        // Same test binary ⇒ same fingerprint ⇒ the entry is valid on reopen.
        let c = KvCache::open(&path, Metadata).expect("fingerprintable");
        assert!(
            c.lookup("T", "td", "cd"),
            "persisted entry hits after reopen"
        );
        assert!(!c.lookup("T", "tdX", "cd"), "persisted tamper still misses");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn a_manifest_does_not_hit_across_fingerprint_modes() {
        // A verdict recorded under Metadata mode is bound to the metadata
        // fingerprint. Opening the SAME on-disk manifest under Content mode must
        // NOT hit (its stored fingerprint mismatches), but reopening under the
        // original Metadata mode still hits. The mode is part of what a verdict
        // is bound to. (The Content open writes nothing, so the disk manifest is
        // unchanged for the Metadata reopen.)
        let path = tmp("crossmode");
        let _ = std::fs::remove_file(&path);
        {
            let mut c = KvCache::open(&path, Metadata).expect("fingerprintable");
            c.record("T", "td".into(), "cd".into(), 1);
            c.save();
        }
        let content = KvCache::open(&path, Content).expect("fingerprintable");
        assert!(
            !content.lookup("T", "td", "cd"),
            "a metadata-mode verdict must not hit in content mode"
        );
        let metadata = KvCache::open(&path, Metadata).expect("fingerprintable");
        assert!(
            metadata.lookup("T", "td", "cd"),
            "the same verdict still hits under its original metadata mode"
        );
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn foreign_fingerprint_or_future_format_is_discarded() {
        let path = tmp("stale");
        // A manifest produced by a DIFFERENT binary must never yield a hit — a
        // changed kernel could change a verdict, so its cache is invalid.
        let foreign = r#"{"generated_by":"x","cache_format":1,
            "kernel_fingerprint":"blake3:deadbeef",
            "entries":{"T":{"target_digest":"td","closure_digest":"cd","closure_names":1,"verdict":"KernelVerified"}}}"#;
        std::fs::write(&path, foreign).unwrap();
        let c = KvCache::open(&path, Metadata).expect("fingerprintable");
        assert!(
            !c.lookup("T", "td", "cd"),
            "foreign-binary entry must not hit"
        );

        // A future cache_format is likewise treated as stale (reset, not mis-hit).
        let future = r#"{"generated_by":"x","cache_format":9999,
            "kernel_fingerprint":"whatever",
            "entries":{"T":{"target_digest":"td","closure_digest":"cd","closure_names":1,"verdict":"KernelVerified"}}}"#;
        std::fs::write(&path, future).unwrap();
        let c2 = KvCache::open(&path, Metadata).expect("fingerprintable");
        assert!(
            !c2.lookup("T", "td", "cd"),
            "future-format entry must not hit"
        );
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn corrupt_manifest_yields_empty_cache_not_error() {
        let path = tmp("corrupt");
        std::fs::write(&path, b"{ not valid json ]").unwrap();
        let c = KvCache::open(&path, Metadata).expect("fingerprintable");
        assert!(
            !c.lookup("anything", "td", "cd"),
            "corrupt cache is simply empty"
        );
        let _ = std::fs::remove_file(&path);
    }
}
