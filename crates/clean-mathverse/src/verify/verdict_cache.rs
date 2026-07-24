// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Persistent verdict cache for re-import deduplication
//! (`designs/2026-06-27-reimport-at-the-speed-of-a-hash.md`, move P1, brick 2).
//!
//! Maps a declaration's Merkle-DAG **verified hash**
//! ([`super::fingerprint::decl_verified_hash`]) to the kernel verdict already
//! computed for that exact content-and-dependency-closure. On re-import, a
//! declaration whose verified hash is already present is **skipped** — its
//! verdict is reused instead of re-running the kernel type-check. Because the
//! key is the *verified* hash (which folds in every transitive dependency), a
//! change in the declaration or in any dependency misses the cache and forces a
//! fresh re-check; only genuinely-unchanged content is reused.
//!
//! SOUNDNESS BOUNDARY (see [`super::fingerprint`]): the cache memoizes the pure,
//! deterministic kernel verdict. Reusing a verdict for a byte-identical
//! content-closure is observationally identical to recomputing it; the TCB is
//! unchanged. A sample-and-re-verify ratchet (next brick) re-checks cache
//! entries from a cold kernel to prove `cache ≡ fresh`, and any skeptic can
//! discard the cache and re-derive every verdict.

use std::collections::HashMap;
use std::path::Path;

use clean_kernel::Name;
use serde::{Deserialize, Serialize};

/// The kernel verdict recorded for one declaration's verified hash.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CachedVerdict {
    /// Did Clean's kernel accept `value : type`?
    pub(crate) kernel_verified: bool,
    /// Sorted transitive axiom-closure names — the input to the foundational-⊆
    /// check. Empty for an axiom-free `KernelVerified` declaration.
    pub(crate) axiom_closure: Vec<Name>,
}

/// Persistent map: declaration verified-hash → recorded kernel verdict.
///
/// Keyed by `[u8; 32]` (not a string), so it is serialized with `bincode`
/// rather than a string-keyed format. Serialized map order is irrelevant: the
/// cache file is loaded back into a map, never hashed, so a non-canonical byte
/// order costs nothing.
#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct VerdictCache {
    entries: HashMap<[u8; 32], CachedVerdict>,
}

impl VerdictCache {
    /// An empty cache.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Number of recorded verdicts.
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache holds no verdicts.
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The recorded verdict for verified-hash `vh`, if any.
    pub(crate) fn lookup(&self, vh: &[u8; 32]) -> Option<&CachedVerdict> {
        self.entries.get(vh)
    }

    /// Record (or overwrite) the verdict for verified-hash `vh`.
    pub(crate) fn record(&mut self, vh: [u8; 32], verdict: CachedVerdict) {
        self.entries.insert(vh, verdict);
    }

    /// Load a cache from a `bincode` sidecar. A missing file is an empty cache
    /// (the first-run case); a present-but-corrupt file is an error rather than
    /// a silent reset, so corruption is surfaced rather than masked.
    pub(crate) fn load(path: impl AsRef<Path>) -> Result<Self, VerdictCacheError> {
        let bytes = match std::fs::read(path.as_ref()) {
            Ok(b) => b,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Self::new()),
            Err(e) => return Err(VerdictCacheError::Io(e)),
        };
        let (cache, _) = bincode::serde::decode_from_slice(&bytes, bincode::config::standard())?;
        Ok(cache)
    }

    /// Persist the cache to a `bincode` sidecar. Writes a sibling temp file then
    /// renames, so a crash mid-write never leaves a half-written cache in place.
    pub(crate) fn save(&self, path: impl AsRef<Path>) -> Result<(), VerdictCacheError> {
        let path = path.as_ref();
        let bytes = bincode::serde::encode_to_vec(self, bincode::config::standard())?;
        let tmp = path.with_extension("tmp");
        std::fs::write(&tmp, &bytes)?;
        std::fs::rename(&tmp, path)?;
        Ok(())
    }
}

/// Errors from loading or saving a [`VerdictCache`].
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum VerdictCacheError {
    /// Reading or writing the cache sidecar failed.
    #[error("verdict cache I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// Encoding the cache to bytes failed.
    #[error("verdict cache encode failed: {0}")]
    Encode(#[from] bincode::error::EncodeError),
    /// Decoding the cache from bytes failed (corrupt or incompatible sidecar).
    #[error("verdict cache decode failed: {0}")]
    Decode(#[from] bincode::error::DecodeError),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn verdict(kernel_verified: bool, axioms: &[&str]) -> CachedVerdict {
        CachedVerdict {
            kernel_verified,
            axiom_closure: axioms.iter().map(|a| Name::from_string(a)).collect(),
        }
    }

    #[test]
    fn test_cache_lookup_hit_and_miss() {
        let mut c = VerdictCache::new();
        let vh = [7u8; 32];
        c.record(vh, verdict(true, &["propext"]));
        assert_eq!(c.lookup(&vh), Some(&verdict(true, &["propext"])));
        assert!(c.lookup(&[0u8; 32]).is_none(), "unknown vh ⇒ miss");
    }

    #[test]
    fn test_cache_roundtrips_through_disk() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("verdicts.bin");
        let mut c = VerdictCache::new();
        c.record([1u8; 32], verdict(true, &[]));
        c.record(
            [2u8; 32],
            verdict(false, &["Classical.choice", "Quot.sound"]),
        );
        c.save(&path).expect("save");

        let loaded = VerdictCache::load(&path).expect("load");
        assert_eq!(loaded.len(), 2, "both verdicts survive the round-trip");
        assert_eq!(loaded.lookup(&[1u8; 32]), Some(&verdict(true, &[])));
        assert_eq!(
            loaded.lookup(&[2u8; 32]),
            Some(&verdict(false, &["Classical.choice", "Quot.sound"])),
        );
    }

    #[test]
    fn test_cache_load_missing_file_is_empty() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("does_not_exist.bin");
        let c = VerdictCache::load(&path).expect("missing file ⇒ empty cache");
        assert!(c.is_empty(), "first run starts empty");
    }
}

/// End-to-end simulation of the topo-order re-import loop over the verified-hash
/// cache (`fingerprint::decl_verified_hash` + [`VerdictCache`]) — exercising the
/// exact algorithm brick 3 will wire into `verify_corpus_incremental`, but in
/// isolation from the trusted verify path. Demonstrates the whole re-import
/// value proposition in one test: speedup, cross-version soundness, precision.
#[cfg(test)]
mod reimport_simulation {
    use super::*;
    use crate::verify::fingerprint::decl_verified_hash;
    use clean_kernel::expr::ExprKind;
    use clean_kernel::Declaration;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn c(s: &str) -> clean_kernel::expr::Expr {
        clean_kernel::expr::Expr::from_kind(ExprKind::Const(
            Name::from_string(s),
            Default::default(),
        ))
    }
    fn app(f: clean_kernel::expr::Expr, a: clean_kernel::expr::Expr) -> clean_kernel::expr::Expr {
        clean_kernel::expr::Expr::from_kind(ExprKind::App(Arc::new(f), Arc::new(a)))
    }
    fn thm(
        name: &str,
        type_: clean_kernel::expr::Expr,
        value: clean_kernel::expr::Expr,
    ) -> Declaration {
        Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        }
    }
    fn def(
        name: &str,
        type_: clean_kernel::expr::Expr,
        value: clean_kernel::expr::Expr,
    ) -> Declaration {
        Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
            is_reducible: false,
        }
    }
    fn name_of(d: &Declaration) -> Name {
        match d {
            Declaration::Definition { name, .. }
            | Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Axiom { name, .. } => name.clone(),
        }
    }

    /// Process `decls` in topological order: resolve each decl's dependency
    /// hashes from the memo built so far (seeded with the trusted closure),
    /// consult the cache (hit ⇒ reuse verdict, miss ⇒ "verify" then record), and
    /// publish the decl's own verified hash for its dependents. Returns
    /// `(hits, misses)`.
    fn run_import(
        decls: &[Declaration],
        cache: &mut VerdictCache,
        trusted: &HashMap<Name, [u8; 32]>,
    ) -> (usize, usize) {
        let mut memo = trusted.clone();
        let (mut hits, mut misses) = (0, 0);
        for d in decls {
            let vh = decl_verified_hash(d, |dep| memo.get(dep).copied())
                .expect("encode ok")
                .expect("all deps resolve in topo order");
            if cache.lookup(&vh).is_some() {
                hits += 1;
            } else {
                misses += 1;
                cache.record(
                    vh,
                    CachedVerdict {
                        kernel_verified: true,
                        axiom_closure: vec![],
                    },
                );
            }
            memo.insert(name_of(d), vh);
        }
        (hits, misses)
    }

    #[test]
    fn test_reimport_speedup_soundness_and_precision() {
        // Trusted closure: imported constants, pre-fingerprinted into the memo.
        // `q` is the alternate proof term used by the mutation below.
        let trusted: HashMap<Name, [u8; 32]> = [("Nat", 1u8), ("Eq", 2), ("p", 3), ("q", 4)]
            .iter()
            .map(|(n, b)| (Name::from_string(n), [*b; 32]))
            .collect();

        // Topo-ordered library: L1 (← trusted), L2 (← L1), D3 (← L2),
        // and U4 (← trusted only; unrelated to L1's subtree).
        let l1 = thm("L1", app(c("Eq"), c("Nat")), c("p"));
        let l2 = thm("L2", c("Nat"), app(c("L1"), c("p")));
        let d3 = def("D3", c("Nat"), app(c("L2"), c("Nat")));
        let u4 = thm("U4", c("Nat"), c("p"));
        let lib = vec![l1, l2.clone(), d3.clone(), u4.clone()];

        let mut cache = VerdictCache::new();

        // Cold cache: everything is verified (the expensive first pass).
        assert_eq!(
            run_import(&lib, &mut cache, &trusted),
            (0, 4),
            "cold cache: all four verified"
        );

        // Unchanged re-import: every decl is a cache hit — THE re-import win.
        assert_eq!(
            run_import(&lib, &mut cache, &trusted),
            (4, 0),
            "unchanged re-import: all cache hits, zero re-verification"
        );

        // Change L1's proof term (`p` -> `q`). Its verified hash changes, and so
        // (transitively) do L2's and D3's; the unrelated U4 is untouched.
        let l1b = thm("L1", app(c("Eq"), c("Nat")), c("q"));
        let lib2 = vec![l1b, l2, d3, u4];
        assert_eq!(
            run_import(&lib2, &mut cache, &trusted),
            (1, 3),
            "changed L1 ⇒ L1+L2+D3 re-checked (transitive soundness); U4 hits (precision)"
        );
    }
}
