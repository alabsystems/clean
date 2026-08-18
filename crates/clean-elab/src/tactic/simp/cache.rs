// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-environment cache for the built [`SimpLemmaSet`].
//!
//! With ~10k imported `@[simp]` lemmas registered through the typed
//! simpExtension decoder, `collect_simp_lemmas` — which re-parses every lemma
//! type (`extract_equality_full`) and re-inserts every LHS into the
//! discrimination tree (`mk_path`, whose per-node `whnf` is expensive) — used
//! to run on EVERY `simp` call. Every by-simp proof in a file paid the full
//! rebuild again. This module caches the built set so repeated simp calls
//! against an unchanged environment reuse it.
//!
//! # Correctness / soundness
//!
//! - **Staleness**: the cache key contains the environment's
//!   `Environment::simp_registry_revision` counter (bumped ONLY by
//!   `register_simp_lemma` / `unregister_simp_lemma`, never by `add_decl`),
//!   the simp-registry count, and an order-independent fingerprint of every
//!   registered simp lemma name + priority. Any registry mutation — including
//!   a count-and-content-neutral remove/re-add cycle — bumps the revision and
//!   rebuilds; append-only declaration growth does NOT invalidate, which is
//!   the cross-declaration reuse the cache exists for (sound because later
//!   declarations are new names that cannot occur in older lemma statements).
//! - **Config**: only configs whose collected set is provably
//!   goal-independent and env-determined are cacheable (see
//!   [`is_cacheable`]); the exclusion set participates in the key. Everything
//!   else — `simp only`, extra lemmas (which may resolve against the local
//!   context or opened namespaces), hypothesis lemmas, aesop bundles —
//!   bypasses the cache and rebuilds exactly as before.
//! - **Goal independence of the cached tree**: the cached set contains only
//!   builtin + registry lemmas, whose LHS patterns come from top-level
//!   constant types and are therefore closed (loose BVars only — no goal
//!   FVars, no metavariables). `mk_path`/`whnf` on a closed expression cannot
//!   observe the goal's local context or meta assignments, so the tree built
//!   under one goal is byte-identical to the tree any other goal in the same
//!   environment would build.
//! - **Backstop**: even a hypothetical stale hit cannot mint an unsound
//!   proof — every rewrite is still guarded by the unifier, the
//!   `lhs_inst ≡ expr` def-eq check, and the kernel re-check at `close_goal`.
//!   A stale set could only cost completeness, and the key makes that
//!   practically unreachable.
//!
//! Storage is a tiny (N=2) thread-local LRU: elaboration of a file is
//! single-threaded, `Environment` is owned per [`ProofState`] (no stable
//! address to key on), and thread-locals avoid imposing `Send`/`Sync` bounds
//! on the cached expressions.

use std::cell::RefCell;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use super::lemmas::collect_simp_lemmas;
use super::types::{SimpConfig, SimpLemmaSet};
use crate::tactic::core::ProofState;

/// Number of distinct (environment, exclusions) snapshots kept per thread.
const CACHE_CAPACITY: usize = 2;

/// Identity of a cacheable collected lemma set.
///
/// The key deliberately does NOT include `Environment::generation()` or the
/// constant count: both bump on every `add_decl`, which would defeat the
/// cache's whole purpose (cross-declaration reuse within a file). That is
/// sound because the cached portion (builtin + registry lemmas, their env
/// types, and the discr-tree paths derived from them) depends only on the
/// simp registry: registered constants are immutable, and declarations added
/// later are NEW names that cannot occur in older lemma statements — so no
/// later `add_decl` can change what this set would rebuild to.
/// `simp_registry_revision` bumps on every register/unregister (including
/// count-and-content-neutral remove/re-add churn), and the count/fingerprint
/// stay as belt-and-suspenders against revision aliasing across distinct
/// environments (two separately-built envs can share a revision number).
#[derive(Debug, Clone, PartialEq, Eq)]
struct SimpSetCacheKey {
    simp_registry_revision: u64,
    simp_lemma_count: usize,
    /// Order-independent fingerprint (wrapping sum of per-entry hashes) of
    /// every registered simp lemma's name and priority.
    simp_registry_fingerprint: u64,
    /// Sorted exclusion list from the config.
    exclude: Vec<String>,
}

thread_local! {
    static SIMP_SET_CACHE: RefCell<Vec<(SimpSetCacheKey, Arc<SimpLemmaSet>)>> =
        const { RefCell::new(Vec::new()) };
}

#[cfg(test)]
thread_local! {
    static CACHEABLE_REBUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Number of cacheable-config lemma-set rebuilds (cache misses) performed on
/// this thread. Test-only observability for the reuse/invalidation tests.
#[cfg(test)]
pub(crate) fn cacheable_rebuild_count() -> usize {
    CACHEABLE_REBUILDS.with(std::cell::Cell::get)
}

/// Whether this call's collected set is env-determined (safe to cache).
///
/// The cached portion must be exactly the builtin + registry lemmas: `simp
/// only` flips the set's composition; `extra_lemmas` resolve through the local
/// context and opened namespaces; `use_hypotheses` reads the current goal;
/// `aesop_simp_lemmas` are caller-constructed expressions we cannot cheaply
/// fingerprint. A state without a current goal builds an index-free set today
/// (`SimpLemmaSet::without_index`), so it must not be served an indexed one —
/// nor seed the cache with an index-free one.
fn is_cacheable(state: &ProofState, config: &SimpConfig) -> bool {
    !config.only
        && config.extra_lemmas.is_empty()
        && !config.use_hypotheses
        && config.aesop_simp_lemmas.is_empty()
        && state.current_goal().is_some()
}

fn cache_key(state: &ProofState, config: &SimpConfig) -> SimpSetCacheKey {
    let env = state.env();
    let mut simp_lemma_count = 0usize;
    let mut simp_registry_fingerprint = 0u64;
    for info in env.get_simp_lemmas() {
        simp_lemma_count += 1;
        let mut hasher = DefaultHasher::new();
        info.name.hash(&mut hasher);
        info.priority.value().hash(&mut hasher);
        simp_registry_fingerprint = simp_registry_fingerprint.wrapping_add(hasher.finish());
    }
    let mut exclude: Vec<String> = config.exclude.iter().cloned().collect();
    exclude.sort_unstable();
    SimpSetCacheKey {
        simp_registry_revision: env.simp_registry_revision(),
        simp_lemma_count,
        simp_registry_fingerprint,
        exclude,
    }
}

/// [`collect_simp_lemmas`] with a per-environment cache in front.
///
/// Cache-eligible calls (see [`is_cacheable`]) reuse the previously built
/// [`SimpLemmaSet`] when the environment identity and exclusion set match;
/// everything else falls through to a fresh build with unchanged semantics.
/// Whether this call can COMPOSE from the cached indexed base even though the
/// full config is not cacheable: the expensive part (builtins + registry with
/// the built discrimination tree) is identical, and the disqualifying inputs
/// (`extra_lemmas`, hypothesis lemmas, `aesop_simp_lemmas`) are cheap per-call
/// overlays. `simp only` changes the base composition outright and a goal-less
/// state builds an index-free set, so both keep the full-rebuild path.
///
/// This is what makes the cache effective on the AESOP path: aesop sets
/// `aesop_simp_lemmas` unconditionally and `simp_all` pushes hypothesis names
/// into `extra_lemmas`, so before this composition every aesop search node
/// re-collected and re-indexed the full ~10k-lemma imported registry — the
/// dominant cost (and, with pathological lemma statements, the OOM) of
/// aesop/tauto under real imports.
fn base_composable(state: &ProofState, config: &SimpConfig) -> bool {
    !config.only && state.current_goal().is_some()
}

pub(crate) fn collect_simp_lemmas_cached(
    state: &ProofState,
    config: &SimpConfig,
) -> Arc<SimpLemmaSet> {
    if !is_cacheable(state, config) {
        if base_composable(state, config) {
            let mut base_config = config.clone();
            base_config.extra_lemmas = Vec::new();
            base_config.use_hypotheses = false;
            base_config.aesop_simp_lemmas = Vec::new();
            // The stripped config satisfies `is_cacheable`, so this recursion
            // lands in the cached arm below (building the base at most once
            // per (registry revision, exclusions) per thread).
            let base = collect_simp_lemmas_cached(state, &base_config);

            // Overlay in the historical collection order (extras, hypotheses,
            // aesop bundle); `base_with_overlay` re-sorts by priority exactly
            // as the historical global sort did.
            let mut overlay = super::lemmas::collect_extra_lemmas(state, config);
            if config.use_hypotheses {
                overlay.extend(super::lemmas::collect_hypothesis_lemmas(state));
            }
            overlay.extend(config.aesop_simp_lemmas.iter().cloned());
            return Arc::new(SimpLemmaSet::base_with_overlay(&base, overlay));
        }
        return Arc::new(collect_simp_lemmas(state, config));
    }

    let key = cache_key(state, config);

    let hit = SIMP_SET_CACHE.with(|cell| {
        let mut cache = cell.borrow_mut();
        let position = cache
            .iter()
            .position(|(cached_key, _)| *cached_key == key)?;
        // LRU: move the hit to the front.
        let entry = cache.remove(position);
        let set = Arc::clone(&entry.1);
        cache.insert(0, entry);
        Some(set)
    });
    if let Some(set) = hit {
        return set;
    }

    #[cfg(test)]
    CACHEABLE_REBUILDS.with(|count| count.set(count.get() + 1));

    let set = Arc::new(collect_simp_lemmas(state, config));
    SIMP_SET_CACHE.with(|cell| {
        let mut cache = cell.borrow_mut();
        cache.insert(0, (key, Arc::clone(&set)));
        cache.truncate(CACHE_CAPACITY);
    });
    set
}
