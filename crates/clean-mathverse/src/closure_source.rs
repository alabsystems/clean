// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
//! Lazy, demand-paged [`ConstantSource`] backing the zero-copy closure loader
//! (Phase 1 / L1-HYBRID; see `~/kv-ceiling-roadmap.md`).
//!
//! Instead of eagerly deserializing the whole import closure into owned
//! `Arc<Expr>` (the ~100GiB OOM on deep Mathlib), the trusted closure is served
//! from a `.mathverse` shard: a constant's [`ConstantInfo`] is materialized on
//! FIRST lookup via the demand fold ([`reconstruct_constant`], which uses the
//! sub-DAG fold proven byte-identical to the full reconstruct) and cached in an
//! append-only [`FrozenMap`] so [`Environment::get_const`] can return a stable
//! `&ConstantInfo`. Untouched closure constants never cost materialization.
//!
//! HYBRID: only `Definition`/`Theorem`/`Axiom`/`Opaque` are served here. Inductive
//! families (`Inductive`/`Constructor`/`Recursor`/`Quot`) stay EAGER, because the
//! shard format cannot losslessly carry recursor reduction rules — installing a
//! stored recursor is a confirmed false-accept hole (iota trusts `rule.rhs`
//! blindly). Making the closure uniformly lazy is Phase 2 / L2 path-(a).

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use clean_kernel::env::{ConstantInfo, ConstantSource, Reducibility};
use clean_kernel::{ConstantKind, Name};

use crate::error::MathverseError;
use crate::frozen_map::FrozenMap;
use crate::shard::ShardMmapReader;
use crate::shard_reconstruct::{reconstruct_level_params, reconstruct_single_subdag_with_reader};
use crate::shard_verify::discover_mathverse_files;
use crate::types::{DeclKind, MathverseConstantHeader, NO_VALUE};
use clean_kernel::expr::Expr;

/// The IMMUTABLE, shareable part of a [`ShardConstantSource`]: the mmap readers
/// and the global name index. These never change after construction and are
/// expensive to rebuild (re-mmap every shard, re-decode every header), so they
/// live behind an [`Arc`] that every [`ShardConstantSource::fresh_view`] shares
/// zero-copy. Only the per-view `FrozenMap` cache is rebuilt — that is the
/// memory the demand-fold accumulates and that a wave boundary must release.
struct SharedReaders {
    /// One DEMAND-PAGED mmap reader per shard. The level pool, level-lists, and
    /// constant headers are decoded up front (small); the bulk `FlatExpr` arena
    /// stays in the mmap and is read one entry at a time during a fold, so an
    /// untouched constant's expr bytes never become resident — the memory win.
    readers: Vec<ShardMmapReader>,
    /// name -> (shard index, constant index), for the lazily-servable
    /// (non-inductive) kinds only. First occurrence wins (append model).
    by_name: HashMap<Name, (u32, u32)>,
    /// Per-shard MODULE name (the shard's `<module>.mathverse` file stem), aligned
    /// with `readers` by index. `None` for readers built without a backing file
    /// (tests). Used by [`ShardConstantSource::owning_module`] so the PARAGON
    /// coverage repair can eager-load the module that defines a missing name.
    shard_modules: Vec<Option<String>>,
}

/// A demand-paged source of trusted-closure constants backed by one OR MORE
/// `.mathverse` shards.
///
/// A closure's trusted import context is one shard per dependency module, so the
/// source spans a whole directory of shards. Each shard is an independent flat
/// arena (independent expr/level pools), so a constant is reconstructed against
/// the shard it came from; the global `by_name` index records `(shard, idx)` and
/// a `FrozenMap` cache makes repeat `get`s O(1) and stable-ref.
///
/// MEMORY DISCIPLINE (PARAGON wave-fresh source): the cache is APPEND-ONLY by
/// construction (`FrozenMap` hands out `&ConstantInfo` borrows stable for the
/// lifetime of `&self`, so it can never evict an entry). On a long full-corpus
/// run that touches every closure constant it would re-accumulate the whole
/// closure's `ConstantInfo` — eroding the demand-paged win back to the eager
/// floor. The PARAGON base therefore drops and rebuilds the source at WAVE
/// boundaries via [`Self::fresh_view`]: each fresh view shares the (immutable,
/// cheap-to-share) `Arc<SharedReaders>` but starts with an EMPTY cache, so peak
/// resident `ConstantInfo` is bounded by one wave's working set, not the whole
/// closure. The shared readers (mmaps + index) are NOT rebuilt.
pub(crate) struct ShardConstantSource {
    /// The immutable mmap readers + name index, shared zero-copy across every
    /// wave-fresh view.
    shared: Arc<SharedReaders>,
    /// Per-shard "load-time verified" flag, indexed by shard. Defaults FALSE for
    /// EVERY shard; the loader flips an entry to `true` only after recomputing
    /// the shard's source-olean digest against the on-disk olean for its OWN
    /// declaring module (see `load_targets_closure_mmap`). SOUNDNESS: `get()`
    /// serves a name ONLY from a verified shard — an unverified shard returns
    /// `None` => coverage miss => HARD EAGER FALLBACK. Per-view & mutable:
    /// `fresh_view` copies it so a wave-fresh view stays verified.
    shard_verified: Vec<bool>,
    /// Append-only cache of materialized `ConstantInfo` (stable `&`-refs for
    /// `get`). Per-view: a `fresh_view` starts empty so wave-boundary drops
    /// reclaim its RSS.
    cache: FrozenMap<Name, ConstantInfo>,
}

impl std::fmt::Debug for ShardConstantSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ShardConstantSource")
            .field("shards", &self.shared.readers.len())
            .field("servable", &self.shared.by_name.len())
            .field("cached", &self.cache.len())
            .finish()
    }
}

impl ShardConstantSource {
    /// Index one shard's lazily-servable (non-inductive) constants by name. The
    /// test constructor marks the shard verified so unit tests that exercise the
    /// materialize/get path do not have to drive the load-time olean-binding
    /// verification (which `load_targets_closure_mmap` does in production).
    #[cfg(test)]
    pub(crate) fn new(reader: ShardMmapReader) -> Self {
        let mut s = Self::from_readers(vec![reader]);
        s.mark_all_verified();
        s
    }

    /// TEST ONLY: mark every shard verified (bypasses the load-time olean-binding
    /// check). Production code marks shards one-by-one via `mark_shard_verified`
    /// only after the per-shard content-binding verification passes.
    #[cfg(test)]
    pub(crate) fn mark_all_verified(&mut self) {
        for slot in &mut self.shard_verified {
            *slot = true;
        }
    }

    /// Index every shard's lazily-servable (non-inductive) constants into one
    /// global name index. First occurrence across shards wins (matching the
    /// merge "last-writer-wins"-free append model and the eager loader's
    /// insert-only/idempotent-on-duplicate registration).
    pub(crate) fn from_readers(readers: Vec<ShardMmapReader>) -> Self {
        let module_count = readers.len();
        Self::from_readers_with_modules(readers, vec![None; module_count])
    }

    /// Like [`Self::from_readers`] but records each shard's MODULE name (its
    /// `<module>.mathverse` file stem), aligned with `readers` by index, so
    /// [`Self::owning_module`] can map a served name back to the module that
    /// defines it (for the PARAGON coverage repair).
    fn from_readers_with_modules(
        readers: Vec<ShardMmapReader>,
        shard_modules: Vec<Option<String>>,
    ) -> Self {
        let mut by_name: HashMap<Name, (u32, u32)> = HashMap::new();
        for (s, reader) in readers.iter().enumerate() {
            for (i, c) in reader.constants.iter().enumerate() {
                if !servable_kind(c.decl_kind) {
                    continue;
                }
                if let Some(name) = reader.strings.get(c.name_idx as usize) {
                    // Kernel-regenerated inductive auxiliaries (`noConfusion`/
                    // `noConfusionType`) are NEVER served lazily — the eager leg
                    // re-derives them via `regenerate_missing_no_confusion`, so a
                    // shard's olean-stored bytes would diverge (the measured
                    // `Mathlib/Logic` fidelity gap; see
                    // `is_kernel_regenerated_aux_name`). Leave them unindexed so
                    // both legs resolve them through the same eager path.
                    if is_kernel_regenerated_aux_name(name) {
                        continue;
                    }
                    by_name
                        .entry(Name::from_string(name))
                        .or_insert((s as u32, i as u32));
                }
            }
        }
        let shard_verified = vec![false; readers.len()];
        Self {
            shared: Arc::new(SharedReaders {
                readers,
                by_name,
                shard_modules,
            }),
            shard_verified,
            cache: FrozenMap::new(),
        }
    }

    /// The MODULE name (shard `<module>.mathverse` file stem) that serves `name`,
    /// if any. The PARAGON coverage repair uses this to eager-load the module that
    /// defines a missing name (e.g. an auto-generated `X.proof_N` whose parent `X`
    /// the source serves — eager-loading `X`'s module synthesizes `X.proof_N` too).
    pub(crate) fn owning_module(&self, name: &Name) -> Option<&str> {
        let (shard, _) = self.shared.by_name.get(name)?;
        self.shared
            .shard_modules
            .get(*shard as usize)
            .and_then(|m| m.as_deref())
    }

    /// A FRESH view over the SAME (immutable, zero-copy-shared) mmap readers and
    /// name index, but with an EMPTY materialization cache.
    ///
    /// This is the PARAGON wave-boundary memory primitive: the demand-fold cache
    /// ([`FrozenMap`]) is append-only and can never evict, so a long run that
    /// touches every closure constant would re-accumulate the whole closure's
    /// `ConstantInfo` in RAM. Dropping the previous source (and the base env that
    /// wrapped it) and installing a `fresh_view` at a wave boundary returns that
    /// accumulated cache to the allocator while the shared readers (the cheap,
    /// mmap-backed part) stay put — so steady-state resident `ConstantInfo` is
    /// bounded by one wave's working set, not the whole closure.
    ///
    /// SOUNDNESS-NEUTRAL: `get` materializes byte-identical `ConstantInfo` from
    /// the same shards regardless of cache state (the cache is a pure memo), so a
    /// fresh view serves exactly the same constants as the original — only the
    /// transient cache differs.
    pub(crate) fn fresh_view(&self) -> Self {
        Self {
            shared: Arc::clone(&self.shared),
            shard_verified: self.shard_verified.clone(),
            cache: FrozenMap::new(),
        }
    }

    /// Number of shards this source holds (the loader iterates these for the
    /// load-time content-binding verification).
    pub(crate) fn shard_count(&self) -> usize {
        self.shared.readers.len()
    }

    /// Borrow one shard's reader (the loader reads its header + `source_module`
    /// to recompute the source-olean digest).
    pub(crate) fn reader(&self, shard: usize) -> Option<&ShardMmapReader> {
        self.shared.readers.get(shard)
    }

    /// Mark a shard as load-time verified so its `by_name` entries become
    /// servable. SOUNDNESS: called ONLY after the loader recomputes the shard's
    /// source-olean digest against the on-disk olean for its declaring module and
    /// confirms a full match (hash + len + subset). Idempotent; out-of-range is
    /// a no-op.
    /// The shard index that would serve `name`, if any (verification-agnostic —
    /// like [`ConstantSource::contains`], this is bookkeeping for on-first-touch
    /// verification, NEVER a serving predicate; `get()` remains the sole gated
    /// serve path).
    pub(crate) fn shard_of(&self, name: &Name) -> Option<u32> {
        self.shared.by_name.get(name).map(|&(shard, _)| shard)
    }

    /// The `(shard, constant index)` that would serve `name` (verification-
    /// agnostic; see [`Self::shard_of`]).
    pub(crate) fn shard_entry_of(&self, name: &Name) -> Option<(u32, u32)> {
        self.shared.by_name.get(name).copied()
    }

    /// The MODULE name of `shard` (its `<module>.mathverse` file stem), if the
    /// shard was loaded from a backing file.
    pub(crate) fn shard_module(&self, shard: usize) -> Option<&str> {
        self.shared.shard_modules.get(shard)?.as_deref()
    }

    /// Whether `shard` has passed load-time content-binding verification.
    pub(crate) fn is_shard_verified(&self, shard: u32) -> bool {
        self.shard_verified
            .get(shard as usize)
            .copied()
            .unwrap_or(false)
    }

    pub(crate) fn mark_shard_verified(&mut self, shard: usize) {
        if let Some(slot) = self.shard_verified.get_mut(shard) {
            *slot = true;
        }
    }

    /// All names this source can serve (verified or not), for the v3-binding
    /// tests that drive the load-time verification explicitly.
    #[cfg(test)]
    pub(crate) fn servable_names_for_test(&self) -> Vec<Name> {
        self.shared.by_name.keys().cloned().collect()
    }

    /// Build a source over EVERY `.mathverse` shard found beneath `dir`
    /// (recursively, matching the library loader's discovery). The closure shards
    /// the zero-copy loader installs live in such a directory (one per dependency
    /// module). Returns an error if no shard is found (a misconfigured
    /// `CLEAN_CLOSURE_SHARDS` must hard-fail, never silently serve nothing).
    pub(crate) fn from_dir(dir: &Path) -> Result<Self, MathverseError> {
        let files = discover_mathverse_files(dir);
        if files.is_empty() {
            return Err(MathverseError::ShardFileUnreadable {
                path: dir.display().to_string(),
                source: std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    "no .mathverse shards found under closure-shards directory",
                ),
            });
        }
        let mut readers = Vec::with_capacity(files.len());
        let mut shard_modules = Vec::with_capacity(files.len());
        for f in files {
            // The shard file is `<dotted.module>.mathverse`; the stem is the module.
            shard_modules.push(
                f.file_stem()
                    .and_then(|s| s.to_str())
                    .map(|s| s.to_string()),
            );
            readers.push(ShardMmapReader::open_lazy(&f)?);
        }
        Ok(Self::from_readers_with_modules(readers, shard_modules))
    }

    /// Number of constants this source can serve (post-hybrid-filter).
    pub(crate) fn servable_len(&self) -> usize {
        self.shared.by_name.len()
    }

    /// All names this source can serve (diagnostics / closure-diff tooling).
    #[cfg(test)]
    pub(crate) fn servable_names(&self) -> Vec<Name> {
        self.shared.by_name.keys().cloned().collect()
    }

    /// DEMAND-PAGED reconstruct of one constant's type/value sub-DAGs straight out
    /// of the shard's mmap'd expr arena — only the reachable 16-byte `FlatExpr`
    /// entries fault in. Byte-identical to the slice-based fold (pinned by
    /// `shard_reconstruct::mmap_subdag_matches_slice_subdag`), so the served
    /// `ConstantInfo` is exactly what the eager `ShardReader` path produced.
    fn reconstruct_subdag(reader: &ShardMmapReader, root_idx: u32) -> Option<Expr> {
        // `read_expr` decodes one FlatExpr from `mmap[base..base+16]` — the only
        // bytes that fault in for that node.
        let read_flat = |i: u32| reader.read_expr(i).map_err(|e| e.to_string());
        reconstruct_single_subdag_with_reader(
            read_flat,
            reader.header.expr_count,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            root_idx,
        )
        .ok()
    }

    fn materialize(&self, shard: u32, idx: u32) -> Option<ConstantInfo> {
        let reader = self.shared.readers.get(shard as usize)?;
        materialize_constant_from_reader(reader, idx)
    }
}

/// The kind-agnostic content of one shard constant — reconstructed for EVERY
/// declaration kind (incl. inductive families, which cannot be expressed as a
/// `ConstantInfo`). What a trust receipt needs: every constant's type (+value)
/// for a content hash and an axiom walk, its declared kind, and its per-constant
/// `KernelVerified` verdict.
pub(crate) struct ShardConstFact {
    /// Fully-qualified name.
    pub(crate) name: Name,
    /// Raw `DeclKind` byte (Definition/Theorem/Opaque/Axiom/Inductive/…).
    pub(crate) decl_kind: u8,
    /// Universe parameters.
    pub(crate) level_params: Vec<Name>,
    /// The constant's type (always present).
    pub(crate) type_: Expr,
    /// The constant's value, if the shard stores one (`None` for axioms /
    /// inductive families / value-less entries).
    pub(crate) value: Option<Expr>,
    /// Whether the shard stamped this constant `KernelVerified`.
    pub(crate) kernel_verified: bool,
}

/// Read a kind-agnostic [`ShardConstFact`] for EVERY constant of every
/// `.mathverse` shard under `dir` — the source-of-truth read for a trust receipt
/// over a stamped Mathverse corpus. Reconstructs each constant's type (+value)
/// straight from the shard's mmap arena (the same demand-paged fold the lazy
/// loader uses), independent of any verify-env proof-value elision. Does NOT gate
/// on the definitional kinds, so inductive families are included (with their
/// type) — needed for a COMPLETE axiom walk and total KernelVerified coverage.
pub(crate) fn shard_dir_facts(dir: &Path) -> Result<Vec<ShardConstFact>, MathverseError> {
    let files = discover_mathverse_files(dir);
    if files.is_empty() {
        return Err(MathverseError::ShardFileUnreadable {
            path: dir.display().to_string(),
            source: std::io::Error::new(std::io::ErrorKind::NotFound, "no .mathverse shards found"),
        });
    }
    let kv = crate::types::ImportConfidence::KernelVerified as u8;
    let mut out: Vec<ShardConstFact> = Vec::new();
    for f in files {
        let reader = ShardMmapReader::open_lazy(&f)?;
        for idx in 0..reader.constants.len() {
            let c = &reader.constants[idx];
            let Some(name) = reader.strings.get(c.name_idx as usize) else {
                continue;
            };
            let Some(type_) = reconstruct_subdag_for(&reader, c.type_idx) else {
                continue;
            };
            let value = if c.value_idx != NO_VALUE {
                reconstruct_subdag_for(&reader, c.value_idx)
            } else {
                None
            };
            let level_params = reconstruct_level_params(
                &reader.strings,
                c.level_params_start,
                c.level_params_count,
            )
            .unwrap_or_default();
            out.push(ShardConstFact {
                name: Name::from_string(name),
                decl_kind: c.decl_kind,
                level_params,
                type_,
                value,
                kernel_verified: c.import_confidence == kv,
            });
        }
    }
    Ok(out)
}

/// Materialize one constant's [`ConstantInfo`] via the EXACT demand-paged path
/// the lazy `get()` serves — extracted so the build-time round-trip oracle
/// (`build_kernel_faithful_shard`) can re-open the serialized bytes and assert
/// it verdict-equals the source. Reconstructs type/value sub-DAGs from the
/// reader's mmap arena, reconstructs level params, and resolves the served
/// `(kind, reducibility)` exactly as `materialize` does.
pub(crate) fn materialize_constant_from_reader(
    reader: &ShardMmapReader,
    idx: u32,
) -> Option<ConstantInfo> {
    let c: &MathverseConstantHeader = reader.constants.get(idx as usize)?;
    let name = reader.strings.get(c.name_idx as usize)?;

    // Type is required; value is optional (sentinel = NO_VALUE). Both are folded
    // demand-paged against the mmap arena.
    let type_expr = reconstruct_subdag_for(reader, c.type_idx)?;
    let value_expr = if c.value_idx != NO_VALUE {
        reconstruct_subdag_for(reader, c.value_idx)
    } else {
        None
    };
    let level_params =
        reconstruct_level_params(&reader.strings, c.level_params_start, c.level_params_count)
            .unwrap_or_default();
    let decl_kind = DeclKind::try_from(c.decl_kind).ok()?;

    let (kind, mut reducibility) = kind_and_reducibility(decl_kind)?;
    // VERDICT PARITY with the eager olean path. The kernel's δ-unfold ordering
    // keys on `reducibility`, so the lazily-served value MUST match eager.
    //
    // PRIMARY: a shard built by the parity-faithful builder records the EXACT
    // eager reducibility (incl. `@[reducible]`/Abbrev and the `Regular(height)`
    // height) in the header; use it verbatim when present.
    if let Some(r) = c.reducibility() {
        reducibility = r;
    } else if matches!(kind, ConstantKind::Definition)
        && !matches!(reducibility, Reducibility::Reducible)
    {
        // LEGACY shards (no recorded reducibility): fall back to the
        // projection-function heuristic that the eager loader also applies in
        // `decl_to_constant_info` — projection functions (`Membership.mem`,
        // `HPow.hPow`, …) are `Reducible` so typeclass projection chains
        // δ-reduce during is_def_eq.
        if let Some(value) = &value_expr {
            if is_projection_fn_body(value) {
                reducibility = Reducibility::Reducible;
            }
        }
    }
    Some(ConstantInfo::new_with_reducibility(
        Name::from_string(name),
        level_params,
        type_expr,
        value_expr,
        reducibility,
        kind,
    ))
}

/// Reconstruct ONLY what the per-constant demand walk needs for reference
/// collection: the constant's TYPE, plus its VALUE only when it is a
/// DEFINITION — the exact discipline of the eager types-only dep loader
/// (`parse_dep_module_types_only` skips Theorem/Opaque proof bodies, so the
/// eager walk never expands their references either). Returns
/// `(name, type_expr, definition_value)`.
///
/// This keeps the lazy walk's transitive closure EQUAL to the eager walk's
/// (not a proof-value superset), and never materializes a theorem proof term
/// during the walk — the two defects the full-constant walk exhibited
/// (4x closure blow-up, minutes of proof-term reconstruction).
pub(crate) fn walk_refs_from_reader(
    reader: &ShardMmapReader,
    idx: u32,
) -> Option<(Name, Expr, Option<Expr>)> {
    let c: &MathverseConstantHeader = reader.constants.get(idx as usize)?;
    let name = reader.strings.get(c.name_idx as usize)?;
    let decl_kind = DeclKind::try_from(c.decl_kind).ok()?;
    let (kind, _) = kind_and_reducibility(decl_kind)?;
    let type_expr = reconstruct_subdag_for(reader, c.type_idx)?;
    let value_expr = if matches!(kind, ConstantKind::Definition) && c.value_idx != NO_VALUE {
        reconstruct_subdag_for(reader, c.value_idx)
    } else {
        None
    };
    Some((Name::from_string(name), type_expr, value_expr))
}

/// Demand-paged reconstruct of one sub-DAG against a reader's mmap arena.
/// Free-function twin of [`ShardConstantSource::reconstruct_subdag`].
fn reconstruct_subdag_for(reader: &ShardMmapReader, root_idx: u32) -> Option<Expr> {
    let read_flat = |i: u32| reader.read_expr(i).map_err(|e| e.to_string());
    reconstruct_single_subdag_with_reader(
        read_flat,
        reader.header.expr_count,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        root_idx,
    )
    .ok()
}

/// Detect a projection-function body: `λ* . Proj(...)`. Mirrors clean-olean's
/// `is_projection_fn_body` (import/convert.rs) so the lazy source assigns the
/// SAME `Reducible` reducibility to projection functions the eager olean path
/// does — required for verdict parity (projection chains must δ-reduce).
fn is_projection_fn_body(expr: &clean_kernel::expr::Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    let mut e = expr;
    loop {
        match e.kind() {
            ExprKind::Lam(_, _, body) => e = body,
            ExprKind::Proj(_, _, _) => return true,
            _ => return false,
        }
    }
}

impl ConstantSource for ShardConstantSource {
    fn get(&self, name: &Name) -> Option<&ConstantInfo> {
        if let Some(ci) = self.cache.get(name) {
            return Some(ci);
        }
        let (shard, idx) = *self.shared.by_name.get(name)?;
        // SOUNDNESS (per-entry serve gate, Step 7): a name is served ONLY from a
        // load-time VERIFIED shard (content-bound to the on-disk olean for its
        // declaring module). An unverified serving shard returns `None` => the
        // hybrid loader treats it as a coverage miss => HARD EAGER FALLBACK. The
        // verify runs BEFORE the prelude-stub override loop that itself calls
        // `get()`, so a forged shard can never forget_decl a trusted stub.
        if !self
            .shard_verified
            .get(shard as usize)
            .copied()
            .unwrap_or(false)
        {
            return None;
        }
        let ci = self.materialize(shard, idx)?;
        // SOUNDNESS (name-binding, adversarial review wubp2ra43 hardening item 5):
        // `materialize` labels the constant with its SHARD-HEADER name. If that does
        // not equal the REQUESTED `name`, the `by_name` index is mis-built/corrupt
        // and serving this entry would silently substitute the wrong (type, value)
        // under `name`. Refuse: `None` propagates as a coverage miss, which the
        // hybrid loader turns into a HARD EAGER FALLBACK — strictly no-weaker than
        // the eager olean path. A correctly-built index makes this branch dead.
        if ci.name != *name {
            return None;
        }
        Some(self.cache.insert(name.clone(), ci))
    }

    fn contains(&self, name: &Name) -> bool {
        // VERIFICATION-AGNOSTIC: reports only whether the name is INDEXED, not
        // whether its shard is load-time verified — so it is NEVER a serving
        // predicate. `get()` is the sole gated serve path (it refuses an
        // unverified shard); `contains()` is for index/coverage bookkeeping only.
        self.shared.by_name.contains_key(name)
    }

    fn names(&self) -> Vec<Name> {
        // All INDEXED names (verification-agnostic, like `contains`): callers
        // enumerate then `get()` each, and `get()` applies the per-entry serve
        // gate (unverified shards yield `None`), so this is not a serving path.
        self.shared.by_name.keys().cloned().collect()
    }

    fn fresh(&self) -> Option<std::sync::Arc<dyn ConstantSource>> {
        // `fresh_view` shares the immutable mmap readers + name index and the
        // per-shard verified flags zero-copy, but starts an EMPTY FrozenMap —
        // the append-only memo of materialized `ConstantInfo` that a long
        // chunked run must periodically release. Materialization is
        // deterministic against the (unchanged) verified arenas, so the fresh
        // view resolves every name byte-identically: the `fresh` contract.
        Some(std::sync::Arc::new(self.fresh_view()))
    }
}

/// Only Definition/Theorem/Axiom/Opaque are served lazily (the HYBRID); inductive
/// families stay eager until the shard format is lossless (Phase 2 / L2 path-(a)).
pub(crate) fn servable_kind(decl_kind: u8) -> bool {
    matches!(
        DeclKind::try_from(decl_kind),
        Ok(DeclKind::Definition | DeclKind::Theorem | DeclKind::Axiom | DeclKind::Opaque)
    )
}

/// True for the KERNEL-REGENERATED inductive auxiliaries `X.noConfusion` and
/// `X.noConfusionType`, which the HYBRID closure loader must serve EAGERLY (never
/// from a shard), exactly like recursors and the rest of an inductive family.
///
/// WHY (the shard-fidelity blocker, measured on `Mathlib/Logic`): although Lean
/// serializes `X.noConfusion`/`X.noConfusionType` as ordinary `Definition`s in
/// the `.olean`, the eager closure loader does NOT trust those stored bytes — it
/// runs [`Environment::regenerate_missing_no_confusion`] as a post-load fixup
/// (see `clean_olean::import::load`), which re-derives the kernel-CANONICAL form
/// (Lean-faithful `casesOn` argument order, `outParam`-preserving parameter
/// binders, Reducible). The shard builder, by contrast, captures the raw
/// olean-STORED form. The two are not byte-identical: over the 56,785-constant
/// `Mathlib/Logic/Basic` closure, EVERY shard-reconstruct vs eager-import
/// divergence is a `noConfusion` (1,316) or `noConfusionType` (199) — 1,515
/// constants, 100% of the gap, and the source of the 10-constant `Mathlib/Logic`
/// KV regression that keeps the demand-paged base default-OFF.
///
/// Excluding them from the lazy shard index makes BOTH legs resolve them through
/// the SAME eager `regenerate_missing_no_confusion` path (the inductive base
/// regenerates them; a target that references one and finds it neither eager nor
/// lazy is a coverage miss that the PARAGON repair / hard-fallback covers — never
/// a wrong verdict). SOUNDNESS-NEUTRAL: this only moves WHERE these auxiliaries
/// are served (eager regen vs shard bytes), strictly toward the eager oracle the
/// KV-invariance gate measures against; it changes no `is_def_eq`/`check_type`.
pub(crate) fn is_kernel_regenerated_aux_name(name: &str) -> bool {
    // Match the LAST dotted component only (e.g. `Foo.Bar.noConfusion`), never a
    // user constant that merely contains the substring.
    let last = name.rsplit('.').next().unwrap_or(name);
    matches!(last, "noConfusion" | "noConfusionType")
}

/// Map shard `DeclKind` to kernel `(ConstantKind, Reducibility)`.
///
/// VERDICT PARITY with the eager olean path (`clean_olean::import::convert::
/// decl_to_constant_info`): a Theorem's reducibility is **`Opaque`**, not
/// `Regular(0)`. The two are NOT interchangeable for the verdict — the lazy
/// δ-delta loop branches on `Regular(_)` (`tc/def_eq/delta.rs:245`
/// `lazy_delta_step_equal`): when both sides are the SAME constant and its
/// reducibility is `Regular(_)`, the kernel takes the args-only fast path and
/// caches an args-failure on miss; when it is `Opaque` it skips straight to the
/// (proof-irrelevant) unfold path. A theorem proof term served as `Regular(0)`
/// therefore drives the same-const comparison down a different reduction route
/// than the eager oracle, producing a spurious `TypeMismatch` for decls whose
/// proofs chain through it (observed: the 7 `Membership`-binder-heavy decls in
/// `Mathlib/Logic/Basic` — `mem_ite`, `dite_mem`, … — diverged eager 355 vs
/// lazy 348 purely on this one field). The HEIGHT inside `Regular(h)` is
/// verdict-neutral (it only orders unfolding), but the `Regular`-vs-`Opaque`
/// CATEGORY is not, so it must mirror the eager oracle exactly. Definition
/// height is verdict-neutral, so `Regular(0)` is sound there. Opaque/Axiom are
/// `Irreducible`. The eager-vs-lazy KernelVerified-set invariance gate is the
/// arbiter.
fn kind_and_reducibility(decl_kind: DeclKind) -> Option<(ConstantKind, Reducibility)> {
    Some(match decl_kind {
        DeclKind::Definition => (ConstantKind::Definition, Reducibility::Regular(0)),
        DeclKind::Theorem => (ConstantKind::Theorem, Reducibility::Opaque),
        DeclKind::Opaque => (ConstantKind::Opaque, Reducibility::Irreducible),
        DeclKind::Axiom => (ConstantKind::Axiom, Reducibility::Irreducible),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardWriter;
    use crate::types::{
        AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
        NO_VALUE,
    };
    use clean_kernel::flat::{FlatExpr, FlatLevel};

    /// DIAGNOSTIC (opt-in): materialize CLEAN_DIAG_NAME from the closure shards
    /// at CLEAN_DIAG_SHARDS and report whether its type/value contain FVar nodes
    /// (a stored constant should be FVar-free; an FVar is the smoking gun for the
    /// olean-import vs shard-reconstruct Expr-identity gap). Skips when unset.
    #[test]
    fn diag_materialize_name() {
        let (Ok(dir), Ok(name)) = (
            std::env::var("CLEAN_DIAG_SHARDS"),
            std::env::var("CLEAN_DIAG_NAME"),
        ) else {
            return;
        };
        let src = ShardConstantSource::from_dir(std::path::Path::new(&dir)).expect("load shards");
        let nm = Name::from_string(&name);
        match src.get(&nm) {
            None => eprintln!(
                "DIAG: `{name}` NOT served lazily (servable={})",
                src.servable_len()
            ),
            Some(ci) => {
                let mut tyset = std::collections::HashSet::new();
                ci.type_.collect_constants_into(&mut tyset);
                eprintln!(
                    "DIAG `{name}`: kind={:?} red={:?} type_fvar={} value_fvar={} type_consts={}",
                    ci.kind,
                    ci.reducibility,
                    expr_has_fvar(&ci.type_),
                    ci.value.as_ref().map(expr_has_fvar).unwrap_or(false),
                    tyset.len(),
                );
                eprintln!("DIAG type = {}", ci.type_);
            }
        }
    }

    fn expr_has_fvar(e: &clean_kernel::expr::Expr) -> bool {
        use clean_kernel::expr::ExprKind;
        let mut stack = vec![e];
        while let Some(cur) = stack.pop() {
            match cur.kind() {
                ExprKind::FVar(_) => return true,
                ExprKind::App(a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    stack.push(t);
                    stack.push(b);
                }
                ExprKind::Let(_, t, v, b, _) => {
                    stack.push(t);
                    stack.push(v);
                    stack.push(b);
                }
                ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => stack.push(x),
                _ => {}
            }
        }
        false
    }

    /// Write a one-constant shard whose single definitional constant `name` has
    /// type `Sort 0` and no value into `dir`, then open it DEMAND-PAGED via
    /// `ShardMmapReader::open_lazy` (the exact path the lazy source uses). Each
    /// shard is written to its own file so the multi-shard index is exercised over
    /// independent arenas; the caller keeps `dir` alive for the reader's mmap.
    fn one_def_shard_reader(dir: &Path, name: &str, kind: DeclKind) -> ShardMmapReader {
        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let ty = w.add_expr(FlatExpr::sort(l0));
        let s = w.add_string(name);
        w.add_constant(MathverseConstantHeader {
            name_idx: s,
            type_idx: ty,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: kind as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        let mut buf = Vec::new();
        w.write(&mut buf).expect("serialize shard");
        // Unique filename per constant so each shard is a distinct file/mmap.
        let path = dir.join(format!("{}.mathverse", name.replace('.', "_")));
        std::fs::write(&path, &buf).expect("write shard file");
        ShardMmapReader::open_lazy(&path).expect("mmap-open shard")
    }

    /// A source over MULTIPLE shards indexes every shard's servable constants into
    /// one name space and materializes each against its own arena, with a stable
    /// cached `&ConstantInfo` per name (the property the lazy loader relies on).
    #[test]
    fn test_multi_shard_source_indexes_and_serves_all_shards() {
        let dir = tempfile::tempdir().expect("tempdir");
        let r1 = one_def_shard_reader(dir.path(), "Closure.Alpha", DeclKind::Definition);
        let r2 = one_def_shard_reader(dir.path(), "Closure.Beta", DeclKind::Theorem);
        let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
        // Mark verified: this unit test exercises the materialize/get path, not
        // the load-time olean-binding check.
        src.mark_all_verified();
        assert_eq!(src.servable_len(), 2, "both shards' constants are servable");

        let alpha = Name::from_string("Closure.Alpha");
        let beta = Name::from_string("Closure.Beta");
        assert!(src.contains(&alpha) && src.contains(&beta));

        let a1 = src.get(&alpha).expect("materialize Alpha");
        assert_eq!(a1.name, alpha);
        assert_eq!(a1.kind, ConstantKind::Definition);
        let a1_ptr = a1 as *const ConstantInfo;
        let a2 = src.get(&alpha).expect("cached Alpha");
        assert!(
            std::ptr::eq(a1_ptr, a2 as *const ConstantInfo),
            "repeat get returns the SAME cached &ConstantInfo"
        );

        let b = src.get(&beta).expect("materialize Beta from the 2nd shard");
        assert_eq!(b.kind, ConstantKind::Theorem);

        // An unknown name resolves nowhere.
        assert!(!src.contains(&Name::from_string("Closure.Missing")));
        assert!(src.get(&Name::from_string("Closure.Missing")).is_none());
    }

    /// PARAGON wave-fresh source: `fresh_view` shares the SAME servable set and
    /// materializes IDENTICAL constants, but starts with an EMPTY cache — so a
    /// wave boundary that drops the old view and installs a fresh one releases the
    /// accumulated `ConstantInfo` while serving exactly the same constants.
    #[test]
    fn test_fresh_view_shares_servable_set_with_empty_cache() {
        let dir = tempfile::tempdir().expect("tempdir");
        let r1 = one_def_shard_reader(dir.path(), "Wave.Alpha", DeclKind::Definition);
        let r2 = one_def_shard_reader(dir.path(), "Wave.Beta", DeclKind::Theorem);
        let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
        // Mark verified: `get()` serves ONLY from a load-time-verified shard
        // (the per-entry serve gate); this unit test exercises the
        // materialize/fresh-view path, not the load-time olean-binding check.
        src.mark_all_verified();

        // Warm the original's cache.
        let alpha = Name::from_string("Wave.Alpha");
        let _ = src.get(&alpha).expect("materialize Alpha");
        assert_eq!(src.cache.len(), 1, "original cached the touched constant");

        // A fresh view: same servable set, EMPTY cache.
        let view = src.fresh_view();
        assert_eq!(
            view.servable_len(),
            src.servable_len(),
            "fresh view serves the same set"
        );
        assert_eq!(view.cache.len(), 0, "fresh view starts with an empty cache");
        assert!(view.contains(&alpha), "fresh view can serve the same names");

        // Materializing through the fresh view yields the SAME constant (kind/name).
        let a_orig = src.get(&alpha).expect("orig Alpha");
        let a_view = view.get(&alpha).expect("view Alpha");
        assert_eq!(a_orig.name, a_view.name);
        assert_eq!(a_orig.kind, a_view.kind);
        assert_eq!(view.cache.len(), 1, "fresh view caches independently");

        // The shared readers/index are zero-copy shared (no re-mmap, no re-index).
        assert!(
            Arc::ptr_eq(&src.shared, &view.shared),
            "fresh view shares the immutable readers Arc"
        );
    }

    /// PARAGON coverage repair: `from_dir` records each shard's MODULE name (its
    /// `<module>.mathverse` file stem), so `owning_module` maps a served name back
    /// to the module that defines it — what the repair uses to eager-load the
    /// owner of a missing name (or its ancestor).
    #[test]
    fn test_owning_module_maps_served_name_to_shard_module() {
        let dir = tempfile::tempdir().expect("tempdir");
        // Write a shard whose FILE STEM is the dotted module name `My.Mod.Foo`
        // and which serves one definitional constant `My.Mod.Foo.bar`.
        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let ty = w.add_expr(FlatExpr::sort(l0));
        let s = w.add_string("My.Mod.Foo.bar");
        w.add_constant(MathverseConstantHeader {
            name_idx: s,
            type_idx: ty,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        let mut buf = Vec::new();
        w.write(&mut buf).expect("serialize shard");
        std::fs::write(dir.path().join("My.Mod.Foo.mathverse"), &buf).expect("write shard");

        let src = ShardConstantSource::from_dir(dir.path()).expect("load shards");
        let bar = Name::from_string("My.Mod.Foo.bar");
        assert_eq!(
            src.owning_module(&bar),
            Some("My.Mod.Foo"),
            "a served name resolves to its shard's module (file stem)"
        );
        // An unserved name has no owning module (the repair then walks ancestors).
        assert_eq!(
            src.owning_module(&Name::from_string("My.Mod.Foo.bar.proof_1")),
            None,
            "an unserved name (e.g. a synthesized child) has no direct owning module"
        );
    }

    /// Inductive-family kinds are NOT servable here (the HYBRID split): an
    /// `Inductive`/`Recursor` constant in a shard is left to the eager olean path.
    #[test]
    fn test_inductive_kinds_are_not_servable() {
        let dir = tempfile::tempdir().expect("tempdir");
        let r = one_def_shard_reader(dir.path(), "Closure.MyInd", DeclKind::Inductive);
        let src = ShardConstantSource::from_readers(vec![r]);
        assert_eq!(
            src.servable_len(),
            0,
            "inductive families are not lazily servable"
        );
        assert!(!src.contains(&Name::from_string("Closure.MyInd")));
    }

    /// THE invariance proof (Phase-1 soundness gate, integration-level): verifying a
    /// constant against a closure served LAZILY (via `set_constant_source`) must yield
    /// the IDENTICAL kernel verdict as against the SAME closure loaded EAGERLY into
    /// `self.constants`. The only variable is WHERE a dep lives (eager map vs lazy
    /// source) — `get_const` returns the same `ConstantInfo` either way, so the kernel
    /// check must be byte-for-byte verdict-identical. Any divergence = a real bug.
    /// Opt-in via `CLEAN_TEST_SHARD`; skips otherwise.
    #[test]
    fn lazy_closure_verdict_matches_eager() {
        let Ok(path) = std::env::var("CLEAN_TEST_SHARD") else {
            eprintln!("skip: set CLEAN_TEST_SHARD to a real .mathverse file");
            return;
        };
        use clean_kernel::env::{Environment, TrustedEnvExt};
        use clean_kernel::Declaration;
        use std::sync::Arc;

        // Reconstruct all servable constants -> ConstantInfo (identical to what the
        // lazy source materializes), then drop the reader.
        // Prelude constants exist in both legs (eager via with_prelude; lazy shadowed
        // by get_const's eager-first), so exclude them from the extended set — else
        // extend_constants_unchecked debug-asserts on the prelude collision.
        let prelude_names: std::collections::HashSet<Name> = Environment::with_prelude()
            .constants()
            .map(|c| c.name.clone())
            .collect();

        // The lazy source serves every servable constant on demand from the mmap.
        let source: Arc<ShardConstantSource> = Arc::new(ShardConstantSource::new(
            ShardMmapReader::open_lazy(&path).expect("mmap-open shard (lazy source)"),
        ));

        // Reference set = the lazy source's OWN materialization for every servable
        // name (== exactly what `get` returns). The eager leg below extends
        // `self.constants` with these; the lazy leg serves them from the source.
        // Excluding prelude names avoids the `extend_constants_unchecked` dup-assert.
        let mut infos: Vec<ConstantInfo> = Vec::new();
        let mut names: Vec<Name> = source.servable_names();
        names.sort();
        for name in names {
            if prelude_names.contains(&name) {
                continue;
            }
            if let Some(ci) = ConstantSource::get(source.as_ref(), &name) {
                infos.push(ci.clone());
            }
        }
        assert!(!infos.is_empty(), "no servable constants");

        let target_idxs: Vec<usize> = infos
            .iter()
            .enumerate()
            .filter(|(_, c)| c.value.is_some())
            .map(|(i, _)| i)
            .collect();
        let stride = (target_idxs.len() / 60).max(1);
        let (mut ok_eq, mut err_eq, mut divergence) = (0u64, 0u64, 0u64);

        for &t in target_idxs.iter().step_by(stride) {
            let target = &infos[t];
            let Some(value) = target.value.clone() else {
                continue;
            };
            let decl = match target.kind {
                ConstantKind::Theorem => Declaration::Theorem {
                    name: target.name.clone(),
                    level_params: target.level_params.clone(),
                    type_: target.type_.clone(),
                    value,
                },
                ConstantKind::Definition => Declaration::Definition {
                    name: target.name.clone(),
                    level_params: target.level_params.clone(),
                    type_: target.type_.clone(),
                    value,
                    is_reducible: false,
                },
                ConstantKind::Opaque => Declaration::Opaque {
                    name: target.name.clone(),
                    level_params: target.level_params.clone(),
                    type_: target.type_.clone(),
                    value,
                },
                ConstantKind::Axiom => continue,
            };

            // EAGER: closure (all servable except the target) in self.constants.
            let mut eager = Environment::with_prelude();
            eager.extend_constants_unchecked(
                infos
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != t)
                    .map(|(_, c)| c.clone()),
            );
            let v_eager = eager.add_decl(decl.clone()).is_ok();

            // LAZY: closure served on demand from the source (nothing eager).
            let mut lazy = Environment::with_prelude();
            lazy.set_constant_source(source.clone());
            let v_lazy = lazy.add_decl(decl).is_ok();

            if v_eager == v_lazy {
                if v_eager {
                    ok_eq += 1;
                } else {
                    err_eq += 1;
                }
            } else {
                divergence += 1;
                eprintln!(
                    "DIVERGENCE {:?}: eager={v_eager} lazy={v_lazy}",
                    target.name
                );
            }
        }
        eprintln!("INVARIANCE on {path}: ok_eq={ok_eq} err_eq={err_eq} divergence={divergence}");
        assert_eq!(
            divergence, 0,
            "lazy closure changed a kernel verdict vs eager"
        );
        assert!(ok_eq + err_eq > 0, "validated nothing");
    }

    /// End-to-end on a real shard: a servable constant materializes to a
    /// `ConstantInfo` with the right name/kind, and a second `get` returns the SAME
    /// cached `&ConstantInfo` (the stable-ref property the lazy loader relies on).
    /// Opt-in via `CLEAN_TEST_SHARD`; skips otherwise.
    #[test]
    fn real_shard_source_materializes_and_caches() {
        let Ok(path) = std::env::var("CLEAN_TEST_SHARD") else {
            eprintln!("skip: set CLEAN_TEST_SHARD to a real .mathverse file");
            return;
        };
        let reader = ShardMmapReader::open_lazy(&path).expect("mmap-open real shard");
        let src = ShardConstantSource::new(reader);
        assert!(src.servable_len() > 0, "no servable constants in shard");
        let name = src
            .shared
            .by_name
            .keys()
            .next()
            .cloned()
            .expect("a servable name");
        assert!(src.contains(&name));
        let ci1 = src.get(&name).expect("materialize");
        assert_eq!(ci1.name, name);
        let ci1_ptr = ci1 as *const ConstantInfo;
        let ci2 = src.get(&name).expect("cached");
        assert!(
            std::ptr::eq(ci1_ptr, ci2 as *const ConstantInfo),
            "second get must return the SAME cached &ConstantInfo"
        );
        assert_eq!(src.cache.len(), 1, "exactly one materialization cached");
        eprintln!(
            "ShardConstantSource: {} servable; materialized {name:?} kind={:?}",
            src.servable_len(),
            ci1.kind
        );
    }

    /// SHARD-FIDELITY INVARIANCE (the `Mathlib/Logic` blocker): kernel-regenerated
    /// inductive auxiliaries (`X.noConfusion` / `X.noConfusionType`) are NEVER
    /// indexed for lazy serving, even when present in a shard's bytes as plain
    /// `Definition`s — the eager leg re-derives them via
    /// `regenerate_missing_no_confusion`, so a shard's olean-stored form would
    /// diverge. A regular `Definition`/`Theorem` IS still served. This pins the
    /// exclusion that drove the `diag_routed_env_diff` Logic-closure struct diffs
    /// from 1,515 (100% noConfusion-family) to 0 and made the lazy KernelVerified
    /// set verdict-identical to eager.
    #[test]
    fn test_no_confusion_aux_excluded_from_lazy_index() {
        let dir = tempfile::tempdir().expect("tempdir");
        // Two ordinary defs/theorems (served) and two noConfusion auxiliaries
        // (excluded), all written as plain definitional kinds in their shards.
        let r_ok_def = one_def_shard_reader(dir.path(), "Foo.bar", DeclKind::Definition);
        let r_ok_thm = one_def_shard_reader(dir.path(), "Foo.baz", DeclKind::Theorem);
        let r_nc = one_def_shard_reader(dir.path(), "Foo.noConfusion", DeclKind::Definition);
        let r_nct = one_def_shard_reader(dir.path(), "Foo.noConfusionType", DeclKind::Definition);
        let mut src = ShardConstantSource::from_readers(vec![r_ok_def, r_ok_thm, r_nc, r_nct]);
        src.mark_all_verified();

        // Ordinary constants ARE servable.
        assert!(src.contains(&Name::from_string("Foo.bar")));
        assert!(src.contains(&Name::from_string("Foo.baz")));
        assert!(src.get(&Name::from_string("Foo.bar")).is_some());

        // The noConfusion auxiliaries are NEITHER indexed NOR served — they fall
        // through to the eager regeneration path.
        assert!(
            !src.contains(&Name::from_string("Foo.noConfusion")),
            "noConfusion must not be lazily indexed"
        );
        assert!(
            !src.contains(&Name::from_string("Foo.noConfusionType")),
            "noConfusionType must not be lazily indexed"
        );
        assert!(src.get(&Name::from_string("Foo.noConfusion")).is_none());
        assert!(src.get(&Name::from_string("Foo.noConfusionType")).is_none());

        // Exactly the two ordinary constants are servable (the two aux excluded).
        assert_eq!(
            src.servable_len(),
            2,
            "only the 2 non-aux constants are indexed"
        );
    }

    /// `is_kernel_regenerated_aux_name` matches the LAST dotted component only, so
    /// it never mis-classifies a user constant that merely contains the substring
    /// (e.g. `My.noConfusionHelper`) nor a bare unqualified name.
    #[test]
    fn test_is_kernel_regenerated_aux_name_matches_last_component_only() {
        assert!(is_kernel_regenerated_aux_name("Nat.noConfusion"));
        assert!(is_kernel_regenerated_aux_name(
            "Lean.MonadBacktrack.noConfusionType"
        ));
        assert!(is_kernel_regenerated_aux_name("noConfusion"));
        // Not the last component / not an exact match: served normally.
        assert!(!is_kernel_regenerated_aux_name("Foo.noConfusion.helper"));
        assert!(!is_kernel_regenerated_aux_name("My.noConfusionHelper"));
        assert!(!is_kernel_regenerated_aux_name("Foo.bar"));
        assert!(!is_kernel_regenerated_aux_name("noConfusionTypeOf"));
    }
}
