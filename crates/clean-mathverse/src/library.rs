// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `MathverseLibrary` — the concrete implementation of [`MathverseSearch`].
//!
//! Ties together shards, discrimination tree, bloom filter, sorted index,
//! trust policy, and knowledge graph into a single searchable library.

use std::collections::VecDeque;

use clean_kernel::expr::{Expr, ExprKind, Literal};
use clean_kernel::flat::{reconstruct_expr, FlatDb, FlatExpr, FlatLevel};
use clean_kernel::{Declaration, Environment, Name};
use hashbrown::HashMap;

use crate::discrim::DiscrimTree;
use crate::embedding::{build_search_index, BM25Index};
use crate::error::{MathverseError, MathverseResult};
use crate::graph_alpha::{
    ConceptEdge, ConceptNode, ConjectureSource, ConjectureStatus, EquivConfidence,
};
use crate::nn_alpha::NNVerificationCert;
use crate::provenance::{add_provenance, ProvenanceRecord, ProvenanceSidecar};
use crate::search::{
    DependencyIterator, DomainQuery, EdgeFilter, MathverseSearch, SearchResult, SubGraph,
};
use crate::shard::ShardReader;
use crate::trust::policy::TrustPolicy;
use crate::types::{
    AxiomProfile, ConjectureIdx, ConstantIdx, ContentDomain, ExprIdx, ImportConfidence,
    MathverseConstantHeader, SourceSystem, NO_VALUE,
};
use crate::verify::{MathverseVerify, ProofFormat, VerificationResult, VerificationStatus};

/// Lazily-built inverse of the forward dependency adjacency.
///
/// `adj[b]` is the sorted, deduplicated list of constants that *directly*
/// depend on `b` — i.e. the reverse of [`MathverseLibrary::deps`]. Built once
/// on the first reverse-dependency query and cached (the inversion is O(V + E)
/// over the whole corpus). Invalidated whenever the forward adjacency's
/// `(node_count, edge_count)` fingerprint diverges, so a fresh `build_deps` or
/// `add_dependency` transparently triggers a rebuild without any dirty-flag
/// plumbing at the call sites.
#[derive(Default)]
struct ReverseDepsCache {
    /// `adj[b]` = sorted, deduped constants that directly depend on `b`.
    adj: Vec<Vec<ConstantIdx>>,
    /// `(forward node_count, forward edge_count)` when `adj` was built;
    /// `None` until the first build.
    fingerprint: Option<(usize, usize)>,
}

/// The Mathverse Library: unified searchable index over all loaded shards.
///
/// Merges constant headers, string tables, expression arenas, and level pools
/// from multiple shards into a single global namespace with remapped indices.
/// Provides all five search modes defined by [`MathverseSearch`].
pub struct MathverseLibrary {
    /// Merged constant table (all shards, globally indexed).
    constants: Vec<MathverseConstantHeader>,
    /// Merged string table.
    strings: Vec<String>,
    /// Merged expression arena.
    exprs: Vec<FlatExpr>,
    /// Merged level arena.
    levels: Vec<FlatLevel>,
    /// Merged per-constant level-lists table (all shards, index-remapped).
    ///
    /// Layout (matching the shard format): `[count, level_idx_0, ..., level_idx_N, count, ...]`.
    /// A `Const` `FlatExpr` references a list by the offset of its `count` entry
    /// (`levels_list_idx`); each `level_idx_k` is an index into [`Self::levels`].
    /// Merging remaps both: the per-`Const` `levels_list_idx` is offset by this
    /// table's base (see [`remap_expr`]), and each `level_idx_k` is offset by the
    /// level-pool base. Without this table, universe-polymorphic constants would
    /// reconstruct their level arguments from an empty list and mistype-check.
    level_lists: Vec<u32>,
    /// Name -> global ConstantIdx lookup (O(1)).
    name_to_idx: HashMap<String, ConstantIdx>,
    /// Type-directed discrimination tree across all loaded constants.
    discrim_tree: DiscrimTree,
    /// Active trust policy for filtering results.
    trust_policy: TrustPolicy,
    /// Adjacency list for dependency walking (from -> [to]).
    deps: Vec<Vec<ConstantIdx>>,
    /// Lazily-built, cached inverse of [`Self::deps`] (to -> [from]). Powers
    /// reverse-dependency search ("which loaded declarations use X"). Behind a
    /// `RefCell` so it builds on first query without a `&mut self`; the library
    /// is thread-local (not `Sync`-shared), mirroring [`Self::bm25_index`].
    reverse_deps_cache: std::cell::RefCell<ReverseDepsCache>,
    /// Equivalence index: constant -> [(confidence, equivalent constant)].
    equivalences: Vec<Vec<(EquivConfidence, ConstantIdx)>>,
    /// Knowledge graph nodes.
    graph_nodes: Vec<ConceptNode>,
    /// Knowledge graph edges: (source_node_idx, target_node_idx, edge).
    graph_edges: Vec<(usize, usize, ConceptEdge)>,
    /// BM25-based semantic search index over constant names and types.
    /// Behind a `RefCell` so it can be rebuilt lazily on first query (see
    /// `search_dirty`); the library is thread-local (not `Sync`-shared).
    bm25_index: std::cell::RefCell<BM25Index>,
    /// Set by `load_shard`, cleared on first semantic search. Lets the BM25
    /// index rebuild ONCE after a batch of shard loads instead of once per shard
    /// (O(N) not O(N^2)), with no caller changes.
    search_dirty: std::cell::Cell<bool>,
    /// Provenance sidecar for detailed import metadata.
    provenance: ProvenanceSidecar,
    /// Conjecture node indices in the knowledge graph (for submit_conjecture).
    conjectures: Vec<usize>,
    /// Reverse lookup: type expression index -> constant that proves it.
    type_to_constant: HashMap<ExprIdx, ConstantIdx>,
    /// Lazy `string -> first-occurrence index` map for [`intern_string`], so a
    /// premise-selection query resolving its goal's constant names costs O(1) per
    /// name instead of an O(corpus) linear scan of `strings`. Rebuilt (first
    /// occurrence wins, matching the old scan) whenever `strings.len()` diverges
    /// from [`string_idx_built_len`] — `strings` is append-only, so that length
    /// check alone detects every bulk shard merge with no dirty-flag plumbing.
    ///
    /// [`intern_string`]: Self::intern_string
    /// [`string_idx_built_len`]: Self::string_idx_built_len
    string_to_idx: HashMap<String, u32>,
    /// `strings.len()` when `string_to_idx` was last (re)built.
    string_idx_built_len: usize,
}

impl MathverseLibrary {
    /// Create an empty library with the given trust policy.
    pub fn new(trust_policy: TrustPolicy) -> Self {
        Self {
            constants: Vec::new(),
            strings: Vec::new(),
            exprs: Vec::new(),
            levels: Vec::new(),
            level_lists: Vec::new(),
            name_to_idx: HashMap::new(),
            discrim_tree: DiscrimTree::new(),
            trust_policy,
            deps: Vec::new(),
            reverse_deps_cache: std::cell::RefCell::new(ReverseDepsCache::default()),
            equivalences: Vec::new(),
            graph_nodes: Vec::new(),
            graph_edges: Vec::new(),
            bm25_index: std::cell::RefCell::new(BM25Index::new()),
            search_dirty: std::cell::Cell::new(false),
            provenance: ProvenanceSidecar::new(),
            conjectures: Vec::new(),
            type_to_constant: HashMap::new(),
            string_to_idx: HashMap::new(),
            string_idx_built_len: 0,
        }
    }

    /// Load a shard into the library, merging its tables into the global namespace.
    ///
    /// All shard-local indices (string, expr, level, constant) are remapped to
    /// global indices. Returns the number of constants added. Rebuilds the
    /// dependency adjacency afterward, so a single shard is immediately queryable.
    ///
    /// For **bulk** multi-shard loads, prefer [`load_shard_deferred`] in the loop
    /// plus one trailing [`build_deps`]: `build_deps` is an O(N) full rebuild, so
    /// calling it per shard makes a multi-shard load O(shards × N). One trailing
    /// call yields a byte-identical `deps` (a per-shard incremental pass would be
    /// *wrong* — it would miss forward cross-shard references resolved by a later
    /// shard).
    ///
    /// [`load_shard_deferred`]: Self::load_shard_deferred
    /// [`build_deps`]: Self::build_deps
    pub fn load_shard(&mut self, reader: &ShardReader) -> MathverseResult<usize> {
        let added = self.load_shard_deferred(reader)?;
        self.build_deps();
        Ok(added)
    }

    /// Merge a shard into the library **without** rebuilding the dependency
    /// adjacency (the O(N) `build_deps` walk). The caller MUST call
    /// [`build_deps`](Self::build_deps) once after the final shard before any
    /// `deps()` / dependency-graph query, or the adjacency will be stale.
    /// Returns the number of constants added.
    pub fn load_shard_deferred(&mut self, reader: &ShardReader) -> MathverseResult<usize> {
        let string_base = self.strings.len() as u32;
        let expr_base = self.exprs.len() as u32;
        let level_base = self.levels.len() as u32;
        let level_lists_base = self.level_lists.len() as u32;

        // Pre-size every arena/index to the exact count this shard contributes,
        // so the merge push-loops below never reallocate mid-load. Capacity-only:
        // the resulting contents and indices are byte-identical to incremental growth.
        self.levels.reserve(reader.levels.len());
        self.level_lists.reserve(reader.level_lists.len());
        self.exprs.reserve(reader.exprs.len());
        self.constants.reserve(reader.constants.len());
        self.deps.reserve(reader.constants.len());
        self.equivalences.reserve(reader.constants.len());
        self.name_to_idx.reserve(reader.constants.len());

        // Merge string table.
        self.strings.extend_from_slice(&reader.strings);

        // Merge level pool with remapped indices.
        for (i, level) in reader.levels.iter().enumerate() {
            let remapped = remap_level(level, i as u32, level_base, string_base)?;
            self.levels.push(remapped);
        }

        // Merge the per-constant level-lists table with remapped indices.
        //
        // The table is a flat run of variable-length records, each
        // `[count, level_idx_0, ..., level_idx_{count-1}]`. A `Const` expr
        // references a record by the offset of its `count` slot. We walk the
        // records structurally: the `count` slots pass through unchanged, while
        // each `level_idx_k` is an index into the shard's level pool and is
        // therefore offset by `level_base` (the same offset applied to the level
        // pool merge above). The whole record block is appended after the
        // existing global table, so a `Const`'s `levels_list_idx` is shifted by
        // `level_lists_base` in `remap_expr` to land on the relocated `count`.
        merge_level_lists(&reader.level_lists, level_base, &mut self.level_lists)?;

        // Merge expression arena with remapped indices.
        for (i, expr) in reader.exprs.iter().enumerate() {
            let remapped = remap_expr(
                expr,
                i as u32,
                expr_base,
                level_base,
                level_lists_base,
                string_base,
            )?;
            self.exprs.push(remapped);
        }

        // Merge constant headers with remapped indices and build name index.
        let mut added = 0;
        for constant in &reader.constants {
            let global_idx = self.constants.len() as ConstantIdx;
            let remapped = MathverseConstantHeader {
                name_idx: constant.name_idx + string_base,
                type_idx: remap_idx(constant.type_idx, expr_base),
                value_idx: remap_idx(constant.value_idx, expr_base),
                source_system: constant.source_system,
                import_confidence: constant.import_confidence,
                content_domain: constant.content_domain,
                decl_kind: constant.decl_kind,
                axiom_profile: constant.axiom_profile,
                sidecar_digest: constant.sidecar_digest,
                provenance_idx: constant.provenance_idx,
                level_params_start: if constant.level_params_count > 0 {
                    constant.level_params_start + string_base
                } else {
                    0
                },
                level_params_count: constant.level_params_count,
                _pad2: remap_inductive_metadata(constant, string_base),
            };

            let name_idx = remapped.name_idx as usize;
            if name_idx < self.strings.len() {
                let name = self.strings[name_idx].clone();
                self.name_to_idx.insert(name, global_idx);
            }

            // Fold the discrim-tree / type_to_constant inserts into this same
            // merge pass (the `exprs` arena is fully merged above), instead of a
            // second O(N) walk over the just-added constants.
            let type_idx = remapped.type_idx;
            self.constants.push(remapped);
            self.deps.push(Vec::new());
            self.equivalences.push(Vec::new());
            if (type_idx as usize) < self.exprs.len() {
                self.discrim_tree.insert(&self.exprs, type_idx, global_idx);
            }
            self.type_to_constant.insert(type_idx, global_idx);
            added += 1;
        }

        // Dependency adjacency is rebuilt by the caller (via `load_shard`'s
        // wrapper, or one trailing `build_deps` after a bulk `load_shard_deferred`
        // loop) — not here, so a multi-shard load stays O(N) instead of O(N²).

        // Defer the BM25 rebuild: mark dirty and rebuild ONCE on first search
        // (lazy), not once per shard. See `ensure_search_index`.
        self.search_dirty.set(true);

        Ok(added)
    }

    /// Rebuild the discrimination tree from scratch (e.g. after multiple loads).
    pub fn build_indices(&mut self) {
        let mut tree = DiscrimTree::new();
        for (i, constant) in self.constants.iter().enumerate() {
            let type_idx = constant.type_idx;
            if (type_idx as usize) < self.exprs.len() {
                tree.insert(&self.exprs, type_idx, i as ConstantIdx);
            }
        }
        self.discrim_tree = tree;
    }

    /// Rebuild the BM25 semantic search index from all loaded constants.
    pub fn build_search_index(&mut self) {
        *self.bm25_index.borrow_mut() =
            build_search_index(&self.constants, &self.strings, &self.exprs);
        self.search_dirty.set(false);
    }

    /// Lazily (re)build the BM25 index iff a shard load marked it dirty.
    ///
    /// Called by every semantic-search query so callers never rebuild indices
    /// manually (batteries-on). The rebuild runs ONCE on the first query after a
    /// batch of `load_shard`s, rather than once per shard — turning the bulk-load
    /// BM25 cost from O(N^2) into O(N). Result is identical to eager rebuild.
    fn ensure_search_index(&self) {
        if self.search_dirty.get() {
            *self.bm25_index.borrow_mut() =
                build_search_index(&self.constants, &self.strings, &self.exprs);
            self.search_dirty.set(false);
        }
    }

    /// Explain a semantic search: returns per-result token-level score breakdowns.
    pub fn search_explain(
        &self,
        query: &str,
        max_results: usize,
    ) -> Vec<crate::embedding::SearchExplanation> {
        self.ensure_search_index();
        self.bm25_index.borrow().search_explain(query, max_results)
    }

    /// Look up a constant's global index by name. Returns `None` if the name
    /// is not in the library or is hidden by the trust policy.
    #[inline]
    pub fn lookup_constant_idx(&self, name: &str) -> Option<ConstantIdx> {
        let &idx = self.name_to_idx.get(name)?;
        let header = self.constants.get(idx as usize)?;
        if self.trust_policy.is_visible(header) {
            Some(idx)
        } else {
            None
        }
    }

    /// Total number of constants in the library.
    #[inline]
    pub fn constant_count(&self) -> usize {
        self.constants.len()
    }

    /// Upgrade the in-memory `import_confidence` of every constant named in the
    /// kernel-verified manifest to [`ImportConfidence::KernelVerified`] —
    /// reflecting that Clean's own kernel re-verified it (see
    /// `verify::incremental::verify_corpus_incremental` and the
    /// `kernel-verified.json` sidecar emitted by `verify-kernel --corpus
    /// --emit-verified`). Names absent from this library are skipped. Returns the
    /// number of constants whose confidence was raised. This is how the
    /// trust-gated `mathverse use` tactic comes to treat Clean-re-verified
    /// constants at the top confidence tier.
    ///
    /// This pass is **in-memory only** — it does not touch the shard files on
    /// disk, so a freshly reloaded library would once again read
    /// `KernelVerified = 0` from the bytes. To make the stamp survive into the
    /// shard bytes (the WS5 goal), use [`stamp_shard_dir_kernel_verified`],
    /// which rewrites each shard file with the verified `import_confidence`
    /// byte set.
    pub fn apply_kernel_verified_manifest(
        &mut self,
        manifest: &crate::verify::kernel_verified_manifest::KernelVerifiedManifest,
    ) -> usize {
        let target = ImportConfidence::KernelVerified as u8;
        let mut upgraded = 0usize;
        for name in &manifest.kernel_verified_names {
            if let Some(&idx) = self.name_to_idx.get(name) {
                let conf = &mut self.constants[idx as usize].import_confidence;
                if *conf != target {
                    *conf = target;
                    upgraded += 1;
                }
            }
        }
        upgraded
    }

    /// Get a constant header by global index.
    #[inline]
    pub fn get_constant(&self, idx: ConstantIdx) -> Option<&MathverseConstantHeader> {
        self.constants.get(idx as usize)
    }

    /// Get the name of a constant by global index.
    pub fn get_name(&self, idx: ConstantIdx) -> Option<&str> {
        let header = self.constants.get(idx as usize)?;
        self.strings
            .get(header.name_idx as usize)
            .map(|s| s.as_str())
    }

    /// Record that `from` depends on `to`.
    pub fn add_dependency(&mut self, from: ConstantIdx, to: ConstantIdx) {
        if let Some(adj) = self.deps.get_mut(from as usize) {
            adj.push(to);
        }
    }

    /// Record an equivalence between two constants.
    pub fn add_equivalence(&mut self, a: ConstantIdx, b: ConstantIdx, confidence: EquivConfidence) {
        if let Some(list) = self.equivalences.get_mut(a as usize) {
            list.push((confidence.clone(), b));
        }
        if let Some(list) = self.equivalences.get_mut(b as usize) {
            list.push((confidence, a));
        }
    }

    /// Add a node to the knowledge graph. Returns the node index.
    pub fn add_graph_node(&mut self, node: ConceptNode) -> usize {
        let idx = self.graph_nodes.len();
        self.graph_nodes.push(node);
        idx
    }

    /// Add an edge to the knowledge graph.
    pub fn add_graph_edge(&mut self, from: usize, to: usize, edge: ConceptEdge) {
        self.graph_edges.push((from, to, edge));
    }

    /// Access the provenance sidecar.
    pub fn provenance(&self) -> &ProvenanceSidecar {
        &self.provenance
    }

    /// Add a provenance record for a constant, updating its header's
    /// `provenance_idx` and `sidecar_digest`.
    pub fn add_provenance_record(&mut self, idx: ConstantIdx, record: ProvenanceRecord) {
        let (prov_idx, digest) = add_provenance(&mut self.provenance, record);
        if let Some(header) = self.constants.get_mut(idx as usize) {
            header.provenance_idx = prov_idx;
            header.sidecar_digest = digest;
        }
    }

    /// Build dependency adjacency lists from expression analysis.
    ///
    /// For each constant, walks its type and value expressions to find all
    /// referenced constants (by name_idx), then resolves to `ConstantIdx`.
    /// Self-references are excluded and results are deduplicated.
    pub fn build_deps(&mut self) {
        let num = self.constants.len();

        // Disambiguation index: `(name, source_system) -> ConstantIdx`.
        //
        // A `Const` reference in a constant's term carries only the dependency's
        // NAME-string (no resolved index — see `extract_const_refs_into`), so
        // resolving via the global `name_to_idx` map maps every homonym to a
        // single winner: a Lean4 term's bare `C` / `z` / `int` would resolve to
        // whatever system's `C` was loaded last, fabricating cross-system edges.
        // Term-level dependencies are always intra-system, and within one system
        // fully-qualified names are unique, so keying by `(name, source_system)`
        // resolves each dep to the homonym in the REFERENCING constant's own
        // system. A dep with no same-system definition is dropped rather than
        // mapped to a foreign-system homonym. Keys borrow `self.strings`, so no
        // name is cloned.
        let mut by_name_system: hashbrown::HashMap<(&str, u8), ConstantIdx> =
            hashbrown::HashMap::with_capacity(num);
        for (idx, header) in self.constants.iter().enumerate() {
            if let Some(name) = self.strings.get(header.name_idx as usize) {
                by_name_system.insert((name.as_str(), header.source_system), idx as ConstantIdx);
            }
        }

        // Build into a local adjacency table so the immutable borrow held by
        // `by_name_system` (into `self.strings` / `self.constants`) does not clash
        // with writing `self.deps` (a disjoint field) at the end.
        let mut deps = vec![Vec::new(); num];

        // Reused scratch across the whole pass — the worklist, visited set, and
        // the transient name-index buffer are cleared per constant rather than
        // reallocated, so this single O(N) walk allocates them once instead of
        // ~3 short-lived allocations per constant. (`resolved` is the owned
        // output for `deps[i]`, so it is allocated per constant by design.)
        let mut dep_name_indices: Vec<u32> = Vec::new();
        let mut stack: Vec<u32> = Vec::new();
        let mut visited: hashbrown::HashSet<u32> = hashbrown::HashSet::new();

        for (i, dep_slot) in deps.iter_mut().enumerate() {
            let type_idx = self.constants[i].type_idx;
            let value_idx = self.constants[i].value_idx;
            let system_i = self.constants[i].source_system;
            dep_name_indices.clear();

            // Extract from type expression.
            extract_const_refs_into(
                &self.exprs,
                type_idx,
                &mut dep_name_indices,
                &mut stack,
                &mut visited,
            );

            // Extract from value expression (if not axiomatized).
            if value_idx != NO_VALUE {
                extract_const_refs_into(
                    &self.exprs,
                    value_idx,
                    &mut dep_name_indices,
                    &mut stack,
                    &mut visited,
                );
            }

            // Resolve each dependency name within the referencing constant's OWN
            // source system; drop a name with no same-system definition rather
            // than fabricate a cross-system edge.
            let mut resolved = Vec::new();
            for &name_idx in &dep_name_indices {
                if let Some(name) = self.strings.get(name_idx as usize) {
                    if let Some(&const_idx) = by_name_system.get(&(name.as_str(), system_i)) {
                        if const_idx != i as u32 {
                            // Skip self-references.
                            resolved.push(const_idx);
                        }
                    }
                }
            }
            resolved.sort_unstable();
            resolved.dedup();
            *dep_slot = resolved;
        }

        self.deps = deps;
    }

    /// Access the dependency adjacency list (for testing / iteration).
    #[inline]
    /// Access the merged expression arena (for shard reconstruction).
    pub fn exprs(&self) -> &[FlatExpr] {
        &self.exprs
    }

    /// Access the merged level pool (for shard reconstruction).
    pub fn levels(&self) -> &[FlatLevel] {
        &self.levels
    }

    /// Access the merged per-constant level-lists table (for shard reconstruction).
    ///
    /// Required by `reconstruct_from_shard_with_level_lists` to rebuild the
    /// universe arguments of `Const` references; see [`Self::level_lists`].
    pub fn level_lists(&self) -> &[u32] {
        &self.level_lists
    }

    /// The environment-free Tier-1.5 *rewrite-canonical* digest (`blake3:<hex>`)
    /// of constant `idx`'s type — the corpus-scale "same object, different form"
    /// key the graduation novelty gate stores in the `.mvix` semantic table.
    ///
    /// Computed by reconstructing the constant's type sub-DAG from the merged
    /// arena (the SAME `reconstruct_single_expr` path the `.mvix` builder uses
    /// per shard, so the digest matches byte-for-byte regardless of index space)
    /// and hashing its commutative-canonical form
    /// ([`clean_cake::identity::structural_rewrite_digest`]). The digest collapses
    /// commutative-operand reorderings (`a + b` / `b + a`, `P ∧ Q` / `Q ∧ P`) so
    /// two differently-stated-but-equivalent statements share a key. A match is a
    /// *candidate* (a search/dedup signal), never a soundness claim.
    ///
    /// Returns `None` when `idx` is unknown or the type sub-DAG cannot be
    /// reconstructed (name-only / mode-extension exprs) — exactly the constants
    /// the `.mvix` builder skips, so a `None` query here can never spuriously hit.
    #[must_use]
    pub fn structural_rewrite_digest_of(&self, idx: ConstantIdx) -> Option<String> {
        let header = self.constants.get(idx as usize)?;
        let expr = crate::shard_reconstruct::reconstruct_single_subdag(
            &self.exprs,
            &self.levels,
            &self.strings,
            &self.level_lists,
            header.type_idx,
        )
        .ok()?;
        Some(clean_cake::identity::structural_rewrite_digest(&expr))
    }

    /// Every loaded constant whose type is structurally equal-up-to-rewrite to
    /// `anchor`'s, excluding `anchor` itself, ranked by import-confidence then
    /// name and capped at `limit`.
    ///
    /// This is the exhaustive *local* equivalence class: it computes
    /// [`Self::structural_rewrite_digest_of`] for the anchor, then scans every
    /// visible loaded constant for the same digest. O(loaded constants) — for
    /// corpus scale, prefer the precomputed `.mvix` semantic lookup
    /// ([`crate::graduate::BaselineIndex::lookup_semantic`]), which answers the
    /// representative in microseconds without reconstructing the whole corpus.
    /// Returns an empty vector if the anchor is unknown or its type is
    /// unreconstructable.
    #[must_use]
    pub fn structural_equivalents_of(&self, anchor: ConstantIdx, limit: usize) -> Vec<ConstantIdx> {
        let Some(target) = self.structural_rewrite_digest_of(anchor) else {
            return Vec::new();
        };
        let mut hits: Vec<ConstantIdx> = Vec::new();
        for idx in 0..self.constants.len() as ConstantIdx {
            if idx == anchor {
                continue;
            }
            let Some(header) = self.constants.get(idx as usize) else {
                continue;
            };
            if !self.trust_policy.is_visible(header) {
                continue;
            }
            if self.structural_rewrite_digest_of(idx).as_deref() == Some(target.as_str()) {
                hits.push(idx);
            }
        }
        hits.sort_by(|&a, &b| {
            let ca = self.constants.get(a as usize).map(|h| h.import_confidence);
            let cb = self.constants.get(b as usize).map(|h| h.import_confidence);
            ca.cmp(&cb).then_with(|| {
                self.get_name(a)
                    .unwrap_or("")
                    .cmp(self.get_name(b).unwrap_or(""))
            })
        });
        hits.truncate(limit);
        hits
    }

    /// Wrap the merged arenas as a single in-memory [`ShardReader`].
    ///
    /// Because `load_shard` has already remapped every shard's
    /// strings/levels/exprs/level_lists into one mutually-consistent index
    /// space, the merged corpus is exactly one big shard. The global corpus
    /// verifier uses this view so it can reuse the per-shard reconstruction and
    /// (sibling-scanning) inductive-family replay logic unchanged, with
    /// cross-shard references now in-arena and therefore resolvable.
    pub(crate) fn as_merged_reader(&self) -> ShardReader {
        ShardReader::from_merged_parts(
            self.strings.clone(),
            self.levels.clone(),
            self.exprs.clone(),
            self.constants.clone(),
            self.level_lists.clone(),
        )
    }

    /// Access the merged string table (for shard reconstruction).
    pub fn strings(&self) -> &[String] {
        &self.strings
    }

    pub fn deps(&self) -> &[Vec<ConstantIdx>] {
        &self.deps
    }

    /// Forward-adjacency fingerprint used to detect a stale reverse cache.
    fn deps_fingerprint(&self) -> (usize, usize) {
        let edges = self.deps.iter().map(Vec::len).sum();
        (self.deps.len(), edges)
    }

    /// Ensure the cached reverse adjacency reflects the current forward `deps`.
    ///
    /// Rebuilds in O(V + E) when the forward fingerprint has changed (first
    /// query, a fresh `build_deps`, or any `add_dependency`); otherwise O(1).
    fn ensure_reverse_deps(&self) {
        let fp = self.deps_fingerprint();
        if self.reverse_deps_cache.borrow().fingerprint == Some(fp) {
            return;
        }
        let mut adj: Vec<Vec<ConstantIdx>> = vec![Vec::new(); self.deps.len()];
        for (from, tos) in self.deps.iter().enumerate() {
            for &to in tos {
                if let Some(slot) = adj.get_mut(to as usize) {
                    slot.push(from as ConstantIdx);
                }
            }
        }
        for users in &mut adj {
            users.sort_unstable();
            users.dedup();
        }
        let mut cache = self.reverse_deps_cache.borrow_mut();
        cache.adj = adj;
        cache.fingerprint = Some(fp);
    }

    /// In-degree of a constant: the number of distinct constants that
    /// *directly* depend on it. A high in-degree marks a widely-reused /
    /// central declaration, and is the impact signal used to rank
    /// reverse-dependency hits.
    #[must_use]
    pub fn reverse_in_degree(&self, idx: ConstantIdx) -> usize {
        self.ensure_reverse_deps();
        self.reverse_deps_cache
            .borrow()
            .adj
            .get(idx as usize)
            .map_or(0, Vec::len)
    }

    /// Reverse-dependency walk: the constants that (transitively) depend on
    /// `root` — i.e. what is impacted if `root` changes or is retired.
    ///
    /// Mirrors the forward `deps()` BFS but over the lazily-built reverse
    /// adjacency. `transitive = false` returns only direct users (one hop);
    /// otherwise the walk is bounded by `depth`. `limit` caps the total hits so
    /// a hub declaration cannot explode the traversal. The root is excluded.
    ///
    /// Hits are ranked by their own in-degree (descending) so the most-reused /
    /// highest-impact users surface first; ties break by shallower depth, then
    /// by index. Returns `(constant_idx, depth)` pairs.
    #[must_use]
    pub fn reverse_deps_bounded(
        &self,
        root: ConstantIdx,
        transitive: bool,
        depth: usize,
        limit: usize,
    ) -> Vec<(ConstantIdx, u32)> {
        self.ensure_reverse_deps();
        let cache = self.reverse_deps_cache.borrow();
        let rev = &cache.adj;

        let mut visited: hashbrown::HashSet<ConstantIdx> = hashbrown::HashSet::new();
        let mut queue: VecDeque<(ConstantIdx, u32)> = VecDeque::new();
        let mut out: Vec<(ConstantIdx, u32)> = Vec::new();

        visited.insert(root);
        if let Some(direct) = rev.get(root as usize) {
            for &u in direct {
                queue.push_back((u, 1));
            }
        }

        while let Some((idx, cur_depth)) = queue.pop_front() {
            if !visited.insert(idx) {
                continue;
            }
            out.push((idx, cur_depth));
            if out.len() >= limit {
                break;
            }
            if !transitive || cur_depth as usize >= depth {
                continue;
            }
            if let Some(next) = rev.get(idx as usize) {
                for &n in next {
                    if !visited.contains(&n) {
                        queue.push_back((n, cur_depth + 1));
                    }
                }
            }
        }

        // Rank by impact: in-degree desc, then shallower depth, then index.
        out.sort_by(|&(a, da), &(b, db)| {
            let ia = rev.get(a as usize).map_or(0, Vec::len);
            let ib = rev.get(b as usize).map_or(0, Vec::len);
            ib.cmp(&ia).then(da.cmp(&db)).then(a.cmp(&b))
        });
        out
    }

    /// Resolve a declaration name for a browse query, tolerant of the
    /// exact-name mismatches that make `deps` / `info` / `uses` hard to drive
    /// by hand (so an agent can pipe a `search` / `find` hit straight in).
    ///
    /// Tries, in order: exact name (O(1)), then a single corpus scan for a
    /// case-insensitive exact match, falling back to the first case-insensitive
    /// substring match (corpus-index order). Trust-policy visibility is honoured
    /// at every tier. Returns the resolved global index, or `None` if nothing
    /// matches.
    #[must_use]
    pub fn resolve_name_loose(&self, query: &str) -> Option<ConstantIdx> {
        if let Some(idx) = self.lookup_constant_idx(query) {
            return Some(idx);
        }
        let q = query.to_lowercase();
        let mut substring: Option<ConstantIdx> = None;
        for idx in 0..self.constants.len() as ConstantIdx {
            let Some(header) = self.constants.get(idx as usize) else {
                continue;
            };
            if !self.trust_policy.is_visible(header) {
                continue;
            }
            let Some(name) = self.strings.get(header.name_idx as usize) else {
                continue;
            };
            let lower = name.to_lowercase();
            if lower == q {
                // Case-insensitive exact beats any substring hit.
                return Some(idx);
            }
            if substring.is_none() && lower.contains(&q) {
                substring = Some(idx);
            }
        }
        substring
    }

    /// Convert a kernel `Expr` into the library's expression arena for
    /// discrimination tree queries.
    ///
    /// Walks the kernel expression tree and builds corresponding `FlatExpr`
    /// nodes in the library's merged expression arena, mapping `Const` names
    /// through the library's string table (or adding new entries if the name
    /// is not yet present).
    ///
    /// Returns the root `ExprIdx` suitable for passing to
    /// [`MathverseSearch::search_type`] or [`search_for_goal`].
    ///
    /// This method is the key enabler for discrimination-tree-based premise
    /// selection from kernel proof goals (issue #3412).
    pub fn add_query_expr(&mut self, expr: &Expr) -> ExprIdx {
        self.add_query_expr_inner(expr)
    }

    /// Recursive inner implementation of `add_query_expr`.
    ///
    /// Uses the library's own string table for name resolution, so that
    /// the resulting `FlatExpr::const_ref` nodes carry the same `name_idx`
    /// values used in the discrimination tree's stored paths.
    fn add_query_expr_inner(&mut self, expr: &Expr) -> ExprIdx {
        match expr.kind() {
            ExprKind::BVar(n) => {
                let idx = self.exprs.len() as u32;
                self.exprs.push(FlatExpr::bvar(*n));
                idx
            }
            ExprKind::Sort(_level) => {
                // For discrimination tree matching, the exact universe level
                // doesn't matter -- all sorts match DiscrimKey::Sort.
                let level_idx = self.levels.len() as u32;
                self.levels.push(FlatLevel::zero());
                let idx = self.exprs.len() as u32;
                self.exprs.push(FlatExpr::sort(level_idx));
                idx
            }
            ExprKind::Const(name, _levels) => {
                let name_str = name.to_string();
                let name_idx = self.intern_string(&name_str);
                let idx = self.exprs.len() as u32;
                self.exprs.push(FlatExpr::const_ref(name_idx, u32::MAX));
                idx
            }
            ExprKind::App(f, a) => {
                let fn_idx = self.add_query_expr_inner(f);
                let arg_idx = self.add_query_expr_inner(a);
                let idx = self.exprs.len() as u32;
                self.exprs.push(FlatExpr::app(fn_idx, arg_idx));
                idx
            }
            ExprKind::Lam(_bi, ty, body) => {
                let ty_idx = self.add_query_expr_inner(ty);
                let body_idx = self.add_query_expr_inner(body);
                let idx = self.exprs.len() as u32;
                self.exprs.push(FlatExpr::lam(0, ty_idx, body_idx));
                idx
            }
            ExprKind::Pi(_bi, ty, body) => {
                let ty_idx = self.add_query_expr_inner(ty);
                let body_idx = self.add_query_expr_inner(body);
                let idx = self.exprs.len() as u32;
                self.exprs.push(FlatExpr::pi(0, ty_idx, body_idx));
                idx
            }
            ExprKind::Let(_, ty, val, body, _) => {
                let ty_idx = self.add_query_expr_inner(ty);
                let val_idx = self.add_query_expr_inner(val);
                let body_idx = self.add_query_expr_inner(body);
                let idx = self.exprs.len() as u32;
                self.exprs
                    .push(FlatExpr::let_expr(ty_idx, val_idx, body_idx));
                idx
            }
            ExprKind::Proj(name, field, e) => {
                let name_str = name.to_string();
                let name_idx = self.intern_string(&name_str);
                let expr_idx = self.add_query_expr_inner(e);
                let idx = self.exprs.len() as u32;
                self.exprs
                    .push(FlatExpr::proj(name_idx, *field as u16, expr_idx));
                idx
            }
            ExprKind::Lit(lit) => {
                let idx = self.exprs.len() as u32;
                match lit {
                    Literal::Nat(n) => {
                        let val = n.to_u64().unwrap_or(0);
                        self.exprs.push(FlatExpr::lit_nat(val));
                    }
                    Literal::String(s) => {
                        let str_idx = self.intern_string(s);
                        self.exprs.push(FlatExpr::lit_str(str_idx));
                    }
                }
                idx
            }
            ExprKind::FVar(fvar_id) => {
                let idx = self.exprs.len() as u32;
                self.exprs.push(FlatExpr::fvar(fvar_id.as_u64()));
                idx
            }
            ExprKind::MData(_, inner) => {
                // MData is transparent — recurse into inner expression.
                self.add_query_expr_inner(inner)
            }
            ExprKind::Squash(inner) => self.add_query_expr_inner(inner),
            // Unsupported expression kinds: encode as a wildcard-like
            // Sort(0) so the discrimination tree uses Star for matching.
            _ => {
                let level_idx = self.levels.len() as u32;
                self.levels.push(FlatLevel::zero());
                let idx = self.exprs.len() as u32;
                self.exprs.push(FlatExpr::sort(level_idx));
                idx
            }
        }
    }

    /// Intern a string in the library's string table, returning its index.
    ///
    /// If the string already exists, returns the existing index.
    /// Otherwise, appends it and returns the new index.
    fn intern_string(&mut self, s: &str) -> u32 {
        // `strings` is append-only, so a length mismatch means a bulk shard merge
        // (or another push site) grew it since the index was built — rebuild the
        // `string -> first-occurrence index` map lazily (once per load batch,
        // amortized over the many queries that follow) instead of the old
        // O(corpus) linear scan on every call.
        if self.string_idx_built_len != self.strings.len() {
            self.string_to_idx.clear();
            self.string_to_idx.reserve(self.strings.len());
            for (i, existing) in self.strings.iter().enumerate() {
                // First occurrence wins — identical to the old linear scan's
                // return value (the merged table carries cross-shard duplicates).
                self.string_to_idx
                    .entry(existing.clone())
                    .or_insert(i as u32);
            }
            self.string_idx_built_len = self.strings.len();
        }
        if let Some(&i) = self.string_to_idx.get(s) {
            return i;
        }
        let idx = self.strings.len() as u32;
        self.strings.push(s.to_string());
        self.string_to_idx.insert(s.to_string(), idx);
        self.string_idx_built_len = self.strings.len();
        idx
    }
}

// ---------------------------------------------------------------------------
// On-disk KernelVerified stamping (WS5)
// ---------------------------------------------------------------------------

/// Outcome of a destructive on-disk `KernelVerified` stamp over a shard dir.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ShardStampResult {
    /// Shard files that were read, stamped, and rewritten.
    pub shards_rewritten: usize,
    /// Total constant headers whose persisted `import_confidence` byte was
    /// raised to `KernelVerified` across all shards.
    pub constants_stamped: usize,
}

/// Destructively rewrite a single shard file so that every constant named in
/// `verified_names` carries [`ImportConfidence::KernelVerified`] in its
/// persisted header byte. Returns the number of headers raised in this shard.
///
/// The shard is read in full ([`ShardReader::from_file`], which checksum-checks
/// the bytes), copied verbatim into a [`crate::shard::ShardWriter`]
/// ([`crate::shard::ShardWriter::from_reader`] — no index remap, since a single
/// shard's arenas are self-consistent), the confidence bytes are flipped
/// ([`crate::shard::ShardWriter::stamp_kernel_verified`]), and the writer is
/// serialized back over `path`. The blake3 footer is recomputed by the writer,
/// so the rewritten file remains a valid, checksummed shard.
///
/// SOUNDNESS: `verified_names` must contain ONLY names whose value genuinely
/// passed Clean's kernel `check_type` — the caller obtains them from
/// [`crate::verify::incremental::verify_corpus_incremental`]'s
/// `kernel_verified_names`, never from heuristic confidence. This function does
/// not re-verify; it only persists a verdict the kernel already rendered.
///
/// # Errors
/// Returns an error if the shard cannot be read, decoded, or rewritten.
pub fn stamp_shard_file_kernel_verified(
    path: &std::path::Path,
    verified_names: &std::collections::HashSet<String>,
) -> MathverseResult<usize> {
    let reader = ShardReader::from_file(path)?;
    let mut writer = crate::shard::ShardWriter::from_reader(&reader);
    let stamped = writer.stamp_kernel_verified(verified_names);
    if stamped > 0 {
        writer.write_to_file(path)?;
    }
    Ok(stamped)
}

/// Destructively stamp every `.mathverse` shard under `shard_dir` so that the
/// constants in `manifest` carry `KernelVerified` in their persisted bytes.
///
/// This is the on-disk counterpart of
/// [`MathverseLibrary::apply_kernel_verified_manifest`]: it walks every shard
/// file, applies [`stamp_shard_file_kernel_verified`], and reports how many
/// shards were rewritten and how many headers were raised in total. After this
/// returns, a fresh load of the directory reads the stamps directly from the
/// shard bytes (stored `KernelVerified > 0`), with no sidecar required.
///
/// Names that appear in the manifest but not in any shard are silently skipped
/// (the manifest is keyed on global names that may span more shards than the
/// directory holds).
///
/// SOUNDNESS: the manifest's `kernel_verified_names` are exactly the constants
/// whose value passed the kernel during
/// [`crate::verify::incremental::verify_corpus_incremental`]; axioms,
/// axiom-fallbacks, and reconstruction failures are excluded upstream and are
/// therefore never stamped here.
///
/// # Errors
/// Returns an error if the directory cannot be scanned or any shard cannot be
/// read or rewritten.
pub fn stamp_shard_dir_kernel_verified(
    shard_dir: &std::path::Path,
    manifest: &crate::verify::kernel_verified_manifest::KernelVerifiedManifest,
) -> MathverseResult<ShardStampResult> {
    let verified: std::collections::HashSet<String> =
        manifest.kernel_verified_names.iter().cloned().collect();
    let files = crate::shard_verify::discover_mathverse_files(shard_dir);
    let mut result = ShardStampResult::default();
    for path in &files {
        let stamped = stamp_shard_file_kernel_verified(path, &verified)?;
        if stamped > 0 {
            result.shards_rewritten += 1;
            result.constants_stamped += stamped;
        }
    }
    Ok(result)
}

/// Count the constant *headers* under `shard_dir` whose name appears in
/// `names`.
///
/// Used by the release gate to compute the *expected* stored `KernelVerified`
/// count: a kernel-verified manifest may be a global verdict spanning more
/// shards than a given directory holds, so the release assertion intersects the
/// manifest names with the headers actually present on disk. This counts
/// headers (not distinct names) so it is directly comparable to
/// [`count_stored_kernel_verified`], which also counts headers — even if a name
/// recurs across shards, both sides count it the same number of times.
///
/// # Errors
/// Returns an error only if the directory itself cannot be scanned.
pub fn count_present_names(
    shard_dir: &std::path::Path,
    names: &[String],
) -> MathverseResult<usize> {
    let wanted: std::collections::HashSet<&str> = names.iter().map(String::as_str).collect();
    let files = crate::shard_verify::discover_mathverse_files(shard_dir);
    let mut count = 0usize;
    for path in &files {
        if let Ok(reader) = ShardReader::from_file(path) {
            for constant in &reader.constants {
                if let Some(name) = reader.strings.get(constant.name_idx as usize) {
                    if wanted.contains(name.as_str()) {
                        count += 1;
                    }
                }
            }
        }
    }
    Ok(count)
}

/// Count, across every `.mathverse` shard under `shard_dir`, how many constant
/// headers carry [`ImportConfidence::KernelVerified`] in their persisted bytes.
///
/// This reads the shards from disk (not an in-memory library), so it reflects
/// exactly what was stamped into the files — the number WS5 must drive above
/// zero. Shards that fail to read are skipped; their paths are returned so the
/// caller can surface them.
///
/// # Errors
/// Returns an error only if the directory itself cannot be scanned.
pub fn count_stored_kernel_verified(
    shard_dir: &std::path::Path,
) -> MathverseResult<(usize, Vec<String>)> {
    let target = ImportConfidence::KernelVerified as u8;
    let files = crate::shard_verify::discover_mathverse_files(shard_dir);
    let mut count = 0usize;
    let mut unreadable = Vec::new();
    for path in &files {
        match ShardReader::from_file(path) {
            Ok(reader) => {
                count += reader
                    .constants
                    .iter()
                    .filter(|c| c.import_confidence == target)
                    .count();
            }
            Err(_) => unreadable.push(path.display().to_string()),
        }
    }
    Ok((count, unreadable))
}

impl MathverseSearch for MathverseLibrary {
    fn lookup_name(&self, name: &str) -> Option<MathverseConstantHeader> {
        let &idx = self.name_to_idx.get(name)?;
        let header = self.constants.get(idx as usize)?;
        if self.trust_policy.is_visible(header) {
            Some(*header)
        } else {
            None
        }
    }

    fn search_type(
        &self,
        query_type: ExprIdx,
        max_results: usize,
    ) -> MathverseResult<Vec<SearchResult>> {
        let candidates = self
            .discrim_tree
            .search(&self.exprs, query_type, max_results * 2);
        let mut results = Vec::new();
        for idx in candidates {
            if results.len() >= max_results {
                break;
            }
            if let Some(header) = self.constants.get(idx as usize) {
                if self.trust_policy.is_visible(header) {
                    results.push(SearchResult {
                        constant_idx: idx,
                        header: *header,
                        score: 1.0,
                    });
                }
            }
        }
        Ok(results)
    }

    fn search_semantic(
        &self,
        query: &str,
        max_results: usize,
    ) -> MathverseResult<Vec<SearchResult>> {
        self.ensure_search_index();
        let hits = self.bm25_index.borrow().search(query, max_results * 2);
        let mut results = Vec::new();
        for (idx, score) in hits {
            if results.len() >= max_results {
                break;
            }
            if let Some(header) = self.constants.get(idx as usize) {
                if self.trust_policy.is_visible(header) {
                    results.push(SearchResult {
                        constant_idx: idx,
                        header: *header,
                        score,
                    });
                }
            }
        }
        Ok(results)
    }

    fn walk_deps(&self, constant: ConstantIdx) -> DependencyIterator {
        // Compute full transitive closure via BFS over the adjacency list,
        // then load all reachable constants into a pre-seeded DependencyIterator.
        let mut visited = hashbrown::HashSet::new();
        let mut queue = VecDeque::new();
        visited.insert(constant);
        queue.push_back(constant);

        // Collect transitive deps (excluding root).
        let mut transitive = Vec::new();
        while let Some(node) = queue.pop_front() {
            if let Some(deps) = self.deps.get(node as usize) {
                for &dep in deps {
                    if visited.insert(dep) {
                        transitive.push(dep);
                        queue.push_back(dep);
                    }
                }
            }
        }

        // Build iterator: root first, then all transitive deps.
        let mut iter = DependencyIterator::new(constant);
        for dep in transitive {
            iter.push(dep);
        }
        iter
    }

    fn find_equivalents(
        &self,
        constant: ConstantIdx,
    ) -> MathverseResult<Vec<(EquivConfidence, ConstantIdx)>> {
        Ok(self
            .equivalences
            .get(constant as usize)
            .cloned()
            .unwrap_or_default())
    }

    fn graph_query(
        &self,
        node: ConstantIdx,
        edge_filter: &EdgeFilter,
        depth: u32,
    ) -> MathverseResult<SubGraph> {
        let max_depth = edge_filter.max_depth.unwrap_or(depth);
        let node_idx = node as usize;

        if node_idx >= self.graph_nodes.len() {
            return Ok(SubGraph::default());
        }

        // BFS from the starting node.
        let mut visited = hashbrown::HashSet::new();
        let mut queue: VecDeque<(usize, u32)> = VecDeque::new();
        queue.push_back((node_idx, 0));
        visited.insert(node_idx);

        let mut result_nodes = Vec::new();
        let mut result_edges = Vec::new();

        // Map from original graph node index -> result node index.
        let mut node_map: HashMap<usize, usize> = HashMap::new();

        while let Some((current, current_depth)) = queue.pop_front() {
            // Add node to result if not already mapped.
            let result_idx = *node_map.entry(current).or_insert_with(|| {
                let idx = result_nodes.len();
                result_nodes.push(self.graph_nodes[current].clone());
                idx
            });

            if current_depth >= max_depth {
                continue;
            }

            // Traverse outgoing edges.
            for (from, to, edge) in &self.graph_edges {
                if *from != current {
                    continue;
                }
                // Apply edge filter.
                if let Some(ref allowed) = edge_filter.allowed_edges {
                    if !allowed.iter().any(|k| k.matches(edge)) {
                        continue;
                    }
                }

                let to_result_idx = *node_map.entry(*to).or_insert_with(|| {
                    let idx = result_nodes.len();
                    if *to < self.graph_nodes.len() {
                        result_nodes.push(self.graph_nodes[*to].clone());
                    }
                    idx
                });
                result_edges.push((result_idx, to_result_idx, edge.clone()));

                if visited.insert(*to) {
                    queue.push_back((*to, current_depth + 1));
                }
            }
        }

        Ok(SubGraph {
            nodes: result_nodes,
            edges: result_edges,
        })
    }

    fn search_domain(
        &self,
        domain: ContentDomain,
        query: &DomainQuery,
    ) -> MathverseResult<Vec<SearchResult>> {
        let domain_byte = domain as u8;
        let query_lower = match query {
            DomainQuery::ComplexityClass(s)
            | DomainQuery::NNArchitecture(s)
            | DomainQuery::SoftwareSpec(s)
            | DomainQuery::MscCode(s)
            | DomainQuery::FreeText(s) => s.to_lowercase(),
        };

        let mut results = Vec::new();
        for (i, header) in self.constants.iter().enumerate() {
            if header.content_domain != domain_byte {
                continue;
            }
            if !self.trust_policy.is_visible(header) {
                continue;
            }
            // Match query against the constant name as a simple substring filter.
            let name_idx = header.name_idx as usize;
            if name_idx < self.strings.len() {
                let name_lower = self.strings[name_idx].to_lowercase();
                if name_lower.contains(&query_lower) {
                    results.push(SearchResult {
                        constant_idx: i as ConstantIdx,
                        header: *header,
                        score: 1.0,
                    });
                }
            }
        }
        Ok(results)
    }
}

// ---------------------------------------------------------------------------
// MathverseVerify implementation
// ---------------------------------------------------------------------------

impl MathverseVerify for MathverseLibrary {
    fn verify_foreign(
        &mut self,
        format: ProofFormat,
        statement: &[u8],
        proof: &[u8],
    ) -> MathverseResult<VerificationResult> {
        // Determine source system from format.
        let source = match &format {
            ProofFormat::OLean => SourceSystem::Lean4,
            ProofFormat::CoqSexp => SourceSystem::Coq,
            ProofFormat::MetamathMm => SourceSystem::Metamath,
            ProofFormat::OpenTheory => SourceSystem::HolLight,
            ProofFormat::Alethe => SourceSystem::Z3,
            ProofFormat::Lfsc => SourceSystem::Cvc5,
            ProofFormat::Tstp => SourceSystem::Vampire,
            ProofFormat::Drat | ProofFormat::Lrat => SourceSystem::CaDiCaL,
            ProofFormat::GammaCrownJson => SourceSystem::GammaCrown,
            ProofFormat::VnnComp => SourceSystem::AlphaBetaCrown,
        };

        // Validate non-empty inputs.
        if statement.is_empty() {
            return Ok(VerificationResult {
                constant_idx: None,
                source,
                confidence: ImportConfidence::Unverified,
                status: VerificationStatus::Failed("empty statement".into()),
                summary: "Rejected: empty statement".into(),
            });
        }
        if proof.is_empty() {
            return Ok(VerificationResult {
                constant_idx: None,
                source,
                confidence: ImportConfidence::Unverified,
                status: VerificationStatus::Failed("empty proof".into()),
                summary: "Rejected: empty proof".into(),
            });
        }

        // Determine axiom profile from format.
        let profile_bits = match &format {
            ProofFormat::OpenTheory => AxiomProfile::HOL_AXIOMS,
            ProofFormat::GammaCrownJson | ProofFormat::VnnComp => {
                AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION
            }
            ProofFormat::Alethe | ProofFormat::Lfsc => AxiomProfile::LRA_TRUSTED,
            _ => AxiomProfile::NONE,
        };

        // Attempt to parse statement and proof bytes as FlatDb and reconstruct
        // kernel Expr values for type-checking via Environment::add_decl().
        let stmt_expr = parse_flat_bytes_to_expr(statement);
        let proof_expr = parse_flat_bytes_to_expr(proof);

        // Determine confidence and verification status via kernel type-checking.
        let (confidence, status, checked_type, checked_proof) = match (&stmt_expr, &proof_expr) {
            (Ok(type_expr), Ok(pf_expr)) => {
                // Both parsed: attempt full kernel verification as a theorem.
                let decl_name =
                    Name::from_string(&format!("foreign.{source:?}.{}", self.constants.len()));
                let decl = Declaration::Theorem {
                    name: decl_name,
                    level_params: vec![],
                    type_: type_expr.clone(),
                    value: pf_expr.clone(),
                };
                let mut env = Environment::new();
                match env.add_decl(decl) {
                    Ok(()) => (
                        ImportConfidence::KernelVerified,
                        VerificationStatus::Verified,
                        Some(type_expr.clone()),
                        Some(pf_expr.clone()),
                    ),
                    Err(e) => {
                        // Type-checking failed: try as axiom (statement-only).
                        let axiom_name = Name::from_string(&format!(
                            "foreign.{source:?}.{}.axiom",
                            self.constants.len()
                        ));
                        let axiom_decl = Declaration::Axiom {
                            name: axiom_name,
                            level_params: vec![],
                            type_: type_expr.clone(),
                        };
                        let mut env2 = Environment::new();
                        match env2.add_decl(axiom_decl) {
                            Ok(()) => (
                                ImportConfidence::Translated,
                                VerificationStatus::Failed(format!(
                                    "Proof type-check failed ({e}), accepted as axiom"
                                )),
                                Some(type_expr.clone()),
                                None,
                            ),
                            Err(e2) => (
                                ImportConfidence::Unverified,
                                VerificationStatus::Failed(format!(
                                    "Type-check failed: theorem={e}, axiom={e2}"
                                )),
                                None,
                                None,
                            ),
                        }
                    }
                }
            }
            (Ok(type_expr), Err(_)) => {
                // Only statement parsed: verify type is well-formed as axiom.
                let axiom_name =
                    Name::from_string(&format!("foreign.{source:?}.{}", self.constants.len()));
                let axiom_decl = Declaration::Axiom {
                    name: axiom_name,
                    level_params: vec![],
                    type_: type_expr.clone(),
                };
                let mut env = Environment::new();
                match env.add_decl(axiom_decl) {
                    Ok(()) => (
                        ImportConfidence::Translated,
                        VerificationStatus::Verified,
                        Some(type_expr.clone()),
                        None,
                    ),
                    Err(e) => (
                        ImportConfidence::Unverified,
                        VerificationStatus::Failed(format!("Statement type-check failed: {e}")),
                        None,
                        None,
                    ),
                }
            }
            (Err(stmt_err), _) => {
                // Statement didn't parse as FlatDb: cannot verify without
                // a well-formed type expression. Mark as Unverified.
                (
                    ImportConfidence::Unverified,
                    VerificationStatus::Failed(format!(
                        "Statement FlatDb parse failed: {stmt_err}"
                    )),
                    None,
                    None,
                )
            }
        };

        // Store the constant in the mathverse library catalog.
        let name = format!("foreign.{source:?}.{}", self.constants.len());
        let name_idx = self.strings.len() as u32;
        self.strings.push(name.clone());

        // If we got a kernel Expr from parsing, convert it back to a FlatExpr
        // and store in the arena. Otherwise use a placeholder.
        let stmt_expr_idx = if let Some(ref _type_expr) = checked_type {
            // Store a FlatExpr::lit_nat(1) marker for successfully parsed types.
            // The actual kernel Expr was used for type-checking above.
            let idx = self.exprs.len() as u32;
            self.exprs.push(FlatExpr::lit_nat(1));
            idx
        } else {
            let idx = self.exprs.len() as u32;
            self.exprs.push(FlatExpr::lit_nat(0));
            idx
        };

        let proof_expr_idx = if checked_proof.is_some() {
            let idx = self.exprs.len() as u32;
            self.exprs.push(FlatExpr::lit_nat(1));
            idx
        } else {
            stmt_expr_idx
        };

        let global_idx = self.constants.len() as ConstantIdx;
        let header = MathverseConstantHeader {
            name_idx,
            type_idx: stmt_expr_idx,
            value_idx: proof_expr_idx,
            source_system: source as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: profile_bits,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        self.name_to_idx.insert(name, global_idx);
        self.constants.push(header);
        self.deps.push(Vec::new());
        self.equivalences.push(Vec::new());
        self.type_to_constant.insert(stmt_expr_idx, global_idx);

        let summary = match &status {
            VerificationStatus::Verified => format!(
                "Kernel-verified {format:?} proof from {source:?} as constant {global_idx} ({confidence:?})"
            ),
            VerificationStatus::Failed(reason) => format!(
                "Accepted {format:?} from {source:?} as constant {global_idx} ({confidence:?}): {reason}"
            ),
            _ => format!(
                "Processed {format:?} from {source:?} as constant {global_idx} ({confidence:?})"
            ),
        };

        Ok(VerificationResult {
            constant_idx: Some(global_idx),
            source,
            confidence,
            status,
            summary,
        })
    }

    fn is_known(&self, statement: ExprIdx) -> Option<ConstantIdx> {
        self.type_to_constant.get(&statement).copied()
    }

    fn submit_proven(
        &mut self,
        name: &str,
        type_expr: ExprIdx,
        proof: ExprIdx,
        _source: ConjectureSource,
    ) -> MathverseResult<ConstantIdx> {
        // Validate expression indices.
        if (type_expr as usize) >= self.exprs.len() {
            return Err(MathverseError::ExprOutOfRange {
                idx: type_expr,
                count: self.exprs.len() as u32,
            });
        }
        if proof != NO_VALUE && (proof as usize) >= self.exprs.len() {
            return Err(MathverseError::ExprOutOfRange {
                idx: proof,
                count: self.exprs.len() as u32,
            });
        }

        // Check for duplicate names.
        if self.name_to_idx.contains_key(name) {
            return Err(MathverseError::DuplicateConstant(name.to_string()));
        }

        let name_idx = self.strings.len() as u32;
        self.strings.push(name.to_string());

        let global_idx = self.constants.len() as ConstantIdx;
        let header = MathverseConstantHeader {
            name_idx,
            type_idx: type_expr,
            value_idx: proof,
            source_system: SourceSystem::CleanNative as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        self.name_to_idx.insert(name.to_string(), global_idx);
        self.constants.push(header);
        self.deps.push(Vec::new());
        self.equivalences.push(Vec::new());
        self.type_to_constant.insert(type_expr, global_idx);

        Ok(global_idx)
    }

    fn submit_conjecture(
        &mut self,
        statement: ExprIdx,
        source: ConjectureSource,
    ) -> MathverseResult<ConjectureIdx> {
        // Validate expression index.
        if (statement as usize) >= self.exprs.len() {
            return Err(MathverseError::ExprOutOfRange {
                idx: statement,
                count: self.exprs.len() as u32,
            });
        }

        // Add a conjecture node to the knowledge graph.
        let node = ConceptNode::Conjecture {
            statement_idx: statement,
            source,
            status: ConjectureStatus::Pending,
        };
        let node_idx = self.add_graph_node(node);
        let conj_idx = self.conjectures.len() as ConjectureIdx;
        self.conjectures.push(node_idx);

        Ok(conj_idx)
    }

    fn submit_nn_certificate(&mut self, cert: NNVerificationCert) -> MathverseResult<ConstantIdx> {
        // Validate the certificate's expression indices.
        for &idx in &[cert.network_spec, cert.property, cert.proof] {
            if (idx as usize) >= self.exprs.len() {
                return Err(MathverseError::ExprOutOfRange {
                    idx,
                    count: self.exprs.len() as u32,
                });
            }
        }

        let name = format!("nn_cert.{}", self.constants.len());
        let name_idx = self.strings.len() as u32;
        self.strings.push(name.clone());

        let global_idx = self.constants.len() as ConstantIdx;
        let header = MathverseConstantHeader {
            name_idx,
            type_idx: cert.property,
            value_idx: cert.proof,
            source_system: cert.source_tool as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::NnVerification as u8,
            decl_kind: 0,
            axiom_profile: cert.axiom_profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        self.name_to_idx.insert(name, global_idx);
        self.constants.push(header);
        self.deps.push(Vec::new());
        self.equivalences.push(Vec::new());
        self.type_to_constant.insert(cert.property, global_idx);

        Ok(global_idx)
    }
}

// ---------------------------------------------------------------------------
// FlatDb parsing helper for verify_foreign
// ---------------------------------------------------------------------------

/// Attempt to parse raw bytes as a FlatDb and reconstruct the last expression
/// as a kernel Expr. The convention is that the "root" expression is the last
/// one in the arena (highest index), matching FlatBuilder's output ordering.
fn parse_flat_bytes_to_expr(bytes: &[u8]) -> Result<clean_kernel::expr::Expr, String> {
    let db = FlatDb::from_bytes(bytes).map_err(|e| format!("FlatDb parse: {e}"))?;
    let count = db.expr_count();
    if count == 0 {
        return Err("empty FlatDb (no expressions)".to_string());
    }
    let root_idx = (count - 1) as u32;
    reconstruct_expr(&db, root_idx).map_err(|e| format!("reconstruct: {e}"))
}

// ---------------------------------------------------------------------------
// Dependency extraction
// ---------------------------------------------------------------------------

/// Extract all `Const` name_idx references reachable from `root` in the
/// expression arena. Uses iterative DFS to avoid stack overflow on deeply
/// nested expressions (e.g. large proof terms).
fn extract_const_refs(exprs: &[FlatExpr], root: u32, out: &mut Vec<u32>) {
    let mut stack = Vec::new();
    let mut visited = hashbrown::HashSet::new();
    extract_const_refs_into(exprs, root, out, &mut stack, &mut visited);
}

/// Like [`extract_const_refs`] but uses caller-provided scratch `stack`/`visited`,
/// reused across the per-constant `build_deps` loop to avoid allocating a fresh
/// worklist + visited set on every call. Both are cleared on entry, so prior
/// contents are irrelevant and the appended `out` (sorted+deduped here) is
/// byte-identical to the fresh-allocation version.
fn extract_const_refs_into(
    exprs: &[FlatExpr],
    root: u32,
    out: &mut Vec<u32>,
    stack: &mut Vec<u32>,
    visited: &mut hashbrown::HashSet<u32>,
) {
    stack.clear();
    stack.push(root);
    visited.clear();

    while let Some(idx) = stack.pop() {
        let i = idx as usize;
        if i >= exprs.len() || !visited.insert(idx) {
            continue;
        }
        let expr = &exprs[i];
        let d = &expr.data;
        let read_u32 = |off: usize| -> u32 {
            u32::from_le_bytes([d[off], d[off + 1], d[off + 2], d[off + 3]])
        };

        match expr.tag {
            0 => {} // BVar — leaf, no children
            1 => {} // Sort — leaf (level ref, not an expr)
            2 => {
                // Const: name_idx at offset 0
                out.push(read_u32(0));
            }
            3 => {
                // App: fn_idx at 0, arg_idx at 4
                stack.push(read_u32(0));
                stack.push(read_u32(4));
            }
            4 | 5 => {
                // Lam / Pi: binder_info at 0, ty_idx at 1..5, body_idx at 5..9
                let ty = u32::from_le_bytes([d[1], d[2], d[3], d[4]]);
                let body = u32::from_le_bytes([d[5], d[6], d[7], d[8]]);
                stack.push(ty);
                stack.push(body);
            }
            6 => {
                // Let: ty_idx at 0, val_idx at 4, body_idx at 8
                stack.push(read_u32(0));
                stack.push(read_u32(4));
                stack.push(read_u32(8));
            }
            7 => {} // LitNat — leaf
            8 => {} // LitStr — leaf (string ref, not an expr)
            9 => {
                // Proj: name_idx at 0, field at 4..6, expr_idx at 6..10
                let e = u32::from_le_bytes([d[6], d[7], d[8], d[9]]);
                stack.push(e);
            }
            10 => {} // FVar — leaf
            _ => {}  // unknown tag, skip
        }
    }
    out.sort_unstable();
    out.dedup();
}

// ---------------------------------------------------------------------------
// Index remapping helpers
// ---------------------------------------------------------------------------

/// Remap a shard-local index by adding a base offset.
/// Preserves the sentinel `NO_VALUE` (u32::MAX).
#[inline]
fn remap_idx(idx: u32, base: u32) -> u32 {
    if idx == NO_VALUE {
        NO_VALUE
    } else {
        idx + base
    }
}

/// Remap the inductive-metadata `_pad2` block when merging a shard constant into
/// the global library arena.
///
/// The block carries two kinds of value:
/// - `InductiveDecl.num_params` — a typed integer that is invariant under the
///   merge, so it (and the version/flags bytes) pass through verbatim.
/// - the `InductiveVal.all_names` block — a *string-table* `(start, count)`
///   range that must be shifted by `string_base`, exactly like every other
///   string index this merge relocates.
///
/// Without this, `load_shard` zeroed `_pad2`, dropping the `num_params` metadata
/// that the corpus verifier reads back to rebuild parameterized inductive
/// families through checked `add_inductive` (a `num_params=0` family survived
/// only by the all-arities-zero fallback; a parameterized one like `eq` did
/// not). The string-table indices are remapped so `all_names` keeps resolving in
/// the merged arena.
#[inline]
fn remap_inductive_metadata(constant: &MathverseConstantHeader, string_base: u32) -> [u8; 26] {
    let mut remapped = *constant;
    if let Some((start, count)) = constant.inductive_decl_all_names_block() {
        remapped.set_inductive_decl_all_names(start + string_base, count);
    }
    remapped._pad2
}

/// Merge a shard's level-lists table into the global table, offsetting each
/// stored level-pool index by `level_base`.
///
/// The table is a flat sequence of variable-length records, each of the form
/// `[count, level_idx_0, ..., level_idx_{count-1}]`. The leading `count` slot is
/// a length, not a level reference, so it is copied verbatim; the following
/// `count` slots are indices into the shard's level pool and are each shifted by
/// `level_base` (the offset that the level pool itself was merged with). Records
/// are appended in order, so a record originally at shard-local offset `o` now
/// lives at global offset `o + base` where `base` was the table length before
/// this call — that shift is applied to each `Const`'s `levels_list_idx` in
/// [`remap_expr`]. A truncated trailing record (declared `count` runs past the
/// table) is a corrupt shard and surfaces as an error rather than silently
/// dropping universe arguments.
fn merge_level_lists(
    shard_level_lists: &[u32],
    level_base: u32,
    out: &mut Vec<u32>,
) -> MathverseResult<()> {
    let mut i = 0usize;
    while i < shard_level_lists.len() {
        let count = shard_level_lists[i] as usize;
        let record_end = i.checked_add(1).and_then(|s| s.checked_add(count)).ok_or(
            MathverseError::Truncated {
                expected: usize::MAX,
                got: shard_level_lists.len(),
            },
        )?;
        if record_end > shard_level_lists.len() {
            return Err(MathverseError::ShardCorrupt {
                path: "<merge>".to_string(),
                reason: format!(
                    "level_lists record at offset {i} claims {count} entries but table has only {} remaining",
                    shard_level_lists.len() - (i + 1)
                ),
            });
        }
        out.push(count as u32);
        for &level_idx in &shard_level_lists[i + 1..record_end] {
            out.push(level_idx + level_base);
        }
        i = record_end;
    }
    Ok(())
}

/// Remap level indices within a FlatLevel.
///
/// `idx` is the shard-local index of the level, used only for error reporting.
/// Fails closed on unknown tags to prevent silent data corruption — adding a
/// new FlatLevel variant forces an update here (#3414).
fn remap_level(
    level: &FlatLevel,
    idx: u32,
    level_base: u32,
    string_base: u32,
) -> MathverseResult<FlatLevel> {
    let result = match level.tag {
        FlatLevel::TAG_ZERO => FlatLevel::zero(),
        FlatLevel::TAG_SUCC => {
            let inner =
                u32::from_le_bytes([level.data[0], level.data[1], level.data[2], level.data[3]]);
            FlatLevel::succ(inner + level_base)
        }
        FlatLevel::TAG_MAX | FlatLevel::TAG_IMAX => {
            let left =
                u32::from_le_bytes([level.data[0], level.data[1], level.data[2], level.data[3]]);
            let right =
                u32::from_le_bytes([level.data[4], level.data[5], level.data[6], level.data[7]]);
            let mut result = FlatLevel::max(left + level_base, right + level_base);
            result.tag = level.tag; // preserve TAG_IMAX
            result
        }
        FlatLevel::TAG_PARAM => {
            let name_idx =
                u32::from_le_bytes([level.data[0], level.data[1], level.data[2], level.data[3]]);
            FlatLevel::param(name_idx + string_base)
        }
        unknown => return Err(MathverseError::UnknownLevelTag { tag: unknown, idx }),
    };
    Ok(result)
}

/// Remap expression indices within a FlatExpr.
///
/// `idx` is the shard-local index of the expression, used only for error reporting.
fn remap_expr(
    expr: &FlatExpr,
    idx: u32,
    expr_base: u32,
    level_base: u32,
    level_lists_base: u32,
    string_base: u32,
) -> MathverseResult<FlatExpr> {
    let d = &expr.data;
    let read_u32 =
        |off: usize| -> u32 { u32::from_le_bytes([d[off], d[off + 1], d[off + 2], d[off + 3]]) };

    let mut result = match expr.tag {
        0 => FlatExpr::bvar(read_u32(0)), // BVar: de Bruijn, no remap
        1 => FlatExpr::sort(read_u32(0) + level_base), // Sort
        // Const: the second u32 is `levels_list_idx`, an offset into the
        // level-lists table (or `u32::MAX` for no level args). Shift it by this
        // shard's level-lists base so it points at the relocated record.
        2 => FlatExpr::const_ref(
            read_u32(0) + string_base,
            remap_idx(read_u32(4), level_lists_base),
        ),
        3 => FlatExpr::app(read_u32(0) + expr_base, read_u32(4) + expr_base), // App
        4 => {
            // Lam
            let bi = d[0];
            let ty = u32::from_le_bytes([d[1], d[2], d[3], d[4]]);
            let body = u32::from_le_bytes([d[5], d[6], d[7], d[8]]);
            FlatExpr::lam(bi, ty + expr_base, body + expr_base)
        }
        5 => {
            // Pi
            let bi = d[0];
            let ty = u32::from_le_bytes([d[1], d[2], d[3], d[4]]);
            let body = u32::from_le_bytes([d[5], d[6], d[7], d[8]]);
            FlatExpr::pi(bi, ty + expr_base, body + expr_base)
        }
        6 => {
            // Let
            FlatExpr::let_expr(
                read_u32(0) + expr_base,
                read_u32(4) + expr_base,
                read_u32(8) + expr_base,
            )
        }
        7 => {
            // LitNat
            let val = u64::from_le_bytes([d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7]]);
            FlatExpr::lit_nat(val)
        }
        8 => FlatExpr::lit_str(read_u32(0) + string_base), // LitStr
        9 => {
            // Proj
            let name = read_u32(0) + string_base;
            let field = u16::from_le_bytes([d[4], d[5]]);
            let e = read_u32(6) + expr_base;
            FlatExpr::proj(name, field, e)
        }
        10 => {
            // FVar
            let val = u64::from_le_bytes([d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7]]);
            FlatExpr::fvar(val)
        }
        unknown => return Err(MathverseError::UnknownExprTag { tag: unknown, idx }),
    };
    result.flags = expr.flags;
    Ok(result)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardWriter;
    use crate::types::{AxiomProfile, ContentDomain, ImportConfidence, SourceSystem};
    use clean_kernel::flat::{FlatExpr, FlatLevel};

    /// The lazy BM25 path must be semantically identical to rebuilding eagerly
    /// after every shard. This bounded synthetic test exercises both paths and
    /// compares their complete ranked result identities and scores.
    #[test]
    fn eager_and_lazy_bm25_indexing_are_equivalent() {
        const SHARD_COUNT: usize = 8;
        const CONSTANTS_PER_SHARD: usize = 32;

        let mut shards: Vec<ShardReader> = Vec::with_capacity(SHARD_COUNT);
        for shard in 0..SHARD_COUNT {
            let names: Vec<String> = (0..CONSTANTS_PER_SHARD)
                .map(|i| format!("Mod{shard}.theorem_{i}_alpha_beta_gamma"))
                .collect();
            let entries: Vec<(&str, ContentDomain, AxiomProfile)> = names
                .iter()
                .map(|name| (name.as_str(), ContentDomain::PureMath, AxiomProfile::NONE))
                .collect();
            shards.push(build_test_shard(&entries));
        }

        let mut eager = MathverseLibrary::new(TrustPolicy::permissive());
        let mut lazy = MathverseLibrary::new(TrustPolicy::permissive());
        for shard in &shards {
            eager.load_shard(shard).expect("load eager shard");
            eager.build_search_index();
            lazy.load_shard(shard).expect("load lazy shard");
        }

        let eager_results = eager.search_explain("theorem alpha", 16);
        let lazy_results = lazy.search_explain("theorem alpha", 16);
        assert!(
            !eager_results.is_empty(),
            "query must exercise the BM25 index"
        );
        assert_eq!(eager.constant_count(), SHARD_COUNT * CONSTANTS_PER_SHARD);
        assert_eq!(lazy.constant_count(), eager.constant_count());
        assert_eq!(lazy_results.len(), eager_results.len());
        for (eager_hit, lazy_hit) in eager_results.iter().zip(&lazy_results) {
            assert_eq!(lazy_hit.constant_idx, eager_hit.constant_idx);
            assert_eq!(
                lazy_hit.total_score.to_bits(),
                eager_hit.total_score.to_bits()
            );
            assert_eq!(lazy_hit.query_tokens, eager_hit.query_tokens);
            assert_eq!(lazy_hit.token_scores.len(), eager_hit.token_scores.len());
            for (eager_token, lazy_token) in
                eager_hit.token_scores.iter().zip(&lazy_hit.token_scores)
            {
                assert_eq!(lazy_token.token, eager_token.token);
                assert_eq!(lazy_token.tf, eager_token.tf);
                assert_eq!(lazy_token.df, eager_token.df);
                assert_eq!(lazy_token.score.to_bits(), eager_token.score.to_bits());
            }
        }
    }

    /// Helper: build a ShardReader with the given named constants.
    fn build_test_shard(names: &[(&str, ContentDomain, AxiomProfile)]) -> ShardReader {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        for &(name, domain, profile) in names {
            let ni = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: domain as u8,
                decl_kind: 0,
                axiom_profile: profile,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        ShardReader::from_bytes(&buf).unwrap()
    }

    #[test]
    fn test_empty_library() {
        let lib = MathverseLibrary::new(TrustPolicy::default_policy());
        assert_eq!(lib.constant_count(), 0);
        assert!(lib.lookup_name("anything").is_none());
    }

    #[test]
    fn test_load_shard_and_lookup() {
        let shard = build_test_shard(&[
            ("Nat.add", ContentDomain::PureMath, AxiomProfile::NONE),
            ("Nat.mul", ContentDomain::PureMath, AxiomProfile::NONE),
            ("Bool.true", ContentDomain::Logic, AxiomProfile::NONE),
        ]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let added = lib.load_shard(&shard).unwrap();
        assert_eq!(added, 3);
        assert_eq!(lib.constant_count(), 3);

        // Name lookup
        assert!(lib.lookup_name("Nat.add").is_some());
        assert!(lib.lookup_name("Nat.mul").is_some());
        assert!(lib.lookup_name("Bool.true").is_some());
        assert!(lib.lookup_name("Nonexistent").is_none());

        // get_name
        assert_eq!(lib.get_name(0), Some("Nat.add"));
        assert_eq!(lib.get_name(1), Some("Nat.mul"));
        assert_eq!(lib.get_name(2), Some("Bool.true"));
        assert_eq!(lib.get_name(99), None);
    }

    #[test]
    fn test_trust_policy_filtering() {
        let shard = build_test_shard(&[
            ("visible.thm", ContentDomain::PureMath, AxiomProfile::NONE),
            (
                "axiomatized.thm",
                ContentDomain::PureMath,
                AxiomProfile::AXIOMATIZED,
            ),
            (
                "also_visible.thm",
                ContentDomain::PureMath,
                AxiomProfile::CHOICE,
            ),
        ]);

        // Default policy: trust-gated constants are hidden.
        let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
        lib.load_shard(&shard).unwrap();

        assert!(lib.lookup_name("visible.thm").is_some());
        assert!(
            lib.lookup_name("axiomatized.thm").is_none(),
            "axiomatized should be hidden by default policy"
        );
        // CHOICE is not trust-gated, so it should be visible.
        assert!(lib.lookup_name("also_visible.thm").is_some());
    }

    #[test]
    fn test_trust_policy_permissive() {
        let shard = build_test_shard(&[
            ("visible.thm", ContentDomain::PureMath, AxiomProfile::NONE),
            (
                "axiomatized.thm",
                ContentDomain::PureMath,
                AxiomProfile::AXIOMATIZED,
            ),
        ]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        assert!(lib.lookup_name("visible.thm").is_some());
        assert!(lib.lookup_name("axiomatized.thm").is_some());
    }

    #[test]
    fn test_type_search() {
        // Build a shard with typed constants for discrimination tree search.
        let mut writer = ShardWriter::new();
        let nat_name = writer.add_string("Nat");
        let bool_name = writer.add_string("Bool");
        let c0_name = writer.add_string("nat_id");
        let c1_name = writer.add_string("nat_to_bool");

        let l0 = writer.add_level(FlatLevel::zero());
        let e_nat = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        let _e_bool = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));
        let e_nat2 = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        let pi_nat_nat = writer.add_expr(FlatExpr::pi(0, e_nat, e_nat2));
        let e_bool2 = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));
        let pi_nat_bool = writer.add_expr(FlatExpr::pi(0, e_nat, e_bool2));
        let sort_e = writer.add_expr(FlatExpr::sort(l0));

        let mk_hdr = |name: u32, ty: u32| MathverseConstantHeader {
            name_idx: name,
            type_idx: ty,
            value_idx: sort_e,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        writer.add_constant(mk_hdr(c0_name, pi_nat_nat));
        writer.add_constant(mk_hdr(c1_name, pi_nat_bool));

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let shard = ShardReader::from_bytes(&buf).unwrap();

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Build a query for Nat -> * (wildcard in return).
        // The query expr arena uses the GLOBAL string indices after remap.
        let global_nat_name = nat_name; // In this single-shard case, string base is 0.
                                        // Illustrative query arena (Nat -> *); search_type below uses the
                                        // library's own arena via type_idx, so this is kept for documentation.
        let _qexprs = [
            FlatExpr::const_ref(global_nat_name, u32::MAX), // 0: Nat
            FlatExpr::lit_nat(0),                           // 1: Star
            FlatExpr::pi(0, 0, 1),                          // 2: Pi(Nat, Star)
        ];

        // We need to put query exprs into the library's expr arena at known indices.
        // Instead, search_type takes an ExprIdx into the library's own arena.
        // For this test, use the global type_idx of constant 0 (pi_nat_nat).
        let results = lib.search_type(lib.constants[0].type_idx, 10).unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].constant_idx, 0);
    }

    #[test]
    fn test_dependency_walking() {
        let shard = build_test_shard(&[
            ("a", ContentDomain::PureMath, AxiomProfile::NONE),
            ("b", ContentDomain::PureMath, AxiomProfile::NONE),
            ("c", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        lib.add_dependency(0, 1);
        lib.add_dependency(0, 2);
        lib.add_dependency(1, 2);

        // Walk from node 0 — should yield 0, then transitive deps 1 and 2.
        let mut deps: Vec<ConstantIdx> = lib.walk_deps(0).collect();
        deps.sort_unstable();
        assert_eq!(deps, vec![0, 1, 2]);

        // Walk from node 1 — should yield 1 and its dep 2.
        let mut deps1: Vec<ConstantIdx> = lib.walk_deps(1).collect();
        deps1.sort_unstable();
        assert_eq!(deps1, vec![1, 2]);

        // Walk from node 2 — leaf, should yield only 2.
        let deps2: Vec<ConstantIdx> = lib.walk_deps(2).collect();
        assert_eq!(deps2, vec![2]);
    }

    #[test]
    fn test_equivalence_queries() {
        let shard = build_test_shard(&[
            ("lean.nat_add", ContentDomain::PureMath, AxiomProfile::NONE),
            ("coq.nat_add", ContentDomain::PureMath, AxiomProfile::NONE),
            (
                "isabelle.nat_add",
                ContentDomain::PureMath,
                AxiomProfile::NONE,
            ),
        ]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        lib.add_equivalence(0, 1, EquivConfidence::ProvedEquivalent);
        lib.add_equivalence(0, 2, EquivConfidence::ErasedCandidate { score: 0.95 });

        let equivs = lib.find_equivalents(0).unwrap();
        assert_eq!(equivs.len(), 2);

        // Bidirectional: querying from 1 should find 0.
        let equivs_from_1 = lib.find_equivalents(1).unwrap();
        assert_eq!(equivs_from_1.len(), 1);
        assert_eq!(equivs_from_1[0].1, 0);
    }

    #[test]
    fn test_domain_search() {
        let shard = build_test_shard(&[
            ("Nat.add", ContentDomain::PureMath, AxiomProfile::NONE),
            ("tcp.spec", ContentDomain::Software, AxiomProfile::NONE),
            (
                "PSPACE.complete",
                ContentDomain::Complexity,
                AxiomProfile::NONE,
            ),
            ("Nat.mul", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let results = lib
            .search_domain(
                ContentDomain::PureMath,
                &DomainQuery::FreeText("Nat".to_string()),
            )
            .unwrap();
        assert_eq!(results.len(), 2);

        let results = lib
            .search_domain(
                ContentDomain::Software,
                &DomainQuery::SoftwareSpec("tcp".to_string()),
            )
            .unwrap();
        assert_eq!(results.len(), 1);

        let results = lib
            .search_domain(
                ContentDomain::Complexity,
                &DomainQuery::ComplexityClass("PSPACE".to_string()),
            )
            .unwrap();
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_multi_shard_load() {
        let shard1 = build_test_shard(&[
            ("Nat.add", ContentDomain::PureMath, AxiomProfile::NONE),
            ("Nat.mul", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);
        let shard2 = build_test_shard(&[
            ("Bool.true", ContentDomain::Logic, AxiomProfile::NONE),
            ("Bool.false", ContentDomain::Logic, AxiomProfile::NONE),
        ]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        assert_eq!(lib.load_shard(&shard1).unwrap(), 2);
        assert_eq!(lib.load_shard(&shard2).unwrap(), 2);
        assert_eq!(lib.constant_count(), 4);

        assert!(lib.lookup_name("Nat.add").is_some());
        assert!(lib.lookup_name("Bool.true").is_some());
    }

    #[test]
    fn test_graph_query_basic() {
        let shard = build_test_shard(&[("a", ContentDomain::PureMath, AxiomProfile::NONE)]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let n0 = lib.add_graph_node(ConceptNode::Theorem { constant_idx: 0 });
        let n1 = lib.add_graph_node(ConceptNode::Structure {
            name: "Group".to_string(),
            axioms: vec![0],
        });
        lib.add_graph_edge(n0, n1, ConceptEdge::DependsOn);

        let subgraph = lib
            .graph_query(n0 as ConstantIdx, &EdgeFilter::default(), 2)
            .unwrap();
        assert_eq!(subgraph.nodes.len(), 2);
        assert_eq!(subgraph.edges.len(), 1);
    }

    #[test]
    fn test_semantic_search_empty_library() {
        let lib = MathverseLibrary::new(TrustPolicy::permissive());
        let results = lib.search_semantic("anything", 10).unwrap();
        assert!(results.is_empty());
    }

    #[test]
    fn test_build_indices_rebuild() {
        let shard = build_test_shard(&[("Nat.add", ContentDomain::PureMath, AxiomProfile::NONE)]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Rebuild should not corrupt anything.
        lib.build_indices();
        assert!(lib.lookup_name("Nat.add").is_some());
        assert_eq!(lib.constant_count(), 1);
    }

    // -----------------------------------------------------------------------
    // Dependency extraction tests
    // -----------------------------------------------------------------------

    /// Helper: build a shard with explicit expression structures for dep tests.
    /// Returns the shard along with the expected dependency names for each constant.
    fn build_dep_test_shard() -> ShardReader {
        let mut writer = ShardWriter::new();

        // String table: 0="Nat", 1="Bool", 2="add_fn", 3="helper"
        let nat_name = writer.add_string("Nat");
        let bool_name = writer.add_string("Bool");
        let add_fn_name = writer.add_string("add_fn");
        let helper_name = writer.add_string("helper");

        // Expression arena:
        let l0 = writer.add_level(FlatLevel::zero());
        let e_sort = writer.add_expr(FlatExpr::sort(l0)); // idx 0: Sort(0)
        let e_nat = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX)); // idx 1: Const("Nat")
        let e_bool = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX)); // idx 2: Const("Bool")
        let e_pi = writer.add_expr(FlatExpr::pi(0, e_nat, e_bool)); // idx 3: Pi(Nat, Bool)
        let e_app = writer.add_expr(FlatExpr::app(e_nat, e_bool)); // idx 4: App(Nat, Bool)

        // Constant 0: "Nat" — type is Sort (no deps)
        writer.add_constant(MathverseConstantHeader {
            name_idx: nat_name,
            type_idx: e_sort,
            value_idx: NO_VALUE, // axiomatized
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        // Constant 1: "Bool" — type is Sort (no deps)
        writer.add_constant(MathverseConstantHeader {
            name_idx: bool_name,
            type_idx: e_sort,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        // Constant 2: "add_fn" — type is Pi(Nat, Bool), depends on Nat and Bool
        writer.add_constant(MathverseConstantHeader {
            name_idx: add_fn_name,
            type_idx: e_pi,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        // Constant 3: "helper" — type is Sort, value is App(Nat, Bool)
        writer.add_constant(MathverseConstantHeader {
            name_idx: helper_name,
            type_idx: e_sort,
            value_idx: e_app,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        ShardReader::from_bytes(&buf).unwrap()
    }

    #[test]
    fn test_build_deps_finds_correct_dependencies() {
        let shard = build_dep_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Nat (idx 0): type=Sort, value=NO_VALUE → no deps
        assert!(lib.deps()[0].is_empty(), "Nat should have no deps");

        // Bool (idx 1): type=Sort, value=NO_VALUE → no deps
        assert!(lib.deps()[1].is_empty(), "Bool should have no deps");

        // add_fn (idx 2): type=Pi(Nat, Bool) → deps on Nat(0) and Bool(1)
        let mut add_deps = lib.deps()[2].clone();
        add_deps.sort_unstable();
        assert_eq!(add_deps, vec![0, 1], "add_fn should depend on Nat and Bool");

        // helper (idx 3): type=Sort, value=App(Nat, Bool) → deps on Nat(0) and Bool(1)
        let mut helper_deps = lib.deps()[3].clone();
        helper_deps.sort_unstable();
        assert_eq!(
            helper_deps,
            vec![0, 1],
            "helper should depend on Nat and Bool via value"
        );
    }

    #[test]
    fn test_build_deps_self_reference_excluded() {
        // Build a constant whose type expression references its own name.
        let mut writer = ShardWriter::new();
        let self_name = writer.add_string("SelfRef");

        let l0 = writer.add_level(FlatLevel::zero());
        let e_self = writer.add_expr(FlatExpr::const_ref(self_name, u32::MAX));

        writer.add_constant(MathverseConstantHeader {
            name_idx: self_name,
            type_idx: e_self,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let _ = l0; // suppress unused warning

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let shard = ShardReader::from_bytes(&buf).unwrap();

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // SelfRef references itself in its type; self-dep should be excluded.
        assert!(
            lib.deps()[0].is_empty(),
            "Self-referencing constant should have no deps"
        );
    }

    #[test]
    fn test_build_deps_resolves_within_same_source_system() {
        // Two homonyms named "C" live in DIFFERENT systems; a Lean4 constant
        // references "C" in its type. The dependency must resolve to the Lean4
        // "C", never the Coq homonym — the cross-system single-letter collision
        // the deps command surfaced as noise. We deliberately load the Coq "C"
        // LAST so the bare-name `name_to_idx` winner is the WRONG (Coq) one; the
        // same-source-system resolver must still pick the Lean4 "C".
        let mut writer = ShardWriter::new();
        let c_name = writer.add_string("C");
        let user_name = writer.add_string("user");

        let l0 = writer.add_level(FlatLevel::zero());
        let e_sort = writer.add_expr(FlatExpr::sort(l0));
        let e_c_ref = writer.add_expr(FlatExpr::const_ref(c_name, u32::MAX));

        // idx 0: Lean4 "C" (the correct dependency target).
        writer.add_constant(MathverseConstantHeader {
            name_idx: c_name,
            type_idx: e_sort,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        // idx 1: Coq "C" — the homonym that must NOT be chosen. Loaded last so it
        // wins the bare-name lookup, proving the resolver is system-aware.
        writer.add_constant(MathverseConstantHeader {
            name_idx: c_name,
            type_idx: e_sort,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        // idx 2: Lean4 "user" whose type references "C".
        writer.add_constant(MathverseConstantHeader {
            name_idx: user_name,
            type_idx: e_c_ref,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let shard = ShardReader::from_bytes(&buf).unwrap();

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // `user` (idx 2) must depend on the Lean4 "C" (idx 0), NOT the Coq one.
        assert_eq!(
            lib.deps()[2],
            vec![0],
            "dep `C` must resolve to the same-system (Lean4) homonym, not the Coq one"
        );
        let dep_idx = lib.deps()[2][0];
        assert_eq!(
            lib.get_constant(dep_idx).map(|h| h.source_system),
            Some(SourceSystem::Lean4 as u8),
            "resolved dependency must be in the referencing constant's own system"
        );
    }

    #[test]
    fn test_walk_deps_transitive_closure() {
        let shard = build_dep_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // add_fn (2) depends on Nat (0) and Bool (1).
        // helper (3) depends on Nat (0) and Bool (1).
        // Now manually add: Nat (0) depends on helper (3) to create a chain
        // for testing transitive closure.
        lib.add_dependency(0, 3);

        // Walk from add_fn (2): should reach Nat (0), Bool (1), and
        // transitively helper (3) via Nat.
        let mut walked: Vec<ConstantIdx> = lib.walk_deps(2).collect();
        walked.sort_unstable();
        assert_eq!(
            walked,
            vec![0, 1, 2, 3],
            "walk_deps should find transitive closure"
        );
    }

    #[test]
    fn test_walk_deps_circular_deps_no_infinite_loop() {
        let shard = build_test_shard(&[
            ("a", ContentDomain::PureMath, AxiomProfile::NONE),
            ("b", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Create a cycle: a -> b -> a
        lib.add_dependency(0, 1);
        lib.add_dependency(1, 0);

        // walk_deps must terminate and yield both.
        let mut walked: Vec<ConstantIdx> = lib.walk_deps(0).collect();
        walked.sort_unstable();
        assert_eq!(walked, vec![0, 1], "circular deps should not infinite loop");
    }

    #[test]
    fn test_reverse_deps_finds_direct_users() {
        let shard = build_dep_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // add_fn (2) and helper (3) both depend on Nat (0) and Bool (1).
        // So the direct users of Nat are {add_fn(2), helper(3)}.
        let users: Vec<ConstantIdx> = lib
            .reverse_deps_bounded(0, false, 1, 200)
            .into_iter()
            .map(|(idx, _)| idx)
            .collect();
        let mut sorted = users.clone();
        sorted.sort_unstable();
        assert_eq!(
            sorted,
            vec![2, 3],
            "Nat's direct users are add_fn and helper"
        );

        // A leaf-of-the-reverse-graph (add_fn) has no users.
        assert!(
            lib.reverse_deps_bounded(2, false, 1, 200).is_empty(),
            "add_fn is used by nothing"
        );
    }

    #[test]
    fn test_reverse_in_degree_counts_users() {
        let shard = build_dep_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        assert_eq!(lib.reverse_in_degree(0), 2, "Nat used by add_fn + helper");
        assert_eq!(lib.reverse_in_degree(1), 2, "Bool used by add_fn + helper");
        assert_eq!(lib.reverse_in_degree(2), 0, "add_fn used by nothing");
    }

    #[test]
    fn test_reverse_deps_transitive_closure() {
        let shard = build_dep_test_shard();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Chain: helper (3) depends on add_fn (2) [add edge], add_fn depends on
        // Nat (0). So transitive reverse-deps of Nat reach add_fn AND helper.
        lib.add_dependency(3, 2);

        let mut users: Vec<ConstantIdx> = lib
            .reverse_deps_bounded(0, true, usize::MAX, 200)
            .into_iter()
            .map(|(idx, _)| idx)
            .collect();
        users.sort_unstable();
        assert_eq!(
            users,
            vec![2, 3],
            "transitive reverse closure of Nat reaches add_fn and helper"
        );
    }

    #[test]
    fn test_reverse_deps_depth_bound() {
        // Linear chain c(2) -> b(1) -> a(0): b is a depth-1 user of a, c is a
        // depth-2 user reachable only transitively through b.
        let shard = build_test_shard(&[
            ("a", ContentDomain::PureMath, AxiomProfile::NONE),
            ("b", ContentDomain::PureMath, AxiomProfile::NONE),
            ("c", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(1, 0); // b -> a
        lib.add_dependency(2, 1); // c -> b

        // Direct (non-transitive): only b, labelled depth 1.
        let direct = lib.reverse_deps_bounded(0, false, 1, 200);
        assert_eq!(
            direct,
            vec![(1, 1)],
            "direct users of a is just b at depth 1"
        );

        // Transitive depth 1: still only b (c is one hop too far).
        let d1: Vec<ConstantIdx> = lib
            .reverse_deps_bounded(0, true, 1, 200)
            .into_iter()
            .map(|(idx, _)| idx)
            .collect();
        assert_eq!(d1, vec![1], "depth-1 transitive walk stops before c");

        // Full transitive: b (depth 1) and c (depth 2).
        let mut full = lib.reverse_deps_bounded(0, true, usize::MAX, 200);
        full.sort_by_key(|&(idx, _)| idx);
        assert_eq!(
            full,
            vec![(1, 1), (2, 2)],
            "full transitive walk reaches c at depth 2"
        );
    }

    #[test]
    fn test_reverse_deps_ranked_by_in_degree() {
        // Build: hub(0); two users a(1), b(2) both depend on hub. a is itself
        // used by c(3) and d(4) (in-degree 2); b is used by nobody (in-degree
        // 0). Reverse-deps of hub must rank a before b (more impactful).
        let shard = build_test_shard(&[
            ("hub", ContentDomain::PureMath, AxiomProfile::NONE),
            ("a", ContentDomain::PureMath, AxiomProfile::NONE),
            ("b", ContentDomain::PureMath, AxiomProfile::NONE),
            ("c", ContentDomain::PureMath, AxiomProfile::NONE),
            ("d", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(1, 0); // a -> hub
        lib.add_dependency(2, 0); // b -> hub
        lib.add_dependency(3, 1); // c -> a
        lib.add_dependency(4, 1); // d -> a

        let ranked: Vec<ConstantIdx> = lib
            .reverse_deps_bounded(0, false, 1, 200)
            .into_iter()
            .map(|(idx, _)| idx)
            .collect();
        assert_eq!(
            ranked,
            vec![1, 2],
            "higher-in-degree user (a) ranks before lower (b)"
        );
    }

    #[test]
    fn test_reverse_deps_cache_invalidates_on_add_dependency() {
        let shard = build_test_shard(&[
            ("x", ContentDomain::PureMath, AxiomProfile::NONE),
            ("y", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // No edges yet: x has no users (this also builds + caches the reverse map).
        assert_eq!(lib.reverse_in_degree(0), 0);

        // Add y -> x; the cache must rebuild and reflect the new edge.
        lib.add_dependency(1, 0);
        assert_eq!(
            lib.reverse_in_degree(0),
            1,
            "reverse cache reflects the freshly added edge"
        );
        let users: Vec<ConstantIdx> = lib
            .reverse_deps_bounded(0, false, 1, 200)
            .into_iter()
            .map(|(idx, _)| idx)
            .collect();
        assert_eq!(users, vec![1], "y is now the sole user of x");
    }

    #[test]
    fn test_resolve_name_loose_tiers() {
        let shard = build_test_shard(&[
            ("Nat.add_comm", ContentDomain::PureMath, AxiomProfile::NONE),
            ("padd_commute", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Exact wins.
        assert_eq!(lib.resolve_name_loose("Nat.add_comm"), Some(0));
        // Case-insensitive exact.
        assert_eq!(lib.resolve_name_loose("nat.ADD_comm"), Some(0));
        // Substring fallback (no exact match for "commute").
        assert_eq!(lib.resolve_name_loose("commute"), Some(1));
        // Nothing matches.
        assert_eq!(lib.resolve_name_loose("nonexistent_zzz"), None);
    }

    #[test]
    fn test_deps_empty_for_no_references() {
        // Constants whose types and values reference no other constants.
        let mut writer = ShardWriter::new();
        let name = writer.add_string("Pure");
        let l0 = writer.add_level(FlatLevel::zero());
        let e_sort = writer.add_expr(FlatExpr::sort(l0));
        let e_nat = writer.add_expr(FlatExpr::lit_nat(42));

        writer.add_constant(MathverseConstantHeader {
            name_idx: name,
            type_idx: e_sort,
            value_idx: e_nat,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let shard = ShardReader::from_bytes(&buf).unwrap();

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        assert!(
            lib.deps()[0].is_empty(),
            "constant with only Sort and LitNat should have no deps"
        );
    }

    #[test]
    fn test_semantic_search_returns_results() {
        let shard = build_test_shard(&[
            ("Nat.add_comm", ContentDomain::PureMath, AxiomProfile::NONE),
            ("Nat.mul_comm", ContentDomain::PureMath, AxiomProfile::NONE),
            ("List.map", ContentDomain::PureMath, AxiomProfile::NONE),
            ("Int.add_comm", ContentDomain::PureMath, AxiomProfile::NONE),
        ]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let results = lib.search_semantic("commutative addition", 10).unwrap();
        assert!(!results.is_empty(), "semantic search should return results");
        // Nat.add_comm and Int.add_comm should both appear.
        let indices: Vec<ConstantIdx> = results.iter().map(|r| r.constant_idx).collect();
        assert!(
            indices.contains(&0),
            "Nat.add_comm should appear in results"
        );
    }

    #[test]
    fn test_semantic_search_filters_by_trust() {
        let shard = build_test_shard(&[
            (
                "visible.add_comm",
                ContentDomain::PureMath,
                AxiomProfile::NONE,
            ),
            (
                "hidden.add_comm",
                ContentDomain::PureMath,
                AxiomProfile::AXIOMATIZED,
            ),
        ]);

        // Default policy hides axiomatized constants.
        let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
        lib.load_shard(&shard).unwrap();

        let results = lib.search_semantic("add comm", 10).unwrap();
        // Only the visible constant should appear.
        for r in &results {
            assert_ne!(
                r.constant_idx, 1,
                "axiomatized constant should be filtered out"
            );
        }
        assert!(
            results.iter().any(|r| r.constant_idx == 0),
            "visible constant should appear"
        );
    }

    #[test]
    fn test_provenance_add_and_retrieve() {
        use crate::provenance::ProvenanceBuilder;

        let shard =
            build_test_shard(&[("Nat.add_comm", ContentDomain::PureMath, AxiomProfile::NONE)]);

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        assert!(lib.provenance().is_empty());

        let record = ProvenanceBuilder::new("Nat.add_comm")
            .source_file("Mathlib/Data/Nat/Basic.lean")
            .source_line(42)
            .build();

        lib.add_provenance_record(0, record);

        assert_eq!(lib.provenance().len(), 1);
        let retrieved = lib.provenance().get(0).expect("record should exist");
        assert_eq!(retrieved.original_name, "Nat.add_comm");
        assert_eq!(
            retrieved.source_file.as_deref(),
            Some("Mathlib/Data/Nat/Basic.lean")
        );

        // Header should be updated with correct provenance_idx and digest.
        let header = lib.get_constant(0).expect("constant should exist");
        assert_eq!(header.provenance_idx, 0);
        assert!(lib.provenance().verify_digest(header));
    }

    #[test]
    fn test_extract_const_refs_let_expr() {
        // Test extraction through Let expressions (3 children).
        let mut writer = ShardWriter::new();
        let a_name = writer.add_string("A");
        let b_name = writer.add_string("B");
        let c_name = writer.add_string("C");
        let d_name = writer.add_string("D");

        let l0 = writer.add_level(FlatLevel::zero());
        let e_sort = writer.add_expr(FlatExpr::sort(l0));
        let e_a = writer.add_expr(FlatExpr::const_ref(a_name, u32::MAX));
        let e_b = writer.add_expr(FlatExpr::const_ref(b_name, u32::MAX));
        let e_c = writer.add_expr(FlatExpr::const_ref(c_name, u32::MAX));
        let e_let = writer.add_expr(FlatExpr::let_expr(e_a, e_b, e_c));

        let mk_hdr = |name: u32, ty: u32| MathverseConstantHeader {
            name_idx: name,
            type_idx: ty,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        // Constants 0-2: A, B, C (type=Sort, no deps)
        writer.add_constant(mk_hdr(a_name, e_sort));
        writer.add_constant(mk_hdr(b_name, e_sort));
        writer.add_constant(mk_hdr(c_name, e_sort));
        // Constant 3: D — type is Let(A, B, C)
        writer.add_constant(mk_hdr(d_name, e_let));

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let shard = ShardReader::from_bytes(&buf).unwrap();

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // D's type is Let(A, B, C), so deps should include A(0), B(1), C(2).
        let mut deps = lib.deps()[3].clone();
        deps.sort_unstable();
        assert_eq!(
            deps,
            vec![0, 1, 2],
            "Let expr should extract all 3 children's const refs"
        );
    }

    // -----------------------------------------------------------------------
    // MathverseVerify implementation tests
    // -----------------------------------------------------------------------

    use crate::graph_alpha::ConjectureSource;
    use crate::nn_alpha::{NNVerificationCert, VerificationMethod};
    use crate::verify::{MathverseVerify, ProofFormat, VerificationStatus};

    #[test]
    fn test_verify_foreign_olean_unparseable_rejected() {
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let shard = build_test_shard(&[("seed", ContentDomain::PureMath, AxiomProfile::NONE)]);
        lib.load_shard(&shard).unwrap();
        let result = lib
            .verify_foreign(ProofFormat::OLean, b"stmt", b"proof")
            .unwrap();
        assert!(matches!(result.status, VerificationStatus::Failed(_)));
        assert!(result.constant_idx.is_some());
        assert_eq!(result.confidence, ImportConfidence::Unverified);
    }

    #[test]
    fn test_verify_foreign_empty_statement_rejected() {
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let result = lib
            .verify_foreign(ProofFormat::CoqSexp, b"", b"proof")
            .unwrap();
        assert!(
            matches!(result.status, VerificationStatus::Failed(_)),
            "empty statement should be rejected"
        );
        assert!(result.constant_idx.is_none());
    }

    #[test]
    fn test_verify_foreign_empty_proof_rejected() {
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let result = lib
            .verify_foreign(ProofFormat::MetamathMm, b"stmt", b"")
            .unwrap();
        assert!(
            matches!(result.status, VerificationStatus::Failed(_)),
            "empty proof should be rejected"
        );
    }

    #[test]
    fn test_is_known_found_and_missing() {
        let shard = build_test_shard(&[("Nat.add", ContentDomain::PureMath, AxiomProfile::NONE)]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // The type_idx of the loaded constant should be findable.
        let header = lib.get_constant(0).unwrap();
        let type_idx = header.type_idx;
        assert!(lib.is_known(type_idx).is_some());

        // Non-existent type index.
        assert!(lib.is_known(99999).is_none());
    }

    #[test]
    fn test_submit_proven_success() {
        let shard = build_test_shard(&[("seed", ContentDomain::PureMath, AxiomProfile::NONE)]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let type_idx = 0; // Sort expr from the shard
        let proof_idx = 0;
        let idx = lib
            .submit_proven(
                "my_theorem",
                type_idx,
                proof_idx,
                ConjectureSource::UserSubmitted,
            )
            .unwrap();

        assert!(lib.lookup_name("my_theorem").is_some());
        let header = lib.get_constant(idx).unwrap();
        assert_eq!(
            header.import_confidence,
            ImportConfidence::KernelVerified as u8
        );
        assert_eq!(header.source_system, SourceSystem::CleanNative as u8);
    }

    #[test]
    fn test_submit_proven_duplicate_name_rejected() {
        let shard = build_test_shard(&[("existing", ContentDomain::PureMath, AxiomProfile::NONE)]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let result = lib.submit_proven("existing", 0, 0, ConjectureSource::UserSubmitted);
        assert!(result.is_err(), "duplicate name should be rejected");
    }

    #[test]
    fn test_submit_conjecture_success() {
        let shard = build_test_shard(&[("seed", ContentDomain::PureMath, AxiomProfile::NONE)]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let conj_idx = lib
            .submit_conjecture(0, ConjectureSource::UserSubmitted)
            .unwrap();
        assert_eq!(conj_idx, 0);

        // Submitting a second conjecture should get index 1.
        let conj_idx2 = lib
            .submit_conjecture(0, ConjectureSource::Enumerated { depth: 3 })
            .unwrap();
        assert_eq!(conj_idx2, 1);
    }

    #[test]
    fn test_submit_conjecture_invalid_expr_rejected() {
        let lib_empty = MathverseLibrary::new(TrustPolicy::permissive());
        // No expressions loaded, so any ExprIdx is out of range.
        let mut lib = lib_empty;
        let result = lib.submit_conjecture(42, ConjectureSource::UserSubmitted);
        assert!(result.is_err());
    }

    #[test]
    fn test_submit_nn_certificate_success() {
        let shard = build_test_shard(&[("seed", ContentDomain::PureMath, AxiomProfile::NONE)]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let cert = NNVerificationCert {
            network_spec: 0,
            property: 0,
            proof: 0,
            source_tool: SourceSystem::GammaCrown,
            method: VerificationMethod::BoundPropagation,
            axiom_profile: AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
        };

        let idx = lib.submit_nn_certificate(cert).unwrap();
        let header = lib.get_constant(idx).unwrap();
        assert_eq!(header.content_domain, ContentDomain::NnVerification as u8);
        assert_eq!(header.source_system, SourceSystem::GammaCrown as u8);
        assert!(header.is_trust_gated(), "NN cert should be trust-gated");
    }

    // -----------------------------------------------------------------------
    // Kernel type-checking integration tests for verify_foreign
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_foreign_with_valid_flatdb_axiom() {
        use clean_kernel::expr::Expr;
        use clean_kernel::flat::FlatBuilder;
        use clean_kernel::level::Level;

        // Build a valid FlatDb containing Prop (Sort(0)) as the statement.
        let prop = Expr::sort(Level::zero());
        let mut builder = FlatBuilder::new();
        let _idx = builder.add_kernel_expr(&prop).unwrap();
        let mut stmt_bytes = Vec::new();
        builder.write_to(&mut stmt_bytes).unwrap();

        // The proof bytes are invalid (not a FlatDb), so only statement parses.
        // The statement is `Prop` which is a valid type, so kernel accepts it as axiom.
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let shard = build_test_shard(&[("seed", ContentDomain::PureMath, AxiomProfile::NONE)]);
        lib.load_shard(&shard).unwrap();

        let result = lib
            .verify_foreign(ProofFormat::OLean, &stmt_bytes, b"invalid_proof")
            .unwrap();
        assert!(result.constant_idx.is_some());
        assert_eq!(result.source, SourceSystem::Lean4);
        // Statement parsed and type-checked as axiom: Translated confidence.
        assert_eq!(result.confidence, ImportConfidence::Translated);
        assert_eq!(result.status, VerificationStatus::Verified);
    }

    #[test]
    fn test_verify_foreign_with_valid_flatdb_theorem() {
        use clean_kernel::expr::{BinderInfo, Expr};
        use clean_kernel::flat::FlatBuilder;
        use clean_kernel::level::Level;

        // Build a theorem: type is `Prop → Prop` (which lives in Sort 1, not Prop),
        // but actually we need a proposition. Let's use `True → True` pattern
        // where True : Prop.
        //
        // For a simpler test: type = Prop, proof = Prop (this won't type-check
        // as a theorem because Prop : Type, not Prop).
        //
        // Use the simplest thing that CAN type-check as a theorem:
        // A proposition whose proof is trivial is hard to construct in raw Expr.
        // Instead, test the fallback: statement is valid Prop type, proof doesn't
        // type-check → should get Translated confidence.
        let prop = Expr::sort(Level::zero()); // Prop : Type

        let mut stmt_builder = FlatBuilder::new();
        let _idx = stmt_builder.add_kernel_expr(&prop).unwrap();
        let mut stmt_bytes = Vec::new();
        stmt_builder.write_to(&mut stmt_bytes).unwrap();

        // Build a proof that is also Prop (will fail type-check since
        // Prop : Sort 1, not Prop itself).
        let mut proof_builder = FlatBuilder::new();
        let _idx = proof_builder.add_kernel_expr(&prop).unwrap();
        let mut proof_bytes = Vec::new();
        proof_builder.write_to(&mut proof_bytes).unwrap();

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let shard = build_test_shard(&[("seed", ContentDomain::PureMath, AxiomProfile::NONE)]);
        lib.load_shard(&shard).unwrap();

        let result = lib
            .verify_foreign(ProofFormat::OLean, &stmt_bytes, &proof_bytes)
            .unwrap();
        // Both parse but theorem type-check fails (Prop is Type, not Prop).
        // Falls back to axiom path: statement is valid type.
        assert!(result.constant_idx.is_some());
        assert_eq!(result.confidence, ImportConfidence::Translated);
        assert!(
            matches!(result.status, VerificationStatus::Failed(_)),
            "Should report type-check failure"
        );
    }

    #[test]
    fn test_verify_foreign_invalid_flatdb_bytes_rejected() {
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let shard = build_test_shard(&[("seed", ContentDomain::PureMath, AxiomProfile::NONE)]);
        lib.load_shard(&shard).unwrap();
        let result = lib
            .verify_foreign(ProofFormat::MetamathMm, b"raw_statement", b"raw_proof")
            .unwrap();
        assert!(result.constant_idx.is_some());
        assert_eq!(result.confidence, ImportConfidence::Unverified);
        assert!(matches!(result.status, VerificationStatus::Failed(_)));
    }

    #[test]
    fn test_load_shard_unknown_expr_tag_returns_error() {
        let mut shard =
            build_test_shard(&[("Test.corrupt", ContentDomain::PureMath, AxiomProfile::NONE)]);
        // Corrupt the tag of the first expression to an invalid value
        assert!(
            !shard.exprs.is_empty(),
            "shard should have at least one expression"
        );
        shard.exprs[0].tag = 200; // invalid tag

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let result = lib.load_shard(&shard);
        assert!(
            result.is_err(),
            "load_shard should fail on unknown expr tag"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("unknown expression tag 200"),
            "error should mention the unknown tag, got: {err_msg}"
        );
    }

    #[test]
    fn test_load_shard_unknown_level_tag_returns_error() {
        // Regression test for #3414: library.rs::remap_level previously silently
        // mapped unknown level tags to FlatLevel::zero(), causing silent data
        // corruption. It must now return MathverseError::UnknownLevelTag.
        let mut shard = build_test_shard(&[(
            "Test.corrupt_level",
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        )]);
        // Corrupt the tag of the first level to an invalid value (valid: 0..=4)
        assert!(
            !shard.levels.is_empty(),
            "shard should have at least one level"
        );
        shard.levels[0].tag = 201;

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        let result = lib.load_shard(&shard);
        assert!(
            result.is_err(),
            "load_shard should fail on unknown level tag"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("unknown level tag 201"),
            "error should mention the unknown level tag, got: {err_msg}"
        );
    }

    /// Helper: write a tiny shard with the given (name, confidence) pairs to a
    /// freshly-created `.mathverse` file under `dir`.
    fn write_unstamped_shard(dir: &std::path::Path, names: &[(&str, ImportConfidence)]) {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let ty = writer.add_expr(FlatExpr::sort(l0));
        for &(name, conf) in names {
            let ni = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: ty,
                value_idx: ty,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: conf as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        writer
            .write_to_file(dir.join("tiny.mathverse"))
            .expect("write tiny shard to disk");
    }

    #[test]
    fn test_stamp_shard_dir_from_manifest_raises_only_named() {
        use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

        let dir = tempfile::tempdir().expect("tempdir");
        // Two constants, both starting below KernelVerified so a stamp is an
        // observable 0 -> N transition.
        write_unstamped_shard(
            dir.path(),
            &[
                ("In.Manifest", ImportConfidence::SourceVerified),
                ("Not.In.Manifest", ImportConfidence::SourceVerified),
            ],
        );

        // Nothing is stored as KernelVerified before stamping.
        let (before, unreadable) = count_stored_kernel_verified(dir.path()).expect("count before");
        assert!(
            unreadable.is_empty(),
            "no unreadable shards: {unreadable:?}"
        );
        assert_eq!(before, 0, "no headers stamped before applying the manifest");

        // Manifest names ONLY the first constant — exactly the kernel's verdict
        // set. The second is absent and must stay un-stamped.
        let manifest = KernelVerifiedManifest::from_worker_parts(
            "tiny.module",
            2,
            0,
            0,
            0.0,
            vec!["In.Manifest".to_string()],
        );

        let stamp = stamp_shard_dir_kernel_verified(dir.path(), &manifest).expect("stamp dir");
        assert_eq!(stamp.shards_rewritten, 1, "the one shard was rewritten");
        assert_eq!(stamp.constants_stamped, 1, "exactly one header raised");

        // The persisted count a `stats` reader sees has risen from 0 to 1.
        let (after, _) = count_stored_kernel_verified(dir.path()).expect("count after");
        assert_eq!(after, 1, "stored KernelVerified rose 0 -> 1");

        // SOUNDNESS: the constant absent from the manifest stays below
        // KernelVerified; no heuristic promotion occurred.
        let reader = ShardReader::from_file(dir.path().join("tiny.mathverse"))
            .expect("re-read stamped shard");
        let conf_of =
            |n: &str| -> u8 { reader.lookup_name(n).expect("present").1.import_confidence };
        assert_eq!(
            conf_of("In.Manifest"),
            ImportConfidence::KernelVerified as u8,
            "the manifest-named constant reads KernelVerified from disk"
        );
        assert_eq!(
            conf_of("Not.In.Manifest"),
            ImportConfidence::SourceVerified as u8,
            "the unnamed constant is left untouched"
        );
    }
}
