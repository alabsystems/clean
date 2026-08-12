// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Framework-agnostic JSON payload builders for the Mathverse Cloud Run
//! distribution front-end (`mathverse_serve`).
//!
//! This module is the single point of reuse between the HTTP binary and the
//! existing library surface: it loads a Core directory once
//! ([`load_built_library`]), then answers the read-only browse / search /
//! describe queries by delegating to [`crate::search`], [`crate::stats`]'s
//! display helpers, and [`crate::shard_reconstruct`]. It builds
//! [`serde_json::Value`] payloads — the HTTP layer only serializes and routes,
//! it owns no library knowledge.
//!
//! ## Trust posture (Phase-1 contract)
//!
//! The service is a **distribution front-end, NOT a trust authority**. Every
//! payload surfaces the *stored* import-confidence label plus the content
//! digest so a consumer can re-verify independently (de Bruijn). Nothing here
//! mints, upgrades, or alters a verdict; `/stats` and `/theorem` carry an
//! explicit note distinguishing the one independently-re-verifiable tier
//! (`KernelVerified`, digest-backed) from the self-attested import tiers.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

use crate::build_library::load_built_library;
use crate::error::MathverseResult;
use crate::graduate::BaselineIndex;
use crate::library::MathverseLibrary;
use crate::manifest::LibraryLoader;
use crate::mathverse_bin_cmds::fmt::{confidence_display, domain_display, source_system_display};
use crate::search::MathverseSearch;
use crate::types::AxiomProfile;

/// Honest one-line trust note attached to every trust-bearing payload.
///
/// Stated once, surfaced everywhere a confidence label is reported, so a
/// consumer never reads a label without the caveat that the service is a
/// distribution front-end and the label is the *stored* import verdict.
pub const TRUST_NOTE: &str =
    "Trust labels are the STORED import verdict, not a re-verification by \
     this service. This endpoint is a distribution front-end, not a trust \
     authority. KernelVerified is the only independently re-verifiable tier: \
     re-run the Clean kernel over the shard constant whose `expr_canonical_digest` \
     is served here (de Bruijn). All other tiers are source/import self-attested.";

/// A loaded Core plus the on-disk directory it was loaded from.
///
/// Built once at startup and shared (read-only) across request handlers. The
/// directory is retained so `/shards` and `/download` can resolve shard files
/// and report their on-disk sizes without reloading.
pub struct CoreHandle {
    library: MathverseLibrary,
    core_dir: PathBuf,
    /// The shipped `baseline.mvix` (MVBIDX01) index, when present. Its semantic
    /// table powers `/equivalent/{name}`'s microsecond corpus-wide
    /// structural-equivalence lookup. `None` (or a v1 index with no semantic
    /// table) disables that fast path; the endpoint then reports the digest only.
    baseline: Option<BaselineIndex>,
}

impl CoreHandle {
    /// Load the Core at `core_dir` (a [`LibraryLoader`] layout: `manifest.json`
    /// plus `base/` / `delta/` shards, optionally a `baseline.mvix`).
    ///
    /// # Errors
    /// Propagates any shard-read / manifest / index failure from
    /// [`load_built_library`].
    pub fn load(core_dir: impl AsRef<Path>) -> MathverseResult<Self> {
        let core_dir = core_dir.as_ref().to_path_buf();
        let library = load_built_library(&core_dir)?;
        // Open the shipped baseline index if present. Fail-soft: a missing or
        // unreadable index just disables the microsecond structural lookup (the
        // service stays a distribution front-end, the index is an accelerator).
        let index_path = core_dir.join(crate::release::BASELINE_INDEX_FILENAME);
        let baseline = if index_path.is_file() {
            BaselineIndex::load(&index_path).ok()
        } else {
            None
        };
        Ok(Self {
            library,
            core_dir,
            baseline,
        })
    }

    /// The underlying read-only library.
    #[must_use]
    pub fn library(&self) -> &MathverseLibrary {
        &self.library
    }

    /// The Core directory this handle was loaded from.
    #[must_use]
    pub fn core_dir(&self) -> &Path {
        &self.core_dir
    }

    /// Total declaration count across all loaded shards.
    #[must_use]
    pub fn constant_count(&self) -> usize {
        self.library.constant_count()
    }

    // -- /stats ------------------------------------------------------------

    /// Corpus statistics: total declarations, shard count, and per-trust /
    /// per-domain / per-system breakdowns, plus the honest trust note.
    ///
    /// Mirrors the `mathverse stats` command's tally (one pass over every
    /// constant header) so the counts match the CLI exactly.
    #[must_use]
    pub fn stats_json(&self) -> Value {
        let count = self.library.constant_count();
        let mut by_system: HashMap<u8, usize> = HashMap::new();
        let mut by_trust: HashMap<u8, usize> = HashMap::new();
        let mut by_domain: HashMap<u8, usize> = HashMap::new();
        let mut with_value = 0usize;
        let mut trust_gated = 0usize;

        for idx in 0..count as u32 {
            if let Some(h) = self.library.get_constant(idx) {
                *by_system.entry(h.source_system).or_default() += 1;
                *by_trust.entry(h.import_confidence).or_default() += 1;
                *by_domain.entry(h.content_domain).or_default() += 1;
                if h.has_value() {
                    with_value += 1;
                }
                if h.is_trust_gated() {
                    trust_gated += 1;
                }
            }
        }

        let kernel_verified = *by_trust.get(&0).unwrap_or(&0);
        let trust_map = display_count_map(&by_trust, confidence_display);
        let domain_map = display_count_map(&by_domain, domain_display);
        let system_map = display_count_map(&by_system, source_system_display);

        let shard_count = self
            .load_manifest()
            .map(|m| m.base_shards.len() + m.delta_shards.len())
            .unwrap_or(0);

        json!({
            "total_declarations": count,
            "shard_count": shard_count,
            "with_proof_term": with_value,
            "trust_gated": trust_gated,
            "by_trust_level": trust_map,
            "by_domain": domain_map,
            "by_source_system": system_map,
            "independently_reverifiable": {
                // The only tier a consumer can re-derive from the served
                // digest. Everything else is import/source self-attested.
                "tier": "KernelVerified",
                "count": kernel_verified,
                "self_attested": count - kernel_verified,
            },
            "trust_note": TRUST_NOTE,
        })
    }

    // -- /search -----------------------------------------------------------

    /// Name / type / axiom / domain search over the loaded shards.
    ///
    /// `q` is a case-insensitive substring name query (same matcher as the
    /// `mathverse search` CLI). Optional filters: `type_query` (prefix of the
    /// canonical type digest), `axiom` (named axiom bit), `domain`
    /// (content-domain name). Returns at most `limit` hits.
    #[must_use]
    pub fn search_json(&self, params: &SearchParams) -> Value {
        let count = self.library.constant_count();
        let q_lower = params.q.to_lowercase();
        let axiom_bit = params.axiom.as_deref().and_then(named_axiom_bit);
        let domain_id = params.domain.as_deref().and_then(parse_domain);
        let type_lower = params.type_query.as_ref().map(|t| t.to_lowercase());

        let mut hits = Vec::new();
        for idx in 0..count as u32 {
            if hits.len() >= params.limit {
                break;
            }
            let Some(name) = self.library.get_name(idx) else {
                continue;
            };
            if !params.q.is_empty() && !name.to_lowercase().contains(&q_lower) {
                continue;
            }
            let Some(h) = self.library.get_constant(idx) else {
                continue;
            };
            if let Some(bit) = axiom_bit {
                if !h.axiom_profile.has(bit) {
                    continue;
                }
            }
            if let Some(d) = domain_id {
                if h.content_domain != d {
                    continue;
                }
            }
            if let Some(ref tq) = type_lower {
                // Type filter is a substring match over the reconstructed type's
                // canonical digest hex OR a name-token match; we keep it honest
                // and cheap by matching the digest prefix the consumer would pin.
                let digest = self.type_digest(idx).unwrap_or_default();
                if !digest.starts_with(tq.as_str()) {
                    continue;
                }
            }
            hits.push(json!({
                "name": name,
                "trust_level": confidence_display(h.import_confidence),
                "source_system": source_system_display(h.source_system),
                "domain": domain_display(h.content_domain),
                "shard": self.shard_of(name),
                "expr_canonical_digest": self.type_digest(idx),
                "has_proof_term": h.has_value(),
                "axiom_count": h.axiom_profile.axiom_count(),
            }));
        }

        json!({
            "query": params.q,
            "count": hits.len(),
            "results": hits,
            "trust_note": TRUST_NOTE,
        })
    }

    // -- /theorem/{name} ---------------------------------------------------

    /// Full honest description of one declaration, or `None` if absent.
    #[must_use]
    pub fn theorem_json(&self, name: &str) -> Option<Value> {
        let idx = self.find_by_name(name)?;
        let h = self.library.get_constant(idx)?;

        let foundational = is_foundational(h.axiom_profile);
        let axiom_names = named_axioms(h.axiom_profile);
        let dep_count = self
            .library
            .deps()
            .get(idx as usize)
            .map(Vec::len)
            .unwrap_or(0);

        let mut obj = json!({
            "name": name,
            "trust_level": confidence_display(h.import_confidence),
            "source_system": source_system_display(h.source_system),
            "domain": domain_display(h.content_domain),
            "decl_kind": h.decl_kind().map(|k| format!("{k:?}")).unwrap_or_else(|raw| format!("Unknown({raw})")),
            "has_proof_term": h.has_value(),
            "expr_canonical_digest": self.type_digest(idx),
            "axiom_profile": {
                "foundational": foundational,
                "axiom_count": h.axiom_profile.axiom_count(),
                "bits": format!("{:#018x}", u64::from(h.axiom_profile)),
                "named_axioms": axiom_names,
                "trust_gated": h.axiom_profile.is_trust_gated(),
            },
            "dependency_count": dep_count,
            "reverify_hint": "Re-run the Clean kernel over the shard constant matching expr_canonical_digest to independently confirm this label.",
            "trust_note": TRUST_NOTE,
        });

        if let Some(record) = self.library.provenance().get(h.provenance_idx) {
            obj["provenance"] = json!({
                "original_name": record.original_name,
                "source_file": record.source_file,
                "source_line": record.source_line,
                "source_version": record.source_version,
                "module_path": record.module_path,
                "pipeline_version": record.pipeline_version,
                "notes": record.notes,
            });
        }
        Some(obj)
    }

    // -- /rdeps/{name} (a.k.a. /uses/{name}) -------------------------------

    /// Reverse-dependency search: the declarations in the loaded Core that
    /// (transitively) depend on `name` — its users / blast radius. `None` if
    /// the name is absent.
    ///
    /// Mirrors the `mathverse deps --reverse` / `uses` CLI verb. `transitive`
    /// follows the reverse adjacency past the direct users (bounded by `depth`);
    /// otherwise only direct users are returned. `limit` caps the hits. Each
    /// dependent carries its own `used_by_count` (in-degree), and hits are
    /// ranked by that impact metric so the most-reused users surface first.
    #[must_use]
    pub fn rdeps_json(
        &self,
        name: &str,
        transitive: bool,
        depth: usize,
        limit: usize,
    ) -> Option<Value> {
        let idx = self.library.lookup_constant_idx(name)?;
        let hits = self
            .library
            .reverse_deps_bounded(idx, transitive, depth, limit);
        let dependents: Vec<Value> = hits
            .iter()
            .map(|&(i, d)| {
                let dep_name = self.library.get_name(i).unwrap_or("?");
                let header = self.library.get_constant(i);
                json!({
                    "name": dep_name,
                    "depth": d,
                    "used_by_count": self.library.reverse_in_degree(i),
                    "source_system": header
                        .map(|h| source_system_display(h.source_system)),
                    "trust_level": header.map(|h| confidence_display(h.import_confidence)),
                })
            })
            .collect();
        Some(json!({
            "root": name,
            "direct_user_count": self.library.reverse_in_degree(idx),
            "count": dependents.len(),
            "transitive": transitive,
            "depth": depth,
            "dependents": dependents,
            "note": "Reverse dependencies: declarations in the loaded Core that \
                     (transitively) depend on `root`. Ranked by each dependent's \
                     own in-degree (impact); bounded by depth/limit. Computed over \
                     the load-time dependency adjacency.",
            "trust_note": TRUST_NOTE,
        }))
    }

    // -- /type?like= -------------------------------------------------------

    /// Type-directed search: declarations whose type structurally
    /// matches/unifies (via the discrimination tree) the type of the reference
    /// declaration `like`. `None` if `like` is absent from the loaded Core.
    ///
    /// Mirrors the `mathverse search --mode type --like` CLI verb: the query
    /// type is the reference declaration's already-interned `ExprIdx`, so no
    /// parser/elaborator is involved. The anchor itself is excluded; hits are
    /// ranked by import confidence then name for a deterministic response.
    #[must_use]
    pub fn type_search_json(&self, like: &str, limit: usize) -> Option<Value> {
        let anchor = self
            .library
            .lookup_constant_idx(like)
            .or_else(|| self.library.resolve_name_loose(like))?;
        let type_idx = self.library.get_constant(anchor)?.type_idx;
        let anchor_name = self.library.get_name(anchor).unwrap_or(like).to_string();

        let pool = limit.saturating_mul(8).max(64);
        let mut hits = self.library.search_type(type_idx, pool).ok()?;
        hits.sort_by(|a, b| {
            b.header
                .import_confidence
                .cmp(&a.header.import_confidence)
                .then_with(|| {
                    self.library
                        .get_name(a.constant_idx)
                        .unwrap_or("")
                        .cmp(self.library.get_name(b.constant_idx).unwrap_or(""))
                })
        });
        let results: Vec<Value> = hits
            .into_iter()
            .filter(|sr| sr.constant_idx != anchor)
            .filter_map(|sr| {
                let name = self.library.get_name(sr.constant_idx)?;
                Some(json!({
                    "name": name,
                    "trust_level": confidence_display(sr.header.import_confidence),
                    "source_system": source_system_display(sr.header.source_system),
                    "domain": domain_display(sr.header.content_domain),
                    "has_proof_term": sr.header.has_value(),
                }))
            })
            .take(limit)
            .collect();
        Some(json!({
            "anchor": anchor_name,
            "count": results.len(),
            "results": results,
            "note": "Type-directed search: declarations whose type matches the \
                     anchor's via the discrimination tree (structural, not lexical). \
                     Excludes the anchor; ranked by import confidence then name.",
            "trust_note": TRUST_NOTE,
        }))
    }

    // -- /equivalent/{name} ------------------------------------------------

    /// Structural-equivalence lookup: is `name`'s statement already in the
    /// corpus, differently stated (equal up to commutative-operand rewrite)?
    /// `None` if `name` is absent or its type cannot be reconstructed.
    ///
    /// Computes `name`'s rewrite-canonical digest and, when a `baseline.mvix`
    /// semantic table is loaded, looks up the corpus-wide canonical
    /// representative in microseconds — the dedup / premise-selection probe the
    /// graduation novelty gate uses. A hit is a candidate match (commutative
    /// rewrite), NOT a kernel identity; `same_object` remains the arbiter.
    #[must_use]
    pub fn equivalent_json(&self, name: &str) -> Option<Value> {
        let idx = self
            .library
            .lookup_constant_idx(name)
            .or_else(|| self.library.resolve_name_loose(name))?;
        let anchor_name = self.library.get_name(idx).unwrap_or(name).to_string();
        let digest = self.library.structural_rewrite_digest_of(idx)?;

        let (representative, index_available) = match &self.baseline {
            Some(index) => (index.lookup_semantic(&digest).map(str::to_string), true),
            None => (None, false),
        };
        let note = if index_available {
            "Structural equivalence is equality up to commutative-operand rewrite \
             (a candidate match, not a kernel identity). `representative` is the \
             corpus-wide canonical name from the baseline.mvix semantic table, \
             looked up in microseconds. `same_object` remains the arbiter for a \
             confirmed identity."
        } else {
            "No baseline.mvix semantic table is loaded, so only the query's \
             rewrite-canonical digest is reported. Ship a baseline.mvix with the \
             Core to enable the microsecond corpus-wide representative lookup."
        };
        Some(json!({
            "anchor": anchor_name,
            "rewrite_canonical_digest": digest,
            "representative": representative,
            "already_in_corpus": representative.is_some(),
            "index_available": index_available,
            "note": note,
            "trust_note": TRUST_NOTE,
        }))
    }

    // -- /shards -----------------------------------------------------------

    /// List every shard with its declaration count and on-disk size.
    #[must_use]
    pub fn shards_json(&self) -> Value {
        let Ok(manifest) = self.load_manifest() else {
            return json!({ "shards": [], "shard_count": 0 });
        };
        let mut shards = Vec::new();
        for entry in manifest.all_shards() {
            let abs = self.core_dir.join(&entry.path);
            let size_bytes = std::fs::metadata(&abs).map(|m| m.len()).ok();
            // The download key is the shard file stem (e.g. `lean4_000`), which
            // `/download/{shard}` resolves back to this manifest path.
            let shard_key = shard_stem(&entry.path);
            shards.push(json!({
                "shard": shard_key,
                "path": entry.path,
                "declaration_count": entry.constant_count,
                "expr_count": entry.expr_count,
                "source": entry.source,
                "content_hash": entry.content_hash,
                "size_bytes": size_bytes,
            }));
        }
        json!({
            "shard_count": shards.len(),
            "total_declarations": manifest.total_constants,
            "shards": shards,
        })
    }

    /// The release manifest (`mathverse-manifest.json` shape) describing every
    /// shard with its blake3 digest, so a server-download client can fetch it
    /// and re-verify the corpus it pulls (the `GET /manifest` route).
    ///
    /// Prefers the on-disk `mathverse-manifest.json` shipped with the Core
    /// (returned verbatim — it carries the exact `release_version`,
    /// `created_at`, and `baseline_index` the release was packaged with). When
    /// absent (a Core whose only manifest is the in-place `manifest.json`), a
    /// release manifest is synthesized from the loader manifest: each shard's
    /// `content_hash` IS the blake3-over-file-bytes digest, so the synthesized
    /// digests match what `verify_release` re-checks. No bytes are re-hashed.
    #[must_use]
    pub fn release_manifest_json(&self) -> Value {
        let on_disk = self
            .core_dir
            .join(crate::manifest::RELEASE_MANIFEST_FILENAME);
        if on_disk.is_file() {
            if let Ok(text) = std::fs::read_to_string(&on_disk) {
                if let Ok(value) = serde_json::from_str::<Value>(&text) {
                    return value;
                }
            }
        }
        // Synthesize from the loader manifest without re-hashing any shard.
        let Ok(manifest) = self.load_manifest() else {
            return json!({ "shards": [], "total_shards": 0, "total_bytes": 0 });
        };
        let mut shards = Vec::new();
        let mut total_bytes: u64 = 0;
        for entry in manifest.all_shards() {
            let abs = self.core_dir.join(&entry.path);
            let size = std::fs::metadata(&abs).map(|m| m.len()).unwrap_or(0);
            total_bytes += size;
            shards.push(json!({
                "path": entry.path,
                "size": size,
                "blake3": entry.content_hash,
            }));
        }
        let baseline = self.core_dir.join(crate::release::BASELINE_INDEX_FILENAME);
        let baseline_index = baseline
            .is_file()
            .then(|| crate::release::BASELINE_INDEX_FILENAME.to_string());
        json!({
            "manifest_version": 1,
            "release_version": "unknown",
            "created_at": "unknown",
            "total_shards": shards.len(),
            "total_bytes": total_bytes,
            "baseline_index": baseline_index,
            "shards": shards,
        })
    }

    /// Resolve a `/download/{shard}` key to its absolute shard file path, if it
    /// exists in the manifest and on disk. Returns `None` for unknown keys so
    /// the HTTP layer can answer 404 without leaking the filesystem layout.
    #[must_use]
    pub fn resolve_shard_path(&self, shard_key: &str) -> Option<PathBuf> {
        let manifest = self.load_manifest().ok()?;
        for entry in manifest.all_shards() {
            if shard_stem(&entry.path) == shard_key {
                let abs = self.core_dir.join(&entry.path);
                if abs.is_file() {
                    return Some(abs);
                }
            }
        }
        None
    }

    /// The relative manifest path for a `/download/{shard}` key, used to build a
    /// `$MATHVERSE_DOWNLOAD_BASE` redirect URL.
    #[must_use]
    pub fn shard_rel_path(&self, shard_key: &str) -> Option<String> {
        let manifest = self.load_manifest().ok()?;
        manifest
            .all_shards()
            .into_iter()
            .find(|e| shard_stem(&e.path) == shard_key)
            .map(|e| e.path.clone())
    }

    // -- internals ---------------------------------------------------------

    fn load_manifest(&self) -> MathverseResult<crate::manifest::MathverseManifest> {
        LibraryLoader::new(self.core_dir.clone()).load_manifest()
    }

    fn find_by_name(&self, name: &str) -> Option<u32> {
        let count = self.library.constant_count();
        (0..count as u32).find(|&idx| self.library.get_name(idx) == Some(name))
    }

    /// `expr_canonical_digest` of the declaration's *type*, reconstructed from
    /// the merged arena. `None` if the type is beyond the reconstructable
    /// prefix (mode-extension exprs) or the digest flatten fails.
    fn type_digest(&self, idx: u32) -> Option<String> {
        let h = self.library.get_constant(idx)?;
        let expr = crate::shard_reconstruct::reconstruct_from_shard_with_level_lists(
            self.library.exprs(),
            self.library.levels(),
            self.library.strings(),
            self.library.level_lists(),
            h.type_idx,
        )
        .ok()?;
        crate::graduate::record::expr_canonical_digest(&expr).ok()
    }

    /// Best-effort shard key for a constant: scans the manifest shards for the
    /// one whose name index contains this name. The merged library loses the
    /// per-constant shard origin, so this re-reads shard readers lazily. Kept
    /// honest: returns `None` when not pinpointable rather than guessing.
    fn shard_of(&self, name: &str) -> Option<String> {
        let manifest = self.load_manifest().ok()?;
        for entry in manifest.all_shards() {
            let abs = self.core_dir.join(&entry.path);
            if let Ok(reader) = crate::shard::ShardReader::from_file(&abs) {
                if reader.lookup_name(name).is_some() {
                    return Some(shard_stem(&entry.path));
                }
            }
        }
        None
    }
}

/// Parsed query parameters for [`CoreHandle::search_json`].
#[derive(Clone, Debug, Default)]
pub struct SearchParams {
    /// Case-insensitive substring name query (empty = match all).
    pub q: String,
    /// Optional type filter: matched as a prefix of the canonical type digest.
    pub type_query: Option<String>,
    /// Optional named-axiom filter (e.g. `CHOICE`, `PROP_EXT`).
    pub axiom: Option<String>,
    /// Optional content-domain filter (e.g. `PureMath`, `NnVerification`).
    pub domain: Option<String>,
    /// Maximum number of results.
    pub limit: usize,
}

impl SearchParams {
    /// Default result cap when a request omits `limit`.
    pub const DEFAULT_LIMIT: usize = 50;
    /// Hard ceiling so a pathological `limit` cannot scan-and-emit the whole
    /// corpus in one response.
    pub const MAX_LIMIT: usize = 1000;
}

/// Map a `u8 -> count` tally through a display function into a JSON object.
fn display_count_map(map: &HashMap<u8, usize>, display: fn(u8) -> &'static str) -> Value {
    let obj: serde_json::Map<String, Value> = map
        .iter()
        .map(|(&id, &n)| (display(id).to_string(), json!(n)))
        .collect();
    Value::Object(obj)
}

/// The file stem of a manifest shard path (`base/lean4_000.mathverse` ->
/// `lean4_000`), used as the stable `/download/{shard}` key.
fn shard_stem(path: &str) -> String {
    Path::new(path)
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| path.to_string())
}

/// Whether an axiom profile is within Clean's foundational closure (the only
/// axioms a `KernelVerified`-grade proof may carry: propext / Quot.sound /
/// Classical.choice + the funext/LEM/quot family Clean treats as foundational).
fn is_foundational(profile: AxiomProfile) -> bool {
    const FOUNDATIONAL: u64 = AxiomProfile::CHOICE.0
        | AxiomProfile::LEM.0
        | AxiomProfile::PROP_EXT.0
        | AxiomProfile::FUNC_EXT.0
        | AxiomProfile::QUOT.0;
    let bits = u64::from(profile);
    bits & !FOUNDATIONAL == 0
}

/// Human-readable names for every axiom bit set in a profile.
fn named_axioms(profile: AxiomProfile) -> Vec<&'static str> {
    const TABLE: &[(AxiomProfile, &str)] = &[
        (AxiomProfile::CHOICE, "CHOICE"),
        (AxiomProfile::LEM, "LEM"),
        (AxiomProfile::PROP_EXT, "PROP_EXT"),
        (AxiomProfile::FUNC_EXT, "FUNC_EXT"),
        (AxiomProfile::QUOT, "QUOT"),
        (AxiomProfile::UNIVALENCE, "UNIVALENCE"),
        (AxiomProfile::LARGE_ELIM, "LARGE_ELIM"),
        (AxiomProfile::HOL_AXIOMS, "HOL_AXIOMS"),
        (AxiomProfile::MIZAR_TG, "MIZAR_TG"),
        (AxiomProfile::UNIVERSE_INCON, "UNIVERSE_INCON"),
        (AxiomProfile::AXIOMATIZED, "AXIOMATIZED"),
        (AxiomProfile::BRIDGE_AXIOM, "BRIDGE_AXIOM"),
        (AxiomProfile::REAL_AXIOMS, "REAL_AXIOMS"),
        (AxiomProfile::LRA_TRUSTED, "LRA_TRUSTED"),
        (AxiomProfile::FLOAT_APPROX, "FLOAT_APPROX"),
        (AxiomProfile::NN_ABSTRACTION, "NN_ABSTRACTION"),
        (AxiomProfile::COQ_SPROP, "COQ_SPROP"),
        (AxiomProfile::COQ_MODULE_FUNCTOR, "COQ_MODULE_FUNCTOR"),
        (AxiomProfile::COQ_COINDUCTIVE, "COQ_COINDUCTIVE"),
        (AxiomProfile::ISABELLE_LCF_ERASED, "ISABELLE_LCF_ERASED"),
        (AxiomProfile::AGDA_CUBICAL, "AGDA_CUBICAL"),
        (AxiomProfile::IDRIS_QTT, "IDRIS_QTT"),
        (AxiomProfile::SMT_ORACLE, "SMT_ORACLE"),
        (AxiomProfile::SAT_CERT, "SAT_CERT"),
        (AxiomProfile::ATP_CERT, "ATP_CERT"),
        (AxiomProfile::ARXIV_NL_IMPORT, "ARXIV_NL_IMPORT"),
    ];
    TABLE
        .iter()
        .filter(|(bit, _)| profile.has(*bit))
        .map(|(_, name)| *name)
        .collect()
}

/// Parse a named-axiom filter string to its profile bit.
fn named_axiom_bit(name: &str) -> Option<AxiomProfile> {
    let upper = name.to_uppercase();
    match upper.as_str() {
        "CHOICE" | "CLASSICAL" => Some(AxiomProfile::CHOICE),
        "LEM" => Some(AxiomProfile::LEM),
        "PROP_EXT" | "PROPEXT" => Some(AxiomProfile::PROP_EXT),
        "FUNC_EXT" | "FUNEXT" => Some(AxiomProfile::FUNC_EXT),
        "QUOT" => Some(AxiomProfile::QUOT),
        "REAL_AXIOMS" | "REAL" => Some(AxiomProfile::REAL_AXIOMS),
        "SMT_ORACLE" | "SMT" => Some(AxiomProfile::SMT_ORACLE),
        "FLOAT_APPROX" | "FLOAT" => Some(AxiomProfile::FLOAT_APPROX),
        "NN_ABSTRACTION" | "NN" => Some(AxiomProfile::NN_ABSTRACTION),
        "AXIOMATIZED" => Some(AxiomProfile::AXIOMATIZED),
        _ => None,
    }
}

/// Parse a content-domain filter string to its stored byte id.
fn parse_domain(name: &str) -> Option<u8> {
    if let Ok(n) = name.parse::<u8>() {
        return Some(n);
    }
    match name.to_lowercase().as_str() {
        "puremath" | "pure" | "math" => Some(0),
        "software" => Some(1),
        "complexity" => Some(2),
        "nnverification" | "nn" => Some(3),
        "physics" => Some(4),
        "logic" => Some(5),
        "cryptography" | "crypto" => Some(6),
        _ => None,
    }
}
