// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-confirmed tree-score / unique-indexing over the KERNEL-VERIFIED corpus.
//!
//! The persistent [`MVBIDX01`](super::baseline_index) index keys its semantic
//! table on the **fast, env-free** Tier-1.5 digest
//! ([`clean_cake::identity::structural_rewrite_digest`]): it scales to the whole
//! 5.77M release because it needs no `TypeChecker`. For the (much smaller) slice
//! of constants that carry a `KernelVerified` stamp we can compute a *stronger*,
//! **kernel-confirmed** tree-signature: the Tier-1
//! [`defeq_canonical_digest`](clean_cake::identity::defeq_canonical_digest) — the
//! statement type reduced to a head/▸children normal form by the kernel
//! (`whnf`: β, η, δ on reducibles, ι, ζ, proj) under a fuel bound, then the
//! commutative-operand canonical-rewrite digest on top of that.
//!
//! ## What this surfaces
//!
//! "Same object, different form" *across* the verified batch: two distinct
//! declarations whose types share the kernel-confirmed semantic tree-signature
//! (`rewrite_digest`) but differ structurally (`structural_digest`). Such a pair
//! is a **uniqueness/dedup candidate** — the corpus stores the same proposition
//! twice under two encodings.
//!
//! ## Soundness — the digest is a bucketing key, NEVER a sameness claim
//!
//! A shared semantic tree-signature means *candidate same*, nothing more.
//! Every candidate pair this module reports as a hit is then **confirmed by the
//! kernel**: [`clean_kernel::tc::TypeChecker::is_def_eq`] (Cake's `same_object`
//! arbiter) is run on the two reconstructed types, and the pair is only recorded
//! as `same_object = true` when the kernel agrees. The `TypeChecker` is built
//! over the env produced by
//! [`verify_corpus_incremental_with_env`](crate::verify::incremental::verify_corpus_incremental_with_env)
//! (prelude + the kernel-trusted replay of the corpus), so `is_def_eq` can
//! δ-unfold corpus-defined and prelude constants. The bounded `whnf` makes the
//! digest *miss* possible (recorded as `complete = false`) — a miss is "unknown",
//! never "distinct" — but it can never falsely merge two genuinely different
//! objects, because the kernel decision, not the hash, is the verdict.
//!
//! This module reads shards and stamps; it never writes them and never alters a
//! `KernelVerified` verdict or a stamp. It only considers constants already
//! stamped at the requested confidence floor.

use std::collections::BTreeMap;
use std::path::Path;

use clean_cake::identity::{defeq_canonical_digest_fueled, structural_rewrite_digest};
use clean_kernel::tc::TypeChecker;
use clean_kernel::{Environment, Expr};

use super::intake::collect_shard_paths;
use crate::error::{MathverseError, MathverseResult};
use crate::library::MathverseLibrary;
use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_from_shard_with_level_lists;
use crate::trust::policy::TrustPolicy;
use crate::types::ImportConfidence;
use crate::verify::incremental::verify_corpus_incremental_with_env;

/// Fuel bound passed to the kernel `whnf` normalisation behind
/// [`defeq_canonical_digest_fueled`]. Kept modest so the tree-score does not hang
/// on heavy mathlib-`Real` statement types; a constant that exhausts it is
/// recorded with `complete = false` (its digest is a partial normal form — still
/// a valid bucket, just less likely to collide). The kernel `is_def_eq` arbiter
/// uses its own internal limits and is unaffected by this bound.
pub const TREE_SCORE_FUEL: u32 = 50_000;

/// Options controlling [`tree_score_verified_corpus`].
#[derive(Debug, Clone)]
pub struct TreeScoreOptions {
    /// Only constants stamped at *at least* this confidence participate. The
    /// kernel-confirmed tree-score is meaningful only for stamps the kernel
    /// produced, so this defaults to [`ImportConfidence::KernelVerified`].
    pub min_confidence: ImportConfidence,
    /// `whnf` fuel for the defeq-canonical digest (see [`TREE_SCORE_FUEL`]).
    pub fuel: u32,
    /// Cap on the number of confirmed same-tree-signature pairs reported, to keep
    /// the JSON output bounded on a large batch. `0` means unbounded.
    pub max_hits: usize,
}

impl Default for TreeScoreOptions {
    fn default() -> Self {
        Self {
            min_confidence: ImportConfidence::KernelVerified,
            fuel: TREE_SCORE_FUEL,
            max_hits: 256,
        }
    }
}

/// One declaration scored by the kernel-confirmed tree-signature.
#[derive(Debug, Clone)]
struct ScoredDecl {
    name: String,
    /// Tier-1 `whnf`-normalised + commutative-canonical digest — the
    /// kernel-confirmed tree-signature (the bucketing key).
    tree_signature: String,
    /// Exact alpha/structural digest of the *un-normalised* type — used to tell
    /// "different form" (distinct structural digest) from a literal duplicate.
    structural_digest: String,
    /// Did `whnf` finish within fuel? `false` ⇒ the tree-signature is a partial
    /// normal form (still a valid bucket, treat misses as "unknown").
    complete: bool,
    /// The reconstructed type, retained so the kernel `is_def_eq` arbiter can be
    /// run on a confirmed-candidate pair.
    type_expr: Expr,
}

/// How two members of a shared tree-signature bucket relate structurally.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollisionForm {
    /// Distinct alpha/structural digests — "same object, *different form*". The
    /// interesting re-encoding case (e.g. a folded vs unfolded statement).
    DifferentForm,
    /// Identical alpha/structural digests — a literal (alpha-equal) duplicate of
    /// the statement under two declaration names.
    LiteralDuplicate,
}

impl CollisionForm {
    /// Stable string label for JSON/report output.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::DifferentForm => "different-form",
            Self::LiteralDuplicate => "literal-duplicate",
        }
    }
}

/// A kernel-CONFIRMED same-tree-signature hit over the verified corpus.
#[derive(Debug, Clone)]
pub struct SameTreeSignatureHit {
    /// First declaration name (lexicographically smaller).
    pub name_a: String,
    /// Second declaration name.
    pub name_b: String,
    /// The shared kernel-confirmed tree-signature (`blake3:<hex>`).
    pub tree_signature: String,
    /// Whether the two members share the same alpha/structural digest
    /// (literal duplicate) or differ structurally (the re-encoding case).
    pub form: CollisionForm,
    /// Whether *both* members normalised within fuel (`complete = true` for both).
    /// When `false`, the shared signature came from a partial normal form — the
    /// kernel `is_def_eq` confirmation below is what makes this a real hit anyway.
    pub complete: bool,
    /// The sound arbiter's verdict: did the kernel `is_def_eq` confirm the two
    /// reconstructed types are the same object? Only `true` hits are reported.
    pub same_object: bool,
}

/// Summary of a kernel-confirmed tree-score pass over a verified shard dir.
#[derive(Debug, Clone)]
pub struct TreeScoreStats {
    /// Shards scanned.
    pub shards: usize,
    /// Constants visited across all shards (every confidence).
    pub constants: u64,
    /// Constants meeting the confidence floor that were scored.
    pub scored: u64,
    /// Of `scored`, how many normalised fully within fuel (`complete = true`).
    pub complete: u64,
    /// Distinct kernel-confirmed tree-signatures among the scored decls.
    pub distinct_tree_signatures: u64,
    /// Pairs sharing a tree-signature with DISTINCT structural digests examined —
    /// "same object, different form" candidates.
    pub different_form_pairs: u64,
    /// Pairs sharing a tree-signature with IDENTICAL structural digests examined —
    /// literal (alpha-equal) duplicate candidates.
    pub literal_duplicate_pairs: u64,
    /// Of all examined candidate pairs, how many the kernel `is_def_eq` arbiter
    /// confirmed as the same object (the sound verdict).
    pub confirmed_same_object: u64,
    /// Of `confirmed_same_object`, how many were "different form" (distinct
    /// structural digests) — the headline uniqueness result.
    pub confirmed_different_form: u64,
    /// Confirmed hits (bounded by [`TreeScoreOptions::max_hits`]).
    pub hits: Vec<SameTreeSignatureHit>,
    /// `blake3:<hex>` corpus digest over the scanned shard bytes (sorted-path
    /// order) — identical pin to [`super::baseline_index::build_baseline_index`].
    pub corpus_digest: String,
}

/// Compute the kernel-confirmed tree-score over a directory of verified shards
/// (or a single shard file).
///
/// Pipeline: load every shard into a [`MathverseLibrary`], rebuild the
/// kernel-trusted env via the dependency-ordered checked replay
/// ([`verify_corpus_incremental_with_env`]), then for every constant stamped at
/// the requested confidence floor compute the Tier-1 `defeq_canonical_digest`
/// and bucket by its `rewrite_digest`. Within each bucket every pair is a
/// candidate, classified [`CollisionForm::DifferentForm`] (distinct structural
/// digests — the "same object, different form" re-encoding case) or
/// [`CollisionForm::LiteralDuplicate`] (alpha-equal under two names); each
/// candidate is confirmed by the kernel `is_def_eq` arbiter before it is
/// reported as a hit. The digest is never the verdict.
///
/// # Errors
///
/// I/O failures, malformed shards, or a failure to build the prelude env.
pub fn tree_score_verified_corpus(
    input: &Path,
    opts: &TreeScoreOptions,
) -> MathverseResult<TreeScoreStats> {
    let shard_paths = collect_shard_paths(input)?;

    // Pin the corpus exactly as the baseline index does: blake3 over shard bytes
    // in sorted-path order. `collect_shard_paths` returns sorted paths.
    let mut corpus_hasher = blake3::Hasher::new();
    let mut readers: Vec<ShardReader> = Vec::with_capacity(shard_paths.len());
    for shard_path in &shard_paths {
        let bytes = std::fs::read(shard_path).map_err(MathverseError::Io)?;
        corpus_hasher.update(&bytes);
        readers.push(ShardReader::from_bytes(&bytes)?);
    }
    let corpus_digest = format!("blake3:{}", corpus_hasher.finalize().to_hex());

    // Rebuild the kernel-trusted env: prelude + the checked replay of the corpus.
    // This lets `whnf`/`is_def_eq` δ-unfold corpus-defined and prelude constants
    // when scoring. If the prelude cannot be built we fall back to an empty env
    // (β/η/ι/proj reduction and a sound structural `is_def_eq` still work; only
    // δ-unfolding of named constants is unavailable — a conservative miss).
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    for reader in &readers {
        lib.load_shard(reader)?;
    }
    let prelude = Environment::try_with_prelude().unwrap_or_else(|_| Environment::new());
    let (env, _report) = verify_corpus_incremental_with_env(&lib, prelude);
    let tc = TypeChecker::new(&env);

    let mut constants: u64 = 0;
    let mut scored: u64 = 0;
    let mut complete: u64 = 0;
    let mut decls: Vec<ScoredDecl> = Vec::new();

    for reader in &readers {
        for header in &reader.constants {
            constants += 1;
            // Confidence floor: only stamps at least as strong as requested.
            // `ImportConfidence`'s `Ord` ranks higher trust *smaller*
            // (`KernelVerified` is the minimum), so "at least as trusted as the
            // floor" is `confidence <= min_confidence`.
            let Ok(confidence) = header.confidence() else {
                continue;
            };
            if confidence > opts.min_confidence {
                continue;
            }
            let Some(name) = reader.strings.get(header.name_idx as usize) else {
                continue;
            };
            let Ok(type_expr) = reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                header.type_idx,
            ) else {
                // A type that fails reconstruction is skipped (name-only); the
                // same best-effort behaviour as the baseline index.
                continue;
            };
            let id = defeq_canonical_digest_fueled(&tc, &type_expr, opts.fuel);
            scored += 1;
            if id.complete {
                complete += 1;
            }
            decls.push(ScoredDecl {
                name: name.clone(),
                tree_signature: id.rewrite_digest,
                structural_digest: id.structural_digest,
                complete: id.complete,
                type_expr,
            });
        }
    }

    let collisions = confirm_collisions(&tc, &decls, opts.max_hits);

    Ok(TreeScoreStats {
        shards: shard_paths.len(),
        constants,
        scored,
        complete,
        distinct_tree_signatures: collisions.distinct_tree_signatures,
        different_form_pairs: collisions.different_form_pairs,
        literal_duplicate_pairs: collisions.literal_duplicate_pairs,
        confirmed_same_object: collisions.confirmed_same_object,
        confirmed_different_form: collisions.confirmed_different_form,
        hits: collisions.hits,
        corpus_digest,
    })
}

/// Accumulator returned by [`confirm_collisions`].
struct CollisionReport {
    distinct_tree_signatures: u64,
    different_form_pairs: u64,
    literal_duplicate_pairs: u64,
    confirmed_same_object: u64,
    confirmed_different_form: u64,
    hits: Vec<SameTreeSignatureHit>,
}

/// Bucket scored decls by the kernel-confirmed tree-signature, then for every
/// pair within a bucket run the kernel `is_def_eq` arbiter to confirm sameness.
///
/// Each pair is classified by its alpha/structural digests:
/// [`CollisionForm::DifferentForm`] (the interesting re-encoding case) or
/// [`CollisionForm::LiteralDuplicate`]. Both are confirmed by the kernel — the
/// digest is never the verdict. Different-form hits are emitted first so they
/// lead the (capped) `hits` list.
fn confirm_collisions(
    tc: &TypeChecker<'_>,
    decls: &[ScoredDecl],
    max_hits: usize,
) -> CollisionReport {
    // Group by tree-signature. BTreeMap for deterministic output order.
    let mut buckets: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    for (i, d) in decls.iter().enumerate() {
        buckets
            .entry(d.tree_signature.as_str())
            .or_default()
            .push(i);
    }
    let distinct_tree_signatures = buckets.len() as u64;

    let mut report = CollisionReport {
        distinct_tree_signatures,
        different_form_pairs: 0,
        literal_duplicate_pairs: 0,
        confirmed_same_object: 0,
        confirmed_different_form: 0,
        hits: Vec::new(),
    };
    // Hold different-form hits separately so they can lead the capped hit list.
    let mut different_form_hits: Vec<SameTreeSignatureHit> = Vec::new();
    let mut literal_duplicate_hits: Vec<SameTreeSignatureHit> = Vec::new();

    for members in buckets.values() {
        if members.len() < 2 {
            continue;
        }
        // All distinct unordered pairs within the bucket. Buckets are tiny in
        // practice (a handful of re-encodings of one proposition), so the
        // quadratic scan is cheap.
        for a_pos in 0..members.len() {
            for b_pos in (a_pos + 1)..members.len() {
                let da = &decls[members[a_pos]];
                let db = &decls[members[b_pos]];
                let form = if da.structural_digest == db.structural_digest {
                    report.literal_duplicate_pairs += 1;
                    CollisionForm::LiteralDuplicate
                } else {
                    report.different_form_pairs += 1;
                    CollisionForm::DifferentForm
                };
                // The SOUND arbiter: never claim sameness on the digest alone.
                if !tc.is_def_eq(&da.type_expr, &db.type_expr) {
                    continue;
                }
                report.confirmed_same_object += 1;
                if form == CollisionForm::DifferentForm {
                    report.confirmed_different_form += 1;
                }
                let (name_a, name_b) = if da.name <= db.name {
                    (da.name.clone(), db.name.clone())
                } else {
                    (db.name.clone(), da.name.clone())
                };
                let hit = SameTreeSignatureHit {
                    name_a,
                    name_b,
                    tree_signature: da.tree_signature.clone(),
                    form,
                    complete: da.complete && db.complete,
                    same_object: true,
                };
                match form {
                    CollisionForm::DifferentForm => different_form_hits.push(hit),
                    CollisionForm::LiteralDuplicate => literal_duplicate_hits.push(hit),
                }
            }
        }
    }

    // Different-form hits lead; literal duplicates fill any remaining budget.
    report.hits = different_form_hits;
    report.hits.extend(literal_duplicate_hits);
    if max_hits != 0 && report.hits.len() > max_hits {
        report.hits.truncate(max_hits);
    }
    report
}

/// The fast, env-free Tier-1.5 tree-signature of a single reconstructed type —
/// the same key the persistent index uses. Exposed so callers can cross-check a
/// kernel-confirmed signature against the index's fast key without depending on
/// `clean-cake` directly.
#[must_use]
pub fn fast_tree_signature(type_expr: &Expr) -> String {
    structural_rewrite_digest(type_expr)
}

#[cfg(test)]
#[path = "tree_score_tests.rs"]
mod tests;
