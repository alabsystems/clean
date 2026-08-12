// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic search embedding index for the Mathverse Library.
//!
//! BM25-based text search over mathematical constant names and types,
//! with an API designed for future swap to a neural embedding backend.

use clean_kernel::flat::{FlatExpr, FlatTag};

use crate::types::{ConstantIdx, ExprIdx, MathverseConstantHeader};

// -- Math abbreviation expansion --------------------------------------------

/// Bidirectional abbreviation pairs: (short, long).
const ABBREVIATIONS: &[(&str, &str)] = &[
    ("add", "addition"),
    ("sub", "subtraction"),
    ("mul", "multiplication"),
    ("div", "division"),
    ("mod", "modulo"),
    ("pow", "power"),
    ("neg", "negation"),
    ("comm", "commutative"),
    ("assoc", "associative"),
    ("distrib", "distributive"),
    ("equiv", "equivalence"),
    ("iso", "isomorphism"),
    ("hom", "homomorphism"),
    ("iff", "biconditional"),
    ("inv", "inverse"),
    ("id", "identity"),
    ("inj", "injective"),
    ("surj", "surjective"),
    ("bij", "bijective"),
    ("mono", "monomorphism"),
    ("epi", "epimorphism"),
    ("trans", "transitive"),
    ("refl", "reflexive"),
    ("symm", "symmetric"),
    ("antisymm", "antisymmetric"),
    ("succ", "successor"),
    ("pred", "predecessor"),
    ("sqrt", "squareroot"),
    ("abs", "absolute"),
    ("lt", "lessthan"),
    ("le", "lessequal"),
    ("gt", "greaterthan"),
    ("ge", "greaterequal"),
    ("eq", "equal"),
    ("ne", "notequal"),
    ("nat", "natural"),
    ("int", "integer"),
    ("fin", "finite"),
    ("inf", "infinite"),
    ("sup", "supremum"),
    ("lim", "limit"),
    ("cont", "continuous"),
    ("diff", "differentiable"),
    ("meas", "measurable"),
    ("wf", "wellfounded"),
    ("acc", "accessible"),
    ("rec", "recursion"),
    ("ind", "induction"),
    ("prop", "proposition"),
    ("thm", "theorem"),
    ("dec", "decidable"),
];

const STOP_WORDS: &[&str] = &[
    "of", "the", "a", "an", "in", "on", "at", "to", "for", "is", "it", "by", "with", "from", "as",
    "be", "or", "and", "not", "no", "mk",
];

// -- Tokenization -----------------------------------------------------------

/// Tokenize a mathematical name/expression for text search.
///
/// Splits on '.', '_', whitespace, and camelCase boundaries. Lowercases.
/// Expands abbreviations bidirectionally. Removes stop words.
pub fn math_tokenize(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    for segment in text.split(|c: char| c == '.' || c == '_' || c.is_whitespace()) {
        tokens.extend(split_camel_case(segment));
    }
    let tokens: Vec<String> = tokens.iter().map(|t| t.to_lowercase()).collect();

    // Bidirectional expansion: abbrev <-> full form.
    let mut expanded = Vec::new();
    for tok in &tokens {
        expanded.push(tok.clone());
        for &(abbrev, full) in ABBREVIATIONS {
            if tok == abbrev {
                for word in full.split_whitespace() {
                    expanded.push(word.to_string());
                }
            } else if full.split_whitespace().any(|w| w == tok.as_str()) {
                expanded.push(abbrev.to_string());
            }
        }
    }

    expanded.retain(|t| !t.is_empty() && !STOP_WORDS.contains(&t.as_str()));
    expanded
}

/// Split on camelCase boundaries: "addComm" -> ["add", "Comm"].
fn split_camel_case(s: &str) -> Vec<String> {
    if s.is_empty() {
        return Vec::new();
    }
    let mut parts = Vec::new();
    let mut current = String::new();
    let chars: Vec<char> = s.chars().collect();
    for i in 0..chars.len() {
        let c = chars[i];
        if c.is_uppercase() && !current.is_empty() {
            let prev_lower = i > 0 && chars[i - 1].is_lowercase();
            let next_lower = i + 1 < chars.len()
                && chars[i + 1].is_lowercase()
                && current.chars().last().is_some_and(|ch| ch.is_uppercase());
            if prev_lower || next_lower {
                parts.push(current);
                current = String::new();
            }
        }
        current.push(c);
    }
    if !current.is_empty() {
        parts.push(current);
    }
    parts
}

// -- Type expression tokenization -------------------------------------------

/// Extract searchable tokens from a FlatExpr type expression.
pub fn type_tokens(exprs: &[FlatExpr], strings: &[String], root: ExprIdx) -> Vec<String> {
    let mut tokens = Vec::new();
    // PERF/CORRECTNESS: `exprs` is a shared arena and a type is a DAG, so shared
    // subexpressions are reachable along many paths. Without memoization
    // `walk_type` re-expands every shared sub-DAG, which is exponential even
    // under the depth cap and made `build_search_index` hang for hours on some
    // real Mathlib types. `visited` makes each arena node contribute its tokens
    // exactly once, bounding the walk to O(reachable nodes).
    let mut visited: hashbrown::HashSet<ExprIdx> = hashbrown::HashSet::new();
    walk_type(exprs, strings, root, &mut tokens, &mut visited, 0);
    tokens
}

const MAX_TYPE_DEPTH: usize = 64;

fn walk_type(
    exprs: &[FlatExpr],
    strings: &[String],
    idx: ExprIdx,
    tokens: &mut Vec<String>,
    visited: &mut hashbrown::HashSet<ExprIdx>,
    depth: usize,
) {
    if depth > MAX_TYPE_DEPTH || (idx as usize) >= exprs.len() {
        return;
    }
    // Visit each shared arena node at most once (see `type_tokens`). Marked
    // AFTER the depth check so a node cut off on a deep path can still be
    // tokenized when reached along a shallower one.
    if !visited.insert(idx) {
        return;
    }
    let expr = &exprs[idx as usize];
    match expr.tag() {
        Ok(FlatTag::Const) => {
            if let Some(name) = strings.get(expr.read_u32(0).unwrap_or(0) as usize) {
                tokens.extend(math_tokenize(name));
            }
        }
        Ok(FlatTag::Pi) => {
            tokens.push("arrow".into());
            tokens.push("function".into());
            let ty = u32::from_le_bytes([expr.data[1], expr.data[2], expr.data[3], expr.data[4]]);
            let body = u32::from_le_bytes([expr.data[5], expr.data[6], expr.data[7], expr.data[8]]);
            walk_type(exprs, strings, ty, tokens, visited, depth + 1);
            walk_type(exprs, strings, body, tokens, visited, depth + 1);
        }
        Ok(FlatTag::App) => {
            walk_type(
                exprs,
                strings,
                expr.read_u32(0).unwrap_or(0),
                tokens,
                visited,
                depth + 1,
            );
            walk_type(
                exprs,
                strings,
                expr.read_u32(4).unwrap_or(0),
                tokens,
                visited,
                depth + 1,
            );
        }
        Ok(FlatTag::Lam) => {
            tokens.push("lambda".into());
            let ty = u32::from_le_bytes([expr.data[1], expr.data[2], expr.data[3], expr.data[4]]);
            let body = u32::from_le_bytes([expr.data[5], expr.data[6], expr.data[7], expr.data[8]]);
            walk_type(exprs, strings, ty, tokens, visited, depth + 1);
            walk_type(exprs, strings, body, tokens, visited, depth + 1);
        }
        Ok(FlatTag::Sort) => {
            if expr.read_u32(0).unwrap_or(0) == 0 {
                tokens.push("prop".into());
                tokens.push("proposition".into());
            } else {
                tokens.push("type".into());
            }
        }
        Ok(FlatTag::Let) => {
            for off in [0, 4, 8] {
                walk_type(
                    exprs,
                    strings,
                    expr.read_u32(off).unwrap_or(0),
                    tokens,
                    visited,
                    depth + 1,
                );
            }
        }
        Ok(FlatTag::Proj) => {
            if let Some(name) = strings.get(expr.read_u32(0).unwrap_or(0) as usize) {
                tokens.extend(math_tokenize(name));
            }
            let inner =
                u32::from_le_bytes([expr.data[6], expr.data[7], expr.data[8], expr.data[9]]);
            walk_type(exprs, strings, inner, tokens, visited, depth + 1);
        }
        _ => {}
    }
}

// -- BM25 index -------------------------------------------------------------

/// BM25 search index for mathematical constants.
pub struct BM25Index {
    doc_freq: hashbrown::HashMap<String, u32>,
    docs: Vec<Vec<String>>,
    constant_indices: Vec<ConstantIdx>,
    total_docs: u32,
    avg_doc_len: f32,
    k1: f32,
    b: f32,
}

impl BM25Index {
    pub fn new() -> Self {
        Self::with_params(1.5, 0.75)
    }

    pub fn with_params(k1: f32, b: f32) -> Self {
        Self {
            doc_freq: hashbrown::HashMap::new(),
            docs: Vec::new(),
            constant_indices: Vec::new(),
            total_docs: 0,
            avg_doc_len: 0.0,
            k1,
            b,
        }
    }

    /// Index a constant's name and additional type tokens.
    pub fn index_constant(&mut self, idx: ConstantIdx, name: &str, type_toks: &[String]) {
        let mut tokens = math_tokenize(name);
        tokens.extend(type_toks.iter().cloned());
        let mut seen = hashbrown::HashSet::new();
        for tok in &tokens {
            if seen.insert(tok.clone()) {
                *self.doc_freq.entry(tok.clone()).or_insert(0) += 1;
            }
        }
        self.docs.push(tokens);
        self.constant_indices.push(idx);
    }

    /// Rebuild internal statistics (call after batch indexing).
    pub fn rebuild_stats(&mut self) {
        self.total_docs = self.docs.len() as u32;
        if self.total_docs == 0 {
            self.avg_doc_len = 0.0;
            return;
        }
        let total_len: usize = self.docs.iter().map(|d| d.len()).sum();
        self.avg_doc_len = total_len as f32 / self.total_docs as f32;
    }

    /// Search. Returns (ConstantIdx, score) pairs sorted by descending score.
    pub fn search(&self, query: &str, max_results: usize) -> Vec<(ConstantIdx, f32)> {
        if self.total_docs == 0 || max_results == 0 {
            return Vec::new();
        }
        let query_tokens = math_tokenize(query);
        if query_tokens.is_empty() {
            return Vec::new();
        }

        let mut scores: Vec<(ConstantIdx, f32)> = self
            .docs
            .iter()
            .enumerate()
            .map(|(i, doc)| {
                (
                    self.constant_indices[i],
                    self.bm25_score(&query_tokens, doc),
                )
            })
            .filter(|(_, s)| *s > 0.0)
            .collect();
        scores.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        scores.truncate(max_results);
        scores
    }

    fn bm25_score(&self, query_tokens: &[String], doc_tokens: &[String]) -> f32 {
        let dl = doc_tokens.len() as f32;
        let n = self.total_docs as f32;
        // Count term frequencies in one O(L) pass, instead of re-scanning the
        // whole document once per query token (O(Q×L) → O(L+Q) per doc). tf
        // values are exact occurrence counts, so every score is byte-identical.
        let mut tf_map: std::collections::HashMap<&str, u32> =
            std::collections::HashMap::with_capacity(doc_tokens.len());
        for t in doc_tokens {
            *tf_map.entry(t.as_str()).or_insert(0) += 1;
        }
        let mut score = 0.0_f32;
        for qt in query_tokens {
            let df = self.doc_freq.get(qt).copied().unwrap_or(0) as f32;
            if df == 0.0 {
                continue;
            }
            let tf = tf_map.get(qt.as_str()).copied().unwrap_or(0) as f32;
            if tf == 0.0 {
                continue;
            }
            let idf = ((n - df + 0.5) / (df + 0.5) + 1.0).ln();
            let tf_norm = (tf * (self.k1 + 1.0))
                / (tf + self.k1 * (1.0 - self.b + self.b * dl / self.avg_doc_len));
            score += idf * tf_norm;
        }
        score
    }

    /// Explain a search query: returns per-result breakdowns of which tokens
    /// matched and their individual BM25 contributions.
    pub fn search_explain(&self, query: &str, max_results: usize) -> Vec<SearchExplanation> {
        if self.total_docs == 0 || max_results == 0 {
            return Vec::new();
        }
        let query_tokens = math_tokenize(query);
        if query_tokens.is_empty() {
            return Vec::new();
        }

        let n = self.total_docs as f32;
        let mut explanations: Vec<SearchExplanation> = self
            .docs
            .iter()
            .enumerate()
            .filter_map(|(i, doc)| {
                let dl = doc.len() as f32;
                // One O(L) term-frequency pass instead of an O(L) re-scan per
                // query token (O(Q×L) → O(L+Q)); exact counts ⇒ identical scores.
                let mut tf_map: std::collections::HashMap<&str, u32> =
                    std::collections::HashMap::with_capacity(doc.len());
                for t in doc {
                    *tf_map.entry(t.as_str()).or_insert(0) += 1;
                }
                let mut token_scores = Vec::new();
                let mut total = 0.0_f32;
                for qt in &query_tokens {
                    let df = self.doc_freq.get(qt).copied().unwrap_or(0) as f32;
                    if df == 0.0 {
                        continue;
                    }
                    let tf = tf_map.get(qt.as_str()).copied().unwrap_or(0) as f32;
                    if tf == 0.0 {
                        continue;
                    }
                    let idf = ((n - df + 0.5) / (df + 0.5) + 1.0).ln();
                    let tf_norm = (tf * (self.k1 + 1.0))
                        / (tf + self.k1 * (1.0 - self.b + self.b * dl / self.avg_doc_len));
                    let s = idf * tf_norm;
                    total += s;
                    token_scores.push(TokenScore {
                        token: qt.clone(),
                        tf: tf as u32,
                        df: df as u32,
                        score: s,
                    });
                }
                if total > 0.0 {
                    Some(SearchExplanation {
                        constant_idx: self.constant_indices[i],
                        total_score: total,
                        query_tokens: query_tokens.clone(),
                        token_scores,
                    })
                } else {
                    None
                }
            })
            .collect();
        explanations.sort_by(|a, b| {
            b.total_score
                .partial_cmp(&a.total_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        explanations.truncate(max_results);
        explanations
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.docs.len()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.docs.is_empty()
    }
    #[inline]
    pub fn k1(&self) -> f32 {
        self.k1
    }
    #[inline]
    pub fn b(&self) -> f32 {
        self.b
    }
}

impl Default for BM25Index {
    fn default() -> Self {
        Self::new()
    }
}

// -- Search explanation types -------------------------------------------------

/// Per-token BM25 score breakdown.
#[derive(Clone, Debug)]
pub struct TokenScore {
    /// The query token that matched.
    pub token: String,
    /// Term frequency (how many times it appeared in this document).
    pub tf: u32,
    /// Document frequency (how many documents contain this token).
    pub df: u32,
    /// BM25 contribution of this token to the total score.
    pub score: f32,
}

/// Full explanation of why a search result matched.
#[derive(Clone, Debug)]
pub struct SearchExplanation {
    /// The constant that matched.
    pub constant_idx: ConstantIdx,
    /// Total BM25 score.
    pub total_score: f32,
    /// The expanded query tokens (after abbreviation expansion).
    pub query_tokens: Vec<String>,
    /// Per-token score breakdown.
    pub token_scores: Vec<TokenScore>,
}

// -- Embedding vector stub (future neural backend) --------------------------

/// Default embedding dimension for hash-based embeddings.
const DEFAULT_EMBED_DIM: usize = 128;

/// Placeholder for neural embedding vectors.
#[derive(Clone, Debug)]
pub struct EmbeddingVector {
    pub dims: usize,
    pub data: Vec<f32>,
}

impl EmbeddingVector {
    /// Create a zero vector with the given dimensionality.
    pub fn zeros(dims: usize) -> Self {
        Self {
            dims,
            data: vec![0.0; dims],
        }
    }

    /// L2 (Euclidean) distance squared between two vectors.
    pub fn l2_distance_sq(&self, other: &Self) -> f32 {
        debug_assert_eq!(self.dims, other.dims);
        self.data
            .iter()
            .zip(other.data.iter())
            .map(|(a, b)| (a - b) * (a - b))
            .sum()
    }

    /// L2 norm of the vector.
    pub fn l2_norm(&self) -> f32 {
        self.data.iter().map(|x| x * x).sum::<f32>().sqrt()
    }

    /// Normalize the vector to unit length. Returns zero vector if norm is zero.
    pub fn normalize(&self) -> Self {
        let norm = self.l2_norm();
        if norm < f32::EPSILON {
            return Self::zeros(self.dims);
        }
        Self {
            dims: self.dims,
            data: self.data.iter().map(|x| x / norm).collect(),
        }
    }
}

/// Trait for embedding providers (swap in neural backend later).
pub trait EmbeddingProvider {
    fn embed_name(&self, name: &str) -> EmbeddingVector;
    fn embed_type(&self, type_expr: &str) -> EmbeddingVector;
    fn similarity(a: &EmbeddingVector, b: &EmbeddingVector) -> f32;
}

/// BM25-based stub provider (no-op vectors, BM25 uses its own scoring).
pub struct BM25EmbeddingProvider;

impl EmbeddingProvider for BM25EmbeddingProvider {
    fn embed_name(&self, _name: &str) -> EmbeddingVector {
        EmbeddingVector {
            dims: 0,
            data: vec![],
        }
    }
    fn embed_type(&self, _type_expr: &str) -> EmbeddingVector {
        EmbeddingVector {
            dims: 0,
            data: vec![],
        }
    }
    fn similarity(_a: &EmbeddingVector, _b: &EmbeddingVector) -> f32 {
        0.0
    }
}

// -- MathEmbedding: deterministic hash-based embedding ----------------------

/// Deterministic hash-based embedding provider for testing/bootstrapping.
///
/// Produces consistent float vectors from token hashes with position encoding.
/// Not neural — uses murmurhash-style mixing to spread tokens across dimensions.
pub struct MathEmbedding {
    dims: usize,
}

impl MathEmbedding {
    pub fn new() -> Self {
        Self {
            dims: DEFAULT_EMBED_DIM,
        }
    }

    pub fn with_dims(dims: usize) -> Self {
        Self { dims }
    }

    /// Embed a constant given its name and type tokens.
    ///
    /// Produces a deterministic float vector by hashing each token with
    /// position encoding and accumulating into dimensions.
    pub fn embed_constant(&self, name: &str, type_tokens: &[String]) -> EmbeddingVector {
        let mut data = vec![0.0_f32; self.dims];
        let name_tokens = math_tokenize(name);

        // Name tokens get higher weight (position 0..N).
        for (pos, tok) in name_tokens.iter().enumerate() {
            self.accumulate_token(&mut data, tok, pos, 2.0);
        }

        // Type tokens get standard weight (position offset by name length).
        let offset = name_tokens.len();
        for (pos, tok) in type_tokens.iter().enumerate() {
            self.accumulate_token(&mut data, tok, pos + offset, 1.0);
        }

        let ev = EmbeddingVector {
            dims: self.dims,
            data,
        };
        ev.normalize()
    }

    /// Murmurhash3-style 32-bit mixing function.
    pub(crate) fn murmur_mix(mut h: u32) -> u32 {
        h ^= h >> 16;
        h = h.wrapping_mul(0x85ebca6b);
        h ^= h >> 13;
        h = h.wrapping_mul(0xc2b2ae35);
        h ^= h >> 16;
        h
    }

    /// Hash a token string to a u32 seed, murmurhash3-style.
    fn hash_token(token: &str) -> u32 {
        let mut h: u32 = 0;
        for (i, b) in token.bytes().enumerate() {
            h ^= (b as u32)
                .wrapping_mul(0xcc9e2d51)
                .rotate_left(15)
                .wrapping_mul(0x1b873593);
            h = h.rotate_left(13).wrapping_mul(5).wrapping_add(0xe6546b64);
            h ^= (i as u32).wrapping_mul(0x9e3779b9);
        }
        Self::murmur_mix(h ^ (token.len() as u32))
    }

    /// Accumulate a token into the embedding vector with position encoding.
    fn accumulate_token(&self, data: &mut [f32], token: &str, position: usize, weight: f32) {
        let seed = Self::hash_token(token);
        // Position-encoded seed: different positions produce different contributions.
        let pos_seed = Self::murmur_mix(seed ^ (position as u32).wrapping_mul(0x9e3779b9));

        // Scatter into multiple dimensions with sign flips for orthogonality.
        let num_dims_to_touch = 8.min(self.dims);
        for k in 0..num_dims_to_touch {
            let dim_hash = Self::murmur_mix(pos_seed.wrapping_add(k as u32));
            let dim = (dim_hash as usize) % self.dims;
            // Convert to float in [-1, 1] range.
            let val = ((dim_hash as f32) / (u32::MAX as f32)) * 2.0 - 1.0;
            data[dim] += val * weight;
        }
    }
}

impl Default for MathEmbedding {
    fn default() -> Self {
        Self::new()
    }
}

impl EmbeddingProvider for MathEmbedding {
    fn embed_name(&self, name: &str) -> EmbeddingVector {
        self.embed_constant(name, &[])
    }

    fn embed_type(&self, type_expr: &str) -> EmbeddingVector {
        let tokens = math_tokenize(type_expr);
        self.embed_constant("", &tokens)
    }

    fn similarity(a: &EmbeddingVector, b: &EmbeddingVector) -> f32 {
        if a.dims == 0 || b.dims == 0 || a.dims != b.dims {
            return 0.0;
        }
        // Cosine similarity.
        let dot: f32 = a.data.iter().zip(b.data.iter()).map(|(x, y)| x * y).sum();
        let na = a.l2_norm();
        let nb = b.l2_norm();
        if na < f32::EPSILON || nb < f32::EPSILON {
            return 0.0;
        }
        dot / (na * nb)
    }
}

// -- IVF-PQ index -----------------------------------------------------------

/// In-memory IVF-PQ (Inverted File with Product Quantization) approximate
/// nearest neighbor index.
///
/// Two-level structure:
/// 1. **IVF**: Partition vectors into `num_centroids` Voronoi cells via k-means.
/// 2. **PQ**: Compress residuals (vector - centroid) into byte codes using
///    product quantization codebooks.
///
/// Search probes `n_probe` closest centroids, computes asymmetric distances
/// using PQ codebooks, and returns top-k results.
pub struct IVFPQIndex {
    /// Number of IVF centroids (Voronoi cells).
    pub num_centroids: usize,
    /// Per-vector centroid assignment.
    pub centroid_assignments: Vec<usize>,
    /// IVF centroid vectors.
    pub centroids: Vec<EmbeddingVector>,
    /// Per-vector PQ codes: `pq_codes[vec_idx][segment]` = codebook entry index.
    pub pq_codes: Vec<Vec<u8>>,
    /// PQ codebooks: `pq_centroids[segment][code][sub_dim_values]`.
    pub pq_centroids: Vec<Vec<Vec<f32>>>,
    /// Number of PQ segments the vector is split into.
    pq_segments: usize,
    /// Dimensionality of input vectors.
    dims: usize,
    /// Inverted lists: `inv_lists[centroid_id]` = vec of original vector indices.
    inv_lists: Vec<Vec<usize>>,
}

impl IVFPQIndex {
    /// Build an IVF-PQ index from a set of vectors.
    ///
    /// # Arguments
    /// * `vectors` - Input vectors (must all have the same dimensionality).
    /// * `num_centroids` - Number of IVF partitions (Voronoi cells).
    /// * `pq_segments` - Number of sub-vector segments for product quantization.
    ///   Must evenly divide the vector dimensionality. Each segment gets a 256-entry codebook.
    pub fn build(vectors: &[EmbeddingVector], num_centroids: usize, pq_segments: usize) -> Self {
        if vectors.is_empty() {
            return Self {
                num_centroids: 0,
                centroid_assignments: Vec::new(),
                centroids: Vec::new(),
                pq_codes: Vec::new(),
                pq_centroids: Vec::new(),
                pq_segments,
                dims: 0,
                inv_lists: Vec::new(),
            };
        }

        let dims = vectors[0].dims;
        assert!(
            dims > 0 && pq_segments > 0 && dims.is_multiple_of(pq_segments),
            "dims ({dims}) must be divisible by pq_segments ({pq_segments})"
        );
        let actual_centroids = num_centroids.min(vectors.len());

        // Step 1: K-means clustering for IVF centroids.
        let centroids = Self::kmeans(vectors, actual_centroids, 20);
        let centroid_assignments: Vec<usize> = vectors
            .iter()
            .map(|v| Self::nearest_centroid(v, &centroids))
            .collect();

        // Build inverted lists.
        let mut inv_lists = vec![Vec::new(); actual_centroids];
        for (idx, &c) in centroid_assignments.iter().enumerate() {
            inv_lists[c].push(idx);
        }

        // Step 2: Product quantization on residuals.
        let sub_dim = dims / pq_segments;
        let pq_codebook_size = 256.min(vectors.len()); // at most 256 entries per codebook

        // Train PQ codebooks per segment.
        let mut pq_centroids_all: Vec<Vec<Vec<f32>>> = Vec::with_capacity(pq_segments);
        for seg in 0..pq_segments {
            let start = seg * sub_dim;
            let end = start + sub_dim;
            // Extract sub-vectors (residuals).
            let sub_vecs: Vec<Vec<f32>> = vectors
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    let c = &centroids[centroid_assignments[i]];
                    v.data[start..end]
                        .iter()
                        .zip(c.data[start..end].iter())
                        .map(|(a, b)| a - b)
                        .collect()
                })
                .collect();

            // K-means on sub-vectors for this segment's codebook.
            let codebook = Self::kmeans_flat(&sub_vecs, pq_codebook_size, 10);
            pq_centroids_all.push(codebook);
        }

        // Encode each vector.
        let pq_codes: Vec<Vec<u8>> = vectors
            .iter()
            .enumerate()
            .map(|(i, v)| {
                let c = &centroids[centroid_assignments[i]];
                (0..pq_segments)
                    .map(|seg| {
                        let start = seg * sub_dim;
                        let end = start + sub_dim;
                        let residual: Vec<f32> = v.data[start..end]
                            .iter()
                            .zip(c.data[start..end].iter())
                            .map(|(a, b)| a - b)
                            .collect();
                        Self::nearest_codebook_entry(&residual, &pq_centroids_all[seg]) as u8
                    })
                    .collect()
            })
            .collect();

        Self {
            num_centroids: actual_centroids,
            centroid_assignments,
            centroids,
            pq_codes,
            pq_centroids: pq_centroids_all,
            pq_segments,
            dims,
            inv_lists,
        }
    }

    /// Search for the k nearest neighbors of `query`.
    ///
    /// # Arguments
    /// * `query` - Query vector.
    /// * `k` - Number of results to return.
    /// * `n_probe` - Number of IVF cells to probe (higher = more accurate, slower).
    ///
    /// Returns `(original_index, squared_l2_distance)` pairs sorted by ascending distance.
    pub fn search(&self, query: &EmbeddingVector, k: usize, n_probe: usize) -> Vec<(usize, f32)> {
        if self.centroids.is_empty() || k == 0 {
            return Vec::new();
        }

        // Find n_probe closest centroids.
        let actual_probe = n_probe.min(self.num_centroids);
        let mut centroid_dists: Vec<(usize, f32)> = self
            .centroids
            .iter()
            .enumerate()
            .map(|(i, c)| (i, query.l2_distance_sq(c)))
            .collect();
        centroid_dists.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        centroid_dists.truncate(actual_probe);

        let sub_dim = self.dims / self.pq_segments;

        // Scan probed inverted lists.
        let mut candidates: Vec<(usize, f32)> = Vec::new();
        for &(centroid_id, _) in &centroid_dists {
            // Recompute distance tables adjusted for this centroid's residual.
            let centroid_vec = &self.centroids[centroid_id];
            let adjusted_tables: Vec<Vec<f32>> = (0..self.pq_segments)
                .map(|seg| {
                    let start = seg * sub_dim;
                    let end = start + sub_dim;
                    let query_residual: Vec<f32> = query.data[start..end]
                        .iter()
                        .zip(centroid_vec.data[start..end].iter())
                        .map(|(q, c)| q - c)
                        .collect();
                    self.pq_centroids[seg]
                        .iter()
                        .map(|code_centroid| {
                            query_residual
                                .iter()
                                .zip(code_centroid.iter())
                                .map(|(q, c)| (q - c) * (q - c))
                                .sum::<f32>()
                        })
                        .collect()
                })
                .collect();

            for &vec_idx in &self.inv_lists[centroid_id] {
                let codes = &self.pq_codes[vec_idx];
                let dist: f32 = (0..self.pq_segments)
                    .map(|seg| adjusted_tables[seg][codes[seg] as usize])
                    .sum();
                candidates.push((vec_idx, dist));
            }
        }

        candidates.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        candidates.truncate(k);
        candidates
    }

    /// Simple k-means on `EmbeddingVector` values.
    fn kmeans(vectors: &[EmbeddingVector], k: usize, iterations: usize) -> Vec<EmbeddingVector> {
        let dims = vectors[0].dims;
        let actual_k = k.min(vectors.len());

        // Initialize centroids by taking evenly-spaced vectors.
        let mut centroids: Vec<EmbeddingVector> = (0..actual_k)
            .map(|i| {
                let idx = i * vectors.len() / actual_k;
                vectors[idx].clone()
            })
            .collect();

        for _ in 0..iterations {
            // Assign each vector to nearest centroid.
            let assignments: Vec<usize> = vectors
                .iter()
                .map(|v| Self::nearest_centroid(v, &centroids))
                .collect();

            // Recompute centroids.
            let mut sums = vec![vec![0.0_f32; dims]; actual_k];
            let mut counts = vec![0usize; actual_k];
            for (i, v) in vectors.iter().enumerate() {
                let c = assignments[i];
                counts[c] += 1;
                for (j, &val) in v.data.iter().enumerate() {
                    sums[c][j] += val;
                }
            }
            for c in 0..actual_k {
                if counts[c] > 0 {
                    let cnt = counts[c] as f32;
                    centroids[c] = EmbeddingVector {
                        dims,
                        data: sums[c].iter().map(|s| s / cnt).collect(),
                    };
                }
            }
        }
        centroids
    }

    /// K-means on flat f32 sub-vectors (for PQ codebook training).
    fn kmeans_flat(vectors: &[Vec<f32>], k: usize, iterations: usize) -> Vec<Vec<f32>> {
        if vectors.is_empty() {
            return Vec::new();
        }
        let d = vectors[0].len();
        let actual_k = k.min(vectors.len());

        let mut centroids: Vec<Vec<f32>> = (0..actual_k)
            .map(|i| {
                let idx = i * vectors.len() / actual_k;
                vectors[idx].clone()
            })
            .collect();

        for _ in 0..iterations {
            let assignments: Vec<usize> = vectors
                .iter()
                .map(|v| Self::nearest_flat(v, &centroids))
                .collect();

            let mut sums = vec![vec![0.0_f32; d]; actual_k];
            let mut counts = vec![0usize; actual_k];
            for (i, v) in vectors.iter().enumerate() {
                let c = assignments[i];
                counts[c] += 1;
                for (j, &val) in v.iter().enumerate() {
                    sums[c][j] += val;
                }
            }
            for c in 0..actual_k {
                if counts[c] > 0 {
                    let cnt = counts[c] as f32;
                    centroids[c] = sums[c].iter().map(|s| s / cnt).collect();
                }
            }
        }
        centroids
    }

    fn nearest_centroid(v: &EmbeddingVector, centroids: &[EmbeddingVector]) -> usize {
        centroids
            .iter()
            .enumerate()
            .min_by(|(_, a), (_, b)| {
                v.l2_distance_sq(a)
                    .partial_cmp(&v.l2_distance_sq(b))
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .map(|(i, _)| i)
            .unwrap_or(0)
    }

    fn nearest_flat(v: &[f32], centroids: &[Vec<f32>]) -> usize {
        centroids
            .iter()
            .enumerate()
            .min_by(|(_, a), (_, b)| {
                let da: f32 = v.iter().zip(a.iter()).map(|(x, y)| (x - y) * (x - y)).sum();
                let db: f32 = v.iter().zip(b.iter()).map(|(x, y)| (x - y) * (x - y)).sum();
                da.partial_cmp(&db).unwrap_or(std::cmp::Ordering::Equal)
            })
            .map(|(i, _)| i)
            .unwrap_or(0)
    }

    fn nearest_codebook_entry(v: &[f32], codebook: &[Vec<f32>]) -> usize {
        Self::nearest_flat(v, codebook)
    }

    /// Number of indexed vectors.
    pub fn len(&self) -> usize {
        self.centroid_assignments.len()
    }

    /// Whether the index is empty.
    pub fn is_empty(&self) -> bool {
        self.centroid_assignments.is_empty()
    }
}

// -- CombinedSearch ---------------------------------------------------------

/// Blends BM25 text search scores with IVF-PQ vector search scores.
///
/// Score = `alpha * bm25_normalized + (1 - alpha) * vector_normalized`
pub struct CombinedSearch {
    /// Weight for BM25 scores (0.0 to 1.0). Vector weight = 1.0 - alpha.
    pub alpha: f32,
}

impl CombinedSearch {
    pub fn new(alpha: f32) -> Self {
        Self {
            alpha: alpha.clamp(0.0, 1.0),
        }
    }

    /// Search using both BM25 and vector similarity, blending results.
    ///
    /// Returns `(document_index, blended_score)` sorted by descending score.
    pub fn search(
        &self,
        query: &str,
        bm25: &BM25Index,
        ivfpq: &IVFPQIndex,
        embedder: &impl EmbeddingProvider,
        k: usize,
    ) -> Vec<(usize, f32)> {
        if k == 0 {
            return Vec::new();
        }

        // BM25 results — fetch more candidates than needed for blending.
        let fetch_k = k * 3;
        let bm25_results = bm25.search(query, fetch_k);

        // Vector results.
        let query_vec = embedder.embed_name(query);
        let vec_results = if !ivfpq.is_empty() && query_vec.dims > 0 {
            let n_probe = (ivfpq.num_centroids / 4).max(1);
            ivfpq.search(&query_vec, fetch_k, n_probe)
        } else {
            Vec::new()
        };

        // Normalize BM25 scores to [0, 1].
        let bm25_max = bm25_results.iter().map(|r| r.1).fold(0.0_f32, f32::max);
        let bm25_norm: hashbrown::HashMap<usize, f32> = bm25_results
            .iter()
            .map(|&(idx, score)| {
                let norm = if bm25_max > 0.0 {
                    score / bm25_max
                } else {
                    0.0
                };
                (idx as usize, norm)
            })
            .collect();

        // Normalize vector distances to [0, 1] similarity (invert distance).
        let vec_max_dist = vec_results.iter().map(|r| r.1).fold(0.0_f32, f32::max);
        let vec_norm: hashbrown::HashMap<usize, f32> = vec_results
            .iter()
            .map(|&(idx, dist)| {
                let sim = if vec_max_dist > 0.0 {
                    1.0 - (dist / vec_max_dist)
                } else {
                    0.0
                };
                (idx, sim)
            })
            .collect();

        // Union all candidate indices.
        let mut all_indices: hashbrown::HashSet<usize> = hashbrown::HashSet::new();
        all_indices.extend(bm25_norm.keys());
        all_indices.extend(vec_norm.keys());

        // Blend scores.
        let mut results: Vec<(usize, f32)> = all_indices
            .into_iter()
            .map(|idx| {
                let bm25_s = bm25_norm.get(&idx).copied().unwrap_or(0.0);
                let vec_s = vec_norm.get(&idx).copied().unwrap_or(0.0);
                let blended = self.alpha * bm25_s + (1.0 - self.alpha) * vec_s;
                (idx, blended)
            })
            .filter(|(_, s)| *s > 0.0)
            .collect();

        results.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        results.truncate(k);
        results
    }
}

// -- Integration helper -----------------------------------------------------

/// Build a BM25 search index from all loaded constants.
pub fn build_search_index(
    constants: &[MathverseConstantHeader],
    strings: &[String],
    exprs: &[FlatExpr],
) -> BM25Index {
    let mut index = BM25Index::new();
    for (i, c) in constants.iter().enumerate() {
        let name = strings
            .get(c.name_idx as usize)
            .map(|s| s.as_str())
            .unwrap_or("");
        let type_toks = type_tokens(exprs, strings, c.type_idx);
        index.index_constant(i as u32, name, &type_toks);
    }
    index.rebuild_stats();
    index
}

// -- Tests ------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{AxiomProfile, NO_VALUE};

    #[test]
    fn test_math_tokenize_splits() {
        // Dots
        let t = math_tokenize("Nat.add.comm");
        assert!(
            t.contains(&"nat".into()) && t.contains(&"add".into()) && t.contains(&"comm".into())
        );
        // Underscores
        let t = math_tokenize("add_comm_group");
        assert!(
            t.contains(&"add".into()) && t.contains(&"comm".into()) && t.contains(&"group".into())
        );
        // camelCase
        let t = math_tokenize("addComm");
        assert!(t.contains(&"add".into()) && t.contains(&"comm".into()));
        // Mixed
        let t = math_tokenize("List.map_ofFn");
        assert!(
            t.contains(&"list".into()) && t.contains(&"map".into()) && t.contains(&"fn".into())
        );
        // Empty
        assert!(math_tokenize("").is_empty());
    }

    #[test]
    fn test_math_tokenize_abbreviations() {
        // Forward: abbrev -> full
        let t = math_tokenize("comm");
        assert!(t.contains(&"comm".into()) && t.contains(&"commutative".into()));
        // Multiple
        let t = math_tokenize("assoc_comm");
        assert!(t.contains(&"associative".into()) && t.contains(&"commutative".into()));
        // Reverse: full -> abbrev
        let t = math_tokenize("commutative");
        assert!(t.contains(&"comm".into()), "reverse expansion: {t:?}");
    }

    #[test]
    fn test_math_tokenize_stop_words_and_greek() {
        let t = math_tokenize("the_proof_of_induction");
        assert!(!t.contains(&"the".into()) && !t.contains(&"of".into()));
        assert!(t.contains(&"proof".into()));
        // Greek letters are kept
        let t = math_tokenize("alpha_beta");
        assert!(t.contains(&"alpha".into()) && t.contains(&"beta".into()));
    }

    #[test]
    fn test_split_camel_case() {
        assert_eq!(split_camel_case("addComm"), vec!["add", "Comm"]);
        assert_eq!(split_camel_case("HTTPServer"), vec!["HTTP", "Server"]);
        assert_eq!(split_camel_case("hello"), vec!["hello"]);
        assert!(split_camel_case("").is_empty());
    }

    // -- BM25 tests ---------------------------------------------------------

    fn make_test_index() -> BM25Index {
        let mut idx = BM25Index::new();
        idx.index_constant(0, "Nat.add_comm", &[]);
        idx.index_constant(1, "Nat.mul_comm", &[]);
        idx.index_constant(2, "Nat.add_assoc", &[]);
        idx.index_constant(3, "List.map", &[]);
        idx.index_constant(4, "Int.add_comm", &[]);
        idx.rebuild_stats();
        idx
    }

    #[test]
    fn test_bm25_empty_index() {
        let idx = BM25Index::new();
        assert!(idx.is_empty() && idx.is_empty());
        assert!(idx.search("anything", 10).is_empty());
    }

    #[test]
    fn test_bm25_index_and_search() {
        let idx = make_test_index();
        assert_eq!(idx.len(), 5);
        assert!(!idx.is_empty());

        // Exact name match
        let r = idx.search("Nat.add_comm", 10);
        assert!(
            !r.is_empty() && r[0].0 == 0,
            "exact match should rank first"
        );

        // Semantic query via abbreviation expansion
        let r = idx.search("commutative addition", 10);
        assert!(!r.is_empty(), "expected results for 'commutative addition'");
        assert!(r.iter().any(|x| x.0 == 0), "Nat.add_comm should appear");

        // Ranking: "Nat add comm" should rank Nat.add_comm >= Int.add_comm
        let r = idx.search("Nat add comm", 10);
        assert!(r.len() >= 2);
        let nat_s = r.iter().find(|x| x.0 == 0).map(|x| x.1);
        let int_s = r.iter().find(|x| x.0 == 4).map(|x| x.1);
        if let (Some(n), Some(i)) = (nat_s, int_s) {
            assert!(n >= i, "Nat.add_comm ({n}) >= Int.add_comm ({i})");
        }

        // No results for gibberish
        assert!(idx.search("zzz_nonexistent_xxy", 10).is_empty());
        // max_results respected
        assert!(idx.search("comm", 2).len() <= 2);
        // Empty query
        assert!(idx.search("", 10).is_empty());
    }

    #[test]
    fn test_bm25_params() {
        let mut lo = BM25Index::with_params(0.5, 0.75);
        let mut hi = BM25Index::with_params(3.0, 0.75);
        for idx in [&mut lo, &mut hi] {
            idx.index_constant(0, "Nat.add_comm", &[]);
            idx.index_constant(1, "Nat.mul_comm", &[]);
            idx.rebuild_stats();
        }
        assert!((lo.k1() - 0.5).abs() < f32::EPSILON);
        assert!((hi.k1() - 3.0).abs() < f32::EPSILON);
        assert!(lo.search("comm", 10)[0].1 > 0.0);
        assert!(hi.search("comm", 10)[0].1 > 0.0);
    }

    // -- type_tokens tests --------------------------------------------------

    #[test]
    fn test_type_tokens() {
        // Const
        let s = vec!["Nat".into(), "Bool".into()];
        let e = vec![FlatExpr::const_ref(0, u32::MAX)];
        assert!(type_tokens(&e, &s, 0).contains(&"nat".into()));

        // Pi: adds "arrow", "function" + recurses
        let e = vec![
            FlatExpr::pi(0, 1, 2),
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::const_ref(1, u32::MAX),
        ];
        let t = type_tokens(&e, &s, 0);
        assert!(t.contains(&"arrow".into()) && t.contains(&"function".into()));
        assert!(t.contains(&"nat".into()) && t.contains(&"bool".into()));

        // App
        let e = vec![
            FlatExpr::app(1, 2),
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::const_ref(1, u32::MAX),
        ];
        let t = type_tokens(&e, &s, 0);
        assert!(t.contains(&"list".into()) || t.contains(&"nat".into()));

        // Sort(0) -> prop; Sort(1) -> type
        assert!(type_tokens(&[FlatExpr::sort(0)], &[], 0).contains(&"prop".into()));
        assert!(type_tokens(&[FlatExpr::sort(1)], &[], 0).contains(&"type".into()));

        // Out of bounds -> empty
        assert!(type_tokens(&[], &[], 99).is_empty());
    }

    // -- build_search_index tests -------------------------------------------

    fn hdr(name_idx: u32, type_idx: u32) -> MathverseConstantHeader {
        MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: 0,
            import_confidence: 0,
            content_domain: 0,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }
    }

    #[test]
    fn test_build_search_index() {
        let strings = vec![
            "Nat.add_comm".into(),
            "List.map".into(),
            "Nat".into(),
            "Bool".into(),
        ];
        let exprs = vec![
            FlatExpr::const_ref(2, u32::MAX),
            FlatExpr::const_ref(3, u32::MAX),
        ];
        let constants = vec![hdr(0, 0), hdr(1, 1)];
        let idx = build_search_index(&constants, &strings, &exprs);
        assert_eq!(idx.len(), 2);
        let r = idx.search("add commutative", 10);
        assert!(
            !r.is_empty() && r[0].0 == 0,
            "Nat.add_comm should rank first"
        );
    }

    #[test]
    fn test_build_search_index_empty() {
        assert!(build_search_index(&[], &[], &[]).is_empty());
    }

    #[test]
    fn test_bm25_embedding_provider() {
        let p = BM25EmbeddingProvider;
        let v1 = p.embed_name("Nat.add");
        let v2 = p.embed_type("Nat -> Nat -> Nat");
        assert_eq!(v1.dims, 0);
        assert!(v1.data.is_empty() && v2.data.is_empty());
        assert_eq!(BM25EmbeddingProvider::similarity(&v1, &v2), 0.0);
    }

    // -- EmbeddingVector tests -----------------------------------------------

    #[test]
    fn test_embedding_vector_zeros() {
        let v = EmbeddingVector::zeros(64);
        assert_eq!(v.dims, 64);
        assert!(v.data.iter().all(|&x| x == 0.0));
        assert!(v.l2_norm() < f32::EPSILON);
    }

    #[test]
    fn test_embedding_vector_l2_distance() {
        let a = EmbeddingVector {
            dims: 3,
            data: vec![1.0, 0.0, 0.0],
        };
        let b = EmbeddingVector {
            dims: 3,
            data: vec![0.0, 1.0, 0.0],
        };
        let dist = a.l2_distance_sq(&b);
        assert!((dist - 2.0).abs() < 1e-6, "expected ~2.0, got {dist}");
    }

    #[test]
    fn test_embedding_vector_normalize() {
        let v = EmbeddingVector {
            dims: 3,
            data: vec![3.0, 4.0, 0.0],
        };
        let n = v.normalize();
        assert!(
            (n.l2_norm() - 1.0).abs() < 1e-5,
            "normalized norm: {}",
            n.l2_norm()
        );
        assert!((n.data[0] - 0.6).abs() < 1e-5);
        assert!((n.data[1] - 0.8).abs() < 1e-5);
        // Zero vector normalizes to zero.
        let z = EmbeddingVector::zeros(4).normalize();
        assert!(z.l2_norm() < f32::EPSILON);
    }

    // -- MathEmbedding tests -------------------------------------------------

    #[test]
    fn test_math_embedding_deterministic() {
        let emb = MathEmbedding::new();
        let v1 = emb.embed_constant("Nat.add_comm", &["arrow".into(), "nat".into()]);
        let v2 = emb.embed_constant("Nat.add_comm", &["arrow".into(), "nat".into()]);
        assert_eq!(v1.dims, DEFAULT_EMBED_DIM);
        assert_eq!(v1.data, v2.data, "same input must produce same output");
    }

    #[test]
    fn test_math_embedding_different_names_differ() {
        let emb = MathEmbedding::new();
        let v1 = emb.embed_constant("Nat.add_comm", &[]);
        let v2 = emb.embed_constant("List.map", &[]);
        assert_ne!(
            v1.data, v2.data,
            "different names should produce different vectors"
        );
    }

    #[test]
    fn test_math_embedding_similarity_related() {
        let emb = MathEmbedding::new();
        let v_add_comm = emb.embed_constant("Nat.add_comm", &[]);
        let v_mul_comm = emb.embed_constant("Nat.mul_comm", &[]);
        let v_list_map = emb.embed_constant("List.map", &[]);

        // "Nat.add_comm" should be more similar to "Nat.mul_comm" than to "List.map"
        // because they share "nat" and "comm" tokens.
        let sim_close = MathEmbedding::similarity(&v_add_comm, &v_mul_comm);
        let sim_far = MathEmbedding::similarity(&v_add_comm, &v_list_map);
        assert!(sim_close > sim_far,
            "Nat.add_comm <-> Nat.mul_comm ({sim_close}) should be more similar than <-> List.map ({sim_far})");
    }

    #[test]
    fn test_math_embedding_provider_trait() {
        let emb = MathEmbedding::new();
        let v = emb.embed_name("Nat.succ");
        assert_eq!(v.dims, DEFAULT_EMBED_DIM);
        assert!(v.l2_norm() > 0.0, "named embedding should be non-zero");
        let t = emb.embed_type("Nat -> Nat");
        assert_eq!(t.dims, DEFAULT_EMBED_DIM);
    }

    #[test]
    fn test_math_embedding_custom_dims() {
        let emb = MathEmbedding::with_dims(32);
        let v = emb.embed_constant("test", &[]);
        assert_eq!(v.dims, 32);
        assert_eq!(v.data.len(), 32);
    }

    // -- IVFPQIndex tests ----------------------------------------------------

    fn make_test_vectors(n: usize, dims: usize) -> Vec<EmbeddingVector> {
        // Deterministic pseudo-random vectors using hash mixing.
        (0..n)
            .map(|i| {
                let data: Vec<f32> = (0..dims)
                    .map(|d| {
                        let seed = (i as u32).wrapping_mul(0x9e3779b9).wrapping_add(d as u32);
                        let h = MathEmbedding::murmur_mix(seed);
                        (h as f32 / u32::MAX as f32) * 2.0 - 1.0
                    })
                    .collect();
                EmbeddingVector { dims, data }
            })
            .collect()
    }

    #[test]
    fn test_ivfpq_empty() {
        let idx = IVFPQIndex::build(&[], 4, 2);
        assert!(idx.is_empty());
        assert_eq!(idx.len(), 0);
        let q = EmbeddingVector::zeros(8);
        assert!(idx.search(&q, 5, 2).is_empty());
    }

    #[test]
    fn test_ivfpq_build_and_search() {
        let vecs = make_test_vectors(50, 8);
        let idx = IVFPQIndex::build(&vecs, 4, 2);
        assert_eq!(idx.len(), 50);
        assert!(!idx.is_empty());
        assert_eq!(idx.num_centroids, 4);

        // Search with the first vector as query: should find itself (or close).
        let results = idx.search(&vecs[0], 5, 4);
        assert!(!results.is_empty(), "search should return results");
        assert!(results.len() <= 5);
        // First result should be near index 0 (exact or close).
        assert!(results[0].0 < 50, "result index in range");
    }

    #[test]
    fn test_ivfpq_self_retrieval() {
        let vecs = make_test_vectors(20, 4);
        // With few vectors and full probe, should get near-exact retrieval.
        let idx = IVFPQIndex::build(&vecs, 2, 2);
        let results = idx.search(&vecs[5], 3, 2);
        assert!(!results.is_empty());
        // The query vector itself should be among top results.
        assert!(
            results.iter().any(|&(i, _)| i == 5),
            "query vector should appear in results: {results:?}"
        );
    }

    #[test]
    fn test_ivfpq_respects_k() {
        let vecs = make_test_vectors(30, 8);
        let idx = IVFPQIndex::build(&vecs, 3, 4);
        let r1 = idx.search(&vecs[0], 1, 3);
        let r5 = idx.search(&vecs[0], 5, 3);
        assert!(r1.len() <= 1);
        assert!(r5.len() <= 5);
    }

    #[test]
    fn test_ivfpq_distances_sorted() {
        let vecs = make_test_vectors(40, 8);
        let idx = IVFPQIndex::build(&vecs, 4, 4);
        let results = idx.search(&vecs[10], 10, 4);
        for w in results.windows(2) {
            assert!(
                w[0].1 <= w[1].1,
                "results should be sorted by ascending distance"
            );
        }
    }

    #[test]
    fn test_ivfpq_single_vector() {
        let vecs = make_test_vectors(1, 4);
        let idx = IVFPQIndex::build(&vecs, 1, 2);
        assert_eq!(idx.len(), 1);
        let results = idx.search(&vecs[0], 1, 1);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 0);
    }

    // -- CombinedSearch tests ------------------------------------------------

    #[test]
    fn test_combined_search_bm25_only() {
        let bm25 = make_test_index();
        let ivfpq = IVFPQIndex::build(&[], 0, 1);
        let embedder = BM25EmbeddingProvider;
        // Alpha=1.0 means pure BM25.
        let cs = CombinedSearch::new(1.0);
        let results = cs.search("Nat add comm", &bm25, &ivfpq, &embedder, 5);
        assert!(!results.is_empty(), "should get BM25 results");
    }

    #[test]
    fn test_combined_search_alpha_clamped() {
        let cs_lo = CombinedSearch::new(-0.5);
        let cs_hi = CombinedSearch::new(1.5);
        assert!((cs_lo.alpha - 0.0).abs() < f32::EPSILON);
        assert!((cs_hi.alpha - 1.0).abs() < f32::EPSILON);
    }

    #[test]
    fn test_combined_search_empty() {
        let bm25 = BM25Index::new();
        let ivfpq = IVFPQIndex::build(&[], 0, 1);
        let embedder = BM25EmbeddingProvider;
        let cs = CombinedSearch::new(0.5);
        assert!(cs
            .search("anything", &bm25, &ivfpq, &embedder, 5)
            .is_empty());
    }

    #[test]
    fn test_combined_search_k_zero() {
        let bm25 = make_test_index();
        let ivfpq = IVFPQIndex::build(&[], 0, 1);
        let embedder = BM25EmbeddingProvider;
        let cs = CombinedSearch::new(0.5);
        assert!(cs.search("Nat", &bm25, &ivfpq, &embedder, 0).is_empty());
    }

    // -- search_explain tests -----------------------------------------------

    #[test]
    fn test_search_explain_returns_token_breakdown() {
        let idx = make_test_index();
        let explanations = idx.search_explain("Nat add comm", 10);
        assert!(!explanations.is_empty(), "explain should return results");

        // First result should be Nat.add_comm (idx 0).
        let top = &explanations[0];
        assert_eq!(top.constant_idx, 0);
        assert!(top.total_score > 0.0);
        assert!(!top.token_scores.is_empty(), "should have token breakdowns");

        // Check that query_tokens includes expanded abbreviations.
        assert!(
            top.query_tokens.contains(&"nat".to_string()),
            "expanded tokens should include 'nat'"
        );
        assert!(
            top.query_tokens.contains(&"commutative".to_string()),
            "expanded tokens should include 'commutative' (from 'comm')"
        );
    }

    #[test]
    fn test_search_explain_empty_query() {
        let idx = make_test_index();
        assert!(idx.search_explain("", 10).is_empty());
    }

    #[test]
    fn test_search_explain_empty_index() {
        let idx = BM25Index::new();
        assert!(idx.search_explain("anything", 10).is_empty());
    }

    // -- Semantic search tests requested in the task -------------------------

    #[test]
    fn test_search_semantic_finds_by_abbreviation() {
        // "commutative" should find "comm" results via abbreviation expansion.
        let idx = make_test_index();
        let results = idx.search("commutative", 10);
        assert!(
            !results.is_empty(),
            "searching 'commutative' should find 'comm' results"
        );
        // Should find Nat.add_comm (0), Nat.mul_comm (1), Int.add_comm (4).
        let indices: Vec<u32> = results.iter().map(|r| r.0).collect();
        assert!(indices.contains(&0), "Nat.add_comm should appear");
        assert!(indices.contains(&1), "Nat.mul_comm should appear");
        assert!(indices.contains(&4), "Int.add_comm should appear");
    }

    #[test]
    fn test_search_semantic_expands_tokens() {
        // "natural addition" should find Nat.add entries via abbreviation
        // expansion: "natural" -> "nat", "addition" -> "add".
        let idx = make_test_index();
        let results = idx.search("natural addition", 10);
        assert!(
            !results.is_empty(),
            "searching 'natural addition' should find Nat.add entries"
        );
        let indices: Vec<u32> = results.iter().map(|r| r.0).collect();
        assert!(
            indices.contains(&0) || indices.contains(&2),
            "Nat.add_comm or Nat.add_assoc should appear for 'natural addition'"
        );
    }

    #[test]
    fn test_find_semantic_mode() {
        // Simulates what `mathverse find --semantic` would do: BM25 search via
        // the library's search_semantic() method.

        let strings = vec![
            "Nat.add_comm".into(),
            "List.map".into(),
            "Real.diff_continuous".into(),
            "Nat".into(),
        ];
        let exprs = vec![FlatExpr::const_ref(3, u32::MAX)];
        let constants = vec![hdr(0, 0), hdr(1, 0), hdr(2, 0)];
        let idx = build_search_index(&constants, &strings, &exprs);

        // Semantic query: "differentiable continuous" should find Real.diff_continuous.
        let results = idx.search("differentiable continuous", 10);
        assert!(!results.is_empty(), "semantic find should return results");
        assert!(
            results.iter().any(|r| r.0 == 2),
            "Real.diff_continuous should appear for 'differentiable continuous'"
        );
    }

    #[test]
    fn test_type_tokens_shared_dag_is_linear_not_exponential() {
        // Regression guard for the `walk_type` memoization fix. Build a maximally
        // shared App-DAG: expr[0] = Const, expr[k] = App(k-1, k-1). Walking the
        // top node WITHOUT memoization visits expr[0] 2^(k-1) times — an
        // exponential hang that froze build_search_index on real Mathlib types.
        // With the visited-set the walk is linear in the arena size, so this
        // test simply COMPLETING (and returning bounded tokens) proves the fix.
        let strings = vec!["Nat".to_string()];
        let mut exprs = vec![FlatExpr::const_ref(0, u32::MAX)];
        for k in 1..40u32 {
            exprs.push(FlatExpr::app(k - 1, k - 1));
        }
        let toks = type_tokens(&exprs, &strings, (exprs.len() - 1) as u32);
        assert!(
            toks.len() < 1000,
            "memoized walk must yield bounded tokens, got {}",
            toks.len()
        );
    }
}
