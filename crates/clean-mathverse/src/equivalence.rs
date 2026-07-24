// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-system equivalence detection and indexing.
//!
//! Finds the "same" theorem across proof systems (Lean 4, Coq, Isabelle, HOL
//! Light, Mizar) via type fingerprinting and name normalization heuristics.

use clean_kernel::flat::{FlatExpr, FlatTag};
use hashbrown::HashMap;

use crate::graph_alpha::EquivConfidence;
use crate::types::{ConstantIdx, ExprIdx, SourceSystem};

/// Fingerprint of a type expression for fast structural comparison.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeFingerprint {
    pub arity: u32,
    pub const_count: u32,
    pub const_hashes: Vec<u64>,
    pub depth: u32,
}

/// Cross-system equivalence detector.
pub struct EquivalenceDetector {
    type_fingerprints: HashMap<TypeFingerprint, Vec<ConstantIdx>>,
    constant_meta: HashMap<ConstantIdx, ConstantMeta>,
}

struct ConstantMeta {
    normalized_name: String,
    source: SourceSystem,
    fingerprint: TypeFingerprint,
}

/// Normalize a constant name for cross-system matching.
///
/// Strips module prefixes, case-folds, and normalizes separators so that the
/// "same" theorem in different proof systems maps to the same canonical name.
pub fn normalize_name(name: &str, source: SourceSystem) -> String {
    let base = match source {
        SourceSystem::Lean4 | SourceSystem::Coq => strip_deep_prefix(name, '.'),
        SourceSystem::Isabelle => name.rsplit('.').next().unwrap_or(name).to_owned(),
        SourceSystem::HolLight | SourceSystem::Hol4 => {
            name.rsplit('.').next().unwrap_or(name).to_lowercase()
        }
        SourceSystem::Metamath => name.rsplit(':').next().unwrap_or(name).to_owned(),
        SourceSystem::Mizar => name.split(':').next().unwrap_or(name).to_lowercase(),
        _ => name.rsplit('.').next().unwrap_or(name).to_owned(),
    };
    base.to_lowercase().replace(['.', ' '], "_")
}

fn strip_deep_prefix(name: &str, sep: char) -> String {
    let parts: Vec<&str> = name.split(sep).collect();
    if parts.len() <= 2 {
        name.to_owned()
    } else {
        format!("{}.{}", parts[parts.len() - 2], parts[parts.len() - 1])
    }
}

/// Known cross-system name equivalences (hand-curated seed set).
pub fn known_equivalences() -> Vec<(&'static str, &'static [(&'static str, SourceSystem)])> {
    vec![
        (
            "nat_add_comm",
            &[
                ("Nat.add_comm", SourceSystem::Lean4),
                ("PeanoNat.Nat.add_comm", SourceSystem::Coq),
                ("Nat.add.comm", SourceSystem::Lean4),
            ][..],
        ),
        (
            "nat_add_assoc",
            &[
                ("Nat.add_assoc", SourceSystem::Lean4),
                ("PeanoNat.Nat.add_assoc", SourceSystem::Coq),
            ][..],
        ),
        (
            "nat_mul_comm",
            &[
                ("Nat.mul_comm", SourceSystem::Lean4),
                ("PeanoNat.Nat.mul_comm", SourceSystem::Coq),
            ][..],
        ),
        (
            "nat_zero_add",
            &[
                ("Nat.zero_add", SourceSystem::Lean4),
                ("PeanoNat.Nat.add_0_l", SourceSystem::Coq),
            ][..],
        ),
        (
            "bool_not_not",
            &[
                ("Bool.not_not", SourceSystem::Lean4),
                ("Bool.negb_involutive", SourceSystem::Coq),
            ][..],
        ),
    ]
}

/// Compute a type fingerprint from a FlatExpr arena.
pub fn fingerprint_type(exprs: &[FlatExpr], root: ExprIdx) -> TypeFingerprint {
    let mut arity = 0u32;
    let mut const_set = hashbrown::HashSet::new();
    let mut depth = 0u32;
    walk_fp(exprs, root, 0, &mut arity, &mut const_set, &mut depth);
    let mut const_hashes: Vec<u64> = const_set.into_iter().collect();
    const_hashes.sort_unstable();
    TypeFingerprint {
        arity,
        const_count: const_hashes.len() as u32,
        const_hashes,
        depth,
    }
}

fn read_u32(data: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([data[off], data[off + 1], data[off + 2], data[off + 3]])
}

fn walk_fp(
    exprs: &[FlatExpr],
    idx: ExprIdx,
    d: u32,
    arity: &mut u32,
    consts: &mut hashbrown::HashSet<u64>,
    max_d: &mut u32,
) {
    let Some(e) = exprs.get(idx as usize) else {
        return;
    };
    *max_d = (*max_d).max(d + 1);
    match e.tag {
        t if t == FlatTag::Pi as u8 => {
            *arity += 1;
            walk_fp(exprs, read_u32(&e.data, 1), d + 1, arity, consts, max_d);
            walk_fp(exprs, read_u32(&e.data, 5), d + 1, arity, consts, max_d);
        }
        t if t == FlatTag::Lam as u8 => {
            walk_fp(exprs, read_u32(&e.data, 1), d + 1, arity, consts, max_d);
            walk_fp(exprs, read_u32(&e.data, 5), d + 1, arity, consts, max_d);
        }
        t if t == FlatTag::App as u8 => {
            walk_fp(exprs, read_u32(&e.data, 0), d + 1, arity, consts, max_d);
            walk_fp(exprs, read_u32(&e.data, 4), d + 1, arity, consts, max_d);
        }
        t if t == FlatTag::Const as u8 => {
            consts.insert(read_u32(&e.data, 0) as u64);
        }
        t if t == FlatTag::Let as u8 => {
            walk_fp(exprs, read_u32(&e.data, 0), d + 1, arity, consts, max_d);
            walk_fp(exprs, read_u32(&e.data, 4), d + 1, arity, consts, max_d);
            walk_fp(exprs, read_u32(&e.data, 8), d + 1, arity, consts, max_d);
        }
        t if t == FlatTag::Proj as u8 => {
            consts.insert(read_u32(&e.data, 0) as u64);
            walk_fp(exprs, read_u32(&e.data, 6), d + 1, arity, consts, max_d);
        }
        _ => {} // BVar, Sort, FVar, LitNat, LitStr: leaves
    }
}

/// LCS-based name similarity in [0.0, 1.0].
fn name_similarity(a: &str, b: &str) -> f32 {
    if a == b {
        return 1.0;
    }
    if a.is_empty() || b.is_empty() {
        return 0.0;
    }
    let (ab, bb) = (a.as_bytes(), b.as_bytes());
    let (m, n) = (ab.len(), bb.len());
    let mut prev = vec![0u32; n + 1];
    let mut curr = vec![0u32; n + 1];
    for i in 1..=m {
        for j in 1..=n {
            curr[j] = if ab[i - 1] == bb[j - 1] {
                prev[j - 1] + 1
            } else {
                curr[j - 1].max(prev[j])
            };
        }
        std::mem::swap(&mut prev, &mut curr);
        curr.iter_mut().for_each(|v| *v = 0);
    }
    *prev.iter().max().unwrap_or(&0) as f32 / m.max(n) as f32
}

fn score_candidate(
    name_a: &str,
    src_a: SourceSystem,
    name_b: &str,
    src_b: SourceSystem,
    fp_a: &TypeFingerprint,
    fp_b: &TypeFingerprint,
) -> f32 {
    let mut s = 0.0f32;
    if fp_a == fp_b {
        s += 0.5;
    }
    s += name_similarity(
        &normalize_name(name_a, src_a),
        &normalize_name(name_b, src_b),
    ) * 0.3;
    if fp_a.arity == fp_b.arity {
        s += 0.1;
    }
    if src_a != src_b {
        s += 0.1;
    }
    s.min(1.0)
}

fn confidence_from_score(score: f32) -> EquivConfidence {
    if score >= 0.95 {
        EquivConfidence::Exact
    } else if score >= 0.7 {
        EquivConfidence::ErasedCandidate { score }
    } else {
        EquivConfidence::ManualReview
    }
}

impl EquivalenceDetector {
    pub fn new() -> Self {
        Self {
            type_fingerprints: HashMap::new(),
            constant_meta: HashMap::new(),
        }
    }

    /// Index a constant for future equivalence detection.
    pub fn index_constant(
        &mut self,
        idx: ConstantIdx,
        name: &str,
        source: SourceSystem,
        exprs: &[FlatExpr],
        type_idx: ExprIdx,
    ) {
        let fp = fingerprint_type(exprs, type_idx);
        self.type_fingerprints
            .entry(fp.clone())
            .or_default()
            .push(idx);
        self.constant_meta.insert(
            idx,
            ConstantMeta {
                normalized_name: normalize_name(name, source),
                source,
                fingerprint: fp,
            },
        );
    }

    pub fn len(&self) -> usize {
        self.constant_meta.len()
    }
    pub fn is_empty(&self) -> bool {
        self.constant_meta.is_empty()
    }

    /// Find candidate equivalences sorted by confidence (highest first).
    pub fn find_candidates(
        &self,
        idx: ConstantIdx,
        name: &str,
        source: SourceSystem,
        exprs: &[FlatExpr],
        type_idx: ExprIdx,
    ) -> Vec<(ConstantIdx, EquivConfidence)> {
        let fp = fingerprint_type(exprs, type_idx);
        let norm = normalize_name(name, source);
        let mut cands: Vec<(ConstantIdx, f32)> = Vec::new();

        if let Some(bucket) = self.type_fingerprints.get(&fp) {
            for &oi in bucket {
                if oi == idx {
                    continue;
                }
                if let Some(m) = self.constant_meta.get(&oi) {
                    cands.push((
                        oi,
                        score_candidate(
                            name,
                            source,
                            &m.normalized_name,
                            m.source,
                            &fp,
                            &m.fingerprint,
                        ),
                    ));
                }
            }
        }
        for (&oi, m) in &self.constant_meta {
            if oi == idx || cands.iter().any(|(c, _)| *c == oi) {
                continue;
            }
            if name_similarity(&norm, &m.normalized_name) >= 0.6 {
                cands.push((
                    oi,
                    score_candidate(
                        name,
                        source,
                        &m.normalized_name,
                        m.source,
                        &fp,
                        &m.fingerprint,
                    ),
                ));
            }
        }
        cands.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        cands
            .into_iter()
            .map(|(c, s)| (c, confidence_from_score(s)))
            .collect()
    }

    /// Batch detection: returns pairs above `min_score` (lower idx first, deduplicated).
    pub fn detect_all(&self, min_score: f32) -> Vec<(ConstantIdx, ConstantIdx, EquivConfidence)> {
        let mut results = Vec::new();
        let mut seen = hashbrown::HashSet::new();

        // Same-fingerprint bucket pairs.
        for bucket in self.type_fingerprints.values() {
            for (i, &a) in bucket.iter().enumerate() {
                for &b in &bucket[i + 1..] {
                    let pair = (a.min(b), a.max(b));
                    if !seen.insert(pair) {
                        continue;
                    }
                    if let (Some(ma), Some(mb)) =
                        (self.constant_meta.get(&a), self.constant_meta.get(&b))
                    {
                        let s = score_candidate(
                            &ma.normalized_name,
                            ma.source,
                            &mb.normalized_name,
                            mb.source,
                            &ma.fingerprint,
                            &mb.fingerprint,
                        );
                        if s >= min_score {
                            results.push((pair.0, pair.1, confidence_from_score(s)));
                        }
                    }
                }
            }
        }
        // Cross-fingerprint name-similar pairs.
        let all: Vec<ConstantIdx> = self.constant_meta.keys().copied().collect();
        for (i, &a) in all.iter().enumerate() {
            let ma = &self.constant_meta[&a];
            for &b in &all[i + 1..] {
                let pair = (a.min(b), a.max(b));
                if seen.contains(&pair) {
                    continue;
                }
                let mb = &self.constant_meta[&b];
                if name_similarity(&ma.normalized_name, &mb.normalized_name) >= 0.6 {
                    let s = score_candidate(
                        &ma.normalized_name,
                        ma.source,
                        &mb.normalized_name,
                        mb.source,
                        &ma.fingerprint,
                        &mb.fingerprint,
                    );
                    if s >= min_score {
                        seen.insert(pair);
                        results.push((pair.0, pair.1, confidence_from_score(s)));
                    }
                }
            }
        }
        results.sort_by(|a, b| {
            let sc = |c: &EquivConfidence| match c {
                EquivConfidence::Exact => 1.0f32,
                EquivConfidence::ProvedEquivalent => 0.95,
                EquivConfidence::ErasedCandidate { score } => *score,
                EquivConfidence::ManualReview => 0.0,
            };
            sc(&b.2)
                .partial_cmp(&sc(&a.2))
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        results
    }
}

impl Default for EquivalenceDetector {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalize_names() {
        assert_eq!(
            normalize_name("Nat.add_comm", SourceSystem::Lean4),
            "nat_add_comm"
        );
        assert_eq!(
            normalize_name("Mathlib.Data.Nat.add_comm", SourceSystem::Lean4),
            "nat_add_comm"
        );
        assert_eq!(
            normalize_name("PeanoNat.Nat.add_comm", SourceSystem::Coq),
            "nat_add_comm"
        );
        assert_eq!(
            normalize_name("Groups.comm_monoid_class.add_comm", SourceSystem::Isabelle),
            "add_comm"
        );
        assert_eq!(normalize_name("ADD_SYM", SourceSystem::HolLight), "add_sym");
        assert_eq!(
            normalize_name("HOL-Algebra.group_comm", SourceSystem::HolLight),
            "group_comm"
        );
        assert_eq!(normalize_name("NAT_1:def 3", SourceSystem::Mizar), "nat_1");
        assert_eq!(
            normalize_name("set.mm:mulcom", SourceSystem::Metamath),
            "mulcom"
        );
        assert_eq!(
            normalize_name("set.mm:addcom", SourceSystem::Metamath),
            "addcom"
        );
        assert_eq!(normalize_name("", SourceSystem::Lean4), "");
    }

    fn pi_nat_nat_arena() -> Vec<FlatExpr> {
        vec![
            FlatExpr::const_ref(10, u32::MAX), // 0: Nat
            FlatExpr::const_ref(10, u32::MAX), // 1: Nat
            FlatExpr::pi(0, 0, 1),             // 2: Pi(Nat, Nat)
        ]
    }

    #[test]
    fn test_fingerprint_simple_const() {
        let arena = vec![FlatExpr::const_ref(10, u32::MAX)];
        let fp = fingerprint_type(&arena, 0);
        assert_eq!((fp.arity, fp.const_count, fp.depth), (0, 1, 1));
        assert_eq!(fp.const_hashes, vec![10]);
    }

    #[test]
    fn test_fingerprint_pi() {
        let fp = fingerprint_type(&pi_nat_nat_arena(), 2);
        assert_eq!((fp.arity, fp.const_count, fp.depth), (1, 1, 2));
    }

    #[test]
    fn test_fingerprint_different_types_differ() {
        let arena_b = vec![
            FlatExpr::const_ref(10, u32::MAX),
            FlatExpr::const_ref(20, u32::MAX),
            FlatExpr::pi(0, 0, 1),
        ];
        assert_ne!(
            fingerprint_type(&pi_nat_nat_arena(), 2),
            fingerprint_type(&arena_b, 2)
        );
    }

    #[test]
    fn test_fingerprint_stability() {
        let a = pi_nat_nat_arena();
        assert_eq!(fingerprint_type(&a, 2), fingerprint_type(&a, 2));
    }

    #[test]
    fn test_fingerprint_out_of_bounds() {
        let fp = fingerprint_type(&[FlatExpr::sort(0)], 999);
        assert_eq!((fp.arity, fp.const_count, fp.depth), (0, 0, 0));
    }

    #[test]
    fn test_name_similarity() {
        assert!((name_similarity("abc", "abc") - 1.0).abs() < f32::EPSILON);
        assert!((name_similarity("", "abc")).abs() < f32::EPSILON);
        let sim = name_similarity("nat_add_comm", "nat_add_assoc");
        assert!(sim > 0.5 && sim < 1.0);
    }

    #[test]
    fn test_scoring() {
        let fp = TypeFingerprint {
            arity: 2,
            const_count: 1,
            const_hashes: vec![10],
            depth: 3,
        };
        let s = score_candidate(
            "Nat.add_comm",
            SourceSystem::Lean4,
            "PeanoNat.Nat.add_comm",
            SourceSystem::Coq,
            &fp,
            &fp,
        );
        assert!(s > 0.7); // fingerprint(0.5) + name + arity(0.1) + cross(0.1)

        let fp2 = TypeFingerprint {
            arity: 1,
            const_count: 2,
            const_hashes: vec![10, 20],
            depth: 2,
        };
        let s2 = score_candidate(
            "Nat.add_comm",
            SourceSystem::Lean4,
            "List.append",
            SourceSystem::Lean4,
            &fp,
            &fp2,
        );
        assert!(s2 < 0.5);

        let fp0 = TypeFingerprint {
            arity: 0,
            const_count: 0,
            const_hashes: vec![],
            depth: 1,
        };
        assert!(
            score_candidate("x", SourceSystem::Lean4, "x", SourceSystem::Coq, &fp0, &fp0) <= 1.0
        );
    }

    #[test]
    fn test_confidence_from_score() {
        assert_eq!(confidence_from_score(0.99), EquivConfidence::Exact);
        assert!(matches!(
            confidence_from_score(0.8),
            EquivConfidence::ErasedCandidate { .. }
        ));
        assert_eq!(confidence_from_score(0.3), EquivConfidence::ManualReview);
    }

    #[test]
    fn test_detector_index_and_find() {
        let mut det = EquivalenceDetector::new();
        assert!(det.is_empty());
        let arena = pi_nat_nat_arena();
        det.index_constant(0, "Nat.add_comm", SourceSystem::Lean4, &arena, 2);
        det.index_constant(1, "PeanoNat.Nat.add_comm", SourceSystem::Coq, &arena, 2);
        assert_eq!(det.len(), 2);
        let cands = det.find_candidates(0, "Nat.add_comm", SourceSystem::Lean4, &arena, 2);
        assert_eq!(cands.len(), 1);
        assert_eq!(cands[0].0, 1);
    }

    #[test]
    fn test_detector_no_self_match() {
        let mut det = EquivalenceDetector::new();
        let arena = pi_nat_nat_arena();
        det.index_constant(0, "Nat.add_comm", SourceSystem::Lean4, &arena, 2);
        assert!(det
            .find_candidates(0, "Nat.add_comm", SourceSystem::Lean4, &arena, 2)
            .is_empty());
    }

    #[test]
    fn test_detect_all() {
        let mut det = EquivalenceDetector::new();
        let arena = pi_nat_nat_arena();
        det.index_constant(0, "Nat.add_comm", SourceSystem::Lean4, &arena, 2);
        det.index_constant(1, "PeanoNat.Nat.add_comm", SourceSystem::Coq, &arena, 2);
        det.index_constant(2, "List.length", SourceSystem::Lean4, &arena, 2);
        let results = det.detect_all(0.5);
        assert!(!results.is_empty());
        // add_comm cross-system pair should rank first.
        let top = (
            results[0].0.min(results[0].1),
            results[0].0.max(results[0].1),
        );
        assert_eq!(top, (0, 1));
    }

    #[test]
    fn test_detect_all_respects_threshold() {
        let mut det = EquivalenceDetector::new();
        det.index_constant(
            0,
            "Nat.add_comm",
            SourceSystem::Lean4,
            &pi_nat_nat_arena(),
            2,
        );
        det.index_constant(
            1,
            "Bool.false",
            SourceSystem::Lean4,
            &[FlatExpr::const_ref(20, u32::MAX), FlatExpr::sort(0)],
            1,
        );
        assert!(det.detect_all(0.9).is_empty());
    }

    #[test]
    fn test_mixed_lean4_coq() {
        let mut det = EquivalenceDetector::new();
        let arena = vec![
            FlatExpr::const_ref(10, u32::MAX),
            FlatExpr::const_ref(10, u32::MAX),
            FlatExpr::const_ref(10, u32::MAX),
            FlatExpr::pi(0, 1, 2),
            FlatExpr::pi(0, 0, 3),
        ];
        det.index_constant(0, "Nat.add_comm", SourceSystem::Lean4, &arena, 4);
        det.index_constant(1, "PeanoNat.Nat.add_comm", SourceSystem::Coq, &arena, 4);
        det.index_constant(2, "Nat.mul_comm", SourceSystem::Lean4, &arena, 4);
        det.index_constant(3, "PeanoNat.Nat.mul_comm", SourceSystem::Coq, &arena, 4);
        let results = det.detect_all(0.5);
        assert!(results.len() >= 2);
        let top = (
            results[0].0.min(results[0].1),
            results[0].0.max(results[0].1),
        );
        assert!(top == (0, 1) || top == (2, 3));
    }

    #[test]
    fn test_known_equivalences_coverage() {
        for (name, mappings) in known_equivalences() {
            assert!(!name.is_empty());
            assert!(mappings.len() >= 2, "Need >=2 systems: {name}");
        }
    }

    #[test]
    fn test_detector_default() {
        let det = EquivalenceDetector::default();
        assert!(det.is_empty() && det.is_empty());
    }
}
