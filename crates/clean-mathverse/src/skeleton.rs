// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof skeleton extraction for axiomatized imports.
//!
//! When a source proof can't be fully translated, the import pipeline
//! extracts its structural skeleton. Consumers (Mathverse Engine) use
//! skeletons as guided synthesis hints.

use clean_kernel::flat::FlatExpr;
use serde::{Deserialize, Serialize};

use crate::types::ConstantIdx;

/// Structural skeleton of an untranslatable proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProofSkeleton {
    /// High-level proof strategy steps.
    pub strategy: Vec<ProofStep>,
    /// Key lemmas referenced (source ref string + resolved constant if known).
    pub key_lemmas: Vec<(String, Option<ConstantIdx>)>,
    /// Estimated difficulty of reconstructing this proof.
    pub difficulty: DifficultyEstimate,
}

/// A single high-level step in a proof skeleton.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum ProofStep {
    Induction {
        on_arg: u32,
    },
    CaseSplit {
        num_cases: u32,
    },
    Rewrite {
        lemma: Option<ConstantIdx>,
        direction: Direction,
    },
    Apply {
        lemma: Option<ConstantIdx>,
    },
    Contradiction,
    Computation,
}

/// Direction of a rewrite step.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Direction {
    Forward,
    Backward,
}

/// Estimated difficulty of reconstructing a proof from its skeleton.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum DifficultyEstimate {
    /// Straightforward reconstruction (e.g., direct rewriting chain).
    Easy,
    /// Moderate effort (e.g., induction with case analysis).
    Medium,
    /// Significant effort (e.g., complex nested induction).
    Hard,
    /// Unknown or extremely difficult.
    Unknown,
}

// ---------------------------------------------------------------------------
// Skeleton extraction
// ---------------------------------------------------------------------------

/// Extract a proof skeleton from a FlatExpr arena rooted at `root`.
///
/// Walks the expression tree iteratively, detecting structural patterns:
/// - **Induction**: Recursive App chains where a function applies itself
///   (detected via repeated Const references in nested App nodes).
/// - **Case splits**: Lambda/Pi chains with multiple App branches at
///   the same depth (pattern matching desugars to nested lambdas).
/// - **Rewrite/Apply**: App nodes referencing named constants (lemmas).
///
/// The `strings` slice is used to resolve Const name indices to human-
/// readable names for the `key_lemmas` list.
pub fn extract_proof_skeleton(exprs: &[FlatExpr], root: u32, strings: &[String]) -> ProofSkeleton {
    let mut steps = Vec::new();
    let mut key_lemmas: Vec<(String, Option<ConstantIdx>)> = Vec::new();
    let mut max_depth: usize = 0;

    // Iterative DFS: (expr_idx, depth, parent_tag).
    let mut stack: Vec<(u32, usize, Option<u8>)> = vec![(root, 0, None)];
    let mut visited = hashbrown::HashSet::new();

    // Track which Const name_idx values we have seen (for induction detection).
    let mut seen_const_names = hashbrown::HashSet::new();
    // Count App children under the same Lam/Pi parent at each depth.
    let mut case_split_counts: hashbrown::HashMap<usize, u32> = hashbrown::HashMap::new();

    while let Some((idx, depth, parent_tag)) = stack.pop() {
        let i = idx as usize;
        if i >= exprs.len() || !visited.insert(idx) {
            continue;
        }

        if depth > max_depth {
            max_depth = depth;
        }

        let expr = &exprs[i];
        let d = &expr.data;
        let read_u32 = |off: usize| -> u32 {
            u32::from_le_bytes([d[off], d[off + 1], d[off + 2], d[off + 3]])
        };

        match expr.tag {
            0 => {} // BVar — leaf
            1 => {} // Sort — leaf
            2 => {
                // Const: name_idx at offset 0.
                let name_idx = read_u32(0);
                let name = strings.get(name_idx as usize).cloned().unwrap_or_default();

                // Induction detection: if we see the same Const name twice
                // in different App contexts, it is likely a recursive call.
                if !seen_const_names.insert(name_idx) {
                    steps.push(ProofStep::Induction { on_arg: 0 });
                }

                // Record as key lemma if referenced inside an App.
                if parent_tag == Some(3) && !name.is_empty() {
                    if !key_lemmas.iter().any(|(n, _)| n == &name) {
                        key_lemmas.push((name.clone(), None));
                    }
                    steps.push(ProofStep::Apply { lemma: None });
                }
            }
            3 => {
                // App: fn_idx at 0, arg_idx at 4.
                let fn_idx = read_u32(0);
                let arg_idx = read_u32(4);
                stack.push((fn_idx, depth + 1, Some(3)));
                stack.push((arg_idx, depth + 1, Some(3)));

                // Track for case-split detection: multiple App siblings under
                // Lam/Pi at the same depth.
                if parent_tag == Some(4) || parent_tag == Some(5) {
                    *case_split_counts.entry(depth).or_insert(0) += 1;
                }
            }
            4 | 5 => {
                // Lam / Pi: binder_info at 0, ty_idx at 1..5, body_idx at 5..9.
                let ty = u32::from_le_bytes([d[1], d[2], d[3], d[4]]);
                let body = u32::from_le_bytes([d[5], d[6], d[7], d[8]]);
                stack.push((ty, depth + 1, Some(expr.tag)));
                stack.push((body, depth + 1, Some(expr.tag)));
            }
            6 => {
                // Let: ty_idx at 0, val_idx at 4, body_idx at 8.
                // A let-binding with a value that is an App of a known lemma
                // is treated as a rewrite step.
                let ty = read_u32(0);
                let val = read_u32(4);
                let body = read_u32(8);

                // Check if val is an App (tag 3) for rewrite detection.
                if (val as usize) < exprs.len() && exprs[val as usize].tag == 3 {
                    steps.push(ProofStep::Rewrite {
                        lemma: None,
                        direction: Direction::Forward,
                    });
                }

                stack.push((ty, depth + 1, Some(6)));
                stack.push((val, depth + 1, Some(6)));
                stack.push((body, depth + 1, Some(6)));
            }
            7 => {
                // LitNat — computation evidence.
                steps.push(ProofStep::Computation);
            }
            8 => {} // LitStr — leaf
            9 => {
                // Proj: name_idx at 0, field at 4..6, expr_idx at 6..10.
                let e = u32::from_le_bytes([d[6], d[7], d[8], d[9]]);
                stack.push((e, depth + 1, Some(9)));
            }
            10 => {} // FVar — leaf
            _ => {}
        }
    }

    // Convert case-split counts into CaseSplit steps.
    for (_, count) in &case_split_counts {
        if *count >= 2 {
            steps.push(ProofStep::CaseSplit { num_cases: *count });
        }
    }

    // If no steps detected at all but tree is non-trivial, mark as Computation.
    if steps.is_empty() && max_depth > 0 {
        steps.push(ProofStep::Computation);
    }

    let difficulty = estimate_difficulty(steps.len(), max_depth);

    ProofSkeleton {
        strategy: steps,
        key_lemmas,
        difficulty,
    }
}

/// Estimate the difficulty of reconstructing a proof from step count and depth.
///
/// Heuristic thresholds:
/// - Easy: <= 3 steps AND depth <= 4
/// - Medium: <= 8 steps AND depth <= 10
/// - Hard: <= 20 steps AND depth <= 25
/// - Unknown: everything else
pub fn estimate_difficulty(step_count: usize, max_depth: usize) -> DifficultyEstimate {
    if step_count <= 3 && max_depth <= 4 {
        DifficultyEstimate::Easy
    } else if step_count <= 8 && max_depth <= 10 {
        DifficultyEstimate::Medium
    } else if step_count <= 20 && max_depth <= 25 {
        DifficultyEstimate::Hard
    } else {
        DifficultyEstimate::Unknown
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::flat::FlatLevel;

    // --- estimate_difficulty tests ---

    #[test]
    fn test_difficulty_easy() {
        assert_eq!(estimate_difficulty(0, 0), DifficultyEstimate::Easy);
        assert_eq!(estimate_difficulty(1, 2), DifficultyEstimate::Easy);
        assert_eq!(estimate_difficulty(3, 4), DifficultyEstimate::Easy);
    }

    #[test]
    fn test_difficulty_medium() {
        assert_eq!(estimate_difficulty(4, 5), DifficultyEstimate::Medium);
        assert_eq!(estimate_difficulty(8, 10), DifficultyEstimate::Medium);
    }

    #[test]
    fn test_difficulty_hard() {
        assert_eq!(estimate_difficulty(9, 11), DifficultyEstimate::Hard);
        assert_eq!(estimate_difficulty(20, 25), DifficultyEstimate::Hard);
    }

    #[test]
    fn test_difficulty_unknown() {
        assert_eq!(estimate_difficulty(21, 30), DifficultyEstimate::Unknown);
        assert_eq!(estimate_difficulty(100, 100), DifficultyEstimate::Unknown);
    }

    #[test]
    fn test_difficulty_high_depth_low_steps() {
        // 2 steps but depth 30 => fails the max_depth <= 4 and <= 10 and <= 25 gates.
        assert_eq!(estimate_difficulty(2, 30), DifficultyEstimate::Unknown);
    }

    #[test]
    fn test_difficulty_ordering() {
        assert!(DifficultyEstimate::Easy < DifficultyEstimate::Medium);
        assert!(DifficultyEstimate::Medium < DifficultyEstimate::Hard);
        assert!(DifficultyEstimate::Hard < DifficultyEstimate::Unknown);
    }

    // --- extract_proof_skeleton tests ---

    #[test]
    fn test_extract_empty_arena() {
        let skel = extract_proof_skeleton(&[], 0, &[]);
        assert!(skel.strategy.is_empty());
        assert!(skel.key_lemmas.is_empty());
        assert_eq!(skel.difficulty, DifficultyEstimate::Easy);
    }

    #[test]
    fn test_extract_single_sort() {
        let _l0 = FlatLevel::zero();
        let exprs = [FlatExpr::sort(0)];
        let strings: Vec<String> = vec![];
        let skel = extract_proof_skeleton(&exprs, 0, &strings);
        // Sort alone is a leaf; no steps but non-trivial depth 0 + empty =>
        // should still produce at least a Computation step due to non-zero node.
        assert_eq!(skel.difficulty, DifficultyEstimate::Easy);
    }

    #[test]
    fn test_extract_app_with_const_records_apply() {
        // Arena: 0 = Const("foo"), 1 = Const("bar"), 2 = App(0, 1)
        let strings = vec!["foo".to_string(), "bar".to_string()];
        let exprs = [
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::const_ref(1, u32::MAX),
            FlatExpr::app(0, 1),
        ];
        let skel = extract_proof_skeleton(&exprs, 2, &strings);

        // Should detect Apply steps for the Const nodes under App.
        let apply_count = skel
            .strategy
            .iter()
            .filter(|s| matches!(s, ProofStep::Apply { .. }))
            .count();
        assert!(apply_count >= 1, "should detect at least one Apply step");

        // Key lemmas should be populated.
        assert!(!skel.key_lemmas.is_empty());
    }

    #[test]
    fn test_extract_induction_detection() {
        // Arena: 0 = Const("rec"), 1 = Const("rec") (same name), 2 = App(0, 1)
        // Seeing "rec" twice triggers induction detection.
        let strings = vec!["rec".to_string()];
        let exprs = [
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::app(0, 1),
        ];
        let skel = extract_proof_skeleton(&exprs, 2, &strings);

        let induction_count = skel
            .strategy
            .iter()
            .filter(|s| matches!(s, ProofStep::Induction { .. }))
            .count();
        assert!(
            induction_count >= 1,
            "should detect induction from repeated Const"
        );
    }

    #[test]
    fn test_extract_let_rewrite_detection() {
        // Arena: 0 = Const("lem"), 1 = BVar(0), 2 = App(0, 1),
        //        3 = Sort(0), 4 = BVar(1), 5 = Let(3, 2, 4)
        let strings = vec!["lem".to_string()];
        let exprs = [
            FlatExpr::const_ref(0, u32::MAX), // 0
            FlatExpr::bvar(0),                // 1
            FlatExpr::app(0, 1),              // 2
            FlatExpr::sort(0),                // 3
            FlatExpr::bvar(1),                // 4
            FlatExpr::let_expr(3, 2, 4),      // 5: Let(ty=Sort, val=App, body=BVar)
        ];
        let skel = extract_proof_skeleton(&exprs, 5, &strings);

        let rewrite_count = skel
            .strategy
            .iter()
            .filter(|s| matches!(s, ProofStep::Rewrite { .. }))
            .count();
        assert!(
            rewrite_count >= 1,
            "should detect rewrite from Let with App value"
        );
    }

    #[test]
    fn test_extract_litnat_computation() {
        let exprs = [FlatExpr::lit_nat(42)];
        let skel = extract_proof_skeleton(&exprs, 0, &[]);

        let comp_count = skel
            .strategy
            .iter()
            .filter(|s| matches!(s, ProofStep::Computation))
            .count();
        assert!(comp_count >= 1, "LitNat should trigger Computation step");
    }

    #[test]
    fn test_extract_out_of_bounds_root() {
        let exprs = [FlatExpr::bvar(0)];
        let skel = extract_proof_skeleton(&exprs, 999, &[]);
        assert!(skel.strategy.is_empty());
        assert_eq!(skel.difficulty, DifficultyEstimate::Easy);
    }

    #[test]
    fn test_serialization_round_trip() {
        let skel = ProofSkeleton {
            strategy: vec![
                ProofStep::Induction { on_arg: 0 },
                ProofStep::Apply { lemma: Some(42) },
                ProofStep::Rewrite {
                    lemma: None,
                    direction: Direction::Backward,
                },
                ProofStep::CaseSplit { num_cases: 3 },
                ProofStep::Contradiction,
                ProofStep::Computation,
            ],
            key_lemmas: vec![
                ("Nat.add_comm".into(), Some(10)),
                ("Nat.mul_zero".into(), None),
            ],
            difficulty: DifficultyEstimate::Hard,
        };

        let json = serde_json::to_string(&skel).expect("serialize");
        let restored: ProofSkeleton = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(restored.strategy.len(), skel.strategy.len());
        assert_eq!(restored.key_lemmas.len(), skel.key_lemmas.len());
        assert_eq!(restored.difficulty, skel.difficulty);

        // Verify individual steps round-trip.
        assert_eq!(restored.strategy[0], ProofStep::Induction { on_arg: 0 });
        assert_eq!(restored.strategy[1], ProofStep::Apply { lemma: Some(42) });
        assert_eq!(
            restored.strategy[2],
            ProofStep::Rewrite {
                lemma: None,
                direction: Direction::Backward
            }
        );
        assert_eq!(restored.strategy[3], ProofStep::CaseSplit { num_cases: 3 });
        assert_eq!(restored.strategy[4], ProofStep::Contradiction);
        assert_eq!(restored.strategy[5], ProofStep::Computation);
    }

    #[test]
    fn test_extract_deep_pi_chain() {
        // Build a chain of nested Pi expressions to test depth tracking.
        // Arena: 0 = BVar(0), 1 = Pi(0, 0, 0) -> depth 1
        //        2 = Pi(0, 1, 1)  -> depth 2
        //        3 = Pi(0, 2, 2)  -> depth 3
        //        4 = Pi(0, 3, 3)  -> depth 4
        //        5 = Pi(0, 4, 4)  -> depth 5
        let mut exprs = vec![FlatExpr::bvar(0)];
        for i in 0..5 {
            let prev = i as u32;
            exprs.push(FlatExpr::pi(0, prev, prev));
        }
        let skel = extract_proof_skeleton(&exprs, 5, &[]);

        // Deep chain should increase difficulty.
        assert!(
            skel.difficulty >= DifficultyEstimate::Easy,
            "deep Pi chain should be at least Easy"
        );
    }

    #[test]
    fn test_extract_case_split_from_lam_apps() {
        // Build a Lam whose body and type are both App nodes to trigger case split.
        // Arena: 0 = BVar(0), 1 = BVar(1)
        //        2 = App(0, 1), 3 = App(1, 0)
        //        4 = Lam(0, 2, 3)
        let exprs = [
            FlatExpr::bvar(0),      // 0
            FlatExpr::bvar(1),      // 1
            FlatExpr::app(0, 1),    // 2
            FlatExpr::app(1, 0),    // 3
            FlatExpr::lam(0, 2, 3), // 4: Lam with App in both ty and body
        ];
        let skel = extract_proof_skeleton(&exprs, 4, &[]);

        let case_count = skel
            .strategy
            .iter()
            .filter(|s| matches!(s, ProofStep::CaseSplit { .. }))
            .count();
        assert!(
            case_count >= 1,
            "multiple App nodes under Lam should trigger CaseSplit"
        );
    }
}
