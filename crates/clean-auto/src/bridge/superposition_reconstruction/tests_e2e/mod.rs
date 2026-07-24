// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests: SuperpositionReconstructor.reconstruct() produces proofs
//! that type-check through the kernel via TypeChecker.
//!
//! These tests build complete refutation traces, call reconstruct(), and verify
//! the resulting proof term has type `False` when type-checked with a local
//! context containing the input hypotheses.
//!
//! Uses axiom constants `testA` and `testB` (not Nat.zero/succ) to avoid
//! shared subterms. The position-aware motive test
//! (`test_superposition_position_aware_motive_type_checks`) verifies correct
//! behavior when lhs appears multiple times in the clause.

mod basic_refutations;
mod equality_factoring;
mod equality_resolution;
mod goal_by_contradiction;
mod goal_eq_true_bridge;
mod goal_implies_iff;
mod goal_or;
mod goal_or3;
mod rewrite_demodulation;
mod rewrite_positions;
mod support;
