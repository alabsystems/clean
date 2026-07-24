// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proptest-based property-based fuzz tests for sat_verify checkers.
//!
//! Complements the xorshift-PRNG tests in [`super::fuzz_tests`] by leveraging
//! proptest's shrinking: when a soundness property fails, proptest minimizes
//! the counterexample to the smallest input that still triggers the failure.
//! This is especially valuable for catching soundness bugs, where minimal
//! reproductions are much easier to debug than random large cases.
//!
//! Each `proptest!` block runs 256 cases by default (proptest's `ProptestConfig`
//! default). Per-test overrides use `#![proptest_config(...)]`.
//!
//! ## Properties checked
//!
//! All checkers share one critical property: **soundness**. A proof system is
//! sound if it can never produce a valid refutation of a satisfiable formula.
//! The tests below generate random inputs and assert:
//!
//! 1. **Determinism:** verifying the same proof twice gives the same answer.
//! 2. **No panics:** random inputs must not panic (only return errors).
//! 3. **Soundness on SAT formulas:** no random proof can refute a clearly
//!    satisfiable formula.
//! 4. **Invalid-step rejection:** proofs referencing invalid indices or
//!    deleted clauses must fail with a clean error.
//! 5. **Empty-clause rejection on empty database:** you cannot derive the
//!    empty clause from an empty formula.
//!
//! Reference: Issue #3334. See also [`super::fuzz_tests`] for xorshift-based
//! coverage that emphasizes known edge cases over shrinkable properties.

#![cfg(test)]

mod checkers;
mod cross;
mod generators;
mod parsers;
