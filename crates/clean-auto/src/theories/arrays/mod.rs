// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Array theory solver implementing select/store with read-over-write axioms.
//!
//! Supports `select(a, i)` (read) and `store(a, i, v)` (write) with axioms:
//! - ROW-same: `select(store(a, i, v), i) = v`
//! - ROW-diff: `i ≠ j → select(store(a, i, v), j) = select(a, j)`
//! - Lazy extensionality via solver-generated witness clauses:
//!   `a = b OR select(a, k_ab) != select(b, k_ab)`

mod stats;
mod theory;

pub(crate) use theory::ArrayTheory;

#[cfg(test)]
mod extensionality_tests;
#[cfg(test)]
mod tests;
