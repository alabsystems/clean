// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E-graph for congruence closure (ported from egg/Z3)
//!
//! An E-graph (equivalence graph) is a data structure that efficiently maintains
//! equivalence classes of terms and supports congruence closure.
//!
//! # Core Concepts
//!
//! - **E-node**: A function application `f(a, b, c, ...)` where the arguments
//!   are e-class IDs rather than terms directly.
//! - **E-class**: An equivalence class containing multiple e-nodes that are
//!   all considered equal.
//! - **Congruence**: If `f(a) = f(b)` when `a = b` (for all arguments).
//!
//! # Usage
//!
//! Internal solver code uses this module directly:
//!
//! ```text
//! use crate::egraph::EGraph;
//!
//! let mut egraph = EGraph::new();
//!
//! // Add terms: f(a, b) and f(a, c)
//! let a = egraph.add_const("a");
//! let b = egraph.add_const("b");
//! let c = egraph.add_const("c");
//! let fab = egraph.add_app("f", vec![a, b]);
//! let fac = egraph.add_app("f", vec![a, c]);
//!
//! // Assert b = c
//! egraph.union(b, c);
//!
//! // By congruence, f(a, b) = f(a, c)
//! assert!(egraph.are_equal(fab, fac));
//! ```
//!
//! External callers should use the crate's supported entry points such as
//! `SmtBridge` and `AutomationEngine` instead of importing `egraph` directly.
//!
//! # Algorithm
//!
//! The congruence closure algorithm works by:
//! 1. Maintaining a union-find for e-class membership
//! 2. Using a hashcons to deduplicate e-nodes
//! 3. Propagating equalities via congruence when e-classes merge

mod ematch;
mod graph;
mod term;
mod types;

pub use ematch::*;
pub use graph::*;
pub use term::*;
pub use types::*;

#[cfg(test)]
mod tests;
