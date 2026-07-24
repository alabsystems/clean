// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof reconstruction for SMT solving
//!
//! This module provides proof term construction from SMT proof traces.
//! When the SMT solver proves a goal, we need to reconstruct a kernel-valid
//! proof term that witnesses the validity.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                    Proof Reconstruction                         │
//! ├─────────────────────────────────────────────────────────────────┤
//! │                                                                  │
//! │  E-graph Union  ──────────► ProofStep ──────────► Kernel Expr   │
//! │  (with reason)    record     (trace)    build    (proof term)   │
//! │                                                                  │
//! │  Proof steps:                                                    │
//! │  - Refl(a)           →  Eq.refl a                               │
//! │  - Symm(pf)          →  Eq.symm pf                              │
//! │  - Trans(pf1, pf2)   →  Eq.trans pf1 pf2                        │
//! │  - Congr(f, args)    →  congrArg f (proof for args)             │
//! │  - Asserted(hyp_id)  →  reference to hypothesis                 │
//! │                                                                  │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Proof Generation Strategy
//!
//! For equality goals like `a = b`, we:
//! 1. Find a path in the E-graph from e-class(a) to e-class(b)
//! 2. Each edge is either a direct assertion or a congruence step
//! 3. Build proof terms for each step and compose with transitivity

mod builder;
mod congr;
mod forest;
mod step;
mod trace;

pub use builder::*;
pub use forest::*;
pub use step::*;
pub use trace::*;

#[cfg(test)]
mod tests;
