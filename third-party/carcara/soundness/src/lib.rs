// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Mechanical rule-soundness battery for the vendored Carcara checker.
//!
//! The battery never trusts Carcara to judge its own output. It generates instances for every
//! rule (seeds harvested from Carcara's rule tests, syntactic mutants of those seeds, and
//! systematic generators for the rule families whose conclusions are computed), runs the real
//! `ProofChecker`, and judges every accepted step with an independent SMT-LIB evaluator over
//! exhaustive or sampled models. An accepted step whose premises hold and whose conclusion is
//! definitely false in some model is a soundness bug in the checker.

pub mod datatypes;
pub mod eval;
pub mod gen;
pub mod literals;
pub mod model;
pub mod mutate;
pub mod oracle;
pub mod regex;
pub mod run;
pub mod seeds;
pub mod sexp;
pub mod sort;
pub mod value;
pub mod worker;
pub mod zero_extend;
