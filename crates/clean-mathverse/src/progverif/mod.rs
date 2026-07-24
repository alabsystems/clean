// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Program verification certificate import infrastructure.
//!
//! Imports proof certificates from 7+ program verification systems into Mathverse
//! format. Each importer extracts verification conditions (VCs) from the tool,
//! tracks axiom profiles and trust levels, and optionally replays SMT proof
//! certificates via the shared `SmtVcBundle` / `CertReplayStrategy` pipeline.
//!
//! Supported systems:
//! - **Dafny** — Boogie VCs with Z3 certificates
//! - **Why3** — SMT-LIB VCs with solver certificates
//! - **PVS** — Higher-order logic with predicate subtypes
//! - **ACL2** — First-order logic with induction schemes
//! - **Nuprl** — Constructive type theory (CTT)
//! - **Liquid Haskell** — Refinement type constraints
//! - **KeY / Frama-C / SPARK** — JML/ACSL annotation VCs
//! - **F\*** — Dependent types with SMT-backed effects
//! - **Metamath** — Minimal axiom set with explicit substitution proofs
//! - **HOL family** — HOL Light, HOL4, Isabelle/HOL via OpenTheory

pub mod cert_replay;
pub mod smt_bridge;

pub mod acl2;
pub mod alloy;
pub mod dafny;
pub mod eth_act;
pub mod fstar;
pub mod hol;
pub mod k_framework;
pub mod key_framac_spark;
pub mod liquid_haskell;
pub mod metamath;
pub mod nuprl;
pub mod p_lang;
pub mod pipeline;
pub mod pvs;
pub mod sail;
pub mod specannot;
pub mod sv_benchmarks;
pub mod why3;

#[cfg(test)]
mod tests;

// Re-export core types at module level.
pub use cert_replay::{
    CertReplayError, CertReplayResult, CertReplayStrategy, Certificate, CertificateFormat,
    NullReplayStrategy,
};
pub use smt_bridge::{
    translate_smt_sort_to_clean, Quantifier, SmtAssertion, SmtBridgeError, SmtLiteral, SmtSort,
    SmtTerm, SmtVcBundle,
};
