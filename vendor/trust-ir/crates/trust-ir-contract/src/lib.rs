// trust-ir-contract — cross-repo shared verification vocabulary
//
// The canonical home for the small set of data types that cross the
// Trust <-> backend boundary:
//   - the SMT `Formula` / `Sort` / `Symbol` vocabulary, with the hash-consed
//     `formula_dag::FormulaDag` (each distinct subterm stored once, printed
//     with `let`/`define-fun` sharing) and `formula_census` (every variant,
//     and a witness of each, for exhaustiveness tests),
//   - the basic-block id `BlockId`,
//   - the translation-validation data records (`CheckKind`, `TranslationCheck`,
//     `RefinementVc`),
//   - the proof-assurance enums (`AssuranceLevel`, `ProofStrength`,
//     `ReasoningKind`, `TrustSpecVariableOrigin`).
//
// Trust's `trust-types` and `trust-verifier-api` re-export these so the
// compiler's call sites are unchanged; backends (e.g. `clean`) depend on this
// leaf crate via the universal-IR sibling path (`../trust-ir/crates/...`)
// instead of reaching into the Trust repo. Leaf by construction: depends only
// on serde + rustc-hash, never on trust-types/trust-verifier-api.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod assurance;
pub mod block;
pub mod body_wp_identity;
pub mod formula;
pub mod formula_census;
pub mod formula_dag;
pub mod fx;
pub mod interner;
pub mod rat;
pub mod sort;
pub mod translation_validation;

pub use assurance::{AssuranceLevel, ProofStrength, ReasoningKind, TrustSpecVariableOrigin};
pub use block::BlockId;
pub use formula::{Formula, escape_smtlib_symbol};
pub use interner::{Interner, Symbol};
pub use rat::{RatLit, RatLitError};
pub use sort::{RoundingMode, Sort};
