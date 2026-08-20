// trust-ir-contract — cross-repo shared verification vocabulary
//
// The canonical home for the small set of data types that cross the
// Trust <-> backend boundary:
//   - the SMT `Formula` / `Sort` / `Symbol` vocabulary,
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
pub mod formula;
pub mod fx;
pub mod interner;
pub mod sort;
pub mod translation_validation;

pub use assurance::{AssuranceLevel, ProofStrength, ReasoningKind, TrustSpecVariableOrigin};
pub use block::BlockId;
pub use formula::{Formula, escape_smtlib_symbol};
pub use interner::{Interner, Symbol};
pub use sort::{RoundingMode, Sort};
