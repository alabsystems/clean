// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! GF(2) Polynomial Calculus for CDCL — Algebraic Proof System
//!
//! Implements Groebner basis computation over GF(2) with boolean reduction
//! (x^2 = x), providing an algebraic proof system that is exponentially
//! stronger than resolution for certain formula classes.
//!
//! ## Key Result
//!
//! Tseitin formulas on d-regular expander graphs require 2^{Mathverse(n/log n)}
//! resolution steps (Ben-Sasson & Wigderson, 1999), but only O(n) steps in
//! GF(2) Polynomial Calculus. This is because XOR constraints — which are
//! single polynomials in GF(2) — require exponentially many clauses in CNF.
//!
//! ## Theorems
//!
//! | ID   | Name                          | Status         |
//! |------|-------------------------------|----------------|
//! | GF01 | Clause-polynomial soundness   | DerivedPending |
//! | GF02 | Tseitin exponential separation| DerivedPending |
//! | GF03 | Boolean Groebner termination  | DerivedPending |
//!
//! ## References
//!
//! - Razborov (1998). "Lower bounds for the polynomial calculus."
//! - Clegg, Edmonds, Impagliazzo (1996). "Using the Groebner basis
//!   algorithm to find proofs of unsatisfiability." STOC 1996.
//! - Buchberger (1965). "An algorithm for finding the basis elements of
//!   the residue class ring of a zero-dimensional polynomial ideal."
//!
pub mod groebner;
pub mod polynomial;
pub(crate) mod spec_registration;
pub mod tseitin;

use crate::spec::ProofStatus;

#[derive(Debug, Clone)]
pub struct Gf2PcEntry {
    pub id: &'static str,
    pub description: &'static str,
    pub status: ProofStatus,
}

pub const GF01_CLAUSE_POLY_SOUNDNESS: Gf2PcEntry = Gf2PcEntry {
    id: "GF01",
    description: "Clause-polynomial encoding soundness: clause OR-semantics \
                  matches GF(2) polynomial zero-evaluation",
    status: ProofStatus::DerivedPending,
};

pub const GF02_TSEITIN_SEPARATION: Gf2PcEntry = Gf2PcEntry {
    id: "GF02",
    description: "Tseitin exponential separation: 2^{Mathverse(n/log n)} resolution \
                  vs O(n) GF(2)-PC on expander graphs",
    status: ProofStatus::DerivedPending,
};

pub const GF03_BOOLEAN_GROEBNER_TERMINATION: Gf2PcEntry = Gf2PcEntry {
    id: "GF03",
    description: "Boolean Groebner basis termination: Buchberger's algorithm \
                  terminates over GF(2) with x^2=x axioms",
    status: ProofStatus::DerivedPending,
};

#[must_use]
pub fn all_entries() -> Vec<Gf2PcEntry> {
    vec![
        GF01_CLAUSE_POLY_SOUNDNESS,
        GF02_TSEITIN_SEPARATION,
        GF03_BOOLEAN_GROEBNER_TERMINATION,
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_entries_count() {
        assert_eq!(all_entries().len(), 3);
    }

    #[test]
    fn test_all_entries_unique_ids() {
        let entries = all_entries();
        let mut ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), entries.len());
    }
}
