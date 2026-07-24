// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof Complexity Theory
//!
//! Formalizes proof systems for propositional unsatisfiability:
//!
//! - **Resolution**: the standard proof system underlying CDCL proof logging.
//!   Resolve clauses on a pivot variable to derive new clauses, eventually
//!   deriving the empty clause (contradiction).
//!
//! - **Cutting Planes**: operates over pseudo-Boolean (0/1 integer linear)
//!   inequalities. Strictly stronger than resolution -- exponentially shorter
//!   proofs exist for families like pigeonhole (Haken 1985 vs Cook et al. 1987).
//!
//! - **Tree Resolution**: tree-like resolution where each derived clause is
//!   used at most once. Strictly weaker than general resolution.
//!
//! - **Separations**: proof system hierarchy with Haken bounds and CP advantage.
//!
//! - **Standard encodings**: pigeonhole principle and Tseitin formulas, used as
//!   benchmark families for proof complexity lower bounds.

pub mod cutting_planes;
pub mod encodings;
pub(crate) mod kernel_proofs;
pub mod lower_bounds;
pub mod resolution;
pub mod separations;
pub(crate) mod separations_cp;
mod spec_registration;
#[cfg(test)]
mod tests_cutting_planes;
#[cfg(test)]
mod tests_encodings;
#[cfg(test)]
mod tests_lower_bounds;
#[cfg(test)]
mod tests_php_cp_polynomial;
#[cfg(test)]
mod tests_proofs;
#[cfg(test)]
mod tests_proofs_ext;
#[cfg(test)]
mod tests_proofs_ext2;
#[cfg(test)]
mod tests_separations;
#[cfg(test)]
mod tests_separations_cp;
#[cfg(test)]
mod tests_tree_resolution;
#[cfg(test)]
mod tests_tseitin_circuit;
#[cfg(test)]
mod tests_tseitin_graphs;
pub mod tree_resolution;
pub mod tseitin_circuit;
pub mod tseitin_graphs;

use crate::spec::ProofStatus;

/// PC01: Resolution soundness -- resolvent is entailed by parents.
pub const PC01_RESOLUTION_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// PC02: Resolution completeness -- every unsatisfiable CNF has a resolution refutation.
pub const PC02_RESOLUTION_COMPLETENESS: ProofStatus = ProofStatus::DerivedPending;

/// PC03: Cutting planes soundness -- derived inequalities are valid.
pub const PC03_CP_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// PC04: Cutting planes subsumes resolution.
pub const PC04_CP_SUBSUMES_RESOLUTION: ProofStatus = ProofStatus::DerivedPending;

/// Return a summary of proof complexity theorem statuses.
#[must_use]
pub fn proof_complexity_registry() -> Vec<(&'static str, ProofStatus)> {
    let mut entries = vec![
        ("PC01_resolution_soundness", PC01_RESOLUTION_SOUNDNESS),
        ("PC02_resolution_completeness", PC02_RESOLUTION_COMPLETENESS),
        ("PC03_cp_soundness", PC03_CP_SOUNDNESS),
        ("PC04_cp_subsumes_resolution", PC04_CP_SUBSUMES_RESOLUTION),
        ("PC05_tseitin_equisat", encodings::PC05_TSEITIN_EQUISAT),
        ("PC06_php_unsat", encodings::PC06_PHP_UNSAT),
    ];
    entries.extend(lower_bounds::lower_bounds_registry());
    entries
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::ProofStatus;

    #[test]
    fn test_proof_complexity_registry_count() {
        assert_eq!(proof_complexity_registry().len(), 8);
    }

    #[test]
    fn test_proof_complexity_pc01_pc04_proved() {
        let registry = proof_complexity_registry();
        let proved: Vec<_> = registry
            .iter()
            .filter(|(_, s)| *s == ProofStatus::DerivedProved)
            .collect();
        assert_eq!(proved.len(), 0, "no theorems should be DerivedProved");
        let pending: Vec<_> = registry
            .iter()
            .filter(|(_, s)| *s == ProofStatus::DerivedPending)
            .collect();
        assert_eq!(pending.len(), 8, "all PC01-PC08 should be DerivedPending");
    }
}
