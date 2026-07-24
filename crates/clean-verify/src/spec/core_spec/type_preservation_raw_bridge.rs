// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Raw compatibility bridge for implementation-soundness conversion wrappers.
//!
//! After #2872 moves the primary `type_conversion` and `def_eq_preserves_typing`
//! to the typed lane (`typing_is_def_eq := TypedDefEq`), these raw compatibility
//! definitions preserve the raw `is_def_eq`-based API surface under explicit
//! names. Implementation-soundness wrappers depend on these raw bridge names
//! instead of the primary typed API.
//!
//! #464 bounded-evidence update: the shims now route through the constructive
//! `raw_to_typed_def_eq` bridge instead of using `Eq.substType + def_eq_to_eq`
//! directly.
//!
//! Part of #2893: explicit raw-to-typed bridge for implementation-soundness
//! conversion wrappers.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_type_preservation_raw_bridge(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Raw type conversion compatibility shim
        // =========================================================
        //
        // Same pre-#2872 statement under an explicit raw-bridge name.
        // Implementation-soundness wrappers depend on this name so they remain
        // stable when the primary type_conversion moves to typing_is_def_eq.

        self.add_definition(SpecDefinition {
            name: "raw_type_conversion".to_string(),
            type_src: "forall (e : KExpr) (T1 : KExpr) (T2 : KExpr), has_type e T1 -> is_def_eq T1 T2 -> has_type e T2".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                "(ht : has_type e T1) (heq : is_def_eq T1 T2) => ",
                "Typing.conv e T1 T2 ht heq"
            ).to_string()),
            is_axiom: false,
            description: concat!(
                "Raw type conversion compatibility shim: if e : T1 and T1 ≡ T2 (raw is_def_eq), ",
                "then e : T2. Proof via the now-untyped Typing.conv applied directly to the raw ",
                "DefEq witness (is_def_eq := DefEq). church_rosser_whnf retirement track; Part of #2893."
            ).to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.conv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // raw_def_eq_preserves_typing is RETIRED: under untyped DefEq.beta, raw
        // (symmetric) DefEq subject reduction is FALSE — `has_type e T -> DefEq e e'
        // -> has_type e' T` admits a subject-EXPANSION counterexample (e' a beta
        // redex whose typing is not recoverable). The only sound preservation is
        // FORWARD over the DIRECTED whnf_to relation, which every real consumer
        // (KernelWhnfPreservesTyping) now uses via whnf_to_preserves_typing.
        // (church_rosser_whnf retirement track.)

        Ok(())
    }
}

#[cfg(test)]
#[path = "type_preservation_raw_bridge_tests.rs"]
mod type_preservation_raw_bridge_tests;
