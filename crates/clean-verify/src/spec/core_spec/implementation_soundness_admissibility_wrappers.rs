// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! KernelInputAdmissible wrappers for constructive closedness inversion (#461).
//!
//! `KernelInputAdmissible` is the state-indexed alias used by the implementation
//! soundness surface. These wrappers keep downstream proofs on that surface while
//! reusing the constructive `is_closed_at_*` inversion lemmas from
//! `implementation_soundness_admissibility.rs`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_kernel_input_admissibility_wrappers(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "kernel_input_admissible_app_fun".to_string(),
            type_src: "forall (st : KernelState) (f : KExpr) (a : KExpr), KernelInputAdmissible st (KExpr.app f a) -> KernelInputAdmissible st f".to_string(),
            value_src: Some("fun (st : KernelState) (f : KExpr) (a : KExpr) (h : KernelInputAdmissible st (KExpr.app f a)) => is_closed_at_app_fun f a Nat.zero h".to_string()),
            is_axiom: false,
            description: "Top-level admissibility inversion for app functions. Since KernelInputAdmissible unfolds to is_closed, closed applications have admissible function subexpressions. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInputAdmissible".to_string(),
                "is_closed_at_app_fun".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_input_admissible_app_arg".to_string(),
            type_src: "forall (st : KernelState) (f : KExpr) (a : KExpr), KernelInputAdmissible st (KExpr.app f a) -> KernelInputAdmissible st a".to_string(),
            value_src: Some("fun (st : KernelState) (f : KExpr) (a : KExpr) (h : KernelInputAdmissible st (KExpr.app f a)) => is_closed_at_app_arg f a Nat.zero h".to_string()),
            is_axiom: false,
            description: "Top-level admissibility inversion for app arguments. Since KernelInputAdmissible unfolds to is_closed, closed applications have admissible argument subexpressions. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInputAdmissible".to_string(),
                "is_closed_at_app_arg".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_input_admissible_lam_type".to_string(),
            type_src: "forall (st : KernelState) (A : KExpr) (body : KExpr), KernelInputAdmissible st (KExpr.lam A body) -> KernelInputAdmissible st A".to_string(),
            value_src: Some("fun (st : KernelState) (A : KExpr) (body : KExpr) (h : KernelInputAdmissible st (KExpr.lam A body)) => is_closed_at_lam_type A body Nat.zero h".to_string()),
            is_axiom: false,
            description: "Top-level admissibility inversion for lambda parameter types. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInputAdmissible".to_string(),
                "is_closed_at_lam_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_input_admissible_pi_type".to_string(),
            type_src: "forall (st : KernelState) (A : KExpr) (body : KExpr), KernelInputAdmissible st (KExpr.pi A body) -> KernelInputAdmissible st A".to_string(),
            value_src: Some("fun (st : KernelState) (A : KExpr) (body : KExpr) (h : KernelInputAdmissible st (KExpr.pi A body)) => is_closed_at_pi_type A body Nat.zero h".to_string()),
            is_axiom: false,
            description: "Top-level admissibility inversion for Pi domains. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInputAdmissible".to_string(),
                "is_closed_at_pi_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
