// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! is_def_eq reflection: eliminate the acceptance to `DefEq a b` (#461).
//!
//! Split from implementation_soundness.rs. Contains:
//! - def_eq_joinable_reflects: DerivedProved elimination of the DefEqJoinable
//!   packaged existential (registered in implementation_soundness.rs) to DefEq a b
//! - kernel_def_eq_reflects_spec: DerivedLemma eliminating a KernelDefEqAccepts
//!   acceptance to DefEq a b
//!
//! The production kernel's is_def_eq algorithm normalizes both sides (WHNF + lazy
//! delta reduction) and compares the normal forms structurally. The faithful
//! `KernelDefEqAccepts` inductive packages that success contract; its single mk
//! constructor's guarded field concludes in `DefEqJoinable a b` — "a and b reduce
//! to definitionally-equal forms nl, nr" — with the common reducts bound
//! INTERNALLY as existential constructor arguments. This RETIRES the two
//! `KernelDefEqNormalLeft` / `KernelDefEqNormalRight` Skolem functions (removed from
//! the census): the joinability witness names no Skolem functions of the inputs.
//! `kernel_def_eq_reflects_spec` chains `KernelDefEqAccepts.rec` then
//! `def_eq_joinable_reflects`; both recursors and DefEqJoinable are non-axioms, so
//! the residual axiom closure is empty.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_defeq_decomposition(
        &mut self,
    ) -> Result<(), SpecError> {
        // =========================================================
        // Derived: def_eq_joinable_reflects
        // =========================================================
        //
        // Eliminate the DefEqJoinable packaged existential (registered in
        // implementation_soundness.rs) to the skolem-free DefEq a b. The single mk
        // constructor bound the two common reducts nl/nr internally with evidence
        // (DefEq a nl, DefEq b nr, DefEq nl nr); we recover a ≡ b by
        //   a ≡ nl ≡ nr ≡ b   (DefEq.trans + DefEq.symm).
        //
        // DefEqJoinable.rec is the promoted-parameter (AndType) shape: a and b are
        // (implicit) inductive parameters, the motive ranges over the major premise
        // only, and the single minor binds the ctor's non-parameter fields
        // (nl, nr, h1, h2, h3) — NOT a/b (which are supplied as the recursor's
        // leading parameters). Verified against the kernel-generated recursor type
        // (diagnostic dump of DefEqJoinable.rec). This lemma is genuinely
        // DerivedProved with an EMPTY axiom closure: DefEqJoinable / DefEqJoinable.rec
        // are kernel-generated non-axioms and DefEq.trans/symm are FoundationalRules.
        self.add_definition(SpecDefinition {
            name: "def_eq_joinable_reflects".to_string(),
            type_src: "forall (a : KExpr) (b : KExpr), DefEqJoinable a b -> DefEq a b".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : KExpr) (b : KExpr) (h : DefEqJoinable a b) => ",
                    "DefEqJoinable.rec a b ",
                    "(fun (_h : DefEqJoinable a b) => DefEq a b) ",
                    "(fun (nl : KExpr) (nr : KExpr) ",
                    "(h1 : DefEq a nl) (h2 : DefEq b nr) (h3 : DefEq nl nr) => ",
                    "DefEq.trans a nl b h1 ",
                    "(DefEq.trans nl nr b h3 (DefEq.symm b nr h2))) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Eliminate DefEqJoinable to definitional equality: DefEqJoinable a b (a and b ",
                "reduce to definitionally-equal forms nl, nr) yields DefEq a b. Proof via ",
                "DefEqJoinable.rec: from DefEq a nl, DefEq b nr, DefEq nl nr, chain ",
                "a ≡ nl ≡ nr ≡ b by DefEq.trans + DefEq.symm. Skolem-free: retires ",
                "KernelDefEqNormalLeft/Right. DerivedProved with empty axiom closure."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEqJoinable".to_string(),
                "DefEqJoinable.rec".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Derived: kernel_def_eq_reflects_spec
        // =========================================================
        //
        // Forward simulation for is_def_eq. KernelDefEqAccepts is a faithful
        // inductive (implementation_soundness.rs) whose single mk constructor field
        // is the GUARDED implication to DefEqJoinable a b. This lemma eliminates the
        // acceptance with KernelDefEqAccepts.rec (param-fixed AndType shape: motive
        // over the major premise only; the minor applies the guarded field to this
        // lemma's own env/ctx/admissibility premises — preserving the old guarded
        // strength), yielding DefEqJoinable a b, then eliminates that to DefEq a b
        // via def_eq_joinable_reflects. No skolem witnesses appear anywhere: the
        // honest residual axiom closure is now EMPTY (DefEqJoinable and both
        // recursors are non-axioms).
        self.add_definition(SpecDefinition {
            name: "kernel_def_eq_reflects_spec".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (a : KExpr) (b : KExpr), ",
                "KernelStateEnvValid st -> ",
                "KernelStateLocalCtxWellFormed st -> ",
                "KernelBinaryInputAdmissible st a b -> ",
                "KernelDefEqAccepts st a b -> ",
                "DefEq a b"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (a : KExpr) (b : KExpr) ",
                    "(henv : KernelStateEnvValid st) ",
                    "(hctx : KernelStateLocalCtxWellFormed st) ",
                    "(hadm : KernelBinaryInputAdmissible st a b) ",
                    "(haccept : KernelDefEqAccepts st a b) => ",
                    "def_eq_joinable_reflects a b ",
                    "(KernelDefEqAccepts.rec st a b ",
                    "(fun (_h : KernelDefEqAccepts st a b) => DefEqJoinable a b) ",
                    "(fun (field : KernelStateEnvValid st -> ",
                    "KernelStateLocalCtxWellFormed st -> ",
                    "KernelBinaryInputAdmissible st a b -> DefEqJoinable a b) => ",
                    "field henv hctx hadm) ",
                    "haccept)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Forward simulation for is_def_eq: derived from the KernelDefEqAccepts \
                          faithful inductive. Eliminate the acceptance (KernelDefEqAccepts.rec, \
                          applying the guarded mk field to the env/ctx/admissibility premises) to \
                          get DefEqJoinable a b, then eliminate that (def_eq_joinable_reflects) to \
                          DefEq a b. Skolem-free: retires KernelDefEqNormalLeft/Right; residual \
                          axiom closure is empty."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "def_eq_joinable_reflects".to_string(),
                "DefEqJoinable".to_string(),
                "KernelDefEqAccepts".to_string(),
                "KernelDefEqAccepts.rec".to_string(),
            ])),
            // The def-eq evidence is carried by the skolem-free DefEqJoinable
            // packaged existential and both recursors are non-axioms, so the honest
            // residual leaves are none.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_defeq_decomposition_tests.rs"]
mod implementation_soundness_defeq_decomposition_tests;
