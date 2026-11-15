// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extend closed empty-context typing through the existing one-entry weakening rule.
//!
//! Context induction and the two lift-identity transports are independently
//! checked over exact exported primitives in the closed-weakening Lean guide.
//! The actual wrapper binds the rule to weaken1 with the live KDeclEnv judgment;
//! no new axiom or assumption of typing in every context is introduced.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn closed_weakening_theorem(
    spec: &mut Specification,
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Requires weaken1, lift_closed_at_id and le_zero_n. Uses the live
    /// TypingCtxConv carrier without inspecting or replacing its constructors.
    pub(super) fn add_typing_closed_weakening(&mut self) -> Result<(), SpecError> {
        closed_weakening_theorem(
            self,
            "closed_weaken_empty_of_weaken1",
            r"forall (J : ListType KExpr -> KExpr -> KExpr -> Type)
    (wk : forall (G : ListType KExpr) (e : KExpr) (T : KExpr), J G e T ->
      forall (C : KExpr), J (ListType.cons KExpr C G)
        (lift_at e Nat.zero (Nat.succ Nat.zero)) (lift_at T Nat.zero (Nat.succ Nat.zero)))
    (e : KExpr) (T : KExpr) (he : is_closed_at e Nat.zero) (hT : is_closed_at T Nat.zero)
    (hnil : J (ListType.nil KExpr) e T), forall (G : ListType KExpr), J G e T",
            r"fun (J : ListType KExpr -> KExpr -> KExpr -> Type)
    (wk : forall (G : ListType KExpr) (e : KExpr) (T : KExpr), J G e T ->
      forall (C : KExpr), J (ListType.cons KExpr C G)
        (lift_at e Nat.zero (Nat.succ Nat.zero)) (lift_at T Nat.zero (Nat.succ Nat.zero)))
    (e : KExpr) (T : KExpr) (he : is_closed_at e Nat.zero) (hT : is_closed_at T Nat.zero)
    (hnil : J (ListType.nil KExpr) e T) (G : ListType KExpr) =>
  ListType.rec KExpr (fun (ctx : ListType KExpr) => J ctx e T) hnil
    (fun (C : KExpr) (ctx : ListType KExpr) (ih : J ctx e T) =>
      Eq.substType KExpr (fun (term : KExpr) => J (ListType.cons KExpr C ctx) term T)
        (lift_at e Nat.zero (Nat.succ Nat.zero)) e
        (lift_closed_at_id e Nat.zero he Nat.zero (Nat.succ Nat.zero) (le_zero_n Nat.zero))
        (Eq.substType KExpr
          (fun (type_ : KExpr) => J (ListType.cons KExpr C ctx)
            (lift_at e Nat.zero (Nat.succ Nat.zero)) type_)
          (lift_at T Nat.zero (Nat.succ Nat.zero)) T
          (lift_closed_at_id T Nat.zero hT Nat.zero (Nat.succ Nat.zero) (le_zero_n Nat.zero))
          (wk ctx e T ih C)))
    G",
            "Generic context-list induction: a one-entry lift-based weakening rule and top-level closure of term/type extend empty-context evidence to every context. The rule is an explicit theorem parameter, not a new axiom.",
        )?;
        closed_weakening_theorem(
            self,
            "typingctxconv_closed_weaken_empty",
            r"forall (tenv : KDeclEnv) (hf : RedEnvFaithful the_red_env) (W : TypingEnvCoherent tenv)
    (e : KExpr) (T : KExpr) (he : is_closed_at e Nat.zero) (hT : is_closed_at T Nat.zero)
    (hnil : TypingCtxConv tenv (ListType.nil KExpr) e T),
    forall (G : ListType KExpr), TypingCtxConv tenv G e T",
            r"fun (tenv : KDeclEnv) (hf : RedEnvFaithful the_red_env) (W : TypingEnvCoherent tenv)
    (e : KExpr) (T : KExpr) (he : is_closed_at e Nat.zero) (hT : is_closed_at T Nat.zero)
    (hnil : TypingCtxConv tenv (ListType.nil KExpr) e T) (G : ListType KExpr) =>
  closed_weaken_empty_of_weaken1 (TypingCtxConv tenv) (weaken1 tenv hf W) e T he hT hnil G",
            "Closed empty-context TypingCtxConv derivations weaken to every context by the existing checked weaken1 rule. Carries only the original RedEnvFaithful/TypingEnvCoherent hypotheses; no assumed per-context typing.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::closed_weakening_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn closed_empty_typing_weakens_through_actual_weaken1_without_extra_axioms() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            closed_weakening_theorem(
                &mut spec,
                "closed_weaken_live_sort_control",
                r"forall (tenv : KDeclEnv) (hf : RedEnvFaithful the_red_env)
    (W : TypingEnvCoherent tenv) (G : ListType KExpr),
    TypingCtxConv tenv G (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))",
                r"fun (tenv : KDeclEnv) (hf : RedEnvFaithful the_red_env)
    (W : TypingEnvCoherent tenv) (G : ListType KExpr) =>
  typingctxconv_closed_weaken_empty tenv hf W
    (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))
    (is_closed_at.sort Level.zero Nat.zero)
    (is_closed_at.sort (Level.succ Level.zero) Nat.zero)
    (TypingCtxConv.sort tenv (ListType.nil KExpr) Level.zero) G",
                "Apply actual weakening to a real empty-context sort derivation with distinct term/type universe levels.",
            )
            .expect("live judgment weakening control");
            closed_weakening_theorem(
                &mut spec,
                "closed_weaken_live_two_entries",
                r"forall (tenv : KDeclEnv) (hf : RedEnvFaithful the_red_env)
    (W : TypingEnvCoherent tenv),
    TypingCtxConv tenv
      (ListType.cons KExpr (KExpr.bvar Nat.zero)
        (ListType.cons KExpr (KExpr.sort Level.zero) (ListType.nil KExpr)))
      (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))",
                r"fun (tenv : KDeclEnv) (hf : RedEnvFaithful the_red_env)
    (W : TypingEnvCoherent tenv) =>
  closed_weaken_live_sort_control tenv hf W
    (ListType.cons KExpr (KExpr.bvar Nat.zero)
      (ListType.cons KExpr (KExpr.sort Level.zero) (ListType.nil KExpr)))",
                "Two nonempty context steps instantiate the generic induction; no context-wide typing premise is supplied.",
            )
            .expect("two-entry context weakening");
            for name in [
                "closed_weaken_empty_of_weaken1",
                "typingctxconv_closed_weaken_empty",
                "closed_weaken_live_sort_control",
                "closed_weaken_live_two_entries",
            ] {
                let proof = spec.definitions().get(name).expect("registered proof");
                assert!(!proof.is_axiom, "{name} must not be an axiom");
                assert_eq!(proof.proof_status, ProofStatus::DerivedProved);
                assert!(
                    proof.elaborated_value.is_some(),
                    "{name} must be kernel checked"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name} must have empty actual transitive axiom closure"
                );
            }
        });
    }
}
