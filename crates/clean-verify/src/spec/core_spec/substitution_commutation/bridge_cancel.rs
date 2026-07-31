// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bridge cancellation lemmas split from substitution_commutation/bridge.rs.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_substitution_commutation_bridge_cancel_lemmas(
        &mut self,
    ) -> Result<(), SpecError> {
        // ── Inst-overlift cancellation ──
        //
        // When an expression is lifted by succ(n) at cutoff 0 and then
        // substituted at depth d <= n, the substitution just strips one unit
        // of lift, yielding lift by n:
        //
        //   inst(lift(e, 0, succ n), val, d) = lift(e, 0, n)  when d <= n
        //
        // Proof: rewrite lift(e, 0, succ n) as lift(lift(e, 0, n), d, 1)
        // via lift_at_shift_succ, then apply lift_cancel_gen at cutoff d.
        //
        // DerivedProved modulo lift_at_shift_succ. Part of #464.
        self.add_definition(SpecDefinition {
            name: "inst_overlift_cancel".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (val : KExpr) (n : Nat) (d : Nat), ",
                "Eq Nat (Nat.sub d n) Nat.zero -> ",
                "Eq KExpr ",
                "(instantiate_at (lift_at e Nat.zero (Nat.succ n)) val d) ",
                "(lift_at e Nat.zero n)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (val : KExpr) (n : Nat) (d : Nat) ",
                    "(h_dn : Eq Nat (Nat.sub d n) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (lift_at e Nat.zero (Nat.succ n)) val d) ",
                    "(instantiate_at (lift_at (lift_at e Nat.zero n) d (Nat.succ Nat.zero)) val d) ",
                    "(lift_at e Nat.zero n) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => instantiate_at x val d) ",
                    "(lift_at e Nat.zero (Nat.succ n)) ",
                    "(lift_at (lift_at e Nat.zero n) d (Nat.succ Nat.zero)) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (lift_at e Nat.zero n) d (Nat.succ Nat.zero)) ",
                    "(lift_at e Nat.zero (Nat.succ n)) ",
                    "(lift_at_shift_succ e n d h_dn))) ",
                    "(lift_cancel_gen (lift_at e Nat.zero n) val d)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "inst(lift(e, 0, succ n), val, d) = lift(e, 0, n) when d <= n. Derived from lift_at_shift_succ + lift_cancel_gen. DerivedProved (lift_at_shift_succ now proved). Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "lift_at_shift_succ".to_string(),
                "lift_cancel_gen".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
