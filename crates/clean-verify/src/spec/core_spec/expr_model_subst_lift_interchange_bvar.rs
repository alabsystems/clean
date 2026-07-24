// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Master subst_lift_interchange_bvar_gen: the generalized bvar substitution-lift
//! interchange lemma.
//!
//! Statement:
//!   inst(lift(bvar i, c, sd), w, add(sd, add(c, od)))
//!   = lift(inst(bvar i, w, add(c, od)), c, sd)
//!
//! DerivedProved via triple Nat.rec convoy dispatching to 4 sub-cases
//! (below/between/equal/above). All sub-cases are DerivedProved in
//! sibling modules. The Below and Between sub-cases use `Nat.add d sd`
//! (where d = c+od) in their type signatures, while the master uses
//! `Nat.add sd (Nat.add c od)`. These differ by `nat_add_comm`
//! (propositionally equal but not definitionally equal), so the assembly
//! bridges via `Eq.trans` + `Eq.cong nat_add_comm` transports.
//!
//! Sub-case helpers are in expr_model_subst_lift_interchange_bvar_helpers.rs
//! and expr_model_subst_lift_interchange_bvar_cases.rs.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_subst_lift_interchange_bvar(&mut self) -> Result<(), SpecError> {
        // subst_lift_interchange_bvar_gen: generalized bvar case at arbitrary cutoff.
        //
        // Statement:
        //   inst(lift(bvar i, c, sd), w, add(sd, add(c, od)))
        //   = lift(inst(bvar i, w, add(c, od)), c, sd)
        //
        // Proof: triple Nat.rec convoy on sub(c, i), sub(add(c,od), i),
        // sub(i, add(c,od)), dispatching to four sub-case helpers:
        //   - below: i < c (sub(c, i) = succ)
        //   - between: c ≤ i < c+od (sub(c, i) = 0, sub(add(c,od), i) = succ)
        //   - equal: i = c+od (all subs = 0)
        //   - above: i > c+od (sub(i, add(c,od)) = succ)
        //
        // Below and Between sub-case helpers produce results with
        // Nat.add (Nat.add c od) sd in the LHS depth position, but the
        // master type uses Nat.add sd (Nat.add c od). The Eq.trans +
        // Eq.cong nat_add_comm transports bridge this gap.
        //
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "subst_lift_interchange_bvar_gen".to_string(),
            type_src: concat!(
                "forall (i : Nat) (w : KExpr) (c : Nat) (sd : Nat) (od : Nat), ",
                "Eq KExpr ",
                "(instantiate_at (lift_at (KExpr.bvar i) c sd) w ",
                "(Nat.add sd (Nat.add c od))) ",
                "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd)",
            )
            .to_string(),
            value_src: Some(bvar_gen_proof()),
            is_axiom: false,
            description: concat!(
                "Generalized bvar case of subst/lift interchange at arbitrary cutoff c: ",
                "inst(lift(bvar i, c, sd), w, sd+(c+od)) = lift(inst(bvar i, w, c+od), c, sd). ",
                "DerivedProved via triple Nat.rec convoy dispatching to below/between/equal/above ",
                "with nat_add_comm transports for below/between argument-order bridge. ",
                "Part of #461, #464.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "nat_add_comm".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_pos_add_right".to_string(),
                "subst_lift_interchange_bvar_above".to_string(),
                "subst_lift_interchange_bvar_below".to_string(),
                "subst_lift_interchange_bvar_between".to_string(),
                "subst_lift_interchange_bvar_equal".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// The master Eq goal type (LHS with master convention).
const LHS: &str = "(instantiate_at (lift_at (KExpr.bvar i) c sd) w (Nat.add sd (Nat.add c od)))";

/// The LHS with Below/Between convention (Nat.add d sd where d=c+od).
const LHS_COMM: &str =
    "(instantiate_at (lift_at (KExpr.bvar i) c sd) w (Nat.add (Nat.add c od) sd))";

/// The master Eq goal type (RHS).
const RHS: &str = "(lift_at (instantiate_at (KExpr.bvar i) w (Nat.add c od)) c sd)";

/// Eq.cong transport bridging Nat.add sd (Nat.add c od) to Nat.add (Nat.add c od) sd.
const ADD_COMM_TRANSPORT: &str = concat!(
    "(Eq.cong Nat KExpr ",
    "(fun (n : Nat) => instantiate_at (lift_at (KExpr.bvar i) c sd) w n) ",
    "(Nat.add sd (Nat.add c od)) (Nat.add (Nat.add c od) sd) ",
    "(nat_add_comm sd (Nat.add c od)))",
);

/// Build the triple Nat.rec convoy proof term.
fn bvar_gen_proof() -> String {
    format!(
        concat!(
            "fun (i : Nat) (w : KExpr) (c : Nat) (sd : Nat) (od : Nat) => ",
            "Nat.rec ",
            "(fun (g : Nat) => Eq Nat (Nat.sub c i) g -> Eq KExpr {lhs} {rhs}) ",
            // Outer zero: sub(c, i) = 0 → enter middle Nat.rec
            "(fun (h_ci : Eq Nat (Nat.sub c i) Nat.zero) => ",
            "Nat.rec ",
            "(fun (g2 : Nat) => Eq Nat (Nat.sub (Nat.add c od) i) g2 -> ",
            "Eq KExpr {lhs} {rhs}) ",
            // Middle zero: sub(c+od, i) = 0 → enter inner Nat.rec
            "(fun (h_codi : Eq Nat (Nat.sub (Nat.add c od) i) Nat.zero) => ",
            "Nat.rec ",
            "(fun (g3 : Nat) => Eq Nat (Nat.sub i (Nat.add c od)) g3 -> ",
            "Eq KExpr {lhs} {rhs}) ",
            // EQUAL: sub(i, c+od) = 0
            "(fun (h_icod : Eq Nat (Nat.sub i (Nat.add c od)) Nat.zero) => ",
            "subst_lift_interchange_bvar_equal i c sd od w h_ci h_codi h_icod) ",
            // ABOVE: sub(i, c+od) = succ(k)
            "(fun (k : Nat) ",
            "(_ : Eq Nat (Nat.sub i (Nat.add c od)) k -> Eq KExpr {lhs} {rhs}) ",
            "(h_icod : Eq Nat (Nat.sub i (Nat.add c od)) (Nat.succ k)) => ",
            "subst_lift_interchange_bvar_above i c sd od w k h_ci h_codi h_icod) ",
            "(Nat.sub i (Nat.add c od)) (Eq.refl Nat (Nat.sub i (Nat.add c od)))) ",
            // BETWEEN: sub(c+od, i) = succ(k) — nat_add_comm transport
            "(fun (k : Nat) ",
            "(_ : Eq Nat (Nat.sub (Nat.add c od) i) k -> Eq KExpr {lhs} {rhs}) ",
            "(h_codi : Eq Nat (Nat.sub (Nat.add c od) i) (Nat.succ k)) => ",
            "Eq.trans KExpr {lhs} {lhs_comm} {rhs} {add_comm} ",
            "(subst_lift_interchange_bvar_between i c sd ",
            "(Nat.add c od) w k h_codi h_ci)) ",
            "(Nat.sub (Nat.add c od) i) (Eq.refl Nat (Nat.sub (Nat.add c od) i))) ",
            // BELOW: sub(c, i) = succ(k3) — nat_add_comm transport
            "(fun (k3 : Nat) ",
            "(_ : Eq Nat (Nat.sub c i) k3 -> Eq KExpr {lhs} {rhs}) ",
            "(h_ci : Eq Nat (Nat.sub c i) (Nat.succ k3)) => ",
            "Eq.trans KExpr {lhs} {lhs_comm} {rhs} {add_comm} ",
            "(subst_lift_interchange_bvar_below i c sd (Nat.add c od) w ",
            "(Nat.sub (Nat.sub (Nat.add c od) i) (Nat.succ Nat.zero)) k3 ",
            "(nat_sub_pos_add_right c od i ",
            "(nat_pos_witness_from_succ_eq (Nat.sub c i) k3 h_ci)) h_ci)) ",
            "(Nat.sub c i) (Eq.refl Nat (Nat.sub c i))",
        ),
        lhs = LHS,
        lhs_comm = LHS_COMM,
        rhs = RHS,
        add_comm = ADD_COMM_TRANSPORT,
    )
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::test_utils::run_with_stack;
    use crate::Specification;

    #[test]
    fn test_bvar_gen_is_derived_proved() {
        let spec = run_with_stack(|| {
            Specification::new_substitution_test_spec()
                .expect("substitution/WHNF test spec should build")
        });

        let bvar_gen = spec
            .definitions()
            .get("subst_lift_interchange_bvar_gen")
            .expect("subst_lift_interchange_bvar_gen should exist");
        assert!(!bvar_gen.is_axiom, "bvar_gen should not be an axiom");
        assert!(
            bvar_gen.value_src.is_some(),
            "bvar_gen should have a proof term"
        );
        assert_eq!(bvar_gen.proof_status, ProofStatus::DerivedProved);
        assert!(
            bvar_gen.axiom_deps.is_empty(),
            "bvar_gen should have no axiom deps (all sub-cases are DerivedProved)"
        );
    }
}
