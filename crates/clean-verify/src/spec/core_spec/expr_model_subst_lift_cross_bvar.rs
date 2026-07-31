// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Arithmetic and bvar groundwork for cutoff-generalized substitution/lift proofs.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model_subst_lift_cross_bvar(&mut self) -> Result<(), SpecError> {
        // nat_sub_zero_trans: transitivity of ≤ expressed via Nat.sub.
        //
        // Statement: sub(a, b) = 0 ∧ sub(b, c) = 0 → sub(a, c) = 0.
        //
        // Proof by Nat.rec on b with a, c universalized in the motive.
        //   b=0: sub(a, 0) = a = 0, so sub(0, c) = 0 by nat_sub_zero_left.
        //   b=succ b': inner Nat.rec on a.
        //     a=0: sub(0, c) = 0 by nat_sub_zero_left.
        //     a=succ a': inner Nat.rec on c.
        //       c=0: sub(succ b', 0) = succ b' = 0 absurd, discriminator.
        //       c=succ c': reduce via nat_sub_succ_succ, apply IH.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_trans".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat) (c : Nat), ",
                "Eq Nat (Nat.sub a b) Nat.zero -> ",
                "Eq Nat (Nat.sub b c) Nat.zero -> ",
                "Eq Nat (Nat.sub a c) Nat.zero",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) ",
                    "(h_ab : Eq Nat (Nat.sub a b) Nat.zero) ",
                    "(h_bc : Eq Nat (Nat.sub b c) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (b : Nat) => forall (a : Nat) (c : Nat), ",
                    "Eq Nat (Nat.sub a b) Nat.zero -> ",
                    "Eq Nat (Nat.sub b c) Nat.zero -> ",
                    "Eq Nat (Nat.sub a c) Nat.zero) ",
                    "(fun (a : Nat) (c : Nat) ",
                    "(h_ab_z : Eq Nat (Nat.sub a Nat.zero) Nat.zero) ",
                    "(_ : Eq Nat (Nat.sub Nat.zero c) Nat.zero) => ",
                    "Eq.trans Nat (Nat.sub a c) (Nat.sub Nat.zero c) Nat.zero ",
                    "(Eq.cong Nat Nat (fun (x : Nat) => Nat.sub x c) a Nat.zero ",
                    "(Eq.trans Nat a (Nat.sub a Nat.zero) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub a Nat.zero) a (nat_sub_zero_right a)) ",
                    "h_ab_z)) ",
                    "(nat_sub_zero_left c)) ",
                    "(fun (b' : Nat) ",
                    "(ih : forall (a : Nat) (c : Nat), ",
                    "Eq Nat (Nat.sub a b') Nat.zero -> ",
                    "Eq Nat (Nat.sub b' c) Nat.zero -> ",
                    "Eq Nat (Nat.sub a c) Nat.zero) => ",
                    "fun (a : Nat) (c : Nat) ",
                    "(h_ab_s : Eq Nat (Nat.sub a (Nat.succ b')) Nat.zero) ",
                    "(h_bc_s : Eq Nat (Nat.sub (Nat.succ b') c) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (a : Nat) => ",
                    "Eq Nat (Nat.sub a (Nat.succ b')) Nat.zero -> ",
                    "Eq Nat (Nat.sub a c) Nat.zero) ",
                    "(fun (_ : Eq Nat (Nat.sub Nat.zero (Nat.succ b')) Nat.zero) => ",
                    "nat_sub_zero_left c) ",
                    "(fun (a' : Nat) ",
                    "(_ : Eq Nat (Nat.sub a' (Nat.succ b')) Nat.zero -> ",
                    "Eq Nat (Nat.sub a' c) Nat.zero) ",
                    "(h_ab_ss : Eq Nat (Nat.sub (Nat.succ a') (Nat.succ b')) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (c : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.succ b') c) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.succ a') c) Nat.zero) ",
                    "(fun (h_bc_z : Eq Nat (Nat.sub (Nat.succ b') Nat.zero) Nat.zero) => ",
                    "Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) Nat.zero ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.sub (Nat.succ a') Nat.zero) n) ",
                    "(Nat.succ b') Nat.zero ",
                    "(Eq.trans Nat (Nat.succ b') (Nat.sub (Nat.succ b') Nat.zero) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ b') Nat.zero) (Nat.succ b') ",
                    "(nat_sub_zero_right (Nat.succ b'))) ",
                    "h_bc_z)) ",
                    "(fun (c' : Nat) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ b') c') Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.succ a') c') Nat.zero) ",
                    "(h_bc_ss : Eq Nat (Nat.sub (Nat.succ b') (Nat.succ c')) Nat.zero) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ a') (Nat.succ c')) ",
                    "(Nat.sub a' c') Nat.zero ",
                    "(nat_sub_succ_succ a' c') ",
                    "(ih a' c' ",
                    "(Eq.trans Nat (Nat.sub a' b') ",
                    "(Nat.sub (Nat.succ a') (Nat.succ b')) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ a') (Nat.succ b')) (Nat.sub a' b') ",
                    "(nat_sub_succ_succ a' b')) ",
                    "h_ab_ss) ",
                    "(Eq.trans Nat (Nat.sub b' c') ",
                    "(Nat.sub (Nat.succ b') (Nat.succ c')) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ b') (Nat.succ c')) (Nat.sub b' c') ",
                    "(nat_sub_succ_succ b' c')) ",
                    "h_bc_ss))) ",
                    "c h_bc_s) ",
                    "a h_ab_s) ",
                    "b a c h_ab h_bc",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Transitivity of ≤ via Nat.sub: sub(a,b)=0 ∧ sub(b,c)=0 → sub(a,c)=0. ",
                "DerivedProved via triple Nat.rec (on b, a, c) with nat_sub_succ_succ reduction. ",
                "Part of #461, #464.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "nat_sub_succ_succ".to_string(),
                "nat_sub_zero_left".to_string(),
                "nat_sub_zero_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_cross_compose_bvar: cross-cutoff lift composition for bvars.
        //
        // Statement: lift_at(lift_at(bvar j, c0, n), add(c0, gap), m) =
        //            lift_at(bvar j, c0, add(n, m))
        //   when gap ≤ n (i.e. sub(gap, n) = 0).
        //
        // Parameterized by gap (= c1 - c0) rather than c1 directly, so that
        // existing helpers nat_sub_pos_add_right and nat_sub_zero_add_monotone
        // apply without new arithmetic lemmas.
        //
        // Proof by Nat.rec convoy on sub(c0, j):
        //   gap=0 (j >= c0): both sides reduce via lift_at_bvar_geq.
        //     Inner sub(add(c0,gap), add(j,n))=0 via nat_sub_zero_add_monotone.
        //     Reassociate via nat_add_assoc.
        //   gap=succ k (j < c0): both lifts leave bvar j unchanged.
        //     Sub(add(c0,gap), j) positivity via nat_sub_pos_add_right.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_cross_compose_bvar".to_string(),
            type_src: concat!(
                "forall (j : Nat) (c0 : Nat) (n : Nat) (gap : Nat) (m : Nat), ",
                "Eq Nat (Nat.sub gap n) Nat.zero -> ",
                "Eq KExpr ",
                "(lift_at (lift_at (KExpr.bvar j) c0 n) (Nat.add c0 gap) m) ",
                "(lift_at (KExpr.bvar j) c0 (Nat.add n m))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (j : Nat) (c0 : Nat) (n : Nat) (gap : Nat) (m : Nat) ",
                    "(h_gn : Eq Nat (Nat.sub gap n) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (g : Nat) => ",
                    "Eq Nat (Nat.sub c0 j) g -> ",
                    "Eq KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) c0 n) (Nat.add c0 gap) m) ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m))) ",
                    "(fun (h0 : Eq Nat (Nat.sub c0 j) Nat.zero) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) c0 n) (Nat.add c0 gap) m) ",
                    "(lift_at (KExpr.bvar (Nat.add j n)) (Nat.add c0 gap) m) ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x (Nat.add c0 gap) m) ",
                    "(lift_at (KExpr.bvar j) c0 n) ",
                    "(KExpr.bvar (Nat.add j n)) ",
                    "(lift_at_bvar_geq j c0 n h0)) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (KExpr.bvar (Nat.add j n)) (Nat.add c0 gap) m) ",
                    "(KExpr.bvar (Nat.add (Nat.add j n) m)) ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m)) ",
                    "(lift_at_bvar_geq (Nat.add j n) (Nat.add c0 gap) m ",
                    "(nat_sub_zero_add_monotone c0 j gap n h0 h_gn)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.bvar (Nat.add (Nat.add j n) m)) ",
                    "(KExpr.bvar (Nat.add j (Nat.add n m))) ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m)) ",
                    "(Eq.cong Nat KExpr KExpr.bvar ",
                    "(Nat.add (Nat.add j n) m) (Nat.add j (Nat.add n m)) ",
                    "(nat_add_assoc j n m)) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m)) ",
                    "(KExpr.bvar (Nat.add j (Nat.add n m))) ",
                    "(lift_at_bvar_geq j c0 (Nat.add n m) h0))))) ",
                    "(fun (k : Nat) ",
                    "(_ : Eq Nat (Nat.sub c0 j) k -> ",
                    "Eq KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) c0 n) (Nat.add c0 gap) m) ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m))) ",
                    "(h_sk : Eq Nat (Nat.sub c0 j) (Nat.succ k)) => ",
                    "Eq.trans KExpr ",
                    "(lift_at (lift_at (KExpr.bvar j) c0 n) (Nat.add c0 gap) m) ",
                    "(lift_at (KExpr.bvar j) (Nat.add c0 gap) m) ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (x : KExpr) => lift_at x (Nat.add c0 gap) m) ",
                    "(lift_at (KExpr.bvar j) c0 n) ",
                    "(KExpr.bvar j) ",
                    "(lift_at_bvar_below j c0 n ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub c0 j) k h_sk))) ",
                    "(Eq.trans KExpr ",
                    "(lift_at (KExpr.bvar j) (Nat.add c0 gap) m) ",
                    "(KExpr.bvar j) ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m)) ",
                    "(lift_at_bvar_below j (Nat.add c0 gap) m ",
                    "(nat_sub_pos_add_right c0 gap j ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub c0 j) k h_sk))) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (KExpr.bvar j) c0 (Nat.add n m)) ",
                    "(KExpr.bvar j) ",
                    "(lift_at_bvar_below j c0 (Nat.add n m) ",
                    "(nat_pos_witness_from_succ_eq (Nat.sub c0 j) k h_sk))))) ",
                    "(Nat.sub c0 j) ",
                    "(Eq.refl Nat (Nat.sub c0 j))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Cross-cutoff lift composition for bvars: ",
                "lift(lift(bvar j, c0, n), add(c0,gap), m) = lift(bvar j, c0, n+m) ",
                "when gap ≤ n. DerivedProved via Nat.rec convoy on sub(c0,j). ",
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
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "lift_at_bvar_below".to_string(),
                "lift_at_bvar_geq".to_string(),
                "nat_add_assoc".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_pos_add_right".to_string(),
                "nat_sub_zero_add_monotone".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
