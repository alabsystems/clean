// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Nat witness transport lemmas for adding the same offset to both sides.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_foundation_arith_transport(&mut self) -> Result<(), SpecError> {
        // nat_sub_zero_add_same_right: if lhs <= rhs, then lhs + offset <= rhs + offset.
        //
        // Proof by Nat.rec on offset. The step case reduces both sides with
        // nat_sub_succ_succ after Nat.add iota on the shared successor. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_add_same_right".to_string(),
            type_src: concat!(
                "forall (lhs : Nat) (rhs : Nat) (offset : Nat), ",
                "Eq Nat (Nat.sub lhs rhs) Nat.zero -> ",
                "Eq Nat (Nat.sub (Nat.add lhs offset) (Nat.add rhs offset)) Nat.zero",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (lhs : Nat) (rhs : Nat) (offset : Nat) ",
                "(h : Eq Nat (Nat.sub lhs rhs) Nat.zero) => ",
                "Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.sub (Nat.add lhs k) (Nat.add rhs k)) Nat.zero) ",
                "h ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.sub (Nat.add lhs k) (Nat.add rhs k)) Nat.zero) => ",
                "Eq.trans Nat ",
                "(Nat.sub (Nat.add lhs (Nat.succ k)) (Nat.add rhs (Nat.succ k))) ",
                "(Nat.sub (Nat.add lhs k) (Nat.add rhs k)) ",
                "Nat.zero ",
                "(nat_sub_succ_succ (Nat.add lhs k) (Nat.add rhs k)) ",
                "ih) ",
                "offset",
            ).to_string()),
            is_axiom: false,
            description: "If lhs <= rhs then lhs + offset <= rhs + offset. DerivedProved via Nat.rec on the shared right offset. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.trans".to_string(),
                "Nat.rec".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_pos_add_same_right: if rhs < lhs, the positive subtraction
        // witness is preserved after adding the same right offset to both sides.
        //
        // Proof by Nat.rec on offset. Each step reduces the outer subtraction via
        // nat_sub_succ_succ, reuses the IH, then transports the successor witness
        // back across the same reduction with Eq.cong. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_pos_add_same_right".to_string(),
            type_src: concat!(
                "forall (lhs : Nat) (rhs : Nat) (offset : Nat), ",
                "Eq Nat (Nat.sub lhs rhs) ",
                "(Nat.succ (Nat.sub (Nat.sub lhs rhs) (Nat.succ Nat.zero))) -> ",
                "Eq Nat (Nat.sub (Nat.add lhs offset) (Nat.add rhs offset)) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add lhs offset) (Nat.add rhs offset)) (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (lhs : Nat) (rhs : Nat) (offset : Nat) ",
                "(h : Eq Nat (Nat.sub lhs rhs) ",
                "(Nat.succ (Nat.sub (Nat.sub lhs rhs) (Nat.succ Nat.zero)))) => ",
                "Nat.rec ",
                "(fun (k : Nat) => ",
                "Eq Nat (Nat.sub (Nat.add lhs k) (Nat.add rhs k)) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add lhs k) (Nat.add rhs k)) (Nat.succ Nat.zero)))) ",
                "h ",
                "(fun (k : Nat) ",
                "(ih : Eq Nat (Nat.sub (Nat.add lhs k) (Nat.add rhs k)) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add lhs k) (Nat.add rhs k)) (Nat.succ Nat.zero)))) => ",
                "Eq.trans Nat ",
                "(Nat.sub (Nat.add lhs (Nat.succ k)) (Nat.add rhs (Nat.succ k))) ",
                "(Nat.sub (Nat.add lhs k) (Nat.add rhs k)) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add lhs (Nat.succ k)) (Nat.add rhs (Nat.succ k))) (Nat.succ Nat.zero))) ",
                "(nat_sub_succ_succ (Nat.add lhs k) (Nat.add rhs k)) ",
                "(Eq.trans Nat ",
                "(Nat.sub (Nat.add lhs k) (Nat.add rhs k)) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add lhs k) (Nat.add rhs k)) (Nat.succ Nat.zero))) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add lhs (Nat.succ k)) (Nat.add rhs (Nat.succ k))) (Nat.succ Nat.zero))) ",
                "ih ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.succ (Nat.sub x (Nat.succ Nat.zero))) ",
                "(Nat.sub (Nat.add lhs k) (Nat.add rhs k)) ",
                "(Nat.sub (Nat.add lhs (Nat.succ k)) (Nat.add rhs (Nat.succ k))) ",
                "(Eq.symm Nat ",
                "(Nat.sub (Nat.add lhs (Nat.succ k)) (Nat.add rhs (Nat.succ k))) ",
                "(Nat.sub (Nat.add lhs k) (Nat.add rhs k)) ",
                "(nat_sub_succ_succ (Nat.add lhs k) (Nat.add rhs k)))))) ",
                "offset",
            ).to_string()),
            is_axiom: false,
            description: "If rhs < lhs then the positive subtraction witness survives adding the same right offset to both sides. DerivedProved via Nat.rec on the shared right offset. Part of #464.".to_string(),
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
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_zero_succ_gap_to_add: if depth <= i and i - depth = succ gap,
        // then i = depth + succ gap.
        //
        // Proof by Nat.rec on depth. The base case rewrites sub i 0 = succ gap
        // back to i = succ gap via nat_sub_zero_right. The step case splits on i:
        // i = 0 is impossible because 0 - succ depth = 0, while i = succ j
        // reduces both subtraction witnesses with nat_sub_succ_succ and reuses
        // the depth IH before wrapping with Nat.succ. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_succ_gap_to_add".to_string(),
            type_src: concat!(
                "forall (i : Nat) (depth : Nat) (gap : Nat), ",
                "Eq Nat (Nat.sub depth i) Nat.zero -> ",
                "Eq Nat (Nat.sub i depth) (Nat.succ gap) -> ",
                "Eq Nat i (Nat.add (Nat.succ gap) depth)",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (depth : Nat) (gap : Nat) ",
                "(h_zero : Eq Nat (Nat.sub depth i) Nat.zero) ",
                "(h_gap : Eq Nat (Nat.sub i depth) (Nat.succ gap)) => ",
                "Nat.rec ",
                "(fun (d : Nat) => forall (idx : Nat) (g : Nat), ",
                "Eq Nat (Nat.sub d idx) Nat.zero -> ",
                "Eq Nat (Nat.sub idx d) (Nat.succ g) -> ",
                "Eq Nat idx (Nat.add (Nat.succ g) d)) ",
                // depth = 0
                "(fun (idx : Nat) (g : Nat) ",
                "(_ : Eq Nat (Nat.sub Nat.zero idx) Nat.zero) ",
                "(h_idx : Eq Nat (Nat.sub idx Nat.zero) (Nat.succ g)) => ",
                "Eq.trans Nat ",
                "idx ",
                "(Nat.succ g) ",
                "(Nat.add (Nat.succ g) Nat.zero) ",
                "(Eq.trans Nat ",
                "idx ",
                "(Nat.sub idx Nat.zero) ",
                "(Nat.succ g) ",
                "(Eq.symm Nat (Nat.sub idx Nat.zero) idx (nat_sub_zero_right idx)) ",
                "h_idx) ",
                "(Eq.symm Nat (Nat.add (Nat.succ g) Nat.zero) (Nat.succ g) ",
                "(nat_add_zero_right (Nat.succ g)))) ",
                // depth = succ d
                "(fun (d : Nat) ",
                "(ih : forall (idx : Nat) (g : Nat), ",
                "Eq Nat (Nat.sub d idx) Nat.zero -> ",
                "Eq Nat (Nat.sub idx d) (Nat.succ g) -> ",
                "Eq Nat idx (Nat.add (Nat.succ g) d)) => ",
                "(fun (idx : Nat) (g : Nat) ",
                "(h_zero_succ : Eq Nat (Nat.sub (Nat.succ d) idx) Nat.zero) ",
                "(h_gap_succ : Eq Nat (Nat.sub idx (Nat.succ d)) (Nat.succ g)) => ",
                "Nat.rec ",
                "(fun (idx : Nat) => forall (g : Nat), ",
                "Eq Nat (Nat.sub (Nat.succ d) idx) Nat.zero -> ",
                "Eq Nat (Nat.sub idx (Nat.succ d)) (Nat.succ g) -> ",
                "Eq Nat idx (Nat.add (Nat.succ g) (Nat.succ d))) ",
                // idx = 0: impossible via sub 0 (succ d) = 0
                "(fun (g : Nat) ",
                "(_ : Eq Nat (Nat.sub (Nat.succ d) Nat.zero) Nat.zero) ",
                "(h_impossible : Eq Nat (Nat.sub Nat.zero (Nat.succ d)) (Nat.succ g)) => ",
                "Eq.symm Nat ",
                "(Nat.add (Nat.succ g) (Nat.succ d)) ",
                "Nat.zero ",
                "(Eq.cong Nat Nat ",
                "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) Nat.zero ",
                "(fun (_ : Nat) (_ : Nat) => Nat.add (Nat.succ g) (Nat.succ d)) n) ",
                "(Nat.succ g) ",
                "Nat.zero ",
                "(Eq.trans Nat ",
                "(Nat.succ g) ",
                "(Nat.sub Nat.zero (Nat.succ d)) ",
                "Nat.zero ",
                "(Eq.symm Nat (Nat.sub Nat.zero (Nat.succ d)) (Nat.succ g) h_impossible) ",
                "(nat_sub_zero_left (Nat.succ d))))) ",
                // idx = succ j
                "(fun (j : Nat) ",
                "(_ : forall (g : Nat), ",
                "Eq Nat (Nat.sub (Nat.succ d) j) Nat.zero -> ",
                "Eq Nat (Nat.sub j (Nat.succ d)) (Nat.succ g) -> ",
                "Eq Nat j (Nat.add (Nat.succ g) (Nat.succ d))) ",
                "(g : Nat) ",
                "(h_succ_zero : Eq Nat (Nat.sub (Nat.succ d) (Nat.succ j)) Nat.zero) ",
                "(h_succ_gap : Eq Nat (Nat.sub (Nat.succ j) (Nat.succ d)) (Nat.succ g)) => ",
                "Eq.cong Nat Nat Nat.succ ",
                "j ",
                "(Nat.add (Nat.succ g) d) ",
                "(ih j g ",
                "(Eq.trans Nat ",
                "(Nat.sub d j) ",
                "(Nat.sub (Nat.succ d) (Nat.succ j)) ",
                "Nat.zero ",
                "(Eq.symm Nat (Nat.sub (Nat.succ d) (Nat.succ j)) (Nat.sub d j) ",
                "(nat_sub_succ_succ d j)) ",
                "h_succ_zero) ",
                "(Eq.trans Nat ",
                "(Nat.sub j d) ",
                "(Nat.sub (Nat.succ j) (Nat.succ d)) ",
                "(Nat.succ g) ",
                "(Eq.symm Nat (Nat.sub (Nat.succ j) (Nat.succ d)) (Nat.sub j d) ",
                "(nat_sub_succ_succ j d)) ",
                "h_succ_gap))) ",
                "idx g h_zero_succ h_gap_succ)) ",
                "depth i gap h_zero h_gap",
            ).to_string()),
            is_axiom: false,
            description: "If depth <= i and i - depth = succ gap, then i = depth + succ gap. DerivedProved by Nat.rec on depth with an impossible idx=0 branch and a nat_sub_succ_succ reduction in the successor case. Part of #464.".to_string(),
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
                "nat_add_zero_right".to_string(),
                "nat_sub_succ_succ".to_string(),
                "nat_sub_zero_left".to_string(),
                "nat_sub_zero_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_zero_add_monotone: if a <= b and c <= d then a+c <= b+d.
        //
        // Proof by Nat.rec on c.
        //   Base c=0: add(a,0)=a definitionally, inline nat_sub_zero_add_right
        //     via Nat.rec on d (sub(a,add(b,d))=0 from sub(a,b)=0).
        //   Step c=succ c': inner Nat.rec convoy on d.
        //     d=0: sub(succ c',0)=succ c'=0 is absurd, derive via Nat.rec selector.
        //     d=succ d': sub(succ c',succ d')=sub(c',d') via defining iota.
        //       add(a,succ c')=succ(add(a,c')) and add(b,succ d')=succ(add(b,d'))
        //       by defining iota. Then nat_sub_succ_succ reduces goal to IH.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_add_monotone".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat) (c : Nat) (d : Nat), ",
                "Eq Nat (Nat.sub a b) Nat.zero -> ",
                "Eq Nat (Nat.sub c d) Nat.zero -> ",
                "Eq Nat (Nat.sub (Nat.add a c) (Nat.add b d)) Nat.zero",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) (d : Nat) ",
                    "(h_ab : Eq Nat (Nat.sub a b) Nat.zero) ",
                    "(h_cd : Eq Nat (Nat.sub c d) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (c : Nat) => forall (d : Nat), ",
                    "Eq Nat (Nat.sub c d) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.add a c) (Nat.add b d)) Nat.zero) ",
                    // Base: c=0
                    "(fun (d : Nat) ",
                    "(_ : Eq Nat (Nat.sub Nat.zero d) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (d : Nat) => Eq Nat (Nat.sub a (Nat.add b d)) Nat.zero) ",
                    "h_ab ",
                    "(fun (k : Nat) (ih : Eq Nat (Nat.sub a (Nat.add b k)) Nat.zero) => ",
                    "nat_sub_zero_implies_sub_succ_zero a (Nat.add b k) ih) ",
                    "d) ",
                    // Step: c = succ c'
                    "(fun (c' : Nat) ",
                    "(ih : forall (d : Nat), ",
                    "Eq Nat (Nat.sub c' d) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.add a c') (Nat.add b d)) Nat.zero) => ",
                    "fun (d : Nat) (h_step : Eq Nat (Nat.sub (Nat.succ c') d) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (d : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.succ c') d) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.add a (Nat.succ c')) (Nat.add b d)) Nat.zero) ",
                    // d=0: impossible (sub(succ c', 0) = succ c' ≠ 0)
                    "(fun (h_impossible : Eq Nat (Nat.sub (Nat.succ c') Nat.zero) Nat.zero) => ",
                    "Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) Nat.zero ",
                    "(fun (_ : Nat) (_ : Nat) => ",
                    "Nat.sub (Nat.add a (Nat.succ c')) (Nat.add b Nat.zero)) n) ",
                    "(Nat.succ c') ",
                    "Nat.zero ",
                    "(Eq.trans Nat (Nat.succ c') ",
                    "(Nat.sub (Nat.succ c') Nat.zero) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ c') Nat.zero) (Nat.succ c') ",
                    "(nat_sub_zero_right (Nat.succ c'))) ",
                    "h_impossible)) ",
                    // d=succ d': definitional iota reduces goal to IH
                    "(fun (d' : Nat) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ c') d') Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.add a (Nat.succ c')) (Nat.add b d')) Nat.zero) => ",
                    "fun (h_succ : Eq Nat (Nat.sub (Nat.succ c') (Nat.succ d')) Nat.zero) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.add a (Nat.succ c')) (Nat.add b (Nat.succ d'))) ",
                    "(Nat.sub (Nat.add a c') (Nat.add b d')) ",
                    "Nat.zero ",
                    "(nat_sub_succ_succ (Nat.add a c') (Nat.add b d')) ",
                    "(ih d' ",
                    "(Eq.trans Nat (Nat.sub c' d') ",
                    "(Nat.sub (Nat.succ c') (Nat.succ d')) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ c') (Nat.succ d')) (Nat.sub c' d') ",
                    "(nat_sub_succ_succ c' d')) ",
                    "h_succ))) ",
                    "d h_step) ",
                    "c d h_cd",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "If a <= b and c <= d then a+c <= b+d. DerivedProved via Nat.rec on c with inner convoy on d. Part of #464.".to_string(),
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
                "nat_sub_zero_implies_sub_succ_zero".to_string(),
                "nat_sub_zero_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
