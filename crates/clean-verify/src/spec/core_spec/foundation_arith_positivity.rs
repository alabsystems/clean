// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Nat subtraction positivity propagation lemmas.
//!
//! Split from foundation_arith_witnesses.rs for file size.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_foundation_arith_positivity(&mut self) -> Result<(), SpecError> {
        // nat_sub_pos_succ: if sub d i > 0 then sub (succ d) i > 0
        //
        // Proof by outer Nat.rec on i (universalizing d).
        //   Base i=0: unconditionally true since sub(succ d)(0) = succ d.
        //   Step i=succ j: inner Nat.rec on d.
        //     d=0: hypothesis gives 0 = succ(...), vacuous via Nat.rec discriminator.
        //     d=succ d': chain nat_sub_succ_succ both sides + apply outer IH.
        // Part of #464, #461.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_pos_succ".to_string(),
            type_src: concat!(
                "forall (d : Nat) (i : Nat), ",
                "Eq Nat (Nat.sub d i) (Nat.succ (Nat.sub (Nat.sub d i) (Nat.succ Nat.zero))) -> ",
                "Eq Nat (Nat.sub (Nat.succ d) i) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d) i) (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (d : Nat) (i : Nat) ",
                    "(h : Eq Nat (Nat.sub d i) (Nat.succ (Nat.sub (Nat.sub d i) (Nat.succ Nat.zero)))) => ",
                    // Outer Nat.rec on i, motive universalizes d
                    "(Nat.rec ",
                    "(fun (j : Nat) => forall (d : Nat), ",
                    "Eq Nat (Nat.sub d j) (Nat.succ (Nat.sub (Nat.sub d j) (Nat.succ Nat.zero))) -> ",
                    "Eq Nat (Nat.sub (Nat.succ d) j) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d) j) (Nat.succ Nat.zero)))) ",
                    // --- base i=0 ---
                    "(fun (d : Nat) (_ : Eq Nat (Nat.sub d Nat.zero) ",
                    "(Nat.succ (Nat.sub (Nat.sub d Nat.zero) (Nat.succ Nat.zero)))) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ d) Nat.zero) ",
                    "(Nat.succ d) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d) Nat.zero) (Nat.succ Nat.zero))) ",
                    "(nat_sub_zero_right (Nat.succ d)) ",
                    "(Eq.symm Nat ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d) Nat.zero) (Nat.succ Nat.zero))) ",
                    "(Nat.succ d) ",
                    "(Eq.trans Nat ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d) Nat.zero) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.succ d) (Nat.succ Nat.zero))) ",
                    "(Nat.succ d) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ (Nat.sub x (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ d) Nat.zero) (Nat.succ d) ",
                    "(nat_sub_zero_right (Nat.succ d))) ",
                    "(Eq.cong Nat Nat (Nat.succ) ",
                    "(Nat.sub (Nat.succ d) (Nat.succ Nat.zero)) d ",
                    "(nat_sub_succ_one d))))) ",
                    // --- step i=succ j ---
                    "(fun (j : Nat) ",
                    "(ih : forall (d : Nat), ",
                    "Eq Nat (Nat.sub d j) (Nat.succ (Nat.sub (Nat.sub d j) (Nat.succ Nat.zero))) -> ",
                    "Eq Nat (Nat.sub (Nat.succ d) j) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d) j) (Nat.succ Nat.zero)))) => ",
                    // Inner Nat.rec on d
                    "Nat.rec ",
                    "(fun (k : Nat) => ",
                    "Eq Nat (Nat.sub k (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub k (Nat.succ j)) (Nat.succ Nat.zero))) -> ",
                    "Eq Nat (Nat.sub (Nat.succ k) (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ k) (Nat.succ j)) (Nat.succ Nat.zero)))) ",
                    // d=0: vacuous via Nat.rec discriminator
                    "(fun (h_zero : Eq Nat (Nat.sub Nat.zero (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub Nat.zero (Nat.succ j)) (Nat.succ Nat.zero)))) => ",
                    "Eq.symm Nat ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ Nat.zero) (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ j)) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ j)) ",
                    "(fun (_ : Nat) (_ : Nat) => ",
                    "Nat.succ (Nat.sub (Nat.sub (Nat.succ Nat.zero) (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "n) ",
                    "(Nat.succ (Nat.sub (Nat.sub Nat.zero (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "Nat.zero ",
                    "(Eq.trans Nat ",
                    "(Nat.succ (Nat.sub (Nat.sub Nat.zero (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "(Nat.sub Nat.zero (Nat.succ j)) ",
                    "Nat.zero ",
                    "(Eq.symm Nat (Nat.sub Nat.zero (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub Nat.zero (Nat.succ j)) (Nat.succ Nat.zero))) h_zero) ",
                    "(nat_sub_zero_left (Nat.succ j))))) ",
                    // d=succ d2: reduce via nat_sub_succ_succ + apply outer IH
                    "(fun (d2 : Nat) ",
                    "(_ : Eq Nat (Nat.sub d2 (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub d2 (Nat.succ j)) (Nat.succ Nat.zero))) -> ",
                    "Eq Nat (Nat.sub (Nat.succ d2) (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d2) (Nat.succ j)) (Nat.succ Nat.zero)))) ",
                    "(h_sd : Eq Nat (Nat.sub (Nat.succ d2) (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d2) (Nat.succ j)) (Nat.succ Nat.zero)))) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ (Nat.succ d2)) (Nat.succ j)) ",
                    "(Nat.sub (Nat.succ d2) j) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ d2)) (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "(nat_sub_succ_succ (Nat.succ d2) j) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.succ d2) j) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d2) j) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ d2)) (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "(ih d2 ",
                    "(Eq.trans Nat (Nat.sub d2 j) (Nat.sub (Nat.succ d2) (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub d2 j) (Nat.succ Nat.zero))) ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ d2) (Nat.succ j)) (Nat.sub d2 j) ",
                    "(nat_sub_succ_succ d2 j)) ",
                    "(Eq.trans Nat (Nat.sub (Nat.succ d2) (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ d2) (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.sub d2 j) (Nat.succ Nat.zero))) ",
                    "h_sd ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ (Nat.sub x (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ d2) (Nat.succ j)) (Nat.sub d2 j) ",
                    "(nat_sub_succ_succ d2 j))))) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ (Nat.sub x (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ d2) j) ",
                    "(Nat.sub (Nat.succ (Nat.succ d2)) (Nat.succ j)) ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ (Nat.succ d2)) (Nat.succ j)) (Nat.sub (Nat.succ d2) j) ",
                    "(nat_sub_succ_succ (Nat.succ d2) j))))) ",
                    // end inner Nat.rec on d
                    ") ",
                    // end outer Nat.rec on i; apply to d and h
                    "i) d h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "If sub d i > 0 then sub (succ d) i > 0. DerivedProved via double Nat.rec (outer on i, inner on d) + Nat.rec discriminator for vacuous d=0. Part of #464, #461."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.cong".to_string(),
                "nat_sub_zero_right".to_string(),
                "nat_sub_zero_left".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_pos_add_right: if sub d i > 0 then sub (add d n) i > 0
        //
        // Proof by Nat.rec on n.
        //   Base n=0: add d 0 = d definitionally, hypothesis suffices.
        //   Step n=succ k: add d (succ k) = succ(add d k) definitionally.
        //     Apply nat_sub_pos_succ to the IH result.
        // Part of #464, #461.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_pos_add_right".to_string(),
            type_src: concat!(
                "forall (d : Nat) (n : Nat) (i : Nat), ",
                "Eq Nat (Nat.sub d i) (Nat.succ (Nat.sub (Nat.sub d i) (Nat.succ Nat.zero))) -> ",
                "Eq Nat (Nat.sub (Nat.add d n) i) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add d n) i) (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (d : Nat) (n : Nat) (i : Nat) ",
                    "(h : Eq Nat (Nat.sub d i) (Nat.succ (Nat.sub (Nat.sub d i) (Nat.succ Nat.zero)))) => ",
                    "Nat.rec ",
                    "(fun (k : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.add d k) i) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add d k) i) (Nat.succ Nat.zero)))) ",
                    // base n=0: add d 0 = d, so same as h
                    "h ",
                    // step n=succ k: add d (succ k) = succ(add d k), apply nat_sub_pos_succ
                    "(fun (k : Nat) (ih : Eq Nat (Nat.sub (Nat.add d k) i) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add d k) i) (Nat.succ Nat.zero)))) => ",
                    "nat_sub_pos_succ (Nat.add d k) i ih) ",
                    "n",
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "If sub d i > 0 then sub (add d n) i > 0. DerivedProved via Nat.rec on n using nat_sub_pos_succ. Part of #464, #461."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "nat_sub_pos_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_pos_witness_from_succ_eq: if n = succ k then n = succ (n - 1).
        //
        // Converts a "successor equality" into the positivity-witness shape
        // required by lift_at_bvar_below. Proof chain:
        //   n = succ k [h]
        //   = succ (n - 1) [Eq.cong succ (Eq.symm (trans (cong sub h) (nat_sub_succ_one k)))]
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_pos_witness_from_succ_eq".to_string(),
            type_src: concat!(
                "forall (n : Nat) (k : Nat), ",
                "Eq Nat n (Nat.succ k) -> ",
                "Eq Nat n (Nat.succ (Nat.sub n (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) (k : Nat) ",
                    "(h : Eq Nat n (Nat.succ k)) => ",
                    "Eq.trans Nat n (Nat.succ k) ",
                    "(Nat.succ (Nat.sub n (Nat.succ Nat.zero))) ",
                    "h ",
                    "(Eq.cong Nat Nat Nat.succ ",
                    "k (Nat.sub n (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat (Nat.sub n (Nat.succ Nat.zero)) k ",
                    "(Eq.trans Nat ",
                    "(Nat.sub n (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.succ k) (Nat.succ Nat.zero)) ",
                    "k ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                    "n (Nat.succ k) h) ",
                    "(nat_sub_succ_one k))))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "If n = succ k then n = succ (n - 1). DerivedProved. Converts successor equality to positivity witness shape. Part of #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.cong".to_string(),
                "nat_sub_succ_one".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // lift_instantiate_swap bvar-convoy positivity helpers (Wave 129, #2859).
        // =========================================================

        // nat_sub_zero_of_sub_pos: antisymmetry — if sub(i, d) = succ(k) then
        // sub(d, i) = 0.
        //
        // Informally: i > d implies d <= i (so d - i = 0). The general-i form
        // missing from the tree (nat_sub_geq_of_sub_succ requires the minuend to
        // be a syntactic successor). Used by the i>d leaves of
        // lift_instantiate_swap_bvar to supply instantiate_bvar_at_above's
        // sub(d,i)=0 hypothesis.
        //
        // Proof by double Nat.rec (outer on d universalizing i,k; inner on i):
        //   d=0: sub(0, i) = 0 by nat_sub_zero_left i.
        //   d=succ d', i=0: sub(0, succ d') = 0 != succ k, absurd. Discriminator.
        //   d=succ d', i=succ i': nat_sub_succ_succ reduces hyp to sub(i', d') = succ k
        //     and goal to sub(d', i'); outer IH closes.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_of_sub_pos".to_string(),
            type_src: concat!(
                "forall (i : Nat) (d : Nat) (k : Nat), ",
                "Eq Nat (Nat.sub i d) (Nat.succ k) -> ",
                "Eq Nat (Nat.sub d i) Nat.zero",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (d : Nat) (k : Nat) ",
                    "(h : Eq Nat (Nat.sub i d) (Nat.succ k)) => ",
                    // outer Nat.rec on d, motive universalizes i, k
                    "Nat.rec ",
                    "(fun (d : Nat) => forall (i : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub i d) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub d i) Nat.zero) ",
                    // d=0: sub(0, i) = 0
                    "(fun (i : Nat) (k : Nat) ",
                    "(_ : Eq Nat (Nat.sub i Nat.zero) (Nat.succ k)) => ",
                    "nat_sub_zero_left i) ",
                    // d=succ d'
                    "(fun (d' : Nat) ",
                    "(ih : forall (i : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub i d') (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub d' i) Nat.zero) ",
                    "(i : Nat) (k : Nat) ",
                    "(h_sd : Eq Nat (Nat.sub i (Nat.succ d')) (Nat.succ k)) => ",
                    // inner Nat.rec on i
                    "Nat.rec ",
                    "(fun (i : Nat) => ",
                    "Eq Nat (Nat.sub i (Nat.succ d')) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub (Nat.succ d') i) Nat.zero) ",
                    // i=0: sub(0, succ d') = 0 != succ k, absurd. f 0 = sub(succ d',0), f(succ _)=0.
                    "(fun (h_z : Eq Nat (Nat.sub Nat.zero (Nat.succ d')) (Nat.succ k)) => ",
                    "Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) ",
                    "(Nat.sub (Nat.succ d') Nat.zero) ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.zero) n) ",
                    "Nat.zero (Nat.succ k) ",
                    "(Eq.trans Nat Nat.zero (Nat.sub Nat.zero (Nat.succ d')) (Nat.succ k) ",
                    "(Eq.symm Nat (Nat.sub Nat.zero (Nat.succ d')) Nat.zero ",
                    "(nat_sub_zero_left (Nat.succ d'))) ",
                    "h_z)) ",
                    // i=succ i': reduce via nat_sub_succ_succ both sides, apply outer IH.
                    "(fun (i' : Nat) ",
                    "(_ : Eq Nat (Nat.sub i' (Nat.succ d')) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub (Nat.succ d') i') Nat.zero) ",
                    "(h_ss : Eq Nat (Nat.sub (Nat.succ i') (Nat.succ d')) (Nat.succ k)) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ d') (Nat.succ i')) ",
                    "(Nat.sub d' i') Nat.zero ",
                    "(nat_sub_succ_succ d' i') ",
                    "(ih i' k ",
                    "(Eq.trans Nat (Nat.sub i' d') ",
                    "(Nat.sub (Nat.succ i') (Nat.succ d')) (Nat.succ k) ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ i') (Nat.succ d')) (Nat.sub i' d') ",
                    "(nat_sub_succ_succ i' d')) ",
                    "h_ss))) ",
                    "i h_sd) ",
                    "d i k h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If sub(i, d) = succ(k) then sub(d, i) = 0 (antisymmetry, general i). ",
                "DerivedProved via double Nat.rec (outer on d, inner on i) with ",
                "nat_sub_succ_succ + discriminator. Supplies instantiate_bvar_at_above's ",
                "sub(d,i)=0 hypothesis in the i>d leaves of lift_instantiate_swap_bvar. ",
                "Part of #2859 Wave 129 (Route B).",
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
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_pred_add_at_pos: if sub(i, d) = succ(k) then
        //   sub(add(i, sd), 1) = add(sub(i, 1), sd).
        //
        // Informally: (i + sd) - 1 = (i - 1) + sd when i >= 1. Identical to
        // nat_pred_add_right (which lives in the later interchange-helpers
        // bundle); re-derived here so the lift_instantiate_swap_bvar i>=succ(d+k)
        // leaf (which loads before that bundle) can use it for the
        // (i-1)+a = (i+a)-1 bridge. Depends only on lemmas available earlier.
        //
        // Proof by Nat.rec on i:
        //   i=0: sub(0, d) = 0 != succ(k), absurd. Discriminator.
        //   i=succ i': both sides reduce to add(i', sd) definitionally
        //     (nat_succ_add + nat_sub_succ_one).
        self.add_definition_structural(SpecDefinition {
            name: "nat_pred_add_at_pos".to_string(),
            type_src: concat!(
                "forall (i : Nat) (sd : Nat) (d : Nat) (k : Nat), ",
                "Eq Nat (Nat.sub i d) (Nat.succ k) -> ",
                "Eq Nat (Nat.sub (Nat.add i sd) (Nat.succ Nat.zero)) ",
                "(Nat.add (Nat.sub i (Nat.succ Nat.zero)) sd)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (sd : Nat) (d : Nat) (k : Nat) ",
                    "(h : Eq Nat (Nat.sub i d) (Nat.succ k)) => ",
                    "Nat.rec ",
                    "(fun (i : Nat) => forall (sd : Nat) (d : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub i d) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub (Nat.add i sd) (Nat.succ Nat.zero)) ",
                    "(Nat.add (Nat.sub i (Nat.succ Nat.zero)) sd)) ",
                    "(fun (sd : Nat) (d : Nat) (k : Nat) ",
                    "(h0 : Eq Nat (Nat.sub Nat.zero d) (Nat.succ k)) => ",
                    "Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) ",
                    "(Nat.sub (Nat.add Nat.zero sd) (Nat.succ Nat.zero)) ",
                    "(fun (_ : Nat) (_ : Nat) => ",
                    "Nat.add (Nat.sub Nat.zero (Nat.succ Nat.zero)) sd) n) ",
                    "Nat.zero (Nat.succ k) ",
                    "(Eq.trans Nat Nat.zero (Nat.sub Nat.zero d) (Nat.succ k) ",
                    "(Eq.symm Nat (Nat.sub Nat.zero d) Nat.zero (nat_sub_zero_left d)) ",
                    "h0)) ",
                    "(fun (i' : Nat) ",
                    "(_ : forall (sd : Nat) (d : Nat) (k : Nat), ",
                    "Eq Nat (Nat.sub i' d) (Nat.succ k) -> ",
                    "Eq Nat (Nat.sub (Nat.add i' sd) (Nat.succ Nat.zero)) ",
                    "(Nat.add (Nat.sub i' (Nat.succ Nat.zero)) sd)) ",
                    "(sd : Nat) (d : Nat) (k : Nat) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ i') d) (Nat.succ k)) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.add (Nat.succ i') sd) (Nat.succ Nat.zero)) ",
                    "(Nat.add i' sd) ",
                    "(Nat.add (Nat.sub (Nat.succ i') (Nat.succ Nat.zero)) sd) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.add (Nat.succ i') sd) (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.succ (Nat.add i' sd)) (Nat.succ Nat.zero)) ",
                    "(Nat.add i' sd) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                    "(Nat.add (Nat.succ i') sd) (Nat.succ (Nat.add i' sd)) ",
                    "(nat_succ_add i' sd)) ",
                    "(nat_sub_succ_one (Nat.add i' sd))) ",
                    "(Eq.symm Nat ",
                    "(Nat.add (Nat.sub (Nat.succ i') (Nat.succ Nat.zero)) sd) ",
                    "(Nat.add i' sd) ",
                    "(Eq.cong Nat Nat (fun (x : Nat) => Nat.add x sd) ",
                    "(Nat.sub (Nat.succ i') (Nat.succ Nat.zero)) i' ",
                    "(nat_sub_succ_one i')))) ",
                    "i sd d k h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If sub(i, d) = succ(k) then sub(add(i, sd), 1) = add(sub(i, 1), sd). ",
                "Early-loading twin of nat_pred_add_right for the lift_instantiate_swap_bvar ",
                "(i-1)+a = (i+a)-1 bridge. DerivedProved via Nat.rec on i. ",
                "Part of #2859 Wave 129 (Route B).",
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
                "nat_sub_succ_one".to_string(),
                "nat_sub_zero_left".to_string(),
                "nat_succ_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_pos_succ_add_witness: if sub(i, d) = 0 then sub(succ(d+k), i)
        // is positive (positivity-witness shape).
        //
        // Informally: i <= d implies i <= d+k < succ(d+k), so succ(d+k) > i.
        // Used by the i<d and i=d leaves of lift_instantiate_swap_bvar to drive
        // the RHS lift_at_bvar_below on the structural lift at cutoff succ(d+k).
        //
        // Proof by Nat.rec on k (motive universalizes nothing extra; d, i fixed):
        //   base k=0:  d+0 = d definitionally; nat_sub_pos_witness i d h gives
        //              sub(succ d, i) positive.
        //   step k=succ k': d+(succ k') = succ(d+k') definitionally, so
        //              succ(d+(succ k')) = succ(succ(d+k')); apply
        //              nat_sub_pos_succ (succ(d+k')) i to the IH.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_pos_succ_add_witness".to_string(),
            type_src: concat!(
                "forall (i : Nat) (d : Nat) (k : Nat), ",
                "Eq Nat (Nat.sub i d) Nat.zero -> ",
                "Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k)) i) (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (d : Nat) (k : Nat) ",
                    "(h : Eq Nat (Nat.sub i d) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (g : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.succ (Nat.add d g)) i) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d g)) i) (Nat.succ Nat.zero)))) ",
                    // base k=0: Nat.add d Nat.zero = d definitionally
                    "(nat_sub_pos_witness i d h) ",
                    // step k=succ k': Nat.add d (succ k') = succ(Nat.add d k') definitionally
                    "(fun (k' : Nat) ",
                    "(ih : Eq Nat (Nat.sub (Nat.succ (Nat.add d k')) i) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k')) i) (Nat.succ Nat.zero)))) => ",
                    "nat_sub_pos_succ (Nat.succ (Nat.add d k')) i ih) ",
                    "k",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If sub(i, d) = 0 then sub(succ(d+k), i) is positive. ",
                "DerivedProved via Nat.rec on k using nat_sub_pos_witness (base) and ",
                "nat_sub_pos_succ (step). Drives the RHS below-lift in the i<=d leaves ",
                "of lift_instantiate_swap_bvar. Part of #2859 Wave 129 (Route B).",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "nat_sub_pos_succ".to_string(),
                "nat_sub_pos_witness".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_zero_pred_of_succ_add_zero: if sub(succ(d+k), i) = 0 then
        // sub(d+k, i-1) = 0.
        //
        // Informally: i >= succ(d+k) implies i-1 >= d+k.
        // Used by the (i>d, i>=succ(d+k)) leaf of lift_instantiate_swap_bvar to
        // drive the LHS lift_at_bvar_geq on the structural lift at cutoff d+k.
        //
        // Proof by Nat.rec on i (motive universalizes nothing; d, k fixed):
        //   i=0: sub(succ(d+k), 0) = succ(d+k) != 0, absurd. Discriminator on h.
        //   i=succ i': sub(i, 1) = i' definitionally (nat_sub_succ_one); goal
        //     sub(d+k, i') = 0 follows from h via nat_sub_succ_succ (d+k) i'.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_pred_of_succ_add_zero".to_string(),
            type_src: concat!(
                "forall (d : Nat) (k : Nat) (i : Nat), ",
                "Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) Nat.zero -> ",
                "Eq Nat (Nat.sub (Nat.add d k) (Nat.sub i (Nat.succ Nat.zero))) Nat.zero",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (d : Nat) (k : Nat) (i : Nat) ",
                    "(h : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (j : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) j) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.add d k) (Nat.sub j (Nat.succ Nat.zero))) Nat.zero) ",
                    // i=0: sub(succ(d+k), 0) = succ(d+k); hypothesis is succ(d+k) = 0, absurd.
                    // Single Eq.cong discriminator: f 0 = goalLHS, f (succ _) = 0; apply to
                    // h0 (succ(d+k) = 0 by defeq) then Eq.symm to land the goal.
                    "(fun (h0 : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) Nat.zero) Nat.zero) => ",
                    "Eq.symm Nat Nat.zero ",
                    "(Nat.sub (Nat.add d k) (Nat.sub Nat.zero (Nat.succ Nat.zero))) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) ",
                    "(Nat.sub (Nat.add d k) (Nat.sub Nat.zero (Nat.succ Nat.zero))) ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.zero) n) ",
                    "(Nat.succ (Nat.add d k)) Nat.zero ",
                    "h0)) ",
                    // i=succ i': sub(succ i', 1) = i' definitionally; need sub(d+k, i') = 0.
                    "(fun (i' : Nat) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i') Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.add d k) (Nat.sub i' (Nat.succ Nat.zero))) Nat.zero) ",
                    "(hs : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) Nat.zero) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.add d k) i') ",
                    "(Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "Nat.zero ",
                    "(Eq.symm Nat ",
                    "(Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "(Nat.sub (Nat.add d k) i') ",
                    "(nat_sub_succ_succ (Nat.add d k) i')) ",
                    "hs) ",
                    "i h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If sub(succ(d+k), i) = 0 then sub(d+k, i-1) = 0. ",
                "DerivedProved via Nat.rec on i (i=0 absurd by discriminator; ",
                "i=succ i' via nat_sub_succ_succ). Drives the LHS geq-lift in the ",
                "(i>d, i>=succ(d+k)) leaf of lift_instantiate_swap_bvar. ",
                "Part of #2859 Wave 129 (Route B).",
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
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_pos_pred_of_succ_add_pos: if sub(succ(d+k), i) is positive and
        // sub(i, d) is positive then sub(d+k, i-1) is positive (witness shapes).
        //
        // Informally: d < i <= d+k implies d <= i-1 < d+k.
        // Used by the (i>d, i<succ(d+k)) leaf of lift_instantiate_swap_bvar to
        // drive the LHS lift_at_bvar_below on the structural lift at cutoff d+k.
        //
        // Proof by Nat.rec on i (motive universalizes nothing; d, k fixed):
        //   i=0: sub(0, d) = 0, contradicting the sub(i,d) positivity hyp.
        //     Discriminator on the positivity hypothesis.
        //   i=succ i': sub(i, 1) = i' definitionally; goal sub(d+k, i') positive
        //     follows from the sub(succ(d+k), succ i') positivity via
        //     nat_sub_succ_succ (d+k) i'.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_pos_pred_of_succ_add_pos".to_string(),
            type_src: concat!(
                "forall (d : Nat) (k : Nat) (i : Nat), ",
                "Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k)) i) (Nat.succ Nat.zero))) -> ",
                "Eq Nat (Nat.sub i d) (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) -> ",
                "Eq Nat (Nat.sub (Nat.add d k) (Nat.sub i (Nat.succ Nat.zero))) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.add d k) (Nat.sub i (Nat.succ Nat.zero))) ",
                "(Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (d : Nat) (k : Nat) (i : Nat) ",
                    "(hck : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k)) i) (Nat.succ Nat.zero)))) ",
                    "(hid : Eq Nat (Nat.sub i d) ",
                    "(Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)))) => ",
                    "Nat.rec ",
                    "(fun (j : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) j) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k)) j) (Nat.succ Nat.zero))) -> ",
                    "Eq Nat (Nat.sub j d) ",
                    "(Nat.succ (Nat.sub (Nat.sub j d) (Nat.succ Nat.zero))) -> ",
                    "Eq Nat (Nat.sub (Nat.add d k) (Nat.sub j (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add d k) (Nat.sub j (Nat.succ Nat.zero))) ",
                    "(Nat.succ Nat.zero)))) ",
                    // i=0: sub(0, d) = 0 (nat_sub_zero_left d) contradicts hid.
                    "(fun (_ : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) Nat.zero) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k)) Nat.zero) ",
                    "(Nat.succ Nat.zero)))) ",
                    "(hid0 : Eq Nat (Nat.sub Nat.zero d) ",
                    "(Nat.succ (Nat.sub (Nat.sub Nat.zero d) (Nat.succ Nat.zero)))) => ",
                    // From nat_sub_zero_left d : sub(0,d)=0, and hid0 : sub(0,d) = succ(...),
                    // derive 0 = succ(...) and discriminate with f 0 = goalLHS,
                    // f (succ _) = goalRHS so Eq.cong directly yields Eq goalLHS goalRHS.
                    "Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) ",
                    "(Nat.sub (Nat.add d k) (Nat.sub Nat.zero (Nat.succ Nat.zero))) ",
                    "(fun (_ : Nat) (_ : Nat) => ",
                    "Nat.succ (Nat.sub (Nat.sub (Nat.add d k) (Nat.sub Nat.zero (Nat.succ Nat.zero))) ",
                    "(Nat.succ Nat.zero))) n) ",
                    "Nat.zero ",
                    "(Nat.succ (Nat.sub (Nat.sub Nat.zero d) (Nat.succ Nat.zero))) ",
                    "(Eq.trans Nat Nat.zero (Nat.sub Nat.zero d) ",
                    "(Nat.succ (Nat.sub (Nat.sub Nat.zero d) (Nat.succ Nat.zero))) ",
                    "(Eq.symm Nat (Nat.sub Nat.zero d) Nat.zero (nat_sub_zero_left d)) ",
                    "hid0)) ",
                    // i=succ i': sub(succ i', 1) = i' definitionally; goal sub(d+k, i') positive.
                    "(fun (i' : Nat) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) i') ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k)) i') (Nat.succ Nat.zero))) -> ",
                    "Eq Nat (Nat.sub i' d) ",
                    "(Nat.succ (Nat.sub (Nat.sub i' d) (Nat.succ Nat.zero))) -> ",
                    "Eq Nat (Nat.sub (Nat.add d k) (Nat.sub i' (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add d k) (Nat.sub i' (Nat.succ Nat.zero))) ",
                    "(Nat.succ Nat.zero)))) ",
                    "(hcks : Eq Nat (Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "(Nat.succ Nat.zero)))) ",
                    "(_ : Eq Nat (Nat.sub (Nat.succ i') d) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ i') d) (Nat.succ Nat.zero)))) => ",
                    // sub(succ i', 1) = i' definitionally, so goal is sub(d+k, i') positive.
                    // sub(d+k, i') = sub(succ(d+k), succ i') via nat_sub_succ_succ; transport hcks.
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.add d k) i') ",
                    "(Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add d k) i') (Nat.succ Nat.zero))) ",
                    "(Eq.symm Nat ",
                    "(Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "(Nat.sub (Nat.add d k) i') ",
                    "(nat_sub_succ_succ (Nat.add d k) i')) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "(Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.add d k) i') (Nat.succ Nat.zero))) ",
                    "hcks ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ (Nat.sub x (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ (Nat.add d k)) (Nat.succ i')) ",
                    "(Nat.sub (Nat.add d k) i') ",
                    "(nat_sub_succ_succ (Nat.add d k) i')))) ",
                    "i hck hid",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If sub(succ(d+k), i) and sub(i, d) are positive then sub(d+k, i-1) ",
                "is positive. DerivedProved via Nat.rec on i (i=0 absurd by ",
                "discriminator on the sub(i,d) positivity; i=succ i' via ",
                "nat_sub_succ_succ). Drives the LHS below-lift in the ",
                "(i>d, i<succ(d+k)) leaf of lift_instantiate_swap_bvar. ",
                "Part of #2859 Wave 129 (Route B).",
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
                "nat_sub_succ_succ".to_string(),
                "nat_sub_zero_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
