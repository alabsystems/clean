// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Derived Nat subtraction witness lemmas split from foundation_arith_lemmas.rs

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_foundation_arith_witnesses(&mut self) -> Result<(), SpecError> {
        // nat_sub_zero_implies_sub_succ_zero: sub c i = 0 -> sub c (succ i) = 0
        //
        // If c ≤ i then c ≤ succ i. Proof by Nat.rec on i (outer), with inner
        // Nat.rec on c in the step case.
        //
        // Base i=0: hypothesis sub c 0 = c = 0, so c = 0, then sub 0 1 = 0
        //   by nat_sub_zero_left. Uses the "pred trick": Eq.cong with
        //   Nat.rec pred to extract c = 0 from succ-like hypothesis.
        //
        // Step i=succ j with IH (forall c, sub c j = 0 -> sub c (succ j) = 0):
        //   Inner Nat.rec on c:
        //     c=0: trivial via nat_sub_zero_left.
        //     c=succ m: nat_sub_succ_succ reduces both hypothesis and goal
        //       from (succ m, succ j) to (m, j), then outer IH closes.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_implies_sub_succ_zero".to_string(),
            type_src: concat!(
                "forall (c : Nat) (i : Nat), ",
                "Eq Nat (Nat.sub c i) Nat.zero -> ",
                "Eq Nat (Nat.sub c (Nat.succ i)) Nat.zero",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (c : Nat) (i : Nat) ",
                    "(h : Eq Nat (Nat.sub c i) Nat.zero) => ",
                    // Outer Nat.rec on i, motive universalizes c
                    "(Nat.rec ",
                    "(fun (j : Nat) => forall (c : Nat), ",
                    "Eq Nat (Nat.sub c j) Nat.zero -> ",
                    "Eq Nat (Nat.sub c (Nat.succ j)) Nat.zero) ",
                    // --- base i=0 ---
                    "(fun (c : Nat) (h0 : Eq Nat (Nat.sub c Nat.zero) Nat.zero) => ",
                    // derive c = 0 from sub c 0 = 0 via nat_sub_zero_right
                    // nat_sub_zero_right c : sub c 0 = c
                    // Eq.symm gives c = sub c 0, then Eq.trans with h0 gives c = 0
                    // Then Eq.cong with (fun x => sub x 1) gives sub c 1 = sub 0 1
                    // Then nat_sub_zero_left 1 gives sub 0 1 = 0
                    "Eq.trans Nat ",
                    "(Nat.sub c (Nat.succ Nat.zero)) ",
                    "(Nat.sub Nat.zero (Nat.succ Nat.zero)) ",
                    "Nat.zero ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                    "c Nat.zero ",
                    "(Eq.trans Nat c (Nat.sub c Nat.zero) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub c Nat.zero) c (nat_sub_zero_right c)) ",
                    "h0)) ",
                    "(nat_sub_zero_left (Nat.succ Nat.zero))) ",
                    // --- step i=succ j ---
                    "(fun (j : Nat) ",
                    "(ih : forall (c : Nat), ",
                    "Eq Nat (Nat.sub c j) Nat.zero -> ",
                    "Eq Nat (Nat.sub c (Nat.succ j)) Nat.zero) => ",
                    // Inner Nat.rec on c
                    "Nat.rec ",
                    "(fun (k : Nat) => ",
                    "Eq Nat (Nat.sub k (Nat.succ j)) Nat.zero -> ",
                    "Eq Nat (Nat.sub k (Nat.succ (Nat.succ j))) Nat.zero) ",
                    // c=0: trivial
                    "(fun (_ : Eq Nat (Nat.sub Nat.zero (Nat.succ j)) Nat.zero) => ",
                    "nat_sub_zero_left (Nat.succ (Nat.succ j))) ",
                    // c=succ m:
                    "(fun (m : Nat) ",
                    "(_ : Eq Nat (Nat.sub m (Nat.succ j)) Nat.zero -> ",
                    "Eq Nat (Nat.sub m (Nat.succ (Nat.succ j))) Nat.zero) ",
                    "(h_sm : Eq Nat (Nat.sub (Nat.succ m) (Nat.succ j)) Nat.zero) => ",
                    // sub (succ m) (succ (succ j)) = sub m (succ j) via nat_sub_succ_succ
                    // sub m j = 0 from h_sm via nat_sub_succ_succ (Eq.symm + Eq.trans)
                    // ih m : sub m j = 0 -> sub m (succ j) = 0
                    // chain: sub (succ m) (succ (succ j)) = sub m (succ j) = 0
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ m) (Nat.succ (Nat.succ j))) ",
                    "(Nat.sub m (Nat.succ j)) ",
                    "Nat.zero ",
                    "(nat_sub_succ_succ m (Nat.succ j)) ",
                    "(ih m ",
                    "(Eq.trans Nat (Nat.sub m j) (Nat.sub (Nat.succ m) (Nat.succ j)) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ m) (Nat.succ j)) (Nat.sub m j) ",
                    "(nat_sub_succ_succ m j)) ",
                    "h_sm))) ",
                    // end inner Nat.rec on c
                    ") ",
                    // end outer Nat.rec on i; apply to c and h
                    "i) c h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "If sub c i = 0 then sub c (succ i) = 0. DerivedProved via double Nat.rec (outer on i, inner on c). Part of #464."
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
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_pos_witness: sub c i = 0 -> sub (succ i) c = succ (sub (sub (succ i) c) 1)
        //
        // If i >= c then (succ i) - c is positive (a successor). The conclusion
        // is the exact "positivity witness" shape expected by instantiate_bvar_at_above.
        //
        // Proof by Nat.rec on i (outer), with inner Nat.rec on c in the step case.
        //
        // Base i=0: inner Nat.rec on c.
        //   c=0: explicit Eq.trans chain via nat_sub_zero_right + nat_sub_succ_succ
        //     (elaborator can't reduce nested sub for Eq.refl).
        //   c=succ m: hypothesis gives succ m = 0 (via nat_sub_zero_right),
        //     which is absurd; Nat.rec discriminator trick proves the goal.
        //
        // Step i=succ j with IH (forall c, sub c j = 0 -> sub (succ j) c = succ ...):
        //   Inner Nat.rec on c:
        //     c=0: explicit Eq.trans chain via nat_sub_zero_right + nat_sub_succ_succ.
        //     c=succ m: nat_sub_succ_succ reduces hypothesis and both sides of goal,
        //       then outer IH closes.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_pos_witness".to_string(),
            type_src: concat!(
                "forall (c : Nat) (i : Nat), ",
                "Eq Nat (Nat.sub c i) Nat.zero -> ",
                "Eq Nat (Nat.sub (Nat.succ i) c) ",
                "(Nat.succ (Nat.sub (Nat.sub (Nat.succ i) c) (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (c : Nat) (i : Nat) ",
                    "(h : Eq Nat (Nat.sub c i) Nat.zero) => ",
                    // Outer Nat.rec on i, motive universalizes c
                    "(Nat.rec ",
                    "(fun (j : Nat) => forall (c : Nat), ",
                    "Eq Nat (Nat.sub c j) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.succ j) c) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ j) c) (Nat.succ Nat.zero)))) ",
                    // --- base i=0 ---
                    // Inner Nat.rec on c
                    "(fun (c : Nat) (h0 : Eq Nat (Nat.sub c Nat.zero) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (k : Nat) => ",
                    "Eq Nat (Nat.sub k Nat.zero) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.succ Nat.zero) k) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ Nat.zero) k) (Nat.succ Nat.zero)))) ",
                    // c=0: explicit chain (elaborator can't reduce nested sub)
                    // Goal: sub 1 0 = succ (sub (sub 1 0) 1)
                    // Chain: sub 1 0 =nat_sub_zero_right= 1 =Eq.symm(cong chain)= succ (sub (sub 1 0) 1)
                    "(fun (_ : Eq Nat (Nat.sub Nat.zero Nat.zero) Nat.zero) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ Nat.zero) Nat.zero) ",
                    "(Nat.succ Nat.zero) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ Nat.zero) Nat.zero) (Nat.succ Nat.zero))) ",
                    "(nat_sub_zero_right (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ Nat.zero) Nat.zero) (Nat.succ Nat.zero))) ",
                    "(Nat.succ Nat.zero) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ x) ",
                    "(Nat.sub (Nat.sub (Nat.succ Nat.zero) Nat.zero) (Nat.succ Nat.zero)) ",
                    "Nat.zero ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.sub (Nat.succ Nat.zero) Nat.zero) (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ Nat.zero)) ",
                    "Nat.zero ",
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.succ Nat.zero) Nat.zero) ",
                    "(Nat.succ Nat.zero) ",
                    "(nat_sub_zero_right (Nat.succ Nat.zero))) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ Nat.zero)) ",
                    "(Nat.sub Nat.zero Nat.zero) ",
                    "Nat.zero ",
                    "(nat_sub_succ_succ Nat.zero Nat.zero) ",
                    "(nat_sub_zero_right Nat.zero)))))) ",
                    // c=succ m: derive succ m = 0 from hypothesis, use Nat.rec discriminator
                    "(fun (m : Nat) ",
                    "(_ : Eq Nat (Nat.sub m Nat.zero) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.succ Nat.zero) m) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ Nat.zero) m) (Nat.succ Nat.zero)))) ",
                    "(h_sm : Eq Nat (Nat.sub (Nat.succ m) Nat.zero) Nat.zero) => ",
                    // Eq.symm (Eq.cong F absurd_h) where F(0)=LHS, F(succ m)=RHS
                    "Eq.symm Nat ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ Nat.zero) (Nat.succ m)) (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ m)) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) ",
                    "(Nat.sub (Nat.succ Nat.zero) (Nat.succ m)) ",
                    "(fun (_ : Nat) (_ : Nat) => ",
                    "Nat.succ (Nat.sub (Nat.sub (Nat.succ Nat.zero) (Nat.succ m)) (Nat.succ Nat.zero))) ",
                    "n) ",
                    "(Nat.succ m) Nat.zero ",
                    "(Eq.trans Nat (Nat.succ m) (Nat.sub (Nat.succ m) Nat.zero) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ m) Nat.zero) (Nat.succ m) ",
                    "(nat_sub_zero_right (Nat.succ m))) ",
                    "h_sm))) ",
                    "c h0) ",
                    // --- step i=succ j ---
                    "(fun (j : Nat) ",
                    "(ih : forall (c : Nat), ",
                    "Eq Nat (Nat.sub c j) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.succ j) c) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ j) c) (Nat.succ Nat.zero)))) => ",
                    // Inner Nat.rec on c
                    "Nat.rec ",
                    "(fun (k : Nat) => ",
                    "Eq Nat (Nat.sub k (Nat.succ j)) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.succ (Nat.succ j)) k) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ j)) k) (Nat.succ Nat.zero)))) ",
                    // c=0: explicit chain — elaborator can't reduce nested sub
                    // Goal: Eq Nat (sub ssj 0) (succ (sub (sub ssj 0) 1))
                    // Proof: trans (sub ssj 0 = ssj) (symm (succ(sub(sub ssj 0)(1)) = ssj))
                    "(fun (_ : Eq Nat (Nat.sub Nat.zero (Nat.succ j)) Nat.zero) => ",
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ (Nat.succ j)) Nat.zero) ",
                    "(Nat.succ (Nat.succ j)) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ j)) Nat.zero) (Nat.succ Nat.zero))) ",
                    // h1: sub(ssj, 0) = ssj
                    "(nat_sub_zero_right (Nat.succ (Nat.succ j))) ",
                    // h2: symm of chain reducing RHS to ssj
                    "(Eq.symm Nat ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ j)) Nat.zero) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.succ j)) ",
                    "(Eq.trans Nat ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ j)) Nat.zero) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.succ j)) ",
                    // cong: rewrite inner sub(ssj,0) -> ssj via nat_sub_zero_right
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ (Nat.sub x (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ (Nat.succ j)) Nat.zero) ",
                    "(Nat.succ (Nat.succ j)) ",
                    "(nat_sub_zero_right (Nat.succ (Nat.succ j)))) ",
                    // chain: succ(sub ssj 1) -> succ(sub sj 0) -> succ(sj) = ssj
                    "(Eq.trans Nat ",
                    "(Nat.succ (Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.succ j) Nat.zero)) ",
                    "(Nat.succ (Nat.succ j)) ",
                    "(Eq.cong Nat Nat Nat.succ ",
                    "(Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.succ j) Nat.zero) ",
                    "(nat_sub_succ_succ (Nat.succ j) Nat.zero)) ",
                    "(Eq.cong Nat Nat Nat.succ ",
                    "(Nat.sub (Nat.succ j) Nat.zero) ",
                    "(Nat.succ j) ",
                    "(nat_sub_zero_right (Nat.succ j))))))) ",
                    // c=succ m: use nat_sub_succ_succ + outer IH
                    "(fun (m : Nat) ",
                    "(_ : Eq Nat (Nat.sub m (Nat.succ j)) Nat.zero -> ",
                    "Eq Nat (Nat.sub (Nat.succ (Nat.succ j)) m) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ j)) m) (Nat.succ Nat.zero)))) ",
                    "(h_sm : Eq Nat (Nat.sub (Nat.succ m) (Nat.succ j)) Nat.zero) => ",
                    // Extract sub m j = 0 from hypothesis via nat_sub_succ_succ
                    // Apply outer IH at c=m to get: sub (succ j) m = succ (sub (sub (succ j) m) 1)
                    // Then chain with nat_sub_succ_succ on both LHS and RHS
                    "Eq.trans Nat ",
                    "(Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ m)) ",
                    "(Nat.sub (Nat.succ j) m) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ m)) (Nat.succ Nat.zero))) ",
                    "(nat_sub_succ_succ (Nat.succ j) m) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.succ j) m) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ j) m) (Nat.succ Nat.zero))) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ m)) (Nat.succ Nat.zero))) ",
                    // outer IH at c=m
                    "(ih m (Eq.trans Nat (Nat.sub m j) (Nat.sub (Nat.succ m) (Nat.succ j)) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ m) (Nat.succ j)) (Nat.sub m j) ",
                    "(nat_sub_succ_succ m j)) ",
                    "h_sm)) ",
                    // rewrite back: cong (fun x => succ (sub x 1)) with symm nat_sub_succ_succ
                    "(Eq.cong Nat Nat ",
                    "(fun (x : Nat) => Nat.succ (Nat.sub x (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ j) m) ",
                    "(Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ m)) ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ (Nat.succ j)) (Nat.succ m)) (Nat.sub (Nat.succ j) m) ",
                    "(nat_sub_succ_succ (Nat.succ j) m))))) ",
                    // end inner Nat.rec on c
                    ") ",
                    // end outer Nat.rec on i; apply to c and h
                    "i) c h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "If sub c i = 0 then sub (succ i) c is a successor. DerivedProved via double Nat.rec (outer on i, inner on c) + Nat.rec discriminator for vacuous base + explicit Eq.trans chains for c=0 branches (elaborator can't reduce nested sub). Part of #464."
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
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
