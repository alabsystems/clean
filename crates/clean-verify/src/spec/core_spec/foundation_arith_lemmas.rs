// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Derived arithmetic lemmas for Nat (split from foundation_types.rs)
//!
//! Building blocks for lift_cancel_gen and the broader trust cut path.
//! All lemmas here are DerivedProved with empty axiom_deps.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_foundation_arith_lemmas(&mut self) -> Result<(), SpecError> {
        // nat_sub_zero_right: n - 0 = n
        // Definitionally true: Nat.sub n 0 matches on Nat.zero, returning n.
        // Single iota on concrete constructor, so Eq.refl type-checks directly.
        // Part of #461.
        self.add_definition(SpecDefinition {
            name: "nat_sub_zero_right".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.sub n Nat.zero) n".to_string(),
            value_src: Some("fun (n : Nat) => Eq.refl Nat n".to_string()),
            is_axiom: false,
            description: "Nat.sub n 0 = n. DerivedProved via Eq.refl (single iota on concrete zero). Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_zero_left: 0 - n = 0
        // Requires Nat.rec on n since the first match in Nat.sub dispatches on b (= n).
        // Base (n=0): Nat.sub 0 0 = 0 by Eq.refl.
        // Step (n=succ k): Nat.sub 0 (succ k) = Nat.pred (Nat.sub 0 k).
        //   Transport the induction hypothesis through Nat.pred, then close
        //   Nat.pred 0 = 0 by the concrete zero branch.
        // Part of #461.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_zero_left".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.sub Nat.zero n) Nat.zero".to_string(),
            value_src: Some(concat!(
                "fun (n : Nat) => Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.sub Nat.zero k) Nat.zero) ",
                "(Eq.refl Nat Nat.zero) ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.sub Nat.zero k) Nat.zero) => ",
                "Eq.trans Nat ",
                "(Nat.sub Nat.zero (Nat.succ k)) ",
                "(Nat.pred Nat.zero) ",
                "Nat.zero ",
                "(Eq.cong Nat Nat Nat.pred (Nat.sub Nat.zero k) Nat.zero ih) ",
                "(Eq.refl Nat Nat.zero)) ",
                "n",
            ).to_string()),
            is_axiom: false,
            description: "Nat.sub 0 n = 0 for all n. DerivedProved via Nat.rec and Nat.pred congruence. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: Some(Self::nat_sub_zero_left_value_expr()),
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Nat.pred".to_string(),
                "Eq.refl".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_add_succ_zero: n + 1 = succ n
        // Definitionally true via two iota reductions:
        //   Nat.add n (succ 0) → succ (Nat.add n 0) → succ n
        // Both matches are on concrete constructors (succ, zero), but the kernel
        // cannot reduce nested iota, so structural registration is needed.
        // Part of #461.
        self.add_definition_structural(SpecDefinition {
            name: "nat_add_succ_zero".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.add n (Nat.succ Nat.zero)) (Nat.succ n)"
                .to_string(),
            value_src: Some(
                "fun (n : Nat) => Eq.refl Nat (Nat.succ n)".to_string(),
            ),
            is_axiom: false,
            description: "Nat.add n 1 = Nat.succ n. DerivedProved via Eq.refl + structural registration (nested iota on concrete succ/zero). Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // nat_add_zero_right: n + 0 = n
        // Definitionally true because Nat.add recurses on the second argument,
        // and the rhs is the concrete constructor Nat.zero. Part of #464.
        self.add_definition(SpecDefinition {
            name: "nat_add_zero_right".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.add n Nat.zero) n".to_string(),
            value_src: Some("fun (n : Nat) => Eq.refl Nat n".to_string()),
            is_axiom: false,
            description:
                "Nat.add n 0 = n. DerivedProved via Eq.refl on the concrete zero branch. Part of #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // nat_zero_add: 0 + n = n
        // Since Nat.add recurses on the second argument, induction on n aligns
        // the step case definitionally: add 0 (succ k) = succ (add 0 k). Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_zero_add".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.add Nat.zero n) n".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) => Nat.rec ",
                    "(fun (k : Nat) => Eq Nat (Nat.add Nat.zero k) k) ",
                    "(Eq.refl Nat Nat.zero) ",
                    "(fun (k : Nat) (ih : Eq Nat (Nat.add Nat.zero k) k) => ",
                    "Eq.cong Nat Nat Nat.succ ",
                    "(Nat.add Nat.zero k) ",
                    "k ",
                    "ih) ",
                    "n",
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Nat.add 0 n = n. DerivedProved via Nat.rec on the second addend. Part of #464."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_succ_add: (succ n) + m = succ (n + m)
        // Since Nat.add recurses on the second argument, this needs induction on
        // m. Base case is definitional. The step case is just congruence by succ
        // on the IH after both sides iota-reduce. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_succ_add".to_string(),
            type_src: "forall (n : Nat) (m : Nat), Eq Nat (Nat.add (Nat.succ n) m) (Nat.succ (Nat.add n m))"
                .to_string(),
            value_src: Some(concat!(
                "fun (n : Nat) (m : Nat) => Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.add (Nat.succ n) k) (Nat.succ (Nat.add n k))) ",
                "(Eq.refl Nat (Nat.succ n)) ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.add (Nat.succ n) k) (Nat.succ (Nat.add n k))) => ",
                "Eq.cong Nat Nat Nat.succ ",
                "(Nat.add (Nat.succ n) k) ",
                "(Nat.succ (Nat.add n k)) ",
                "ih) ",
                "m",
            ).to_string()),
            is_axiom: false,
            description: "(succ n) + m = succ (n + m). DerivedProved via Nat.rec on the second addend. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_add_comm: a + b = b + a
        // Induction on b. The step case rewrites the left via the defining iota
        // add a (succ k) = succ (add a k), applies congruence over the IH, then
        // rewrites the right via nat_succ_add. Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_add_comm".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Eq Nat (Nat.add a b) (Nat.add b a)"
                .to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) => Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.add a k) (Nat.add k a)) ",
                "(Eq.trans Nat ",
                "(Nat.add a Nat.zero) ",
                "a ",
                "(Nat.add Nat.zero a) ",
                "(Eq.refl Nat a) ",
                "(Eq.symm Nat (Nat.add Nat.zero a) a (nat_zero_add a))) ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.add a k) (Nat.add k a)) => ",
                "Eq.trans Nat ",
                "(Nat.add a (Nat.succ k)) ",
                "(Nat.succ (Nat.add a k)) ",
                "(Nat.add (Nat.succ k) a) ",
                "(Eq.refl Nat (Nat.succ (Nat.add a k))) ",
                "(Eq.trans Nat ",
                "(Nat.succ (Nat.add a k)) ",
                "(Nat.succ (Nat.add k a)) ",
                "(Nat.add (Nat.succ k) a) ",
                "(Eq.cong Nat Nat Nat.succ ",
                "(Nat.add a k) ",
                "(Nat.add k a) ",
                "ih) ",
                "(Eq.symm Nat ",
                "(Nat.add (Nat.succ k) a) ",
                "(Nat.succ (Nat.add k a)) ",
                "(nat_succ_add k a)))) ",
                "b",
            ).to_string()),
            is_axiom: false,
            description: "Nat.add a b = Nat.add b a. DerivedProved via Nat.rec on the second addend. Part of #464.".to_string(),
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
                "nat_succ_add".to_string(),
                "nat_zero_add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_succ_one: (succ n) - 1 = n
        // Definitionally true: Nat.sub (succ n) (succ 0) → Nat.sub n 0 → n.
        // Chain of nat_sub_succ_succ + nat_sub_zero_right, or direct Eq.refl
        // via structural registration (three nested iotas on concrete constructors).
        // Part of #461.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_succ_one".to_string(),
            type_src:
                "forall (n : Nat), Eq Nat (Nat.sub (Nat.succ n) (Nat.succ Nat.zero)) n"
                    .to_string(),
            value_src: Some("fun (n : Nat) => Eq.refl Nat n".to_string()),
            is_axiom: false,
            description: "Nat.sub (succ n) 1 = n. DerivedProved via Eq.refl + structural registration (chain of succ_succ + zero_right iotas). Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_add_succ_zero_one: (n + 1) - 1 = n
        // Direct composite of nat_add_succ_zero and nat_sub_succ_one.
        // This is the concrete predecessor equality used by the lift_cancel_gen
        // bvar-above branch after re-expressing the shifted index as n + 1.
        // Part of #464.
        self.add_definition(SpecDefinition {
            name: "nat_sub_add_succ_zero_one".to_string(),
            type_src:
                "forall (n : Nat), Eq Nat (Nat.sub (Nat.add n (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) n"
                    .to_string(),
            value_src: Some(concat!(
                "fun (n : Nat) => Eq.trans Nat ",
                "(Nat.sub (Nat.add n (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) ",
                "(Nat.sub (Nat.succ n) (Nat.succ Nat.zero)) ",
                "n ",
                "(Eq.cong Nat Nat ",
                "(fun (x : Nat) => Nat.sub x (Nat.succ Nat.zero)) ",
                "(Nat.add n (Nat.succ Nat.zero)) ",
                "(Nat.succ n) ",
                "(nat_add_succ_zero n)) ",
                "(nat_sub_succ_one n)",
            ).to_string()),
            is_axiom: false,
            description: "(n + 1) - 1 = n. DerivedProved via nat_add_succ_zero + nat_sub_succ_one. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "nat_add_succ_zero".to_string(),
                "nat_sub_succ_one".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_add_succ_zero_is_succ_pred: n + 1 = succ ((n + 1) - 1)
        // Packages the previous predecessor equality into the exact shape used by
        // the instantiate_bvar_at_above witness when the shifted index is n + 1.
        // Part of #464.
        self.add_definition(SpecDefinition {
            name: "nat_add_succ_zero_is_succ_pred".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.add n (Nat.succ Nat.zero)) (Nat.succ (Nat.sub (Nat.add n (Nat.succ Nat.zero)) (Nat.succ Nat.zero)))".to_string(),
            value_src: Some(concat!(
                "fun (n : Nat) => Eq.trans Nat ",
                "(Nat.add n (Nat.succ Nat.zero)) ",
                "(Nat.succ n) ",
                "(Nat.succ (Nat.sub (Nat.add n (Nat.succ Nat.zero)) (Nat.succ Nat.zero))) ",
                "(nat_add_succ_zero n) ",
                "(Eq.cong Nat Nat Nat.succ ",
                "n ",
                "(Nat.sub (Nat.add n (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) ",
                "(Eq.symm Nat ",
                "(Nat.sub (Nat.add n (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) ",
                "n ",
                "(nat_sub_add_succ_zero_one n)))",
            ).to_string()),
            is_axiom: false,
            description: "n + 1 = succ ((n + 1) - 1). DerivedProved via nat_add_succ_zero and nat_sub_add_succ_zero_one. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "nat_add_succ_zero".to_string(),
                "nat_sub_add_succ_zero_one".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_add_succ_right: j + succ(n) = succ(j + n)
        // Definitionally true via the defining iota of Nat.add on the second
        // argument: Nat.add j (succ n) matches succ → succ (Nat.add j n).
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_add_succ_right".to_string(),
            type_src:
                "forall (j : Nat) (n : Nat), Eq Nat (Nat.add j (Nat.succ n)) (Nat.succ (Nat.add j n))"
                    .to_string(),
            value_src: Some(
                "fun (j : Nat) (n : Nat) => Eq.refl Nat (Nat.succ (Nat.add j n))".to_string(),
            ),
            is_axiom: false,
            description: "j + succ(n) = succ(j + n). Definitionally true via the defining iota of Nat.add. DerivedProved via Eq.refl + structural registration. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "foundation_arith_lemmas_tests.rs"]
mod foundation_arith_lemmas_tests;
