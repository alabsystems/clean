// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::spec::{AxiomCategory, SpecDefinition, Specification};
use crate::test_utils::build_spec_with_stack;
use crate::test_utils::run_with_stack;
use clean_kernel::Environment;
use std::collections::{HashMap, HashSet};

#[test]
fn test_arithmetic_lemmas_are_constructive() {
    let spec = build_spec_with_stack();
    for name in [
        "nat_sub_succ_succ",
        "nat_sub_self",
        "nat_sub_zero_right",
        "nat_sub_zero_left",
        "nat_add_succ_zero",
        "nat_add_zero_right",
        "nat_zero_add",
        "nat_add_comm",
        "nat_succ_add",
        "nat_sub_succ_one",
        "nat_sub_add_succ_zero_one",
        "nat_add_succ_zero_is_succ_pred",
        "nat_sub_zero_implies_sub_succ_zero",
        "nat_sub_pos_witness",
        "nat_sub_zero_add_same_right",
        "nat_sub_pos_add_same_right",
        "nat_sub_zero_succ_gap_to_add",
        "nat_add_succ_right",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("Missing definition {name}"));
        assert!(def.value_src.is_some(), "{name} should have a proof term");
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have no remaining helper blockers: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_nat_add_zero_right_elaborates_in_isolation() {
    run_with_stack(|| {
        let mut spec = Specification {
            env: Environment::new(),
            definitions: HashMap::new(),
            red_env_script_override: None,
        };

        spec.add_inductive(
            r"inductive Eq (α : Sort u) : α → α → Prop
| refl : forall (a : α), Eq α a a",
            "Parameterized equality",
        )
        .expect("Eq inductive should succeed");

        spec.add_inductive(
            r"inductive Nat : Type
| zero : Nat
| succ : Nat → Nat",
            "Natural numbers",
        )
        .expect("Nat inductive should succeed");

        spec.add_recursive_def(
            r"def Nat.add (n : Nat) (m : Nat) : Nat := match m with
| Nat.zero => n
| Nat.succ m' => Nat.succ (Nat.add n m')",
            "Addition on natural numbers.",
        )
        .expect("Nat.add should succeed");

        let result = spec.add_definition(SpecDefinition {
            name: "nat_add_zero_right".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.add n Nat.zero) n".to_string(),
            value_src: Some("fun (n : Nat) => Eq.refl Nat n".to_string()),
            is_axiom: false,
            description: "Nat.add n 0 = n. DerivedProved via Eq.refl on the concrete zero branch."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        });
        assert!(
            result.is_ok(),
            "nat_add_zero_right should elaborate in isolation: {:?}",
            result.err()
        );
    });
}

#[test]
fn test_nat_sub_zero_left_elaborates_in_isolation() {
    run_with_stack(|| {
        let mut spec = Specification {
            env: Environment::new(),
            definitions: HashMap::new(),
            red_env_script_override: None,
        };

        spec.add_inductive(
            r"inductive Eq (α : Sort u) : α → α → Prop
| refl : forall (a : α), Eq α a a",
            "Parameterized equality",
        )
        .expect("Eq inductive should succeed");

        for (name, type_src) in [
            (
                "Eq.cong",
                "forall (α : Sort u) (β : Sort v) (f : α -> β) (a : α) (b : α), Eq α a b -> Eq β (f a) (f b)",
            ),
            (
                "Eq.trans",
                "forall (α : Sort u) (a : α) (b : α) (c : α), Eq α a b -> Eq α b c -> Eq α a c",
            ),
        ] {
            spec.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: type_src.to_string(),
                value_src: None,
                is_axiom: true,
                description: name.to_string(),
                category: AxiomCategory::FoundationalRule,
                proof_status: ProofStatus::default(),
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            })
            .unwrap_or_else(|err| panic!("{name} should register: {err:?}"));
        }

        spec.add_inductive(
            r"inductive Nat : Type
| zero : Nat
| succ : Nat → Nat",
            "Natural numbers",
        )
        .expect("Nat inductive should succeed");

        spec.add_recursive_def(
            r"def Nat.pred (n : Nat) : Nat := Nat.rec (fun (_ : Nat) => Nat) Nat.zero (fun (m : Nat) (_ : Nat) => m) n",
            "Predecessor on natural numbers.",
        )
        .expect("Nat.pred should succeed");

        spec.add_recursive_def(
            r"def Nat.sub (a : Nat) (b : Nat) : Nat := match b with
| Nat.zero => a
| Nat.succ b' => Nat.pred (Nat.sub a b')",
            "Subtraction on natural numbers.",
        )
        .expect("Nat.sub should succeed");

        let result = spec.add_definition(SpecDefinition {
            name: "nat_sub_zero_left".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.sub Nat.zero n) Nat.zero".to_string(),
            value_src: Some(
                concat!(
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
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Nat.sub 0 n = 0.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: Some(Specification::nat_sub_zero_left_value_expr()),
            dependencies: None,
            axiom_deps: HashSet::new(),
        });
        assert!(
            result.is_ok(),
            "nat_sub_zero_left should elaborate in isolation: {:?}",
            result.err()
        );
    });
}

#[test]
fn test_nat_sub_succ_succ_elaborates_in_isolation() {
    run_with_stack(|| {
        let mut spec = Specification {
            env: Environment::new(),
            definitions: HashMap::new(),
            red_env_script_override: None,
        };

        spec.add_inductive(
            r"inductive Eq (α : Sort u) : α → α → Prop
| refl : forall (a : α), Eq α a a",
            "Parameterized equality",
        )
        .expect("Eq inductive should succeed");

        spec.add_definition(SpecDefinition {
            name: "Eq.cong".to_string(),
            type_src: "forall (α : Sort u) (β : Sort v) (f : α -> β) (a : α) (b : α), Eq α a b -> Eq β (f a) (f b)".to_string(),
            value_src: None,
            is_axiom: true,
            description: "Congruence: if a = b then f(a) = f(b).".to_string(),
            category: AxiomCategory::FoundationalRule,
            proof_status: ProofStatus::default(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })
        .expect("Eq.cong should register");

        spec.add_inductive(
            r"inductive Nat : Type
| zero : Nat
| succ : Nat → Nat",
            "Natural numbers",
        )
        .expect("Nat inductive should succeed");

        spec.add_recursive_def(
            r"def Nat.pred (n : Nat) : Nat := Nat.rec (fun (_ : Nat) => Nat) Nat.zero (fun (m : Nat) (_ : Nat) => m) n",
            "Predecessor on natural numbers.",
        )
        .expect("Nat.pred should succeed");

        spec.add_recursive_def(
            r"def Nat.sub (a : Nat) (b : Nat) : Nat := match b with
| Nat.zero => a
| Nat.succ b' => Nat.pred (Nat.sub a b')",
            "Subtraction on natural numbers.",
        )
        .expect("Nat.sub should succeed");

        let result = spec.add_definition(SpecDefinition {
            name: "nat_sub_succ_succ".to_string(),
            type_src:
                "forall (a : Nat) (b : Nat), Eq Nat (Nat.sub (Nat.succ a) (Nat.succ b)) (Nat.sub a b)"
                    .to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) => Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.sub (Nat.succ a) (Nat.succ k)) (Nat.sub a k)) ",
                "(Eq.refl Nat a) ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.sub (Nat.succ a) (Nat.succ k)) (Nat.sub a k)) => ",
                "Eq.cong Nat Nat Nat.pred ",
                "(Nat.sub (Nat.succ a) (Nat.succ k)) ",
                "(Nat.sub a k) ",
                "ih) ",
                "b",
            )
            .to_string()),
            is_axiom: false,
            description: "Nat.sub (succ a) (succ b) = Nat.sub a b.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: Some(Specification::nat_sub_succ_succ_value_expr()),
            dependencies: None,
            axiom_deps: HashSet::new(),
        });
        assert!(
            result.is_ok(),
            "nat_sub_succ_succ should elaborate in isolation: {:?}",
            result.err()
        );
    });
}
