// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! App generation split from `type_preservation_generation.rs`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// typing_app_gen: Typing (App f a) T → CPS with (A, B, Typing f (Pi A B), Typing a A, ...).
    pub(super) fn add_typing_app_gen(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "typing_app_gen".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr) (T : KExpr) (R : Type), ",
                "Typing (KExpr.app f a) T -> ",
                "(forall (A : KExpr) (B : KExpr), ",
                "Typing f (KExpr.pi A B) -> Typing a A -> ",
                "DefEq T (instantiate B a) -> R) -> ",
                "R"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (a : KExpr) (T : KExpr) (R : Type) ",
                    "(h : Typing (KExpr.app f a) T) ",
                    "(k : forall (A : KExpr) (B : KExpr), ",
                    "Typing f (KExpr.pi A B) -> Typing a A -> DefEq T (instantiate B a) -> R) => ",
                    "Typing.rec ",
                    "(fun (e : KExpr) (T0 : KExpr) (_ : Typing e T0) => ",
                    "forall (f0 : KExpr) (a0 : KExpr), ",
                    "Eq KExpr e (KExpr.app f0 a0) -> ",
                    "(forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq T0 (instantiate B a0) -> R) -> R) ",
                    "(fun (n : Level) (f0 : KExpr) (a0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.sort n) (KExpr.app f0 a0)) ",
                    "(_ : forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq (KExpr.sort (Level.succ n)) (instantiate B a0) -> R) => ",
                    "sort_ne_app n f0 a0 R eq) ",
                    "(fun (A1 : KExpr) (B1 : KExpr) (_n1 : Level) (m1 : Level) ",
                    "(_hA : Typing A1 (KExpr.sort _n1)) (_hB : Typing B1 (KExpr.sort m1)) ",
                    "(_ihA : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr A1 (KExpr.app f0 a0) -> ",
                    "(forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq (KExpr.sort _n1) (instantiate B a0) -> R) -> R) ",
                    "(_ihB : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr B1 (KExpr.app f0 a0) -> ",
                    "(forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq (KExpr.sort m1) (instantiate B a0) -> R) -> R) ",
                    "(f0 : KExpr) (a0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.app f0 a0)) ",
                    "(_ : forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq (KExpr.sort (Level.imax _n1 m1)) (instantiate B a0) -> R) => ",
                    "pi_ne_app A1 B1 f0 a0 R eq) ",
                    "(fun (A2 : KExpr) (b2 : KExpr) (B2 : KExpr) (_u2 : Level) ",
                    "(_hA : Typing A2 (KExpr.sort _u2)) (_hb : Typing b2 B2) ",
                    "(_ihA : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr A2 (KExpr.app f0 a0) -> ",
                    "(forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq (KExpr.sort _u2) (instantiate B a0) -> R) -> R) ",
                    "(_ihb : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr b2 (KExpr.app f0 a0) -> ",
                    "(forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq B2 (instantiate B a0) -> R) -> R) ",
                    "(f0 : KExpr) (a0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.lam A2 b2) (KExpr.app f0 a0)) ",
                    "(_ : forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq (KExpr.pi A2 B2) (instantiate B a0) -> R) => ",
                    "lam_ne_app A2 b2 f0 a0 R eq) ",
                    "(fun (f1 : KExpr) (a1 : KExpr) (A2 : KExpr) (B2 : KExpr) ",
                    "(hf1 : Typing f1 (KExpr.pi A2 B2)) (ha1 : Typing a1 A2) ",
                    "(_ihf : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr f1 (KExpr.app f0 a0) -> ",
                    "(forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq (KExpr.pi A2 B2) (instantiate B a0) -> R) -> R) ",
                    "(_iha : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr a1 (KExpr.app f0 a0) -> ",
                    "(forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq A2 (instantiate B a0) -> R) -> R) ",
                    "(f0 : KExpr) (a0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.app f1 a1) (KExpr.app f0 a0)) ",
                    "(k0 : forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq (instantiate B2 a1) (instantiate B a0) -> R) => ",
                    "k0 A2 B2 ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.pi A2 B2)) f1 f0 ",
                    "(app_inj_fst f1 a1 f0 a0 eq) hf1) ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x A2) a1 a0 ",
                    "(app_inj_snd f1 a1 f0 a0 eq) ha1) ",
                    "(def_eq_eq_right (instantiate B2 a1) (instantiate B2 a1) (instantiate B2 a0) ",
                    "(DefEq.refl (instantiate B2 a1)) ",
                    "(Eq.cong KExpr KExpr (fun (x : KExpr) => instantiate B2 x) a1 a0 ",
                    "(app_inj_snd f1 a1 f0 a0 eq)))) ",
                    "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(_he : Typing e0 T1) (deq : DefEq T1 T2) ",
                    "(ih : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr e0 (KExpr.app f0 a0) -> ",
                    "(forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq T1 (instantiate B a0) -> R) -> R) ",
                    "(f0 : KExpr) (a0 : KExpr) ",
                    "(eq : Eq KExpr e0 (KExpr.app f0 a0)) ",
                    "(k0 : forall (A : KExpr) (B : KExpr), ",
                    "Typing f0 (KExpr.pi A B) -> Typing a0 A -> DefEq T2 (instantiate B a0) -> R) => ",
                    "ih f0 a0 eq ",
                    "(fun (A : KExpr) (B : KExpr) ",
                    "(hfAB : Typing f0 (KExpr.pi A B)) (haA : Typing a0 A) ",
                    "(deq_T1 : DefEq T1 (instantiate B a0)) => ",
                    "k0 A B hfAB haA ",
                    "(DefEq.trans T2 T1 (instantiate B a0) ",
                    "(DefEq.symm T1 T2 deq) deq_T1))) ",
                    "(KExpr.app f a) T h f a (Eq.refl KExpr (KExpr.app f a)) k"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "App generation lemma (CPS): if (App f a) : T, then ∃ A B with ",
                "f : Pi A B, a : A, and DefEq T (instantiate B a). ",
                "DerivedProved via Typing.rec + discrimination. ",
                "Part of #461, #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "typed_def_eq_to_def_eq".to_string(),
                "def_eq_eq_right".to_string(),
                "sort_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "lam_ne_app".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
