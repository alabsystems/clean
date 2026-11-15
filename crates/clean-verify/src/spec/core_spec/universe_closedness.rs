// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural closedness prerequisites for universe-aware declaration types.
//!
//! These terms are ported from the exact-export Lean guides in
//! scratch/self-verification-{instl,psubst}-closed-2026-09-08.lean and checked
//! again against the live specification. They do not assert closedness of
//! admitted Rust declarations or correspondence with smart level substitution.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn closedness_theorem(
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
    /// Unchanged arithmetic proof moved from richmodel for early closedness.
    pub(super) fn add_closedness_arithmetic(&mut self) -> Result<(), SpecError> {
        // lt_to_le_succ: Lt a b -> Le (succ a) b. Lt.rec; zero_lt_succ =
        // le_succ_succ 0 n (le_zero_n n), succ_lt_succ = le_succ_succ (succ n) m ih.
        self.add_definition_structural(SpecDefinition {
            name: "lt_to_le_succ".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt a b -> Le (Nat.succ a) b".to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) (h : Lt a b) => ",
                "Lt.rec (fun (x : Nat) (y : Nat) (_ : Lt x y) => Le (Nat.succ x) y) ",
                "(fun (n : Nat) => le_succ_succ Nat.zero n (le_zero_n n)) ",
                "(fun (n : Nat) (m : Nat) (_hnm : Lt n m) (ih : Le (Nat.succ n) m) => le_succ_succ (Nat.succ n) m ih) ",
                "a b h",
            ).to_string()),
            is_axiom: false,
            description: "Lt a b -> Le (succ a) b. DerivedProved via Lt.rec (zero_lt_succ = le_succ_succ 0 n (le_zero_n n), succ = le_succ_succ). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(), "Lt.rec".to_string(), "Le".to_string(),
                "le_zero_n".to_string(), "le_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Only raw instL and is_closed_at: needed before polymorphic delta.
    pub(super) fn add_universe_closedness_syntax(&mut self) -> Result<(), SpecError> {
        closedness_theorem(
            self,
            "instL_preserves_closed_at",
            r"forall (s : Name -> Level) (e : KExpr) (d : Nat)
    (h : is_closed_at e d),
    is_closed_at (instL s e) d",
            r"fun (s : Name -> Level) (e : KExpr) (d : Nat)
    (h : is_closed_at e d) =>
  is_closed_at.rec
    (fun (e0 : KExpr) (d0 : Nat) (_h : is_closed_at e0 d0) =>
      is_closed_at (instL s e0) d0)
    (fun (u : Level) (d0 : Nat) => is_closed_at.sort (substL s u) d0)
    (fun (i : Nat) (d0 : Nat) (hlt : Lt i d0) => is_closed_at.bvar i d0 hlt)
    (fun (f : KExpr) (a : KExpr) (d0 : Nat)
      (_hf : is_closed_at f d0) (_ha : is_closed_at a d0)
      (ihf : is_closed_at (instL s f) d0)
      (iha : is_closed_at (instL s a) d0) =>
        is_closed_at.app (instL s f) (instL s a) d0 ihf iha)
    (fun (A : KExpr) (b : KExpr) (d0 : Nat)
      (_hA : is_closed_at A d0) (_hb : is_closed_at b (Nat.succ d0))
      (ihA : is_closed_at (instL s A) d0)
      (ihb : is_closed_at (instL s b) (Nat.succ d0)) =>
        is_closed_at.lam (instL s A) (instL s b) d0 ihA ihb)
    (fun (A : KExpr) (B : KExpr) (d0 : Nat)
      (_hA : is_closed_at A d0) (_hB : is_closed_at B (Nat.succ d0))
      (ihA : is_closed_at (instL s A) d0)
      (ihB : is_closed_at (instL s B) (Nat.succ d0)) =>
        is_closed_at.pi (instL s A) (instL s B) d0 ihA ihB)
    (fun (n : Name) (us : ListType Level) (d0 : Nat) =>
      is_closed_at.const n (mapLL (substL s) us) d0)
    (fun (A : KExpr) (v : KExpr) (b : KExpr) (d0 : Nat)
      (_hA : is_closed_at A d0) (_hv : is_closed_at v d0)
      (_hb : is_closed_at b (Nat.succ d0))
      (ihA : is_closed_at (instL s A) d0)
      (ihv : is_closed_at (instL s v) d0)
      (ihb : is_closed_at (instL s b) (Nat.succ d0)) =>
        is_closed_at.let_ (instL s A) (instL s v) (instL s b) d0 ihA ihv ihb)
    (fun (sn : Name) (i : Nat) (sub : KExpr) (d0 : Nat)
      (_hsub : is_closed_at sub d0) (ihsub : is_closed_at (instL s sub) d0) =>
        is_closed_at.proj sn i (instL s sub) d0 ihsub)
    (fun (n : Nat) (d0 : Nat) => is_closed_at.lit n d0)
    e d h",
            "Raw universe instantiation preserves de Bruijn closedness at every depth, by induction on the actual nine-constructor is_closed_at witness. No admission or Rust correspondence premise.",
        )?;

        closedness_theorem(
            self,
            "instL_preserves_top_level_closed",
            r"forall (s : Name -> Level) (e : KExpr)
    (h : is_closed_at e Nat.zero),
    is_closed_at (instL s e) Nat.zero",
            r"fun (s : Name -> Level) (e : KExpr)
    (h : is_closed_at e Nat.zero) =>
  instL_preserves_closed_at s e Nat.zero h",
            "Depth-zero specialization of instL_preserves_closed_at.",
        )?;

        Ok(())
    }

    /// Remaining parallel-substitution proofs need richmodel's upn_apply_lt.
    pub(super) fn add_universe_closedness(&mut self) -> Result<(), SpecError> {
        closedness_theorem(
            self,
            "psubst_closed_cong2",
            r"forall (c : KExpr -> KExpr -> KExpr) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
    (ha : Eq KExpr a a2) (hb : Eq KExpr b b2),
    Eq KExpr (c a b) (c a2 b2)",
            r"fun (c : KExpr -> KExpr -> KExpr) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
    (ha : Eq KExpr a a2) (hb : Eq KExpr b b2) =>
  Eq.trans KExpr (c a b) (c a2 b) (c a2 b2)
    (Eq.cong KExpr KExpr (fun (x : KExpr) => c x b) a a2 ha)
    (Eq.cong KExpr KExpr (fun (x : KExpr) => c a2 x) b b2 hb)",
            "Two-argument expression-constructor congruence, proved using Eq.cong and Eq.trans.",
        )?;

        closedness_theorem(
            self,
            "psubst_closed_cong3",
            r"forall (c : KExpr -> KExpr -> KExpr -> KExpr) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr) (d : KExpr) (d2 : KExpr)
    (ha : Eq KExpr a a2) (hb : Eq KExpr b b2) (hd : Eq KExpr d d2),
    Eq KExpr (c a b d) (c a2 b2 d2)",
            r"fun (c : KExpr -> KExpr -> KExpr -> KExpr) (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr) (d : KExpr) (d2 : KExpr)
    (ha : Eq KExpr a a2) (hb : Eq KExpr b b2) (hd : Eq KExpr d d2) =>
  Eq.trans KExpr (c a b d) (c a2 b2 d) (c a2 b2 d2)
    (psubst_closed_cong2 (fun (x : KExpr) (y : KExpr) => c x y d) a a2 b b2 ha hb)
    (Eq.cong KExpr KExpr (fun (x : KExpr) => c a2 b2 x) d d2 hd)",
            "Three-argument expression-constructor congruence, proved using checked equality congruence.",
        )?;

        closedness_theorem(
            self,
            "psubst_closed_upn_id",
            r"forall (e : KExpr) (depth : Nat) (h : is_closed_at e depth),
    forall (s : Nat -> KExpr), Eq KExpr (psubst (upn depth s) e) e",
            r"fun (e : KExpr) (depth : Nat) (h : is_closed_at e depth) =>
  is_closed_at.rec
    (fun (e0 : KExpr) (d : Nat) (_h : is_closed_at e0 d) =>
      forall (s : Nat -> KExpr), Eq KExpr (psubst (upn d s) e0) e0)
    (fun (u : Level) (_d : Nat) (_s : Nat -> KExpr) =>
      Eq.refl KExpr (KExpr.sort u))
    (fun (i : Nat) (d : Nat) (hlt : Lt i d) (s : Nat -> KExpr) =>
      upn_apply_lt d s i hlt)
    (fun (f : KExpr) (a : KExpr) (d : Nat)
      (_hf : is_closed_at f d) (_ha : is_closed_at a d)
      (ihf : forall (s : Nat -> KExpr), Eq KExpr (psubst (upn d s) f) f)
      (iha : forall (s : Nat -> KExpr), Eq KExpr (psubst (upn d s) a) a)
      (s : Nat -> KExpr) =>
        psubst_closed_cong2 KExpr.app
          (psubst (upn d s) f) f (psubst (upn d s) a) a (ihf s) (iha s))
    (fun (A : KExpr) (b : KExpr) (d : Nat)
      (_hA : is_closed_at A d) (_hb : is_closed_at b (Nat.succ d))
      (ihA : forall (s : Nat -> KExpr), Eq KExpr (psubst (upn d s) A) A)
      (ihb : forall (s : Nat -> KExpr),
        Eq KExpr (psubst (upn (Nat.succ d) s) b) b)
      (s : Nat -> KExpr) =>
        psubst_closed_cong2 KExpr.lam
          (psubst (upn d s) A) A (psubst (upn (Nat.succ d) s) b) b
          (ihA s) (ihb s))
    (fun (A : KExpr) (B : KExpr) (d : Nat)
      (_hA : is_closed_at A d) (_hB : is_closed_at B (Nat.succ d))
      (ihA : forall (s : Nat -> KExpr), Eq KExpr (psubst (upn d s) A) A)
      (ihB : forall (s : Nat -> KExpr),
        Eq KExpr (psubst (upn (Nat.succ d) s) B) B)
      (s : Nat -> KExpr) =>
        psubst_closed_cong2 KExpr.pi
          (psubst (upn d s) A) A (psubst (upn (Nat.succ d) s) B) B
          (ihA s) (ihB s))
    (fun (n : Name) (us : ListType Level) (_d : Nat) (_s : Nat -> KExpr) =>
      Eq.refl KExpr (KExpr.const n us))
    (fun (A : KExpr) (v : KExpr) (b : KExpr) (d : Nat)
      (_hA : is_closed_at A d) (_hv : is_closed_at v d)
      (_hb : is_closed_at b (Nat.succ d))
      (ihA : forall (s : Nat -> KExpr), Eq KExpr (psubst (upn d s) A) A)
      (ihv : forall (s : Nat -> KExpr), Eq KExpr (psubst (upn d s) v) v)
      (ihb : forall (s : Nat -> KExpr),
        Eq KExpr (psubst (upn (Nat.succ d) s) b) b)
      (s : Nat -> KExpr) =>
        psubst_closed_cong3 KExpr.let_
          (psubst (upn d s) A) A (psubst (upn d s) v) v
          (psubst (upn (Nat.succ d) s) b) b (ihA s) (ihv s) (ihb s))
    (fun (sn : Name) (i : Nat) (sub : KExpr) (d : Nat)
      (_hsub : is_closed_at sub d)
      (ihsub : forall (s : Nat -> KExpr), Eq KExpr (psubst (upn d s) sub) sub)
      (s : Nat -> KExpr) =>
        Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj sn i x)
          (psubst (upn d s) sub) sub (ihsub s))
    (fun (n : Nat) (_d : Nat) (_s : Nat -> KExpr) =>
      Eq.refl KExpr (KExpr.lit n))
    e depth h",
            "Parallel substitution lifted under the closedness depth is identity; the bound-variable case reuses upn_apply_lt and binder cases increment depth.",
        )?;

        closedness_theorem(
            self,
            "psubst_closed_id",
            r"forall (s : Nat -> KExpr) (A : KExpr) (h : is_closed_at A Nat.zero),
    Eq KExpr (psubst s A) A",
            r"fun (s : Nat -> KExpr) (A : KExpr) (h : is_closed_at A Nat.zero) =>
  psubst_closed_upn_id A Nat.zero h s",
            "Any parallel substitution is identity on a de Bruijn-closed expression. A structural model theorem, not a declaration-admission assertion.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::closedness_theorem;
    use crate::spec::core_spec::bundles::build_universe_closedness_prefix;
    use crate::spec::types::ProofStatus;
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;

    #[test]
    fn registered_universe_closedness_terms_are_axiom_free_and_keep_their_premise() {
        run_with_stack(|| {
            let mut spec = Specification::new_empty();
            build_universe_closedness_prefix(&mut spec)
                .expect("actual reordered stage prefix must kernel-check");

            for name in [
                "instL_preserves_closed_at",
                "instL_preserves_top_level_closed",
                "psubst_closed_cong2",
                "psubst_closed_cong3",
                "psubst_closed_upn_id",
                "psubst_closed_id",
            ] {
                let def = spec.definitions().get(name).expect("registered theorem");
                assert!(!def.is_axiom, "{name} must carry a proof");
                assert_eq!(def.proof_status, ProofStatus::DerivedProved);
                assert!(def.elaborated_value.is_some(), "{name} must be elaborated");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name} must have no transitive axiom dependency"
                );
            }

            let closed_binder = concat!(
                "is_closed_at.lam (KExpr.sort (Level.param u)) ",
                "(KExpr.bvar Nat.zero) Nat.zero ",
                "(is_closed_at.sort (Level.param u) Nat.zero) ",
                "(is_closed_at.bvar Nat.zero (Nat.succ Nat.zero) ",
                "(Lt.zero_lt_succ Nat.zero))"
            );
            let binder = "KExpr.lam (KExpr.sort (Level.param u)) (KExpr.bvar Nat.zero)";
            closedness_theorem(
                &mut spec,
                "instL_closed_binder_regression",
                &format!("forall (s : Name -> Level) (u : Name), is_closed_at (instL s ({binder})) Nat.zero"),
                &format!("fun (s : Name -> Level) (u : Name) => instL_preserves_closed_at s ({binder}) Nat.zero ({closed_binder})"),
                "Regression: level substitution preserves a closed lambda whose body needs successor depth.",
            )
            .expect("instL binder witness");
            closedness_theorem(
                &mut spec,
                "psubst_closed_binder_regression",
                &format!("forall (s : Nat -> KExpr) (u : Name), Eq KExpr (psubst s ({binder})) ({binder})"),
                &format!("fun (s : Nat -> KExpr) (u : Name) => psubst_closed_id s ({binder}) ({closed_binder})"),
                "Regression: arbitrary parallel substitution fixes a closed lambda, not merely inert leaves.",
            )
            .expect("parallel-substitution binder witness");

            for name in [
                "instL_closed_binder_regression",
                "psubst_closed_binder_regression",
            ] {
                assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
            }

            assert!(
                closedness_theorem(
                    &mut spec,
                    "psubst_open_identity_must_fail",
                    "Eq KExpr (psubst (fun (_ : Nat) => KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)",
                    "Eq.refl KExpr (KExpr.bvar Nat.zero)",
                    "Negative control: substitution does change an open bound-variable expression.",
                )
                .is_err(),
                "closedness cannot be dropped from the identity theorem"
            );
            assert!(
                closedness_theorem(
                    &mut spec,
                    "closedness_zero_depth_must_fail",
                    "is_closed_at (KExpr.bvar Nat.zero) Nat.zero",
                    "is_closed_at.bvar Nat.zero Nat.zero (Lt.zero_lt_succ Nat.zero)",
                    "Negative control: the successor-depth witness is not valid at depth zero.",
                )
                .is_err(),
                "a dangling bound variable cannot supply the missing premise"
            );
        });
    }
}
