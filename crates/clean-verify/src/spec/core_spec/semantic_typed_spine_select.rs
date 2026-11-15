// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recover actual argument typing from the existing typed raw Pi-spine.
//!
//! Seven model proof records, with declaration binders mechanically desugared
//! into explicit forall/fun records. The general CPS result recovers the actual
//! selected argument's typing and the computed preceding raw telescope; it
//! assumes neither a wanted field typing nor a wanted output conversion.
//! C : Type remains fixed outside the trace induction. The whole-constant
//! wrapper derives its trace through the existing guarded-lookup/whole-typing
//! theorem; only that wrapper needs RedEnvFaithful.
//!
//! The dependent identity is an existing inhabited model telescope, not a new
//! source projection witness. The two reflected Prod callers consume the
//! existing metadata-connected constructor package. These are typings of actual
//! arguments, not projection beta, dependent projection-domain conversion,
//! uniform constructor-return validity, domain formation, or Rust refinement.
//!
//! Independent prototype provenance: target-quality/typed-spine-select.drh4PU/README.md.
//! Registered after projection metadata, with executable registration and refusal tests.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str, &str)] = &[
    (
        "typed_raw_pi_spine_select",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U) (C : Type), forall (k : Nat) (a : KExpr),
 Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a) ->
 (forall (A B : KExpr),
  Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
   (OptionType.some KExpr (KExpr.pi A B)) ->
  TypingCtxConvIn R tenv G a A -> C) -> C",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U) (C : Type) => TypedRawPiSpine.rec R tenv G
  (fun (F0 : KExpr) (xs : ListType KExpr) (V : KExpr)
   (_tr : TypedRawPiSpine R tenv G F0 xs V) =>
   forall (k : Nat) (a : KExpr),
   Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr a) ->
   (forall (A B : KExpr),
    Eq (OptionType KExpr) (raw_pi_spine (list_take k xs) F0)
     (OptionType.some KExpr (KExpr.pi A B)) ->
    TypingCtxConvIn R tenv G a A -> C) -> C)
  (fun (F0 : KExpr) (k : Nat) (a : KExpr)
   (selected : Eq (OptionType KExpr)
    (list_head (list_drop k (ListType.nil KExpr))) (OptionType.some KExpr a))
   (_consume : forall (A B : KExpr),
    Eq (OptionType KExpr) (raw_pi_spine (list_take k (ListType.nil KExpr)) F0)
     (OptionType.some KExpr (KExpr.pi A B)) ->
    TypingCtxConvIn R tenv G a A -> C) =>
   option_none_ne_some_type KExpr a C
    (Eq.trans (OptionType KExpr) (OptionType.none KExpr)
     (list_head (list_drop k (ListType.nil KExpr))) (OptionType.some KExpr a)
     (Eq.symm (OptionType KExpr)
      (list_head (list_drop k (ListType.nil KExpr))) (OptionType.none KExpr)
      (Eq.cong (ListType KExpr) (OptionType KExpr)
       (fun (xs : ListType KExpr) => list_head xs)
       (list_drop k (ListType.nil KExpr)) (ListType.nil KExpr) (list_drop_nil k)))
     selected))
  (fun (A B x : KExpr) (xs : ListType KExpr) (V : KExpr)
   (hx : TypingCtxConvIn R tenv G x A)
   (_tail : TypedRawPiSpine R tenv G (instantiate B x) xs V)
   (ih : forall (k : Nat) (a : KExpr),
    Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr a) ->
    (forall (A1 B1 : KExpr),
     Eq (OptionType KExpr) (raw_pi_spine (list_take k xs) (instantiate B x))
      (OptionType.some KExpr (KExpr.pi A1 B1)) ->
     TypingCtxConvIn R tenv G a A1 -> C) -> C) =>
   Nat.rec
    (fun (k : Nat) => forall (a : KExpr),
     Eq (OptionType KExpr) (list_head (list_drop k (ListType.cons KExpr x xs)))
      (OptionType.some KExpr a) ->
     (forall (A1 B1 : KExpr),
      Eq (OptionType KExpr)
       (raw_pi_spine (list_take k (ListType.cons KExpr x xs)) (KExpr.pi A B))
       (OptionType.some KExpr (KExpr.pi A1 B1)) ->
      TypingCtxConvIn R tenv G a A1 -> C) -> C)
    (fun (a : KExpr)
     (selected : Eq (OptionType KExpr) (OptionType.some KExpr x) (OptionType.some KExpr a))
     (consume : forall (A1 B1 : KExpr),
      Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.pi A B))
       (OptionType.some KExpr (KExpr.pi A1 B1)) ->
      TypingCtxConvIn R tenv G a A1 -> C) =>
     consume A B (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi A B)))
      (Eq.substType KExpr (fun (z : KExpr) => TypingCtxConvIn R tenv G z A)
       x a (option_some_inj KExpr x a selected) hx))
    (fun (k : Nat) (_index_ih : forall (a : KExpr),
     Eq (OptionType KExpr) (list_head (list_drop k (ListType.cons KExpr x xs)))
      (OptionType.some KExpr a) ->
     (forall (A1 B1 : KExpr),
      Eq (OptionType KExpr)
       (raw_pi_spine (list_take k (ListType.cons KExpr x xs)) (KExpr.pi A B))
       (OptionType.some KExpr (KExpr.pi A1 B1)) ->
      TypingCtxConvIn R tenv G a A1 -> C) -> C)
     (a : KExpr)
     (selected : Eq (OptionType KExpr) (list_head (list_drop k xs))
      (OptionType.some KExpr a))
     (consume : forall (A1 B1 : KExpr),
      Eq (OptionType KExpr) (raw_pi_spine (list_take k xs) (instantiate B x))
       (OptionType.some KExpr (KExpr.pi A1 B1)) ->
      TypingCtxConvIn R tenv G a A1 -> C) => ih k a selected consume))
  F args U trace",
    ),
    (
        "typed_raw_pi_spine_select_at",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U) (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))), TypingCtxConvIn R tenv G a A",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U) (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))) => typed_raw_pi_spine_select R tenv G F args U trace (TypingCtxConvIn R tenv G a A) k a selected
  (fun (A1 B1 : KExpr)
   (actual : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
    (OptionType.some KExpr (KExpr.pi A1 B1)))
   (typed : TypingCtxConvIn R tenv G a A1) =>
   Eq.substType KExpr (fun (D : KExpr) => TypingCtxConvIn R tenv G a D) A1 A
    (kexpr_pi_inj_fst A1 B1 A B
     (option_some_inj KExpr (KExpr.pi A1 B1) (KExpr.pi A B)
      (Eq.trans (OptionType KExpr) (OptionType.some KExpr (KExpr.pi A1 B1))
       (raw_pi_spine (list_take k args) F) (OptionType.some KExpr (KExpr.pi A B))
       (Eq.symm (OptionType KExpr) (raw_pi_spine (list_take k args) F)
        (OptionType.some KExpr (KExpr.pi A1 B1)) actual) prefix_run))) typed)",
    ),
    (
        "semantic_typed_spine_select_at",
        r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (h F : KExpr) (args : ListType KExpr) (U T : KExpr)
 (package : SemanticTypedSpineReturn R tenv G h F args U T) (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))), TypingCtxConvIn R tenv G a A",
        r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (h F : KExpr) (args : ListType KExpr) (U T : KExpr)
 (package : SemanticTypedSpineReturn R tenv G h F args U T) (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))) => SemanticTypedSpineReturn.rec R tenv G h F args U T
  (fun (_p : SemanticTypedSpineReturn R tenv G h F args U T) => TypingCtxConvIn R tenv G a A)
  (fun (_head : TypingCtxConvIn R tenv G h F)
   (trace : TypedRawPiSpine R tenv G F args U) (_convert : DefEqIn R U T) =>
   typed_raw_pi_spine_select_at R tenv G F args U trace k a A B selected prefix_run) package",
    ),
    (
        "typingctxconv_in_const_spine_select_at",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T)
 (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))), TypingCtxConvIn R tenv G a A",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T)
 (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))) => semantic_typed_spine_select_at R tenv G (KExpr.const n us) F args U T
  (typingctxconv_in_const_spine R faithful tenv G n us F args U T lookup run typed)
  k a A B selected prefix_run",
    ),
    (
        "typed_spine_identity_selected_argument",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr), TypingCtxConvIn R typed_spine_identity_tenv G
 (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr) => typingctxconv_in_const_spine_select_at R faithful typed_spine_identity_tenv G
  Name.anonymous (ListType.nil Level) (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
  typed_spine_identity_args (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  typed_spine_identity_lookup typed_spine_identity_run (typed_raw_pi_spine_identity_const_apply R G)
  (Nat.succ Nat.zero) (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))
  (KExpr.sort (Level.succ Level.zero))
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero)))
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr
   (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero)))))",
    ),
    (
        "projection_prod_selected_zero_argument",
        r"TypingCtxConvIn the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr) rfnz_zero rfnz_nat",
        r"semantic_typed_spine_select_at the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr)
  projection_prod_ctor (projection_meta_ctor_type projection_prod_result) projection_prod_args
  kcre_witness_prod_type kcre_witness_prod_type projection_prod_typed_constructor_spine
  (Nat.succ (Nat.succ Nat.zero)) rfnz_zero rfnz_nat (KExpr.pi rfnz_nat kcre_witness_prod_type)
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr rfnz_zero))
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr projection_prod_field_telescope))",
    ),
    (
        "projection_prod_selected_succ_argument",
        r"TypingCtxConvIn the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr) (KExpr.app rfnz_succ rfnz_zero) rfnz_nat",
        r"semantic_typed_spine_select_at the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr)
  projection_prod_ctor (projection_meta_ctor_type projection_prod_result) projection_prod_args
  kcre_witness_prod_type kcre_witness_prod_type projection_prod_typed_constructor_spine
  (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ rfnz_zero) rfnz_nat kcre_witness_prod_type
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero)))
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi rfnz_nat kcre_witness_prod_type)))",
    ),
];

const PROOF_ROOTS: &[&str] = &[
    "typed_raw_pi_spine_select",
    "typed_raw_pi_spine_select_at",
    "semantic_typed_spine_select_at",
    "typingctxconv_in_const_spine_select_at",
    "typed_spine_identity_selected_argument",
    "projection_prod_selected_zero_argument",
    "projection_prod_selected_succ_argument",
];

impl Specification {
    /// Register after projection_metadata: the two final callers consume its
    /// actual typed constructor package; the generic roots reuse typed spines.
    pub(super) fn add_semantic_typed_spine_select(&mut self) -> Result<(), SpecError> {
        debug_assert_eq!(PROOF_ROOTS.len(), PROOFS.len());
        for &(name, ty, body) in PROOFS {
            theorem(
                self,
                name,
                ty,
                body,
                "Actual raw-spine argument selection, derived through the existing typed trace; no desired field typing or projection conversion premise.",
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{theorem, PROOFS, PROOF_ROOTS};
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};
    use clean_kernel::{ConstantKind, ExprKind, Name, TypeChecker};

    // Exact original independently checked declaration strings.
    const PROTOTYPES: &[&str] = &[
        r"def typed_raw_pi_spine_select (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U) (C : Type) :
 forall (k : Nat) (a : KExpr),
 Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a) ->
 (forall (A B : KExpr),
  Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
   (OptionType.some KExpr (KExpr.pi A B)) ->
  TypingCtxConvIn R tenv G a A -> C) -> C :=
 TypedRawPiSpine.rec R tenv G
  (fun (F0 : KExpr) (xs : ListType KExpr) (V : KExpr)
   (_tr : TypedRawPiSpine R tenv G F0 xs V) =>
   forall (k : Nat) (a : KExpr),
   Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr a) ->
   (forall (A B : KExpr),
    Eq (OptionType KExpr) (raw_pi_spine (list_take k xs) F0)
     (OptionType.some KExpr (KExpr.pi A B)) ->
    TypingCtxConvIn R tenv G a A -> C) -> C)
  (fun (F0 : KExpr) (k : Nat) (a : KExpr)
   (selected : Eq (OptionType KExpr)
    (list_head (list_drop k (ListType.nil KExpr))) (OptionType.some KExpr a))
   (_consume : forall (A B : KExpr),
    Eq (OptionType KExpr) (raw_pi_spine (list_take k (ListType.nil KExpr)) F0)
     (OptionType.some KExpr (KExpr.pi A B)) ->
    TypingCtxConvIn R tenv G a A -> C) =>
   option_none_ne_some_type KExpr a C
    (Eq.trans (OptionType KExpr) (OptionType.none KExpr)
     (list_head (list_drop k (ListType.nil KExpr))) (OptionType.some KExpr a)
     (Eq.symm (OptionType KExpr)
      (list_head (list_drop k (ListType.nil KExpr))) (OptionType.none KExpr)
      (Eq.cong (ListType KExpr) (OptionType KExpr)
       (fun (xs : ListType KExpr) => list_head xs)
       (list_drop k (ListType.nil KExpr)) (ListType.nil KExpr) (list_drop_nil k)))
     selected))
  (fun (A B x : KExpr) (xs : ListType KExpr) (V : KExpr)
   (hx : TypingCtxConvIn R tenv G x A)
   (_tail : TypedRawPiSpine R tenv G (instantiate B x) xs V)
   (ih : forall (k : Nat) (a : KExpr),
    Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr a) ->
    (forall (A1 B1 : KExpr),
     Eq (OptionType KExpr) (raw_pi_spine (list_take k xs) (instantiate B x))
      (OptionType.some KExpr (KExpr.pi A1 B1)) ->
     TypingCtxConvIn R tenv G a A1 -> C) -> C) =>
   Nat.rec
    (fun (k : Nat) => forall (a : KExpr),
     Eq (OptionType KExpr) (list_head (list_drop k (ListType.cons KExpr x xs)))
      (OptionType.some KExpr a) ->
     (forall (A1 B1 : KExpr),
      Eq (OptionType KExpr)
       (raw_pi_spine (list_take k (ListType.cons KExpr x xs)) (KExpr.pi A B))
       (OptionType.some KExpr (KExpr.pi A1 B1)) ->
      TypingCtxConvIn R tenv G a A1 -> C) -> C)
    (fun (a : KExpr)
     (selected : Eq (OptionType KExpr) (OptionType.some KExpr x) (OptionType.some KExpr a))
     (consume : forall (A1 B1 : KExpr),
      Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.pi A B))
       (OptionType.some KExpr (KExpr.pi A1 B1)) ->
      TypingCtxConvIn R tenv G a A1 -> C) =>
     consume A B (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi A B)))
      (Eq.substType KExpr (fun (z : KExpr) => TypingCtxConvIn R tenv G z A)
       x a (option_some_inj KExpr x a selected) hx))
    (fun (k : Nat) (_index_ih : forall (a : KExpr),
     Eq (OptionType KExpr) (list_head (list_drop k (ListType.cons KExpr x xs)))
      (OptionType.some KExpr a) ->
     (forall (A1 B1 : KExpr),
      Eq (OptionType KExpr)
       (raw_pi_spine (list_take k (ListType.cons KExpr x xs)) (KExpr.pi A B))
       (OptionType.some KExpr (KExpr.pi A1 B1)) ->
      TypingCtxConvIn R tenv G a A1 -> C) -> C)
     (a : KExpr)
     (selected : Eq (OptionType KExpr) (list_head (list_drop k xs))
      (OptionType.some KExpr a))
     (consume : forall (A1 B1 : KExpr),
      Eq (OptionType KExpr) (raw_pi_spine (list_take k xs) (instantiate B x))
       (OptionType.some KExpr (KExpr.pi A1 B1)) ->
      TypingCtxConvIn R tenv G a A1 -> C) => ih k a selected consume))
  F args U trace",
        r"def typed_raw_pi_spine_select_at (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U) (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))) : TypingCtxConvIn R tenv G a A :=
 typed_raw_pi_spine_select R tenv G F args U trace (TypingCtxConvIn R tenv G a A) k a selected
  (fun (A1 B1 : KExpr)
   (actual : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
    (OptionType.some KExpr (KExpr.pi A1 B1)))
   (typed : TypingCtxConvIn R tenv G a A1) =>
   Eq.substType KExpr (fun (D : KExpr) => TypingCtxConvIn R tenv G a D) A1 A
    (kexpr_pi_inj_fst A1 B1 A B
     (option_some_inj KExpr (KExpr.pi A1 B1) (KExpr.pi A B)
      (Eq.trans (OptionType KExpr) (OptionType.some KExpr (KExpr.pi A1 B1))
       (raw_pi_spine (list_take k args) F) (OptionType.some KExpr (KExpr.pi A B))
       (Eq.symm (OptionType KExpr) (raw_pi_spine (list_take k args) F)
        (OptionType.some KExpr (KExpr.pi A1 B1)) actual) prefix_run))) typed)",
        r"def semantic_typed_spine_select_at (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (h F : KExpr) (args : ListType KExpr) (U T : KExpr)
 (package : SemanticTypedSpineReturn R tenv G h F args U T) (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))) : TypingCtxConvIn R tenv G a A :=
 SemanticTypedSpineReturn.rec R tenv G h F args U T
  (fun (_p : SemanticTypedSpineReturn R tenv G h F args U T) => TypingCtxConvIn R tenv G a A)
  (fun (_head : TypingCtxConvIn R tenv G h F)
   (trace : TypedRawPiSpine R tenv G F args U) (_convert : DefEqIn R U T) =>
   typed_raw_pi_spine_select_at R tenv G F args U trace k a A B selected prefix_run) package",
        r"def typingctxconv_in_const_spine_select_at (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U T : KExpr)
 (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr F))
 (run : Eq (OptionType KExpr) (raw_pi_spine args F) (OptionType.some KExpr U))
 (typed : TypingCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) T)
 (k : Nat) (a A B : KExpr)
 (selected : Eq (OptionType KExpr) (list_head (list_drop k args)) (OptionType.some KExpr a))
 (prefix_run : Eq (OptionType KExpr) (raw_pi_spine (list_take k args) F)
  (OptionType.some KExpr (KExpr.pi A B))) : TypingCtxConvIn R tenv G a A :=
 semantic_typed_spine_select_at R tenv G (KExpr.const n us) F args U T
  (typingctxconv_in_const_spine R faithful tenv G n us F args U T lookup run typed)
  k a A B selected prefix_run",
        r"def typed_spine_identity_selected_argument (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr) : TypingCtxConvIn R typed_spine_identity_tenv G
 (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero)) :=
 typingctxconv_in_const_spine_select_at R faithful typed_spine_identity_tenv G
  Name.anonymous (ListType.nil Level) (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
  typed_spine_identity_args (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  typed_spine_identity_lookup typed_spine_identity_run (typed_raw_pi_spine_identity_const_apply R G)
  (Nat.succ Nat.zero) (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))
  (KExpr.sort (Level.succ Level.zero))
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero)))
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr
   (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero)))))",
        r"def projection_prod_selected_zero_argument :
 TypingCtxConvIn the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr) rfnz_zero rfnz_nat :=
 semantic_typed_spine_select_at the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr)
  projection_prod_ctor (projection_meta_ctor_type projection_prod_result) projection_prod_args
  kcre_witness_prod_type kcre_witness_prod_type projection_prod_typed_constructor_spine
  (Nat.succ (Nat.succ Nat.zero)) rfnz_zero rfnz_nat (KExpr.pi rfnz_nat kcre_witness_prod_type)
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr rfnz_zero))
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr projection_prod_field_telescope))",
        r"def projection_prod_selected_succ_argument :
 TypingCtxConvIn the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr) (KExpr.app rfnz_succ rfnz_zero) rfnz_nat :=
 semantic_typed_spine_select_at the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr)
  projection_prod_ctor (projection_meta_ctor_type projection_prod_result) projection_prod_args
  kcre_witness_prod_type kcre_witness_prod_type projection_prod_typed_constructor_spine
  (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ rfnz_zero) rfnz_nat kcre_witness_prod_type
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero)))
  (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi rfnz_nat kcre_witness_prod_type)))",
    ];

    // Exact binder-desugared forms of the three independently rejected controls.
    const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
        (
            "forged_selected_domain",
            r"forall (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr), TypingCtxConvIn R typed_spine_identity_tenv G
 (KExpr.sort Level.zero) (KExpr.sort Level.zero)",
            r"fun (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr) => typed_spine_identity_selected_argument R faithful G",
        ),
        (
            "forged_dependent_prefix_domain",
            r"Eq (OptionType KExpr)
 (raw_pi_spine (list_take (Nat.succ Nat.zero) typed_spine_identity_args)
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero))))
 (OptionType.some KExpr (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))))",
            r"Eq.refl (OptionType KExpr) (OptionType.some KExpr
  (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))))",
        ),
        (
            "forged_out_of_range_argument",
            r"Eq (OptionType KExpr)
 (list_head (list_drop (Nat.succ (Nat.succ Nat.zero)) typed_spine_identity_args))
 (OptionType.some KExpr (KExpr.sort Level.zero))",
            r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero))",
        ),
    ];

    #[test]
    fn typed_spine_select_records_parse_and_preserve_checked_terms() {
        use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl, SurfaceExpr};
        fn fragment(source: &str, span: Span) -> Vec<&str> {
            source[span.start..span.end].split_whitespace().collect()
        }

        assert_eq!(PROOFS.len(), 7);
        assert_eq!(PROTOTYPES.len(), PROOFS.len());
        assert_eq!(PROOF_ROOTS.len(), PROOFS.len());
        for ((&(name, ty, body), prototype), root) in PROOFS.iter().zip(PROTOTYPES).zip(PROOF_ROOTS)
        {
            assert_eq!(name, *root);
            parse_check(prototype).expect("original checked declaration parses");
            parse_check(&format!("def {name} : {ty} := {body}"))
                .expect("explicit checked record parses");
            let SurfaceDecl::Def {
                name: original_name,
                binders,
                ty: Some(result),
                val,
                ..
            } = parse_decl(prototype).expect("checked prototype AST")
            else {
                panic!("expected definition prototype")
            };
            assert_eq!(
                clean_parser::parse_name(name).expect("explicit source name"),
                original_name
            );
            let parsed_ty = parse_expr(ty).expect("explicit theorem type");
            let parsed_body = parse_expr(body).expect("explicit theorem body");
            if binders.is_empty() {
                assert_eq!(
                    fragment(prototype, result.span()),
                    fragment(ty, parsed_ty.span()),
                    "{name}: unbound result type"
                );
                assert_eq!(
                    fragment(prototype, val.span()),
                    fragment(body, parsed_body.span()),
                    "{name}: unbound proof body"
                );
            } else {
                let SurfaceExpr::Pi(_, type_binders, explicit_result) = parsed_ty else {
                    panic!("{name}: expected explicit forall")
                };
                let SurfaceExpr::Lambda(_, value_binders, explicit_body) = parsed_body else {
                    panic!("{name}: expected explicit fun")
                };
                assert_eq!(binders.len(), type_binders.len(), "{name}: type binders");
                assert_eq!(binders.len(), value_binders.len(), "{name}: value binders");
                for ((original, type_binder), value_binder) in
                    binders.iter().zip(&type_binders).zip(&value_binders)
                {
                    assert_eq!(
                        fragment(prototype, original.span),
                        fragment(ty, type_binder.span),
                        "{name}: forall binder"
                    );
                    assert_eq!(
                        fragment(prototype, original.span),
                        fragment(body, value_binder.span),
                        "{name}: fun binder"
                    );
                }
                assert_eq!(
                    fragment(prototype, result.span()),
                    fragment(ty, explicit_result.span()),
                    "{name}: result type"
                );
                assert_eq!(
                    fragment(prototype, val.span()),
                    fragment(body, explicit_body.span()),
                    "{name}: proof body"
                );
            }
            assert_ne!(body.trim(), name, "no self-constant proof");
        }
        assert_eq!(NEGATIVE_CONTROLS.len(), 3);
        for &(name, ty, body) in NEGATIVE_CONTROLS {
            parse_check(&format!("def {name} : {ty} := {body}"))
                .expect("deliberate refusal must parse");
        }
    }

    #[test]
    fn typed_spine_select_actual_roots_values_types_and_closures_recheck() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for &(name, ty_source, body_source) in PROOFS {
                let definition = spec
                    .definitions()
                    .get(name)
                    .expect("registered proof record");
                let kernel_name = Name::from_string(name);
                let constant = spec
                    .env()
                    .get_const(&kernel_name)
                    .expect("actual environment root");
                let ty = definition
                    .elaborated_type
                    .as_ref()
                    .expect("actual checked type");
                let body = definition
                    .elaborated_value
                    .as_ref()
                    .expect("actual checked body");
                assert!(!definition.is_axiom, "{name}");
                assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
                assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                assert_eq!(
                    definition.proof_status,
                    ProofStatus::DerivedProved,
                    "{name}"
                );
                assert_eq!(definition.type_src, ty_source, "{name}");
                assert_eq!(definition.value_src.as_deref(), Some(body_source), "{name}");
                assert_eq!(&constant.type_, ty, "{name}: stored type");
                assert_eq!(constant.value.as_ref(), Some(body), "{name}: stored body");
                assert!(
                    !matches!(body.kind(), ExprKind::Const(n, _) if n == &kernel_name),
                    "{name}: no self-reference body"
                );
                spec.verify_definition(name)
                    .expect("actual body rechecks against actual type");
                assert!(
                    spec.env()
                        .axiom_deps(&kernel_name)
                        .expect("root exists for domain closure")
                        .is_empty(),
                    "{name}: domain closure"
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&kernel_name)
                        .expect("root exists for foundation closure")
                        .is_empty(),
                    "{name}: foundation closure"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}: computed closure"
                );
            }
        });
    }

    #[test]
    fn typed_spine_select_real_dependent_and_reflected_callers_check() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for (value_src, type_src) in [
                (
                    "typed_spine_identity_selected_argument the_red_env the_red_env_faithful (ListType.nil KExpr)",
                    "TypingCtxConvIn the_red_env typed_spine_identity_tenv (ListType.nil KExpr) (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))",
                ),
                (
                    "projection_prod_selected_zero_argument",
                    "TypingCtxConvIn the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr) rfnz_zero rfnz_nat",
                ),
                (
                    "projection_prod_selected_succ_argument",
                    "TypingCtxConvIn the_red_env kcre_ind_ctor_tenv (ListType.nil KExpr) (KExpr.app rfnz_succ rfnz_zero) rfnz_nat",
                ),
            ] {
                let value = spec.elaborate_source(value_src, "actual selected argument caller").expect("caller elaborates");
                let expected = spec.elaborate_source(type_src, "actual selected argument type").expect("result type elaborates");
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let inferred = checker.infer_type(&value).expect("actual caller checks");
                assert!(checker.is_def_eq(&inferred, &expected), "{value_src}");
            }
        });
    }

    #[test]
    fn typed_spine_select_refuses_wrong_domain_and_out_of_range() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for &(name, ty, body) in NEGATIVE_CONTROLS {
                parse_check(&format!("def {name} : {ty} := {body}"))
                    .expect("forgery is well parsed");
                let error = theorem(
                    &mut spec,
                    name,
                    ty,
                    body,
                    "Deliberately rejected argument/domain forgery.",
                )
                .expect_err("wrong domain or fabricated list selection must be rejected");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                assert!(
                    !spec.definitions().contains_key(name),
                    "{name}: rejected record absent"
                );
                assert!(
                    spec.env().get_const(&Name::from_string(name)).is_none(),
                    "{name}: rejected kernel root absent"
                );
            }
        });
    }
}
