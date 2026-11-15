// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive structural field proofs ported from independently checked Lean terms.
//!
//! The Byte constructor installs these declarations and checks their proof terms.
//! Runtime output checks and existing field APIs are unchanged. Catalog inputs
//! and nominal type metadata are not authenticated source/native certificates.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_field_set_laws_v1(&mut self) -> Result<(), SpecError> {
        for source in [
            OPTION_NONE_SOME_FALSE,
            OPTION_SOME_INJECTIVE,
            TYPED_SPINE_SET,
        ] {
            self.add_recursive_def(
                source,
                "Generic structural field typing derived from actual admission/lookups. No output typing assumption, source authentication, or native authority; runtime guards retained.",
            )?;
        }
        Ok(())
    }
}

const OPTION_NONE_SOME_FALSE: &str = r"def ir_byte_field_option_none_some_false_v1 (A : Type) (value : A)
  (h : @Eq (IROption A) (@IROption.none A) (@IROption.some A value)) : False :=
  @Eq.subst (IROption A)
    (fun option => @IROption.rec A (fun _ => Prop) True (fun _ => False) option)
    (@IROption.none A) (@IROption.some A value) h True.intro";

const OPTION_SOME_INJECTIVE: &str = r"def ir_byte_field_option_some_injective_v1 (A : Type) (first second : A)
  (h : @Eq (IROption A) (@IROption.some A first) (@IROption.some A second)) :
  @Eq A first second :=
  ir_eq_cong (IROption A) A
    (fun option => @IROption.rec A (fun _ => A) first (fun value => value) option)
    (@IROption.some A first) (@IROption.some A second) h";

const TYPED_SPINE_SET: &str = r"def ir_byte_field_spine_set_typed_v1 (ctx : IRByteContextV1)
  (spine : IRScalar) (types : IRList IRTy) (index : Nat)
  (selected : IRTy) (replacement : IRScalar)
  (input : @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx spine) types) Bool.true)
  (lane : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected))
  (replacementTyped : @Eq Bool (ir_byte_value_matches_v1 ctx selected replacement) Bool.true) :
  @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set spine index replacement)) types) Bool.true :=
  let invalid : forall (value : IRScalar),
    (forall (types : IRList IRTy),
      @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx value) types) Bool.false) ->
    forall (types : IRList IRTy) (index : Nat) (selected : IRTy) (replacement : IRScalar),
      @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx value) types) Bool.true ->
      @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected) ->
      @Eq Bool (ir_byte_value_matches_v1 ctx selected replacement) Bool.true ->
      @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set value index replacement)) types) Bool.true :=
    fun value refused types index selected replacement input _ _ =>
      @False.elim
        (@Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set value index replacement)) types) Bool.true)
        (ir_byte_world_false_true_v1
          (@Eq.trans Bool Bool.false
            (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx value) types) Bool.true
            (@Eq.symm Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx value) types) Bool.false (refused types)) input))
  @IRScalar.rec
    (fun value =>
      forall (types : IRList IRTy) (index : Nat) (selected : IRTy) (replacement : IRScalar),
        @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx value) types) Bool.true ->
        @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types index) (@IROption.some IRTy selected) ->
        @Eq Bool (ir_byte_value_matches_v1 ctx selected replacement) Bool.true ->
        @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set value index replacement)) types) Bool.true)
    (invalid IRScalar.undef_ (fun _ => @Eq.refl Bool Bool.false))
    (fun b => invalid (IRScalar.bool_ b) (fun _ => @Eq.refl Bool Bool.false))
    (fun n => invalid (IRScalar.int_ n) (fun _ => @Eq.refl Bool Bool.false))
    (fun n => invalid (IRScalar.float_ n) (fun _ => @Eq.refl Bool Bool.false))
    (invalid IRScalar.unit_ (fun _ => @Eq.refl Bool Bool.false))
    (fun n => invalid (IRScalar.ptr_ n) (fun _ => @Eq.refl Bool Bool.false))
    (invalid IRScalar.nullptr_ (fun _ => @Eq.refl Bool Bool.false))
    (fun data metadata => invalid (IRScalar.fat_ data metadata) (fun _ => @Eq.refl Bool Bool.false))
    (fun fid => invalid (IRScalar.fnptr_ fid) (fun _ => @Eq.refl Bool Bool.false))
    (fun inner _ => invalid (IRScalar.aggv inner) (fun _ => @Eq.refl Bool Bool.false))
    (fun types index selected replacement input lane _ =>
      @IRList.rec IRTy
        (fun rows =>
          @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx IRScalar.vnil) rows) Bool.true ->
          @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 rows index) (@IROption.some IRTy selected) ->
          @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set IRScalar.vnil index replacement)) rows) Bool.true)
        (fun _ missing => @False.elim
          (@Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx IRScalar.vnil) (@IRList.nil IRTy)) Bool.true)
          (ir_byte_field_option_none_some_false_v1 IRTy selected missing))
        (fun ty rest _ impossible _ => @False.elim
          (@Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx IRScalar.vnil) (@IRList.cons IRTy ty rest)) Bool.true)
          (ir_byte_world_false_true_v1 impossible)) types input lane)
    (fun head tail _ tailIH => fun types index selected replacement input lane replacementTyped =>
      @IRList.rec IRTy
        (fun rows =>
          @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.vcons head tail)) rows) Bool.true ->
          @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 rows index) (@IROption.some IRTy selected) ->
          @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set (IRScalar.vcons head tail) index replacement)) rows) Bool.true)
        (fun impossible _ => @False.elim
          (@Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set (IRScalar.vcons head tail) index replacement)) (@IRList.nil IRTy)) Bool.true)
          (ir_byte_world_false_true_v1 impossible))
        (fun ty rest _ =>
          @Nat.rec
            (fun position =>
              @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (IRScalar.vcons head tail)) (@IRList.cons IRTy ty rest)) Bool.true ->
              @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 (@IRList.cons IRTy ty rest) position) (@IROption.some IRTy selected) ->
              @Eq Bool (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set (IRScalar.vcons head tail) position replacement)) (@IRList.cons IRTy ty rest)) Bool.true)
            (fun input lane =>
              ir_byte_world_and_intro_v1
                (ir_byte_value_matches_v1 ctx ty replacement)
                (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest)
                (@Eq.subst IRTy
                  (fun actual => @Eq Bool (ir_byte_value_matches_v1 ctx actual replacement) Bool.true)
                  selected ty
                  (@Eq.symm IRTy ty selected (ir_byte_field_option_some_injective_v1 IRTy ty selected lane)) replacementTyped)
                (ir_byte_world_and_right_v1
                  (ir_byte_value_matches_v1 ctx ty head)
                  (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest) input))
            (fun previous _ input lane =>
              ir_byte_world_and_intro_v1
                (ir_byte_value_matches_v1 ctx ty head)
                (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx (ir_vals_set tail previous replacement)) rest)
                (ir_byte_world_and_left_v1
                  (ir_byte_value_matches_v1 ctx ty head)
                  (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest) input)
                (tailIH rest previous selected replacement
                  (ir_byte_world_and_right_v1
                    (ir_byte_value_matches_v1 ctx ty head)
                    (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx tail) rest) input)
                  lane replacementTyped)) index) types input lane)
    spine types index selected replacement input lane replacementTyped";

#[cfg(test)]
#[path = "eval_ir_byte_field_set_laws_tests.rs"]
mod tests;
