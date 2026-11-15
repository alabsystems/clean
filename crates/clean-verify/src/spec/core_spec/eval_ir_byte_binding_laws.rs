// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Positional binding and fresh-SSA lookup framing for the actual IR machine.
//!
//! The positional premises describe the input lists, not the lookup being
//! proved. Only earlier IDs must differ from the requested ID. An existing
//! argument at that position suffices; whole-call arity and type admission
//! remain separate obligations of the actual byte call rule. These laws retain
//! the operational common-prefix behavior on mismatched lists and current-
//! frame-only lookup. They do not establish a captured closure's semantics.

use crate::spec::{SpecError, Specification};

const SCALAR_AT: &str = r"def ir_byte_scalar_at_v1 (values : IRList IRScalar) (index : Nat) : IROption IRScalar :=
@IRList.rec IRScalar (fun (_ : IRList IRScalar) => Nat -> IROption IRScalar)
  (fun (_ : Nat) => @IROption.none IRScalar)
  (fun (value : IRScalar) (_ : IRList IRScalar) (ih : Nat -> IROption IRScalar) =>
    fun (position : Nat) => @Nat.rec (fun (_ : Nat) => IROption IRScalar)
      (@IROption.some IRScalar value)
      (fun (previous : Nat) (_ : IROption IRScalar) => ih previous) position)
  values index";

const FIRST_PARAM: &str = r"def ir_byte_first_param_v1 (ids : IRList Nat) (index key : Nat) : Prop :=
@IRList.rec Nat (fun (_ : IRList Nat) => Nat -> Prop)
  (fun (_ : Nat) => False)
  (fun (id : Nat) (_ : IRList Nat) (ih : Nat -> Prop) =>
    fun (position : Nat) => @Nat.rec (fun (_ : Nat) => Prop)
      (@Eq Nat id key)
      (fun (previous : Nat) (_ : Prop) =>
        And (@Eq Bool (ir_nat_eqb id key) Bool.false) (ih previous)) position)
  ids index";

const IDS_AVOID: &str = r"def ir_byte_ids_avoid_v1 (ids : IRList Nat) (key : Nat) : Prop :=
@IRList.rec Nat (fun (_ : IRList Nat) => Prop) True
  (fun (id : Nat) (_ : IRList Nat) (ih : Prop) =>
    And (@Eq Bool (ir_nat_eqb id key) Bool.false) ih) ids";

const NONE_NOT_SOME: &str = r"def ir_byte_binding_none_not_some_v1 (value : IRScalar)
  (bad : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) : False :=
@Eq.subst (IROption IRScalar)
  (fun (option : IROption IRScalar) =>
    @IROption.rec IRScalar (fun (_ : IROption IRScalar) => Prop) True
      (fun (_ : IRScalar) => False) option)
  (@IROption.none IRScalar) (@IROption.some IRScalar value) bad True.intro";

const LOOKUP_HEAD: &str = r"def ir_byte_binding_lookup_head_v1
  (id key : Nat) (value : IRScalar) (locals : IRList IRBinding) (same : @Eq Nat id key) :
@Eq (IROption IRScalar)
  (ir_binding_lookup (@IRList.cons IRBinding (IRBinding.mk id value) locals) key)
  (@IROption.some IRScalar value) :=
ir_eq_cong Bool (IROption IRScalar)
  (fun (flag : Bool) => @Bool.rec (fun (_ : Bool) => IROption IRScalar)
    (ir_binding_lookup locals key) (@IROption.some IRScalar value) flag)
  (ir_nat_eqb id key) Bool.true
  (@Eq.trans Bool (ir_nat_eqb id key) (ir_nat_eqb key key) Bool.true
    (ir_eq_cong Nat Bool (fun (candidate : Nat) => ir_nat_eqb candidate key) id key same)
    (ir_byte_function_nat_eq_self_v1 key))";

const LOOKUP_SKIP: &str = r"def ir_byte_binding_lookup_skip_v1
  (id key : Nat) (value : IRScalar) (locals : IRList IRBinding)
  (different : @Eq Bool (ir_nat_eqb id key) Bool.false) :
@Eq (IROption IRScalar)
  (ir_binding_lookup (@IRList.cons IRBinding (IRBinding.mk id value) locals) key)
  (ir_binding_lookup locals key) :=
ir_eq_cong Bool (IROption IRScalar)
  (fun (flag : Bool) => @Bool.rec (fun (_ : Bool) => IROption IRScalar)
    (ir_binding_lookup locals key) (@IROption.some IRScalar value) flag)
  (ir_nat_eqb id key) Bool.false different";

fn lookup(ids: &str, values: &str) -> String {
    format!("(ir_binding_lookup (ir_bind_params {ids} {values} locals) key)")
}

fn positional_type(ids: &str, values: &str, index: &str) -> String {
    format!(
        "forall (locals : IRList IRBinding) (key : Nat) (value : IRScalar),
        ir_byte_first_param_v1 {ids} {index} key ->
        @Eq (IROption IRScalar) (ir_byte_scalar_at_v1 {values} {index}) (@IROption.some IRScalar value) ->
        @Eq (IROption IRScalar) {} (@IROption.some IRScalar value)",
        lookup(ids, values)
    )
}

fn positional_source() -> String {
    let ids = "(@IRList.cons Nat id tailIds)";
    let values = "(@IRList.cons IRScalar actual tailValues)";
    let nil_ids = "(@IRList.nil Nat)";
    let nil_values = "(@IRList.nil IRScalar)";
    let all = |ps: &str| {
        format!(
            "forall (values : IRList IRScalar) (index : Nat), {}",
            positional_type(ps, "values", "index")
        )
    };
    let values_motive = |vs: &str| {
        format!(
            "forall (index : Nat), {}",
            positional_type(ids, vs, "index")
        )
    };
    let result = |ps: &str, vs: &str| {
        format!(
            "(@Eq (IROption IRScalar) {} (@IROption.some IRScalar value))",
            lookup(ps, vs)
        )
    };
    format!(
        "def ir_byte_bind_params_at_v1
  (ids : IRList Nat) (values : IRList IRScalar) (index : Nat)
  (locals : IRList IRBinding) (key : Nat) (value : IRScalar)
  (first : ir_byte_first_param_v1 ids index key)
  (argument : @Eq (IROption IRScalar) (ir_byte_scalar_at_v1 values index) (@IROption.some IRScalar value)) :
@Eq (IROption IRScalar) {outer} (@IROption.some IRScalar value) :=
@IRList.rec Nat (fun (ps : IRList Nat) => {all_ps})
  (fun (values : IRList IRScalar) (index : Nat) (locals : IRList IRBinding) (key : Nat)
    (value : IRScalar) (first : ir_byte_first_param_v1 {nil_ids} index key)
    (_ : @Eq (IROption IRScalar) (ir_byte_scalar_at_v1 values index) (@IROption.some IRScalar value)) =>
      @False.elim {empty_result} first)
  (fun (id : Nat) (tailIds : IRList Nat) (ih : {all_tail}) =>
    fun (values : IRList IRScalar) =>
    @IRList.rec IRScalar (fun (vs : IRList IRScalar) => {values_motive})
      (fun (index : Nat) (locals : IRList IRBinding) (key : Nat) (value : IRScalar)
        (_ : ir_byte_first_param_v1 {ids} index key)
        (argument : @Eq (IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar value)) =>
          @False.elim {missing_result} (ir_byte_binding_none_not_some_v1 value argument))
      (fun (actual : IRScalar) (tailValues : IRList IRScalar) (_ : {tail_value_type}) =>
        fun (index : Nat) => @Nat.rec (fun (position : Nat) => {position_type})
          (fun (locals : IRList IRBinding) (key : Nat) (value : IRScalar)
            (first : @Eq Nat id key)
            (argument : @Eq (IROption IRScalar) (@IROption.some IRScalar actual) (@IROption.some IRScalar value)) =>
              @Eq.trans (IROption IRScalar) {cons_lookup} (@IROption.some IRScalar actual) (@IROption.some IRScalar value)
                (ir_byte_binding_lookup_head_v1 id key actual (ir_bind_params tailIds tailValues locals) first)
                argument)
          (fun (previous : Nat) (_ : {previous_type}) =>
            fun (locals : IRList IRBinding) (key : Nat) (value : IRScalar)
              (first : And (@Eq Bool (ir_nat_eqb id key) Bool.false) (ir_byte_first_param_v1 tailIds previous key))
              (argument : @Eq (IROption IRScalar) (ir_byte_scalar_at_v1 tailValues previous) (@IROption.some IRScalar value)) =>
                @Eq.trans (IROption IRScalar) {cons_lookup} {tail_lookup} (@IROption.some IRScalar value)
                  (ir_byte_binding_lookup_skip_v1 id key actual (ir_bind_params tailIds tailValues locals)
                    (@And.left (@Eq Bool (ir_nat_eqb id key) Bool.false) (ir_byte_first_param_v1 tailIds previous key) first))
                  (ih tailValues previous locals key value
                    (@And.right (@Eq Bool (ir_nat_eqb id key) Bool.false) (ir_byte_first_param_v1 tailIds previous key) first) argument))
          index)
      values)
  ids values index locals key value first argument",
        outer = lookup("ids", "values"),
        all_ps = all("ps"),
        all_tail = all("tailIds"),
        empty_result = result(nil_ids, "values"),
        values_motive = values_motive("vs"),
        missing_result = result(ids, nil_values),
        tail_value_type = values_motive("tailValues"),
        position_type = positional_type(ids, values, "position"),
        previous_type = positional_type(ids, values, "previous"),
        cons_lookup = lookup(ids, values),
        tail_lookup = lookup("tailIds", "tailValues"),
    )
}

fn preservation_type(ids: &str, values: &str) -> String {
    format!(
        "forall (locals : IRList IRBinding) (key : Nat),
        ir_byte_ids_avoid_v1 {ids} key ->
        @Eq (IROption IRScalar) {} (ir_binding_lookup locals key)",
        lookup(ids, values)
    )
}

fn preservation_source() -> String {
    let ids = "(@IRList.cons Nat id tailIds)";
    let values = "(@IRList.cons IRScalar value tailValues)";
    let all = |ps: &str| {
        format!(
            "forall (values : IRList IRScalar), {}",
            preservation_type(ps, "values")
        )
    };
    format!(
        "def ir_byte_bind_params_preserves_v1
  (ids : IRList Nat) (values : IRList IRScalar) (locals : IRList IRBinding) (key : Nat)
  (fresh : ir_byte_ids_avoid_v1 ids key) :
@Eq (IROption IRScalar) {outer} (ir_binding_lookup locals key) :=
@IRList.rec Nat (fun (ps : IRList Nat) => {all_ps})
  (fun (values : IRList IRScalar) (locals : IRList IRBinding) (key : Nat) (_ : True) =>
    @Eq.refl (IROption IRScalar) (ir_binding_lookup locals key))
  (fun (id : Nat) (tailIds : IRList Nat) (ih : {all_tail}) =>
    fun (values : IRList IRScalar) =>
    @IRList.rec IRScalar (fun (vs : IRList IRScalar) => {value_type})
      (fun (locals : IRList IRBinding) (key : Nat) (_ : ir_byte_ids_avoid_v1 {ids} key) =>
        @Eq.refl (IROption IRScalar) (ir_binding_lookup locals key))
      (fun (value : IRScalar) (tailValues : IRList IRScalar) (_ : {tail_type}) =>
        fun (locals : IRList IRBinding) (key : Nat) (fresh : ir_byte_ids_avoid_v1 {ids} key) =>
          @Eq.trans (IROption IRScalar) {cons_lookup} {tail_lookup} (ir_binding_lookup locals key)
            (ir_byte_binding_lookup_skip_v1 id key value (ir_bind_params tailIds tailValues locals)
              (@And.left (@Eq Bool (ir_nat_eqb id key) Bool.false) (ir_byte_ids_avoid_v1 tailIds key) fresh))
            (ih tailValues locals key
              (@And.right (@Eq Bool (ir_nat_eqb id key) Bool.false) (ir_byte_ids_avoid_v1 tailIds key) fresh)))
      values)
  ids values locals key fresh",
        outer = lookup("ids", "values"),
        all_ps = all("ps"),
        all_tail = all("tailIds"),
        value_type = preservation_type(ids, "vs"),
        tail_type = preservation_type(ids, "tailValues"),
        cons_lookup = lookup(ids, values),
        tail_lookup = lookup("tailIds", "tailValues"),
    )
}

const GETD_AT: &str = r"def ir_byte_getd_param_at_v1
  (fid block pc : Nat) (destinations : IRList Nat) (tail : IRList IRFrame)
  (legacy : IRList IRMemSlot) (cursor : Nat)
  (ids : IRList Nat) (values : IRList IRScalar) (index : Nat)
  (locals : IRList IRBinding) (key : Nat) (value : IRScalar)
  (first : ir_byte_first_param_v1 ids index key)
  (argument : @Eq (IROption IRScalar) (ir_byte_scalar_at_v1 values index) (@IROption.some IRScalar value)) :
@Eq IRScalar
  (ir_getd (IRMachine.mk
    (@IRList.cons IRFrame (IRFrame.mk fid block pc (ir_bind_params ids values locals) destinations) tail)
    legacy cursor) key) value :=
ir_eq_cong (IROption IRScalar) IRScalar ir_opt_value
  (ir_binding_lookup (ir_bind_params ids values locals) key) (@IROption.some IRScalar value)
  (ir_byte_bind_params_at_v1 ids values index locals key value first argument)";

const FRAME_PRESERVES: &str = r"def ir_byte_frame_set_many_preserves_v1
  (frame : IRFrame) (ids : IRList Nat) (values : IRList IRScalar) (key : Nat)
  (fresh : ir_byte_ids_avoid_v1 ids key) :
@Eq IRScalar (ir_frame_get (ir_frame_set_many frame ids values) key) (ir_frame_get frame key) :=
@IRFrame.rec (fun (current : IRFrame) =>
  @Eq IRScalar (ir_frame_get (ir_frame_set_many current ids values) key) (ir_frame_get current key))
  (fun (fid block pc : Nat) (locals : IRList IRBinding) (destinations : IRList Nat) =>
    ir_eq_cong (IROption IRScalar) IRScalar ir_opt_value
      (ir_binding_lookup (ir_bind_params ids values locals) key) (ir_binding_lookup locals key)
      (ir_byte_bind_params_preserves_v1 ids values locals key fresh)) frame";

const ADVANCE_PRESERVES: &str = r"def ir_byte_frame_advance_preserves_v1 (frame : IRFrame) (key : Nat) :
@Eq IRScalar (ir_frame_get (ir_frame_advance frame) key) (ir_frame_get frame key) :=
@IRFrame.rec (fun (current : IRFrame) =>
  @Eq IRScalar (ir_frame_get (ir_frame_advance current) key) (ir_frame_get current key))
  (fun (fid block pc : Nat) (locals : IRList IRBinding) (destinations : IRList Nat) =>
    @Eq.refl IRScalar (ir_opt_value (ir_binding_lookup locals key))) frame";

const ADVANCE_SET_PRESERVES: &str = r"def ir_byte_frame_advance_set_preserves_v1
  (frame : IRFrame) (ids : IRList Nat) (values : IRList IRScalar) (key : Nat)
  (fresh : ir_byte_ids_avoid_v1 ids key) :
@Eq IRScalar (ir_frame_get (ir_frame_advance (ir_frame_set_many frame ids values)) key)
  (ir_frame_get frame key) :=
@Eq.trans IRScalar
  (ir_frame_get (ir_frame_advance (ir_frame_set_many frame ids values)) key)
  (ir_frame_get (ir_frame_set_many frame ids values) key) (ir_frame_get frame key)
  (ir_byte_frame_advance_preserves_v1 (ir_frame_set_many frame ids values) key)
  (ir_byte_frame_set_many_preserves_v1 frame ids values key fresh)";

pub(super) fn laws() -> Vec<(&'static str, String)> {
    let mut roots = [
        ("ir_byte_scalar_at_v1", SCALAR_AT),
        ("ir_byte_first_param_v1", FIRST_PARAM),
        ("ir_byte_ids_avoid_v1", IDS_AVOID),
        ("ir_byte_binding_none_not_some_v1", NONE_NOT_SOME),
        ("ir_byte_binding_lookup_head_v1", LOOKUP_HEAD),
        ("ir_byte_binding_lookup_skip_v1", LOOKUP_SKIP),
    ]
    .into_iter()
    .map(|(name, source)| (name, source.to_owned()))
    .collect::<Vec<_>>();
    roots.push(("ir_byte_bind_params_at_v1", positional_source()));
    roots.push(("ir_byte_bind_params_preserves_v1", preservation_source()));
    roots.extend([
        ("ir_byte_getd_param_at_v1", GETD_AT.to_owned()),
        (
            "ir_byte_frame_set_many_preserves_v1",
            FRAME_PRESERVES.to_owned(),
        ),
        (
            "ir_byte_frame_advance_preserves_v1",
            ADVANCE_PRESERVES.to_owned(),
        ),
        (
            "ir_byte_frame_advance_set_preserves_v1",
            ADVANCE_SET_PRESERVES.to_owned(),
        ),
    ]);
    roots
}

impl Specification {
    pub(super) fn add_eval_ir_byte_binding_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(
                &source,
                "Checked positional input binding and fresh SSA lookup framing; no assumed postlookup or closure semantics.",
            )
            .map_err(|error| SpecError::TypeError(format!("{name}: {error}")))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_binding_tests.rs"]
mod tests;
