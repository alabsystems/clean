// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Nominally typed SSA field operations over complete values.
//!
//! Site catalogs are semantic inputs, not source/reflection certificates. The
//! locked validator distinguishes ExtractField's field result type from
//! InsertField's aggregate result type. Runtime enum lanes belong to the
//! active tag-selected variant, and tag lane zero is read-only. There is no
//! physical aggregate decoding, partial builder, RustCC or producer binding.
//! Insert success rechecks complete output admission. The selected-insert law
//! carries that computed guard as an obligation. The adjacent constructive
//! preservation laws derive it from the input and replacement premises for
//! selected writable lanes, while retaining this runtime check and API.

use crate::spec::{SpecError, Specification};

const BAD: &str = "IRStepResult.fault (IROutcome.type_error IRFault.bad_field)";
const BOUNDS: &str = "IRStepResult.fault (IROutcome.ub IRFault.bad_field)";
const ABSENT: &str = "IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded)";

impl Specification {
    pub(super) fn add_eval_ir_byte_field_v1(&mut self) -> Result<(), SpecError> {
        for source in [
            r"def ir_byte_operand_contains_v1 (rows : IRList IRByteOperandV1) (id : Nat) : Bool :=
@IRList.rec IRByteOperandV1 (fun (_ : IRList IRByteOperandV1) => Bool) Bool.false
  (fun (row : IRByteOperandV1) (_ : IRList IRByteOperandV1) (ih : Bool) =>
    Bool.or (ir_nat_eqb (ir_byte_operand_id_v1 row) id) ih) rows",
            r"def ir_byte_operands_unique_v1 (rows : IRList IRByteOperandV1) : Bool :=
@IRList.rec IRByteOperandV1 (fun (_ : IRList IRByteOperandV1) => Bool) Bool.true
  (fun (row : IRByteOperandV1) (rest : IRList IRByteOperandV1) (ih : Bool) =>
    Bool.and (Bool.not (ir_byte_operand_contains_v1 rest (ir_byte_operand_id_v1 row))) ih) rows",
            r"def ir_byte_operand_find_v1 (rows : IRList IRByteOperandV1) (id : Nat) : IROption IRTy :=
@IRList.rec IRByteOperandV1 (fun (_ : IRList IRByteOperandV1) => IROption IRTy) (@IROption.none IRTy)
  (fun (row : IRByteOperandV1) (_ : IRList IRByteOperandV1) (ih : IROption IRTy) =>
    @Bool.rec (fun (_ : Bool) => IROption IRTy) ih (@IROption.some IRTy (ir_byte_operand_ty_v1 row))
      (ir_nat_eqb (ir_byte_operand_id_v1 row) id)) rows",
            r"def ir_byte_site_key_eq_v1 (a b : IRByteSiteV1) : Bool :=
Bool.and (ir_nat_eqb (ir_byte_site_fid_v1 a) (ir_byte_site_fid_v1 b))
  (Bool.and (ir_nat_eqb (ir_byte_site_block_v1 a) (ir_byte_site_block_v1 b))
    (ir_nat_eqb (ir_byte_site_pc_v1 a) (ir_byte_site_pc_v1 b)))",
            r"def ir_byte_sites_contain_v1 (sites : IRList IRByteSiteV1) (key : IRByteSiteV1) : Bool :=
@IRList.rec IRByteSiteV1 (fun (_ : IRList IRByteSiteV1) => Bool) Bool.false
  (fun (site : IRByteSiteV1) (_ : IRList IRByteSiteV1) (ih : Bool) =>
    Bool.or (ir_byte_site_key_eq_v1 site key) ih) sites",
            r"def ir_byte_sites_unique_v1 (sites : IRList IRByteSiteV1) : Bool :=
@IRList.rec IRByteSiteV1 (fun (_ : IRList IRByteSiteV1) => Bool) Bool.true
  (fun (site : IRByteSiteV1) (rest : IRList IRByteSiteV1) (ih : Bool) =>
    Bool.and (Bool.not (ir_byte_sites_contain_v1 rest site)) ih) sites",
            r"def ir_byte_field_site_valid_v1 (ctx : IRByteContextV1) (site : IRByteSiteV1)
  (rows : IRList IRByteOperandV1) (resultTy : IRTy) : Bool :=
Bool.and (ir_byte_sites_unique_v1 (ir_byte_context_sites_v1 ctx))
  (Bool.and (ir_byte_operands_unique_v1 rows)
    (ir_byte_ty_list_eq_v1 (ir_byte_site_results_v1 site) (@IRList.cons IRTy resultTy (@IRList.nil IRTy))))",
            r"def ir_byte_field_ty_at_v1 (types : IRList IRTy) (index : Nat) : IROption IRTy :=
@IRList.rec IRTy (fun (_ : IRList IRTy) => Nat -> IROption IRTy)
  (fun (_ : Nat) => @IROption.none IRTy)
  (fun (ty : IRTy) (_ : IRList IRTy) (ih : Nat -> IROption IRTy) =>
    fun (position : Nat) => @Nat.rec (fun (_ : Nat) => IROption IRTy)
      (@IROption.some IRTy ty) (fun (previous : Nat) (_ : IROption IRTy) => ih previous) position)
  types index",
            r"def ir_byte_field_types_v1 (ctx : IRByteContextV1) (ty : IRTy) (spine : IRScalar) : IROption (IRList IRTy) := match ty with
| IRTy.struct_ id => @IROption.rec IRByteLayoutV1 (fun (_ : IROption IRByteLayoutV1) => IROption (IRList IRTy))
    (@IROption.none (IRList IRTy)) (fun (layout : IRByteLayoutV1) => @IROption.some (IRList IRTy) (ir_byte_layout_fields_v1 layout)) (ir_byte_layout_v1 ctx ty)
| IRTy.enum_ id => ir_byte_enum_spine_types_v1 ctx id spine
| _ => @IROption.none (IRList IRTy)",
            r"def ir_byte_field_writable_v1 (ty : IRTy) (field : Nat) : Bool := match ty with
| IRTy.enum_ id => Bool.not (ir_nat_iszero field)
| IRTy.struct_ id => Bool.true
| _ => Bool.false",
            &format!(
                r"def ir_byte_field_nominal_fault_v1 (ty : IRTy) (field : Nat) : IRStepResult := match ty with
| IRTy.enum_ id => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BOUNDS}) ({BAD}) (ir_nat_iszero field)
| _ => {BAD}"
            ),
            r"def ir_byte_field_layout_contains_v1 (layouts : IRList IRByteLayoutV1) (ty : IRTy) : Bool :=
@IRList.rec IRByteLayoutV1 (fun (_ : IRList IRByteLayoutV1) => Bool) Bool.false
  (fun (layout : IRByteLayoutV1) (_ : IRList IRByteLayoutV1) (ih : Bool) =>
    Bool.or (ir_byte_ty_eq_v1 (ir_byte_layout_ty_v1 layout) ty) ih) layouts",
            r"def ir_byte_field_layouts_unique_v1 (layouts : IRList IRByteLayoutV1) : Bool :=
@IRList.rec IRByteLayoutV1 (fun (_ : IRList IRByteLayoutV1) => Bool) Bool.true
  (fun (layout : IRByteLayoutV1) (rest : IRList IRByteLayoutV1) (ih : Bool) =>
    Bool.and (Bool.not (ir_byte_field_layout_contains_v1 rest (ir_byte_layout_ty_v1 layout))) ih) layouts",
            r"def ir_byte_field_aggregate_valid_v1 (ctx : IRByteContextV1) (ty : IRTy) (value : IRScalar) : Bool :=
Bool.and (ir_byte_field_layouts_unique_v1 (ir_byte_context_layouts_v1 ctx))
  (Bool.and (ir_byte_enum_catalog_valid_v1 (ir_byte_context_enums_v1 ctx))
    (ir_byte_value_matches_v1 ctx ty value))",
            &format!(
                r"def ir_byte_field_checked_v1 (ctx : IRByteContextV1) (ty : IRTy) (value : IRScalar) : IRStepResult :=
@Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD}) (IRStepResult.value value) (ir_byte_value_matches_v1 ctx ty value)"
            ),
            &format!(
                r"def ir_byte_field_read_v1 (ctx : IRByteContextV1) (fieldTy : IRTy) (spine : IRScalar) (field : Nat) : IRStepResult :=
@IROption.rec IRScalar (fun (_ : IROption IRScalar) => IRStepResult) ({BOUNDS})
  (fun (value : IRScalar) => ir_byte_field_checked_v1 ctx fieldTy value) (ir_vals_get spine field)"
            ),
            &format!(
                r"def ir_byte_field_write_v1 (ctx : IRByteContextV1) (aggregateTy fieldTy : IRTy)
  (spine : IRScalar) (field : Nat) (value : IRScalar) : IRStepResult :=
@Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD})
  (@Bool.rec (fun (_ : Bool) => IRStepResult) ({BOUNDS})
    (ir_byte_field_checked_v1 ctx aggregateTy (IRScalar.aggv (ir_vals_set spine field value)))
    (ir_nat_ltb field (ir_vals_len spine))) (ir_byte_value_matches_v1 ctx fieldTy value)"
            ),
            &format!(
                r"def ir_byte_extract_spine_v1 (ctx : IRByteContextV1) (aggregateTy fieldTy : IRTy)
  (spine : IRScalar) (field : Nat) : IRStepResult :=
@IROption.rec (IRList IRTy) (fun (_ : IROption (IRList IRTy)) => IRStepResult) ({BAD})
  (fun (types : IRList IRTy) => @IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BOUNDS})
    (fun (selected : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult) (ir_byte_field_nominal_fault_v1 aggregateTy field)
      (ir_byte_field_read_v1 ctx fieldTy spine field) (ir_byte_ty_eq_v1 selected fieldTy))
    (ir_byte_field_ty_at_v1 types field)) (ir_byte_field_types_v1 ctx aggregateTy spine)"
            ),
            &format!(
                r"def ir_byte_insert_spine_v1 (ctx : IRByteContextV1) (aggregateTy replacementTy : IRTy)
  (spine : IRScalar) (field : Nat) (value : IRScalar) : IRStepResult :=
@Bool.rec (fun (_ : Bool) => IRStepResult) ({BOUNDS})
  (@IROption.rec (IRList IRTy) (fun (_ : IROption (IRList IRTy)) => IRStepResult) ({BAD})
    (fun (types : IRList IRTy) => @IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BOUNDS})
      (fun (selected : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult) (ir_byte_field_nominal_fault_v1 aggregateTy field)
        (ir_byte_field_write_v1 ctx aggregateTy selected spine field value) (ir_byte_ty_eq_v1 selected replacementTy))
      (ir_byte_field_ty_at_v1 types field)) (ir_byte_field_types_v1 ctx aggregateTy spine))
  (ir_byte_field_writable_v1 aggregateTy field)"
            ),
            &format!(
                r"def ir_byte_extract_typed_v1 (ctx : IRByteContextV1) (aggregateTy fieldTy : IRTy)
  (aggregate : IRScalar) (field : Nat) : IRStepResult :=
@Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD})
  (match aggregate with
  | IRScalar.aggv spine => ir_byte_extract_spine_v1 ctx aggregateTy fieldTy spine field
  | _ => IRStepResult.fault (IROutcome.type_error IRFault.not_agg))
  (ir_byte_field_aggregate_valid_v1 ctx aggregateTy aggregate)"
            ),
            &format!(
                r"def ir_byte_insert_typed_v1 (ctx : IRByteContextV1) (aggregateTy replacementTy : IRTy)
  (aggregate : IRScalar) (field : Nat) (value : IRScalar) : IRStepResult :=
@Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD})
  (match aggregate with
  | IRScalar.aggv spine => ir_byte_insert_spine_v1 ctx aggregateTy replacementTy spine field value
  | _ => IRStepResult.fault (IROutcome.type_error IRFault.not_agg))
  (ir_byte_field_aggregate_valid_v1 ctx aggregateTy aggregate)"
            ),
            &format!(
                r"def ir_byte_extract_field_v1 (ctx : IRByteContextV1) (site : IRByteSiteV1) (fieldTy : IRTy)
  (aggregateId : Nat) (aggregate : IRScalar) (field : Nat) : IRStepResult :=
@IROption.rec (IRList IRByteOperandV1) (fun (_ : IROption (IRList IRByteOperandV1)) => IRStepResult) ({ABSENT})
  (fun (rows : IRList IRByteOperandV1) => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD})
    (@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BAD})
      (fun (aggregateTy : IRTy) => ir_byte_extract_typed_v1 ctx aggregateTy fieldTy aggregate field)
      (ir_byte_operand_find_v1 rows aggregateId)) (ir_byte_field_site_valid_v1 ctx site rows fieldTy))
  (ir_byte_site_operands_v1 site)"
            ),
            &format!(
                r"def ir_byte_insert_field_v1 (ctx : IRByteContextV1) (site : IRByteSiteV1) (resultTy : IRTy)
  (aggregateId : Nat) (aggregate : IRScalar) (field replacementId : Nat) (value : IRScalar) : IRStepResult :=
@IROption.rec (IRList IRByteOperandV1) (fun (_ : IROption (IRList IRByteOperandV1)) => IRStepResult) ({ABSENT})
  (fun (rows : IRList IRByteOperandV1) => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD})
    (@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BAD})
      (fun (aggregateTy : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD})
        (@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BAD})
          (fun (replacementTy : IRTy) => ir_byte_insert_typed_v1 ctx aggregateTy replacementTy aggregate field value)
          (ir_byte_operand_find_v1 rows replacementId)) (ir_byte_ty_eq_v1 aggregateTy resultTy))
      (ir_byte_operand_find_v1 rows aggregateId)) (ir_byte_field_site_valid_v1 ctx site rows resultTy))
  (ir_byte_site_operands_v1 site)"
            ),
        ] {
            self.add_recursive_def(source, "Complete nominal SSA field semantics. Metadata is an explicit input, never native/reflection authority. Bounds, enum tag writes and active enum payload type mismatch have UB endpoints; tag-read/struct nominal and admission errors are type errors; absent old-site metadata is unmodelled.")?;
        }
        Ok(())
    }

    pub(super) fn add_eval_ir_byte_field_laws_v1(&mut self) -> Result<(), SpecError> {
        for source in field_laws() {
            self.add_recursive_def(&source, "Checked complete-value/site field rules. Lookup, nominal type, bounds and admission premises are proof obligations; no source authentication or native execution authority.")?;
        }
        Ok(())
    }
}

fn truth(
    guard: &str,
    failure: &str,
    success: &str,
    expected: &str,
    h: &str,
    proof: &str,
) -> String {
    format!("(ir_byte_case_true_v1 IRStepResult ({guard}) ({failure}) ({success}) ({expected}) {h} ({proof}))")
}

fn found(
    ty: &str,
    option: &str,
    value: &str,
    failure: &str,
    success: &str,
    expected: &str,
    h: &str,
    proof: &str,
) -> String {
    format!("(ir_byte_case_some_v1 ({ty}) IRStepResult ({option}) ({value}) ({failure}) ({success}) ({expected}) {h} ({proof}))")
}

fn field_laws() -> Vec<String> {
    let expected = "IRStepResult.value value";
    let checked = "ir_byte_field_checked_input_v1 ctx fieldTy value admitted";
    let read = found(
        "IRScalar",
        "ir_vals_get spine field",
        "value",
        BOUNDS,
        "fun (selectedValue : IRScalar) => ir_byte_field_checked_v1 ctx fieldTy selectedValue",
        expected,
        "valueFound",
        checked,
    );
    let selected_read = truth(
        "ir_byte_ty_eq_v1 selected fieldTy",
        "ir_byte_field_nominal_fault_v1 aggregateTy field",
        "ir_byte_field_read_v1 ctx fieldTy spine field",
        expected,
        "nominal",
        &read,
    );
    let lane_read = found("IRTy", "ir_byte_field_ty_at_v1 types field", "selected", BOUNDS,
        "fun (selected : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult) (ir_byte_field_nominal_fault_v1 aggregateTy field) (ir_byte_field_read_v1 ctx fieldTy spine field) (ir_byte_ty_eq_v1 selected fieldTy)",
        expected, "laneFound", &selected_read);
    let types_read = found("IRList IRTy", "ir_byte_field_types_v1 ctx aggregateTy spine", "types", BAD,
        &format!("fun (types : IRList IRTy) => @IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BOUNDS}) (fun (selected : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult) (ir_byte_field_nominal_fault_v1 aggregateTy field) (ir_byte_field_read_v1 ctx fieldTy spine field) (ir_byte_ty_eq_v1 selected fieldTy)) (ir_byte_field_ty_at_v1 types field)"),
        expected, "typesFound", &lane_read);
    let extract = truth(
        "ir_byte_field_aggregate_valid_v1 ctx aggregateTy (IRScalar.aggv spine)",
        BAD,
        "ir_byte_extract_spine_v1 ctx aggregateTy fieldTy spine field",
        expected,
        "complete",
        &types_read,
    );

    let rebuilt = "IRScalar.aggv (ir_vals_set spine field value)";
    let updated = format!("IRStepResult.value ({rebuilt})");
    let output =
        format!("ir_byte_field_checked_input_v1 ctx aggregateTy ({rebuilt}) outputAdmitted");
    let bounded = truth(
        "ir_nat_ltb field (ir_vals_len spine)",
        BOUNDS,
        &format!("ir_byte_field_checked_v1 ctx aggregateTy ({rebuilt})"),
        &updated,
        "bounded",
        &output,
    );
    let replacement = truth("ir_byte_value_matches_v1 ctx selected value", BAD,
        &format!("@Bool.rec (fun (_ : Bool) => IRStepResult) ({BOUNDS}) (ir_byte_field_checked_v1 ctx aggregateTy ({rebuilt})) (ir_nat_ltb field (ir_vals_len spine))"),
        &updated, "replacementAdmitted", &bounded);
    let nominal_write = truth(
        "ir_byte_ty_eq_v1 selected replacementTy",
        "ir_byte_field_nominal_fault_v1 aggregateTy field",
        "ir_byte_field_write_v1 ctx aggregateTy selected spine field value",
        &updated,
        "nominal",
        &replacement,
    );
    let lane_write = found("IRTy", "ir_byte_field_ty_at_v1 types field", "selected", BOUNDS,
        "fun (selected : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult) (ir_byte_field_nominal_fault_v1 aggregateTy field) (ir_byte_field_write_v1 ctx aggregateTy selected spine field value) (ir_byte_ty_eq_v1 selected replacementTy)",
        &updated, "laneFound", &nominal_write);
    let types_write_success = format!("fun (types : IRList IRTy) => @IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BOUNDS}) (fun (selected : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult) (ir_byte_field_nominal_fault_v1 aggregateTy field) (ir_byte_field_write_v1 ctx aggregateTy selected spine field value) (ir_byte_ty_eq_v1 selected replacementTy)) (ir_byte_field_ty_at_v1 types field)");
    let types_write = found(
        "IRList IRTy",
        "ir_byte_field_types_v1 ctx aggregateTy spine",
        "types",
        BAD,
        &types_write_success,
        &updated,
        "typesFound",
        &lane_write,
    );
    let writable = truth("ir_byte_field_writable_v1 aggregateTy field", BOUNDS,
        &format!("@IROption.rec (IRList IRTy) (fun (_ : IROption (IRList IRTy)) => IRStepResult) ({BAD}) ({types_write_success}) (ir_byte_field_types_v1 ctx aggregateTy spine)"),
        &updated, "writable", &types_write);
    let insert = truth(
        "ir_byte_field_aggregate_valid_v1 ctx aggregateTy (IRScalar.aggv spine)",
        BAD,
        "ir_byte_insert_spine_v1 ctx aggregateTy replacementTy spine field value",
        &updated,
        "complete",
        &writable,
    );
    let old = "(IRByteSiteV1.mk fid block pc align cc results)";
    let mut laws = vec![
        format!(
            r"def ir_byte_field_checked_input_v1 (ctx : IRByteContextV1) (ty : IRTy) (value : IRScalar)
  (admitted : @Eq Bool (ir_byte_value_matches_v1 ctx ty value) Bool.true) :
@Eq IRStepResult (ir_byte_field_checked_v1 ctx ty value) (IRStepResult.value value) :=
ir_eq_cong Bool IRStepResult (fun (flag : Bool) => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD}) (IRStepResult.value value) flag)
  (ir_byte_value_matches_v1 ctx ty value) Bool.true admitted"
        ),
        format!(
            r"def ir_byte_field_selected_extract_v1 (ctx : IRByteContextV1) (aggregateTy fieldTy selected : IRTy)
  (spine : IRScalar) (field : Nat) (types : IRList IRTy) (value : IRScalar)
  (complete : @Eq Bool (ir_byte_field_aggregate_valid_v1 ctx aggregateTy (IRScalar.aggv spine)) Bool.true)
  (typesFound : @Eq (IROption (IRList IRTy)) (ir_byte_field_types_v1 ctx aggregateTy spine) (@IROption.some (IRList IRTy) types))
  (laneFound : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types field) (@IROption.some IRTy selected))
  (nominal : @Eq Bool (ir_byte_ty_eq_v1 selected fieldTy) Bool.true)
  (valueFound : @Eq (IROption IRScalar) (ir_vals_get spine field) (@IROption.some IRScalar value))
  (admitted : @Eq Bool (ir_byte_value_matches_v1 ctx fieldTy value) Bool.true) :
@Eq IRStepResult (ir_byte_extract_typed_v1 ctx aggregateTy fieldTy (IRScalar.aggv spine) field) ({expected}) := {extract}"
        ),
        format!(
            r"def ir_byte_field_selected_insert_v1 (ctx : IRByteContextV1) (aggregateTy replacementTy selected : IRTy)
  (spine : IRScalar) (field : Nat) (types : IRList IRTy) (value : IRScalar)
  (complete : @Eq Bool (ir_byte_field_aggregate_valid_v1 ctx aggregateTy (IRScalar.aggv spine)) Bool.true)
  (writable : @Eq Bool (ir_byte_field_writable_v1 aggregateTy field) Bool.true)
  (typesFound : @Eq (IROption (IRList IRTy)) (ir_byte_field_types_v1 ctx aggregateTy spine) (@IROption.some (IRList IRTy) types))
  (laneFound : @Eq (IROption IRTy) (ir_byte_field_ty_at_v1 types field) (@IROption.some IRTy selected))
  (nominal : @Eq Bool (ir_byte_ty_eq_v1 selected replacementTy) Bool.true)
  (replacementAdmitted : @Eq Bool (ir_byte_value_matches_v1 ctx selected value) Bool.true)
  (bounded : @Eq Bool (ir_nat_ltb field (ir_vals_len spine)) Bool.true)
  (outputAdmitted : @Eq Bool (ir_byte_value_matches_v1 ctx aggregateTy ({rebuilt})) Bool.true) :
@Eq IRStepResult (ir_byte_insert_typed_v1 ctx aggregateTy replacementTy (IRScalar.aggv spine) field value) ({updated}) := {insert}"
        ),
        format!(
            r"def ir_byte_field_extract_old_refused_v1 (ctx : IRByteContextV1)
  (fid block pc align cc : Nat) (results : IRList IRTy) (ty : IRTy) (id : Nat) (value : IRScalar) (field : Nat) :
@Eq IRStepResult (ir_byte_extract_field_v1 ctx {old} ty id value field) ({ABSENT}) := @Eq.refl IRStepResult ({ABSENT})"
        ),
        format!(
            r"def ir_byte_field_insert_old_refused_v1 (ctx : IRByteContextV1)
  (fid block pc align cc : Nat) (results : IRList IRTy) (ty : IRTy) (id : Nat) (aggregate : IRScalar) (field replacement : Nat) (value : IRScalar) :
@Eq IRStepResult (ir_byte_insert_field_v1 ctx {old} ty id aggregate field replacement value) ({ABSENT}) := @Eq.refl IRStepResult ({ABSENT})"
        ),
        format!(
            r"def ir_byte_field_enum_tag_write_refused_v1 (ctx : IRByteContextV1) (id : Nat) (replacementTy : IRTy) (spine value : IRScalar)
  (complete : @Eq Bool (ir_byte_field_aggregate_valid_v1 ctx (IRTy.enum_ id) (IRScalar.aggv spine)) Bool.true) :
@Eq IRStepResult (ir_byte_insert_typed_v1 ctx (IRTy.enum_ id) replacementTy (IRScalar.aggv spine) 0 value) ({BOUNDS}) :=
ir_eq_cong Bool IRStepResult (fun (flag : Bool) => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD}) ({BOUNDS}) flag)
  (ir_byte_field_aggregate_valid_v1 ctx (IRTy.enum_ id) (IRScalar.aggv spine)) Bool.true complete"
        ),
    ];
    laws.extend(metadata_laws());
    laws.extend(world_laws());
    laws.extend(fetched_laws());
    laws
}

fn metadata_laws() -> Vec<String> {
    let site = "(IRByteSiteV1.mkt fid block pc align cc results rows)";
    let args = "(ctx : IRByteContextV1) (fid block pc align cc : Nat) (results : IRList IRTy)
  (rows : IRList IRByteOperandV1) (ty aggregateTy : IRTy) (id : Nat) (aggregate : IRScalar) (field : Nat)";
    let extract = "ir_byte_extract_typed_v1 ctx aggregateTy ty aggregate field";
    let extract_found = found(
        "IRTy",
        "ir_byte_operand_find_v1 rows id",
        "aggregateTy",
        BAD,
        "fun (aggregateTy : IRTy) => ir_byte_extract_typed_v1 ctx aggregateTy ty aggregate field",
        extract,
        "aggregateFound",
        &format!("@Eq.refl IRStepResult ({extract})"),
    );
    let extract_body = format!("@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BAD}) (fun (aggregateTy : IRTy) => ir_byte_extract_typed_v1 ctx aggregateTy ty aggregate field) (ir_byte_operand_find_v1 rows id)");
    let extract_proof = truth(
        &format!("ir_byte_field_site_valid_v1 ctx {site} rows ty"),
        BAD,
        &extract_body,
        extract,
        "valid",
        &extract_found,
    );
    let insert = "ir_byte_insert_typed_v1 ctx aggregateTy replacementTy aggregate field value";
    let replacement_body = format!("@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BAD}) (fun (replacementTy : IRTy) => ir_byte_insert_typed_v1 ctx aggregateTy replacementTy aggregate field value) (ir_byte_operand_find_v1 rows replacement)");
    let replacement_proof = found("IRTy", "ir_byte_operand_find_v1 rows replacement", "replacementTy", BAD,
        "fun (replacementTy : IRTy) => ir_byte_insert_typed_v1 ctx aggregateTy replacementTy aggregate field value", insert,
        "replacementFound", &format!("@Eq.refl IRStepResult ({insert})"));
    let nominal = truth(
        "ir_byte_ty_eq_v1 aggregateTy ty",
        BAD,
        &replacement_body,
        insert,
        "nominal",
        &replacement_proof,
    );
    let aggregate_body = format!("fun (aggregateTy : IRTy) => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD}) (@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BAD}) (fun (replacementTy : IRTy) => ir_byte_insert_typed_v1 ctx aggregateTy replacementTy aggregate field value) (ir_byte_operand_find_v1 rows replacement)) (ir_byte_ty_eq_v1 aggregateTy ty)");
    let aggregate_proof = found(
        "IRTy",
        "ir_byte_operand_find_v1 rows id",
        "aggregateTy",
        BAD,
        &aggregate_body,
        insert,
        "aggregateFound",
        &nominal,
    );
    let insert_body = format!("@IROption.rec IRTy (fun (_ : IROption IRTy) => IRStepResult) ({BAD}) ({aggregate_body}) (ir_byte_operand_find_v1 rows id)");
    let insert_proof = truth(
        &format!("ir_byte_field_site_valid_v1 ctx {site} rows ty"),
        BAD,
        &insert_body,
        insert,
        "valid",
        &aggregate_proof,
    );
    vec![
        format!(
            r"def ir_byte_field_extract_mkt_v1 {args}
  (valid : @Eq Bool (ir_byte_field_site_valid_v1 ctx {site} rows ty) Bool.true)
  (aggregateFound : @Eq (IROption IRTy) (ir_byte_operand_find_v1 rows id) (@IROption.some IRTy aggregateTy)) :
@Eq IRStepResult (ir_byte_extract_field_v1 ctx {site} ty id aggregate field) ({extract}) := {extract_proof}"
        ),
        format!(
            r"def ir_byte_field_insert_mkt_v1 {args} (replacement : Nat) (replacementTy : IRTy) (value : IRScalar)
  (valid : @Eq Bool (ir_byte_field_site_valid_v1 ctx {site} rows ty) Bool.true)
  (aggregateFound : @Eq (IROption IRTy) (ir_byte_operand_find_v1 rows id) (@IROption.some IRTy aggregateTy))
  (nominal : @Eq Bool (ir_byte_ty_eq_v1 aggregateTy ty) Bool.true)
  (replacementFound : @Eq (IROption IRTy) (ir_byte_operand_find_v1 rows replacement) (@IROption.some IRTy replacementTy)) :
@Eq IRStepResult (ir_byte_insert_field_v1 ctx {site} ty id aggregate field replacement value) ({insert}) := {insert_proof}"
        ),
        format!(
            r"def ir_byte_field_extract_metadata_refused_v1 {args}
  (invalid : @Eq Bool (ir_byte_field_site_valid_v1 ctx {site} rows ty) Bool.false) :
@Eq IRStepResult (ir_byte_extract_field_v1 ctx {site} ty id aggregate field) ({BAD}) :=
ir_eq_cong Bool IRStepResult (fun (flag : Bool) => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD}) ({extract_body}) flag)
  (ir_byte_field_site_valid_v1 ctx {site} rows ty) Bool.false invalid"
        ),
        format!(
            r"def ir_byte_field_insert_metadata_refused_v1 {args} (replacement : Nat) (value : IRScalar)
  (invalid : @Eq Bool (ir_byte_field_site_valid_v1 ctx {site} rows ty) Bool.false) :
@Eq IRStepResult (ir_byte_insert_field_v1 ctx {site} ty id aggregate field replacement value) ({BAD}) :=
ir_eq_cong Bool IRStepResult (fun (flag : Bool) => @Bool.rec (fun (_ : Bool) => IRStepResult) ({BAD}) ({insert_body}) flag)
  (ir_byte_field_site_valid_v1 ctx {site} rows ty) Bool.false invalid"
        ),
    ]
}

fn world_laws() -> Vec<String> {
    let guard = "(Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat rs) (ir_byte_length_v1 IRScalar values)) (ir_byte_values_match_v1 ctx types values))";
    let failure = "(@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) world)";
    let nil = "(@IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_frame) world)";
    let cons = "(@IRByteConfigV1.running W (IRMachine.mk (@IRList.cons IRFrame (ir_frame_advance (ir_frame_set_many current rs values)) rest) legacy cursor) world)";
    let bool_proof = |success: &str| {
        format!("@Bool.rec (fun (flag : Bool) => @Eq (IRByteWorldV1 W) (ir_byte_final_world_v1 W (@Bool.rec (fun (_ : Bool) => IRByteConfigV1 W) {failure} {success} flag)) world) (@Eq.refl (IRByteWorldV1 W) world) (@Eq.refl (IRByteWorldV1 W) world) {guard}")
    };
    vec![
        format!(r"def ir_byte_field_bind_world_v1 (W : Type) (ctx : IRByteContextV1) (state : IRMachine) (world : IRByteWorldV1 W)
  (rs : IRList Nat) (types : IRList IRTy) (values : IRList IRScalar) :
@Eq (IRByteWorldV1 W) (ir_byte_final_world_v1 W (ir_byte_bind_values_v1 W ctx state world rs types values)) world :=
@IRMachine.rec (fun (s : IRMachine) => @Eq (IRByteWorldV1 W) (ir_byte_final_world_v1 W (ir_byte_bind_values_v1 W ctx s world rs types values)) world)
  (fun (frames : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat) =>
    @IRList.rec IRFrame (fun (fs : IRList IRFrame) => @Eq (IRByteWorldV1 W) (ir_byte_final_world_v1 W (ir_byte_bind_values_v1 W ctx (IRMachine.mk fs legacy cursor) world rs types values)) world)
      ({nil_proof})
      (fun (current : IRFrame) (rest : IRList IRFrame) (_ : @Eq (IRByteWorldV1 W) (ir_byte_final_world_v1 W (ir_byte_bind_values_v1 W ctx (IRMachine.mk rest legacy cursor) world rs types values)) world) => {cons_proof}) frames) state",
            nil_proof = bool_proof(nil), cons_proof = bool_proof(cons)),
        r"def ir_byte_field_scalar_world_v1 (W : Type) (ctx : IRByteContextV1) (state : IRMachine) (world : IRByteWorldV1 W)
  (rs : IRList Nat) (types : IRList IRTy) (result : IRStepResult) :
@Eq (IRByteWorldV1 W) (ir_byte_final_world_v1 W (ir_byte_scalar_result_v1 W ctx state world rs types result)) world :=
@IRStepResult.rec (fun (r : IRStepResult) => @Eq (IRByteWorldV1 W) (ir_byte_final_world_v1 W (ir_byte_scalar_result_v1 W ctx state world rs types r)) world)
  (fun (value : IRScalar) => ir_byte_field_bind_world_v1 W ctx state world rs types (@IRList.cons IRScalar value (@IRList.nil IRScalar)))
  (fun (_ : IROutcome) => @Eq.refl (IRByteWorldV1 W) world) result".to_owned(),
        r"def ir_byte_field_fault_world_v1 (W : Type) (ctx : IRByteContextV1) (state : IRMachine) (world : IRByteWorldV1 W)
  (rs : IRList Nat) (types : IRList IRTy) (fault : IROutcome) :
@Eq (IRByteConfigV1 W) (ir_byte_scalar_result_v1 W ctx state world rs types (IRStepResult.fault fault))
  (@IRByteConfigV1.halted W fault world) := @Eq.refl (IRByteConfigV1 W) (@IRByteConfigV1.halted W fault world)".to_owned(),
    ]
}

fn fetched_laws() -> Vec<String> {
    let state = "(IRMachine.mk (@IRList.cons IRFrame current tail) legacy cursor)";
    let common = format!(
        r"(W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)
  (current : IRFrame) (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)
  (world : IRByteWorldV1 W) (function : IRFunc) (block : IRBlock) (site : IRByteSiteV1)
  (ty : IRTy) (aggregate field : Nat) (results : IRList Nat)
  (before : @Eq Bool (ir_byte_world_valid_v1 W {state} world) Bool.true)
  (functionFound : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_frame_func current)) (@IROption.some IRFunc function))
  (blockFound : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks function) (ir_frame_block current)) (@IROption.some IRBlock block))
  (siteFound : @Eq (IROption IRByteSiteV1) (ir_byte_site_v1 ctx (ir_frame_func current) (ir_frame_block current) (ir_frame_pc current)) (@IROption.some IRByteSiteV1 site))
  (arity : @Eq Bool (ir_nat_eqb (ir_byte_length_v1 Nat results) (ir_byte_length_v1 IRTy (ir_byte_site_results_v1 site))) Bool.true)"
    );
    [
        ("extract", "", "(IRInst.extractfield ty aggregate field)", format!("(ir_byte_extract_field_v1 ctx site ty aggregate (ir_getd {state} aggregate) field)")),
        ("insert", "(replacement : Nat)", "(IRInst.insertfield ty aggregate field replacement)", format!("(ir_byte_insert_field_v1 ctx site ty aggregate (ir_getd {state} aggregate) field replacement (ir_getd {state} replacement))")),
    ].into_iter().map(|(name, extra, instruction, result)| format!(r"def ir_byte_step_field_{name}_v1 {common} {extra}
  (nodeFound : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes block) (ir_frame_pc current)) (@IROption.some IRNode (IRNode.mk {instruction} results))) :
@Eq (IRByteConfigV1 W) (ir_byte_step_v1 W ctx providers (@IRByteConfigV1.running W {state} world))
  (ir_byte_scalar_result_v1 W ctx {state} world results (ir_byte_site_results_v1 site) {result}) :=
ir_byte_step_fetched_v1 W ctx providers current tail legacy cursor world function block {instruction} results site
  before functionFound blockFound nodeFound siteFound arity")).collect()
}
