// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Opt-in structural SSA enum values, not enum memory layouts or Rust binding.
//!
//! Schema inputs describe resolved discriminant bit patterns and ordered field
//! types. The format follows the locked trust-ir fca90a2 EnumDef tag convention:
//! effective_discriminants rejects ambiguity; canonical_tag_repr permits an
//! explicit wider repr, and U128 discriminants remain limited by i128::MAX.
//! A future producer must authenticate those facts and their module identities.
//! This catalog contains canonical NONEMPTY schemas, not a blind translation of
//! all module EnumDefs: an empty/uninhabited EnumDef has no tag and must be absent
//! or explicitly refused by that future producer, never assigned ordinal zero.
//! Any invalid row makes enum admission fail for this whole catalog. Exhaustive
//! coverage of constructible source enums is a separate producer obligation.
//! These descriptors do not compute a Rust layout, attach a source callee, or
//! change byte decoding, the C/Fast call guard, or publication authority.

use crate::spec::{SpecError, Specification};

const TYPES: &str = "IRList IRTy";
const OPTION: &str = "IROption (IRList IRTy)";
const NONE: &str = "@IROption.none (IRList IRTy)";
const CONTEXT_ARGS: &str = "(program : IRModule) (layouts : IRList IRByteLayoutV1)
  (signatures : IRList IRByteSignatureV1) (functions : IRList IRByteFunctionV1)
  (sites : IRList IRByteSiteV1)";
const OLD_CONTEXT: &str = "IRByteContextV1.mk program layouts signatures functions sites";

fn full_types(schema: &str, variant: &str) -> String {
    format!("@IRList.cons IRTy (ir_byte_enum_tag_ty_v1 {schema}) (ir_byte_enum_variant_fields_v1 {variant})")
}

fn guarded_spine(schema: &str, spine: &str) -> String {
    format!(
        "@Bool.rec (fun (_ : Bool) => {OPTION}) ({NONE})
  (ir_byte_enum_schema_spine_v1 {schema} ({spine}))
  (ir_byte_enum_catalog_valid_v1 (ir_byte_context_enums_v1 ctx))"
    )
}

impl Specification {
    pub(super) fn add_eval_ir_byte_enum_descriptors_v1(&mut self) -> Result<(), SpecError> {
        for (name, fields) in [
            (
                "IRByteEnumVariantV1",
                vec![("tag", "Nat"), ("fields", TYPES)],
            ),
            (
                "IRByteEnumV1",
                vec![
                    ("id", "Nat"),
                    ("tag_ty", "IRTy"),
                    ("variants", "IRList IRByteEnumVariantV1"),
                ],
            ),
        ] {
            let prefix = if name == "IRByteEnumV1" {
                "enum"
            } else {
                "enum_variant"
            };
            let telescope = fields
                .iter()
                .map(|(_, ty)| format!("{ty} -> "))
                .collect::<String>();
            self.add_inductive(
                &format!("inductive {name} : Type\n| mk : {telescope}{name}"),
                "Explicit SSA discriminant/payload schema. No offsets, ABI, heap decoding, source provenance or proof authority.",
            )?;
            let pattern = (0..fields.len())
                .map(|i| format!("f{i}"))
                .collect::<Vec<_>>()
                .join(" ");
            for (i, (field, ty)) in fields.iter().enumerate() {
                self.add_recursive_def(
                    &format!("def ir_byte_{prefix}_{field}_v1 (x : {name}) : {ty} := match x with\n| {name}.mk {pattern} => f{i}"),
                    "SSA enum schema projection; reflected input, not a source correspondence certificate.",
                )?;
            }
        }
        Ok(())
    }

    pub(super) fn add_eval_ir_byte_enum_checks_v1(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def ir_byte_enum_width_v1 (bits : Nat) : Bool :=
Bool.or (ir_nat_eqb bits 8) (Bool.or (ir_nat_eqb bits 16)
  (Bool.or (ir_nat_eqb bits 32) (Bool.or (ir_nat_eqb bits 64) (ir_nat_eqb bits 128))))",
            "Exactly the locked trust-ir signed/unsigned discriminant widths; not arbitrary integers or target-sized Usize.",
        )?;
        self.add_recursive_def(
            "def ir_byte_enum_tag_fits_v1 (ty : IRTy) (word : Nat) : Bool := match ty with
| IRTy.int_ bits => Bool.and (ir_byte_enum_width_v1 bits) (ir_byte_integer_fits_v1 ty word)
| IRTy.uint_ bits => Bool.and (ir_byte_enum_width_v1 bits)
    (Bool.and (ir_byte_integer_fits_v1 ty word)
      (@Bool.rec (fun (_ : Bool) => Bool) Bool.true (ir_nat_ltb word (ir_nat_pow2 127)) (ir_nat_eqb bits 128)))
| _ => Bool.false",
            "Canonical tag words. Signed tags use two's-complement bit patterns; U128 cannot encode a source discriminant above i128::MAX. No ordinal interpretation or truncation.",
        )?;
        for (prefix, ty, key) in [
            ("enum_find", "IRByteEnumV1", "ir_byte_enum_id_v1 x"),
            (
                "enum_variant_find",
                "IRByteEnumVariantV1",
                "ir_byte_enum_variant_tag_v1 x",
            ),
        ] {
            self.add_recursive_def(
                &format!("def ir_byte_{prefix}_v1 (xs : IRList {ty}) (key : Nat) : IROption {ty} :=
@IRList.rec {ty} (fun (_ : IRList {ty}) => IROption {ty}) (@IROption.none {ty})
  (fun (x : {ty}) (_ : IRList {ty}) (ih : IROption {ty}) =>
    @Bool.rec (fun (_ : Bool) => IROption {ty}) ih (@IROption.some {ty} x) (ir_nat_eqb ({key}) key)) xs"),
                "Exact schema lookup. Admission separately rejects duplicate keys, including nonadjacent duplicates.",
            )?;
        }
        self.add_recursive_def(
            "def ir_byte_enum_variants_valid_v1 (tagTy : IRTy) (xs : IRList IRByteEnumVariantV1) : Bool :=
@IRList.rec IRByteEnumVariantV1 (fun (_ : IRList IRByteEnumVariantV1) => Bool) Bool.true
  (fun (x : IRByteEnumVariantV1) (rest : IRList IRByteEnumVariantV1) (ih : Bool) =>
    Bool.and (ir_byte_enum_tag_fits_v1 tagTy (ir_byte_enum_variant_tag_v1 x))
      (Bool.and (@IROption.rec IRByteEnumVariantV1 (fun (_ : IROption IRByteEnumVariantV1) => Bool)
        Bool.true (fun (_ : IRByteEnumVariantV1) => Bool.false)
        (ir_byte_enum_variant_find_v1 rest (ir_byte_enum_variant_tag_v1 x))) ih)) xs",
            "Every discriminant fits the exact declared tag carrier and is unique. Payload types are checked structurally against values, not recursively traversed as a type graph.",
        )?;
        self.add_recursive_def(
            "def ir_byte_enum_schema_valid_v1 (schema : IRByteEnumV1) : Bool :=
Bool.and (ir_nat_pos (ir_byte_length_v1 IRByteEnumVariantV1 (ir_byte_enum_variants_v1 schema)))
  (ir_byte_enum_variants_valid_v1 (ir_byte_enum_tag_ty_v1 schema) (ir_byte_enum_variants_v1 schema))",
            "An uninhabited empty enum has no admissible tag. Explicit wider tag representations remain valid.",
        )?;
        self.add_recursive_def(
            "def ir_byte_enum_catalog_valid_v1 (xs : IRList IRByteEnumV1) : Bool :=
@IRList.rec IRByteEnumV1 (fun (_ : IRList IRByteEnumV1) => Bool) Bool.true
  (fun (x : IRByteEnumV1) (rest : IRList IRByteEnumV1) (ih : Bool) =>
    Bool.and (ir_byte_enum_schema_valid_v1 x)
      (Bool.and (@IROption.rec IRByteEnumV1 (fun (_ : IROption IRByteEnumV1) => Bool)
        Bool.true (fun (_ : IRByteEnumV1) => Bool.false)
        (ir_byte_enum_find_v1 rest (ir_byte_enum_id_v1 x))) ih)) xs",
            "All enum IDs and each enum's discriminants are unambiguous. This guard is used only for enum admission: old scalar/struct behavior and layout namespaces are unchanged.",
        )?;
        self.add_recursive_def(
            &format!("def ir_byte_enum_tag_types_v1 (schema : IRByteEnumV1) (tag : Nat) : {OPTION} :=
@IROption.rec IRByteEnumVariantV1 (fun (_ : IROption IRByteEnumVariantV1) => {OPTION}) ({NONE})
  (fun (variant : IRByteEnumVariantV1) => @IROption.some ({TYPES}) ({}))
  (ir_byte_enum_variant_find_v1 (ir_byte_enum_variants_v1 schema) tag)", full_types("schema", "variant")),
            "The exact selected variant contributes tag followed by its ordered payload types; no common-prefix or variant-index matching.",
        )?;
        self.add_recursive_def(
            &format!("def ir_byte_enum_schema_spine_v1 (schema : IRByteEnumV1) (spine : IRScalar) : {OPTION} := match spine with
| IRScalar.vcons head tail => match head with
  | IRScalar.int_ tag => ir_byte_enum_tag_types_v1 schema tag
  | _ => {NONE}
| _ => {NONE}"),
            "Only a real spine whose first lane is an integer tag can select an enum variant. Complete payload checking is still required by the structural value fold.",
        )?;
        self.add_recursive_def(
            &format!("def ir_byte_enum_spine_types_v1 (ctx : IRByteContextV1) (id : Nat) (spine : IRScalar) : {OPTION} :=
@IROption.rec IRByteEnumV1 (fun (_ : IROption IRByteEnumV1) => {OPTION}) ({NONE})
  (fun (schema : IRByteEnumV1) => {})
  (ir_byte_enum_find_v1 (ir_byte_context_enums_v1 ctx) id)", guarded_spine("schema", "spine")),
            "Lookup precedes spine inspection: old contexts definitionally refuse even an abstract enum spine. Catalog validation grants no source or physical-layout authority.",
        )?;
        Ok(())
    }

    pub(super) fn add_eval_ir_byte_enum_laws_v1(&mut self) -> Result<(), SpecError> {
        let spine = "IRScalar.vcons (IRScalar.int_ tag) payload";
        let full = full_types("schema", "variant");
        let some = format!("@IROption.some ({TYPES}) ({full})");
        let premises = "(valid : @Eq Bool (ir_byte_enum_catalog_valid_v1 (ir_byte_context_enums_v1 ctx)) Bool.true)
  (found : @Eq (IROption IRByteEnumV1) (ir_byte_enum_find_v1 (ir_byte_context_enums_v1 ctx) id) (@IROption.some IRByteEnumV1 schema))
  (selected : @Eq (IROption IRByteEnumVariantV1) (ir_byte_enum_variant_find_v1 (ir_byte_enum_variants_v1 schema) tag) (@IROption.some IRByteEnumVariantV1 variant))";
        let inputs = "(ctx : IRByteContextV1) (id : Nat) (schema : IRByteEnumV1)
  (variant : IRByteEnumVariantV1) (tag : Nat) (payload : IRScalar)";
        self.add_recursive_def(
            &format!("def ir_byte_enum_selected_fields_v1 {inputs} {premises} :
@Eq ({OPTION}) (ir_byte_enum_spine_types_v1 ctx id ({spine})) ({some}) :=
ir_byte_case_some_v1 IRByteEnumV1 ({OPTION})
  (ir_byte_enum_find_v1 (ir_byte_context_enums_v1 ctx) id) schema ({NONE})
  (fun (s : IRByteEnumV1) => {}) ({some}) found
  (ir_byte_case_true_v1 ({OPTION}) (ir_byte_enum_catalog_valid_v1 (ir_byte_context_enums_v1 ctx))
    ({NONE}) (ir_byte_enum_tag_types_v1 schema tag) ({some}) valid
    (ir_byte_case_some_v1 IRByteEnumVariantV1 ({OPTION})
      (ir_byte_enum_variant_find_v1 (ir_byte_enum_variants_v1 schema) tag) variant ({NONE})
      (fun (v : IRByteEnumVariantV1) => @IROption.some ({TYPES}) ({})) ({some}) selected
      (@Eq.refl ({OPTION}) ({some}))))", guarded_spine("s", spine), full_types("schema", "v")),
            "Selected complete field list derived from catalog validity and exact schema/discriminant lookups; no value-check success premise.",
        )?;
        let actual =
            format!("ir_byte_value_matches_v1 ctx (IRTy.enum_ id) (IRScalar.aggv ({spine}))");
        let tag_check = "ir_byte_integer_fits_v1 tagTy tag";
        let payload_check = "ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx payload) fields";
        let both = format!("Bool.and ({tag_check}) ({payload_check})");
        let shape = format!("ir_byte_enum_spine_types_v1 ctx id ({spine})");
        let shape_some = "@IROption.some (IRList IRTy) (@IRList.cons IRTy tagTy fields)";
        self.add_recursive_def(
            &format!("def ir_byte_enum_ssa_selected_v1 (ctx : IRByteContextV1) (id tag : Nat)
  (payload : IRScalar) (tagTy : IRTy) (fields : IRList IRTy)
  (selected : @Eq ({OPTION}) ({shape}) ({shape_some})) :
@Eq Bool ({actual}) ({both}) :=
ir_eq_cong ({OPTION}) Bool
  (fun (ts : {OPTION}) => @IROption.rec ({TYPES}) (fun (_ : {OPTION}) => Bool) Bool.false
    (ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx ({spine}))) ts)
  ({shape}) ({shape_some}) selected"),
            "Exact elimination equation for the actual structural value fold: the canonical tag and every payload field, including nested aggregates, are checked together.",
        )?;
        let exact_tag = "ir_byte_enum_tag_ty_v1 schema";
        let exact_fields = "ir_byte_enum_variant_fields_v1 variant";
        let tag_check = format!("ir_byte_integer_fits_v1 ({exact_tag}) tag");
        let payload_check = format!(
            "ir_byte_match_fields_v1 (ir_byte_value_match_v1 ctx payload) ({exact_fields})"
        );
        let both = format!("Bool.and ({tag_check}) ({payload_check})");
        let selection = format!(
            "ir_byte_enum_ssa_selected_v1 ctx id tag payload ({exact_tag}) ({exact_fields})
  (ir_byte_enum_selected_fields_v1 ctx id schema variant tag payload valid found selected)"
        );
        self.add_recursive_def(
            &format!("def ir_byte_enum_ssa_input_v1 {inputs} {premises}
  (tagFits : @Eq Bool ({tag_check}) Bool.true)
  (payloadFits : @Eq Bool ({payload_check}) Bool.true) : @Eq Bool ({actual}) Bool.true :=
@Eq.trans Bool ({actual}) ({both}) Bool.true ({selection})
  (ir_byte_world_and_intro_v1 ({tag_check}) ({payload_check}) tagFits payloadFits)"),
            "Actual enum SSA admission from schema/catalog inputs and complete tag/payload typing. No assumed admission, native execution or Rust representation conclusion.",
        )?;
        for (name, check, projection) in [
            ("tag", &tag_check, "ir_byte_world_and_left_v1"),
            ("payload", &payload_check, "ir_byte_world_and_right_v1"),
        ] {
            self.add_recursive_def(
                &format!("def ir_byte_enum_ssa_{name}_v1 {inputs} {premises}
  (admitted : @Eq Bool ({actual}) Bool.true) : @Eq Bool ({check}) Bool.true :=
{projection} ({tag_check}) ({payload_check})
  (@Eq.trans Bool ({both}) ({actual}) Bool.true (@Eq.symm Bool ({actual}) ({both}) ({selection})) admitted)"),
                "Admission elimination for a selected enum schema; a successful whole-value check entails this actual structural component check.",
            )?;
        }
        self.add_recursive_def(
            &format!("def ir_byte_enum_empty_extension_v1 {CONTEXT_ARGS} (ty : IRTy) (value : IRScalar) :
@Eq Bool (ir_byte_value_matches_v1 (IRByteContextV1.mke program layouts signatures functions sites (@IRList.nil IRByteEnumV1)) ty value)
  (ir_byte_value_matches_v1 ({OLD_CONTEXT}) ty value) :=
@Eq.refl Bool (ir_byte_value_matches_v1 ({OLD_CONTEXT}) ty value)"),
            "An explicit empty enum extension has exactly the old context's value semantics for every value/type, including malformed values; no new global guard.",
        )?;
        let motive = format!("fun (v : IRScalar) => @Eq Bool (ir_byte_value_matches_v1 ({OLD_CONTEXT}) (IRTy.enum_ id) v) Bool.false");
        let mut induction = format!("@IRScalar.rec ({motive}) ");
        for binders in [
            "",
            "(b : Bool)",
            "(n : Nat)",
            "(n : Nat)",
            "",
            "(a : Nat)",
            "",
            "(a : Nat) (b : Nat)",
            "(fid : Nat)",
            &format!("(v : IRScalar) (ih : ({motive}) v)"),
            "",
            &format!(
                "(head : IRScalar) (tail : IRScalar) (ih : ({motive}) head) (it : ({motive}) tail)"
            ),
        ] {
            if binders.is_empty() {
                induction.push_str("(@Eq.refl Bool Bool.false) ");
            } else {
                induction.push_str(&format!("(fun {binders} => @Eq.refl Bool Bool.false) "));
            }
        }
        self.add_recursive_def(
            &format!("def ir_byte_enum_empty_context_refused_v1 {CONTEXT_ARGS} (id : Nat) (value : IRScalar) :
@Eq Bool (ir_byte_value_matches_v1 ({OLD_CONTEXT}) (IRTy.enum_ id) value) Bool.false := {induction} value"),
            "All enum values remain refused by the exact old constructor, proved by structural value induction; even an abstract aggregate spine needs no inspection.",
        )?;
        self.add_recursive_def(
            "def ir_byte_enum_raw_lane_refused_v1 (id : Nat) :
@Eq (IROption Nat) (ir_byte_lane_size_v1 (IRTy.enum_ id)) (@IROption.none Nat) := @Eq.refl (IROption Nat) (@IROption.none Nat)",
            "SSA schema support does not add a byte lane for enums.",
        )?;
        self.add_recursive_def(
            "def ir_byte_enum_raw_decode_refused_v1 (ctx : IRByteContextV1) (id word : Nat) :
@Eq (IROption IRScalar) (ir_byte_decode_word_v1 ctx (IRTy.enum_ id) word) (@IROption.none IRScalar) := @Eq.refl (IROption IRScalar) (@IROption.none IRScalar)",
            "No enum memory decoder, tag offset, niche layout or Rust ABI assertion is introduced.",
        )?;
        for (name, parameter, argument) in
            [("load", "", ""), ("store", "(value : IRScalar)", "value")]
        {
            let fault =
                "IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem";
            self.add_recursive_def(
                &format!("def ir_byte_enum_raw_{name}_refused_v1 (ctx : IRByteContextV1) (id : Nat)
  (ptr : IRScalar) {parameter} (align : Nat) (mem : IRByteMemoryV1) :
@Eq IRByteMemoryResultV1 (ir_byte_{name}_v1 ctx (IRTy.enum_ id) ptr {argument} align Bool.false mem)
  ({fault}) := @Eq.refl IRByteMemoryResultV1 ({fault})"),
                "The actual public raw enum memory operation remains unmodelled and preserves its exact input memory, even with an otherwise valid enum schema.",
            )?;
        }
        Ok(())
    }
}
