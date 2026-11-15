// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closed data and value typing for the versioned byte/world EvalIR profile.
//!
//! These declarations do not alter the legacy cell-addressed machine. Contexts
//! carry a module and explicit catalogs, including function-address assignments.
//! Authenticating their reflection from source is a separate obligation. They
//! are not certificates and do not authorize native code.
//! The dispatch and final-state driver are separate: these utilities alone do
//! not admit or execute a module.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_types(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_byte_enum_descriptors_v1()?;
        for (name, fields) in [
            (
                "IRByteLayoutV1",
                vec![
                    ("ty", "IRTy"),
                    ("size", "Nat"),
                    ("align", "Nat"),
                    ("fields", "IRList IRTy"),
                    ("offsets", "IRList Nat"),
                ],
            ),
            (
                "IRByteSignatureV1",
                vec![
                    ("id", "Nat"),
                    ("params", "IRList IRTy"),
                    ("returns", "IRList IRTy"),
                    ("vararg", "Bool"),
                ],
            ),
            (
                "IRByteFunctionV1",
                vec![
                    ("fid", "Nat"),
                    ("sig", "Nat"),
                    ("address", "Nat"),
                    ("cc", "Nat"),
                    ("import", "Bool"),
                ],
            ),
            ("IRByteOperandV1", vec![("id", "Nat"), ("ty", "IRTy")]),
            (
                "IRByteSiteV1",
                vec![
                    ("fid", "Nat"),
                    ("block", "Nat"),
                    ("pc", "Nat"),
                    ("align", "Nat"),
                    ("cc", "Nat"),
                    ("results", "IRList IRTy"),
                ],
            ),
            (
                "IRByteContextV1",
                vec![
                    ("module", "IRModule"),
                    ("layouts", "IRList IRByteLayoutV1"),
                    ("signatures", "IRList IRByteSignatureV1"),
                    ("functions", "IRList IRByteFunctionV1"),
                    ("sites", "IRList IRByteSiteV1"),
                ],
            ),
            (
                "IRByteAllocationV1",
                vec![
                    ("base", "Nat"),
                    ("size", "Nat"),
                    ("owner", "Nat"),
                    ("live", "Bool"),
                ],
            ),
            (
                "IRByteMemoryV1",
                vec![
                    ("allocs", "IRList IRByteAllocationV1"),
                    ("bytes", "Nat -> IROption Nat"),
                    ("next", "Nat"),
                ],
            ),
        ] {
            let prefix = match name {
                "IRByteLayoutV1" => "layout",
                "IRByteSignatureV1" => "signature",
                "IRByteFunctionV1" => "binding",
                "IRByteOperandV1" => "operand",
                "IRByteSiteV1" => "site",
                "IRByteContextV1" => "context",
                "IRByteAllocationV1" => "alloc",
                _ => "mem",
            };
            let telescope = fields
                .iter()
                .map(|(_, ty)| {
                    // An anonymous parenthesized identifier is parsed as an
                    // untyped binder by this declaration parser. Ordinary
                    // type applications need no parentheses before an arrow;
                    // only the function-valued byte map does.
                    if ty.contains("->") {
                        format!("({ty}) -> ")
                    } else {
                        format!("{ty} -> ")
                    }
                })
                .collect::<String>();
            // Preserve the old constructors' exact telescopes and execution
            // choices. mki explicitly opts GEP into nominal index decoding;
            // mkt remains the historical catalog without changing its GEP.
            // No constructor authenticates source or physical layout.
            let extension = if name == "IRByteContextV1" {
                format!("\n| mke : {telescope}IRList IRByteEnumV1 -> {name}")
            } else if name == "IRByteSiteV1" {
                format!(
                    "\n| mkt : {telescope}IRList IRByteOperandV1 -> {name}\n| mki : {telescope}IRList IRByteOperandV1 -> {name}"
                )
            } else {
                String::new()
            };
            self.add_inductive(
                &format!("inductive {name} : Type\n| mk : {telescope}{name}{extension}"),
                "Exact byte-profile data. No proof or native publication authority.",
            )?;
            let pattern = (0..fields.len())
                .map(|index| format!("f{index}"))
                .collect::<Vec<_>>()
                .join(" ");
            for (index, (field, ty)) in fields.iter().enumerate() {
                let extension = if name == "IRByteContextV1" {
                    format!("\n| {name}.mke {pattern} enums => f{index}")
                } else if name == "IRByteSiteV1" {
                    format!(
                        "\n| {name}.mkt {pattern} operands => f{index}\n| {name}.mki {pattern} operands => f{index}"
                    )
                } else {
                    String::new()
                };
                self.add_recursive_def(&format!("def ir_byte_{prefix}_{field}_v1 (x : {name}) : {ty} := match x with\n| {name}.mk {pattern} => f{index}{extension}"),
                    "Byte-profile record projection; all fields remain semantic inputs.")?;
            }
        }
        self.add_recursive_def("def ir_byte_site_operands_v1 (site : IRByteSiteV1) : IROption (IRList IRByteOperandV1) := match site with\n| IRByteSiteV1.mk fid block pc align cc results => @IROption.none (IRList IRByteOperandV1)\n| IRByteSiteV1.mkt fid block pc align cc results operands => @IROption.some (IRList IRByteOperandV1) operands\n| IRByteSiteV1.mki fid block pc align cc results operands => @IROption.some (IRList IRByteOperandV1) operands",
            "Opt-in nominal SSA operand catalog. Old sites have absent metadata, not inferred carrier types. Catalog/source authentication remains separate.")?;
        self.add_recursive_def("def ir_byte_context_enums_v1 (ctx : IRByteContextV1) : IRList IRByteEnumV1 := match ctx with\n| IRByteContextV1.mk program layouts signatures functions sites => @IRList.nil IRByteEnumV1\n| IRByteContextV1.mke program layouts signatures functions sites enums => enums",
            "Opt-in SSA enum schemas. Every old context has an empty catalog; no physical enum layout is inferred.")?;
        self.add_inductive("inductive IRByteMemoryResultV1 : Type\n| value : IRScalar -> IRByteMemoryV1 -> IRByteMemoryResultV1\n| fault : IROutcome -> IRByteMemoryV1 -> IRByteMemoryResultV1",
            "Memory operation result retaining the actual memory on success and failure.")?;
        self.add_inductive("inductive IRByteWorldV1 (W : Type) : Type\n| mk : IRByteMemoryV1 -> W -> IRList Nat -> Nat -> IRByteWorldV1 W",
            "Byte memory, external world, current-first activation owners, next fresh owner.")?;
        for (name, ty, value) in [
            ("memory", "IRByteMemoryV1", "memory"),
            ("host", "W", "host"),
            ("owners", "IRList Nat", "owners"),
            ("next", "Nat", "next"),
        ] {
            self.add_recursive_def(&format!("def ir_byte_world_{name}_v1 (W : Type) (w : IRByteWorldV1 W) : {ty} := match w with\n| IRByteWorldV1.mk memory host owners next => {value}"),
                "World projection; activation and provider state remain explicit.")?;
        }
        self.add_inductive("inductive IRByteConfigV1 (W : Type) : Type\n| running : IRMachine -> IRByteWorldV1 W -> IRByteConfigV1 W\n| halted : IROutcome -> IRByteWorldV1 W -> IRByteConfigV1 W",
            "Both terminal and running configurations retain their exact byte/provider world.")?;
        self.add_inductive("inductive IRByteImportResultV1 (W : Type) : Type\n| mk : IROutcome -> IRByteMemoryV1 -> W -> IRByteImportResultV1 W",
            "Explicit imported-function semantics; normal returns carry all lanes. This is an execution-environment parameter, not an assertion of runtime fidelity.")?;
        self.add_recursive_def("def IRByteProvidersV1 (W : Type) : Type := Nat -> IRList IRScalar -> IRByteMemoryV1 -> W -> IRByteImportResultV1 W",
            "Exact function-id-indexed external semantics; only imported functions may invoke it.")?;
        self.add_eval_ir_byte_type_equality()?;
        self.add_eval_ir_byte_catalogs()?;
        self.add_eval_ir_byte_fat_types_v1()?;
        self.add_eval_ir_byte_value_typing()
    }

    fn add_eval_ir_byte_type_equality(&mut self) -> Result<(), SpecError> {
        let variants: &[(&str, &[&str])] = &[
            ("bool_", &[]),
            ("int_", &["Nat"]),
            ("uint_", &["Nat"]),
            ("float_", &["Nat"]),
            ("ptr_", &[]),
            ("ref_", &["IRTy"]),
            ("refmut_", &["IRTy"]),
            ("rawconst_", &["IRTy"]),
            ("rawmut_", &["IRTy"]),
            ("rc_", &["IRTy"]),
            ("fatptr_", &["IRTy"]),
            ("unit_", &[]),
            ("never_", &[]),
            ("tuple_", &["Nat"]),
            ("array_", &["IRTy", "Nat"]),
            ("struct_", &["Nat"]),
            ("enum_", &["Nat"]),
            ("func_", &["Nat"]),
            ("usize_", &["Nat"]),
            ("fatstr_", &[]),
            ("fatslice_", &["IRTy"]),
            ("fatdyn_", &["Nat"]),
            ("containerlen_", &[]),
            ("containervtable_", &[]),
        ];
        let mut source = "def ir_byte_ty_eq_v1 (a : IRTy) (b : IRTy) : Bool := @IRTy.rec (fun (_ : IRTy) => IRTy -> Bool) ".to_owned();
        for (variant, fields) in variants {
            source.push_str("(fun ");
            for (index, ty) in fields.iter().enumerate() {
                source.push_str(&format!("(a{index} : {ty}) "));
            }
            for (index, ty) in fields.iter().enumerate() {
                if *ty == "IRTy" {
                    source.push_str(&format!("(h{index} : IRTy -> Bool) "));
                }
            }
            source.push_str("(other : IRTy) => match other with\n");
            for (other, other_fields) in variants {
                source.push_str(&format!("| IRTy.{other}"));
                for index in 0..other_fields.len() {
                    source.push_str(&format!(" b{index}"));
                }
                source.push_str(" => ");
                if variant != other {
                    source.push_str("Bool.false\n");
                } else {
                    let mut check = "Bool.true".to_owned();
                    for (index, ty) in fields.iter().enumerate().rev() {
                        let equality = if *ty == "IRTy" {
                            format!("h{index} b{index}")
                        } else {
                            format!("ir_nat_eqb a{index} b{index}")
                        };
                        check = format!("Bool.and ({equality}) ({check})");
                    }
                    source.push_str(&check);
                    source.push('\n');
                }
            }
            source.push_str(") ");
        }
        source.push_str("a b");
        self.add_recursive_def(
            &source,
            "Structural equality of actual reflected types, not equality of physical width.",
        )?;
        self.add_recursive_def("def ir_byte_length_v1 (A : Type) (xs : IRList A) : Nat := @IRList.rec A (fun (_ : IRList A) => Nat) Nat.zero (fun (_ : A) (_ : IRList A) (n : Nat) => Nat.succ n) xs",
            "Shared exact list arity; no common-prefix call binding is accepted in this profile.")?;
        self.add_recursive_def("def ir_byte_ty_list_eq_v1 (xs : IRList IRTy) (ys : IRList IRTy) : Bool := @IRList.rec IRTy (fun (_ : IRList IRTy) => IRList IRTy -> Bool) (fun (zs : IRList IRTy) => @IRList.rec IRTy (fun (_ : IRList IRTy) => Bool) Bool.true (fun (_ : IRTy) (_ : IRList IRTy) (_ : Bool) => Bool.false) zs) (fun (x : IRTy) (_ : IRList IRTy) (ih : IRList IRTy -> Bool) => fun (zs : IRList IRTy) => @IRList.rec IRTy (fun (_ : IRList IRTy) => Bool) Bool.false (fun (y : IRTy) (rest : IRList IRTy) (_ : Bool) => Bool.and (ir_byte_ty_eq_v1 x y) (ih rest)) zs) xs ys",
            "Exact ordered signature/result-type equality.")?;
        Ok(())
    }

    fn add_eval_ir_byte_catalogs(&mut self) -> Result<(), SpecError> {
        for (name, ty, arg_ty, field, predicate) in [
            (
                "layout",
                "IRByteLayoutV1",
                "IRTy",
                "layouts",
                "ir_byte_ty_eq_v1 (ir_byte_layout_ty_v1 x) key",
            ),
            (
                "signature",
                "IRByteSignatureV1",
                "Nat",
                "signatures",
                "ir_nat_eqb (ir_byte_signature_id_v1 x) key",
            ),
            (
                "function",
                "IRByteFunctionV1",
                "Nat",
                "functions",
                "ir_nat_eqb (ir_byte_binding_fid_v1 x) key",
            ),
            (
                "function_address",
                "IRByteFunctionV1",
                "Nat",
                "functions",
                "ir_nat_eqb (ir_byte_binding_address_v1 x) key",
            ),
        ] {
            self.add_recursive_def(&format!("def ir_byte_{name}_v1 (ctx : IRByteContextV1) (key : {arg_ty}) : IROption {ty} := @IRList.rec {ty} (fun (_ : IRList {ty}) => IROption {ty}) (@IROption.none {ty}) (fun (x : {ty}) (_ : IRList {ty}) (ih : IROption {ty}) => @Bool.rec (fun (_ : Bool) => IROption {ty}) ih (@IROption.some {ty} x) ({predicate})) (ir_byte_context_{field}_v1 ctx)"),
                "Lookup in the exact reflected module catalog. Missing data is not a wildcard. Reflection rejects duplicate keys.")?;
        }
        self.add_recursive_def("def ir_byte_site_v1 (ctx : IRByteContextV1) (fid : Nat) (block : Nat) (pc : Nat) : IROption IRByteSiteV1 := @IRList.rec IRByteSiteV1 (fun (_ : IRList IRByteSiteV1) => IROption IRByteSiteV1) (@IROption.none IRByteSiteV1) (fun (x : IRByteSiteV1) (_ : IRList IRByteSiteV1) (ih : IROption IRByteSiteV1) => @Bool.rec (fun (_ : Bool) => IROption IRByteSiteV1) ih (@IROption.some IRByteSiteV1 x) (Bool.and (ir_nat_eqb (ir_byte_site_fid_v1 x) fid) (Bool.and (ir_nat_eqb (ir_byte_site_block_v1 x) block) (ir_nat_eqb (ir_byte_site_pc_v1 x) pc)))) (ir_byte_context_sites_v1 ctx)",
            "Exact function/block/node site identity, including sparse IDs and actual node order.")?;
        Ok(())
    }

    fn add_eval_ir_byte_value_typing(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def("def ir_byte_pointer_ty_v1 (ty : IRTy) : Bool := match ty with\n| IRTy.ptr_ => Bool.true\n| IRTy.ref_ t => Bool.true\n| IRTy.refmut_ t => Bool.true\n| IRTy.rawconst_ t => Bool.true\n| IRTy.rawmut_ t => Bool.true\n| IRTy.rc_ t => Bool.true\n| _ => Bool.false",
            "Thin data pointer carriers; typed function identities remain distinct.")?;
        self.add_recursive_def("def ir_byte_integer_width_v1 (ty : IRTy) : IROption Nat := match ty with\n| IRTy.usize_ bits => @Bool.rec (fun (_ : Bool) => IROption Nat) (@IROption.none Nat) (@IROption.some Nat bits) (ir_nat_eqb bits 64)\n| _ => ir_ty_int_width ty",
            "Byte-only target-indexed integer width. Usize is distinct from fixed-width integers; this LE64 profile refuses every other pointer width. The legacy width helper is unchanged.")?;
        self.add_recursive_def("def ir_byte_integer_fits_v1 (ty : IRTy) (n : Nat) : Bool := @IROption.rec Nat (fun (_ : IROption Nat) => Bool) Bool.false (fun (bits : Nat) => Bool.and (ir_nat_pos bits) (Bool.and (ir_nat_leb bits 128) (ir_nat_ltb n (ir_nat_pow2 bits)))) (ir_byte_integer_width_v1 ty)",
            "Canonical finite-width integer bit patterns, not signed Nat coercions.")?;
        self.add_recursive_def("def ir_byte_function_fits_v1 (ctx : IRByteContextV1) (ty : IRTy) (fid : Nat) : Bool := match ty with\n| IRTy.func_ sig => @IROption.rec IRByteFunctionV1 (fun (_ : IROption IRByteFunctionV1) => Bool) Bool.false (fun (binding : IRByteFunctionV1) => Bool.and (ir_nat_eqb sig (ir_byte_binding_sig_v1 binding)) (Bool.and (ir_nat_pos (ir_byte_binding_address_v1 binding)) (ir_nat_ltb (ir_byte_binding_address_v1 binding) (ir_nat_pow2 64)))) (ir_byte_function_v1 ctx fid)\n| _ => Bool.false",
            "A function carrier names an exact existing target with its actual signature and nonzero 64-bit code address.")?;
        self.add_eval_ir_byte_enum_checks_v1()?;
        self.add_inductive("inductive IRByteValueMatchV1 : Type\n| mk : (IRTy -> Bool) -> (IRList IRTy -> Bool) -> IRByteValueMatchV1",
            "Structural value recursion computes value and aggregate-spine checking together, avoiding type-graph recursion or a fresh depth cutoff.")?;
        self.add_recursive_def("def ir_byte_match_value_v1 (m : IRByteValueMatchV1) : IRTy -> Bool := match m with\n| IRByteValueMatchV1.mk value fields => value", "Value-check projection.")?;
        self.add_recursive_def("def ir_byte_match_fields_v1 (m : IRByteValueMatchV1) : IRList IRTy -> Bool := match m with\n| IRByteValueMatchV1.mk value fields => fields", "Aggregate-spine-check projection.")?;
        self.add_recursive_def("def ir_byte_match_scalar_v1 (check : IRTy -> Bool) : IRByteValueMatchV1 := IRByteValueMatchV1.mk check (fun (_ : IRList IRTy) => Bool.false)", "A scalar is not an aggregate spine.")?;
        self.add_recursive_def("def ir_byte_match_aggregate_v1 (ctx : IRByteContextV1) (spine : IRScalar) (fields : IRList IRTy -> Bool) (ty : IRTy) : Bool := match ty with\n| IRTy.struct_ id => @IROption.rec IRByteLayoutV1 (fun (_ : IROption IRByteLayoutV1) => Bool) Bool.false (fun (layout : IRByteLayoutV1) => fields (ir_byte_layout_fields_v1 layout)) (ir_byte_layout_v1 ctx ty)\n| IRTy.enum_ id => @IROption.rec (IRList IRTy) (fun (_ : IROption (IRList IRTy)) => Bool) Bool.false fields (ir_byte_enum_spine_types_v1 ctx id spine)\n| _ => Bool.false",
            "Typed SSA structs and explicitly cataloged tagged enum spines. The existing recursive checker checks the entire tag/payload list; neither family gains raw memory decoding.")?;
        self.add_recursive_def(concat!(
            "def ir_byte_value_match_v1 (ctx : IRByteContextV1) (v : IRScalar) : IRByteValueMatchV1 := @IRScalar.rec (fun (_ : IRScalar) => IRByteValueMatchV1) ",
            "(ir_byte_match_scalar_v1 (fun (_ : IRTy) => Bool.false)) ",
            "(fun (_ : Bool) => ir_byte_match_scalar_v1 (fun (ty : IRTy) => ir_byte_ty_eq_v1 ty IRTy.bool_)) ",
            "(fun (n : Nat) => ir_byte_match_scalar_v1 (fun (ty : IRTy) => ir_byte_integer_fits_v1 ty n)) ",
            "(fun (_ : Nat) => ir_byte_match_scalar_v1 (fun (_ : IRTy) => Bool.false)) ",
            "(ir_byte_match_scalar_v1 (fun (ty : IRTy) => ir_byte_ty_eq_v1 ty IRTy.unit_)) ",
            "(fun (a : Nat) => ir_byte_match_scalar_v1 (fun (ty : IRTy) => Bool.and (ir_byte_pointer_ty_v1 ty) (Bool.and (ir_nat_pos a) (ir_nat_ltb a (ir_nat_pow2 64))))) ",
            "(ir_byte_match_scalar_v1 ir_byte_pointer_ty_v1) ",
            "(fun (data : Nat) (metadata : Nat) => ir_byte_match_scalar_v1 (fun (ty : IRTy) => ir_byte_fat_value_matches_v1 ty data metadata)) ",
            "(fun (fid : Nat) => ir_byte_match_scalar_v1 (fun (ty : IRTy) => ir_byte_function_fits_v1 ctx ty fid)) ",
            "(fun (spine : IRScalar) (ih : IRByteValueMatchV1) => ir_byte_match_scalar_v1 (ir_byte_match_aggregate_v1 ctx spine (ir_byte_match_fields_v1 ih))) ",
            "(IRByteValueMatchV1.mk (fun (_ : IRTy) => Bool.false) (fun (ts : IRList IRTy) => ir_nat_iszero (ir_byte_length_v1 IRTy ts))) ",
            "(fun (_ : IRScalar) (_ : IRScalar) (head : IRByteValueMatchV1) (tail : IRByteValueMatchV1) => IRByteValueMatchV1.mk (fun (_ : IRTy) => Bool.false) ",
            "(fun (ts : IRList IRTy) => @IRList.rec IRTy (fun (_ : IRList IRTy) => Bool) Bool.false ",
            "(fun (ty : IRTy) (rest : IRList IRTy) (_ : Bool) => Bool.and (ir_byte_match_value_v1 head ty) (ir_byte_match_fields_v1 tail rest)) ts)) v"
        ), "Structural checking of complete runtime values and nested SSA structs/enums, preserving pointer/function and scalar sort distinctions. Schema cycles do not introduce type-graph recursion.")?;
        self.add_recursive_def("def ir_byte_value_matches_v1 (ctx : IRByteContextV1) (ty : IRTy) (v : IRScalar) : Bool := ir_byte_match_value_v1 (ir_byte_value_match_v1 ctx v) ty",
            "Typed value admission for root arguments, imported results and local calls.")?;
        self.add_recursive_def("def ir_byte_values_match_v1 (ctx : IRByteContextV1) (types : IRList IRTy) (values : IRList IRScalar) : Bool := @IRList.rec IRTy (fun (_ : IRList IRTy) => IRList IRScalar -> Bool) (fun (vs : IRList IRScalar) => ir_nat_iszero (ir_byte_length_v1 IRScalar vs)) (fun (ty : IRTy) (_ : IRList IRTy) (ih : IRList IRScalar -> Bool) => fun (vs : IRList IRScalar) => @IRList.rec IRScalar (fun (_ : IRList IRScalar) => Bool) Bool.false (fun (v : IRScalar) (rest : IRList IRScalar) (_ : Bool) => Bool.and (ir_byte_value_matches_v1 ctx ty v) (ih rest)) vs) types values",
            "Exact result and argument arity plus every lane's type; never prefix-only matching.")?;
        Ok(())
    }
}
