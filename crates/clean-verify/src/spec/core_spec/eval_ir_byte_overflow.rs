// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Byte-native checked integer arithmetic with two ordered result lanes.
//! The existing scalar value/flag functions supply arithmetic, not the legacy
//! cell-memory dispatcher. Input carriers, exact result types and result arity
//! remain checked by ByteV1. Neither an overflow flag nor a normal return is
//! assumed by the transfer laws. Assert/panic semantics remain unsupported.

use super::eval_ir_byte_atomic::with_declaration_name;
use crate::spec::{SpecError, Specification};

const INTS: &str = r"def ir_byte_overflow_ints_v1
  (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (world : IRByteWorldV1 W)
  (results : IRList Nat) (site : IRByteSiteV1) (op : IROverflowOp)
  (ty : IRTy) (signed : Bool) (width a b : Nat) : IRByteConfigV1 W :=
@Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
  (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) world)
  (ir_byte_bind_values_v1 W ctx s world results (ir_byte_site_results_v1 site)
    (@IRList.cons IRScalar (IRScalar.int_ (ir_overflow_value op width a b))
      (@IRList.cons IRScalar (IRScalar.bool_ (ir_overflow_flag op signed width a b))
        (@IRList.nil IRScalar))))
  (Bool.and
    (ir_byte_ty_list_eq_v1 (ir_byte_site_results_v1 site)
      (@IRList.cons IRTy ty (@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy))))
    (Bool.and (ir_byte_integer_fits_v1 ty a) (ir_byte_integer_fits_v1 ty b)))";

const VALUES: &str = r"def ir_byte_overflow_vals_v1
  (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (world : IRByteWorldV1 W)
  (results : IRList Nat) (site : IRByteSiteV1) (op : IROverflowOp)
  (ty : IRTy) (signed : Bool) (width : Nat) (a b : IRScalar) : IRByteConfigV1 W :=
@IROption.rec Nat (fun (_ : IROption Nat) => IRByteConfigV1 W)
  (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_int) world)
  (fun (x : Nat) => @IROption.rec Nat (fun (_ : IROption Nat) => IRByteConfigV1 W)
    (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_int) world)
    (fun (y : Nat) => ir_byte_overflow_ints_v1 W ctx s world results site op ty signed width x y)
    (ir_as_int b)) (ir_as_int a)";

const EXEC: &str = r"def ir_byte_overflow_exec_v1
  (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (world : IRByteWorldV1 W)
  (results : IRList Nat) (site : IRByteSiteV1) (op : IROverflowOp)
  (ty : IRTy) (a b : IRScalar) : IRByteConfigV1 W :=
match ty with
| IRTy.int_ width => ir_byte_overflow_vals_v1 W ctx s world results site op ty Bool.true width a b
| IRTy.uint_ width => ir_byte_overflow_vals_v1 W ctx s world results site op ty Bool.false width a b
| _ => @IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_int) world";

const CONFIG: &str = "(IRByteConfigV1 W)";
const MACHINE: &str = "(IRMachine.mk (@IRList.cons IRFrame current tail) legacy cursor)";

fn types(ty: &str) -> String {
    format!("(@IRList.cons IRTy {ty} (@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy)))")
}

fn values(signed: &str) -> String {
    format!(
        "(@IRList.cons IRScalar (IRScalar.int_ (ir_overflow_value op width a b))
      (@IRList.cons IRScalar (IRScalar.bool_ (ir_overflow_flag op {signed} width a b))
        (@IRList.nil IRScalar)))"
    )
}

fn bound(machine: &str, signed: &str) -> String {
    format!(
        "(ir_byte_bind_values_v1 W ctx {machine} world results (ir_byte_site_results_v1 site) {})",
        values(signed)
    )
}

fn execution(machine: &str, ty: &str, left: &str, right: &str) -> String {
    format!("(ir_byte_overflow_exec_v1 W ctx {machine} world results site op {ty} {left} {right})")
}

fn input_premises(ty: &str) -> String {
    format!(
        "(aFits : @Eq Bool (ir_byte_integer_fits_v1 {ty} a) Bool.true)
  (bFits : @Eq Bool (ir_byte_integer_fits_v1 {ty} b) Bool.true)
  (resultTypes : @Eq Bool (ir_byte_ty_list_eq_v1 (ir_byte_site_results_v1 site) {}) Bool.true)",
        types(ty)
    )
}

fn transfer(name: &str, ty: &str, signed: &str) -> String {
    let actual = execution("s", ty, "(IRScalar.int_ a)", "(IRScalar.int_ b)");
    let after = bound("s", signed);
    let same_types = format!(
        "(ir_byte_ty_list_eq_v1 (ir_byte_site_results_v1 site) {})",
        types(ty)
    );
    let left = format!("(ir_byte_integer_fits_v1 {ty} a)");
    let right = format!("(ir_byte_integer_fits_v1 {ty} b)");
    let guard = format!("(Bool.and {same_types} (Bool.and {left} {right}))");
    format!(
        "def {name} (W : Type) (ctx : IRByteContextV1) (s : IRMachine)
  (world : IRByteWorldV1 W) (results : IRList Nat) (site : IRByteSiteV1)
  (op : IROverflowOp) (width a b : Nat) {} : @Eq {CONFIG} {actual} {after} :=
ir_eq_cong Bool {CONFIG}
  (fun (accepted : Bool) => @Bool.rec (fun (_ : Bool) => {CONFIG})
    (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) world) {after} accepted)
  {guard} Bool.true
  (ir_byte_function_and_true_v1 {same_types} (Bool.and {left} {right}) resultTypes
    (ir_byte_function_and_true_v1 {left} {right} aFits bFits))",
        input_premises(ty)
    )
}

fn congr(map: &str, left: &str, right: &str, proof: &str) -> String {
    format!("(ir_eq_cong IRScalar {CONFIG} {map} {left} {right} {proof})")
}

fn trans(left: &str, middle: &str, right: &str, first: &str, second: &str) -> String {
    format!("(@Eq.trans {CONFIG} {left} {middle} {right} {first} {second})")
}

fn fetched(name: &str, ty: &str, signed: &str, law: &str) -> String {
    let instruction = format!("(IRInst.overflow op {ty} left right)");
    let actual =
        format!("(ir_byte_step_v1 W ctx providers (@IRByteConfigV1.running W {MACHINE} world))");
    let exec =
        format!("(ir_byte_exec_v1 W ctx providers {MACHINE} world site {instruction} results)");
    let old_left = format!("(ir_getd {MACHINE} left)");
    let old_right = format!("(ir_getd {MACHINE} right)");
    let x = "(IRScalar.int_ a)";
    let y = "(IRScalar.int_ b)";
    let first = execution(MACHINE, ty, x, &old_right);
    let both = execution(MACHINE, ty, x, y);
    let after = bound(MACHINE, signed);
    let operand_proof = trans(
        &exec,
        &first,
        &both,
        &congr(
            &format!(
                "(fun (v : IRScalar) => {})",
                execution(MACHINE, ty, "v", &old_right)
            ),
            &old_left,
            x,
            "leftFound",
        ),
        &congr(
            &format!("(fun (v : IRScalar) => {})", execution(MACHINE, ty, x, "v")),
            &old_right,
            y,
            "rightFound",
        ),
    );
    let fetch_proof = format!(
        "(ir_byte_step_fetched_v1 W ctx providers current tail legacy cursor world
      function block {instruction} results site before functionFound blockFound nodeFound siteFound arity)"
    );
    let transfer_proof =
        format!("({law} W ctx {MACHINE} world results site op width a b aFits bFits resultTypes)");
    format!(
        "def {name} (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)
  (current : IRFrame) (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)
  (world : IRByteWorldV1 W) (left right : Nat) (results : IRList Nat) (site : IRByteSiteV1)
  (function : IRFunc) (block : IRBlock) (op : IROverflowOp) (width a b : Nat)
  {}
  (before : @Eq Bool (ir_byte_world_valid_v1 W {MACHINE} world) Bool.true)
  (leftFound : @Eq IRScalar {old_left} {x}) (rightFound : @Eq IRScalar {old_right} {y})
  (functionFound : @Eq (IROption IRFunc)
    (ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_frame_func current))
    (@IROption.some IRFunc function))
  (blockFound : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks function) (ir_frame_block current))
    (@IROption.some IRBlock block))
  (nodeFound : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes block) (ir_frame_pc current))
    (@IROption.some IRNode (IRNode.mk {instruction} results)))
  (siteFound : @Eq (IROption IRByteSiteV1)
    (ir_byte_site_v1 ctx (ir_frame_func current) (ir_frame_block current) (ir_frame_pc current))
    (@IROption.some IRByteSiteV1 site))
  (arity : @Eq Bool (ir_nat_eqb (ir_byte_length_v1 Nat results)
    (ir_byte_length_v1 IRTy (ir_byte_site_results_v1 site))) Bool.true) :
@Eq {CONFIG} {actual} {after} := {}",
        input_premises(ty),
        trans(&actual, &exec, &after, &fetch_proof, &trans(&exec, &both, &after, &operand_proof, &transfer_proof))
    )
}

impl Specification {
    pub(super) fn add_eval_ir_byte_overflow_v1(&mut self) -> Result<(), SpecError> {
        for source in [INTS, VALUES, EXEC] {
            self.add_recursive_def(source,
                "Byte-native two-lane checked integer arithmetic. Exact input/site/result checks retain the whole world; no legacy dispatcher or Assert rule.")?;
        }
        Ok(())
    }

    pub(super) fn add_eval_ir_byte_overflow_laws_v1(&mut self) -> Result<(), SpecError> {
        for (kind, signed) in [("uint", "Bool.false"), ("int", "Bool.true")] {
            let ty = format!("(IRTy.{kind}_ width)");
            let transfer_name = format!("ir_byte_overflow_{kind}_transfer_v1");
            let step_name = format!("ir_byte_step_overflow_{kind}_v1");
            for (name, source) in [
                (transfer_name.clone(), transfer(&transfer_name, &ty, signed)),
                (
                    step_name.clone(),
                    fetched(&step_name, &ty, signed, &transfer_name),
                ),
            ] {
                self.add_recursive_def(&source,
                    "Checked generic Overflow transfer through actual fetched instruction. Input/lookup/site premises only; computed result lanes still pass Byte binding checks.")
                    .map_err(|error| with_declaration_name(&name, error))?;
                self.verify_definition(&name)?;
            }
        }
        Ok(())
    }
}
