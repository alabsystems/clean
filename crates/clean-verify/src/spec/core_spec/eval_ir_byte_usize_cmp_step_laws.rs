// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real fetched Usize64 ICmp with exact result binding and unchanged world.
//! Premises describe canonical input values, SSA lookups and the actual fetched
//! instruction/site. There is no successful-evaluation or post-world premise.
//! This proves neither a conditional branch nor a native Arc/abort behavior.

use super::eval_ir_byte_atomic::with_declaration_name;
use crate::spec::{SpecError, Specification};

const CONFIG: &str = "(IRByteConfigV1 W)";
const MACHINE: &str = "(IRMachine.mk (@IRList.cons IRFrame current tail) legacy cursor)";
const RESULTS: &str = "(@IRList.cons Nat destination (@IRList.nil Nat))";
const TYPES: &str = "(@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy))";
const INSTRUCTION: &str = "(IRInst.icmp IRICmpOp.ugt (IRTy.usize_ 64) left right)";
const ARGS: &str = "W ctx providers current tail legacy cursor world
  left right destination alignment convention function block a b
  aFits bFits before leftFound rightFound functionFound blockFound nodeFound siteFound";

fn site() -> String {
    format!(
        "(IRByteSiteV1.mk (ir_frame_func current) (ir_frame_block current)
      (ir_frame_pc current) alignment convention {TYPES})"
    )
}

fn common() -> String {
    format!(
        "(W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)
  (current : IRFrame) (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)
  (world : IRByteWorldV1 W)
  (left right destination alignment convention : Nat) (function : IRFunc) (block : IRBlock)
  (a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 64)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 64)) Bool.true)
  (before : @Eq Bool (ir_byte_world_valid_v1 W {MACHINE} world) Bool.true)
  (leftFound : @Eq IRScalar (ir_getd {MACHINE} left) (IRScalar.int_ a))
  (rightFound : @Eq IRScalar (ir_getd {MACHINE} right) (IRScalar.int_ b))
  (functionFound : @Eq (IROption IRFunc)
    (ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_frame_func current))
    (@IROption.some IRFunc function))
  (blockFound : @Eq (IROption IRBlock)
    (ir_block_find (ir_func_blocks function) (ir_frame_block current))
    (@IROption.some IRBlock block))
  (nodeFound : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes block) (ir_frame_pc current))
    (@IROption.some IRNode (IRNode.mk {INSTRUCTION} {RESULTS})))
  (siteFound : @Eq (IROption IRByteSiteV1)
    (ir_byte_site_v1 ctx (ir_frame_func current) (ir_frame_block current) (ir_frame_pc current))
    (@IROption.some IRByteSiteV1 {}))",
        site()
    )
}

fn after() -> String {
    format!(
        "(@IRByteConfigV1.running W
      (IRMachine.mk (@IRList.cons IRFrame
        (ir_frame_advance (ir_frame_set_many current {RESULTS}
          (@IRList.cons IRScalar (IRScalar.bool_ (ir_nat_ltb b a)) (@IRList.nil IRScalar))))
        tail) legacy cursor) world)"
    )
}

fn actual() -> String {
    format!("(ir_byte_step_v1 W ctx providers (@IRByteConfigV1.running W {MACHINE} world))")
}

fn scalar_result() -> String {
    format!("(ir_byte_scalar_result_v1 W ctx {MACHINE} world {RESULTS} {TYPES})")
}

fn fits(value: &str) -> String {
    format!("(ir_byte_value_matches_v1 ctx (IRTy.usize_ 64) {value})")
}

fn operation(left: &str, right: &str) -> String {
    format!(
        "(@Bool.rec (fun (_ : Bool) => {CONFIG})
      (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) world)
      ({} (ir_byte_icmp_eval_v1 IRICmpOp.ugt (IRTy.usize_ 64) {left} {right}))
      (Bool.and {} {}))",
        scalar_result(),
        fits(left),
        fits(right)
    )
}

fn congr(a: &str, b: &str, f: &str, x: &str, y: &str, proof: &str) -> String {
    format!("(ir_eq_cong {a} {b} {f} {x} {y} {proof})")
}

fn trans(ty: &str, a: &str, b: &str, c: &str, ab: &str, bc: &str) -> String {
    format!("(@Eq.trans {ty} {a} {b} {c} {ab} {bc})")
}

fn step_source() -> String {
    let left = format!("(ir_getd {MACHINE} left)");
    let right = format!("(ir_getd {MACHINE} right)");
    let x = "(IRScalar.int_ a)";
    let y = "(IRScalar.int_ b)";
    let exec = format!(
        "(ir_byte_exec_v1 W ctx providers {MACHINE} world {} {INSTRUCTION} {RESULTS})",
        site()
    );
    let operands = trans(
        CONFIG,
        &exec,
        &operation(x, &right),
        &operation(x, y),
        &congr(
            "IRScalar",
            CONFIG,
            &format!("(fun (v : IRScalar) => {})", operation("v", &right)),
            &left,
            x,
            "leftFound",
        ),
        &congr(
            "IRScalar",
            CONFIG,
            &format!("(fun (v : IRScalar) => {})", operation(x, "v")),
            &right,
            y,
            "rightFound",
        ),
    );
    let comparison = format!("(ir_byte_icmp_eval_v1 IRICmpOp.ugt (IRTy.usize_ 64) {x} {y})");
    let returned = "(IRStepResult.value (IRScalar.bool_ (ir_nat_ltb b a)))";
    let evaluated = congr(
        "IRStepResult",
        CONFIG,
        &scalar_result(),
        &comparison,
        returned,
        "(ir_byte_icmp_usize64_ugt_canonical_v1 a b aFits bFits)",
    );
    let guard = format!(
        "(ir_byte_function_and_true_v1 {} {}
      (ir_byte_usize64_value_fits_v1 ctx a aFits)
      (ir_byte_usize64_value_fits_v1 ctx b bFits))",
        fits(x),
        fits(y)
    );
    let after = after();
    let known = format!(
        "(ir_byte_case_true_v1 {CONFIG} (Bool.and {} {})
      (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) world)
      ({} {comparison}) {after} {guard} {evaluated})",
        fits(x),
        fits(y),
        scalar_result()
    );
    let fetched = format!(
        "(ir_byte_step_fetched_v1 W ctx providers current tail legacy cursor world
      function block {INSTRUCTION} {RESULTS} {} before functionFound blockFound nodeFound siteFound
      (@Eq.refl Bool Bool.true))",
        site()
    );
    format!(
        "def ir_byte_step_icmp_usize64_ugt_v1 {} :
@Eq {CONFIG} {} {after} := {}",
        common(),
        actual(),
        trans(
            CONFIG,
            &actual(),
            &exec,
            &after,
            &fetched,
            &trans(CONFIG, &exec, &operation(x, y), &after, &operands, &known)
        )
    )
}

impl Specification {
    pub(super) fn add_eval_ir_byte_usize_cmp_step_laws_v1(&mut self) -> Result<(), SpecError> {
        let execution = format!("(ir_byte_step_icmp_usize64_ugt_v1 {ARGS})");
        let observe = "(ir_byte_final_world_v1 W)";
        for (name, source) in [
            ("ir_byte_step_icmp_usize64_ugt_v1", step_source()),
            (
                "ir_byte_run_icmp_usize64_ugt_one_v1",
                format!(
                    "def ir_byte_run_icmp_usize64_ugt_one_v1 {} :
@Eq {CONFIG} (ir_byte_run_v1 W ctx providers 1 (@IRByteConfigV1.running W {MACHINE} world))
  {} := {execution}",
                    common(),
                    after()
                ),
            ),
            (
                "ir_byte_step_icmp_usize64_ugt_world_v1",
                format!(
                    "def ir_byte_step_icmp_usize64_ugt_world_v1 {} :
@Eq (IRByteWorldV1 W) ({observe} {}) world := {}",
                    common(),
                    actual(),
                    congr(
                        CONFIG,
                        "(IRByteWorldV1 W)",
                        observe,
                        &actual(),
                        &after(),
                        &execution
                    )
                ),
            ),
        ] {
            self.add_recursive_def(&source,
                "Checked fetched nominal Usize64/Ugt with exact input SSA/site and unchanged byte/host/owner world; no assumed execution or source/branch/abort authority.")
                .map_err(|error| with_declaration_name(name, error))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}
