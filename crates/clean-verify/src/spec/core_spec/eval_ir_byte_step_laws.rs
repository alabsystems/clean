// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked composition through the actual byte evaluator's fetch/step path.
//!
//! Every lookup is rooted in the same context and current frame. Lookup
//! equations are proof obligations, not trusted metadata. The Alloca consumer
//! derives its exact result and post-world validity from the existing checked
//! allocation laws; high-water and representation/native fidelity are not
//! inferred from world validity or from a function/block identifier.

use crate::spec::{SpecError, Specification};

const RESULT: &str = "(IRByteConfigV1 W)";
const MACHINE: &str = "(IRMachine.mk (@IRList.cons IRFrame current tail) legacy cursor)";
const FRAME_PARAMS: &str = "(current : IRFrame) (tail : IRList IRFrame)
  (legacy : IRList IRMemSlot) (cursor : Nat)";

fn fault(kind: &str, world: &str) -> String {
    format!("(@IRByteConfigV1.halted W ({kind}) {world})")
}

fn some(
    a: &str,
    option: &str,
    value: &str,
    failure: &str,
    success: &str,
    expected: &str,
    premise: &str,
    proof: &str,
) -> String {
    format!("(ir_byte_case_some_v1 {a} {RESULT} {option} {value} {failure} {success} {expected} {premise} {proof})")
}

fn truth(
    guard: &str,
    failure: &str,
    success: &str,
    expected: &str,
    premise: &str,
    proof: &str,
) -> String {
    format!(
        "(ir_byte_case_true_v1 {RESULT} {guard} {failure} {success} {expected} {premise} {proof})"
    )
}

fn function_lookup() -> &'static str {
    "(ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_frame_func current))"
}

fn block_lookup(function: &str) -> String {
    format!("(ir_block_find (ir_func_blocks {function}) (ir_frame_block current))")
}

fn node_lookup(block: &str) -> String {
    format!("(ir_nodes_get (ir_block_nodes {block}) (ir_frame_pc current))")
}

fn site_lookup() -> &'static str {
    "(ir_byte_site_v1 ctx (ir_frame_func current) (ir_frame_block current) (ir_frame_pc current))"
}

fn lookup_premises(node: &str, site: &str) -> String {
    format!(
        "(functionFound : @Eq (IROption IRFunc) {} (@IROption.some IRFunc function))
  (blockFound : @Eq (IROption IRBlock) {} (@IROption.some IRBlock block))
  (nodeFound : @Eq (IROption IRNode) {} (@IROption.some IRNode {node}))
  (siteFound : @Eq (IROption IRByteSiteV1) {} (@IROption.some IRByteSiteV1 {site}))",
        function_lookup(),
        block_lookup("function"),
        node_lookup("block"),
        site_lookup()
    )
}

fn fetched_source() -> (&'static str, String) {
    let expected =
        format!("(ir_byte_exec_v1 W ctx providers {MACHINE} world site instruction results)");
    let node = "(IRNode.mk instruction results)";
    let arity = |site: &str| {
        format!("(ir_nat_eqb (ir_byte_length_v1 Nat results) (ir_byte_length_v1 IRTy (ir_byte_site_results_v1 {site})))")
    };
    let bad_field = fault("IROutcome.type_error IRFault.bad_field", "world");
    let missing_node = fault("IROutcome.stuck IRFault.fetch_past_end", "world");
    let site_body = format!("(fun (foundSite : IRByteSiteV1) => @Bool.rec (fun (_ : Bool) => {RESULT})
      {bad_field} (ir_byte_exec_v1 W ctx providers {MACHINE} world foundSite instruction results) {})", arity("foundSite"));
    let leaf = truth(
        &arity("site"),
        &bad_field,
        &expected,
        &expected,
        "arity",
        &format!("(@Eq.refl {RESULT} {expected})"),
    );
    let site_proof = some(
        "IRByteSiteV1",
        site_lookup(),
        "site",
        &missing_node,
        &site_body,
        &expected,
        "siteFound",
        &leaf,
    );
    let node_body = format!("(fun (foundNode : IRNode) => ir_byte_step_node_v1 W ctx providers {MACHINE} world current foundNode)");
    let node_dispatch = |block: &str| {
        format!("(@IROption.rec IRNode (fun (_ : IROption IRNode) => {RESULT}) {missing_node} {node_body} {})", node_lookup(block))
    };
    let node_proof = some(
        "IRNode",
        &node_lookup("block"),
        node,
        &missing_node,
        &node_body,
        &expected,
        "nodeFound",
        &site_proof,
    );
    let missing_block = fault("IROutcome.stuck IRFault.no_block", "world");
    let block_body = format!(
        "(fun (foundBlock : IRBlock) => {})",
        node_dispatch("foundBlock")
    );
    let block_dispatch = |function: &str| {
        format!("(@IROption.rec IRBlock (fun (_ : IROption IRBlock) => {RESULT}) {missing_block} {block_body} {})", block_lookup(function))
    };
    let block_proof = some(
        "IRBlock",
        &block_lookup("function"),
        "block",
        &missing_block,
        &block_body,
        &expected,
        "blockFound",
        &node_proof,
    );
    let function_body = format!(
        "(fun (foundFunction : IRFunc) => {})",
        block_dispatch("foundFunction")
    );
    let function_proof = some(
        "IRFunc",
        function_lookup(),
        "function",
        &fault("IROutcome.stuck IRFault.no_func", "world"),
        &function_body,
        &expected,
        "functionFound",
        &block_proof,
    );
    let proof = truth(
        &format!("(ir_byte_world_valid_v1 W {MACHINE} world)"),
        &fault("IROutcome.type_error IRFault.bad_addr", "world"),
        &format!("(ir_byte_step_machine_v1 W ctx providers {MACHINE} world)"),
        &expected,
        "before",
        &function_proof,
    );
    (
        "ir_byte_step_fetched_v1",
        format!(
            "def ir_byte_step_fetched_v1
  (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)
  {FRAME_PARAMS} (world : IRByteWorldV1 W) (function : IRFunc) (block : IRBlock)
  (instruction : IRInst) (results : IRList Nat) (site : IRByteSiteV1)
  (before : @Eq Bool (ir_byte_world_valid_v1 W {MACHINE} world) Bool.true)
  {} (arity : @Eq Bool {} Bool.true) :
@Eq {RESULT} (ir_byte_step_v1 W ctx providers (@IRByteConfigV1.running W {MACHINE} world))
  {expected} := {proof}",
            lookup_premises(node, "site"),
            arity("site")
        ),
    )
}

fn frame16_sources() -> Vec<(&'static str, String)> {
    let base = "(ir_byte_aligned_base_v1 allocationCursor 8)";
    let ty = "(IRTy.array_ (IRTy.uint_ 8) 16)";
    let instruction = format!("(IRInst.alloca {ty} (@IROption.none Nat))");
    let results = "(@IRList.cons Nat destination (@IRList.nil Nat))";
    let types = "(@IRList.cons IRTy IRTy.ptr_ (@IRList.nil IRTy))";
    let node = format!("(IRNode.mk {instruction} {results})");
    let site = format!("(IRByteSiteV1.mk (ir_frame_func current) (ir_frame_block current) (ir_frame_pc current) 8 convention {types})");
    let layout = format!("(IRByteLayoutV1.mk {ty} 16 1 (@IRList.nil IRTy) (@IRList.nil Nat))");
    let world = "(@IRByteWorldV1.mk W (IRByteMemoryV1.mk allocs bytes allocationCursor) host (@IRList.cons Nat owner owners) next)";
    let fresh = format!("(ir_byte_fresh_memory_v1 allocs bytes {base} 16 owner)");
    let values = format!("(@IRList.cons IRScalar (IRScalar.ptr_ {base}) (@IRList.nil IRScalar))");
    let updated = format!("(ir_frame_advance (ir_frame_set_many current {results} {values}))");
    let expected = format!(
        "(@IRByteConfigV1.running W
      (IRMachine.mk (@IRList.cons IRFrame {updated} tail) legacy cursor)
      (ir_byte_with_memory_v1 W {world} {fresh}))"
    );
    let actual =
        format!("(ir_byte_step_v1 W ctx providers (@IRByteConfigV1.running W {MACHINE} {world}))");
    let helper = format!("(ir_byte_alloca_exec_v1 W ctx {MACHINE} {world} {results} {site} {ty} (@IROption.none Nat))");
    let common = format!("(W : Type) (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (allocationCursor : Nat) (host : W) (owner : Nat) (owners : IRList Nat) (next : Nat)
  {FRAME_PARAMS} (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)
  (destination convention : Nat) (function : IRFunc) (block : IRBlock)
  (cursorPositive : Nat.lt 0 allocationCursor)
  (room : Nat.lt (Nat.add {base} 16) ir_byte_limit_v1)
  (highWater : ir_byte_high_water_v1 allocs allocationCursor)
  (layoutFound : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx {ty}) (@IROption.some IRByteLayoutV1 {layout}))
  (before : @Eq Bool (ir_byte_world_valid_v1 W {MACHINE} {world}) Bool.true)
  {}", lookup_premises(&node, &site));
    let fetched = format!("(ir_byte_step_fetched_v1 W ctx providers current tail legacy cursor {world}
      function block {instruction} {results} {site} before functionFound blockFound nodeFound siteFound (@Eq.refl Bool Bool.true))");
    let helper_args =
        "W allocs bytes allocationCursor host owner owners next current tail legacy cursor ctx
      destination (ir_frame_func current) (ir_frame_block current) (ir_frame_pc current) convention
      cursorPositive room highWater layoutFound";
    let predicate = "(fun (c : IRByteConfigV1 W) => @IRByteConfigV1.rec W (fun (_ : IRByteConfigV1 W) => Prop)
      (fun (s : IRMachine) (w : IRByteWorldV1 W) => @Eq Bool (ir_byte_world_valid_v1 W s w) Bool.true)
      (fun (_ : IROutcome) (_ : IRByteWorldV1 W) => False) c)";
    vec![
        (
            "ir_byte_step_frame16_exact_v1",
            format!(
                "def ir_byte_step_frame16_exact_v1 {common} :
@Eq {RESULT} {actual} {expected} := @Eq.trans {RESULT} {actual} {helper} {expected}
  {fetched} (ir_byte_alloca_frame16_exact_v1 {helper_args})"
            ),
        ),
        (
            "ir_byte_step_frame16_world_v1",
            format!(
                "def ir_byte_step_frame16_world_v1 {common} :
{predicate} {actual} := @Eq.subst {RESULT} {predicate} {helper} {actual}
  (@Eq.symm {RESULT} {actual} {helper} {fetched})
  (ir_byte_alloca_frame16_world_v1 {helper_args} before)"
            ),
        ),
    ]
}

fn laws() -> Vec<(&'static str, String)> {
    let mut out = vec![fetched_source()];
    out.extend(frame16_sources());
    out
}

impl Specification {
    pub(super) fn add_eval_ir_byte_step_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(&source, "Checked actual module fetch/step composition; lookup and pre-world premises are kernel proof obligations, not metadata authority.")
                .map_err(|error| match error {
                    SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                    SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                    SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
                    other => other,
                })?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_step_tests.rs"]
mod tests;
