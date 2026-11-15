// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fetched sequential fetch-add execution, including the actual result SSA id,
//! next program counter and complete post-world. The byte representation law
//! derives primitive success; no successful-result or post-validity premise
//! replaces that proof. This machine has no interfering threads: attaching its
//! step to concurrent Rust still requires the separate ownership/interference
//! argument. Nothing here authenticates a reflected compiler module.

use super::eval_ir_byte_atomic::with_declaration_name;
use crate::spec::{SpecError, Specification};

const CONFIG: &str = "(IRByteConfigV1 W)";
const MACHINE: &str = "(IRMachine.mk (@IRList.cons IRFrame current tail) legacy cursor)";
const WORLD: &str = "(@IRByteWorldV1.mk W mem host owners next)";
const RESULTS: &str = "(@IRList.cons Nat destination (@IRList.nil Nat))";
const TYPES: &str = "(@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy))";
const INSTRUCTION: &str = "(IRInst.atomic_fetch_add_relaxed_u64_seq pointer value)";
const LAYOUT: &str = "(IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat))";
const ARGS: &str = "W ctx providers current tail legacy cursor mem host owners next
  pointer value destination alignment convention function block p n delta
  location_bounded layout_found accessible rep sum_bounded before
  pointerFound valueFound functionFound blockFound nodeFound siteFound";

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
  (mem : IRByteMemoryV1) (host : W) (owners : IRList Nat) (next : Nat)
  (pointer value destination alignment convention : Nat) (function : IRFunc) (block : IRBlock)
  (p n delta : Nat)
  (location_bounded : Nat.lt p ir_byte_limit_v1)
  (layout_found : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx (IRTy.uint_ 64))
    (@IROption.some IRByteLayoutV1 {LAYOUT}))
  (accessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) p 8
    (ir_byte_effective_align_v1 8 (ir_byte_layout_align_v1 {LAYOUT}))) Bool.true)
  (rep : ir_byte_u64_rep_v1 mem p n)
  (sum_bounded : Nat.lt (Nat.add n delta) ir_byte_limit_v1)
  (before : @Eq Bool (ir_byte_world_valid_v1 W {MACHINE} {WORLD}) Bool.true)
  (pointerFound : @Eq IRScalar (ir_getd {MACHINE} pointer) (IRScalar.ptr_ p))
  (valueFound : @Eq IRScalar (ir_getd {MACHINE} value) (IRScalar.int_ delta))
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

fn written() -> &'static str {
    "(IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 mem)
      (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) p 8 (Nat.add n delta))
      (ir_byte_mem_next_v1 mem))"
}

fn after() -> String {
    format!(
        "(@IRByteConfigV1.running W
      (IRMachine.mk (@IRList.cons IRFrame
        (ir_frame_advance (ir_frame_set_many current {RESULTS}
          (@IRList.cons IRScalar (IRScalar.int_ n) (@IRList.nil IRScalar)))) tail) legacy cursor)
      (ir_byte_with_memory_v1 W {WORLD} {}))",
        written()
    )
}

fn actual() -> String {
    format!("(ir_byte_step_v1 W ctx providers (@IRByteConfigV1.running W {MACHINE} {WORLD}))")
}

fn execution() -> String {
    format!("(ir_byte_step_fetch_add_relaxed_u64_seq_below_v1 {ARGS})")
}

fn trans(ty: &str, a: &str, b: &str, c: &str, ab: &str, bc: &str) -> String {
    format!("(@Eq.trans {ty} {a} {b} {c} {ab} {bc})")
}

fn congr(a: &str, b: &str, f: &str, x: &str, y: &str, equality: &str) -> String {
    format!("(ir_eq_cong {a} {b} {f} {x} {y} {equality})")
}

fn step_source() -> String {
    let op = format!(
        "(ir_byte_fetch_add_relaxed_u64_seq_v1 ctx
      (ir_getd {MACHINE} pointer) (ir_getd {MACHINE} value) mem)"
    );
    let at_pointer = format!(
        "(ir_byte_fetch_add_relaxed_u64_seq_v1 ctx
      (IRScalar.ptr_ p) (ir_getd {MACHINE} value) mem)"
    );
    let known =
        "(ir_byte_fetch_add_relaxed_u64_seq_v1 ctx (IRScalar.ptr_ p) (IRScalar.int_ delta) mem)";
    let returned = format!(
        "(IRByteMemoryResultV1.value (IRScalar.int_ n) {})",
        written()
    );
    let operand_proof = trans("IRByteMemoryResultV1", &op, &at_pointer, known,
      &congr("IRScalar", "IRByteMemoryResultV1",
        &format!("(fun (ptr : IRScalar) => ir_byte_fetch_add_relaxed_u64_seq_v1 ctx ptr (ir_getd {MACHINE} value) mem)"),
        &format!("(ir_getd {MACHINE} pointer)"), "(IRScalar.ptr_ p)", "pointerFound"),
      &congr("IRScalar", "IRByteMemoryResultV1",
        "(fun (deltaValue : IRScalar) => ir_byte_fetch_add_relaxed_u64_seq_v1 ctx (IRScalar.ptr_ p) deltaValue mem)",
        &format!("(ir_getd {MACHINE} value)"), "(IRScalar.int_ delta)", "valueFound"));
    let evaluated = trans(
        "IRByteMemoryResultV1",
        &op,
        known,
        &returned,
        &operand_proof,
        "(ir_byte_fetch_add_relaxed_u64_seq_below_v1 ctx mem p n delta
        location_bounded layout_found accessible rep sum_bounded)",
    );
    let memory_result =
        format!("(ir_byte_memory_result_v1 W ctx {MACHINE} {WORLD} {RESULTS} {TYPES} Bool.false)");
    let exec = format!(
        "(ir_byte_exec_v1 W ctx providers {MACHINE} {WORLD} {} {INSTRUCTION} {RESULTS})",
        site()
    );
    let bound = "(@Nat.le_trans (Nat.succ n) (Nat.succ (Nat.add n delta)) ir_byte_limit_v1
      (@Nat.succ_le_succ n (Nat.add n delta) (Nat.le_add_right n delta)) sum_bounded)";
    let fits = format!(
        "(ir_byte_u64_value_fits_v1 ctx n
      (ir_byte_ltb_of_lt_v1 n (ir_nat_pow2 64) {bound}))"
    );
    let guard = format!(
        "(Bool.and
      (ir_nat_eqb (ir_byte_length_v1 Nat {RESULTS})
        (ir_byte_length_v1 IRScalar (@IRList.cons IRScalar (IRScalar.int_ n) (@IRList.nil IRScalar))))
      (ir_byte_values_match_v1 ctx {TYPES}
        (@IRList.cons IRScalar (IRScalar.int_ n) (@IRList.nil IRScalar))))"
    );
    let guard_proof = congr(
        "Bool",
        "Bool",
        "(fun (b : Bool) => Bool.and Bool.true (Bool.and b Bool.true))",
        "(ir_byte_value_matches_v1 ctx (IRTy.uint_ 64) (IRScalar.int_ n))",
        "Bool.true",
        &fits,
    );
    let after = after();
    let binding = format!(
        "(ir_byte_case_true_v1 {CONFIG} {guard}
      (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field)
        (ir_byte_with_memory_v1 W {WORLD} {}))
      {after} {after} {guard_proof} (@Eq.refl {CONFIG} {after}))",
        written()
    );
    let exec_proof = trans(
        CONFIG,
        &exec,
        &format!("({memory_result} {returned})"),
        &after,
        &congr(
            "IRByteMemoryResultV1",
            CONFIG,
            &memory_result,
            &op,
            &returned,
            &evaluated,
        ),
        &binding,
    );
    let fetched = format!(
        "(ir_byte_step_fetched_v1 W ctx providers current tail legacy cursor {WORLD}
      function block {INSTRUCTION} {RESULTS} {} before functionFound blockFound nodeFound siteFound
      (@Eq.refl Bool Bool.true))",
        site()
    );
    format!(
        "def ir_byte_step_fetch_add_relaxed_u64_seq_below_v1 {} :
      @Eq {CONFIG} {} {after} := {}",
        common(),
        actual(),
        trans(CONFIG, &actual(), &exec, &after, &fetched, &exec_proof)
    )
}

fn observation(frame: bool) -> (&'static str, String) {
    let (name, extra, size, base, expected, law) = if frame {
        ("ir_byte_step_fetch_add_relaxed_u64_seq_frame_v1",
         "(readBase readSize : Nat)
  (apart : Or (Nat.le (Nat.add readBase readSize) p) (Nat.le (Nat.add p 8) readBase))",
         "readSize", "readBase",
         "(ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) readSize readBase)",
         "(ir_byte_read_write_disjoint_v1 (ir_byte_mem_bytes_v1 mem) readBase readSize p 8 (Nat.add n delta) apart)")
    } else {
        ("ir_byte_step_fetch_add_relaxed_u64_seq_new_v1", "", "8", "p",
         "(@IROption.some Nat (Nat.add n delta))",
         "(ir_byte_read_write_eight_v1 (ir_byte_mem_bytes_v1 mem) p (Nat.add n delta) sum_bounded)")
    };
    let observe = format!("(fun (c : {CONFIG}) => ir_byte_read_word_v1
      (ir_byte_mem_bytes_v1 (ir_byte_world_memory_v1 W (ir_byte_final_world_v1 W c))) {size} {base})");
    let actual = format!("({observe} {})", actual());
    let middle = format!("({observe} {})", after());
    let proof = congr(
        CONFIG,
        "(IROption Nat)",
        &observe,
        &self::actual(),
        &after(),
        &execution(),
    );
    (
        name,
        format!(
            "def {name} {} {extra} :
      @Eq (IROption Nat) {actual} {expected} := {}",
            common(),
            trans("(IROption Nat)", &actual, &middle, expected, &proof, law)
        ),
    )
}

pub(super) fn laws() -> Vec<(&'static str, String)> {
    let predicate = format!("(fun (c : {CONFIG}) => @IRByteConfigV1.rec W (fun (_ : {CONFIG}) => Prop)
      (fun (s : IRMachine) (w : IRByteWorldV1 W) => @Eq Bool (ir_byte_world_valid_v1 W s w) Bool.true)
      (fun (_ : IROutcome) (_ : IRByteWorldV1 W) => False) c)");
    vec![
        (
            "ir_byte_step_fetch_add_relaxed_u64_seq_below_v1",
            step_source(),
        ),
        (
            "ir_byte_run_fetch_add_relaxed_u64_seq_one_v1",
            format!(
                "def ir_byte_run_fetch_add_relaxed_u64_seq_one_v1 {} :
  @Eq {CONFIG} (ir_byte_run_v1 W ctx providers 1 (@IRByteConfigV1.running W {MACHINE} {WORLD}))
    {} := {}",
                common(),
                after(),
                execution()
            ),
        ),
        (
            "ir_byte_step_fetch_add_relaxed_u64_seq_world_v1",
            format!(
                "def ir_byte_step_fetch_add_relaxed_u64_seq_world_v1 {} :
  {predicate} {} := @Eq.subst {CONFIG} {predicate} {} {}
    (@Eq.symm {CONFIG} {} {} {}) before",
                common(),
                actual(),
                after(),
                actual(),
                actual(),
                after(),
                execution()
            ),
        ),
        observation(false),
        observation(true),
    ]
}

impl Specification {
    pub(super) fn add_eval_ir_byte_atomic_step_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(&source,
                "Checked fetched sequential fetch-add: exact old-result SSA binding, byte update, continuation and world; no concurrent or source-reflection authority.")
                .map_err(|error| with_declaration_name(name, error))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}
