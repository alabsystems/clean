// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The strict_monads chain — the first over a MUTATING body, the first with
//! a `store`, and the first with a VOID return:
//! `env::Environment::set_lean4_core_strict_monads`.**
//!
//! ```text
//! rustcc fn @env::Environment::set_lean4_core_strict_monads(functy.404) {
//!     ; #names: %0="self", %1="strict"
//! bb0(%0: ptr, %1: bool):
//!     %2 = load struct.441, ptr %0
//!     %3 = insertfield struct.441 %2, 81, %1
//!     store struct.441 %3, ptr %0
//!     ret
//! }
//! ```
//!
//! Four instructions, and three of them are firsts for the chain program: no
//! earlier chained body WRITES memory, none carries an `insertfield` the gate
//! could compare (the lane landed 2026-08-20, ahead of this chain), and none
//! returns void. The outcome of this body is deliberately information-free —
//! `IROutcome.ret []` — so the theorem with content is about the HEAP:
//!
//! * **A4, outcome half** (`ir_sm_correct`): for every heap holding a live
//!   Environment aggregate of at least 82 fields at the receiver's address,
//!   every Bool, every next-address counter and every fuel ≥ 4, the machine
//!   returns void.
//! * **A4, heap half** (`ir_sm_writes_field81` / `ir_sm_final_mem`): after
//!   exactly 3 steps the machine's memory IS
//!   `ir_mem_update mem a (env_set_strict_monads sp b)` — the same heap whose
//!   receiver cell holds the same aggregate with FIELD 81 replaced by the Bool
//!   argument. Stated at `ir_steps`, because the machine's `ret` discards the
//!   heap and `ir_eval` therefore cannot see the mutation.
//! * **A5, both halves, FULL SYMBOLIC** (`ir_sm_machine_sound`,
//!   `ir_sm_config_sound`): any returned value is `[]` (at every fuel >= 4 —
//!   `Le ir_d4 fuel`, the cost of the body's four instructions, below which
//!   `ret` is unreachable and the claim is about nothing), and any 3-step
//!   configuration is the updated-heap machine. The float trio's A5 split does
//!   NOT apply here, and the reason is measured in kind rather than assumed:
//!   their wall is defeq descending into the `*_fin` rounding pipeline at
//!   symbolic operands, while this body's only value-level computation,
//!   `ir_vals_set` on a SYMBOLIC spine, is inert (an `IRScalar.rec` stuck on
//!   its major premise) and no theorem here ever needs to reduce it. Measured
//!   in the EvalIR scratchpad (2026-08-20, 61/61 PASS in one run): all 55
//!   declarations elaborate and kernel-check in ~5.5 s of declaration time;
//!   A4's outcome half costs 0.400 s, its heap half 0.446 s, the two A5
//!   inversions 0.116 s / 0.087 s, and the only declarations over a second
//!   are the two CONCRETE spines (the 82-cell probe, 1.39 s; the 81-cell
//!   boundary, 1.30 s).
//! * **Field preservation, symbolic where it counts**
//!   (`ir_sm_write_replaces_only_81` + the four `preserves` lemmas): over an
//!   82-field probe spine with symbolic slots 0/40/80/81 and a symbolic tail,
//!   the write replaces slot 81 and provably nothing else — `Eq.refl`, kernel
//!   computed. A statement over a FULLY symbolic spine would need
//!   `ir_vals_get`/`ir_vals_set` commutation inductions nobody has earned;
//!   the probe form is the affordable strength, and it is stated as such.
//!
//! ## Quantifying over 82-field aggregates: what was measured
//!
//! The bounds check `ir_nat_ltb 81 (ir_vals_len sp)` is stuck on a symbolic
//! spine, so A4 does not case on the spine at all: the representation premise
//! `EncodesEnvRef` carries the length fact as an EQUATION and one `Eq.subst`
//! rewrites the check to `Bool.true`. That keeps A4's spine quantification
//! TOTAL over all `≥ 82`-field aggregates (any values, any tail) at symbolic
//! defeq cost — the 82-cell shape is never unrolled in the symbolic theorems,
//! only in the concrete witnesses, where the kernel computes it directly.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `env_set_strict_monads` is a SPINE-level specification: slot 81 of the
//! struct.441 aggregate. That slot IS where trustc lays out the
//! `lean4_core_strict_monads: bool` field of `env::Environment` in this
//! artifact — the fixture's `insertfield … 81` says so — but no theorem here
//! proves the layout correspondence between the Rust struct and the spine;
//! that is the same open layout obligation every chain states
//! (`EncodesFlatFlags`'s comment is the canonical form). The producer's
//! interpreter differential is NOT-RUN on this body (0 samples — recorded in
//! `strict_monads.lineage.json`); the evidence is `agreed` + `markers_exact`
//! (2 real marker lines) + flip-lineage equality + the kernel-executed
//! witnesses HERE, and nothing in this module claims interpreter agreement.
//! The link between the proved module and the emitted one is STRUCTURAL
//! (`tests/crystal_a1_lineage/strict_monads.rs`); everything past the flip
//! seam is downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// Shared helpers REUSED, not re-declared (the eighth chain's one real error):
// `ir_vl2` (contains stage), `ir_run_le_ret` (fuel stage), `ir_outcome_is_ret`
// (correct stage), `ir_cfg_mach` (bvar_range stage), `ir_cell` / `ir_sp0` /
// `ir_mem0` (crystal stage). This stage must therefore register AFTER all of
// them — see the CoreSpecStage comment in bundles.rs.

// ── the reflected write, its type, its representation premise ─────────
const SRC_IR_SM_TENV: &str = "def ir_sm_tenv : IRTy := IRTy.struct_ 441";

const SRC_ENV_SET_STRICT_MONADS: &str = "def env_set_strict_monads (sp : IRScalar) (b : Bool) : IRScalar := IRScalar.aggv (ir_vals_set sp 81 (IRScalar.bool_ b))";

const SRC_ENCODESENVREF: &str = "inductive EncodesEnvRef (mem : IRList IRMemSlot) : IRScalar -> IRScalar -> Type\n| mk : forall (a : Nat) (sp : IRScalar), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) -> Eq Bool (ir_nat_ltb 81 (ir_vals_len sp)) Bool.true -> EncodesEnvRef mem (IRScalar.ptr_ a) sp";

// ── the emitted module, transcribed ───────────────────────────────────
const SRC_IR_SM_B0: &str = "def ir_sm_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (ir_nd1 (IRInst.load ir_sm_tenv ir_d0 Bool.false) ir_d2) (ir_bd3 (ir_nd1 (IRInst.insertfield ir_sm_tenv ir_d2 81 ir_d1) ir_d3) (ir_nd (IRInst.store ir_sm_tenv ir_d0 ir_d3 Bool.false)) (ir_nd (IRInst.ret ir_nl0))))";

const SRC_IR_SM_FUNC: &str = "def ir_sm_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_sm_b0 ir_blk0)";

const SRC_IR_SM_MODULE: &str = "def ir_sm_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_sm_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── the machine, step by step ─────────────────────────────────────────
const SRC_IR_SM_MACH0: &str = "def ir_sm_mach0 (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl2 ir_d0 ir_d1) (ir_vl2 (IRScalar.ptr_ a) (IRScalar.bool_ b)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_SM_AFTER_LOAD: &str = "def ir_sm_after_load (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (o : IROption IRMemSlot) : IRConfig := ir_bind_result (ir_sm_mach0 mem a b na) (ir_nl1 ir_d2) (ir_load_slot o)";

const SRC_IR_SM_LOCALS1: &str = "def ir_sm_locals1 (a : Nat) (b : Bool) (sp : IRScalar) : IRList IRBinding := IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.aggv sp)) (ir_bind_params (ir_nl2 ir_d0 ir_d1) (ir_vl2 (IRScalar.ptr_ a) (IRScalar.bool_ b)) (IRList.nil IRBinding))";

const SRC_IR_SM_M1: &str = "def ir_sm_m1 (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 ir_d1 (ir_sm_locals1 a b sp) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_SM_AFTER_INSERT: &str = "def ir_sm_after_insert (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) (t : Bool) : IRConfig := ir_bind_result (ir_sm_m1 mem a b na sp) (ir_nl1 ir_d3) (Bool.rec (fun (_ : Bool) => IRStepResult) (IRStepResult.fault (IROutcome.type_error IRFault.bad_field)) (IRStepResult.value (env_set_strict_monads sp b)) t)";

const SRC_IR_SM_LOCALS2: &str = "def ir_sm_locals2 (a : Nat) (b : Bool) (sp : IRScalar) : IRList IRBinding := IRList.cons IRBinding (IRBinding.mk ir_d3 (env_set_strict_monads sp b)) (ir_sm_locals1 a b sp)";

const SRC_IR_SM_M2: &str = "def ir_sm_m2 (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 ir_d2 (ir_sm_locals2 a b sp) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_SM_AFTER_STORE: &str = "def ir_sm_after_store (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) (o : IROption IRMemSlot) : IRConfig := ir_store_checked (ir_sm_m2 mem a b na sp) a (env_set_strict_monads sp b) o";

const SRC_IR_SM_HEAP_AFTER: &str = "def ir_sm_heap_after (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (sp : IRScalar) : IRList IRMemSlot := ir_mem_update mem a (env_set_strict_monads sp b)";

const SRC_IR_SM_M3: &str = "def ir_sm_m3 (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 ir_d3 (ir_sm_locals2 a b sp) (IRList.nil Nat)) (IRList.nil IRFrame)) (ir_sm_heap_after mem a b sp) na";

// ── the four transitions, each identified by Eq.refl ──────────────────
const SRC_IR_SM_STEP1: &str = "def ir_sm_step1 (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) : Eq IRConfig (ir_steps ir_d1 ir_sm_module (IRConfig.running (ir_sm_mach0 mem a b na))) (ir_sm_after_load mem a b na (ir_mem_lookup mem a)) := Eq.refl IRConfig (ir_sm_after_load mem a b na (ir_mem_lookup mem a))";

const SRC_IR_SM_LOAD_BINDS: &str = "def ir_sm_load_binds (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : Eq IRConfig (ir_sm_after_load mem a b na (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true))) (IRConfig.running (ir_sm_m1 mem a b na sp)) := Eq.refl IRConfig (IRConfig.running (ir_sm_m1 mem a b na sp))";

const SRC_IR_SM_STEP2: &str = "def ir_sm_step2 (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : Eq IRConfig (ir_steps ir_d1 ir_sm_module (IRConfig.running (ir_sm_m1 mem a b na sp))) (ir_sm_after_insert mem a b na sp (ir_nat_ltb 81 (ir_vals_len sp))) := Eq.refl IRConfig (ir_sm_after_insert mem a b na sp (ir_nat_ltb 81 (ir_vals_len sp)))";

const SRC_IR_SM_INSERT_IN_BOUNDS: &str = "def ir_sm_insert_in_bounds (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : Eq IRConfig (ir_sm_after_insert mem a b na sp Bool.true) (IRConfig.running (ir_sm_m2 mem a b na sp)) := Eq.refl IRConfig (IRConfig.running (ir_sm_m2 mem a b na sp))";

const SRC_IR_SM_INSERT_OUT_OF_BOUNDS: &str = "def ir_sm_insert_out_of_bounds (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : Eq IRConfig (ir_sm_after_insert mem a b na sp Bool.false) (IRConfig.halted (IROutcome.type_error IRFault.bad_field)) := Eq.refl IRConfig (IRConfig.halted (IROutcome.type_error IRFault.bad_field))";

const SRC_IR_SM_STEP3: &str = "def ir_sm_step3 (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : Eq IRConfig (ir_steps ir_d1 ir_sm_module (IRConfig.running (ir_sm_m2 mem a b na sp))) (ir_sm_after_store mem a b na sp (ir_mem_lookup mem a)) := Eq.refl IRConfig (ir_sm_after_store mem a b na sp (ir_mem_lookup mem a))";

const SRC_IR_SM_STORE_COMMITS: &str = "def ir_sm_store_commits (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : Eq IRConfig (ir_sm_after_store mem a b na sp (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true))) (IRConfig.running (ir_sm_m3 mem a b na sp)) := Eq.refl IRConfig (IRConfig.running (ir_sm_m3 mem a b na sp))";

const SRC_IR_SM_STORE_ON_MISSING_CELL: &str = "def ir_sm_store_on_missing_cell (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : Eq IRConfig (ir_sm_after_store mem a b na sp (IROption.none IRMemSlot)) (IRConfig.halted (IROutcome.ub IRFault.bad_addr)) := Eq.refl IRConfig (IRConfig.halted (IROutcome.ub IRFault.bad_addr))";

const SRC_IR_SM_RET_IS_VOID: &str = "def ir_sm_ret_is_void (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) : Eq IROutcome (ir_run ir_d1 ir_sm_module (IRConfig.running (ir_sm_m3 mem a b na sp))) (IROutcome.ret ir_vl0) := Eq.refl IROutcome (IROutcome.ret ir_vl0)";

// ── A4 (outcome + heap), A5, and the corollaries ──────────────────────
const SRC_IR_SM_EXACT: &str = "def ir_sm_exact (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) (hmem : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true))) (hlen : Eq Bool (ir_nat_ltb 81 (ir_vals_len sp)) Bool.true) : Eq IROutcome (ir_run ir_d4 ir_sm_module (IRConfig.running (ir_sm_mach0 mem a b na))) (IROutcome.ret ir_vl0) := Eq.subst (IROption IRMemSlot) (fun (o : IROption IRMemSlot) => Eq IROutcome (ir_run ir_d3 ir_sm_module (ir_sm_after_load mem a b na o)) (IROutcome.ret ir_vl0)) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) hmem) (Eq.subst Bool (fun (t : Bool) => Eq IROutcome (ir_run ir_d2 ir_sm_module (ir_sm_after_insert mem a b na sp t)) (IROutcome.ret ir_vl0)) Bool.true (ir_nat_ltb 81 (ir_vals_len sp)) (Eq.symm Bool (ir_nat_ltb 81 (ir_vals_len sp)) Bool.true hlen) (Eq.subst (IROption IRMemSlot) (fun (o : IROption IRMemSlot) => Eq IROutcome (ir_run ir_d1 ir_sm_module (ir_sm_after_store mem a b na sp o)) (IROutcome.ret ir_vl0)) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) hmem) (Eq.refl IROutcome (IROutcome.ret ir_vl0))))";

const SRC_IR_SM_CORRECT: &str = "def ir_sm_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (sp : IRScalar) (b : Bool) (henc : EncodesEnvRef mem r sp) : Le ir_d4 fuel -> Eq IROutcome (ir_eval fuel ir_sm_module ir_d0 (ir_vl2 r (IRScalar.bool_ b)) mem na) (IROutcome.ret ir_vl0) := EncodesEnvRef.rec mem (fun (r0 : IRScalar) (sp0 : IRScalar) (_ : EncodesEnvRef mem r0 sp0) => Le ir_d4 fuel -> Eq IROutcome (ir_eval fuel ir_sm_module ir_d0 (ir_vl2 r0 (IRScalar.bool_ b)) mem na) (IROutcome.ret ir_vl0)) (fun (a : Nat) (sp0 : IRScalar) (hmem : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp0) Bool.true))) (hlen : Eq Bool (ir_nat_ltb 81 (ir_vals_len sp0)) Bool.true) (hle : Le ir_d4 fuel) => ir_run_le_ret ir_sm_module ir_d4 fuel hle (IRConfig.running (ir_sm_mach0 mem a b na)) ir_vl0 (ir_sm_exact mem a b na sp0 hmem hlen)) r sp henc";

const SRC_IR_SM_WRITES_FIELD81: &str = "def ir_sm_writes_field81 (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) (hmem : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true))) (hlen : Eq Bool (ir_nat_ltb 81 (ir_vals_len sp)) Bool.true) : Eq IRConfig (ir_steps ir_d3 ir_sm_module (IRConfig.running (ir_sm_mach0 mem a b na))) (IRConfig.running (ir_sm_m3 mem a b na sp)) := Eq.subst (IROption IRMemSlot) (fun (o : IROption IRMemSlot) => Eq IRConfig (ir_steps ir_d2 ir_sm_module (ir_sm_after_load mem a b na o)) (IRConfig.running (ir_sm_m3 mem a b na sp))) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) hmem) (Eq.subst Bool (fun (t : Bool) => Eq IRConfig (ir_steps ir_d1 ir_sm_module (ir_sm_after_insert mem a b na sp t)) (IRConfig.running (ir_sm_m3 mem a b na sp))) Bool.true (ir_nat_ltb 81 (ir_vals_len sp)) (Eq.symm Bool (ir_nat_ltb 81 (ir_vals_len sp)) Bool.true hlen) (Eq.subst (IROption IRMemSlot) (fun (o : IROption IRMemSlot) => Eq IRConfig (ir_sm_after_store mem a b na sp o) (IRConfig.running (ir_sm_m3 mem a b na sp))) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true)) hmem) (Eq.refl IRConfig (IRConfig.running (ir_sm_m3 mem a b na sp))))))";

const SRC_IR_SM_FINAL_MEM: &str = "def ir_sm_final_mem (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) (hmem : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true))) (hlen : Eq Bool (ir_nat_ltb 81 (ir_vals_len sp)) Bool.true) : Eq (IRList IRMemSlot) (ir_mach_mem (ir_cfg_mach (ir_steps ir_d3 ir_sm_module (IRConfig.running (ir_sm_mach0 mem a b na))) (ir_sm_mach0 mem a b na))) (ir_sm_heap_after mem a b sp) := Eq.cong IRConfig (IRList IRMemSlot) (fun (c : IRConfig) => ir_mach_mem (ir_cfg_mach c (ir_sm_mach0 mem a b na))) (ir_steps ir_d3 ir_sm_module (IRConfig.running (ir_sm_mach0 mem a b na))) (IRConfig.running (ir_sm_m3 mem a b na sp)) (ir_sm_writes_field81 mem a b na sp hmem hlen)";

const SRC_IR_SM_RET_PAYLOAD: &str = "def ir_sm_ret_payload (o : IROutcome) : IRList IRScalar := IROutcome.rec (fun (_ : IROutcome) => IRList IRScalar) (fun (v : IRList IRScalar) => v) (fun (_ : IRFault) => ir_vl0) (fun (_ : IRFault) => ir_vl0) (fun (_ : IRFault) => ir_vl0) (fun (_ : IRFault) => ir_vl0) ir_vl0 o";

const SRC_IR_SM_MACHINE_SOUND: &str = "def ir_sm_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (sp : IRScalar) (b : Bool) (v : IRList IRScalar) (henc : EncodesEnvRef mem r sp) (hle : Le ir_d4 fuel) (hret : Eq IROutcome (ir_eval fuel ir_sm_module ir_d0 (ir_vl2 r (IRScalar.bool_ b)) mem na) (IROutcome.ret v)) : Eq (IRList IRScalar) ir_vl0 v := Eq.cong IROutcome (IRList IRScalar) ir_sm_ret_payload (IROutcome.ret ir_vl0) (IROutcome.ret v) (Eq.trans IROutcome (IROutcome.ret ir_vl0) (ir_eval fuel ir_sm_module ir_d0 (ir_vl2 r (IRScalar.bool_ b)) mem na) (IROutcome.ret v) (Eq.symm IROutcome (ir_eval fuel ir_sm_module ir_d0 (ir_vl2 r (IRScalar.bool_ b)) mem na) (IROutcome.ret ir_vl0) (ir_sm_correct mem fuel na r sp b henc hle)) hret)";

const SRC_IR_SM_CONFIG_SOUND: &str = "def ir_sm_config_sound (mem : IRList IRMemSlot) (a : Nat) (b : Bool) (na : Nat) (sp : IRScalar) (c : IRConfig) (hmem : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv sp) Bool.true))) (hlen : Eq Bool (ir_nat_ltb 81 (ir_vals_len sp)) Bool.true) (hc : Eq IRConfig (ir_steps ir_d3 ir_sm_module (IRConfig.running (ir_sm_mach0 mem a b na))) c) : Eq IRConfig (IRConfig.running (ir_sm_m3 mem a b na sp)) c := Eq.trans IRConfig (IRConfig.running (ir_sm_m3 mem a b na sp)) (ir_steps ir_d3 ir_sm_module (IRConfig.running (ir_sm_mach0 mem a b na))) c (Eq.symm IRConfig (ir_steps ir_d3 ir_sm_module (IRConfig.running (ir_sm_mach0 mem a b na))) (IRConfig.running (ir_sm_m3 mem a b na sp)) (ir_sm_writes_field81 mem a b na sp hmem hlen)) hc";

const SRC_IR_SM_NEVER_FAULTS: &str = "def ir_sm_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (sp : IRScalar) (b : Bool) (henc : EncodesEnvRef mem r sp) (hle : Le ir_d4 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_sm_module ir_d0 (ir_vl2 r (IRScalar.bool_ b)) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_sm_module ir_d0 (ir_vl2 r (IRScalar.bool_ b)) mem na) (IROutcome.ret ir_vl0) (ir_sm_correct mem fuel na r sp b henc hle)";

// ── the 82-field probe and the kernel-executed witnesses ──────────────
const SRC_IR_SM_PROBE: &str = "def ir_sm_probe (x0 : IRScalar) (x40 : IRScalar) (x80 : IRScalar) (x81 : IRScalar) (rest : IRScalar) : IRScalar := IRScalar.vcons x0 (IRScalar.vcons (IRScalar.int_ 1) (IRScalar.vcons (IRScalar.int_ 2) (IRScalar.vcons (IRScalar.int_ 3) (IRScalar.vcons (IRScalar.int_ 4) (IRScalar.vcons (IRScalar.int_ 5) (IRScalar.vcons (IRScalar.int_ 6) (IRScalar.vcons (IRScalar.int_ 7) (IRScalar.vcons (IRScalar.int_ 8) (IRScalar.vcons (IRScalar.int_ 9) (IRScalar.vcons (IRScalar.int_ 10) (IRScalar.vcons (IRScalar.int_ 11) (IRScalar.vcons (IRScalar.int_ 12) (IRScalar.vcons (IRScalar.int_ 13) (IRScalar.vcons (IRScalar.int_ 14) (IRScalar.vcons (IRScalar.int_ 15) (IRScalar.vcons (IRScalar.int_ 16) (IRScalar.vcons (IRScalar.int_ 17) (IRScalar.vcons (IRScalar.int_ 18) (IRScalar.vcons (IRScalar.int_ 19) (IRScalar.vcons (IRScalar.int_ 20) (IRScalar.vcons (IRScalar.int_ 21) (IRScalar.vcons (IRScalar.int_ 22) (IRScalar.vcons (IRScalar.int_ 23) (IRScalar.vcons (IRScalar.int_ 24) (IRScalar.vcons (IRScalar.int_ 25) (IRScalar.vcons (IRScalar.int_ 26) (IRScalar.vcons (IRScalar.int_ 27) (IRScalar.vcons (IRScalar.int_ 28) (IRScalar.vcons (IRScalar.int_ 29) (IRScalar.vcons (IRScalar.int_ 30) (IRScalar.vcons (IRScalar.int_ 31) (IRScalar.vcons (IRScalar.int_ 32) (IRScalar.vcons (IRScalar.int_ 33) (IRScalar.vcons (IRScalar.int_ 34) (IRScalar.vcons (IRScalar.int_ 35) (IRScalar.vcons (IRScalar.int_ 36) (IRScalar.vcons (IRScalar.int_ 37) (IRScalar.vcons (IRScalar.int_ 38) (IRScalar.vcons (IRScalar.int_ 39) (IRScalar.vcons x40 (IRScalar.vcons (IRScalar.int_ 41) (IRScalar.vcons (IRScalar.int_ 42) (IRScalar.vcons (IRScalar.int_ 43) (IRScalar.vcons (IRScalar.int_ 44) (IRScalar.vcons (IRScalar.int_ 45) (IRScalar.vcons (IRScalar.int_ 46) (IRScalar.vcons (IRScalar.int_ 47) (IRScalar.vcons (IRScalar.int_ 48) (IRScalar.vcons (IRScalar.int_ 49) (IRScalar.vcons (IRScalar.int_ 50) (IRScalar.vcons (IRScalar.int_ 51) (IRScalar.vcons (IRScalar.int_ 52) (IRScalar.vcons (IRScalar.int_ 53) (IRScalar.vcons (IRScalar.int_ 54) (IRScalar.vcons (IRScalar.int_ 55) (IRScalar.vcons (IRScalar.int_ 56) (IRScalar.vcons (IRScalar.int_ 57) (IRScalar.vcons (IRScalar.int_ 58) (IRScalar.vcons (IRScalar.int_ 59) (IRScalar.vcons (IRScalar.int_ 60) (IRScalar.vcons (IRScalar.int_ 61) (IRScalar.vcons (IRScalar.int_ 62) (IRScalar.vcons (IRScalar.int_ 63) (IRScalar.vcons (IRScalar.int_ 64) (IRScalar.vcons (IRScalar.int_ 65) (IRScalar.vcons (IRScalar.int_ 66) (IRScalar.vcons (IRScalar.int_ 67) (IRScalar.vcons (IRScalar.int_ 68) (IRScalar.vcons (IRScalar.int_ 69) (IRScalar.vcons (IRScalar.int_ 70) (IRScalar.vcons (IRScalar.int_ 71) (IRScalar.vcons (IRScalar.int_ 72) (IRScalar.vcons (IRScalar.int_ 73) (IRScalar.vcons (IRScalar.int_ 74) (IRScalar.vcons (IRScalar.int_ 75) (IRScalar.vcons (IRScalar.int_ 76) (IRScalar.vcons (IRScalar.int_ 77) (IRScalar.vcons (IRScalar.int_ 78) (IRScalar.vcons (IRScalar.int_ 79) (IRScalar.vcons x80 (IRScalar.vcons x81 rest)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))";

const SRC_IR_SM_ENV0: &str = "def ir_sm_env0 : IRScalar := ir_sm_probe (IRScalar.int_ 100) (IRScalar.int_ 140) (IRScalar.int_ 180) (IRScalar.bool_ Bool.false) IRScalar.vnil";

const SRC_IR_SM_HEAP0: &str =
    "def ir_sm_heap0 : IRList IRMemSlot := ir_cell ir_d0 (IRScalar.aggv ir_sm_env0) ir_mem0";

const SRC_IR_SM_SPINE81: &str = "def ir_sm_spine81 : IRScalar := IRScalar.vcons (IRScalar.int_ 0) (IRScalar.vcons (IRScalar.int_ 1) (IRScalar.vcons (IRScalar.int_ 2) (IRScalar.vcons (IRScalar.int_ 3) (IRScalar.vcons (IRScalar.int_ 4) (IRScalar.vcons (IRScalar.int_ 5) (IRScalar.vcons (IRScalar.int_ 6) (IRScalar.vcons (IRScalar.int_ 7) (IRScalar.vcons (IRScalar.int_ 8) (IRScalar.vcons (IRScalar.int_ 9) (IRScalar.vcons (IRScalar.int_ 10) (IRScalar.vcons (IRScalar.int_ 11) (IRScalar.vcons (IRScalar.int_ 12) (IRScalar.vcons (IRScalar.int_ 13) (IRScalar.vcons (IRScalar.int_ 14) (IRScalar.vcons (IRScalar.int_ 15) (IRScalar.vcons (IRScalar.int_ 16) (IRScalar.vcons (IRScalar.int_ 17) (IRScalar.vcons (IRScalar.int_ 18) (IRScalar.vcons (IRScalar.int_ 19) (IRScalar.vcons (IRScalar.int_ 20) (IRScalar.vcons (IRScalar.int_ 21) (IRScalar.vcons (IRScalar.int_ 22) (IRScalar.vcons (IRScalar.int_ 23) (IRScalar.vcons (IRScalar.int_ 24) (IRScalar.vcons (IRScalar.int_ 25) (IRScalar.vcons (IRScalar.int_ 26) (IRScalar.vcons (IRScalar.int_ 27) (IRScalar.vcons (IRScalar.int_ 28) (IRScalar.vcons (IRScalar.int_ 29) (IRScalar.vcons (IRScalar.int_ 30) (IRScalar.vcons (IRScalar.int_ 31) (IRScalar.vcons (IRScalar.int_ 32) (IRScalar.vcons (IRScalar.int_ 33) (IRScalar.vcons (IRScalar.int_ 34) (IRScalar.vcons (IRScalar.int_ 35) (IRScalar.vcons (IRScalar.int_ 36) (IRScalar.vcons (IRScalar.int_ 37) (IRScalar.vcons (IRScalar.int_ 38) (IRScalar.vcons (IRScalar.int_ 39) (IRScalar.vcons (IRScalar.int_ 40) (IRScalar.vcons (IRScalar.int_ 41) (IRScalar.vcons (IRScalar.int_ 42) (IRScalar.vcons (IRScalar.int_ 43) (IRScalar.vcons (IRScalar.int_ 44) (IRScalar.vcons (IRScalar.int_ 45) (IRScalar.vcons (IRScalar.int_ 46) (IRScalar.vcons (IRScalar.int_ 47) (IRScalar.vcons (IRScalar.int_ 48) (IRScalar.vcons (IRScalar.int_ 49) (IRScalar.vcons (IRScalar.int_ 50) (IRScalar.vcons (IRScalar.int_ 51) (IRScalar.vcons (IRScalar.int_ 52) (IRScalar.vcons (IRScalar.int_ 53) (IRScalar.vcons (IRScalar.int_ 54) (IRScalar.vcons (IRScalar.int_ 55) (IRScalar.vcons (IRScalar.int_ 56) (IRScalar.vcons (IRScalar.int_ 57) (IRScalar.vcons (IRScalar.int_ 58) (IRScalar.vcons (IRScalar.int_ 59) (IRScalar.vcons (IRScalar.int_ 60) (IRScalar.vcons (IRScalar.int_ 61) (IRScalar.vcons (IRScalar.int_ 62) (IRScalar.vcons (IRScalar.int_ 63) (IRScalar.vcons (IRScalar.int_ 64) (IRScalar.vcons (IRScalar.int_ 65) (IRScalar.vcons (IRScalar.int_ 66) (IRScalar.vcons (IRScalar.int_ 67) (IRScalar.vcons (IRScalar.int_ 68) (IRScalar.vcons (IRScalar.int_ 69) (IRScalar.vcons (IRScalar.int_ 70) (IRScalar.vcons (IRScalar.int_ 71) (IRScalar.vcons (IRScalar.int_ 72) (IRScalar.vcons (IRScalar.int_ 73) (IRScalar.vcons (IRScalar.int_ 74) (IRScalar.vcons (IRScalar.int_ 75) (IRScalar.vcons (IRScalar.int_ 76) (IRScalar.vcons (IRScalar.int_ 77) (IRScalar.vcons (IRScalar.int_ 78) (IRScalar.vcons (IRScalar.int_ 79) (IRScalar.vcons (IRScalar.int_ 80) IRScalar.vnil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))";

const SRC_IR_SM_WRITE_REPLACES_ONLY_81: &str = "def ir_sm_write_replaces_only_81 (x0 : IRScalar) (x40 : IRScalar) (x80 : IRScalar) (x81 : IRScalar) (rest : IRScalar) (b : Bool) : Eq IRScalar (env_set_strict_monads (ir_sm_probe x0 x40 x80 x81 rest) b) (IRScalar.aggv (ir_sm_probe x0 x40 x80 (IRScalar.bool_ b) rest)) := Eq.refl IRScalar (IRScalar.aggv (ir_sm_probe x0 x40 x80 (IRScalar.bool_ b) rest))";

const SRC_IR_SM_WRITES_SLOT81: &str = "def ir_sm_writes_slot81 (x0 : IRScalar) (x40 : IRScalar) (x80 : IRScalar) (x81 : IRScalar) (rest : IRScalar) (b : Bool) : Eq (IROption IRScalar) (ir_vals_get (ir_vals_set (ir_sm_probe x0 x40 x80 x81 rest) 81 (IRScalar.bool_ b)) 81) (IROption.some IRScalar (IRScalar.bool_ b)) := Eq.refl (IROption IRScalar) (IROption.some IRScalar (IRScalar.bool_ b))";

const SRC_IR_SM_PRESERVES_SLOT0: &str = "def ir_sm_preserves_slot0 (x0 : IRScalar) (x40 : IRScalar) (x80 : IRScalar) (x81 : IRScalar) (rest : IRScalar) (b : Bool) : Eq (IROption IRScalar) (ir_vals_get (ir_vals_set (ir_sm_probe x0 x40 x80 x81 rest) 81 (IRScalar.bool_ b)) 0) (IROption.some IRScalar x0) := Eq.refl (IROption IRScalar) (IROption.some IRScalar x0)";

const SRC_IR_SM_PRESERVES_SLOT1: &str = "def ir_sm_preserves_slot1 (x0 : IRScalar) (x40 : IRScalar) (x80 : IRScalar) (x81 : IRScalar) (rest : IRScalar) (b : Bool) : Eq (IROption IRScalar) (ir_vals_get (ir_vals_set (ir_sm_probe x0 x40 x80 x81 rest) 81 (IRScalar.bool_ b)) 1) (IROption.some IRScalar (IRScalar.int_ 1)) := Eq.refl (IROption IRScalar) (IROption.some IRScalar (IRScalar.int_ 1))";

const SRC_IR_SM_PRESERVES_SLOT40: &str = "def ir_sm_preserves_slot40 (x0 : IRScalar) (x40 : IRScalar) (x80 : IRScalar) (x81 : IRScalar) (rest : IRScalar) (b : Bool) : Eq (IROption IRScalar) (ir_vals_get (ir_vals_set (ir_sm_probe x0 x40 x80 x81 rest) 81 (IRScalar.bool_ b)) 40) (IROption.some IRScalar x40) := Eq.refl (IROption IRScalar) (IROption.some IRScalar x40)";

const SRC_IR_SM_PRESERVES_SLOT80: &str = "def ir_sm_preserves_slot80 (x0 : IRScalar) (x40 : IRScalar) (x80 : IRScalar) (x81 : IRScalar) (rest : IRScalar) (b : Bool) : Eq (IROption IRScalar) (ir_vals_get (ir_vals_set (ir_sm_probe x0 x40 x80 x81 rest) 81 (IRScalar.bool_ b)) 80) (IROption.some IRScalar x80) := Eq.refl (IROption IRScalar) (IROption.some IRScalar x80)";

const SRC_ENCODESENVREF_WITNESS: &str = "def encodesenvref_witness : EncodesEnvRef ir_sm_heap0 (IRScalar.ptr_ ir_d0) ir_sm_env0 := EncodesEnvRef.mk ir_sm_heap0 ir_d0 ir_sm_env0 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (IRScalar.aggv ir_sm_env0) Bool.true))) (Eq.refl Bool Bool.true)";

const SRC_IR_SM_ON_TRUE: &str = "def ir_sm_on_true : Eq IROutcome (ir_eval ir_d4 ir_sm_module ir_d0 (ir_vl2 (IRScalar.ptr_ ir_d0) (IRScalar.bool_ Bool.true)) ir_sm_heap0 ir_d1) (IROutcome.ret ir_vl0) := Eq.refl IROutcome (IROutcome.ret ir_vl0)";

const SRC_IR_SM_CONFIG_WITNESS: &str = "def ir_sm_config_witness : Eq IRConfig (ir_steps ir_d3 ir_sm_module (IRConfig.running (ir_sm_mach0 ir_sm_heap0 ir_d0 Bool.true ir_d1))) (IRConfig.running (ir_sm_m3 ir_sm_heap0 ir_d0 Bool.true ir_d1 ir_sm_env0)) := Eq.refl IRConfig (IRConfig.running (ir_sm_m3 ir_sm_heap0 ir_d0 Bool.true ir_d1 ir_sm_env0))";

const SRC_IR_SM_HEAP_READ_WITNESS: &str = "def ir_sm_heap_read_witness : Eq (IROption IRMemSlot) (ir_mem_lookup (ir_sm_heap_after ir_sm_heap0 ir_d0 Bool.true ir_sm_env0) ir_d0) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (IRScalar.aggv (ir_sm_probe (IRScalar.int_ 100) (IRScalar.int_ 140) (IRScalar.int_ 180) (IRScalar.bool_ Bool.true) IRScalar.vnil)) Bool.true)) := Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (IRScalar.aggv (ir_sm_probe (IRScalar.int_ 100) (IRScalar.int_ 140) (IRScalar.int_ 180) (IRScalar.bool_ Bool.true) IRScalar.vnil)) Bool.true))";

const SRC_IR_SM_ON_MISSING_CELL_IS_UB: &str = "def ir_sm_on_missing_cell_is_ub : Eq IROutcome (ir_eval ir_d4 ir_sm_module ir_d0 (ir_vl2 (IRScalar.ptr_ ir_d0) (IRScalar.bool_ Bool.true)) ir_mem0 ir_d1) (IROutcome.ub IRFault.bad_addr) := Eq.refl IROutcome (IROutcome.ub IRFault.bad_addr)";

const SRC_IR_SM_ON_DEAD_CELL_IS_UB: &str = "def ir_sm_on_dead_cell_is_ub : Eq IROutcome (ir_eval ir_d4 ir_sm_module ir_d0 (ir_vl2 (IRScalar.ptr_ ir_d0) (IRScalar.bool_ Bool.true)) (IRList.cons IRMemSlot (IRMemSlot.mk ir_d0 (IRScalar.aggv ir_sm_env0) Bool.false) ir_mem0) ir_d1) (IROutcome.ub IRFault.bad_addr) := Eq.refl IROutcome (IROutcome.ub IRFault.bad_addr)";

const SRC_IR_SM_ON_EMPTY_AGGREGATE_IS_BAD_FIELD: &str = "def ir_sm_on_empty_aggregate_is_bad_field : Eq IROutcome (ir_eval ir_d4 ir_sm_module ir_d0 (ir_vl2 (IRScalar.ptr_ ir_d0) (IRScalar.bool_ Bool.true)) (ir_cell ir_d0 (IRScalar.aggv ir_sp0) ir_mem0) ir_d1) (IROutcome.type_error IRFault.bad_field) := Eq.refl IROutcome (IROutcome.type_error IRFault.bad_field)";

const SRC_IR_SM_ON_81_FIELDS_IS_BAD_FIELD: &str = "def ir_sm_on_81_fields_is_bad_field : Eq IROutcome (ir_eval ir_d4 ir_sm_module ir_d0 (ir_vl2 (IRScalar.ptr_ ir_d0) (IRScalar.bool_ Bool.true)) (ir_cell ir_d0 (IRScalar.aggv ir_sm_spine81) ir_mem0) ir_d1) (IROutcome.type_error IRFault.bad_field) := Eq.refl IROutcome (IROutcome.type_error IRFault.bad_field)";

const SRC_IR_SM_ON_NULL_RECEIVER_IS_UB: &str = "def ir_sm_on_null_receiver_is_ub : Eq IROutcome (ir_eval ir_d4 ir_sm_module ir_d0 (ir_vl2 IRScalar.nullptr_ (IRScalar.bool_ Bool.true)) ir_sm_heap0 ir_d1) (IROutcome.ub IRFault.null_deref) := Eq.refl IROutcome (IROutcome.ub IRFault.null_deref)";

const SRC_IR_SM_ON_INT_RECEIVER_IS_TYPE_ERROR: &str = "def ir_sm_on_int_receiver_is_type_error : Eq IROutcome (ir_eval ir_d4 ir_sm_module ir_d0 (ir_vl2 (IRScalar.int_ ir_d5) (IRScalar.bool_ Bool.true)) ir_sm_heap0 ir_d1) (IROutcome.type_error IRFault.not_ptr) := Eq.refl IROutcome (IROutcome.type_error IRFault.not_ptr)";

const SRC_IR_SM_CORRECT_WITNESS: &str = "def ir_sm_correct_witness : Eq IROutcome (ir_eval ir_d4 ir_sm_module ir_d0 (ir_vl2 (IRScalar.ptr_ ir_d0) (IRScalar.bool_ Bool.true)) ir_sm_heap0 ir_d1) (IROutcome.ret ir_vl0) := ir_sm_correct ir_sm_heap0 ir_d4 ir_d1 (IRScalar.ptr_ ir_d0) ir_sm_env0 Bool.true encodesenvref_witness (Le.refl ir_d4)";

const SRC_IR_SM_MACHINE_SOUND_WITNESS: &str = "def ir_sm_machine_sound_witness : Eq (IRList IRScalar) ir_vl0 ir_vl0 := ir_sm_machine_sound ir_sm_heap0 ir_d4 ir_d1 (IRScalar.ptr_ ir_d0) ir_sm_env0 Bool.true ir_vl0 encodesenvref_witness (Le.refl ir_d4) (Eq.refl IROutcome (IROutcome.ret ir_vl0))";

impl Specification {
    /// Register the strict_monads chain: the first over a MUTATING body,
    /// the first with a `store`, and the first with a void return —
    /// `env::Environment::set_lean4_core_strict_monads`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_strict_monads(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IR_SM_TENV, "ir_sm_tenv: struct.441, the whole-crate struct id the emitted body names in all three of its instructions. Transcribed for fidelity and compared by the load_tys/insertfields/stores type slots; the value-addressed semantics never consults it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENV_SET_STRICT_MONADS, "env_set_strict_monads: the reflected env::Environment::set_lean4_core_strict_monads, at the level the machine actually works at -- replace slot 81 of the Environment aggregate's spine with the Bool argument, via the machine's own ir_vals_set. This is a SPINE-level specification, not a proof that field 81 of struct.441 IS the strict_monads flag of the Rust Environment: that correspondence is a producer layout fact, stated in the module doc and closed nowhere. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESENVREF, "EncodesEnvRef mem r sp: r is a pointer to a LIVE heap cell holding the Environment aggregate whose payload spine is sp, and sp has at least 82 fields -- the exact bound ir_if_at checks before writing slot 81 (ir_nat_ltb 81 (ir_vals_len sp)). Stated as an EQUATION on ir_mem_lookup, like EncodesCleanMode's, so a shadowed duplicate cell cannot satisfy it while the machine reads a different one. Spine-agnostic in every slot VALUE: nothing pins what any field holds, because the body reads none of them -- it writes exactly one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_B0, "ir_sm_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/strict_monads.trust-ir.txt). Load struct.441 through %0 into %2, insertfield at FIELD 81 of %2 with %1 into %3, store %3 back through %0, ret VOID. The store's constructor operand order is pointer-then-value (IRInst.store : IRTy -> Nat -> Nat -> Bool) -- the REVERSE of the printed `store {ty} %3, ptr %0` -- and both CFG parsers normalize to (POINTER, TYPE, value) so a single-side swap fails by construction. Both volatile slots are Bool.false; a Bool.true here is REFUSED by the Clean-side parser rather than dropped. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_FUNC, "ir_sm_func: the setter as EvalIR -- TWO parameters (%0 the &mut Environment receiver, %1 the bool), entry block 0, one block. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_MODULE, "ir_sm_module: the module for env::Environment::set_lean4_core_strict_monads, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/strict_monads.trust-ir.txt and checked lane for lane (including the insertfields and stores lanes that were added for it) by tests/crystal_a1_lineage/strict_monads.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_MACH0, "ir_sm_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds the receiver pointer and the Bool positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_AFTER_LOAD, "ir_sm_after_load: the configuration one step in, with the heap LOOKUP abstracted to a parameter -- the same device ir_pv_after_load uses, for the same reason: on a symbolic heap ir_mem_lookup is stuck, and the representation premise's equation is what unsticks it. At o := ir_mem_lookup mem a this is DEFINITIONALLY one ir_step of mach0 (ir_sm_step1). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_LOCALS1, "ir_sm_locals1: the frame locals after the load binds %2 to the loaded aggregate. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_M1, "ir_sm_m1: the machine after the load -- pc 1, %2 bound, heap UNTOUCHED. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_AFTER_INSERT, "ir_sm_after_insert: the configuration after the insertfield's BOUNDS CHECK is abstracted to a Bool parameter. ir_if_at is Bool.rec over ir_nat_ltb 81 (ir_vals_len sp), which is stuck on a symbolic spine; the premise's length equation rewrites it to Bool.true. The false minor is the fault arm (type_error bad_field), transcribed exactly -- ir_sm_insert_out_of_bounds executes it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_LOCALS2, "ir_sm_locals2: the locals after the insertfield binds %3 to the REWRITTEN aggregate -- env_set_strict_monads sp b, which is definitionally the machine's own ir_vals_set term. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_M2, "ir_sm_m2: the machine after the insertfield -- pc 2, %3 bound, heap STILL untouched. Values are immutable: the write so far exists only in the frame. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_AFTER_STORE, "ir_sm_after_store: the store step with the SECOND heap lookup abstracted -- ir_store_exec re-reads the cell at a before committing, and the SAME premise equation discharges it. This is where the mutation leaves the frame and reaches memory. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_HEAP_AFTER, "ir_sm_heap_after: THE FINAL HEAP -- ir_mem_update at the receiver's address with the field-81-rewritten aggregate, every other cell preserved by ir_mem_update's own definition, liveness preserved by ir_store_live's. This is the entire observable effect of the body. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_M3, "ir_sm_m3: the machine after the store -- pc 3, memory ir_sm_heap_after. The next step returns void. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_STEP1, "ir_sm_step1: one step of mach0 IS after_load at the (stuck) lookup. Eq.refl -- the kernel runs the fetch and the pointer dispatch and stops exactly at the heap read. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_LOAD_BINDS, "ir_sm_load_binds: at a live aggregate-holding cell, the load binds %2 and advances -- after_load at `some cell` IS running m1, by Eq.refl. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_STEP2, "ir_sm_step2: one step of m1 IS after_insert at the (stuck) bounds check. Eq.refl: ir_insert_field destructures the aggv constructor, ir_if_at unfolds to Bool.rec over ir_nat_ltb 81 (ir_vals_len sp), and the machine stops exactly there. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_INSERT_IN_BOUNDS, "ir_sm_insert_in_bounds: a true bounds check binds %3 to the rewritten aggregate and advances -- after_insert Bool.true IS running m2. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_INSERT_OUT_OF_BOUNDS, "ir_sm_insert_out_of_bounds: a false bounds check is the fault arm, executed -- type_error bad_field, halting the machine. This is the arm the length premise exists to rule out, and ir_sm_on_81_fields_is_bad_field runs the whole body into it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_STEP3, "ir_sm_step3: one step of m2 IS after_store at the (stuck) SECOND lookup of the same address. Eq.refl -- ir_getd finds %0 and %3 in the frame and ir_store_exec dispatches on the ptr_ constructor. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_STORE_COMMITS, "ir_sm_store_commits: at the same live cell, the store COMMITS -- after_store at `some cell` IS running m3, whose memory is ir_mem_update mem a (env_set_strict_monads sp b). The liveness read is ir_slot_live of the premise's cell, so a dead cell can never take this arm. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_STORE_ON_MISSING_CELL, "ir_sm_store_on_missing_cell: storing to an address with no cell is out-of-bounds UB, executed -- ub bad_addr. Unreachable under the premise (the load already found the cell and nothing freed it), but transcribed because it is ir_store_checked's other arm. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_RET_IS_VOID, "ir_sm_ret_is_void: from m3 the bare ret halts the outermost frame with IROutcome.ret [] -- the VOID return, the first in any chain. ir_resolve of the empty id list never touches the locals, so this is Eq.refl at a fully symbolic machine. Note the heap is DROPPED here: ir_eval observes outcomes, which is why the mutation theorems are stated at ir_steps 3, one step before. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_EXACT, "ir_sm_exact: the machine agrees with the void outcome at EXACTLY 4 steps, for every heap, address, spine and Bool satisfying the two premise equations. Three Eq.subst rewrites at the three stuck points -- the load's lookup, the bounds check, the store's RE-lookup of the same address (the same hmem discharged twice, which is the aliasing fact of the body: it stores through the pointer it loaded from) -- and everything between them is kernel computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_CORRECT, "ir_sm_correct: *** A4, THE OUTCOME HALF -- OVER THE EMITTED SHAPE, FOR THE FIRST MUTATING BODY. *** For every heap, every pointer-and-spine pair it represents an Environment through (any aggregate of >= 82 fields, any field values, any tail), every Bool argument, every next-address counter and every fuel at or above 4, ir_eval on ir_sm_module returns exactly IROutcome.ret [] -- void. The OTHER half of what the body does is deliberately not in this statement, because ir_eval discards the final heap at ret: ir_sm_writes_field81 states it at ir_steps 3. 

A0 is measured on the SHIPPED kernel (tests/fixtures/strict_monads.lineage.json): lowered, spliced, unsupported [], derived_mir agreed (5 canonical lines), markers_exact TRUE over 2 REAL marker lines, 0 calls, codegen flip with flip-event lineage == coverage-row lineage, three byte-identical clean builds. The producer's interpreter differential is NOT-RUN on this body (0 samples) and NOTHING here claims it. A1 is gated by tests/crystal_a1_lineage/strict_monads.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_WRITES_FIELD81, "ir_sm_writes_field81: *** A4, THE HEAP HALF -- THE MUTATION ITSELF. *** After exactly 3 steps (load, insertfield, store) the configuration IS running m3: same frame, and memory ir_mem_update mem a (env_set_strict_monads sp b) -- the SAME heap with the receiver's cell now holding the SAME aggregate with field 81 replaced by the Bool argument, every other cell untouched by ir_mem_update's definition and every other FIELD untouched by ir_vals_set's (witnessed symbolically by ir_sm_write_replaces_only_81 and the four preserves lemmas). Stated at ir_steps rather than ir_eval because the machine's ret discards the heap; this is the strongest place the effect is observable. Same three-subst proof as ir_sm_exact, at IRConfig. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_FINAL_MEM, "ir_sm_final_mem: the memory projection of the 3-step configuration IS ir_sm_heap_after -- the heap-half theorem composed with ir_mach_mem, so a consumer can name the final heap without destructuring a configuration. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_RET_PAYLOAD, "ir_sm_ret_payload: the returned value list of an outcome, empty on every non-ret. Used only to invert a ret-equation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_MACHINE_SOUND, "ir_sm_machine_sound: *** A5 AT THE OUTCOME, FULL SYMBOLIC. *** If the machine running the emitted body on a represented heap returns v at any fuel >= 4 (Le ir_d4 fuel; ret is unreachable below the cost of the four instructions), then v IS the empty list -- the body returns nothing else on any represented input. Goes through A4 rather than restating it. The outcome of a setter is deliberately information-free; the A5 with content is ir_sm_config_sound, one declaration down. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_CONFIG_SOUND, "ir_sm_config_sound: *** A5 AT THE HEAP, FULL SYMBOLIC -- THE INVERSION THAT CARRIES THE MUTATION. *** Any configuration the machine reaches after the store IS the m3 of the premise's heap, address, spine and Bool: final memory ir_mem_update mem a (env_set_strict_monads sp b), nothing else. Unlike the float trio's A5 -- split at a measured defeq wall in the rounding pipeline -- this inversion holds symbolically, because ir_vals_set on a symbolic spine is INERT (IRScalar.rec stuck on the spine variable) and nothing here ever needs to reduce it. Both directions cost one Eq.trans over the heap-half A4. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_NEVER_FAULTS, "ir_sm_never_faults: *** NO UB, NO TYPE ERROR, NO STUCK STATE, NO EXHAUSTION -- on any represented heap. *** Concretely: the load never faults bad_addr/null_deref (the premise's cell is live), the insertfield never faults bad_field (the length premise is exactly its bounds check), the store's re-read finds the same live cell, and 4 steps always suffice. Every fault arm is separately EXECUTED by the ir_sm_on_* witnesses on heaps that violate the premise, so the corollary is earned, not decorative. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_PROBE, "ir_sm_probe: an 82-field probe spine with SYMBOLIC slots 0, 40, 80 and 81 and a SYMBOLIC tail past slot 81; the other 78 slots are pinned distinct integers. This is the shape that makes field-preservation PROVABLE BY KERNEL COMPUTATION at symbolic field values: ir_vals_set recurses on the spine constructors and the literal index, never on the slot contents. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_ENV0, "ir_sm_env0: the concrete witness Environment -- sentinel integers at the probe slots, strict_monads (slot 81) = Bool.false, no tail. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_HEAP0, "ir_sm_heap0: one live cell at address 0 holding ir_sm_env0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_SPINE81, "ir_sm_spine81: an 81-field aggregate -- ONE FIELD SHORT of what the body needs. The exact boundary of the length premise; ir_sm_on_81_fields_is_bad_field runs the body into the fault it causes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_WRITE_REPLACES_ONLY_81, "ir_sm_write_replaces_only_81: *** THE FIELD-PRESERVATION THEOREM, SYMBOLIC WHERE IT COUNTS. *** For ANY values at slots 0, 40 and 80, ANY prior value at slot 81, ANY tail past 82 fields and ANY Bool, the reflected write is exactly the same spine with slot 81 replaced -- Eq.refl, so the KERNEL computes the 82-slot rewrite and checks the other 81 slots and the tail land unchanged. This is the honest, affordable form of every-other-field-unchanged: general enough to carry arbitrary values at the spot-checked slots, without the unearned induction a fully symbolic spine would need. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_WRITES_SLOT81, "ir_sm_writes_slot81: reading slot 81 back out of the written spine yields the Bool argument -- for every prior slot-81 value. The flip, observed by ir_vals_get. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_PRESERVES_SLOT0, "ir_sm_preserves_slot0: slot 0 reads back as the SYMBOLIC x0 it held before the write. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_PRESERVES_SLOT1, "ir_sm_preserves_slot1: a pinned interior slot is untouched too. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_PRESERVES_SLOT40, "ir_sm_preserves_slot40: slot 40 reads back as the symbolic x40. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_PRESERVES_SLOT80, "ir_sm_preserves_slot80: slot 80 -- the immediate neighbour of the written slot -- reads back as the symbolic x80. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENCODESENVREF_WITNESS, "encodesenvref_witness: the representation premise is SATISFIABLE, by constructor application with both equations discharged by Eq.refl -- the kernel runs the heap lookup and decides 81 < 82 by computing it. Registered in-module so the premise gate and the vacuity firewall see EncodesEnvRef concluded, never blessed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_ON_TRUE, "*** CONCRETE EXECUTION WITNESS -- THE KERNEL RUNS THE MUTATING BODY END TO END. *** Four steps on a real one-cell heap holding an 82-field Environment: load, in-bounds insertfield at slot 81, store, void ret. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_CONFIG_WITNESS, "ir_sm_config_witness: the 3-step CONFIGURATION witness, fully concrete -- the kernel executes load+insertfield+store on ir_sm_heap0 and the result is m3 exactly, including the updated memory. The heap-half theorem, checked once by pure computation with no premise machinery in the term. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_HEAP_READ_WITNESS, "ir_sm_heap_read_witness: *** THE FLIP, VISIBLE TO THE NEXT LOAD. *** Looking the receiver's address up in the final heap yields the SAME live cell holding the SAME probe aggregate with slot 81 flipped false -> true and the three sentinel slots intact. What a subsequent `load` of self would read. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_ON_MISSING_CELL_IS_UB, "FAIL-CLOSED WITNESS -- an EMPTY heap: the load is out-of-bounds UB (bad_addr), not a default value. The premise's lookup equation is load-bearing. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_ON_DEAD_CELL_IS_UB, "FAIL-CLOSED WITNESS -- a DEAD cell at the right address with the right aggregate: still UB (bad_addr). Liveness is checked by the machine, which is why the premise pins Bool.true in the cell. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_ON_EMPTY_AGGREGATE_IS_BAD_FIELD, "FAIL-CLOSED WITNESS -- a ZERO-field aggregate: the load succeeds and the insertfield faults bad_field. The length premise is load-bearing, not decorative. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_ON_81_FIELDS_IS_BAD_FIELD, "FAIL-CLOSED WITNESS -- an 81-field aggregate, ONE short: bad_field at the exact boundary. 81 < 82 is the least length the premise accepts, and this shows 81 fields is genuinely outside it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_ON_NULL_RECEIVER_IS_UB, "FAIL-CLOSED WITNESS -- a NULL receiver: ub null_deref at the load, the panic-shaped arm a &mut can never produce in safe Rust and the machine still refuses explicitly. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_ON_INT_RECEIVER_IS_TYPE_ERROR, "FAIL-CLOSED WITNESS -- an INTEGER where the pointer should be: type_error not_ptr, not a wrong address. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_CORRECT_WITNESS, "ir_sm_correct_witness: A4's premises all discharged concretely -- the one-cell heap, the 82-field Environment, the exact fuel by Le.refl, the representation by encodesenvref_witness -- and the conclusion RUNS the machine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SM_MACHINE_SOUND_WITNESS, "ir_sm_machine_sound_witness: A5's premises are satisfiable -- the observation is discharged by Eq.refl, which the kernel checks by executing the body. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
