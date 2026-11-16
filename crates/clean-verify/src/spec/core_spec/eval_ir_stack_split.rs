// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **`ir_stk_split` -- the frame-stacking split keyed on the FETCHED NODE**
//! (decision memo §6 Phase E, E1; statements settled in
//! `designs/2026-09-24-e1-stk-split.md`).
//!
//! The running-keyed stacking family (`eval_ir_stack*.rs`) can only transport a
//! run that is still RUNNING. This stage, over the node-keyed twin
//! `ir_stkn_step` and the classifier `ir_stk_botret` minted by
//! `scripts/gen_stack_lemmas.py`, transports every run whose running prefixes
//! stay in the commuting class -- nonempty frame list, not a bottom `ret` --
//! whatever its OUTCOME:
//!
//! * **R** (still running) `ir_stk_split_running`, **F** (halted: faulted or
//!   otherwise) `ir_stk_split_halted`, both corollaries of `ir_stk_split`, and
//!   `ir_stk_split_outcome` for the outcome reading;
//! * **T** (first classifier hit) `ir_stk_botret_hit` + `ir_stk_clear_of_running`
//!   (the hit and its firstness), `ir_stk_split_ret_standalone` (the standalone
//!   run halts `ret vs`) and `ir_stk_split_ret` / `ir_stk_activation` (the stacked
//!   run pops into `rest` with the same `vs`);
//! * `ir_stk_activation_dests` -- `ir_stk_activation` in the `forall d r` contract
//!   form, connecting the returning frame's dests to the entry frame's;
//! * `ir_call_push` -- the generic call step, with `ir_push_cons`.
//!
//! No Or / And / Exists / False: the three cases are Bool-premised theorems, and
//! a conjunction of Bool tests is a nested `Bool.rec` guard taken apart by
//! `ir_bool_guard_false` / `ir_bool_guard_rest`.
//!
//! The R and F witnesses sit at the `ir_lzc_module` run on Max(Zero, Zero)
//! that `ir_lzc_max_running_at_8` / `ir_lzc_max_stuck_at_9` already prove,
//! CITED rather than recomputed. The T witness needs the Full-only
//! heartbeat model and lives in `eval_ir_stk_witness.rs`.
//!
//! Registered in BOTH the Full stage list and the EvalIr bundle, after
//! `add_eval_ir_stack_theorems`. `DerivedProved`, empty axiom closures, every
//! declaration by name.

use super::eval_ir_lzc::lzc_maxzz_init;
use super::{SpecError, Specification};

const SRC_BOOL_GUARD_FALSE: &str = "def ir_bool_guard_false (b : Bool) (x : Bool) (h : @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x Bool.false b) Bool.true) : @Eq Bool b Bool.false := @Bool.rec (fun (b0 : Bool) => @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x Bool.false b0) Bool.true -> @Eq Bool b0 Bool.false) (fun (_ : @Eq Bool x Bool.true) => @Eq.refl Bool Bool.false) (fun (h0 : @Eq Bool Bool.false Bool.true) => ir_bool_false_ne_true (@Eq Bool Bool.true Bool.false) h0) b h";
const SRC_BOOL_GUARD_REST: &str = "def ir_bool_guard_rest (b : Bool) (x : Bool) (h : @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x Bool.false b) Bool.true) : @Eq Bool x Bool.true := @Bool.rec (fun (b0 : Bool) => @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x Bool.false b0) Bool.true -> @Eq Bool x Bool.true) (fun (h0 : @Eq Bool x Bool.true) => h0) (fun (h0 : @Eq Bool Bool.false Bool.true) => ir_bool_false_ne_true (@Eq Bool x Bool.true) h0) b h";
const SRC_BOOL_GUARD_INTRO: &str = "def ir_bool_guard_intro (b : Bool) (x : Bool) (hb : @Eq Bool b Bool.false) (hx : @Eq Bool x Bool.true) : @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x Bool.false b) Bool.true := @Eq.subst Bool (fun (b0 : Bool) => @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) x Bool.false b0) Bool.true) Bool.false b (@Eq.symm Bool b Bool.false hb) hx";
const SRC_STK_CLEAR: &str = "def ir_stk_clear (n : Nat) (m : IRModule) (c : IRConfig) : Bool := @Nat.rec (fun (_ : Nat) => IRConfig -> Bool) (fun (_ : IRConfig) => Bool.true) (fun (_ : Nat) (ih : IRConfig -> Bool) => fun (c0 : IRConfig) => @IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (s : IRMachine) => @Bool.rec (fun (_ : Bool) => Bool) (@Bool.rec (fun (_ : Bool) => Bool) (ih (ir_step m s)) Bool.false (ir_stk_botret m s)) Bool.false (ir_frames_is_nil (ir_mach_frames s))) (fun (_ : IROutcome) => Bool.true) c0) n c";
const SRC_STK_CLEAR_ZERO: &str = "def ir_stk_clear_zero (m : IRModule) (c : IRConfig) : @Eq Bool (ir_stk_clear Nat.zero m c) Bool.true := @Eq.refl Bool Bool.true";
const SRC_STK_CLEAR_SUCC: &str = "def ir_stk_clear_succ (k : Nat) (m : IRModule) (s : IRMachine) : @Eq Bool (ir_stk_clear (Nat.succ k) m (IRConfig.running s)) (@Bool.rec (fun (_ : Bool) => Bool) (@Bool.rec (fun (_ : Bool) => Bool) (ir_stk_clear k m (ir_step m s)) Bool.false (ir_stk_botret m s)) Bool.false (ir_frames_is_nil (ir_mach_frames s))) := @Eq.refl Bool (@Bool.rec (fun (_ : Bool) => Bool) (@Bool.rec (fun (_ : Bool) => Bool) (ir_stk_clear k m (ir_step m s)) Bool.false (ir_stk_botret m s)) Bool.false (ir_frames_is_nil (ir_mach_frames s)))";
const SRC_STK_CLEAR_HALTED: &str = "def ir_stk_clear_halted (n : Nat) (m : IRModule) (o : IROutcome) : @Eq Bool (ir_stk_clear n m (IRConfig.halted o)) Bool.true := @Nat.rec (fun (k : Nat) => @Eq Bool (ir_stk_clear k m (IRConfig.halted o)) Bool.true) (@Eq.refl Bool Bool.true) (fun (k : Nat) (_ : @Eq Bool (ir_stk_clear k m (IRConfig.halted o)) Bool.true) => @Eq.refl Bool Bool.true) n";
const SRC_STK_NONNIL_OF_RUNNING: &str = "def ir_stk_nonnil_of_running (m : IRModule) (s : IRMachine) (hrun : @Eq Bool (ir_stk_running (ir_step m s)) Bool.true) : @Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.false := @IRMachine.rec (fun (s0 : IRMachine) => @Eq Bool (ir_stk_running (ir_step m s0)) Bool.true -> @Eq Bool (ir_frames_is_nil (ir_mach_frames s0)) Bool.false) (fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => @IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => @Eq Bool (ir_stk_running (ir_step m (IRMachine.mk fs0 mem na))) Bool.true -> @Eq Bool (ir_frames_is_nil fs0) Bool.false) (fun (h : @Eq Bool (ir_stk_running (ir_step m (IRMachine.mk (@IRList.nil IRFrame) mem na))) Bool.true) => ir_bool_false_ne_true (@Eq Bool (ir_frames_is_nil (@IRList.nil IRFrame)) Bool.false) h) (fun (f : IRFrame) (t : IRList IRFrame) (_ih : @Eq Bool (ir_stk_running (ir_step m (IRMachine.mk t mem na))) Bool.true -> @Eq Bool (ir_frames_is_nil t) Bool.false) (_ : @Eq Bool (ir_stk_running (ir_step m (IRMachine.mk (@IRList.cons IRFrame f t) mem na))) Bool.true) => @Eq.refl Bool Bool.false) fs) s hrun";
const SRC_STK_CLEAR_OF_RUNNING: &str = "def ir_stk_clear_of_running (m : IRModule) (n : Nat) : forall (c : IRConfig), @Eq Bool (ir_stk_running (ir_steps n m c)) Bool.true -> @Eq Bool (ir_stk_clear n m c) Bool.true := @Nat.rec (fun (k : Nat) => forall (c : IRConfig), @Eq Bool (ir_stk_running (ir_steps k m c)) Bool.true -> @Eq Bool (ir_stk_clear k m c) Bool.true) (fun (c : IRConfig) (_ : @Eq Bool (ir_stk_running (ir_steps Nat.zero m c)) Bool.true) => @Eq.refl Bool Bool.true) (fun (k : Nat) (ih : forall (c : IRConfig), @Eq Bool (ir_stk_running (ir_steps k m c)) Bool.true -> @Eq Bool (ir_stk_clear k m c) Bool.true) => fun (c : IRConfig) => @IRConfig.rec (fun (c0 : IRConfig) => @Eq Bool (ir_stk_running (ir_steps (Nat.succ k) m c0)) Bool.true -> @Eq Bool (ir_stk_clear (Nat.succ k) m c0) Bool.true) (fun (s : IRMachine) (hrun : @Eq Bool (ir_stk_running (ir_steps (Nat.succ k) m (IRConfig.running s))) Bool.true) => ir_bool_guard_intro (ir_frames_is_nil (ir_mach_frames s)) (@Bool.rec (fun (_ : Bool) => Bool) (ir_stk_clear k m (ir_step m s)) Bool.false (ir_stk_botret m s)) (ir_stk_nonnil_of_running m s (ir_stk_running_back m k (ir_step m s) hrun)) (ir_bool_guard_intro (ir_stk_botret m s) (ir_stk_clear k m (ir_step m s)) (ir_stk_botret_false_of_running m s (ir_stk_running_back m k (ir_step m s) hrun)) (ih (ir_step m s) hrun))) (fun (o : IROutcome) (_ : @Eq Bool (ir_stk_running (ir_steps (Nat.succ k) m (IRConfig.halted o))) Bool.true) => @Eq.refl Bool Bool.true) c) n";
const SRC_STK_SPLIT: &str = "def ir_stk_split (m : IRModule) (rest : IRList IRFrame) (n : Nat) : forall (c : IRConfig), @Eq Bool (ir_stk_clear n m c) Bool.true -> @Eq IRConfig (ir_steps n m (ir_config_stack c rest)) (ir_config_stack (ir_steps n m c) rest) := @Nat.rec (fun (k : Nat) => forall (c : IRConfig), @Eq Bool (ir_stk_clear k m c) Bool.true -> @Eq IRConfig (ir_steps k m (ir_config_stack c rest)) (ir_config_stack (ir_steps k m c) rest)) (fun (c : IRConfig) (_ : @Eq Bool (ir_stk_clear Nat.zero m c) Bool.true) => @Eq.refl IRConfig (ir_config_stack c rest)) (fun (k : Nat) (ih : forall (c : IRConfig), @Eq Bool (ir_stk_clear k m c) Bool.true -> @Eq IRConfig (ir_steps k m (ir_config_stack c rest)) (ir_config_stack (ir_steps k m c) rest)) => fun (c : IRConfig) => @IRConfig.rec (fun (c0 : IRConfig) => @Eq Bool (ir_stk_clear (Nat.succ k) m c0) Bool.true -> @Eq IRConfig (ir_steps (Nat.succ k) m (ir_config_stack c0 rest)) (ir_config_stack (ir_steps (Nat.succ k) m c0) rest)) (fun (s : IRMachine) (h : @Eq Bool (ir_stk_clear (Nat.succ k) m (IRConfig.running s)) Bool.true) => @Eq.trans IRConfig (ir_steps k m (ir_step m (ir_mach_stack s rest))) (ir_steps k m (ir_config_stack (ir_step m s) rest)) (ir_config_stack (ir_steps k m (ir_step m s)) rest) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_steps k m c1) (ir_step m (ir_mach_stack s rest)) (ir_config_stack (ir_step m s) rest) (ir_stkn_step m s rest (ir_bool_guard_false (ir_frames_is_nil (ir_mach_frames s)) (@Bool.rec (fun (_ : Bool) => Bool) (ir_stk_clear k m (ir_step m s)) Bool.false (ir_stk_botret m s)) h) (ir_bool_guard_false (ir_stk_botret m s) (ir_stk_clear k m (ir_step m s)) (ir_bool_guard_rest (ir_frames_is_nil (ir_mach_frames s)) (@Bool.rec (fun (_ : Bool) => Bool) (ir_stk_clear k m (ir_step m s)) Bool.false (ir_stk_botret m s)) h)))) (ih (ir_step m s) (ir_bool_guard_rest (ir_stk_botret m s) (ir_stk_clear k m (ir_step m s)) (ir_bool_guard_rest (ir_frames_is_nil (ir_mach_frames s)) (@Bool.rec (fun (_ : Bool) => Bool) (ir_stk_clear k m (ir_step m s)) Bool.false (ir_stk_botret m s)) h)))) (fun (o : IROutcome) (_ : @Eq Bool (ir_stk_clear (Nat.succ k) m (IRConfig.halted o)) Bool.true) => @Eq.refl IRConfig (IRConfig.halted o)) c) n";
const SRC_STK_SPLIT_RUNNING: &str = "def ir_stk_split_running (m : IRModule) (rest : IRList IRFrame) (n : Nat) (c : IRConfig) (s2 : IRMachine) (hcl : @Eq Bool (ir_stk_clear n m c) Bool.true) (hr : @Eq IRConfig (ir_steps n m c) (IRConfig.running s2)) : @Eq IRConfig (ir_steps n m (ir_config_stack c rest)) (IRConfig.running (ir_mach_stack s2 rest)) := @Eq.trans IRConfig (ir_steps n m (ir_config_stack c rest)) (ir_config_stack (ir_steps n m c) rest) (IRConfig.running (ir_mach_stack s2 rest)) (ir_stk_split m rest n c hcl) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_config_stack c1 rest) (ir_steps n m c) (IRConfig.running s2) hr)";
const SRC_STK_SPLIT_HALTED: &str = "def ir_stk_split_halted (m : IRModule) (rest : IRList IRFrame) (n : Nat) (c : IRConfig) (o : IROutcome) (hcl : @Eq Bool (ir_stk_clear n m c) Bool.true) (hh : @Eq IRConfig (ir_steps n m c) (IRConfig.halted o)) : @Eq IRConfig (ir_steps n m (ir_config_stack c rest)) (IRConfig.halted o) := @Eq.trans IRConfig (ir_steps n m (ir_config_stack c rest)) (ir_config_stack (ir_steps n m c) rest) (IRConfig.halted o) (ir_stk_split m rest n c hcl) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_config_stack c1 rest) (ir_steps n m c) (IRConfig.halted o) hh)";
const SRC_CONFIG_OUTCOME_STACK: &str = "def ir_config_outcome_stack (c : IRConfig) (rest : IRList IRFrame) : @Eq IROutcome (ir_config_outcome (ir_config_stack c rest)) (ir_config_outcome c) := @IRConfig.rec (fun (c0 : IRConfig) => @Eq IROutcome (ir_config_outcome (ir_config_stack c0 rest)) (ir_config_outcome c0)) (fun (_ : IRMachine) => @Eq.refl IROutcome IROutcome.fuel_out) (fun (o : IROutcome) => @Eq.refl IROutcome o) c";
const SRC_STK_SPLIT_OUTCOME: &str = "def ir_stk_split_outcome (m : IRModule) (rest : IRList IRFrame) (n : Nat) (c : IRConfig) (hcl : @Eq Bool (ir_stk_clear n m c) Bool.true) : @Eq IROutcome (ir_config_outcome (ir_steps n m (ir_config_stack c rest))) (ir_config_outcome (ir_steps n m c)) := @Eq.trans IROutcome (ir_config_outcome (ir_steps n m (ir_config_stack c rest))) (ir_config_outcome (ir_config_stack (ir_steps n m c) rest)) (ir_config_outcome (ir_steps n m c)) (ir_eq_cong IRConfig IROutcome (fun (c1 : IRConfig) => ir_config_outcome c1) (ir_steps n m (ir_config_stack c rest)) (ir_config_stack (ir_steps n m c) rest) (ir_stk_split m rest n c hcl)) (ir_config_outcome_stack (ir_steps n m c) rest)";
const SRC_STK_BOTRET_HIT: &str = "def ir_stk_botret_hit (m : IRModule) (f : IRFrame) (mem : IRList IRMemSlot) (na : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (hf : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@IROption.some IRFunc fn)) (hb : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@IROption.some IRBlock b)) (hn : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : @Eq Bool (ir_stk_botret m (IRMachine.mk (@IRList.cons IRFrame f (@IRList.nil IRFrame)) mem na)) Bool.true := @Eq.subst (IROption IRFunc) (fun (o : IROption IRFunc) => @Eq Bool (ir_fetch_f_ret (ir_frame_block f) (ir_frame_pc f) o) Bool.true) (@IROption.some IRFunc fn) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@Eq.symm (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@IROption.some IRFunc fn) hf) (@Eq.subst (IROption IRBlock) (fun (ob : IROption IRBlock) => @Eq Bool (ir_fetch_b_ret (ir_frame_pc f) ob) Bool.true) (@IROption.some IRBlock b) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@Eq.symm (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@IROption.some IRBlock b) hb) (@Eq.subst (IROption IRNode) (fun (on : IROption IRNode) => @Eq Bool (ir_fetch_n_ret on) Bool.true) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs)) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@Eq.symm (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs)) hn) (@Eq.refl Bool Bool.true)))";
const SRC_STK_SPLIT_RET_STANDALONE: &str = "def ir_stk_split_ret_standalone (m : IRModule) (k : Nat) (c : IRConfig) (fk : IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (hr : @Eq IRConfig (ir_steps k m c) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2))) (hf : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func fk)) (@IROption.some IRFunc fn)) (hb : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block fk)) (@IROption.some IRBlock b)) (hn : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc fk)) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : @Eq IRConfig (ir_steps (Nat.add ir_d1 k) m c) (IRConfig.halted (IROutcome.ret (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids))) := @Eq.trans IRConfig (ir_steps (Nat.add ir_d1 k) m c) (ir_steps ir_d1 m (ir_steps k m c)) (IRConfig.halted (IROutcome.ret (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids))) (ir_steps_add m ir_d1 k c) (@Eq.trans IRConfig (ir_steps ir_d1 m (ir_steps k m c)) (ir_steps ir_d1 m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2))) (IRConfig.halted (IROutcome.ret (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids))) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_steps ir_d1 m c1) (ir_steps k m c) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2)) hr) (ir_stk_ret_step m fk (@IRList.nil IRFrame) mem2 na2 fn b ids rs hf hb hn))";
const SRC_STK_SPLIT_RET: &str = "def ir_stk_split_ret (m : IRModule) (k : Nat) (c : IRConfig) (fk : IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (rest : IRList IRFrame) (hcl : @Eq Bool (ir_stk_clear k m c) Bool.true) (hr : @Eq IRConfig (ir_steps k m c) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2))) (hf : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func fk)) (@IROption.some IRFunc fn)) (hb : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block fk)) (@IROption.some IRBlock b)) (hn : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc fk)) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : @Eq IRConfig (ir_steps (Nat.add ir_d1 k) m (ir_config_stack c rest)) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2) ids)) := @Eq.trans IRConfig (ir_steps (Nat.add ir_d1 k) m (ir_config_stack c rest)) (ir_steps ir_d1 m (ir_steps k m (ir_config_stack c rest))) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2) ids)) (ir_steps_add m ir_d1 k (ir_config_stack c rest)) (@Eq.trans IRConfig (ir_steps ir_d1 m (ir_steps k m (ir_config_stack c rest))) (ir_steps ir_d1 m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2))) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2) ids)) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_steps ir_d1 m c1) (ir_steps k m (ir_config_stack c rest)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2)) (ir_stk_split_running m rest k c (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) hcl hr)) (ir_stk_ret_step m fk rest mem2 na2 fn b ids rs hf hb hn))";
const SRC_FRAME_DESTS_BIND: &str = "def ir_frame_dests_bind (f : IRFrame) (rs : IRList Nat) (v : IRScalar) : @Eq (IRList Nat) (ir_frame_dests (ir_frame_bind f rs v)) (ir_frame_dests f) := @IRFrame.rec (fun (f0 : IRFrame) => @Eq (IRList Nat) (ir_frame_dests (ir_frame_bind f0 rs v)) (ir_frame_dests f0)) (fun (fnid : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (ds : IRList Nat) => @Eq.refl (IRList Nat) ds) f";
const SRC_FRAME_DESTS_BIND2: &str = "def ir_frame_dests_bind2 (f : IRFrame) (rs : IRList Nat) (v : IRScalar) (u : IRScalar) : @Eq (IRList Nat) (ir_frame_dests (ir_frame_bind2 f rs v u)) (ir_frame_dests f) := @IRFrame.rec (fun (f0 : IRFrame) => @Eq (IRList Nat) (ir_frame_dests (ir_frame_bind2 f0 rs v u)) (ir_frame_dests f0)) (fun (fnid : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (ds : IRList Nat) => @Eq.refl (IRList Nat) ds) f";
const SRC_FRAME_DESTS_ADVANCE: &str = "def ir_frame_dests_advance (f : IRFrame) : @Eq (IRList Nat) (ir_frame_dests (ir_frame_advance f)) (ir_frame_dests f) := @IRFrame.rec (fun (f0 : IRFrame) => @Eq (IRList Nat) (ir_frame_dests (ir_frame_advance f0)) (ir_frame_dests f0)) (fun (fnid : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (ds : IRList Nat) => @Eq.refl (IRList Nat) ds) f";
const SRC_FRAME_DESTS_GOTO: &str = "def ir_frame_dests_goto (f : IRFrame) (blk : Nat) (bs : IRList IRBinding) : @Eq (IRList Nat) (ir_frame_dests (ir_frame_goto f blk bs)) (ir_frame_dests f) := @IRFrame.rec (fun (f0 : IRFrame) => @Eq (IRList Nat) (ir_frame_dests (ir_frame_goto f0 blk bs)) (ir_frame_dests f0)) (fun (fnid : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (ds : IRList Nat) => @Eq.refl (IRList Nat) ds) f";
const SRC_FRAME_DESTS_SET_MANY: &str = "def ir_frame_dests_set_many (f : IRFrame) (rs : IRList Nat) (vs : IRList IRScalar) : @Eq (IRList Nat) (ir_frame_dests (ir_frame_set_many f rs vs)) (ir_frame_dests f) := @IRFrame.rec (fun (f0 : IRFrame) => @Eq (IRList Nat) (ir_frame_dests (ir_frame_set_many f0 rs vs)) (ir_frame_dests f0)) (fun (fnid : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (ds : IRList Nat) => @Eq.refl (IRList Nat) ds) f";
const SRC_STK_ACTIVATION_DESTS: &str = "def ir_stk_activation_dests (m : IRModule) (k : Nat) (fi : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (mem : IRList IRMemSlot) (na : Nat) (fi2 : Nat) (bl2 : Nat) (pc2 : Nat) (loc2 : IRList IRBinding) (mem2 : IRList IRMemSlot) (na2 : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (hrun : forall (d : IRList Nat), @Eq IRConfig (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk fi bl pc loc d) (@IRList.nil IRFrame)) mem na))) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk fi2 bl2 pc2 loc2 d) (@IRList.nil IRFrame)) mem2 na2))) (hf : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) fi2) (@IROption.some IRFunc fn)) (hb : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) bl2) (@IROption.some IRBlock b)) (hn : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) pc2) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : forall (d : IRList Nat) (r : IRList IRFrame), @Eq IRConfig (ir_steps (Nat.add ir_d1 k) m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk fi bl pc loc d) r) mem na))) (ir_ret_to d r mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk fi2 bl2 pc2 loc2 d) r) mem2 na2) ids)) := fun (d : IRList Nat) (r : IRList IRFrame) => ir_stk_activation m k (IRFrame.mk fi bl pc loc d) mem na (IRFrame.mk fi2 bl2 pc2 loc2 d) mem2 na2 fn b ids rs r (hrun d) hf hb hn";
const SRC_PUSH_CONS: &str = "def ir_push_cons (f : IRFrame) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) (rs : IRList Nat) (g : IRFunc) (vs : IRList IRScalar) : @Eq IRConfig (ir_push (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) rs g vs) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id g) (ir_func_entry g) Nat.zero (ir_bind_params (ir_func_params g) vs (@IRList.nil IRBinding)) rs) (@IRList.cons IRFrame (ir_frame_advance f) rest)) mem na)) := @Eq.refl IRConfig (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id g) (ir_func_entry g) Nat.zero (ir_bind_params (ir_func_params g) vs (@IRList.nil IRBinding)) rs) (@IRList.cons IRFrame (ir_frame_advance f) rest)) mem na))";
const SRC_CALL_PUSH: &str = "def ir_call_push (m : IRModule) (f : IRFrame) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) (fn : IRFunc) (b : IRBlock) (fid : Nat) (args : IRList Nat) (rs : IRList Nat) (g : IRFunc) (hf : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@IROption.some IRFunc fn)) (hb : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@IROption.some IRBlock b)) (hn : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@IROption.some IRNode (IRNode.mk (IRInst.call fid args) rs))) (hg : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) fid) (@IROption.some IRFunc g)) : @Eq IRConfig (ir_step m (IRMachine.mk (@IRList.cons IRFrame f rest) mem na)) (ir_push (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) rs g (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) args)) := @Eq.subst (IROption IRFunc) (fun (o : IROption IRFunc) => @Eq IRConfig (ir_step_f m (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) (ir_frame_block f) (ir_frame_pc f) o) (ir_push (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) rs g (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) args))) (@IROption.some IRFunc fn) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@Eq.symm (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@IROption.some IRFunc fn) hf) (@Eq.subst (IROption IRBlock) (fun (ob : IROption IRBlock) => @Eq IRConfig (ir_step_b m (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) (ir_frame_pc f) ob) (ir_push (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) rs g (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) args))) (@IROption.some IRBlock b) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@Eq.symm (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@IROption.some IRBlock b) hb) (@Eq.subst (IROption IRNode) (fun (on : IROption IRNode) => @Eq IRConfig (ir_step_n m (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) on) (ir_push (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) rs g (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) args))) (@IROption.some IRNode (IRNode.mk (IRInst.call fid args) rs)) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@Eq.symm (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@IROption.some IRNode (IRNode.mk (IRInst.call fid args) rs)) hn) (@Eq.subst (IROption IRFunc) (fun (og : IROption IRFunc) => @Eq IRConfig (@IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) (IRConfig.halted (IROutcome.stuck IRFault.no_func)) (fun (g0 : IRFunc) => ir_push (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) rs g0 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) args)) og) (ir_push (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) rs g (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) args))) (@IROption.some IRFunc g) (ir_func_find (ir_mod_funcs m) fid) (@Eq.symm (IROption IRFunc) (ir_func_find (ir_mod_funcs m) fid) (@IROption.some IRFunc g) hg) (@Eq.refl IRConfig (ir_push (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) rs g (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) args))))))";
const SRC_STK_CLEAR_LZC_MAXZZ_8: &str = "def ir_stk_clear_lzc_maxzz_8 : @Eq Bool (ir_stk_clear ir_d8 ir_lzc_module {INIT}) Bool.true := @Eq.refl Bool Bool.true";
const SRC_STK_CLEAR_LZC_MAXZZ_9: &str = "def ir_stk_clear_lzc_maxzz_9 : @Eq Bool (ir_stk_clear ir_d9 ir_lzc_module {INIT}) Bool.true := @Eq.refl Bool Bool.true";
const SRC_STK_SPLIT_WITNESS_R: &str = "def ir_stk_split_witness_r (rest : IRList IRFrame) : @Eq IROutcome (ir_config_outcome (ir_steps ir_d8 ir_lzc_module (ir_config_stack {INIT} rest))) IROutcome.fuel_out := @Eq.trans IROutcome (ir_config_outcome (ir_steps ir_d8 ir_lzc_module (ir_config_stack {INIT} rest))) (ir_config_outcome (ir_steps ir_d8 ir_lzc_module {INIT})) IROutcome.fuel_out (ir_stk_split_outcome ir_lzc_module rest ir_d8 {INIT} ir_stk_clear_lzc_maxzz_8) ir_lzc_max_running_at_8";
const SRC_STK_SPLIT_WITNESS_F: &str = "def ir_stk_split_witness_f (rest : IRList IRFrame) : @Eq IRConfig (ir_steps ir_d9 ir_lzc_module (ir_config_stack {INIT} rest)) (IRConfig.halted (IROutcome.stuck IRFault.no_func)) := ir_stk_split_halted ir_lzc_module rest ir_d9 {INIT} (IROutcome.stuck IRFault.no_func) ir_stk_clear_lzc_maxzz_9 ir_lzc_max_stuck_at_9";
const SRC_STK_NIL_BREAKS_COMMUTING: &str = "def ir_stk_nil_breaks_commuting (mem : IRList IRMemSlot) (na : Nat) (C : Prop) (h : @Eq IRConfig (ir_step ir_lzb_module (ir_mach_stack (IRMachine.mk (@IRList.nil IRFrame) mem na) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d1 Nat.zero (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame)))) (ir_config_stack (ir_step ir_lzb_module (IRMachine.mk (@IRList.nil IRFrame) mem na)) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d1 Nat.zero (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame)))) : C := ir_bool_false_ne_true C (@Eq.symm Bool (ir_stk_running (ir_step ir_lzb_module (ir_mach_stack (IRMachine.mk (@IRList.nil IRFrame) mem na) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d1 Nat.zero (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame))))) (ir_stk_running (ir_config_stack (ir_step ir_lzb_module (IRMachine.mk (@IRList.nil IRFrame) mem na)) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d1 Nat.zero (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame)))) (ir_eq_cong IRConfig Bool (fun (c1 : IRConfig) => ir_stk_running c1) (ir_step ir_lzb_module (ir_mach_stack (IRMachine.mk (@IRList.nil IRFrame) mem na) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d1 Nat.zero (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame)))) (ir_config_stack (ir_step ir_lzb_module (IRMachine.mk (@IRList.nil IRFrame) mem na)) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d1 Nat.zero (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame))) h))";
const SRC_STK_BOTRET_LZ_B6: &str = "def ir_stk_botret_lz_b6 (ds : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) : @Eq Bool (ir_stk_botret ir_lzb_module (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d6 Nat.zero (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) ds) (@IRList.nil IRFrame)) mem na)) Bool.true := @Eq.refl Bool Bool.true";
const SRC_STK_BOTRET_BREAKS_COMMUTING: &str = "def ir_stk_botret_breaks_commuting (ds : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) (c : IRFrame) (r : IRList IRFrame) (C : Prop) (h : @Eq IRConfig (ir_step ir_lzb_module (ir_mach_stack (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d6 Nat.zero (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) ds) (@IRList.nil IRFrame)) mem na) (@IRList.cons IRFrame c r))) (ir_config_stack (ir_step ir_lzb_module (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d6 Nat.zero (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) ds) (@IRList.nil IRFrame)) mem na)) (@IRList.cons IRFrame c r))) : C := ir_bool_false_ne_true C (@Eq.symm Bool (ir_stk_running (ir_step ir_lzb_module (ir_mach_stack (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d6 Nat.zero (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) ds) (@IRList.nil IRFrame)) mem na) (@IRList.cons IRFrame c r)))) (ir_stk_running (ir_config_stack (ir_step ir_lzb_module (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d6 Nat.zero (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) ds) (@IRList.nil IRFrame)) mem na)) (@IRList.cons IRFrame c r))) (ir_eq_cong IRConfig Bool (fun (c1 : IRConfig) => ir_stk_running c1) (ir_step ir_lzb_module (ir_mach_stack (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d6 Nat.zero (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) ds) (@IRList.nil IRFrame)) mem na) (@IRList.cons IRFrame c r))) (ir_config_stack (ir_step ir_lzb_module (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d6 Nat.zero (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) ds) (@IRList.nil IRFrame)) mem na)) (@IRList.cons IRFrame c r)) h))";

/// The names this stage registers, in registration order.
pub const STACK_SPLIT_NAMES: &[&str] = &[
    "ir_bool_guard_false",
    "ir_bool_guard_rest",
    "ir_bool_guard_intro",
    "ir_stk_clear",
    "ir_stk_clear_zero",
    "ir_stk_clear_succ",
    "ir_stk_clear_halted",
    "ir_stk_nonnil_of_running",
    "ir_stk_clear_of_running",
    "ir_stk_split",
    "ir_stk_split_running",
    "ir_stk_split_halted",
    "ir_config_outcome_stack",
    "ir_stk_split_outcome",
    "ir_stk_botret_hit",
    "ir_stk_split_ret_standalone",
    "ir_stk_split_ret",
    "ir_frame_dests_bind",
    "ir_frame_dests_bind2",
    "ir_frame_dests_advance",
    "ir_frame_dests_goto",
    "ir_frame_dests_set_many",
    "ir_stk_activation_dests",
    "ir_push_cons",
    "ir_call_push",
    "ir_stk_clear_lzc_maxzz_8",
    "ir_stk_clear_lzc_maxzz_9",
    "ir_stk_split_witness_r",
    "ir_stk_split_witness_f",
    "ir_stk_nil_breaks_commuting",
    "ir_stk_botret_lz_b6",
    "ir_stk_botret_breaks_commuting",
];

/// `(source, description)`, positionally paired with [`STACK_SPLIT_NAMES`].
/// A source containing `{INIT}` is a witness at the `ir_lzc` Max(Zero, Zero)
/// run; the placeholder is replaced by `lzc_maxzz_init()` at registration.
const DECLS: &[(&str, &str)] = &[
    (
        SRC_BOOL_GUARD_FALSE,
        "ir_bool_guard_false: from `if b then false else x` being true, b is false. @Bool.rec on b with a premise-passing motive: the false minor is Eq.refl, the true minor's premise reduces to @Eq Bool Bool.false Bool.true and ir_bool_false_ne_true discharges it. The stage has no And, so a conjunction of Bool facts is spelled as this nested @Bool.rec and taken apart by these two lemmas. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BOOL_GUARD_REST,
        "ir_bool_guard_rest: from `if b then false else x` being true, x is true -- the other projection of the same guard, the same @Bool.rec with the false minor returning its premise unchanged. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BOOL_GUARD_INTRO,
        "ir_bool_guard_intro: the converse -- b false and x true make the guard true. One @Eq.subst along @Eq.symm of hb, at the guard's own motive, whose Bool.false instance is hx by iota. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_CLEAR,
        "ir_stk_clear: *** THE RUN PREDICATE OF THE SPLIT. *** True when, for each of the first n steps of the run from c, a RUNNING configuration is in the commuting class -- nonempty frame list (ir_frames_is_nil false) and not a bottom ret (ir_stk_botret false) -- and a HALTED one ends the check (ir_steps leaves it alone, so nothing after it can fail to commute). @Nat.rec generalised over the configuration, the shape of ir_steps itself, with the two tests spelled as nested @Bool.rec guards because the stage has no And. It says nothing about the OUTCOME of any step: a run that faults inside the first n steps is clear. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_CLEAR_ZERO,
        "ir_stk_clear_zero: vacuity pin -- the zero case is true for every configuration, by computation. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_CLEAR_SUCC,
        "ir_stk_clear_succ: vacuity pin -- the successor case at a running machine IS the two guards over the rest of the run, by computation, so the definition is held to this spelling and not only to its name. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_CLEAR_HALTED,
        "ir_stk_clear_halted: a halted configuration is clear at every n -- Nat.rec, both arms Eq.refl. The F case rests on this: once the standalone run has halted, the predicate asks nothing more of it. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_NONNIL_OF_RUNNING,
        "ir_stk_nonnil_of_running: a machine whose step stays RUNNING has a nonempty frame list -- on the empty list ir_step halts stuck no_frame, so the running hypothesis reduces to @Eq Bool Bool.false Bool.true. The first half of `the old running premise implies the new commuting class`; ir_stk_botret_false_of_running (minted) is the second. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_CLEAR_OF_RUNNING,
        "ir_stk_clear_of_running: a run that is still RUNNING after n steps is clear for those n -- so the running-keyed family (ir_stk_steps, ir_stk_activation) is the special case of the split, and a running endpoint at k makes k the FIRST classifier hit. @Nat.rec on n over the configuration: the running arm builds both guards with ir_bool_guard_intro from ir_stk_nonnil_of_running and ir_stk_botret_false_of_running at the one-step premise ir_stk_running_back recovers, and the rest from the induction hypothesis; the halted arm is Eq.refl. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT,
        "ir_stk_split: *** THE SPLIT. *** n steps of a run that stays in the commuting class at every running prefix commute with stacking `rest` beneath the frames -- whatever the run's OUTCOME. Same n on both sides; @Nat.rec on n generalised over the configuration, the succ case ir_stkn_step at the two premises read off the clear predicate by the guard lemmas, then the induction hypothesis; the halted case is definitional (ir_config_stack is the identity on a halted configuration and ir_steps leaves it alone). The running-keyed ir_stk_steps needed the run to be running AT n; this needs only that no prefix is an empty stack or a bottom ret, so a FAULTING run transports too. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_RUNNING,
        "ir_stk_split_running (case R, still running): a clear run that is running at n is, stacked over any `rest`, running at n on the stacked machine -- ir_stk_split then ir_eq_cong of ir_config_stack along the endpoint equation. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_HALTED,
        "ir_stk_split_halted (case F, halted -- faulted or otherwise): a clear run that has halted with outcome o by step n halts with the SAME outcome, at the same n, over EVERY caller stack. This is the case the running-keyed family could not state: a callee that faults faults its caller identically. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CONFIG_OUTCOME_STACK,
        "ir_config_outcome_stack: stacking does not change the outcome reading -- a running configuration reads fuel_out on both sides and a halted one its own outcome. IRConfig.rec, both arms Eq.refl. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_OUTCOME,
        "ir_stk_split_outcome: the split at the OUTCOME level -- for a clear run, the stacked run's ir_config_outcome at n equals the standalone run's, for every caller stack. Covers R (fuel_out) and F (halted o) in one statement, and lets a witness CITE an existing outcome theorem instead of recomputing the configuration. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_BOTRET_HIT,
        "ir_stk_botret_hit (case T, the hit): if a single frame's three fetch lookups resolve to a ret node, the classifier is TRUE there -- the three suspended-lookup @Eq.subst of ir_stk_ret_step at the classifier's Bool layers. With ir_stk_clear_of_running, the T premises of ir_stk_activation are exactly: clear before k, classifier hit at k. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_RET_STANDALONE,
        "ir_stk_split_ret_standalone (case T, standalone side): at the first hit the STANDALONE run halts one step later with IROutcome.ret of the resolved ret operands -- ir_steps_add, the endpoint, then ir_stk_ret_step at the empty caller list, where ir_ret_to halts. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_RET,
        "ir_stk_split_ret (case T, stacked side, through the classifier split): a run clear for k steps whose k-th configuration is a single frame fetching a ret returns, stacked over ANY `rest`, in 1 + k steps through ir_ret_to into `rest` with the head frame's dests and the SAME values the standalone run halts with (ir_stk_split_ret_standalone). ir_steps_add, ir_stk_split_running, ir_stk_ret_step. At a single-frame start this is ir_stk_activation's conclusion, reached from the clear premise instead of the running one. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_FRAME_DESTS_BIND,
        "ir_frame_dests_bind: binding a result leaves a frame's dests untouched, at EVERY frame (IRFrame.rec, the constructor case Eq.refl). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_FRAME_DESTS_BIND2,
        "ir_frame_dests_bind2: so does the two-result bind overflow uses. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_FRAME_DESTS_ADVANCE,
        "ir_frame_dests_advance: so does advancing the pc -- the writer a call applies to the CALLER frame it pushes over. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_FRAME_DESTS_GOTO,
        "ir_frame_dests_goto: so does a jump to another block with its arguments bound. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_FRAME_DESTS_SET_MANY,
        "ir_frame_dests_set_many: so does a return's write of the returned values into the CALLER frame it pops into. With the four above this is every frame writer on the step path: the WRITER half of a general bottom-frame dests invariant. The per-IRInst-arm assembly of that invariant over an ABSTRACT body is NOT built here; it is ir_stk_bot_dests_inv (eval_ir_stack_axes.rs, over the minted ir_bdst family; designs/2026-09-25-e1-axes.md). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_ACTIVATION_DESTS,
        "ir_stk_activation_dests: *** THE DESTS CONNECTION -- ir_stk_activation in the CONTRACT FORM. *** ir_stk_activation returns through `ir_frame_dests fk`, the frame that RETURNS; a callee contract (hc1/hc2 of ir_it_ag_activation) is stated `forall d r` with d on the ENTRY frame. This lemma takes the standalone run in the form that carries the entry's dests to the returning frame -- from IRFrame.mk fi bl pc loc d to IRFrame.mk fi2 bl2 pc2 loc2 d, the SAME d, for every d -- and the fetched ret, and concludes the contract form: for every d and every caller stack r, the stacked run returns through ir_ret_to d r. The connection is ir_frame_dests (IRFrame.mk .. d) = d by iota. What is NOT proved HERE: that every standalone run preserves the bottom frame's dests over an ABSTRACT body -- that is ir_stk_bot_dests_inv, and the form of this lemma that needs no premise about the body is ir_stk_activation_dests_gen (eval_ir_stack_axes.rs); for a concrete body the premise here is discharged by computation at abstract d (ir_stk_split_witness_t does). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PUSH_CONS,
        "ir_push_cons: vacuity pin -- ir_push on a cons machine pushes the callee frame (its id, its entry block, pc 0, its parameters bound to the resolved arguments, dests the call's result ids) over the ADVANCED caller frame over `rest`, heap and counter unchanged. Eq.refl; this is the configuration a callee contract's hypothesis starts from. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CALL_PUSH,
        "ir_call_push: *** THE GENERIC CALL STEP. *** For ANY module and ANY frame whose three fetch lookups resolve to a `call fid args` node, and whose callee id resolves in the module to g, one ir_step pushes g: ir_push (resolved arguments from the head frame) -- see ir_push_cons for the machine it builds. Four suspended lookups, each one @Eq.subst along @Eq.symm (the ir_stk_ret_step idiom); the last motive is ir_it_ag_call_k's body spelled inline, because ir_it_ag_call_k lives in the Full-only itf stage and this lemma belongs to the EvalIr bundle. ir_it_ag_step_call (infer_type's call 1) and ir_hlb_call_step (has_loose_bvars' call) are re-derived through it. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_CLEAR_LZC_MAXZZ_8,
        "ir_stk_clear_lzc_maxzz_8: the classifier computed along a REAL run -- the ir_lzc_module (Level::is_zero with the promoted global) run on Max(Zero, Zero) is in the commuting class at every running prefix of its first 8 steps. Eq.refl: the kernel runs the machine and the classifier together. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_CLEAR_LZC_MAXZZ_9,
        "ir_stk_clear_lzc_maxzz_9: and for its first 9 -- including step 8, the deref frame's `call 2` into a function the module lacks, which FAULTS stuck no_func: a faulting step is not a bottom ret, so the run is still clear. Eq.refl. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_WITNESS_R,
        "ir_stk_split_witness_r: *** WITNESS R. *** The Max(Zero, Zero) run over ir_lzc_module, stacked over ANY caller stack, is STILL RUNNING after 8 steps -- ir_stk_split_outcome at the clear run, then ir_lzc_max_running_at_8, CITED rather than recomputed. The premises of the R case are satisfied at a run the tree already proves. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_WITNESS_F,
        "ir_stk_split_witness_f: *** WITNESS F. *** The same run, stacked over ANY caller stack, HALTS stuck no_func at step 9 -- ir_stk_split_halted at the clear run and ir_lzc_max_stuck_at_9, CITED. A standalone FAULT transported to every caller context, which the running-keyed stacking family cannot state at all. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_NIL_BREAKS_COMMUTING,
        "ir_stk_nil_breaks_commuting: *** THE EMPTY FRAME LIST IS OUTSIDE THE COMMUTING CLASS, kernel-checked. *** At an empty frame list stacked over a caller frame that runs (ir_lzb_module, block 1 of Level::is_zero: const, br), the commuting equation of ir_stkn_step IMPLIES ANYTHING: the standalone step halts stuck no_frame while the stacked step runs the caller, so ir_eq_cong of ir_stk_running turns the equation into @Eq Bool Bool.true Bool.false. This is why ir_stkn_step takes the nonempty premise SEPARATELY from the classifier, which is false on the empty list. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_BOTRET_LZ_B6,
        "ir_stk_botret_lz_b6: the classifier FIRES at a real bottom ret -- a single frame at block 6 of Level::is_zero (its `ret [1]`), for every dests, heap and counter. Eq.refl: the positive polarity at a concrete module, beside the pins' negative ones. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_BOTRET_BREAKS_COMMUTING,
        "ir_stk_botret_breaks_commuting: *** A BOTTOM RET IS OUTSIDE THE COMMUTING CLASS, kernel-checked. *** At the frame ir_stk_botret_lz_b6 classifies, stacked over ANY caller frame c and stack r, the commuting equation implies anything: standalone the ret halts with IROutcome.ret, stacked it pops into c and keeps running. So the classifier excludes exactly a step that genuinely does not commute, and the T case needs its own theorems. DerivedProved, zero axiom_deps.",
    ),
];

impl Specification {
    /// The split keyed on the fetched node. MUST follow
    /// `add_eval_ir_stack_theorems` (for `ir_stk_activation`), which follows
    /// `add_eval_ir_stack_minted` (`ir_stkn_step`, `ir_stk_botret`,
    /// `ir_stk_botret_false_of_running`), and `add_eval_ir_lzc_steps` (the two
    /// ir_lzc run theorems the R and F witnesses cite).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_stack_split(&mut self) -> Result<(), SpecError> {
        let init = lzc_maxzz_init();
        for (source, description) in DECLS {
            self.add_recursive_def(&source.replace("{INIT}", &init), description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sources_balanced_ascii_and_named() {
        assert_eq!(DECLS.len(), STACK_SPLIT_NAMES.len());
        for ((src, _), name) in DECLS.iter().zip(STACK_SPLIT_NAMES) {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
        }
    }

    /// The F witness must name the fault it transports and cite the existing
    /// run theorem; the R witness likewise. A witness that recomputed the run
    /// would say nothing about the premises of the split.
    #[test]
    fn test_witnesses_cite_the_existing_runs() {
        assert!(SRC_STK_SPLIT_WITNESS_F.contains("ir_lzc_max_stuck_at_9"));
        assert!(SRC_STK_SPLIT_WITNESS_F.contains("ir_stk_split_halted"));
        assert!(SRC_STK_SPLIT_WITNESS_R.contains("ir_lzc_max_running_at_8"));
        assert!(SRC_STK_SPLIT_WITNESS_R.contains("ir_stk_split_outcome"));
        assert!(lzc_maxzz_init().starts_with("(ir_init ir_lzc_module "));
    }
}
