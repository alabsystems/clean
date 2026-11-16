// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **The two axes E1's split left open, as theorems** (decision memo §6 Phase
//! E / §11 item 8; statements settled in `designs/2026-09-25-e1-axes.md`),
//! over the families minted by `scripts/gen_stack_axes.py`
//! (`eval_ir_stack_axes_minted.rs`).
//!
//! **Axis 1 -- the bottom frame's dests, over an ABSTRACT body.** E1's
//! `ir_stk_activation_dests` needs the standalone run in a shape that already
//! carries the entry's dests to the returning frame, so it holds only where the
//! run is computed at an abstract `d`. Here the fact is proved for every module
//! and every run, with NO premise: the machine never reads the bottom frame's
//! dests (the only reader is a `ret`, and a bottom `ret` hands them to
//! `ir_ret_to` at an empty caller list, which discards them), so
//!
//! * `ir_bdst_step` / `ir_bdst_steps` -- one step / n steps commute with
//!   rewriting the bottom frame's dests;
//! * `ir_stk_bot_dests_inv` -- every configuration a single-frame run reaches
//!   is a fixed point of setting its bottom dests to the entry frame's, and
//!   `ir_stk_dests_preserved` its reading at a single-frame endpoint;
//! * `ir_stk_activation_dests_gen` -- E1's T case in the `forall d r` contract
//!   form from ONE standalone run at ONE dests list, whatever the body.
//!
//! **Axis 2 -- the module.** `ir_mexto_run` transports a HALTED run to every
//! extension module unless its outcome is a lookup miss (`ir_mext_ok`), and the
//! split's three cases compose with it: `ir_stk_split_halted_mext` (F),
//! `ir_stk_split_running_mext` (R), `ir_stk_split_ret_mext` (T).
//!
//! The witness `ir_bdst_witness_lzd_maxzz` CITES the 107-step derived-module
//! run rather than recomputing it. Registered in BOTH the Full stage list and
//! the EvalIr bundle, after `add_eval_ir_stack_axes_minted`. Every declaration
//! kernel-checked, empty axiom closure, by name. No Or / And / Exists / False.

use super::eval_ir_lzd::{lzd_maxzz_init, lzd_numeral};
use super::{SpecError, Specification};

// ── axis 1: the bottom frame's dests ───────────────────────────────────────
const SRC_BDST_STEP: &str = "def ir_bdst_step (m : IRModule) (s : IRMachine) (d : IRList Nat) : @Eq IRConfig (ir_step m (ir_mach_set_bot s d)) (ir_config_set_bot (ir_step m s) d) := @IRMachine.rec (fun (s0 : IRMachine) => @Eq IRConfig (ir_step m (ir_mach_set_bot s0 d)) (ir_config_set_bot (ir_step m s0) d)) (fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => @IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => @Eq IRConfig (ir_step m (ir_mach_set_bot (IRMachine.mk fs0 mem na) d)) (ir_config_set_bot (ir_step m (IRMachine.mk fs0 mem na)) d)) (@Eq.refl IRConfig (IRConfig.halted (IROutcome.stuck IRFault.no_frame))) (fun (f : IRFrame) (t : IRList IRFrame) (_ : @Eq IRConfig (ir_step m (ir_mach_set_bot (IRMachine.mk t mem na) d)) (ir_config_set_bot (ir_step m (IRMachine.mk t mem na)) d)) => @IRList.rec IRFrame (fun (t0 : IRList IRFrame) => @Eq IRConfig (ir_step m (ir_mach_set_bot (IRMachine.mk (@IRList.cons IRFrame f t0) mem na) d)) (ir_config_set_bot (ir_step m (IRMachine.mk (@IRList.cons IRFrame f t0) mem na)) d)) (@IRFrame.rec (fun (f0 : IRFrame) => @Eq IRConfig (ir_step m (ir_mach_set_bot (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na) d)) (ir_config_set_bot (ir_step m (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na)) d)) (fun (fi : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (ds : IRList Nat) => ir_bdst_step1 m fi bl pc loc ds d mem na) f) (fun (g : IRFrame) (t2 : IRList IRFrame) (_ : @Eq IRConfig (ir_step m (ir_mach_set_bot (IRMachine.mk (@IRList.cons IRFrame f t2) mem na) d)) (ir_config_set_bot (ir_step m (IRMachine.mk (@IRList.cons IRFrame f t2) mem na)) d)) => ir_bdst_step_cons m f g t2 d mem na) t) fs) s";
const SRC_BDST_STEPS: &str = "def ir_bdst_steps (m : IRModule) (d : IRList Nat) (n : Nat) : forall (c : IRConfig), @Eq IRConfig (ir_steps n m (ir_config_set_bot c d)) (ir_config_set_bot (ir_steps n m c) d) := @Nat.rec (fun (k : Nat) => forall (c : IRConfig), @Eq IRConfig (ir_steps k m (ir_config_set_bot c d)) (ir_config_set_bot (ir_steps k m c) d)) (fun (c : IRConfig) => @Eq.refl IRConfig (ir_config_set_bot c d)) (fun (k : Nat) (ih : forall (c : IRConfig), @Eq IRConfig (ir_steps k m (ir_config_set_bot c d)) (ir_config_set_bot (ir_steps k m c) d)) => fun (c : IRConfig) => @IRConfig.rec (fun (c0 : IRConfig) => @Eq IRConfig (ir_steps (Nat.succ k) m (ir_config_set_bot c0 d)) (ir_config_set_bot (ir_steps (Nat.succ k) m c0) d)) (fun (s : IRMachine) => @Eq.trans IRConfig (ir_steps k m (ir_step m (ir_mach_set_bot s d))) (ir_steps k m (ir_config_set_bot (ir_step m s) d)) (ir_config_set_bot (ir_steps k m (ir_step m s)) d) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_steps k m c1) (ir_step m (ir_mach_set_bot s d)) (ir_config_set_bot (ir_step m s) d) (ir_bdst_step m s d)) (ih (ir_step m s))) (fun (o : IROutcome) => @Eq.refl IRConfig (IRConfig.halted o)) c) n";
const SRC_CONFIG_OUTCOME_SET_BOT: &str = "def ir_config_outcome_set_bot (c : IRConfig) (d : IRList Nat) : @Eq IROutcome (ir_config_outcome (ir_config_set_bot c d)) (ir_config_outcome c) := @IRConfig.rec (fun (c0 : IRConfig) => @Eq IROutcome (ir_config_outcome (ir_config_set_bot c0 d)) (ir_config_outcome c0)) (fun (_ : IRMachine) => @Eq.refl IROutcome IROutcome.fuel_out) (fun (o : IROutcome) => @Eq.refl IROutcome o) c";
const SRC_FRAME_SET_DESTS_SELF: &str = "def ir_frame_set_dests_self (f : IRFrame) : @Eq IRFrame (ir_frame_set_dests f (ir_frame_dests f)) f := @IRFrame.rec (fun (f0 : IRFrame) => @Eq IRFrame (ir_frame_set_dests f0 (ir_frame_dests f0)) f0) (fun (fi : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (ds : IRList Nat) => @Eq.refl IRFrame (IRFrame.mk fi bl pc loc ds)) f";
const SRC_STK_BOT_DESTS_INV: &str = "def ir_stk_bot_dests_inv (m : IRModule) (k : Nat) (f0 : IRFrame) (mem : IRList IRMemSlot) (na : Nat) : @Eq IRConfig (ir_config_set_bot (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (ir_frame_dests f0)) (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) := @Eq.trans IRConfig (ir_config_set_bot (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (ir_frame_dests f0)) (ir_steps k m (ir_config_set_bot (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na)) (ir_frame_dests f0))) (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (@Eq.symm IRConfig (ir_steps k m (ir_config_set_bot (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na)) (ir_frame_dests f0))) (ir_config_set_bot (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (ir_frame_dests f0)) (ir_bdst_steps m (ir_frame_dests f0) k (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na)))) (ir_eq_cong IRFrame IRConfig (fun (x : IRFrame) => ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame x (@IRList.nil IRFrame)) mem na))) (ir_frame_set_dests f0 (ir_frame_dests f0)) f0 (ir_frame_set_dests_self f0))";
const SRC_CONFIG_HEAD_DESTS: &str = "def ir_config_head_dests (c : IRConfig) : IRList Nat := @IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRList Nat) (@IRList.nil Nat) (fun (x : IRFrame) (_ : IRList IRFrame) (_ : IRList Nat) => ir_frame_dests x) (ir_config_frames c)";
const SRC_STK_DESTS_PRESERVED: &str = "def ir_stk_dests_preserved (m : IRModule) (k : Nat) (f0 : IRFrame) (mem : IRList IRMemSlot) (na : Nat) (fk : IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (hrun : @Eq IRConfig (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2))) : @Eq (IRList Nat) (ir_frame_dests fk) (ir_frame_dests f0) := @Eq.symm (IRList Nat) (ir_frame_dests f0) (ir_frame_dests fk) (ir_eq_cong IRConfig (IRList Nat) (fun (c1 : IRConfig) => ir_config_head_dests c1) (ir_config_set_bot (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2)) (ir_frame_dests f0)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2)) (@Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq IRConfig (ir_config_set_bot c1 (ir_frame_dests f0)) c1) (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2)) hrun (ir_stk_bot_dests_inv m k f0 mem na)))";
const SRC_RESOLVE_SET_DESTS: &str = "def ir_resolve_set_dests (fk : IRFrame) (d : IRList Nat) (r : IRList IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (ids : IRList Nat) : @Eq (IRList IRScalar) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_dests fk d) r) mem2 na2) ids) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids) := @IRList.rec Nat (fun (ids0 : IRList Nat) => @Eq (IRList IRScalar) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_dests fk d) r) mem2 na2) ids0) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids0)) (@Eq.refl (IRList IRScalar) (@IRList.nil IRScalar)) (fun (i : Nat) (ids2 : IRList Nat) (ih : @Eq (IRList IRScalar) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_dests fk d) r) mem2 na2) ids2) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids2)) => ir_eq_cong (IRList IRScalar) (IRList IRScalar) (fun (vs : IRList IRScalar) => @IRList.cons IRScalar (ir_frame_get fk i) vs) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_dests fk d) r) mem2 na2) ids2) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids2) ih) ids";
const SRC_STK_ACTIVATION_DESTS_GEN: &str = "def ir_stk_activation_dests_gen (m : IRModule) (k : Nat) (f0 : IRFrame) (mem : IRList IRMemSlot) (na : Nat) (fk : IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (hrun : @Eq IRConfig (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2))) (hf : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func fk)) (@IROption.some IRFunc fn)) (hb : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block fk)) (@IROption.some IRBlock b)) (hn : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc fk)) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : forall (d : IRList Nat) (r : IRList IRFrame), @Eq IRConfig (ir_steps (Nat.add ir_d1 k) m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_dests f0 d) r) mem na))) (ir_ret_to d r mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids)) := fun (d : IRList Nat) (r : IRList IRFrame) => @Eq.subst (IRList IRScalar) (fun (vs : IRList IRScalar) => @Eq IRConfig (ir_steps (Nat.add ir_d1 k) m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_dests f0 d) r) mem na))) (ir_ret_to d r mem2 na2 vs)) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_dests fk d) r) mem2 na2) ids) (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2) ids) (ir_resolve_set_dests fk d r mem2 na2 ids) (ir_stk_activation m k (ir_frame_set_dests f0 d) mem na (ir_frame_set_dests fk d) mem2 na2 fn b ids rs r (@Eq.trans IRConfig (ir_steps k m (ir_config_set_bot (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na)) d)) (ir_config_set_bot (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) d) (ir_config_set_bot (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2)) d) (ir_bdst_steps m d k (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_config_set_bot c1 d) (ir_steps k m (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame f0 (@IRList.nil IRFrame)) mem na))) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2)) hrun)) hf hb hn)";
const SRC_BDST_LZD_MAXZZ_CFG: &str = "def ir_bdst_lzd_maxzz_cfg (d : IRList Nat) : @Eq IROutcome (ir_config_outcome (ir_steps {N107} ir_lzd_module (ir_config_set_bot {INIT} d))) (ir_config_outcome (ir_config_set_bot (ir_steps {N107} ir_lzd_module {INIT}) d)) := ir_eq_cong IRConfig IROutcome ir_config_outcome (ir_steps {N107} ir_lzd_module (ir_config_set_bot {INIT} d)) (ir_config_set_bot (ir_steps {N107} ir_lzd_module {INIT}) d) (ir_bdst_steps ir_lzd_module d {N107} {INIT})";
const SRC_BDST_LZD_MAXZZ_OUT: &str = "def ir_bdst_lzd_maxzz_out (d : IRList Nat) : @Eq IROutcome (ir_config_outcome (ir_config_set_bot (ir_steps {N107} ir_lzd_module {INIT}) d)) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := @Eq.trans IROutcome (ir_config_outcome (ir_config_set_bot (ir_steps {N107} ir_lzd_module {INIT}) d)) (ir_config_outcome (ir_steps {N107} ir_lzd_module {INIT})) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) (ir_config_outcome_set_bot (ir_steps {N107} ir_lzd_module {INIT}) d) ir_lzd_max_zz_returns_true_at_107";
const SRC_BDST_WITNESS_LZD_MAXZZ: &str = "def ir_bdst_witness_lzd_maxzz (d : IRList Nat) : @Eq IROutcome (ir_config_outcome (ir_steps {N107} ir_lzd_module (ir_config_set_bot {INIT} d))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := @Eq.trans IROutcome (ir_config_outcome (ir_steps {N107} ir_lzd_module (ir_config_set_bot {INIT} d))) (ir_config_outcome (ir_config_set_bot (ir_steps {N107} ir_lzd_module {INIT}) d)) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) (ir_bdst_lzd_maxzz_cfg d) (ir_bdst_lzd_maxzz_out d)";

// ── axis 2: the module, and the split across it ────────────────────────────
const MEXT_BLOCK: &str = "(fs0 : IRList IRFunc) (gs0 : IRList IRGlobal) (fs : IRList IRFunc) (gs : IRList IRGlobal) (hf : forall (kf : Nat) (gf : IRFunc), @Eq (IROption IRFunc) (ir_func_find fs0 kf) (@IROption.some IRFunc gf) -> @Eq (IROption IRFunc) (ir_func_find fs kf) (@IROption.some IRFunc gf)) (hg : forall (kg : Nat) (gg : IRGlobal), @Eq (IROption IRGlobal) (ir_global_find gs0 kg) (@IROption.some IRGlobal gg) -> @Eq (IROption IRGlobal) (ir_global_find gs kg) (@IROption.some IRGlobal gg))";
const SRC_MEXTO_RUN: &str = "def ir_mexto_run {MB} (k : Nat) (c : IRConfig) (o : IROutcome) (hh : @Eq IRConfig (ir_steps k (IRModule.mk fs0 gs0) c) (IRConfig.halted o)) (hok : @Eq Bool (ir_mext_ok (IRConfig.halted o)) Bool.true) : @Eq IRConfig (ir_steps k (IRModule.mk fs gs) c) (IRConfig.halted o) := @Eq.trans IRConfig (ir_steps k (IRModule.mk fs gs) c) (ir_steps k (IRModule.mk fs0 gs0) c) (IRConfig.halted o) (@Eq.symm IRConfig (ir_steps k (IRModule.mk fs0 gs0) c) (ir_steps k (IRModule.mk fs gs) c) (ir_mexto_steps fs0 gs0 fs gs hf hg k c (@Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq Bool (ir_mext_ok c1) Bool.true) (IRConfig.halted o) (ir_steps k (IRModule.mk fs0 gs0) c) (@Eq.symm IRConfig (ir_steps k (IRModule.mk fs0 gs0) c) (IRConfig.halted o) hh) hok))) hh";
const SRC_STK_SPLIT_HALTED_MEXT: &str = "def ir_stk_split_halted_mext {MB} (rest : IRList IRFrame) (n : Nat) (c : IRConfig) (o : IROutcome) (hcl : @Eq Bool (ir_stk_clear n (IRModule.mk fs0 gs0) c) Bool.true) (hh : @Eq IRConfig (ir_steps n (IRModule.mk fs0 gs0) c) (IRConfig.halted o)) (hok : @Eq Bool (ir_mext_ok (IRConfig.halted o)) Bool.true) : @Eq IRConfig (ir_steps n (IRModule.mk fs gs) (ir_config_stack c rest)) (IRConfig.halted o) := ir_mexto_run fs0 gs0 fs gs hf hg n (ir_config_stack c rest) o (ir_stk_split_halted (IRModule.mk fs0 gs0) rest n c o hcl hh) hok";
const SRC_STK_SPLIT_RUNNING_MEXT: &str = "def ir_stk_split_running_mext {MB} (rest : IRList IRFrame) (n : Nat) (c : IRConfig) (s2 : IRMachine) (hcl : @Eq Bool (ir_stk_clear n (IRModule.mk fs0 gs0) c) Bool.true) (hr : @Eq IRConfig (ir_steps n (IRModule.mk fs0 gs0) c) (IRConfig.running s2)) : @Eq IRConfig (ir_steps n (IRModule.mk fs gs) (ir_config_stack c rest)) (IRConfig.running (ir_mach_stack s2 rest)) := ir_mext_run fs0 gs0 fs gs hf hg n (ir_config_stack c rest) (ir_mach_stack s2 rest) (ir_stk_split_running (IRModule.mk fs0 gs0) rest n c s2 hcl hr)";
const SRC_STK_SPLIT_RET_MEXT: &str = "def ir_stk_split_ret_mext {MB} (k : Nat) (c : IRConfig) (fk : IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (rest : IRList IRFrame) (hcl : @Eq Bool (ir_stk_clear k (IRModule.mk fs0 gs0) c) Bool.true) (hr : @Eq IRConfig (ir_steps k (IRModule.mk fs0 gs0) c) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame fk (@IRList.nil IRFrame)) mem2 na2))) (hfn : @Eq (IROption IRFunc) (ir_func_find fs0 (ir_frame_func fk)) (@IROption.some IRFunc fn)) (hbk : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block fk)) (@IROption.some IRBlock b)) (hnd : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc fk)) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : @Eq IRConfig (ir_steps (Nat.add ir_d1 k) (IRModule.mk fs gs) (ir_config_stack c rest)) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2) ids)) := @Eq.trans IRConfig (ir_steps (Nat.add ir_d1 k) (IRModule.mk fs gs) (ir_config_stack c rest)) (ir_steps (Nat.add ir_d1 k) (IRModule.mk fs0 gs0) (ir_config_stack c rest)) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2) ids)) (@Eq.symm IRConfig (ir_steps (Nat.add ir_d1 k) (IRModule.mk fs0 gs0) (ir_config_stack c rest)) (ir_steps (Nat.add ir_d1 k) (IRModule.mk fs gs) (ir_config_stack c rest)) (ir_mexto_steps fs0 gs0 fs gs hf hg (Nat.add ir_d1 k) (ir_config_stack c rest) (@Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq Bool (ir_mext_ok c1) Bool.true) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2) ids)) (ir_steps (Nat.add ir_d1 k) (IRModule.mk fs0 gs0) (ir_config_stack c rest)) (@Eq.symm IRConfig (ir_steps (Nat.add ir_d1 k) (IRModule.mk fs0 gs0) (ir_config_stack c rest)) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2) ids)) (ir_stk_split_ret (IRModule.mk fs0 gs0) k c fk mem2 na2 fn b ids rs rest hcl hr hfn hbk hnd)) (ir_mext_ok_ret_to (ir_frame_dests fk) mem2 na2 (ir_resolve (IRMachine.mk (@IRList.cons IRFrame fk rest) mem2 na2) ids) rest)))) (ir_stk_split_ret (IRModule.mk fs0 gs0) k c fk mem2 na2 fn b ids rs rest hcl hr hfn hbk hnd)";

/// The names this stage registers, in registration order.
pub const STACK_AXES_NAMES: &[&str] = &[
    "ir_bdst_step",
    "ir_bdst_steps",
    "ir_config_outcome_set_bot",
    "ir_frame_set_dests_self",
    "ir_stk_bot_dests_inv",
    "ir_config_head_dests",
    "ir_stk_dests_preserved",
    "ir_resolve_set_dests",
    "ir_stk_activation_dests_gen",
    "ir_bdst_lzd_maxzz_cfg",
    "ir_bdst_lzd_maxzz_out",
    "ir_bdst_witness_lzd_maxzz",
    "ir_mexto_run",
    "ir_stk_split_halted_mext",
    "ir_stk_split_running_mext",
    "ir_stk_split_ret_mext",
];

/// `(source, description)`, positionally paired with [`STACK_AXES_NAMES`].
/// `{MB}` is the module-extension block (two modules, `hf`, `hg`); `{INIT}`
/// and `{N107}` are the derived-module Max(Zero, Zero) run's initial
/// configuration and step count, spelled exactly as the theorem the witness
/// cites spells them.
const DECLS: &[(&str, &str)] = &[
    (
        SRC_BDST_STEP,
        "ir_bdst_step: *** ONE STEP COMMUTES WITH REWRITING THE BOTTOM FRAME'S DESTS -- at EVERY module and EVERY machine, with NO premise. *** IRMachine.rec, @IRList.rec on the frames: the empty list is stuck no_frame on both sides (Eq.refl); a single frame is ir_bdst_step1 after @IRFrame.rec (the executing frame IS the bottom one, so the field that changes belongs to the frame that runs); a frame with a caller beneath it is ir_bdst_step_cons. The machine never reads the bottom frame's dests: the only reader is a ret, and a bottom ret hands them to ir_ret_to at an empty caller list, which discards them. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BDST_STEPS,
        "ir_bdst_steps: n steps likewise -- @Nat.rec on n generalised over the configuration, the shape of ir_steps: the running case is ir_bdst_step then the induction hypothesis, the halted case is @Eq.refl (ir_config_set_bot is the identity on a halted configuration). Unconditional: it holds for a run that faults, returns, calls or runs out of fuel alike. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CONFIG_OUTCOME_SET_BOT,
        "ir_config_outcome_set_bot: rewriting the bottom dests does not change the outcome reading -- a running configuration reads fuel_out on both sides, a halted one its own outcome. IRConfig.rec, both arms Eq.refl. With ir_bdst_steps it transports an OUTCOME theorem to every entry dests. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_FRAME_SET_DESTS_SELF,
        "ir_frame_set_dests_self: setting a frame's dests to its own dests is the identity -- IRFrame.rec, the constructor case @Eq.refl (eta for the frame record, stated as a lemma because the kernel is not asked to use structure eta). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_BOT_DESTS_INV,
        "ir_stk_bot_dests_inv: *** THE BOTTOM-FRAME DESTS INVARIANT OVER AN ABSTRACT BODY, the fact E1 left open. *** For every module, every entry frame f0 and every k, the configuration k steps into the run from the single frame f0 is a FIXED POINT of setting its bottom dests to f0's own: whatever the body does -- calls, returns into the bottom frame, faults -- the bottom frame keeps the entry's dests. NO premise. ir_bdst_steps at d := dests f0, then ir_frame_set_dests_self. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CONFIG_HEAD_DESTS,
        "ir_config_head_dests: the dests of a configuration's first frame (the empty list on a halted configuration or an empty frame list) -- the projection ir_stk_dests_preserved reads the invariant through. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_DESTS_PRESERVED,
        "ir_stk_dests_preserved: the invariant read at a single-frame endpoint -- if the run from [f0] is running at a single frame [fk] after k steps, then dests fk = dests f0, for EVERY body. ir_stk_bot_dests_inv rewritten along the endpoint equation, then ir_eq_cong of ir_config_head_dests. This is exactly the connection ir_stk_activation's conclusion (the returning frame's dests) and a callee contract's forall-d form (the entry frame's dests) needed, and E1 could only obtain it by computing the body. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_RESOLVE_SET_DESTS,
        "ir_resolve_set_dests: resolving a return's operands reads the locals of the executing frame and nothing else, so it is the same list at the rewritten frame over any caller stack as at the standalone single frame. @IRList.rec on the ids, the cons case ir_eq_cong over @IRList.cons of the head read. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_ACTIVATION_DESTS_GEN,
        "ir_stk_activation_dests_gen: *** E1's T CASE IN THE CONTRACT FORM, OVER AN ABSTRACT BODY. *** From ONE standalone run -- the single frame f0 reaching a single frame fk that fetches a ret, at whatever dests f0 happens to carry -- conclude, for EVERY dests d and EVERY caller stack r, that the run entered at f0 with its dests rewritten to d returns in 1 + k steps through ir_ret_to d r with exactly the values the standalone run halts with. E1's ir_stk_activation_dests needed the run at every d with the SAME d at both ends, which only a body computed at an abstract d supplies; this needs no premise about the body at all. ir_stk_activation at the rewritten frames, its run obtained by ir_bdst_steps from the one given, the fetch premises reused as they are (a rewritten frame fetches exactly what the original does), the returned values transported by ir_resolve_set_dests. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BDST_LZD_MAXZZ_CFG,
        "ir_bdst_lzd_maxzz_cfg: the first half of the witness below -- ir_bdst_steps at the derived-module Max(Zero, Zero) run, read through ir_config_outcome. Split out as its own declaration because the same content spelled as ONE @Eq.trans term did not finish elaborating in a debug build in over ten minutes, while the three halves each register in well under a second (measured 2026-09-25, EvalIr scratchpad); the kernel checks the same facts either way. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BDST_LZD_MAXZZ_OUT,
        "ir_bdst_lzd_maxzz_out: the second half -- rewriting the bottom dests does not change the outcome (ir_config_outcome_set_bot), then ir_lzd_max_zz_returns_true_at_107 CITED. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BDST_WITNESS_LZD_MAXZZ,
        "ir_bdst_witness_lzd_maxzz: *** WITNESS, THROUGH CALLS AND RETURNS. *** The derived five-body module's Max(Zero, Zero) run -- 107 steps through the compiler's own bodies for the deref, as_deref, expect and Arc::deref, every one of them a push over the bottom frame and a return into it -- entered with ANY dests d on its bottom frame, still returns [bool true]. @Eq.trans of the two halves above, ir_lzd_max_zz_returns_true_at_107 CITED rather than recomputed: the 107-step run the tree already proves at the empty dests is transported, not re-executed. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_MEXTO_RUN,
        "ir_mexto_run: *** THE MODULE AXIS FOR A HALTED RUN (E1's F case). *** A run in M0 that halts with outcome o halts with the SAME o in every extension M (hf / hg) unless o is a lookup miss (ir_mext_ok) -- ir_mexto_steps at the halted endpoint. The running-keyed ir_mext_run could transport only a run still running; this is the case a callee that FAULTS -- or panics sanctionedly, or returns -- needs. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_HALTED_MEXT,
        "ir_stk_split_halted_mext: *** F ACROSS BOTH AXES. *** A callee run clear in its OWN module M0 that halts with o -- not a lookup miss -- halts with o over EVERY caller stack in EVERY extension of M0: ir_stk_split_halted in M0, then ir_mexto_run. The composition E1's design note said F could not make, because a lookup that misses in a small module is exactly what an extension can cure -- and ir_mext_ok is exactly the exclusion of those two outcomes. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_RUNNING_MEXT,
        "ir_stk_split_running_mext: R across both axes -- a clear run of M0 still running at n is, over every caller stack, still running at n in every extension of M0: ir_stk_split_running then the running-keyed ir_mext_run. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_RET_MEXT,
        "ir_stk_split_ret_mext: T across both axes -- E1's ir_stk_split_ret premises in M0 (clear for k, a single frame fetching ret at k) give, over every caller stack and in every extension of M0, the return into that stack in 1 + k steps. The outcome-keyed twin carries it even when the return is the LAST thing the run does (at an empty caller stack ir_ret_to halts, which the running-keyed ir_mext_run cannot transport); ir_mext_ok_ret_to discharges the premise at every caller stack. DerivedProved, zero axiom_deps.",
    ),
];

/// A declaration's source with the stage's placeholders expanded.
fn expand(source: &str) -> String {
    source
        .replace("{MB}", MEXT_BLOCK)
        .replace("{INIT}", &lzd_maxzz_init())
        .replace("{N107}", &lzd_numeral(107))
}

impl Specification {
    /// The two axes' theorems. MUST follow `add_eval_ir_stack_axes_minted`
    /// (the `ir_bdst_*` / `ir_mexto_*` families and `ir_mext_ok`),
    /// `add_eval_ir_stack_split` (the split's three cases),
    /// `add_eval_ir_stack_theorems` (`ir_stk_activation`, `ir_mext_run`) and
    /// `add_eval_ir_lzd_steps` (the run the witness cites).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_stack_axes(&mut self) -> Result<(), SpecError> {
        for (source, description) in DECLS {
            self.add_recursive_def(&expand(source), description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sources_balanced_ascii_and_named() {
        assert_eq!(DECLS.len(), STACK_AXES_NAMES.len());
        for ((src, _), name) in DECLS.iter().zip(STACK_AXES_NAMES) {
            let src = expand(src);
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
            assert!(!src.contains('{'), "{name}: an unexpanded placeholder");
        }
    }

    /// The general theorems take NO premise about the body: the dests theorems
    /// quantify the module, and the invariant has no hypothesis at all.
    #[test]
    fn test_the_dests_theorems_are_premise_free_over_the_body() {
        let header = |src: &str| src.split(" := ").next().unwrap_or_default().to_string();
        let inv = header(SRC_STK_BOT_DESTS_INV);
        assert!(inv.contains("(m : IRModule)") && !inv.contains("(h"));
        let step = header(SRC_BDST_STEP);
        assert!(step.contains("(m : IRModule) (s : IRMachine)") && !step.contains("(h"));
        // The general T case takes ONE run, not a forall-d run.
        let general = header(SRC_STK_ACTIVATION_DESTS_GEN);
        assert!(!general.contains("(hrun : forall"), "{general}");
        assert!(general.contains("forall (d : IRList Nat) (r : IRList IRFrame)"));
    }

    /// The witness CITES the existing run; it does not recompute it.
    #[test]
    fn test_the_witness_cites_the_existing_run() {
        assert!(SRC_BDST_LZD_MAXZZ_OUT.contains("ir_lzd_max_zz_returns_true_at_107"));
        assert!(SRC_BDST_LZD_MAXZZ_CFG.contains("ir_bdst_steps"));
        assert!(SRC_BDST_WITNESS_LZD_MAXZZ.contains("ir_bdst_lzd_maxzz_cfg d"));
        assert!(SRC_BDST_WITNESS_LZD_MAXZZ.contains("ir_bdst_lzd_maxzz_out d"));
    }
}
