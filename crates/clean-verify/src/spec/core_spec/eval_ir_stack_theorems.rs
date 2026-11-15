// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! The frame-stacking family's HAND-AUTHORED theorems that sit ABOVE the minted
//! layer: S3 `ir_stk_steps` and S5 `ir_stk_activation` over `ir_stk_step`, and
//! `ir_mext_run`, the module-extension transport of a standalone run over
//! `ir_mext_steps`. Their statements are `plan_lemma_statement` S3/S5 verbatim
//! (2026-09-20). Registered AFTER `add_eval_ir_stack_minted`, which is where
//! `ir_stk_step` / `ir_mext_steps` live; `eval_ir_stack.rs` holds the foundation
//! and the two theorems that need no minted term (S2, S4).
//!
//! WHAT THE THREE SAY.
//! * `ir_stk_steps` (S3): `n` steps of a run that is still RUNNING after them
//!   commute with stacking `rest` beneath the frames -- same `n` on both sides,
//!   by Nat.rec on `n` generalised over the configuration; the succ case is
//!   `ir_stk_step` (one step) under `ir_stk_running_back` (S2), the halted case
//!   is definitional.
//! * `ir_stk_activation` (S5): THE COMPOSITIONAL CALL RULE. A callee whose
//!   STANDALONE run (`rest = nil`) reaches a running pre-return configuration
//!   in `k` steps, and whose head frame then FETCHES a `ret`, returns into ANY
//!   caller stack `rest` in `Nat.add ir_d1 k` steps, popping through
//!   `ir_ret_to` with the dests read off the head frame. The premise is the
//!   running pre-return configuration on purpose: an A4-shaped `ir_eval ... =
//!   ret [v]` fact erases the heap and the counter and could never be lifted
//!   (plan_risks 7c).
//! * `ir_mext_run`: a run that reaches a RUNNING configuration in a module
//!   `IRModule.mk fs0 gs0` reaches the same configuration in any module whose
//!   function and global lookups extend it on every hit (`hf`, `hg`) -- the
//!   module axis, which is the binding blocker for infer_type (plan_risks 9): a
//!   callee's closure is proved in a module holding only that closure and then
//!   carried into the whole derived module.
//!
//! Every proof term is Eq.trans / Eq.subst / ir_eq_cong over the minted and
//! foundation lemmas; no new axioms, and the census test asserts the closures
//! are empty.

use super::{SpecError, Specification};

const SRC_STK_STEPS: &str = "def ir_stk_steps (m : IRModule) (rest : IRList IRFrame) (n : Nat) : forall (c : IRConfig), Eq Bool (ir_stk_running (ir_steps n m c)) Bool.true -> Eq IRConfig (ir_steps n m (ir_config_stack c rest)) (ir_config_stack (ir_steps n m c) rest) := Nat.rec (fun (k : Nat) => forall (c : IRConfig), Eq Bool (ir_stk_running (ir_steps k m c)) Bool.true -> Eq IRConfig (ir_steps k m (ir_config_stack c rest)) (ir_config_stack (ir_steps k m c) rest)) (fun (c : IRConfig) (_ : Eq Bool (ir_stk_running (ir_steps Nat.zero m c)) Bool.true) => Eq.refl IRConfig (ir_config_stack c rest)) (fun (k : Nat) (ih : forall (c : IRConfig), Eq Bool (ir_stk_running (ir_steps k m c)) Bool.true -> Eq IRConfig (ir_steps k m (ir_config_stack c rest)) (ir_config_stack (ir_steps k m c) rest)) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => Eq Bool (ir_stk_running (ir_steps (Nat.succ k) m c0)) Bool.true -> Eq IRConfig (ir_steps (Nat.succ k) m (ir_config_stack c0 rest)) (ir_config_stack (ir_steps (Nat.succ k) m c0) rest)) (fun (s : IRMachine) (hrun : Eq Bool (ir_stk_running (ir_steps (Nat.succ k) m (IRConfig.running s))) Bool.true) => Eq.trans IRConfig (ir_steps k m (ir_step m (ir_mach_stack s rest))) (ir_steps k m (ir_config_stack (ir_step m s) rest)) (ir_config_stack (ir_steps k m (ir_step m s)) rest) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_steps k m c1) (ir_step m (ir_mach_stack s rest)) (ir_config_stack (ir_step m s) rest) (ir_stk_step m s rest (ir_stk_running_back m k (ir_step m s) hrun))) (ih (ir_step m s) hrun)) (fun (o : IROutcome) (_ : Eq Bool (ir_stk_running (ir_steps (Nat.succ k) m (IRConfig.halted o))) Bool.true) => Eq.refl IRConfig (IRConfig.halted o)) c) n";
const SRC_STK_ACTIVATION: &str = "def ir_stk_activation (m : IRModule) (k : Nat) (f0 : IRFrame) (mem : IRList IRMemSlot) (na : Nat) (fk : IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (rest : IRList IRFrame) (hrun : Eq IRConfig (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 (IRList.nil IRFrame)) mem na))) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2))) (hf : Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func fk)) (IROption.some IRFunc fn)) (hb : Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block fk)) (IROption.some IRBlock b)) (hn : Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc fk)) (IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : Eq IRConfig (ir_steps (Nat.add ir_d1 k) m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 rest) mem na))) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (IRList.cons IRFrame fk rest) mem2 na2) ids)) := Eq.trans IRConfig (ir_steps (Nat.add ir_d1 k) m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 rest) mem na))) (ir_steps ir_d1 m (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 rest) mem na)))) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (IRList.cons IRFrame fk rest) mem2 na2) ids)) (ir_steps_add m ir_d1 k (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 rest) mem na))) (Eq.trans IRConfig (ir_steps ir_d1 m (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 rest) mem na)))) (ir_steps ir_d1 m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk rest) mem2 na2))) (ir_ret_to (ir_frame_dests fk) rest mem2 na2 (ir_resolve (IRMachine.mk (IRList.cons IRFrame fk rest) mem2 na2) ids)) (ir_eq_cong IRConfig IRConfig (fun (c : IRConfig) => ir_steps ir_d1 m c) (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 rest) mem na))) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk rest) mem2 na2)) (Eq.trans IRConfig (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 rest) mem na))) (ir_config_stack (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 (IRList.nil IRFrame)) mem na))) rest) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk rest) mem2 na2)) (ir_stk_steps m rest k (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 (IRList.nil IRFrame)) mem na)) (Eq.subst IRConfig (fun (c : IRConfig) => Eq Bool (ir_stk_running c) Bool.true) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2)) (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 (IRList.nil IRFrame)) mem na))) (Eq.symm IRConfig (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 (IRList.nil IRFrame)) mem na))) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2)) hrun) (Eq.refl Bool Bool.true))) (ir_eq_cong IRConfig IRConfig (fun (c : IRConfig) => ir_config_stack c rest) (ir_steps k m (IRConfig.running (IRMachine.mk (IRList.cons IRFrame f0 (IRList.nil IRFrame)) mem na))) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2)) hrun))) (ir_stk_ret_step m fk rest mem2 na2 fn b ids rs hf hb hn))";
const SRC_MEXT_RUN: &str = "def ir_mext_run (fs0 : IRList IRFunc) (gs0 : IRList IRGlobal) (fs : IRList IRFunc) (gs : IRList IRGlobal) (hf : forall (kf : Nat) (gf : IRFunc), Eq (IROption IRFunc) (ir_func_find fs0 kf) (IROption.some IRFunc gf) -> Eq (IROption IRFunc) (ir_func_find fs kf) (IROption.some IRFunc gf)) (hg : forall (kg : Nat) (gg : IRGlobal), Eq (IROption IRGlobal) (ir_global_find gs0 kg) (IROption.some IRGlobal gg) -> Eq (IROption IRGlobal) (ir_global_find gs kg) (IROption.some IRGlobal gg)) (k : Nat) (c : IRConfig) (s2 : IRMachine) (hrun : Eq IRConfig (ir_steps k (IRModule.mk fs0 gs0) c) (IRConfig.running s2)) : Eq IRConfig (ir_steps k (IRModule.mk fs gs) c) (IRConfig.running s2) := Eq.trans IRConfig (ir_steps k (IRModule.mk fs gs) c) (ir_steps k (IRModule.mk fs0 gs0) c) (IRConfig.running s2) (Eq.symm IRConfig (ir_steps k (IRModule.mk fs0 gs0) c) (ir_steps k (IRModule.mk fs gs) c) (ir_mext_steps fs0 gs0 fs gs hf hg k c (Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_stk_running c1) Bool.true) (IRConfig.running s2) (ir_steps k (IRModule.mk fs0 gs0) c) (Eq.symm IRConfig (ir_steps k (IRModule.mk fs0 gs0) c) (IRConfig.running s2) hrun) (Eq.refl Bool Bool.true)))) hrun";

/// The names this stage registers, in registration order.
pub const STACK_THEOREM_NAMES: &[&str] = &["ir_stk_steps", "ir_stk_activation", "ir_mext_run"];

impl Specification {
    /// S3, S5 and the module-extension transport. MUST follow
    /// `add_eval_ir_stack_minted` (ir_stk_step, ir_mext_steps) and
    /// `add_eval_ir_steps` (ir_steps_add).
    pub(super) fn add_eval_ir_stack_theorems(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_STK_STEPS, "ir_stk_steps (S3): n steps of a still-running run commute with stacking `rest` beneath the frames, same n both sides. Nat.rec on n generalised over the configuration; succ case = ir_stk_step under ir_stk_running_back, halted case definitional. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STK_ACTIVATION, "ir_stk_activation (S5): THE COMPOSITIONAL CALL RULE. A callee whose standalone run reaches a running pre-return configuration in k steps and then fetches a ret returns into ANY caller stack `rest` in (ir_d1 + k) steps, popping through ir_ret_to with the dests of the head frame. ir_steps_add, then ir_stk_steps, then ir_stk_ret_step. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_MEXT_RUN, "ir_mext_run: MODULE EXTENSION of a standalone run. A run reaching a running configuration in IRModule.mk fs0 gs0 reaches it in every module whose function/global lookups extend fs0/gs0 on each hit. ir_mext_steps under the running premise read off the conclusion. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
