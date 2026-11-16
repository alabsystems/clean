// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **The two axes' witnesses and necessity refutations** -- at runs the tree
//! already proves, in stages only the Full spec carries (the heartbeat model
//! `ir_itb_hb`, the meta-tag OOB module `ir_mt_oob_module`, the globaladdr
//! module `ir_w2c_ga_module`, and itf's inclusion lemma `ir_it_hg_nil`).
//!
//! * `ir_stk_split_witness_t_gen` -- E1's T witness re-derived through
//!   `ir_stk_activation_dests_gen` from ONE standalone run at the EMPTY dests;
//!   its statement is `ir_it_ag_hc1_at_itd`'s, character for character (the
//!   census holds the elaborated types equal).
//! * `ir_mexto_witness_mt_oob` -- F across BOTH axes at a real faulting run: the
//!   meta-tag OOB body's sanctioned panic at step 6, over every caller stack, in
//!   every module whose function 0 is that body.
//! * `ir_mexto_needs_no_func`, `ir_mexto_needs_no_global` -- BOTH exclusions in
//!   `ir_mext_ok` are necessary, kernel-checked: the one-step transport of a
//!   halted step WITHOUT the premise implies any proposition, once at a function
//!   lookup miss (the empty module against the OOB module) and once at a global
//!   lookup miss (the globaladdr body without its global against the module
//!   with it).
//!
//! Full-only: registered right after `add_eval_ir_stk_witness`. Every
//! declaration kernel-checked, empty axiom closure, by name.

use super::{SpecError, Specification};

const HB_F0: &str = "(IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) (@IRList.nil Nat))";
const HB_FK: &str = "(IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) (@IRList.nil Nat))";
const HB_MEM: &str = "(@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem)";

const SRC_STK_SPLIT_WITNESS_T_GEN: &str = "def ir_stk_split_witness_t_gen (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) : forall (d : IRList Nat) (r : IRList IRFrame), @Eq IRConfig (ir_steps ir_d2 (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) r) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)))) (ir_ret_to d r (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp))) := ir_stk_activation_dests_gen (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) ir_d1 {F0} {MEM} (Nat.succ na) {FK} {MEM} (Nat.succ na) ir_itb_hb ir_itb_hb_b0 (ir_nl1 ir_d1) ir_nl0 (ir_stk_split_witness_t_run spc p mem na (@IRList.nil Nat)) (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc ir_itb_hb)) (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock ir_itb_hb_b0)) (@Eq.refl (IROption IRNode) (@IROption.some IRNode (IRNode.mk (IRInst.ret (ir_nl1 ir_d1)) ir_nl0)))";
const SRC_MT_OOB_HF_OF_H0: &str = "def ir_mt_oob_hf_of_h0 (fs : IRList IRFunc) (h0 : @Eq (IROption IRFunc) (ir_func_find fs ir_d0) (@IROption.some IRFunc ir_mt_oob_func)) : forall (kf : Nat) (gf : IRFunc), @Eq (IROption IRFunc) (ir_func_find (@IRList.cons IRFunc ir_mt_oob_func (@IRList.nil IRFunc)) kf) (@IROption.some IRFunc gf) -> @Eq (IROption IRFunc) (ir_func_find fs kf) (@IROption.some IRFunc gf) := fun (kf : Nat) (gf : IRFunc) (hs : @Eq (IROption IRFunc) (ir_func_find (@IRList.cons IRFunc ir_mt_oob_func (@IRList.nil IRFunc)) kf) (@IROption.some IRFunc gf)) => @Bool.rec (fun (b : Bool) => @Eq Bool (ir_nat_eqb ir_d0 kf) b -> @Eq (IROption IRFunc) (@Bool.rec (fun (_ : Bool) => IROption IRFunc) (@IROption.none IRFunc) (@IROption.some IRFunc ir_mt_oob_func) b) (@IROption.some IRFunc gf) -> @Eq (IROption IRFunc) (ir_func_find fs kf) (@IROption.some IRFunc gf)) (fun (_ : @Eq Bool (ir_nat_eqb ir_d0 kf) Bool.false) (hn : @Eq (IROption IRFunc) (@Bool.rec (fun (_ : Bool) => IROption IRFunc) (@IROption.none IRFunc) (@IROption.some IRFunc ir_mt_oob_func) Bool.false) (@IROption.some IRFunc gf)) => ir_bool_false_ne_true (@Eq (IROption IRFunc) (ir_func_find fs kf) (@IROption.some IRFunc gf)) (ir_eq_cong (IROption IRFunc) Bool (fun (o : IROption IRFunc) => ir_opt_func_is_some o) (@Bool.rec (fun (_ : Bool) => IROption IRFunc) (@IROption.none IRFunc) (@IROption.some IRFunc ir_mt_oob_func) Bool.false) (@IROption.some IRFunc gf) hn)) (fun (ht : @Eq Bool (ir_nat_eqb ir_d0 kf) Bool.true) (hy : @Eq (IROption IRFunc) (@Bool.rec (fun (_ : Bool) => IROption IRFunc) (@IROption.none IRFunc) (@IROption.some IRFunc ir_mt_oob_func) Bool.true) (@IROption.some IRFunc gf)) => Eq.subst Nat (fun (k : Nat) => @Eq (IROption IRFunc) (ir_func_find fs k) (@IROption.some IRFunc gf)) ir_d0 kf (ir_nat_eqb_sound ir_d0 kf ht) (Eq.subst (IROption IRFunc) (fun (o : IROption IRFunc) => @Eq (IROption IRFunc) (ir_func_find fs ir_d0) o) (@Bool.rec (fun (_ : Bool) => IROption IRFunc) (@IROption.none IRFunc) (@IROption.some IRFunc ir_mt_oob_func) Bool.true) (@IROption.some IRFunc gf) hy h0)) (ir_nat_eqb ir_d0 kf) (@Eq.refl Bool (ir_nat_eqb ir_d0 kf)) hs";
const SRC_MEXTO_WITNESS_MT_OOB: &str = "def ir_mexto_witness_mt_oob (fs : IRList IRFunc) (gs : IRList IRGlobal) (h0 : @Eq (IROption IRFunc) (ir_func_find fs ir_d0) (@IROption.some IRFunc ir_mt_oob_func)) (mem : IRList IRMemSlot) (na : Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_steps ir_d6 (IRModule.mk fs gs) (ir_config_stack (IRConfig.running (ir_mt_oob_mach0 mem na)) rest)) (IRConfig.halted (IROutcome.ub IRFault.assert_failed)) := ir_stk_split_halted_mext (@IRList.cons IRFunc ir_mt_oob_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal) fs gs (ir_mt_oob_hf_of_h0 fs h0) (ir_it_hg_nil gs) rest ir_d6 (IRConfig.running (ir_mt_oob_mach0 mem na)) (IROutcome.ub IRFault.assert_failed) (ir_mt_oob_clear_of_mid mem na) (ir_mt_oob_halts_at_six mem na) (@Eq.refl Bool Bool.true)";
const SRC_MEXT_HF_NIL: &str = "def ir_mext_hf_nil (fs : IRList IRFunc) : forall (kf : Nat) (gf : IRFunc), @Eq (IROption IRFunc) (ir_func_find (@IRList.nil IRFunc) kf) (@IROption.some IRFunc gf) -> @Eq (IROption IRFunc) (ir_func_find fs kf) (@IROption.some IRFunc gf) := fun (kf : Nat) (gf : IRFunc) (h : @Eq (IROption IRFunc) (ir_func_find (@IRList.nil IRFunc) kf) (@IROption.some IRFunc gf)) => ir_bool_false_ne_true (@Eq (IROption IRFunc) (ir_func_find fs kf) (@IROption.some IRFunc gf)) (ir_eq_cong (IROption IRFunc) Bool (fun (o : IROption IRFunc) => ir_opt_func_is_some o) (ir_func_find (@IRList.nil IRFunc) kf) (@IROption.some IRFunc gf) h)";
const UNGUARDED: &str = "(H : forall (fs0 : IRList IRFunc) (gs0 : IRList IRGlobal) (fs : IRList IRFunc) (gs : IRList IRGlobal), (forall (kf : Nat) (gf : IRFunc), @Eq (IROption IRFunc) (ir_func_find fs0 kf) (@IROption.some IRFunc gf) -> @Eq (IROption IRFunc) (ir_func_find fs kf) (@IROption.some IRFunc gf)) -> (forall (kg : Nat) (gg : IRGlobal), @Eq (IROption IRGlobal) (ir_global_find gs0 kg) (@IROption.some IRGlobal gg) -> @Eq (IROption IRGlobal) (ir_global_find gs kg) (@IROption.some IRGlobal gg)) -> forall (s : IRMachine) (o : IROutcome), @Eq IRConfig (ir_step (IRModule.mk fs0 gs0) s) (IRConfig.halted o) -> @Eq IRConfig (ir_step (IRModule.mk fs gs) s) (IRConfig.halted o))";
const OOB_S: &str = "(ir_mt_oob_mach0 (@IRList.nil IRMemSlot) Nat.zero)";
const OOB_M: &str =
    "(IRModule.mk (@IRList.cons IRFunc ir_mt_oob_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal))";
const SRC_MEXTO_NEEDS_NO_FUNC: &str = "def ir_mexto_needs_no_func (C : Prop) {UNG} : C := ir_bool_false_ne_true C (Eq.symm Bool (ir_stk_running (ir_step {OOB_M} {OOB_S})) (ir_stk_running (IRConfig.halted (IROutcome.stuck IRFault.no_func))) (ir_eq_cong IRConfig Bool (fun (c1 : IRConfig) => ir_stk_running c1) (ir_step {OOB_M} {OOB_S}) (IRConfig.halted (IROutcome.stuck IRFault.no_func)) (H (@IRList.nil IRFunc) (@IRList.nil IRGlobal) (@IRList.cons IRFunc ir_mt_oob_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal) (ir_mext_hf_nil (@IRList.cons IRFunc ir_mt_oob_func (@IRList.nil IRFunc))) (ir_it_hg_nil (@IRList.nil IRGlobal)) {OOB_S} (IROutcome.stuck IRFault.no_func) (@Eq.refl IRConfig (IRConfig.halted (IROutcome.stuck IRFault.no_func))))))";
const GA_S: &str = "(IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame)) (@IRList.nil IRMemSlot) Nat.zero)";
const GA_FS: &str = "(@IRList.cons IRFunc ir_w2c_ga_func (@IRList.nil IRFunc))";
const GA_GS: &str =
    "(@IRList.cons IRGlobal (IRGlobal.mk ir_d0 (IRConst.int_ ir_d7)) (@IRList.nil IRGlobal))";
const SRC_MEXTO_NEEDS_NO_GLOBAL: &str = "def ir_mexto_needs_no_global (C : Prop) {UNG} : C := ir_bool_false_ne_true C (Eq.symm Bool (ir_stk_running (ir_step (IRModule.mk {GA_FS} {GA_GS}) {GA_S})) (ir_stk_running (IRConfig.halted (IROutcome.type_error IRFault.no_global))) (ir_eq_cong IRConfig Bool (fun (c1 : IRConfig) => ir_stk_running c1) (ir_step (IRModule.mk {GA_FS} {GA_GS}) {GA_S}) (IRConfig.halted (IROutcome.type_error IRFault.no_global)) (H {GA_FS} (@IRList.nil IRGlobal) {GA_FS} {GA_GS} (fun (kf : Nat) (gf : IRFunc) (h : @Eq (IROption IRFunc) (ir_func_find {GA_FS} kf) (@IROption.some IRFunc gf)) => h) (ir_it_hg_nil {GA_GS}) {GA_S} (IROutcome.type_error IRFault.no_global) (@Eq.refl IRConfig (IRConfig.halted (IROutcome.type_error IRFault.no_global))))))";

const SRC_MT_OOB_CLEAR_OF_MID: &str = "def ir_mt_oob_clear_of_mid (mem : IRList IRMemSlot) (na : Nat) : @Eq Bool (ir_stk_clear ir_d6 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) Bool.true := ir_stk_clear_of_mid ir_mt_oob_module ir_d6 (IRConfig.running (ir_mt_oob_mach0 mem na)) (Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq Bool (ir_halt_mid c1) Bool.true) (IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_steps ir_d6 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) (Eq.symm IRConfig (ir_steps ir_d6 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) (IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_mt_oob_halts_at_six mem na)) (@Eq.refl Bool Bool.true))";
const SRC_CTR_HB: &str = "def ir_ctr_hb (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) (n : Nat) : ir_ctr_at (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (fun (d0 : IRList Nat) (r0 : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d0) r0) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) (ir_post_exact (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp))) n := ir_ctr_exact (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (fun (d0 : IRList Nat) (r0 : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d0) r0) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) ir_d2 (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp)) (ir_it_ag_hc1_at_itd spc p mem na) n";
const SRC_CTR_TRI_STACK_HB: &str = "def ir_ctr_tri_stack_hb (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) (n : Nat) (d : IRList Nat) (r : IRList IRFrame) (k : Nat) (j : Nat) (hk : @Eq Nat (Nat.add k j) n) : ir_stk_tri (ir_post_exact (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp))) r (ir_steps k (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running ((fun (d0 : IRList Nat) (r0 : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d0) r0) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) d (@IRList.nil IRFrame)))) (ir_steps k (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running ((fun (d0 : IRList Nat) (r0 : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d0) r0) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) d r))) := ir_ctr_tri_stack (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (fun (d0 : IRList Nat) (r0 : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d0) r0) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) (ir_post_exact (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp))) n (ir_ctr_hb spc p mem na n) (fun (d1 : IRList Nat) (r1 : IRList IRFrame) => @Eq.refl IRMachine ((fun (d0 : IRList Nat) (r0 : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d0) r0) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) d1 r1)) d r k j hk";
const SRC_CTR_RET_POST_STACK_HB: &str = "def ir_ctr_ret_post_stack_hb (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) (d : IRList Nat) : ir_ret_post (ir_post_exact (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp))) (IROutcome.ret (ir_resolve (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) (ir_nl1 ir_d1))) := ir_ctr_ret_post_stack (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (fun (d0 : IRList Nat) (r0 : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d0) r0) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) (ir_post_exact (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp))) ir_d2 (ir_ctr_hb spc p mem na ir_d2) d ir_d1 Nat.zero (@Eq.refl Nat ir_d2) (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) ir_itb_hb ir_itb_hb_b0 (ir_nl1 ir_d1) ir_nl0 (ir_stk_split_witness_t_run spc p mem na d) (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc ir_itb_hb)) (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock ir_itb_hb_b0)) (@Eq.refl (IROption IRNode) (@IROption.some IRNode (IRNode.mk (IRInst.ret (ir_nl1 ir_d1)) ir_nl0)))";
/// The names this stage registers, in registration order.
pub const STACK_AXES_WITNESS_NAMES: &[&str] = &[
    "ir_stk_split_witness_t_gen",
    "ir_mt_oob_hf_of_h0",
    "ir_mt_oob_clear_of_mid",
    "ir_mexto_witness_mt_oob",
    "ir_mext_hf_nil",
    "ir_mexto_needs_no_func",
    "ir_mexto_needs_no_global",
    "ir_ctr_hb",
    "ir_ctr_tri_stack_hb",
    "ir_ctr_ret_post_stack_hb",
];

/// `(source, description)`, positionally paired with [`STACK_AXES_WITNESS_NAMES`].
const DECLS: &[(&str, &str)] = &[
    (
        SRC_STK_SPLIT_WITNESS_T_GEN,
        "ir_stk_split_witness_t_gen: *** WITNESS for ir_stk_activation_dests_gen. *** E1's T witness re-derived from ONE standalone run of the heartbeat model -- at the EMPTY dests, not at every d -- through the general theorem, which supplies every other d itself. Its statement is ir_it_ag_hc1_at_itd's (the census holds the elaborated types equal), so the premise ir_it_ag_correct consumes is reached with no computation at an abstract dests list. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_MT_OOB_HF_OF_H0,
        "ir_mt_oob_hf_of_h0: the function-table INCLUSION the module axis needs for the one-function OOB module, from the single hypothesis that function 0 of the target table IS ir_mt_oob_func -- a Bool equation convoy on ir_nat_eqb ir_d0 kf, the pattern of ir_it_hf_of_h0. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_MT_OOB_CLEAR_OF_MID,
        "ir_mt_oob_clear_of_mid: *** WITNESS for ir_halt_mid and ir_stk_clear_of_mid at a real run. *** The meta-tag OOB run halts with a sanctioned panic at step 6 (ir_mt_oob_halts_at_six, CITED), which is a mid halt, so the run was in the commuting class at every running prefix -- DERIVED through ir_stk_clear_of_mid rather than computed. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_MEXTO_WITNESS_MT_OOB,
        "ir_mexto_witness_mt_oob: *** WITNESS F ACROSS BOTH AXES, at a real FAULTING run. *** The meta-tag OOB body halts with the sanctioned panic `ub assert_failed` at step 6 (ir_mt_oob_halts_at_six, CITED); stacked over EVERY caller stack, in EVERY module whose function 0 is that body, it halts identically at step 6. ir_stk_split_halted_mext with the clear predicate DERIVED from the halt (ir_mt_oob_clear_of_mid) and ir_mext_ok of the halt by computation. The running-keyed module axis could not state this: the run does not stay running. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_MEXT_HF_NIL,
        "ir_mext_hf_nil: the EMPTY function table is included in every table -- ir_func_find on nil computes to none, so the premise is none = some gf, refuted through ir_opt_func_is_some. With ir_it_hg_nil it makes the empty module a legitimate source of the module axis, which is what the no_func refutation needs. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_MEXTO_NEEDS_NO_FUNC,
        "ir_mexto_needs_no_func: *** THE no_func EXCLUSION OF ir_mext_ok IS NECESSARY, kernel-checked. *** Assume the one-step module axis for HALTED steps with no outcome premise at all; instantiate it at the EMPTY module (included in every module) against the OOB module, at the OOB body's entry machine: the empty module's step halts stuck no_func (the fetch misses), so the assumption says the OOB module's step does too -- but that step runs (its first instruction is a const). ir_eq_cong of ir_stk_running turns the equation into Eq Bool Bool.false Bool.true, and anything follows. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_MEXTO_NEEDS_NO_GLOBAL,
        "ir_mexto_needs_no_global: *** THE no_global EXCLUSION OF ir_mext_ok IS NECESSARY, kernel-checked. *** The same assumption, instantiated at the globaladdr body WITHOUT its global against the same body WITH it (ir_w2c_ga_module's function list and global): the first instruction is `globaladdr 0`, which halts type_error no_global in the smaller module and binds the address in the larger one. So each of ir_mext_ok's two exclusions is witnessed by a real body whose halt an extension cures. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_HB,
        "ir_ctr_hb: the heartbeat model's contract at every budget -- E2's adapter ir_ctr_exact over the exact run ir_it_ag_hc1_at_itd, the post its exact final triple. An instance of ir_ctr_at at a run the tree already proves, for the two readings below. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_TRI_STACK_HB,
        "ir_ctr_tri_stack_hb: *** WITNESS for ir_stk_tri and ir_ctr_tri_stack with NO side premise. *** The heartbeat model's contract read three ways at an ARBITRARY caller stack, every budget n, every k + j = n; the entry premise is Eq.refl (one frame over its caller stack). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_RET_POST_STACK_HB,
        "ir_ctr_ret_post_stack_hb: *** WITNESS for ir_ctr_ret_post_stack with every premise discharged. *** At the heartbeat model, for EVERY entry dests d: the one-step standalone run reaches the bottom ret (ir_stk_split_witness_t_run at d), 1 + 1 fits the budget 2, and the values it returns satisfy the post -- the return case of the reading, made exact. DerivedProved, zero axiom_deps.",
    ),
];

fn expand(source: &str) -> String {
    source
        .replace("{F0}", HB_F0)
        .replace("{FK}", HB_FK)
        .replace("{MEM}", HB_MEM)
        .replace("{UNG}", UNGUARDED)
        .replace("{OOB_S}", OOB_S)
        .replace("{OOB_M}", OOB_M)
        .replace("{GA_S}", GA_S)
        .replace("{GA_FS}", GA_FS)
        .replace("{GA_GS}", GA_GS)
}

impl Specification {
    /// The axes' witnesses. Full-only; MUST follow `add_eval_ir_stk_witness`
    /// (`ir_stk_split_witness_t_run`), `add_eval_ir_itf` (`ir_it_hg_nil`,
    /// `ir_opt_func_is_some`), `add_eval_ir_meta_tag` and
    /// `add_eval_ir_w2c_synth`, and the two axes' stages.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_stack_axes_witness(&mut self) -> Result<(), SpecError> {
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
        assert_eq!(DECLS.len(), STACK_AXES_WITNESS_NAMES.len());
        for ((src, _), name) in DECLS.iter().zip(STACK_AXES_WITNESS_NAMES) {
            let src = expand(src);
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
            assert!(!src.contains('{'), "{name}: an unexpanded placeholder");
        }
    }

    /// The witnesses go THROUGH the general theorems and CITE the runs.
    #[test]
    fn test_witnesses_go_through_the_general_theorems() {
        assert!(SRC_STK_SPLIT_WITNESS_T_GEN.contains("ir_stk_activation_dests_gen"));
        assert!(SRC_STK_SPLIT_WITNESS_T_GEN.contains("(@IRList.nil Nat))"));
        assert!(SRC_MEXTO_WITNESS_MT_OOB.contains("ir_stk_split_halted_mext"));
        assert!(SRC_MEXTO_WITNESS_MT_OOB.contains("ir_mt_oob_halts_at_six"));
    }
}
