// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **The stacking split's T witness** -- the case "first classifier hit" of
//! `ir_stk_split` (`eval_ir_stack_split.rs`) applied at a run the tree already
//! proves: the authored heartbeat model `ir_itb_hb` in the itd module.
//!
//! One standalone step from the model's entry frame (at EVERY dests list `d`)
//! reaches a single frame fetching `ret`; the split's T case -- clear before the
//! hit (`ir_stk_clear_of_running`), the hit (`ir_stk_botret_hit`), the
//! standalone `ret` (`ir_stk_split_ret_standalone`) and the stacked return in
//! the `forall d r` contract form (`ir_stk_activation_dests`, which applies
//! `ir_stk_activation`) -- then yields EXACTLY the statement of
//! `ir_it_ag_hc1_at_itd`, the premise `ir_it_ag_correct` consumes, by the general
//! call rule instead of a flat `Eq.refl`.
//!
//! Full-only: it names `ir_itb_hb` (add_eval_ir_itb) and `ir_it_ag_itd_fs` /
//! `ir_it_ag_itd_hbsp` (add_eval_ir_itf), so it is registered right after
//! `add_eval_ir_itf`. `DerivedProved`, empty axiom closures.

use super::{SpecError, Specification};

const SRC_STK_SPLIT_WITNESS_T_RUN: &str = "def ir_stk_split_witness_t_run (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) : forall (d : IRList Nat), @Eq IRConfig (ir_steps ir_d1 (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)))) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na))) := fun (d : IRList Nat) => @Eq.refl IRConfig (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)))";
const SRC_STK_SPLIT_WITNESS_T_FIRST: &str = "def ir_stk_split_witness_t_first (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) (d : IRList Nat) : @Eq Bool (ir_stk_clear ir_d1 (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)))) Bool.true := ir_stk_clear_of_running (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) ir_d1 (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na))) (Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq Bool (ir_stk_running c1) Bool.true) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na))) (ir_steps ir_d1 (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)))) (Eq.symm IRConfig (ir_steps ir_d1 (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)))) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na))) (ir_stk_split_witness_t_run spc p mem na d)) (@Eq.refl Bool Bool.true))";
const SRC_STK_SPLIT_WITNESS_T_HIT: &str = "def ir_stk_split_witness_t_hit (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) (d : IRList Nat) : @Eq Bool (ir_stk_botret (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na))) Bool.true := ir_stk_botret_hit (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) ir_itb_hb ir_itb_hb_b0 (ir_nl1 ir_d1) ir_nl0 (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc ir_itb_hb)) (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock ir_itb_hb_b0)) (@Eq.refl (IROption IRNode) (@IROption.some IRNode (IRNode.mk (IRInst.ret (ir_nl1 ir_d1)) ir_nl0)))";
const SRC_STK_SPLIT_WITNESS_T_STANDALONE: &str = "def ir_stk_split_witness_t_standalone (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) (d : IRList Nat) : @Eq IRConfig (ir_steps ir_d2 (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)))) (IRConfig.halted (IROutcome.ret (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp)))) := ir_stk_split_ret_standalone (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) ir_d1 (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) (@IRList.nil IRFrame)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na))) (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) d) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) ir_itb_hb ir_itb_hb_b0 (ir_nl1 ir_d1) ir_nl0 (ir_stk_split_witness_t_run spc p mem na d) (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc ir_itb_hb)) (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock ir_itb_hb_b0)) (@Eq.refl (IROption IRNode) (@IROption.some IRNode (IRNode.mk (IRInst.ret (ir_nl1 ir_d1)) ir_nl0)))";
const SRC_STK_SPLIT_WITNESS_T: &str = "def ir_stk_split_witness_t (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) : forall (d : IRList Nat) (r : IRList IRFrame), @Eq IRConfig (ir_steps ir_d2 (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) r) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)))) (ir_ret_to d r (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_vl1 (ir_it_hb_answer ir_it_ag_itd_hbsp))) := ir_stk_activation_dests (IRModule.mk (ir_it_ag_itd_fs spc) (@IRList.nil IRGlobal)) ir_d1 (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) Nat.zero (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) (ir_func_id ir_itb_hb) (ir_func_entry ir_itb_hb) (Nat.succ Nat.zero) (ir_bind_params (ir_nl1 ir_d1) (@IRList.cons IRScalar (ir_it_hb_answer ir_it_ag_itd_hbsp) (@IRList.nil IRScalar)) (ir_bind_params (ir_func_params ir_itb_hb) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding))) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) ir_itb_hb ir_itb_hb_b0 (ir_nl1 ir_d1) ir_nl0 (ir_stk_split_witness_t_run spc p mem na) (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc ir_itb_hb)) (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock ir_itb_hb_b0)) (@Eq.refl (IROption IRNode) (@IROption.some IRNode (IRNode.mk (IRInst.ret (ir_nl1 ir_d1)) ir_nl0)))";

/// The names this stage registers, in registration order.
pub const STK_WITNESS_NAMES: &[&str] = &[
    "ir_stk_split_witness_t_run",
    "ir_stk_split_witness_t_first",
    "ir_stk_split_witness_t_hit",
    "ir_stk_split_witness_t_standalone",
    "ir_stk_split_witness_t",
];

/// `(source, description)`, positionally paired with [`STK_WITNESS_NAMES`].
const DECLS: &[(&str, &str)] = &[
    (
        SRC_STK_SPLIT_WITNESS_T_RUN,
        "ir_stk_split_witness_t_run: the authored heartbeat model ir_itb_hb, run STANDALONE in the itd module from its entry frame at EVERY dests list d: one step (the aggregate constant) reaches a single frame at pc 1 that carries the SAME d and binds the answer. Eq.refl under fun d -- the dests-preservation premise of ir_stk_activation_dests, discharged by computation at abstract d. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_WITNESS_T_FIRST,
        "ir_stk_split_witness_t_first: that run is clear for its first step -- through ir_stk_clear_of_running from the running endpoint, so step 1 is the FIRST classifier hit. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_WITNESS_T_HIT,
        "ir_stk_split_witness_t_hit: and the classifier HITS at step 1 -- the frame fetches b0's ret -- through ir_stk_botret_hit at the three concrete lookups. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_WITNESS_T_STANDALONE,
        "ir_stk_split_witness_t_standalone: standalone, the run halts at step 2 with IROutcome.ret of the heartbeat answer -- ir_stk_split_ret_standalone at the hit. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_SPLIT_WITNESS_T,
        "ir_stk_split_witness_t: *** WITNESS T. *** The frame-generic contract for the heartbeat model -- for every dests d and caller stack r, two steps from the pushed frame return through ir_ret_to d r with the answer -- derived through the split's T case (ir_stk_activation_dests, hence ir_stk_activation) from the ONE-step standalone run, instead of by a flat Eq.refl. Its statement is ir_it_ag_hc1_at_itd's, character for character (the census test holds them equal): the premise ir_it_ag_correct consumes is reached by the general call rule. DerivedProved, zero axiom_deps.",
    ),
];

impl Specification {
    /// The T witness of the stacking split. MUST follow `add_eval_ir_itf`
    /// (`ir_it_ag_itd_fs`, `ir_it_ag_itd_hbsp`), `add_eval_ir_itb` (`ir_itb_hb`)
    /// and `add_eval_ir_stack_split`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_stk_witness(&mut self) -> Result<(), SpecError> {
        for (source, description) in DECLS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sources_balanced_ascii_and_named() {
        assert_eq!(DECLS.len(), STK_WITNESS_NAMES.len());
        for ((src, _), name) in DECLS.iter().zip(STK_WITNESS_NAMES) {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
        }
    }

    /// The T witness goes THROUGH the split's T case, not around it.
    #[test]
    fn test_t_witness_goes_through_the_split() {
        assert!(SRC_STK_SPLIT_WITNESS_T.contains("ir_stk_activation_dests"));
        assert!(SRC_STK_SPLIT_WITNESS_T.contains("ir_stk_split_witness_t_run"));
        assert!(!SRC_STK_SPLIT_WITNESS_T.contains(":= Eq.refl"));
        assert!(!SRC_STK_SPLIT_WITNESS_T.contains(":= @Eq.refl"));
        assert!(SRC_STK_SPLIT_WITNESS_T_FIRST.contains("ir_stk_clear_of_running"));
        assert!(SRC_STK_SPLIT_WITNESS_T_HIT.contains("ir_stk_botret_hit"));
        assert!(SRC_STK_SPLIT_WITNESS_T_STANDALONE.contains("ir_stk_split_ret_standalone"));
    }
}
