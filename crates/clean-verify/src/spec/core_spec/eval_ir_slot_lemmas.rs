// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The return-slot lemmas** — an `alloca` / `store` / `load` / `ret` slot,
//! closed at an ABSTRACT allocation counter.
//!
//! Phase B has to prove activation lemmas for callee bodies the crystal's A0
//! closure needs — `Option::as_deref`, `Option::expect`, `<Arc<T>>::deref` —
//! and every one of them opens by writing its result into a stack temporary:
//!
//! ```text
//! %1 = alloca T
//! store T %0, ptr %1
//! %2 = load T, ptr %1
//! ret %2
//! ```
//!
//! The open question was whether that pattern can be proved WITHOUT knowing the
//! heap or the next free address — because a lemma that pinned either could not
//! be spliced into a caller, and the alternative was a mem2reg-style rewrite of
//! the derived bundle before the semantics ever saw it. It can. The measured
//! answer is `ir_slot_activation`: four steps, arbitrary `mem`, arbitrary
//! `na`, arbitrary caller, value in equals value out.
//!
//! ## Why it works, in one line
//!
//! `alloca` conses its fresh cell at the HEAD of memory, so the store's
//! liveness read and the load's read are both lookups at the head — and a
//! lookup at the head resolves by `ir_nat_eqb na na = true`, a Nat induction,
//! rather than by a walk over an unknown heap. Everything else is transport.
//!
//! ## The five substrate lemmas, and why they live here
//!
//! `ir_nat_sub_self`, `ir_nat_eqb_refl`, `ir_mem_lookup_head`,
//! `ir_mem_update_head` and `ir_mem_lookup_skip` are general facts about the
//! EvalIR substrate whose neighbours (`ir_nat_eqb`, `ir_mem_lookup`,
//! `ir_mem_update`) live in [`super::eval_ir_state`]. They are registered here
//! instead for one reason, stated so it is not mistaken for a design claim:
//! `eval_ir_state.rs` is already 1,463 lines against this tree's 500-line
//! convention, and the composition-boundary rule documented in
//! `add_eval_ir_nat_helpers` binds everything reachable from `add_eval_ir` —
//! this stage is not, so the vocabulary question does not arise for it. If
//! `eval_ir_state.rs` is ever split, these five belong beside the definitions
//! they are about.
//!
//! ## Two boundaries, named rather than discovered downstream
//!
//! 1. `ir_slot_load_seg` and everything above it are stated at
//!    `v := IRScalar.int_ n`, not at an opaque scalar: `ir_load_slot`
//!    dispatches on the value's constructor, so a fully abstract value is stuck
//!    for a reason no memory lemma can remove.
//! 2. `ir_mem_lookup_skip` takes its disequality as a hypothesis. Addresses
//!    are symbolic here and the machine's own `ir_nat_eqb` is the only decision
//!    procedure in scope.
//!
//! Every proof term in this file is the one the Phase-B probe kernel-checked
//! against this same bundle (28/28 candidates), carried across with the probe
//! prefix renamed and nothing else changed.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_NAT_SUB_SELF: &str = "def ir_nat_sub_self (k : Nat) : @Eq Nat (Nat.sub k k) Nat.zero := @Nat.rec (fun (m : Nat) => @Eq Nat (Nat.sub m m) Nat.zero) (@Eq.refl Nat Nat.zero) (fun (m : Nat) (ih : @Eq Nat (Nat.sub m m) Nat.zero) => @Eq.trans Nat (Nat.sub (Nat.succ m) (Nat.succ m)) (Nat.sub m m) Nat.zero (ir_nat_sub_succ_succ m m) ih) k";

const SRC_NAT_EQB_WALK_REFL: &str = "def ir_nat_eqb_walk_refl (n : Nat) : @Eq Bool (ir_nat_eqb_walk n n) Bool.true := @Nat.rec (fun (k : Nat) => @Eq Bool (ir_nat_eqb_walk k k) Bool.true) (@Eq.refl Bool Bool.true) (fun (k : Nat) (ih : @Eq Bool (ir_nat_eqb_walk k k) Bool.true) => ih) n";
const SRC_NAT_EQB_REFL: &str = "def ir_nat_eqb_refl (n : Nat) : @Eq Bool (ir_nat_eqb n n) Bool.true := @Eq.trans Bool (ir_nat_eqb n n) (ir_nat_eqb_walk n n) Bool.true (ir_nat_eqb_walk_eq n n) (ir_nat_eqb_walk_refl n)";

const SRC_MEM_LOOKUP_HEAD: &str = "def ir_mem_lookup_head (a : Nat) (v : IRScalar) (live : Bool) (m : IRList IRMemSlot) : @Eq (IROption IRMemSlot) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk a v live) m) a) (@IROption.some IRMemSlot (IRMemSlot.mk a v live)) := ir_eq_cong Bool (IROption IRMemSlot) (fun (b : Bool) => @Bool.rec (fun (_ : Bool) => IROption IRMemSlot) (ir_mem_lookup m a) (@IROption.some IRMemSlot (IRMemSlot.mk a v live)) b) (ir_nat_eqb a a) Bool.true (ir_nat_eqb_refl a)";

const SRC_MEM_UPDATE_HEAD: &str = "def ir_mem_update_head (a : Nat) (v0 : IRScalar) (live : Bool) (m : IRList IRMemSlot) (v : IRScalar) : @Eq (IRList IRMemSlot) (ir_mem_update (@IRList.cons IRMemSlot (IRMemSlot.mk a v0 live) m) a v) (@IRList.cons IRMemSlot (IRMemSlot.mk a v live) m) := ir_eq_cong Bool (IRList IRMemSlot) (fun (b : Bool) => @Bool.rec (fun (_ : Bool) => IRList IRMemSlot) (@IRList.cons IRMemSlot (IRMemSlot.mk a v0 live) (ir_mem_update m a v)) (@IRList.cons IRMemSlot (IRMemSlot.mk a v live) m) b) (ir_nat_eqb a a) Bool.true (ir_nat_eqb_refl a)";

const SRC_MEM_LOOKUP_SKIP: &str = "def ir_mem_lookup_skip (k : Nat) (p : Nat) (v : IRScalar) (live : Bool) (m : IRList IRMemSlot) (hne : @Eq Bool (ir_nat_eqb k p) Bool.false) : @Eq (IROption IRMemSlot) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk k v live) m) p) (ir_mem_lookup m p) := ir_eq_cong Bool (IROption IRMemSlot) (fun (b : Bool) => @Bool.rec (fun (_ : Bool) => IROption IRMemSlot) (ir_mem_lookup m p) (@IROption.some IRMemSlot (IRMemSlot.mk k v live)) b) (ir_nat_eqb k p) Bool.false hne";

const SRC_SLOT_B0: &str = "def ir_slot_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (@IRList.cons IRNode (ir_nd1 (IRInst.alloca (IRTy.enum_ ir_d0) (@IROption.none Nat)) ir_d1) (ir_bd3 (ir_nd (IRInst.store (IRTy.enum_ ir_d0) ir_d1 ir_d0 Bool.false)) (ir_nd1 (IRInst.load (IRTy.enum_ ir_d0) ir_d1 Bool.false) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2)))))";

const SRC_SLOT_FUNC: &str =
    "def ir_slot_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_slot_b0 ir_blk0)";

const SRC_SLOT_MODULE: &str = "def ir_slot_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_slot_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)";

const SRC_MACH0: &str = "def ir_slot_mach0 (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (@IRList.nil IRBinding)) dests) rest) mem na";

const SRC_SMACH: &str = "def ir_slot_smach (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (ir_frame_bind (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (@IRList.nil IRBinding)) dests) (ir_nl1 ir_d1) (IRScalar.ptr_ na)) rest) (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)";

const SRC_LMACH: &str = "def ir_slot_lmach (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (ir_frame_advance (ir_frame_bind (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (@IRList.nil IRBinding)) dests) (ir_nl1 ir_d1) (IRScalar.ptr_ na))) rest) (@IRList.cons IRMemSlot (IRMemSlot.mk na v Bool.true) mem) (Nat.succ na)";

const SRC_RMACH: &str = "def ir_slot_rmach (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (ir_frame_bind (ir_frame_advance (ir_frame_bind (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (@IRList.nil IRBinding)) dests) (ir_nl1 ir_d1) (IRScalar.ptr_ na))) (ir_nl1 ir_d2) v) rest) (@IRList.cons IRMemSlot (IRMemSlot.mk na v Bool.true) mem) (Nat.succ na)";

const SRC_AFTER_STORE_LOOKUP: &str = "def ir_slot_after_store_lookup (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (o : IROption IRMemSlot) : IRConfig := ir_store_checked (ir_slot_smach mem v na dests rest) na v o";

const SRC_AFTER_STORE_UPDATE: &str = "def ir_slot_after_store_update (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (m2 : IRList IRMemSlot) : IRConfig := ir_advance (ir_set_mem (ir_slot_smach mem v na dests rest) m2)";

const SRC_AFTER_LOAD: &str = "def ir_slot_after_load (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (o : IROption IRMemSlot) : IRConfig := ir_bind_result (ir_slot_lmach mem v na dests rest) (ir_nl1 ir_d2) (ir_load_slot o)";

const SRC_STEP_ALLOCA: &str = "def ir_slot_step_alloca (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_step ir_slot_module (ir_slot_mach0 mem v na dests rest)) (IRConfig.running (ir_slot_smach mem v na dests rest)) := @Eq.refl IRConfig (IRConfig.running (ir_slot_smach mem v na dests rest))";

const SRC_STEP_STORE: &str = "def ir_slot_step_store (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_step ir_slot_module (ir_slot_smach mem v na dests rest)) (ir_slot_after_store_lookup mem v na dests rest (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na)) := @Eq.refl IRConfig (ir_slot_after_store_lookup mem v na dests rest (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na))";

const SRC_STORE_RESOLVED: &str = "def ir_slot_store_resolved (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_slot_after_store_lookup mem v na dests rest (@IROption.some IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true))) (ir_slot_after_store_update mem v na dests rest (ir_mem_update (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na v)) := @Eq.refl IRConfig (ir_slot_after_store_update mem v na dests rest (ir_mem_update (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na v))";

const SRC_STEP_LOAD: &str = "def ir_slot_step_load (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_step ir_slot_module (ir_slot_lmach mem v na dests rest)) (ir_slot_after_load mem v na dests rest (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na v Bool.true) mem) na)) := @Eq.refl IRConfig (ir_slot_after_load mem v na dests rest (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na v Bool.true) mem) na))";

const SRC_STORE_SEG: &str = "def ir_slot_store_seg (mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_smach mem v na dests rest))) (IRConfig.running (ir_slot_lmach mem v na dests rest)) := @Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => @Eq IRConfig (ir_slot_after_store_lookup mem v na dests rest o) (IRConfig.running (ir_slot_lmach mem v na dests rest))) (@IROption.some IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true)) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na) (@Eq.symm (IROption IRMemSlot) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na) (@IROption.some IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true)) (ir_mem_lookup_head na IRScalar.undef_ Bool.true mem)) (@Eq.subst (IRList IRMemSlot) (fun (m2 : (IRList IRMemSlot)) => @Eq IRConfig (ir_slot_after_store_update mem v na dests rest m2) (IRConfig.running (ir_slot_lmach mem v na dests rest))) (@IRList.cons IRMemSlot (IRMemSlot.mk na v Bool.true) mem) (ir_mem_update (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na v) (@Eq.symm (IRList IRMemSlot) (ir_mem_update (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na v) (@IRList.cons IRMemSlot (IRMemSlot.mk na v Bool.true) mem) (ir_mem_update_head na IRScalar.undef_ Bool.true mem v)) (@Eq.refl IRConfig (IRConfig.running (ir_slot_lmach mem v na dests rest))))";

const SRC_LOAD_SEG: &str = "def ir_slot_load_seg (mem : IRList IRMemSlot) (n : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_lmach mem (IRScalar.int_ n) na dests rest))) (IRConfig.running (ir_slot_rmach mem (IRScalar.int_ n) na dests rest)) := @Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => @Eq IRConfig (ir_slot_after_load mem (IRScalar.int_ n) na dests rest o) (IRConfig.running (ir_slot_rmach mem (IRScalar.int_ n) na dests rest))) (@IROption.some IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true)) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) na) (@Eq.symm (IROption IRMemSlot) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) na) (@IROption.some IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true)) (ir_mem_lookup_head na (IRScalar.int_ n) Bool.true mem)) (@Eq.refl IRConfig (IRConfig.running (ir_slot_rmach mem (IRScalar.int_ n) na dests rest)))";

const SRC_ACTIVATION: &str = "def ir_slot_activation (mem : IRList IRMemSlot) (n : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_steps ir_d4 ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest))) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n))) := @Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => @Eq IRConfig (ir_steps ir_d2 ir_slot_module (ir_slot_after_store_lookup mem (IRScalar.int_ n) na dests rest o)) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n)))) (@IROption.some IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true)) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na) (@Eq.symm (IROption IRMemSlot) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na) (@IROption.some IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true)) (ir_mem_lookup_head na IRScalar.undef_ Bool.true mem)) (@Eq.subst (IRList IRMemSlot) (fun (m2 : (IRList IRMemSlot)) => @Eq IRConfig (ir_steps ir_d2 ir_slot_module (ir_slot_after_store_update mem (IRScalar.int_ n) na dests rest m2)) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n)))) (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (ir_mem_update (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na (IRScalar.int_ n)) (@Eq.symm (IRList IRMemSlot) (ir_mem_update (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) na (IRScalar.int_ n)) (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (ir_mem_update_head na IRScalar.undef_ Bool.true mem (IRScalar.int_ n))) (@Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => @Eq IRConfig (ir_steps ir_d1 ir_slot_module (ir_slot_after_load mem (IRScalar.int_ n) na dests rest o)) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n)))) (@IROption.some IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true)) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) na) (@Eq.symm (IROption IRMemSlot) (ir_mem_lookup (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) na) (@IROption.some IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true)) (ir_mem_lookup_head na (IRScalar.int_ n) Bool.true mem)) (@Eq.refl IRConfig (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n))))))";

const SRC_SEG: &str = "def ir_slot_seg (mem : IRList IRMemSlot) (n : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : @Eq IRConfig (ir_steps (Nat.add (Nat.add (Nat.add ir_d1 ir_d1) ir_d1) ir_d1) ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest))) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n))) := (@Eq.trans IRConfig (ir_steps (Nat.add (Nat.add (Nat.add ir_d1 ir_d1) ir_d1) ir_d1) ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest))) (ir_steps (Nat.add (Nat.add ir_d1 ir_d1) ir_d1) ir_slot_module (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest)))) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n))) (ir_steps_add ir_slot_module (Nat.add (Nat.add ir_d1 ir_d1) ir_d1) ir_d1 (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest))) (@Eq.trans IRConfig (ir_steps (Nat.add (Nat.add ir_d1 ir_d1) ir_d1) ir_slot_module (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest)))) (ir_steps (Nat.add ir_d1 ir_d1) ir_slot_module (ir_steps ir_d1 ir_slot_module (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest))))) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n))) (ir_steps_add ir_slot_module (Nat.add ir_d1 ir_d1) ir_d1 (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest)))) (@Eq.subst IRConfig (fun (k : IRConfig) => @Eq IRConfig (ir_steps (Nat.add ir_d1 ir_d1) ir_slot_module k) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n)))) (IRConfig.running (ir_slot_lmach mem (IRScalar.int_ n) na dests rest)) (ir_steps ir_d1 ir_slot_module (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest)))) (@Eq.symm IRConfig (ir_steps ir_d1 ir_slot_module (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests rest)))) (IRConfig.running (ir_slot_lmach mem (IRScalar.int_ n) na dests rest)) (ir_slot_store_seg mem (IRScalar.int_ n) na dests rest)) (@Eq.trans IRConfig (ir_steps (Nat.add ir_d1 ir_d1) ir_slot_module (IRConfig.running (ir_slot_lmach mem (IRScalar.int_ n) na dests rest))) (ir_steps ir_d1 ir_slot_module (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_lmach mem (IRScalar.int_ n) na dests rest)))) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n))) (ir_steps_add ir_slot_module ir_d1 ir_d1 (IRConfig.running (ir_slot_lmach mem (IRScalar.int_ n) na dests rest))) (@Eq.subst IRConfig (fun (k : IRConfig) => @Eq IRConfig (ir_steps ir_d1 ir_slot_module k) (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n)))) (IRConfig.running (ir_slot_rmach mem (IRScalar.int_ n) na dests rest)) (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_lmach mem (IRScalar.int_ n) na dests rest))) (@Eq.symm IRConfig (ir_steps ir_d1 ir_slot_module (IRConfig.running (ir_slot_lmach mem (IRScalar.int_ n) na dests rest))) (IRConfig.running (ir_slot_rmach mem (IRScalar.int_ n) na dests rest)) (ir_slot_load_seg mem n na dests rest)) (@Eq.refl IRConfig (ir_ret_to dests rest (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na) (ir_vl1 (IRScalar.int_ n)))))))))";

const SRC_COST_IS_4: &str = "def ir_slot_cost_is_4 : @Eq Nat (Nat.add (Nat.add (Nat.add ir_d1 ir_d1) ir_d1) ir_d1) ir_d4 := @Eq.refl Nat ir_d4";

const SRC_CONCRETE: &str = "def ir_slot_concrete : @Eq IROutcome (ir_eval ir_d8 ir_slot_module ir_d0 (ir_vl1 (IRScalar.int_ ir_d5)) ir_mem0 ir_d7) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d5))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d5)))";

const SRC_RESUMES_CALLER: &str = "def ir_slot_resumes_caller (mem : IRList IRMemSlot) (n : Nat) (na : Nat) (dests : IRList Nat) (caller : IRFrame) (rest2 : IRList IRFrame) : @Eq IRConfig (ir_steps ir_d4 ir_slot_module (IRConfig.running (ir_slot_mach0 mem (IRScalar.int_ n) na dests (@IRList.cons IRFrame caller rest2)))) (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_many caller dests (ir_vl1 (IRScalar.int_ n))) rest2) (@IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem) (Nat.succ na))) := ir_slot_activation mem n na dests (@IRList.cons IRFrame caller rest2)";

/// **Every declaration this stage registers**, in registration order.
///
/// `pub` on purpose. The acceptance gate
/// (`crates/clean-verify/tests/eval_ir/slot_lemmas.rs`) holds its own census
/// copy against THIS list rather than against a name prefix, which is what
/// makes its exactness clause cover all 26 -- the five substrate
/// lemmas included. Those five (`ir_nat_sub_self`, `ir_nat_eqb_refl`,
/// `ir_mem_lookup_head`, `ir_mem_update_head`, `ir_mem_lookup_skip`) share no
/// prefix with the `ir_slot_` family, so a prefix-scoped clause pins the other
/// 21 and says nothing at all about them.
pub const SLOT_LEMMA_NAMES: &[&str] = &[
    // The store/load view family. Positionally FIRST because DECLS registers
    // them first; they depend on nothing below and everything below is
    // unchanged by them.
    "ir_exec_load_is_view",
    "ir_view_word_agg",
    "ir_view_opt_agg",
    "ir_view_ty_agg",
    "ir_load_view_opt_agg",
    "ir_load_view_agg",
    "ir_exec_load_agg",
    "ir_nat_sub_self",
    "ir_nat_eqb_walk_refl",
    "ir_nat_eqb_refl",
    "ir_mem_lookup_head",
    "ir_mem_update_head",
    "ir_mem_lookup_skip",
    "ir_slot_b0",
    "ir_slot_func",
    "ir_slot_module",
    "ir_slot_mach0",
    "ir_slot_smach",
    "ir_slot_lmach",
    "ir_slot_rmach",
    "ir_slot_after_store_lookup",
    "ir_slot_after_store_update",
    "ir_slot_after_load",
    "ir_slot_step_alloca",
    "ir_slot_step_store",
    "ir_slot_store_resolved",
    "ir_slot_step_load",
    "ir_slot_store_seg",
    "ir_slot_load_seg",
    "ir_slot_activation",
    "ir_slot_seg",
    "ir_slot_cost_is_4",
    "ir_slot_concrete",
    "ir_slot_resumes_caller",
];

// ---------------------------------------------------------------- the store/load
// asymmetry, stated at last.
//
// `ir_exec`'s two memory arms are NOT symmetric (eval_ir_machine.rs):
//
//     | IRInst.load  t p vol   => ir_bind_result s rs (ir_load_view (ir_mod_encs m) t (...))
//     | IRInst.store t p v vol => ir_store_exec s (ir_getd s p) (ir_getd s v)
//
// The load images the raw word through the module's encodings table at `t`; the
// store binds `t` and never uses it.
//
// The ASYMMETRY was already stated -- `ir_exec_store_ty_irrelevant`
// (eval_ir_adequacy.rs) proves a store executes identically at two different
// types, and re-deriving it here was refused as a duplicate, which is the
// registry working. What was NOT stated is why that is SOUND, and the answer
// was sitting unnamed in one match arm of each image function:
// `| IRScalar.aggv sp => IRScalar.aggv sp`. The view is the identity on a value
// that is already structured, so a store that writes structure and a load that
// images words agree exactly there. These declarations say that out loud, and
// say how far it goes.

const SRC_EXEC_LOAD_IS_VIEW: &str = "def ir_exec_load_is_view (m : IRModule) (t : IRTy) (p : Nat) (vol : Bool) (rs : IRList Nat) (s : IRMachine) : @Eq IRConfig (ir_exec m (IRInst.load t p vol) rs s) (ir_bind_result s rs (ir_load_view (ir_mod_encs m) t (ir_load_eval s (ir_getd s p)))) := @Eq.refl IRConfig (ir_bind_result s rs (ir_load_view (ir_mod_encs m) t (ir_load_eval s (ir_getd s p))))";

const SRC_VIEW_WORD_AGG: &str = "def ir_view_word_agg (rec_ : IRTy -> IRScalar -> IRScalar) (e : IREnc) (fs : IRScalar) : @Eq IRScalar (ir_view_word rec_ e (IRScalar.aggv fs)) (IRScalar.aggv fs) := @IREnc.rec (fun (e0 : IREnc) => @Eq IRScalar (ir_view_word rec_ e0 (IRScalar.aggv fs)) (IRScalar.aggv fs)) (fun (k : Nat) (no : Nat) (so : Nat) (pt : IRTy) => @Eq.refl IRScalar (IRScalar.aggv fs)) (fun (k : Nat) (i : Nat) (c : Nat) (pt : IRTy) => @Eq.refl IRScalar (IRScalar.aggv fs)) e";

const SRC_VIEW_OPT_AGG: &str = "def ir_view_opt_agg (ih : IRTy -> IRScalar -> IRScalar) (fs : IRScalar) (o : IROption IREnc) : @Eq IRScalar (@IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) (IRScalar.aggv fs) (fun (e : IREnc) => ir_view_word ih e (IRScalar.aggv fs)) o) (IRScalar.aggv fs) := @IROption.rec IREnc (fun (o0 : IROption IREnc) => @Eq IRScalar (@IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) (IRScalar.aggv fs) (fun (e : IREnc) => ir_view_word ih e (IRScalar.aggv fs)) o0) (IRScalar.aggv fs)) (@Eq.refl IRScalar (IRScalar.aggv fs)) (fun (e : IREnc) => ir_view_word_agg ih e fs) o";

const SRC_VIEW_TY_AGG: &str = "def ir_view_ty_agg (encs : IRList IREnc) (fs : IRScalar) : forall (n : Nat) (t : IRTy), @Eq IRScalar (ir_view_ty encs n t (IRScalar.aggv fs)) (IRScalar.aggv fs) := @Nat.rec (fun (k : Nat) => forall (t : IRTy), @Eq IRScalar (ir_view_ty encs k t (IRScalar.aggv fs)) (IRScalar.aggv fs)) (fun (t : IRTy) => @Eq.refl IRScalar (IRScalar.aggv fs)) (fun (k : Nat) (_ih : forall (t : IRTy), @Eq IRScalar (ir_view_ty encs k t (IRScalar.aggv fs)) (IRScalar.aggv fs)) (t : IRTy) => ir_view_opt_agg (ir_view_ty encs k) fs (ir_enc_find encs t))";

const SRC_LOAD_VIEW_OPT_AGG: &str = "def ir_load_view_opt_agg (encs : IRList IREnc) (fs : IRScalar) (o : IROption IREnc) : @Eq IRStepResult (@IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) (IRStepResult.value (IRScalar.aggv fs)) (fun (e : IREnc) => ir_view_result encs e (IRStepResult.value (IRScalar.aggv fs))) o) (IRStepResult.value (IRScalar.aggv fs)) := @IROption.rec IREnc (fun (o0 : IROption IREnc) => @Eq IRStepResult (@IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) (IRStepResult.value (IRScalar.aggv fs)) (fun (e : IREnc) => ir_view_result encs e (IRStepResult.value (IRScalar.aggv fs))) o0) (IRStepResult.value (IRScalar.aggv fs))) (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv fs))) (fun (e : IREnc) => @Eq.subst IRScalar (fun (x : IRScalar) => @Eq IRStepResult (IRStepResult.value x) (IRStepResult.value (IRScalar.aggv fs))) (IRScalar.aggv fs) (ir_view_word (ir_view_ty encs (ir_enc_len encs)) e (IRScalar.aggv fs)) (@Eq.symm IRScalar (ir_view_word (ir_view_ty encs (ir_enc_len encs)) e (IRScalar.aggv fs)) (IRScalar.aggv fs) (ir_view_word_agg (ir_view_ty encs (ir_enc_len encs)) e fs)) (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv fs)))) o";

const SRC_LOAD_VIEW_AGG: &str = "def ir_load_view_agg (encs : IRList IREnc) (t : IRTy) (fs : IRScalar) : @Eq IRStepResult (ir_load_view encs t (IRStepResult.value (IRScalar.aggv fs))) (IRStepResult.value (IRScalar.aggv fs)) := ir_load_view_opt_agg encs fs (ir_enc_find encs t)";

const SRC_EXEC_LOAD_AGG: &str = "def ir_exec_load_agg (m : IRModule) (t : IRTy) (p : Nat) (vol : Bool) (rs : IRList Nat) (s : IRMachine) (fs : IRScalar) (h : @Eq IRStepResult (ir_load_eval s (ir_getd s p)) (IRStepResult.value (IRScalar.aggv fs))) : @Eq IRConfig (ir_exec m (IRInst.load t p vol) rs s) (ir_bind_result s rs (IRStepResult.value (IRScalar.aggv fs))) := @Eq.subst IRStepResult (fun (r : IRStepResult) => @Eq IRConfig (ir_bind_result s rs (ir_load_view (ir_mod_encs m) t r)) (ir_bind_result s rs (IRStepResult.value (IRScalar.aggv fs)))) (IRStepResult.value (IRScalar.aggv fs)) (ir_load_eval s (ir_getd s p)) (@Eq.symm IRStepResult (ir_load_eval s (ir_getd s p)) (IRStepResult.value (IRScalar.aggv fs)) h) (@Eq.subst IRStepResult (fun (r : IRStepResult) => @Eq IRConfig (ir_bind_result s rs r) (ir_bind_result s rs (IRStepResult.value (IRScalar.aggv fs)))) (IRStepResult.value (IRScalar.aggv fs)) (ir_load_view (ir_mod_encs m) t (IRStepResult.value (IRScalar.aggv fs))) (@Eq.symm IRStepResult (ir_load_view (ir_mod_encs m) t (IRStepResult.value (IRScalar.aggv fs))) (IRStepResult.value (IRScalar.aggv fs)) (ir_load_view_agg (ir_mod_encs m) t fs)) (@Eq.refl IRConfig (ir_bind_result s rs (IRStepResult.value (IRScalar.aggv fs)))))";

/// `(source, description)`, positionally paired with [`SLOT_LEMMA_NAMES`].
///
/// The stage registers this table and NOTHING else, so the list above is the
/// set of declarations it adds by construction rather than by convention: an
/// added registration is a row here, and `test_every_source_declares_its_listed_name`
/// refuses a row whose source does not declare the name sitting beside it.
const DECLS: &[(&str, &str)] = &[
    (SRC_EXEC_LOAD_IS_VIEW, "ir_exec_load_is_view: the load arm of `ir_exec` IS the encoding view applied to the raw slot read -- by Eq.refl, so the kernel REDUCED the dispatch rather than taking anyone's word for it. Registered for two reasons. It pins the arm, so a change to the dispatch that moved the view breaks here rather than silently downstream. And it is the VACUITY CONTROL for ir_exec_load_agg: `ir_exec` occurs there only in a TYPE, where this elaborator turns an undeclared identifier into a free variable SILENTLY (measured -- ir_lzd_max_running_at_9 shipped that way naming an ir_d64 the bundle does not declare). An @Eq.refl against the spelled-out body cannot be satisfied by a free variable, so this declaration elaborating is what makes the one below a statement about the real dispatch. DerivedProved, zero axiom_deps."),
    (SRC_VIEW_WORD_AGG, "ir_view_word_agg: the encoding view at ONE row is the IDENTITY on a value that is already an aggregate. @IREnc.rec over the two rows, @Eq.refl at each, because ir_niche_image and ir_wrap_image both carry `| IRScalar.aggv sp => IRScalar.aggv sp`. That clause is why `ir_exec`'s store arm can bind its type and never use it: a store writes a STRUCTURED value into a cell, and the load that reads it back applies the table to a value the table leaves alone. `ir_exec_store_ty_irrelevant` (adequacy) already stated that the store ignores its type; what nothing stated is that ignoring it is HARMLESS, which needs this clause named. DerivedProved, zero axiom_deps."),
    (SRC_VIEW_OPT_AGG, "ir_view_opt_agg: the same across the table LOOKUP, whose result is stuck at an abstract table and an abstract type. Stated for an arbitrary IROption and applied at `ir_enc_find encs t` afterwards, which is cheaper than a convoy and says the stronger thing: the identity holds whether or not the type has a row at all. DerivedProved, zero axiom_deps."),
    (SRC_VIEW_TY_AGG, "ir_view_ty_agg: at EVERY fuel and EVERY type. @Nat.rec on the fuel; the induction hypothesis is unused, which is the content -- the recursive view is passed to ir_view_word and discarded by the aggregate arm before it can be applied, so the identity does not depend on the payload chain terminating. A table that chains deeper than it is long fails open to the identity, and this says the identity is right there too. DerivedProved, zero axiom_deps."),
    (SRC_LOAD_VIEW_OPT_AGG, "ir_load_view_opt_agg: the step-result level, over an arbitrary table lookup. The some-arm is a congruence of IRStepResult.value over ir_view_word_agg at the table's own length as fuel. DerivedProved, zero axiom_deps."),
    (SRC_LOAD_VIEW_AGG, "ir_load_view_agg: *** A LOAD RETURNS A STRUCTURED CELL UNCHANGED, AT ANY TYPE, UNDER ANY TABLE. *** One application of the lemma above at the real lookup. DerivedProved, zero axiom_deps."),
    (SRC_EXEC_LOAD_AGG, "ir_exec_load_agg: *** THE ANSWER TO THE STORE/LOAD ASYMMETRY, AND ITS EXACT SCOPE. *** For ANY module -- so any encodings table -- and ANY type, if the cell a load reaches holds an aggregate, the instruction binds that aggregate. Two nested Eq.substs over ir_load_view_agg. \n\nSO: `ir_exec`'s store arm ignoring its type is SOUND for structured values, and this is the theorem that says so rather than an inspection of two match arms. `ir_exec_store_ty_irrelevant` states the asymmetry; this states its licence. The scope it does NOT cover, named rather than left to be found: a store of a RAW WORD at an encoded type. Memory would then hold a word the load images, so store-then-load is the view rather than the identity, and the missing store-side LOWERING would be needed to make that round-trip. No body in this chain does it -- every store in the derived bundle writes a value the machine already structured -- and a body that did would need the inverse of ir_view_word, which no row carries. That is the general-niche residual, now stated as a boundary of a proved theorem instead of a gap in an unexamined one. DerivedProved, zero axiom_deps."),
    (SRC_NAT_SUB_SELF, "ir_nat_sub_self: k - k = 0, by @Nat.rec on k. The successor case is ir_nat_sub_succ_succ followed by the induction hypothesis; the zero case is @Eq.refl because Nat.sub recurses on its SECOND argument and `0 - 0` peels. Stated under an `ir_` name for the same reason ir_nat_sub_zero_left is: the Lean production prelude has no `k - k = 0`, and the foundation stage's `@Nat.sub_self` is not in the dependency-scoped EvalIr bundle (measured: the probe's negative control `neg:Nat.sub_self_available` is the one that does not elaborate here). DerivedProved, zero axiom_deps."),
    (SRC_NAT_EQB_WALK_REFL, "ir_nat_eqb_walk_refl: the unary walk says true at n compared with itself, by induction with the induction hypothesis used UNCHANGED -- `ir_nat_eqb_walk (succ k) (succ k)` reduces to `ir_nat_eqb_walk k k` by two iota steps and delta, so the successor minor is `ih` and nothing else. No subtraction appears anywhere in it, which is the point: the exporter's replay guard rewrites `Nat.sub` inside reflected COMPARISON bodies and this walk has none, so the shape Clean checks and the shape Lean checks are the same shape. DerivedProved, zero axiom_deps."),
    (SRC_NAT_EQB_REFL, "ir_nat_eqb_refl: the machine's equality test says true at a symbolic address compared with itself. THE lemma the whole return slot rests on -- every head-cell resolution below is this fact under an ir_eq_cong. It is NOT Eq.refl: ir_nat_eqb peels to a @Bool.rec whose scrutinee is a subtraction test, and that test is stuck at a symbolic k (the probe's negative control `neg:eqb_refl_by_computation` is exactly that failure). It is also NO LONGER a rewrite of that subtraction: through 2026-09-15 this was `ir_eq_cong` moving ir_nat_sub_self under the Bool.rec, which Clean accepts and Lean CANNOT, because the exporter's replay guard emits `ReplayBridge.sub` inside `ir_nat_sub_eqb` and leaves ir_nat_sub_self speaking about the raw `Nat.sub` -- at a symbolic k the two are not defeq and the rewrite lands on a term the goal does not contain (`gate::leancross` type mismatch). It now goes through the unary walk instead: ir_nat_eqb_walk_eq to change representation, then ir_nat_eqb_walk_refl, neither of which names a subtraction. DerivedProved, zero axiom_deps, and re-checked by a disjoint kernel."),
    (SRC_MEM_LOOKUP_HEAD, "ir_mem_lookup_head: a lookup at the address of the HEAD cell returns that cell. ir_mem_lookup's cons case is a @Bool.rec on `ir_nat_eqb i a`, stuck at a symbolic address; ir_eq_cong on that major with ir_nat_eqb_refl closes it. This is what makes an alloca'd return slot resolvable at an ABSTRACT allocation counter: alloca conses its cell at the head, so every store and load through `ptr_ na` lands here. DerivedProved, zero axiom_deps."),
    (SRC_MEM_UPDATE_HEAD, "ir_mem_update_head: a store at the address of the HEAD cell rewrites that cell and leaves the tail alone -- liveness preserved, no walk. The dual of ir_mem_lookup_head and the same proof: ir_eq_cong on the @Bool.rec major with ir_nat_eqb_refl. DerivedProved, zero axiom_deps."),
    (SRC_MEM_LOOKUP_SKIP, "ir_mem_lookup_skip: the FRAME half. A lookup at any other address walks past the head cell untouched, so an activation that allocates a fresh slot does not disturb what the caller could already read. Takes the disequality as a hypothesis rather than deciding it -- addresses are symbolic here and the machine's own test is the only decision procedure in scope. DerivedProved, zero axiom_deps."),
    (SRC_SLOT_B0, "ir_slot_b0: the return-slot block, four nodes -- `%1 = alloca T`, `store T %0, ptr %1`, `%2 = load T, ptr %1`, `ret %2`. This is the shape rustc emits for a by-value return through a stack temporary, and it is the shape the derived bundle's as_deref / expect / Arc::deref bodies open with. Modelled with the alloca KEPT: no mem2reg rewrite is needed for it to close."),
    (SRC_SLOT_FUNC, "ir_slot_func: function 0 -- one parameter, one block, no locals beyond the slot."),
    (SRC_SLOT_MODULE, "ir_slot_module: the one-function module the slot lemmas below are stated against. Its own module, not ir_lzb_module: these lemmas are about an instruction PATTERN, and pinning them to the designated target's module would make them unusable for the callee bodies that motivated them."),
    (SRC_MACH0, "ir_slot_mach0: the machine at block entry -- the parameter bound to an arbitrary scalar, on an ARBITRARY heap `mem`, at an ARBITRARY next-address counter `na`, stacked on whatever the caller had. Every one of those stays quantified, which is the whole point: a slot lemma that needed a concrete heap or a concrete counter could not be spliced into a caller's segment."),
    (SRC_SMACH, "ir_slot_smach: after the alloca. `%1` is bound to `ptr_ na`, the fresh cell is consed at the memory HEAD holding `undef_`, and the counter is bumped to `succ na`. The head position is what every resolution below exploits."),
    (SRC_LMACH, "ir_slot_lmach: after the store. The frame has advanced one node and the head cell now holds the stored value; the tail of memory is untouched."),
    (SRC_RMACH, "ir_slot_rmach: after the load. `%2` is bound to the value that was stored -- the round-trip the slot exists to perform."),
    (SRC_AFTER_STORE_LOOKUP, "ir_slot_after_store_lookup: the store step as a function of the LOOKED-UP SLOT. Same device as ir_lzm_after_load: the goal never mentions `ir_mem_lookup`, so @Eq.subst has nothing to rewrite until a shape lemma restates the step with the lookup occurring literally."),
    (SRC_AFTER_STORE_UPDATE, "ir_slot_after_store_update: the store step's continuation as a function of the UPDATED MEMORY. The store has two stuck subterms, not one -- the liveness lookup and the write -- so it needs two abstraction points where the load needs one."),
    (SRC_AFTER_LOAD, "ir_slot_after_load: the load step as a function of the looked-up slot."),
    (SRC_STEP_ALLOCA, "ir_slot_step_alloca: the alloca COMPUTES. Eq.refl, at an abstract heap and an abstract counter -- allocation consults nothing, so nothing is stuck, and the cost of the node is one step. The content is the shape, not the equality."),
    (SRC_STEP_STORE, "ir_slot_step_store: the store step, restated so `ir_mem_lookup (fresh cell :: mem) na` occurs syntactically. Eq.refl; this is the hook ir_mem_lookup_head fires through."),
    (SRC_STORE_RESOLVED, "ir_slot_store_resolved: once the liveness lookup is the concrete head cell, the store commits by computation to `ir_mem_update` on the same memory. @Eq.refl -- the remaining stuck term is the write itself, which ir_mem_update_head resolves."),
    (SRC_STEP_LOAD, "ir_slot_step_load: the load step, restated so its lookup occurs syntactically. Eq.refl."),
    (SRC_STORE_SEG, "ir_slot_store_seg: ONE step from the post-alloca machine to the post-store machine, at an abstract heap and an abstract counter. Two nested Eq.substs -- ir_mem_lookup_head for the liveness read, then ir_mem_update_head for the write -- and @Eq.refl underneath. Both go through @Eq.symm because the proofs live on the concrete side and the goal sits on the stuck side. DerivedProved, zero axiom_deps."),
    (SRC_LOAD_SEG, "ir_slot_load_seg: ONE step from the post-store machine to the post-load machine. Stated at `v := int_ n` for an abstract n rather than at an abstract scalar, because ir_load_slot dispatches on the value's CONSTRUCTOR: a fully opaque `v` is stuck for a reason no lemma about memory can remove. That is a real boundary of this family and it is named here rather than discovered downstream. DerivedProved, zero axiom_deps."),
    (SRC_ACTIVATION, "ir_slot_activation: THE SLOT LEMMA. Four steps from block entry to the caller's resumption, on an arbitrary heap, at an arbitrary allocation counter, under an arbitrary caller -- and the value returned is the value passed in. Three nested Eq.substs (lookup, update, lookup) with @Eq.refl at the leaf, the ir_lzm_activation_* shape. This is what the Phase-B probe was built to settle: the alloca/store/load return slot closes at an ABSTRACT counter, so no mem2reg rewrite is needed anywhere in the derived bundle. DerivedProved, zero axiom_deps."),
    (SRC_SEG, "ir_slot_seg: the SAME fact by the segment-splicing shape a generator emits -- @Eq.trans / ir_steps_add / @Eq.subst per segment, with the two literal nodes left to compute and the two lemma-backed nodes spliced in as opaque segments. Proving the slot twice, by the leaf shape above and by the chain shape here, is what licenses a generator to emit the chain form for these nodes without re-deriving the semantics each time. DerivedProved, zero axiom_deps."),
    (SRC_COST_IS_4, "ir_slot_cost_is_4: the chain's right-nested Nat.add of segment costs IS 4, by Eq.refl. One node, one step, four nodes -- the arithmetic pin that stops a generator from silently mis-costing a slot."),
    (SRC_CONCRETE, "ir_slot_concrete: a closed run of the same function through ir_eval -- called with `int_ 5` on the empty heap at counter 7, it halts returning `[5]`. Eq.refl, so the kernel RAN the machine. The abstract lemmas above could in principle be true of a machine that does something else entirely at concrete arguments; this is the control that says they are not."),
    (SRC_RESUMES_CALLER, "ir_slot_resumes_caller: with a real caller frame underneath, the four steps land ON that caller with its result ids bound to the returned value. ir_ret_to is stuck on an opaque frame stack in ir_slot_activation; instantiating it with `cons caller rest2` unsticks it and the whole statement follows by application alone. The composition half of the slot lemma, and what a caller's segment proof actually consumes."),
];

impl Specification {
    /// Register the return-slot lemmas and the substrate facts they rest on.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_slot_lemmas(&mut self) -> Result<(), SpecError> {
        for (source, description) in DECLS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The sources stay ASCII and balanced — the same cheap structural check
    /// the sibling activation stage runs.
    #[test]
    fn test_sources_balanced_ascii() {
        for src in all_sources() {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(
                src.matches('(').count(),
                src.matches(')').count(),
                "unbalanced parens in: {}",
                &src[..60.min(src.len())]
            );
        }
    }

    /// Each source declares the name the gate list claims it declares, and the
    /// two lists stay the same length.
    #[test]
    fn test_every_source_declares_its_listed_name() {
        assert_eq!(all_sources().len(), SLOT_LEMMA_NAMES.len());
        for (src, name) in all_sources().iter().zip(SLOT_LEMMA_NAMES) {
            assert!(
                src.starts_with(&format!("def {name} ")),
                "{name} is not what {} declares",
                &src[..40.min(src.len())]
            );
        }
    }

    /// The probe prefix must not survive the port.
    #[test]
    fn test_no_probe_names_remain() {
        for src in all_sources() {
            assert!(
                !src.contains("ir_probe_"),
                "probe prefix leaked into the spec"
            );
        }
    }

    /// The four shape witnesses earn their place by SHAPE: each must stay an
    /// `Eq.refl`, because their content is that the step is already
    /// definitionally what the next lemma rewrites in.
    #[test]
    fn test_shape_witnesses_are_refl() {
        for src in [
            SRC_STEP_ALLOCA,
            SRC_STEP_STORE,
            SRC_STORE_RESOLVED,
            SRC_STEP_LOAD,
        ] {
            assert!(src.contains(":= @Eq.refl IRConfig"));
        }
    }

    /// The caller's state stays universally quantified everywhere it appears.
    /// A slot lemma that fixed the heap, the allocation counter or the frame
    /// stack could not be spliced into a caller's segment, which is the only
    /// thing these lemmas are for.
    #[test]
    fn test_slot_is_stated_at_an_abstract_heap_and_counter() {
        for src in [SRC_MACH0, SRC_STORE_SEG, SRC_ACTIVATION, SRC_SEG] {
            assert!(src.contains("(mem : IRList IRMemSlot)"), "heap abstract");
            assert!(src.contains("(na : Nat)"), "allocation counter abstract");
            assert!(src.contains("(rest : IRList IRFrame)"), "caller abstract");
        }
    }

    /// The stage's own table, projected. Nothing is re-listed here: a source
    /// that is not registered cannot be tested, and a registration that is not
    /// listed cannot exist.
    fn all_sources() -> Vec<&'static str> {
        DECLS.iter().map(|(src, _doc)| *src).collect()
    }
}
