// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **`ir_ctr` -- step-indexed contracts with a safety conjunct, and their
//! soundness** (decision memo §6 Phase E, E2; D5(a)/(b); statements settled in
//! `designs/2026-09-24-e2-contract-soundness.md`).
//!
//! A contract is stated in the tree's shape: the post is attached to the
//! POST-RETURN configuration `ir_ret_to d r mem2 na2 vs`, for every caller
//! `d r` -- the configuration the exact contracts `hc1`/`hc2` of
//! `ir_it_ag_activation` and the recursion hypotheses of the `ir_lzd_*_seg`
//! lemmas name. What changes is that it is no longer an EXACT run:
//!
//! * `ir_safe G m n c` -- for every k <= n, the configuration after k steps is
//!   running, halted with a SANCTIONED panic (`ir_sanctioned`: `ub
//!   assert_failed` and nothing else), or halted with an outcome `G` accepts.
//!   Downward closed in n (`ir_safe_down`, `ir_safe_down_add`), and composes
//!   with an exact run (`ir_safe_steps`, `ir_safe_steps_inv`, `ir_safe_pad`).
//! * `ir_ctr_at m E Q n` -- in continuation form: for every `G`, every caller
//!   `d r`, if the caller's continuation from every `Q`-satisfying return is
//!   safe for n steps, then the callee's entry is safe for n steps. The reading
//!   at the empty caller stack is the three-way statement of D5(b)
//!   (`ir_ctr_tri`): at every k <= n the run is running, has halted with a
//!   sanctioned panic, or has returned values some final heap satisfies `Q` for.
//! * `ir_ctr_of_exact` -- an EXACT run in the `hc1` shape implies the contract
//!   at every budget (the adapter), and `ir_ctr_group_sound` -- a recursion
//!   group whose bodies meet their local obligation at `n + 1` assuming the
//!   group's contracts at `n` meets every contract at every budget. Plain
//!   `Nat.rec`; the downward closure lives in `ir_safe`, so no strong induction
//!   is needed and this stage stays in the EvalIr bundle.
//!
//! Partial correctness only. Nothing here says a run TERMINATES; D5 gives that
//! up on purpose (the target's recursion group has no measure).
//!
//! No Or / And / Exists / False: a disjunction is a `Bool.rec` into `Prop`,
//! falsity is `forall (C : Prop), C`, and truth is `Eq Bool Bool.true
//! Bool.true`. Registered in BOTH the Full stage list and the EvalIr bundle,
//! after `add_eval_ir_stack_split`. Every declaration kernel-checked, empty
//! axiom closure, by name.

use super::{SpecError, Specification};

// ── A. the sanctioned-halt classifier ─────────────────────────────────────
// IRFault has 24 constructors; `assert_failed` is the 15th. Appending a
// constructor makes this recursor fail to elaborate, loudly, by name.
const SRC_FAULT_IS_ASSERT: &str = "def ir_fault_is_assert (f : IRFault) : Bool := IRFault.rec (fun (_ : IRFault) => Bool) Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.true Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false Bool.false f";
const SRC_SANCTIONED: &str = "def ir_sanctioned (o : IROutcome) : Bool := IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (_ : IRList IRScalar) => Bool.false) (fun (f : IRFault) => ir_fault_is_assert f) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) Bool.false o";
const SRC_BAD_HALT: &str = "def ir_bad_halt (o : IROutcome) : Bool := IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (_ : IRList IRScalar) => Bool.false) (fun (f : IRFault) => Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false (ir_fault_is_assert f)) (fun (_ : IRFault) => Bool.true) (fun (_ : IRFault) => Bool.true) (fun (_ : IRFault) => Bool.true) Bool.false o";
const SRC_SANCTIONED_ASSERT: &str = "def ir_sanctioned_assert_failed : Eq Bool (ir_sanctioned (IROutcome.ub IRFault.assert_failed)) Bool.true := Eq.refl Bool Bool.true";
const SRC_SANCTIONED_UNREACHABLE: &str = "def ir_sanctioned_unreachable : Eq Bool (ir_sanctioned (IROutcome.ub IRFault.unreachable)) Bool.false := Eq.refl Bool Bool.false";
const SRC_SANCTIONED_ATOMIC: &str = "def ir_sanctioned_atomic_arm (m : IRModule) (p : Nat) (v : Nat) (rs : IRList Nat) (s : IRMachine) : Eq Bool (ir_sanctioned (ir_config_outcome (ir_exec m (IRInst.atomic_fetch_add_relaxed_u64_seq p v) rs s))) Bool.false := Eq.refl Bool Bool.false";
const SRC_BAD_ATOMIC: &str = "def ir_bad_halt_atomic_arm (m : IRModule) (p : Nat) (v : Nat) (rs : IRList Nat) (s : IRMachine) : Eq Bool (ir_bad_halt (ir_config_outcome (ir_exec m (IRInst.atomic_fetch_add_relaxed_u64_seq p v) rs s))) Bool.true := Eq.refl Bool Bool.true";
// Crystal decision memo §15 (lead's ruling on D10), executed in §18: the projector images an
// undefined-behaviour halt as `IRInst.unreachable` (never the sanctioned-panic `assert`), and these
// two pin that the `unreachable` ARM -- at every module and machine, so at every projected body --
// halts with an outcome the sanctioned-panic arm refuses and the contract device calls bad.
const SRC_SANCTIONED_UNREACHABLE_ARM: &str = "def ir_sanctioned_unreachable_arm (m : IRModule) (rs : IRList Nat) (s : IRMachine) : Eq Bool (ir_sanctioned (ir_config_outcome (ir_exec m IRInst.unreachable rs s))) Bool.false := Eq.refl Bool Bool.false";
const SRC_BAD_UNREACHABLE_ARM: &str = "def ir_bad_halt_unreachable_arm (m : IRModule) (rs : IRList Nat) (s : IRMachine) : Eq Bool (ir_bad_halt (ir_config_outcome (ir_exec m IRInst.unreachable rs s))) Bool.true := Eq.refl Bool Bool.true";
const SRC_BAD_UNREACHABLE: &str = "def ir_bad_halt_unreachable : Eq Bool (ir_bad_halt (IROutcome.ub IRFault.unreachable)) Bool.true := Eq.refl Bool Bool.true";
const SRC_BAD_ASSERT: &str = "def ir_bad_halt_assert_failed : Eq Bool (ir_bad_halt (IROutcome.ub IRFault.assert_failed)) Bool.false := Eq.refl Bool Bool.false";
const SRC_BAD_TYPE_ERROR: &str = "def ir_bad_halt_type_error (f : IRFault) : Eq Bool (ir_bad_halt (IROutcome.type_error f)) Bool.true := Eq.refl Bool Bool.true";
const SRC_BAD_UNMODELLED: &str = "def ir_bad_halt_unmodelled (f : IRFault) : Eq Bool (ir_bad_halt (IROutcome.unmodelled f)) Bool.true := Eq.refl Bool Bool.true";
const SRC_BAD_STUCK: &str = "def ir_bad_halt_stuck (f : IRFault) : Eq Bool (ir_bad_halt (IROutcome.stuck f)) Bool.true := Eq.refl Bool Bool.true";
const SRC_BAD_RET: &str = "def ir_bad_halt_ret (vs : IRList IRScalar) : Eq Bool (ir_bad_halt (IROutcome.ret vs)) Bool.false := Eq.refl Bool Bool.false";

// ── B. safety over a step budget ───────────────────────────────────────────
const SRC_BPROP: &str = "def ir_bprop (P : Prop) (Q : Prop) (b : Bool) : Prop := Bool.rec (fun (_ : Bool) => Prop) P Q b";
const SRC_OKHALT: &str = "def ir_okhalt (G : IROutcome -> Prop) (o : IROutcome) : Prop := ir_bprop (G o) (Eq Bool Bool.true Bool.true) (ir_sanctioned o)";
const SRC_HALTOK: &str = "def ir_haltok (G : IROutcome -> Prop) (c : IRConfig) : Prop := IRConfig.rec (fun (_ : IRConfig) => Prop) (fun (_ : IRMachine) => Eq Bool Bool.true Bool.true) (fun (o : IROutcome) => ir_okhalt G o) c";
const SRC_SAFE: &str = "def ir_safe (G : IROutcome -> Prop) (m : IRModule) (n : Nat) (c : IRConfig) : Prop := Nat.rec (fun (_ : Nat) => IRConfig -> Prop) (fun (c0 : IRConfig) => ir_haltok G c0) (fun (_ : Nat) (ih : IRConfig -> Prop) => fun (c0 : IRConfig) => IRConfig.rec (fun (_ : IRConfig) => Prop) (fun (s : IRMachine) => ih (ir_step m s)) (fun (o : IROutcome) => ir_okhalt G o) c0) n c";
const SRC_RUN_OK: &str = "def ir_run_ok (G : IROutcome -> Prop) (o : IROutcome) : Prop := IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (vs : IRList IRScalar) => ir_okhalt G (IROutcome.ret vs)) (fun (f : IRFault) => ir_okhalt G (IROutcome.ub f)) (fun (f : IRFault) => ir_okhalt G (IROutcome.type_error f)) (fun (f : IRFault) => ir_okhalt G (IROutcome.unmodelled f)) (fun (f : IRFault) => ir_okhalt G (IROutcome.stuck f)) (Eq Bool Bool.true Bool.true) o";
const SRC_SAFE_ZERO_RUNNING: &str = "def ir_safe_zero_running (G : IROutcome -> Prop) (m : IRModule) (s : IRMachine) : ir_safe G m Nat.zero (IRConfig.running s) := Eq.refl Bool Bool.true";
const SRC_SAFE_SUCC_RUNNING: &str = "def ir_safe_succ_running (G : IROutcome -> Prop) (m : IRModule) (n : Nat) (s : IRMachine) (h : ir_safe G m n (ir_step m s)) : ir_safe G m (Nat.succ n) (IRConfig.running s) := h";
const SRC_SAFE_HALTED: &str = "def ir_safe_halted (G : IROutcome -> Prop) (m : IRModule) (o : IROutcome) (n : Nat) (h : ir_okhalt G o) : ir_safe G m n (IRConfig.halted o) := Nat.rec (fun (k : Nat) => ir_safe G m k (IRConfig.halted o)) h (fun (k : Nat) (_ : ir_safe G m k (IRConfig.halted o)) => h) n";
const SRC_SAFE_HALTED_INV: &str = "def ir_safe_halted_inv (G : IROutcome -> Prop) (m : IRModule) (o : IROutcome) (n : Nat) (h : ir_safe G m n (IRConfig.halted o)) : ir_okhalt G o := Nat.rec (fun (k : Nat) => ir_safe G m k (IRConfig.halted o) -> ir_okhalt G o) (fun (h0 : ir_safe G m Nat.zero (IRConfig.halted o)) => h0) (fun (k : Nat) (_ : ir_safe G m k (IRConfig.halted o) -> ir_okhalt G o) (h0 : ir_safe G m (Nat.succ k) (IRConfig.halted o)) => h0) n h";
const SRC_SAFE_DOWN: &str = "def ir_safe_down (G : IROutcome -> Prop) (m : IRModule) (n : Nat) : forall (c : IRConfig), ir_safe G m (Nat.succ n) c -> ir_safe G m n c := Nat.rec (fun (k : Nat) => forall (c : IRConfig), ir_safe G m (Nat.succ k) c -> ir_safe G m k c) (fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => ir_safe G m (Nat.succ Nat.zero) c0 -> ir_safe G m Nat.zero c0) (fun (s : IRMachine) (_ : ir_safe G m (Nat.succ Nat.zero) (IRConfig.running s)) => Eq.refl Bool Bool.true) (fun (o : IROutcome) (h : ir_safe G m (Nat.succ Nat.zero) (IRConfig.halted o)) => h) c) (fun (k : Nat) (ih : forall (c : IRConfig), ir_safe G m (Nat.succ k) c -> ir_safe G m k c) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => ir_safe G m (Nat.succ (Nat.succ k)) c0 -> ir_safe G m (Nat.succ k) c0) (fun (s : IRMachine) (h : ir_safe G m (Nat.succ (Nat.succ k)) (IRConfig.running s)) => ih (ir_step m s) h) (fun (o : IROutcome) (h : ir_safe G m (Nat.succ (Nat.succ k)) (IRConfig.halted o)) => h) c) n";
const SRC_SAFE_DOWN_ADD: &str = "def ir_safe_down_add (G : IROutcome -> Prop) (m : IRModule) (n : Nat) (a : Nat) : forall (c : IRConfig), ir_safe G m (Nat.add n a) c -> ir_safe G m n c := Nat.rec (fun (k : Nat) => forall (c : IRConfig), ir_safe G m (Nat.add n k) c -> ir_safe G m n c) (fun (c : IRConfig) (h : ir_safe G m (Nat.add n Nat.zero) c) => h) (fun (k : Nat) (ih : forall (c : IRConfig), ir_safe G m (Nat.add n k) c -> ir_safe G m n c) => fun (c : IRConfig) (h : ir_safe G m (Nat.add n (Nat.succ k)) c) => ih c (ir_safe_down G m (Nat.add n k) c h)) a";
const SRC_SAFE_STEPS: &str = "def ir_safe_steps (G : IROutcome -> Prop) (m : IRModule) (b : Nat) (a : Nat) : forall (c : IRConfig), ir_safe G m b (ir_steps a m c) -> ir_safe G m (Nat.add b a) c := Nat.rec (fun (k : Nat) => forall (c : IRConfig), ir_safe G m b (ir_steps k m c) -> ir_safe G m (Nat.add b k) c) (fun (c : IRConfig) (h : ir_safe G m b (ir_steps Nat.zero m c)) => h) (fun (k : Nat) (ih : forall (c : IRConfig), ir_safe G m b (ir_steps k m c) -> ir_safe G m (Nat.add b k) c) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => ir_safe G m b (ir_steps (Nat.succ k) m c0) -> ir_safe G m (Nat.add b (Nat.succ k)) c0) (fun (s : IRMachine) (h : ir_safe G m b (ir_steps (Nat.succ k) m (IRConfig.running s))) => ih (ir_step m s) h) (fun (o : IROutcome) (h : ir_safe G m b (ir_steps (Nat.succ k) m (IRConfig.halted o))) => ir_safe_halted G m o (Nat.add b (Nat.succ k)) (ir_safe_halted_inv G m o b h)) c) a";
const SRC_SAFE_STEPS_INV: &str = "def ir_safe_steps_inv (G : IROutcome -> Prop) (m : IRModule) (b : Nat) (a : Nat) : forall (c : IRConfig), ir_safe G m (Nat.add b a) c -> ir_safe G m b (ir_steps a m c) := Nat.rec (fun (k : Nat) => forall (c : IRConfig), ir_safe G m (Nat.add b k) c -> ir_safe G m b (ir_steps k m c)) (fun (c : IRConfig) (h : ir_safe G m (Nat.add b Nat.zero) c) => h) (fun (k : Nat) (ih : forall (c : IRConfig), ir_safe G m (Nat.add b k) c -> ir_safe G m b (ir_steps k m c)) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => ir_safe G m (Nat.add b (Nat.succ k)) c0 -> ir_safe G m b (ir_steps (Nat.succ k) m c0)) (fun (s : IRMachine) (h : ir_safe G m (Nat.add b (Nat.succ k)) (IRConfig.running s)) => ih (ir_step m s) h) (fun (o : IROutcome) (h : ir_safe G m (Nat.add b (Nat.succ k)) (IRConfig.halted o)) => ir_safe_halted G m o b (ir_safe_halted_inv G m o (Nat.add b (Nat.succ k)) h)) c) a";
const SRC_SAFE_PAD: &str = "def ir_safe_pad (G : IROutcome -> Prop) (m : IRModule) (n : Nat) (a : Nat) (c : IRConfig) (h : ir_safe G m n (ir_steps a m c)) : ir_safe G m n c := ir_safe_down_add G m n a c (ir_safe_steps G m n a c h)";
const SRC_SAFE_END: &str = "def ir_safe_end (G : IROutcome -> Prop) (m : IRModule) (n : Nat) : forall (c : IRConfig), ir_safe G m n c -> ir_haltok G (ir_steps n m c) := Nat.rec (fun (k : Nat) => forall (c : IRConfig), ir_safe G m k c -> ir_haltok G (ir_steps k m c)) (fun (c : IRConfig) (h : ir_safe G m Nat.zero c) => h) (fun (k : Nat) (ih : forall (c : IRConfig), ir_safe G m k c -> ir_haltok G (ir_steps k m c)) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => ir_safe G m (Nat.succ k) c0 -> ir_haltok G (ir_steps (Nat.succ k) m c0)) (fun (s : IRMachine) (h : ir_safe G m (Nat.succ k) (IRConfig.running s)) => ih (ir_step m s) h) (fun (o : IROutcome) (h : ir_safe G m (Nat.succ k) (IRConfig.halted o)) => h) c) n";
const SRC_SAFE_AT: &str = "def ir_safe_at (G : IROutcome -> Prop) (m : IRModule) (n : Nat) (c : IRConfig) (h : ir_safe G m n c) (k : Nat) (j : Nat) (hk : Eq Nat (Nat.add k j) n) : ir_haltok G (ir_steps k m c) := ir_safe_end G m k c (ir_safe_down_add G m k j c (Eq.subst Nat (fun (x : Nat) => ir_safe G m x c) n (Nat.add k j) (Eq.symm Nat (Nat.add k j) n hk) h))";
const SRC_HALTOK_OUTCOME: &str = "def ir_haltok_outcome (G : IROutcome -> Prop) (c : IRConfig) (h : ir_haltok G c) : ir_run_ok G (ir_config_outcome c) := IRConfig.rec (fun (c0 : IRConfig) => ir_haltok G c0 -> ir_run_ok G (ir_config_outcome c0)) (fun (s : IRMachine) (_ : ir_haltok G (IRConfig.running s)) => Eq.refl Bool Bool.true) (fun (o : IROutcome) (h0 : ir_haltok G (IRConfig.halted o)) => IROutcome.rec (fun (o0 : IROutcome) => ir_okhalt G o0 -> ir_run_ok G o0) (fun (vs : IRList IRScalar) (h1 : ir_okhalt G (IROutcome.ret vs)) => h1) (fun (f : IRFault) (h1 : ir_okhalt G (IROutcome.ub f)) => h1) (fun (f : IRFault) (h1 : ir_okhalt G (IROutcome.type_error f)) => h1) (fun (f : IRFault) (h1 : ir_okhalt G (IROutcome.unmodelled f)) => h1) (fun (f : IRFault) (h1 : ir_okhalt G (IROutcome.stuck f)) => h1) (fun (_ : ir_okhalt G IROutcome.fuel_out) => Eq.refl Bool Bool.true) o h0) c h";
const SRC_BAD_GOAL: &str = "def ir_bad_goal (C : Prop) (o : IROutcome) : Prop := ir_bprop (Eq Bool Bool.true Bool.true) C (ir_bad_halt o)";
const SRC_OKHALT_BAD: &str = "def ir_okhalt_bad (C : Prop) (o : IROutcome) (hbad : Eq Bool (ir_bad_halt o) Bool.true) (h : ir_okhalt (ir_bad_goal C) o) : C := IROutcome.rec (fun (o0 : IROutcome) => Eq Bool (ir_bad_halt o0) Bool.true -> ir_okhalt (ir_bad_goal C) o0 -> C) (fun (vs : IRList IRScalar) (hb : Eq Bool (ir_bad_halt (IROutcome.ret vs)) Bool.true) (_ : ir_okhalt (ir_bad_goal C) (IROutcome.ret vs)) => ir_bool_false_ne_true C hb) (fun (f : IRFault) (hb : Eq Bool (ir_bad_halt (IROutcome.ub f)) Bool.true) (hk : ir_okhalt (ir_bad_goal C) (IROutcome.ub f)) => Bool.rec (fun (b : Bool) => Eq Bool (Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false b) Bool.true -> ir_bprop (ir_bprop (Eq Bool Bool.true Bool.true) C (Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false b)) (Eq Bool Bool.true Bool.true) b -> C) (fun (_ : Eq Bool Bool.true Bool.true) (hc : C) => hc) (fun (hb2 : Eq Bool Bool.false Bool.true) (_ : Eq Bool Bool.true Bool.true) => ir_bool_false_ne_true C hb2) (ir_fault_is_assert f) hb hk) (fun (f : IRFault) (_ : Eq Bool (ir_bad_halt (IROutcome.type_error f)) Bool.true) (hk : ir_okhalt (ir_bad_goal C) (IROutcome.type_error f)) => hk) (fun (f : IRFault) (_ : Eq Bool (ir_bad_halt (IROutcome.unmodelled f)) Bool.true) (hk : ir_okhalt (ir_bad_goal C) (IROutcome.unmodelled f)) => hk) (fun (f : IRFault) (_ : Eq Bool (ir_bad_halt (IROutcome.stuck f)) Bool.true) (hk : ir_okhalt (ir_bad_goal C) (IROutcome.stuck f)) => hk) (fun (hb : Eq Bool (ir_bad_halt IROutcome.fuel_out) Bool.true) (_ : ir_okhalt (ir_bad_goal C) IROutcome.fuel_out) => ir_bool_false_ne_true C hb) o hbad h";

// ── C. contracts ───────────────────────────────────────────────────────────
const SRC_CTR_AT: &str = "def ir_ctr_at (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (n : Nat) : Prop := forall (G : IROutcome -> Prop) (d : IRList Nat) (r : IRList IRFrame), (forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), Q mem2 na2 vs -> ir_safe G m n (ir_ret_to d r mem2 na2 vs)) -> ir_safe G m n (IRConfig.running (E d r))";
const SRC_POST_EXACT: &str = "def ir_post_exact (mX : IRList IRMemSlot) (nX : Nat) (vX : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) : Prop := forall (P : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop), P mX nX vX -> P mem2 na2 vs";
const SRC_POST_EXACT_REFL: &str = "def ir_post_exact_refl (mX : IRList IRMemSlot) (nX : Nat) (vX : IRList IRScalar) : ir_post_exact mX nX vX mX nX vX := fun (P : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (p : P mX nX vX) => p";
const SRC_RET_POST: &str = "def ir_ret_post (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (o : IROutcome) : Prop := IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (vs : IRList IRScalar) => forall (C : Prop), (forall (mem2 : IRList IRMemSlot) (na2 : Nat), Q mem2 na2 vs -> C) -> C) (fun (_ : IRFault) => forall (C : Prop), C) (fun (_ : IRFault) => forall (C : Prop), C) (fun (_ : IRFault) => forall (C : Prop), C) (fun (_ : IRFault) => forall (C : Prop), C) (forall (C : Prop), C) o";
const SRC_CTR_ZERO: &str = "def ir_ctr_zero (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) : ir_ctr_at m E Q Nat.zero := fun (G : IROutcome -> Prop) (d : IRList Nat) (r : IRList IRFrame) (_ : forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), Q mem2 na2 vs -> ir_safe G m Nat.zero (ir_ret_to d r mem2 na2 vs)) => Eq.refl Bool Bool.true";
const SRC_CTR_OF_EXACT: &str = "def ir_ctr_of_exact (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (c : Nat) (mX : IRList IRMemSlot) (nX : Nat) (vX : IRList IRScalar) (hex : forall (d : IRList Nat) (r : IRList IRFrame), Eq IRConfig (ir_steps c m (IRConfig.running (E d r))) (ir_ret_to d r mX nX vX)) (hq : Q mX nX vX) (n : Nat) : ir_ctr_at m E Q n := fun (G : IROutcome -> Prop) (d : IRList Nat) (r : IRList IRFrame) (hK : forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), Q mem2 na2 vs -> ir_safe G m n (ir_ret_to d r mem2 na2 vs)) => ir_safe_pad G m n c (IRConfig.running (E d r)) (Eq.subst IRConfig (fun (k : IRConfig) => ir_safe G m n k) (ir_ret_to d r mX nX vX) (ir_steps c m (IRConfig.running (E d r))) (Eq.symm IRConfig (ir_steps c m (IRConfig.running (E d r))) (ir_ret_to d r mX nX vX) (hex d r)) (hK mX nX vX hq))";
const SRC_CTR_EXACT: &str = "def ir_ctr_exact (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (c : Nat) (mX : IRList IRMemSlot) (nX : Nat) (vX : IRList IRScalar) (hex : forall (d : IRList Nat) (r : IRList IRFrame), Eq IRConfig (ir_steps c m (IRConfig.running (E d r))) (ir_ret_to d r mX nX vX)) (n : Nat) : ir_ctr_at m E (ir_post_exact mX nX vX) n := ir_ctr_of_exact m E (ir_post_exact mX nX vX) c mX nX vX hex (fun (P : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (p : P mX nX vX) => p) n";
const SRC_CTR_WEAKEN: &str = "def ir_ctr_weaken (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (Q2 : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (n : Nat) (hQ : forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), Q mem2 na2 vs -> Q2 mem2 na2 vs) (h : ir_ctr_at m E Q n) : ir_ctr_at m E Q2 n := fun (G : IROutcome -> Prop) (d : IRList Nat) (r : IRList IRFrame) (hK : forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), Q2 mem2 na2 vs -> ir_safe G m n (ir_ret_to d r mem2 na2 vs)) => h G d r (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) (hq : Q mem2 na2 vs) => hK mem2 na2 vs (hQ mem2 na2 vs hq))";
const SRC_CTR_GROUP_SOUND: &str = "def ir_ctr_group_sound (m : IRModule) (A : Type) (P : A -> Type) (E : A -> IRList Nat -> IRList IRFrame -> IRMachine) (Q : A -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (hloc : forall (n : Nat), (forall (a : A), P a -> ir_ctr_at m (E a) (Q a) n) -> forall (a : A), P a -> ir_ctr_at m (E a) (Q a) (Nat.succ n)) (n : Nat) : forall (a : A), P a -> ir_ctr_at m (E a) (Q a) n := Nat.rec (fun (k : Nat) => forall (a : A), P a -> ir_ctr_at m (E a) (Q a) k) (fun (a : A) (_ : P a) => ir_ctr_zero m (E a) (Q a)) (fun (k : Nat) (ih : forall (a : A), P a -> ir_ctr_at m (E a) (Q a) k) => hloc k ih) n";

// ── D. readings: what a contract says about a run ──────────────────────────
const SRC_CTR_RUN: &str = "def ir_ctr_run (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (n : Nat) (hc : ir_ctr_at m E Q n) (G : IROutcome -> Prop) (d : IRList Nat) (hq : forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), Q mem2 na2 vs -> G (IROutcome.ret vs)) : ir_run_ok G (ir_run n m (IRConfig.running (E d (IRList.nil IRFrame)))) := Eq.subst IROutcome (fun (o : IROutcome) => ir_run_ok G o) (ir_config_outcome (ir_steps n m (IRConfig.running (E d (IRList.nil IRFrame))))) (ir_run n m (IRConfig.running (E d (IRList.nil IRFrame)))) (Eq.symm IROutcome (ir_run n m (IRConfig.running (E d (IRList.nil IRFrame)))) (ir_config_outcome (ir_steps n m (IRConfig.running (E d (IRList.nil IRFrame))))) (ir_run_of_steps m n (IRConfig.running (E d (IRList.nil IRFrame))))) (ir_haltok_outcome G (ir_steps n m (IRConfig.running (E d (IRList.nil IRFrame)))) (ir_safe_end G m n (IRConfig.running (E d (IRList.nil IRFrame))) (hc G d (IRList.nil IRFrame) (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) (h : Q mem2 na2 vs) => ir_safe_halted G m (IROutcome.ret vs) n (hq mem2 na2 vs h)))))";
const SRC_CTR_TRI: &str = "def ir_ctr_tri (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (n : Nat) (hc : ir_ctr_at m E Q n) (d : IRList Nat) (k : Nat) (j : Nat) (hk : Eq Nat (Nat.add k j) n) : ir_run_ok (ir_ret_post Q) (ir_config_outcome (ir_steps k m (IRConfig.running (E d (IRList.nil IRFrame))))) := ir_haltok_outcome (ir_ret_post Q) (ir_steps k m (IRConfig.running (E d (IRList.nil IRFrame)))) (ir_safe_at (ir_ret_post Q) m n (IRConfig.running (E d (IRList.nil IRFrame))) (hc (ir_ret_post Q) d (IRList.nil IRFrame) (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) (h : Q mem2 na2 vs) => ir_safe_halted (ir_ret_post Q) m (IROutcome.ret vs) n (fun (C : Prop) (kk : forall (m3 : IRList IRMemSlot) (n3 : Nat), Q m3 n3 vs -> C) => kk mem2 na2 h))) k j hk)";
const SRC_CTR_REFUTES_BAD: &str = "def ir_ctr_refutes_bad (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (c : Nat) (d : IRList Nat) (o : IROutcome) (hrun : Eq IRConfig (ir_steps c m (IRConfig.running (E d (IRList.nil IRFrame)))) (IRConfig.halted o)) (hbad : Eq Bool (ir_bad_halt o) Bool.true) (hc : ir_ctr_at m E Q c) (C : Prop) : C := ir_okhalt_bad C o hbad (Eq.subst IRConfig (fun (k : IRConfig) => ir_haltok (ir_bad_goal C) k) (ir_steps c m (IRConfig.running (E d (IRList.nil IRFrame)))) (IRConfig.halted o) hrun (ir_safe_end (ir_bad_goal C) m c (IRConfig.running (E d (IRList.nil IRFrame))) (hc (ir_bad_goal C) d (IRList.nil IRFrame) (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) (_ : Q mem2 na2 vs) => ir_safe_halted (ir_bad_goal C) m (IROutcome.ret vs) c (Eq.refl Bool Bool.true)))))";

/// The names this stage registers, in registration order.
pub const CTR_NAMES: &[&str] = &[
    "ir_fault_is_assert",
    "ir_sanctioned",
    "ir_bad_halt",
    "ir_sanctioned_assert_failed",
    "ir_sanctioned_unreachable",
    "ir_sanctioned_atomic_arm",
    "ir_bad_halt_atomic_arm",
    "ir_sanctioned_unreachable_arm",
    "ir_bad_halt_unreachable_arm",
    "ir_bad_halt_unreachable",
    "ir_bad_halt_assert_failed",
    "ir_bad_halt_type_error",
    "ir_bad_halt_unmodelled",
    "ir_bad_halt_stuck",
    "ir_bad_halt_ret",
    "ir_bprop",
    "ir_okhalt",
    "ir_haltok",
    "ir_safe",
    "ir_run_ok",
    "ir_safe_zero_running",
    "ir_safe_succ_running",
    "ir_safe_halted",
    "ir_safe_halted_inv",
    "ir_safe_down",
    "ir_safe_down_add",
    "ir_safe_steps",
    "ir_safe_steps_inv",
    "ir_safe_pad",
    "ir_safe_end",
    "ir_safe_at",
    "ir_haltok_outcome",
    "ir_bad_goal",
    "ir_okhalt_bad",
    "ir_ctr_at",
    "ir_post_exact",
    "ir_post_exact_refl",
    "ir_ret_post",
    "ir_ctr_zero",
    "ir_ctr_of_exact",
    "ir_ctr_exact",
    "ir_ctr_weaken",
    "ir_ctr_group_sound",
    "ir_ctr_run",
    "ir_ctr_tri",
    "ir_ctr_refutes_bad",
];

/// `(source, description)`, positionally paired with [`CTR_NAMES`].
const DECLS: &[(&str, &str)] = &[
    (
        SRC_FAULT_IS_ASSERT,
        "ir_fault_is_assert: true at IRFault.assert_failed and false at every other constructor. One IRFault.rec with 24 minors, the 15th true; a 25th constructor makes it fail to elaborate, by name. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SANCTIONED,
        "ir_sanctioned: *** THE SANCTIONED-HALT PREDICATE (D5(b)). *** True exactly at `IROutcome.ub IRFault.assert_failed` -- a Rust panic's failed assert, which is how the producer lowers a diverging panic terminal. False at every other ub fault (unreachable, null_deref, div_zero, ...), at every type_error, unmodelled and stuck outcome, at ret and at fuel_out. A panic is admitted as SAFE; it is not a value, so a contract's functional post never rests on one. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_HALT,
        "ir_bad_halt: the complement a contract refuses -- true at every halt that is neither a return, a sanctioned panic, nor fuel exhaustion: ub with any fault but assert_failed, and every type_error, unmodelled and stuck outcome. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SANCTIONED_ASSERT,
        "ir_sanctioned_assert_failed: vacuity pin -- the one sanctioned outcome, by computation. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SANCTIONED_UNREACHABLE,
        "ir_sanctioned_unreachable: vacuity pin -- reaching an `unreachable` is NOT sanctioned; the switch defaults the producer emits must be shown dead, not admitted. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SANCTIONED_ATOMIC,
        "ir_sanctioned_atomic_arm: the 31st IRInst arm, `atomic_fetch_add_relaxed_u64_seq`, halts `unmodelled width_bounded` in the cell executor at every module, operand and machine -- and that outcome is NOT sanctioned. Eq.refl through ir_exec. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_ATOMIC,
        "ir_bad_halt_atomic_arm: and it is a BAD halt, so no contract admits a run that reaches it (ir_ctr_refutes_bad). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SANCTIONED_UNREACHABLE_ARM,
        "ir_sanctioned_unreachable_arm: the `unreachable` IRInst arm halts `ub unreachable` in the cell executor at every module and machine, and that outcome is NOT sanctioned. It is the image the crystal projector gives an UNDEFINED-BEHAVIOUR halt (decision memo sections 15 and 18: the trust bridge lowers a reached unreachable_unchecked as `assert false`, the panic shape; the projector images the assert its UB obligation sites as `unreachable`), so the sanctioned-panic arm refuses every UB halt of every projected body. Eq.refl through ir_exec. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_UNREACHABLE_ARM,
        "ir_bad_halt_unreachable_arm: and it is a BAD halt, so no contract admits a run that reaches a projected UB halt (ir_ctr_refutes_bad). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_UNREACHABLE,
        "ir_bad_halt_unreachable: vacuity pin, by computation. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_ASSERT,
        "ir_bad_halt_assert_failed: vacuity pin -- the sanctioned panic is not bad. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_TYPE_ERROR,
        "ir_bad_halt_type_error: every type_error is bad, at every fault. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_UNMODELLED,
        "ir_bad_halt_unmodelled: every unmodelled outcome is bad, at every fault. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_STUCK,
        "ir_bad_halt_stuck: every stuck outcome is bad, at every fault. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_RET,
        "ir_bad_halt_ret: a return is never bad. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BPROP,
        "ir_bprop: `if b then Q else P` at the level of propositions -- a Bool.rec into Prop behind a constant, so it may stand in a BINDER TYPE: a bare recursor application there has type `(fun _ => Prop) b`, which the elaborator refuses as not a sort (measured). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_OKHALT,
        "ir_okhalt: a halt outcome is acceptable to G -- true outright at a sanctioned panic, otherwise G o. The disjunction is a Bool.rec into Prop on ir_sanctioned, so the stage names no Or. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_HALTOK,
        "ir_haltok: a configuration is acceptable -- a running one always, a halted one when ir_okhalt accepts its outcome. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE,
        "ir_safe: *** STEP-INDEXED SAFETY. *** `ir_safe G m n c` holds when, for every k <= n, the configuration k steps from c is running, halted with a sanctioned panic, or halted with an outcome G accepts. Nat.rec on the budget generalised over the configuration -- the shape of ir_steps and ir_stk_clear: at budget 0 it is ir_haltok; at succ n a running machine asks it of its successor at n, a halted one asks ir_okhalt (a halted configuration is a fixed point of the machine, so nothing later can differ). The downward closure is a lemma (ir_safe_down), not built in. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_RUN_OK,
        "ir_run_ok: the outcome reading of ir_haltok -- fuel_out (the run is still going) always, every other outcome when ir_okhalt accepts it. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_ZERO_RUNNING,
        "ir_safe_zero_running: vacuity pin -- budget zero asks nothing of a running configuration, by computation. The base case of every contract. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_SUCC_RUNNING,
        "ir_safe_succ_running: vacuity pin -- safety at succ n of a running machine IS safety at n of its successor, by computation (the proof is the hypothesis). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_HALTED,
        "ir_safe_halted: HALTED IS ABSORBING -- an acceptable halt is safe at every budget. Nat.rec, both arms the hypothesis. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_HALTED_INV,
        "ir_safe_halted_inv: and conversely, safety of a halted configuration at any budget is acceptance of its outcome. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_DOWN,
        "ir_safe_down: *** DOWNWARD CLOSURE. *** Safe at succ n implies safe at n. Nat.rec on n over the configuration: at the bottom a running configuration is trivially acceptable; above it the running arm is the induction hypothesis at the successor and the halted arm is the hypothesis itself. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_DOWN_ADD,
        "ir_safe_down_add: safe at n + a implies safe at n -- ir_safe_down a times, Nat.rec on a. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_STEPS,
        "ir_safe_steps: *** COMPOSE (join). *** If the configuration a steps on is safe for b steps, the start is safe for b + a -- for EVERY run, not only a running one: a run that halts inside the a steps halts with the same outcome ir_steps reports at a (halted is absorbing), so its acceptance is the same fact. Nat.rec on a; the halted arm moves acceptance across budgets with ir_safe_halted / ir_safe_halted_inv. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_STEPS_INV,
        "ir_safe_steps_inv: *** STEP BACK (split). *** Safe for b + a implies the configuration a steps on is safe for b. With ir_safe_steps this is the equivalence safe(b + a, c) <-> safe(b, steps a c). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_PAD,
        "ir_safe_pad: an exact run of a steps is FREE -- safety at n of where it lands gives safety at n of where it starts. ir_safe_steps then ir_safe_down_add. This is how a local obligation spends budget only on the steps it cannot compute: every literal run and every exact callee pads, and only the one step that separates a body's budget succ n from its callees' n is paid. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_END,
        "ir_safe_end: the endpoint reading -- safe for n steps implies the configuration after exactly n steps is acceptable. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SAFE_AT,
        "ir_safe_at: the `every k <= n` reading, with the slack explicit: for k + j = n, the configuration after k steps is acceptable. ir_safe_down_add at j then ir_safe_end at k. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_HALTOK_OUTCOME,
        "ir_haltok_outcome: an acceptable configuration has an acceptable outcome reading -- a running one reads fuel_out. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_BAD_GOAL,
        "ir_bad_goal: the refutation acceptor -- a bad halt must prove C, every other outcome is accepted. Used to show a contract cannot hold at a run that halts badly. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_OKHALT_BAD,
        "ir_okhalt_bad: a bad halt accepted by ir_bad_goal C yields C -- IROutcome.rec, and for ub a Bool.rec on ir_fault_is_assert (the assert case contradicts badness, every other fault yields C). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_AT,
        "ir_ctr_at: *** THE STEP-INDEXED CONTRACT (D5(a)/(b)). *** For every acceptor G, every caller -- dests d and caller stack r -- if the caller's continuation from EVERY post-satisfying return `ir_ret_to d r mem2 na2 vs` is safe for n steps, then the callee entered at `E d r` is safe for n steps. The post is attached to the POST-RETURN configuration for every caller, the shape of ir_it_ag_activation's hc1/hc2 and the ir_lzd segments' ih1/ih2; the SAFETY conjunct is carried by ir_safe (running, sanctioned panic, or accepted halt, at every k <= n); and returning is the only way to reach G's non-panic halts from inside the callee, which is why the continuation form needs no `inside the callee` predicate. At the empty caller stack it reads as the three-way statement (ir_ctr_tri). Partial correctness: nothing here says the callee returns. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_POST_EXACT,
        "ir_post_exact: the post of an EXACT callee -- Leibniz equality of (heap, counter, values) with a fixed triple, so its eliminator is a substitution and no And is needed. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_POST_EXACT_REFL,
        "ir_post_exact_refl: vacuity pin -- the exact post holds at its own triple. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_RET_POST,
        "ir_ret_post: the acceptor that reads a return as `some final heap and counter satisfy Q` (Church-encoded existential) and refuses every other halt. Its ir_run_ok is the three-way reading. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_ZERO,
        "ir_ctr_zero: every contract holds at budget ZERO, because every entry is a running machine. The base case of ir_ctr_group_sound -- which is why E is machine-valued. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_OF_EXACT,
        "ir_ctr_of_exact: *** THE ADAPTER. *** An EXACT run in the hc1 shape -- for every caller, c steps from the entry reach ir_ret_to d r mX nX vX -- whose final triple satisfies Q meets the step-indexed contract at EVERY budget. ir_safe_pad over the exact run, then the continuation hypothesis at the final triple. This is how an exact callee (ir_lzd_deref_activation, the activation leaves, any hc1/hc2 premise) enters an assume-guarantee proof without a step index of its own. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_EXACT,
        "ir_ctr_exact: the adapter at the exact post ir_post_exact -- the strongest contract an exact run gives. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_WEAKEN,
        "ir_ctr_weaken: the consequence rule -- a contract with a stronger post meets any weaker post at the same budget. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_GROUP_SOUND,
        "ir_ctr_group_sound: *** CONTRACT-TABLE SOUNDNESS. *** A recursion group is a table indexed by A (function id and inputs), with a precondition P, an entry machine E and a post Q per index. If every body meets its LOCAL OBLIGATION -- its contract at succ n, assuming every contract of the group at the strictly smaller budget n -- then every contract in the table holds at EVERY budget. Plain Nat.rec on the budget with the motive `forall a, P a -> ir_ctr_at ..`: the base is ir_ctr_zero, the step is the local obligation. No strong induction: the downward closure a local obligation needs is ir_safe's (ir_safe_pad), so the obligation consumes its callees at exactly n. Callees OUTSIDE the group enter the local obligation as ordinary facts (ir_ctr_of_exact for an exact one). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_RUN,
        "ir_ctr_run: *** THE OUTCOME READING. *** A contract at budget n, entered at the EMPTY caller stack (the top level, where a return halts), gives ir_run_ok G for the n-step run, for any acceptor G that accepts every post-satisfying return: the outcome is fuel_out, a sanctioned panic, or a G-accepted halt. ir_run_of_steps, ir_safe_end, ir_haltok_outcome. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_TRI,
        "ir_ctr_tri: *** THE THREE-WAY STATEMENT OF D5(b). *** From a contract at n, for every k with k + j = n -- every k <= n -- the run from the entry at the empty caller stack, after k steps, is running (fuel_out), has halted with a sanctioned panic, or has returned values vs for which SOME final heap and counter satisfy the post; every other halt is refused. ir_safe_at at the acceptor ir_ret_post. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_REFUTES_BAD,
        "ir_ctr_refutes_bad: *** THE CONTRACT IS NOT VACUOUS. *** If the run from the entry at the empty caller stack halts BADLY within c steps -- ub other than assert_failed, type_error, unmodelled or stuck -- then the entry meets NO contract at budget c, whatever its post: instantiate the contract at ir_bad_goal C, whose continuation obligation at a return is trivial. DerivedProved, zero axiom_deps.",
    ),
];

impl Specification {
    /// The step-indexed contract device. MUST follow `add_eval_ir_steps`
    /// (`ir_steps`, `ir_run_of_steps`, `ir_config_outcome`) and
    /// `add_eval_ir_lzd_fresh` (`ir_bool_false_ne_true`); placed after
    /// `add_eval_ir_stack_split`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_ctr(&mut self) -> Result<(), SpecError> {
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
        assert_eq!(DECLS.len(), CTR_NAMES.len());
        for ((src, _), name) in DECLS.iter().zip(CTR_NAMES) {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
        }
    }

    /// The classifier's recursor must have one minor per IRFault constructor
    /// (24) and exactly one `true`, in the `assert_failed` position (15th).
    #[test]
    fn test_fault_classifier_has_one_true_minor_at_assert_failed() {
        let minors: Vec<&str> = SRC_FAULT_IS_ASSERT
            .split_whitespace()
            .filter(|w| *w == "Bool.true" || *w == "Bool.false")
            .collect();
        assert_eq!(minors.len(), 24);
        assert_eq!(
            minors.iter().position(|w| *w == "Bool.true"),
            Some(14),
            "assert_failed is the 15th IRFault constructor"
        );
        assert_eq!(minors.iter().filter(|w| **w == "Bool.true").count(), 1);
    }
}
