// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Prerequisites for the budget induction behind `stuck_head_star_preserved`.
//!
//! Two independent pieces, landed together because the induction needs both.
//!
//! ## 1. A strictly decreasing budget measure
//!
//! `whnf_fuel_red_wh3_result_stuck_lt` upgrades the existing result-stuck lemma
//! to carry `Lt j n`. The strictness is load-bearing and is *not* bookkeeping
//! luck: `wh3_stuck_at` is indexed by the **pre-pass** budget, while the loop at
//! fuel `succ k` evaluates its step against the pre-pass at `k`. There is
//! therefore no execution that returns a result at budget `n` while being stuck
//! only at `n` itself. Had the bound been `Le`, the budget induction would not
//! terminate and this route would be dead.
//!
//! ## 2. A `wstuck` inverter for the iota chain
//!
//! The chain has seven binds; a `wstuck` verdict can arise at six of them.
//! **Level 4 is impossible**, and that is a theorem rather than a convention:
//! level 4 passes `wstarved` as its failure branch, and `wstuck` is not
//! `wstarved`. The arm is discharged constructively by `wh_stuck_ne_starved`.
//!
//! The inverter does **not** make `wstuck` budget-independent. Levels 1-3
//! mention neither `wh` nor `wmajor`, so those are; levels 5-7 read the head,
//! rule and guarded tail after the pre-pass *result*, so those are not. Thus
//! `k5`, `k6` and `ktail` hand back `wh major = some wmajor` instead of hiding it
//! inside the proof term.
//!
//! Registered last, after `add_stuck_major_confluence`, so that every
//! dependency -- `hnf_discharge3`, `wh3_stuck_head` and the `whc3` chain -- is
//! already in scope regardless of how the earlier stages are reordered.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `(source, description)` for each prerequisite, in dependency order.
const DECLS: [(&str, &str); 9] = [
    (
        "def whnf_fuel_red_wh3_result_stuck_lt (n : Nat) (e : KExpr) (r : KExpr) (C : Type) : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n e) (@OptionType.some KExpr r) -> (forall (j : Nat), Lt j n -> wh3_stuck_at j r -> C) -> C := @Nat.rec (fun (m : Nat) => forall (e0 : KExpr) (r0 : KExpr), @Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env m e0) (@OptionType.some KExpr r0) -> (forall (j : Nat), Lt j m -> wh3_stuck_at j r0 -> C) -> C) (fun (e0 : KExpr) (r0 : KExpr) (h : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env Nat.zero e0) (@OptionType.some KExpr r0)) (_kk : forall (j : Nat), Lt j Nat.zero -> wh3_stuck_at j r0 -> C) => option_none_ne_some_type KExpr r0 C h) (fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), @Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env k e0) (@OptionType.some KExpr r0) -> (forall (j : Nat), Lt j k -> wh3_stuck_at j r0 -> C) -> C) (e0 : KExpr) (r0 : KExpr) (h : @Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env (Nat.succ k) e0) (@OptionType.some KExpr r0)) (kk : (forall (j : Nat), Lt j (Nat.succ k) -> wh3_stuck_at j r0 -> C)) => @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e0) o -> @Eq (OptionType KExpr) (wh_dispatch3 o e0 (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (@OptionType.some KExpr r0) -> C) (fun (hq : @Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e0) WhStepR.wstuck) (h2 : @Eq (OptionType KExpr) (wh_dispatch3 WhStepR.wstuck e0 (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (@OptionType.some KExpr r0)) => kk k (lt_succ_self k) (Eq.subst KExpr (fun (zz : KExpr) => wh3_stuck_at k zz) e0 r0 (option_some_inj KExpr e0 r0 h2) hq)) (fun (_hq : @Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e0) WhStepR.wstarved) (h2 : @Eq (OptionType KExpr) (wh_dispatch3 WhStepR.wstarved e0 (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (@OptionType.some KExpr r0)) => option_none_ne_some_type KExpr r0 C h2) (fun (e2 : KExpr) (_hq : @Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e0) (WhStepR.wstep e2)) (h2 : @Eq (OptionType KExpr) (wh_dispatch3 (WhStepR.wstep e2) e0 (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (@OptionType.some KExpr r0)) => ih e2 r0 h2 (fun (j : Nat) (hj : Lt j k) (hs : wh3_stuck_at j r0) => kk j (lt_succ_weaken j k hj) hs)) (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e0) (@Eq.refl WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e0)) h) n e r",
        "whnf_fuel_red_wh3_result_stuck_lt: the three-way loop returning a result at budget n exhibits a STRICTLY SMALLER budget j < n at which the result is stuck. The strictness is the whole point and it is not an accident of bookkeeping: wh3_stuck_at is indexed by the PRE-PASS budget, while the loop at fuel (succ k) evaluates its step against the pre-pass at k. So the loop never evaluates its step with pre-pass n at fuel n, and the wstuck arm hands back Lt k (succ k) honestly. The wstep arm inherits Lt j k from the induction hypothesis and weakens. The base case returns none, so the strict bound is never demanded over an empty range. This is the descent measure the budget induction for stuck_head_star_preserved runs on; had it been only Le, that induction would not terminate and the route would be sunk. Delivers ONE j < n, not all j < n -- wh3_stuck_at is not known to be budget-monotone -- which is exactly the shape nat_strong_rec's step consumes. DerivedProved, zero axiom_deps.",
    ),
    (
        "def reduce_app_head_wh3_stuck_forces_iota_stuck (k : Nat) (za : KExpr) (zf : KExpr) : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za zf WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app zf za)) WhStepR.wstuck := @KExpr.rec (fun (y : KExpr) => @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za y WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app y za)) WhStepR.wstuck) (fun (sl : Level) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.sort sl) WhStepR.wstuck) WhStepR.wstuck) => h) (fun (bi : Nat) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.bvar bi) WhStepR.wstuck) WhStepR.wstuck) => h) (fun (af : KExpr) (aa : KExpr) (_ihaf : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za af WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app af za)) WhStepR.wstuck) (_ihaa : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za aa WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app aa za)) WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.app af aa) WhStepR.wstuck) WhStepR.wstuck) => h) (fun (lty : KExpr) (lb : KExpr) (_ihlty : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za lty WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app lty za)) WhStepR.wstuck) (_ihlb : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za lb WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app lb za)) WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.lam lty lb) WhStepR.wstuck) WhStepR.wstuck) => wh_stuck_ne_step (instantiate lb za) (@Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app (KExpr.lam lty lb) za)) WhStepR.wstuck) (Eq.symm WhStepR (WhStepR.wstep (instantiate lb za)) WhStepR.wstuck h)) (fun (pty : KExpr) (pb : KExpr) (_ihpty : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za pty WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app pty za)) WhStepR.wstuck) (_ihpb : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za pb WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app pb za)) WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.pi pty pb) WhStepR.wstuck) WhStepR.wstuck) => h) (fun (cn : Name) (cus : ListType Level) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.const cn cus) WhStepR.wstuck) WhStepR.wstuck) => h) (fun (zty : KExpr) (zv : KExpr) (zb : KExpr) (_ihzty : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za zty WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app zty za)) WhStepR.wstuck) (_ihzv : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za zv WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app zv za)) WhStepR.wstuck) (_ihzb : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za zb WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app zb za)) WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.let_ zty zv zb) WhStepR.wstuck) WhStepR.wstuck) => h) (fun (psn : Name) (pix : Nat) (psub : KExpr) (_ihpsub : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za psub WhStepR.wstuck) WhStepR.wstuck -> @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app psub za)) WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.proj psn pix psub) WhStepR.wstuck) WhStepR.wstuck) => h) (fun (lv : Nat) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za (KExpr.lit lv) WhStepR.wstuck) WhStepR.wstuck) => h) zf",
        "reduce_app_head_wh3_stuck_forces_iota_stuck: if the three-way app-head reducer reports wstuck, the iota chain at the applied spine reports wstuck. Proved by the nine-arm KExpr.rec on the head. Eight arms are the identity -- the hypothesis IS the goal, by iota on WhStepR.rec at a literal wstuck -- because every non-lam head routes through opt_app_ilift3, whose only wstuck-producing arm has the iota chain as its value. The lam arm dies by wh_stuck_ne_step, since a lam head beta-steps and cannot be stuck. DerivedProved, zero axiom_deps.",
    ),
    (
        "def wh3_stuck_app_forces_iota_stuck (k : Nat) (zf : KExpr) (za : KExpr) (hs : wh3_stuck_at k (KExpr.app zf za)) : @Eq WhStepR (iota_reduct_whc3 (red_rec the_red_env) (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app zf za)) WhStepR.wstuck := reduce_app_head_wh3_stuck_forces_iota_stuck k za zf (Eq.subst WhStepR (fun (o : WhStepR) => @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) za zf o) WhStepR.wstuck) (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) zf) WhStepR.wstuck (wh3_stuck_app_fn_stuck k zf za hs) hs)",
        "wh3_stuck_app_forces_iota_stuck: a stuck three-way step at an application forces the iota chain to be stuck at that application. Gets the head's stuckness from wh3_stuck_app_fn_stuck, transports the stuckness equation along it, and feeds reduce_app_head_wh3_stuck_forces_iota_stuck. Splitting the Eq.subst out of the nine-arm recursion keeps eight of those nine arms literally the identity. DerivedProved, zero axiom_deps.",
    ),
    (
        "def opt_step_bind_stuck_inv_type (A : Type) (o : OptionType A) (d : WhStepR) (f : A -> WhStepR) (C : Type) (h : @Eq WhStepR (opt_step_bind A o d f) WhStepR.wstuck) (kn : (@Eq (OptionType A) o (@OptionType.none A) -> @Eq WhStepR d WhStepR.wstuck -> C)) (ks : (forall (w : A), @Eq (OptionType A) o (@OptionType.some A w) -> @Eq WhStepR (f w) WhStepR.wstuck -> C)) : C := @OptionType.rec A (fun (o0 : OptionType A) => @Eq WhStepR (opt_step_bind A o0 d f) WhStepR.wstuck -> (@Eq (OptionType A) o0 (@OptionType.none A) -> @Eq WhStepR d WhStepR.wstuck -> C) -> (forall (w : A), @Eq (OptionType A) o0 (@OptionType.some A w) -> @Eq WhStepR (f w) WhStepR.wstuck -> C) -> C) (fun (h0 : @Eq WhStepR (opt_step_bind A (@OptionType.none A) d f) WhStepR.wstuck) (kn0 : @Eq (OptionType A) (@OptionType.none A) (@OptionType.none A) -> @Eq WhStepR d WhStepR.wstuck -> C) (_ks0 : (forall (w : A), @Eq (OptionType A) (@OptionType.none A) (@OptionType.some A w) -> @Eq WhStepR (f w) WhStepR.wstuck -> C)) => kn0 (@Eq.refl (OptionType A) (@OptionType.none A)) h0) (fun (w : A) (h0 : @Eq WhStepR (opt_step_bind A (@OptionType.some A w) d f) WhStepR.wstuck) (_kn0 : @Eq (OptionType A) (@OptionType.some A w) (@OptionType.none A) -> @Eq WhStepR d WhStepR.wstuck -> C) (ks0 : (forall (w0 : A), @Eq (OptionType A) (@OptionType.some A w) (@OptionType.some A w0) -> @Eq WhStepR (f w0) WhStepR.wstuck -> C)) => ks0 w (@Eq.refl (OptionType A) (@OptionType.some A w)) h0) o h kn ks",
        "opt_step_bind_stuck_inv_type: inverting a wstuck verdict through one opt_step_bind layer, Type-motive variant. Two continuations, not one: for a wstuck verdict the none arm is the INFORMATIVE branch, not a nuisance to refute. Critically the recursor motive abstracts the scrutinee into an equation, so the none arm proves o0 = none and names WHICH level declined; without that the arm would prove only that something declined and the entire content the caller wants would be lost. That is why this could not be copied from opt_step_bind_some_inv, whose motive does not carry the equation. DerivedProved, zero axiom_deps.",
    ),
    (
        "def opt_step_bind_stuck_inv (A : Type) (o : OptionType A) (d : WhStepR) (f : A -> WhStepR) (C : Prop) (h : @Eq WhStepR (opt_step_bind A o d f) WhStepR.wstuck) (kn : (@Eq (OptionType A) o (@OptionType.none A) -> @Eq WhStepR d WhStepR.wstuck -> C)) (ks : (forall (w : A), @Eq (OptionType A) o (@OptionType.some A w) -> @Eq WhStepR (f w) WhStepR.wstuck -> C)) : C := @OptionType.rec A (fun (o0 : OptionType A) => @Eq WhStepR (opt_step_bind A o0 d f) WhStepR.wstuck -> (@Eq (OptionType A) o0 (@OptionType.none A) -> @Eq WhStepR d WhStepR.wstuck -> C) -> (forall (w : A), @Eq (OptionType A) o0 (@OptionType.some A w) -> @Eq WhStepR (f w) WhStepR.wstuck -> C) -> C) (fun (h0 : @Eq WhStepR (opt_step_bind A (@OptionType.none A) d f) WhStepR.wstuck) (kn0 : @Eq (OptionType A) (@OptionType.none A) (@OptionType.none A) -> @Eq WhStepR d WhStepR.wstuck -> C) (_ks0 : (forall (w : A), @Eq (OptionType A) (@OptionType.none A) (@OptionType.some A w) -> @Eq WhStepR (f w) WhStepR.wstuck -> C)) => kn0 (@Eq.refl (OptionType A) (@OptionType.none A)) h0) (fun (w : A) (h0 : @Eq WhStepR (opt_step_bind A (@OptionType.some A w) d f) WhStepR.wstuck) (_kn0 : @Eq (OptionType A) (@OptionType.some A w) (@OptionType.none A) -> @Eq WhStepR d WhStepR.wstuck -> C) (ks0 : (forall (w0 : A), @Eq (OptionType A) (@OptionType.some A w) (@OptionType.some A w0) -> @Eq WhStepR (f w0) WhStepR.wstuck -> C)) => ks0 w (@Eq.refl (OptionType A) (@OptionType.some A w)) h0) o h kn ks",
        "opt_step_bind_stuck_inv: as opt_step_bind_stuck_inv_type, with a Prop motive. The kernel is non-cumulative, so the two motive universes need separate declarations. DerivedProved, zero axiom_deps.",
    ),
    (
        r"def iota_reduct_whc3_stuck_inv_type (env : RecEnv)
 (wh : KExpr -> OptionType KExpr) (e : KExpr) (C : Type)
 (h : @Eq WhStepR (iota_reduct_whc3 env wh e) WhStepR.wstuck)
 (k1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name) -> C)
 (k2 : forall (recname : Name), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.none RecMeta) -> C)
 (k3 : forall (recname : Name) (meta : RecMeta), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.none KExpr) -> C)
 (k5 : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.none Name) -> C)
 (k6 : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname) -> @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.none RecRule) -> C)
 (ktail : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname) -> @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule) -> @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.none KExpr) -> C) : C :=
 opt_step_bind_stuck_inv_type Name (kexpr_const_name (kapp_fn e)) WhStepR.wstuck (fun (recname : Name) => opt_step_bind RecMeta (recmeta_for env recname) WhStepR.wstuck (fun (meta : RecMeta) => opt_step_bind KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))))))) C h
 (fun (hn : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k1   hn)
 (fun (recname : Name) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname))
  (h1r : @Eq WhStepR ((fun (recname : Name) => opt_step_bind RecMeta (recmeta_for env recname) WhStepR.wstuck (fun (meta : RecMeta) => opt_step_bind KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))))))) recname) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv_type RecMeta (recmeta_for env recname) WhStepR.wstuck (fun (meta : RecMeta) => opt_step_bind KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)))))) C h1r
 (fun (hn : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.none RecMeta)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k2 recname h1 hn)
 (fun (meta : RecMeta) (h2 : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta))
  (h2r : @Eq WhStepR ((fun (meta : RecMeta) => opt_step_bind KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)))))) meta) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv_type KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))))) C h2r
 (fun (hn : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.none KExpr)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k3 recname meta h1 h2 hn)
 (fun (major : KExpr) (h3 : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major))
  (h3r : @Eq WhStepR ((fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))))) major) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv_type KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)))) C h3r
 (fun (_none : @Eq (OptionType KExpr) (wh major) (@OptionType.none KExpr)) (bad : @Eq WhStepR WhStepR.wstarved WhStepR.wstuck) =>
   wh_stuck_ne_starved_type C (Eq.symm WhStepR WhStepR.wstarved WhStepR.wstuck bad))
 (fun (wmajor : KExpr) (hw : @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor))
  (h4r : @Eq WhStepR ((fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)))) wmajor) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv_type Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))) C h4r
 (fun (hn : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.none Name)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k5 recname meta major wmajor h1 h2 h3 hw hn)
 (fun (cname : Name) (h4 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname))
  (h5r : @Eq WhStepR ((fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))) cname) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv_type RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)) C h5r
 (fun (hn : @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.none RecRule)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k6 recname meta major wmajor cname h1 h2 h3 hw h4 hn)
 (fun (rule : RecRule) (h5 : @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule))
  (h6r : @Eq WhStepR ((fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)) rule) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv_type KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result) C h6r
 (fun (hn : @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.none KExpr)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   ktail recname meta major wmajor cname rule h1 h2 h3 hw h4 h5 hn)
 (fun (result : KExpr) (htail : @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.some KExpr result))
  (h7r : @Eq WhStepR ((fun (result : KExpr) => WhStepR.wstep result) result) WhStepR.wstuck) =>
 wh_stuck_ne_step_type result C
  (Eq.symm WhStepR (WhStepR.wstep result) WhStepR.wstuck h7r))))))))",
        "iota_reduct_whc3_stuck_inv_type: the SIX-WAY inversion of an actual wstuck verdict. There is deliberately NO k4 continuation: the pre-pass defaults to wstarved, constructively distinct from wstuck. Each continuation preserves preceding lookup equations. The new ktail case retains all six successful outer lookups and actual iota_contractum_at = none; successful rule lookup alone no longer forces a step. Levels 5-7 retain the pre-pass result explicitly. This view does not establish budget independence or eliminate the monotonicity obligation for that result. DerivedProved, zero axiom_deps.",
    ),
    (
        r"def iota_reduct_whc3_stuck_inv (env : RecEnv)
 (wh : KExpr -> OptionType KExpr) (e : KExpr) (C : Prop)
 (h : @Eq WhStepR (iota_reduct_whc3 env wh e) WhStepR.wstuck)
 (k1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name) -> C)
 (k2 : forall (recname : Name), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.none RecMeta) -> C)
 (k3 : forall (recname : Name) (meta : RecMeta), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.none KExpr) -> C)
 (k5 : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.none Name) -> C)
 (k6 : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname) -> @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.none RecRule) -> C)
 (ktail : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname) -> @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule) -> @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.none KExpr) -> C) : C :=
 opt_step_bind_stuck_inv Name (kexpr_const_name (kapp_fn e)) WhStepR.wstuck (fun (recname : Name) => opt_step_bind RecMeta (recmeta_for env recname) WhStepR.wstuck (fun (meta : RecMeta) => opt_step_bind KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))))))) C h
 (fun (hn : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k1   hn)
 (fun (recname : Name) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname))
  (h1r : @Eq WhStepR ((fun (recname : Name) => opt_step_bind RecMeta (recmeta_for env recname) WhStepR.wstuck (fun (meta : RecMeta) => opt_step_bind KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))))))) recname) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv RecMeta (recmeta_for env recname) WhStepR.wstuck (fun (meta : RecMeta) => opt_step_bind KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)))))) C h1r
 (fun (hn : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.none RecMeta)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k2 recname h1 hn)
 (fun (meta : RecMeta) (h2 : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta))
  (h2r : @Eq WhStepR ((fun (meta : RecMeta) => opt_step_bind KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)))))) meta) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) WhStepR.wstuck (fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))))) C h2r
 (fun (hn : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.none KExpr)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k3 recname meta h1 h2 hn)
 (fun (major : KExpr) (h3 : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major))
  (h3r : @Eq WhStepR ((fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))))) major) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv KExpr (wh major) WhStepR.wstarved (fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)))) C h3r
 (fun (_none : @Eq (OptionType KExpr) (wh major) (@OptionType.none KExpr)) (bad : @Eq WhStepR WhStepR.wstarved WhStepR.wstuck) =>
   wh_stuck_ne_starved C (Eq.symm WhStepR WhStepR.wstarved WhStepR.wstuck bad))
 (fun (wmajor : KExpr) (hw : @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor))
  (h4r : @Eq WhStepR ((fun (wmajor : KExpr) => opt_step_bind Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)))) wmajor) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck (fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))) C h4r
 (fun (hn : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.none Name)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k5 recname meta major wmajor h1 h2 h3 hw hn)
 (fun (cname : Name) (h4 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname))
  (h5r : @Eq WhStepR ((fun (cname : Name) => opt_step_bind RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result))) cname) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv RecRule (recrule_for env recname cname) WhStepR.wstuck (fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)) C h5r
 (fun (hn : @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.none RecRule)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   k6 recname meta major wmajor cname h1 h2 h3 hw h4 hn)
 (fun (rule : RecRule) (h5 : @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule))
  (h6r : @Eq WhStepR ((fun (rule : RecRule) => opt_step_bind KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result)) rule) WhStepR.wstuck) =>
 opt_step_bind_stuck_inv KExpr (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) WhStepR.wstuck (fun (result : KExpr) => WhStepR.wstep result) C h6r
 (fun (hn : @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.none KExpr)) (_stuck : @Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>
   ktail recname meta major wmajor cname rule h1 h2 h3 hw h4 h5 hn)
 (fun (result : KExpr) (htail : @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.some KExpr result))
  (h7r : @Eq WhStepR ((fun (result : KExpr) => WhStepR.wstep result) result) WhStepR.wstuck) =>
 wh_stuck_ne_step result C
  (Eq.symm WhStepR (WhStepR.wstep result) WhStepR.wstuck h7r))))))))",
        "iota_reduct_whc3_stuck_inv: as iota_reduct_whc3_stuck_inv_type, with a Prop motive. DerivedProved, zero axiom_deps.",
    ),
    (
        r"def iota_reduct_whc3_stuck_late_inv_type (env : RecEnv)
 (wh : KExpr -> OptionType KExpr) (e : KExpr) (C : Type)
 (h : @Eq WhStepR (iota_reduct_whc3 env wh e) WhStepR.wstuck)
 (kearly : C)
 (kcname : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.none Name) -> C)
 (krule : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname) -> @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.none RecRule) -> C)
 (ktail : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname) -> @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule) -> @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.none KExpr) -> C) : C :=
 iota_reduct_whc3_stuck_inv_type env wh e C h
  (fun (hn : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name)) => kearly)
  (fun (recname : Name) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (hn : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.none RecMeta)) => kearly)
  (fun (recname : Name) (meta : RecMeta) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (h2 : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta)) (hn : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.none KExpr)) => kearly)
  kcname krule ktail",
        "iota_reduct_whc3_stuck_late_inv_type: the LATE-LEVEL collapse of the six-way inversion -- levels 1-3 fold into one kearly continuation, leaving the name, rule and guarded-tail levels separate. Derived by INSTANTIATION ONLY from the six-way form, so it cannot typecheck around a gap. The split is by kind, not depth: levels 1-3 are facts about the term's own shape, levels 5-7 are facts about the pre-pass result, and consumers branch on that distinction. DerivedProved, zero axiom_deps.",
    ),
    (
        r"def iota_reduct_whc3_stuck_late_inv (env : RecEnv)
 (wh : KExpr -> OptionType KExpr) (e : KExpr) (C : Prop)
 (h : @Eq WhStepR (iota_reduct_whc3 env wh e) WhStepR.wstuck)
 (kearly : C)
 (kcname : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.none Name) -> C)
 (krule : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname) -> @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.none RecRule) -> C)
 (ktail : forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule), @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname) -> @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta) -> @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major) -> @Eq (OptionType KExpr) (wh major) (@OptionType.some KExpr wmajor) -> @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname) -> @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule) -> @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.none KExpr) -> C) : C :=
 iota_reduct_whc3_stuck_inv env wh e C h
  (fun (hn : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name)) => kearly)
  (fun (recname : Name) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (hn : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.none RecMeta)) => kearly)
  (fun (recname : Name) (meta : RecMeta) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (h2 : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta meta)) (hn : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.none KExpr)) => kearly)
  kcname krule ktail",
        "iota_reduct_whc3_stuck_late_inv: as iota_reduct_whc3_stuck_late_inv_type, with a Prop motive. DerivedProved, zero axiom_deps.",
    ),
];

impl Specification {
    /// The strict budget measure and the `wstuck` inverter.
    pub(super) fn add_budget_induction_prereqs(&mut self) -> Result<(), SpecError> {
        for (src, desc) in DECLS {
            self.add_recursive_def(src, desc)?;
        }
        Ok(())
    }
}

// Finite operational fixtures; these are not admitted or faithful environments.
const GUARD_CONTROLS: &[&str] = &[
    r"def prepass_tail_fixture_env : RecEnv :=
 RecEnv.addRec RecEnv.empty Name.anonymous iota_tail_fixture_meta
  (RecRules.cons iota_tail_fixture_rule RecRules.nil)",
    r"def prepass_tail_fixture_major : KExpr :=
 apply_spine iota_tail_fixture_fields (KExpr.const Name.anonymous (@ListType.nil Level))",
    r"def prepass_tail_fixture_term (us : ListType Level) (major : KExpr) : KExpr :=
 KExpr.app
  (KExpr.app
    (KExpr.app (KExpr.const Name.anonymous us) (KExpr.sort Level.zero)) major)
  (KExpr.sort (Level.succ (Level.succ Level.zero)))",
    r"def prepass_tail_fixture_identity (e : KExpr) : OptionType KExpr :=
 @OptionType.some KExpr e",
    r"def prepass_tail_fixture_whc_accepts : @Eq (OptionType KExpr)
 (iota_reduct_whc prepass_tail_fixture_env prepass_tail_fixture_identity (prepass_tail_fixture_term (@ListType.cons Level iota_tail_fixture_level (@ListType.nil Level)) prepass_tail_fixture_major)) (@OptionType.some KExpr iota_tail_fixture_result) :=
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr iota_tail_fixture_result)",
    r"def prepass_tail_fixture_whc3_accepts : @Eq WhStepR
 (iota_reduct_whc3 prepass_tail_fixture_env prepass_tail_fixture_identity (prepass_tail_fixture_term (@ListType.cons Level iota_tail_fixture_level (@ListType.nil Level)) prepass_tail_fixture_major)) (WhStepR.wstep iota_tail_fixture_result) :=
 @Eq.refl WhStepR (WhStepR.wstep iota_tail_fixture_result)",
    r"def prepass_tail_fixture_missing_universe_stuck : @Eq WhStepR
 (iota_reduct_whc3 prepass_tail_fixture_env prepass_tail_fixture_identity (prepass_tail_fixture_term (@ListType.nil Level) prepass_tail_fixture_major)) WhStepR.wstuck := @Eq.refl WhStepR WhStepR.wstuck",
    r"def prepass_tail_fixture_extra_universe_stuck : @Eq WhStepR
 (iota_reduct_whc3 prepass_tail_fixture_env prepass_tail_fixture_identity (prepass_tail_fixture_term (@ListType.cons Level iota_tail_fixture_level (@ListType.cons Level Level.zero (@ListType.nil Level))) prepass_tail_fixture_major)) WhStepR.wstuck := @Eq.refl WhStepR WhStepR.wstuck",
    r"def prepass_tail_fixture_missing_field_stuck : @Eq WhStepR
 (iota_reduct_whc3 prepass_tail_fixture_env prepass_tail_fixture_identity (prepass_tail_fixture_term (@ListType.cons Level iota_tail_fixture_level (@ListType.nil Level)) (KExpr.const Name.anonymous (@ListType.nil Level)))) WhStepR.wstuck := @Eq.refl WhStepR WhStepR.wstuck",
    r"def prepass_tail_fixture_starved_before_guards : @Eq WhStepR
 (iota_reduct_whc3 prepass_tail_fixture_env
   (fun (_e : KExpr) => @OptionType.none KExpr) (prepass_tail_fixture_term (@ListType.nil Level) (KExpr.const Name.anonymous (@ListType.nil Level))))
 WhStepR.wstarved := @Eq.refl WhStepR WhStepR.wstarved",
    r"def prepass_tail_fixture_stuck_tag (e : KExpr)
 (h : @Eq WhStepR (iota_reduct_whc3 prepass_tail_fixture_env prepass_tail_fixture_identity e)
   WhStepR.wstuck) : Nat :=
 iota_reduct_whc3_stuck_inv_type prepass_tail_fixture_env prepass_tail_fixture_identity e Nat h
 (fun   (hn : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.none Name)) => Nat.zero)
 (fun (recname : Name) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (hn : @Eq (OptionType RecMeta) (recmeta_for prepass_tail_fixture_env recname) (@OptionType.none RecMeta)) => Nat.zero)
 (fun (recname : Name) (meta : RecMeta) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (h2 : @Eq (OptionType RecMeta) (recmeta_for prepass_tail_fixture_env recname) (@OptionType.some RecMeta meta)) (hn : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.none KExpr)) => Nat.zero)
 (fun (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (h2 : @Eq (OptionType RecMeta) (recmeta_for prepass_tail_fixture_env recname) (@OptionType.some RecMeta meta)) (h3 : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major)) (hw : @Eq (OptionType KExpr) (prepass_tail_fixture_identity major) (@OptionType.some KExpr wmajor)) (hn : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.none Name)) => Nat.zero)
 (fun (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (h2 : @Eq (OptionType RecMeta) (recmeta_for prepass_tail_fixture_env recname) (@OptionType.some RecMeta meta)) (h3 : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major)) (hw : @Eq (OptionType KExpr) (prepass_tail_fixture_identity major) (@OptionType.some KExpr wmajor)) (h4 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname)) (hn : @Eq (OptionType RecRule) (recrule_for prepass_tail_fixture_env recname cname) (@OptionType.none RecRule)) => Nat.zero)
 (fun (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule) (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)) (h2 : @Eq (OptionType RecMeta) (recmeta_for prepass_tail_fixture_env recname) (@OptionType.some RecMeta meta)) (h3 : @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (@OptionType.some KExpr major)) (hw : @Eq (OptionType KExpr) (prepass_tail_fixture_identity major) (@OptionType.some KExpr wmajor)) (h4 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (@OptionType.some Name cname)) (h5 : @Eq (OptionType RecRule) (recrule_for prepass_tail_fixture_env recname cname) (@OptionType.some RecRule rule)) (hn : @Eq (OptionType KExpr) (iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args wmajor)) (@OptionType.none KExpr)) => Nat.succ Nat.zero)",
    r"def prepass_tail_fixture_missing_universe_uses_ktail : @Eq Nat
 (prepass_tail_fixture_stuck_tag (prepass_tail_fixture_term (@ListType.nil Level) prepass_tail_fixture_major) prepass_tail_fixture_missing_universe_stuck)
 (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)",
    r"def prepass_tail_fixture_extra_universe_uses_ktail : @Eq Nat
 (prepass_tail_fixture_stuck_tag (prepass_tail_fixture_term (@ListType.cons Level iota_tail_fixture_level (@ListType.cons Level Level.zero (@ListType.nil Level))) prepass_tail_fixture_major) prepass_tail_fixture_extra_universe_stuck)
 (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)",
    r"def prepass_tail_fixture_missing_field_uses_ktail : @Eq Nat
 (prepass_tail_fixture_stuck_tag (prepass_tail_fixture_term (@ListType.cons Level iota_tail_fixture_level (@ListType.nil Level)) (KExpr.const Name.anonymous (@ListType.nil Level))) prepass_tail_fixture_missing_field_stuck)
 (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)",
];

impl Specification {
    /// Late controls: require the root-tail fixtures and the actual pre-pass views.
    pub(super) fn add_iota_prepass_guard_controls(&mut self) -> Result<(), SpecError> {
        for source in GUARD_CONTROLS {
            self.add_recursive_def(
                source,
                "Actual pre-pass guarded-tail control: distinguish success, guard refusal and starvation; no environment admission or typing claim.",
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const GUARD_NEGATIVES: &[&str] = &[
        r"def prepass_tail_forged_guard_failure_starves : @Eq WhStepR
 (iota_reduct_whc3 prepass_tail_fixture_env prepass_tail_fixture_identity (prepass_tail_fixture_term (@ListType.nil Level) prepass_tail_fixture_major)) WhStepR.wstarved := @Eq.refl WhStepR WhStepR.wstarved",
        r"def prepass_tail_forged_starved_is_stuck : @Eq WhStepR
 (iota_reduct_whc3 prepass_tail_fixture_env
   (fun (_e : KExpr) => @OptionType.none KExpr) (prepass_tail_fixture_term (@ListType.nil Level) (KExpr.const Name.anonymous (@ListType.nil Level))))
 WhStepR.wstuck := @Eq.refl WhStepR WhStepR.wstuck",
        r"def prepass_tail_forged_lookups_alone_fire : @Eq WhStepR
 (iota_reduct_whc3 prepass_tail_fixture_env prepass_tail_fixture_identity (prepass_tail_fixture_term (@ListType.cons Level iota_tail_fixture_level (@ListType.nil Level)) (KExpr.const Name.anonymous (@ListType.nil Level)))) (WhStepR.wstep iota_tail_fixture_result) :=
 @Eq.refl WhStepR (WhStepR.wstep iota_tail_fixture_result)",
    ];

    #[test]
    fn actual_prepass_guard_controls_parse() {
        for source in GUARD_CONTROLS.iter().chain(GUARD_NEGATIVES) {
            crate::test_utils::parse_check(source).expect("actual guarded pre-pass source parses");
        }
    }

    #[test]
    fn actual_prepass_guard_controls_and_verdict_refusals_are_checked() {
        let mut spec = crate::test_utils::build_spec_with_stack();
        if !spec
            .definitions()
            .contains_key("prepass_tail_fixture_stuck_tag")
        {
            spec.add_iota_prepass_guard_controls()
                .expect("actual guard controls check");
        }
        for name in [
            "prepass_tail_fixture_whc_accepts",
            "prepass_tail_fixture_whc3_accepts",
            "prepass_tail_fixture_missing_universe_stuck",
            "prepass_tail_fixture_extra_universe_stuck",
            "prepass_tail_fixture_missing_field_stuck",
            "prepass_tail_fixture_starved_before_guards",
            "prepass_tail_fixture_missing_universe_uses_ktail",
            "prepass_tail_fixture_extra_universe_uses_ktail",
            "prepass_tail_fixture_missing_field_uses_ktail",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("checked actual pre-pass control");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
        for source in GUARD_NEGATIVES {
            assert!(spec
                .add_recursive_def(
                    source,
                    "Reject conflated starvation, guard refusal or a forged success."
                )
                .is_err());
        }
    }

    /// The bound must be strict. `Le` here would mean the budget induction has
    /// no descent measure, which is the one failure mode that sinks the route --
    /// so it is pinned by a test rather than left to review.
    #[test]
    fn test_result_stuck_bound_is_strict() {
        let src = DECLS[0].0;
        assert!(src.contains("whnf_fuel_red_wh3_result_stuck_lt"));
        assert!(
            src.contains("Lt j n"),
            "the delivered bound must be strict: Lt, never Le"
        );
        assert!(
            src.contains("lt_succ_self"),
            "the wstuck arm's bound comes from lt_succ_self k : Lt k (succ k)"
        );
        assert!(
            src.contains("lt_succ_weaken"),
            "the wstep arm must weaken the inherited bound"
        );
    }

    /// Level 4 is refuted, not skipped. If a `k4` continuation ever appears the
    /// inverter has stopped being an inversion and started being an assumption.
    #[test]
    fn test_level_four_is_discharged_not_assumed() {
        // Anchored to the declaration head: the LATE forms cite the six-way
        // form in their bodies and would otherwise match, but they are derived
        // by instantiation and correctly carry no refutation of their own.
        for (src, _) in DECLS
            .iter()
            .filter(|(s, _)| s.starts_with("def iota_reduct_whc3_stuck_inv"))
        {
            assert!(
                src.contains("wh_stuck_ne_starved"),
                "level 4 must be killed constructively by wh_stuck_ne_starved"
            );
            assert!(
                !src.contains("(k4 "),
                "there is no level-4 continuation: wstuck cannot arise there"
            );
        }
    }

    /// Levels 5, 6 and the guarded tail depend on the pre-pass result, so they must surface the
    /// `wh major = some wmajor` equation. Hiding it would silently suggest that
    /// a `wstuck` verdict is budget-independent, which it is not.
    #[test]
    fn test_late_levels_surface_the_prepass_equation() {
        let six_way = DECLS
            .iter()
            .find(|(s, _)| s.contains("def iota_reduct_whc3_stuck_inv_type"))
            .expect("six-way inverter present")
            .0;
        assert!(
            six_way.contains("OptionType.some KExpr wmajor"),
            "k5/k6/ktail must hand back the pre-pass equation, not hide it"
        );
    }

    /// The late form is an instantiation of the six-way form. If it ever grows
    /// its own recursion it could typecheck around a gap the six-way form
    /// reports honestly.
    #[test]
    fn test_late_inverter_is_derived_not_reproved() {
        let late = DECLS
            .iter()
            .find(|(s, _)| s.contains("def iota_reduct_whc3_stuck_late_inv_type"))
            .expect("late inverter present")
            .0;
        assert!(
            late.contains("iota_reduct_whc3_stuck_inv_type"),
            "the late form must be derived from the six-way form by instantiation"
        );
        assert!(
            !late.contains("WhStepR.rec"),
            "the late form must not run its own recursion"
        );
    }

    /// Successful rule lookup can still be declined by the actual guarded tail.
    #[test]
    fn test_tail_decline_is_a_separate_stuck_cause() {
        for (source, _) in DECLS.iter().filter(|(s, _)| {
            s.starts_with("def iota_reduct_whc3_stuck_inv")
                || s.starts_with("def iota_reduct_whc3_stuck_late_inv")
        }) {
            assert!(source.contains("(ktail : forall"));
            assert!(
                source.contains("iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e))")
            );
            assert!(source.contains("(@OptionType.some RecRule rule) -> @Eq (OptionType KExpr)"));
            assert!(!source.contains("(k4 "));
        }
    }

    #[test]
    fn test_all_sources_parens_balanced_and_ascii() {
        for (src, desc) in DECLS {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in {src:.60}");
            }
            assert_eq!(depth, 0, "unbalanced parens in {src:.60}");
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert!(
                !src.contains('\''),
                "a prime lexes as an identifier-continue char and silently makes a new name"
            );
            assert!(
                desc.len() > 80,
                "every declaration carries a real description"
            );
        }
    }
}
