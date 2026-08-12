// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fuel adequacy for the THREE-WAY loop, and pairing.
//!
//! # Why not accessibility
//!
//! The original capstone recurses on `rbelow_plus_acc` and gets its fuel from
//! `whnf_fuel_from_acc`. That is unavailable here: `rbelow`'s two arms are
//! `whnf_red_step` and `subexpr_step`, and a three-way step does **not** embed
//! into `whnf_red_step` — nothing there lets a delta or a nested iota fire
//! inside an argument, and a recursor's major premise is an argument.
//! `wh3_fires_here` settles that by computation. The two-way faithful port hit
//! the same wall and reached for the same repair.
//!
//! So fuel comes from a **normalisation derivation** instead. Monotonicity does
//! not remove the need for one: it raises a budget you already have, it does not
//! produce one.
//!
//! # What the three-way split buys, concretely
//!
//! Two things the two-way faithful port could not have:
//!
//! * `WhnfFuelReachesWh3` needs **no packaged stuckness field**. The two-way
//!   witness carries one because its monotonicity is restricted; `whnf_fuel_red_wh3_le`
//!   is unrestricted, so the witness matches the ORIGINAL `WhnfFuelReaches`.
//! * `wh3_step_mono_le` carries **no `i2`/`i8`**. The two-way `wh_step_mono_le`
//!   discharges its stability premise through `wh_hsm_all`, which needs two
//!   environment interfaces; `whnf_fuel_red_wh3_monotone` is unconditional.
//!
//! Nothing downstream of this file carries environment side conditions as a
//! result.
//!
//! # One design correction worth recording
//!
//! `WhNormalizes3`'s `stuck` field is budget-**indexed**. Fixing it at
//! `Nat.zero` is *sound* — a starved pre-pass reports `wstarved`, never
//! `wstuck` — but strictly stronger than needed, and it costs coverage: a term
//! stuck only at the iota chain's later levels is `wstarved` at budget 0 and
//! would have had no witness at all. Worse, the natural producer,
//! `whnf_fuel_red_wh3_result_stuck`, hands back an arbitrary budget that cannot
//! be lowered, so the two would not have composed. Quantifying costs nothing —
//! the same proof, at fuel `succ j`.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Fuel adequacy and pairing, over the three-way loop.
    pub(super) fn add_wh3_fuel_adequacy(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_WH3_STEP_MONO_LE,
            "wh3_step_mono_le: a three-way step that FIRES at one pre-pass budget still fires, at the same reduct, at every larger one. Le.rec on the bound, closing each successor with wh3_step_step_stable. \\\n\
             \\\n\
             Worth naming rather than inlining, because of what its signature does NOT contain. The two-way wh_step_mono_le carries i2 and i8 — it discharges its stability premise through wh_hsm_all, which needs RecEnvCtorNoRecMeta and RecEnvCtorNoDefVal. Here whnf_fuel_red_wh3_monotone is UNCONDITIONAL, so it discharges the premise with no side conditions at all. That is the single mechanical consequence of wstarved being its own constructor, and it is why nothing downstream of this carries environment hypotheses. DerivedProved, zero axiom_deps.",
        )?;
        self.add_inductive(
            SRC_WHNORMALIZES3,
            "WhNormalizes3 r e: a CONSTRUCTIVE witness that e reaches the normal form r under the three-way loop — either e is already genuinely stuck at some budget, or it steps at some budget to a term that normalises to r. \\\n\
             \\\n\
             A derivation rather than a proposition, for the reason the two-way WhNormalizes gives: an accessibility argument would need to decide whether a term steps at SOME budget, which is not constructive, and the tempting repair is a decidability assumption — the vacuity trap this program has already fallen into once. \\\n\
             \\\n\
             The stuck field is BUDGET-INDEXED, and that is not cosmetic. Fixing it at Nat.zero is sound, because a starved pre-pass reports wstarved and never wstuck, but it is strictly stronger than needed and it costs coverage: a term stuck only at the iota chain's later levels is wstarved at budget 0, so it would have had no witness at all, and the natural producer — whnf_fuel_red_wh3_result_stuck — hands back an arbitrary budget that cannot be lowered. Quantifying gives the same proof at fuel succ j and composes with that producer directly. Census-neutral.",
        )?;
        self.add_inductive(
            SRC_WHNFFUELREACHESWH3,
            "WhnfFuelReachesWh3 e: some budget suffices for the three-way loop on e. \\\n\
             \\\n\
             Note what is ABSENT compared with the two-way WhnfFuelReachesWh, which packages a stuckness proof inside its constructor: it has to, because two-way monotonicity is RESTRICTED and takes stuckness as a hypothesis, so a witness recording only the budget would be unusable for pairing. whnf_fuel_red_wh3_le carries no such premise, so this witness carries no such field and matches the ORIGINAL WhnfFuelReaches instead. Nothing is lost: whnf_fuel_red_wh3_result_stuck recovers the stuckness certificate from any successful run, unconditionally. Census-neutral.",
        )?;
        self.add_recursive_def(
            SRC_WH3_FUEL_FROM_NORMALIZES,
            "wh3_fuel_from_normalizes: a normalisation derivation yields a concrete budget. THE FUEL-ADEQUACY BRIDGE for the three-way loop. \\\n\
             \\\n\
             Why a normalisation derivation and not accessibility, which is what the original capstone uses: the rbelow order cannot see this loop. Its two arms are whnf_red_step and subexpr_step, and a three-way step does not embed into whnf_red_step — no congruence lets a delta or a nested iota fire inside an argument, and a recursor's major premise is an argument. wh3_fires_here settles that by computation. So accessibility in the algorithm's own order is not available, exactly as the two-way faithful port found. \\\n\
             \\\n\
             Monotonicity does not remove the need for this: it raises a budget you already have, it does not produce one. What it does buy is that the bound arithmetic is unrestricted — no i2, no i8, no stuckness side conditions anywhere in this term. DerivedProved, zero axiom_deps.",
        )?;
        self.add_inductive(
            SRC_WHNFFUELPAIRWH3,
            "WhnfFuelPairWh3 a b: ONE budget at which the three-way loop returns on both a and b, with both results. The capstone reduces two terms and needs their loops to terminate at a shared bound; carrying two separate budgets would make every later step carry two. Census-neutral.",
        )?;
        self.add_recursive_def(
            SRC_WHNF_FUEL_PAIR_WH3,
            "whnf_fuel_pair_wh3: two independent budget witnesses yield ONE budget that works for both. The bound is na + nb rather than the maximum, for the same reason the original gives — the tree has no nat_max with the accompanying order facts, while both addition bounds are already present, and nothing wants the bound tight. \\\n\
             \\\n\
             A direct retarget of whnf_fuel_pair, which it can be precisely because whnf_fuel_red_wh3_le is unrestricted: the two-way faithful analogue would have to thread a stuckness proof through both legs. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

const SRC_WH3_STEP_MONO_LE: &str = "def wh3_step_mono_le (k : Nat) (m : Nat) (hle : Le k m) (e : KExpr) (y : KExpr) : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) (WhStepR.wstep y) -> Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env m z) e) (WhStepR.wstep y) := Le.rec k (fun (j : Nat) (_hj : Le k j) => Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) (WhStepR.wstep y) -> Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env j z) e) (WhStepR.wstep y)) (fun (h : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) (WhStepR.wstep y)) => h) (fun (j : Nat) (_hj : Le k j) (ihj : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) (WhStepR.wstep y) -> Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env j z) e) (WhStepR.wstep y)) (h : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) (WhStepR.wstep y)) => wh3_step_step_stable j (whnf_fuel_red_wh3_monotone j) e y (ihj h)) m hle";

const SRC_WHNORMALIZES3: &str = "inductive WhNormalizes3 (r : KExpr) : KExpr -> Type\n\
             | stuck : forall (j : Nat), wh3_stuck_at j r -> WhNormalizes3 r r\n\
             | step : forall (e : KExpr) (x2 : KExpr) (k : Nat), Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) (WhStepR.wstep x2) -> WhNormalizes3 r x2 -> WhNormalizes3 r e";

const SRC_WHNFFUELREACHESWH3: &str = "inductive WhnfFuelReachesWh3 : KExpr -> Type\n\
             | mk : forall (e : KExpr) (n : Nat) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n e) (OptionType.some KExpr r) -> WhnfFuelReachesWh3 e";

const SRC_WH3_FUEL_FROM_NORMALIZES: &str = "def wh3_fuel_from_normalizes (r : KExpr) (e : KExpr) (d : WhNormalizes3 r e) : WhnfFuelReachesWh3 e := WhNormalizes3.rec r (fun (x : KExpr) (_h : WhNormalizes3 r x) => WhnfFuelReachesWh3 x) (fun (j : Nat) (hst : wh3_stuck_at j r) => WhnfFuelReachesWh3.mk r (Nat.succ j) r (Eq.trans (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env (Nat.succ j) r) (wh_dispatch3 WhStepR.wstuck r (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2)) (OptionType.some KExpr r) (Eq.cong WhStepR (OptionType KExpr) (fun (o : WhStepR) => wh_dispatch3 o r (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2)) (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) r) WhStepR.wstuck hst) (Eq.refl (OptionType KExpr) (OptionType.some KExpr r)))) (fun (e0 : KExpr) (x2 : KExpr) (k : Nat) (hs : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e0) (WhStepR.wstep x2)) (_w : WhNormalizes3 r x2) (ih : WhnfFuelReachesWh3 x2) => WhnfFuelReachesWh3.rec x2 (fun (_wt : WhnfFuelReachesWh3 x2) => WhnfFuelReachesWh3 e0) (fun (n : Nat) (rr : KExpr) (heq : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n x2) (OptionType.some KExpr rr)) => WhnfFuelReachesWh3.mk e0 (Nat.succ (Nat.add k n)) rr (Eq.trans (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env (Nat.succ (Nat.add k n)) e0) (wh_dispatch3 (WhStepR.wstep x2) e0 (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env (Nat.add k n) z)) (OptionType.some KExpr rr) (Eq.cong WhStepR (OptionType KExpr) (fun (o : WhStepR) => wh_dispatch3 o e0 (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env (Nat.add k n) z)) (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env (Nat.add k n) z) e0) (WhStepR.wstep x2) (wh3_step_mono_le k (Nat.add k n) (le_add_self_left k n) e0 x2 hs)) (whnf_fuel_red_wh3_le n (Nat.add k n) (le_add_self_right k n) x2 rr heq))) ih) e d";

const SRC_WHNFFUELPAIRWH3: &str = "inductive WhnfFuelPairWh3 (a : KExpr) (b : KExpr) : Type\n\
             | mk : forall (n : Nat) (ra : KExpr) (rb : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n a) (OptionType.some KExpr ra) -> Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n b) (OptionType.some KExpr rb) -> WhnfFuelPairWh3 a b";

const SRC_WHNF_FUEL_PAIR_WH3: &str = "def whnf_fuel_pair_wh3 (a : KExpr) (b : KExpr) (wa : WhnfFuelReachesWh3 a) (wb : WhnfFuelReachesWh3 b) : WhnfFuelPairWh3 a b := WhnfFuelReachesWh3.rec a (fun (_x : WhnfFuelReachesWh3 a) => WhnfFuelPairWh3 a b) (fun (na : Nat) (ra : KExpr) (hra : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env na a) (OptionType.some KExpr ra)) => WhnfFuelReachesWh3.rec b (fun (_y : WhnfFuelReachesWh3 b) => WhnfFuelPairWh3 a b) (fun (nb : Nat) (rb : KExpr) (hrb : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env nb b) (OptionType.some KExpr rb)) => WhnfFuelPairWh3.mk a b (Nat.add na nb) ra rb (whnf_fuel_red_wh3_le na (Nat.add na nb) (le_add_self_left na nb) a ra hra) (whnf_fuel_red_wh3_le nb (Nat.add na nb) (le_add_self_right na nb) b rb hrb)) wb) wa";
