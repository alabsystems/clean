// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The descent order for the THREE-WAY loop.
//!
//! # Why a new order rather than a bridge
//!
//! The capstone recurses on `rbelow_plus_acc` and gets its descent from
//! `whnf_fuel_red_rbelow_rtc`. Both are blocked here: `rbelow`'s `red` arm is
//! over `whnf_red_step`, and a three-way step does not embed into that relation
//! at any strength — nothing there lets a delta or a nested iota fire inside an
//! argument, and a recursor's major premise is an argument. `wh3_fires_here`
//! settles it by computation.
//!
//! The mismatch is an accident of history, not an obstruction. `rbelow`'s own
//! comment describes its `red` arm as *"the relation the executable loop
//! actually steps by"* — true of the ORIGINAL loop. The three-way loop steps by
//! something else, so it gets its own order, and the descent fact then falls out
//! of a plain fuel induction: `wbelow3.red` IS the loop's step, so there is
//! nothing to bridge. The two-way version needs three lemmas where this needs
//! none.
//!
//! # What is NOT verbatim, and must travel with any statement using this
//!
//! `wbelow3.red` carries a **budget**, so the relation says *y steps to x at
//! SOME budget* — an existential packed into the constructor, which `rbelow.red`
//! has no analogue of. Therefore **`wbelow3_plus_acc` is a strictly stronger
//! hypothesis than `rbelow_plus_acc`**, not the same assumption retargeted. It
//! stays a hypothesis rather than a discharged fact, so nothing becomes unsound
//! — but a theorem carrying it assumes more, and saying otherwise would be a
//! quiet overclaim.
//!
//! Everything else here is genuinely verbatim: `wbelow3_rtc_snoc`,
//! `wbelow3_plus_of_step_rtc` and `wbelow3_plus_acc_inv` are pure relation
//! algebra and never inspect the `red` arm's payload.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The three-way descent order, its closures, and the two component premises.
    pub(super) fn add_wbelow3(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            SRC_WBELOW3,
            "wbelow3 x y: x lies one step below y in the order the THREE-WAY algorithm descends on — either y takes one executable three-way step TO x at some pre-pass budget (note the reversed argument order, since reduction goes downward), or x is an immediate subexpression of y. \\\n\
             \\\n\
             Identical in SHAPE to rbelow, but NOT a retarget of it in force, and the difference must travel with any statement that uses it. rbelow's red arm is over whnf_red_step, and rbelow's own comment calls that the relation the executable loop actually steps by — true of the ORIGINAL loop. The three-way loop steps by something else, and does not embed into whnf_red_step at any strength (wh3_fires_here settles that by computation), so it needs its own order rather than a bridge. \\\n\
             \\\n\
             The red arm carries a BUDGET k, so the relation is y steps to x at SOME budget — an existential packed into the constructor, which rbelow.red has no analogue of. Consequence, stated plainly: wbelow3_plus_acc is a STRICTLY STRONGER hypothesis than rbelow_plus_acc, not the same assumption retargeted. It remains a hypothesis and not a discharged fact, so nothing becomes unsound; but a theorem carrying it assumes more. Census-neutral.",
        )?;
        self.add_inductive(
            SRC_WBELOW3_PLUS,
            "wbelow3_plus: the transitive closure of wbelow3. The completeness recursion descends on this rather than on wbelow3 because a single conversion round both reduces and then enters a subterm. Verbatim retarget of rbelow_plus. Census-neutral.",
        )?;
        self.add_inductive(
            SRC_WBELOW3_PLUS_ACC,
            "wbelow3_plus_acc e: e is accessible in the transitive wbelow3 order. THE well-foundedness witness the three-way conversion algorithm's termination argument consumes. \\\n\
             \\\n\
             Permanently a hypothesis, not something to discharge internally: discharging it for all terms is strong normalisation, which by Godel-2 cannot be proved inside the system it is about — and which is in any case FALSE for this calculus as reflected. Carrying it is therefore the correct shape for the theorem, not a gap in it. Note it is stronger than rbelow_plus_acc, because wbelow3's red arm quantifies over budgets; see wbelow3. Census-neutral.",
        )?;
        self.add_inductive(
            SRC_WBELOW3_RTC,
            "wbelow3_rtc x z: x is AT OR BELOW z in the three-way algorithm's order. The reflexive case is not a technicality — a term already in weak head normal form does not step at all, so its reduction leg is genuinely empty and a strict relation could not describe it. Verbatim retarget of rbelow_rtc. Census-neutral.",
        )?;
        self.add_recursive_def(
            SRC_WBELOW3_RTC_SNOC,
            "wbelow3_rtc_snoc: append one wbelow3 step at the BACK of a wbelow3_rtc chain. Pure relation algebra — it never inspects the red arm's payload, which is why it retargets verbatim from rbelow_rtc_snoc despite wbelow3.red carrying a budget. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WBELOW3_PLUS_OF_STEP_RTC,
            "wbelow3_plus_of_step_rtc: one strict step followed by a reflexive-transitive chain is a strict chain. Verbatim retarget; again pure relation algebra. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WHNF_FUEL_RED_WH3_WBELOW3_RTC,
            "whnf_fuel_red_wh3_wbelow3_rtc: whatever the THREE-WAY loop returns is at or below its input in the algorithm's order. THE DESCENT FACT the capstone's recursion consumes. \\\n\
             \\\n\
             Proved DIRECTLY by fuel induction, and that is the point of defining the order over the loop's own step. The two-way whnf_fuel_red_rbelow_rtc composes THREE lemmas — reach-soundness, a step-star embedding, and an order embedding — because its order is phrased over a relation the loop has to be shown to implement. Here there is nothing to show: wbelow3.red IS the loop's step, so the induction closes against the convoy equation itself and none of those three bridges appears. \\\n\
             \\\n\
             Nat.rec generalised over both a and r, with a WhStepR.rec convoy inside: wstuck gives refl transported along some-injectivity, wstarved is absurd because the dispatch returns none, and wstep appends with wbelow3_rtc_snoc. Structurally the same term as whnf_fuel_red_wh3_result_stuck, differing only in the two arms that are supposed to differ. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WBELOW3_PLUS_ACC_INV,
            "wbelow3_plus_acc_inv: accessibility is inherited downward — the field of the intro node. Verbatim retarget of rbelow_plus_acc_inv. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WHNF_COMPONENT_BELOW_WH3,
            "whnf_component_below_wh3: an immediate subexpression of a THREE-WAY whnf result is strictly below the original term. One of the two premises each recursive completeness round must supply before it may descend. Composes the descent fact above with wbelow3_plus_of_step_rtc. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WHNF_COMPONENT_ACC_WH3,
            "whnf_component_acc_wh3: an immediate subexpression of a THREE-WAY whnf result inherits accessibility. The other of the two premises. Together with whnf_component_below_wh3 this is what unblocks the eleven spine declarations, which could not be ported while the descent ran through whnf_red_step. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

const SRC_WBELOW3: &str = "inductive wbelow3 : KExpr -> KExpr -> Type\n\
             | red : forall (x : KExpr) (y : KExpr) (k : Nat), Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) y) (WhStepR.wstep x) -> wbelow3 x y\n\
             | sub : forall (x : KExpr) (y : KExpr), subexpr_step x y -> wbelow3 x y";

const SRC_WBELOW3_PLUS: &str = "inductive wbelow3_plus : KExpr -> KExpr -> Type\n\
             | base : forall (x : KExpr) (y : KExpr), wbelow3 x y -> wbelow3_plus x y\n\
             | step : forall (x : KExpr) (y : KExpr) (z : KExpr), wbelow3 x y -> wbelow3_plus y z -> wbelow3_plus x z";

const SRC_WBELOW3_PLUS_ACC: &str = "inductive wbelow3_plus_acc : KExpr -> Type\n\
             | intro : forall (e : KExpr), (forall (e2 : KExpr), wbelow3_plus e2 e -> wbelow3_plus_acc e2) -> wbelow3_plus_acc e";

const SRC_WBELOW3_RTC: &str = "inductive wbelow3_rtc : KExpr -> KExpr -> Type\n\
             | refl : forall (x : KExpr), wbelow3_rtc x x\n\
             | step : forall (x : KExpr) (y : KExpr) (z : KExpr), wbelow3 x y -> wbelow3_rtc y z -> wbelow3_rtc x z";

const SRC_WBELOW3_RTC_SNOC: &str = "def wbelow3_rtc_snoc (x : KExpr) (y : KExpr) (hxy : wbelow3_rtc x y) : forall (z : KExpr), wbelow3 y z -> wbelow3_rtc x z := wbelow3_rtc.rec (fun (p : KExpr) (q : KExpr) (_h : wbelow3_rtc p q) => forall (z : KExpr), wbelow3 q z -> wbelow3_rtc p z) (fun (p : KExpr) (z : KExpr) (hz : wbelow3 p z) => wbelow3_rtc.step p z z hz (wbelow3_rtc.refl z)) (fun (p : KExpr) (q : KExpr) (r : KExpr) (hpq : wbelow3 p q) (_hqr : wbelow3_rtc q r) (ih : forall (z : KExpr), wbelow3 r z -> wbelow3_rtc q z) (z : KExpr) (hz : wbelow3 r z) => wbelow3_rtc.step p q z hpq (ih z hz)) x y hxy";

const SRC_WBELOW3_PLUS_OF_STEP_RTC: &str = "def wbelow3_plus_of_step_rtc (x : KExpr) (y : KExpr) (z : KExpr) (hxy : wbelow3 x y) (hyz : wbelow3_rtc y z) : wbelow3_plus x z := wbelow3_rtc.rec (fun (p : KExpr) (q : KExpr) (_h : wbelow3_rtc p q) => forall (w : KExpr), wbelow3 w p -> wbelow3_plus w q) (fun (p : KExpr) (w : KExpr) (hw : wbelow3 w p) => wbelow3_plus.base w p hw) (fun (p : KExpr) (q : KExpr) (r : KExpr) (hpq : wbelow3 p q) (_hqr : wbelow3_rtc q r) (ih : forall (w : KExpr), wbelow3 w q -> wbelow3_plus w r) (w : KExpr) (hw : wbelow3 w p) => wbelow3_plus.step w p r hw (ih p hpq)) y z hyz x hxy";

const SRC_WHNF_FUEL_RED_WH3_WBELOW3_RTC: &str = "def whnf_fuel_red_wh3_wbelow3_rtc (n : Nat) : forall (a : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n a) (OptionType.some KExpr r) -> wbelow3_rtc r a := Nat.rec (fun (m : Nat) => forall (a : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env m a) (OptionType.some KExpr r) -> wbelow3_rtc r a) (fun (a : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env Nat.zero a) (OptionType.some KExpr r)) => option_none_ne_some_type KExpr r (wbelow3_rtc r a) h) (fun (k : Nat) (ih : forall (a0 : KExpr) (r0 : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env k a0) (OptionType.some KExpr r0) -> wbelow3_rtc r0 a0) (a : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env (Nat.succ k) a) (OptionType.some KExpr r)) => WhStepR.rec (fun (o : WhStepR) => Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) a) o -> Eq (OptionType KExpr) (wh_dispatch3 o a (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (OptionType.some KExpr r) -> wbelow3_rtc r a) (fun (_hq : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) a) WhStepR.wstuck) (h2 : Eq (OptionType KExpr) (wh_dispatch3 WhStepR.wstuck a (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (OptionType.some KExpr r)) => Eq.substType KExpr (fun (zz : KExpr) => wbelow3_rtc zz a) a r (option_some_inj KExpr a r h2) (wbelow3_rtc.refl a)) (fun (_hs : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) a) WhStepR.wstarved) (h2 : Eq (OptionType KExpr) (wh_dispatch3 WhStepR.wstarved a (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (OptionType.some KExpr r)) => option_none_ne_some_type KExpr r (wbelow3_rtc r a) h2) (fun (a2 : KExpr) (hq : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) a) (WhStepR.wstep a2)) (h2 : Eq (OptionType KExpr) (wh_dispatch3 (WhStepR.wstep a2) a (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (OptionType.some KExpr r)) => wbelow3_rtc_snoc r a2 (ih a2 r h2) a (wbelow3.red a2 a k hq)) (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) a) (Eq.refl WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) a)) h) n";

const SRC_WBELOW3_PLUS_ACC_INV: &str = "def wbelow3_plus_acc_inv (e : KExpr) (h : wbelow3_plus_acc e) : forall (e2 : KExpr), wbelow3_plus e2 e -> wbelow3_plus_acc e2 := wbelow3_plus_acc.rec (fun (x : KExpr) (_h : wbelow3_plus_acc x) => forall (e2 : KExpr), wbelow3_plus e2 x -> wbelow3_plus_acc e2) (fun (x : KExpr) (hfield : forall (e2 : KExpr), wbelow3_plus e2 x -> wbelow3_plus_acc e2) (_ih : forall (e2 : KExpr), wbelow3_plus e2 x -> forall (e3 : KExpr), wbelow3_plus e3 e2 -> wbelow3_plus_acc e3) => hfield) e h";

const SRC_WHNF_COMPONENT_BELOW_WH3: &str = "def whnf_component_below_wh3 (n : Nat) (a : KExpr) (r : KExpr) (c : KExpr) (hr : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n a) (OptionType.some KExpr r)) (hc : subexpr_step c r) : wbelow3_plus c a := wbelow3_plus_of_step_rtc c r a (wbelow3.sub c r hc) (whnf_fuel_red_wh3_wbelow3_rtc n a r hr)";

const SRC_WHNF_COMPONENT_ACC_WH3: &str = "def whnf_component_acc_wh3 (n : Nat) (a : KExpr) (r : KExpr) (c : KExpr) (hr : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n a) (OptionType.some KExpr r)) (hc : subexpr_step c r) (hacc : wbelow3_plus_acc a) : wbelow3_plus_acc c := wbelow3_plus_acc_inv a hacc c (wbelow3_plus_of_step_rtc c r a (wbelow3.sub c r hc) (whnf_fuel_red_wh3_wbelow3_rtc n a r hr))";
