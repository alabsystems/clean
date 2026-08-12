// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The hnf discharge** — turning the completeness capstone's false premise
//! into a conditional one.
//!
//! ```text
//! hnf   : whnf_fuel_red     the_red_env m e = some r -> nf_head r     -- FALSE
//! hnf3  : whnf_fuel_red_wh3 the_red_env m e = some r -> nf_head r     -- given the app residual
//! ```
//!
//! `hnf` is refuted (`hnf_is_false`). A false premise makes every theorem
//! carrying it **vacuous rather than unprovable**, and that is precisely the
//! failure no axiom ratchet can see: a theorem about an impossible hypothesis
//! has an impeccably empty axiom closure.
//!
//! # Why the three-way loop is what unlocks this
//!
//! `hnf_conv` is the honest replacement, conditioned on `wh_perm_stuck` — the
//! step finds nothing **at every** pre-pass budget. That quantifier is not
//! fussiness: the two-way step returns `none` both when genuinely stuck and when
//! merely starved, so stuckness at any single budget is no evidence at all.
//!
//! The three-way step separates those (`wstuck` / `wstarved`), so:
//!
//! * a single-budget hypothesis (`wh3_stuck_at`) is already a genuine claim, and
//! * the loop **hands you one for free** — `wh_dispatch3` yields `some e` only on
//!   the `wstuck` arm, so a returned result carries its own certificate
//!   (`whnf_fuel_red_wh3_result_stuck`).
//!
//! And a single budget is *enough*: `hnf_conv`'s nine arms consult the hypothesis
//! exactly twice, at `const` and `let_`, both arms whose step never looks at the
//! pre-pass.
//!
//! # What is still open, precisely
//!
//! The `app` case. It is a **premise, not an assumption** — the difference being
//! that this one is satisfiable: `hnf_conv_rigid` discharges it for every
//! rigid-headed spine, and `iota_immune_of_dead_const_head`,
//! `iota_immune_of_under_applied` and `iota_immune_of_bvar_major` supply three
//! more classes. Missing: a major stuck for some other reason, and spines with
//! arguments past the major slot.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The `hnf3` binder, in `HNF`'s shape (`nf_head.rs:66`) with the three-way loop.
///
/// Kept verbatim-parallel to `HNF` so a ported round can bind this instead
/// without any other change to its statement.
#[allow(dead_code)]
pub(super) const HNF3: &str = "(hnf3 : forall (m : Nat) (e : KExpr) (r : KExpr), \
     Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env m e) (OptionType.some KExpr r) -> \
     nf_head r) ";

impl Specification {
    /// The single-budget stuckness predicate, the classification over it, the
    /// discharge, their composition, and the non-vacuity witnesses.
    pub(super) fn add_hnf_discharge3(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_WH3_STUCK_AT,
            "wh3_stuck_at j x: the three-way step finds NOTHING TO DO on x at pre-pass budget j. This is hnf_conv's convergence hypothesis with the quantifier REMOVED, and removing it is the whole point. wh_perm_stuck had to range over EVERY budget because the two-way step returns none both when genuinely stuck and when merely starved, so stuckness at any one budget said nothing. The three-way step separates those into wstuck and wstarved, so a single budget is already a genuine claim. Registered with add_recursive_def, NOT add_definition: this is Nat -> KExpr -> Prop, a FUNCTION type rather than a Prop, and definition_registration marks any non-Prop-typed valued def Declaration::Opaque to block WHNF unfolding. As an opaque, no Wh3ResultStuck value could ever be built, because mk's field type could never be matched against a raw Eq WhStepR proof. Census-neutral.",
        )?;
        self.add_inductive(
            SRC_WH3RESULTSTUCK,
            "Wh3ResultStuck r: SOME budget exists at which the three-way step is stuck on r. The fragment has no Exists, so this is the single-constructor witness idiom already used by WhnfFuelPair and DefEqFuelAcceptsWh3. Registering the target type is not a claim that it is inhabited; whnf_fuel_red_wh3_result_stuck is what makes it so. Census-neutral.",
        )?;
        self.add_recursive_def(
            SRC_HNF_CONV3,
            "hnf_conv3: the head classification, conditioned on SINGLE-BUDGET stuckness — the honest replacement for the false hnf, over the three-way loop. Nine arms, of which SEVEN are hnf_conv's verbatim: sort, pi, lit and proj are rigid, lam and bvar have their own nf_head arms, and app is handed back to the caller as a premise. Only the two arms that actually consult the hypothesis change, and they change only because the equation's TYPE did, from Eq (OptionType KExpr) ... none to Eq WhStepR ... wstuck: const convoys on defval_for and refutes the some branch with wh_stuck_ne_step, then feeds the unchanged delta_reduct_eq_none_of_defval_none; let_ is refuted outright, since the three-way step fires on a let_ unconditionally. Those two arms conclude at DIFFERENT UNIVERSES — the const convoy at Prop, the let_ absurdity at Type, because nf_head is Type-valued — so they take wh_stuck_ne_step and wh_stuck_ne_step_type respectively. That is non-cumulativity biting once in each direction inside a single term. Note what is NOT needed: hnf_conv applies its hypothesis at Nat.zero twice, and those are its only two uses. Both arms are ones whose step never consults the pre-pass, which is exactly why one budget suffices here. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WHNF_FUEL_RED_WH3_RESULT_STUCK,
            "whnf_fuel_red_wh3_result_stuck: THE DISCHARGE — if the three-way loop returns a term, that term is genuinely stuck at some budget. This is the property the three-way split was built to have, now proved rather than asserted: wh_dispatch3 yields some e ONLY on the wstuck arm, so a returned result carries its own stuckness certificate. Nat.rec on the fuel with the motive generalised over BOTH e and r — the recursion moves to a different term, so a motive fixing e cannot close — and a convoy on the step result inside. The wstuck arm transports along some-injectivity with an explicit motive; wstarved and the base case are absurd by none-vs-some; wstep is the induction hypothesis. The convoy carries the equation in the same orientation as whnf_fuel_red_wh3_monotone, which makes the arm hypothesis LITERALLY wh3_stuck_at k e — no Eq.symm anywhere. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_HNF3_OF_APP_RESIDUAL,
            "hnf3_of_app_residual: the capstone's hnf premise, DISCHARGED down to the application case — and this is what stops the completeness capstone being vacuous. hnf claimed every whnf result has a normal-form head. It is FALSE (hnf_is_false), and a false premise makes a theorem VACUOUS rather than unprovable, which is why no axiom ratchet ever flagged the capstone: a theorem about an impossible hypothesis has a perfectly empty axiom closure. This composes the discharge with the classification — whnf_fuel_red_wh3_result_stuck then hnf_conv3 — to give the same statement over the three-way loop with NO convergence hypothesis at all, conditional only on the residual application case. Its type is HNF's verbatim with whnf_fuel_red_wh3 for whnf_fuel_red, so it plugs directly into a ported round's binder rather than needing one to be reshaped around it. WHAT REMAINS OPEN, stated precisely: the residual asks for nf_head at an application. It is SATISFIABLE, which is the entire difference from hnf — hnf_conv_rigid supplies it for every rigid-headed spine, and iota_immune_of_dead_const_head, iota_immune_of_under_applied and iota_immune_of_bvar_major supply three further classes. What is still missing is a major stuck for some other reason, and spines with arguments past the major slot. Conditional theorem, never an axiom. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_ACCEPTS_PI_SORT,
            "wh3_accepts_pi_sort: NON-VACUITY. The three-way acceptance predicate is INHABITED, by kernel computation over the real reflected environment — a single Eq.refl in which the kernel evaluates the algorithm down to Bool.true. This is not decoration. Every def_eq_complete_step_wh3_* consumes a DefEqFuelAcceptsWh3 and produces one, so without a base the predicate could be EMPTY and every step a theorem about nothing. No axiom ratchet detects that: an empty predicate has an empty axiom closure. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_ACCEPTS_SORT_ZERO,
            "wh3_accepts_sort_zero: NON-VACUITY. The three-way acceptance predicate is INHABITED, by kernel computation over the real reflected environment — a single Eq.refl in which the kernel evaluates the algorithm down to Bool.true. This is not decoration. Every def_eq_complete_step_wh3_* consumes a DefEqFuelAcceptsWh3 and produces one, so without a base the predicate could be EMPTY and every step a theorem about nothing. No axiom ratchet detects that: an empty predicate has an empty axiom closure. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_ACCEPTS_BETA,
            "wh3_accepts_beta: NON-VACUITY, and the strong form — the three-way algorithm accepts a GENUINE CONVERSION between two syntactically different terms, not merely a term against itself. The left side is a beta-redex whose contractum is the right side; the loop fires beta, both sides land on the same sort, and level_eqb closes it. Fuel 3 is the minimum: the loop needs one layer to fire beta and one to see the contractum is stuck. \\
\\
wh3_accepts_sort_zero shows the predicate is inhabited; this shows it is inhabited for a REASON, which is the property a completeness theorem is actually about. \\
\\
MEASURED, and worth recording: the analogous DELTA witness computes to Bool.false at fuel 4, 6 and 8. def_eq_struct has no fast path for syntactically identical terms, so comparing an unfolded reflected value costs fuel proportional to its DEPTH — and reflected kernel values are deep enough that this environment already needs generated helper defs to stay under the parser's depth guard. Not a defect; a measurement. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_RIGID_APP_IS_STUCK,
            "wh3_rigid_app_is_stuck: the residual's DOMAIN is non-empty — a rigid-headed application really is stuck under the three-way step, by kernel computation. reduce_app_head_red_wh3 lifts a stuck head, and a sort head is stuck at any budget, so no pre-pass is consulted. \\
\\
This matters because hnf3_of_app_residual's premise is restricted to STUCK applications. A restriction that emptied the domain would make the premise trivially true and the theorem vacuous again — the same failure by the opposite route. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_HNF3_APP_RESIDUAL_OF_RIGID,
            "hnf3_app_residual_of_rigid: hnf3_of_app_residual's residual, SUPPLIED for every rigid-headed application — so the premise is satisfiable on a whole class, not just at a point. One constructor: rigid_app_head's own app arm already says a rigid head survives being applied, so nf_head.rigid closes it and both the stuckness and the shape equation go unused. \\
\\
That the hypotheses are unused is the POINT: it shows the rigid class needs neither. What is NOT covered, and why the const case is genuinely harder: nf_head.neutral wants iota_neutral f as well as iota_immune (app f a), and iota_neutral's own app arm recurses — so a const-headed spine needs immunity at EVERY PREFIX, not just at the whole term. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

const SRC_WH3_STUCK_AT: &str = "def wh3_stuck_at (j : Nat) (x : KExpr) : Prop := Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) x) WhStepR.wstuck";

const SRC_WH3RESULTSTUCK: &str = "inductive Wh3ResultStuck (r : KExpr) : Type
| mk : forall (k : Nat), wh3_stuck_at k r -> Wh3ResultStuck r";

const SRC_HNF_CONV3: &str = "def hnf_conv3 (j : Nat) (r : KExpr) : wh3_stuck_at j r -> (forall (zf : KExpr) (za : KExpr), Eq KExpr r (KExpr.app zf za) -> nf_head r) -> nf_head r := KExpr.rec (fun (x : KExpr) => Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) x) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr x (KExpr.app zf za) -> nf_head x) -> nf_head x) (fun (n : Level) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.sort n)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.sort n) (KExpr.app zf za) -> nf_head (KExpr.sort n)) => nf_head.rigid (KExpr.sort n) (rigid_app_head.sort n)) (fun (i : Nat) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.bvar i)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.bvar i) (KExpr.app zf za) -> nf_head (KExpr.bvar i)) => nf_head.bvar i) (fun (f : KExpr) (a : KExpr) (_c0 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) f) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr f (KExpr.app zf za) -> nf_head f) -> nf_head f) (_c1 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) a) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr a (KExpr.app zf za) -> nf_head a) -> nf_head a) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.app f a)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.app f a) (KExpr.app zf za) -> nf_head (KExpr.app f a)) => happ f a (Eq.refl KExpr (KExpr.app f a))) (fun (ty : KExpr) (b : KExpr) (_c0 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) ty) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr ty (KExpr.app zf za) -> nf_head ty) -> nf_head ty) (_c1 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) b) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr b (KExpr.app zf za) -> nf_head b) -> nf_head b) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.lam ty b)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.lam ty b) (KExpr.app zf za) -> nf_head (KExpr.lam ty b)) => nf_head.lam ty b) (fun (ty : KExpr) (b : KExpr) (_c0 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) ty) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr ty (KExpr.app zf za) -> nf_head ty) -> nf_head ty) (_c1 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) b) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr b (KExpr.app zf za) -> nf_head b) -> nf_head b) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.pi ty b)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.pi ty b) (KExpr.app zf za) -> nf_head (KExpr.pi ty b)) => nf_head.rigid (KExpr.pi ty b) (rigid_app_head.pi ty b)) (fun (n : Name) (us : ListType Level) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.const n us)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.const n us) (KExpr.app zf za) -> nf_head (KExpr.const n us)) => nf_head.constdead n us (delta_reduct_eq_none_of_defval_none (red_def the_red_env) (KExpr.const n us) n (Eq.refl (OptionType Name) (OptionType.some Name n)) (OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq WhStepR (opt_step_bind KExpr o WhStepR.wstuck (fun (v : KExpr) => WhStepR.wstep v)) WhStepR.wstuck -> Eq (OptionType KExpr) o (OptionType.none KExpr)) (fun (_hn : Eq WhStepR WhStepR.wstuck WhStepR.wstuck) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (dv : KExpr) (hsv : Eq WhStepR (WhStepR.wstep dv) WhStepR.wstuck) => wh_stuck_ne_step dv (Eq (OptionType KExpr) (OptionType.some KExpr dv) (OptionType.none KExpr)) (Eq.symm WhStepR (WhStepR.wstep dv) WhStepR.wstuck hsv)) (defval_for (red_def the_red_env) n) hstuck))) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c0 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) ty) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr ty (KExpr.app zf za) -> nf_head ty) -> nf_head ty) (_c1 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) v) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr v (KExpr.app zf za) -> nf_head v) -> nf_head v) (_c2 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) b) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr b (KExpr.app zf za) -> nf_head b) -> nf_head b) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.let_ ty v b)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.let_ ty v b) (KExpr.app zf za) -> nf_head (KExpr.let_ ty v b)) => wh_stuck_ne_step_type (instantiate b v) (nf_head (KExpr.let_ ty v b)) (Eq.symm WhStepR (WhStepR.wstep (instantiate b v)) WhStepR.wstuck hstuck)) (fun (s : Name) (i : Nat) (sub : KExpr) (_c0 : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) sub) WhStepR.wstuck -> (forall (zf : KExpr) (za : KExpr), Eq KExpr sub (KExpr.app zf za) -> nf_head sub) -> nf_head sub) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.proj s i sub)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.proj s i sub) (KExpr.app zf za) -> nf_head (KExpr.proj s i sub)) => nf_head.rigid (KExpr.proj s i sub) (rigid_app_head.proj s i sub)) (fun (v : Nat) (hstuck : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env j e2) (KExpr.lit v)) WhStepR.wstuck) (happ : forall (zf : KExpr) (za : KExpr), Eq KExpr (KExpr.lit v) (KExpr.app zf za) -> nf_head (KExpr.lit v)) => nf_head.rigid (KExpr.lit v) (rigid_app_head.lit v)) r";

const SRC_WHNF_FUEL_RED_WH3_RESULT_STUCK: &str = "def whnf_fuel_red_wh3_result_stuck (n : Nat) : forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env n e) (OptionType.some KExpr r) -> Wh3ResultStuck r := Nat.rec (fun (m : Nat) => forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env m e) (OptionType.some KExpr r) -> Wh3ResultStuck r) (fun (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env Nat.zero e) (OptionType.some KExpr r)) => option_none_ne_some_type KExpr r (Wh3ResultStuck r) h) (fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env k e0) (OptionType.some KExpr r0) -> Wh3ResultStuck r0) (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env (Nat.succ k) e) (OptionType.some KExpr r)) => WhStepR.rec (fun (o : WhStepR) => Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) o -> Eq (OptionType KExpr) (wh_dispatch3 o e (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (OptionType.some KExpr r) -> Wh3ResultStuck r) (fun (hq : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) WhStepR.wstuck) (h2 : Eq (OptionType KExpr) (wh_dispatch3 WhStepR.wstuck e (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (OptionType.some KExpr r)) => Eq.substType KExpr (fun (zz : KExpr) => Wh3ResultStuck zz) e r (option_some_inj KExpr e r h2) (Wh3ResultStuck.mk e k hq)) (fun (_hq : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) WhStepR.wstarved) (h2 : Eq (OptionType KExpr) (wh_dispatch3 WhStepR.wstarved e (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (OptionType.some KExpr r)) => option_none_ne_some_type KExpr r (Wh3ResultStuck r) h2) (fun (e2 : KExpr) (_hq : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) (WhStepR.wstep e2)) (h2 : Eq (OptionType KExpr) (wh_dispatch3 (WhStepR.wstep e2) e (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z)) (OptionType.some KExpr r)) => ih e2 r h2) (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e) (Eq.refl WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) e)) h) n";

const SRC_HNF3_OF_APP_RESIDUAL: &str = "def hnf3_of_app_residual (app_res : forall (r0 : KExpr) (k0 : Nat) (zf : KExpr) (za : KExpr), wh3_stuck_at k0 r0 -> Eq KExpr r0 (KExpr.app zf za) -> nf_head r0) : forall (m : Nat) (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env m e) (OptionType.some KExpr r) -> nf_head r := fun (m : Nat) (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red_wh3 the_red_env m e) (OptionType.some KExpr r)) => Wh3ResultStuck.rec r (fun (_w : Wh3ResultStuck r) => nf_head r) (fun (k : Nat) (hs : wh3_stuck_at k r) => hnf_conv3 k r hs (fun (zf : KExpr) (za : KExpr) (heq : Eq KExpr r (KExpr.app zf za)) => app_res r k zf za hs heq)) (whnf_fuel_red_wh3_result_stuck m e r h)";

const SRC_WH3_ACCEPTS_PI_SORT: &str = "def wh3_accepts_pi_sort : DefEqFuelAcceptsWh3 (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) := DefEqFuelAcceptsWh3.mk (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Eq.refl Bool Bool.true)";

const SRC_WH3_ACCEPTS_SORT_ZERO: &str = "def wh3_accepts_sort_zero : DefEqFuelAcceptsWh3 (KExpr.sort Level.zero) (KExpr.sort Level.zero) := DefEqFuelAcceptsWh3.mk (KExpr.sort Level.zero) (KExpr.sort Level.zero) (Nat.succ (Nat.succ Nat.zero)) (Eq.refl Bool Bool.true)";

const SRC_WH3_ACCEPTS_BETA: &str = "def wh3_accepts_beta : DefEqFuelAcceptsWh3 (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero) := DefEqFuelAcceptsWh3.mk (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Eq.refl Bool Bool.true)";

const SRC_WH3_RIGID_APP_IS_STUCK: &str = "def wh3_rigid_app_is_stuck : wh3_stuck_at Nat.zero (KExpr.app (KExpr.sort Level.zero) (KExpr.sort Level.zero)) := Eq.refl WhStepR WhStepR.wstuck";

const SRC_HNF3_APP_RESIDUAL_OF_RIGID: &str = "def hnf3_app_residual_of_rigid (r0 : KExpr) (k0 : Nat) (zf : KExpr) (za : KExpr) (hrig : rigid_app_head r0) (_hs : wh3_stuck_at k0 r0) (_heq : Eq KExpr r0 (KExpr.app zf za)) : nf_head r0 := nf_head.rigid r0 hrig";
