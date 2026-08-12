// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The major-premise whnf pre-pass — the fidelity gap, made executable.
//!
//! ```text
//! iota_reduct_wh        : RedEnv -> Nat -> KExpr -> OptionType KExpr
//! iota_reduct_stuck_here: iota_reduct (red_rec the_red_env) cx_stuck = none
//! iota_reduct_wh_fires  : iota_reduct_wh the_red_env 2 cx_stuck
//!                           = some kcre_witness_nat_zero_reduct
//! ```
//!
//! Two `Eq.refl`s on the same term, disagreeing. That is the whole point.
//!
//! # The gap
//!
//! The **deployed** kernel whnf-reduces a recursor's major premise before looking
//! up the constructor rule:
//!
//! * `crates/clean-kernel/src/micro/checker.rs:777` —
//!   `let major = self.whnf_impl(&args[major_idx])?;`
//! * `crates/clean-kernel/src/tc/whnf.rs:70-77` — with `cheap_rec = false`, which
//!   is the mode clean actually uses, "the major premise gets **full whnf**
//!   (including delta)". Matches Lean 4 `type_checker.cpp:340`.
//!
//! The **reflected** `iota_reduct` does not: its fourth `opt_bind` level is a bare
//! `kexpr_const_name (kapp_fn major)` (`iota_step.rs:127`), so a major premise that
//! is a β-redex — rather than literally constructor-headed — blocks ι forever.
//!
//! That gap is exactly why `hnf` is false (`hnf_is_false`,
//! `hnf_refutation.rs`) and why the def-eq completeness capstone and the eight
//! declarations sharing its premise are vacuous. It is also why
//! `wall_a_completeness.rs:356-357` can describe `iota_whnf` as "Faithful to the
//! real kernel's whnf results (major pre-pass)" while the reduction implements no
//! pre-pass at all: **the predicate and the reduction were built against different
//! specifications.**
//!
//! # Why this is additive rather than a repair in place
//!
//! Giving `iota_reduct` itself the pre-pass changes its signature twice over — it
//! needs a `RedEnv` (whnf reduces with δ, so `RecEnv` no longer suffices) and it
//! needs fuel (whnf is fuel-indexed). `iota_reduct` is mentioned **1,065 times
//! across 38 files** and sits under `iota_subst_commutes`,
//! `iota_reduct_some_inv`'s five-level CPS inversion, the E-core commutation and
//! most of the confluence development. Rewiring it in one step would put the whole
//! ι/δ layer in flight at once.
//!
//! So `iota_reduct_wh` is registered *beside* the original, changing no existing
//! declaration. What it buys immediately:
//!
//! 1. The divergence stops being an argument about two Rust files and becomes two
//!    `Eq.refl`s that the kernel evaluates over the real reflected environment.
//! 2. There is now a concrete migration target with the intended semantics
//!    written down and checked.
//! 3. If the pre-pass is ever ruled *out* instead — i.e. the model is declared
//!    correct and the kernel's pre-pass deemed an implementation detail — then
//!    `iota_whnf`'s fidelity claim is what must be edited, and this module is the
//!    evidence for that conversation.
//!
//! # The faithful loop
//!
//! `whnf_fuel_red_wh` and its three supporting definitions are the same loop with
//! the pre-pass wired in, each **derived from the shared source constant by one
//! explicit substitution** rather than re-typed. The load-bearing one is that the
//! loop passes `ih` — itself, at one less fuel — as the pre-pass, so the reduction
//! drills down a whole head spine instead of one level. That recursion is not
//! decoration: a one-level pre-pass still gets stuck on a recursor whose own major
//! premise is another recursor with a β-redex major, while the recursive one fires
//! the inner recursor first. Structurally decreasing on the fuel `Nat.rec`, so it
//! is an ordinary definition needing no termination argument.
//!
//! And the counterexample closes:
//!
//! ```text
//! reduce_once_red_stuck_here : reduce_once_red the_red_env cx_stuck = none
//! reduce_once_red_wh_fires   : reduce_once_red_wh the_red_env (whnf_fuel_red_wh …) cx_stuck
//!                                = some kcre_witness_nat_zero_reduct
//! ```
//!
//! `cx_stuck` **is** a whnf result under the current loop and is **not** one under
//! the faithful loop. Since `hnf` quantifies over whnf results and `cx_stuck` was
//! the term refuting it, the fix addresses the actual failure rather than an
//! adjacent one.
//!
//! # The foundation for classifying results
//!
//! `whnf_fuel_red_wh_no_redex` mirrors the original `whnf_fuel_red_no_redex` with
//! one forced change: the faithful loop steps with `reduce_once_red_wh renv ih`,
//! so the no-redex witness sits at a fuel level that **decreases** down the
//! recursion, and the honest conclusion is that *some* level witnesses it — stated
//! in CPS, since the fragment has no `Sigma`/`Exists`.
//!
//! `C` is a **parameter of the theorem**, not quantified inside the conclusion.
//! That is not style: `forall (C : Type), (… -> C) -> C` lives in `Sort 2`, and
//! nothing in the tree can discharge a `Sort 2` goal from `none = some r` —
//! `option_none_ne_some` targets a `Prop`, and `opt_none_ne_some_t` /
//! `option_none_ne_some_type` both fix `C : Type`. Hoisting `C` keeps everything
//! in `Sort 1` and follows `opt_bind_some_inv_t`'s precedent.
//!
//! # What this still does NOT do
//!
//! It does not prove `hnf` for the new loop. That is a statement about *all*
//! terms; the witnesses above are one term. What remains is a classifier for the
//! new loop — the current `whnf_fuel_red_classifies_at_result`,
//! `whnf_noredex_class_red` and `is_whnf_red` all assume the pre-pass-free reduct
//! — and then the permanence argument for `iota_immune`, which is where the real
//! mathematical content sits.
//!
//! Of `nf_head`'s cases only **one** is genuinely open. `lam` is immediate;
//! `sort`/`pi`/`lit`/`proj` and non-const-headed applications go through
//! `rigid_app_head`; a bare `const` is `nf_head.constdead` once δ-deadness is read
//! off the no-redex fact; and an application on a δ-dead **recmeta-free** const
//! head is already covered by `iota_immune_of_dead_const_head`
//! (`iota_immunity.rs`). The open case is an application on a δ-dead const head
//! that *does* carry recursor metadata — a stuck recursor.
//!
//! **Until that lands the capstone remains vacuous and must not be reported as a
//! result.**
//!
//! # Soundness must target `DefEq`, NOT `whnf_red_conv` — checked, not assumed
//!
//! The obvious next brick is "the faithful loop's result is convertible to its
//! input", mirroring `whnf_fuel_red_conv`. **That mirror does not exist**, and the
//! reason is structural rather than a gap in the development:
//!
//! `whnf_red_step` (`whnf_progress.rs:4236`) has congruence arms for `app_left`
//! and `proj` — and **no `app_right`**. It is a weak-head relation, so it cannot
//! relate two terms that differ inside an *argument*. But a recursor's major
//! premise *is* an argument, and reducing it is precisely what the pre-pass does.
//! Its `iota` arm also fires the original `iota_reduct`, not `iota_reduct_whc`.
//!
//! So `whnf_red_conv` cannot even state the faithful loop's soundness. The right
//! target is **`DefEq`**, which has `app_cong` along with `delta`, `iota` and
//! `zeta`:
//!
//! ```text
//! whnf_fuel_red_wh_defeq : whnf_fuel_red_wh the_red_env m e = some r -> DefEq e r
//! ```
//!
//! and the ι case factors as two `DefEq` steps rather than one reduction step —
//! `app_cong` to replace the major by its whnf, then `iota` on the resulting
//! genuinely-constructor-headed spine. `DefEq` is also what `def_eq_fuel_wh`'s
//! soundness actually needs, so nothing is lost by skipping the intermediary.
//!
//! Recording this because the mirror is the natural thing to try and it is
//! unprovable; discovering that by attempting it costs a validation cycle.
//!
//! `DerivedProved`, empty axiom closures.

use super::whnf_progress::{
    SRC_OPT_APP_ILIFT, SRC_REDUCE_APP_HEAD_RED, SRC_REDUCE_ONCE_RED, SRC_WHNF_FUEL_RED,
};
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// Spine position of the major premise: params + motives + minors + indices.
pub(super) const MAJOR_IDX: &str = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) \
     (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";

/// Arguments consumed before the indices: params + motives + minors.
const PREFIX_N: &str = "(Nat.add (Nat.add (recmeta_num_params meta) \
     (recmeta_num_motives meta)) (recmeta_num_minors meta))";

impl Specification {
    /// The pre-pass reduct, the whnf loop built on it, and the witnesses.
    pub(super) fn add_iota_prepass(&mut self) -> Result<(), SpecError> {
        self.add_iota_reduct_wh()?;
        self.add_prepass_whnf_chain()?;
        self.add_divergence_witnesses()?;
        self.add_prepass_iota_defeq()?;
        // ORDER: the boundary list lemmas must precede the minimal-spine facts,
        // which transport them. Registration is sequential, and getting this
        // backwards broke the whole spec build — see the test below.
        self.add_boundary_list_facts()?;
        self.add_minimal_spine_facts()?;
        self.add_step_defeq_bricks()?;
        self.add_whc_inverter()?;
        self.add_whc_recmeta_none()?;
        self.add_whc_reassembly()?;
        self.add_whc_no_major()?;
        self.add_whc_no_head()?;
        self.add_wh_no_redex()?;
        self.add_starvation_witness()?;
        self.add_monotonicity_refutation()?;
        self.add_three_way_step()?;
        Ok(())
    }

    /// The fuel artifact: the SAME term is stuck at fuel 1 and fires at fuel 2.
    ///
    /// This is not a curiosity. It shows `hnf` is false for the faithful loop
    /// too, and for a reason no amount of fidelity can fix.
    /// The THREE-WAY step result, and the ι chain rebuilt on it.
    ///
    /// The refutation above traces every pathology in this layer to one
    /// conflation: a single `none` means both "no rule applies" and "ran out of
    /// budget mid-decision". `iota_reduct_whc` binds the pre-pass with
    /// `opt_bind`, so a starved pre-pass is indistinguishable from ι declining,
    /// and `loop_dispatch` then reports the term as a normal form.
    ///
    /// Separating the two is the repair. `WhStepR` has `wstuck`, `wstarved` and
    /// `wstep`; a loop dispatching on it returns `some r` only when it genuinely
    /// finished, so more fuel can only turn `none` into `some` — never `some`
    /// into `none`, and never `some` into a DIFFERENT `some`. That is
    /// monotonicity by construction, rather than as a theorem that turns out to
    /// be false.
    ///
    /// The chain itself is DERIVED from `whc_chain` by substitution, so the
    /// three-way version cannot drift from the two-way one: each `opt_bind`
    /// becomes an `opt_step_bind` with a default, and exactly ONE of those
    /// defaults is `wstarved` — the pre-pass level. That single asymmetry is the
    /// entire semantic content of the change.
    fn add_three_way_step(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive WhStepR : Type\n             | wstuck : WhStepR\n             | wstarved : WhStepR\n             | wstep : KExpr -> WhStepR",
            "WhStepR: the step's result, three ways rather than two. wstuck means no rule applies \
             at any budget; wstarved means the decision itself ran out of fuel; wstep carries the \
             reduct. The two-way version conflates the first two, which is the root cause of false \
             stucks, of hnf's falsity, and of the non-monotonicity refuted just above. \
             Census-neutral.",
        )?;
        self.add_recursive_def(
            "def opt_step_bind (A : Type) (o : OptionType A) (d : WhStepR) \
             (f : A -> WhStepR) : WhStepR := \
             OptionType.rec A (fun (_o : OptionType A) => WhStepR) d f o",
            "opt_step_bind: opt_bind, but the failure branch is CHOSEN rather than fixed. Every \
             level of the iota chain supplies wstuck except the pre-pass level, which supplies \
             wstarved — and that one choice is the whole difference between a loop that lies about \
             normal forms and one that does not. DerivedProved, zero axiom_deps.",
        )?;
        self.add_whc3_chain()?;
        self.add_three_way_loop()?;
        self.add_three_way_witnesses()?;
        self.add_wh_step_no_confusion()?;
        // LAST: consumes opt_step_bind and both wh_*_ne_step families registered
        // above. Registration is sequential, so ordering this ahead of them
        // fails at elaboration 26 minutes later; and nothing consumes it, so a
        // rejection here cannot mask anything earlier.
        self.add_whc3_inverter()?;
        Ok(())
    }

    /// `WhStepR` discriminators and no-confusion, in both universes.
    ///
    /// The three constructors have to be provably distinct before any convoy on
    /// a step result can discharge its impossible arms. The construction is the
    /// one `option_none_ne_some` uses: a discriminator sending ONE constructor
    /// to an inhabited type and the rest to `Empty`, transported along the false
    /// equation.
    ///
    /// Both universes are emitted because both are needed and the kernel is
    /// non-cumulative. A convoy on a step result has arms concluding in `Eq`
    /// (the stability lemmas) and arms concluding in `Empty` or a relation. A
    /// `Type`-valued conclusion parameter cannot be instantiated at an `Eq`
    /// goal, so a single form would leave half the call sites unserved — which
    /// is exactly how the CPS inverter came to be unusable by every equational
    /// caller earlier in this development.
    fn add_wh_step_no_confusion(&mut self) -> Result<(), SpecError> {
        for (name, stuck, starved, step) in [
            ("wh_is_stuck", "Nat", "Empty", "Empty"),
            ("wh_is_starved", "Empty", "Nat", "Empty"),
            ("wh_is_step", "Empty", "Empty", "Nat"),
        ] {
            let src = format!(
                "def {name} (o : WhStepR) : Type := \
                 WhStepR.rec (fun (_o : WhStepR) => Type) {stuck} {starved} \
                 (fun (_e : KExpr) => {step}) o"
            );
            debug_assert!(Self::balanced(&src), "{name} parens");
            self.add_recursive_def(
                &src,
                &format!(
                    "{name}: the discriminator that separates one WhStepR constructor from the \
                     other two — inhabited on its own case, Empty elsewhere. The standard \
                     no-confusion device, as opt_is_none is for OptionType. DerivedProved, zero \
                     axiom_deps."
                ),
            )?;
        }

        for (lo, hi, l, r, disc, binder) in [
            (
                "stuck",
                "starved",
                "WhStepR.wstuck",
                "WhStepR.wstarved",
                "wh_is_stuck",
                "",
            ),
            (
                "stuck",
                "step",
                "WhStepR.wstuck",
                "(WhStepR.wstep e2)",
                "wh_is_stuck",
                "(e2 : KExpr) ",
            ),
            (
                "starved",
                "step",
                "WhStepR.wstarved",
                "(WhStepR.wstep e2)",
                "wh_is_starved",
                "(e2 : KExpr) ",
            ),
        ] {
            for (suffix, univ) in [("_type", "Type"), ("", "Prop")] {
                let name = format!("wh_{lo}_ne_{hi}{suffix}");
                let src = format!(
                    "def {name} {binder}(C : {univ}) (h : Eq WhStepR {l} {r}) : C := \
                     Empty.rec (fun (_ : Empty) => C) \
                     (Eq.substType WhStepR {disc} {l} {r} h Nat.zero)"
                );
                debug_assert!(Self::balanced(&src), "{name} parens");
                self.add_recursive_def(
                    &src,
                    &format!(
                        "{name}: WhStepR no-confusion, {lo} is not {hi}, concluding at C : {univ}. \
                         Transport the discriminator along the false equation to reach Empty. \
                         Emitted at both universes because a convoy on a step result has arms \
                         concluding in Eq and arms concluding in Empty, and this kernel is \
                         non-cumulative. DerivedProved, zero axiom_deps."
                    ),
                )?;
            }
        }
        Ok(())
    }

    /// The repair, checked on the term that refuted the original.
    ///
    /// `whnf_fuel_red_wh_monotone_is_false` turns on two computations:
    /// the two-way loop returns `some D` at fuel 1 — a FALSE STUCK, since the
    /// pre-pass was merely starved — and `none` at fuel 2, once ι fires and
    /// leaves too little fuel to finish. That `some → none` flip is the
    /// refutation.
    ///
    /// On the same term the three-way loop returns `none` at both. The false
    /// stuck is gone at its source, and with it the flip. These are regression
    /// witnesses: if a later edit reintroduces the conflation, they stop
    /// elaborating.
    ///
    /// This is evidence the design is right, NOT a proof that the new loop is
    /// monotone. That still has to be proved, and the proof reduces to step
    /// stability — see the note on `whnf_fuel_red_wh3`.
    fn add_three_way_witnesses(&mut self) -> Result<(), SpecError> {
        let o = "OptionType KExpr";
        let d = "kcre_witness_nat_zero_redex";
        for (name, fuel, term, why) in [
            (
                "wh3_no_false_stuck",
                "(Nat.succ Nat.zero)",
                d,
                "where the two-way loop announces a false stuck (wh_redex_false_stuck returns the                  term itself), the three-way loop reports honest exhaustion",
            ),
            (
                "wh3_no_flip",
                "(Nat.succ (Nat.succ Nat.zero))",
                d,
                "and at the next budget it is still none, so the some-to-none flip that refutes                  two-way monotonicity does not occur",
            ),
            (
                "wh3_cx_stuck_honest",
                "(Nat.succ Nat.zero)",
                "cx_stuck",
                "the same on cx_stuck, which the two-way loop returns unchanged at budgets 1 and                  2 — the behaviour that makes hnf false",
            ),
        ] {
            let src = format!(
                "def {name} : Eq ({o}) (whnf_fuel_red_wh3 the_red_env {fuel} {term}) \
                 (OptionType.none KExpr) := Eq.refl ({o}) (OptionType.none KExpr)"
            );
            debug_assert!(Self::balanced(&src), "{name} parens");
            self.add_recursive_def(
                &src,
                &format!(
                    "{name}: pure computation over the real reduction environment — {why}. A                      REGRESSION WITNESS: if the starved/stuck distinction is ever collapsed again                      this stops elaborating. DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }

    /// The loop itself, on the three-way step.
    ///
    /// Mirrors the two-way definitions arm for arm. The only places the extra
    /// case does any work are the three that can propagate it: `opt_app_ilift3`
    /// passes starvation outward instead of swallowing it, `proj` passes it up
    /// from its subterm, and the dispatch turns it into `none` rather than into
    /// a false claim of normality.
    fn add_three_way_loop(&mut self) -> Result<(), SpecError> {
        let o = "OptionType KExpr";
        // Dispatch: a genuine normal form yields the term, exhaustion yields
        // none, a real step continues. This is the whole monotonicity argument.
        self.add_recursive_def(
            &format!(
                "def wh_dispatch3 (o : WhStepR) (e0 : KExpr) (ih : KExpr -> {o}) : {o} := \
                 WhStepR.rec (fun (_o : WhStepR) => {o}) (OptionType.some KExpr e0) \
                 (OptionType.none KExpr) (fun (e2 : KExpr) => ih e2) o"
            ),
            "wh_dispatch3: the loop's dispatch on a three-way step. wstuck yields the term, which \
             is now an honest claim of normality; wstarved yields none, honest exhaustion; wstep \
             continues. The two-way dispatch cannot distinguish the first two and so returns the \
             term in both cases — that is the false stuck, in one line. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def opt_app_ilift3 (renv : RedEnv) (wh : KExpr -> {o}) (f : KExpr) (a : KExpr) \
                 (cf : WhStepR) : WhStepR := \
                 WhStepR.rec (fun (_o : WhStepR) => WhStepR) \
                 (iota_reduct_whc3 (red_rec renv) wh (KExpr.app f a)) \
                 WhStepR.wstarved \
                 (fun (f2 : KExpr) => WhStepR.wstep (KExpr.app f2 a)) cf"
            ),
            "opt_app_ilift3: a stuck head reaches for iota, a STARVED head propagates outward \
             rather than being mistaken for a stuck one, and a reduced head takes the congruence. \
             The middle arm is the one the two-way version cannot express. DerivedProved, zero \
             axiom_deps.",
        )?;

        let lam_beta = "WhStepR.wstep (instantiate b a)";
        let ilift = "opt_app_ilift3 renv wh f a cf";
        let arms = [
            format!("(fun (n : Level) => {ilift})"),
            format!("(fun (i : Nat) => {ilift})"),
            format!("(fun (g : KExpr) (b : KExpr) (_cg : WhStepR) (_cb : WhStepR) => {ilift})"),
            format!("(fun (ty : KExpr) (b : KExpr) (_cty : WhStepR) (_cb : WhStepR) => {lam_beta})"),
            format!("(fun (ty : KExpr) (b : KExpr) (_cty : WhStepR) (_cb : WhStepR) => {ilift})"),
            format!("(fun (n : Name) (us : ListType Level) => {ilift})"),
            format!(
                "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : WhStepR) (_c2 : WhStepR) (_c3 : WhStepR) \
                 => {ilift})"
            ),
            format!("(fun (s : Name) (i : Nat) (sub : KExpr) (_csub : WhStepR) => {ilift})"),
            format!("(fun (v : Nat) => {ilift})"),
        ];
        self.add_recursive_def(
            &format!(
                "def reduce_app_head_red_wh3 (renv : RedEnv) (wh : KExpr -> {o}) (a : KExpr) \
                 (f : KExpr) (cf : WhStepR) : WhStepR := \
                 KExpr.rec (fun (_e : KExpr) => WhStepR) {arms} f",
                arms = arms.join(" "),
            ),
            "reduce_app_head_red_wh3: beta at a lambda head, ilift everywhere else — the same \
             nine-arm split as the two-way version, with the results retyped. DerivedProved, zero \
             axiom_deps.",
        )?;

        let step_arms = [
            "(fun (n : Level) => WhStepR.wstuck)",
            "(fun (i : Nat) => WhStepR.wstuck)",
            "(fun (f : KExpr) (a : KExpr) (cf : WhStepR) (_ca : WhStepR) => \
                 reduce_app_head_red_wh3 renv wh a f cf)",
            "(fun (ty : KExpr) (b : KExpr) (_cty : WhStepR) (_cb : WhStepR) => WhStepR.wstuck)",
            "(fun (ty : KExpr) (b : KExpr) (_cty : WhStepR) (_cb : WhStepR) => WhStepR.wstuck)",
            "(fun (n : Name) (us : ListType Level) => opt_step_bind KExpr \
                 (defval_for (red_def renv) n) WhStepR.wstuck (fun (v : KExpr) => WhStepR.wstep v))",
            "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : WhStepR) (_c2 : WhStepR) (_c3 : WhStepR) \
                 => WhStepR.wstep (instantiate b v))",
            // proj carries starvation up from its subterm rather than losing it
            "(fun (s : Name) (i : Nat) (sub : KExpr) (csub : WhStepR) => \
                 WhStepR.rec (fun (_o : WhStepR) => WhStepR) WhStepR.wstuck WhStepR.wstarved \
                 (fun (sub2 : KExpr) => WhStepR.wstep (KExpr.proj s i sub2)) csub)",
            "(fun (v : Nat) => WhStepR.wstuck)",
        ];
        self.add_recursive_def(
            &format!(
                "def reduce_once_red_wh3 (renv : RedEnv) (wh : KExpr -> {o}) (e : KExpr) : WhStepR := \
                 KExpr.rec (fun (_e : KExpr) => WhStepR) {arms} e",
                arms = step_arms.join(" "),
            ),
            "reduce_once_red_wh3: one executable step, reporting WHY it stopped. Five shapes are \
             genuinely stuck; const consults its value; let_ contracts; app delegates; and proj \
             carries starvation UP from its subterm instead of losing it, which is the one arm \
             where the extra case does real work outside the application spine. DerivedProved, \
             zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def whnf_fuel_red_wh3 (renv : RedEnv) (fuel : Nat) (e : KExpr) : {o} := \
                 Nat.rec (fun (_n : Nat) => KExpr -> {o}) (fun (_e0 : KExpr) => \
                 OptionType.none KExpr) (fun (k : Nat) (ih : KExpr -> {o}) (e0 : KExpr) => \
                 wh_dispatch3 (reduce_once_red_wh3 renv ih e0) e0 ih) fuel e"
            ),
            "whnf_fuel_red_wh3: the faithful loop, on the three-way step. Same shape as \
             whnf_fuel_red_wh — the loop at one less fuel serves as its own pre-pass — but it now \
             returns some r ONLY when the step reported genuine stuckness. Exhaustion returns \
             none instead of a term. \
             \
             That is what should make it monotone: more fuel can turn none into some, and cannot \
             turn some into none or into a different some, because a some is only ever produced \
             at a point where no rule applies at any budget. The refutation \
             whnf_fuel_red_wh_monotone_is_false applies to the TWO-way loop and should not \
             transfer — establishing that for this loop is the next obligation, and it must be \
             PROVED rather than assumed. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The ι chain, three ways.
    ///
    /// Built level-for-level against `whc_chain`, with every `opt_bind` becoming
    /// an `opt_step_bind` carrying a default. Five levels default to `wstuck`;
    /// the pre-pass level defaults to `wstarved`. That one asymmetry is the
    /// whole change — a starved pre-pass now says so, instead of being
    /// indistinguishable from ι having nothing to do.
    /// The six continuation levels of `iota_reduct_whc3`'s `opt_step_bind` chain,
    /// built in ONE place — the three-way twin of `whc_chain`.
    ///
    /// Shared by the chain and its inverter. A six-level CPS inversion cannot
    /// survive its subject drifting out from under it, and re-transcribing the
    /// layers is exactly how that happens; `whc_chain` exists for the same
    /// reason on the two-way side.
    ///
    /// No `recname` parameter, unlike `whc_chain`: every reader of the three-way
    /// chain binds the recursor name with `l2`'s own lambda.
    pub(super) fn whc3_layers() -> [String; 6] {
        let mi = MAJOR_IDX;
        let reduct = Self::whc_reduct();
        // Innermost first, mirroring whc_chain exactly.
        let l7 = format!("(fun (rule : RecRule) => WhStepR.wstep {reduct})");
        let l6 = format!(
            "(fun (cname : Name) => opt_step_bind RecRule \
             (recrule_for env recname cname) WhStepR.wstuck {l7})"
        );
        let l5 = format!(
            "(fun (wmajor : KExpr) => opt_step_bind Name \
             (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck {l6})"
        );
        // THE ONE ASYMMETRY: a starved pre-pass is reported, not swallowed.
        let l4 = format!(
            "(fun (major : KExpr) => opt_step_bind KExpr (wh major) WhStepR.wstarved {l5})"
        );
        let l3 = format!(
            "(fun (meta : RecMeta) => opt_step_bind KExpr \
             (list_head (list_drop {mi} (kapp_args e))) WhStepR.wstuck {l4})"
        );
        let l2 = format!(
            "(fun (recname : Name) => opt_step_bind RecMeta \
             (recmeta_for env recname) WhStepR.wstuck {l3})"
        );
        [l2, l3, l4, l5, l6, l7]
    }

    fn add_whc3_chain(&mut self) -> Result<(), SpecError> {
        let [l2, _l3, _l4, _l5, _l6, _l7] = Self::whc3_layers();
        let src = format!(
            "def iota_reduct_whc3 (env : RecEnv) (wh : KExpr -> OptionType KExpr) (e : KExpr) : \
             WhStepR := opt_step_bind Name (kexpr_const_name (kapp_fn e)) WhStepR.wstuck {l2}"
        );
        debug_assert!(Self::balanced(&src), "whc3 parens");
        debug_assert_eq!(
            src.matches("WhStepR.wstarved").count(),
            1,
            "exactly ONE level may report starvation, and it must be the pre-pass"
        );
        debug_assert_eq!(
            src.matches("WhStepR.wstuck").count(),
            5,
            "the other five levels fail as genuinely stuck"
        );
        self.add_recursive_def(
            &src,
            "iota_reduct_whc3: the iota chain, reporting WHY it declined. Level-for-level against \
             iota_reduct_whc, with each opt_bind replaced by opt_step_bind and a default. Five \
             levels default to wstuck — no head name, no metadata, no major premise, a \
             non-constructor major, no matching rule — and exactly ONE, the pre-pass, defaults to \
             wstarved. \
             \
             That single asymmetry is the entire semantic content of the repair. In the two-way \
             chain a starved pre-pass short-circuits to none and is indistinguishable from iota \
             having nothing to do, so the loop announces a false stuck; here it says so, and a \
             loop dispatching on the result can return none rather than lying about a normal \
             form. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// FUEL MONOTONICITY OF THE FAITHFUL LOOP IS FALSE — refuted, not deferred.
    ///
    /// `whnf_fuel_red` is monotone (`whnf_fuel_red_monotone`): a successful run
    /// survives more fuel. The faithful loop is **not**, and the failure is
    /// worse than the one `whnf_fuel_red_wh_starves` already records. That
    /// witness shows more budget can CHANGE the answer. These show more budget
    /// can DESTROY it.
    ///
    /// At budget 1 the pre-pass is starved, ι declines, and the loop announces
    /// the redex as a normal form. At budget 2 the pre-pass succeeds, ι FIRES —
    /// and the loop must now normalise the reduct with one unit less fuel than
    /// it just spent reaching it. The reduct is a three-fold lambda applied to
    /// three arguments, so it does not fit. The loop returns `none`.
    ///
    /// `some` at one budget, `none` at the next.
    ///
    /// This is why the completeness chain cannot simply be ported. Four of its
    /// layers close a step with `whnf_fuel_red_monotone`, and no faithful
    /// analogue can exist. It is not that the port is hard — the lemma it needs
    /// is false. Recording it as a refutation rather than an open item is the
    /// same discipline `hnf_is_false` applies: an unproved-but-true statement
    /// and a false one call for completely different work.
    fn add_monotonicity_refutation(&mut self) -> Result<(), SpecError> {
        let o = "OptionType KExpr";
        let d = "kcre_witness_nat_zero_redex";
        for (name, fuel, rhs, why) in [
            (
                "wh_redex_false_stuck",
                "(Nat.succ Nat.zero)",
                format!("(OptionType.some KExpr {d})"),
                "at budget 1 the pre-pass is starved, so iota declines and the loop announces the                  redex as its own normal form",
            ),
            (
                "wh_redex_collapses",
                "(Nat.succ (Nat.succ Nat.zero))",
                "(OptionType.none KExpr)".to_string(),
                "at budget 2 the pre-pass succeeds and iota FIRES, leaving too little fuel to                  normalise the reduct — so the loop returns none, having returned some at the                  smaller budget",
            ),
            (
                "wh_cx_stuck_collapses",
                "(Nat.succ (Nat.succ (Nat.succ Nat.zero)))",
                "(OptionType.none KExpr)".to_string(),
                "the same collapse one wrapper further out, on the counterexample cx_stuck that                  already refutes hnf",
            ),
        ] {
            let term = if name == "wh_cx_stuck_collapses" { "cx_stuck" } else { d };
            let src = format!(
                "def {name} : Eq ({o}) (whnf_fuel_red_wh the_red_env {fuel} {term}) {rhs} :=                  Eq.refl ({o}) {rhs}"
            );
            debug_assert!(Self::balanced(&src), "{name} parens");
            self.add_recursive_def(
                &src,
                &format!(
                    "{name}: pure computation over the real reduction environment — {why}.                      DerivedProved, zero axiom_deps."
                ),
            )?;
        }

        // The refutation proper: assume the lemma the port would need, derive Empty.
        let mono = format!(
            "forall (fuel : Nat) (e : KExpr) (r : KExpr), Eq ({o}) \
             (whnf_fuel_red_wh the_red_env fuel e) (OptionType.some KExpr r) -> Eq ({o}) \
             (whnf_fuel_red_wh the_red_env (Nat.succ fuel) e) (OptionType.some KExpr r)"
        );
        let src = format!(
            "def whnf_fuel_red_wh_monotone_is_false (mono : {mono}) : Empty := \
             option_none_ne_some_type KExpr {d} Empty \
             (Eq.trans ({o}) (OptionType.none KExpr) \
             (whnf_fuel_red_wh the_red_env (Nat.succ (Nat.succ Nat.zero)) {d}) \
             (OptionType.some KExpr {d}) \
             (Eq.symm ({o}) \
             (whnf_fuel_red_wh the_red_env (Nat.succ (Nat.succ Nat.zero)) {d}) \
             (OptionType.none KExpr) wh_redex_collapses) \
             (mono (Nat.succ Nat.zero) {d} {d} wh_redex_false_stuck))"
        );
        debug_assert!(Self::balanced(&src), "monotonicity refutation parens");
        self.add_recursive_def(
            &src,
            "whnf_fuel_red_wh_monotone_is_false: THE REFUTATION — fuel monotonicity for the              faithful loop is FALSE, so no faithful analogue of whnf_fuel_red_monotone can be              written.                           Instantiate the hypothetical lemma at budget 1 on the generated Nat.rec redex, which              the loop returns unchanged there (wh_redex_false_stuck), to obtain a some at budget              2 — where the loop in fact returns none (wh_redex_collapses). Both endpoints are              Eq.refl computations over the real reduction environment, so this is settled by the              kernel rather than argued.                           CONSEQUENCE for the completeness capstone: defeq_fuel_mono, half of fuel_pairing,              defeq_complete_steps and defeq_capstone each close a step with whnf_fuel_red_monotone              applied to both whnf legs. Those layers are blocked not by difficulty but by              falsity, and porting them cannot work. The conversion algorithm's fuel discipline              has to change, or the completeness argument has to stop raising two independently              obtained fuels to a common bound. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_starvation_witness(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def whnf_fuel_red_wh_starves : Eq (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env (Nat.succ Nat.zero) cx_stuck) \
             (OptionType.some KExpr cx_stuck) := \
             Eq.refl (OptionType KExpr) (OptionType.some KExpr cx_stuck)",
            "whnf_fuel_red_wh_starves: THE FUEL ARTIFACT, and it is bad news for hnf. \
             \
             At fuel 1 the faithful loop returns cx_stuck UNCHANGED — the same term that \
             reduce_once_red_wh_fires shows it reduces at fuel 2. The reason is structural: the \
             loop's pre-pass is the loop at ONE LESS fuel, and whnf_fuel_red_wh renv Nat.zero \
             returns none for EVERY term (SRC_WHNF_FUEL_RED's zero arm). So the pre-pass \
             short-circuits, iota_reduct_whc's fourth opt_bind level yields none, and iota cannot \
             fire — not because the term is stuck, but because the budget ran out. \
             \
             CONSEQUENCE: hnf is FALSE for the faithful loop as well, and no improvement in \
             fidelity can repair it. cx_stuck IS a whnf_fuel_red_wh result (at fuel 1) and it has \
             no normal-form head — exactly the shape of hnf_is_false, now driven by fuel \
             exhaustion rather than by the missing pre-pass. A fuel-indexed whnf manufactures \
             spurious stuck results at every insufficient budget, so `whnf returns r` can never on \
             its own imply that r is permanently iota-dead. \
             \
             What this rules OUT is the naive statement, not the goal. hnf must carry a \
             CONVERGENCE hypothesis — that the result is stable under more fuel, or that the term \
             genuinely normalises (the rbelow_plus_acc accessibility the capstone already \
             carries for exactly this kind of reason). Discovering that the missing hypothesis is \
             convergence rather than fidelity is the substantive result of this increment. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The faithful loop at fuel `j`, eta-expanded — the form the recursor's own
    /// induction hypothesis takes.
    ///
    /// The binder name is a parameter because the `some` arm of the convoy
    /// `OptionType.rec` already binds `e2`; the original proof renames to `e3`
    /// there (`whnf_progress.rs`), and mirroring it exactly is the whole point of
    /// mirroring.
    fn wh_at_named(j: &str, binder: &str) -> String {
        format!("(fun ({binder} : KExpr) => whnf_fuel_red_wh renv {j} {binder})")
    }

    fn wh_at(j: &str) -> String {
        Self::wh_at_named(j, "e2")
    }

    /// `whnf_fuel_red_wh_no_redex` — the foundation for everything downstream.
    ///
    /// The original `whnf_fuel_red_no_redex` (`whnf_progress.rs:712`) concludes
    /// `reduce_once_red renv r = none` outright, because its step function takes
    /// no continuation. The faithful loop's does: at fuel `succ k` it steps with
    /// `reduce_once_red_wh renv ih`, where `ih` is the loop itself at fuel `k`.
    /// So the "no redex" witness for a result sits at a fuel level that
    /// **decreases** as the recursion descends, and the honest conclusion is
    /// therefore existential: *some* level witnesses it.
    ///
    /// The reflected fragment has no `Sigma`/`Exists`, so that existential is
    /// stated in CPS — the same idiom the rest of this development uses for
    /// inversions. Everything else mirrors the original proof exactly, which is
    /// deliberate: that proof is known to typecheck, so any rejection here
    /// isolates to the continuation change rather than to the induction.
    fn wh_no_redex_src() -> String {
        let no_redex_at = |j: &str, term: &str| {
            format!(
                "Eq (OptionType KExpr) (reduce_once_red_wh renv {} {term}) (OptionType.none KExpr)",
                Self::wh_at(j)
            )
        };
        // The CPS conclusion: some fuel level witnesses that `t` is stuck.
        //
        // `C` is a PARAMETER of the whole theorem, not quantified inside the
        // conclusion. Writing `forall (C : Type), (… -> C) -> C` would put the
        // statement in `Sort 2`, and then nothing can discharge the base arm:
        // `option_none_ne_some` targets a `Prop` and `opt_none_ne_some_t` /
        // `option_none_ne_some_type` both fix `C : Type` — there is no
        // `Sort 2`-targeted option no-confusion in the tree. Hoisting `C` keeps
        // everything in `Sort 1`, and follows `opt_bind_some_inv_t`'s precedent.
        let stuck = |t: &str| format!("(forall (j : Nat), {} -> C) -> C", no_redex_at("j", t));
        let motive = format!(
            "(fun (n : Nat) => forall (e : KExpr) (r : KExpr), \
             Eq (OptionType KExpr) (whnf_fuel_red_wh renv n e) (OptionType.some KExpr r) -> {})",
            stuck("r")
        );
        let src = format!(
            "def whnf_fuel_red_wh_no_redex (renv : RedEnv) (fuel : Nat) (C : Type) : \
             forall (e : KExpr) (r : KExpr), \
             Eq (OptionType KExpr) (whnf_fuel_red_wh renv fuel e) (OptionType.some KExpr r) -> {goal} := \
             Nat.rec {motive} \
             (fun (e : KExpr) (r : KExpr) \
             (h : Eq (OptionType KExpr) (whnf_fuel_red_wh renv Nat.zero e) \
             (OptionType.some KExpr r)) => \
             opt_none_ne_some_t KExpr r ({goal_r}) h) \
             (fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), \
             Eq (OptionType KExpr) (whnf_fuel_red_wh renv k e0) (OptionType.some KExpr r0) -> {goal_r0}) \
             (e : KExpr) (r : KExpr) \
             (h : Eq (OptionType KExpr) (whnf_fuel_red_wh renv (Nat.succ k) e) \
             (OptionType.some KExpr r)) => \
             OptionType.rec KExpr \
             (fun (o : OptionType KExpr) => \
             Eq (OptionType KExpr) (reduce_once_red_wh renv {whk} e) o -> \
             Eq (OptionType KExpr) (loop_dispatch o e {whk}) (OptionType.some KExpr r) -> {goal_r}) \
             (fun (heq : {heq_ty}) \
             (h2 : Eq (OptionType KExpr) \
             (loop_dispatch (OptionType.none KExpr) e {whk}) (OptionType.some KExpr r)) \
             (kk : forall (j : Nat), {no_redex_j_r} -> C) => \
             kk k (Eq.rec KExpr e \
             (fun (x : KExpr) (_hx : Eq KExpr e x) => {no_redex_k_x}) \
             heq r (option_some_inj KExpr e r h2))) \
             (fun (e2 : KExpr) \
             (_heq : Eq (OptionType KExpr) (reduce_once_red_wh renv {whk} e) \
             (OptionType.some KExpr e2)) \
             (h2 : Eq (OptionType KExpr) \
             (loop_dispatch (OptionType.some KExpr e2) e {whk3}) (OptionType.some KExpr r)) => \
             ih e2 r h2) \
             (reduce_once_red_wh renv {whk} e) \
             (Eq.refl (OptionType KExpr) (reduce_once_red_wh renv {whk} e)) h) \
             fuel",
            goal = stuck("r"),
            goal_r = stuck("r"),
            goal_r0 = stuck("r0"),
            whk = Self::wh_at("k"),
            whk3 = Self::wh_at_named("k", "e3"),
            heq_ty = no_redex_at("k", "e"),
            no_redex_j_r = no_redex_at("j", "r"),
            no_redex_k_x = no_redex_at("k", "x"),
        );
        src
    }

    /// The six-level CPS inverter for `iota_reduct_whc`.
    ///
    /// Mirrors `iota_reduct_some_inv_type` (`par_reduces_c.rs`) with the one extra
    /// `opt_bind` level the pre-pass adds, and recovers the same five witnesses
    /// plus `wmajor` and the equation `wh major = some wmajor`.
    ///
    /// This is the brick every soundness argument for the faithful loop needs.
    /// The intended use: `h4` says `wmajor` is constructor-headed, so the spine
    /// with `wmajor` in the major slot is a genuine ι-redex, and `hw` says the
    /// original major reduces to it — which is exactly the two `DefEq` steps
    /// (`app_cong` then `iota`) the soundness proof factors through.
    /// Paren balance — the cheapest possible guard, and the one this module
    /// forgot. An unbalanced source is a PARSE error, which aborts the whole spec
    /// build before a single declaration is checked: 26 minutes to learn that six
    /// nested lambdas were closed five times.
    pub(super) fn balanced(src: &str) -> bool {
        let mut depth: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            if depth < 0 {
                return false;
            }
        }
        depth == 0
    }

    /// The three positional facts that connect the pre-pass's firing condition to
    /// a plain ι on the swapped spine — the obligation `defeq_of_prepass_iota`
    /// isolated.
    ///
    /// All three are the same move: transport a boundary list fact along the
    /// spine-length equation. Validated first in the scratchpad
    /// (`tests/spec_scratchpad.rs`), which elaborated all three against one spec
    /// build instead of three 26-minute cycles.
    fn add_minimal_spine_facts(&mut self) -> Result<(), SpecError> {
        let mi = MAJOR_IDX;
        let pre = PREFIX_N;
        self.add_recursive_def(
            &format!(
                "def minimal_major_is_last (meta : RecMeta) (f : KExpr) (wmajor : KExpr) \
                 (hlen : Eq Nat (list_length (kapp_args f)) {mi}) : \
                 Eq (OptionType KExpr) \
                 (list_head (list_drop {mi} (kapp_args (KExpr.app f wmajor)))) \
                 (OptionType.some KExpr wmajor) := \
                 Eq.substType Nat (fun (z : Nat) => Eq (OptionType KExpr) \
                 (list_head (list_drop z (kapp_args (KExpr.app f wmajor)))) \
                 (OptionType.some KExpr wmajor)) \
                 (list_length (kapp_args f)) {mi} hlen \
                 (list_head_drop_len_append (kapp_args f) wmajor)"
            ),
            "minimal_major_is_last: for a spine carrying exactly major_idx arguments, the \
             major-premise slot holds the LAST argument. Transport list_head_drop_len_append \
             along the length equation. This is what lets iota_reduct's third lookup be \
             discharged without any positional search. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            &format!(
                "def minimal_suffix_nil (meta : RecMeta) (f : KExpr) (x : KExpr) \
                 (hlen : Eq Nat (list_length (kapp_args f)) {mi}) : \
                 Eq (ListType KExpr) \
                 (list_drop (Nat.succ {mi}) (kapp_args (KExpr.app f x))) (ListType.nil KExpr) := \
                 Eq.substType Nat (fun (z : Nat) => Eq (ListType KExpr) \
                 (list_drop (Nat.succ z) (kapp_args (KExpr.app f x))) (ListType.nil KExpr)) \
                 (list_length (kapp_args f)) {mi} hlen \
                 (list_drop_succ_len_append x (kapp_args f))"
            ),
            "minimal_suffix_nil: nothing follows the major premise in a minimally fully-applied \
             spine — so iota_reduct's reduct formula has an EMPTY outer apply_spine, and the two \
             reducts (pre-pass side and plain side) coincide there. DerivedProved, zero \
             axiom_deps.",
        )?;
        self.add_recursive_def(
            &format!(
                "def minimal_prefix_is_args (meta : RecMeta) (f : KExpr) (x : KExpr) \
                 (hlen : Eq Nat (list_length (kapp_args f)) {pre}) : \
                 Eq (ListType KExpr) \
                 (list_take {pre} (kapp_args (KExpr.app f x))) (kapp_args f) := \
                 Eq.substType Nat (fun (z : Nat) => Eq (ListType KExpr) \
                 (list_take z (kapp_args (KExpr.app f x))) (kapp_args f)) \
                 (list_length (kapp_args f)) {pre} hlen \
                 (list_take_len_append x (kapp_args f))"
            ),
            "minimal_prefix_is_args: the rule RHS is applied to exactly the function part's \
             arguments. Stated at PREFIX (params + motives + minors), which is what the reduct \
             formula's list_take actually uses — NOT major_idx, which additionally counts the \
             indices. Those coincide only for an index-free recursor, and conflating them is the \
             kind of off-by-one that elaborates fine and means something else. DerivedProved, \
             zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The step-level `DefEq` bricks, plus the positional obligation.
    ///
    /// All four validated in the scratchpad first — one spec build for four
    /// bricks rather than four 26-minute cycles. Registered AFTER
    /// `add_minimal_spine_facts`, because `whc_fires_plain_minimal` transports
    /// `minimal_major_is_last`.
    fn add_step_defeq_bricks(&mut self) -> Result<(), SpecError> {
        let mi = MAJOR_IDX;
        let sp = "(KExpr.app f wmajor)";
        let reduct = |mtv: &str, mjv: &str, rlv: &str| {
            let miv = format!(
                "(Nat.add (Nat.add (Nat.add (recmeta_num_params {mtv}) \
                 (recmeta_num_motives {mtv})) (recmeta_num_minors {mtv})) \
                 (recmeta_num_indices {mtv}))"
            );
            let prev = format!(
                "(Nat.add (Nat.add (recmeta_num_params {mtv}) (recmeta_num_motives {mtv})) \
                 (recmeta_num_minors {mtv}))"
            );
            format!(
                "(apply_spine (list_drop (Nat.succ {miv}) (kapp_args {sp})) \
                 (apply_spine (list_drop (Nat.sub (list_length (kapp_args {mjv})) \
                 (recrule_num_fields {rlv})) (kapp_args {mjv})) \
                 (apply_spine (list_take {prev} (kapp_args {sp})) (recrule_rhs {rlv}))))"
            )
        };

        self.add_recursive_def(
            "def defeq_of_zeta_step (ty : KExpr) (v : KExpr) (b : KExpr) : \
             DefEq (KExpr.let_ ty v b) (instantiate b v) := DefEq.zeta ty v b",
            "defeq_of_zeta_step: the loop's let_ step is DefEq, by the zeta constructor directly. \
             One of the three non-iota arms of reduce_once_red_wh's soundness, and the only one \
             that needs no construction at all. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def defeq_of_const_delta (n : Name) (us : ListType Level) (v : KExpr) \
             (h : Eq (OptionType KExpr) (defval_for (red_def the_red_env) n) \
             (OptionType.some KExpr v)) : DefEq (KExpr.const n us) v := \
             DefEq.delta (KExpr.const n us) v (delta_reduces.mk (KExpr.const n us) v \
             (opt_bind_some_intro Name KExpr \
             (kexpr_const_name (kapp_fn (KExpr.const n us))) \
             (fun (dname : Name) => opt_bind KExpr KExpr \
             (defval_for (red_def the_red_env) dname) \
             (fun (val : KExpr) => OptionType.some KExpr \
             (apply_spine (kapp_args (KExpr.const n us)) val))) \
             n v (Eq.refl (OptionType Name) (OptionType.some Name n)) \
             (opt_bind_some_intro KExpr KExpr (defval_for (red_def the_red_env) n) \
             (fun (val : KExpr) => OptionType.some KExpr \
             (apply_spine (kapp_args (KExpr.const n us)) val)) \
             v v h (Eq.refl (OptionType KExpr) (OptionType.some KExpr v)))))",
            "defeq_of_const_delta: the loop's const step is DefEq, by delta. Two \
             opt_bind_some_intro levels rebuild delta_reduct's chain — the head name is Eq.refl \
             because kexpr_const_name (kapp_fn (const n us)) computes, and the inner equation is \
             Eq.refl because a bare const has no arguments, so apply_spine nil v reduces to v. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def whnf_fuel_red_wh_zero_none (renv : RedEnv) (e : KExpr) : \
             Eq (OptionType KExpr) (whnf_fuel_red_wh renv Nat.zero e) (OptionType.none KExpr) := \
             Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "whnf_fuel_red_wh_zero_none: the faithful loop returns nothing at fuel 0 — the base \
             case of every induction over it, and the reason those base cases are absurd rather \
             than arguments. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def whc_fires_plain_minimal (f : KExpr) (wmajor : KExpr) (recname : Name) \
                 (cname : Name) (meta : RecMeta) (rule : RecRule) (e2 : KExpr) \
                 (hlenmi : Eq Nat (list_length (kapp_args f)) {mi}) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) \
                 (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) recname) \
                 (OptionType.some RecMeta meta)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) \
                 (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) \
                 (recrule_for (red_rec the_red_env) recname cname) \
                 (OptionType.some RecRule rule)) \
                 (hred : Eq (OptionType KExpr) (OptionType.some KExpr {r_meta_wmajor_rule}) \
                 (OptionType.some KExpr e2)) : \
                 iota_step (red_rec the_red_env) {sp} e2 := \
                 opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {sp})) \
                 (fun (rn : Name) => opt_bind RecMeta KExpr \
                 (recmeta_for (red_rec the_red_env) rn) \
                 (fun (mt : RecMeta) => opt_bind KExpr KExpr \
                 (list_head (list_drop {mi_mt} (kapp_args {sp}))) \
                 (fun (mj : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn mj)) \
                 (fun (cn : Name) => opt_bind RecRule KExpr \
                 (recrule_for (red_rec the_red_env) rn cn) \
                 (fun (rl : RecRule) => OptionType.some KExpr {r_mt_mj_rl}))))) \
                 recname e2 h1 \
                 (opt_bind_some_intro RecMeta KExpr \
                 (recmeta_for (red_rec the_red_env) recname) \
                 (fun (mt : RecMeta) => opt_bind KExpr KExpr \
                 (list_head (list_drop {mi_mt} (kapp_args {sp}))) \
                 (fun (mj : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn mj)) \
                 (fun (cn : Name) => opt_bind RecRule KExpr \
                 (recrule_for (red_rec the_red_env) recname cn) \
                 (fun (rl : RecRule) => OptionType.some KExpr {r_mt_mj_rl})))) \
                 meta e2 h2 \
                 (opt_bind_some_intro KExpr KExpr \
                 (list_head (list_drop {mi} (kapp_args {sp}))) \
                 (fun (mj : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn mj)) \
                 (fun (cn : Name) => opt_bind RecRule KExpr \
                 (recrule_for (red_rec the_red_env) recname cn) \
                 (fun (rl : RecRule) => OptionType.some KExpr {r_meta_mj_rl}))) \
                 wmajor e2 (minimal_major_is_last meta f wmajor hlenmi) \
                 (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn wmajor)) \
                 (fun (cn : Name) => opt_bind RecRule KExpr \
                 (recrule_for (red_rec the_red_env) recname cn) \
                 (fun (rl : RecRule) => OptionType.some KExpr {r_meta_wmajor_rl})) \
                 cname e2 h4 \
                 (opt_bind_some_intro RecRule KExpr \
                 (recrule_for (red_rec the_red_env) recname cname) \
                 (fun (rl : RecRule) => OptionType.some KExpr {r_meta_wmajor_rl}) \
                 rule e2 h5 hred))))",
                mi_mt = "(Nat.add (Nat.add (Nat.add (recmeta_num_params mt) \
                         (recmeta_num_motives mt)) (recmeta_num_minors mt)) \
                         (recmeta_num_indices mt))",
                r_meta_wmajor_rule = reduct("meta", "wmajor", "rule"),
                r_mt_mj_rl = reduct("mt", "mj", "rl"),
                r_meta_mj_rl = reduct("meta", "mj", "rl"),
                r_meta_wmajor_rl = reduct("meta", "wmajor", "rl"),
            ),
            "whc_fires_plain_minimal: THE POSITIONAL OBLIGATION — for a spine carrying exactly \
             major_idx arguments, the pre-pass's five lookups are enough to fire a PLAIN iota on \
             the swapped spine. \
             \
             The mirror image of iota_reduct_whc_some_inv: six nested eliminations there, five \
             nested introductions here. minimal_major_is_last discharges the level that would \
             otherwise need a positional search through kapp_args, which is the whole reason the \
             minimal-spine restriction buys anything. \
             \
             With defeq_of_prepass_iota this completes the iota case of the faithful loop's \
             soundness: that lemma turns `plain iota fires on the swapped spine` into DefEq, and \
             this one supplies the firing. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// A PRE-PASS ι IS TWO `DefEq` STEPS — the factoring, stated in four lines.
    ///
    /// This is the whole semantic content of the pre-pass's soundness, and it
    /// needs no inverter, no list surgery and no restriction on the recursor:
    /// congruence to swap the major premise for its whnf, then a genuine ι on the
    /// now constructor-headed spine.
    ///
    /// I spent a while heading toward this via `iota_reduct_whc_some_inv` plus
    /// boundary list lemmas plus an index-free restriction — all of which are
    /// needed to connect `iota_reduct_whc`'s *firing condition* to
    /// `iota_step (app f wmajor)`, but none of which the factoring itself
    /// requires. Separating the two makes the hard part exactly one statement:
    /// *the pre-pass fires ⟹ the plain ι fires on the swapped spine.*
    ///
    /// It is also the concrete reason soundness targets `DefEq`: the first step is
    /// `app_cong`, which reduces inside an ARGUMENT, and `whnf_red_step` has no
    /// such congruence.
    fn add_prepass_iota_defeq(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def defeq_of_prepass_iota (f : KExpr) (major : KExpr) (wmajor : KExpr) \
             (r : KExpr) (hdm : DefEq major wmajor) \
             (hfire : iota_step (red_rec the_red_env) (KExpr.app f wmajor) r) : \
             DefEq (KExpr.app f major) r := \
             DefEq.trans (KExpr.app f major) (KExpr.app f wmajor) r \
             (DefEq.app_cong f f major wmajor (DefEq.refl f) hdm) \
             (DefEq.iota (KExpr.app f wmajor) r \
             (iota_reduces.mk (KExpr.app f wmajor) r hfire))",
            "defeq_of_prepass_iota: a pre-pass iota is exactly TWO DefEq steps — app_cong to \
             replace the major premise by its whnf, then a genuine iota on the now \
             constructor-headed spine. \
             \
             This is the entire semantic content of the faithful loop's soundness, and it needs \
             no inverter, no list lemmas and no restriction on the recursor. Isolating it makes \
             the remaining obligation exactly one statement — that iota_reduct_whc's firing \
             condition implies iota_step on the swapped spine — which is where the positional \
             work actually lives, rather than smeared through the semantics. \
             \
             It is also the concrete reason soundness must target DefEq rather than \
             whnf_red_conv: the FIRST step is app_cong, which reduces inside an ARGUMENT, and \
             whnf_red_step has app_left and proj congruence but no app_right. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// Two boundary facts about a spine whose major premise is its LAST argument.
    ///
    /// `list_head_drop_len_append` already gives the major itself; these give the
    /// prefix and the (empty) suffix, which is everything `iota_reduct`'s reduct
    /// formula reads. Together they let the ι-soundness argument avoid positional
    /// surgery on `kapp_args` entirely — the same last-argument shortcut that made
    /// the bvar-major half of the stuck-recursor case tractable.
    ///
    /// Both are `ListType.rec` inductions whose `cons` case reduces
    /// definitionally: `list_drop (succ n)` is `list_drop n ∘ list_tail`, and
    /// `list_take (succ n) (cons x l)` is `cons x (list_take n l)`.
    fn add_boundary_list_facts(&mut self) -> Result<(), SpecError> {
        let single = "(ListType.cons KExpr a (ListType.nil KExpr))";
        self.add_recursive_def(
            &format!(
                "def list_take_len_append (a : KExpr) (xs : ListType KExpr) : \
                 Eq (ListType KExpr) \
                 (list_take (list_length xs) (list_append xs {single})) xs := \
                 ListType.rec KExpr \
                 (fun (l : ListType KExpr) => Eq (ListType KExpr) \
                 (list_take (list_length l) (list_append l {single})) l) \
                 (Eq.refl (ListType KExpr) (ListType.nil KExpr)) \
                 (fun (x : KExpr) (rest : ListType KExpr) \
                 (ih : Eq (ListType KExpr) \
                 (list_take (list_length rest) (list_append rest {single})) rest) => \
                 Eq.cong (ListType KExpr) (ListType KExpr) \
                 (fun (t : ListType KExpr) => ListType.cons KExpr x t) \
                 (list_take (list_length rest) (list_append rest {single})) rest ih) \
                 xs"
            ),
            "list_take_len_append: taking exactly (length xs) from xs ++ [a] returns xs. \
             ListType.rec on xs; the nil case is refl and the cons case is succ-congruence on the \
             induction hypothesis, because list_take (succ n) (cons x l) reduces to \
             cons x (list_take n l). \
             \
             This is the spine PREFIX of a minimally fully-applied recursor — the arguments \
             iota_reduct's reduct formula applies the rule RHS to. DerivedProved, zero \
             axiom_deps.",
        )?;
        self.add_recursive_def(
            &format!(
                "def list_drop_succ_len_append (a : KExpr) (xs : ListType KExpr) : \
                 Eq (ListType KExpr) \
                 (list_drop (Nat.succ (list_length xs)) (list_append xs {single})) \
                 (ListType.nil KExpr) := \
                 ListType.rec KExpr \
                 (fun (l : ListType KExpr) => Eq (ListType KExpr) \
                 (list_drop (Nat.succ (list_length l)) (list_append l {single})) \
                 (ListType.nil KExpr)) \
                 (Eq.refl (ListType KExpr) (ListType.nil KExpr)) \
                 (fun (x : KExpr) (rest : ListType KExpr) \
                 (ih : Eq (ListType KExpr) \
                 (list_drop (Nat.succ (list_length rest)) (list_append rest {single})) \
                 (ListType.nil KExpr)) => ih) \
                 xs"
            ),
            "list_drop_succ_len_append: dropping one MORE than (length xs) from xs ++ [a] leaves \
             nothing. ListType.rec on xs; the cons case is literally the induction hypothesis, \
             because list_drop (succ n) is list_drop n after one list_tail, and that tail strips \
             exactly the cons this arm added. \
             \
             This is the spine SUFFIX past the major premise of a minimally fully-applied \
             recursor — empty, which is what makes the reduct formula's outer apply_spine \
             disappear. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The six continuation levels of `iota_reduct_whc`'s opt_bind chain, built
    /// in ONE place so every lemma about that chain reads the same shape.
    ///
    /// `recname` is a parameter because the callers use it differently: the
    /// inverter passes `"recname"`, the name its own `l2` lambda binds, while
    /// the recmeta short-circuit instantiates it at a concrete name. Generating
    /// both from one function is what stops the chain being transcribed twice
    /// and drifting — the same discipline `join_sources` applies to the
    /// confluence join.
    pub(super) fn whc_reduct() -> String {
        let mi = MAJOR_IDX;
        let pre = PREFIX_N;
        format!(
            "(apply_spine (list_drop (Nat.succ {mi}) (kapp_args e)) \
             (apply_spine (list_drop (Nat.sub (list_length (kapp_args wmajor)) \
             (recrule_num_fields rule)) (kapp_args wmajor)) \
             (apply_spine (list_take {pre} (kapp_args e)) (recrule_rhs rule))))"
        )
    }

    fn whc_layers(recname: &str) -> [String; 6] {
        Self::whc_chain(recname).0
    }

    /// The chain as both LAMBDAS and BODIES.
    ///
    /// `layers[k]` is `(fun (x : T) => bodies[k])`. Inversion consumes the
    /// lambdas; re-assembly consumes the bodies, because each intermediate term
    /// of its `Eq.trans` chain is one level's body with the binder instantiated.
    /// That works only because the binder names here (`recname`, `meta`,
    /// `major`, `wmajor`, `cname`, `rule`) are exactly the parameter names the
    /// re-assembly lemma uses — so the bodies need no substitution.
    ///
    /// Four declarations now read this one chain: `iota_reduct_whc` itself, the
    /// inverter, the recmeta short-circuit, and the re-assembly. Emitting it
    /// once is what stops those four drifting apart.
    fn whc_chain(recname: &str) -> ([String; 6], [String; 6]) {
        let mi = MAJOR_IDX;
        let reduct = Self::whc_reduct();
        let b7 = format!("OptionType.some KExpr {reduct}");
        let l7 = format!("(fun (rule : RecRule) => {b7})");
        let b6 = format!("opt_bind RecRule KExpr (recrule_for env {recname} cname) {l7}");
        let l6 = format!("(fun (cname : Name) => {b6})");
        let b5 = format!("opt_bind Name KExpr (kexpr_const_name (kapp_fn wmajor)) {l6}");
        let l5 = format!("(fun (wmajor : KExpr) => {b5})");
        let b4 = format!("opt_bind KExpr KExpr (wh major) {l5}");
        let l4 = format!("(fun (major : KExpr) => {b4})");
        let b3 = format!("opt_bind KExpr KExpr (list_head (list_drop {mi} (kapp_args e))) {l4}");
        let l3 = format!("(fun (meta : RecMeta) => {b3})");
        let b2 = format!("opt_bind RecMeta KExpr (recmeta_for env recname) {l3}");
        let l2 = format!("(fun (recname : Name) => {b2})");
        ([l2, l3, l4, l5, l6, l7], [b2, b3, b4, b5, b6, b7])
    }

    /// The ι chain short-circuits at LEVEL ONE when the head is not a constant.
    ///
    /// The shallowest of the three exits, and the cheapest: one `Eq.cong` on the
    /// very first `opt_bind`. A term whose spine head is a lambda, a sort, a
    /// bound variable, a projection or a literal has no head name at all, so the
    /// chain stops before it ever looks for recursor metadata.
    ///
    /// With `add_whc_recmeta_none` (level two) and `add_whc_no_major` (level
    /// three) this completes the family: no head name, no metadata, no major
    /// premise. Every way ι can fail to fire for a *structural* reason — as
    /// opposed to starvation, which is about budget — is one of these three, and
    /// deciding which applies is exactly what the `app` arm of step monotonicity
    /// does.
    fn add_whc_no_head(&mut self) -> Result<(), SpecError> {
        let o = "OptionType KExpr";
        let l2 = Self::whc_layers("recname")[0].clone();
        let src = format!(
            "def iota_reduct_whc_none_of_no_head (env : RecEnv) \
             (wh : KExpr -> OptionType KExpr) (e : KExpr) \
             (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.none Name)) : \
             Eq ({o}) (iota_reduct_whc env wh e) (OptionType.none KExpr) := \
             Eq.cong (OptionType Name) ({o}) \
             (fun (on : OptionType Name) => opt_bind Name KExpr on {l2}) \
             (kexpr_const_name (kapp_fn e)) (OptionType.none Name) hh"
        );
        debug_assert!(Self::balanced(&src), "whc no-head parens");
        self.add_recursive_def(
            &src,
            "iota_reduct_whc_none_of_no_head: iota cannot fire on a term whose spine head is not \
             a constant. One Eq.cong on the first opt_bind — the chain stops before it ever asks \
             for recursor metadata. \
             \
             The shallowest of the chain's three structural exits, completing the family with the \
             missing-metadata exit at level two and the under-application exit at level three. \
             Every STRUCTURAL reason iota can decline is one of these; starvation, which is about \
             budget rather than shape, is the separate phenomenon that makes plain fuel \
             monotonicity false. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The ι chain also short-circuits when the spine is too SHORT to have a
    /// major premise.
    ///
    /// Level three rather than level two: head and metadata both resolve, and
    /// the chain then asks for the argument at `MAJOR_IDX`, which an
    /// under-applied spine does not have. Unlike starvation this is
    /// budget-independent — it holds for every `wh` — which is exactly what the
    /// `app` arm of step monotonicity needs in its second case.
    fn add_whc_no_major(&mut self) -> Result<(), SpecError> {
        let mi = MAJOR_IDX;
        let o = "OptionType KExpr";
        // l2 binds `recname` itself, so it comes from that instantiation; the
        // deeper layers are read at the concrete name. Same split as
        // add_whc_recmeta_none.
        let l2 = Self::whc_layers("recname")[0].clone();
        let [_, l3, l4, _, _, _] = Self::whc_layers("nm");
        let b2 = format!("(opt_bind RecMeta KExpr (recmeta_for env nm) {l3})");
        let b3 = format!("(opt_bind KExpr KExpr (list_head (list_drop {mi} (kapp_args e))) {l4})");
        let goal = "(OptionType.none KExpr)";
        let c1 = format!(
            "(Eq.cong (OptionType Name) ({o}) \
             (fun (on : OptionType Name) => opt_bind Name KExpr on {l2}) \
             (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) hh)"
        );
        let c2 = format!(
            "(Eq.cong (OptionType RecMeta) ({o}) \
             (fun (om : OptionType RecMeta) => opt_bind RecMeta KExpr om {l3}) \
             (recmeta_for env nm) (OptionType.some RecMeta meta) hrm)"
        );
        let c3 = format!(
            "(Eq.cong ({o}) ({o}) \
             (fun (oj : {o}) => opt_bind KExpr KExpr oj {l4}) \
             (list_head (list_drop {mi} (kapp_args e))) (OptionType.none KExpr) hno)"
        );
        let src = format!(
            "def iota_reduct_whc_none_of_no_major (env : RecEnv) \
             (wh : KExpr -> OptionType KExpr) (e : KExpr) (nm : Name) (meta : RecMeta) \
             (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.some Name nm)) \
             (hrm : Eq (OptionType RecMeta) (recmeta_for env nm) \
             (OptionType.some RecMeta meta)) \
             (hno : Eq ({o}) (list_head (list_drop {mi} (kapp_args e))) \
             (OptionType.none KExpr)) : \
             Eq ({o}) (iota_reduct_whc env wh e) {goal} := \
             Eq.trans ({o}) (iota_reduct_whc env wh e) {b2} {goal} {c1} \
             (Eq.trans ({o}) {b2} {b3} {goal} {c2} {c3})"
        );
        debug_assert!(Self::balanced(&src), "whc no-major parens");
        self.add_recursive_def(
            &src,
            "iota_reduct_whc_none_of_no_major: an UNDER-APPLIED recursor spine cannot fire iota, \
             at any budget. Three rewrites: the head resolves, the metadata resolves, and then \
             the argument at MAJOR_IDX is absent, so opt_bind short-circuits. \
             \
             The third short-circuit of this chain, alongside the missing-metadata one and \
             starvation, and the only one that is BUDGET-INDEPENDENT: it holds for every wh, \
             because the spine's length has nothing to do with how much fuel the pre-pass had. \
             That is precisely what the app arm of step monotonicity needs in the case where the \
             major premise is the outermost argument — there the shorter spine is under-applied \
             at every budget, so its head-reduct cannot flip from none to some and change which \
             branch the step takes. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// RE-ASSEMBLY: the six lookups, run forward, rebuild the ι reduct.
    ///
    /// The converse of `iota_reduct_whc_some_inv`. Six `Eq.cong`s chained by
    /// transitivity, each rewriting one `opt_bind` scrutinee to `some …` so the
    /// bind fires and the chain advances one level. No mathematics — the content
    /// is entirely in getting the six intermediate terms right, which is why
    /// they come from `whc_chain` rather than being written out here.
    ///
    /// This is what lets step monotonicity move a fired ι from one budget to the
    /// next: invert at `j`, transport the pre-pass with restricted monotonicity,
    /// re-assemble at `j+1` from the same five other facts, which do not mention
    /// the budget at all.
    ///
    /// A narrower congruence — "pre-passes agreeing at the major give equal ι
    /// results" — cannot be stated cleanly, because the major is extracted
    /// *inside* the chain and `MAJOR_IDX` depends on `meta`, which is recovered
    /// inside it too; there is no way to name the agreement point from outside.
    fn add_whc_reassembly(&mut self) -> Result<(), SpecError> {
        let mi = MAJOR_IDX;
        let reduct = Self::whc_reduct();
        let ([l2, l3, l4, l5, l6, l7], [b2, b3, b4, b5, b6, _b7]) = Self::whc_chain("recname");
        let o = "OptionType KExpr";
        // Each step rewrites one scrutinee; `hole` names the option being rewritten.
        let cong = |ty: &str, var: &str, layer: &str, from: &str, to: &str, h: &str| {
            format!(
                "(Eq.cong (OptionType {ty}) ({o})                  (fun ({var} : OptionType {ty}) => opt_bind {ty} KExpr {var} {layer})                  {from} {to} {h})"
            )
        };
        let c1 = cong(
            "Name",
            "on",
            &l2,
            "(kexpr_const_name (kapp_fn e))",
            "(OptionType.some Name recname)",
            "h1",
        );
        let c2 = cong(
            "RecMeta",
            "om",
            &l3,
            "(recmeta_for env recname)",
            "(OptionType.some RecMeta meta)",
            "h2",
        );
        let c3 = cong(
            "KExpr",
            "oj",
            &l4,
            &format!("(list_head (list_drop {mi} (kapp_args e)))"),
            "(OptionType.some KExpr major)",
            "h3",
        );
        let c4 = cong(
            "KExpr",
            "ow",
            &l5,
            "(wh major)",
            "(OptionType.some KExpr wmajor)",
            "hw",
        );
        let c5 = cong(
            "Name",
            "oc",
            &l6,
            "(kexpr_const_name (kapp_fn wmajor))",
            "(OptionType.some Name cname)",
            "h4",
        );
        let c6 = cong(
            "RecRule",
            "orr",
            &l7,
            "(recrule_for env recname cname)",
            "(OptionType.some RecRule rule)",
            "h5",
        );
        let goal = format!("(OptionType.some KExpr {reduct})");
        // Right-nested: iota -> b2 -> b3 -> b4 -> b5 -> b6 -> the reduct.
        let mut proof = c6;
        for (from, to, c) in [
            (format!("({b5})"), format!("({b6})"), c5),
            (format!("({b4})"), format!("({b5})"), c4),
            (format!("({b3})"), format!("({b4})"), c3),
            (format!("({b2})"), format!("({b3})"), c2),
            (
                "(iota_reduct_whc env wh e)".to_string(),
                format!("({b2})"),
                c1,
            ),
        ] {
            proof = format!("(Eq.trans ({o}) {from} {to} {goal} {c} {proof})");
        }
        let src = format!(
            "def iota_reduct_whc_some_of_facts (env : RecEnv) \
             (wh : KExpr -> OptionType KExpr) (e : KExpr) (recname : Name) (meta : RecMeta) \
             (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule) \
             (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.some Name recname)) \
             (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) \
             (OptionType.some RecMeta meta)) \
             (h3 : Eq ({o}) (list_head (list_drop {mi} (kapp_args e))) \
             (OptionType.some KExpr major)) \
             (hw : Eq ({o}) (wh major) (OptionType.some KExpr wmajor)) \
             (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) \
             (OptionType.some Name cname)) \
             (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) \
             (OptionType.some RecRule rule)) : \
             Eq ({o}) (iota_reduct_whc env wh e) {goal} := {proof}"
        );
        debug_assert!(Self::balanced(&src), "whc reassembly parens");
        self.add_recursive_def(
            &src,
            "iota_reduct_whc_some_of_facts: the six lookups, run FORWARD, rebuild the iota reduct \
             — the converse of iota_reduct_whc_some_inv. Six Eq.cong chained by transitivity, \
             each rewriting one opt_bind scrutinee to some so the bind fires and the chain \
             advances a level. \
             \
             This is what moves a fired iota from one budget to the next: invert at j, transport \
             the pre-pass result with restricted monotonicity, then re-assemble at j+1 from the \
             same five remaining facts, none of which mentions the budget. The narrower \
             congruence one would rather have — pre-passes agreeing at the major give equal iota \
             results — cannot be stated, because the major is extracted inside the chain and \
             MAJOR_IDX depends on meta, recovered inside it as well. \
             \
             The six intermediate terms come from whc_chain, the same source the definition and \
             the inverter read. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The ι chain SHORT-CIRCUITS when the head carries no recursor metadata.
    ///
    /// The mirror of `iota_reduct_whc_some_inv`: that one walks all six levels
    /// down to a reduct, this one stops at level two. Both read their chain from
    /// `whc_layers`, so neither can drift from the definition or from each other.
    ///
    /// This is what discharges the `hcnone` hypothesis of `wh_step_none_of_neutral`,
    /// and it is the ι half of "a δ-dead const spine has no step at any budget" —
    /// the fact `i2` (`RecEnvCtorNoRecMeta`) supplies for constructor heads.
    fn add_whc_recmeta_none(&mut self) -> Result<(), SpecError> {
        let l2 = Self::whc_layers("recname")[0].clone();
        let l3_nm = Self::whc_layers("nm")[1].clone();
        let mid = format!("(opt_bind RecMeta KExpr (recmeta_for env nm) {l3_nm})");
        let src = format!(
            "def iota_reduct_whc_none_of_no_recmeta (env : RecEnv) \
             (wh : KExpr -> OptionType KExpr) (e : KExpr) (nm : Name) \
             (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.some Name nm)) \
             (hrm : Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.none RecMeta)) : \
             Eq (OptionType KExpr) (iota_reduct_whc env wh e) (OptionType.none KExpr) := \
             Eq.trans (OptionType KExpr) (iota_reduct_whc env wh e) {mid} \
             (OptionType.none KExpr) \
             (Eq.cong (OptionType Name) (OptionType KExpr) \
             (fun (on : OptionType Name) => opt_bind Name KExpr on {l2}) \
             (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) hh) \
             (Eq.cong (OptionType RecMeta) (OptionType KExpr) \
             (fun (om : OptionType RecMeta) => opt_bind RecMeta KExpr om {l3_nm}) \
             (recmeta_for env nm) (OptionType.none RecMeta) hrm)"
        );
        debug_assert!(Self::balanced(&src), "whc recmeta-none parens");
        self.add_recursive_def(
            &src,
            "iota_reduct_whc_none_of_no_recmeta: the faithful iota chain returns none as soon as \
             the head carries no recursor metadata. Two rewrites and a transitivity: the first \
             cong turns the head-name lookup into `some nm`, landing on level two; the second \
             turns the metadata lookup into none, at which point opt_bind short-circuits. \
             \
             The mirror of iota_reduct_whc_some_inv, which walks the same chain the other way. \
             Both read the chain from whc_layers rather than transcribing it, so a change to \
             iota_reduct_whc cannot leave either of them describing a shape that no longer \
             exists. \
             \
             This discharges the iota half of `a delta-dead const spine has no step at any \
             budget`, which is what step monotonicity turns on: the pre-pass result that made \
             iota fire is constructor-headed, hence carries no recmeta (i2) and no defval (i8), \
             hence is genuinely stuck, hence stable under more fuel. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// The CPS inverter, in BOTH universes.
    ///
    /// The kernel here is NON-CUMULATIVE (`tc/def_eq/mod.rs`: `is_le` falls back
    /// to `is_def_eq` unless `cumulative`), `Type` parses to `Sort 1`, and the
    /// spec's `Eq` is `Prop`-valued. So a `(C : Type)` conclusion parameter
    /// CANNOT be instantiated at an `Eq` goal — a CPS eliminator fixed at `Type`
    /// is unusable by every equational caller.
    ///
    /// Both variants are therefore emitted from one source, differing only in
    /// the universe and in which `opt_bind` inverter they call (`_type` takes
    /// `(C : Type)`, the plain one `(C : Prop)`, argument orders identical).
    /// That mirrors the pair `iota_reduct_some_inv` / `iota_reduct_some_inv_type`
    /// which already exists for the non-pre-pass chain, and it keeps the two
    /// from drifting.
    fn add_whc_inverter(&mut self) -> Result<(), SpecError> {
        self.add_whc_inverter_at("_type", "Type", "opt_bind_some_inv_type")?;
        self.add_whc_inverter_at("", "Prop", "opt_bind_some_inv")?;
        Ok(())
    }

    fn add_whc_inverter_at(
        &mut self,
        suffix: &str,
        univ: &str,
        binder_inv: &str,
    ) -> Result<(), SpecError> {
        let mi = MAJOR_IDX;
        let reduct = Self::whc_reduct();
        // l2 binds `recname` itself, so the inner levels must use that same name.
        let [l2, l3, l4, l5, l6, l7] = Self::whc_layers("recname");
        let kont = format!(
            "(forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) \
             (cname : Name) (rule : RecRule), \
             Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.some Name recname) -> \
             Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
             Eq (OptionType KExpr) (list_head (list_drop {mi} (kapp_args e))) \
             (OptionType.some KExpr major) -> \
             Eq (OptionType KExpr) (wh major) (OptionType.some KExpr wmajor) -> \
             Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) \
             (OptionType.some Name cname) -> \
             Eq (OptionType RecRule) (recrule_for env recname cname) \
             (OptionType.some RecRule rule) -> \
             Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
             C)"
        );
        let src = format!(
            "def iota_reduct_whc_some_inv{suffix} (env : RecEnv) \
             (wh : KExpr -> OptionType KExpr) \
             (e : KExpr) (e' : KExpr) (C : {univ}) \
             (h : Eq (OptionType KExpr) (iota_reduct_whc env wh e) (OptionType.some KExpr e')) \
             (k : {kont}) : C := \
             {binder_inv} Name KExpr (kexpr_const_name (kapp_fn e)) {l2} e' C h \
             (fun (recname : Name) \
             (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.some Name recname)) \
             (h1r : Eq (OptionType KExpr) ({l2} recname) (OptionType.some KExpr e')) => \
             {binder_inv} RecMeta KExpr (recmeta_for env recname) {l3} e' C h1r \
             (fun (meta : RecMeta) \
             (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) \
             (OptionType.some RecMeta meta)) \
             (h2r : Eq (OptionType KExpr) ({l3} meta) (OptionType.some KExpr e')) => \
             {binder_inv} KExpr KExpr \
             (list_head (list_drop {mi} (kapp_args e))) {l4} e' C h2r \
             (fun (major : KExpr) \
             (h3 : Eq (OptionType KExpr) (list_head (list_drop {mi} (kapp_args e))) \
             (OptionType.some KExpr major)) \
             (h3r : Eq (OptionType KExpr) ({l4} major) (OptionType.some KExpr e')) => \
             {binder_inv} KExpr KExpr (wh major) {l5} e' C h3r \
             (fun (wmajor : KExpr) \
             (hw : Eq (OptionType KExpr) (wh major) (OptionType.some KExpr wmajor)) \
             (h4r : Eq (OptionType KExpr) ({l5} wmajor) (OptionType.some KExpr e')) => \
             {binder_inv} Name KExpr (kexpr_const_name (kapp_fn wmajor)) {l6} e' C h4r \
             (fun (cname : Name) \
             (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) \
             (OptionType.some Name cname)) \
             (h5r : Eq (OptionType KExpr) ({l6} cname) (OptionType.some KExpr e')) => \
             {binder_inv} RecRule KExpr (recrule_for env recname cname) {l7} e' C h5r \
             (fun (rule : RecRule) \
             (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) \
             (OptionType.some RecRule rule)) \
             (h6r : Eq (OptionType KExpr) ({l7} rule) (OptionType.some KExpr e')) => \
             k recname meta major wmajor cname rule h1 h2 h3 hw h4 h5 h6r))))))"
        );
        debug_assert!(Self::balanced(&src), "whc inverter parens");
        self.add_recursive_def(
            &src,
            "iota_reduct_whc_some_inv: the CPS inversion of iota_reduct_whc's SIX-level opt_bind \
             chain, recovering the recursor name, its metadata, the raw major, ITS WHNF, the \
             constructor name and the rule, together with every lookup equation and the reduct \
             identity. Six nested opt_bind_some_inv_type, mirroring \
             iota_reduct_some_inv_type's five. \
             \
             This is the brick every soundness argument for the faithful loop needs, and the two \
             witnesses it adds are exactly the ones that argument turns on: `hw` says the raw \
             major reduces to wmajor, and `h4` says wmajor is constructor-headed. Together they \
             factor a pre-pass iota into the two DefEq steps it really is — app_cong to replace \
             the major by its whnf, then a genuine iota on the now constructor-headed spine. \
             \
             That factoring is why soundness must target DefEq rather than whnf_red_conv: \
             whnf_red_step has no app_right congruence, so it cannot express the first step at \
             all. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_wh_no_redex(&mut self) -> Result<(), SpecError> {
        let src = Self::wh_no_redex_src();
        self.add_recursive_def(
            &src,
            "whnf_fuel_red_wh_no_redex: a result of the FAITHFUL loop has no executable step left \
             — the foundation every classification of whnf results rests on. \
             \
             It differs from the original whnf_fuel_red_no_redex (whnf_progress.rs:712) in exactly \
             one respect, and that respect is forced. The original's step function takes no \
             continuation, so it can conclude `reduce_once_red renv r = none` outright. The \
             faithful loop steps with `reduce_once_red_wh renv ih`, where ih is the loop itself at \
             one less fuel — so the no-redex witness for a result sits at a fuel level that \
             DECREASES as the recursion descends, and the honest conclusion is that SOME level \
             witnesses it. \
             \
             The reflected fragment has no Sigma or Exists, so that existential is CPS — the same \
             idiom this development already uses for inversions. Everything else mirrors the \
             original proof structurally: Nat.rec on fuel, the zero arm killing an impossible \
             `none = some r`, and the succ arm casing on the step via OptionType.rec, its none \
             branch transporting the stuckness along e = r and its some branch handing off to the \
             induction hypothesis. Mirroring rather than reinventing is deliberate — the original \
             is known to typecheck, so a rejection here isolates to the continuation change. \
             \
             This does NOT yet give nf_head. It gives the hypothesis that the classifier needs. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The four whnf-loop definitions, each DERIVED from the shared source
    /// constant by one explicit substitution.
    ///
    /// Deriving rather than re-typing is the point. These mirror
    /// `opt_app_ilift`, `reduce_app_head_red`, `reduce_once_red` and
    /// `whnf_fuel_red` — nine-arm `KExpr.rec` terms whose hand-copies would drift
    /// the instant either version changed. Four verbatim copies of one string is
    /// precisely what turned a single false premise into nine vacuous
    /// declarations; that lesson applies to source strings as much as to
    /// premises.
    ///
    /// The substitutions, in dependency order:
    ///
    /// | from | to |
    /// |---|---|
    /// | `iota_reduct (red_rec renv)` | `iota_reduct_whc (red_rec renv) wh` |
    /// | `opt_app_ilift renv` | `opt_app_ilift_wh renv wh` |
    /// | `reduce_app_head_red renv` | `reduce_app_head_red_wh renv wh` |
    /// | `reduce_once_red renv e0` | `reduce_once_red_wh renv ih e0` |
    ///
    /// The last one is the load-bearing one: `ih` is `whnf_fuel_red_wh` at one
    /// less fuel, so the pre-pass is the loop itself. Structurally decreasing on
    /// the fuel `Nat.rec`, so it is a definition rather than a recursion that
    /// needs justifying.
    fn add_prepass_whnf_chain(&mut self) -> Result<(), SpecError> {
        for (src, subs, name, desc) in Self::prepass_chain() {
            let mut out = src.to_string();
            for (from, to) in subs {
                assert!(
                    out.contains(from),
                    "{name}: substitution target `{from}` absent — the shared source moved"
                );
                out = out.replace(from, to);
            }
            self.add_recursive_def(&out, desc)?;
        }
        Ok(())
    }

    /// `(shared source, substitutions, name, description)`, in dependency order.
    #[allow(clippy::type_complexity)]
    fn prepass_chain() -> Vec<(
        &'static str,
        Vec<(&'static str, &'static str)>,
        &'static str,
        &'static str,
    )> {
        vec![
            (
                SRC_OPT_APP_ILIFT,
                vec![
                    (
                        "def opt_app_ilift (renv : RedEnv)",
                        "def opt_app_ilift_wh (renv : RedEnv) (wh : KExpr -> OptionType KExpr)",
                    ),
                    (
                        "iota_reduct (red_rec renv)",
                        "iota_reduct_whc (red_rec renv) wh",
                    ),
                ],
                "opt_app_ilift_wh",
                "opt_app_ilift_wh: the loop's application dispatch tail, attempting the PRE-PASS \
                 iota at the current node. Derived from opt_app_ilift by one substitution — \
                 iota_reduct becomes iota_reduct_whc carrying the whnf continuation — so the two \
                 cannot drift. DerivedProved, zero axiom_deps.",
            ),
            (
                SRC_REDUCE_APP_HEAD_RED,
                vec![
                    ("def reduce_app_head_red (renv : RedEnv)",
                     "def reduce_app_head_red_wh (renv : RedEnv) (wh : KExpr -> OptionType KExpr)"),
                    ("opt_app_ilift renv", "opt_app_ilift_wh renv wh"),
                ],
                "reduce_app_head_red_wh",
                "reduce_app_head_red_wh: the nine-arm application-node dispatch, threading the \
                 whnf continuation to the pre-pass iota. Derived from reduce_app_head_red. \
                 DerivedProved, zero axiom_deps.",
            ),
            (
                SRC_REDUCE_ONCE_RED,
                vec![
                    (
                        "def reduce_once_red (renv : RedEnv)",
                        "def reduce_once_red_wh (renv : RedEnv) (wh : KExpr -> OptionType KExpr)",
                    ),
                    ("reduce_app_head_red renv", "reduce_app_head_red_wh renv wh"),
                ],
                "reduce_once_red_wh",
                "reduce_once_red_wh: the single weak-head step with the pre-pass iota. Still \
                 weak-head — the app arm still discards the argument's recursive result — but the \
                 iota it attempts now whnf-reduces the major premise first, which is the whole \
                 difference. DerivedProved, zero axiom_deps.",
            ),
            (
                SRC_WHNF_FUEL_RED,
                vec![
                    (
                        "def whnf_fuel_red (renv : RedEnv)",
                        "def whnf_fuel_red_wh (renv : RedEnv)",
                    ),
                    ("reduce_once_red renv e0", "reduce_once_red_wh renv ih e0"),
                ],
                "whnf_fuel_red_wh",
                "whnf_fuel_red_wh: THE LOOP, closed under its own pre-pass. The single \
                 substitution passes `ih` — this very function at one less fuel — as the \
                 major-premise whnf, so the pre-pass drills down a whole head spine instead of one \
                 level. \
                 \
                 That recursion is what distinguishes fixing the original counterexample from \
                 fixing the nested one: with a one-level pre-pass, a recursor whose major is \
                 ANOTHER recursor with a beta-redex major is still stuck; with this one the inner \
                 fires first. It is structurally decreasing on the fuel Nat.rec, so it is an \
                 ordinary definition and needs no termination argument. \
                 \
                 This does NOT by itself make hnf true — that is a theorem about this function, \
                 not a property of writing it down. DerivedProved, zero axiom_deps.",
            ),
        ]
    }

    /// The reduct, keyed on the WHNF'd major premise (`wmajor`), matching the
    /// kernel: it takes the constructor's fields off the reduced major, not the
    /// unreduced one.
    fn wh_reduct() -> String {
        format!(
            "(apply_spine (list_drop (Nat.succ {MAJOR_IDX}) (kapp_args e)) \
             (apply_spine (list_drop (Nat.sub (list_length (kapp_args wmajor)) \
             (recrule_num_fields rule)) (kapp_args wmajor)) \
             (apply_spine (list_take {PREFIX_N} (kapp_args e)) (recrule_rhs rule))))"
        )
    }

    /// The pre-pass reduct in CONTINUATION form: the whnf used on the major
    /// premise is a parameter, not a fuel count.
    ///
    /// This is the primary definition; the fuel-indexed `iota_reduct_wh` is a
    /// specialisation of it. The continuation form exists because the whnf loop
    /// must pass *itself* (at one less fuel) as the pre-pass — that mutual
    /// recursion is what makes the pre-pass drill down a whole head spine rather
    /// than one level, and it is the difference between fixing the original
    /// counterexample and fixing the nested one.
    fn iota_reduct_whc_src() -> String {
        format!(
            "def iota_reduct_whc (env : RecEnv) (wh : KExpr -> OptionType KExpr) (e : KExpr) : \
             OptionType KExpr := \
             opt_bind Name KExpr (kexpr_const_name (kapp_fn e)) (fun (recname : Name) => \
             opt_bind RecMeta KExpr (recmeta_for env recname) \
             (fun (meta : RecMeta) => \
             opt_bind KExpr KExpr (list_head (list_drop {MAJOR_IDX} (kapp_args e))) \
             (fun (major : KExpr) => \
             opt_bind KExpr KExpr (wh major) (fun (wmajor : KExpr) => \
             opt_bind Name KExpr (kexpr_const_name (kapp_fn wmajor)) (fun (cname : Name) => \
             opt_bind RecRule KExpr (recrule_for env recname cname) \
             (fun (rule : RecRule) => OptionType.some KExpr {reduct}))))))",
            reduct = Self::wh_reduct(),
        )
    }

    /// The fuel-indexed view, defined THROUGH the continuation form so the
    /// six-level chain exists exactly once.
    fn iota_reduct_wh_src() -> String {
        "def iota_reduct_wh (renv : RedEnv) (fuel : Nat) (e : KExpr) : OptionType KExpr := \
         iota_reduct_whc (red_rec renv) (whnf_fuel_red renv fuel) e"
            .to_string()
    }

    /// `iota_reduct` with one extra `opt_bind` level: whnf the major premise.
    ///
    /// Every other level is `iota_reduct`'s, verbatim, so the two differ in
    /// exactly the way the kernel and the model differ — and in no other way.
    fn add_iota_reduct_wh(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::iota_reduct_whc_src(),
            "iota_reduct_whc: the pre-pass reduct with the major-premise whnf as a CONTINUATION \
             parameter rather than a fuel count. The primary definition — iota_reduct_wh is a \
             specialisation — so the six-level chain exists exactly once. \
             \
             The continuation form is what lets the whnf loop pass ITSELF, at one less fuel, as \
             the pre-pass. That mutual recursion is not a stylistic choice: it is the difference \
             between a pre-pass that reduces one level and one that drills down a whole head \
             spine. A single-level pre-pass still loses on a nested recursor whose own major is a \
             beta-redex; the recursive one fires the inner recursor first and so never gets stuck. \
             DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            &Self::iota_reduct_wh_src(),
            "iota_reduct_wh: iota_reduct WITH the major-premise whnf pre-pass the deployed kernel \
             performs and the reflected model omits. \
             \
             THE ONLY DIFFERENCE from iota_reduct (iota_step.rs:127) is one extra opt_bind level: \
             the major premise is whnf-reduced before its head constant is read, and the \
             constructor's fields are taken off the REDUCED major. Every other level is verbatim, \
             so the two functions differ exactly where the kernel and the model differ and nowhere \
             else. \
             \
             The kernel side: micro/checker.rs:777 is `let major = self.whnf_impl(&args[major_idx])?`, \
             and tc/whnf.rs:70-77 records that with cheap_rec=false — the mode clean actually uses \
             — the major premise gets FULL whnf including delta, matching Lean 4 \
             type_checker.cpp:340. \
             \
             It takes a RedEnv rather than a RecEnv because whnf reduces with delta, and it takes \
             fuel because whnf is fuel-indexed. Those two signature changes are precisely why this \
             is registered BESIDE iota_reduct instead of replacing it: iota_reduct is mentioned \
             1,065 times across 38 files and sits under iota_subst_commutes, \
             iota_reduct_some_inv's five-level CPS inversion and most of the confluence \
             development. Migration is staged; this is the target. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The same closed term, two answers.
    fn add_divergence_witnesses(&mut self) -> Result<(), SpecError> {
        // Fuel 2, and the count is not arbitrary: whnf_fuel_red at fuel 1 spends
        // its only step firing the beta-redex and then calls the zero-fuel
        // continuation, which returns none. Fuel 2 fires beta, then observes that
        // the constructor has no further step and lands.
        self.add_recursive_def(
            "def iota_reduct_stuck_here : Eq (OptionType KExpr) \
             (iota_reduct (red_rec the_red_env) cx_stuck) (OptionType.none KExpr) := \
             Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "iota_reduct_stuck_here: the REFLECTED iota_reduct finds no redex in cx_stuck. Proof \
             by refl — the kernel evaluates the five-level opt_bind chain over the real reflected \
             environment and reaches none at level four, because cx_stuck's major premise is a \
             beta-redex whose kapp_fn is a lam, and lams carry no constant name. \
             \
             This is the half that makes hnf false: whnf therefore returns cx_stuck unchanged \
             (cx_whnf_stuck), and cx_stuck has no normal-form head. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def iota_reduct_wh_fires : Eq (OptionType KExpr) \
             (iota_reduct_wh the_red_env (Nat.succ (Nat.succ Nat.zero)) cx_stuck) \
             (OptionType.some KExpr kcre_witness_nat_zero_reduct) := \
             Eq.refl (OptionType KExpr) \
             (OptionType.some KExpr kcre_witness_nat_zero_reduct)",
            "iota_reduct_wh_fires: THE DIVERGENCE, executable. On the SAME closed term the \
             pre-pass version fires, and lands on exactly the reduct the Guard-4 witness records \
             for the whnf'd redex (kcre_witness_nat_zero_reduct). Proof by refl — the kernel \
             whnf-evaluates both sides over the real reflected environment. \
             \
             Read together with iota_reduct_stuck_here this is a machine-checked FIDELITY BUG \
             REPORT: two Eq.refls on one term, disagreeing, one matching the deployed kernel and \
             one matching the model. It was found by attempting a proof and failing, not by \
             reading the two Rust files side by side — which matters, because \
             SELF_VERIFICATION_CERTIFICATE.md's 2b fidelity argument currently rests on exactly \
             that reading. \
             \
             The reduct is the witness's own because cx_stuck and the witness share their spine \
             prefix and their post-major arguments (both empty), and the whnf'd major is the \
             witness's major — so only the major premise ever differed. \
             \
             Fuel 2 is not arbitrary: at fuel 1 whnf spends its single step firing the beta-redex \
             and then calls the zero-fuel continuation, which returns none. DerivedProved, zero \
             axiom_deps.",
        )?;

        // The same contrast one layer up, at the loop's STEP function. This is
        // the level that actually decides `hnf`: `hnf` quantifies over whnf
        // RESULTS, and a term is a whnf result exactly when the step function
        // returns none on it.
        self.add_recursive_def(
            "def reduce_once_red_stuck_here : Eq (OptionType KExpr) \
             (reduce_once_red the_red_env cx_stuck) (OptionType.none KExpr) := \
             Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "reduce_once_red_stuck_here: the CURRENT loop's step function finds nothing to do on \
             cx_stuck — which is precisely why whnf returns it unchanged (cx_whnf_stuck) and why \
             hnf is false, since cx_stuck has no normal-form head. Proof by refl. DerivedProved, \
             zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def reduce_once_red_wh_fires : Eq (OptionType KExpr) \
             (reduce_once_red_wh the_red_env \
             (whnf_fuel_red_wh the_red_env (Nat.succ (Nat.succ Nat.zero))) cx_stuck) \
             (OptionType.some KExpr kcre_witness_nat_zero_reduct) := \
             Eq.refl (OptionType KExpr) \
             (OptionType.some KExpr kcre_witness_nat_zero_reduct)",
            "reduce_once_red_wh_fires: THE PAYOFF — the pre-pass loop's step function FIRES on \
             the very term the current one is stuck on, and lands on the Guard-4 witness's reduct. \
             Proof by refl, so the kernel evaluates the whole nine-arm dispatch, the application \
             lift and the six-level pre-pass reduct over the real reflected environment. \
             \
             Read with reduce_once_red_stuck_here this says: cx_stuck is a whnf result under the \
             current loop and is NOT one under the faithful loop. Since hnf quantifies over whnf \
             results, and cx_stuck was the counterexample refuting it (hnf_is_false), this is the \
             counterexample being closed — the term simply stops being a whnf result. \
             \
             It is NOT yet a proof of hnf for the new loop. That is a theorem about all terms, and \
             this is one term. What it establishes is that the fix addresses the actual failure \
             rather than an adjacent one, which is worth checking before building the general \
             argument on top of it. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    /// The CPS inverter must exist in BOTH universes, and the un-suffixed name
    /// must be the Prop one.
    ///
    /// The kernel is non-cumulative, `Type` is `Sort 1`, and the spec's `Eq` is
    /// `Prop`-valued — so a CPS eliminator fixed at `(C : Type)` cannot be used
    /// by any caller whose goal is an equation, which is most of them. The
    /// naming follows the pair `iota_reduct_some_inv` / `..._type` that already
    /// exists for the non-pre-pass chain: plain means Prop.
    #[test]
    fn test_whc_inverter_exists_in_both_universes() {
        let src = include_str!("iota_prepass.rs");
        let body = src.split("mod tests").next().expect("module body");
        assert!(
            body.contains(r#"self.add_whc_inverter_at("_type", "Type", "opt_bind_some_inv_type")"#),
            "the Type-valued inverter must be emitted"
        );
        assert!(
            body.contains(r#"self.add_whc_inverter_at("", "Prop", "opt_bind_some_inv")"#),
            "the Prop-valued inverter must be emitted, un-suffixed"
        );
        // One source, two instantiations — not two transcriptions.
        assert_eq!(
            body.matches("def iota_reduct_whc_some_inv{suffix}").count(),
            1,
            "both variants must come from ONE source string"
        );
    }
    use super::*;

    /// Dependencies must be registered BEFORE their users.
    ///
    /// The minimal-spine facts transport the boundary list lemmas, so those must
    /// come first. Registration is sequential and a backwards order does not fail
    /// at compile time — it breaks the entire spec build at elaboration, which is
    /// 26 minutes away.
    ///
    /// This is the SECOND ordering bug in this program, and the first one that
    /// reached a commit. The scratchpad cannot catch it by construction: it
    /// appends candidates to an ALREADY-BUILT spec, so every dependency is
    /// trivially in scope. Fast iteration and registration order are orthogonal
    /// checks, and passing the first is not evidence about the second.
    #[test]
    fn test_dependencies_register_before_their_users() {
        let src = include_str!("iota_prepass.rs");
        let body = src
            .split("pub(super) fn add_iota_prepass")
            .nth(1)
            .expect("the registration function");
        let boundary = body
            .find("self.add_boundary_list_facts()")
            .expect("boundary registration");
        let minimal = body
            .find("self.add_minimal_spine_facts()")
            .expect("minimal registration");
        assert!(
            boundary < minimal,
            "the minimal-spine facts transport the boundary list lemmas, so those must \
             register first"
        );
    }

    /// Every generated source in this module must be paren-balanced.
    ///
    /// Unbalanced parens are a PARSE error, which aborts the entire spec build
    /// before any declaration is elaborated — so it costs a full 26-minute cycle
    /// and tells you nothing about the other declarations. The six-level inverter
    /// was closed five times.
    #[test]
    fn test_generated_sources_are_paren_balanced() {
        for (name, src) in [
            ("iota_reduct_whc", Specification::iota_reduct_whc_src()),
            ("iota_reduct_wh", Specification::iota_reduct_wh_src()),
            ("wh_no_redex", Specification::wh_no_redex_src()),
        ] {
            assert!(
                Specification::balanced(&src),
                "{name} is not paren-balanced"
            );
        }
        for (src, subs, name, _d) in Specification::prepass_chain() {
            let mut out = src.to_string();
            for (from, to) in &subs {
                out = out.replace(from, to);
            }
            assert!(
                Specification::balanced(&out),
                "{name} is not paren-balanced"
            );
        }
    }

    /// SIX `opt_bind` levels where `iota_reduct` has five, and the extra one is
    /// the whnf. If `iota_reduct_wh` drifted anywhere else, the two witnesses
    /// would still disagree but would no longer isolate the pre-pass as the
    /// cause — the entire evidential value of this module would be gone.
    #[test]
    fn test_differs_from_iota_reduct_by_exactly_the_prepass_level() {
        let src = Specification::iota_reduct_whc_src();
        assert_eq!(
            src.matches("opt_bind ").count(),
            6,
            "iota_reduct has five levels; the pre-pass adds exactly one"
        );
        assert_eq!(
            src.matches("wh major").count(),
            1,
            "the added level whnf-reduces the MAJOR premise, once"
        );
        // The level order matters: the whnf must sit between extracting the
        // major and reading its head constant.
        let at_major = src.find("(fun (major : KExpr)").expect("major level");
        let at_whnf = src.find("wh major").expect("whnf level");
        let at_cname = src
            .find("kexpr_const_name (kapp_fn wmajor)")
            .expect("cname level");
        assert!(
            at_major < at_whnf && at_whnf < at_cname,
            "the pre-pass must run AFTER the major is extracted and BEFORE its head is read"
        );
        // The fuel-indexed view must be a THIN specialisation of the
        // continuation form, not a second copy of the six-level chain. Two
        // copies of one chain is the duplication that this program already paid
        // for once, in the four verbatim `HNF` premises.
        let fuel_view = Specification::iota_reduct_wh_src();
        assert!(
            fuel_view.contains("iota_reduct_whc (red_rec renv) (whnf_fuel_red renv fuel) e"),
            "the fuel view must delegate: {fuel_view}"
        );
        assert_eq!(
            fuel_view.matches("opt_bind ").count(),
            0,
            "the fuel view must not restate the chain"
        );
    }

    /// Every `_wh` variant must be its original modulo exactly the listed
    /// substitutions — same length delta, same arm count, nothing else moved.
    ///
    /// This is the guarantee that makes deriving worth more than re-typing: if
    /// the shared source ever changes, the derived version changes with it, and
    /// if a substitution target disappears the build fails loudly instead of
    /// silently producing a variant that no longer mirrors anything.
    #[test]
    fn test_wh_chain_is_the_original_modulo_named_substitutions() {
        for (src, subs, name, _desc) in Specification::prepass_chain() {
            let mut out = src.to_string();
            for (from, to) in &subs {
                assert!(
                    out.contains(from),
                    "{name}: substitution target `{from}` is absent from the shared source"
                );
                out = out.replace(from, to);
            }
            // The only textual differences are the substitutions themselves.
            let mut back = out.clone();
            for (from, to) in &subs {
                back = back.replace(to, from);
            }
            assert_eq!(
                back, src,
                "{name}: reversing the substitutions must recover the shared source exactly — \
                 anything else means the variant drifted"
            );
            // Same number of `KExpr.rec` / `OptionType.rec` arms as the original.
            assert_eq!(
                out.matches("(fun ").count(),
                src.matches("(fun ").count(),
                "{name}: arm count changed"
            );
        }
    }

    /// The loop must pass ITSELF as the pre-pass — `ih`, the fuel-decremented
    /// whnf — not the original `whnf_fuel_red`. A one-level pre-pass still loses
    /// on a nested recursor whose own major is a β-redex.
    #[test]
    fn test_the_loop_feeds_itself_as_the_prepass() {
        let (src, subs, _, _) = Specification::prepass_chain()
            .into_iter()
            .find(|(_, _, n, _)| *n == "whnf_fuel_red_wh")
            .expect("the loop is in the chain");
        let mut out = src.to_string();
        for (from, to) in &subs {
            out = out.replace(from, to);
        }
        assert!(
            out.contains("reduce_once_red_wh renv ih e0"),
            "the pre-pass continuation must be `ih`, the loop at one less fuel: {out}"
        );
        assert!(
            !out.contains("whnf_fuel_red renv"),
            "the loop must not fall back to the pre-pass-free whnf"
        );
    }

    /// `C` must be a PARAMETER of `whnf_fuel_red_wh_no_redex`, never quantified
    /// inside its conclusion.
    ///
    /// `forall (C : Type), (… -> C) -> C` lives in `Sort 2`, and nothing in the
    /// tree can discharge a `Sort 2` goal from an absurd `none = some r`:
    /// `option_none_ne_some` targets a `Prop`, and both `opt_none_ne_some_t` and
    /// `option_none_ne_some_type` fix `C : Type`. Written the wrong way the base
    /// arm is unprovable, which is not obvious from reading it — it cost a caught
    /// rejection here and would otherwise have cost a 24-minute cycle.
    #[test]
    fn test_cps_answer_type_is_a_parameter_not_an_inner_quantifier() {
        let src = Specification::wh_no_redex_src();
        assert!(
            src.contains("def whnf_fuel_red_wh_no_redex (renv : RedEnv) (fuel : Nat) (C : Type)"),
            "C must be a theorem parameter so the statement stays in Sort 1: {src}"
        );
        assert!(
            !src.contains("forall (C : Type)"),
            "quantifying C inside the conclusion pushes the goal to Sort 2, which no \
             option no-confusion lemma in the tree can discharge"
        );
        assert!(
            src.contains("opt_none_ne_some_t"),
            "the base arm needs the Type-targeted no-confusion, not the Prop one"
        );
    }

    /// The convoy's `some` arm binds `e2`, so the loop lambda spliced into that
    /// arm must rename — the original proof uses `e3`. Shadowing here is
    /// semantically harmless but breaks the "mirror the proof exactly" discipline
    /// that makes a rejection isolate to the intended change.
    #[test]
    fn test_some_arm_avoids_shadowing_the_convoy_binder() {
        let src = Specification::wh_no_redex_src();
        assert!(
            src.contains("(fun (e3 : KExpr) => whnf_fuel_red_wh renv k e3)"),
            "the some arm's loop lambda must rename its binder to e3"
        );
    }

    /// The prefix stops before the indices; the major index includes them.
    /// Confusing the two takes the wrong arguments off the spine, and typechecks.
    #[test]
    fn test_prefix_excludes_indices_and_major_index_includes_them() {
        assert!(
            MAJOR_IDX.contains("recmeta_num_indices meta"),
            "the major sits after the indices"
        );
        assert!(
            !PREFIX_N.contains("recmeta_num_indices"),
            "the rule's prefix arguments stop before the indices"
        );
    }

    /// The reduct must key on the WHNF'd major (`wmajor`), not the raw one.
    /// Taking the constructor's fields off the unreduced major would silently
    /// reduce with the wrong arguments — and would still typecheck.
    #[test]
    fn test_reduct_uses_the_reduced_major() {
        let reduct = Specification::wh_reduct();
        assert_eq!(
            reduct.matches("kapp_args wmajor").count(),
            2,
            "both field-extraction sites must read the REDUCED major"
        );
        assert!(
            !reduct.contains("kapp_args major)"),
            "no site may read the unreduced major"
        );
        assert_eq!(
            reduct.matches("kapp_args e").count(),
            2,
            "the spine prefix and the post-major arguments still come from e"
        );
    }
}
