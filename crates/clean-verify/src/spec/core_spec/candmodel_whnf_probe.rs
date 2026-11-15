// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **THE WHNF-INDEXED CANDIDATE** — the third family in
//! `designs/2026-09-18-is-candmodel-uninhabited.md`.
//!
//! The other two are refuted on complementary halves of the Pi pair. The
//! type-blind family has `pi_elim` PROVED FALSE (`pi_elim_blind_refuted_uncond`);
//! the step-indexed family, which decides reducibility by the type's HEAD
//! CONSTRUCTOR, has `redTypeStep` PROVED FALSE (`redstep_redTypeStep_refuted`) —
//! because a type step can move the head across the `pi` boundary. This family
//! decides by the type's WEAK HEAD NORMAL FORM, so that particular step is
//! invisible to it.
//!
//! **Two sentences that used to stand here are now FALSE, and the correction is
//! the finding.** This module used to call itself *the first with no refutation
//! against it*, and to say a type step is *invisible* to it full stop. Measured
//! 2026-09-19 (`candmodel_whnf_typestep.rs`): a step is invisible to the HEAD
//! reading and NOT to the FUEL. `RedW (succ n)` reads the whnf at fuel
//! `succ n` exactly, every beta redex STARVES at fuel one while an already-whnf
//! `pi` does not, and `RedWClause` dispatches on an `OptionType` — so across one
//! beta step the clause flips KIND, from blind `whnf_acc e0` to the `pi`
//! `AndType`. `redTypeStep` is therefore REFUTED at the fixed index
//! (`redw_typestep_refuted_at_index_one_r1`).
//!
//! **Scope, which is narrower than that headline — and MEASURED.** The
//! refutation is at `RedW n`. At `RedWStep`, the index-quantified family every
//! law here is ultimately stated at, the law HOLDS for that very pair, in both
//! directions (`redw_typestep_{fwd,bwd}_at_redwstep_for_the_refuting_pair`). So
//! the reading is the same one `redw_pi_elim`'s deliberate index BUMP already
//! forces: **the index is load-bearing**, and a per-index family is not a
//! candidate model. Do not cite the refutation as a refutation of this
//! candidate — that is now a measurement, not a caution.
//!
//! **Everything here is SCRATCH and unwired.** These are probes of individual
//! laws at one candidate, not a model: a `CandModel` needs all fourteen, and the
//! measured column is far short of that. Read the design note's table for the
//! per-law state and this module for the terms.
//!
//! **Why `RedWInner` and `RedWClause` exist.** Written inline, `RedW`'s successor
//! clause has type `(fun _o => Type) o` — a beta-redex. Harmless while the body
//! is checked against a DECLARED `Type`, and fatal the moment a proof needs the
//! clause as the DOMAIN of an arrow, where the sort must be inferred: `redw_cr2`
//! failed exactly there with `ExpectedSort` before the split. Naming each
//! elimination level with a declared `Type` result gives motives something to
//! say, and BOTH levels needed one.

use crate::spec::Specification;

impl Specification {
    /// **THE WHNF-INDEXED CANDIDATE — scratch.**
    ///
    /// §3k's step 1. `RedStep` decides reducibility by the type's HEAD
    /// CONSTRUCTOR, and `redstep_redTypeStep_refuted` proves that cannot survive
    /// a step in the type. This decides it by the type's WEAK HEAD NORMAL FORM
    /// instead, so a step that only moves the head is invisible to it.
    ///
    /// ```text
    /// RedW 0     T e := whnf_acc e
    /// RedW (n+1) T e := case whnf_fuel_red_wh3 the_red_env (n+1) T of
    ///                     some (pi A B) => whnf_acc e AND
    ///                                      (forall x, RedW n A x -> RedW n (instantiate B x) (app e x))
    ///                     _             => whnf_acc e
    /// ```
    ///
    /// **The index does double duty, and that is forced.** There is no total
    /// whnf here and cannot be one without the strong normalization this
    /// telescope exists to prove; `whnf_fuel_red_wh3` STARVES to `none`. So the
    /// step index is also the fuel — which is why §3k predicts `redTypeStep`
    /// holds only under a fuel side condition rather than outright, and why the
    /// `none` arm falls back to bare `whnf_acc` instead of failing.
    ///
    /// **The clause is FACTORED into `RedWInner` and `RedWClause`, and that is
    /// not cosmetic.** Written inline, `RedW`'s successor clause has type
    /// `(fun _o => Type) o` — a beta-redex. That is harmless while the body is
    /// checked against a DECLARED `Type`, and fatal the moment a proof needs the
    /// clause as the DOMAIN of an arrow, where the sort must be inferred:
    /// `redw_cr2` failed exactly there with `ExpectedSort`. Naming each level
    /// with a declared `Type` result gives motives something to say.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_indexed_sources() -> Vec<(String, String)> {
        let blind = "whnf_acc e0";
        let arm = |vals: &str| format!("(fun ({vals}) => {blind})");
        let inner = format!(
            "def RedWInner (ih : KExpr -> KExpr -> Type) (e0 : KExpr) (t : KExpr) : Type := \
             KExpr.rec (fun (_t : KExpr) => Type) \
             {sort} {bvar} {app} {lam} \
             (fun (ty : KExpr) (bb : KExpr) (i1 : Type) (i2 : Type) => \
             AndType (whnf_acc e0) \
             (forall (x : KExpr), ih ty x -> ih (instantiate bb x) (KExpr.app e0 x))) \
             {konst} {let_} {proj} {mvar} t",
            sort = arm("l : Level"),
            bvar = arm("i : Nat"),
            app = arm("ff : KExpr) (aa : KExpr) (i1 : Type) (i2 : Type"),
            lam = arm("lty : KExpr) (lb : KExpr) (i1 : Type) (i2 : Type"),
            konst = arm("nm : Name) (us : ListType Level"),
            let_ =
                arm("zty : KExpr) (zv : KExpr) (zb : KExpr) (i1 : Type) (i2 : Type) (i3 : Type",),
            proj = arm("ps : Name) (pidx : Nat) (sub : KExpr) (i1 : Type"),
            mvar = arm("v : Nat"),
        );
        vec![
            ("RedWInner".to_string(), inner),
            (
                "RedWClause".to_string(),
                "def RedWClause (ih : KExpr -> KExpr -> Type) (e0 : KExpr) \
                 (o : OptionType KExpr) : Type := \
                 OptionType.rec KExpr (fun (_o : OptionType KExpr) => Type) \
                 (whnf_acc e0) (fun (U : KExpr) => RedWInner ih e0 U) o"
                    .to_string(),
            ),
            (
                "RedW".to_string(),
                "def RedW : Nat -> KExpr -> KExpr -> Type := \
                 Nat.rec (fun (_k : Nat) => KExpr -> KExpr -> Type) \
                 (fun (T0 : KExpr) (e0 : KExpr) => whnf_acc e0) \
                 (fun (n : Nat) (ih : KExpr -> KExpr -> Type) => \
                 fun (T0 : KExpr) (e0 : KExpr) => \
                 RedWClause ih e0 \
                 (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T0))"
                    .to_string(),
            ),
            (
                "RedWStep".to_string(),
                "def RedWStep (T : KExpr) (e : KExpr) : Type := \
                 forall (n : Nat), RedW n T e"
                    .to_string(),
            ),
            (
                "redw_cr1".to_string(),
                "def redw_cr1 (T : KExpr) (e : KExpr) (h : RedWStep T e) : \
                 whnf_acc e := h Nat.zero"
                    .to_string(),
            ),
        ]
    }

    /// **`cr2` at the WHNF-INDEXED candidate — scratch, retried after the
    /// refactor.**
    ///
    /// The first attempt failed with `ExpectedSort((fun _o => Type) fvar)`: the
    /// proof must case on the `OptionType` that `whnf_fuel_red_wh3` returns, so
    /// its motive names the successor clause AS A TYPE at a bound scrutinee, and
    /// written inline that clause's own type is a beta-redex the elaborator will
    /// not reduce in a sort position.
    ///
    /// `RedWInner` and `RedWClause` exist to give the motives a name with a
    /// DECLARED `Type` result. Both levels needed one — the `OptionType` layer
    /// and the `KExpr` layer inside it — which is why there are two.
    ///
    /// The mathematics is unchanged from `redstep_cr2`: `Nat.rec` on the index
    /// with a `KExpr.rec` on the type, the `pi` arm consuming the OUTER
    /// hypothesis at a DIFFERENT type (`instantiate bb z`), which is why the
    /// outer motive quantifies the type. What the whnf candidate adds is the
    /// `OptionType` layer between them.
    /// **`redConst` at this candidate, at the EMPTY environment — scratch.**
    ///
    /// Where the two threads of the design note meet. §3j reduces the whole
    /// vacuity question to `CandModel ⟨empty⟩`, because exactly ONE of the
    /// fifteen binders mentions `tenv` — `redConst` — and every declaration in
    /// the tree quantifies it. §3k builds a candidate that survives both
    /// impossibility results.
    ///
    /// They compose, and the composition is a one-liner, because
    /// `redconst_premise_is_refutable_at_the_empty_env` is CANDIDATE-INDEPENDENT:
    /// it refutes the premise `kdecl_type_at kdecl_empty n us = some A` outright,
    /// so it yields any goal at all, including this family's.
    ///
    /// That is the point worth recording rather than the term. At the empty
    /// environment `redConst` is free for EVERY candidate, so §3d's three-way
    /// split moves 8/5/1 to 9/4/1 there — and the law it moves is the one §3e's
    /// constraint was built on, which is why the reduction is worth having.
    ///
    /// What it does NOT do is make the candidate a model: the four `redRec*`
    /// side conditions are about the FIXED reduction environment reached through
    /// `denv`/`renv`, which those fields bind themselves, so emptying the TYPE
    /// environment says nothing about them.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_redconst_sources() -> Vec<(String, String)> {
        vec![(
            "redw_redConst_free_at_the_empty_env".to_string(),
            "def redw_redConst_free_at_the_empty_env (n : Name) (us : ListType Level) \
             (A : KExpr) (s : Nat -> KExpr) \
             (h : Eq (OptionType KExpr) (kdecl_type_at kdecl_empty n us) \
             (OptionType.some KExpr A)) : \
             RedWStep (psubst s A) (KExpr.const n us) := \
             redconst_premise_is_refutable_at_the_empty_env n us A \
             (RedWStep (psubst s A) (KExpr.const n us)) h"
                .to_string(),
        )]
    }

    /// **Testing the forward/backward prediction: `cr3` at a NON-PI type —
    /// scratch.**
    ///
    /// The design note derives that the seven laws `RedW` lacks are all BACKWARD
    /// (reduct to redex), that the `whnf_acc` half of a backward step is
    /// available, and that only the POINTWISE half stalls. It then predicts:
    /// each of the seven should HOLD at any type whose whnf is not a `pi`, where
    /// the clause degenerates to `whnf_acc` and no pointwise half exists.
    ///
    /// This is that prediction at its cleanest instance. `cr3` is the hardest of
    /// the seven — §3k derives it needs the argument-side accessibility
    /// induction AND a type transport — and at `sort 0` it should collapse to
    /// `whnf_acc.intro`, because `RedW k (sort 0) e` IS `whnf_acc e` at every
    /// index (a `sort` is its own whnf, so the `sort` arm is selected).
    ///
    /// If it goes through, the prediction survives its first test and the
    /// obstruction really is localised to the `pi` arm. If it does not, the
    /// characterization is wrong and that is the more interesting outcome.
    ///
    /// **It is one type, not the general law.** `cr3` at an arbitrary `T`
    /// remains unmeasured, and nothing here bears on the `pi` arm.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_cr3_at_sort_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        vec![(
            "redw_cr3_at_a_non_pi_type".to_string(),
            format!(
                "def redw_cr3_at_a_non_pi_type (e : KExpr) (hn : Neutral e) \
                 (hall : forall (e2 : KExpr), whnf_step e e2 -> RedWStep {s0} e2) : \
                 RedWStep {s0} e := \
                 fun (n : Nat) => \
                 Nat.rec (fun (k : Nat) => RedW k {s0} e) \
                 (whnf_acc.intro e (fun (e2 : KExpr) (st : whnf_step e e2) => \
                 hall e2 st Nat.zero)) \
                 (fun (k : Nat) (_ih : RedW k {s0} e) => \
                 whnf_acc.intro e (fun (e2 : KExpr) (st : whnf_step e e2) => \
                 hall e2 st (Nat.succ k))) n"
            ),
        )]
    }

    /// **The forward/backward prediction, SECOND test: `redAbstraction` at a
    /// non-`pi` type — scratch.**
    ///
    /// `cr3` was the first test and is the hardest of the seven. This is a
    /// different KIND of backward law: `cr3` quantifies over successors, while
    /// `redAbstraction` names one contractum and rebuilds a specific redex. If
    /// the characterization is right, both should go through at a type whose
    /// whnf is not a `pi`, for the same reason and by different means.
    ///
    /// It reuses `redabstraction_blind` rather than re-proving SN of the redex.
    /// That lemma carries FOUR ι/δ side conditions — three carriers rather than
    /// the usual two, because the redex is two constructors deep — and they are
    /// passed straight through as hypotheses here rather than discharged, since
    /// discharging them is that probe's business and not this one's.
    ///
    /// At `sort 0` the clause is `whnf_acc` at every index, so the `Nat.rec` is
    /// the same term twice and the whole law reduces to the blind probe's
    /// conclusion. That IS the prediction: where the pointwise half does not
    /// exist, a backward law costs exactly what it costs at the type-blind
    /// candidate.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_redabstraction_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        let redex = "(KExpr.app (KExpr.lam A bb) aa)";
        let carriers = "(hiota : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
                        iota_reduces p q -> beta_reduces (psubst t p) (psubst t q)) \
                        (kio : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
                        iota_reduces (KExpr.app (KExpr.lam p q) r) z -> whnf_acc z) \
                        (kde : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
                        delta_reduces (KExpr.app (KExpr.lam p q) r) z -> whnf_acc z) \
                        (klio : forall (p : KExpr) (q : KExpr) (z : KExpr) (r : KExpr), \
                        iota_reduces (KExpr.lam p q) z -> whnf_acc (KExpr.app z r))";
        let app = "redabstraction_blind hiota kio kde klio A hA aa haa bb hbb hb";
        vec![(
            "redw_redAbstraction_at_a_non_pi_type".to_string(),
            format!(
                "def redw_redAbstraction_at_a_non_pi_type {carriers} \
                 (A : KExpr) (hA : whnf_acc A) \
                 (aa : KExpr) (haa : whnf_acc aa) \
                 (bb : KExpr) (hbb : whnf_acc bb) \
                 (hb : forall (x : KExpr), whnf_acc x -> \
                 whnf_acc (instantiate bb x)) : \
                 RedWStep {s0} {redex} := \
                 fun (n : Nat) => \
                 Nat.rec (fun (k : Nat) => RedW k {s0} {redex}) \
                 ({app}) \
                 (fun (k : Nat) (_ih : RedW k {s0} {redex}) => ({app})) n"
            ),
        )]
    }

    /// **Locating the stall: `cr3` at a PI type needs the pointwise half and
    /// NOTHING ELSE — scratch.**
    ///
    /// The two prediction tests show the backward laws hold off the `pi` arm.
    /// This says what the `pi` arm actually costs, and it says it by proving the
    /// law under ONE extra premise rather than by writing a term that fails.
    ///
    /// Given `cr3`'s own hypothesis — every successor of `e` is reducible at the
    /// `pi` type — the `whnf_acc` half comes FREE: project `AndType.left` out of
    /// each successor's pair and feed them to `whnf_acc.intro`. So the
    /// accessibility that §3g makes the whole difficulty of `pi_elim` is not
    /// what blocks `cr3` here.
    ///
    /// The POINTWISE half is the entire gap, and it is supplied here as `hpt`.
    /// §3k derives why it cannot be built: the recursion needs
    /// `RedW k (instantiate bb x) (app e x')` at the type the UNSTEPPED argument
    /// determines, while what is available is at `instantiate bb x'` — different
    /// types, related only by a transport that `redw_typeStep_*` gives under a
    /// fuel side condition.
    ///
    /// So the residual is ONE obligation, not a pile: produce the pointwise half.
    /// That is a sharper statement than "cr3 is hard" and it is what a next
    /// attempt should target.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_cr3_pi_stall_sources() -> Vec<(String, String)> {
        let pointwise = "(forall (x : KExpr), RedW k ty x -> \
                         RedW k (instantiate bb x) (KExpr.app e x))";
        let pointwise_at = |t: &str| {
            format!(
                "(forall (x : KExpr), RedW k ty x -> \
                 RedW k (instantiate bb x) (KExpr.app {t} x))"
            )
        };
        vec![(
            "redw_cr3_at_a_pi_reduces_to_the_pointwise_half".to_string(),
            format!(
                "def redw_cr3_at_a_pi_reduces_to_the_pointwise_half \
                 (k : Nat) (ty : KExpr) (bb : KExpr) (e : KExpr) (hn : Neutral e) \
                 (hall : forall (e2 : KExpr), whnf_step e e2 -> \
                 AndType (whnf_acc e2) {p2}) \
                 (hpt : {pointwise}) : \
                 AndType (whnf_acc e) {pointwise} := \
                 AndType.intro (whnf_acc e) {pointwise} \
                 (whnf_acc.intro e (fun (e2 : KExpr) (st : whnf_step e e2) => \
                 AndType.left (whnf_acc e2) {p2} (hall e2 st))) \
                 hpt",
                p2 = pointwise_at("e2"),
            ),
        )]
    }

    /// **`cr1` AT A FIXED INDEX — scratch, and a building block rather than a
    /// result.**
    ///
    /// `redw_cr1` is `h Nat.zero`: it reads `whnf_acc` off `RedWStep`, which
    /// quantifies every index. Any argument INSIDE the recursion has only
    /// `RedW k T x` at one index, and needs `whnf_acc x` from it — to start an
    /// accessibility induction on the argument, which is what the `pi` arm's
    /// pointwise half requires.
    ///
    /// It holds at every index because every clause carries `whnf_acc`: the
    /// zero case IS `whnf_acc`, both `OptionType` fallbacks are, and the `pi`
    /// arm has it as the left conjunct. So the proof is a case analysis with no
    /// induction on the index — `Nat.rec` only to get past `k`, then
    /// `OptionType.rec` and `KExpr.rec`, identity everywhere except one
    /// `AndType.left`.
    ///
    /// Recorded as a block rather than folded into a bigger attempt, because it
    /// is the piece every further `RedW` proof needs and it is worth knowing it
    /// exists before spending a cycle on something that assumes it.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_cr1_at_index_sources() -> Vec<(String, String)> {
        let idarm = "fun (h : whnf_acc e) => h";
        let ih_ty = |t: &str| format!("RedWInner (RedW j) e {t} -> whnf_acc e");
        let arm = |vals: &str, subs: &[&str]| {
            let ihs: String = subs
                .iter()
                .enumerate()
                .map(|(n, t)| format!(" (q{n} : {})", ih_ty(t)))
                .collect();
            format!("(fun ({vals}){ihs} => {idarm})")
        };
        let pi_arm = format!(
            "(fun (ty : KExpr) (bb : KExpr) (q0 : {ihty}) (q1 : {ihbb}) => \
             fun (h : RedWInner (RedW j) e (KExpr.pi ty bb)) => \
             AndType.left (whnf_acc e) \
             (forall (x : KExpr), RedW j ty x -> \
             RedW j (instantiate bb x) (KExpr.app e x)) h)",
            ihty = ih_ty("ty"),
            ihbb = ih_ty("bb"),
        );
        vec![(
            "redw_cr1_at_index".to_string(),
            format!(
                "def redw_cr1_at_index (k : Nat) (T : KExpr) (e : KExpr) \
                 (h : RedW k T e) : whnf_acc e := \
                 Nat.rec (fun (kk : Nat) => forall (T0 : KExpr) (e0 : KExpr), \
                 RedW kk T0 e0 -> whnf_acc e0) \
                 (fun (T0 : KExpr) (e0 : KExpr) (h0 : whnf_acc e0) => h0) \
                 (fun (j : Nat) (_ih : forall (T0 : KExpr) (e0 : KExpr), \
                 RedW j T0 e0 -> whnf_acc e0) => \
                 fun (T0 : KExpr) (e : KExpr) => \
                 OptionType.rec KExpr \
                 (fun (o : OptionType KExpr) => \
                 RedWClause (RedW j) e o -> whnf_acc e) \
                 ({idarm}) \
                 (fun (U : KExpr) => \
                 KExpr.rec (fun (t0 : KExpr) => \
                 RedWInner (RedW j) e t0 -> whnf_acc e) \
                 {sort} {bvar} {app} {lam} {pi_arm} {konst} {let_} {proj} {mvar} U) \
                 (whnf_fuel_red_wh3 the_red_env (Nat.succ j) T0)) \
                 k T e h",
                sort = arm("l : Level", &[]),
                bvar = arm("i : Nat", &[]),
                app = arm("ff : KExpr) (aa : KExpr", &["ff", "aa"]),
                lam = arm("lty : KExpr) (lb : KExpr", &["lty", "lb"]),
                konst = arm("nm : Name) (us : ListType Level", &[]),
                let_ = arm(
                    "zty : KExpr) (zv : KExpr) (zb : KExpr",
                    &["zty", "zv", "zb"],
                ),
                proj = arm("ps : Name) (pidx : Nat) (sub : KExpr", &["sub"]),
                mvar = arm("v : Nat", &[]),
            ),
        )]
    }

    /// **THE POINTWISE HALF, non-dependent codomain — scratch, and the route's
    /// steps 1–6 in one term.**
    ///
    /// The `pi` arm's whole residual, discharged for the case where the codomain
    /// does not mention its binder. The design note's route is followed exactly:
    ///
    /// 1. `redw_cr1_at_index` turns `RedW k ty x` into `whnf_acc x`, which
    ///    STARTS the accessibility induction — the Girard induction §3h names.
    ///    `redw_cr1` cannot do this: it reads off `RedWStep`, and inside the
    ///    recursion only one index is available.
    /// 2. `whnf_step_app_inv` dispatches the successors of `app e w` five ways.
    /// 3. `kbeta` is REFUTED: it supplies `Eq KExpr e (lam A0 body)`, transport
    ///    that onto `Neutral e`, and `Neutral`'s `lam` arm is `Empty`.
    /// 4. `kfn` comes straight from the successors hypothesis at `f2`.
    /// 5. `karg` uses the accessibility IH at `a2`, with `redw_cr2_at_index`
    ///    carrying `RedW k ty w` along the step — again the INDEXED form,
    ///    because `RedWStep` is not what the recursion holds.
    /// 6. `kiota` / `kdelta` are carried, as everywhere in this chain.
    ///
    /// **Non-dependence is what makes step 5 close**, and it is visible in the
    /// statement rather than assumed: the codomain is written `bb` throughout,
    /// where the general law needs `instantiate bb x` at the goal and
    /// `instantiate bb a2` at the hypothesis. Those differ, and only a transport
    /// relates them — §3k's residual inside the residual. Here they are the same
    /// term and the transport is the identity.
    ///
    /// `hcr3` is `cr3` AT INDEX `k` AND AT THE CODOMAIN — not at every type.
    /// The first draft quantified the type, and the outer induction then could
    /// not supply it: `redw_cr3_at_sort_at_index` fixes the type to the codomain,
    /// which is all this proof ever uses (`hcr3 (app e w)`, at `bb`). An
    /// over-general hypothesis hid what the term actually needs, and the failure
    /// that exposed it named the mismatch exactly.
    ///
    /// In a real proof `hcr3` is an outer `Nat.rec`'s induction hypothesis;
    /// assuming it here is what makes this a probe of the `pi` ARM rather than of
    /// the whole law.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_pointwise_sources() -> Vec<(String, String)> {
        let goal = "RedW k bb (KExpr.app e w)";
        vec![(
            "redw_cr3_pointwise_at_a_nondependent_codomain".to_string(),
            format!(
                "def redw_cr3_pointwise_at_a_nondependent_codomain \
                 (k : Nat) (ty : KExpr) (bb : KExpr) (e : KExpr) \
                 (hn : Neutral e) \
                 (hcr3 : forall (t : KExpr), Neutral t -> \
                 (forall (z : KExpr), whnf_step t z -> RedW k bb z) -> RedW k bb t) \
                 (hall : forall (e2 : KExpr), whnf_step e e2 -> \
                 forall (u : KExpr), RedW k ty u -> RedW k bb (KExpr.app e2 u)) \
                 (kio : forall (a0 : KExpr) (z : KExpr), \
                 iota_reduces (KExpr.app e a0) z -> RedW k bb z) \
                 (kde : forall (a0 : KExpr) (z : KExpr), \
                 delta_reduces (KExpr.app e a0) z -> RedW k bb z) : \
                 forall (x : KExpr), RedW k ty x -> RedW k bb (KExpr.app e x) := \
                 fun (x : KExpr) (hx : RedW k ty x) => \
                 whnf_acc.rec \
                 (fun (w : KExpr) (_hw : whnf_acc w) => \
                 RedW k ty w -> {goal}) \
                 (fun (w : KExpr) \
                 (_f : forall (y : KExpr), whnf_step w y -> whnf_acc y) \
                 (ih : forall (y : KExpr) (_s : whnf_step w y), \
                 RedW k ty y -> RedW k bb (KExpr.app e y)) \
                 (hw : RedW k ty w) => \
                 hcr3 (KExpr.app e w) ConstFreeUnit.triv \
                 (fun (z : KExpr) (sz : whnf_step (KExpr.app e w) z) => \
                 whnf_step_app_inv e w z (RedW k bb z) sz \
                 (fun (A0 : KExpr) (body : KExpr) \
                 (heq : Eq KExpr e (KExpr.lam A0 body)) \
                 (_hz : Eq KExpr z (instantiate body w)) => \
                 Empty.rec (fun (_x : Empty) => RedW k bb z) \
                 (Eq.substType KExpr (fun (q : KExpr) => Neutral q) \
                 e (KExpr.lam A0 body) heq hn)) \
                 (fun (f2 : KExpr) (hf : beta_reduces e f2) \
                 (hz : Eq KExpr z (KExpr.app f2 w)) => \
                 Eq.substType KExpr (fun (q : KExpr) => RedW k bb q) \
                 (KExpr.app f2 w) z \
                 (Eq.symm KExpr z (KExpr.app f2 w) hz) \
                 (hall f2 (whnf_step.beta e f2 hf) w hw)) \
                 (fun (a2 : KExpr) (ha : beta_reduces w a2) \
                 (hz : Eq KExpr z (KExpr.app e a2)) => \
                 Eq.substType KExpr (fun (q : KExpr) => RedW k bb q) \
                 (KExpr.app e a2) z \
                 (Eq.symm KExpr z (KExpr.app e a2) hz) \
                 (ih a2 (whnf_step.beta w a2 ha) \
                 (redw_cr2_at_index k ty w a2 hw \
                 (whnf_step.beta w a2 ha)))) \
                 (fun (hi : iota_reduces (KExpr.app e w) z) => kio w z hi) \
                 (fun (hd : delta_reduces (KExpr.app e w) z) => kde w z hd))) \
                 x (redw_cr1_at_index k ty x hx) hx"
            ),
        )]
    }

    /// **`cr3` AT A NON-DEPENDENT PI TYPE — scratch, and `hcr3` discharged.**
    ///
    /// The previous probe proved the `pi` arm's pointwise half MODULO `cr3` at
    /// index `k`, which in a real proof is an outer `Nat.rec`'s induction
    /// hypothesis. This writes that induction, so nothing about `cr3` is assumed
    /// any more — only the ι/δ carriers this chain carries everywhere.
    ///
    /// It closes at a codomain that is non-dependent AND non-`pi`, and both
    /// conditions earn their place:
    ///
    /// * **non-dependent** makes `karg`'s transport the identity, which is the
    ///   previous probe's whole content;
    /// * **non-`pi`** makes `cr3` AT THE CODOMAIN trivial — `RedW k (sort 0) e`
    ///   IS `whnf_acc e` at every index, so `redw_cr3_at_sort_at_index` is
    ///   `whnf_acc.intro` twice. Without that the induction would need `cr3` at
    ///   the codomain, which is the law being proved.
    ///
    /// So the fragment is exactly the one where the recursion bottoms out
    /// immediately. `sort 0` is the concrete witness; any closed non-`pi`
    /// codomain would do.
    ///
    /// **The ι/δ carriers are stated at EVERY index, and that is forced.** Stating
    /// them at `whnf_acc z` fails with `whnf_acc vs Nat.rec`: the pointwise
    /// lemma wants `RedW k bb z`, which IS `whnf_acc z` — but only after reducing
    /// `RedW k`, and at a bound `k` the `Nat.rec` is stuck. The carriers are
    /// parameters of this definition, ahead of the induction, so they cannot
    /// mention `k`; quantifying the index inside them is the only spelling that
    /// typechecks.
    ///
    /// **What this is NOT.** `cr3` in general, which quantifies every type
    /// including `pi`s with dependent codomains — there the transport is real and
    /// §3k's residual stands. This is the fragment where the obstruction is
    /// absent, proved rather than assumed, which is what makes the obstruction's
    /// identity a measurement rather than a reading.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_cr3_nondependent_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        let pi = format!("(KExpr.pi ty {s0})");
        let pointwise =
            |t: &str| format!("(forall (x : KExpr), RedW k ty x -> RedW k {s0} (KExpr.app {t} x))");
        vec![
            (
                "redw_cr3_at_sort_at_index".to_string(),
                format!(
                    "def redw_cr3_at_sort_at_index : forall (k : Nat) (t : KExpr), \
                     Neutral t -> \
                     (forall (z : KExpr), whnf_step t z -> RedW k {s0} z) -> \
                     RedW k {s0} t := \
                     Nat.rec (fun (kk : Nat) => forall (t : KExpr), Neutral t -> \
                     (forall (z : KExpr), whnf_step t z -> RedW kk {s0} z) -> \
                     RedW kk {s0} t) \
                     (fun (t : KExpr) (_hn : Neutral t) \
                     (ha : forall (z : KExpr), whnf_step t z -> whnf_acc z) => \
                     whnf_acc.intro t ha) \
                     (fun (j : Nat) (_ih : forall (t : KExpr), Neutral t -> \
                     (forall (z : KExpr), whnf_step t z -> RedW j {s0} z) -> \
                     RedW j {s0} t) => \
                     fun (t : KExpr) (_hn : Neutral t) \
                     (ha : forall (z : KExpr), whnf_step t z -> whnf_acc z) => \
                     whnf_acc.intro t ha)"
                ),
            ),
            (
                "redw_cr3_at_a_nondependent_pi".to_string(),
                format!(
                    "def redw_cr3_at_a_nondependent_pi (ty : KExpr) \
                     (kio : forall (kk : Nat) (t0 : KExpr) (a0 : KExpr) (z : KExpr), \
                     iota_reduces (KExpr.app t0 a0) z -> RedW kk {s0} z) \
                     (kde : forall (kk : Nat) (t0 : KExpr) (a0 : KExpr) (z : KExpr), \
                     delta_reduces (KExpr.app t0 a0) z -> RedW kk {s0} z) : \
                     forall (k : Nat) (t : KExpr), Neutral t -> \
                     (forall (z : KExpr), whnf_step t z -> RedW k {pi} z) -> \
                     RedW k {pi} t := \
                     Nat.rec (fun (kk : Nat) => forall (t : KExpr), Neutral t -> \
                     (forall (z : KExpr), whnf_step t z -> RedW kk {pi} z) -> \
                     RedW kk {pi} t) \
                     (fun (t : KExpr) (_hn : Neutral t) \
                     (ha : forall (z : KExpr), whnf_step t z -> whnf_acc z) => \
                     whnf_acc.intro t ha) \
                     (fun (k : Nat) (_ih : forall (t : KExpr), Neutral t -> \
                     (forall (z : KExpr), whnf_step t z -> RedW k {pi} z) -> \
                     RedW k {pi} t) => \
                     fun (t : KExpr) (hn : Neutral t) \
                     (hall : forall (z : KExpr), whnf_step t z -> \
                     AndType (whnf_acc z) {pw_z}) => \
                     AndType.intro (whnf_acc t) {pw_t} \
                     (whnf_acc.intro t (fun (z : KExpr) (sz : whnf_step t z) => \
                     AndType.left (whnf_acc z) {pw_z} (hall z sz))) \
                     (redw_cr3_pointwise_at_a_nondependent_codomain k ty {s0} t hn \
                     (redw_cr3_at_sort_at_index k) \
                     (fun (e2 : KExpr) (st : whnf_step t e2) => \
                     AndType.right (whnf_acc e2) {pw_e2} (hall e2 st)) \
                     (fun (a0 : KExpr) (z : KExpr) \
                     (hi : iota_reduces (KExpr.app t a0) z) => kio k t a0 z hi) \
                     (fun (a0 : KExpr) (z : KExpr) \
                     (hd : delta_reduces (KExpr.app t a0) z) => kde k t a0 z hd)))",
                    pw_t = pointwise("t"),
                    pw_z = pointwise("z"),
                    pw_e2 = pointwise("e2"),
                ),
            ),
        ]
    }

    /// **`cr3` PROPAGATES UP a non-dependent pi — scratch, the general form.**
    ///
    /// `redw_cr3_at_a_nondependent_pi` fixes the codomain to `sort 0`, which
    /// makes `cr3` at the codomain free and hides that it was ever needed. This
    /// takes the codomain as a parameter and the codomain's `cr3` as a
    /// HYPOTHESIS, so the shape of the result is visible:
    ///
    /// > if `cr3` holds at `bb`, and `bb` does not mention its binder, then
    /// > `cr3` holds at `pi ty bb`.
    ///
    /// That is a PROPAGATION statement rather than a fact about one type, and it
    /// iterates: `sort 0` discharges the hypothesis at the base, so `cr3` follows
    /// at `pi ty (sort 0)`, then at `pi ty' (pi ty (sort 0))`, and so on up any
    /// non-dependent tower.
    ///
    /// **Non-dependence is now an explicit premise rather than a spelling.**
    /// `hnd` says `instantiate bb v = bb` for every `v`, and it is used exactly
    /// where the clause and the pointwise lemma disagree: the clause is stated at
    /// `instantiate bb x`, the lemma delivers `bb`. Each use is one
    /// `Eq.substType`. Where the fixed-`sort 0` version got this for free by
    /// computation, here it is carried and visible — which is the point, since
    /// `hnd` is precisely the assumption §3k identifies as the whole residual.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_cr3_propagates_sources() -> Vec<(String, String)> {
        let pi = "(KExpr.pi ty bb)";
        // The clause's pointwise half, as the CLAUSE states it (at `instantiate`).
        let pw_clause = |t: &str| {
            format!(
                "(forall (x : KExpr), RedW k ty x -> \
                 RedW k (instantiate bb x) (KExpr.app {t} x))"
            )
        };
        vec![(
            "redw_cr3_propagates_up_a_nondependent_pi".to_string(),
            format!(
                "def redw_cr3_propagates_up_a_nondependent_pi (ty : KExpr) (bb : KExpr) \
                 (hnd : forall (v : KExpr), Eq KExpr (instantiate bb v) bb) \
                 (hcod : forall (kk : Nat) (t : KExpr), Neutral t -> \
                 (forall (z : KExpr), whnf_step t z -> RedW kk bb z) -> RedW kk bb t) \
                 (kio : forall (kk : Nat) (t0 : KExpr) (a0 : KExpr) (z : KExpr), \
                 iota_reduces (KExpr.app t0 a0) z -> RedW kk bb z) \
                 (kde : forall (kk : Nat) (t0 : KExpr) (a0 : KExpr) (z : KExpr), \
                 delta_reduces (KExpr.app t0 a0) z -> RedW kk bb z) : \
                 forall (k : Nat) (t : KExpr), Neutral t -> \
                 (forall (z : KExpr), whnf_step t z -> RedW k {pi} z) -> \
                 RedW k {pi} t := \
                 Nat.rec (fun (kk : Nat) => forall (t : KExpr), Neutral t -> \
                 (forall (z : KExpr), whnf_step t z -> RedW kk {pi} z) -> \
                 RedW kk {pi} t) \
                 (fun (t : KExpr) (_hn : Neutral t) \
                 (ha : forall (z : KExpr), whnf_step t z -> whnf_acc z) => \
                 whnf_acc.intro t ha) \
                 (fun (k : Nat) (_ih : forall (t : KExpr), Neutral t -> \
                 (forall (z : KExpr), whnf_step t z -> RedW k {pi} z) -> \
                 RedW k {pi} t) => \
                 fun (t : KExpr) (hn : Neutral t) \
                 (hall : forall (z : KExpr), whnf_step t z -> \
                 AndType (whnf_acc z) {pwc_z}) => \
                 AndType.intro (whnf_acc t) {pwc_t} \
                 (whnf_acc.intro t (fun (z : KExpr) (sz : whnf_step t z) => \
                 AndType.left (whnf_acc z) {pwc_z} (hall z sz))) \
                 (fun (x : KExpr) (hx : RedW k ty x) => \
                 Eq.substType KExpr (fun (q : KExpr) => RedW k q (KExpr.app t x)) \
                 bb (instantiate bb x) \
                 (Eq.symm KExpr (instantiate bb x) bb (hnd x)) \
                 (redw_cr3_pointwise_at_a_nondependent_codomain k ty bb t hn \
                 (hcod k) \
                 (fun (e2 : KExpr) (st : whnf_step t e2) => \
                 fun (u : KExpr) (hu : RedW k ty u) => \
                 Eq.substType KExpr \
                 (fun (q : KExpr) => RedW k q (KExpr.app e2 u)) \
                 (instantiate bb u) bb (hnd u) \
                 (AndType.right (whnf_acc e2) {pwc_e2} (hall e2 st) u hu)) \
                 (fun (a0 : KExpr) (z : KExpr) \
                 (hi : iota_reduces (KExpr.app t a0) z) => kio k t a0 z hi) \
                 (fun (a0 : KExpr) (z : KExpr) \
                 (hd : delta_reduces (KExpr.app t a0) z) => kde k t a0 z hd) \
                 x hx)))",
                pwc_t = pw_clause("t"),
                pwc_z = pw_clause("z"),
                pwc_e2 = pw_clause("e2"),
            ),
        )]
    }

    #[cfg(test)]
    pub(super) fn candmodel_whnf_cr2_sources() -> Vec<(String, String)> {
        let step_arm = "fun (h : whnf_acc x) (st : whnf_step x y) => whnf_acc_step x y h st";
        let ih_ty = |t: &str| {
            format!("RedWInner (RedW k) x {t} -> whnf_step x y -> RedWInner (RedW k) y {t}")
        };
        let arm = |vals: &str, subs: &[&str]| {
            let ihs: String = subs
                .iter()
                .enumerate()
                .map(|(n, t)| format!(" (j{n} : {})", ih_ty(t)))
                .collect();
            format!("(fun ({vals}){ihs} => {step_arm})")
        };
        let pi_arm = format!(
            "(fun (ty : KExpr) (bb : KExpr) (j0 : {ihty}) (j1 : {ihbb}) => \
             fun (hh : RedWInner (RedW k) x (KExpr.pi ty bb)) (st : whnf_step x y) => \
             AndType.intro (whnf_acc y) \
             (forall (z : KExpr), RedW k ty z -> \
             RedW k (instantiate bb z) (KExpr.app y z)) \
             (whnf_acc_step x y \
             (AndType.left (whnf_acc x) \
             (forall (z : KExpr), RedW k ty z -> \
             RedW k (instantiate bb z) (KExpr.app x z)) hh) st) \
             (fun (z : KExpr) (hz : RedW k ty z) => \
             ih (instantiate bb z) (KExpr.app x z) (KExpr.app y z) \
             (AndType.right (whnf_acc x) \
             (forall (w : KExpr), RedW k ty w -> \
             RedW k (instantiate bb w) (KExpr.app x w)) hh z hz) \
             (whnfStep_app_left x y z st)))",
            ihty = ih_ty("ty"),
            ihbb = ih_ty("bb"),
        );
        let body_open = format!(
            "Nat.rec (fun (kk : Nat) => forall (T : KExpr) (x : KExpr) (y : KExpr), \
             RedW kk T x -> whnf_step x y -> RedW kk T y) \
             (fun (T : KExpr) (x : KExpr) (y : KExpr) (h : whnf_acc x) \
             (st : whnf_step x y) => whnf_acc_step x y h st) \
             (fun (k : Nat) (ih : forall (T : KExpr) (x : KExpr) (y : KExpr), \
             RedW k T x -> whnf_step x y -> RedW k T y) => \
             fun (T : KExpr) (x : KExpr) (y : KExpr) => \
             OptionType.rec KExpr \
             (fun (o : OptionType KExpr) => \
             RedWClause (RedW k) x o -> whnf_step x y -> RedWClause (RedW k) y o) \
             ({step_arm}) \
             (fun (U : KExpr) => \
             KExpr.rec (fun (t0 : KExpr) => \
             RedWInner (RedW k) x t0 -> whnf_step x y -> RedWInner (RedW k) y t0) \
             {sort} {bvar} {app} {lam} {pi_arm} {konst} {let_} {proj} {mvar} U) \
             (whnf_fuel_red_wh3 the_red_env (Nat.succ k) T))",
            sort = arm("l : Level", &[]),
            bvar = arm("i : Nat", &[]),
            app = arm("ff : KExpr) (aa : KExpr", &["ff", "aa"]),
            lam = arm("lty : KExpr) (lb : KExpr", &["lty", "lb"]),
            konst = arm("nm : Name) (us : ListType Level", &[]),
            let_ = arm(
                "zty : KExpr) (zv : KExpr) (zb : KExpr",
                &["zty", "zv", "zb"],
            ),
            proj = arm("ps : Name) (pidx : Nat) (sub : KExpr", &["sub"]),
            mvar = arm("v : Nat", &[]),
        );
        // The `Nat.rec` establishes cr2 AT A FIXED INDEX -- that is literally its
        // motive. `redw_cr2` then reads off the `RedWStep` form in one line.
        // Both are registered because the indexed form is what an argument
        // INSIDE the recursion needs: the `pi` arm's `karg` case has
        // `RedW k ty x` and a step, and wants `RedW k ty a2`, at ONE index.
        // `redw_cr1_at_index` exists for the same reason.
        vec![
            (
                "redw_cr2_at_index".to_string(),
                format!(
                    "def redw_cr2_at_index : forall (k : Nat) (T : KExpr) \
                     (x : KExpr) (y : KExpr), \
                     RedW k T x -> whnf_step x y -> RedW k T y := {body_open}"
                ),
            ),
            (
                "redw_cr2".to_string(),
                "def redw_cr2 (TT : KExpr) (e : KExpr) (e2 : KExpr) \
                 (h : RedWStep TT e) (st : whnf_step e e2) : RedWStep TT e2 := \
                 fun (n : Nat) => redw_cr2_at_index n TT e e2 (h n) st"
                    .to_string(),
            ),
        ]
    }

    #[cfg(test)]
    pub(super) fn candmodel_whnf_pi_elim_sources() -> Vec<(String, String)> {
        vec![(
            "redw_pi_elim".to_string(),
            "def redw_pi_elim (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr) \
             (hf : RedWStep (KExpr.pi A B) f) (ha : RedWStep A a) : \
             RedWStep (instantiate B a) (KExpr.app f a) := \
             fun (n : Nat) => \
             AndType.right (whnf_acc f) \
             (forall (x : KExpr), RedW n A x -> \
             RedW n (instantiate B x) (KExpr.app f x)) \
             (hf (Nat.succ n)) a (ha n)"
                .to_string(),
        )]
    }

    /// **`redTypeStep` at the WHNF-INDEXED candidate, under its fuel side
    /// condition — scratch.**
    ///
    /// `redstep_redTypeStep_refuted` proves the law FALSE at the head-indexed
    /// family, by a beta redex whose contractum is a `pi`. This asks what
    /// survives when the clause is selected by the type's whnf instead.
    ///
    /// The honest statement is conditional, and §3k derives why it must be: the
    /// only whnf available STARVES, so the step index doubles as the fuel, and a
    /// type step shifts it (`whnf (n+1) T = whnf n T2`). Given that the two
    /// types' whnfs AGREE at the fuel in hand, the two clauses are not merely
    /// equivalent — they are the SAME TYPE, and the law degenerates to a
    /// transport along that equation.
    ///
    /// Both directions come out of one `Eq.substType`, which is why they are
    /// registered as a pair rather than an `AndType`: the field's shape is an
    /// `AndType` of two implications, and each is this transport run one way.
    ///
    /// **What it would establish, stated narrowly.** That `redTypeStep` moves
    /// from the PROVED FALSE row to the CONDITIONAL row — the middle row of
    /// §3d's three-way split, where five laws already sit at the type-blind
    /// candidate. A law holding under a side condition the field does not carry
    /// is not a law the field has. It is, however, a different object from one
    /// with a counterexample, and the split is what this file tracks.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_typestep_sources() -> Vec<(String, String)> {
        let blind = "whnf_acc e";
        let arm = |vals: &str| format!("(fun ({vals}) => {blind})");
        // The clause as a function OF the whnf result -- literally the body of
        // `RedW`'s successor case with the scrutinee abstracted. `RedW (succ n)
        // T e` is defeq to this applied at `whnf_fuel_red_wh3 .. (succ n) T`.
        let clause = format!(
            "(fun (o : OptionType KExpr) => \
             OptionType.rec KExpr (fun (_o : OptionType KExpr) => Type) \
             ({blind}) \
             (fun (U : KExpr) => \
             KExpr.rec (fun (_t : KExpr) => Type) \
             {sort} {bvar} {app} {lam} \
             (fun (ty : KExpr) (bb : KExpr) (i1 : Type) (i2 : Type) => \
             AndType (whnf_acc e) \
             (forall (x : KExpr), RedW n ty x -> \
             RedW n (instantiate bb x) (KExpr.app e x))) \
             {konst} {let_} {proj} {mvar} \
             U) o)",
            sort = arm("l : Level"),
            bvar = arm("i : Nat"),
            app = arm("ff : KExpr) (aa : KExpr) (i1 : Type) (i2 : Type"),
            lam = arm("lty : KExpr) (lb : KExpr) (i1 : Type) (i2 : Type"),
            konst = arm("nm : Name) (us : ListType Level"),
            let_ =
                arm("zty : KExpr) (zv : KExpr) (zb : KExpr) (i1 : Type) (i2 : Type) (i3 : Type",),
            proj = arm("ps : Name) (pidx : Nat) (sub : KExpr) (i1 : Type"),
            mvar = arm("v : Nat"),
        );
        let hyp = "(hagree : Eq (OptionType KExpr) \
                   (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T) \
                   (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T2))";
        vec![
            (
                "redw_typeStep_fwd_under_agreeing_whnf".to_string(),
                format!(
                    "def redw_typeStep_fwd_under_agreeing_whnf (n : Nat) (T : KExpr) \
                     (T2 : KExpr) (e : KExpr) {hyp} \
                     (h : RedW (Nat.succ n) T e) : RedW (Nat.succ n) T2 e := \
                     Eq.substType (OptionType KExpr) {clause} \
                     (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T) \
                     (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T2) hagree h"
                ),
            ),
            (
                "redw_typeStep_bwd_under_agreeing_whnf".to_string(),
                format!(
                    "def redw_typeStep_bwd_under_agreeing_whnf (n : Nat) (T : KExpr) \
                     (T2 : KExpr) (e : KExpr) {hyp} \
                     (h : RedW (Nat.succ n) T2 e) : RedW (Nat.succ n) T e := \
                     Eq.substType (OptionType KExpr) {clause} \
                     (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T2) \
                     (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T) \
                     (Eq.symm (OptionType KExpr) \
                     (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T) \
                     (whnf_fuel_red_wh3 the_red_env (Nat.succ n) T2) hagree) h"
                ),
            ),
        ]
    }

    /// **`pi_intro`'s residual at the WHNF-INDEXED candidate — scratch.**
    ///
    /// §3k predicts the residual is UNCHANGED by moving from head-indexing to
    /// whnf-indexing, on the grounds that a quantifier position should not care
    /// how the type is inspected. This measures that instead of asserting it,
    /// the same way `redstep_pi_intro_per_index` did at the previous candidate:
    /// prove the STRENGTHENED form and read off which premises had to be added.
    ///
    /// If the same two suffice — `whnf_acc f` outright, and the pointwise
    /// premise PER INDEX where the field states it at `RedWStep` — then the
    /// residual is stable across two structurally different candidates, which is
    /// evidence it belongs to the FIELD rather than to either family. If a THIRD
    /// premise were needed here, the whnf indirection would have cost something
    /// and that would be the finding instead.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_pi_intro_sources() -> Vec<(String, String)> {
        vec![(
            "redw_pi_intro_per_index".to_string(),
            "def redw_pi_intro_per_index (A : KExpr) (B : KExpr) (f : KExpr) \
             (hw : whnf_acc f) \
             (hp : forall (k : Nat) (x : KExpr), RedW k A x -> \
             RedW k (instantiate B x) (KExpr.app f x)) : \
             RedWStep (KExpr.pi A B) f := \
             fun (n : Nat) => \
             Nat.rec (fun (k : Nat) => RedW k (KExpr.pi A B) f) hw \
             (fun (k : Nat) (_ih : RedW k (KExpr.pi A B) f) => \
             AndType.intro (whnf_acc f) \
             (forall (x : KExpr), RedW k A x -> \
             RedW k (instantiate B x) (KExpr.app f x)) hw (hp k)) n"
                .to_string(),
        )]
    }

    /// **`RedW` is NOT the blind family in disguise, plus `red_sort` — scratch.**
    ///
    /// The question that has to be asked before any `RedW` result is trusted:
    /// is the `pi` clause ever REACHED? `RedW`'s successor case selects on
    /// `whnf_fuel_red_wh3`, and BOTH its fallbacks — `none`-starvation and every
    /// non-`pi` whnf — collapse to bare `whnf_acc e`. If the `some (pi ..)` arm
    /// were unreachable, `RedW` would be the type-blind family wearing an
    /// indirection, every law measured at it would be a law about `whnf_acc`,
    /// and `pi_elim` "holding" would be worthless.
    ///
    /// `redw_pi_elim` elaborating already implies the arm is reached — the
    /// `AndType.right` projection would not typecheck otherwise — but that is an
    /// inference from a proof term about something else. `redw_pi_clause_reached`
    /// says it directly, as an `Eq Type` discharged by `Eq.refl`: at index 1 and
    /// a literal `pi`, `RedW` IS the `AndType`, not `whnf_acc`.
    ///
    /// This is the same hazard the vacuity firewall exists for, asked of a
    /// scratch candidate rather than a registered relation.
    ///
    /// `redw_red_sort` rides along: a third law at this candidate, and a one-line
    /// `Nat.rec` for the same reason it was at `RedStep` — a `sort` is already
    /// its own whnf, so the clause is the `sort` arm at every index.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_nonvacuity_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        let pi = format!("(KExpr.pi {s0} {s0})");
        vec![
            (
                "redw_pi_clause_reached".to_string(),
                format!(
                    "def redw_pi_clause_reached (e : KExpr) : \
                     Eq Type (RedW (Nat.succ Nat.zero) {pi} e) \
                     (AndType (whnf_acc e) \
                     (forall (x : KExpr), RedW Nat.zero {s0} x -> \
                     RedW Nat.zero {s0} (KExpr.app e x))) := \
                     Eq.refl Type (AndType (whnf_acc e) \
                     (forall (x : KExpr), RedW Nat.zero {s0} x -> \
                     RedW Nat.zero {s0} (KExpr.app e x)))"
                ),
            ),
            (
                "redw_red_sort".to_string(),
                "def redw_red_sort (nn : Level) (e : KExpr) (h : whnf_acc e) : \
                 RedWStep (KExpr.sort nn) e := \
                 fun (n : Nat) => \
                 Nat.rec (fun (k : Nat) => RedW k (KExpr.sort nn) e) h \
                 (fun (k : Nat) (_ih : RedW k (KExpr.sort nn) e) => h) n"
                    .to_string(),
            ),
        ]
    }
}
