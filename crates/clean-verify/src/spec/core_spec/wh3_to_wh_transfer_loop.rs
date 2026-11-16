// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Three-way to two-way TRANSFER — the STEP's tail, the LOOP and the ALGORITHM.
//!
//! Second of two modules split out of `wh3_to_wh_transfer.rs` for SIZE alone;
//! see `wh3_to_wh_transfer_step.rs` for why and for the guarantee that no
//! emitted string changed. This file carries the head-stuck lemma onward
//! through the loop and algorithm transfers (items 4 through 8).

use crate::spec::Specification;

impl Specification {
    /// **The head's own stuckness, and nothing else** — the transport that
    /// makes the `app` arm cheap.
    ///
    /// **Not named `wh3_app_head_stuck_forces_head_stuck`, because that name
    /// is taken.** `wh3_stuck_head.rs` registers exactly this statement at a
    /// FIXED `the_red_env` and a fixed budget's pre-pass
    /// (`fun e2 => whnf_fuel_red_wh3 the_red_env k e2`). This one is the
    /// same argument parametric in `renv` and the pre-pass, which is what a
    /// transfer quantified over two arbitrary pre-passes needs; registering
    /// it under the taken name would abort the spec build on the duplicate.
    ///
    /// The tree's own precedent says to do it this way. `budget_induction_prereqs.rs`
    /// carries `wh3_stuck_app_forces_iota_stuck`, whose description is explicit:
    /// *"Splitting the `Eq.subst` out of the nine-arm recursion keeps eight of
    /// those nine arms literally the identity."* This is that split, stated
    /// parametrically in `renv` and the pre-pass instead of at a fixed budget.
    ///
    /// The motive here carries ONE small equation. The version that carried the
    /// whole two-way goal through all nine arms had to ι-reduce and compare two
    /// nine-arm recursors per arm, and that is what made it expensive.
    pub(super) fn wh3_to_wh_head_stuck_src() -> String {
        let o = "OptionType KExpr";
        let hyp = |z: &str| {
            format!("@Eq WhStepR (reduce_app_head_red_wh3 renv wh3 a {z} c3) WhStepR.wstuck")
        };
        let concl = "@Eq WhStepR c3 WhStepR.wstuck";
        let motive = format!("(fun (z : KExpr) => {} -> {concl})", hyp("z"));
        let arm = |binders: &str, z: &str| {
            format!(
                "(fun {binders} (hz : {}) => opt_app_ilift3_stuck_inv renv wh3 {z} a c3 hz)",
                hyp(z)
            )
        };
        let at = |z: &str| format!("({} -> {concl})", hyp(z));
        format!(
            "def wh3_app_head_stuck_gives_head_stuck (renv : RedEnv) (wh3 : KExpr -> {o}) \
             (a : KExpr) (c3 : WhStepR) (f : KExpr) (h : {hyp_f}) : {concl} := \
             @KExpr.rec {motive} \
             {a_sort} {a_bvar} {a_app} {a_lam} {a_pi} {a_const} {a_let} {a_proj} {a_lit} \
             f h",
            hyp_f = hyp("f"),
            a_sort = arm("(n : Level)", "(KExpr.sort n)"),
            a_bvar = arm("(i : Nat)", "(KExpr.bvar i)"),
            a_app = arm(
                &format!(
                    "(g : KExpr) (b : KExpr) (_cg : {}) (_cb : {})",
                    at("g"),
                    at("b")
                ),
                "(KExpr.app g b)",
            ),
            a_lam = format_args!(
                "(fun (ty : KExpr) (b : KExpr) (_cty : {mt}) (_cb : {mb}) \
                 (hz : @Eq WhStepR (WhStepR.wstep (instantiate b a)) WhStepR.wstuck) => \
                 wh_stuck_ne_step (instantiate b a) ({concl}) \
                 (Eq.symm WhStepR (WhStepR.wstep (instantiate b a)) WhStepR.wstuck hz))",
                mt = at("ty"),
                mb = at("b"),
            ),
            a_pi = arm(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {}) (_cb : {})",
                    at("ty"),
                    at("b")
                ),
                "(KExpr.pi ty b)",
            ),
            a_const = arm("(n : Name) (us : ListType Level)", "(KExpr.const n us)"),
            a_let = arm(
                &format!(
                    "(ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) (_c3 : {})",
                    at("ty"),
                    at("v"),
                    at("b")
                ),
                "(KExpr.let_ ty v b)",
            ),
            a_proj = arm(
                &format!("(s : Name) (i : Nat) (sub : KExpr) (_csub : {})", at("sub")),
                "(KExpr.proj s i sub)",
            ),
            a_lit = arm("(v : Nat)", "(KExpr.lit v)"),
        )
    }

    /// The `app` arm **at the literals** — where eight arms collapse to one
    /// chain application each and the ilift convoy disappears entirely.
    ///
    /// With `c3` known to be `WhStepR.wstuck` and `c2` known to be `none`, the
    /// two app-head reducers ι-reduce, at every non-`lam` head `z`, to
    /// `iota_reduct_whc3 (red_rec renv) wh3 (app z a)` and
    /// `iota_reduct_whc (red_rec renv) wh2 (app z a)` — because
    /// `opt_app_ilift3`'s `wstuck` arm and `opt_app_ilift_wh`'s `none` arm ARE
    /// those chains. So each arm is one `wh3_chain_stuck_gives_none`, with no
    /// `WhStepR.rec` between them.
    ///
    /// That is the whole saving. [`Self::wh3_to_wh_ilift_src`] remains the
    /// general statement — it is what the SUCCESS direction needs, where the
    /// head result cannot be transported to a literal first — but this
    /// direction does not have to pay for it.
    pub(super) fn wh3_to_wh_app_head_lit_src() -> String {
        let o = "OptionType KExpr";
        let hyp = |z: &str| {
            format!(
                "@Eq WhStepR (reduce_app_head_red_wh3 renv wh3 a {z} WhStepR.wstuck) \
                 WhStepR.wstuck"
            )
        };
        let goal = |z: &str| {
            format!(
                "@Eq ({o}) (reduce_app_head_red_wh renv wh2 a {z} (@OptionType.none KExpr)) \
                 (@OptionType.none KExpr)"
            )
        };
        let motive = format!("(fun (z : KExpr) => {} -> {})", hyp("z"), goal("z"));
        let at = |z: &str| format!("({} -> {})", hyp(z), goal(z));
        let arm = |binders: &str, z: &str| {
            format!(
                "(fun {binders} (hz : {}) => \
                 wh3_chain_stuck_gives_none renv wh3 wh2 hw (KExpr.app {z} a) hz)",
                hyp(z)
            )
        };
        format!(
            "def wh3_app_head_stuck_gives_none_at_lit (renv : RedEnv) (wh3 : KExpr -> {o}) \
             (wh2 : KExpr -> {o}) \
             (hw : forall (x : KExpr) (y : KExpr), @Eq ({o}) (wh3 x) (@OptionType.some KExpr y) -> \
             @Eq ({o}) (wh2 x) (@OptionType.some KExpr y)) \
             (a : KExpr) (f : KExpr) (h : {hyp_f}) : {goal_f} := \
             @KExpr.rec {motive} \
             {a_sort} {a_bvar} {a_app} {a_lam} {a_pi} {a_const} {a_let} {a_proj} {a_lit} \
             f h",
            hyp_f = hyp("f"),
            goal_f = goal("f"),
            a_sort = arm("(n : Level)", "(KExpr.sort n)"),
            a_bvar = arm("(i : Nat)", "(KExpr.bvar i)"),
            a_app = arm(
                &format!(
                    "(g : KExpr) (b : KExpr) (_cg : {}) (_cb : {})",
                    at("g"),
                    at("b")
                ),
                "(KExpr.app g b)",
            ),
            a_lam = format_args!(
                "(fun (ty : KExpr) (b : KExpr) (_cty : {mt}) (_cb : {mb}) \
                 (hz : @Eq WhStepR (WhStepR.wstep (instantiate b a)) WhStepR.wstuck) => \
                 wh_stuck_ne_step (instantiate b a) ({g}) \
                 (Eq.symm WhStepR (WhStepR.wstep (instantiate b a)) WhStepR.wstuck hz))",
                mt = at("ty"),
                mb = at("b"),
                g = goal("(KExpr.lam ty b)"),
            ),
            a_pi = arm(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {}) (_cb : {})",
                    at("ty"),
                    at("b")
                ),
                "(KExpr.pi ty b)",
            ),
            a_const = arm("(n : Name) (us : ListType Level)", "(KExpr.const n us)"),
            a_let = arm(
                &format!(
                    "(ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) (_c3 : {})",
                    at("ty"),
                    at("v"),
                    at("b")
                ),
                "(KExpr.let_ ty v b)",
            ),
            a_proj = arm(
                &format!("(s : Name) (i : Nat) (sub : KExpr) (_csub : {})", at("sub")),
                "(KExpr.proj s i sub)",
            ),
            a_lit = arm("(v : Nat)", "(KExpr.lit v)"),
        )
    }

    /// The `app` arm as the assembly consumes it: the two transports around
    /// [`Self::wh3_to_wh_app_head_lit_src`].
    ///
    /// Same statement as the direct version, so the assembly does not change —
    /// only the cost. `wh3_app_head_stuck_gives_head_stuck` gives `c3 =
    /// wstuck`; the induction hypothesis turns that into `c2 = none`; and the
    /// two `Eq.substType`s move the hypothesis and the goal to those literals,
    /// where the cheap recursor applies.
    pub(super) fn wh3_to_wh_app_head_via_lit_src() -> String {
        let o = "OptionType KExpr";
        format!(
            "def wh3_app_head_stuck_gives_none (renv : RedEnv) (wh3 : KExpr -> {o}) \
             (wh2 : KExpr -> {o}) \
             (hw : forall (x : KExpr) (y : KExpr), @Eq ({o}) (wh3 x) (@OptionType.some KExpr y) -> \
             @Eq ({o}) (wh2 x) (@OptionType.some KExpr y)) \
             (a : KExpr) (c3 : WhStepR) (c2 : {o}) \
             (ih : @Eq WhStepR c3 WhStepR.wstuck -> @Eq ({o}) c2 (@OptionType.none KExpr)) \
             (f : KExpr) \
             (h : @Eq WhStepR (reduce_app_head_red_wh3 renv wh3 a f c3) WhStepR.wstuck) : \
             @Eq ({o}) (reduce_app_head_red_wh renv wh2 a f c2) (@OptionType.none KExpr) := \
             Eq.substType ({o}) \
             (fun (z : {o}) => \
             @Eq ({o}) (reduce_app_head_red_wh renv wh2 a f z) (@OptionType.none KExpr)) \
             (@OptionType.none KExpr) c2 \
             (Eq.symm ({o}) c2 (@OptionType.none KExpr) \
             (ih (wh3_app_head_stuck_gives_head_stuck renv wh3 a c3 f h))) \
             (wh3_app_head_stuck_gives_none_at_lit renv wh3 wh2 hw a f \
             (Eq.substType WhStepR \
             (fun (q : WhStepR) => \
             @Eq WhStepR (reduce_app_head_red_wh3 renv wh3 a f q) WhStepR.wstuck) \
             c3 WhStepR.wstuck \
             (wh3_app_head_stuck_gives_head_stuck renv wh3 a c3 f h) h))"
        )
    }

    /// **ITEM 4** — `whnf_fuel_red_wh3_to_wh`: the LOOP transfer.
    ///
    /// `Nat.rec` on the fuel, and the arm that matters is `succ k`, where the
    /// induction hypothesis
    ///
    /// ```text
    /// forall (x y : KExpr), whnf_fuel_red_wh3 renv k x = some y
    ///                    -> whnf_fuel_red_wh  renv k x = some y
    /// ```
    ///
    /// **IS the `hw` that items 2 and 3 take as a parameter** — the same type,
    /// binder for binder. Nothing else in the development supplies it, which is
    /// why every arm lemma carries it rather than closing over a fixed pre-pass.
    /// Both loops pass THEMSELVES at `k` as their pre-pass, so at `succ k` the
    /// hypothesis is available exactly where the step transfer needs it.
    ///
    /// The convoy carries its own EQUATION (`Eq WhStepR s3 q`, discharged with
    /// `Eq.refl` at the call) as well as the dispatch, because the two arms that
    /// do work need to know WHICH step result they are in, not just what the
    /// dispatch computed from it.
    ///
    /// **The fuel is never raised.** The target at `succ k` has both legs at
    /// `k` and the induction hypothesis is used at `k` only, which is the whole
    /// reason this route touches monotonicity nowhere — see §1 blocker B of the
    /// design doc.
    pub(super) fn wh3_to_wh_loop_src() -> String {
        let o = "OptionType KExpr";
        // Eta-expanded, as `reduce_app_head_wh3_par` writes it: the loop at one
        // less fuel, as a FUNCTION, is what both loops hand their step.
        //
        // **This rests on the kernel having lambda eta**, and it is worth saying
        // because nothing else here does. What the `Nat.rec` hands the succ arm
        // is the recursor application itself, `Nat.rec … k`; what is written
        // below is `fun e2 => whnf_fuel_red_wh3 renv k e2`, which δ-unfolds to
        // `fun e2 => (Nat.rec … k) e2`. Those are equal only up to η.
        // `crates/clean-kernel/src/tc/eta.rs` supplies it —
        // `try_eta_expansion_impl`, lambda eta, `λ x. f x ≡ f`. Writing the
        // pre-pass unexpanded does not avoid the obligation: a partially applied
        // `def` unfolds to the same η-expanded shape.
        let ih3 = "(fun (e2 : KExpr) => whnf_fuel_red_wh3 renv k e2)";
        let ih2 = "(fun (e2 : KExpr) => whnf_fuel_red_wh renv k e2)";
        let s3 = format!("(reduce_once_red_wh3 renv {ih3} e)");
        let s2 = format!("(reduce_once_red_wh renv {ih2} e)");
        let goal = format!("@Eq ({o}) (loop_dispatch {s2} e {ih2}) (@OptionType.some KExpr y)");
        let motive_n = |m: &str| {
            format!(
                "(fun ({m} : Nat) => forall (e : KExpr) (y : KExpr), \
                 @Eq ({o}) (whnf_fuel_red_wh3 renv {m} e) (@OptionType.some KExpr y) -> \
                 @Eq ({o}) (whnf_fuel_red_wh renv {m} e) (@OptionType.some KExpr y))"
            )
        };
        let dispatched = |q: &str| format!("(wh_dispatch3 {q} e {ih3})");
        let conv_motive = format!(
            "(fun (q : WhStepR) => @Eq WhStepR {s3} q -> \
             @Eq ({o}) {d} (@OptionType.some KExpr y) -> {goal})",
            d = dispatched("q"),
        );
        // wstuck: the three-way loop announces normality, so the two-way step
        // declines by item 2 and the two-way dispatch announces the SAME term.
        let arm_stuck = format!(
            "(fun (heq : @Eq WhStepR {s3} WhStepR.wstuck) \
             (hd : @Eq ({o}) {d} (@OptionType.some KExpr y)) => \
             Eq.substType ({o}) \
             (fun (z : {o}) => @Eq ({o}) (loop_dispatch z e {ih2}) (@OptionType.some KExpr y)) \
             (@OptionType.none KExpr) {s2} \
             (Eq.symm ({o}) {s2} (@OptionType.none KExpr) \
             (wh_step3_stuck_to_none renv {ih3} {ih2} ihn e heq)) hd)",
            d = dispatched("WhStepR.wstuck"),
        );
        // wstarved: the three-way loop reports honest exhaustion, so the
        // hypothesis is `none = some y` and there is nothing to transfer. This
        // is the arm the two-way loop cannot express, and it is why the
        // transfer is one-directional.
        let arm_starved = format!(
            "(fun (_heq : @Eq WhStepR {s3} WhStepR.wstarved) \
             (hd : @Eq ({o}) {d} (@OptionType.some KExpr y)) => \
             option_none_ne_some KExpr y ({goal}) hd)",
            d = dispatched("WhStepR.wstarved"),
        );
        // wstep: both loops continue at the same reduct and the SAME budget.
        let arm_step = format!(
            "(fun (e2 : KExpr) (heq : @Eq WhStepR {s3} (WhStepR.wstep e2)) \
             (hd : @Eq ({o}) {d} (@OptionType.some KExpr y)) => \
             Eq.substType ({o}) \
             (fun (z : {o}) => @Eq ({o}) (loop_dispatch z e {ih2}) (@OptionType.some KExpr y)) \
             (@OptionType.some KExpr e2) {s2} \
             (Eq.symm ({o}) {s2} (@OptionType.some KExpr e2) \
             (wh_step3_step_to_some renv {ih3} {ih2} ihn e e2 heq)) \
             (ihn e2 y hd))",
            d = dispatched("(WhStepR.wstep e2)"),
        );
        format!(
            "def whnf_fuel_red_wh3_to_wh (renv : RedEnv) (n : Nat) : \
             forall (e : KExpr) (y : KExpr), \
             @Eq ({o}) (whnf_fuel_red_wh3 renv n e) (@OptionType.some KExpr y) -> \
             @Eq ({o}) (whnf_fuel_red_wh renv n e) (@OptionType.some KExpr y) := \
             @Nat.rec {motive} \
             (fun (e : KExpr) (y : KExpr) \
             (h : @Eq ({o}) (@OptionType.none KExpr) (@OptionType.some KExpr y)) => \
             option_none_ne_some KExpr y \
             (@Eq ({o}) (whnf_fuel_red_wh renv Nat.zero e) (@OptionType.some KExpr y)) h) \
             (fun (k : Nat) (ihn : {motive_k}) (e : KExpr) (y : KExpr) \
             (h : @Eq ({o}) {d3} (@OptionType.some KExpr y)) => \
             @WhStepR.rec {conv_motive} {arm_stuck} {arm_starved} {arm_step} \
             {s3} (@Eq.refl WhStepR {s3}) h) \
             n",
            motive = motive_n("m"),
            motive_k = format_args!(
                "forall (e : KExpr) (y : KExpr), \
                 @Eq ({o}) (whnf_fuel_red_wh3 renv k e) (@OptionType.some KExpr y) -> \
                 @Eq ({o}) (whnf_fuel_red_wh renv k e) (@OptionType.some KExpr y)"
            ),
            d3 = dispatched(&s3),
        )
    }

    /// **ITEM 5** — `def_eq_fuel_wh_of_struct`, derived from its three-way twin
    /// by whole-identifier substitution rather than by transcribing the proof.
    ///
    /// The introduction rule: if the loop takes `a` to `na` and `b` to `nb` at
    /// fuel `k`, and the structural grid accepts `na` against `nb` with the
    /// fuel-`k` algorithm as comparator, the algorithm accepts `a` against `b`
    /// at `succ k`. Both algorithms have the same shape one substitution apart,
    /// so the proof transports verbatim — and the assertions below are what make
    /// that a checked claim instead of a hope: every pattern must be present,
    /// and no three-way identifier may survive.
    pub(super) fn wh3_to_wh_of_struct_src() -> String {
        let mut s = super::defeq_fuel_wh3_mono::SRC_WH3_OF_STRUCT.to_string();
        // Longest first, so a prefix never wins over the identifier containing
        // it — the rule `retarget_to_wh3` states for the other direction.
        for (from, to) in [
            ("def_eq_fuel_wh3_of_struct", "def_eq_fuel_wh_of_struct"),
            ("def_eq_fuel_wh3_succ", "def_eq_fuel_wh_succ"),
            ("def_eq_fuel_wh3", "def_eq_fuel_wh"),
            ("whnf_fuel_red_wh3", "whnf_fuel_red_wh"),
        ] {
            assert!(
                s.contains(from),
                "{from} absent — the three-way source moved and this substitution is stale"
            );
            s = s.replace(from, to);
        }
        assert!(
            !s.contains("wh3"),
            "a three-way identifier survived the substitution"
        );
        s
    }

    /// **ITEM 6** — `def_eq_fuel_wh3_to_wh`: the ALGORITHM transfer.
    ///
    /// `Nat.rec` on the fuel, and it is EASIER than its three-way twin, for the
    /// reason §3 of the design doc gives: the target lands at `succ j` with both
    /// legs at `j`, so nothing is raised and `def_eq_fuel_succ_mono` is never
    /// reached. The whole content is two option convoys and three appeals:
    ///
    /// * each whnf leg transfers by **item 4**, at the same fuel;
    /// * the structural layer transfers by `def_eq_struct_mono`, which needs NO
    ///   port because `def_eq_struct` is parametric in its comparator and the
    ///   induction hypothesis IS the pointwise implication it wants;
    /// * the layer folds back up by **item 5**.
    ///
    /// The `none` arms are refuted rather than handled: a leg that fails to
    /// reduce makes the algorithm `false`, so the hypothesis is `false = true`.
    /// `bool_false_ne_true` is the Prop variant, because the goal is an `Eq`.
    pub(super) fn wh3_to_wh_defeq_src() -> String {
        let o = "OptionType KExpr";
        let env = "the_red_env";
        let leg3 = |x: &str| format!("(whnf_fuel_red_wh3 {env} k {x})");
        let goal = format!("@Eq Bool (def_eq_fuel_wh {env} (Nat.succ k) a b) Bool.true");
        let grid = |na: &str, nb: &str| {
            format!("@Eq Bool (def_eq_struct (def_eq_fuel_wh3 {env} k) {na} {nb}) Bool.true")
        };
        // The body of `def_eq_fuel_wh3 env (succ k) a b`, with the outer
        // scrutinee abstracted so the convoy's motive can name it.
        let body = |oa: &str| {
            format!(
                "(@OptionType.rec KExpr (fun (_ : {o}) => Bool) Bool.false \
                 (fun (na : KExpr) => @OptionType.rec KExpr (fun (_ : {o}) => Bool) Bool.false \
                 (fun (nb : KExpr) => def_eq_struct (def_eq_fuel_wh3 {env} k) na nb) \
                 {legb}) {oa})",
                legb = leg3("b"),
            )
        };
        let inner_body = |ob: &str| {
            format!(
                "(@OptionType.rec KExpr (fun (_ : {o}) => Bool) Bool.false \
                 (fun (nb : KExpr) => def_eq_struct (def_eq_fuel_wh3 {env} k) na nb) {ob})"
            )
        };
        let inner = format!(
            "(@OptionType.rec KExpr \
             (fun (ob : {o}) => @Eq ({o}) {legb} ob -> @Eq Bool {ib} Bool.true -> {goal}) \
             (fun (_hb : @Eq ({o}) {legb} (@OptionType.none KExpr)) \
             (hf : @Eq Bool Bool.false Bool.true) => bool_false_ne_true ({goal}) hf) \
             (fun (nb : KExpr) (hb3 : @Eq ({o}) {legb} (@OptionType.some KExpr nb)) \
             (hg : {grid}) => \
             def_eq_fuel_wh_of_struct k a b na nb \
             (whnf_fuel_red_wh3_to_wh {env} k a na ha3) \
             (whnf_fuel_red_wh3_to_wh {env} k b nb hb3) \
             (def_eq_struct_mono (def_eq_fuel_wh3 {env} k) (def_eq_fuel_wh {env} k) ihn \
             na nb hg)) \
             {legb} (@Eq.refl ({o}) {legb}) hi)",
            legb = leg3("b"),
            ib = inner_body("ob"),
            grid = grid("na", "nb"),
        );
        format!(
            "def def_eq_fuel_wh3_to_wh (n : Nat) : forall (a : KExpr) (b : KExpr), \
             @Eq Bool (def_eq_fuel_wh3 {env} n a b) Bool.true -> \
             @Eq Bool (def_eq_fuel_wh {env} n a b) Bool.true := \
             @Nat.rec {motive} \
             (fun (a : KExpr) (b : KExpr) (h : @Eq Bool Bool.false Bool.true) => \
             bool_false_ne_true (@Eq Bool (def_eq_fuel_wh {env} Nat.zero a b) Bool.true) h) \
             (fun (k : Nat) (ihn : {motive_k}) (a : KExpr) (b : KExpr) \
             (h : @Eq Bool {body_a} Bool.true) => \
             @OptionType.rec KExpr \
             (fun (oa : {o}) => @Eq ({o}) {lega} oa -> @Eq Bool {body_oa} Bool.true -> {goal}) \
             (fun (_ha : @Eq ({o}) {lega} (@OptionType.none KExpr)) \
             (hf : @Eq Bool Bool.false Bool.true) => bool_false_ne_true ({goal}) hf) \
             (fun (na : KExpr) (ha3 : @Eq ({o}) {lega} (@OptionType.some KExpr na)) \
             (hi : @Eq Bool {ib_legb} Bool.true) => {inner}) \
             {lega} (@Eq.refl ({o}) {lega}) h) \
             n",
            motive = format_args!(
                "(fun (m : Nat) => forall (a : KExpr) (b : KExpr), \
                 @Eq Bool (def_eq_fuel_wh3 {env} m a b) Bool.true -> \
                 @Eq Bool (def_eq_fuel_wh {env} m a b) Bool.true)"
            ),
            motive_k = format_args!(
                "forall (a : KExpr) (b : KExpr), \
                 @Eq Bool (def_eq_fuel_wh3 {env} k a b) Bool.true -> \
                 @Eq Bool (def_eq_fuel_wh {env} k a b) Bool.true"
            ),
            lega = leg3("a"),
            body_a = body(&leg3("a")),
            body_oa = body("oa"),
            ib_legb = inner_body(&leg3("b")),
        )
    }

    /// **ITEM 7** — `def_eq_accepts_wh3_to_wh`: the witness transfer.
    ///
    /// One arm. `DefEqFuelAcceptsWh3` and `DefEqFuelAcceptsWh` are the same
    /// single-constructor witness idiom over the two algorithms, so unwrapping
    /// one and rewrapping the other around item 6 is the whole proof — **and
    /// the budget is carried across UNCHANGED**, which is the property the whole
    /// route exists to preserve.
    pub(super) fn wh3_to_wh_accepts_src() -> String {
        "def def_eq_accepts_wh3_to_wh (a : KExpr) (b : KExpr) \
         (h : DefEqFuelAcceptsWh3 a b) : DefEqFuelAcceptsWh a b := \
         @DefEqFuelAcceptsWh3.rec a b \
         (fun (_q : DefEqFuelAcceptsWh3 a b) => DefEqFuelAcceptsWh a b) \
         (fun (n : Nat) \
         (hn : @Eq Bool (def_eq_fuel_wh3 the_red_env n a b) Bool.true) => \
         @DefEqFuelAcceptsWh.mk a b n (def_eq_fuel_wh3_to_wh n a b hn)) h"
            .to_string()
    }

    /// **ITEM 8** — `def_eq_fuel_complete_wh`: COMPLETENESS OF THE
    /// DEPLOYED-FAITHFUL CONVERSION ALGORITHM.
    ///
    /// Item 7 of the three-way capstone. Two caveats travel with it and neither
    /// is optional; they are restated in the registered description because a
    /// theorem's own statement cannot carry them:
    ///
    /// * **The premise is `Wh3NormAcc`** — a normalisation-accessibility
    ///   predicate about the ANALYSIS loop, carried onto a theorem about the
    ///   DEPLOYED-FAITHFUL one. It is satisfiable and hereditary, but it is not
    ///   a statement about `whnf_fuel_red_wh`'s own normalisation.
    /// * **The witnessed fuel's guarantee is CONDITIONAL on how the budget was
    ///   obtained**, which is narrower than "not monotone" and is the accurate
    ///   form. `whnf_fuel_red_wh_monotone_is_false` stands at loop (ii), so a
    ///   budget reached by an arbitrary route may fail at a larger one. But the
    ///   budget THIS theorem witnesses comes through the three-way capstone, and
    ///   `def_eq_fuel_wh_accepts_at_every_larger` shows such a budget is upward
    ///   closed: every `m` with `Le k m` works too. Two-way monotonicity itself
    ///   remains open and is NOT what that constant proves.
    pub(super) fn wh3_to_wh_complete_src() -> String {
        "def def_eq_fuel_complete_wh (a : KExpr) (acca : Wh3NormAcc a) : \
         forall (b : KExpr), DefEq a b -> Wh3NormAcc b -> DefEqFuelAcceptsWh a b := \
         fun (b : KExpr) (hd : DefEq a b) (accb : Wh3NormAcc b) => \
         def_eq_accepts_wh3_to_wh a b \
         (def_eq_fuel_complete_wh3_final a acca b hd accb)"
            .to_string()
    }

    /// **THE COMPLETENESS THEOREM IS NOT VACUOUS**, and this is the constant
    /// that says so rather than a sentence claiming it.
    ///
    /// `def_eq_fuel_complete_wh` is a conditional whose premise is
    /// `Wh3NormAcc`, and the soundness certificate is explicit about the hazard
    /// this creates: *"a vacuous conditional passes every axiom-closure gate"*
    /// — it fired once already, on loop (i)'s `def_eq_fuel_complete`, whose
    /// `hnf` premise turned out to be false. The type alone cannot distinguish
    /// complete from empty, so the three-way capstone carries
    /// `def_eq_fuel_complete_wh3_final_witness` and the two-way one must carry
    /// its counterpart.
    ///
    /// It is one application of item 7 to that existing witness, which is the
    /// point: the transfer moves the WITNESS as readily as the theorem, so
    /// non-vacuity costs nothing extra and there is no excuse for omitting it.
    pub(super) fn wh3_to_wh_complete_witness_src() -> String {
        let z = "(KExpr.sort Level.zero)";
        format!(
            "def def_eq_fuel_complete_wh_witness : DefEqFuelAcceptsWh {z} {z} := \
             def_eq_accepts_wh3_to_wh {z} {z} def_eq_fuel_complete_wh3_final_witness"
        )
    }

    /// **THE PAIR, AS ONE OBJECT** — `def_eq_wh_sound_and_complete`.
    ///
    /// `def_eq_wh3_sound_and_complete` does this for loop (iii); until now
    /// there was no counterpart at loop (ii), because there was no completeness
    /// half to pair. Registering the conjunction rather than leaving two
    /// theorems side by side is what makes "loop (ii) has both directions"
    /// greppable instead of a sentence someone has to assemble.
    ///
    /// The two halves are NOT symmetric in what they cost. Completeness is item
    /// 8 and carries `Wh3NormAcc` on both terms; soundness is
    /// `def_eq_fuel_wh_sound_final` and carries NOTHING — it is unconditional,
    /// at any fuel. So the accessibility premises on this statement are there
    /// for the completeness direction alone, and a reader who wants soundness
    /// should take it directly rather than through this pair.
    pub(super) fn wh3_to_wh_pair_src() -> String {
        let fwd = "DefEq a b -> DefEqFuelAcceptsWh a b";
        let bwd = "DefEqFuelAcceptsWh a b -> DefEq a b";
        format!(
            "def def_eq_wh_sound_and_complete (a : KExpr) (acca : Wh3NormAcc a) (b : KExpr) \
             (accb : Wh3NormAcc b) : AndType ({fwd}) ({bwd}) := \
             @AndType.intro ({fwd}) ({bwd}) \
             (fun (hd : DefEq a b) => def_eq_fuel_complete_wh a acca b hd accb) \
             (fun (hx : DefEqFuelAcceptsWh a b) => def_eq_fuel_wh_accepts_sound a b hx)"
        )
    }

    /// **The non-monotonicity caveat, made PRECISE** — and much less bad than
    /// the blanket form suggests.
    ///
    /// `def_eq_fuel_complete_wh` says *a budget exists*. The obvious worry is
    /// that a caller cannot then re-run with more fuel, because
    /// `whnf_fuel_red_wh_monotone_is_false` refutes the two-way loop's
    /// monotonicity. This constant says how much of that worry is real:
    ///
    /// > from a THREE-way acceptance at `k`, the TWO-way algorithm accepts at
    /// > **every** `m` with `Le k m`.
    ///
    /// It is two lines — `def_eq_fuel_wh3_le` to raise the budget on the
    /// monotone side, then item 6 at the raised budget — and it does NOT prove
    /// two-way monotonicity, which stays open. The distinction is the whole
    /// point and the design doc's §1 already explains why it holds: acceptance
    /// at each `m` is derived FRESHLY at `m` through the transfer, never
    /// carried from `m - 1`. So the refuted statement and this one are
    /// compatible: a budget the two-way algorithm reaches by some OTHER route
    /// may still fail at a larger one, and that is exactly the refutation's
    /// witness.
    ///
    /// **What this buys the capstone.** The budget `def_eq_fuel_complete_wh`
    /// witnesses comes through `def_eq_fuel_complete_wh3_final`, so it IS of
    /// this form — every larger budget works too. The caveat that must travel
    /// is therefore narrower than "not monotone": it is that the guarantee
    /// attaches to budgets certified through the three-way route, not to the
    /// two-way algorithm in general.
    pub(super) fn wh3_to_wh_upward_closed_src() -> String {
        "def def_eq_fuel_wh_accepts_at_every_larger (k : Nat) (a : KExpr) (b : KExpr) \
         (h : @Eq Bool (def_eq_fuel_wh3 the_red_env k a b) Bool.true) : \
         forall (m : Nat), Le k m -> \
         @Eq Bool (def_eq_fuel_wh the_red_env m a b) Bool.true := \
         fun (m : Nat) (hle : Le k m) => \
         def_eq_fuel_wh3_to_wh m a b (def_eq_fuel_wh3_le k m hle a b h)"
            .to_string()
    }

    /// The SOUNDNESS direction at the witness level, factored out.
    ///
    /// The three-way lane has `def_eq_fuel_wh3_accepts_sound`; this is its
    /// two-way counterpart, and factoring it out of the pair is what makes the
    /// roundtrip below expressible. Unwrap the witness, apply
    /// `def_eq_fuel_wh_sound_final` at the budget it carries. Unconditional —
    /// no `Wh3NormAcc`, no fuel side condition.
    pub(super) fn wh3_to_wh_accepts_sound_src() -> String {
        "def def_eq_fuel_wh_accepts_sound (a : KExpr) (b : KExpr) \
         (h : DefEqFuelAcceptsWh a b) : DefEq a b := \
         @DefEqFuelAcceptsWh.rec a b (fun (_q : DefEqFuelAcceptsWh a b) => DefEq a b) \
         (fun (n : Nat) \
         (hn : @Eq Bool (def_eq_fuel_wh the_red_env n a b) Bool.true) => \
         def_eq_fuel_wh_sound_final n a b hn) h"
            .to_string()
    }

    /// **THE PAIR COMPOSES** — the two-way counterpart of
    /// `def_eq_wh3_roundtrip_witness`.
    ///
    /// Two theorems existing side by side is weaker than it looks: each could
    /// be true of a different object, or one could be vacuous. This runs the
    /// ROUND TRIP on completeness's own witness — take the `DefEqFuelAcceptsWh`
    /// that `def_eq_fuel_complete_wh_witness` produces, feed it to soundness,
    /// and get a `DefEq` back. So the two halves are demonstrably about the
    /// same object, on an inhabitant rather than in the abstract.
    pub(super) fn wh3_to_wh_roundtrip_witness_src() -> String {
        let z = "(KExpr.sort Level.zero)";
        format!(
            "def def_eq_wh_roundtrip_witness : DefEq {z} {z} := \
             def_eq_fuel_wh_accepts_sound {z} {z} def_eq_fuel_complete_wh_witness"
        )
    }
}
