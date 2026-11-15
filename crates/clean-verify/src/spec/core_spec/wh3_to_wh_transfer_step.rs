// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Three-way to two-way TRANSFER — the STEP, first half.
//!
//! Split out of `wh3_to_wh_transfer.rs` purely for SIZE: that file reached
//! 2,077 lines, four times this repo's 500-line guideline, and tripped the
//! paragon `files_over_1000` ratchet. Nothing moved between modules changes
//! what any generator EMITS — every one returns a `String` and the strings are
//! byte-identical — so the split is verifiable by compiling, not by a spec
//! build. Read `wh3_to_wh_transfer.rs`'s module doc for the route; this file
//! is the arms of items 2 and 3 up to the head-stuck lemma.

use crate::spec::Specification;

impl Specification {
    /// The `const` arm of the `wstuck ⟹ none` direction.
    ///
    /// The three-way step at a constant is
    /// `opt_step_bind KExpr (kdef_value_at (red_def renv) n us) wstuck
    /// (fun v => wstep v)`, and the two-way step is `kdef_value_at (red_def
    /// renv) n us` itself. So the obligation is exactly an OPTION INVERSION:
    /// the bind reports `wstuck` only on the `none` branch, because the `some`
    /// branch reports `wstep v`, and `wstuck` is not `wstep` by
    /// `wh_stuck_ne_step_type`.
    ///
    /// This is the smallest arm that does real work, and it is here first for
    /// that reason: it exercises the option convoy and the `WhStepR`
    /// no-confusion lemma that every other non-trivial arm also needs.
    ///
    /// **Take the `Prop` variant, not the `_type` one.** This arm concludes in
    /// `Eq`, and `wh_stuck_ne_step_type` concludes at `C : Type`, so using it
    /// here is a `0 vs 1` universe conflict in a NON-CUMULATIVE kernel. The
    /// generator that emits both (`iota_prepass.rs`) says exactly this in its
    /// own description — "a convoy on a step result has arms concluding in `Eq`
    /// and arms concluding in `Empty`" — and I reached for the wrong one
    /// anyway. Every later arm concluding in `Eq` takes the unsuffixed name.
    pub(super) fn wh3_to_wh_const_arm_src() -> String {
        let o = "OptionType KExpr";
        let val = "(kdef_value_at (red_def renv) n us)";
        let bind = |scrut: &str| {
            format!(
                "(opt_step_bind KExpr {scrut} WhStepR.wstuck (fun (v : KExpr) => WhStepR.wstep v))"
            )
        };
        format!(
            "def wh3_const_stuck_gives_none (renv : RedEnv) (n : Name) (us : ListType Level) \
             (h : Eq WhStepR {bind_val} WhStepR.wstuck) : \
             Eq ({o}) {val} (OptionType.none KExpr) := \
             OptionType.rec KExpr \
             (fun (q : {o}) => Eq WhStepR {bind_q} WhStepR.wstuck -> \
             Eq ({o}) q (OptionType.none KExpr)) \
             (fun (_hn : Eq WhStepR {bind_none} WhStepR.wstuck) => \
             Eq.refl ({o}) (OptionType.none KExpr)) \
             (fun (v : KExpr) (hv : Eq WhStepR {bind_some} WhStepR.wstuck) => \
             wh_stuck_ne_step v \
             (Eq ({o}) (OptionType.some KExpr v) (OptionType.none KExpr)) \
             (Eq.symm WhStepR (WhStepR.wstep v) WhStepR.wstuck hv)) \
             {val} h",
            bind_val = bind(val),
            bind_q = bind("q"),
            bind_none = bind("(OptionType.none KExpr)"),
            bind_some = bind("(OptionType.some KExpr v)"),
        )
    }

    /// The `proj` arm of the `wstuck ⟹ none` direction.
    ///
    /// This is the one arm outside the application spine where the three-way
    /// step does real extra work: it carries STARVATION UP from its subterm
    /// rather than losing it (`reduce_once_red_wh3`'s own description says so).
    /// The two-way step has no such case — `opt_proj_lift` sees only `none`.
    ///
    /// It is a genuine induction arm, so it takes the induction hypothesis as a
    /// HYPOTHESIS rather than closing over it: given the subterm's three-way
    /// result `c3` and two-way result `c2`, and the IH relating them, the arm
    /// follows by a three-way convoy on `c3`:
    ///
    /// * `wstuck` — the IH gives `c2 = none`, and `opt_proj_lift s i none`
    ///   reduces to `none`;
    /// * `wstarved` — refuted, `wstarved` is not `wstuck`;
    /// * `wstep sub2` — refuted, `wstep _` is not `wstuck`.
    ///
    /// Stating it this way is what keeps it separately elaborable: the arm is
    /// checked without assembling the nine-arm recursor around it.
    pub(super) fn wh3_to_wh_proj_arm_src() -> String {
        let o = "OptionType KExpr";
        let lifted = |c: &str| format!("(opt_proj_lift s i {c})");
        let conv = |c: &str| {
            format!(
                "(WhStepR.rec (fun (_q : WhStepR) => WhStepR) WhStepR.wstuck WhStepR.wstarved                  (fun (sub2 : KExpr) => WhStepR.wstep (KExpr.proj s i sub2)) {c})"
            )
        };
        format!(
            "def wh3_proj_stuck_gives_none (s : Name) (i : Nat) (c3 : WhStepR) (c2 : {o})              (ih : Eq WhStepR c3 WhStepR.wstuck -> Eq ({o}) c2 (OptionType.none KExpr))              (h : Eq WhStepR {conv_c3} WhStepR.wstuck) :              Eq ({o}) {lift_c2} (OptionType.none KExpr) :=              WhStepR.rec              (fun (q : WhStepR) =>              (Eq WhStepR q WhStepR.wstuck -> Eq ({o}) c2 (OptionType.none KExpr)) ->              Eq WhStepR {conv_q} WhStepR.wstuck ->              Eq ({o}) {lift_c2} (OptionType.none KExpr))              (fun (ihs : Eq WhStepR WhStepR.wstuck WhStepR.wstuck ->              Eq ({o}) c2 (OptionType.none KExpr))              (_hs : Eq WhStepR WhStepR.wstuck WhStepR.wstuck) =>              Eq.substType ({o}) (fun (z : {o}) => Eq ({o}) {lift_c2} (OptionType.none KExpr))              c2 c2 (Eq.refl ({o}) c2)              (Eq.substType ({o})              (fun (z : {o}) => Eq ({o}) (opt_proj_lift s i z) (OptionType.none KExpr))              (OptionType.none KExpr) c2              (Eq.symm ({o}) c2 (OptionType.none KExpr)              (ihs (Eq.refl WhStepR WhStepR.wstuck)))              (Eq.refl ({o}) (OptionType.none KExpr))))              (fun (_iha : Eq WhStepR WhStepR.wstarved WhStepR.wstuck ->              Eq ({o}) c2 (OptionType.none KExpr))              (ha : Eq WhStepR WhStepR.wstarved WhStepR.wstuck) =>              wh_stuck_ne_starved (Eq ({o}) {lift_c2} (OptionType.none KExpr))              (Eq.symm WhStepR WhStepR.wstarved WhStepR.wstuck ha))              (fun (sub2 : KExpr)              (_ihp : Eq WhStepR (WhStepR.wstep sub2) WhStepR.wstuck ->              Eq ({o}) c2 (OptionType.none KExpr))              (hp : Eq WhStepR (WhStepR.wstep (KExpr.proj s i sub2)) WhStepR.wstuck) =>              wh_stuck_ne_step (KExpr.proj s i sub2)              (Eq ({o}) {lift_c2} (OptionType.none KExpr))              (Eq.symm WhStepR (WhStepR.wstep (KExpr.proj s i sub2)) WhStepR.wstuck hp))              c3 ih h",
            conv_c3 = conv("c3"),
            conv_q = conv("q"),
            lift_c2 = lifted("c2"),
        )
    }

    /// **THE CONTENT OF THE `app` ARM**: the ι chain itself transfers.
    ///
    /// The `app` arm of the step is `opt_app_ilift3`, a three-way convoy whose
    /// `wstuck` branch is `iota_reduct_whc3 (red_rec renv) wh (app f a)`. So the
    /// arm reduces to this: if the THREE-WAY chain is stuck, the TWO-WAY chain
    /// declines.
    ///
    /// It is one application of `iota_reduct_whc3_stuck_inv` — the Prop variant,
    /// because the goal is an `Eq` — whose six continuations map ONE-TO-ONE
    /// onto decline lemmas:
    ///
    /// | continuation | decline lemma |
    /// |---|---|
    /// | `k1` no head | `iota_reduct_whc_none_of_no_head` |
    /// | `k2` no recmeta | `iota_reduct_whc_none_of_no_recmeta` |
    /// | `k3` no major | `iota_reduct_whc_none_of_no_major` |
    /// | `k5` pre-pass result has no head | `iota_reduct_whc_none_of_no_wmajor_head` |
    /// | `k6` no rule | `iota_reduct_whc_none_of_no_rule` |
    /// | `ktail` tail declines | `iota_reduct_whc_none_of_tail_none` |
    ///
    /// **There is no `k4`, and that absence is the whole reason this works.**
    /// Level 4 is the pre-pass, and it cannot produce a `wstuck` — a starved
    /// pre-pass yields `wstarved`, which `wh_stuck_ne_starved` separates. That
    /// is precisely why starvation cannot leak into the transfer.
    ///
    /// The continuation hypothesis `hw` is spent in exactly three places —
    /// `k5`, `k6`, `ktail` — transporting `wh3 major = some wmajor` to
    /// `wh2 major = some wmajor`. Every other fact the decline lemmas need
    /// mentions no pre-pass at all, which is why the bottom three levels of the
    /// chain needed no new work.
    pub(super) fn wh3_to_wh_chain_src() -> String {
        let o = "OptionType KExpr";
        let env = "(red_rec renv)";
        let mi = |m: &str| {
            format!(
            "(Nat.add (Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m}))              (recmeta_num_minors {m})) (recmeta_num_indices {m}))"
        )
        };
        let e_head = "Eq (OptionType Name) (kexpr_const_name (kapp_fn e))";
        let h1 = |rn: &str| format!("{e_head} (OptionType.some Name {rn})");
        let h2 = |rn: &str, m: &str| {
            format!(
                "Eq (OptionType RecMeta) (recmeta_for {env} {rn}) (OptionType.some RecMeta {m})"
            )
        };
        let h3 = |m: &str, mj: &str| {
            format!(
                "Eq ({o}) (list_head (list_drop {} (kapp_args e))) (OptionType.some KExpr {mj})",
                mi(m)
            )
        };
        let hwm = |mj: &str, wm: &str| format!("Eq ({o}) (wh3 {mj}) (OptionType.some KExpr {wm})");
        let h4 = |wm: &str, cn: &str| {
            format!(
            "Eq (OptionType Name) (kexpr_const_name (kapp_fn {wm})) (OptionType.some Name {cn})"
        )
        };
        let h5 = |rn: &str, cn: &str, rl: &str| {
            format!(
            "Eq (OptionType RecRule) (recrule_for {env} {rn} {cn}) (OptionType.some RecRule {rl})"
        )
        };
        let goal = format!("Eq ({o}) (iota_reduct_whc {env} wh2 e) (OptionType.none KExpr)");

        let k1 = format!(
            "(fun (hn : {e_head} (OptionType.none Name)) =>              iota_reduct_whc_none_of_no_head {env} wh2 e hn)"
        );
        let k2 = format!(
            "(fun (rn : Name) (q1 : {})              (hnm : Eq (OptionType RecMeta) (recmeta_for {env} rn) (OptionType.none RecMeta)) =>              iota_reduct_whc_none_of_no_recmeta {env} wh2 e rn q1 hnm)",
            h1("rn")
        );
        let k3 = format!(
            "(fun (rn : Name) (mt : RecMeta) (q1 : {}) (q2 : {})              (hnj : Eq ({o}) (list_head (list_drop {} (kapp_args e))) (OptionType.none KExpr)) =>              iota_reduct_whc_none_of_no_major {env} wh2 e rn mt q1 q2 hnj)",
            h1("rn"), h2("rn", "mt"), mi("mt")
        );
        let k5 = format!(
            "(fun (rn : Name) (mt : RecMeta) (mj : KExpr) (wm : KExpr)              (q1 : {}) (q2 : {}) (q3 : {}) (qw : {})              (hnc : Eq (OptionType Name) (kexpr_const_name (kapp_fn wm)) (OptionType.none Name)) =>              iota_reduct_whc_none_of_no_wmajor_head {env} wh2 e rn mt mj wm q1 q2 q3              (hw mj wm qw) hnc)",
            h1("rn"), h2("rn", "mt"), h3("mt", "mj"), hwm("mj", "wm")
        );
        let k6 = format!(
            "(fun (rn : Name) (mt : RecMeta) (mj : KExpr) (wm : KExpr) (cn : Name)              (q1 : {}) (q2 : {}) (q3 : {}) (qw : {}) (q4 : {})              (hnr : Eq (OptionType RecRule) (recrule_for {env} rn cn) (OptionType.none RecRule)) =>              iota_reduct_whc_none_of_no_rule {env} wh2 e rn mt mj wm q1 q2 q3 (hw mj wm qw)              cn q4 hnr)",
            h1("rn"), h2("rn", "mt"), h3("mt", "mj"), hwm("mj", "wm"), h4("wm", "cn")
        );
        let ktail = format!(
            "(fun (rn : Name) (mt : RecMeta) (mj : KExpr) (wm : KExpr) (cn : Name) (rl : RecRule)              (q1 : {}) (q2 : {}) (q3 : {}) (qw : {}) (q4 : {}) (q5 : {})              (ht : Eq ({o}) (iota_contractum_at mt rl (kexpr_const_levels (kapp_fn e))              (kapp_args e) (kapp_args wm)) (OptionType.none KExpr)) =>              iota_reduct_whc_none_of_tail_none {env} wh2 e rn mt mj wm q1 q2 q3 (hw mj wm qw)              cn q4 rl q5 ht)",
            h1("rn"), h2("rn", "mt"), h3("mt", "mj"), hwm("mj", "wm"), h4("wm", "cn"),
            h5("rn", "cn", "rl")
        );

        format!(
            "def wh3_chain_stuck_gives_none (renv : RedEnv) (wh3 : KExpr -> {o})              (wh2 : KExpr -> {o})              (hw : forall (x : KExpr) (y : KExpr), Eq ({o}) (wh3 x) (OptionType.some KExpr y) ->              Eq ({o}) (wh2 x) (OptionType.some KExpr y)) (e : KExpr)              (h : Eq WhStepR (iota_reduct_whc3 {env} wh3 e) WhStepR.wstuck) : {goal} :=              iota_reduct_whc3_stuck_inv {env} wh3 e ({goal}) h {k1} {k2} {k3} {k5} {k6} {ktail}"
        )
    }

    /// The ilift convoy: `opt_app_ilift3` stuck ⟹ `opt_app_ilift_wh` declines.
    ///
    /// One layer above the chain lemma and one below the `app` arm. Both ilifts
    /// are a convoy on the HEAD's result, and they differ exactly as the loops
    /// do:
    ///
    /// * head stuck — three-way reaches for ι (`iota_reduct_whc3`), two-way
    ///   reaches for ι (`iota_reduct_whc`); this is where the chain lemma goes;
    /// * head starved — three-way propagates `wstarved` OUTWARD rather than
    ///   letting it be mistaken for stuck. **This is the arm where the naive
    ///   "the divergence is confined to the chain" reading is wrong**: the
    ///   two-way `opt_app_ilift` sees only `none` and DOES attempt ι here. It
    ///   is harmless only because `wstarved` is not `wstuck`, so this branch is
    ///   refuted rather than transferred;
    /// * head reduced — both take the congruence, and `wstep _` is not
    ///   `wstuck`, so this branch is refuted too.
    pub(super) fn wh3_to_wh_ilift_src() -> String {
        let o = "OptionType KExpr";
        let goal =
            "Eq (OptionType KExpr) (opt_app_ilift_wh renv wh2 f a c2) (OptionType.none KExpr)";
        let conv3 = |c: &str| format!("(opt_app_ilift3 renv wh3 f a {c})");
        format!(
            "def wh3_ilift_stuck_gives_none (renv : RedEnv) (wh3 : KExpr -> {o})              (wh2 : KExpr -> {o})              (hw : forall (x : KExpr) (y : KExpr), Eq ({o}) (wh3 x) (OptionType.some KExpr y) ->              Eq ({o}) (wh2 x) (OptionType.some KExpr y))              (f : KExpr) (a : KExpr) (c3 : WhStepR) (c2 : {o})              (ih : Eq WhStepR c3 WhStepR.wstuck -> Eq ({o}) c2 (OptionType.none KExpr))              (h : Eq WhStepR {conv_c3} WhStepR.wstuck) : {goal} :=              WhStepR.rec              (fun (q : WhStepR) =>              (Eq WhStepR q WhStepR.wstuck -> Eq ({o}) c2 (OptionType.none KExpr)) ->              Eq WhStepR {conv_q} WhStepR.wstuck -> {goal})              (fun (ihs : Eq WhStepR WhStepR.wstuck WhStepR.wstuck ->              Eq ({o}) c2 (OptionType.none KExpr))              (hs : Eq WhStepR (iota_reduct_whc3 (red_rec renv) wh3 (KExpr.app f a))              WhStepR.wstuck) =>              Eq.substType ({o})              (fun (z : {o}) => Eq ({o}) (opt_app_ilift_wh renv wh2 f a z)              (OptionType.none KExpr))              (OptionType.none KExpr) c2              (Eq.symm ({o}) c2 (OptionType.none KExpr) (ihs (Eq.refl WhStepR WhStepR.wstuck)))              (wh3_chain_stuck_gives_none renv wh3 wh2 hw (KExpr.app f a) hs))              (fun (_iha : Eq WhStepR WhStepR.wstarved WhStepR.wstuck ->              Eq ({o}) c2 (OptionType.none KExpr))              (ha : Eq WhStepR WhStepR.wstarved WhStepR.wstuck) =>              wh_stuck_ne_starved ({goal})              (Eq.symm WhStepR WhStepR.wstarved WhStepR.wstuck ha))              (fun (f2 : KExpr)              (_ihp : Eq WhStepR (WhStepR.wstep f2) WhStepR.wstuck ->              Eq ({o}) c2 (OptionType.none KExpr))              (hp : Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) WhStepR.wstuck) =>              wh_stuck_ne_step (KExpr.app f2 a) ({goal})              (Eq.symm WhStepR (WhStepR.wstep (KExpr.app f2 a)) WhStepR.wstuck hp))              c3 ih h",
            conv_c3 = conv3("c3"),
            conv_q = conv3("q"),
        )
    }

    /// **ITEM 2 ASSEMBLED** — `wh_step3_stuck_to_none`: one three-way step
    /// reporting genuine stuckness forces the two-way step to decline.
    ///
    /// The nine arms of `reduce_once_red_wh3` against the nine of
    /// `reduce_once_red_wh`, and only three of them carry content:
    ///
    /// * **five are `Eq.refl`** — `sort`, `bvar`, `lam`, `pi`, `lit`. The
    ///   three-way step calls these genuinely stuck and the two-way step
    ///   declines outright, so both sides ι-reduce to the same `none` and the
    ///   hypothesis is never looked at. That five of nine arms are free is the
    ///   measure of how narrow the refinement is.
    /// * **`let_` is absurd** and inlined rather than given its own lemma: the
    ///   three-way step contracts, yielding `wstep (instantiate b v)`, so the
    ///   hypothesis is refuted by `wh_stuck_ne_step` on the spot.
    /// * **`const`, `proj` and `app` delegate** to the three arm lemmas above.
    ///
    /// Note how each delegating arm spends its induction hypothesis. The
    /// recursor hands it `motive sub`, which is *definitionally* the `ih`
    /// parameter those lemmas take — `Eq WhStepR (reduce_once_red_wh3 … sub)
    /// wstuck -> Eq _ (reduce_once_red_wh … sub) none` — so the arm passes it
    /// straight through with the two results supplied explicitly. That is the
    /// payoff of having stated each arm lemma with its IH as a HYPOTHESIS
    /// instead of closing over the recursion: the assembly is a pass-through,
    /// and every arm was checkable before this constant existed.
    pub(super) fn wh3_to_wh_step_src() -> String {
        let o = "OptionType KExpr";
        let goal =
            |z: &str| format!("Eq ({o}) (reduce_once_red_wh renv wh2 {z}) (OptionType.none KExpr)");
        let hyp = |z: &str| format!("Eq WhStepR (reduce_once_red_wh3 renv wh3 {z}) WhStepR.wstuck");
        let motive = format!("(fun (z : KExpr) => {} -> {})", hyp("z"), goal("z"));
        // `motive` applied at a sub-binder, spelled out. The recursor's minor
        // premises want the motive at EACH recursive position separately, and
        // building two of them from one binder is a mismatch the kernel reports
        // as a minor-premise error rather than as anything about the proof.
        let at = |z: &str| format!("({} -> {})", hyp(z), goal(z));
        // The five free arms: both steps reduce to `none` here.
        let refl = |binders: &str, z: &str| {
            format!(
                "(fun {binders} (_hz : {}) => Eq.refl ({o}) (OptionType.none KExpr))",
                hyp(z)
            )
        };
        let c3 = |z: &str| format!("(reduce_once_red_wh3 renv wh3 {z})");
        let c2 = |z: &str| format!("(reduce_once_red_wh renv wh2 {z})");
        format!(
            "def wh_step3_stuck_to_none (renv : RedEnv) (wh3 : KExpr -> {o}) \
             (wh2 : KExpr -> {o}) \
             (hw : forall (x : KExpr) (y : KExpr), Eq ({o}) (wh3 x) (OptionType.some KExpr y) -> \
             Eq ({o}) (wh2 x) (OptionType.some KExpr y)) \
             (e : KExpr) (h : {hyp_e}) : {goal_e} := \
             KExpr.rec {motive} \
             {a_sort} {a_bvar} {a_app} {a_lam} {a_pi} {a_const} {a_let} {a_proj} {a_lit} \
             e h",
            hyp_e = hyp("e"),
            goal_e = goal("e"),
            a_sort = refl("(n : Level)", "(KExpr.sort n)"),
            a_bvar = refl("(i : Nat)", "(KExpr.bvar i)"),
            a_app = format_args!(
                "(fun (f : KExpr) (a : KExpr) (cf : {mf}) (_ca : {ma}) (hz : {hz}) => \
                 wh3_app_head_stuck_gives_none renv wh3 wh2 hw a {cf3} {cf2} cf f hz)",
                mf = at("f"),
                ma = at("a"),
                hz = hyp("(KExpr.app f a)"),
                cf3 = c3("f"),
                cf2 = c2("f"),
            ),
            a_lam = refl(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {mt}) (_cb : {mb})",
                    mt = at("ty"),
                    mb = at("b")
                ),
                "(KExpr.lam ty b)",
            ),
            a_pi = refl(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {mt}) (_cb : {mb})",
                    mt = at("ty"),
                    mb = at("b")
                ),
                "(KExpr.pi ty b)",
            ),
            a_const = format_args!(
                "(fun (n : Name) (us : ListType Level) (hz : {hz}) => \
                 wh3_const_stuck_gives_none renv n us hz)",
                hz = hyp("(KExpr.const n us)"),
            ),
            a_let = format_args!(
                "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {mt}) (_c2 : {mv}) \
                 (_c3 : {mb}) (hz : {hz}) => \
                 wh_stuck_ne_step (instantiate b v) ({g}) \
                 (Eq.symm WhStepR (WhStepR.wstep (instantiate b v)) WhStepR.wstuck hz))",
                mt = at("ty"),
                mv = at("v"),
                mb = at("b"),
                hz = hyp("(KExpr.let_ ty v b)"),
                g = goal("(KExpr.let_ ty v b)"),
            ),
            a_proj = format_args!(
                "(fun (s : Name) (i : Nat) (sub : KExpr) (csub : {ms}) (hz : {hz}) => \
                 wh3_proj_stuck_gives_none s i {s3} {s2} csub hz)",
                ms = at("sub"),
                hz = hyp("(KExpr.proj s i sub)"),
                s3 = c3("sub"),
                s2 = c2("sub"),
            ),
            a_lit = refl("(v : Nat)", "(KExpr.lit v)"),
        )
    }

    /// **ITEM 3 BEGINS — the SUCCESS direction of the chain.**
    ///
    /// The mirror of [`Self::wh3_to_wh_chain_src`], and it is markedly
    /// smaller: `iota_reduct_whc3_some_inv` has ONE continuation where the
    /// stuck inverter has six, because a fired ι has exactly one shape and a
    /// declined one has six ways to decline. The continuation's six binders and
    /// seven facts land one-for-one on `iota_reduct_whc_some_of_facts`'s
    /// parameters, with the pre-pass fact — and only that one — routed through
    /// `hw`.
    ///
    /// **The guarded tail transfers untouched, and that is worth stating.**
    /// `iota_contractum_at meta rule (kexpr_const_levels (kapp_fn e))
    /// (kapp_args e) (kapp_args wmajor)` mentions no whnf continuation at all,
    /// so the fact the three-way inverter hands out is *literally* the fact the
    /// two-way reassembler wants. The two loops differ only where a pre-pass is
    /// consulted, and the tail never consults one.
    pub(super) fn wh3_to_wh_chain_some_src() -> String {
        let o = "OptionType KExpr";
        let env = "(red_rec renv)";
        let mi = |m: &str| {
            format!(
                "(Nat.add (Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) \
                 (recmeta_num_minors {m})) (recmeta_num_indices {m}))"
            )
        };
        let h1 = |rn: &str| {
            format!(
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name {rn})"
            )
        };
        let h2 = |rn: &str, m: &str| {
            format!(
                "Eq (OptionType RecMeta) (recmeta_for {env} {rn}) (OptionType.some RecMeta {m})"
            )
        };
        let h3 = |m: &str, mj: &str| {
            format!(
                "Eq ({o}) (list_head (list_drop {} (kapp_args e))) (OptionType.some KExpr {mj})",
                mi(m)
            )
        };
        let hwm = |mj: &str, wm: &str| format!("Eq ({o}) (wh3 {mj}) (OptionType.some KExpr {wm})");
        let h4 = |wm: &str, cn: &str| {
            format!(
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn {wm})) \
                 (OptionType.some Name {cn})"
            )
        };
        let h5 = |rn: &str, cn: &str, rl: &str| {
            format!(
                "Eq (OptionType RecRule) (recrule_for {env} {rn} {cn}) \
                 (OptionType.some RecRule {rl})"
            )
        };
        let goal = format!("Eq ({o}) (iota_reduct_whc {env} wh2 e) (OptionType.some KExpr r)");
        let ktail = |mt: &str, rl: &str, wm: &str| {
            format!(
                "Eq ({o}) (iota_contractum_at {mt} {rl} (kexpr_const_levels (kapp_fn e)) \
                 (kapp_args e) (kapp_args {wm})) (OptionType.some KExpr r)"
            )
        };
        let k = format!(
            "(fun (rn : Name) (mt : RecMeta) (mj : KExpr) (wm : KExpr) (cn : Name) (rl : RecRule) \
             (q1 : {}) (q2 : {}) (q3 : {}) (qw : {}) (q4 : {}) (q5 : {}) (qt : {}) => \
             iota_reduct_whc_some_of_facts {env} wh2 e rn mt mj wm cn rl r \
             q1 q2 q3 (hw mj wm qw) q4 q5 qt)",
            h1("rn"),
            h2("rn", "mt"),
            h3("mt", "mj"),
            hwm("mj", "wm"),
            h4("wm", "cn"),
            h5("rn", "cn", "rl"),
            ktail("mt", "rl", "wm"),
        );
        format!(
            "def wh3_chain_step_gives_some (renv : RedEnv) (wh3 : KExpr -> {o}) \
             (wh2 : KExpr -> {o}) \
             (hw : forall (x : KExpr) (y : KExpr), Eq ({o}) (wh3 x) (OptionType.some KExpr y) -> \
             Eq ({o}) (wh2 x) (OptionType.some KExpr y)) (e : KExpr) (r : KExpr) \
             (h : Eq WhStepR (iota_reduct_whc3 {env} wh3 e) (WhStepR.wstep r)) : {goal} := \
             iota_reduct_whc3_some_inv {env} wh3 e r ({goal}) h {k}"
        )
    }

    /// The `const` arm of the SUCCESS direction.
    ///
    /// The mirror of [`Self::wh3_to_wh_const_arm_src`], and the branches swap
    /// roles: there the `none` branch was the free one and `some` was refuted;
    /// here `none` is refuted and `some` carries the work. What the `some`
    /// branch needs beyond the stuck version is `wh_step_inj` — the three-way
    /// step wraps the stored value in `wstep`, and recovering the payload is
    /// where a `some`-direction transfer always spends a no-confusion lemma its
    /// `none`-direction twin does not.
    pub(super) fn wh3_to_wh_const_some_src() -> String {
        let o = "OptionType KExpr";
        let val = "(kdef_value_at (red_def renv) n us)";
        let bind = |scrut: &str| {
            format!(
                "(opt_step_bind KExpr {scrut} WhStepR.wstuck (fun (v : KExpr) => WhStepR.wstep v))"
            )
        };
        format!(
            "def wh3_const_step_gives_some (renv : RedEnv) (n : Name) (us : ListType Level) \
             (r : KExpr) (h : Eq WhStepR {bind_val} (WhStepR.wstep r)) : \
             Eq ({o}) {val} (OptionType.some KExpr r) := \
             OptionType.rec KExpr \
             (fun (q : {o}) => Eq WhStepR {bind_q} (WhStepR.wstep r) -> \
             Eq ({o}) q (OptionType.some KExpr r)) \
             (fun (hn : Eq WhStepR {bind_none} (WhStepR.wstep r)) => \
             wh_stuck_ne_step r \
             (Eq ({o}) (OptionType.none KExpr) (OptionType.some KExpr r)) hn) \
             (fun (v : KExpr) (hv : Eq WhStepR {bind_some} (WhStepR.wstep r)) => \
             Eq.substType KExpr \
             (fun (X : KExpr) => Eq ({o}) (OptionType.some KExpr v) (OptionType.some KExpr X)) \
             v r (wh_step_inj v r hv) (Eq.refl ({o}) (OptionType.some KExpr v))) \
             {val} h",
            bind_val = bind(val),
            bind_q = bind("q"),
            bind_none = bind("(OptionType.none KExpr)"),
            bind_some = bind("(OptionType.some KExpr v)"),
        )
    }

    /// The `proj` arm of the SUCCESS direction.
    ///
    /// **It needs only ONE of the two induction hypotheses**, and the asymmetry
    /// is the point. A `proj` can only report a step when its subterm did, so
    /// the `wstuck` and `wstarved` branches are both refuted outright and the
    /// stuck-direction hypothesis is never consulted. Compare the `ilift` and
    /// `app` arms below, which need both because a stuck HEAD is exactly when
    /// the two-way ι is attempted.
    pub(super) fn wh3_to_wh_proj_some_src() -> String {
        let o = "OptionType KExpr";
        let conv = |c: &str| {
            format!(
                "(WhStepR.rec (fun (_q : WhStepR) => WhStepR) WhStepR.wstuck WhStepR.wstarved \
                 (fun (sub2 : KExpr) => WhStepR.wstep (KExpr.proj s i sub2)) {c})"
            )
        };
        let goal = format!("Eq ({o}) (opt_proj_lift s i c2) (OptionType.some KExpr r)");
        format!(
            "def wh3_proj_step_gives_some (s : Name) (i : Nat) (c3 : WhStepR) (c2 : {o}) \
             (ihp : forall (y : KExpr), Eq WhStepR c3 (WhStepR.wstep y) -> \
             Eq ({o}) c2 (OptionType.some KExpr y)) (r : KExpr) \
             (h : Eq WhStepR {conv_c3} (WhStepR.wstep r)) : {goal} := \
             WhStepR.rec \
             (fun (q : WhStepR) => \
             (forall (y : KExpr), Eq WhStepR q (WhStepR.wstep y) -> \
             Eq ({o}) c2 (OptionType.some KExpr y)) -> \
             Eq WhStepR {conv_q} (WhStepR.wstep r) -> {goal}) \
             (fun (_ihs : forall (y : KExpr), Eq WhStepR WhStepR.wstuck (WhStepR.wstep y) -> \
             Eq ({o}) c2 (OptionType.some KExpr y)) \
             (hs : Eq WhStepR WhStepR.wstuck (WhStepR.wstep r)) => \
             wh_stuck_ne_step r ({goal}) hs) \
             (fun (_iha : forall (y : KExpr), Eq WhStepR WhStepR.wstarved (WhStepR.wstep y) -> \
             Eq ({o}) c2 (OptionType.some KExpr y)) \
             (ha : Eq WhStepR WhStepR.wstarved (WhStepR.wstep r)) => \
             wh_starved_ne_step r ({goal}) ha) \
             (fun (sub2 : KExpr) \
             (ihp2 : forall (y : KExpr), Eq WhStepR (WhStepR.wstep sub2) (WhStepR.wstep y) -> \
             Eq ({o}) c2 (OptionType.some KExpr y)) \
             (hp : Eq WhStepR (WhStepR.wstep (KExpr.proj s i sub2)) (WhStepR.wstep r)) => \
             Eq.substType KExpr \
             (fun (X : KExpr) => Eq ({o}) (opt_proj_lift s i c2) (OptionType.some KExpr X)) \
             (KExpr.proj s i sub2) r \
             (wh_step_inj (KExpr.proj s i sub2) r hp) \
             (Eq.substType ({o}) \
             (fun (z : {o}) => \
             Eq ({o}) (opt_proj_lift s i z) (OptionType.some KExpr (KExpr.proj s i sub2))) \
             (OptionType.some KExpr sub2) c2 \
             (Eq.symm ({o}) c2 (OptionType.some KExpr sub2) \
             (ihp2 sub2 (Eq.refl WhStepR (WhStepR.wstep sub2)))) \
             (Eq.refl ({o}) (OptionType.some KExpr (KExpr.proj s i sub2))))) \
             c3 ihp h",
            conv_c3 = conv("c3"),
            conv_q = conv("q"),
        )
    }

    /// The ilift convoy, SUCCESS direction — **and it needs BOTH hypotheses.**
    ///
    /// This is where item 3 genuinely consumes item 2 rather than mirroring it.
    /// A head reporting `wstuck` is exactly the case in which both loops reach
    /// for ι, so to compute the two-way ilift at all one must know the two-way
    /// head result, and a `wstuck` three-way head says nothing about it except
    /// through the stuck-direction transfer. Hence `ihs` beside `ihp`:
    ///
    /// * head `wstuck` — `ihs` gives `c2 = none`, the two-way ilift reduces to
    ///   the two-way ι chain, and `wh3_chain_step_gives_some` finishes;
    /// * head `wstarved` — the three-way ilift propagates `wstarved`, which is
    ///   not a `wstep`, so the branch is refuted. **Starvation is excluded on
    ///   this side too**, and for the same reason as in the stuck direction;
    /// * head `wstep f2` — both take the congruence; `wh_step_inj` recovers
    ///   `r = app f2 a` and `ihp` supplies `c2 = some f2`.
    pub(super) fn wh3_to_wh_ilift_some_src() -> String {
        let o = "OptionType KExpr";
        let goal = format!("Eq ({o}) (opt_app_ilift_wh renv wh2 f a c2) (OptionType.some KExpr r)");
        let conv3 = |c: &str| format!("(opt_app_ilift3 renv wh3 f a {c})");
        let ihp_ty = |q: &str| {
            format!(
                "forall (y : KExpr), Eq WhStepR {q} (WhStepR.wstep y) -> \
                 Eq ({o}) c2 (OptionType.some KExpr y)"
            )
        };
        let ihs_ty = |q: &str| {
            format!("Eq WhStepR {q} WhStepR.wstuck -> Eq ({o}) c2 (OptionType.none KExpr)")
        };
        format!(
            "def wh3_ilift_step_gives_some (renv : RedEnv) (wh3 : KExpr -> {o}) \
             (wh2 : KExpr -> {o}) \
             (hw : forall (x : KExpr) (y : KExpr), Eq ({o}) (wh3 x) (OptionType.some KExpr y) -> \
             Eq ({o}) (wh2 x) (OptionType.some KExpr y)) \
             (f : KExpr) (a : KExpr) (c3 : WhStepR) (c2 : {o}) \
             (ihs : {ihs_c3}) (ihp : {ihp_c3}) (r : KExpr) \
             (h : Eq WhStepR {conv_c3} (WhStepR.wstep r)) : {goal} := \
             WhStepR.rec \
             (fun (q : WhStepR) => ({ihs_q}) -> ({ihp_q}) -> \
             Eq WhStepR {conv_q} (WhStepR.wstep r) -> {goal}) \
             (fun (ihs0 : {ihs_stuck}) (_ihp0 : {ihp_stuck}) \
             (hs : Eq WhStepR (iota_reduct_whc3 (red_rec renv) wh3 (KExpr.app f a)) \
             (WhStepR.wstep r)) => \
             Eq.substType ({o}) \
             (fun (z : {o}) => \
             Eq ({o}) (opt_app_ilift_wh renv wh2 f a z) (OptionType.some KExpr r)) \
             (OptionType.none KExpr) c2 \
             (Eq.symm ({o}) c2 (OptionType.none KExpr) (ihs0 (Eq.refl WhStepR WhStepR.wstuck))) \
             (wh3_chain_step_gives_some renv wh3 wh2 hw (KExpr.app f a) r hs)) \
             (fun (_ihs1 : {ihs_starved}) (_ihp1 : {ihp_starved}) \
             (ha : Eq WhStepR WhStepR.wstarved (WhStepR.wstep r)) => \
             wh_starved_ne_step r ({goal}) ha) \
             (fun (f2 : KExpr) (_ihs2 : {ihs_step}) (ihp2 : {ihp_step}) \
             (hp : Eq WhStepR (WhStepR.wstep (KExpr.app f2 a)) (WhStepR.wstep r)) => \
             Eq.substType KExpr \
             (fun (X : KExpr) => \
             Eq ({o}) (opt_app_ilift_wh renv wh2 f a c2) (OptionType.some KExpr X)) \
             (KExpr.app f2 a) r (wh_step_inj (KExpr.app f2 a) r hp) \
             (Eq.substType ({o}) \
             (fun (z : {o}) => Eq ({o}) (opt_app_ilift_wh renv wh2 f a z) \
             (OptionType.some KExpr (KExpr.app f2 a))) \
             (OptionType.some KExpr f2) c2 \
             (Eq.symm ({o}) c2 (OptionType.some KExpr f2) \
             (ihp2 f2 (Eq.refl WhStepR (WhStepR.wstep f2)))) \
             (Eq.refl ({o}) (OptionType.some KExpr (KExpr.app f2 a))))) \
             c3 ihs ihp h",
            conv_c3 = conv3("c3"),
            conv_q = conv3("q"),
            ihs_c3 = ihs_ty("c3"),
            ihp_c3 = ihp_ty("c3"),
            ihs_q = ihs_ty("q"),
            ihp_q = ihp_ty("q"),
            ihs_stuck = ihs_ty("WhStepR.wstuck"),
            ihp_stuck = ihp_ty("WhStepR.wstuck"),
            ihs_starved = ihs_ty("WhStepR.wstarved"),
            ihp_starved = ihp_ty("WhStepR.wstarved"),
            ihs_step = ihs_ty("(WhStepR.wstep f2)"),
            ihp_step = ihp_ty("(WhStepR.wstep f2)"),
        )
    }

    /// **ITEM 3 ASSEMBLED** — `wh_step3_step_to_some`: a three-way step that
    /// actually reduces forces the two-way step to reduce to the same term.
    ///
    /// The same nine-arm shape as item 2 with the arms' fortunes reversed: the
    /// five shapes that were free there (`sort`, `bvar`, `lam`, `pi`, `lit`)
    /// are *refuted* here, because the three-way step reports `wstuck` at all
    /// of them and `wstuck` is not a `wstep`; and `let_`, absurd there, is the
    /// computing arm here.
    ///
    /// **The `app` arm is where item 3 consumes item 2.** It must supply the
    /// head's stuck-direction transfer as well as its own induction hypothesis,
    /// and that is not something the recursor can hand it — the motive carries
    /// one implication, not two. It comes instead from `wh_step3_stuck_to_none`
    /// applied at the head, a closed lemma needing no induction. That is why
    /// the two items are sequenced rather than proved as one mutual induction.
    pub(super) fn wh3_to_wh_step_some_src() -> String {
        let o = "OptionType KExpr";
        let goal = |z: &str, y: &str| {
            format!("Eq ({o}) (reduce_once_red_wh renv wh2 {z}) (OptionType.some KExpr {y})")
        };
        let hyp = |z: &str, y: &str| {
            format!("Eq WhStepR (reduce_once_red_wh3 renv wh3 {z}) (WhStepR.wstep {y})")
        };
        let motive = format!(
            "(fun (z : KExpr) => forall (y : KExpr), {} -> {})",
            hyp("z", "y"),
            goal("z", "y")
        );
        let at = |z: &str| format!("(forall (y : KExpr), {} -> {})", hyp(z, "y"), goal(z, "y"));
        // The three-way step calls these five genuinely stuck, so the
        // hypothesis is refuted outright.
        let stuck_arm = |binders: &str, z: &str| {
            format!(
                "(fun {binders} (y : KExpr) (hy : {}) => wh_stuck_ne_step y ({}) hy)",
                hyp(z, "y"),
                goal(z, "y")
            )
        };
        let c3 = |z: &str| format!("(reduce_once_red_wh3 renv wh3 {z})");
        let c2 = |z: &str| format!("(reduce_once_red_wh renv wh2 {z})");
        format!(
            "def wh_step3_step_to_some (renv : RedEnv) (wh3 : KExpr -> {o}) \
             (wh2 : KExpr -> {o}) \
             (hw : forall (x : KExpr) (y : KExpr), Eq ({o}) (wh3 x) (OptionType.some KExpr y) -> \
             Eq ({o}) (wh2 x) (OptionType.some KExpr y)) \
             (e : KExpr) (r : KExpr) (h : {hyp_e}) : {goal_e} := \
             KExpr.rec {motive} \
             {a_sort} {a_bvar} {a_app} {a_lam} {a_pi} {a_const} {a_let} {a_proj} {a_lit} \
             e r h",
            hyp_e = hyp("e", "r"),
            goal_e = goal("e", "r"),
            a_sort = stuck_arm("(n : Level)", "(KExpr.sort n)"),
            a_bvar = stuck_arm("(i : Nat)", "(KExpr.bvar i)"),
            a_app = format_args!(
                "(fun (f : KExpr) (a : KExpr) (cf : {mf}) (_ca : {ma}) (y : KExpr) (hy : {hz}) => \
                 wh3_app_head_step_gives_some renv wh3 wh2 hw a {cf3} {cf2} \
                 (wh_step3_stuck_to_none renv wh3 wh2 hw f) cf f y hy)",
                mf = at("f"),
                ma = at("a"),
                hz = hyp("(KExpr.app f a)", "y"),
                cf3 = c3("f"),
                cf2 = c2("f"),
            ),
            a_lam = stuck_arm(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {}) (_cb : {})",
                    at("ty"),
                    at("b")
                ),
                "(KExpr.lam ty b)",
            ),
            a_pi = stuck_arm(
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {}) (_cb : {})",
                    at("ty"),
                    at("b")
                ),
                "(KExpr.pi ty b)",
            ),
            a_const = format_args!(
                "(fun (n : Name) (us : ListType Level) (y : KExpr) (hy : {hz}) => \
                 wh3_const_step_gives_some renv n us y hy)",
                hz = hyp("(KExpr.const n us)", "y"),
            ),
            a_let = format_args!(
                "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {mt}) (_c2 : {mv}) \
                 (_c3 : {mb}) (y : KExpr) \
                 (hy : Eq WhStepR (WhStepR.wstep (instantiate b v)) (WhStepR.wstep y)) => \
                 Eq.substType KExpr \
                 (fun (X : KExpr) => Eq ({o}) (OptionType.some KExpr (instantiate b v)) \
                 (OptionType.some KExpr X)) \
                 (instantiate b v) y (wh_step_inj (instantiate b v) y hy) \
                 (Eq.refl ({o}) (OptionType.some KExpr (instantiate b v))))",
                mt = at("ty"),
                mv = at("v"),
                mb = at("b"),
            ),
            a_proj = format_args!(
                "(fun (s : Name) (i : Nat) (sub : KExpr) (csub : {ms}) (y : KExpr) (hy : {hz}) => \
                 wh3_proj_step_gives_some s i {s3} {s2} csub y hy)",
                ms = at("sub"),
                hz = hyp("(KExpr.proj s i sub)", "y"),
                s3 = c3("sub"),
                s2 = c2("sub"),
            ),
            a_lit = stuck_arm("(v : Nat)", "(KExpr.lit v)"),
        )
    }
}
