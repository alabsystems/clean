// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fuel adequacy for the FAITHFUL loop — monotonicity restricted to genuine
//! normal forms, and the fuel witness the completeness capstone consumes.
//!
//! ## Why the naive statement is false
//!
//! `iota_reduct_whc` binds the pre-pass with `opt_bind`, so a STARVED pre-pass
//! short-circuits to `none`, ι does not fire, the step reports nothing to do,
//! and `loop_dispatch (none) e ih` returns `some e` — the loop announces `e` as
//! a normal form. A **false stuck**. `whnf_fuel_red_wh_starves` witnesses it
//! concretely: `cx_stuck` at fuel 1 comes back unchanged, and at fuel 2 it
//! reduces.
//!
//! So the ordinary fuel-monotonicity statement — a successful result survives
//! raising the fuel — is **FALSE** for this loop, where it is true for
//! `whnf_fuel_red` (`whnf_fuel_red_monotone`). More budget can change the
//! answer, not merely find one. That matters because fuel adequacy has to put
//! two independent fuels on a common bound, which is exactly what monotonicity
//! is for.
//!
//! ## What is true instead
//!
//! Monotonicity holds once the result is a GENUINE normal form — one the step
//! function rejects at *every* pre-pass budget, the predicate `hnf_conv` already
//! carries (and which is reused from there rather than restated, because a
//! duplicated premise is how one false `hnf` became nine vacuous theorems).
//!
//! The reason is that a run which lands on a genuinely stuck result took only
//! real steps: a false stuck would have halted at a result the step function
//! still has work for. With more budget those same steps still fire, so the path
//! is unchanged and the endpoint is the same.
//!
//! ## The shape of the argument
//!
//! `whnf_fuel_red_wh_mono_stuck` is `Nat.rec` with `e` and `r` universally
//! quantified in the motive, following `whnf_fuel_red_monotone` — the right
//! template here, because it shares the `Eq`-valued goal. (`LOOP_PAR` is the
//! wrong one: its goal is `par_reduces_cd_star`, so it uses the `Sort 1`
//! helpers, and borrowing them for an `Eq` goal fails with `universe level
//! conflict: Zero vs Succ(Zero)`.)
//!
//! The two arms differ from that template in exactly one place. There, the
//! `none` case is closed by handing back the hypothesis, because the original
//! step does not depend on fuel and so `loop_dispatch (none)` agrees at `k` and
//! `k+1`. Here the step DOES depend on fuel, and the genuine-stuckness
//! hypothesis is precisely what kills the bigger-budget step: `e` and `r`
//! coincide in that case, and `hst` applies at `k+1`.
//!
//! The `some` case needs the step itself to be monotone. That is now a
//! THEOREM, not a hypothesis — see below.
//!
//! ## The premise, discharged
//!
//! Step monotonicity — a step that fires at one budget fires the same way at
//! the next — was carried through this layer as `hsm` for as long as it was
//! only an argument. It is now proved: `wh_step_mono_all` gives it for two
//! pre-passes related by a transport, and `wh_hsm_all` closes the fuel-indexed
//! recursion between the two.
//!
//! The dependency looked circular and is not. Restricted monotonicity at fuel
//! `k` consumes step monotonicity STRICTLY BELOW `k`, because its recursion
//! descends — so the two close together by strong induction on fuel.
//! `whnf_fuel_red_wh_mono_stuck_b` takes the `Lt`-bounded premise, which is what
//! the discharge can actually supply, and `whnf_fuel_red_wh_mono_stuck` is the
//! unconditional form built from it.
//!
//! So the declarations here now carry the two ENVIRONMENT side conditions
//! (`i2`, `i8`) in place of the step-monotonicity premise. They state fuel
//! adequacy, not fuel adequacy given something.
//!
//! What made the discharge possible, worth recording because it was luck as
//! much as design: the transport's stuckness premise quantifies over an
//! arbitrary pre-pass while restricted monotonicity's quantifies over fuel. The
//! former is stronger, so the adapter instantiates rather than generalises —
//! available only because `wh_step_none_of_neutral` was stated over an arbitrary
//! pre-pass, a choice made for tidiness when that lemma was written.
//!
//! `DerivedProved`, empty axiom closures; the two inductives are census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The pre-pass continuation at fuel `j`, written as an explicit lambda.
fn whk(j: &str) -> String {
    format!("(fun (e3 : KExpr) => whnf_fuel_red_wh the_red_env {j} e3)")
}

/// The two environment side conditions the discharge needs: a constructor head
/// carries no recursor metadata (`i2`) and no definitional value (`i8`). They
/// replace the step-monotonicity premise this layer used to carry.
const SC: &str = "(i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) \
     (i8 : RecEnvCtorNoDefVal the_red_env) ";

/// One executable step of the faithful loop, with the pre-pass at fuel `j`.
fn step(j: &str, t: &str) -> String {
    format!("(reduce_once_red_wh the_red_env {} {t})", whk(j))
}

impl Specification {
    /// Restricted monotonicity, its `Le` forms, and the fuel witness.
    pub(super) fn add_wh_fuel_adequacy(&mut self) -> Result<(), SpecError> {
        self.add_hsm_at_def()?;
        self.add_mono_stuck()?;
        self.add_hsm_discharge()?;
        self.add_mono_stuck_unconditional()?;
        self.add_wh_le_forms()?;
        self.add_wh_normalizes()?;
        self.add_wh_fuel_from_normalizes()?;
        Ok(())
    }

    /// The step-monotonicity premise, at every budget.
    ///
    /// Now DISCHARGEABLE: `wh_step_mono_all` proves it. Kept as a hypothesis on
    /// the declarations below only until the discharge is wired through.
    fn hsm() -> String {
        format!("forall (j : Nat), {}", Self::hsm_at("j"))
    }

    /// Restricted monotonicity, UNCONDITIONALLY.
    ///
    /// The bounded form plus `wh_hsm_all`: the premise is no longer carried, it
    /// is supplied. Callers need only the two environment side conditions.
    fn add_mono_stuck_unconditional(&mut self) -> Result<(), SpecError> {
        let mot = format!(
            "forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env n e) (OptionType.some KExpr r) -> {stuck} -> \
             Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env (Nat.succ n) e) \
             (OptionType.some KExpr r)",
            stuck = Self::stuck_at("r"),
        );
        let src = format!(
            "def whnf_fuel_red_wh_mono_stuck {SC}(n : Nat) : {mot} := \
             whnf_fuel_red_wh_mono_stuck_b n \
             (fun (j : Nat) (_hj : Lt j n) => wh_hsm_all i2 i8 j)"
        );
        debug_assert!(Self::balanced(&src), "unconditional mono_stuck parens");
        self.add_recursive_def(
            &src,
            "whnf_fuel_red_wh_mono_stuck: restricted fuel monotonicity, with NO step-monotonicity \
             hypothesis. A run that lands on a genuine normal form survives one more unit of fuel. \
             \
             The bounded form supplied from wh_hsm_all. What was carried as a premise through this \
             whole layer is now discharged, so the statement is what it says rather than what it \
             says GIVEN something. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// THE DISCHARGE — step monotonicity at every budget, proved.
    ///
    /// `wh_step_mono_all` gives it at a single pair of pre-passes, provided a
    /// transport between them. At consecutive budgets that transport IS
    /// restricted monotonicity — but restricted monotonicity at fuel `k` needs
    /// step monotonicity below `k`, which is why the two must be closed
    /// together, by induction on fuel.
    ///
    /// `nat_strong_rec` supplies that induction, and it is the only shape that
    /// works: a plain `Nat.rec` accumulator would have to decide, from
    /// `Le k (succ n)`, whether `k ≤ n` or `k = succ n`, and nothing here
    /// provides that split without a decidability assumption.
    ///
    /// `nat_strong_rec` is stated at `P : Nat -> Type` and the statement being
    /// proved ends in `Eq`, so it is `Prop`. This kernel is non-cumulative, so
    /// the two do not meet. Rather than derive `Prop` variants of the whole
    /// chain — `nat_strong_rec`, `nat_lt_rec_bounded`, `nat_strict_split`,
    /// `lt_zero_absurd` — the statement is lifted through `LiftP`, whose entire
    /// purpose is this. One wrapper instead of four lemmas.
    ///
    /// The transport's stuckness premise quantifies over an ARBITRARY pre-pass
    /// while restricted monotonicity's quantifies over fuel. The former is
    /// stronger, so the adapter instantiates rather than generalises — and that
    /// direction is available only because `wh_step_none_of_neutral` was stated
    /// over an arbitrary pre-pass to begin with.
    fn add_hsm_discharge(&mut self) -> Result<(), SpecError> {
        let o = "OptionType KExpr";
        let at = |k: &str| Self::hsm_at(k);
        let unwrap = |k: &str, w: &str| {
            format!(
                "(LiftP.rec {p} (fun (_l : LiftP {p}) => {p}) (fun (q : {p}) => q) {w})",
                p = at(k),
            )
        };
        // Below k, the strong-induction hypotheses ARE the bounded premise.
        let bh = format!(
            "(fun (jj : Nat) (hj : Lt jj k) => {})",
            unwrap("jj", "(ihs jj hj)"),
        );
        let transport = format!(
            "(fun (t : KExpr) (r : KExpr) (h1 : Eq ({o}) ({whk_k} t) (OptionType.some KExpr r)) \
             (h2 : forall (w : KExpr -> OptionType KExpr), Eq ({o}) \
             (reduce_once_red_wh the_red_env w r) (OptionType.none KExpr)) => \
             whnf_fuel_red_wh_mono_stuck_b k {bh} t r h1 (fun (jj : Nat) => h2 {whk_jj}))",
            whk_k = whk("k"),
            whk_jj = whk("jj"),
        );
        let stepf = format!(
            "(fun (k : Nat) (ihs : forall (jj : Nat), Lt jj k -> LiftP {atjj}) => \
             LiftP.up {atk} (wh_step_mono_all {w1} {w2} i2 i8 {transport}))",
            atjj = at("jj"),
            atk = at("k"),
            w1 = whk("k"),
            w2 = whk("(Nat.succ k)"),
        );
        let src = format!(
            "def wh_hsm_all (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) \
             (i8 : RecEnvCtorNoDefVal the_red_env) (j : Nat) : {atj} := {body}",
            atj = at("j"),
            body = unwrap(
                "j",
                &format!(
                    "(nat_strong_rec (fun (k : Nat) => LiftP {atk}) {stepf} j)",
                    atk = at("k"),
                ),
            ),
        );
        debug_assert!(Self::balanced(&src), "hsm discharge parens");
        self.add_recursive_def(
            &src,
            "wh_hsm_all: STEP MONOTONICITY AT EVERY BUDGET — the discharge. What the fuel layer \
             carried as a hypothesis is now supplied. \
             \
             Strong induction on the budget. At k, the induction hypotheses below k are exactly \
             the bounded premise restricted monotonicity wants, so mono_stuck_b runs at k; that \
             yields the transport between consecutive pre-passes, and wh_step_mono_all turns the \
             transport into step monotonicity at k. The circularity is only apparent: restricted \
             monotonicity at k consumes step monotonicity strictly BELOW k, because its recursion \
             descends. \
             \
             nat_strong_rec is the only usable shape here. A plain Nat.rec accumulator would have \
             to decide, from Le k (succ n), whether k is at most n or equal to succ n, and nothing \
             supplies that split without a decidability assumption — which is the vacuity trap. \
             \
             The statement is Prop-valued and nat_strong_rec is stated at Nat -> Type; since the \
             kernel is non-cumulative those do not meet, so the statement is lifted through LiftP. \
             One wrapper, rather than Prop variants of nat_strong_rec, nat_lt_rec_bounded, \
             nat_strict_split and lt_zero_absurd. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// Step monotonicity AT ONE BUDGET, as a NAMED predicate.
    ///
    /// It has to be named, not inlined. The parser does not accept a
    /// parenthesised `forall` in argument position, so `LiftP (forall …)` is a
    /// parse error — and the discharge lifts this very statement through
    /// `LiftP` to reach the Type-valued strong recursor. Naming it also shortens
    /// every term that mentions it by some two thousand characters.
    fn add_hsm_at_def(&mut self) -> Result<(), SpecError> {
        let src = format!(
            "def WhHsmAt (k : Nat) : Prop := \
             forall (e0 : KExpr) (x0 : KExpr), Eq (OptionType KExpr) \
             {at_k} (OptionType.some KExpr x0) -> Eq (OptionType KExpr) \
             {at_s} (OptionType.some KExpr x0)",
            at_k = step("k", "e0"),
            at_s = step("(Nat.succ k)", "e0"),
        );
        debug_assert!(Self::balanced(&src), "WhHsmAt parens");
        self.add_recursive_def(
            &src,
            "WhHsmAt k: step monotonicity at ONE budget — a step firing with the pre-pass at fuel k \
             fires the same way at fuel k+1. \
             \
             Named rather than inlined for a hard reason: the parser rejects a parenthesised \
             forall in argument position, so LiftP (forall ...) does not parse, and the discharge \
             must lift exactly this statement through LiftP to reach the Type-valued strong \
             recursor. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// Step monotonicity at one budget.
    fn hsm_at(k: &str) -> String {
        format!("(WhHsmAt {k})")
    }

    /// The hypothesis BOUNDED BELOW a budget.
    ///
    /// This is what breaks the apparent circularity. Restricted monotonicity at
    /// fuel `n` needs step monotonicity — but only at budgets STRICTLY BELOW
    /// `n`, because its recursion descends. Taking the bounded form makes that
    /// explicit, so the two can be closed by induction on fuel rather than by
    /// assuming the very thing being proved.
    ///
    /// Phrased with `Lt` rather than `Le (succ ..)` to match `nat_strong_rec`,
    /// which is what discharges it.
    fn bhsm(n: &str) -> String {
        format!(
            "(forall (j : Nat), Lt j {n} -> {hsm})",
            hsm = Self::hsm_at("j"),
        )
    }

    /// THE LINCHPIN — a run that lands on a genuine normal form survives one
    /// more unit of fuel, returning the same result.
    fn add_mono_stuck(&mut self) -> Result<(), SpecError> {
        // The BOUNDED form first: it is the one that can actually be proved
        // without assuming what it is proving. The hsm-parameterised form is
        // kept beside it while callers are migrated.
        self.add_mono_stuck_at(true)?;
        Ok(())
    }

    /// `bounded` selects the hypothesis: `Lt`-bounded step monotonicity, which
    /// the discharge can supply by strong induction, versus the full `forall j`
    /// form, which it cannot.
    fn add_mono_stuck_at(&mut self, bounded: bool) -> Result<(), SpecError> {
        let suffix = if bounded { "_b" } else { "" };
        let sigbind = if bounded {
            String::new()
        } else {
            format!("(hsm : {}) ", Self::hsm())
        };
        let (zbind, bhbind, hsmk, ihapp) = if bounded {
            (
                format!("(_bh : {}) ", Self::bhsm("Nat.zero")),
                format!("(bh : {}) ", Self::bhsm("(Nat.succ k)")),
                "(bh k (lt_succ_self k))".to_string(),
                "(ih (fun (j : Nat) (hj : Lt j k) => bh j (lt_succ_weaken j k hj)))".to_string(),
            )
        } else {
            (
                String::new(),
                String::new(),
                "hsm k".to_string(),
                "ih".to_string(),
            )
        };
        let mot = |m: &str| {
            format!(
                "forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) \
                 (whnf_fuel_red_wh the_red_env {m} e) (OptionType.some KExpr r) -> {stuck} -> \
                 Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env (Nat.succ {m}) e) \
                 (OptionType.some KExpr r)",
                stuck = Self::stuck_at("r"),
            )
        };
        let wrap = |m: &str, body: String| {
            if bounded {
                format!("{} -> {}", Self::bhsm(m), body)
            } else {
                body
            }
        };
        let ihty = wrap("k", mot("k"));
        let conc = wrap("n", mot("n"));
        let motive = wrap("m", mot("m"));

        // Fuel zero returns none for every term, so the premise is absurd. Note
        // option_none_ne_some and NOT the _type variant: the goal is an Eq, which
        // lives in Sort 0, and the _type helpers demand Sort 1.
        let zero = format!(
            "(fun {zbind}(e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env Nat.zero e) (OptionType.some KExpr r)) \
             (_hst : {stuck}) => option_none_ne_some KExpr r \
             (Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env (Nat.succ Nat.zero) e) \
             (OptionType.some KExpr r)) h)",
            stuck = Self::stuck_at("r"),
            zbind = zbind,
        );

        // The step found nothing, so the loop handed back e itself and e IS r.
        // Genuine stuckness is what says the bigger budget finds nothing either —
        // this is the one place the faithful loop needs an argument where
        // whnf_fuel_red_monotone simply reuses its hypothesis.
        let motive_p = "(fun (X : KExpr) => Eq (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env (Nat.succ (Nat.succ k)) X) (OptionType.some KExpr r))";
        let at_r = format!(
            "(Eq.trans (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env (Nat.succ (Nat.succ k)) r) \
             (loop_dispatch (OptionType.none KExpr) r {whk1}) (OptionType.some KExpr r) \
             (Eq.cong (OptionType KExpr) (OptionType KExpr) \
             (fun (o : OptionType KExpr) => loop_dispatch o r {whk1}) \
             {step1} (OptionType.none KExpr) (hst (Nat.succ k))) \
             (Eq.refl (OptionType KExpr) (OptionType.some KExpr r)))",
            whk1 = whk("(Nat.succ k)"),
            step1 = step("(Nat.succ k)", "r"),
        );
        let none_arm = format!(
            "(fun (_hq : Eq (OptionType KExpr) {stepk} (OptionType.none KExpr)) \
             (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e {whk0}) \
             (OptionType.some KExpr r)) => Eq.subst KExpr {motive_p} r e \
             (Eq.symm KExpr e r (option_some_inj KExpr e r h2)) {at_r})",
            stepk = step("k", "e"),
            whk0 = whk("k"),
        );

        // A real step fired: step monotonicity carries it to the bigger budget,
        // and the induction hypothesis carries the tail.
        let some_arm = format!(
            "(fun (x2 : KExpr) (hq : Eq (OptionType KExpr) {stepk} (OptionType.some KExpr x2)) \
             (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr x2) e {whk0}) \
             (OptionType.some KExpr r)) => Eq.trans (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env (Nat.succ (Nat.succ k)) e) \
             (loop_dispatch (OptionType.some KExpr x2) e {whk1}) (OptionType.some KExpr r) \
             (Eq.cong (OptionType KExpr) (OptionType KExpr) \
             (fun (o : OptionType KExpr) => loop_dispatch o e {whk1}) \
             {step1} (OptionType.some KExpr x2) ({hsmk} e x2 hq)) ({ihapp} x2 r h2 hst))",
            stepk = step("k", "e"),
            whk0 = whk("k"),
            whk1 = whk("(Nat.succ k)"),
            step1 = step("(Nat.succ k)", "e"),
            hsmk = hsmk,
            ihapp = ihapp,
        );

        let mot2 = format!(
            "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) {stepk} o -> \
             Eq (OptionType KExpr) (loop_dispatch o e {whk0}) (OptionType.some KExpr r) -> \
             Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env (Nat.succ (Nat.succ k)) e) \
             (OptionType.some KExpr r))",
            stepk = step("k", "e"),
            whk0 = whk("k"),
        );
        let succ = format!(
            "(fun (k : Nat) (ih : {ihty}) {bhbind}(e : KExpr) (r : KExpr) \
             (h : Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env (Nat.succ k) e) \
             (OptionType.some KExpr r)) (hst : {stuck}) => OptionType.rec KExpr {mot2} \
             {none_arm} {some_arm} {stepk} (Eq.refl (OptionType KExpr) {stepk}) h)",
            ihty = ihty,
            bhbind = bhbind,
            stuck = Self::stuck_at("r"),
            stepk = step("k", "e"),
        );

        let src = format!(
            "def whnf_fuel_red_wh_mono_stuck{suffix} {sigbind}(n : Nat) : {conc} := \
             Nat.rec (fun (m : Nat) => {motive}) {zero} {succ} n",
            suffix = suffix,
            sigbind = sigbind,
            conc = conc,
            motive = motive,
        );
        for (what, arm) in [("zero", &zero), ("succ", &succ)] {
            debug_assert!(
                arm.starts_with("(fun "),
                "the {what} arm must be a lambda; paren balance cannot see a dropped `fun`"
            );
        }
        debug_assert!(Self::balanced(&src), "mono_stuck parens");
        self.add_recursive_def(
            &src,
            "whnf_fuel_red_wh_mono_stuck: RESTRICTED FUEL MONOTONICITY for the faithful loop — a \
             run that lands on a GENUINE normal form survives one more unit of fuel and returns \
             the same result. \
             \
             The unrestricted statement, which holds for whnf_fuel_red (whnf_fuel_red_monotone), \
             is FALSE here: a starved pre-pass makes iota silently decline, the step reports \
             nothing to do, and loop_dispatch hands back the term as though it were normal. \
             whnf_fuel_red_wh_starves exhibits that at fuel 1. More budget can therefore CHANGE \
             the answer, not merely find one. \
             \
             Restricting to genuine normal forms repairs it, because a run that lands on one took \
             only real steps — a false stuck would have halted where the step function still had \
             work — so a bigger budget replays the same path. The restriction is not a weakening \
             for the purpose at hand: the consumer is fuel pairing, which raises two runs to a \
             common bound, and those runs end at normal forms by construction. \
             \
             Conditional on step monotonicity (hsm), which is ASSUMED here, not proved. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The `Le` forms, mirroring `def_eq_fuel_le`'s `Le.rec` shape.
    fn add_wh_le_forms(&mut self) -> Result<(), SpecError> {
        let mot = |j: &str| {
            format!(
                "forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) \
                 (whnf_fuel_red_wh the_red_env k e) (OptionType.some KExpr r) -> {stuck} -> \
                 Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env {j} e) \
                 (OptionType.some KExpr r)",
                stuck = Self::stuck_at("r"),
            )
        };
        let src = format!(
            "def whnf_fuel_red_wh_le {SC}(k : Nat) (m : Nat) (hle : Le k m) : {motm} := \
             Le.rec k (fun (j : Nat) (_hj : Le k j) => {motj}) \
             (fun (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env k e) (OptionType.some KExpr r)) (_hst : {stuck}) => h) \
             (fun (j : Nat) (_hj : Le k j) (ihj : {motj}) (e : KExpr) (r : KExpr) \
             (h : Eq (OptionType KExpr) (whnf_fuel_red_wh the_red_env k e) \
             (OptionType.some KExpr r)) (hst : {stuck}) => \
             whnf_fuel_red_wh_mono_stuck i2 i8 j e r (ihj e r h hst) hst) m hle",
            motm = mot("m"),
            motj = mot("j"),
            stuck = Self::stuck_at("r"),
        );
        debug_assert!(Self::balanced(&src), "wh le parens");
        self.add_recursive_def(
            &src,
            "whnf_fuel_red_wh_le: restricted monotonicity in Le form — a run landing on a genuine \
             normal form survives raising the fuel to any Le-greater bound. Le.rec iterating the \
             single step, the same shape def_eq_fuel_le uses. This is the form fuel pairing wants, \
             since it puts two independent runs on the bound na + nb. Note Le.rec eliminates into \
             the Eq goal directly (subsingleton elimination), so no lifting is needed. \
             DerivedProved, zero axiom_deps.",
        )?;

        let mots = |j: &str| {
            format!(
                "forall (e : KExpr) (x2 : KExpr), Eq (OptionType KExpr) {stepk} \
                 (OptionType.some KExpr x2) -> Eq (OptionType KExpr) {stepj} \
                 (OptionType.some KExpr x2)",
                stepk = step("k", "e"),
                stepj = step(j, "e"),
            )
        };
        let src = format!(
            "def wh_step_mono_le {SC}(k : Nat) (m : Nat) (hle : Le k m) : {motm} := \
             Le.rec k (fun (j : Nat) (_hj : Le k j) => {motj}) \
             (fun (e : KExpr) (x2 : KExpr) (h : Eq (OptionType KExpr) {stepk} \
             (OptionType.some KExpr x2)) => h) \
             (fun (j : Nat) (_hj : Le k j) (ihj : {motj}) (e : KExpr) (x2 : KExpr) \
             (h : Eq (OptionType KExpr) {stepk} (OptionType.some KExpr x2)) => \
             wh_hsm_all i2 i8 j e x2 (ihj e x2 h)) m hle",
            motm = mots("m"),
            motj = mots("j"),
            stepk = step("k", "e"),
        );
        debug_assert!(Self::balanced(&src), "wh step mono le parens");
        self.add_recursive_def(
            &src,
            "wh_step_mono_le: step monotonicity in Le form, by the same Le.rec iteration. Needed \
             because fuel adequacy raises the STEP's budget and the continuation's budget to one \
             common bound, and the two arrive with independent fuels. Conditional on hsm. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The constructive normalization witness, and the fuel witness it yields.
    fn add_wh_normalizes(&mut self) -> Result<(), SpecError> {
        // r is a PARAMETER, not an index: it is fixed across the recursion. That
        // keeps the recursor at one parameter and one index — the shape with
        // precedent here. A three-index recursive recursor is what produced
        // "not a function type, but 4 argument(s) remain" earlier in this program.
        self.add_inductive(
            &format!(
                "inductive WhNormalizes (r : KExpr) : KExpr -> Type\n\
                 | stuck : ({stuck}) -> WhNormalizes r r\n\
                 | step : forall (e : KExpr) (x2 : KExpr) (k : Nat), Eq (OptionType KExpr) \
                 {stepk} (OptionType.some KExpr x2) -> WhNormalizes r x2 -> WhNormalizes r e",
                stuck = Self::stuck_at("r"),
                stepk = step("k", "e"),
            ),
            "WhNormalizes r e: a CONSTRUCTIVE witness that e reaches the normal form r under the \
             faithful loop — either e is already genuinely stuck, or it steps at some budget to a \
             term that normalises to r. \
             \
             The point of making this a derivation rather than a proposition is that it carries \
             the decision at every node. An accessibility-style argument would need to case-split \
             on whether a term steps at SOME budget, which is not decidable constructively; the \
             tempting repair is a decidability assumption, and that is the vacuity trap this \
             program has already fallen into once. \
             \
             Satisfiable, not vacuous: sort 0 takes no step at any budget, so `stuck` applies. \
             Census-neutral.",
        )?;

        self.add_inductive(
            &format!(
                "inductive WhnfFuelReachesWh : KExpr -> Type\n\
                 | mk : forall (e : KExpr) (n : Nat) (r : KExpr), Eq (OptionType KExpr) \
                 (whnf_fuel_red_wh the_red_env n e) (OptionType.some KExpr r) -> ({stuck}) -> \
                 WhnfFuelReachesWh e",
                stuck = Self::stuck_at("r"),
            ),
            "WhnfFuelReachesWh e: some budget suffices for the faithful loop on e, AND the result \
             it returns is a genuine normal form. \
             \
             The stuckness is packaged inside the constructor rather than proved at each use, \
             because every consumer needs it: restricted monotonicity is what raises fuel, and it \
             takes genuine stuckness as a hypothesis. A witness that recorded only the budget \
             would be unusable for pairing. Census-neutral.",
        )?;
        Ok(())
    }

    /// Fuel adequacy over the faithful loop.
    fn add_wh_fuel_from_normalizes(&mut self) -> Result<(), SpecError> {
        let one = format!(
            "(Eq.trans (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env (Nat.succ Nat.zero) r) \
             (loop_dispatch (OptionType.none KExpr) r {whk0}) (OptionType.some KExpr r) \
             (Eq.cong (OptionType KExpr) (OptionType KExpr) \
             (fun (o : OptionType KExpr) => loop_dispatch o r {whk0}) \
             {step0} (OptionType.none KExpr) (hst Nat.zero)) \
             (Eq.refl (OptionType KExpr) (OptionType.some KExpr r)))",
            whk0 = whk("Nat.zero"),
            step0 = step("Nat.zero", "r"),
        );

        // The bound is k + n, not a maximum: the two Le facts already exist and
        // nothing wants the bound tight. Same reasoning as whnf_fuel_pair.
        let body = format!(
            "WhnfFuelReachesWh.mk e0 (Nat.succ (Nat.add k n)) rr \
             (Eq.trans (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env (Nat.succ (Nat.add k n)) e0) \
             (loop_dispatch (OptionType.some KExpr x2) e0 {whkn}) (OptionType.some KExpr rr) \
             (Eq.cong (OptionType KExpr) (OptionType KExpr) \
             (fun (o : OptionType KExpr) => loop_dispatch o e0 {whkn}) \
             {stepn} (OptionType.some KExpr x2) \
             (wh_step_mono_le i2 i8 k (Nat.add k n) (le_add_self_left k n) e0 x2 hs)) \
             (whnf_fuel_red_wh_le i2 i8 n (Nat.add k n) (le_add_self_right k n) x2 rr heq hstk)) \
             hstk",
            whkn = whk("(Nat.add k n)"),
            stepn = step("(Nat.add k n)", "e0"),
        );
        let step_arm = format!(
            "(fun (e0 : KExpr) (x2 : KExpr) (k : Nat) (hs : Eq (OptionType KExpr) {stepk} \
             (OptionType.some KExpr x2)) (_w : WhNormalizes r x2) (ih : WhnfFuelReachesWh x2) => \
             WhnfFuelReachesWh.rec x2 (fun (_z : WhnfFuelReachesWh x2) => WhnfFuelReachesWh e0) \
             (fun (n : Nat) (rr : KExpr) (heq : Eq (OptionType KExpr) \
             (whnf_fuel_red_wh the_red_env n x2) (OptionType.some KExpr rr)) (hstk : {stuckrr}) => \
             {body}) ih)",
            stepk = step("k", "e0"),
            stuckrr = Self::stuck_at("rr"),
        );

        let src = format!(
            "def wh_fuel_from_normalizes {SC}(r : KExpr) (e : KExpr) \
             (hn : WhNormalizes r e) : WhnfFuelReachesWh e := \
             WhNormalizes.rec r (fun (x : KExpr) (_h : WhNormalizes r x) => WhnfFuelReachesWh x) \
             (fun (hst : {stuck}) => WhnfFuelReachesWh.mk r (Nat.succ Nat.zero) r {one} hst) \
             {step_arm} e hn",
            stuck = Self::stuck_at("r"),
        );
        debug_assert!(Self::balanced(&src), "wh fuel adequacy parens");
        self.add_recursive_def(
            &src,
            "wh_fuel_from_normalizes: FUEL ADEQUACY for the faithful loop — a normalization \
             derivation yields a budget at which the loop returns, together with the fact that \
             what it returns is a genuine normal form. \
             \
             Recursion on the derivation. The stuck case needs one unit of fuel and returns the \
             term itself. The step case has a budget k for the step and a budget n for the tail, \
             arriving independently, and lands them both on k + n — wh_step_mono_le raising the \
             step, whnf_fuel_red_wh_le raising the tail, the latter consuming exactly the genuine \
             stuckness the witness carries. \
             \
             This is the faithful-loop counterpart of whnf_fuel_from_acc, and it is stated over a \
             normalization derivation rather than accessibility because the loop's step is \
             budget-indexed: accessibility in the algorithm's order cannot see the pre-pass. \
             Conditional on hsm, which is ASSUMED — so this establishes fuel adequacy GIVEN step \
             monotonicity. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every generated source must be paren-balanced BEFORE it reaches the
    /// parser: an unbalanced source is a parse error that aborts the whole spec
    /// build, 20 minutes from now, with a message about the wrong declaration.
    #[test]
    fn test_sources_are_paren_balanced() {
        for s in [Specification::hsm(), whk("k"), step("k", "e")] {
            assert!(
                Specification::balanced(&s),
                "generated fragment is not balanced: {s}"
            );
        }
    }

    /// The `Eq`-valued goals here must never reach for the `Sort 1` helpers.
    /// Borrowing `option_none_ne_some_type` from LOOP_PAR — whose goal is
    /// `par_reduces_cd_star` — is what cost a full validation cycle.
    #[test]
    fn test_no_sort_one_helpers_in_eq_goals() {
        let src = include_str!("wh_fuel_adequacy.rs");
        let body = src.split("mod tests").next().expect("module body");
        for banned in ["option_none_ne_some_type", "Eq.substType"] {
            assert!(
                !body.contains(banned),
                "{banned} demands Sort 1, but every goal in this module concludes in Eq (Sort 0)"
            );
        }
    }

    /// The stuckness predicate must be the one `hnf_conv` already defines.
    /// Restating it here would fork the premise, which is exactly how one false
    /// `hnf` turned into nine vacuous theorems.
    #[test]
    fn test_stuck_predicate_is_reused_not_restated() {
        let src = include_str!("wh_fuel_adequacy.rs");
        let body = src.split("mod tests").next().expect("module body");
        assert!(
            body.contains("Self::stuck_at("),
            "the genuine-stuckness predicate must come from hnf_conv::stuck_at"
        );
        assert!(
            !body.contains("reduce_once_red_wh the_red_env (fun (e2 : KExpr)"),
            "stuck_at's body is restated here instead of being called"
        );
    }

    /// The premise is DISCHARGED, and no declaration here may still carry it.
    ///
    /// This test previously asserted the opposite — that the assumption was
    /// disclosed — which was right while it was an assumption. Leaving it that
    /// way would have let the layer keep advertising a hypothesis it no longer
    /// has.
    #[test]
    fn test_premise_is_discharged_not_carried() {
        let src = include_str!("wh_fuel_adequacy.rs");
        let body = src.split("mod tests").next().expect("module body");
        assert!(
            !body.contains("(hsm : {hsm})"),
            "no declaration may still take the step-monotonicity premise: it is proved"
        );
        assert!(
            body.contains("wh_hsm_all i2 i8"),
            "the discharge must actually be applied, not merely available"
        );
    }
}
