// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Towards `hnf_conv`: the convergence premise, witnessed before it is used.
//!
//! ```text
//! wh_perm_stuck e      : forall j, reduce_once_red_wh the_red_env (whnf … j) e = none
//! wh_perm_stuck_sort   : wh_perm_stuck (sort 0)
//! wh_perm_stuck_app    : wh_perm_stuck (app (const anonymous []) (sort 0))
//! ```
//!
//! # Why the convergence hypothesis is "stuck at EVERY budget"
//!
//! One-step fuel stability is too weak. `cx_stuck` is returned unchanged at fuel 1
//! *and* at fuel 2 — its pre-pass runs at one less fuel, and needs two — and only
//! fires at fuel 3. So `whnf m e = some r` together with `whnf (m+1) e = some r`
//! does not mean the loop has converged.
//!
//! `wh_perm_stuck` is the honest condition: the step function finds nothing **at
//! any pre-pass budget**. It rules `cx_stuck` out (at budget 2 the step fires,
//! `reduce_once_red_wh_fires`) while remaining satisfiable — which is checked here
//! rather than assumed, at a sort *and* at an application, because an application
//! is the shape where the whole question bites.
//!
//! **Checking a premise is inhabited before building on it is the entire lesson of
//! this program.** `def_eq_fuel_complete` is vacuous because nobody asked whether
//! anything could satisfy `hnf`.
//!
//! # The `bvar` gap — found here, and now CLOSED
//!
//! Asking that question here immediately produced another answer, and a
//! humbling one — `nf_head` used to have four arms and none covered `bvar`:
//!
//! > `reduce_once_red`'s `bvar` arm returns `none`, so `whnf_fuel_red renv 1
//! > (bvar i) = some (bvar i)`. But `nf_head` has four arms — `lam`, `rigid`,
//! > `neutral`, `constdead` — and `rigid_app_head` has five — `sort`, `pi`,
//! > `lit`, `app`, `proj`. **Neither mentions `bvar`.** So `nf_head (bvar i)` is
//! > uninhabited, and `hnf` is false at `bvar 0`.
//!
//! That was a **one-line counterexample**, and it refuted `hnf` on its own. The
//! elaborate `cx_stuck` construction in `hnf_refutation.rs` was not the simplest
//! disproof available, and it should have been found first.
//!
//! **`nf_head` now has a fifth arm, `bvar`, so this gap is closed.** The arm is
//! unconditional and cheaply so: `par_reduces_cd` has no arm mentioning `bvar`,
//! and both `iota_step` and `delta_step` require a const head, so only `refl`
//! relates a bound variable to anything. A `bvar` is as rigid as a normal form
//! gets, and `nf_head_star_preserves_tag`'s new arm needs no `LiftP` because the
//! `bvar` inversion is equation-form rather than CPS.
//!
//! It does not make that work redundant, and the difference matters for what to
//! fix. `bvar` is a **shallow** refutation: a predicate is missing an arm, and the
//! repair is local — add the arm, or carry a closedness hypothesis such as
//! `red_closed_at`. `cx_stuck` is a **deep** one: it exposed a divergence between
//! the reflected reduction and the deployed kernel (`iota_prepass.rs`), which no
//! amount of arm-adding repairs. And `whnf_fuel_red_wh_starves` exposed a third,
//! independent obstruction — fuel exhaustion — which no amount of fidelity
//! repairs. Three refutations, three distinct causes, three distinct fixes.
//!
//! # What `hnf_conv` must therefore say
//!
//! ```text
//! hnf_conv : wh_perm_stuck r          -- convergence: stuck at every budget
//!         -> <the stuck-recursor case>
//!         -> nf_head r
//! ```
//!
//! One side condition fewer than when this module was written, because the `bvar`
//! gap was closed rather than hypothesised around. Of `nf_head`'s cases, `lam`,
//! `sort`/`pi`/`lit`/`proj`, `const`, **`bvar`** and applications on δ-dead
//! **recmeta-free** const heads are now reachable; only the stuck recursor is
//! not.
//!
//! `DerivedProved`, empty axiom closures.

use super::defeq_fuel::SRC_DEF_EQ_FUEL;
use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The convergence predicate, its inhabitants, and the `bvar` refutation.
    pub(super) fn add_hnf_conv(&mut self) -> Result<(), SpecError> {
        self.add_perm_stuck()?;
        self.add_hnf_conv_theorem()?;
        self.add_app_supplier()?;
        self.add_def_eq_fuel_wh()?;
        self.add_def_eq_fuel_wh3()?;
        self.add_wh_algorithm_base()?;
        Ok(())
    }

    /// The convergence witnesses: a sort, and — the one that matters — an
    /// APPLICATION, since that is the shape `nf_head`'s hard case has.
    fn perm_stuck_witnesses() -> [(&'static str, &'static str, &'static str); 2] {
        [
            (
                "wh_perm_stuck_sort",
                "(KExpr.sort Level.zero)",
                "a sort: reduce_once_red_wh's sort arm returns none regardless of the pre-pass \
                 continuation, so one Eq.refl serves every budget",
            ),
            (
                "wh_perm_stuck_app",
                "(KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero))",
                "an APPLICATION, which is the shape that matters: nf_head's hard case is an \
                 application on a const head. Name.anonymous is in neither component of the \
                 reflected env, so the head neither delta-unfolds nor carries recursor metadata, \
                 iota_reduct_whc short-circuits at its second opt_bind level before ever consulting \
                 the pre-pass, and the step is none at every budget",
            ),
        ]
    }

    /// The stuck hypothesis, spelled out rather than named.
    ///
    /// `wh_perm_stuck x` is definitionally this, but writing it inline means the
    /// proof never depends on whether that definition unfolds at application —
    /// a question this fragment answers differently for reducible and ordinary
    /// definitions, and not one worth a 26-minute cycle to discover.
    pub(super) fn stuck_at(x: &str) -> String {
        // PARENTHESISED. A bare `forall (j : Nat), P j` used as the left side of
        // an arrow scopes over EVERYTHING to its right, so
        // `forall j, P j -> Q -> R` means `forall j, (P j -> Q -> R)` — a
        // different and much weaker statement, which typechecks as a motive and
        // then fails to match the recursor's arm types. That is what the first two
        // attempts at hnf_conv did.
        format!(
            "(forall (j : Nat), Eq (OptionType KExpr) \
             (reduce_once_red_wh the_red_env \
             (fun (e2 : KExpr) => whnf_fuel_red_wh the_red_env j e2) {x}) \
             (OptionType.none KExpr))"
        )
    }

    /// The residual application premise.
    /// The residual application premise.
    ///
    /// The binders are `zf`/`za`, NOT `f`/`a`, and that is load-bearing. This
    /// premise gets substituted into arms whose own payload binders are named `f`
    /// and `a` — the `app` arm's `x` is literally `(KExpr.app f a)` — so naming
    /// the quantifiers `f`/`a` CAPTURES the arm's variables under the premise's
    /// own quantifiers. String substitution has no alpha-renaming to save you.
    /// The kernel reported it as `fvar mismatch: FVarId(4) vs FVarId(1)`: the
    /// right complaint, at the wrong distance from the cause.
    fn app_side(x: &str) -> String {
        format!("forall (zf : KExpr) (za : KExpr), Eq KExpr {x} (KExpr.app zf za) -> nf_head {x}")
    }

    fn hnf_conv_goal(x: &str) -> String {
        format!(
            "{stuck} -> ({app}) -> nf_head {x}",
            stuck = Self::stuck_at(x),
            app = Self::app_side(x),
        )
    }

    /// `hnf_conv` — the convergence-conditioned head classification.
    ///
    /// Eight of `KExpr`'s nine constructors discharge outright; only `app` is
    /// residual, and it is handed back to the caller as an explicit premise
    /// rather than assumed away. That premise is genuinely satisfiable — three
    /// lemmas now supply it (`iota_immune_of_dead_const_head`,
    /// `iota_immune_of_under_applied`, `iota_immune_of_bvar_major`) — which is
    /// the difference between this and `hnf`.
    fn add_hnf_conv_theorem(&mut self) -> Result<(), SpecError> {
        // (payload binders, RECURSIVE FIELD NAMES, form, arm body).
        //
        // The induction-hypothesis binders must be typed at the MOTIVE APPLIED TO
        // EACH RECURSIVE FIELD, not at KExpr. Typing them `KExpr` is what the
        // first attempt did, and the kernel reported `expected Pi(...), got
        // Discriminant(6) vs Discriminant(3)` — Pi where Const was supplied.
        // Recursors whose motive is a function type make this easy to get wrong,
        // because the nearby precedent (kexpr_lit_inj) has motive `fun _ => Nat`
        // and so really does bind its IHs at a constant.
        let arms: [(&str, &[&str], &str, &str); 9] = [
            (
                "(n : Level)",
                &[],
                "(KExpr.sort n)",
                "nf_head.rigid (KExpr.sort n) (rigid_app_head.sort n)",
            ),
            ("(i : Nat)", &[], "(KExpr.bvar i)", "nf_head.bvar i"),
            (
                "(f : KExpr) (a : KExpr)",
                &["f", "a"],
                "(KExpr.app f a)",
                "happ f a (Eq.refl KExpr (KExpr.app f a))",
            ),
            (
                "(ty : KExpr) (b : KExpr)",
                &["ty", "b"],
                "(KExpr.lam ty b)",
                "nf_head.lam ty b",
            ),
            (
                "(ty : KExpr) (b : KExpr)",
                &["ty", "b"],
                "(KExpr.pi ty b)",
                "nf_head.rigid (KExpr.pi ty b) (rigid_app_head.pi ty b)",
            ),
            (
                "(n : Name) (us : ListType Level)",
                &[],
                "(KExpr.const n us)",
                "nf_head.constdead n us \
              (delta_reduct_eq_none_of_defval_none (red_def the_red_env) \
              (KExpr.const n us) n \
              (Eq.refl (OptionType Name) (OptionType.some Name n)) (hstuck Nat.zero))",
            ),
            (
                "(ty : KExpr) (v : KExpr) (b : KExpr)",
                &["ty", "v", "b"],
                "(KExpr.let_ ty v b)",
                "option_none_ne_some_type KExpr (instantiate b v) \
              (nf_head (KExpr.let_ ty v b)) \
              (Eq.symm (OptionType KExpr) \
              (OptionType.some KExpr (instantiate b v)) (OptionType.none KExpr) \
              (hstuck Nat.zero))",
            ),
            (
                "(s : Name) (i : Nat) (sub : KExpr)",
                &["sub"],
                "(KExpr.proj s i sub)",
                "nf_head.rigid (KExpr.proj s i sub) (rigid_app_head.proj s i sub)",
            ),
            (
                "(v : Nat)",
                &[],
                "(KExpr.lit v)",
                "nf_head.rigid (KExpr.lit v) (rigid_app_head.lit v)",
            ),
        ];
        let mut body = String::new();
        for (payload, fields, form, arm) in arms {
            let mut ihs = String::new();
            for (n, fld) in fields.iter().enumerate() {
                ihs.push_str(&format!("(_c{n} : {}) ", Self::hnf_conv_goal(fld)));
            }
            body.push_str(&format!(
                "(fun {payload} {ihs}(hstuck : {stuck}) (happ : {app}) => {arm}) ",
                stuck = Self::stuck_at(form),
                app = Self::app_side(form),
            ));
        }
        self.add_recursive_def(
            &format!(
                "def hnf_conv (r : KExpr) : {goal} := \
                 KExpr.rec (fun (x : KExpr) => {motive}) {body}r",
                goal = Self::hnf_conv_goal("r"),
                motive = Self::hnf_conv_goal("x"),
            ),
            "hnf_conv: THE CONVERGENCE-CONDITIONED HEAD CLASSIFICATION — the honest replacement for \
             the false hnf. \
             \
             hnf claimed every whnf result has a normal-form head, and was refuted THREE ways: a \
             missing nf_head arm (fixed), a fidelity gap between the reflected reduction and the \
             deployed kernel (closed by the pre-pass loop), and fuel exhaustion, which is \
             structural and no fidelity repairs. This statement carries the convergence the third \
             refutation forces — the step function finds nothing AT ANY pre-pass budget — and \
             hands back the one case it cannot discharge instead of assuming it away. \
             \
             EIGHT OF NINE CONSTRUCTORS DISCHARGE OUTRIGHT. sort, pi, lit and proj are rigid \
             (proj's arm takes any subject); lam and bvar have their own nf_head arms; a const is \
             constdead because reduce_once_red_wh's const arm IS defval_for, so the stuck \
             hypothesis is delta-deadness definitionally; and a let_ cannot be stuck at all, since \
             the step always fires on it. \
             \
             ONLY app IS RESIDUAL, and it is a PREMISE, not an assumption — the difference being \
             that this one is satisfiable. Three lemmas now supply it: \
             iota_immune_of_dead_const_head for a delta-dead recmeta-free head, \
             iota_immune_of_under_applied for a recursor with no major present, and \
             iota_immune_of_bvar_major for the canonical Nat.rec P z s (bvar i). What is still \
             missing is a major stuck for some other reason, and spines with arguments past the \
             major slot. \
             \
             SCOPE, which must travel with any statement of this: it is about the reflected \
             calculus at the fixed environment, and DefEq contains no eta, no proof irrelevance, \
             no structure-eta, no universe conversion and no literal computation — all of which \
             the shipping is_def_eq implements. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The residual premise, discharged for RIGID-headed applications.
    ///
    /// `rigid_app_head`'s own `app` arm already says a rigid head survives being
    /// applied, so this is one constructor away — but it is the supplier that
    /// makes `hnf_conv` usable without any side condition on the huge class of
    /// applications whose spine head is a sort, pi, literal or projection.
    ///
    /// What it does NOT cover, and why the const case is genuinely harder:
    /// `nf_head.neutral` needs `iota_neutral f` as well as
    /// `iota_immune (app f a)`, and `iota_neutral`'s own `app` arm recurses — so a
    /// const-headed spine needs immunity at EVERY PREFIX, not just at the whole
    /// term. For an under-applied spine every prefix is also under-applied, so
    /// `iota_immune_of_under_applied` should chain; that induction is not written
    /// yet.
    fn add_app_supplier(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def nf_head_app_of_rigid (f : KExpr) (a : KExpr) (hr : rigid_app_head f) : \
             nf_head (KExpr.app f a) := \
             nf_head.rigid (KExpr.app f a) (rigid_app_head.app f a hr)",
            "nf_head_app_of_rigid: an application on a rigid head has a normal-form head. \
             Discharges hnf_conv's residual premise for every application whose spine head is a \
             sort, pi, literal or projection — the whole non-const, non-bvar class — in one \
             constructor. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            "def hnf_conv_rigid (r : KExpr) \
             (hstuck : (forall (j : Nat), Eq (OptionType KExpr) \
             (reduce_once_red_wh the_red_env \
             (fun (e2 : KExpr) => whnf_fuel_red_wh the_red_env j e2) r) \
             (OptionType.none KExpr))) \
             (hrig : forall (f : KExpr) (a : KExpr), Eq KExpr r (KExpr.app f a) -> \
             rigid_app_head f) : nf_head r := \
             hnf_conv r hstuck \
             (fun (f : KExpr) (a : KExpr) (heq : Eq KExpr r (KExpr.app f a)) => \
             Eq.substType KExpr (fun (X : KExpr) => nf_head X) (KExpr.app f a) r \
             (Eq.symm KExpr r (KExpr.app f a) heq) \
             (nf_head_app_of_rigid f a (hrig f a heq)))",
            "hnf_conv_rigid: hnf_conv with its residual premise replaced by the far weaker demand \
             that IF the term is an application THEN its function part is rigid-headed. \
             \
             This is the usable form for everything except const-headed and bvar-headed spines. \
             It is stated separately rather than folded in, because the two remaining classes need \
             genuinely different arguments — a const head needs the iota_neutral prefix chain, and \
             a bvar head is now covered by rigid_app_head's bvar arm. Collapsing them would hide which \
             is which. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The conversion algorithm on the FAITHFUL loop.
    ///
    /// Derived from `SRC_DEF_EQ_FUEL` by one substitution — `whnf_fuel_red renv k`
    /// becomes `whnf_fuel_red_wh renv k` — so the two cannot drift.
    ///
    /// # Why the algorithm has to move, and why no restatement saves the old one
    ///
    /// `def_eq_fuel_complete` carries `hnf`, which is FALSE, so it proves nothing.
    /// The natural repair is to weaken the premise rather than change the
    /// algorithm — but that does not work here, and the reason is specific:
    ///
    /// `hnf_conv`'s case analysis discharges eight of nine constructors using only
    /// the step function's `const`, `let_`, `lam`, `sort`, `pi`, `lit`, `proj` and
    /// `bvar` arms, and **those arms are identical in both loops** (the pre-pass
    /// substitution touched only `reduce_app_head_red`). So the same argument
    /// works for the old loop too, leaving the same single residual: applications.
    ///
    /// And for the OLD loop that residual is genuinely **false**. `cx_stuck` is an
    /// old-loop whnf result (`cx_whnf_stuck`, by `Eq.refl`) which is an
    /// application and has no normal-form head (`cx_not_nf_head`). So every
    /// candidate premise strong enough to finish the capstone is unsatisfiable
    /// over the old loop's stuck set. The algorithm itself is what must change.
    ///
    /// Under the faithful loop `cx_stuck` is no longer stuck at all
    /// (`reduce_once_red_wh_fires`), so it is not a counterexample to anything.
    /// The conversion algorithm on the THREE-WAY loop, and its computation
    /// rules.
    ///
    /// Same single substitution that produced `def_eq_fuel_wh`, one loop
    /// further on. The point of it is that this one is FUEL-MONOTONE: its whnf
    /// legs are `whnf_fuel_red_wh3`, for which `whnf_fuel_red_wh3_monotone`
    /// holds, where the two-way legs have `whnf_fuel_red_wh_monotone_is_false`.
    /// Every layer of the completeness chain that closes a step with whnf-leg
    /// monotonicity was blocked by that falsity and is reachable here.
    fn add_def_eq_fuel_wh3(&mut self) -> Result<(), SpecError> {
        let src = SRC_DEF_EQ_FUEL
            .replace("def def_eq_fuel (renv", "def def_eq_fuel_wh3 (renv")
            .replace("whnf_fuel_red renv k", "whnf_fuel_red_wh3 renv k");
        assert!(
            src.contains("whnf_fuel_red_wh3 renv k b")
                && src.contains("whnf_fuel_red_wh3 renv k a"),
            "both reduction sites must be redirected to the three-way loop"
        );
        assert!(
            !src.contains("whnf_fuel_red renv"),
            "no two-way reduction site may survive the substitution"
        );
        self.add_recursive_def(
            &src,
            "def_eq_fuel_wh3: the conversion algorithm on the three-way loop. Same shape as \
             def_eq_fuel and def_eq_fuel_wh, one substitution apart, but with a property neither \
             of the others has where it matters: its whnf legs are MONOTONE in the fuel. \
             \
             def_eq_fuel's legs are monotone but its loop is not faithful to the deployed kernel; \
             def_eq_fuel_wh's loop is faithful but its legs are NOT monotone, refuted by \
             computation. This one is both. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            "def def_eq_fuel_wh3_zero (renv : RedEnv) (a : KExpr) (b : KExpr) : \
             Eq Bool (def_eq_fuel_wh3 renv Nat.zero a b) Bool.false := \
             Eq.refl Bool (def_eq_fuel_wh3 renv Nat.zero a b)",
            "def_eq_fuel_wh3_zero: fails closed at fuel 0, definitionally. DerivedProved, zero \
             axiom_deps.",
        )?;
        self.add_recursive_def(
            "def def_eq_fuel_wh3_succ (renv : RedEnv) (k : Nat) (a : KExpr) (b : KExpr) : \
             Eq Bool (def_eq_fuel_wh3 renv (Nat.succ k) a b) \
             (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (na : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false (fun (nb : KExpr) => def_eq_struct (def_eq_fuel_wh3 renv k) na nb) \
             (whnf_fuel_red_wh3 renv k b)) \
             (whnf_fuel_red_wh3 renv k a)) := \
             Eq.refl Bool (def_eq_fuel_wh3 renv (Nat.succ k) a b)",
            "def_eq_fuel_wh3_succ: one fuel layer unfolds to whnf both sides through the THREE-WAY \
             loop, then compare structurally at fuel k (Eq.refl, definitional). \
             \
             The comparison is def_eq_struct applied to the two results, and def_eq_struct is \
             parametric in its comparator — which is why def_eq_struct_mono needs NO port to reach \
             this algorithm, and why the structural half of the completeness chain comes free \
             here as it did for def_eq_fuel_wh. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_def_eq_fuel_wh(&mut self) -> Result<(), SpecError> {
        let src = SRC_DEF_EQ_FUEL
            .replace("def def_eq_fuel (renv", "def def_eq_fuel_wh (renv")
            .replace("whnf_fuel_red renv k", "whnf_fuel_red_wh renv k");
        assert!(
            src.contains("whnf_fuel_red_wh renv k b") && src.contains("whnf_fuel_red_wh renv k a"),
            "both reduction sites must be redirected to the faithful loop"
        );
        self.add_recursive_def(
            &src,
            "def_eq_fuel_wh: THE CONVERSION ALGORITHM ON THE FAITHFUL LOOP — the object a \
             non-vacuous completeness theorem has to be about. \
             \
             Identical to def_eq_fuel except that both reductions go through whnf_fuel_red_wh, \
             which performs the major-premise whnf pre-pass the DEPLOYED kernel performs \
             (micro/checker.rs:777) and the original reflected loop omits. Derived from the same \
             source constant by one substitution, so the two cannot drift. \
             \
             WHY THE ALGORITHM AND NOT JUST THE PREMISE. def_eq_fuel_complete's hnf premise is \
             false, and the natural repair — weaken the premise — provably fails here. \
             hnf_conv discharges eight of nine constructors using step-function arms that are \
             IDENTICAL in both loops, so the same analysis applies to the old loop and leaves the \
             same single residual: applications. For the old loop that residual is FALSE, because \
             cx_stuck is an old-loop whnf result (cx_whnf_stuck, by refl) that is an application \
             with no normal-form head (cx_not_nf_head). Any premise strong enough to finish the \
             capstone is therefore unsatisfiable over the old loop's stuck set. Under the faithful \
             loop cx_stuck is not stuck at all (reduce_once_red_wh_fires), so it is not a \
             counterexample to anything. \
             \
             This is a DEFINITION, census-neutral, and it does not by itself prove completeness — \
             the completeness spine (rounds, dispatch, capstone: ~17 files) still has to be \
             re-derived over it. What it does is make the non-vacuous statement expressible about \
             an algorithm that can satisfy it, which the old one cannot. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// The algorithm-side base for the faithful loop: the acceptance witness and
    /// the two computation rules.
    ///
    /// Small, and deliberately landed before anything is built on them. Both rules
    /// are `Eq.refl` — the algorithm's fuel structure is definitional — so the only
    /// real content is that the target type exists and unfolds the same way.
    ///
    /// # What this reveals about the size of the remaining job
    ///
    /// The struct layer is **parametric in the comparator** (`def {name} {cmp} …`),
    /// so `def_eq_struct_sound`, `def_eq_struct_intro` and the nine computation
    /// rules need **no change whatever** — they instantiate at `def_eq_fuel_wh`
    /// exactly as they do at `def_eq_fuel`. That is 65 of the ~100 `def_eq_fuel`
    /// mentions across the spine, discharged by a design decision made long before
    /// this problem appeared.
    ///
    /// What genuinely needs re-deriving splits in two:
    ///
    /// * **reduction-side** — `fuel_adequacy`, `rbelow_descent`, `defeq_whnf_join`,
    ///   `defeq_nf_agree`, `whnf_classify`: facts about `whnf_fuel_red` that need
    ///   `whnf_fuel_red_wh` counterparts. The `rbelow` layer is the awkward one,
    ///   because the faithful loop's steps include ι-with-pre-pass, a different
    ///   step relation.
    /// * **algorithm-side** — `defeq_fuel_mono`, `fuel_pairing`,
    ///   `defeq_complete_*`, `defeq_round_*`, `defeq_capstone`: everything phrased
    ///   in terms of `DefEqFuelAccepts`, which is tied to a specific comparator.
    fn add_wh_algorithm_base(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive DefEqFuelAcceptsWh (a : KExpr) (b : KExpr) : Type\n\
             | mk : forall (n : Nat), Eq Bool (def_eq_fuel_wh the_red_env n a b) Bool.true -> \
             DefEqFuelAcceptsWh a b",
            "DefEqFuelAcceptsWh a b: some fuel is enough for the FAITHFUL algorithm to accept a \
             against b — the conclusion a non-vacuous completeness capstone must reach. Same \
             single-constructor witness idiom as DefEqFuelAccepts, since the fragment has no \
             Exists. Registering the target type is not a completeness claim. Census-neutral.",
        )?;
        self.add_recursive_def(
            "def def_eq_fuel_wh_zero (renv : RedEnv) (a : KExpr) (b : KExpr) : \
             Eq Bool (def_eq_fuel_wh renv Nat.zero a b) Bool.false := \
             Eq.refl Bool (def_eq_fuel_wh renv Nat.zero a b)",
            "def_eq_fuel_wh_zero: the faithful algorithm also fails CLOSED at fuel 0 (Eq.refl, \
             definitional). Failing closed is what makes a soundness base case absurd rather than \
             an argument — and it is why completeness, not soundness, is the hard direction here. \
             DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            "def def_eq_fuel_wh_succ (renv : RedEnv) (k : Nat) (a : KExpr) (b : KExpr) : \
             Eq Bool (def_eq_fuel_wh renv (Nat.succ k) a b) \
             (OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (na : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false (fun (nb : KExpr) => def_eq_struct (def_eq_fuel_wh renv k) na nb) \
             (whnf_fuel_red_wh renv k b)) \
             (whnf_fuel_red_wh renv k a)) := \
             Eq.refl Bool (def_eq_fuel_wh renv (Nat.succ k) a b)",
            "def_eq_fuel_wh_succ: one fuel layer of the faithful algorithm unfolds to whnf both \
             sides THROUGH THE PRE-PASS LOOP, then compare structurally at fuel k (Eq.refl, \
             definitional). \
             \
             Note what this exposes: the structural comparison is `def_eq_struct` applied to \
             `def_eq_fuel_wh renv k` — the SAME def_eq_struct the original algorithm uses. The \
             struct layer is parametric in its comparator, so def_eq_struct_sound, \
             def_eq_struct_intro and the nine computation rules carry over to the faithful \
             algorithm with no change at all. That is 65 of the ~100 def_eq_fuel mentions in the \
             completeness spine discharged by a design decision made long before this problem \
             appeared. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_perm_stuck(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def wh_perm_stuck (e : KExpr) : Prop := \
             forall (j : Nat), Eq (OptionType KExpr) \
             (reduce_once_red_wh the_red_env \
             (fun (e2 : KExpr) => whnf_fuel_red_wh the_red_env j e2) e) \
             (OptionType.none KExpr)",
            "wh_perm_stuck e: the faithful loop's step function finds nothing to do on e AT ANY \
             pre-pass budget. This is the convergence hypothesis hnf needs, and the quantifier is \
             load-bearing. \
             \
             One-step fuel stability would NOT do: cx_stuck is returned unchanged at fuel 1 and \
             again at fuel 2 — its pre-pass runs at one less fuel and needs two — and only fires \
             at fuel 3. So agreement between consecutive fuels does not mean the loop converged. \
             Quantifying over every budget rules cx_stuck out, since at budget 2 the step fires \
             (reduce_once_red_wh_fires). \
             \
             Prop-valued: a forall into Eq stays in Prop. Census-neutral.",
        )?;

        // Non-vacuity, at two shapes. The sort is the easy one; the application
        // is the one that matters, since applications are where nf_head's hard
        // case lives.
        for (name, subject, why) in Self::perm_stuck_witnesses() {
            self.add_recursive_def(
                &format!(
                    "def {name} : wh_perm_stuck {subject} := \
                     fun (j : Nat) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)"
                ),
                &format!(
                    "{name} (NON-VACUITY): wh_perm_stuck holds at {why}. \
                     \
                     Registered BEFORE anything is built on wh_perm_stuck, deliberately. The def-eq \
                     completeness capstone is vacuous precisely because nobody asked whether \
                     anything could satisfy hnf, and a convergence hypothesis nothing satisfies \
                     would repeat that failure one level down. DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The residual premise's binders must not collide with ANY constructor
    /// payload name used in the arms.
    ///
    /// String substitution has no alpha-renaming. The `app` arm substitutes
    /// `x := (KExpr.app f a)` into a premise that quantifies its own variables; if
    /// those are also called `f`/`a`, the arm's binders are captured. It
    /// elaborates as a well-formed but WRONG type and surfaces later as an fvar
    /// mismatch, far from the cause.
    #[test]
    fn test_residual_premise_binders_cannot_capture() {
        let side = Specification::app_side("(KExpr.app f a)");
        for payload in [
            "(f :", "(a :", "(n :", "(i :", "(ty :", "(b :", "(v :", "(us :", "(s :", "(sub :",
        ] {
            assert!(
                !side.contains(payload),
                "premise binder {payload} collides with a constructor payload name: {side}"
            );
        }
        assert!(side.contains("(zf : KExpr) (za : KExpr)"));
    }

    /// The convergence hypothesis must be PARENTHESISED.
    ///
    /// `forall j, P j -> Q -> R` parses as `forall j, (P j -> Q -> R)`, which is a
    /// different — and much weaker — statement than `(forall j, P j) -> Q -> R`.
    /// It typechecks perfectly well as a motive and then fails to match the
    /// recursor's arm types, so the kernel reports a Pi/Const shape mismatch far
    /// from the actual mistake. Two cycles.
    #[test]
    fn test_convergence_hypothesis_is_parenthesised() {
        let stuck = Specification::stuck_at("r");
        assert!(
            stuck.starts_with("(forall (j : Nat)") && stuck.ends_with(')'),
            "the whole quantified hypothesis must be bracketed: {stuck}"
        );
        let goal = Specification::hnf_conv_goal("r");
        assert!(
            goal.starts_with("(forall (j : Nat)"),
            "and it must sit to the LEFT of the first arrow: {goal}"
        );
    }

    /// `KExpr.rec`'s induction hypotheses are the MOTIVE APPLIED to each
    /// recursive field — not `KExpr`.
    ///
    /// Easy to get wrong here because the nearest precedent, `kexpr_lit_inj`, has
    /// motive `fun _ => Nat` and so genuinely does bind its IHs at a constant.
    /// When the motive is a function type, binding them at `KExpr` yields
    /// `expected Pi(...), got Discriminant(6) vs Discriminant(3)` — Pi where Const
    /// was supplied. That cost a cycle.
    #[test]
    fn test_induction_hypotheses_are_typed_at_the_motive() {
        let goal = Specification::hnf_conv_goal("f");
        assert!(
            goal.contains("nf_head f"),
            "the motive at a field mentions that field: {goal}"
        );
        assert!(
            goal.contains("->"),
            "the motive is a function type, which is exactly why IHs cannot be KExpr"
        );
    }

    /// The convergence premise must be witnessed at an APPLICATION, not only at
    /// a sort. `nf_head`'s hard case is an application, so a hypothesis
    /// satisfied only by sorts would be technically inhabited and useless — the
    /// same shape of mistake as a premise satisfied by nothing at all.
    #[test]
    fn test_convergence_is_witnessed_where_it_matters() {
        let ws = Specification::perm_stuck_witnesses();
        assert_eq!(ws.len(), 2, "a sort and an application");
        assert!(
            ws.iter()
                .any(|(_, subject, _)| subject.contains("KExpr.app")),
            "the witness that matters must be at an APPLICATION — nf_head's hard case is an \
             application, so a premise satisfied only by sorts would be inhabited and useless"
        );
        assert!(
            ws.iter()
                .any(|(_, subject, _)| subject.contains("KExpr.sort")),
            "and the easy shape too"
        );
    }
}
