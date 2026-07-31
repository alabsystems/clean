// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `hnf` is FALSE — so `def_eq_fuel_complete` is VACUOUS.
//!
//! ```text
//! hnf_is_false :
//!   (forall (m e r : KExpr), whnf_fuel_red the_red_env m e = some r -> nf_head r)
//!     -> Empty
//! ```
//!
//! The def-eq completeness capstone (`defeq_capstone.rs`) carries `hnf` as its
//! last premise, and its own comment called that premise "open". It is not open.
//! It is false, and a conditional theorem with a false premise proves nothing.
//! This module says so in the kernel rather than in prose.
//!
//! ## The one-line reason
//!
//! `whnf_fuel_red` is **weak-head**: `reduce_once_red`'s `app` arm discards the
//! argument's recursive result (`_ca`, `whnf_progress.rs:545`) and `opt_app_ilift`
//! only ever rebuilds `KExpr.app f2 a` with the *original* `a`. So whnf never
//! reduces inside a recursor's major premise.
//!
//! But `nf_head`'s only arm that can accept a const-headed application spine is
//! `neutral`, and that arm demands `iota_immune`, which is **permanent** ι-deadness:
//!
//! ```text
//! iota_immune e := forall e2 r, par_reduces_cd_star the_red_env e e2
//!                                 -> iota_step (red_rec the_red_env) e2 r -> Empty
//! ```
//!
//! quantified over *every* reduct — and `par_reduces_cd`'s `app` arm **does**
//! reduce arguments. A permanence property closed under a reduction that goes
//! under arguments cannot be read off a weak-head algorithm's stopping condition.
//! That gap is the whole content of this refutation.
//!
//! ## The counterexample
//!
//! Take the generated Guard-4 ι-redex `kcre_witness_nat_zero_redex` — real
//! reflected `Nat.rec` (`RecMeta` 0 params / 1 motive / 2 minors / 0 indices, so
//! the major premise is the **last** of four arguments) applied to three `sort 0`
//! placeholders and the constructor `Nat.zero` — and wrap its major premise in an
//! identity β-redex:
//!
//! ```text
//! cx_stuck := app cx_prefix (app (lam (sort 0) cx_major) (sort 0))
//! ```
//!
//! * **whnf is stuck on it.** `iota_reduct`'s fourth level is
//!   `kexpr_const_name (kapp_fn major)` (`iota_step.rs:127`) — the major must be
//!   *literally* const-headed, and there is **no** major-premise whnf pre-pass.
//!   Here `kapp_fn` of the β-redex is a `lam`, so `iota_reduct` is `none`; the head
//!   `Nat.rec` is a recursor so δ finds nothing; the head is not a `lam` so β finds
//!   nothing. `cx_whnf_stuck` is `Eq.refl` — the kernel computes it.
//! * **But it reduces to a real ι-redex.** One `par_reduces_cd.app` step with
//!   `refl` on the spine and `beta` on the argument lands exactly on
//!   `kcre_witness_nat_zero_redex`, whose ι-step is already proved by the Guard-4
//!   witness `the_red_env_iota_nonvacuous`. So `iota_immune cx_stuck` is refuted.
//! * **And no other `nf_head` arm fits.** Not `lam` and not `constdead` (it is an
//!   application — `kexpr_tag` discriminates, and that is arithmetic because
//!   `kexpr_tag` computes); not `rigid`, because `rigid_app_head` has **no const
//!   arm** by design, which `rigid_app_head_no_const` turns into
//!   `kexpr_const_name (kapp_fn cx_stuck) = none` against a head that computes to
//!   `some Nat.rec`.
//!
//! ## Why the spine is projected rather than written out
//!
//! The reflected constant names are interned as generated `kcre_name_<tag>` atoms
//! (`red_env_reflect.rs:1131`), so hardcoding `Nat.rec`/`Nat.zero` here would drift
//! the moment the interning table is regenerated. `cx_app_fn` / `cx_app_arg`
//! project the outermost application's two halves straight out of the generated
//! witness, so this module names **no** interned atom and cannot drift.
//!
//! ## Guard 3
//!
//! This is a designated `the_red_env` value-computation site, for the same reason
//! the two Guard-4 non-vacuity witnesses are: refuting a premise about the real
//! reflected environment requires computing over it. The carried metatheory stays
//! schematic.
//!
//! `DerivedProved`, empty axiom closure — the refutation is constructive.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The generated Guard-4 ι-redex: reflected `Nat.rec` applied through its
/// metadata-derived prefix to the `Nat.zero` constructor.
const WITNESS: &str = "kcre_witness_nat_zero_redex";

/// `KExpr.sort Level.zero` — the placeholder the generator itself uses, since
/// `iota_reduct` is name-keyed spine surgery and never inspects these.
const S0: &str = "(KExpr.sort Level.zero)";

impl Specification {
    /// `hnf` is false, hence the completeness capstone is vacuous.
    pub(super) fn add_hnf_refutation(&mut self) -> Result<(), SpecError> {
        self.add_spine_projections()?;
        self.add_counterexample()?;
        self.add_counterexample_facts()?;
        self.add_not_nf_head()?;
        self.add_refutation()?;
        Ok(())
    }

    /// `KExpr.rec` arms rebuilding the term unchanged, except `app`, which
    /// returns `pick` — `"f"` for the function half, `"a"` for the argument.
    ///
    /// Constructor order is `KExpr`'s own (`expr_model.rs:65`): sort, bvar, app,
    /// lam, pi, const, let_, proj, lit. Nine arms.
    fn spine_arms(pick: &str) -> String {
        format!(
            "(fun (sn : Level) => KExpr.sort sn) \
             (fun (bi : Nat) => KExpr.bvar bi) \
             (fun (f : KExpr) (a : KExpr) (_cf : KExpr) (_ca : KExpr) => {pick}) \
             (fun (lty : KExpr) (lb : KExpr) (_cl1 : KExpr) (_cl2 : KExpr) => \
             KExpr.lam lty lb) \
             (fun (pty : KExpr) (pb : KExpr) (_cp1 : KExpr) (_cp2 : KExpr) => \
             KExpr.pi pty pb) \
             (fun (cn : Name) (cus : ListType Level) => KExpr.const cn cus) \
             (fun (zty : KExpr) (zv : KExpr) (zb : KExpr) (_cz1 : KExpr) (_cz2 : KExpr) \
             (_cz3 : KExpr) => KExpr.let_ zty zv zb) \
             (fun (psn : Name) (pin : Nat) (psub : KExpr) (_cs : KExpr) => \
             KExpr.proj psn pin psub) \
             (fun (lv : Nat) => KExpr.lit lv) "
        )
    }

    fn add_spine_projections(&mut self) -> Result<(), SpecError> {
        for (name, pick, half) in [
            ("cx_app_fn", "f", "function"),
            ("cx_app_arg", "a", "argument"),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} (e : KExpr) : KExpr := \
                     KExpr.rec (fun (_e : KExpr) => KExpr) {arms}e",
                    arms = Self::spine_arms(pick),
                ),
                &format!(
                    "{name} e: the {half} half of e's OUTERMOST application, or e itself when e \
                     is not an application. Exists so the hnf refutation can take the generated \
                     Guard-4 iota redex apart WITHOUT naming an interned constant atom — the \
                     kcre_name_<tag> atoms are generated, so a hardcoded Nat.rec/Nat.zero here \
                     would drift the moment the interning table is regenerated. Note this is NOT \
                     kapp_fn, which peels the whole spine to the head; this peels exactly one \
                     layer. DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }

    fn add_counterexample(&mut self) -> Result<(), SpecError> {
        for (name, proj, what) in [
            (
                "cx_prefix",
                "cx_app_fn",
                "the three-argument Nat.rec spine prefix (params+motive+minors, no indices)",
            ),
            (
                "cx_major",
                "cx_app_arg",
                "the major premise, the Nat.zero constructor",
            ),
        ] {
            self.add_recursive_def(
                &format!("def {name} : KExpr := {proj} {WITNESS}"),
                &format!(
                    "{name}: {what}, projected out of the generated Guard-4 iota redex. Computes \
                     by unfolding — {WITNESS} is a value-ful def. DerivedProved, zero axiom_deps."
                ),
            )?;
        }

        // The counterexample: the SAME spine, with the major premise wrapped in
        // an identity beta-redex. The lam body is cx_major (a closed const), NOT
        // a bvar, so `instantiate` hits instantiate_at's one-step const leaf
        // (expr_model.rs:125) instead of the bvar/lift path.
        self.add_recursive_def(
            &format!(
                "def cx_stuck : KExpr := \
                 KExpr.app cx_prefix (KExpr.app (KExpr.lam {S0} cx_major) {S0})"
            ),
            "cx_stuck: THE COUNTEREXAMPLE to hnf. The real reflected Nat.rec applied to its \
             metadata-derived prefix and a major premise wrapped in an identity beta-redex. whnf \
             is stuck on it (iota_reduct needs a LITERALLY const-headed major and there is no \
             major-premise whnf pre-pass; kapp_fn of a beta-redex is a lam), yet one parallel step \
             reduces it to a genuine iota redex — so it is whnf-stuck without being permanently \
             iota-dead, which is exactly the gap between a weak-head algorithm and iota_immune. \
             \
             The lam body is cx_major, a closed const, rather than a bvar: instantiate then hits \
             instantiate_at's one-step const leaf instead of the bvar/lift path, so the conversion \
             the kernel must see is as short as possible. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_counterexample_facts(&mut self) -> Result<(), SpecError> {
        // (1) whnf really does stop on it — pure computation, exactly the shape
        // of the Guard-4 witnesses.
        self.add_recursive_def(
            "def cx_whnf_stuck : Eq (OptionType KExpr) \
             (whnf_fuel_red the_red_env (Nat.succ Nat.zero) cx_stuck) \
             (OptionType.some KExpr cx_stuck) := \
             Eq.refl (OptionType KExpr) (OptionType.some KExpr cx_stuck)",
            "cx_whnf_stuck: whnf_fuel_red returns cx_stuck UNCHANGED at one unit of fuel. Proof \
             by refl — the kernel whnf-evaluates reduce_once_red over the real reflected env to \
             none, and loop_dispatch's none branch returns some e0 (whnf_progress.rs:4186). \
             \
             This is the hypothesis side of hnf, discharged by computation: a designated \
             the_red_env value-computation site (Guard 3), for the same reason the two Guard-4 \
             non-vacuity witnesses are one. DerivedProved, zero axiom_deps.",
        )?;

        // (2) ...yet it reduces to the real iota redex, in one parallel step:
        // refl on the spine, beta on the argument.
        self.add_recursive_def(
            &format!(
                "def cx_reduces : par_reduces_cd_star the_red_env cx_stuck {WITNESS} := \
                 par_reduces_cd_star.step the_red_env cx_stuck {WITNESS} {WITNESS} \
                 (par_reduces_cd.app the_red_env cx_prefix cx_prefix \
                 (KExpr.app (KExpr.lam {S0} cx_major) {S0}) cx_major \
                 (par_reduces_cd.refl the_red_env cx_prefix) \
                 (par_reduces_cd.beta the_red_env {S0} {S0} cx_major cx_major {S0} {S0} \
                 (par_reduces_cd.refl the_red_env {S0}) \
                 (par_reduces_cd.refl the_red_env cx_major) \
                 (par_reduces_cd.refl the_red_env {S0}))) \
                 (par_reduces_cd_star.refl the_red_env {WITNESS})"
            ),
            "cx_reduces: cx_stuck reduces to the generated Guard-4 iota redex in ONE parallel \
             step — par_reduces_cd.app with refl on the spine and beta on the argument. The step's \
             target is app cx_prefix (instantiate cx_major (sort 0)), which converts to the \
             witness because cx_prefix and cx_major ARE its two halves and instantiate on a const \
             is a one-step leaf. \
             \
             This is the half whnf cannot see: par_reduces_cd's app arm reduces ARGUMENTS \
             (par_reduces_cd.rs:190) while reduce_once_red's app arm discards the argument's \
             result. DerivedProved, zero axiom_deps.",
        )?;

        // A no-name option discriminator, so the rigid arm never has to write
        // the interned Nat.rec atom.
        self.add_recursive_def(
            "def opt_name_is_none (o : OptionType Name) : Bool := \
             OptionType.rec Name (fun (_o : OptionType Name) => Bool) Bool.true \
             (fun (_v : Name) => Bool.false) o",
            "opt_name_is_none o: whether an optional Name is none. Exists so the refutation's \
             rigid arm can contradict `kexpr_const_name (kapp_fn cx_stuck) = none` WITHOUT naming \
             the interned Nat.rec atom that the left side computes to — option_none_ne_some would \
             require writing that generated name explicitly. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_not_nf_head(&mut self) -> Result<(), SpecError> {
        let goal = "Eq KExpr z cx_stuck -> Empty";
        // The two shape-impossible arms: an application is neither a lam nor a
        // const, and kexpr_tag computes, so this is arithmetic.
        let discriminate = |form: &str| {
            format!("kexpr_discr_t Empty {form} cx_stuck heq (Eq.refl Bool Bool.false)")
        };
        self.add_recursive_def(
            &format!(
                "def cx_not_nf_head (h : nf_head cx_stuck) : Empty := \
                 nf_head.rec (fun (z : KExpr) (_hz : nf_head z) => {goal}) \
                 (fun (lty : KExpr) (lbody : KExpr) \
                 (heq : Eq KExpr (KExpr.lam lty lbody) cx_stuck) => {lam}) \
                 (fun (e0 : KExpr) (hr : rigid_app_head e0) \
                 (heq : Eq KExpr e0 cx_stuck) => \
                 bool_false_ne_true_t Empty \
                 (Eq.substType (OptionType Name) \
                 (fun (o : OptionType Name) => Eq Bool Bool.false (opt_name_is_none o)) \
                 (kexpr_const_name (kapp_fn cx_stuck)) (OptionType.none Name) \
                 (rigid_app_head_no_const cx_stuck \
                 (Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) e0 cx_stuck heq hr)) \
                 (Eq.refl Bool Bool.false))) \
                 (fun (nff : KExpr) (nfa : KExpr) (_hin : iota_neutral nff) \
                 (hii : iota_immune (KExpr.app nff nfa)) \
                 (heq : Eq KExpr (KExpr.app nff nfa) cx_stuck) => \
                 Eq.substType KExpr (fun (z : KExpr) => iota_immune z) \
                 (KExpr.app nff nfa) cx_stuck heq hii \
                 {WITNESS} kcre_witness_nat_zero_reduct cx_reduces \
                 the_red_env_iota_nonvacuous) \
                 (fun (cn : Name) (cus : ListType Level) \
                 (_hdd : Eq (OptionType KExpr) \
                 (delta_reduct (red_def the_red_env) (KExpr.const cn cus)) \
                 (OptionType.none KExpr)) \
                 (heq : Eq KExpr (KExpr.const cn cus) cx_stuck) => {constdead}) \
                 cx_stuck h (Eq.refl KExpr cx_stuck)",
                lam = discriminate("(KExpr.lam lty lbody)"),
                constdead = discriminate("(KExpr.const cn cus)"),
            ),
            "cx_not_nf_head: cx_stuck has NO normal-form head — all four nf_head arms fail. \
             \
             lam and constdead die by generic discrimination (an application is neither), which is \
             arithmetic because kexpr_tag computes. rigid dies because rigid_app_head has NO const \
             arm by design: rigid_app_head_no_const turns the transported witness into \
             kexpr_const_name (kapp_fn cx_stuck) = none, while that head computes to some Nat.rec \
             — contradicted through opt_name_is_none so no generated atom is named. \
             \
             neutral is the substantive arm and the whole point: it carries \
             iota_immune (app f a) as a FIELD, and iota_immune is PERMANENT iota-deadness over \
             every par_reduces_cd_star reduct, so feeding it cx_reduces and the Guard-4 iota \
             witness yields Empty directly. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_refutation(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def hnf_is_false (hnf : forall (m : Nat) (e : KExpr) (r : KExpr), \
             Eq (OptionType KExpr) (whnf_fuel_red the_red_env m e) \
             (OptionType.some KExpr r) -> nf_head r) : Empty := \
             cx_not_nf_head (hnf (Nat.succ Nat.zero) cx_stuck cx_stuck cx_whnf_stuck)",
            "hnf_is_false: THE REFUTATION — def_eq_fuel_complete's last premise is FALSE, so the \
             capstone is VACUOUS and proves nothing about the conversion algorithm. Its own \
             comment called hnf 'open'; open would have meant unproved-but-true. \
             \
             Instantiate hnf at one unit of fuel on cx_stuck, which whnf returns unchanged \
             (cx_whnf_stuck, by computation), to obtain nf_head cx_stuck — then refute that \
             (cx_not_nf_head). \
             \
             WHY, in one line: whnf_fuel_red is WEAK-HEAD and never reduces inside a recursor's \
             major premise, while iota_immune — which nf_head's only const-headed-spine arm \
             demands — is PERMANENT iota-deadness quantified over every par_reduces_cd_star \
             reduct, and that reduction DOES go under arguments. A permanence property cannot be \
             read off a weak-head stopping condition. \
             \
             WHAT THIS DOES NOT TOUCH: def_eq_fuel_sound carries no hnf and stands. The \
             supporting development — confluence legs, the eight rounds, nf_app_leg_inv, tag \
             preservation — is all real and reusable. \
             \
             WHAT IT COSTS THE GATES: this passed a census of 0 axioms, 0 domain axioms and 0 \
             DerivedProved debt, because an axiom-closure walk structurally cannot see an \
             UNSATISFIABLE HYPOTHESIS. Zero axioms is not zero assumptions. The vacuity firewall's \
             eight items check generated relations for hidden Typing dependencies, which is a \
             different failure mode and would not have caught this either. \
             \
             THE ROUTE TO A NON-VACUOUS THEOREM: iota_step_no_recmeta_absurd proves a const-headed \
             spine whose head carries NO recmeta can never fire a top iota, which yields \
             iota_immune for non-recursor-headed spines and hence honest completeness for the \
             recursor-free fragment. The principled full fix is a major-premise whnf pre-pass in \
             iota_reduct, matching the real kernel. DerivedProved, zero axiom_deps — the \
             refutation is constructive.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The projections must peel exactly ONE application layer. If `cx_app_fn`
    /// were `kapp_fn` (which peels the whole spine to the head) then `cx_prefix`
    /// would be `const Nat.rec` and `app cx_prefix cx_major` would not convert
    /// back to the witness — the refutation would silently target a different
    /// term.
    #[test]
    fn test_app_arm_returns_one_layer_not_the_head() {
        let f = Specification::spine_arms("f");
        let a = Specification::spine_arms("a");
        assert!(
            f.contains("(_cf : KExpr) (_ca : KExpr) => f)"),
            "cx_app_fn's app arm must return the function half itself, not recurse"
        );
        assert!(
            a.contains("(_cf : KExpr) (_ca : KExpr) => a)"),
            "cx_app_arg's app arm must return the argument half"
        );
        assert!(
            !f.contains("kapp_fn") && !a.contains("kapp_fn"),
            "these are one-layer projections, NOT kapp_fn"
        );
    }

    /// Nine arms, one per `KExpr` constructor. A missing arm would not
    /// typecheck, but a DUPLICATED constructor shape (pi written where lam
    /// belongs) would — and would silently rebuild the wrong term.
    #[test]
    fn test_nine_arms_rebuild_their_own_constructor() {
        let arms = Specification::spine_arms("f");
        for ctor in [
            "KExpr.sort",
            "KExpr.bvar",
            "KExpr.lam",
            "KExpr.pi",
            "KExpr.const",
            "KExpr.let_",
            "KExpr.proj",
            "KExpr.lit",
        ] {
            assert_eq!(
                arms.matches(ctor).count(),
                1,
                "{ctor} must be rebuilt exactly once"
            );
        }
        // The app arm is the only one that does NOT rebuild its constructor.
        assert!(
            !arms.contains("KExpr.app"),
            "the app arm projects instead of rebuilding"
        );
        assert_eq!(arms.matches("(fun ").count(), 9, "nine constructors");
    }
}
