// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **PROBE — all four `CandModel.redRec*` laws at the type-blind candidate,
//! inert head.**
//!
//! `designs/2026-09-18-is-candmodel-uninhabited.md` §3g predicts that every
//! `redRec*` law holds at `Red T e := whnf_acc e` by a spine induction needing
//! nothing type-aware. This is the decisive test of that prediction, because it
//! is the one place the principle could fail without `pi_elim` being involved.
//!
//! ```text
//! whnf_acc m -> WhnfAccAll ms -> whnf_acc t
//!   -> whnf_acc (genRecApp fam sig u m ms t)
//! ```
//!
//! # It is STRONGER than the field, and weaker in one named way
//!
//! Stronger: the field supplies `Red T contractum` and this does not use it.
//! With an inert head ι never fires, so the contractum is irrelevant to whether
//! the spine normalizes. The type-blind reading of `redRecGen` therefore holds
//! with one hypothesis to spare.
//!
//! Weaker: it assumes the recursor head is INERT — no δ-body and no recursor
//! rule in the fixed `the_red_env`. That is exactly the assumption certificate
//! §2a records the field as NOT making: R4's `r4_genRecHead_delta_live` shows a
//! family the field accepts can have a recursor constant that is δ-live in the
//! real env, and `r4_genFresh_empty` shows `GenFresh` constrains that env not at
//! all. So this probe answers the spine question and leaves R4's quantifier
//! question exactly where R4 left it.
//!
//! # Why it is four lines and not a session
//!
//! Every piece already existed, and the pricing of this item moved three times
//! today before anyone read them:
//!
//! * `whnfAcc_inertSpine` (`mutual_schema.rs`) — arbitrary-length inert-headed
//!   spine, BY `ListType` INDUCTION over the argument list. This is the
//!   variable-arity induction that `wRecApp_step_inv` never needed and that the
//!   third estimate said would have to be built.
//! * `whnfAccAll_append` (`schema.rs`) — assembles `WhnfAccAll` across the
//!   `ms ++ [t]` join.
//! * `whnfAcc_const` (`acc_wtype.rs`) — the head itself is SN, from the same
//!   δ-freshness hypothesis.
//!
//! The head-name side condition is `Eq.refl`: `genRecC` is a bare `const`, and a
//! bare const is its own spine head.

use crate::spec::Specification;

impl Specification {
    /// The probe. An assembly of four existing facts, not an induction.
    #[cfg(test)]
    pub(super) fn redrecgen_blind_inert_src() -> String {
        let tail = "(ListType.cons KExpr t (ListType.nil KExpr))";
        let args = format!("(ListType.cons KExpr m (list_append ms {tail}))");
        format!(
            "def redrecgen_blind_inert (fam : Name) (sig : ListType Nat) (u : Level) \
             (hdef : Eq (OptionType KExpr) \
             (defval_for (red_def the_red_env) (genRecName fam sig)) (OptionType.none KExpr)) \
             (hrec : Eq (OptionType RecMeta) \
             (recmeta_for (red_rec the_red_env) (genRecName fam sig)) (OptionType.none RecMeta)) \
             (m : KExpr) (ms : ListType KExpr) (t : KExpr) \
             (hm : whnf_acc m) (hms : WhnfAccAll ms) (ht : whnf_acc t) : \
             whnf_acc (genRecApp fam sig u m ms t) := \
             whnfAcc_inertSpine (genRecName fam sig) hdef hrec {args} \
             (WhnfAccAll.cons m (list_append ms {tail}) hm \
             (whnfAccAll_append ms {tail} hms \
             (WhnfAccAll.cons t (ListType.nil KExpr) ht WhnfAccAll.nil))) \
             (genRecC fam sig u) \
             (Eq.refl (OptionType Name) (OptionType.some Name (genRecName fam sig))) \
             (whnfAcc_const (genRecName fam sig) \
             (ListType.cons Level u (ListType.nil Level)) hdef)"
        )
    }

    /// `redRecW` at the same candidate and the same inert assumption.
    ///
    /// `wRecApp u m mn t` is written as a FIXED three-argument nesting rather
    /// than through `apply_spine`, but the two are definitionally equal —
    /// `apply_spine (cons x rest) h` reduces to `apply_spine rest (app h x)`,
    /// so `apply_spine [m, mn, t] h` IS `app (app (app h m) mn) t`. That is why
    /// the same assembly reaches it with no spine lemma of its own.
    #[cfg(test)]
    pub(super) fn redrecw_blind_inert_src() -> String {
        "def redrecw_blind_inert (u : Level) \
         (hdef : Eq (OptionType KExpr) \
         (defval_for (red_def the_red_env) wRecName) (OptionType.none KExpr)) \
         (hrec : Eq (OptionType RecMeta) \
         (recmeta_for (red_rec the_red_env) wRecName) (OptionType.none RecMeta)) \
         (m : KExpr) (mn : KExpr) (t : KExpr) \
         (hm : whnf_acc m) (hmn : whnf_acc mn) (ht : whnf_acc t) : \
         whnf_acc (wRecApp u m mn t) := \
         whnfAcc_inertSpine wRecName hdef hrec \
         (ListType.cons KExpr m (ListType.cons KExpr mn \
         (ListType.cons KExpr t (ListType.nil KExpr)))) \
         (WhnfAccAll.cons m (ListType.cons KExpr mn \
         (ListType.cons KExpr t (ListType.nil KExpr))) hm \
         (WhnfAccAll.cons mn (ListType.cons KExpr t (ListType.nil KExpr)) hmn \
         (WhnfAccAll.cons t (ListType.nil KExpr) ht WhnfAccAll.nil))) \
         (wRecC u) \
         (Eq.refl (OptionType Name) (OptionType.some Name wRecName)) \
         (whnfAcc_const wRecName (ListType.cons Level u (ListType.nil Level)) hdef)"
            .to_string()
    }

    /// `redRecMut` — the mutual block. Two `whnfAccAll_append` joins rather than
    /// one, `mutRecApp` being `apply_spine (cs ++ (ms ++ [t]))`.
    #[cfg(test)]
    pub(super) fn redrecmut_blind_inert_src() -> String {
        let tail = "(ListType.cons KExpr t (ListType.nil KExpr))";
        let inner = format!("(list_append ms {tail})");
        format!(
            "def redrecmut_blind_inert (msig : ListType FamSpec) (u : Level) (i : Nat) \
             (hdef : Eq (OptionType KExpr) \
             (defval_for (red_def the_red_env) (mutRecName msig i)) (OptionType.none KExpr)) \
             (hrec : Eq (OptionType RecMeta) \
             (recmeta_for (red_rec the_red_env) (mutRecName msig i)) (OptionType.none RecMeta)) \
             (cs : ListType KExpr) (ms : ListType KExpr) (t : KExpr) \
             (hcs : WhnfAccAll cs) (hms : WhnfAccAll ms) (ht : whnf_acc t) : \
             whnf_acc (mutRecApp msig u i cs ms t) := \
             whnfAcc_inertSpine (mutRecName msig i) hdef hrec \
             (list_append cs {inner}) \
             (whnfAccAll_append cs {inner} hcs \
             (whnfAccAll_append ms {tail} hms \
             (WhnfAccAll.cons t (ListType.nil KExpr) ht WhnfAccAll.nil))) \
             (mutRecC msig u i) \
             (Eq.refl (OptionType Name) (OptionType.some Name (mutRecName msig i))) \
             (whnfAcc_const (mutRecName msig i) \
             (ListType.cons Level u (ListType.nil Level)) hdef)"
        )
    }

    /// `redRecIdx` — the indexed family. Three joins: `m :: (ms ++ (ix ++ [t]))`.
    #[cfg(test)]
    pub(super) fn redrecidx_blind_inert_src() -> String {
        let tail = "(ListType.cons KExpr t (ListType.nil KExpr))";
        let ixt = format!("(list_append ix {tail})");
        let inner = format!("(list_append ms {ixt})");
        format!(
            "def redrecidx_blind_inert (fam : Name) (isig : ListType ICtor) (u : Level) \
             (hdef : Eq (OptionType KExpr) \
             (defval_for (red_def the_red_env) (iRecName fam isig)) (OptionType.none KExpr)) \
             (hrec : Eq (OptionType RecMeta) \
             (recmeta_for (red_rec the_red_env) (iRecName fam isig)) (OptionType.none RecMeta)) \
             (m : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (t : KExpr) \
             (hm : whnf_acc m) (hms : WhnfAccAll ms) (hix : WhnfAccAll ix) (ht : whnf_acc t) : \
             whnf_acc (iRecApp fam isig u m ms ix t) := \
             whnfAcc_inertSpine (iRecName fam isig) hdef hrec \
             (ListType.cons KExpr m {inner}) \
             (WhnfAccAll.cons m {inner} hm \
             (whnfAccAll_append ms {ixt} hms \
             (whnfAccAll_append ix {tail} hix \
             (WhnfAccAll.cons t (ListType.nil KExpr) ht WhnfAccAll.nil)))) \
             (iRecC fam isig u) \
             (Eq.refl (OptionType Name) (OptionType.some Name (iRecName fam isig))) \
             (whnfAcc_const (iRecName fam isig) \
             (ListType.cons Level u (ListType.nil Level)) hdef)"
        )
    }

    #[cfg(test)]
    pub(super) fn redrecgen_probe_sources() -> Vec<(String, String)> {
        vec![
            (
                "redrecgen_blind_inert".to_string(),
                Self::redrecgen_blind_inert_src(),
            ),
            (
                "redrecw_blind_inert".to_string(),
                Self::redrecw_blind_inert_src(),
            ),
            (
                "redrecmut_blind_inert".to_string(),
                Self::redrecmut_blind_inert_src(),
            ),
            (
                "redrecidx_blind_inert".to_string(),
                Self::redrecidx_blind_inert_src(),
            ),
        ]
    }
}

#[cfg(test)]
#[path = "redrecgen_probe_tests.rs"]
mod tests;
