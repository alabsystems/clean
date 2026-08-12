// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inverting an application leg from an `nf_head` witness alone.
//!
//! ```text
//! nf_app_leg_inv :
//!   nf_head e -> Eq KExpr e (app f a) -> par_reduces_cd_star the_red_env e w
//!     -> StuckAppRedWitness the_red_env f a w
//! ```
//!
//! ## Why the dispatch needs this
//!
//! `def_eq_round_app` takes two `StuckAppRedWitness`es, deliberately, so it never
//! learns whether each side was rigid- or neutral-headed. But *somebody* has to
//! choose the inverter, and at the dispatch the only evidence in hand is
//! `nf_head`.
//!
//! Doing that choice inline would mean an inner case analysis **per side** —
//! and since `nf_head` has eight leaves, that is sixty-four combinations in the
//! dispatch's application case. Hoisting it here makes it eight, once, and the
//! dispatch's application leaf becomes two calls.
//!
//! This is the same collapse as the head grid and the `app` round: case-split at
//! the point where the alternatives converge, not after.
//!
//! ## Six of the eight leaves are impossible
//!
//! Only `rigid/app` and `neutral` can be applications. The other six — `lam`,
//! `rigid/sort`, `rigid/pi`, `rigid/lit`, `rigid/proj`, `constdead` — contradict
//! the `Eq KExpr e (app f a)` hypothesis and die by generic discrimination,
//! which is arithmetic because `kexpr_tag` computes.
//!
//! `DerivedProved`, empty axiom closure.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Choose an application leg-inverter from an `nf_head` witness.
    pub(super) fn add_nf_app_leg(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::nf_app_leg_src(),
            "nf_app_leg_inv: invert an application leg given only an nf_head witness, choosing \
             the rigid or neutral inverter internally. \
             \
             def_eq_round_app takes two StuckAppRedWitnesses so that it never learns which side \
             was which, but somebody must make that choice, and at the dispatch the only evidence \
             in hand is nf_head. Doing it inline would mean an inner case analysis PER SIDE — and \
             nf_head has eight leaves, so sixty-four combinations in the application case. \
             Hoisting it here makes it eight, once, and the dispatch's application leaf becomes \
             two calls. Same collapse as the head grid: split where the alternatives converge, \
             not after. \
             \
             Six of the eight leaves are impossible — only rigid/app and neutral can be \
             applications — and they die by generic discrimination, which is arithmetic because \
             kexpr_tag computes. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn nf_app_leg_src() -> String {
        let goal = "StuckAppRedWitness the_red_env f a w";
        let motive = |z: &str| {
            format!(
                "forall (f : KExpr) (a : KExpr), Eq KExpr {z} (KExpr.app f a) -> \
                 par_reduces_cd_star the_red_env {z} w -> {goal}"
            )
        };
        // An impossible leaf: the term is not an application.
        let kill = |form: &str| {
            format!(
                "(fun (f : KExpr) (a : KExpr) (heq : Eq KExpr {form} (KExpr.app f a)) \
                 (_hs : par_reduces_cd_star the_red_env {form} w) => \
                 kexpr_discr_t ({goal}) {form} (KExpr.app f a) heq (Eq.refl Bool Bool.false))"
            )
        };
        // Transport a fact about the leaf's own form onto `app f a`.
        let onto = |ty: &str, form: &str, val: &str| {
            format!(
                "(Eq.substType KExpr (fun (z : KExpr) => {ty}) {form} (KExpr.app f a) heq {val})"
            )
        };

        // rigid_app_head declaration order: sort, pi, lit, app, proj, bvar.
        let rigid_app_form = "(KExpr.app raf raa)";
        let rigid_arms = format!(
            "{sort} {pi} {lit} \
             (fun (raf : KExpr) (raa : KExpr) (hraf : rigid_app_head raf) \
             (_ihr : {ih}) (f : KExpr) (a : KExpr) \
             (heq : Eq KExpr {rigid_app_form} (KExpr.app f a)) \
             (hs : par_reduces_cd_star the_red_env {rigid_app_form} w) => \
             rigid_app_leg_inv f a w \
             {rig} \
             {leg}) \
             {proj} {bvar}",
            sort = kill("(KExpr.sort rn)"),
            pi = kill("(KExpr.pi rpty rpbody)"),
            lit = kill("(KExpr.lit rv)"),
            proj = kill("(KExpr.proj rs ri rsub)"),
            bvar = kill("(KExpr.bvar rbi)"),
            ih = motive("raf"),
            rig = onto(
                "rigid_app_head z",
                rigid_app_form,
                "(rigid_app_head.app raf raa hraf)"
            ),
            leg = onto("par_reduces_cd_star the_red_env z w", rigid_app_form, "hs"),
        );
        // The rigid arms need their payload binders; kill() supplies them via
        // the forms, but the recursor binds them, so prefix each.
        let rigid_arms = rigid_arms
            .replacen("(fun (f : KExpr)", "(fun (rn : Level) (f : KExpr)", 1)
            .replacen(
                "(fun (f : KExpr) (a : KExpr) (heq : Eq KExpr (KExpr.pi rpty rpbody)",
                "(fun (rpty : KExpr) (rpbody : KExpr) (f : KExpr) (a : KExpr) \
                 (heq : Eq KExpr (KExpr.pi rpty rpbody)",
                1,
            )
            .replacen(
                "(fun (f : KExpr) (a : KExpr) (heq : Eq KExpr (KExpr.lit rv)",
                "(fun (rv : Nat) (f : KExpr) (a : KExpr) (heq : Eq KExpr (KExpr.lit rv)",
                1,
            )
            .replacen(
                "(fun (f : KExpr) (a : KExpr) (heq : Eq KExpr (KExpr.proj rs ri rsub)",
                "(fun (rs : Name) (ri : Nat) (rsub : KExpr) (f : KExpr) (a : KExpr) \
                 (heq : Eq KExpr (KExpr.proj rs ri rsub)",
                1,
            )
            .replacen(
                "(fun (f : KExpr) (a : KExpr) (heq : Eq KExpr (KExpr.bvar rbi)",
                "(fun (rbi : Nat) (f : KExpr) (a : KExpr) (heq : Eq KExpr (KExpr.bvar rbi)",
                1,
            );

        let neutral_form = "(KExpr.app nfh nag)";
        format!(
            "def nf_app_leg_inv (w : KExpr) (e : KExpr) (hn : nf_head e) : {m} := \
             nf_head.rec (fun (z : KExpr) (_h : nf_head z) => {mz}) \
             (fun (qty : KExpr) (qbody : KExpr) (f : KExpr) (a : KExpr) \
             (heq : Eq KExpr (KExpr.lam qty qbody) (KExpr.app f a)) \
             (_hs : par_reduces_cd_star the_red_env (KExpr.lam qty qbody) w) => \
             kexpr_discr_t ({goal}) (KExpr.lam qty qbody) (KExpr.app f a) heq \
             (Eq.refl Bool Bool.false)) \
             (fun (e0 : KExpr) (hr : rigid_app_head e0) => \
             rigid_app_head.rec (fun (z : KExpr) (_h : rigid_app_head z) => {mz}) \
             {rigid_arms} e0 hr) \
             (fun (nfh : KExpr) (nag : KExpr) (hin : iota_neutral nfh) \
             (hii : iota_immune {neutral_form}) (f : KExpr) (a : KExpr) \
             (heq : Eq KExpr {neutral_form} (KExpr.app f a)) \
             (hs : par_reduces_cd_star the_red_env {neutral_form} w) => \
             neutral_app_leg_inv f a w \
             (Eq.substType KExpr (fun (z : KExpr) => iota_neutral z) nfh f \
             (app_inj_fst nfh nag f a heq) hin) \
             {nimm} \
             {nleg}) \
             (fun (cn : Name) (cus : ListType Level) \
             (_hdd : Eq (OptionType KExpr) \
             (delta_reduct (red_def the_red_env) (KExpr.const cn cus)) (OptionType.none KExpr)) \
             (f : KExpr) (a : KExpr) \
             (heq : Eq KExpr (KExpr.const cn cus) (KExpr.app f a)) \
             (_hs : par_reduces_cd_star the_red_env (KExpr.const cn cus) w) => \
             kexpr_discr_t ({goal}) (KExpr.const cn cus) (KExpr.app f a) heq \
             (Eq.refl Bool Bool.false)) \
             (fun (bi : Nat) (f : KExpr) (a : KExpr) \
             (heq : Eq KExpr (KExpr.bvar bi) (KExpr.app f a)) \
             (_hs : par_reduces_cd_star the_red_env (KExpr.bvar bi) w) => \
             kexpr_discr_t ({goal}) (KExpr.bvar bi) (KExpr.app f a) heq \
             (Eq.refl Bool Bool.false)) \
             e hn",
            m = motive("e"),
            mz = motive("z"),
            nimm = onto("iota_immune z", neutral_form, "hii"),
            nleg = onto("par_reduces_cd_star the_red_env z w", neutral_form, "hs"),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `nf_head` has FIVE constructors, so `nf_head.rec` takes a motive plus
    /// five minor premises — six top-level lambdas. The `rigid` arm then fans out
    /// to `rigid_app_head`'s five, giving nine leaves in total.
    ///
    /// (The first version of this test forgot the MOTIVE is also a top-level
    /// lambda and expected four. Counting recursor arguments means counting the
    /// motive too.)
    #[test]
    fn test_four_arms_plus_motive_and_one_fanout() {
        let src = Specification::nf_app_leg_src();
        let chars: Vec<char> = src.chars().collect();
        let mut depth: i64 = 0;
        let mut top = 0usize;
        for (idx, ch) in chars.iter().enumerate() {
            match ch {
                '(' => {
                    if depth == 0 && src[idx..].starts_with("(fun ") {
                        top += 1;
                    }
                    depth += 1;
                }
                ')' => depth -= 1,
                _ => {}
            }
        }
        assert_eq!(
            top, 6,
            "nf_head.rec takes a motive plus five minor premises; found {top} top-level lambdas"
        );
        assert_eq!(
            src.matches("rigid_app_head.rec").count(),
            1,
            "the rigid arm fans out via its own recursor, giving nine leaves in total"
        );
    }

    /// Exactly two leaves can be applications; the other seven are impossible
    /// and must be discriminated. If a substantive leaf were ever discriminated
    /// away, the lemma would still typecheck and quietly cover less.
    #[test]
    fn test_seven_leaves_are_impossible_and_two_are_real() {
        let src = Specification::nf_app_leg_src();
        assert_eq!(
            src.matches("kexpr_discr_t (StuckAppRedWitness").count(),
            8,
            "lam, rigid/sort, rigid/pi, rigid/lit, rigid/proj, rigid/bvar, constdead and bvar \
             cannot be applications"
        );
        assert_eq!(
            src.matches("rigid_app_leg_inv f a w").count(),
            1,
            "the rigid application leaf must invert, not discriminate"
        );
        assert_eq!(
            src.matches("neutral_app_leg_inv f a w").count(),
            1,
            "the neutral leaf must invert, not discriminate"
        );
    }

    /// Both substantive leaves must transport their evidence AND their leg onto
    /// `app f a`. Forgetting the leg would apply the inverter to the wrong
    /// reduction.
    #[test]
    fn test_substantive_leaves_transport_evidence_and_leg() {
        let src = Specification::nf_app_leg_src();
        assert!(
            src.contains("(fun (z : KExpr) => rigid_app_head z)"),
            "the rigid leaf must transport its head evidence"
        );
        assert!(
            src.contains("(fun (z : KExpr) => iota_neutral z)")
                && src.contains("(fun (z : KExpr) => iota_immune z)"),
            "the neutral leaf must transport BOTH of its obligations"
        );
        assert_eq!(
            src.matches("(fun (z : KExpr) => par_reduces_cd_star the_red_env z w)")
                .count(),
            2,
            "each substantive leaf must transport its reduction leg"
        );
    }

    #[test]
    fn test_nf_app_leg_parens_balanced() {
        let src = Specification::nf_app_leg_src();
        let mut depth: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open");
        }
        assert_eq!(depth, 0);
    }
}
