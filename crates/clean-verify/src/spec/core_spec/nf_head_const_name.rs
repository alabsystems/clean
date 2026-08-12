// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Head **constant-name** preservation under reduction.
//!
//! The companion to `nf_head_star_preserves_tag` (`nf_head.rs`), and the piece
//! the def-eq completeness residual needs: it is head *names*, not head *tags*,
//! that the confluence argument compares.
//!
//! ## Why this is not a retype of the tag lemma
//!
//! `nf_head_star_preserves_tag` has exactly the right arm structure and is
//! already proved, so the const-name version looks like a mechanical
//! `Nat`→`OptionType Name`, `kexpr_tag`→`fun z => kexpr_const_name (kapp_fn z)`
//! substitution. Four of the five arms do survive it. The **neutral-app arm
//! does not**, and the reason is a genuine difference in what the two functions
//! see:
//!
//! | | tag lemma | const-name lemma |
//! |---|---|---|
//! | goal after inversion | `kexpr_tag (app f2 a2) = kexpr_tag (app nf na2)` | `CN f2 = CN nf` |
//! | why | both sides are the `app` tag whatever `f2` is — **trivial** | `CN (app f a)` reduces to `CN f`: a real claim about the reduced head |
//!
//! `kexpr_tag` inspects only the top constructor; `kexpr_const_name ∘ kapp_fn`
//! looks all the way down the spine. And `nf_head`'s neutral constructor
//! carries `iota_neutral nf`, **not** `nf_head nf`, so `nf_head.rec` offers no
//! induction hypothesis there. Hence the separate spine induction below, to
//! which that arm delegates.
//!
//! ## Why this route does not re-open the residual
//!
//! `iota_neutral`'s own `app` constructor already carries
//! `iota_immune (KExpr.app f a)`, and `par_reduces_cd_star_neutral_app_inv_eq`
//! hands the corresponding fact back for the reduct — so the recursion sustains
//! itself with nothing threaded in. That is exactly the condition
//! `whnf_stuck_head`'s `projw` arm lacks, which is why *its* preservation is
//! false (see `stuck_app_rigidity.rs`) and this one is not.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_IOTA_NEUTRAL_CN: &str = "def iota_neutral_star_preserves_const_name (e : KExpr) (hn : iota_neutral e) : forall (w : KExpr), par_reduces_cd_star the_red_env e w -> Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (kexpr_const_name (kapp_fn w)) := iota_neutral.rec (fun (x : KExpr) (_h : iota_neutral x) => forall (w : KExpr), par_reduces_cd_star the_red_env x w -> Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (kexpr_const_name (kapp_fn w))) (fun (n : Name) (us : ListType Level) (_hcw : const_whnf n us) (hdd : Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const n us)) (OptionType.none KExpr)) (w : KExpr) (hs : par_reduces_cd_star the_red_env (KExpr.const n us) w) => Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn w)) (kexpr_const_name (kapp_fn (KExpr.const n us))) (Eq.cong KExpr (OptionType Name) (fun (z : KExpr) => kexpr_const_name (kapp_fn z)) w (KExpr.const n us) (par_reduces_cd_star_const_dead_inv_eq n us w hdd hs))) (fun (f : KExpr) (a : KExpr) (hin : iota_neutral f) (hii : iota_immune (KExpr.app f a)) (ih : forall (w : KExpr), par_reduces_cd_star the_red_env f w -> Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn w))) (w : KExpr) (hs : par_reduces_cd_star the_red_env (KExpr.app f a) w) => LiftP.rec (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (kexpr_const_name (kapp_fn w))) (fun (_l : LiftP (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (kexpr_const_name (kapp_fn w)))) => Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (kexpr_const_name (kapp_fn w))) (fun (p : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (kexpr_const_name (kapp_fn w))) => p) (par_reduces_cd_star_neutral_app_inv_eq f a w (LiftP (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (kexpr_const_name (kapp_fn w)))) hin hii hs (fun (f2 : KExpr) (a2 : KExpr) (heq : Eq KExpr w (KExpr.app f2 a2)) (r1 : par_reduces_cd_star the_red_env f f2) (_r2 : par_reduces_cd_star the_red_env a a2) (_hin2 : iota_neutral f2) (_hii2 : iota_immune (KExpr.app f2 a2)) => LiftP.up (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (kexpr_const_name (kapp_fn w))) (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (kexpr_const_name (kapp_fn f2)) (kexpr_const_name (kapp_fn w)) (ih f2 r1) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn w)) (kexpr_const_name (kapp_fn f2)) (Eq.cong KExpr (OptionType Name) (fun (z : KExpr) => kexpr_const_name (kapp_fn z)) w (KExpr.app f2 a2) heq)))))) e hn";

const SRC_NF_HEAD_CN: &str = "def nf_head_star_preserves_const_name (e : KExpr) (hn : nf_head e) : forall (w : KExpr), par_reduces_cd_star the_red_env e w -> Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (kexpr_const_name (kapp_fn w)) := nf_head.rec (fun (x : KExpr) (_h : nf_head x) => forall (w : KExpr), par_reduces_cd_star the_red_env x w -> Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (kexpr_const_name (kapp_fn w))) (fun (lty : KExpr) (lbody : KExpr) (w : KExpr) (hs : par_reduces_cd_star the_red_env (KExpr.lam lty lbody) w) => LiftP.rec (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam lty lbody))) (kexpr_const_name (kapp_fn w))) (fun (_l : LiftP (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam lty lbody))) (kexpr_const_name (kapp_fn w)))) => Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam lty lbody))) (kexpr_const_name (kapp_fn w))) (fun (p : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam lty lbody))) (kexpr_const_name (kapp_fn w))) => p) (par_reduces_cd_star_lam_inv_eq the_red_env lty lbody w (LiftP (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam lty lbody))) (kexpr_const_name (kapp_fn w)))) hs (fun (ty2 : KExpr) (body2 : KExpr) (heq : Eq KExpr w (KExpr.lam ty2 body2)) (_h1 : par_reduces_cd_star the_red_env lty ty2) (_h2 : par_reduces_cd_star the_red_env lbody body2) => LiftP.up (Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam lty lbody))) (kexpr_const_name (kapp_fn w))) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn w)) (kexpr_const_name (kapp_fn (KExpr.lam ty2 body2))) (Eq.cong KExpr (OptionType Name) (fun (z : KExpr) => kexpr_const_name (kapp_fn z)) w (KExpr.lam ty2 body2) heq))))) (fun (e0 : KExpr) (hr : rigid_app_head e0) (w : KExpr) (hs : par_reduces_cd_star the_red_env e0 w) => Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.none Name) (kexpr_const_name (kapp_fn w)) (rigid_app_head_no_const e0 hr) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn w)) (OptionType.none Name) (rigid_app_head_no_const w (rigid_app_head_star_preserved the_red_env e0 w hs hr)))) (fun (nf : KExpr) (na2 : KExpr) (hin : iota_neutral nf) (hii : iota_immune (KExpr.app nf na2)) (w : KExpr) (hs : par_reduces_cd_star the_red_env (KExpr.app nf na2) w) => iota_neutral_star_preserves_const_name (KExpr.app nf na2) (iota_neutral.app nf na2 hin hii) w hs) (fun (cn : Name) (cus : ListType Level) (hdd : Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const cn cus)) (OptionType.none KExpr)) (w : KExpr) (hs : par_reduces_cd_star the_red_env (KExpr.const cn cus) w) => Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn w)) (kexpr_const_name (kapp_fn (KExpr.const cn cus))) (Eq.cong KExpr (OptionType Name) (fun (z : KExpr) => kexpr_const_name (kapp_fn z)) w (KExpr.const cn cus) (par_reduces_cd_star_const_dead_inv_eq cn cus w hdd hs))) (fun (bi : Nat) (w : KExpr) (hs : par_reduces_cd_star the_red_env (KExpr.bvar bi) w) => Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn w)) (kexpr_const_name (kapp_fn (KExpr.bvar bi))) (Eq.cong KExpr (OptionType Name) (fun (z : KExpr) => kexpr_const_name (kapp_fn z)) w (KExpr.bvar bi) (par_reduces_cd_star_bvar_inv_eq the_red_env bi w hs))) e hn";

impl Specification {
    /// Head constant-name preservation: the spine induction, then all of `nf_head`.
    pub(super) fn add_nf_head_const_name(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IOTA_NEUTRAL_CN, "iota_neutral_star_preserves_const_name: reduction out of an iota-neutral spine preserves the SPINE HEAD's constant name. Two arms. The const arm is delta-dead and closes by the equation-form dead-const inversion. The app arm recurses through par_reduces_cd_star_neutral_app_inv_eq, which is exactly the inversion that rules out beta (iota_neutral has no lam arm), delta (the head is delta-dead) and iota. \
\
No side condition has to be threaded: iota_neutral's OWN app constructor already carries iota_immune (KExpr.app f a), and the inversion hands the corresponding fact back for the reduct, so the recursion sustains itself. That is the contrast with the whnf_stuck_head route, whose projw arm has no such condition and whose preservation is therefore FALSE. \
\
NOTE the recursor's binder order: all constructor fields come first and the induction hypothesis LAST, so the app arm binds (f) (a) (hin) (hii) (ih). rigid_app_head's app constructor has no field after its recursive one, so that predicate does not expose the distinction; copying its arm shape here is a type error. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_NF_HEAD_CN, "nf_head_star_preserves_const_name: reduction out of a normal-form-headed term preserves the spine head's CONSTANT NAME, for every nf_head shape. The const-name companion to nf_head_star_preserves_tag. \
\
*** THIS IS NOT A RETYPE OF THE TAG LEMMA. *** kexpr_tag inspects only the TOP constructor, so the tag lemma's neutral-app arm is trivial -- kexpr_tag (app f2 a2) is the app tag whatever f2 is. kexpr_const_name after kapp_fn looks DEEP into the spine, where kapp_fn (app f a) reduces to kapp_fn f, so the same arm becomes a real claim that the reduced head keeps its name. And nf_head's neutral constructor carries iota_neutral nf, NOT nf_head nf, so nf_head.rec supplies no induction hypothesis there. \
\
The arm therefore DELEGATES to iota_neutral_star_preserves_const_name, rebuilding iota_neutral.app from the two hypotheses it already binds. The other four arms do survive the substitution: lam through the binder inversion (LiftP-wrapped, since that inversion takes its answer type as Type while the goal is a Prop-valued Eq), rigid by rigid_app_head_no_const on both ends of rigid_app_head_star_preserved, and the delta-dead const and bvar arms through their equation-form inversions, which need no wrap. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The neutral arm must DELEGATE to the spine induction. Closing it with a
    /// bare `Eq.cong` on the inversion's equation is the tag-lemma move, and it
    /// is wrong here: that would prove `CN w = CN (app f2 a2)` and then silently
    /// need `CN f2 = CN nf`, which is the whole content.
    #[test]
    fn test_neutral_arm_delegates_to_the_spine_induction() {
        assert!(
            SRC_NF_HEAD_CN.contains("iota_neutral_star_preserves_const_name"),
            "the neutral arm must delegate; kexpr_const_name looks deep into the spine"
        );
        assert!(
            SRC_NF_HEAD_CN.contains("iota_neutral.app nf na2 hin hii"),
            "it delegates by rebuilding iota_neutral.app from the hypotheses already bound"
        );
    }

    /// Recursor binder order: constructor fields first, induction hypothesis
    /// LAST. `iota_neutral.app` has `iota_immune` AFTER its recursive premise,
    /// so `(hin) (hii) (ih)` is forced. `rigid_app_head` has no field after its
    /// recursive one and so does not expose the distinction — copying its arm
    /// shape here is a type error, and was one.
    #[test]
    fn test_spine_app_arm_binds_the_ih_last() {
        let hin = SRC_IOTA_NEUTRAL_CN
            .find("(hin : iota_neutral f)")
            .expect("app arm binds its recursive premise");
        let hii = SRC_IOTA_NEUTRAL_CN
            .find("(hii : iota_immune (KExpr.app f a))")
            .expect("app arm binds iota_immune");
        let ih = SRC_IOTA_NEUTRAL_CN
            .find("(ih : forall (w : KExpr)")
            .expect("app arm binds an induction hypothesis");
        assert!(
            hin < hii && hii < ih,
            "order must be (hin) (hii) (ih), got {hin}/{hii}/{ih}"
        );
    }

    /// Both lemmas must go through `kapp_fn` — the DEEP head. A term mentioning
    /// `kexpr_tag` would be the shallow tag lemma wearing this one's name.
    #[test]
    fn test_both_use_the_deep_head_not_the_tag() {
        for src in [SRC_IOTA_NEUTRAL_CN, SRC_NF_HEAD_CN] {
            assert!(
                src.contains("kexpr_const_name (kapp_fn"),
                "must use the deep spine head"
            );
            assert!(
                !src.contains("kexpr_tag"),
                "the tag is the shallow invariant, not this one"
            );
        }
    }

    /// The spine induction must actually invert, on both arms.
    #[test]
    fn test_spine_arms_each_apply_an_inversion() {
        for inv in [
            "par_reduces_cd_star_const_dead_inv_eq",
            "par_reduces_cd_star_neutral_app_inv_eq",
        ] {
            assert!(SRC_IOTA_NEUTRAL_CN.contains(inv), "no arm applies {inv}");
        }
    }

    #[test]
    fn test_sources_balanced_ascii_and_prime_free() {
        for src in [SRC_IOTA_NEUTRAL_CN, SRC_NF_HEAD_CN] {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open");
            }
            assert_eq!(depth, 0, "unbalanced parens");
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert!(
                !src.contains('\''),
                "a prime silently lexes as a new identifier"
            );
        }
    }
}
