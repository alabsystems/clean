// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Normal-form heads: `rigid_app_head` plus `lam`.
//!
//! ## Why `lam` needs its own arm rather than joining `rigid_app_head`
//!
//! A lambda in normal-form position is perfectly tag-stable — nothing reduces
//! `lam ty body` to a non-lambda. But it must **not** be admitted into
//! `rigid_app_head`, because that predicate's `app` arm relies on the head not
//! being a lambda: `app (lam A b) c` is a β-redex, so an application on a
//! lambda head is neither rigid nor a normal form. Adding a `lam` arm to
//! `rigid_app_head` would silently break `rigid_app_head_not_lam`, and with it
//! every ι/δ immunity argument downstream.
//!
//! So `nf_head` is the coarser predicate, with `lam` alongside a `rigid`
//! injection. It is what the completeness capstone case-splits on.
//!
//! ```text
//! nf_head_star_preserves_tag :
//!   nf_head e -> par_reduces_cd_star env e w -> Eq Nat (kexpr_tag e) (kexpr_tag w)
//! nf_join_same_tag :
//!   nf_head na -> nf_head nb -> … common reduct … -> Eq Nat (kexpr_tag na) (kexpr_tag nb)
//! ```
//!
//! The `lam` arm goes through `par_reduces_cd_star_lam_inv_eq`, whose answer
//! type is `C : Type` — so the `Eq` goal is wrapped in `LiftP`, exactly as the
//! `pi` arm of the rigid version had to be. Both binder inversions share that
//! shape; that is now a known fact about this family rather than a surprise.
//!
//! ## Coverage against `is_whnf`
//!
//! `is_whnf` (`whnf_reduction.rs:82-88`) has six arms. `nf_head` covers five of
//! them: `sort`, `lam`, `pi`, `proj` and `lit`, plus applications on rigid heads
//! (the `stuck` shape). The **one** shape it does not cover is `neutral` at a
//! `const` head, and that gap is real rather than an oversight: whether a
//! constant-headed term δ-unfolds depends on the environment, so its tag
//! stability needs δ-deadness — `consts_defined_red`. Recorded, not papered
//! over.
//!
//! `DerivedProved`, empty axiom closures; the predicate is census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// THE premise: every `whnf_fuel_red` result has a normal-form head.
///
/// **This premise is FALSE** — `hnf_is_false` (`hnf_refutation.rs`) refutes it in
/// the kernel, because the deployed kernel whnf-reduces a recursor's major premise
/// before the constructor-rule lookup (`micro/checker.rs:777`) and the reflected
/// `iota_reduct` does not (`iota_step.rs:127`). Everything spliced with it is
/// therefore vacuous, and must not be reported as a result.
///
/// It lives here, once, because it did not used to. This exact text was
/// copy-pasted **verbatim into four files** — `defeq_capstone.rs`,
/// `defeq_round_binder.rs`, `defeq_round_leaf.rs`, `defeq_round_rest.rs` — which is
/// how a single false premise became **nine** vacuous declarations before anyone
/// noticed. One definition means one place to correct, one place to delete, and
/// one grep to find every carrier. `test_hnf_premise_is_defined_only_here` keeps it
/// that way.
///
/// Its home is `nf_head.rs` because it is a statement *about* `nf_head`: when the
/// pre-pass gap is closed, this premise and `nf_head`'s `neutral` arm move
/// together.
pub(super) const HNF: &str = "(hnf : forall (m : Nat) (e : KExpr) (r : KExpr), \
     Eq (OptionType KExpr) (whnf_fuel_red the_red_env m e) (OptionType.some KExpr r) -> \
     nf_head r) ";

impl Specification {
    /// The normal-form head predicate and its tag stability.
    pub(super) fn add_nf_head(&mut self) -> Result<(), SpecError> {
        self.add_nf_head_type()?;
        self.add_nf_head_tag()?;
        Ok(())
    }

    fn add_nf_head_type(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive nf_head : KExpr -> Type\n\
             | lam : forall (lty : KExpr) (lbody : KExpr), nf_head (KExpr.lam lty lbody)\n\
             | rigid : forall (e : KExpr), rigid_app_head e -> nf_head e\n\
             | neutral : forall (f : KExpr) (a : KExpr), iota_neutral f -> \
             iota_immune (KExpr.app f a) -> nf_head (KExpr.app f a)\n\
             | constdead : forall (cn : Name) (cus : ListType Level), \
             Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const cn cus)) \
             (OptionType.none KExpr) -> nf_head (KExpr.const cn cus)\n\
             | bvar : forall (bi : Nat), nf_head (KExpr.bvar bi)",
            "nf_head e: e has a normal-form head — a lambda, or a rigid head (sort, pi, literal, \
             projection, or an application on one of those). Deliberately COARSER than \
             rigid_app_head and deliberately NOT the same predicate: rigid_app_head's app arm \
             depends on the head not being a lambda, since app (lam A b) c is a beta-redex, so \
             admitting lam there would silently break rigid_app_head_not_lam and every iota/delta \
             immunity argument built on it. Covers five of is_whnf's six arms; the one gap is a \
             const-headed neutral, whose tag stability genuinely needs delta-deadness. \
             Census-neutral.",
        )?;
        Ok(())
    }

    fn add_nf_head_tag(&mut self) -> Result<(), SpecError> {
        // Four arms. Two of the four binder-style inversions take their answer
        // type as `C : Type` while the goal is a Prop-valued `Eq`, so those go
        // through `LiftP`; the const arm's inversion is equation-form and needs
        // no wrap. That asymmetry is a property of the inversion family, now
        // recorded in three places rather than rediscovered.
        let lam_tag = "Eq Nat (kexpr_tag (KExpr.lam lty lbody)) (kexpr_tag w)";
        let neu_tag = "Eq Nat (kexpr_tag (KExpr.app nf na2)) (kexpr_tag w)";
        self.add_recursive_def(
            &format!(
                "def nf_head_star_preserves_tag (e : KExpr) (hn : nf_head e) : \
                 forall (w : KExpr), par_reduces_cd_star the_red_env e w -> \
                 Eq Nat (kexpr_tag e) (kexpr_tag w) := \
                 nf_head.rec \
                 (fun (x : KExpr) (_h : nf_head x) => \
                 forall (w : KExpr), par_reduces_cd_star the_red_env x w -> \
                 Eq Nat (kexpr_tag x) (kexpr_tag w)) \
                 (fun (lty : KExpr) (lbody : KExpr) (w : KExpr) \
                 (hs : par_reduces_cd_star the_red_env (KExpr.lam lty lbody) w) => \
                 LiftP.rec ({lam_tag}) \
                 (fun (_l : LiftP ({lam_tag})) => {lam_tag}) \
                 (fun (p : {lam_tag}) => p) \
                 (par_reduces_cd_star_lam_inv_eq the_red_env lty lbody w \
                 (LiftP ({lam_tag})) hs \
                 (fun (ty2 : KExpr) (body2 : KExpr) \
                 (heq : Eq KExpr w (KExpr.lam ty2 body2)) \
                 (_h1 : par_reduces_cd_star the_red_env lty ty2) \
                 (_h2 : par_reduces_cd_star the_red_env lbody body2) => \
                 LiftP.up ({lam_tag}) \
                 (Eq.symm Nat (kexpr_tag w) (kexpr_tag (KExpr.lam ty2 body2)) \
                 (Eq.cong KExpr Nat kexpr_tag w (KExpr.lam ty2 body2) heq))))) \
                 (fun (e0 : KExpr) (hr : rigid_app_head e0) (w : KExpr) \
                 (hs : par_reduces_cd_star the_red_env e0 w) => \
                 rigid_app_head_star_preserves_tag the_red_env e0 hr w hs) \
                 (fun (nf : KExpr) (na2 : KExpr) (hin : iota_neutral nf) \
                 (hii : iota_immune (KExpr.app nf na2)) (w : KExpr) \
                 (hs : par_reduces_cd_star the_red_env (KExpr.app nf na2) w) => \
                 LiftP.rec ({neu_tag}) \
                 (fun (_l : LiftP ({neu_tag})) => {neu_tag}) \
                 (fun (p : {neu_tag}) => p) \
                 (par_reduces_cd_star_neutral_app_inv_eq nf na2 w (LiftP ({neu_tag})) \
                 hin hii hs \
                 (fun (f2 : KExpr) (a2 : KExpr) \
                 (heq : Eq KExpr w (KExpr.app f2 a2)) \
                 (_r1 : par_reduces_cd_star the_red_env nf f2) \
                 (_r2 : par_reduces_cd_star the_red_env na2 a2) \
                 (_hin2 : iota_neutral f2) \
                 (_hii2 : iota_immune (KExpr.app f2 a2)) => \
                 LiftP.up ({neu_tag}) \
                 (Eq.symm Nat (kexpr_tag w) (kexpr_tag (KExpr.app f2 a2)) \
                 (Eq.cong KExpr Nat kexpr_tag w (KExpr.app f2 a2) heq))))) \
                 (fun (cn : Name) (cus : ListType Level) \
                 (hdd : Eq (OptionType KExpr) \
                 (delta_reduct (red_def the_red_env) (KExpr.const cn cus)) \
                 (OptionType.none KExpr)) (w : KExpr) \
                 (hs : par_reduces_cd_star the_red_env (KExpr.const cn cus) w) => \
                 Eq.symm Nat (kexpr_tag w) (kexpr_tag (KExpr.const cn cus)) \
                 (Eq.cong KExpr Nat kexpr_tag w (KExpr.const cn cus) \
                 (par_reduces_cd_star_const_dead_inv_eq cn cus w hdd hs))) \
                 (fun (bi : Nat) (w : KExpr) \
                 (hs : par_reduces_cd_star the_red_env (KExpr.bvar bi) w) => \
                 Eq.symm Nat (kexpr_tag w) (kexpr_tag (KExpr.bvar bi)) \
                 (Eq.cong KExpr Nat kexpr_tag w (KExpr.bvar bi) \
                 (par_reduces_cd_star_bvar_inv_eq the_red_env bi w hs))) \
                 e hn"
            ),
            "nf_head_star_preserves_tag: reduction out of a normal-form-headed term preserves the \
             head tag, for EVERY is_whnf shape. Five arms: lam via the binder inversion, rigid by \
             delegation, a const-headed neutral application via the neutral-app inversion, a \
             delta-dead bare constant via the dead-const inversion, and a bound variable via the \
             rigid bvar inversion. The lam and neutral arms wrap their Prop-valued goal in LiftP \
             because those inversions take C : Type; the const and bvar arms' inversions are \
             equation-form and need no wrap. \
             \
             The bvar arm is unconditional, and cheaply so: par_reduces_cd has NO arm mentioning \
             bvar, and both iota_step and delta_step need a const head, so only refl relates a \
             bound variable to anything. A bvar is as rigid as a normal form gets. \
             \
             The neutral arm's iota_neutral and iota_immune obligations are carried in the \
             PREDICATE, deliberately visible rather than absent: a const-headed spine can \
             iota-fire when its arguments become constructor-headed, so its tag stability is \
             genuinely conditional and no structural argument removes that. Making nf_head total \
             over is_whnf with those fields explicit is strictly better than a predicate that \
             silently omits the case. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def nf_join_same_tag (na : KExpr) (nb : KExpr) (w : KExpr) \
             (hna : nf_head na) (hnb : nf_head nb) \
             (hsa : par_reduces_cd_star the_red_env na w) \
             (hsb : par_reduces_cd_star the_red_env nb w) : \
             Eq Nat (kexpr_tag na) (kexpr_tag nb) := \
             Eq.trans Nat (kexpr_tag na) (kexpr_tag w) (kexpr_tag nb) \
             (nf_head_star_preserves_tag na hna w hsa) \
             (Eq.symm Nat (kexpr_tag nb) (kexpr_tag w) \
             (nf_head_star_preserves_tag nb hnb w hsb))",
            "nf_join_same_tag: two normal-form-headed terms with a COMMON REDUCT have the same \
             head tag, now across every is_whnf shape. One arithmetic equation in place of a grid \
             over head pairs, dispatched by nat_discr. Stated at the FIXED the_red_env with no \
             RedEnv parameter: iota_neutral, iota_immune and both const-side inversions are all \
             pinned there, so a parameter would advertise generality the statement does not have. \
             DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    /// `nf_head` must NOT be conflated with `rigid_app_head`. The whole reason
    /// it exists is that `lam` cannot join the rigid predicate: `rigid_app_head`'s
    /// `app` arm depends on the head not being a lambda (`app (lam A b) c` is a
    /// β-redex), so a `lam` arm there would break `rigid_app_head_not_lam` and
    /// every ι/δ immunity argument downstream.
    #[test]
    fn test_nf_head_keeps_lam_out_of_the_rigid_predicate() {
        let rigid = include_str!("rigid_app_head.rs");
        let decl_start = rigid
            .find("inductive rigid_app_head")
            .expect("rigid_app_head is declared");
        let decl = &rigid[decl_start..decl_start + 800];
        let decl = &decl[..decl.find("\",").unwrap_or(decl.len())];
        assert!(
            !decl.contains("| lam "),
            "rigid_app_head must have NO lam arm — its app arm and every immunity lemma depend on \
             the head not being a lambda. lam belongs in nf_head instead."
        );

        let nf = include_str!("nf_head.rs");
        let nf_decl_start = nf.find("inductive nf_head").expect("nf_head is declared");
        let nf_decl = &nf[nf_decl_start..nf_decl_start + 400];
        assert!(nf_decl.contains("| lam "), "nf_head must have a lam arm");
        assert!(
            nf_decl.contains("| rigid "),
            "nf_head must inject rigid_app_head rather than duplicate its arms"
        );
    }

    /// The `lam` arm needs the `LiftP` wrap for the same reason the rigid `pi`
    /// arm did: the binder inversions take `C : Type` and the goal is an `Eq`.
    #[test]
    fn test_lam_arm_wraps_in_liftp() {
        let src = include_str!("nf_head.rs");
        let term_start = src
            .find("def nf_head_star_preserves_tag")
            .expect("declaration present");
        let term = &src[term_start..src[term_start..].find("\",\n").unwrap() + term_start];
        assert!(
            term.contains("LiftP.rec") && term.contains("LiftP.up"),
            "the lam arm must wrap its Prop-valued goal in LiftP — par_reduces_cd_star_lam_inv_eq \
             takes C : Type"
        );
        assert!(
            term.contains("rigid_app_head_star_preserves_tag the_red_env e0 hr w hs"),
            "the rigid arm must delegate rather than re-prove"
        );
    }

    /// Both legs, as in the rigid version.
    #[test]
    fn test_nf_join_same_tag_uses_both_legs() {
        let src = include_str!("nf_head.rs");
        let term_start = src
            .find("def nf_join_same_tag")
            .expect("declaration present");
        let term = &src[term_start..src[term_start..].find("\",\n").unwrap() + term_start];
        assert_eq!(
            term.matches("nf_head_star_preserves_tag ").count(),
            2,
            "both legs must be pushed to the common reduct"
        );
    }

    /// The `hnf` premise must be DEFINED IN EXACTLY ONE PLACE.
    ///
    /// It used to be copy-pasted verbatim into four files, and that is precisely
    /// how one false premise became nine vacuous declarations: correcting or
    /// deleting it meant finding all four, and nothing made the fourth
    /// discoverable from the first.
    ///
    /// This test reads the four former carriers and asserts none of them defines
    /// the premise again. It deliberately scans SOURCE TEXT rather than a
    /// generated string, because the property under test *is* a property of the
    /// source. (The usual rule in this program — assert on generated strings, not
    /// source — exists to stop tests measuring their own literals; that trap is
    /// avoided here because this test lives in nf_head.rs and never scans it.)
    #[test]
    fn test_hnf_premise_is_defined_only_here() {
        let marker = concat!("const ", "HNF");
        for (name, src) in [
            ("defeq_capstone.rs", include_str!("defeq_capstone.rs")),
            (
                "defeq_round_binder.rs",
                include_str!("defeq_round_binder.rs"),
            ),
            ("defeq_round_leaf.rs", include_str!("defeq_round_leaf.rs")),
            ("defeq_round_rest.rs", include_str!("defeq_round_rest.rs")),
        ] {
            assert!(
                !src.contains(marker),
                "{name} defines the hnf premise again — it belongs in nf_head.rs alone. \
                 Four verbatim copies are how ONE false premise became NINE vacuous \
                 declarations."
            );
            assert!(
                src.contains("use super::nf_head::HNF;"),
                "{name} must import the single shared premise"
            );
        }
    }
}
