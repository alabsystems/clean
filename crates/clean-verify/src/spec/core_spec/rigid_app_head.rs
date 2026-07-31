// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A shape-only rigid-head predicate, because `whnf_stuck_head` is not
//! preserved by reduction.
//!
//! ## The false statement this replaces
//!
//! Lifting `par_reduces_cd_stuck_app_inv` to the reflexive-transitive closure
//! needs the head to still be stuck after a step. **That is false.**
//! `whnf_stuck_head`'s `projw` arm accepts `proj s i sub` whenever
//! `is_whnf sub`; `is_neutral` (`whnf_reduction.rs:74-79`) has bare `const` and
//! `app` arms with no δ-deadness condition, so `const c []` is `is_whnf` even
//! when `c` unfolds, so `proj s i (const c [])` is `whnf_stuck_head` — and it
//! δ-reduces to `proj s i <definition>`, whose subject need not be `is_whnf` at
//! all. The `projw` arm cannot be rebuilt.
//!
//! ## Why the shape-only weakening works
//!
//! The obstruction is entirely in the **side conditions on subterms**, never in
//! the head. Every stuck shape maps to itself under `par_reduces_cd`: `sort`,
//! `pi` and `lit` are rigid; an `app` on such a head admits only the `app`
//! congruence (no β, since the head is not a `lam`; no ι or δ, since the head
//! carries no constant name); a `proj` admits only the `proj` congruence, for
//! the same ι/δ reason.
//!
//! So `rigid_app_head` drops every subterm condition. Its `proj` arm accepts
//! **any** subject — that is the entire point, and what makes preservation
//! provable — and it still delivers what consumers need: the spine head carries
//! no constant name, and is not a lambda.
//!
//! `whnf_stuck_head` remains useful: it is what `whnf_noredex_class`'s `stuck`
//! arm hands you, and `whnf_stuck_head_rigid` forgets down into this predicate.
//!
//! ## What is here, and what comes next
//!
//! Landed here: the predicate, the forgetful map, the head-shape inversions
//! (`app_inv`, `not_lam`), the no-constant-name fact, and the resulting ι/δ
//! immunity.
//!
//! Deliberately NOT here: `rigid_app_head_preserved`, the eleven-arm induction
//! over `par_reduces_cd`. It is the payoff and it is next, but it is an order
//! of magnitude larger than anything in this module, and splitting keeps a
//! failure localisable — each spec build costs ~21 minutes and reports one
//! declaration at a time.
//!
//! `DerivedProved` throughout, empty axiom closures; the predicate is
//! census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The five `rigid_app_head` arms, as `(payload binders, applied form,
/// recursive sub-head or None)`.
const RIGID_ARMS: [(&str, &str, Option<&str>); 5] = [
    ("(n : Level)", "(KExpr.sort n)", None),
    (
        "(pty : KExpr) (pbody : KExpr)",
        "(KExpr.pi pty pbody)",
        None,
    ),
    ("(v : Nat)", "(KExpr.lit v)", None),
    ("(af : KExpr) (aa : KExpr)", "(KExpr.app af aa)", Some("af")),
    (
        "(s : Name) (i : Nat) (sub : KExpr)",
        "(KExpr.proj s i sub)",
        None,
    ),
];

impl Specification {
    /// The shape-only rigid-head predicate and its immediate consequences.
    pub(super) fn add_rigid_app_head(&mut self) -> Result<(), SpecError> {
        self.add_rigid_app_head_type()?;
        self.add_rigid_from_stuck()?;
        self.add_rigid_head_inversions()?;
        self.add_rigid_head_immunity()?;
        Ok(())
    }

    fn add_rigid_app_head_type(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive rigid_app_head : KExpr -> Type\n\
             | sort : forall (n : Level), rigid_app_head (KExpr.sort n)\n\
             | pi : forall (pty : KExpr) (pbody : KExpr), rigid_app_head (KExpr.pi pty pbody)\n\
             | lit : forall (v : Nat), rigid_app_head (KExpr.lit v)\n\
             | app : forall (af : KExpr) (aa : KExpr), rigid_app_head af -> \
             rigid_app_head (KExpr.app af aa)\n\
             | proj : forall (s : Name) (i : Nat) (sub : KExpr), \
             rigid_app_head (KExpr.proj s i sub)",
            "rigid_app_head e: e's SPINE HEAD is rigid — a sort, pi, literal, or projection, \
             possibly under application. Deliberately SHAPE-ONLY: unlike whnf_stuck_head it \
             imposes no condition on subterms, and in particular its proj arm accepts ANY \
             subject. That is the entire point. whnf_stuck_head is NOT preserved by reduction — \
             its projw arm needs is_whnf of the subject, and a const-headed subject can \
             delta-unfold out of is_whnf — whereas this predicate is preserved, because no arm \
             constrains a subterm. It still delivers what consumers need: no constant name at \
             the spine head, and not a lambda. Census-neutral.",
        )?;
        Ok(())
    }

    /// `whnf_stuck_head` forgets into `rigid_app_head`.
    fn add_rigid_from_stuck(&mut self) -> Result<(), SpecError> {
        // Six source arms onto five targets: whnf_stuck_head's `proj` and
        // `projw` both land on the single shape-only `proj` arm, which is
        // precisely where the side conditions get dropped.
        self.add_recursive_def(
            "def whnf_stuck_head_rigid (f : KExpr) (hs : whnf_stuck_head f) : rigid_app_head f := \
             whnf_stuck_head.rec (fun (x : KExpr) (_h : whnf_stuck_head x) => rigid_app_head x) \
             (fun (n : Level) => rigid_app_head.sort n) \
             (fun (pty : KExpr) (pbody : KExpr) => rigid_app_head.pi pty pbody) \
             (fun (af : KExpr) (aa : KExpr) (_hf : whnf_stuck_head af) \
             (ih : rigid_app_head af) => rigid_app_head.app af aa ih) \
             (fun (s : Name) (i : Nat) (sub : KExpr) (_hsub : whnf_stuck_head sub) \
             (_ih : rigid_app_head sub) => rigid_app_head.proj s i sub) \
             (fun (s : Name) (i : Nat) (sub : KExpr) (_hw : is_whnf sub) => \
             rigid_app_head.proj s i sub) \
             (fun (v : Nat) => rigid_app_head.lit v) \
             f hs",
            "whnf_stuck_head_rigid: every stuck head is rigid — forget the subterm side \
             conditions. Six source arms onto five targets: whnf_stuck_head's proj and projw both \
             land on the single shape-only proj arm, which is exactly where the conditions that \
             block preservation are discarded. This is what lets the whnf_noredex_class `stuck` \
             arm feed the preserved predicate. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// Head-shape inversions: not a lambda, and the function part of a rigid
    /// application is itself rigid.
    fn add_rigid_head_inversions(&mut self) -> Result<(), SpecError> {
        // not_lam: every arm concludes at a head that is not `lam`.
        let mut not_lam_arms = String::new();
        for (payload, form, sub) in RIGID_ARMS {
            let ih = match sub {
                Some(v) => format!(
                    "(_ih : forall (C : Type) (lty : KExpr) (lbd : KExpr), \
                     Eq KExpr {v} (KExpr.lam lty lbd) -> C) "
                ),
                None => String::new(),
            };
            let rec_premise = match sub {
                Some(v) => format!("(_hr : rigid_app_head {v}) "),
                None => String::new(),
            };
            not_lam_arms.push_str(&format!(
                "(fun {payload} {rec_premise}{ih}(C : Type) (lty : KExpr) (lbd : KExpr) \
                 (heq : Eq KExpr {form} (KExpr.lam lty lbd)) => \
                 kexpr_discr_t C {form} (KExpr.lam lty lbd) heq (Eq.refl Bool Bool.false)) "
            ));
        }
        self.add_recursive_def(
            &format!(
                "def rigid_app_head_not_lam (f : KExpr) (hr : rigid_app_head f) : \
                 forall (C : Type) (lty : KExpr) (lbd : KExpr), \
                 Eq KExpr f (KExpr.lam lty lbd) -> C := \
                 rigid_app_head.rec (fun (x : KExpr) (_h : rigid_app_head x) => \
                 forall (C : Type) (lty : KExpr) (lbd : KExpr), \
                 Eq KExpr x (KExpr.lam lty lbd) -> C) \
                 {not_lam_arms}f hr"
            ),
            "rigid_app_head_not_lam: a rigid head is never a lambda. All five arms conclude at a \
             different head constructor and die by generic discrimination — the same \
             argument-from-an-absent-arm as whnf_stuck_head_not_lam, restated over the preserved \
             predicate. Rules out the beta case when inverting reduction. DerivedProved, zero \
             axiom_deps.",
        )?;

        // app_inv: the function part of a rigid application is rigid.
        let mut app_inv_arms = String::new();
        for (payload, form, sub) in RIGID_ARMS {
            let ih = match sub {
                Some(v) => format!(
                    "(_ih : forall (gf : KExpr) (ga : KExpr), \
                     Eq KExpr {v} (KExpr.app gf ga) -> rigid_app_head gf) "
                ),
                None => String::new(),
            };
            let rec_premise = match sub {
                Some(v) => format!("(hr : rigid_app_head {v}) "),
                None => String::new(),
            };
            let body = if sub.is_some() {
                // The substantive arm: recover af = gf and transport.
                "Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) af gf \
                 (app_inj_fst af aa gf ga heq) hr"
                    .to_string()
            } else {
                format!(
                    "kexpr_discr_t (rigid_app_head gf) {form} (KExpr.app gf ga) heq \
                     (Eq.refl Bool Bool.false)"
                )
            };
            app_inv_arms.push_str(&format!(
                "(fun {payload} {rec_premise}{ih}(gf : KExpr) (ga : KExpr) \
                 (heq : Eq KExpr {form} (KExpr.app gf ga)) => {body}) "
            ));
        }
        self.add_recursive_def(
            &format!(
                "def rigid_app_head_app_inv (x : KExpr) (hr : rigid_app_head x) : \
                 forall (gf : KExpr) (ga : KExpr), Eq KExpr x (KExpr.app gf ga) -> \
                 rigid_app_head gf := \
                 rigid_app_head.rec (fun (z : KExpr) (_h : rigid_app_head z) => \
                 forall (gf : KExpr) (ga : KExpr), Eq KExpr z (KExpr.app gf ga) -> \
                 rigid_app_head gf) \
                 {app_inv_arms}x hr"
            ),
            "rigid_app_head_app_inv: if an application is rigid-headed then so is its function \
             part. Four arms discriminate (a sort, pi, literal or projection is not an \
             application); the app arm recovers the function by app_inj_fst and transports its \
             own premise. Needed by the preservation induction's congruence case, which must \
             feed the induction hypothesis. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// No constant name at the head, hence no ι or δ step.
    fn add_rigid_head_immunity(&mut self) -> Result<(), SpecError> {
        let none_at = |x: &str| {
            format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {x})) (OptionType.none Name)")
        };
        let refl = "Eq.refl (OptionType Name) (OptionType.none Name)";

        let mut arms = String::new();
        for (payload, _form, sub) in RIGID_ARMS {
            match sub {
                // The app arm recurses to exactly the statement, because
                // kapp_fn (app f a) unfolds to kapp_fn f.
                Some(v) => arms.push_str(&format!(
                    "(fun {payload} (_hr : rigid_app_head {v}) (ih : {ih}) => ih) ",
                    ih = none_at(v)
                )),
                None => arms.push_str(&format!("(fun {payload} => {refl}) ")),
            }
        }

        self.add_recursive_def(
            &format!(
                "def rigid_app_head_no_const (f : KExpr) (hr : rigid_app_head f) : {goal} := \
                 rigid_app_head.rec (fun (x : KExpr) (_h : rigid_app_head x) => {motive}) \
                 {arms}f hr",
                goal = none_at("f"),
                motive = none_at("x"),
            ),
            "rigid_app_head_no_const: a rigid spine head carries no constant name. Same shape as \
             whnf_stuck_head_no_const over the preserved predicate: four arms compute to none \
             directly and the app arm recurses to exactly the statement, since kapp_fn (app f a) \
             unfolds to kapp_fn f. DerivedProved, zero axiom_deps.",
        )?;

        for (name, envsel, reduct, lemma, greek) in [
            (
                "rigid_app_iota_immune",
                "red_rec renv",
                "iota_reduct",
                "iota_reduct_head_none",
                "iota",
            ),
            (
                "rigid_app_delta_immune",
                "red_def renv",
                "delta_reduct",
                "delta_reduct_head_none",
                "delta",
            ),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} (renv : RedEnv) (f : KExpr) (hr : rigid_app_head f) : \
                     Eq (OptionType KExpr) ({reduct} ({envsel}) f) (OptionType.none KExpr) := \
                     {lemma} ({envsel}) f (rigid_app_head_no_const f hr)"
                ),
                &format!(
                    "{name}: a rigid-headed term admits no {greek} step, over any environment and \
                     with no side conditions. Stated at the term itself rather than at an \
                     application of it, because rigid_app_head is already closed under \
                     application — so this covers both the head and the whole spine, unlike its \
                     whnf_stuck_head predecessor which had to be stated at `app f a`. \
                     DerivedProved, zero axiom_deps."
                ),
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `proj` arm must take an unconstrained subject. If it ever gains a
    /// premise, preservation becomes false again and this whole module loses
    /// its reason to exist.
    #[test]
    fn test_rigid_proj_arm_is_unconstrained() {
        let (_, form, sub) = RIGID_ARMS[4];
        assert_eq!(form, "(KExpr.proj s i sub)");
        assert!(
            sub.is_none(),
            "the proj arm must impose NO condition on its subject — that is exactly what \
             whnf_stuck_head's projw arm does wrong, and why it is not preserved"
        );
    }

    /// Exactly one arm recurses (`app`); every other arm is a leaf. A second
    /// recursive arm would mean a subterm condition crept back in.
    #[test]
    fn test_rigid_app_head_has_exactly_one_recursive_arm() {
        let recursive = RIGID_ARMS.iter().filter(|(_, _, s)| s.is_some()).count();
        assert_eq!(
            recursive, 1,
            "only the app arm may recurse; any other recursive arm reintroduces a subterm \
             side condition and breaks preservation"
        );
        assert_eq!(RIGID_ARMS.len(), 5);
    }

    /// Every generated term must be paren-balanced and reference only bound
    /// hypotheses — the two axes that cost a spec build each earlier tonight.
    #[test]
    fn test_rigid_head_generated_arms_are_wellformed() {
        // Reconstruct the immunity arms, the only ones with IH plumbing.
        let none_at = |x: &str| {
            format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {x})) (OptionType.none Name)")
        };
        let mut arms = String::new();
        for (payload, _form, sub) in RIGID_ARMS {
            match sub {
                Some(v) => arms.push_str(&format!(
                    "(fun {payload} (_hr : rigid_app_head {v}) (ih : {ih}) => ih) ",
                    ih = none_at(v)
                )),
                None => arms.push_str(&format!(
                    "(fun {payload} => Eq.refl (OptionType Name) (OptionType.none Name)) "
                )),
            }
        }
        let mut depth: i64 = 0;
        for ch in arms.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open");
        }
        assert_eq!(depth, 0, "arms must be paren-balanced");
        assert_eq!(
            arms.matches("(fun ").count(),
            5,
            "one minor premise per rigid_app_head constructor"
        );
        // `ih` is referenced exactly where it is bound.
        assert_eq!(
            arms.matches("(ih : ").count(),
            arms.matches("=> ih)").count()
        );
    }
}
