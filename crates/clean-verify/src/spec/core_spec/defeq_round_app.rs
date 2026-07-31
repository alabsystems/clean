// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The completeness round at an **application** head.
//!
//! ## Four sub-cases, three declarations
//!
//! `nf_head` reaches an application by two arms — `rigid` and `neutral` — so an
//! application-versus-application round has four evidence combinations. Writing
//! four rounds would be the obvious response and the wrong one.
//!
//! Both inversions conclude at the **same shape**: `w = app g x`, plus component
//! reductions. So the factoring is
//!
//! ```text
//! rigid_app_leg_inv   : rigid evidence   -> one leg -> StuckAppRedWitness
//! neutral_app_leg_inv : neutral evidence -> one leg -> StuckAppRedWitness
//! app_align           : two witnesses at the same w -> component joins
//! ```
//!
//! and then a **single** round taking the two witnesses. The dispatch picks a
//! leg-inverter per side; the mixed cases need nothing extra, because after
//! inversion both sides look identical.
//!
//! This is the same collapse that turned the 7×7 head grid into five cases:
//! find the point where the alternatives converge, and case-split before it
//! rather than after.
//!
//! ## Why the mixed cases are not absurd
//!
//! Worth recording, because the opposite is tempting to assume: a rigid-headed
//! spine and a const-headed neutral spine **can** be joinable. Both preserve the
//! application tag under reduction, so nothing about the head forces a
//! contradiction, and the meet is a perfectly ordinary application. Trying to
//! discharge the mixed cases as impossible would be attempting to prove
//! something false.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The recursion hypothesis, as in the binder rounds.
const RECUR: &str = "(recur : forall (c1 : KExpr) (c2 : KExpr), rbelow_plus c1 x -> \
     DefEq c1 c2 -> rbelow_plus_acc c2 -> DefEqFuelAccepts c1 c2) ";

impl Specification {
    /// Leg inverters, alignment, and the application round.
    pub(super) fn add_defeq_round_app(&mut self) -> Result<(), SpecError> {
        self.add_app_leg_inverters()?;
        self.add_app_align()?;
        self.add_app_round()?;
        Ok(())
    }

    /// One inverter per kind of head evidence, both landing on the same witness.
    fn add_app_leg_inverters(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def rigid_app_leg_inv (f : KExpr) (a : KExpr) (w : KExpr) \
             (hr : rigid_app_head (KExpr.app f a)) \
             (hs : par_reduces_cd_star the_red_env (KExpr.app f a) w) : \
             StuckAppRedWitness the_red_env f a w := \
             par_reduces_cd_star_rigid_app_inv the_red_env (KExpr.app f a) w hs f a hr \
             (Eq.refl KExpr (KExpr.app f a))",
            "rigid_app_leg_inv: invert ONE reduction leg out of a rigid-headed application. A \
             thin specialisation of par_reduces_cd_star_rigid_app_inv at the reflexive equation, \
             but naming it matters: it and its neutral twin land on the SAME witness type, which \
             is what lets the application round be one lemma instead of four. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            "def neutral_app_leg_inv (f : KExpr) (a : KExpr) (w : KExpr) \
             (hn : iota_neutral f) (hi : iota_immune (KExpr.app f a)) \
             (hs : par_reduces_cd_star the_red_env (KExpr.app f a) w) : \
             StuckAppRedWitness the_red_env f a w := \
             par_reduces_cd_star_neutral_app_inv_eq f a w \
             (StuckAppRedWitness the_red_env f a w) hn hi hs \
             (fun (g : KExpr) (y : KExpr) (heq : Eq KExpr w (KExpr.app g y)) \
             (hf : par_reduces_cd_star the_red_env f g) \
             (ha : par_reduces_cd_star the_red_env a y) \
             (_n2 : iota_neutral g) (_i2 : iota_immune (KExpr.app g y)) => \
             StuckAppRedWitness.mk the_red_env f a w g y heq hf ha)",
            "neutral_app_leg_inv: invert ONE reduction leg out of a const-headed neutral \
             application, landing on the same witness type as the rigid inverter. The two \
             obligations it consumes — iota_neutral and iota_immune — are exactly what nf_head's \
             neutral arm carries, and the continuation simply repackages the inversion's output as \
             a witness. Converting the continuation form to the witness form here, once, is what \
             makes the two evidence kinds interchangeable downstream. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// Two witnesses at the same meet give the component joins.
    fn add_app_align(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def app_align (f1 : KExpr) (a1 : KExpr) (f2 : KExpr) (a2 : KExpr) (w : KExpr) \
             (w1 : StuckAppRedWitness the_red_env f1 a1 w) \
             (w2 : StuckAppRedWitness the_red_env f2 a2 w) : \
             BinderJoinComponents f1 a1 f2 a2 := \
             StuckAppRedWitness.rec the_red_env f1 a1 w \
             (fun (_x : StuckAppRedWitness the_red_env f1 a1 w) => \
             BinderJoinComponents f1 a1 f2 a2) \
             (fun (g1 : KExpr) (x1 : KExpr) (heq1 : Eq KExpr w (KExpr.app g1 x1)) \
             (hf1 : par_reduces_cd_star the_red_env f1 g1) \
             (ha1 : par_reduces_cd_star the_red_env a1 x1) => \
             StuckAppRedWitness.rec the_red_env f2 a2 w \
             (fun (_y : StuckAppRedWitness the_red_env f2 a2 w) => \
             BinderJoinComponents f1 a1 f2 a2) \
             (fun (g2 : KExpr) (x2 : KExpr) (heq2 : Eq KExpr w (KExpr.app g2 x2)) \
             (hf2 : par_reduces_cd_star the_red_env f2 g2) \
             (ha2 : par_reduces_cd_star the_red_env a2 x2) => \
             (fun (hsame : Eq KExpr (KExpr.app g1 x1) (KExpr.app g2 x2)) => \
             BinderJoinComponents.mk f1 a1 f2 a2 \
             (par_strips_witness_cd_star.intro the_red_env f1 f2 g1 hf1 \
             (Eq.substType KExpr \
             (fun (z : KExpr) => par_reduces_cd_star the_red_env f2 z) \
             g2 g1 (Eq.symm KExpr g1 g2 (app_inj_fst g1 x1 g2 x2 hsame)) hf2)) \
             (par_strips_witness_cd_star.intro the_red_env a1 a2 x1 ha1 \
             (Eq.substType KExpr \
             (fun (z : KExpr) => par_reduces_cd_star the_red_env a2 z) \
             x2 x1 (Eq.symm KExpr x1 x2 (app_inj_snd g1 x1 g2 x2 hsame)) ha2))) \
             (Eq.trans KExpr (KExpr.app g1 x1) w (KExpr.app g2 x2) \
             (Eq.symm KExpr w (KExpr.app g1 x1) heq1) heq2)) w2) w1",
            "app_align: two application legs that reached the SAME meet have joinable components. \
             Independent of how each leg was inverted, which is the point — the rigid and neutral \
             inverters both hand over a StuckAppRedWitness, so this single alignment serves all \
             four evidence combinations. The argument is the usual one: compose the two \
             descriptions of w and let app-injectivity align them. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    /// The round, taking both witnesses.
    fn add_app_round(&mut self) -> Result<(), SpecError> {
        let accept = |slot: usize| {
            let (c1, c2, sub) = if slot == 0 {
                ("f1", "f2", "subexpr_step.app_f")
            } else {
                ("a1", "a2", "subexpr_step.app_a")
            };
            format!(
                "(recur {c1} {c2} \
                 (whnf_component_below n x (KExpr.app f1 a1) {c1} hx ({sub} f1 a1)) \
                 (join_to_def_eq {c1} {c2} j{slot}) \
                 (whnf_component_acc n bb (KExpr.app f2 a2) {c2} hb ({sub} f2 a2) accb))"
            )
        };
        self.add_recursive_def(
            &format!(
                "def def_eq_round_app (n : Nat) (x : KExpr) (bb : KExpr) \
                 (f1 : KExpr) (a1 : KExpr) (f2 : KExpr) (a2 : KExpr) (w : KExpr) \
                 (hx : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
                 (OptionType.some KExpr (KExpr.app f1 a1))) \
                 (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
                 (OptionType.some KExpr (KExpr.app f2 a2))) \
                 (wit1 : StuckAppRedWitness the_red_env f1 a1 w) \
                 (wit2 : StuckAppRedWitness the_red_env f2 a2 w) \
                 (accb : rbelow_plus_acc bb) {RECUR}: DefEqFuelAccepts x bb := \
                 BinderJoinComponents.rec f1 a1 f2 a2 \
                 (fun (_c : BinderJoinComponents f1 a1 f2 a2) => DefEqFuelAccepts x bb) \
                 (fun (j0 : par_strips_witness_cd_star the_red_env f1 f2) \
                 (j1 : par_strips_witness_cd_star the_red_env a1 a2) => \
                 def_eq_complete_step_app n x bb f1 a1 f2 a2 hx hb {a0} {a1}) \
                 (app_align f1 a1 f2 a2 w wit1 wit2)",
                a0 = accept(0),
                a1 = accept(1),
            ),
            "def_eq_round_app: ONE completeness round at an application head, covering all four \
             evidence combinations. It takes the two inverted legs as StuckAppRedWitness \
             hypotheses rather than the head evidence itself, so the caller picks a leg-inverter \
             per side and this lemma never learns which — the mixed rigid/neutral cases need \
             nothing extra because after inversion both sides look identical. \
             \
             Worth recording that the mixed cases are NOT absurd, since assuming otherwise is \
             tempting: a rigid-headed spine and a const-headed neutral spine can genuinely be \
             joinable, both preserve the application tag under reduction, and their meet is an \
             ordinary application. Trying to discharge them as impossible would be attempting to \
             prove something false. \
             \
             Same collapse as the head grid: find where the alternatives converge and case-split \
             BEFORE that point rather than after. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    /// The two inverters must land on the SAME witness type. That is the entire
    /// mechanism by which four evidence combinations become one round.
    #[test]
    fn test_both_inverters_produce_the_same_witness() {
        let src = include_str!("defeq_round_app.rs");
        let body = src
            .split("impl Specification {")
            .nth(1)
            .expect("impl block present");
        for inverter in ["rigid_app_leg_inv", "neutral_app_leg_inv"] {
            let at = body.find(&format!("def {inverter}")).expect("declared");
            let decl = &body[at..at + 600];
            assert!(
                decl.contains("StuckAppRedWitness the_red_env f a w"),
                "{inverter} must conclude at the shared witness type"
            );
        }
    }

    /// The round must NOT mention head evidence — it takes inverted legs, which
    /// is what makes it evidence-agnostic.
    #[test]
    fn test_the_round_is_evidence_agnostic() {
        let src = include_str!("defeq_round_app.rs");
        let at = src.find("def def_eq_round_app").expect("declared");
        let decl = &src[at..at + 1400];
        for evidence in ["rigid_app_head", "iota_neutral", "iota_immune"] {
            assert!(
                !decl.contains(evidence),
                "the round must not require {evidence}; it takes inverted legs so that the \
                 caller chooses an inverter per side and the mixed cases cost nothing"
            );
        }
        assert!(decl.contains("StuckAppRedWitness the_red_env f1 a1 w"));
        assert!(decl.contains("StuckAppRedWitness the_red_env f2 a2 w"));
    }

    /// Both components recurse, each with its own descent and accessibility.
    #[test]
    fn test_both_components_recurse() {
        let src = include_str!("defeq_round_app.rs");
        let at = src.find("let accept =").expect("accept generator present");
        let generator = &src[at..at + 800];
        assert!(
            generator.contains("subexpr_step.app_f") && generator.contains("subexpr_step.app_a")
        );
        assert!(generator.contains("whnf_component_below n x (KExpr.app f1 a1)"));
        assert!(generator.contains("whnf_component_acc n bb (KExpr.app f2 a2)"));
        assert!(generator.contains("join_to_def_eq"));
    }

    /// `app_align` must compose the two meet descriptions and use both
    /// injectivities — the step that makes the components comparable at all.
    #[test]
    fn test_align_composes_the_meets() {
        let src = include_str!("defeq_round_app.rs");
        let at = src.find("def app_align").expect("declared");
        let decl = &src[at..src[at..].find("\",\n").unwrap() + at];
        assert!(
            decl.contains("Eq.trans KExpr (KExpr.app g1 x1) w (KExpr.app g2 x2)"),
            "the two descriptions of the meet must be composed through w"
        );
        assert!(decl.contains("app_inj_fst") && decl.contains("app_inj_snd"));
        assert_eq!(
            decl.matches("StuckAppRedWitness.rec").count(),
            2,
            "both witnesses must be unpacked"
        );
    }
}
