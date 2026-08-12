// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Component joins for the **spine** heads: application and projection.
//!
//! The binder heads were handled in `binder_join_components.rs`. These three
//! complete the family:
//!
//! ```text
//! rigid_app_join_components   : rigid-headed applications
//! neutral_app_join_components : const-headed neutral applications
//! proj_join_components        : projections, plus the name/index equalities
//! ```
//!
//! ## Why `app` needs two versions
//!
//! `nf_head` reaches an application by two different arms — `rigid` and
//! `neutral` — and they carry different evidence. The rigid arm gives
//! `rigid_app_head`, which unlocks `par_reduces_cd_star_rigid_app_inv`; the
//! neutral arm gives `iota_neutral` plus `iota_immune`, which unlock
//! `par_reduces_cd_star_neutral_app_inv_eq`. **Neither implies the other**: a
//! const-headed spine is not rigid (a constant is not a rigid head), and a
//! rigid-headed spine has no `iota_neutral` witness (that predicate has only
//! `const` and `app` arms).
//!
//! So the capstone's two application leaves genuinely need two lemmas. Trying to
//! unify them would mean proving one of those implications, and both are false.
//!
//! ## Shape of the argument
//!
//! The same as the binder case, with one difference in the plumbing: these
//! inversions return **witnesses** (`StuckAppRedWitness`, `ProjRedWitness`)
//! rather than taking continuations, so each is unpacked by its own recursor
//! before the meets can be aligned. The alignment itself is identical —
//! compose the two descriptions of `w` and apply constructor injectivity.
//!
//! `proj` additionally returns the **name and index equalities**. Those are not
//! free: `nf_tag_forces_proj` only says both sides are projections, so their
//! struct names and field indices could differ a priori. They agree because both
//! reduce to the same `w`, and that is where the equalities come from.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Component joins for applications and projections.
    pub(super) fn add_spine_join_components(&mut self) -> Result<(), SpecError> {
        self.add_proj_components_witness()?;
        self.add_rigid_app_components()?;
        self.add_neutral_app_components()?;
        self.add_proj_components()?;
        Ok(())
    }

    fn add_proj_components_witness(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive ProjJoinComponents (s1 : Name) (i1 : Nat) (u1 : KExpr) (s2 : Name) \
             (i2 : Nat) (u2 : KExpr) : Type\n\
             | mk : Eq Name s1 s2 -> Eq Nat i1 i2 -> \
             par_strips_witness_cd_star the_red_env u1 u2 -> \
             ProjJoinComponents s1 i1 u1 s2 i2 u2",
            "ProjJoinComponents s1 i1 u1 s2 i2 u2: two joinable projections agree on their struct \
             name and field index, and their subjects are joinable. The name and index equalities \
             are NOT free — nf_tag_forces_proj says only that both sides are projections, so a \
             priori they could differ. They agree because both reduce to the same common reduct, \
             which is where the equalities come from. Census-neutral.",
        )?;
        Ok(())
    }

    /// The rigid-headed application case.
    fn add_rigid_app_components(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::app_components_src(true),
            "rigid_app_join_components: a joinable pair of RIGID-headed applications has joinable \
             components. Both legs go through par_reduces_cd_star_rigid_app_inv, whose witness is \
             unpacked before the two descriptions of the common reduct are composed and \
             app-injectivity aligns them. \
             \
             This is one of TWO application lemmas, and the split is forced: nf_head reaches an \
             application by both its rigid and its neutral arm, and neither piece of evidence \
             implies the other — a const-headed spine is not rigid, and a rigid-headed spine has \
             no iota_neutral witness. Unifying them would require proving one of those \
             implications, and both are false. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The const-headed neutral application case.
    fn add_neutral_app_components(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::app_components_src(false),
            "neutral_app_join_components: a joinable pair of CONST-HEADED NEUTRAL applications has \
             joinable components. Same argument as the rigid version but through \
             par_reduces_cd_star_neutral_app_inv_eq, which takes continuations rather than \
             returning a witness and demands iota_neutral plus iota_immune on each side — the \
             obligations nf_head's neutral arm carries precisely so that this step is available. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// `rigid` selects between the two application inversions.
    fn app_components_src(rigid: bool) -> String {
        let goal = "BinderJoinComponents f1 a1 f2 a2";
        let (name, extra_binders) = if rigid {
            (
                "rigid_app_join_components",
                "(hr1 : rigid_app_head (KExpr.app f1 a1)) \
                 (hr2 : rigid_app_head (KExpr.app f2 a2)) ",
            )
        } else {
            (
                "neutral_app_join_components",
                "(hn1 : iota_neutral f1) (hi1 : iota_immune (KExpr.app f1 a1)) \
                 (hn2 : iota_neutral f2) (hi2 : iota_immune (KExpr.app f2 a2)) ",
            )
        };

        // The two component joins, once g1 = g2 and x1 = x2 are known.
        let build = String::from(
            "(fun (hsame : Eq KExpr (KExpr.app g1 x1) (KExpr.app g2 x2)) => \
             BinderJoinComponents.mk f1 a1 f2 a2 \
             (par_strips_witness_cd_star.intro the_red_env f1 f2 g1 hlf \
             (Eq.substType KExpr \
             (fun (z : KExpr) => par_reduces_cd_star the_red_env f2 z) \
             g2 g1 (Eq.symm KExpr g1 g2 (app_inj_fst g1 x1 g2 x2 hsame)) hrf)) \
             (par_strips_witness_cd_star.intro the_red_env a1 a2 x1 hla \
             (Eq.substType KExpr \
             (fun (z : KExpr) => par_reduces_cd_star the_red_env a2 z) \
             x2 x1 (Eq.symm KExpr x1 x2 (app_inj_snd g1 x1 g2 x2 hsame)) hra))) \
             (Eq.trans KExpr (KExpr.app g1 x1) w (KExpr.app g2 x2) \
             (Eq.symm KExpr w (KExpr.app g1 x1) heql) heqr)",
        );

        // Inversion of one leg, binding (g, x, heq, leg_f, leg_a).
        let invert = |side: char| {
            let (form, ev, g, x, heq, lf, la) = if side == 'l' {
                (
                    "(KExpr.app f1 a1)",
                    if rigid { "hr1" } else { "hn1" },
                    "g1",
                    "x1",
                    "heql",
                    "hlf",
                    "hla",
                )
            } else {
                (
                    "(KExpr.app f2 a2)",
                    if rigid { "hr2" } else { "hn2" },
                    "g2",
                    "x2",
                    "heqr",
                    "hrf",
                    "hra",
                )
            };
            let (fst, snd) = if side == 'l' {
                ("f1", "a1")
            } else {
                ("f2", "a2")
            };
            let leg = if side == 'l' { "hlw" } else { "hrw" };
            if rigid {
                // Witness form: unpack with StuckAppRedWitness.rec.
                format!(
                    "StuckAppRedWitness.rec the_red_env {fst} {snd} w \
                     (fun (_x : StuckAppRedWitness the_red_env {fst} {snd} w) => {goal}) \
                     (fun ({g} : KExpr) ({x} : KExpr) \
                     ({heq} : Eq KExpr w (KExpr.app {g} {x})) \
                     ({lf} : par_reduces_cd_star the_red_env {fst} {g}) \
                     ({la} : par_reduces_cd_star the_red_env {snd} {x}) => BODY) \
                     (par_reduces_cd_star_rigid_app_inv the_red_env {form} w {leg} \
                     {fst} {snd} {ev} (Eq.refl KExpr {form}))"
                )
            } else {
                // Continuation form: pass the answer type directly.
                let ii = if side == 'l' { "hi1" } else { "hi2" };
                format!(
                    "par_reduces_cd_star_neutral_app_inv_eq {fst} {snd} w ({goal}) {ev} {ii} \
                     {leg} \
                     (fun ({g} : KExpr) ({x} : KExpr) \
                     ({heq} : Eq KExpr w (KExpr.app {g} {x})) \
                     ({lf} : par_reduces_cd_star the_red_env {fst} {g}) \
                     ({la} : par_reduces_cd_star the_red_env {snd} {x}) \
                     (_n2 : iota_neutral {g}) \
                     (_i2 : iota_immune (KExpr.app {g} {x})) => BODY)"
                )
            }
        };

        let inner = invert('r').replace("BODY", &build);
        let outer = invert('l').replace("BODY", &inner);

        format!(
            "def {name} (f1 : KExpr) (a1 : KExpr) (f2 : KExpr) (a2 : KExpr) {extra_binders}\
             (hj : par_strips_witness_cd_star the_red_env (KExpr.app f1 a1) \
             (KExpr.app f2 a2)) : {goal} := \
             @par_strips_witness_cd_star.rec the_red_env (KExpr.app f1 a1) (KExpr.app f2 a2) \
             (fun (_j : par_strips_witness_cd_star the_red_env (KExpr.app f1 a1) \
             (KExpr.app f2 a2)) => {goal}) \
             (fun (w : KExpr) \
             (hlw : par_reduces_cd_star the_red_env (KExpr.app f1 a1) w) \
             (hrw : par_reduces_cd_star the_red_env (KExpr.app f2 a2) w) => {outer}) hj"
        )
    }

    fn add_proj_components(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::proj_components_src(),
            "proj_join_components: two joinable projections agree on struct name and field index, \
             and their subjects are joinable. Both legs go through \
             par_reduces_cd_star_proj_inv; the witnesses are unpacked, the two descriptions of the \
             common reduct composed, and all THREE projection injectivities applied — name, index \
             and subject. The name and index equalities are the interesting output: \
             nf_tag_forces_proj establishes only that both sides are projections, so a priori they \
             could disagree, and it is the shared reduct that rules that out. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    fn proj_components_src() -> String {
        let goal = "ProjJoinComponents s1 i1 u1 s2 i2 u2";
        let build = String::from(
            "(fun (hsame : Eq KExpr (KExpr.proj s1 i1 v1) (KExpr.proj s2 i2 v2)) => \
             ProjJoinComponents.mk s1 i1 u1 s2 i2 u2 \
             (proj_inj_name s1 i1 v1 s2 i2 v2 hsame) \
             (proj_inj_idx s1 i1 v1 s2 i2 v2 hsame) \
             (par_strips_witness_cd_star.intro the_red_env u1 u2 v1 hl1 \
             (Eq.substType KExpr \
             (fun (z : KExpr) => par_reduces_cd_star the_red_env u2 z) \
             v2 v1 (Eq.symm KExpr v1 v2 (proj_inj_sub s1 i1 v1 s2 i2 v2 hsame)) hl2))) \
             (Eq.trans KExpr (KExpr.proj s1 i1 v1) w (KExpr.proj s2 i2 v2) \
             (Eq.symm KExpr w (KExpr.proj s1 i1 v1) heq1) heq2)",
        );
        let invert = |side: u8| {
            let (s, i, u, v, heq, hl, leg) = if side == 1 {
                ("s1", "i1", "u1", "v1", "heq1", "hl1", "hlw")
            } else {
                ("s2", "i2", "u2", "v2", "heq2", "hl2", "hrw")
            };
            format!(
                "ProjRedWitness.rec the_red_env {s} {i} {u} w \
                 (fun (_x : ProjRedWitness the_red_env {s} {i} {u} w) => {goal}) \
                 (fun ({v} : KExpr) ({heq} : Eq KExpr w (KExpr.proj {s} {i} {v})) \
                 ({hl} : par_reduces_cd_star the_red_env {u} {v}) => BODY) \
                 (par_reduces_cd_star_proj_inv the_red_env (KExpr.proj {s} {i} {u}) w {leg} \
                 {s} {i} {u} (Eq.refl KExpr (KExpr.proj {s} {i} {u})))"
            )
        };
        let inner = invert(2).replace("BODY", &build);
        let outer = invert(1).replace("BODY", &inner);
        format!(
            "def proj_join_components (s1 : Name) (i1 : Nat) (u1 : KExpr) (s2 : Name) \
             (i2 : Nat) (u2 : KExpr) \
             (hj : par_strips_witness_cd_star the_red_env (KExpr.proj s1 i1 u1) \
             (KExpr.proj s2 i2 u2)) : {goal} := \
             @par_strips_witness_cd_star.rec the_red_env (KExpr.proj s1 i1 u1) \
             (KExpr.proj s2 i2 u2) \
             (fun (_j : par_strips_witness_cd_star the_red_env (KExpr.proj s1 i1 u1) \
             (KExpr.proj s2 i2 u2)) => {goal}) \
             (fun (w : KExpr) \
             (hlw : par_reduces_cd_star the_red_env (KExpr.proj s1 i1 u1) w) \
             (hrw : par_reduces_cd_star the_red_env (KExpr.proj s2 i2 u2) w) => {outer}) hj"
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The two application lemmas must use DIFFERENT inversions and different
    /// evidence. Collapsing them would require proving that rigid implies
    /// iota-neutral or vice versa, and both implications are false.
    #[test]
    fn test_the_two_app_lemmas_use_different_evidence() {
        let rigid = Specification::app_components_src(true);
        let neutral = Specification::app_components_src(false);

        assert!(rigid.contains("rigid_app_head (KExpr.app f1 a1)"));
        assert!(rigid.contains("par_reduces_cd_star_rigid_app_inv"));
        assert!(
            !rigid.contains("iota_neutral"),
            "the rigid lemma must not require iota_neutral — a rigid-headed spine has no such \
             witness"
        );

        assert!(neutral.contains("iota_neutral f1"));
        assert!(neutral.contains("iota_immune (KExpr.app f1 a1)"));
        assert!(neutral.contains("par_reduces_cd_star_neutral_app_inv_eq"));
        assert!(
            !neutral.contains("rigid_app_head"),
            "the neutral lemma must not require rigid_app_head — a const-headed spine is not rigid"
        );
    }

    /// Both legs inverted, both descriptions of the meet composed, both
    /// components joined — in every one of the three lemmas.
    #[test]
    fn test_every_lemma_inverts_both_legs_and_aligns_the_meets() {
        for (label, src, inv, injs) in [
            (
                "rigid app",
                Specification::app_components_src(true),
                "par_reduces_cd_star_rigid_app_inv",
                2,
            ),
            (
                "neutral app",
                Specification::app_components_src(false),
                "par_reduces_cd_star_neutral_app_inv_eq",
                2,
            ),
            (
                "proj",
                Specification::proj_components_src(),
                "par_reduces_cd_star_proj_inv",
                3,
            ),
        ] {
            assert_eq!(
                src.matches(inv).count(),
                2,
                "{label}: both legs must be inverted"
            );
            assert_eq!(
                src.matches("Eq.trans KExpr").count(),
                1,
                "{label}: the two meet descriptions must be composed exactly once, through w"
            );
            let inj_count = src.matches("_inj_").count();
            assert_eq!(
                inj_count, injs,
                "{label}: expected {injs} injectivity applications, found {inj_count}"
            );
        }
    }

    /// `proj` must produce the name and index equalities. Without them the
    /// capstone could not apply `def_eq_complete_step_proj`, which fixes both on
    /// each side.
    #[test]
    fn test_proj_returns_the_name_and_index_equalities() {
        let src = Specification::proj_components_src();
        for inj in ["proj_inj_name", "proj_inj_idx", "proj_inj_sub"] {
            assert!(src.contains(inj), "proj must apply {inj}");
        }
        assert!(
            src.contains("ProjJoinComponents.mk s1 i1 u1 s2 i2 u2"),
            "the witness must carry both equalities alongside the subject join"
        );
    }

    #[test]
    fn test_spine_component_terms_parens_balanced() {
        for (label, src) in [
            ("rigid app", Specification::app_components_src(true)),
            ("neutral app", Specification::app_components_src(false)),
            ("proj", Specification::proj_components_src()),
        ] {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "{label}: close paren before its open");
            }
            assert_eq!(depth, 0, "{label}: unbalanced parens");
        }
        // The BODY placeholder must be fully substituted in every lemma.
        for (label, src) in [
            ("rigid app", Specification::app_components_src(true)),
            ("neutral app", Specification::app_components_src(false)),
            ("proj", Specification::proj_components_src()),
        ] {
            assert!(
                !src.contains("BODY"),
                "{label}: an unsubstituted BODY placeholder would be an unknown identifier"
            );
        }
    }
}
