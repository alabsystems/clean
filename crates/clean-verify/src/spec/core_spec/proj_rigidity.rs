// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `proj` head-rigidity inversion — the last one the completeness capstone
//! needs.
//!
//! With `sort` / `lam` / `pi` / neutral-app / dead-const already in tree and
//! `lit` / `bvar` landed in `kexpr_discr.rs`, this completes the family:
//!
//! ```text
//! par_reduces_cd_star_proj_inv :
//!   par_reduces_cd_star env (KExpr.proj s i sub) t -> ProjRedWitness env s i sub t
//! ```
//!
//! i.e. anything reachable from a projection is a projection **at the same
//! struct name and field index**, whose subject is reachable from the original
//! subject.
//!
//! ## Why this is not as hard as it looked
//!
//! `proj` was flagged as the difficult case because, unlike `lit` and `bvar`,
//! it genuinely reduces — inside its subject. But the ι and δ arms turn out to
//! be absurd here for exactly the same reason they are for the rigid forms:
//! `kapp_fn` on a projection returns the projection itself (a `proj` node is
//! not an application spine), so `kexpr_const_name (kapp_fn (proj s i sub))` is
//! `none` definitionally and the head-none absurdity lemmas apply with
//! `Eq.refl` as the premise. A projection cannot δ-unfold or ι-fire *at its
//! own head*.
//!
//! So the only substantive arm is `proj` itself, and the extra work over the
//! rigid cases is one witness inductive for the existential — the spec has no
//! `Exists` and no `Sigma`, so every existential is a single-constructor
//! inductive (the `par_strips_witness_cd_star` idiom).
//!
//! ## Universe note
//!
//! The goals here are `ProjRedWitness …`, which is `Type`-valued, so this
//! module uses `kexpr_discr_t` and `iota_step_head_none_absurd_type` —
//! the opposite variants from `kexpr_discr.rs`, whose goals were `Eq`s.
//! Having built both halves of each pair earlier, this is now a choice rather
//! than a discovery.
//!
//! `DerivedProved` throughout, empty axiom closures; the witness is
//! census-neutral.

use crate::spec::core_spec::kexpr_discr::CD_STRUCTURAL_ARMS;
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// Index of the `proj` arm within `CD_STRUCTURAL_ARMS` — the one substantive
/// case, skipped when generating the absurd arms.
const PROJ_ARM_INDEX: usize = 7;

impl Specification {
    /// `proj` head rigidity, single-step and multi-step.
    pub(super) fn add_proj_rigidity(&mut self) -> Result<(), SpecError> {
        self.add_proj_red_witness()?;
        self.add_proj_inv_step()?;
        self.add_proj_inv_star()?;
        Ok(())
    }

    fn add_proj_red_witness(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive ProjRedWitness (env : RedEnv) (s : Name) (i : Nat) (sub : KExpr) \
             (t : KExpr) : Type\n\
             | mk : forall (sub2 : KExpr), Eq KExpr t (KExpr.proj s i sub2) -> \
             par_reduces_cd_star env sub sub2 -> ProjRedWitness env s i sub t",
            "ProjRedWitness env s i sub t packages the conclusion of proj head rigidity: t IS a \
             projection at the SAME struct name and field index, and its subject is reachable \
             from sub. The spec has no Exists and no Sigma, so this existential is a \
             single-constructor witness inductive — the par_strips_witness_cd_star idiom. \
             Census-neutral.",
        )?;
        Ok(())
    }

    /// The eight non-`proj` `par_reduces_cd` arms are absurd against a `proj`
    /// source; `refl` and `proj` are the survivors.
    fn proj_inv_arms(target_kind: &str) -> String {
        let goal = |tgt: &str| format!("(ProjRedWitness env s i sub {tgt})");

        // refl: nothing moved, so the subject reaches itself.
        let mut arms = format!(
            "(fun (e0 : KExpr) (s : Name) (i : Nat) (sub : KExpr) \
             (heq : Eq KExpr e0 (KExpr.proj s i sub)) => \
             ProjRedWitness.mk env s i sub e0 sub heq (par_reduces_cd_star.refl env sub)) "
        );

        let absurd = |idx: usize| {
            let (payload_binders, rec_pairs, src, tgt) = CD_STRUCTURAL_ARMS[idx];
            let mut proofs = String::new();
            let mut ihs = String::new();
            for (from, to) in rec_pairs {
                proofs.push_str(&format!("(_ : par_reduces_cd env {from} {to}) "));
                ihs.push_str(&format!(
                    "(_ : forall (s : Name) (i : Nat) (sub : KExpr), \
                     Eq KExpr {from} (KExpr.proj s i sub) -> \
                     {g}) ",
                    g = goal(to)
                ));
            }
            format!(
                "(fun {payload_binders} {proofs}{ihs}(s : Name) (i : Nat) (sub : KExpr) \
                 (heq : Eq KExpr {src} (KExpr.proj s i sub)) => \
                 kexpr_discr_t {g} {src} (KExpr.proj s i sub) heq \
                 (Eq.refl Bool Bool.false)) ",
                g = goal(tgt)
            )
        };

        // Declaration order: refl beta app lam pi forall_ let_ iota delta
        // let_cong proj. iota and delta sit at 8 and 9, BEFORE let_cong.
        for idx in 0..6 {
            arms.push_str(&absurd(idx));
        }

        // iota / delta: a projection is not an application spine, so
        // kexpr_const_name (kapp_fn (proj s i sub)) is none definitionally and
        // neither can fire at the head.
        for (ctor, envsel, lemma, var) in [
            (
                "iota",
                "red_rec env",
                "iota_step_head_none_absurd_type",
                "ie",
            ),
            (
                "delta",
                "red_def env",
                "delta_step_head_none_absurd_type",
                "de",
            ),
        ] {
            let _ = ctor;
            arms.push_str(&format!(
                "(fun ({var} : KExpr) ({var}2 : KExpr) \
                 (hst : {ctor}_step ({envsel}) {var} {var}2) \
                 (s : Name) (i : Nat) (sub : KExpr) \
                 (heq : Eq KExpr {var} (KExpr.proj s i sub)) => \
                 {lemma} ({envsel}) (KExpr.proj s i sub) {var}2 \
                 {g} (Eq.refl (OptionType Name) (OptionType.none Name)) \
                 (Eq.substType KExpr \
                 (fun (z : KExpr) => {ctor}_step ({envsel}) z {var}2) \
                 {var} (KExpr.proj s i sub) heq hst)) ",
                g = goal(&format!("{var}2"))
            ));
        }

        arms.push_str(&absurd(6)); // let_cong

        // proj: THE substantive arm. Recover the name / index / subject
        // equalities from the in-tree projection injectivity, then rebuild.
        arms.push_str(&format!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub2 : KExpr) \
             (hp : par_reduces_cd env psub psub2) \
             (_ih : forall (s : Name) (i : Nat) (sub : KExpr), \
             Eq KExpr psub (KExpr.proj s i sub) -> \
             ProjRedWitness env s i sub psub2) \
             (s : Name) (i : Nat) (sub : KExpr) \
             (heq : Eq KExpr (KExpr.proj ps pidx psub) (KExpr.proj s i sub)) => \
             (fun (hn : Eq Name ps s) (hi : Eq Nat pidx i) (hs : Eq KExpr psub sub) => \
             ProjRedWitness.mk env s i sub (KExpr.proj ps pidx psub2) psub2 \
             (Eq.trans KExpr (KExpr.proj ps pidx psub2) (KExpr.proj s pidx psub2) \
             (KExpr.proj s i psub2) \
             (Eq.cong Name KExpr (fun (w : Name) => KExpr.proj w pidx psub2) ps s hn) \
             (Eq.cong Nat KExpr (fun (w : Nat) => KExpr.proj s w psub2) pidx i hi)) \
             (par_reduces_cd_star.step env sub psub2 psub2 \
             (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd env z psub2) \
             psub sub hs hp) (par_reduces_cd_star.refl env psub2))) \
             (proj_inj_name ps pidx psub s i sub heq) \
             (proj_inj_idx ps pidx psub s i sub heq) \
             (proj_inj_sub ps pidx psub s i sub heq)) "
        ));

        let _ = target_kind;
        arms
    }

    fn add_proj_inv_step(&mut self) -> Result<(), SpecError> {
        let arms = Self::proj_inv_arms("step");
        self.add_recursive_def(
            &format!(
                "def par_reduces_cd_proj_inv (env : RedEnv) (p : KExpr) (q : KExpr) \
                 (h : par_reduces_cd env p q) : \
                 forall (s : Name) (i : Nat) (sub : KExpr), \
                 Eq KExpr p (KExpr.proj s i sub) -> ProjRedWitness env s i sub q := \
                 par_reduces_cd.rec env \
                 (fun (pp : KExpr) (qq : KExpr) (_h : par_reduces_cd env pp qq) => \
                 forall (s : Name) (i : Nat) (sub : KExpr), \
                 Eq KExpr pp (KExpr.proj s i sub) -> ProjRedWitness env s i sub qq) \
                 {arms}p q h"
            ),
            "par_reduces_cd_proj_inv: SINGLE-STEP proj head rigidity — one parallel step out of a \
             projection lands on a projection at the SAME struct name and field index, with the \
             subject stepped. proj was expected to be the hard head because, unlike lit and bvar, \
             it genuinely reduces; but its iota and delta arms are absurd for exactly the same \
             reason as theirs — kapp_fn on a projection returns the projection itself, so \
             kexpr_const_name is none definitionally and a projection cannot fire at its own \
             head. The only substantive arm is proj, closed by the in-tree projection \
             injectivity (proj_inj_name / _idx / _sub). DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_proj_inv_star(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def par_reduces_cd_star_proj_inv (env : RedEnv) (p : KExpr) (t : KExpr) \
             (h : par_reduces_cd_star env p t) : \
             forall (s : Name) (i : Nat) (sub : KExpr), \
             Eq KExpr p (KExpr.proj s i sub) -> ProjRedWitness env s i sub t := \
             par_reduces_cd_star.rec env \
             (fun (pp : KExpr) (qq : KExpr) (_h : par_reduces_cd_star env pp qq) => \
             forall (s : Name) (i : Nat) (sub : KExpr), \
             Eq KExpr pp (KExpr.proj s i sub) -> ProjRedWitness env s i sub qq) \
             (fun (e0 : KExpr) (s : Name) (i : Nat) (sub : KExpr) \
             (heq : Eq KExpr e0 (KExpr.proj s i sub)) => \
             ProjRedWitness.mk env s i sub e0 sub heq (par_reduces_cd_star.refl env sub)) \
             (fun (e0 : KExpr) (e1 : KExpr) (e2 : KExpr) \
             (hstep : par_reduces_cd env e0 e1) \
             (_hstar : par_reduces_cd_star env e1 e2) \
             (ih : forall (s : Name) (i : Nat) (sub : KExpr), \
             Eq KExpr e1 (KExpr.proj s i sub) -> ProjRedWitness env s i sub e2) \
             (s : Name) (i : Nat) (sub : KExpr) \
             (heq : Eq KExpr e0 (KExpr.proj s i sub)) => \
             ProjRedWitness.rec env s i sub e1 \
             (fun (_w : ProjRedWitness env s i sub e1) => ProjRedWitness env s i sub e2) \
             (fun (sub1 : KExpr) (he1 : Eq KExpr e1 (KExpr.proj s i sub1)) \
             (hr1 : par_reduces_cd_star env sub sub1) => \
             ProjRedWitness.rec env s i sub1 e2 \
             (fun (_w2 : ProjRedWitness env s i sub1 e2) => ProjRedWitness env s i sub e2) \
             (fun (sub2 : KExpr) (he2 : Eq KExpr e2 (KExpr.proj s i sub2)) \
             (hr2 : par_reduces_cd_star env sub1 sub2) => \
             ProjRedWitness.mk env s i sub e2 sub2 he2 \
             (par_reduces_cd_star_trans env sub sub1 sub2 hr1 hr2)) \
             (ih s i sub1 he1)) \
             (par_reduces_cd_proj_inv env e0 e1 hstep s i sub heq)) \
             p t h",
            "par_reduces_cd_star_proj_inv: MULTI-STEP proj head rigidity — anything reachable \
             from a projection is a projection at the same struct name and field index, with a \
             reachable subject. Induction on the closure: each step is held in place by the \
             single-step inversion, the two witnesses are unpacked, and the subject reductions \
             compose with par_reduces_cd_star_trans. This completes the head-rigidity family the \
             completeness capstone needs — sort / lam / pi / neutral-app / dead-const were \
             already in tree, lit and bvar landed with the discrimination brick, and proj is the \
             last. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Eleven minor premises, one per `par_reduces_cd` constructor.
    #[test]
    fn test_proj_inv_arms_has_eleven_minor_premises() {
        let arms = Specification::proj_inv_arms("step");
        let minors = arms.matches("(fun ").count()
            - arms.matches("(fun (z : KExpr)").count()
            - arms.matches("(fun (w : Name)").count()
            - arms.matches("(fun (w : Nat)").count()
            - arms.matches("(fun (hn :").count();
        assert_eq!(minors, 11, "expected 11 minor premises, got {minors}");
    }

    /// Declaration order: iota and delta at positions 8 and 9, before
    /// `let_cong` and the substantive `proj` arm.
    #[test]
    fn test_proj_inv_arms_declaration_order() {
        let arms = Specification::proj_inv_arms("step");
        let landmarks = [
            "(fun (e0 : KExpr)",
            "(KExpr.app (KExpr.lam bA bbody) barg)",
            "(KExpr.app af aa)",
            "(KExpr.lam lty lbody)",
            "(KExpr.pi pdom pbody)",
            "(KExpr.forall_ qdom qbody)",
            "(KExpr.let_ zty zval zbody)",
            "iota_step_head_none_absurd_type",
            "delta_step_head_none_absurd_type",
            "(KExpr.let_ cty cval cbody)",
            "proj_inj_name",
        ];
        let mut cursor = 0usize;
        for (position, mark) in landmarks.iter().enumerate() {
            let found = arms[cursor..].find(mark).unwrap_or_else(|| {
                panic!("minor premise {position} ({mark}) missing/out of order")
            });
            cursor += found + mark.len();
        }
    }

    /// The goals here are `ProjRedWitness`, which is `Type`-valued, so the
    /// Type-CPS eliminators are required. Using the Prop variants — correct in
    /// `kexpr_discr.rs`, whose goals were `Eq`s — would be a universe conflict.
    #[test]
    fn test_proj_inv_arms_use_type_valued_eliminators() {
        let arms = Specification::proj_inv_arms("step");
        assert!(arms.contains("kexpr_discr_t "), "goals are Type-valued");
        assert_eq!(
            arms.matches("kexpr_discr_p ").count(),
            0,
            "kexpr_discr_p is Prop-valued and cannot discharge a ProjRedWitness goal"
        );
        assert_eq!(arms.matches("_absurd_type ").count(), 2);
        assert_eq!(
            arms.matches("_absurd (").count(),
            0,
            "the Prop-CPS head-none lemmas cannot discharge a Type-valued goal"
        );
    }

    /// Every absurd arm must discriminate into its own TARGET equation.
    #[test]
    fn test_proj_inv_arms_discriminate_into_the_target() {
        let arms = Specification::proj_inv_arms("step");
        for (idx, (_, _, _, tgt)) in CD_STRUCTURAL_ARMS.iter().enumerate() {
            if idx == PROJ_ARM_INDEX {
                continue; // the substantive arm, not an absurdity
            }
            assert!(
                arms.contains(&format!("kexpr_discr_t (ProjRedWitness env s i sub {tgt})")),
                "arm with target {tgt} must discriminate into its target's witness goal"
            );
        }
    }

    /// The substantive arm must actually use all three projection injectivity
    /// lemmas — dropping any one would leave a name, index or subject
    /// unconstrained.
    #[test]
    fn test_proj_inv_substantive_arm_uses_all_three_injectivities() {
        let arms = Specification::proj_inv_arms("step");
        for lemma in ["proj_inj_name", "proj_inj_idx", "proj_inj_sub"] {
            assert!(
                arms.contains(lemma),
                "substantive proj arm must use {lemma}"
            );
        }
    }

    #[test]
    fn test_proj_inv_arms_parens_balanced() {
        let arms = Specification::proj_inv_arms("step");
        let mut depth: i64 = 0;
        for ch in arms.chars() {
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
