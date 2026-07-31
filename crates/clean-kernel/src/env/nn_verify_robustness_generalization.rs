// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C010: Robustness-generalization bounds from verification certificates.
//!
//! Original mathematics connecting neural network verification certificates to
//! learning theory generalization bounds. The key insight: tighter verification
//! certificates (higher certified robustness radius) imply smaller local
//! Lipschitz constants, which bound Rademacher complexity, which gives
//! PAC-learning generalization guarantees.
//!
//! Proof chain:
//! 1. Certificate => local Lipschitz (from IBP/CROWN bounds)
//! 2. Lipschitz => Rademacher complexity bound (classical)
//! 3. Rademacher => generalization bound (PAC-learning)
//! 4. Certificate => generalization bound (composition of 1-3)
//! 5. Tighter certificate => better generalization (monotonicity)
//!
//! Theorem type builders live in `nn_verify_robustness_generalization_defs`.
//!
//! Part of #3262.

#[cfg(test)]
use super::nn_verify_robustness_generalization_defs;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for robustness-generalization formalization.
#[cfg(test)]
pub(super) struct RobustnessGenConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_div: Expr,
    pub(super) rat_one: Expr,
    pub(super) rat_zero: Expr,
    pub(super) le_le: Expr,
    pub(super) lt_lt: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) inst_lt_rat: Expr,
    pub(super) and: Expr,
    pub(super) nat_to_rat: Expr,
    pub(super) sqrt: Expr,
    pub(super) ln: Expr,
    pub(super) certified_robust: Expr,
    pub(super) lipschitz_local: Expr,
    pub(super) rademacher_complexity: Expr,
    pub(super) generalization_gap: Expr,
    pub(super) gen_bound: Expr,
}

#[cfg(test)]
impl RobustnessGenConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            lt_lt: Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            inst_lt_rat: Expr::const_(Name::from_string("instLTRat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            nat_to_rat: Expr::const_(
                Name::from_string("NNVerify.RobustnessGen.nat_to_rat"),
                vec![],
            ),
            sqrt: Expr::const_(Name::from_string("NNVerify.RobustnessGen.sqrt"), vec![]),
            ln: Expr::const_(Name::from_string("NNVerify.RobustnessGen.ln"), vec![]),
            certified_robust: Expr::const_(
                Name::from_string("NNVerify.RobustnessGen.certified_robust"),
                vec![],
            ),
            lipschitz_local: Expr::const_(
                Name::from_string("NNVerify.RobustnessGen.lipschitz_local"),
                vec![],
            ),
            rademacher_complexity: Expr::const_(
                Name::from_string("NNVerify.RobustnessGen.rademacher_complexity"),
                vec![],
            ),
            generalization_gap: Expr::const_(
                Name::from_string("NNVerify.RobustnessGen.generalization_gap"),
                vec![],
            ),
            gen_bound: Expr::const_(
                Name::from_string("NNVerify.RobustnessGen.gen_bound"),
                vec![],
            ),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    #[cfg(test)]
    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `LT.lt @Rat instLTRat lhs rhs`.
    #[cfg(test)]
    pub(super) fn rat_lt(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.lt_lt.clone(), self.rat.clone()),
                    self.inst_lt_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `Rat.add a b`.
    #[cfg(test)]
    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    /// Build `Rat.mul a b`.
    #[cfg(test)]
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    /// Build `Rat.div a b`.
    #[cfg(test)]
    pub(super) fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_div.clone(), a), b)
    }

    /// Build `NNVerify.NNVec n`.
    #[cfg(test)]
    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    /// Function type `NNVerify.NNVec n -> NNVerify.NNVec n`.
    #[cfg(test)]
    pub(super) fn endo_ty(&self, n: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.vec_of(n.clone()),
            self.vec_of(n.clone()),
        )
    }

    /// `Rat.add Rat.one Rat.one` (the constant 2).
    #[cfg(test)]
    pub(super) fn two(&self) -> Expr {
        self.add(self.rat_one.clone(), self.rat_one.clone())
    }
}

// =============================================================================
// Environment impl
// =============================================================================

#[cfg(test)]
impl Environment {
    /// Initialize C010 (robustness-generalization bounds) declarations.
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec
    /// - `init_rat()` / `init_rat_ord()` for Rat arithmetic and ordering
    /// - `init_eq()` for equality, `init_and()` for conjunction
    #[cfg(test)]
    pub(crate) fn init_nn_verify_robustness_gen(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.RobustnessGen.certified_robust",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_eq()?;
        self.init_and()?;
        self.init_true_false()?;

        let c = RobustnessGenConsts::new();

        // Definitions
        self.register_rg_certified_robust(&c)?;
        self.register_rg_lipschitz_local(&c)?;
        self.register_rg_nat_to_rat(&c)?;
        self.register_rg_sqrt(&c)?;
        self.register_rg_ln(&c)?;
        self.register_rg_rademacher_complexity(&c)?;
        self.register_rg_generalization_gap(&c)?;
        self.register_rg_gen_bound(&c)?;

        // Theorems
        self.register_rg_certified_implies_lipschitz_local(&c)?;
        self.register_rg_lipschitz_rademacher_bound(&c)?;
        self.register_rg_rademacher_gen_bound(&c)?;
        self.register_rg_certificate_gen_bound(&c)?;
        self.register_rg_tighter_cert_better_gen(&c)?;

        Ok(())
    }

    // Opaque definition register functions (register_rg_certified_robust through
    // register_rg_gen_bound) are in nn_verify_robustness_generalization_values.rs

    // -- Theorems (5 total) --------------------------------------------------
    //
    // (1) `certified_implies_lipschitz_local` (#3578 Branch A demasquerade):
    //     `Declaration::Axiom` with honest Pi type. Previously (#3463) a
    //     `Declaration::Theorem` carrying the `True.intro`-closed proof term
    //     `fun d f eps _h1 _h2 => True.intro` that type-checked only because
    //     `lipschitz_local` was simultaneously promoted to a reducible
    //     Definition with body `fun _ _ _ _ => True` — MASQUERADE per
    //     `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M2
    //     (argument-discarding carrier) + M4 (inner-proof = `True.intro`).
    //     Branch A demotion reverts `lipschitz_local` to `Declaration::Opaque`
    //     (closes delta-reduction path) AND demotes
    //     `certified_implies_lipschitz_local` to `Declaration::Axiom` (drops
    //     the vacuous proof term). The companion `_axiom` Opaque is removed
    //     entirely — the primary declaration is now itself the axiom.
    //     Sibling demotions: #3568 C007 `merge_sound_helper`, #3566 C011
    //     softmax family, #3567 C028 `sos_existence`.
    //
    // (2)-(5) Four PAC-generalization bounds (#3571 Branch A): honest
    //     `Declaration::Axiom` + `Declaration::Theorem` wrapper referencing
    //     the axiom. This replaces the prior sorry-Opaque + Theorem pattern
    //     (#3381) with a correctly-attributed axiom dependency. The
    //     axiom_deps closure for each Theorem now returns {_axiom}, so
    //     `proof_mechanism` for C010 is `masquerade_demoted` (5 axioms total
    //     after #3578: 1 honest bare axiom + 4 axiom-wrappers; the former
    //     `certified_implies_lipschitz_local_axiom` Opaque is deleted).

    /// `NNVerify.RobustnessGen.certified_implies_lipschitz_local`:
    /// `forall d f eps, certified_robust d f eps -> 0 < eps ->
    ///    lipschitz_local d f eps (1/eps)`.
    ///
    /// **#3578 Branch A demasquerade (2026-04-20).** Demoted from
    /// `Declaration::Theorem` (with #3463 `True.intro`-closed proof term
    /// `fun d f eps _h1 _h2 => True.intro`) to `Declaration::Axiom`
    /// (stored value = None). Per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M2 + M4,
    /// the #3463 proof was a MASQUERADE: it type-checked only because
    /// `lipschitz_local` was simultaneously promoted to a reducible
    /// Definition with body `fun _ _ _ _ => True`, collapsing the
    /// theorem's conclusion `lipschitz_local d f eps (1/eps)` to `True`
    /// under delta-reduction. The five lambda binders (`d`, `f`, `eps`,
    /// `_h1`, `_h2`) were never inspected — the proof discarded its
    /// hypotheses and carried zero mathematical content beyond the
    /// alias collapse. design doc Proof Soundness Rules forbid calling
    /// this a "constructive proof."
    ///
    /// Branch A demotion:
    /// 1. `lipschitz_local` reverted to `Declaration::Opaque` (closes
    ///    delta-reduction path — see `register_rg_lipschitz_local`).
    /// 2. `certified_implies_lipschitz_local` demoted to
    ///    `Declaration::Axiom` with the original Pi type preserved.
    /// 3. Backing `_axiom` Opaque removed entirely (the primary
    ///    declaration is now itself the axiom — no auxiliary wrapper).
    /// 4. Constructive-proof builder
    ///    `build_certified_implies_lipschitz_local_constructive_proof`
    ///    deleted.
    ///
    /// Sibling demotions: #3568 C007 `merge_sound_helper`, #3566 C011
    /// softmax family, #3567 C028 `sos_existence`. Branch B (faithful
    /// Lipschitz predicate over NNVec + `Rat.abs` with bound `1/eps`) is
    /// tracked under epic #3470 and requires the Rat ordered-field
    /// infrastructure (`designs/2026-04-20-rat-ordered-field-constructive.md`).
    ///
    /// **SOUNDNESS:** `NNVerify.RobustnessGen.certified_implies_lipschitz_local`
    /// is now a domain-specific `Declaration::Axiom`. It claims that
    /// certified robustness radius `eps` implies the vacuous placeholder
    /// predicate `lipschitz_local d f eps (1/eps)` — which is trivially
    /// inhabited by `True.intro` UNTIL `lipschitz_local`'s body is
    /// replaced with a faithful Lipschitz predicate. Axiom retirement
    /// requires Branch B (faithful `lipschitz_local`) plus a genuine
    /// certificate-to-Lipschitz proof.
    #[cfg(test)]
    fn register_rg_certified_implies_lipschitz_local(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        let thm_type =
            nn_verify_robustness_generalization_defs::build_certified_implies_lipschitz_local_type(
                c,
            );
        // #3578 Branch A: honest Declaration::Axiom (no stored value). The
        // prior #3463 `True.intro`-closed proof term is removed along with
        // the backing `_axiom` Opaque — the primary declaration is itself
        // the axiom. Future Branch B work will replace this with a real
        // proof once `lipschitz_local` carries a faithful predicate.
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.RobustnessGen.certified_implies_lipschitz_local"),
            level_params: vec![],
            type_: thm_type,
        })
    }

    // -- Branch A: Honest Declaration::Axiom (#3571) -------------------------
    //
    // The four PAC-generalization bounds below are registered as honest
    // `Declaration::Axiom` values — NOT as sorry-Opaque + Theorem wrappers,
    // and NOT as True-placeholder masquerades. The conclusion of each is a
    // real `Rat.le lhs rhs` inequality that cannot currently be closed
    // constructively without PAC-learning infrastructure outside the kernel
    // (Rademacher complexity, empirical-process tail bounds, sqrt/ln
    // analytic inequalities). Issue #3571 mandates Branch A ("honest axiom")
    // over Branch B ("True.intro masquerade") because the task constraint
    // forbids masquerade.
    //
    // For name-compatibility with the prior sorry-Opaque + Theorem wrapper
    // pattern, we register BOTH names:
    //   - `<name>_axiom`   : Declaration::Axiom (the primitive posit)
    //   - `<name>`         : Declaration::Theorem whose value references the
    //                        axiom. `env.axiom_deps(<name>)` then correctly
    //                        returns `{<name>_axiom}` under transitive
    //                        closure — this is the intended, honest
    //                        proof_mechanism = `axiom_wrapper` semantics.
    //
    // SOUNDNESS: each `_axiom` is a domain-specific `Declaration::Axiom`.
    // Retiring it requires one of:
    //   (a) formalizing Rademacher complexity / PAC tail bounds in the
    //       kernel, or
    //   (b) importing Mathlib's `Real.rpow` / `MeasureTheory.Probability`
    //       machinery via the Tier-2 .olean bridge.
    // Both are out of scope for #3571.

    #[cfg(test)]
    fn register_rg_lipschitz_rademacher_bound(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        let thm_type =
            nn_verify_robustness_generalization_defs::build_lipschitz_rademacher_bound_type(c);
        // Honest Declaration::Axiom (#3571 Branch A). The conclusion is a
        // real Rat.le inequality backed by classical Rademacher-complexity
        // theory (L-Lipschitz class on R^d has Rademacher complexity
        // bounded by L*sqrt(d)/sqrt(m)); the kernel lacks the analytic
        // machinery to discharge it constructively.
        let axiom_name =
            Name::from_string("NNVerify.RobustnessGen.lipschitz_rademacher_bound_axiom");
        self.add_decl(Declaration::Axiom {
            name: axiom_name.clone(),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(axiom_name, vec![]);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.RobustnessGen.lipschitz_rademacher_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_rg_rademacher_gen_bound(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        let thm_type = nn_verify_robustness_generalization_defs::build_rademacher_gen_bound_type(c);
        // Honest Declaration::Axiom (#3571 Branch A). Standard PAC-learning
        // generalization bound via Rademacher complexity + McDiarmid's
        // inequality; kernel has no probabilistic reasoning primitives.
        let axiom_name = Name::from_string("NNVerify.RobustnessGen.rademacher_gen_bound_axiom");
        self.add_decl(Declaration::Axiom {
            name: axiom_name.clone(),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(axiom_name, vec![]);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.RobustnessGen.rademacher_gen_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_rg_certificate_gen_bound(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        let thm_type =
            nn_verify_robustness_generalization_defs::build_certificate_gen_bound_type(c);
        // Honest Declaration::Axiom (#3571 Branch A). Composes the
        // Rademacher + PAC generalization bounds via the
        // certificate => Lipschitz bridge; requires the two building-block
        // axioms plus algebraic manipulation beyond current reducibility.
        let axiom_name = Name::from_string("NNVerify.RobustnessGen.certificate_gen_bound_axiom");
        self.add_decl(Declaration::Axiom {
            name: axiom_name.clone(),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(axiom_name, vec![]);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.RobustnessGen.certificate_gen_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_rg_tighter_cert_better_gen(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        let thm_type =
            nn_verify_robustness_generalization_defs::build_tighter_cert_better_gen_type(c);
        // Honest Declaration::Axiom (#3571 Branch A). Monotonicity of the
        // gen_bound in `eps` follows from the 1/eps Rademacher factor;
        // requires ordered-field inequality manipulation and sqrt/ln
        // monotonicity lemmas not yet in the kernel.
        let axiom_name = Name::from_string("NNVerify.RobustnessGen.tighter_cert_better_gen_axiom");
        self.add_decl(Declaration::Axiom {
            name: axiom_name.clone(),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(axiom_name, vec![]);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.RobustnessGen.tighter_cert_better_gen"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
