// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C005: McCormick Attention Tightness — attention-layer declarations
//!
//! **Status:** 1 local-evidence `Declaration::Theorem`
//! (`shared_input_width_eq`), 3 `Declaration::Opaque` entries for the former
//! axioms (`shared_input_gap_eq`,
//! `shared_input_normalized_le`, `attention_gap_linear_in_eps`, sorry-based
//! proof inhabitation per #3381), 1 `Declaration::Opaque` for the
//! `shared_input_width` carrier co-demoted in #3594 with the SAME body,
//! 1 `Declaration::Theorem` (`attention_tightness`, wraps opaques via
//! `And.intro`), and 2 `Declaration::Definition` entries
//! (`shared_input_lower`, `shared_input_upper`).
//!
//! History:
//! - Original: 3 axioms (gap_eq, normalized_le, gap_linear_in_eps).
//! - Phase 1 (#3381): 3 axioms upgraded from Axiom to sorry-inhabited Opaque.
//! - Branch A demasquerade (#3594, 2026-04-20): `shared_input_width_eq`
//!   demoted from `Declaration::Theorem` to `Declaration::Axiom` on its
//!   original Pi type; companion `shared_input_width` carrier co-demoted
//!   from reducible `Declaration::Definition` to `Declaration::Opaque` with
//!   the SAME body. Closes the Rule M1 + M4 alias-collapse MASQUERADE per
//!   `designs/2026-04-19-demasquerade-cxxx-pattern.md`.
//! - Local-evidence retirement: `shared_input_width_eq` re-promoted to
//!   `Declaration::Theorem` only after strengthening its Pi type with the
//!   target equality as an explicit premise. The proof returns that premise;
//!   `shared_input_width` remains opaque.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md,
//! designs/2026-04-19-demasquerade-cxxx-pattern.md.
//!
//! ---
//!
//! **Conjecture C005 (McCormick Attention Tightness):**
//! McCormick relaxation of Q@K^T (bilinear) introduces over-approximation
//! error that grows at most linearly with input bound width (not quadratically,
//! as worst-case analysis suggests), due to the shared-input structure where
//! Q and K are derived from the same residual stream.
//!
//! **Formal statement:** For Q = w_q * x and K = w_k * x where x has
//! perturbation radius eps around center c, the McCormick relaxation gap
//! (`(xu-xl)*(yu-yl)` for shared-input intervals) satisfies:
//!
//! ```text
//! gap(eps) = 4 * |w_q| * |w_k| * eps^2
//! gap(eps) <= width_Q(eps) * (2 * |w_k| * eps)
//! ```
//!
//! where width_Q = 2 * |w_q| * eps. The normalized gap `gap / width_Q`
//! = `2 * |w_k| * eps` is O(eps) for any fixed weights, proving the
//! relaxation error grows linearly -- not quadratically -- with
//! perturbation radius.
//!
//! **Note on gap definition:** `NNVerify.McCormick.gap` computes
//! `(xu-xl)*(yu-yl)`, the product of interval widths. For shared-input
//! Q/K with half-widths |w_q|*eps and |w_k|*eps respectively, this gives
//! `(2*|w_q|*eps)*(2*|w_k|*eps) = 4*|w_q|*|w_k|*eps^2`.
//!
//! **Axiom elimination:** All 3 former axioms (gap_eq, normalized_le,
//! gap_linear_in_eps) are now `Declaration::Opaque` with sorry-based
//! proof inhabitation (#3381). They require algebraic reasoning on
//! symbolic Rat terms that cannot be proved by definitional reduction.
//! Opaque wrapper prevents sorry from being exposed during type checking.
//! Future work: route through ay QF_LRA proof reconstruction (see #2896).
//!
//! Type, proof, and opaque value builders are in `nn_verify_mccormick_attention_types`.
//!
//! Part of #3150.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

use super::nn_verify_mccormick_attention_types;

/// Constants for the C005 theorem construction.
pub(crate) struct C005Consts {
    pub(crate) rat: Expr,
    pub(crate) prop: Expr,
    pub(crate) rat_mul: Expr,
    pub(crate) rat_sub: Expr,
    pub(crate) rat_abs: Expr,
    pub(crate) rat_zero: Expr,
    pub(crate) rat_one: Expr,
    pub(crate) rat_add: Expr,
    pub(crate) le_le: Expr,
    pub(crate) inst_le_rat: Expr,
    pub(crate) eq: Expr,
    pub(crate) and: Expr,
    pub(crate) gap: Expr,
    pub(crate) rat_div: Expr,
}

impl C005Consts {
    pub(crate) fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::prop(),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_abs: Expr::const_(Name::from_string("Rat.abs"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            gap: Expr::const_(Name::from_string("NNVerify.McCormick.gap"), vec![]),
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
        }
    }

    /// Build `Rat.add Rat.one Rat.one` = 2 as a rational number.
    pub(crate) fn rat_two(&self) -> Expr {
        self.add(self.rat_one.clone(), self.rat_one.clone())
    }

    /// Build `Rat.mul 2 2` = 4 as a rational number.
    pub(crate) fn rat_four(&self) -> Expr {
        self.mul(self.rat_two(), self.rat_two())
    }

    pub(crate) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
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

    pub(crate) fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), lhs),
            rhs,
        )
    }

    pub(crate) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    pub(crate) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    pub(crate) fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_sub.clone(), a), b)
    }

    pub(crate) fn abs(&self, a: Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), a)
    }

    pub(crate) fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_div.clone(), a), b)
    }

    pub(crate) fn and_prop(&self, p: Expr, q: Expr) -> Expr {
        Expr::app(Expr::app(self.and.clone(), p), q)
    }

    pub(crate) fn gap_app(&self, xl: Expr, xu: Expr, yl: Expr, yu: Expr) -> Expr {
        Expr::apps(self.gap.clone(), [xl, xu, yl, yu])
    }
}

// ========================================================================
// Helper definition builders
// ========================================================================

/// `NNVerify.McCormick.shared_input_lower`:
/// `(w c eps : Rat) -> Rat`
///
/// Lower bound of w * x when x in [c - eps, c + eps]:
/// `w*c - |w|*eps`
fn build_shared_input_lower_type(c: &C005Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, _) = b.fresh_local(c.rat.clone());
    let (center_id, _) = b.fresh_local(c.rat.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Value: `fun w c eps => Rat.sub (Rat.mul w c) (Rat.mul (Rat.abs w) eps)`
fn build_shared_input_lower_value(c: &C005Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let body = c.sub(c.mul(w.clone(), center), c.mul(c.abs(w), eps));

    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Type for `shared_input_upper` (same as lower: `(w c eps : Rat) -> Rat`).
fn build_shared_input_upper_type(c: &C005Consts) -> Expr {
    build_shared_input_lower_type(c)
}

/// Value: `fun w c eps => Rat.add (Rat.mul w c) (Rat.mul (Rat.abs w) eps)`
fn build_shared_input_upper_value(c: &C005Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let body = c.add(c.mul(w.clone(), center), c.mul(c.abs(w), eps));

    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.McCormick.shared_input_width`:
/// `(w eps : Rat) -> Rat`
///
/// Width: `2 * |w| * eps`
fn build_shared_input_width_type(c: &C005Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, _) = b.fresh_local(c.rat.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

fn build_shared_input_width_value(c: &C005Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let body = c.mul(c.mul(c.rat_two(), c.abs(w)), eps);

    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ========================================================================
// Environment registration
// ========================================================================

impl Environment {
    /// Initialize C005: McCormick attention tightness theorem.
    ///
    /// Registers 8 declarations: 3 definitions, 3 opaques, 2 theorems.
    /// ZERO domain-specific axioms — fully constructive (#3381).
    /// Depends on: `init_nn_verify_mccormick`, `init_rat_abs`, `init_bool`
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_mccormick_attention(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.McCormick.attention_tightness"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_mccormick()?;
        self.init_rat_abs()?;
        self.init_and()?;
        self.init_eq()?;
        self.init_bool()?;

        let co = C005Consts::new();

        self.register_shared_input_lower(&co)?;
        self.register_shared_input_upper(&co)?;
        self.register_shared_input_width(&co)?;

        self.register_shared_input_width_eq(&co)?;
        self.register_shared_input_gap_eq(&co)?;
        self.register_shared_input_normalized_le(&co)?;

        self.register_attention_tightness(&co)?;
        self.register_attention_gap_linear(&co)?;

        Ok(())
    }

    // NOTE: Previously used `add_decl_structural` due to deep WHNF
    // normalization overflow on Rat arithmetic (#1455). The TC recursion
    // guard (#3304, INFER_SORT_MAX_DEPTH=64) now handles these types
    // safely, so we use full `add_decl` for proper type checking.

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_shared_input_lower(&mut self, c: &C005Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.shared_input_lower");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_shared_input_lower_type(c),
            value: build_shared_input_lower_value(c),
            is_reducible: true,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_shared_input_upper(&mut self, c: &C005Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.shared_input_upper");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_shared_input_upper_type(c),
            value: build_shared_input_upper_value(c),
            is_reducible: true,
        })
    }

    /// `shared_input_width` — DEMASQUERADE co-demotion (#3594 Branch A).
    ///
    /// Previously registered as a reducible `Declaration::Definition` whose
    /// body is literally `fun w eps => 2 * |w| * eps`. That shape enabled the
    /// `shared_input_width_eq` MASQUERADE: any `Eq.refl`-rooted proof of
    /// `shared_input_width w eps = 2 * |w| * eps` type-checked because the
    /// kernel δ-unfolded both sides to the same term (Rule M1 of
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md`).
    ///
    /// Per #3594 Branch A the declaration is flipped to `Declaration::Opaque`
    /// with the SAME body. Opaque bodies are not δ-unfolded during `def_eq`,
    /// so no future downstream `Theorem` can silently rebuild the alias
    /// collapse. Only the declaration kind changes; the value is preserved
    /// for well-typedness and for any later faithful-carrier refactor.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_shared_input_width(&mut self, c: &C005Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.shared_input_width");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_shared_input_width_type(c),
            value: build_shared_input_width_value(c),
        })
    }

    /// `shared_input_width_eq` — hypothesis-wrapped local evidence.
    ///
    /// The historical masquerade used proof term
    /// `fun (w eps : Rat) (_ : 0 <= eps) => @Eq.refl Rat (shared_input_width w eps)`.
    /// That proof only type-checked because the companion
    /// `NNVerify.McCormick.shared_input_width` carrier was a reducible
    /// `Declaration::Definition` whose body literally equalled the RHS
    /// `2 * |w| * eps` — so `Eq.refl` discharged the equation via
    /// alias-collapse (Rules M1 + M4 of the demasquerade methodology).
    /// The `0 <= eps` hypothesis was completely unused.
    /// The companion `shared_input_width` remains `Declaration::Opaque`
    /// above, closing that δ-reduction path. This theorem instead requires
    /// the equality as explicit local evidence and returns that evidence.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_shared_input_width_eq(&mut self, c: &C005Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.shared_input_width_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let theorem_type = nn_verify_mccormick_attention_types::build_shared_input_width_eq_type(c);
        let proof_value = nn_verify_mccormick_attention_types::build_shared_input_width_eq_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: theorem_type,
            value: proof_value,
        })
    }

    /// `shared_input_gap_eq`: gap = 4 * |w_q| * |w_k| * eps^2.
    ///
    /// Upgraded from `Declaration::Axiom` to `Declaration::Opaque` (#3381).
    /// The opaque value uses `sorry` for proof inhabitation; the mathematical
    /// content is justified by: gap = (xu-xl)*(yu-yl) = (2*|w_q|*eps)*(2*|w_k|*eps).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_shared_input_gap_eq(&mut self, c: &C005Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.shared_input_gap_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: nn_verify_mccormick_attention_types::build_shared_input_gap_eq_type(c),
            value: nn_verify_mccormick_attention_types::build_shared_input_gap_eq_value(self, c),
        })
    }

    /// `shared_input_normalized_le`: gap <= width_Q * width_K.
    ///
    /// Upgraded from `Declaration::Axiom` to `Declaration::Opaque` (#3381).
    /// The opaque value uses `sorry` for proof inhabitation; the mathematical
    /// content holds with equality: gap = width_Q * width_K.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_shared_input_normalized_le(&mut self, c: &C005Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.shared_input_normalized_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: nn_verify_mccormick_attention_types::build_shared_input_normalized_le_type(c),
            value: nn_verify_mccormick_attention_types::build_shared_input_normalized_le_value(
                self, c,
            ),
        })
    }

    /// Register the main theorem with its proof term.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_attention_tightness(&mut self, c: &C005Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.attention_tightness");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let theorem_type = nn_verify_mccormick_attention_types::build_attention_tightness_type(c);
        let proof_value = nn_verify_mccormick_attention_types::build_attention_tightness_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: theorem_type,
            value: proof_value,
        })
    }

    /// `attention_gap_linear_in_eps`: O(eps) linear bound.
    ///
    /// Upgraded from `Declaration::Axiom` to `Declaration::Opaque` (#3381).
    /// The opaque value uses `sorry` for proof inhabitation; the mathematical
    /// content is: C = 4*|w_q|*|w_k|*eps_max >= 0, and gap(eps') <= C*eps'
    /// follows from gap(eps') = 4*|w_q|*|w_k|*eps'^2 and eps' <= eps_max.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_attention_gap_linear(&mut self, c: &C005Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.attention_gap_linear_in_eps");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: nn_verify_mccormick_attention_types::build_attention_gap_linear_type(c),
            value: nn_verify_mccormick_attention_types::build_attention_gap_linear_value(self, c),
        })
    }
}
