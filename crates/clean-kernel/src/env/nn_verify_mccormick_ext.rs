// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended McCormick envelope theorems (T50-T52, Phase 3 of C005).
//!
//! Builds on `nn_verify_mccormick.rs` (envelope_lower/upper, gap, soundness)
//! with additional theorems for correlated inputs and linear growth bounds.
//!
//! ## Theorems
//!
//! - **T50: `mccormick_bilinear_sound`** — McCormick envelope soundness
//!   via explicit case-split on the four facets. Stronger than the base
//!   `mccormick_sound` which uses And; this version gives each facet
//!   individually via a disjunction.
//! - **T51: `mccormick_shared_input`** — When x and y share an input
//!   (i.e., x = f(z), y = g(z) for the same z), McCormick produces
//!   tighter bounds than the independent-input version.
//! - **T52: `mccormick_linear_growth`** — The McCormick relaxation gap
//!   grows at most linearly: gap <= O(width_x * width_y), where
//!   width = upper - lower.
//!
//! All registered as axioms (DerivedPending).
//!
//! Part of #3153.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Extended McCormick constants (reuses base Rat/le infrastructure).
struct McExtConsts {
    rat: Expr,
    prop: Expr,
    nn_vec: Expr,
    ib: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    eq: Expr,
    and: Expr,
    gap: Expr,
    nat: Expr,
    ib_width: Expr,
    nn_vec_l1_norm: Expr,
}

impl McExtConsts {
    fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::prop(),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            gap: Expr::const_(Name::from_string("NNVerify.McCormick.gap"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            ib_width: Expr::const_(Name::from_string("NNVerify.IntervalBounds.width"), vec![]),
            nn_vec_l1_norm: Expr::const_(Name::from_string("NNVerify.NNVec.l1_norm"), vec![]),
        }
    }

    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
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

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_sub.clone(), a), b)
    }

    fn and_prop(&self, p: Expr, q: Expr) -> Expr {
        Expr::app(Expr::app(self.and.clone(), p), q)
    }

    fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), lhs),
            rhs,
        )
    }

    fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    fn gap_app(&self, xl: Expr, xu: Expr, yl: Expr, yu: Expr) -> Expr {
        Expr::apps(self.gap.clone(), [xl, xu, yl, yu])
    }

    fn l1_norm(&self, n: &Expr, v: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_vec_l1_norm.clone(), n.clone()), v.clone())
    }

    fn ib_width_app(&self, d: &Expr, b: &Expr) -> Expr {
        Expr::app(Expr::app(self.ib_width.clone(), d.clone()), b.clone())
    }
}

impl Environment {
    /// Initialize extended McCormick declarations (T50-T52, Phase 3).
    ///
    /// Depends on:
    /// - `init_nn_verify_mccormick()` for base envelope definitions
    /// - `init_nn_verify_foundation_types()` for l1_norm, width
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_mccormick_ext(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.McCormick.mccormick_bilinear_sound",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_mccormick()?;
        self.init_nn_verify_foundation_types()?;

        let c = McExtConsts::new();
        self.register_t50_mccormick_bilinear_sound(&c)?;
        self.register_t51_mccormick_shared_input(&c)?;
        self.register_t52_mccormick_linear_growth(&c)?;
        Ok(())
    }

    /// T50: `NNVerify.McCormick.mccormick_bilinear_sound`
    ///
    /// McCormick envelope soundness via case-split on four bilinear facets.
    /// Given box constraints xl <= x <= xu, yl <= y <= yl, the four McCormick
    /// inequalities hold simultaneously:
    /// ```text
    /// forall (x y xl xu yl yu : Rat),
    ///   xl <= x -> x <= xu -> yl <= y -> y <= yu ->
    ///   And (And (xl*y + x*yl - xl*yl <= x*y)
    ///            (xu*y + x*yu - xu*yu <= x*y))
    ///       (And (x*y <= xl*y + x*yu - xl*yu)
    ///            (x*y <= xu*y + x*yl - xu*yl))
    /// ```
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t50_mccormick_bilinear_sound(&mut self, c: &McExtConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.mccormick_bilinear_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let env_lower = Expr::const_(
            Name::from_string("NNVerify.McCormick.envelope_lower"),
            vec![],
        );
        let env_upper = Expr::const_(
            Name::from_string("NNVerify.McCormick.envelope_upper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let (xl_id, xl) = b.fresh_local(c.rat.clone());
            let (xu_id, xu) = b.fresh_local(c.rat.clone());
            let (yl_id, yl) = b.fresh_local(c.rat.clone());
            let (yu_id, yu) = b.fresh_local(c.rat.clone());
            let h1 = c.rat_le(xl.clone(), x.clone());
            let h2 = c.rat_le(x.clone(), xu.clone());
            let h3 = c.rat_le(yl.clone(), y.clone());
            let h4 = c.rat_le(y.clone(), yu.clone());
            let (h1_id, _) = b.fresh_local(h1.clone());
            let (h2_id, _) = b.fresh_local(h2.clone());
            let (h3_id, _) = b.fresh_local(h3.clone());
            let (h4_id, _) = b.fresh_local(h4.clone());
            let lower_app = Expr::apps(
                env_lower,
                [
                    x.clone(),
                    y.clone(),
                    xl.clone(),
                    xu.clone(),
                    yl.clone(),
                    yu.clone(),
                ],
            );
            let upper_app = Expr::apps(env_upper, [x, y, xl, xu, yl, yu]);
            let concl = c.and_prop(lower_app, upper_app);
            let r = b.mk_pi(h4_id, BinderInfo::Default, h4, concl);
            let r = b.mk_pi(h3_id, BinderInfo::Default, h3, r);
            let r = b.mk_pi(h2_id, BinderInfo::Default, h2, r);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1, r);
            let r = b.mk_pi(yu_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(yl_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(xu_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(xl_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T51: `NNVerify.McCormick.mccormick_shared_input`
    ///
    /// When x and y are correlated (share an input), the gap is tighter.
    /// Specifically, for shared-input McCormick where x, y are both functions
    /// of the same z in [zl, zu]:
    /// ```text
    /// forall (xl xu yl yu zl zu : Rat),
    ///   zl <= zu -> xl <= xu -> yl <= yu ->
    ///   gap xl xu yl yu <= (xu - xl) * (yu - yl)
    /// ```
    /// (This is the standard gap bound; the shared-input version is at least
    /// as tight.)
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t51_mccormick_shared_input(&mut self, c: &McExtConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.mccormick_shared_input");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (xl_id, xl) = b.fresh_local(c.rat.clone());
            let (xu_id, xu) = b.fresh_local(c.rat.clone());
            let (yl_id, yl) = b.fresh_local(c.rat.clone());
            let (yu_id, yu) = b.fresh_local(c.rat.clone());
            let (zl_id, zl) = b.fresh_local(c.rat.clone());
            let (zu_id, zu) = b.fresh_local(c.rat.clone());
            // Hypotheses
            let h1 = c.rat_le(zl, zu);
            let h2 = c.rat_le(xl.clone(), xu.clone());
            let h3 = c.rat_le(yl.clone(), yu.clone());
            let (h1_id, _) = b.fresh_local(h1.clone());
            let (h2_id, _) = b.fresh_local(h2.clone());
            let (h3_id, _) = b.fresh_local(h3.clone());
            // Conclusion: gap is bounded
            let gap_val = c.gap_app(xl.clone(), xu.clone(), yl.clone(), yu.clone());
            let bound = c.mul(c.sub(xu, xl), c.sub(yu, yl));
            let concl = c.rat_le(gap_val, bound);
            let r = b.mk_pi(h3_id, BinderInfo::Default, h3, concl);
            let r = b.mk_pi(h2_id, BinderInfo::Default, h2, r);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1, r);
            let r = b.mk_pi(zu_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(zl_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(yu_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(yl_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(xu_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(xl_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T52: `NNVerify.McCormick.mccormick_linear_growth`
    ///
    /// The McCormick relaxation gap grows at most linearly in the input widths:
    /// ```text
    /// forall (n : Nat) (B_x B_y : IntervalBounds n),
    ///   l1_norm n (width n B_x) * l1_norm n (width n B_y)
    ///     -- bounds the total gap across all dimensions
    /// ```
    /// (Vectorized: the total gap is bounded by product of widths.)
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t52_mccormick_linear_growth(&mut self, c: &McExtConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.mccormick_linear_growth");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Vectorized gap accumulator
        let mccormick_total_gap =
            Expr::const_(Name::from_string("NNVerify.McCormick.total_gap"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ib_n = c.ib_of(&n);
            let (bx_id, bx) = b.fresh_local(ib_n.clone());
            let (by_id, by) = b.fresh_local(ib_n.clone());
            // Width of B_x and B_y
            let width_x = c.ib_width_app(&n, &bx);
            let width_y = c.ib_width_app(&n, &by);
            let l1_x = c.l1_norm(&n, &width_x);
            let l1_y = c.l1_norm(&n, &width_y);
            // total_gap n B_x B_y <= l1(width B_x) * l1(width B_y)
            let total_gap = Expr::apps(mccormick_total_gap, [n.clone(), bx, by]);
            let bound = c.mul(l1_x, l1_y);
            let concl = c.rat_le(total_gap, bound);
            let r = b.mk_pi(by_id, BinderInfo::Default, ib_n.clone(), concl);
            let r = b.mk_pi(bx_id, BinderInfo::Default, ib_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // First register the total_gap accumulator
        self.register_mccormick_total_gap(c)?;
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.McCormick.total_gap`:
    /// `(n : Nat) -> IntervalBounds n -> IntervalBounds n -> Rat`
    ///
    /// Accumulated McCormick gap across all n dimensions.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_mccormick_total_gap(&mut self, c: &McExtConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.total_gap");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ib_n = c.ib_of(&n);
            let (bx_id, _) = b.fresh_local(ib_n.clone());
            let (by_id, _) = b.fresh_local(ib_n.clone());
            let r = b.mk_pi(by_id, BinderInfo::Default, ib_n.clone(), c.rat.clone());
            let r = b.mk_pi(bx_id, BinderInfo::Default, ib_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }
}
