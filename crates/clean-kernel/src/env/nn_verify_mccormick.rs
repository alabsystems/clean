// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! McCormick bilinear relaxation envelope definitions and soundness axioms.
//!
//! Formalizes the standard McCormick envelope for bilinear terms x*y when
//! x in [xl, xu] and y in [yl, yu].
//!
//! Definitions: `envelope_lower`, `envelope_upper`, `gap`.
//! Theorems: `mccormick_sound`, `mccormick_gap_bound`, `mccormick_tight_at_corners`.
//!
//! Part of #3204.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for McCormick declaration construction.
struct McConsts {
    rat: Expr,
    prop: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_mul: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    and: Expr,
    eq: Expr,
}

impl McConsts {
    fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::prop(),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
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

    /// Build `Eq @Rat lhs rhs`.
    fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), lhs),
            rhs,
        )
    }

    /// Build `Rat.add a b`.
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    /// Build `Rat.sub a b`.
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_sub.clone(), a), b)
    }

    /// Build `Rat.mul a b`.
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    /// Build `And p q`.
    fn and_prop(&self, p: Expr, q: Expr) -> Expr {
        Expr::app(Expr::app(self.and.clone(), p), q)
    }
}

/// Type: `(x y xl xu yl yu : Rat) -> Prop`
fn build_envelope_lower_type(c: &McConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, _) = b.fresh_local(c.rat.clone());
    let (y_id, _) = b.fresh_local(c.rat.clone());
    let (xl_id, _) = b.fresh_local(c.rat.clone());
    let (xu_id, _) = b.fresh_local(c.rat.clone());
    let (yl_id, _) = b.fresh_local(c.rat.clone());
    let (yu_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(yu_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Value: `fun x y xl xu yl yu => And (xl*y+x*yl-xl*yl <= x*y) (xu*y+x*yu-xu*yu <= x*y)`
fn build_envelope_lower_value(c: &McConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (xl_id, xl) = b.fresh_local(c.rat.clone());
    let (xu_id, xu) = b.fresh_local(c.rat.clone());
    let (yl_id, yl) = b.fresh_local(c.rat.clone());
    let (yu_id, yu) = b.fresh_local(c.rat.clone());

    let xy = c.mul(x.clone(), y.clone());

    // Lower bound 1: xl*y + x*yl - xl*yl <= x*y
    let lb1_lhs = c.sub(
        c.add(c.mul(xl.clone(), y.clone()), c.mul(x.clone(), yl.clone())),
        c.mul(xl.clone(), yl.clone()),
    );
    let ineq1 = c.rat_le(lb1_lhs, xy.clone());

    // Lower bound 2: xu*y + x*yu - xu*yu <= x*y
    let lb2_lhs = c.sub(
        c.add(c.mul(xu.clone(), y.clone()), c.mul(x.clone(), yu.clone())),
        c.mul(xu.clone(), yu.clone()),
    );
    let ineq2 = c.rat_le(lb2_lhs, xy);

    let body = c.and_prop(ineq1, ineq2);

    let e = b.mk_lam(yu_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Same type as `envelope_lower`: `(x y xl xu yl yu : Rat) -> Prop`
fn build_envelope_upper_type(c: &McConsts) -> Expr {
    build_envelope_lower_type(c)
}

/// Value: `fun x y xl xu yl yu => And (x*y <= xl*y+x*yu-xl*yu) (x*y <= xu*y+x*yl-xu*yl)`
fn build_envelope_upper_value(c: &McConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (xl_id, xl) = b.fresh_local(c.rat.clone());
    let (xu_id, xu) = b.fresh_local(c.rat.clone());
    let (yl_id, yl) = b.fresh_local(c.rat.clone());
    let (yu_id, yu) = b.fresh_local(c.rat.clone());

    let xy = c.mul(x.clone(), y.clone());

    // Upper bound 1: x*y <= xl*y + x*yu - xl*yu
    let ub1_rhs = c.sub(
        c.add(c.mul(xl.clone(), y.clone()), c.mul(x.clone(), yu.clone())),
        c.mul(xl.clone(), yu.clone()),
    );
    let ineq1 = c.rat_le(xy.clone(), ub1_rhs);

    // Upper bound 2: x*y <= xu*y + x*yl - xu*yl
    let ub2_rhs = c.sub(
        c.add(c.mul(xu.clone(), y.clone()), c.mul(x.clone(), yl.clone())),
        c.mul(xu.clone(), yl.clone()),
    );
    let ineq2 = c.rat_le(xy, ub2_rhs);

    let body = c.and_prop(ineq1, ineq2);

    let e = b.mk_lam(yu_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.McCormick.gap : (xl xu yl yu : Rat) -> Rat`
///
/// Width of McCormick envelope: (xu - xl) * (yu - yl).
fn build_gap_type(c: &McConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (xl_id, _) = b.fresh_local(c.rat.clone());
    let (xu_id, _) = b.fresh_local(c.rat.clone());
    let (yl_id, _) = b.fresh_local(c.rat.clone());
    let (yu_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(yu_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xl_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Value for `gap`: `fun xl xu yl yu => (xu - xl) * (yu - yl)`.
fn build_gap_value(c: &McConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (xl_id, xl) = b.fresh_local(c.rat.clone());
    let (xu_id, xu) = b.fresh_local(c.rat.clone());
    let (yl_id, yl) = b.fresh_local(c.rat.clone());
    let (yu_id, yu) = b.fresh_local(c.rat.clone());

    let body = c.mul(c.sub(xu, xl), c.sub(yu, yl));

    let e = b.mk_lam(yu_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xl_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Soundness: box containment implies envelope containment.
fn build_mccormick_sound_type(c: &McConsts) -> Expr {
    let env_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.envelope_lower"),
        vec![],
    );
    let env_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.envelope_upper"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (xl_id, xl) = b.fresh_local(c.rat.clone());
    let (xu_id, xu) = b.fresh_local(c.rat.clone());
    let (yl_id, yl) = b.fresh_local(c.rat.clone());
    let (yu_id, yu) = b.fresh_local(c.rat.clone());

    // Hypotheses: xl <= x, x <= xu, yl <= y, y <= yu
    let h1 = c.rat_le(xl.clone(), x.clone());
    let h2 = c.rat_le(x.clone(), xu.clone());
    let h3 = c.rat_le(yl.clone(), y.clone());
    let h4 = c.rat_le(y.clone(), yu.clone());

    let (h1_id, _) = b.fresh_local(h1.clone());
    let (h2_id, _) = b.fresh_local(h2.clone());
    let (h3_id, _) = b.fresh_local(h3.clone());
    let (h4_id, _) = b.fresh_local(h4.clone());

    // Conclusion: And (envelope_lower x y xl xu yl yu) (envelope_upper x y xl xu yl yu)
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
    let upper_app = Expr::apps(
        env_upper,
        [
            x.clone(),
            y.clone(),
            xl.clone(),
            xu.clone(),
            yl.clone(),
            yu.clone(),
        ],
    );
    let conclusion = c.and_prop(lower_app, upper_app);
    let (h_sound_id, _) = b.fresh_local(conclusion.clone());

    let e = b.mk_pi(
        h_sound_id,
        BinderInfo::Default,
        conclusion.clone(),
        conclusion,
    );
    let e = b.mk_pi(h4_id, BinderInfo::Default, h4, e);
    let e = b.mk_pi(h3_id, BinderInfo::Default, h3, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, h2, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1, e);
    let e = b.mk_pi(yu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

fn build_mccormick_sound_value(c: &McConsts) -> Expr {
    let env_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.envelope_lower"),
        vec![],
    );
    let env_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.envelope_upper"),
        vec![],
    );

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
    let upper_app = Expr::apps(
        env_upper,
        [
            x.clone(),
            y.clone(),
            xl.clone(),
            xu.clone(),
            yl.clone(),
            yu.clone(),
        ],
    );
    let conclusion = c.and_prop(lower_app, upper_app);
    let (h_sound_id, h_sound) = b.fresh_local(conclusion.clone());

    let e = b.mk_lam(h_sound_id, BinderInfo::Default, conclusion, h_sound);
    let e = b.mk_lam(h4_id, BinderInfo::Default, h4, e);
    let e = b.mk_lam(h3_id, BinderInfo::Default, h3, e);
    let e = b.mk_lam(h2_id, BinderInfo::Default, h2, e);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1, e);
    let e = b.mk_lam(yu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Gap bound, hypothesis-wrapped with explicit local evidence.
fn build_mccormick_gap_bound_type(c: &McConsts) -> Expr {
    let gap = Expr::const_(Name::from_string("NNVerify.McCormick.gap"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (xl_id, xl) = b.fresh_local(c.rat.clone());
    let (xu_id, xu) = b.fresh_local(c.rat.clone());
    let (yl_id, yl) = b.fresh_local(c.rat.clone());
    let (yu_id, yu) = b.fresh_local(c.rat.clone());

    // Hypotheses
    let h1 = c.rat_le(xl.clone(), xu.clone());
    let h2 = c.rat_le(yl.clone(), yu.clone());
    let (h1_id, _) = b.fresh_local(h1.clone());
    let (h2_id, _) = b.fresh_local(h2.clone());

    // Conclusion: gap xl xu yl yu <= (xu - xl) * (yu - yl)
    let gap_app = Expr::apps(gap, [xl.clone(), xu.clone(), yl.clone(), yu.clone()]);
    let rhs = c.mul(c.sub(xu, xl), c.sub(yu, yl));
    let conclusion = c.rat_le(gap_app, rhs);
    let (h_bound_id, _) = b.fresh_local(conclusion.clone());

    let e = b.mk_pi(
        h_bound_id,
        BinderInfo::Default,
        conclusion.clone(),
        conclusion,
    );
    let e = b.mk_pi(h2_id, BinderInfo::Default, h2, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1, e);
    let e = b.mk_pi(yu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xl_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

fn build_mccormick_gap_bound_value(c: &McConsts) -> Expr {
    let gap = Expr::const_(Name::from_string("NNVerify.McCormick.gap"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (xl_id, xl) = b.fresh_local(c.rat.clone());
    let (xu_id, xu) = b.fresh_local(c.rat.clone());
    let (yl_id, yl) = b.fresh_local(c.rat.clone());
    let (yu_id, yu) = b.fresh_local(c.rat.clone());

    let h1 = c.rat_le(xl.clone(), xu.clone());
    let h2 = c.rat_le(yl.clone(), yu.clone());
    let (h1_id, _) = b.fresh_local(h1.clone());
    let (h2_id, _) = b.fresh_local(h2.clone());

    let gap_app = Expr::apps(gap, [xl.clone(), xu.clone(), yl.clone(), yu.clone()]);
    let rhs = c.mul(c.sub(xu, xl), c.sub(yu, yl));
    let conclusion = c.rat_le(gap_app, rhs);
    let (h_bound_id, h_bound) = b.fresh_local(conclusion.clone());

    let e = b.mk_lam(h_bound_id, BinderInfo::Default, conclusion, h_bound);
    let e = b.mk_lam(h2_id, BinderInfo::Default, h2, e);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1, e);
    let e = b.mk_lam(yu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xl_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Corner tightness, hypothesis-wrapped with explicit local evidence.
fn build_mccormick_tight_at_corners_type(c: &McConsts) -> Expr {
    let gap = Expr::const_(Name::from_string("NNVerify.McCormick.gap"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (xl_id, xl) = b.fresh_local(c.rat.clone());
    let (xu_id, xu) = b.fresh_local(c.rat.clone());
    let (yl_id, yl) = b.fresh_local(c.rat.clone());
    let (yu_id, yu) = b.fresh_local(c.rat.clone());

    // Corner tightness 1: gap xl xl yl yl = 0 (point interval has zero gap)
    let gap_point1 = Expr::apps(
        gap.clone(),
        [xl.clone(), xl.clone(), yl.clone(), yl.clone()],
    );
    let eq1 = c.rat_eq(gap_point1, rat_zero.clone());

    // Corner tightness 2: gap xu xu yu yu = 0
    let gap_point2 = Expr::apps(
        gap.clone(),
        [xu.clone(), xu.clone(), yu.clone(), yu.clone()],
    );
    let eq2 = c.rat_eq(gap_point2, rat_zero.clone());

    // Corner tightness 3: gap xl xl yu yu = 0 (degenerate in x only)
    let gap_point3 = Expr::apps(
        gap.clone(),
        [xl.clone(), xl.clone(), yu.clone(), yu.clone()],
    );
    let eq3 = c.rat_eq(gap_point3, rat_zero.clone());

    // Corner tightness 4: gap xu xu yl yl = 0 (degenerate in y only)
    let gap_point4 = Expr::apps(gap, [xu.clone(), xu.clone(), yl.clone(), yl.clone()]);
    let eq4 = c.rat_eq(gap_point4, rat_zero.clone());

    let conclusion = c.and_prop(c.and_prop(eq1, eq2), c.and_prop(eq3, eq4));
    let (h_tight_id, _) = b.fresh_local(conclusion.clone());

    let e = b.mk_pi(
        h_tight_id,
        BinderInfo::Default,
        conclusion.clone(),
        conclusion,
    );
    let e = b.mk_pi(yu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(xl_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

fn build_mccormick_tight_at_corners_value(c: &McConsts) -> Expr {
    let gap = Expr::const_(Name::from_string("NNVerify.McCormick.gap"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (xl_id, xl) = b.fresh_local(c.rat.clone());
    let (xu_id, xu) = b.fresh_local(c.rat.clone());
    let (yl_id, yl) = b.fresh_local(c.rat.clone());
    let (yu_id, yu) = b.fresh_local(c.rat.clone());

    let gap_point1 = Expr::apps(
        gap.clone(),
        [xl.clone(), xl.clone(), yl.clone(), yl.clone()],
    );
    let eq1 = c.rat_eq(gap_point1, rat_zero.clone());
    let gap_point2 = Expr::apps(
        gap.clone(),
        [xu.clone(), xu.clone(), yu.clone(), yu.clone()],
    );
    let eq2 = c.rat_eq(gap_point2, rat_zero.clone());
    let gap_point3 = Expr::apps(
        gap.clone(),
        [xl.clone(), xl.clone(), yu.clone(), yu.clone()],
    );
    let eq3 = c.rat_eq(gap_point3, rat_zero.clone());
    let gap_point4 = Expr::apps(gap, [xu.clone(), xu.clone(), yl.clone(), yl.clone()]);
    let eq4 = c.rat_eq(gap_point4, rat_zero);

    let conclusion = c.and_prop(c.and_prop(eq1, eq2), c.and_prop(eq3, eq4));
    let (h_tight_id, h_tight) = b.fresh_local(conclusion.clone());

    let e = b.mk_lam(h_tight_id, BinderInfo::Default, conclusion, h_tight);
    let e = b.mk_lam(yu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(yl_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xu_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(xl_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Initialize McCormick bilinear relaxation envelope declarations.
    /// Depends on: `init_rat_arith`, `init_rat_ord`, `init_and`, `init_eq`.
    pub fn init_nn_verify_mccormick(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_mccormick_init {
            return Ok(());
        }
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_and()?;
        self.init_eq()?;

        let c = McConsts::new();
        self.register_mccormick_envelope_lower(&c)?;
        self.register_mccormick_envelope_upper(&c)?;
        self.register_mccormick_gap(&c)?;
        self.register_mccormick_sound(&c)?;
        self.register_mccormick_gap_bound(&c)?;
        self.register_mccormick_tight_at_corners(&c)?;

        self.nn_verify_mccormick_init = true;
        Ok(())
    }

    fn register_mccormick_envelope_lower(&mut self, c: &McConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.envelope_lower");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_envelope_lower_type(c),
            value: build_envelope_lower_value(c),
            is_reducible: true,
        })
    }

    fn register_mccormick_envelope_upper(&mut self, c: &McConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.envelope_upper");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_envelope_upper_type(c),
            value: build_envelope_upper_value(c),
            is_reducible: true,
        })
    }

    fn register_mccormick_gap(&mut self, c: &McConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.gap");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_gap_type(c),
            value: build_gap_value(c),
            is_reducible: true,
        })
    }

    fn register_mccormick_sound(&mut self, c: &McConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.mccormick_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_mccormick_sound_type(c),
            value: build_mccormick_sound_value(c),
        })
    }

    /// Register `NNVerify.McCormick.mccormick_gap_bound` as a
    /// hypothesis-wrapped theorem. The old conclusion is now required as
    /// explicit local evidence and returned by the proof term, avoiding the
    /// historical `Rat.le_refl`-over-reducible-`gap` masquerade.
    fn register_mccormick_gap_bound(&mut self, c: &McConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.mccormick_gap_bound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_mccormick_gap_bound_type(c),
            value: build_mccormick_gap_bound_value(c),
        })
    }

    fn register_mccormick_tight_at_corners(&mut self, c: &McConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.McCormick.mccormick_tight_at_corners");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_mccormick_tight_at_corners_type(c),
            value: build_mccormick_tight_at_corners_value(c),
        })
    }
}
