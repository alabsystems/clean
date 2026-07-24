// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitions for IEEE 754 float-to-rational bridge.
//!
//! Formalizes the bridge between IEEE 754 floating-point and rational arithmetic,
//! critical for NN verification where weights are floats but proofs use rationals.
//!
//! ## Definitions
//!
//! - `NNVerify.FloatRational.float_to_rational` — exact conversion from Float to Rat
//! - `NNVerify.FloatRational.rounding_error` — |round(x) - x| for a rounding mode
//! - `NNVerify.FloatRational.ulp` — unit in the last place for a float value
//! - `NNVerify.FloatRational.interval_float_rational` — interval [lo_rat, hi_rat]
//! - `NNVerify.FloatRational.accumulated_error` — error through a chain of float ops
//!
//! Part of #3185.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for float-rational declaration construction.
pub(crate) struct FRConsts {
    pub(crate) nat: Expr,
    pub(crate) rat: Expr,
    pub(crate) float: Expr,
    pub(crate) prop: Expr,
    pub(crate) type0: Expr,
    pub(crate) rat_sub: Expr,
    pub(crate) rat_mul: Expr,
    pub(crate) rat_add: Expr,
    pub(crate) le_le: Expr,
    pub(crate) inst_le_rat: Expr,
    pub(crate) and: Expr,
    pub(crate) eq: Expr,
    pub(crate) rat_abs: Expr,
}

impl FRConsts {
    pub(crate) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            float: Expr::const_(Name::from_string("Float"), vec![]),
            prop: Expr::prop(),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            rat_abs: Expr::const_(Name::from_string("Rat.abs"), vec![]),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
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

    /// Build `Eq @Rat lhs rhs`.
    pub(crate) fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), lhs),
            rhs,
        )
    }

    /// Build `Rat.add a b`.
    pub(crate) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    /// Build `Rat.sub a b`.
    pub(crate) fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_sub.clone(), a), b)
    }

    /// Build `Rat.mul a b`.
    pub(crate) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    /// Build `And p q`.
    pub(crate) fn and_prop(&self, p: Expr, q: Expr) -> Expr {
        Expr::app(Expr::app(self.and.clone(), p), q)
    }

    /// Build `Rat.abs x`.
    pub(crate) fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), x)
    }
}

impl Environment {
    /// Register `NNVerify.FloatRational.float_to_rational : Float -> Rat`
    ///
    /// Exact conversion from IEEE 754 float to rational representation.
    /// Every finite float has an exact rational representation (as m * 2^e).
    pub(crate) fn register_float_to_rational(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.float_to_rational");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Type: Float -> Rat
        let ty = Expr::pi(BinderInfo::Default, c.float.clone(), c.rat.clone());
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// Register `NNVerify.FloatRational.ulp : Float -> Rat`
    ///
    /// Unit in the last place: the spacing between adjacent floats at this value.
    /// For a float f with exponent e, ulp(f) = 2^(e - p + 1) where p = precision.
    pub(crate) fn register_ulp(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.ulp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Type: Float -> Rat
        let ty = Expr::pi(BinderInfo::Default, c.float.clone(), c.rat.clone());
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// Register `NNVerify.FloatRational.rounding_error : Rat -> Float -> Rat`
    ///
    /// The rounding error: |float_to_rational(round(x)) - x| for a real value x
    /// and its floating-point approximation. Takes the exact rational value and
    /// the rounded float, returns the error magnitude.
    pub(crate) fn register_rounding_error(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.rounding_error");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Type: Rat -> Float -> Rat
        // (exact_value : Rat) -> (rounded : Float) -> Rat
        let inner = Expr::pi(BinderInfo::Default, c.float.clone(), c.rat.clone());
        let ty = Expr::pi(BinderInfo::Default, c.rat.clone(), inner);
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// Register `NNVerify.FloatRational.interval_float_rational`
    ///   `: Float -> Float -> Rat -> Rat -> Prop`
    ///
    /// Asserts that the rational interval [lo_rat, hi_rat] covers the
    /// float interval [lo_float, hi_float] after exact conversion plus
    /// rounding error margins.
    pub(crate) fn register_interval_float_rational(
        &mut self,
        c: &FRConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.interval_float_rational");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let f2r = Expr::const_(
            Name::from_string("NNVerify.FloatRational.float_to_rational"),
            vec![],
        );

        let mut b = EnvDeclBuilder::new();
        let (flo_id, flo) = b.fresh_local(c.float.clone());
        let (fhi_id, fhi) = b.fresh_local(c.float.clone());
        let (rlo_id, rlo) = b.fresh_local(c.rat.clone());
        let (rhi_id, rhi) = b.fresh_local(c.rat.clone());

        // lo_rat <= float_to_rational(lo_float) AND
        // float_to_rational(hi_float) <= hi_rat
        let f2r_lo = Expr::app(f2r.clone(), flo);
        let f2r_hi = Expr::app(f2r, fhi);
        let cond1 = c.rat_le(rlo, f2r_lo);
        let cond2 = c.rat_le(f2r_hi, rhi);
        let body = c.and_prop(cond1, cond2);

        let e = b.mk_lam(rhi_id, BinderInfo::Default, c.rat.clone(), body);
        let e = b.mk_lam(rlo_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_lam(fhi_id, BinderInfo::Default, c.float.clone(), e);
        let e = b.mk_lam(flo_id, BinderInfo::Default, c.float.clone(), e);
        let value = b.finish(e);

        // Type: Float -> Float -> Rat -> Rat -> Prop
        let ty = {
            let mut b2 = EnvDeclBuilder::new();
            let (a_id, _) = b2.fresh_local(c.float.clone());
            let (b_id, _) = b2.fresh_local(c.float.clone());
            let (c_id, _) = b2.fresh_local(c.rat.clone());
            let (d_id, _) = b2.fresh_local(c.rat.clone());
            let e = b2.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
            let e = b2.mk_pi(c_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b2.mk_pi(b_id, BinderInfo::Default, c.float.clone(), e);
            let e = b2.mk_pi(a_id, BinderInfo::Default, c.float.clone(), e);
            b2.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// Register `Float.toRatExact : Float -> Rat` and `Float.ulpExact : Float
    /// -> Rat` as `Declaration::Opaque` constants.
    ///
    /// These are the kernel-CHECKED exact decomposition of an IEEE-754 binary64
    /// into its dyadic rational value / unit-in-the-last-place. The computational
    /// content is supplied ENTIRELY by the native reducers in
    /// `native_reducers_float_to_rat.rs` (registered via
    /// `init_float_to_rat_native_reducers`), exactly mirroring how `Float.add` /
    /// `Float.round` are `Opaque` placeholders backed by native reducers.
    ///
    /// `Opaque` (not `Axiom`) is the load-bearing choice: an opaque body is
    /// NEVER unfolded by delta, so the ONLY way `Float.toRatExact (Float.mk
    /// <bits>)` reduces is through the native reducer, and the declaration adds
    /// NO entry to `env.axiom_deps`. The never-unfolded placeholder body is the
    /// closed value `Rat.zero` (type-correct: `Float -> Rat`).
    pub(crate) fn register_float_exact_decomp(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        // Placeholder body `fun (_ : Float) => Rat.zero`.
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let placeholder = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _f) = b.fresh_local(c.float.clone());
            let e = b.mk_lam(f_id, BinderInfo::Default, c.float.clone(), rat_zero);
            b.finish(e)
        };
        // Type: Float -> Rat.
        let ty = Expr::pi(BinderInfo::Default, c.float.clone(), c.rat.clone());

        for op in ["Float.toRatExact", "Float.ulpExact"] {
            let name = Name::from_string(op);
            if self.get_const(&name).is_some() {
                continue;
            }
            self.add_decl(Declaration::Opaque {
                name,
                level_params: vec![],
                type_: ty.clone(),
                value: placeholder.clone(),
            })?;
        }
        Ok(())
    }

    /// Register `NNVerify.FloatRational.accumulated_error : Nat -> Rat -> Rat`
    ///
    /// Error accumulated through a chain of n floating-point operations,
    /// where eps is the machine epsilon. Models worst-case error growth.
    pub(crate) fn register_accumulated_error(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.accumulated_error");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Type: Nat -> Rat -> Rat
        // (n_ops : Nat) -> (eps : Rat) -> Rat
        let inner = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), inner);
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }
}
