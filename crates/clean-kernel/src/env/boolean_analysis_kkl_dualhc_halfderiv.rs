// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — the **pointwise integer `{0,±2}` algebra leaf** of the discrete
//! derivative `g := pm a − pm b ∈ {0,±2}`: the cube collapse
//!
//! ```text
//! BoolAnalysis.deriv_cube_eq_four_deriv :
//!   ∀ (a b : Bool), g·(g·g) = 4·g          (g := Rat.sub (pm a) (pm b))
//! ```
//!
//! This is the `e³ = e` two-valued identity in its DENOMINATOR-FREE form. Working
//! with the genuine `D_i f = g ∈ {0,±2}` (rather than the halved `e = g/2`)
//! keeps every quantity integer-valued (`Rat.mk … 1`), so on the four concrete
//! `(a,b)` both `g·(g·g)` and `4·g` native-reduce to the SAME `Rat.mk` numeral
//! (`0` or `±8`) and each leaf is `@Eq.refl Rat`. The halved-derivative facts R2
//! consumes — `e·(e·e) = e`, `(e·e)·(e·e) = e·e` — then follow downstream by ring
//! algebra distributing the `half := 1/2` scalar over THIS integer identity and
//! the landed `BoolAnalysis.disagree_sq_self_eq_four_mul` (`(g·g)·(g·g) = 4·(g·g)`),
//! NOT by quotient-carrier reduction (which fails for `1/2`-scaled reps: `g³` has
//! denominator `8`, `g` denominator `2`, so `Eq.refl` cannot close `e³ = e`).
//!
//! Kernel-checked `Declaration::Theorem`, `ProofQuality::Constructive`, EMPTY
//! admitted-axiom closure (leaves: `Bool.rec`, `Eq.refl`, `pm` — all
//! foundational). No axiom added or removed. The construction mirrors
//! `BoolAnalysis.disagree_sq_self_eq_four_mul` byte-for-byte.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the integer derivative cube leaf.
struct DerivCubeConsts {
    order: OrderConsts,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    pm: Expr,
    bool_rec_prop: Expr,
}

impl DerivCubeConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            pm: k("BoolAnalysis.pm"),
            // `Bool.rec` into the `Eq Rat` (Sort 0 / Prop) motive.
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.order.sub(a, b)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn pm_of(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    /// `four := Rat.mk (Int.ofNat 4) 1`.
    fn four(&self) -> Expr {
        let mut four_nat = self.nat_zero.clone();
        for _ in 0..4 {
            four_nat = Expr::app(self.nat_succ.clone(), four_nat);
        }
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), four_nat), one],
        )
    }
    /// `g(a,b) := pm a − pm b`.
    fn g_of(&self, a: Expr, b: Expr) -> Expr {
        self.sub(self.pm_of(a), self.pm_of(b))
    }
    /// `@Eq.refl Rat x`.
    fn eq_refl(&self, x: Expr) -> Expr {
        Expr::apps(self.order.eq_refl.clone(), [self.rat(), x])
    }
}

impl Environment {
    /// Register the integer derivative cube leaf. Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_halfderiv(&mut self) -> Result<(), EnvError> {
        self.register_deriv_cube_eq_four_deriv()?;
        Ok(())
    }

    /// `BoolAnalysis.deriv_cube_eq_four_deriv : ∀ a b, g·(g·g) = 4·g`
    /// (`g := pm a − pm b`). The denominator-free `{0,±2}` cube identity.
    pub fn register_deriv_cube_eq_four_deriv(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_cube_eq_four_deriv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // pm, Rat foundations
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_bool()?;
        let c = DerivCubeConsts::new();
        // lhs := g·(g·g) ;  rhs := 4·g.
        let lhs = |a: Expr, b: Expr| {
            let g = c.g_of(a, b);
            c.mul(g.clone(), c.mul(g.clone(), g))
        };
        let rhs = |a: Expr, b: Expr| c.mul(c.four(), c.g_of(a, b));
        let (ty, value) = build_eq_leaf(&c, &lhs, &rhs);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build `∀ (a b : Bool), lhs(a,b) = rhs(a,b)` with a `Bool.rec`-on-`a`-then-`b`
/// proof whose four ground leaves are `@Eq.refl Rat (lhs)`. Requires that
/// `lhs(a,b)` and `rhs(a,b)` native-reduce to the SAME `Rat` numeral on each
/// concrete `(a,b)` (true for the integer `{0,±2}` derivative facts).
fn build_eq_leaf(
    c: &DerivCubeConsts,
    lhs: &dyn Fn(Expr, Expr) -> Expr,
    rhs: &dyn Fn(Expr, Expr) -> Expr,
) -> (Expr, Expr) {
    let bool_c = c.bool_.clone();
    let bt = c.bool_true.clone();
    let bf = c.bool_false.clone();

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, av) = b.fresh_local(bool_c.clone());
        let (b_id, bv) = b.fresh_local(bool_c.clone());
        let concl = c.eq(lhs(av.clone(), bv.clone()), rhs(av.clone(), bv.clone()));
        let e = b.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), concl);
        let e = b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut bld = EnvDeclBuilder::new();
        let (a_id, av) = bld.fresh_local(bool_c.clone());
        let (b_id, bv) = bld.fresh_local(bool_c.clone());

        // motive_a : fun a' => lhs a' b = rhs a' b
        let motive_a = {
            let mut d = EnvDeclBuilder::child_of(&bld);
            let (ap_id, ap) = d.fresh_local(bool_c.clone());
            let body = c.eq(lhs(ap.clone(), bv.clone()), rhs(ap.clone(), bv.clone()));
            d.finish_child(d.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), body))
        };

        // For a fixed concrete `av_c`, split on `b` with Eq.refl leaves.
        let inner_rec = |av_c: Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let motive_b = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (bp_id, bp) = e.fresh_local(bool_c.clone());
                let body = c.eq(lhs(av_c.clone(), bp.clone()), rhs(av_c.clone(), bp.clone()));
                e.finish_child(e.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), body))
            };
            let leaf = |bv_c: Expr| c.eq_refl(lhs(av_c.clone(), bv_c));
            let b_false = leaf(bf.clone());
            let b_true = leaf(bt.clone());
            let e = Expr::apps(
                c.bool_rec_prop.clone(),
                [motive_b, b_false, b_true, bv.clone()],
            );
            d.finish_child(e)
        };

        let a_false = inner_rec(bf.clone(), &bld);
        let a_true = inner_rec(bt.clone(), &bld);
        let rec_a = Expr::apps(
            c.bool_rec_prop.clone(),
            [motive_a, a_false, a_true, av.clone()],
        );
        let e = bld.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec_a);
        let e = bld.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e);
        bld.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_halfderiv()
            .expect("init_boolean_analysis_kkl_dualhc_halfderiv");
        env.init_boolean_analysis_kkl_dualhc_halfderiv()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_deriv_cube_eq_four_deriv_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.deriv_cube_eq_four_deriv");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
