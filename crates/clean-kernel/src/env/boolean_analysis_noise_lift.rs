// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the `liftH` coordinate-peel cross integrand.
//!
//! The operator peel `noiseFn_succ_{low,high}` folds the two cube halves of
//! `noiseFn ρ (n+1) F` into two `n`-level `noiseFn` legs:
//!
//! - the **`gPart` leg** `noiseFn ρ n (gPart n F)` collecting the unweighted
//!   half-sum (`gPart n F x ≡ F(extendF n x) + F(extendT n x)`, already a
//!   reducible `Definition` from `boolean_analysis_peel_parts.rs`), and
//! - the **cross leg** `±ρ · noiseFn ρ n (liftH n F)` collecting the ρ-weighted
//!   half-sum.
//!
//! The pointwise ring keystone (`peel_pointwise_keystone`) lands the cross term
//! as `ρ·((p−q)·d)` with `p := F(extendF n x)`, `q := F(extendT n x)`. So the
//! cross integrand is `(p − q)·d = (F(extendF n x) − F(extendT n x))·d`, which is
//! NOT `hPart n F x ≡ F(extendT n x) − F(extendF n x)` (the opposite sign). To
//! make the operator-peel statement δ-recognize the cross leg as a literal
//! `n`-level `noiseFn`, register the matching un-normalized part
//!
//! ```text
//! BoolAnalysis.liftH (n : Nat) (F : HCPoint (n+1) → Rat) (x : HCPoint n) : Rat
//!   := Rat.sub (F (extendF n x)) (F (extendT n x))
//! ```
//!
//! i.e. `liftH n F = −(hPart n F)` (the `extendF − extendT` sign), a reducible
//! `Declaration::Definition` over the peel extension maps. (`gPart` already serves
//! the mission's `liftG`; no separate `liftG` decl is registered — `gPart n F` IS
//! `liftG F`.) No axiom is added or removed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared constants for the `liftH` cross integrand.
pub(super) struct LiftConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    nat_succ: Expr,
    rat_sub: Expr,
    hcpoint: Expr,
    extend_f: Expr,
    extend_t: Expr,
}

impl LiftConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            extend_f: Expr::const_(Name::from_string("BoolAnalysis.extendF"), vec![]),
            extend_t: Expr::const_(Name::from_string("BoolAnalysis.extendT"), vec![]),
        }
    }

    pub(super) fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    pub(super) fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    /// `HCPoint (n+1) → Rat` — the type of the peeled function `F`.
    pub(super) fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.hcpoint_of(&self.succ(n)),
            self.rat.clone(),
        )
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    /// `F (extendF n x)`.
    fn f_ext_f(&self, f: &Expr, n: &Expr, x: &Expr) -> Expr {
        Expr::app(
            f.clone(),
            Expr::apps(self.extend_f.clone(), [n.clone(), x.clone()]),
        )
    }
    /// `F (extendT n x)`.
    fn f_ext_t(&self, f: &Expr, n: &Expr, x: &Expr) -> Expr {
        Expr::app(
            f.clone(),
            Expr::apps(self.extend_t.clone(), [n.clone(), x.clone()]),
        )
    }
}

impl Environment {
    /// Register `BoolAnalysis.liftH`: the `extendF − extendT` cross integrand.
    /// Reducible `Definition`. Idempotent; axiom-free.
    pub(crate) fn register_lift_h(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.liftH");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_peel()?; // extendF / extendT
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.sub
        }

        let c = LiftConsts::new();
        let (ty, value) = build_lift_h(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

/// Build the type + value of `liftH`:
/// `(n : Nat) → (F : HCPoint (n+1) → Rat) → (x : HCPoint n) → Rat`,
/// `value n F x := F (extendF n x) − F (extendT n x)`.
fn build_lift_h(c: &LiftConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (f_id, _f) = b.fresh_local(c.f_type(&n));
        let (x_id, _x) = b.fresh_local(c.hcpoint_of(&n));
        let e = b.mk_pi(x_id, BinderInfo::Default, c.hcpoint_of(&n), c.rat.clone());
        let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&n));
        let (x_id, x) = b.fresh_local(c.hcpoint_of(&n));
        let body = c.sub(c.f_ext_f(&f, &n, &x), c.f_ext_t(&f, &n, &x)); // F(extF) − F(extT)
        let e = b.mk_lam(x_id, BinderInfo::Default, c.hcpoint_of(&n), body);
        let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::Environment;
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_lift_h_registered_as_reducible_definition() {
        let mut env = Environment::with_prelude();
        env.register_lift_h().expect("register_lift_h");
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.liftH"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("BoolAnalysis.liftH"),
                vec![],
            ))
            .expect("liftH should type-check");
    }

    #[test]
    fn test_lift_h_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_lift_h().expect("register_lift_h");
        let deps = env
            .axiom_deps(&Name::from_string("BoolAnalysis.liftH"))
            .expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "liftH must be axiom-free, got {names:?}");
    }
}
