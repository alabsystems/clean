// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3, the **operator-materialization layer**
//! (design `2026-06-18-kkl-real-sqrt-layer-plan.md` §10.8, the pinned blocker).
//!
//! # The gap this closes
//!
//! §10.8 pins the SOLE remaining §9.6 content to the absence of an axiom-free
//! materialized noise operator as a function on cube points. The overlay carries
//! the spatial double-sum kernel `BoolAnalysis.noiseDensityW ρ n x y` and the
//! spectral identities over it, but NO `applyT ρ n g : HCPoint n → Rat` — so the
//! per-coordinate sequence `z := T_{1/9}(D_i f)` that H1 / `m2_from_contraction`
//! / `deriv_holder_fourth_support` consume has nothing concrete to instantiate
//! at. (`BoolAnalysis.noiseFn` is the only related object but is `Fin (2^n) →
//! Rat` and carries a `2^n` normalization — the wrong shape.)
//!
//! # What this module lands
//!
//! ```text
//! BoolAnalysis.applyT (ρ : Rat) (n : Nat) (g : HCPoint n → Rat) : HCPoint n → Rat
//!   := fun x => subsetSum n (fun y => Rat.mul (g y) (noiseDensityW ρ n x y))
//! ```
//!
//! the genuine `T_ρ` as a point function (no `2^n`), a reducible
//! `Declaration::Definition`. It δ-unfolds to a `subsetSum` over the landed
//! kernel, so every `subsetSum` lemma applies to it verbatim and any theorem
//! stated over it stays `ProofQuality::Constructive` (the closure bottoms out in
//! `subsetSum` / `noiseDensityW`, both reducible and admitted-axiom-free).
//!
//! No axiom is added or removed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached atoms for the `applyT` materialization.
struct ApplyTConsts {
    nat: Expr,
    rat: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    subset_sum: Expr,
    noise_density: Expr,
}

impl ApplyTConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_mul: k("Rat.mul"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn noise_density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
}

/// `(ρ : Rat) → (n : Nat) → (HCPoint n → Rat) → HCPoint n → Rat`.
fn build_applyt_type(c: &ApplyTConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, _rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, _g) = b.fresh_local(g_ty.clone());
    // result: HCPoint n → Rat
    let res = c.hcpoint_to_rat(&n);
    let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, res);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

/// `fun ρ n g x => subsetSum n (fun y => g y · noiseDensityW ρ n x y)`.
fn build_applyt_value(c: &ApplyTConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    // inner summand over y: fun y => g y · noiseDensityW ρ n x y
    let summand = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let body = c.mul(
            Expr::app(g.clone(), y.clone()),
            c.noise_density(&rho, &n, &x, &y),
        );
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let body = c.ssum(&n, summand);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, body);
    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.applyT` — the materialized noise operator
    /// `T_ρ` as a point function `HCPoint n → Rat` (NO `2^n`). Reducible
    /// `Declaration::Definition`; closure bottoms out in `subsetSum` /
    /// `noiseDensityW` (both reducible, admitted-axiom-free). Idempotent.
    pub fn register_applyt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.applyT");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_noise_density_w()?; // noiseDensityW (+ subsetSum, HCPoint, Rat)
        self.register_subset_sum()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = ApplyTConsts::new();
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_applyt_type(&c),
            value: build_applyt_value(&c),
            is_reducible: true,
        })
    }

    /// Init hook for the `applyT` materialization overlay module.
    pub fn init_boolean_analysis_kkl_applyt(&mut self) -> Result<(), EnvError> {
        self.register_applyt()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_applyt()
            .expect("init_boolean_analysis_kkl_applyt");
        env.init_boolean_analysis_kkl_applyt().expect("idempotent");
        env
    }

    #[test]
    fn test_applyt_is_reducible_definition() {
        let env = env();
        let name = Name::from_string("BoolAnalysis.applyT");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition, "must be a Definition");
        assert!(info.is_reducible, "applyT must be reducible");
    }

    #[test]
    fn test_applyt_value_checks_against_type() {
        let env = env();
        let name = Name::from_string("BoolAnalysis.applyT");
        let info = env.get_const(&name).expect("registered");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("applyT value must check against its type: {e:?}"));
    }
}
