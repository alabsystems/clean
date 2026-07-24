// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — the **spectral glue** sub-lemmas that bridge the landed bricks
//! (R1 self-adjointness, R2 4th-power Hölder, the descent) into the
//! per-coordinate squared dual-HC `W² ≤ 16·Inf_i³`.
//!
//! This module works in the **un-normalized `subsetSum` / `HCPoint`** world —
//! the native carrier of `noise_self_adjoint` and the derivative-4norm bricks —
//! to minimise normalization threading. The named sub-lemmas of the decomposition
//! (`designs/2026-06-12-kkl-endgame-worked-chain.md`) land here one at a time,
//! each kernel-checked, `Constructive`, with an EMPTY admitted-axiom closure.
//!
//! ## Carrier: `BoolAnalysis.noiseOp`
//!
//! The noise operator `T_ρ` as a FUNCTION on the cube (so its square `T²` is
//! expressible), spelled byte-for-byte the way `noise_self_adjoint`'s `t_of_y`
//! inner sum is spelled (so the self-adjoint instance is def-eq to the glue
//! statement):
//!
//! ```text
//! BoolAnalysis.noiseOp (ρ : Rat) (n : Nat) (g : HCPoint n → Rat) : HCPoint n → Rat :=
//!   fun (y : HCPoint n) =>
//!     subsetSum n (fun (x : HCPoint n) => noiseDensityW ρ n y x · g x)
//! ```
//!
//! This is the un-normalized `T_ρ` (the `2^n` factor lives in the cube sum, not
//! in the operator). Reducible `Declaration::Definition`.
//!
//! ## GLUE-2 (R1 self-adjoint instantiation): `noise_self_adjoint_sq`
//!
//! ```text
//! BoolAnalysis.noise_self_adjoint_sq :
//!   ∀ (ρ : Rat) (n : Nat) (g : HCPoint n → Rat),
//!     subsetSum n (fun y => noiseOp ρ n g y · noiseOp ρ n g y)
//!   = subsetSum n (fun x => g x · noiseOp ρ n (noiseOp ρ n g) x)
//! ```
//!
//! i.e. `Σ_y (T_ρ g)(y)² = Σ_x g(x)·(T_ρ² g)(x)` — the self-adjoint "move one
//! operator across the inner product" identity, the spectral pivot the dual-HC
//! argument turns on. It is exactly `noise_self_adjoint ρ n g (noiseOp ρ n g)`:
//! with `h := T_ρ g`, the self-adjoint LHS integrand `h y · T_g(y)` β/δ-reduces to
//! `(T_ρ g)(y)·(T_ρ g)(y)`, and the RHS inner sum `U_h(x)` is exactly
//! `(T_ρ (T_ρ g))(x)`. Constructive, EMPTY closure (sole leaf:
//! `noise_self_adjoint`, itself Constructive with empty closure). No axiom added
//! or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the spectral glue. The `noiseDensityW` / `subsetSum`
/// spellings are byte-identical to `boolean_analysis_noise_self_adjoint.rs` so
/// the self-adjoint instance is def-eq to the glue statement.
struct GlueConsts {
    nat: Expr,
    rat: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    noise_density: Expr,
    noise_op: Expr,
    subset_sum: Expr,
    self_adjoint: Expr,
    eq1: Expr,
}

impl GlueConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_mul: k("Rat.mul"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            noise_op: k("BoolAnalysis.noiseOp"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            self_adjoint: k("BoolAnalysis.noise_self_adjoint"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → Rat`.
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    /// `noiseDensityW ρ n a b`.
    fn dens(&self, rho: &Expr, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), a.clone(), b.clone()],
        )
    }
    /// `noiseOp ρ n g`.
    fn op(&self, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(self.noise_op.clone(), [rho.clone(), n.clone(), g.clone()])
    }
}

impl Environment {
    /// Register `BoolAnalysis.noiseOp` — the un-normalized noise operator `T_ρ`
    /// as a function on the cube. Reducible `Declaration::Definition`. Idempotent;
    /// no axiom added/removed. Spelled byte-for-byte the way the self-adjoint
    /// inner sum is spelled so the instance is def-eq.
    pub fn register_noise_op(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseOp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_noise_density_w()?; // noiseDensityW (+ subsetSum)
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = GlueConsts::new();
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_noise_op_type(&c),
            value: build_noise_op_value(&c),
            is_reducible: true,
        })
    }

    /// Register the spectral glue sub-lemmas. Idempotent; each kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_glue(&mut self) -> Result<(), EnvError> {
        self.register_noise_op()?;
        self.register_noise_self_adjoint_sq()?;
        Ok(())
    }

    /// `BoolAnalysis.noise_self_adjoint_sq` — GLUE-2, the R1 self-adjoint
    /// instantiation `Σ_y (T_ρ g)(y)² = Σ_x g(x)·(T_ρ² g)(x)`. See module docs.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_noise_self_adjoint_sq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_self_adjoint_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_op()?;
        self.register_noise_self_adjoint()?; // the pivot
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = GlueConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_self_adjoint_sq(&c, false),
            value: build_self_adjoint_sq(&c, true),
        })
    }
}

/// `(ρ : Rat) → (n : Nat) → (g : HCPoint n → Rat) → (HCPoint n → Rat)`.
fn build_noise_op_type(c: &GlueConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, _rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (g_id, _g) = b.fresh_local(c.hcpoint_to_rat(&n));
    let result = c.hcpoint_to_rat(&n);
    let e = b.mk_pi(g_id, BinderInfo::Default, c.hcpoint_to_rat(&n), result);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `fun ρ n g => fun y => subsetSum n (fun x => noiseDensityW ρ n y x · g x)`.
fn build_noise_op_value(c: &GlueConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (g_id, g) = b.fresh_local(c.hcpoint_to_rat(&n));
    let hcp = c.hcpoint_of(&n);

    // fun (y : HCPoint n) => subsetSum n (fun x => dens ρ n y x · g x)
    let outer = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let inner = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (x_id, x) = e.fresh_local(hcp.clone());
            let body = c.mul(c.dens(&rho, &n, &y, &x), Expr::app(g.clone(), x.clone()));
            e.finish_child(e.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = c.ssum(&n, inner);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };

    let e = b.mk_lam(g_id, BinderInfo::Default, c.hcpoint_to_rat(&n), outer);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `noise_self_adjoint_sq`.
fn build_self_adjoint_sq(c: &GlueConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let hcp = c.hcpoint_of(&n);

    // tg := noiseOp ρ n g  ;  ttg := noiseOp ρ n (noiseOp ρ n g).
    let tg = c.op(&rho, &n, &g);
    let ttg = c.op(&rho, &n, &tg);

    // lhs := subsetSum n (fun y => (tg y)·(tg y)).
    let lhs = {
        let lhs_fn = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = d.fresh_local(hcp.clone());
            let tgy = Expr::app(tg.clone(), y.clone());
            let body = c.mul(tgy.clone(), tgy);
            d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        c.ssum(&n, lhs_fn)
    };
    // rhs := subsetSum n (fun x => g x · (ttg x)).
    let rhs = {
        let rhs_fn = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = d.fresh_local(hcp.clone());
            let body = c.mul(
                Expr::app(g.clone(), x.clone()),
                Expr::app(ttg.clone(), x.clone()),
            );
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        c.ssum(&n, rhs_fn)
    };

    let concl = c.eq_rat(lhs, rhs);

    let tail = if for_value {
        // noise_self_adjoint ρ n g (noiseOp ρ n g)  —  def-eq to the stated concl.
        Expr::apps(
            c.self_adjoint.clone(),
            [rho.clone(), n.clone(), g.clone(), tg.clone()],
        )
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, g_id, fn_ty, tail);
    let e = bind(&b, n_id, c.nat.clone(), e);
    let e = bind(&b, rho_id, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_glue()
            .expect("init_boolean_analysis_kkl_dualhc_glue");
        env.init_boolean_analysis_kkl_dualhc_glue()
            .expect("idempotent");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    /// `noiseOp` is a reducible Definition that type-checks.
    #[test]
    fn test_noise_op_is_definition() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.noiseOp");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition, "must be Definition");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("noiseOp must kernel-check: {e:?}"));
    }

    /// GLUE-2 is a kernel-checked, `Constructive`, empty-closure Theorem.
    #[test]
    fn test_noise_self_adjoint_sq_is_constructive_theorem() {
        let env = env();
        assert_constructive_theorem(&env, "BoolAnalysis.noise_self_adjoint_sq");
    }
}
