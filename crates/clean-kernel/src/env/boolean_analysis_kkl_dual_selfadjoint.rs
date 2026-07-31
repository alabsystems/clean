// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bridge — Component B2: the **self-adjointness** of the
//! noise operator `T_ρ` as a bilinear `subsetSum` inner-product identity.
//!
//! The dual hypercontractive bound (O'Donnell §9.6) rewrites
//! `‖T_{1/3} g‖₂² = ⟨T_{1/9} g, g⟩` using `⟨T_ρ g, h⟩ = ⟨g, T_ρ h⟩`. With the
//! un-normalized inner product `⟨a, b⟩ := subsetSum n (fun x => a x · b x)` and
//! the noise operator's correlated kernel `W(x,y) := noiseDensityW ρ n x y`
//! (so `(T_ρ g)(x) = Σ_y g(y)·W(x,y)` up to the `2^n` normalization), the
//! bilinear pairing through the kernel is:
//! - `⟨T_ρ g, h⟩ = Σ_x (Σ_y g(y)·W(x,y))·h(x) = Σ_x Σ_y (g y · h x)·W(x,y)`,
//! - `⟨g, T_ρ h⟩ = Σ_x g(x)·(Σ_y h(y)·W(x,y)) = Σ_x Σ_y (g x · h y)·W(x,y)`.
//!
//! ```text
//! BoolAnalysis.noise_pairing_self_adjoint :
//!   ∀ (ρ : Rat) (n : Nat) (g h : HCPoint n → Rat),
//!     subsetSum n (fun x => subsetSum n (fun y =>
//!       Rat.mul (Rat.mul (g y) (h x)) (noiseDensityW ρ n x y)))      -- ⟨T_ρ g, h⟩
//!       = subsetSum n (fun x => subsetSum n (fun y =>
//!           Rat.mul (Rat.mul (g x) (h y)) (noiseDensityW ρ n x y)))  -- ⟨g, T_ρ h⟩
//! ```
//!
//! Self-adjointness — the symmetric spectral sum both sides equal is
//! `Σ_S ρ^{|S|}·ĝ(S)·ĥ(S)` (the bilinear polarization of `noise_spectral_core`;
//! this module proves the operator self-adjointness it pivots through, which is
//! the kernel-symmetry content the spectral sum makes manifest).
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! Let `K(x,y) = (g y · h x)·W(x,y)` be the LHS kernel. Two legs:
//!
//! 1. **Fubini swap** `subsetSum_swap n (fun x y => K(x,y))` :
//!    `Σ_x Σ_y K(x,y) = Σ_y Σ_x K(x,y)`. Renaming the outer/inner binders, the
//!    RHS of this leg is `Σ_x Σ_y (g x · h y)·W(y,x)` (outer var plays the role
//!    of `y`, inner of `x`).
//! 2. **Kernel symmetry** `noiseDensityW_symm` (`W(y,x) = W(x,y)`) under a double
//!    `subsetSum_congr` + `congrArg (Rat.mul ((g x)·(h y)))` collapses
//!    `Σ_x Σ_y (g x · h y)·W(y,x)` to `Σ_x Σ_y (g x · h y)·W(x,y)` — the RHS.
//!
//! `Eq.trans` chains the two legs. Every leaf (`subsetSum_swap`,
//! `subsetSum_congr`, `congrArg`, `Eq.trans`, `noiseDensityW_symm`) is
//! `Constructive` with empty admitted-axiom closure, so this identity is too. No
//! axiom is added or removed. Idempotent.

#[cfg(test)]
use super::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use super::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Atoms for the self-adjointness identity.
#[cfg(test)]
struct SelfAdjConsts {
    nat: Expr,
    rat: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    noise_density: Expr,
    noise_density_symm: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_swap: Expr,
    congr_arg: Expr,
    eq1: Expr,
    eq_trans: Expr,
}

#[cfg(test)]
impl SelfAdjConsts {
    #[cfg(test)]
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            noise_density_symm: Expr::const_(
                Name::from_string("BoolAnalysis.noiseDensityW_symm"),
                vec![],
            ),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            subset_sum_swap: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_swap"), vec![]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
        }
    }

    #[cfg(test)]
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    #[cfg(test)]
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    #[cfg(test)]
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    #[cfg(test)]
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    #[cfg(test)]
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    #[cfg(test)]
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    #[cfg(test)]
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `@congrArg.{1,1} Rat Rat from to motive h : motive from = motive to`.
    #[cfg(test)]
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `subsetSum_congr n G H hyp : subsetSum n G = subsetSum n H`.
    #[cfg(test)]
    fn ssum_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    /// `noiseDensityW_symm ρ n x y : noiseDensityW ρ n x y = noiseDensityW ρ n y x`.
    #[cfg(test)]
    fn dens_symm(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density_symm.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }

    /// The LHS inner integrand `fun y => (g y · h x)·W(x,y)` (⟨T_ρ g, h⟩ form,
    /// `x` free): the `y` is summed, so the coefficient reads `g` at the summed
    /// slot `y` and `h` at the free slot `x`.
    #[cfg(test)]
    fn lhs_x_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        g: &Expr,
        h: &Expr,
        x: &Expr,
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = xb.fresh_local(hcp.clone());
        let coeff = self.mul(
            Expr::app(g.clone(), y.clone()),
            Expr::app(h.clone(), x.clone()),
        );
        let body = self.mul(coeff, self.density(rho, n, x, &y));
        xb.finish_child(xb.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
    /// The LHS outer integrand `fun x => Σ_y (g y · h x)·W(x,y)`.
    #[cfg(test)]
    fn lhs_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let inner = self.ssum(n, self.lhs_x_fn(&b, rho, n, g, h, &x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, inner))
    }
    /// The RHS outer integrand `fun x => Σ_y (g x · h y)·W(x,y)` (⟨g, T_ρ h⟩).
    #[cfg(test)]
    fn rhs_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let inner = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let coeff = self.mul(
                Expr::app(g.clone(), x.clone()),
                Expr::app(h.clone(), y.clone()),
            );
            let body = self.mul(coeff, self.density(rho, n, &x, &y));
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, self.ssum(n, inner)))
    }
    /// The post-swap MID outer integrand `fun x => Σ_y (g x · h y)·W(y,x)` (the
    /// `subsetSum_swap` RHS with binders renamed to match `rhs_fn` modulo the
    /// kernel argument order `W(y,x)`).
    #[cfg(test)]
    fn mid_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let inner = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let coeff = self.mul(
                Expr::app(g.clone(), x.clone()),
                Expr::app(h.clone(), y.clone()),
            );
            let body = self.mul(coeff, self.density(rho, n, &y, &x));
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, self.ssum(n, inner)))
    }
    /// The 2-arg swap kernel `fun x y => (g y · h x)·W(x,y)` for `subsetSum_swap`.
    /// `subsetSum_swap n F : Σ_x Σ_y F x y = Σ_y Σ_x F x y`.
    #[cfg(test)]
    fn swap_kernel(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        g: &Expr,
        h: &Expr,
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let lam_y = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let coeff = self.mul(
                Expr::app(g.clone(), y.clone()),
                Expr::app(h.clone(), x.clone()),
            );
            let body = self.mul(coeff, self.density(rho, n, &x, &y));
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, lam_y))
    }
}

/// `∀ (ρ : Rat) (n : Nat) (g h : HCPoint n → Rat), ⟨T_ρ g, h⟩ = ⟨g, T_ρ h⟩`.
#[cfg(test)]
fn build_type(c: &SelfAdjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let (h_id, h) = b.fresh_local(fn_ty.clone());
    let lhs = c.ssum(&n, c.lhs_fn(&b, &rho, &n, &g, &h));
    let rhs = c.ssum(&n, c.rhs_fn(&b, &rho, &n, &g, &h));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(h_id, BinderInfo::Default, fn_ty.clone(), concl);
    let e = b.mk_pi(g_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Body: `λ ρ n g h => Eq.trans LHS MID RHS swap symm_congr`.
#[cfg(test)]
fn build_value(c: &SelfAdjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let (h_id, h) = b.fresh_local(fn_ty.clone());
    let hcp = c.hcpoint_of(&n);

    let lhs = c.ssum(&n, c.lhs_fn(&b, &rho, &n, &g, &h));
    let mid = c.ssum(&n, c.mid_fn(&b, &rho, &n, &g, &h));
    let rhs = c.ssum(&n, c.rhs_fn(&b, &rho, &n, &g, &h));

    // leg1 (swap) : Σ_x Σ_y (g y·h x)·W(x,y) = Σ_x' Σ_y' (g x'·h y')·W(y',x')
    //   subsetSum_swap n K with K x y = (g y·h x)·W(x,y) gives
    //   Σ_x Σ_y K x y = Σ_x Σ_y K y x; reading the RHS, the outer binder plays the
    //   role previously played by `y` (now named x') and the inner by `x` (y'), so
    //   K (outer) (inner) = (g inner · h outer)·W(outer,inner)... but `subsetSum_swap`
    //   RHS is `fun o => Σ_i K i o`, i.e. Σ_o Σ_i (g o·h i)·W(i,o) = `mid`.
    let leg1 = Expr::apps(
        c.subset_sum_swap.clone(),
        [n.clone(), c.swap_kernel(&b, &rho, &n, &g, &h)],
    );

    // leg2 (kernel symmetry) : MID = RHS via double subsetSum_congr over
    //   noiseDensityW_symm (W(y,x) = W(x,y)) under congrArg ((g x·h y)·).
    let leg2 = {
        // outer hyp : ∀ x, (Σ_y (g x·h y)·W(y,x)) = (Σ_y (g x·h y)·W(x,y))
        let mut xb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        // inner integrands at fixed x: MID_in y = (g x·h y)·W(y,x); RHS_in y = (g x·h y)·W(x,y)
        let mid_in = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let coeff = c.mul(
                Expr::app(g.clone(), x.clone()),
                Expr::app(h.clone(), y.clone()),
            );
            let body = c.mul(coeff, c.density(&rho, &n, &y, &x));
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        let rhs_in = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let coeff = c.mul(
                Expr::app(g.clone(), x.clone()),
                Expr::app(h.clone(), y.clone()),
            );
            let body = c.mul(coeff, c.density(&rho, &n, &x, &y));
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        // inner hyp : ∀ y, (g x·h y)·W(y,x) = (g x·h y)·W(x,y)
        //   = fun y => congrArg ((g x·h y)·) (noiseDensityW_symm ρ n y x)
        let inner_hyp = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let coeff = c.mul(
                Expr::app(g.clone(), x.clone()),
                Expr::app(h.clone(), y.clone()),
            );
            let w_yx = c.density(&rho, &n, &y, &x);
            let w_xy = c.density(&rho, &n, &x, &y);
            let symm = c.dens_symm(&rho, &n, &y, &x); // W(y,x) = W(x,y)
                                                      // motive : fun (t : Rat) => (g x·h y)·t
            let motive = {
                let mut e = EnvDeclBuilder::child_of(&yb);
                let (t_id, t) = e.fresh_local(c.rat.clone());
                e.finish_child(e.mk_lam(
                    t_id,
                    BinderInfo::Default,
                    c.rat.clone(),
                    c.mul(coeff.clone(), t),
                ))
            };
            let body = c.congr_rat(w_yx, w_xy, motive, symm);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        let inner_congr = c.ssum_congr(&n, &mid_in, &rhs_in, inner_hyp);
        let outer_hyp =
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), inner_congr));
        c.ssum_congr(
            &n,
            &c.mid_fn(&b, &rho, &n, &g, &h),
            &c.rhs_fn(&b, &rho, &n, &g, &h),
            outer_hyp,
        )
    };

    let proof = c.trans(lhs, mid, rhs, leg1, leg2);

    let val = b.mk_lam(h_id, BinderInfo::Default, fn_ty.clone(), proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, fn_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val))
}

#[cfg(test)]
impl Environment {
    /// Register `BoolAnalysis.noise_pairing_self_adjoint` — the self-adjointness
    /// of the noise operator as a bilinear `subsetSum` inner-product identity
    /// `⟨T_ρ g, h⟩ = ⟨g, T_ρ h⟩`. `subsetSum_swap` (Fubini) chained with the
    /// kernel symmetry `noiseDensityW_symm` under a double `subsetSum_congr`.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    #[cfg(test)]
    pub(crate) fn register_noise_pairing_self_adjoint(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_pairing_self_adjoint");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_density_w_symm()?; // + noiseDensityW, subsetSum_congr, Rat.mul_comm
        self.register_subset_sum_swap_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = SelfAdjConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        let deps = env.axiom_deps(&nm).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
    }

    #[test]
    fn test_noise_pairing_self_adjoint_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_pairing_self_adjoint()
            .expect("register_noise_pairing_self_adjoint");
        env.register_noise_pairing_self_adjoint()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.noise_pairing_self_adjoint");
    }
}
