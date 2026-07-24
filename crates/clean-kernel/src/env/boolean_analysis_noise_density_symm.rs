// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Noise-operator self-adjointness — the symmetry atom toward the DUAL HC bound.
//!
//! ## Why this lemma exists
//!
//! The sharp-KKL retirement (`designs/2026-06-18-kkl-root-free-obstruction.md`)
//! is walled by the dual `(4/3→2)` hypercontractive bound
//! `‖T_{1/3} D_i f‖₂² ≤ 4·Inf_i^{3/2}`. The standard derivation of that bound
//! from the LANDED forward `(2→4)` bound (`hc24_at_third`) goes through the
//! SELF-ADJOINTNESS of the noise operator `T_ρ`:
//!
//! ```text
//!   <T_ρ g, h>  =  <g, T_ρ h>          (T_ρ self-adjoint)
//! ```
//!
//! which itself reduces to the SYMMETRY of the noise density:
//!
//! ```text
//!   noiseDensityW ρ n x y  =  noiseDensityW ρ n y x.
//! ```
//!
//! This file lands that symmetry atom AND the un-normalized self-adjoint pairing
//! identity it implies. Both are genuine constructive Theorems with EMPTY
//! domain-axiom closure (`ProofQuality::Constructive`) — NO axiom is introduced,
//! so no trust is relocated.
//!
//! ## The density-symmetry lemma (constructive, empty closure)
//!
//! ```text
//! BoolAnalysis.noiseDensityW_symm :
//!   ∀ (ρ : Rat) (n : Nat) (x y : HCPoint n),
//!     noiseDensityW ρ n x y = noiseDensityW ρ n y x
//! ```
//!
//! `noiseDensityW ρ n x y` δ-unfolds (it is a reducible Definition) to
//! `subsetSum n (fun S => ρ^{|S|}·(χ_S x · χ_S y))`. Swapping `x,y` gives
//! `subsetSum n (fun S => ρ^{|S|}·(χ_S y · χ_S x))`. The two integrands agree
//! pointwise by `Rat.mul_comm (χ_S x) (χ_S y)`, lifted through the `ρ^{|S|}·_`
//! head via `congrArg`; `subsetSum_congr` then lifts the pointwise equality to
//! the sums. The `noiseDensityW` head being reducible makes the
//! `subsetSum_congr` output def-eq to the stated `noiseDensityW _ _ x y =
//! noiseDensityW _ _ y x` goal.
//!
//! ## The self-adjoint pairing identity (constructive, empty closure)
//!
//! ```text
//! BoolAnalysis.noiseDensityW_pair_symm :
//!   ∀ (ρ : Rat) (n : Nat) (x y : HCPoint n) (a b : Rat),
//!     (a·b)·noiseDensityW ρ n x y = (b·a)·noiseDensityW ρ n y x
//! ```
//!
//! This is the per-`(x,y)` summand of the bilinear pairing
//! `Σ_x Σ_y a(x)·b(y)·dens(x,y)` — symmetric under the simultaneous swap of the
//! coefficient pair `(a,b)` and the density arguments `(x,y)`. It is the leaf the
//! full `<T_ρ g, h> = <h, T_ρ g>` Fubini-symmetry would consume; landing it
//! records the self-adjoint content at the summand level where it is unambiguous
//! and root-free. Proof: `Rat.mul_comm a b` on the left factor + `noiseDensityW_symm`
//! on the right factor, combined by congruence on `Rat.mul`.
//!
//! ## Honest scope
//!
//! These two facts are the SYMMETRY half of self-adjointness. The full operator
//! identity `<T_ρ g, h> = <g, T_ρ h>` over the un-normalized `Fin.sum (2^n)`
//! cube requires, in addition, a Fubini double-sum swap (`subsetSum_swap`, landed)
//! threaded through the `noiseFn` decode telescope — assembled but not closed in
//! this pass. The dual HC bound ABOVE self-adjointness additionally needs a
//! discrete Hölder for the fractional conjugate pair `(4/3, 4)`, which is NOT
//! `Rat`-expressible without a fractional-power carrier on a non-perfect-square
//! base (the genuine residual — see the report-back). NO axiom is admitted here.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the density-symmetry lemmas.
struct DensitySymmConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat_mul: Expr,
    mul_comm: Expr,
    pow_nat: Expr,
    chi: Expr,
    subset_sum_congr: Expr,
    noise_density: Expr,
    eq1: Expr,
}

impl DensitySymmConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            rat_mul: k("Rat.mul"),
            mul_comm: k("Rat.mul_comm"),
            pow_nat: k("Rat.powNat"),
            chi: k("BoolAnalysis.chi"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn chi_of(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn pow(&self, rho: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [rho.clone(), k.clone()])
    }
    /// `noiseDensityW ρ n x y`.
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `congrArg.{1,1} Rat Rat from to f h : f from = f to`.
    fn congr_arg(&self, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        let u1 = Level::succ(Level::zero());
        let congr = Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]);
        Expr::apps(congr, [self.rat.clone(), self.rat.clone(), from, to, f, h])
    }
    /// `Eq.trans.{1} Rat a b c h1 h2 : a = c`.
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_trans, [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `subsetSum_congr n G H hpw : subsetSum n G = subsetSum n H`.
    fn subset_sum_congr_of(&self, n: &Expr, g: Expr, h: Expr, hpw: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, hpw])
    }
    /// `indNat (S i) = @Bool.rec.{1} (fun _ => Nat) 0 1 (S i)` — byte-for-byte
    /// the `NoiseConsts::ind_nat` build (so the integrand δ-matches noiseDensityW).
    fn ind_nat(&self, s_i: Expr) -> Expr {
        let nat_one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        let bool_rec_nat = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(
            bool_rec_nat,
            [nat_motive, self.nat_zero.clone(), nat_one, s_i],
        )
    }
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — byte-for-byte the
    /// `NoiseConsts::popcount` build.
    fn popcount(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(Expr::app(s.clone(), i.clone()));
        let pc_fn = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            [n.clone(), pc_fn],
        )
    }
    /// The ρ-weighted subset integrand `fun S => ρ^{pc n S}·(χ_S x · χ_S y)` —
    /// byte-for-byte the `NoiseConsts::ss_int_rho` build, so `subsetSum n (this)`
    /// is def-eq (reducible δ) to `noiseDensityW ρ n x y`.
    fn density_integrand(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let weight = self.pow(rho, &self.popcount(&b, n, &s));
        let chis = self.mul(self.chi_of(n, &s, x), self.chi_of(n, &s, y));
        let body = self.mul(weight, chis);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register both density-symmetry facts. Idempotent. Standalone (not wired
    /// into `init_boolean_analysis`); no axiom added or removed.
    pub fn init_boolean_analysis_noise_density_symm(&mut self) -> Result<(), EnvError> {
        self.register_noise_density_w_symm()?;
        self.register_noise_density_w_pair_symm()?;
        Ok(())
    }

    /// `BoolAnalysis.noiseDensityW_symm :
    ///    ∀ ρ n x y, noiseDensityW ρ n x y = noiseDensityW ρ n y x`.
    /// Constructive, empty closure. The symmetry atom of `T_ρ` self-adjointness.
    pub fn register_noise_density_w_symm(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseDensityW_symm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_density_w()?; // noiseDensityW (+ chi, powNat, subsetSum)
        self.register_subset_sum_congr()?; // subsetSum_congr
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = DensitySymmConsts::new();

        // Type: ∀ ρ n x y, noiseDensityW ρ n x y = noiseDensityW ρ n y x.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = b.fresh_local(hcp.clone());
            let (y_id, y) = b.fresh_local(hcp.clone());
            let concl = c.eq_rat(c.density(&rho, &n, &x, &y), c.density(&rho, &n, &y, &x));
            let e = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, hcp, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        // Value: fun ρ n x y =>
        //   subsetSum_congr n (int x y) (int y x) (fun S => congrArg (ρ^|S|·_) (mul_comm ...)).
        // `int x y := fun S => ρ^{pc n S}·(χ_S x · χ_S y)` is byte-for-byte the
        // `noiseDensityW` integrand, so `subsetSum n (int x y)` is def-eq to
        // `noiseDensityW ρ n x y` (reducible δ), and likewise the y-x side.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = b.fresh_local(hcp.clone());
            let (y_id, y) = b.fresh_local(hcp.clone());

            // The two integrands.
            let int_xy = c.density_integrand(&b, &rho, &n, &x, &y);
            let int_yx = c.density_integrand(&b, &rho, &n, &y, &x);

            // Pointwise hypothesis: fun (S : HCPoint n) =>
            //   congrArg (fun t => ρ^{pc n S}·t)
            //            (χ_S x · χ_S y) (χ_S y · χ_S x) (mul_comm (χ_S x) (χ_S y)).
            let hpw = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (s_id, s) = d.fresh_local(hcp.clone());
                let weight = c.pow(&rho, &c.popcount(&d, &n, &s));
                let chi_x = c.chi_of(&n, &s, &x);
                let chi_y = c.chi_of(&n, &s, &y);
                let from = c.mul(chi_x.clone(), chi_y.clone()); // χ_S x · χ_S y
                let to = c.mul(chi_y.clone(), chi_x.clone()); // χ_S y · χ_S x
                let comm = c.mul_comm_of(chi_x, chi_y);
                // f := fun t => ρ^{|S|}·t.
                let f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (t_id, t) = e.fresh_local(c.rat.clone());
                    let body = c.mul(weight.clone(), t);
                    e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let body = c.congr_arg(from, to, f, comm);
                d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
            };

            let body = c.subset_sum_congr_of(&n, int_xy, int_yx, hpw);
            let e = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, hcp, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.noiseDensityW_pair_symm :
    ///    ∀ ρ n x y a b, (a·b)·noiseDensityW ρ n x y = (b·a)·noiseDensityW ρ n y x`.
    /// The self-adjoint content at the bilinear-pairing summand level.
    /// Constructive, empty closure.
    pub fn register_noise_density_w_pair_symm(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseDensityW_pair_symm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_density_w_symm()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = DensitySymmConsts::new();
        let noise_symm = Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW_symm"), vec![]);

        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = b.fresh_local(hcp.clone());
            let (y_id, y) = b.fresh_local(hcp.clone());
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bb_id, bb) = b.fresh_local(c.rat.clone());

            let dens_xy = c.density(&rho, &n, &x, &y);
            let dens_yx = c.density(&rho, &n, &y, &x);
            let ab = c.mul(a.clone(), bb.clone()); // a·b
            let ba = c.mul(bb.clone(), a.clone()); // b·a
            let lhs = c.mul(ab.clone(), dens_xy.clone());
            let rhs = c.mul(ba.clone(), dens_yx.clone());
            let concl = c.eq_rat(lhs.clone(), rhs.clone());

            let tail = if for_value {
                // Step 1: (a·b)·dens_xy = (b·a)·dens_xy   [congrArg (·dens_xy) (mul_comm a b)]
                let f1 = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.mul(t, dens_xy.clone());
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let h1 = c.congr_arg(
                    ab.clone(),
                    ba.clone(),
                    f1,
                    c.mul_comm_of(a.clone(), bb.clone()),
                );
                let mid = c.mul(ba.clone(), dens_xy.clone()); // (b·a)·dens_xy

                // Step 2: (b·a)·dens_xy = (b·a)·dens_yx   [congrArg ((b·a)·_) (noise_symm ...)]
                let f2 = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.mul(ba.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let h_dens = Expr::apps(
                    noise_symm.clone(),
                    [rho.clone(), n.clone(), x.clone(), y.clone()],
                ); // dens_xy = dens_yx
                let h2 = c.congr_arg(dens_xy.clone(), dens_yx.clone(), f2, h_dens);

                c.trans(lhs, mid, rhs, h1, h2)
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
            let e = bind(&b, bb_id, c.rat.clone(), tail);
            let e = bind(&b, a_id, c.rat.clone(), e);
            let e = bind(&b, y_id, hcp.clone(), e);
            let e = bind(&b, x_id, hcp, e);
            let e = bind(&b, n_id, c.nat.clone(), e);
            let e = bind(&b, rho_id, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "BoolAnalysis.noiseDensityW_symm",
        "BoolAnalysis.noiseDensityW_pair_symm",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_noise_density_symm()
            .expect("init_boolean_analysis_noise_density_symm");
        env.init_boolean_analysis_noise_density_symm()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_noise_density_symm_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} transitive axiom closure must be empty"
            );
        }
    }
}
