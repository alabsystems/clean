// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_pow4_spectral.rs — the type + proof builders for
// `pow4_noisefn_fourfold` (the noiseFn-specialized 4-fold expansion of the
// operator-side 4th moment).

/// Atoms specific to the `noiseFn`-side 4-fold expansion.
#[cfg(test)]
struct Pow4NoiseConsts {
    base: Pow4Consts,
    nat: Expr,
    rat: Expr,
    nat_pow: Expr,
    two: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    noise_density: Expr,
    noise_fn: Expr,
    fin: Expr,
    fin_sum_pow4: Expr,
}

#[cfg(test)]
impl Pow4NoiseConsts {
    #[cfg(test)]
    fn new() -> Self {
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        Self {
            base: Pow4Consts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two: Expr::app(nat_succ, nat_one),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            noise_fn: Expr::const_(Name::from_string("BoolAnalysis.noiseFn"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum_pow4: Expr::const_(Name::from_string("Fin.sum_pow4"), vec![]),
        }
    }

    #[cfg(test)]
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → Rat`.
    #[cfg(test)]
    fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    /// `Nat.pow 2 n`.
    #[cfg(test)]
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    /// `Fin (Nat.pow 2 n)`.
    #[cfg(test)]
    fn fin_pow(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), self.pow2(n))
    }
    /// `BoolAnalysis.hcDecode n k`.
    #[cfg(test)]
    fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), k.clone()])
    }
    /// `noiseDensityW ρ n x y`.
    #[cfg(test)]
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `noiseFn ρ n F jx`.
    #[cfg(test)]
    fn noise_fn(&self, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [rho.clone(), n.clone(), f.clone(), jx.clone()],
        )
    }
    /// `Fin.sum (2^n) g`.
    #[cfg(test)]
    fn sum_pow(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.base.fin_sum.clone(), [self.pow2(n), g])
    }

    /// `gx jx := fun (jy : Fin (2^n)) => F(decode jy)·noiseDensityW ρ n (decode jx)(decode jy)`
    /// — the `noiseFn` integrand at fixed `jx`, byte-for-byte the `noiseFn` body
    /// so `Fin.sum (2^n) (gx jx) ≡ noiseFn ρ n F jx`.
    #[cfg(test)]
    fn gx(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_pow(n);
        let (jy_id, jy) = b.fresh_local(fin_p.clone());
        let x = self.decode(n, jx);
        let y = self.decode(n, &jy);
        let f_y = Expr::app(f.clone(), y.clone());
        let dens = self.density(rho, n, &x, &y);
        let body = self.base.mul(f_y, dens);
        b.finish_child(b.mk_lam(jy_id, BinderInfo::Default, fin_p, body))
    }
}

/// The `pow4_noisefn_fourfold` conclusion type
/// `∀ (ρ : Rat) (n : Nat) (F : HCPoint n → Rat),
///    Fin.sum (2^n) (fun jx => pow4 (noiseFn ρ n F jx))
///      = Fin.sum (2^n) (fun jx => Σ_{j1}Σ_{j3}Σ_{j2}Σ_{j4}
///           (gx jx j1·gx jx j2)·(gx jx j3·gx jx j4))`
/// where `gx jx jy := F(decode jy)·noiseDensityW ρ n (decode jx)(decode jy)`.
#[cfg(test)]
fn build_fourfold_type(c: &Pow4NoiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, build_lhs_jx_fn(c, &b, &rho, &n, &f));
    let rhs = c.sum_pow(&n, build_rhs_jx_fn(c, &b, &rho, &n, &f));
    let concl = c.base.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

/// `fun (jx : Fin (2^n)) => pow4 (noiseFn ρ n F jx)`.
#[cfg(test)]
fn build_lhs_jx_fn(
    c: &Pow4NoiseConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_p = c.fin_pow(n);
    let (jx_id, jx) = b.fresh_local(fin_p.clone());
    let nf = c.noise_fn(rho, n, f, &jx);
    let body = pow4_of(&c.base, &nf);
    b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin_p, body))
}

/// `fun (jx : Fin (2^n)) => Σ_{j1}Σ_{j3}Σ_{j2}Σ_{j4} (g j1·g j2)·(g j3·g j4)`
/// where `g := gx jx`. This is `build_quad_rhs` of the base brick at `f := gx jx`,
/// over the `Fin (2^n)` index, so it is byte-for-byte the `Fin.sum_pow4 (2^n)
/// (gx jx)` RHS.
#[cfg(test)]
fn build_rhs_jx_fn(
    c: &Pow4NoiseConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_p = c.fin_pow(n);
    let (jx_id, jx) = b.fresh_local(fin_p.clone());
    let g = c.gx(&b, rho, n, f, &jx);
    let pow2n = c.pow2(n);
    let body = build_quad_rhs(&c.base, &b, &pow2n, &g);
    b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin_p, body))
}

/// `pow4 x := (x·x)·(x·x)` over the base atoms.
#[cfg(test)]
fn pow4_of(c: &Pow4Consts, x: &Expr) -> Expr {
    let sq = c.mul(x.clone(), x.clone());
    c.mul(sq.clone(), sq)
}

/// Proof of `pow4_noisefn_fourfold` : `Fin.sum_congr` over `jx` of the pointwise
/// `Fin.sum_pow4 (2^n) (gx jx)` (whose LHS `pow4(Fin.sum (2^n) (gx jx))` is
/// def-eq to `pow4(noiseFn ρ n F jx)`).
#[cfg(test)]
fn build_fourfold_value(c: &Pow4NoiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs_fn = build_lhs_jx_fn(c, &b, &rho, &n, &f);
    let rhs_fn = build_rhs_jx_fn(c, &b, &rho, &n, &f);

    // H : fun jx => (pow4 (noiseFn ρ n F jx) = quadRHS (gx jx))
    //   = Fin.sum_pow4 (2^n) (gx jx)   (LHS def-eq to pow4 (noiseFn …)).
    let h = {
        let mut jxb = EnvDeclBuilder::child_of(&b);
        let fin_p = c.fin_pow(&n);
        let (jx_id, jx) = jxb.fresh_local(fin_p.clone());
        let g = c.gx(&jxb, &rho, &n, &f, &jx);
        let pow2n = c.pow2(&n);
        let pf = Expr::apps(c.fin_sum_pow4.clone(), [pow2n, g]);
        jxb.finish_child(jxb.mk_lam(jx_id, BinderInfo::Default, fin_p, pf))
    };

    // Fin.sum_congr (2^n) lhs_fn rhs_fn H : Σ_jx pow4(noiseFn) = Σ_jx quadRHS.
    let pow2n = c.pow2(&n);
    let proof = Expr::apps(c.base.fin_sum_congr.clone(), [pow2n, lhs_fn, rhs_fn, h]);

    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}
