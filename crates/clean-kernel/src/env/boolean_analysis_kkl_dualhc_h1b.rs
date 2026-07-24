// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC connect — H1 STEP 2a: the `W_i` spectral → band-form bridge.
//!
//! ## What this proves
//!
//! Lifting the per-`S` identity (`dualhc_per_s_spectral`, H1 STEP 1) across the
//! `subsetSum`, then pulling the constant `D·D` (`= 4^n`) OUT of the sum and
//! reassociating the cube factor, the dual-HC `W_i` collapses to the `8^n`-scaled
//! `(1/9)^{|S|}`-weighted band-feedstock sum:
//!
//! ```text
//! BoolAnalysis.dualhc_W_eq_band_form :
//!   ∀ (n : Nat) (f : BoolFn n) (i : Fin n),
//!     @Eq Rat
//!       (subsetSum n (fun y => noiseOp third n (D_i b) y · noiseOp third n (D_i b) y))
//!       (Rat.mul (Rat.mul D (Rat.mul D D))                       -- D·(D·D) = 8^n (ofNat-spelling)
//!                (subsetSum n (fun S =>
//!                   Rat.mul (Rat.powNat (third·third) (setSizeNat n S)) -- (1/9)^{|S|}
//!                           (Rat.mul (Rat.mul 4 (ind (S i)))      -- 4·ind(S i)
//!                                    (FourierCoefficient n f S · FourierCoefficient n f S)))))
//! ```
//!
//! with `third := Rat.mk (Int.ofNat 1) 3`, `D := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1
//! ≡ 2^n` (the `dualhc_W_eq_spectral` `cube`), `b := pm∘f := fun x => pm (f x)`,
//! `D_i b x := b x − b (hcFlip n x i)`. The `D·(D·D)` measure is the
//! `ofNat(2^n)`-spelling of `8^n` (its reconcile to `Rat.powNat 8 n` is the named
//! downstream STEP-2b spelling-rewrite via `dualhc_pow8_eq_two_pow_cube` ∘
//! `powNat_two_eq_ofNat_pow`).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Let `D := cube n`, `P := third·third`, `lw := levelWt third n S`,
//! `Ad := A(D_i b,S)`, `w S := (4·ind(S i))·(f̂·f̂)`, and the band integrand
//! `G_band S := P^{|S|}·((D·D)·(w S))`, the pulled integrand `G_pull S :=
//! (D·D)·(P^{|S|}·(w S))`, the feedstock integrand `g S := P^{|S|}·(w S)`.
//!
//! 1. `dualhc_W_eq_spectral n (D_i b)` : `W_i = D·Σ_S [lw·(Ad·Ad)]`.
//! 2. per-`S` (`dualhc_per_s_spectral n f S i`) lifted by `subsetSum_congr`:
//!    `Σ_S [lw·(Ad·Ad)] = Σ_S G_band S`. `congrArg (D·)`.
//! 3. per-`S` regroup `G_band S = G_pull S` (`P^{|S|}·((D·D)·w) = (D·D)·(P^{|S|}·w)`
//!    via `mul_assoc⁻¹ ∘ mul_comm ∘ mul_assoc` — the `mul_left_comm` move) lifted
//!    by `subsetSum_congr`: `Σ_S G_band S = Σ_S G_pull S`. `congrArg (D·)`.
//! 4. `subsetSum_smul n (D·D) g` : `Σ_S G_pull S = (D·D)·Σ_S g S`. `congrArg (D·)`,
//!    landing `D·Σ_S G_pull = D·((D·D)·Σ_S g)`.
//! 5. `symm (mul_assoc D (D·D) (Σ_S g))` : `D·((D·D)·Σ) = (D·(D·D))·Σ`.
//! 6. `Eq.trans` chains (1)·(2)·(3)·(4)·(5).
//!
//! Every leaf (`dualhc_W_eq_spectral`, `dualhc_per_s_spectral`, `subsetSum_congr`,
//! `subsetSum_smul`, `Rat.mul_assoc`, `Rat.mul_comm`, `Eq.refl/symm/trans/congrArg`)
//! is a landed `Constructive` Theorem with empty closure, so this is too. NO axiom
//! is added or removed. NOT wired into the always-on `init_boolean_analysis`
//! aggregate (reachable via `init_boolean_analysis_kkl_dualhc_h1`). Idempotent.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the `W_i` band-form bridge. All spellings are byte-for-byte
/// the landed `WSpectralConsts` / `H1Consts` conventions so the brick instances
/// stay def-eq to their endpoints.
struct H1bConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    pm: Expr,
    ind: Expr,
    chi: Expr,
    hc_flip: Expr,
    noise_op: Expr,
    level_wt: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_smul: Expr,
    fourier_coeff: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl H1bConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            chi: k("BoolAnalysis.chi"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            noise_op: k("BoolAnalysis.noiseOp"),
            level_wt: k("BoolAnalysis.levelWt"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            fourier_coeff: k("BoolAnalysis.FourierCoefficient"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one_nat())
    }
    fn three_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.two_nat())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `D := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1 ≡ 2^n` — byte-for-byte
    /// `WSpectralConsts::cube` / `H1Consts::cube`.
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    /// `third := Rat.mk (Int.ofNat 1) 3`.
    fn third(&self) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.one_nat());
        Expr::apps(self.rat_mk.clone(), [ofnat, self.three_nat()])
    }
    /// `four := Rat.mk (Int.ofNat 4) 1`.
    fn four(&self) -> Expr {
        let four_nat = Expr::app(
            self.nat_succ.clone(),
            Expr::app(self.nat_succ.clone(), self.two_nat()),
        );
        let ofnat = Expr::app(self.int_of_nat.clone(), four_nat);
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn pow(&self, base: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [base.clone(), k.clone()])
    }
    fn pm_(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn ind_(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn hc_flip_(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn op(&self, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(self.noise_op.clone(), [rho.clone(), n.clone(), g.clone()])
    }
    fn level_wt(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.level_wt.clone(), [rho.clone(), n.clone(), s.clone()])
    }
    fn set_size_nat(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn ssum_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    fn ssum_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum_smul.clone(),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    fn fcoeff(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            self.fourier_coeff.clone(),
            [n.clone(), f.clone(), s.clone()],
        )
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn congr(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    fn mul_left_motive(&self, parent: &EnvDeclBuilder, left: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(left.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    fn mul_right_motive(&self, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(z, right.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }

    /// `pm∘f := fun x => pm (f x)`.
    fn pm_f(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.pm_(Expr::app(f.clone(), x.clone()));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `D_i b := fun x => b x − b (hcFlip n x i)`.
    fn deriv(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.sub(
            Expr::app(b.clone(), x.clone()),
            Expr::app(b.clone(), self.hc_flip_(n, &x, i)),
        );
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `A(g,S) := subsetSum n (fun y => (g y)·(chi n S y))`.
    fn acoeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), y.clone()), self.chi_(n, s, &y));
        let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    // ── the four S-integrands ───────────────────────────────────────────────
    /// `w S := (4·ind(S i))·(f̂·f̂)` — the band feedstock weight.
    fn w_s(&self, n: &Expr, f: &Expr, s: &Expr, i: &Expr) -> Expr {
        let si = Expr::app(s.clone(), i.clone());
        let c4 = self.mul(self.four(), self.ind_(si));
        let fhat = self.fcoeff(n, f, s);
        self.mul(c4, self.mul(fhat.clone(), fhat))
    }
    /// `G_spec S := levelWt third n S · (A(D_i b,S)·A(D_i b,S))` — the
    /// `spec_rhs_s_fn` integrand at `g = D_i b` (the `dualhc_W_eq_spectral` RHS sum).
    fn g_spec_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let bf = self.pm_f(&b, n, f);
        let db = self.deriv(&b, n, &bf, i);
        let ad = self.acoeff(&b, n, &db, &s);
        let lw = self.level_wt(&self.third(), n, &s);
        let body = self.mul(lw, self.mul(ad.clone(), ad));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `G_band S := P^{|S|}·((D·D)·(w S))` — the `dualhc_per_s_spectral` RHS.
    fn g_band_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let p_base = self.mul(self.third(), self.third());
        let p_pow = self.pow(&p_base, &self.set_size_nat(n, &s));
        let dd = {
            let d = self.cube(n);
            self.mul(d.clone(), d)
        };
        let body = self.mul(p_pow, self.mul(dd, self.w_s(n, f, &s, i)));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `G_pull S := (D·D)·(P^{|S|}·(w S))`.
    fn g_pull_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let p_base = self.mul(self.third(), self.third());
        let p_pow = self.pow(&p_base, &self.set_size_nat(n, &s));
        let dd = {
            let d = self.cube(n);
            self.mul(d.clone(), d)
        };
        let body = self.mul(dd, self.mul(p_pow, self.w_s(n, f, &s, i)));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `g S := P^{|S|}·(w S)` — the inner feedstock integrand (D·D pulled out).
    fn g_feed_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let p_base = self.mul(self.third(), self.third());
        let p_pow = self.pow(&p_base, &self.set_size_nat(n, &s));
        let body = self.mul(p_pow, self.w_s(n, f, &s, i));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// `BoolAnalysis.dualhc_W_eq_band_form` — see the module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_w_eq_band_form(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_W_eq_band_form");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_noise_op()?;
        self.register_dualhc_w_eq_spectral()?;
        self.register_dualhc_per_s_spectral()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = H1bConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_band_form(&c, false),
            value: build_band_form(&c, true),
        })
    }
}

fn build_band_form(c: &H1bConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let third = c.third();
    let dcap = c.cube(&n); // D
    let dd = c.mul(dcap.clone(), dcap.clone()); // D·D
    let d_dd = c.mul(dcap.clone(), dd.clone()); // D·(D·D)

    // LHS : W_i = Σ_y (noiseOp third n (D_i b) y)²
    let bf = c.pm_f(&b, &n, &f);
    let db = c.deriv(&b, &n, &bf, &i);
    let tg = c.op(&third, &n, &db);
    let lhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let tgy = Expr::app(tg.clone(), y.clone());
        let body = c.mul(tgy.clone(), tgy);
        let yfn = d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp, body));
        c.ssum(&n, yfn)
    };

    // integrands
    let g_spec = c.g_spec_fn(&b, &n, &f, &i);
    let g_band = c.g_band_fn(&b, &n, &f, &i);
    let g_pull = c.g_pull_fn(&b, &n, &f, &i);
    let g_feed = c.g_feed_fn(&b, &n, &f, &i);

    let sum_spec = c.ssum(&n, g_spec.clone());
    let sum_band = c.ssum(&n, g_band.clone());
    let sum_pull = c.ssum(&n, g_pull.clone());
    let sum_feed = c.ssum(&n, g_feed.clone());

    let rhs = c.mul(d_dd.clone(), sum_feed.clone());
    let concl = c.eq_rat(lhs.clone(), rhs.clone());

    let tail = if for_value {
        // (1) wsp : W_i = D·Σ_S G_spec
        let wsp = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_W_eq_spectral"),
                vec![],
            ),
            [n.clone(), db.clone()],
        );
        let d_sum_spec = c.mul(dcap.clone(), sum_spec.clone()); // D·Σ_S G_spec

        // (2) per-S : G_spec S = G_band S  ⇒  Σ_S G_spec = Σ_S G_band, lifted by D·
        let pointwise_2 = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let body = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.dualhc_per_s_spectral"),
                    vec![],
                ),
                [n.clone(), f.clone(), s.clone(), i.clone()],
            );
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        let congr_spec_band = c.ssum_congr(&n, &g_spec, &g_band, pointwise_2);
        let leg2 = {
            let mot = c.mul_left_motive(&b, &dcap);
            c.congr(sum_spec.clone(), sum_band.clone(), mot, congr_spec_band)
        };
        let d_sum_band = c.mul(dcap.clone(), sum_band.clone());

        // (3) regroup : G_band S = G_pull S
        //   P^|S|·((D·D)·w) = (D·D)·(P^|S|·w)  via mul_left_comm:
        //     P·((D·D)·w) =[symm assoc P (D·D) w] (P·(D·D))·w
        //                 =[congr (·w) (mul_comm P (D·D))] ((D·D)·P)·w
        //                 =[assoc (D·D) P w] (D·D)·(P·w)
        let pointwise_3 = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let p_base = c.mul(third.clone(), third.clone());
            let p_pow = c.pow(&p_base, &c.set_size_nat(&n, &s));
            let w = c.w_s(&n, &f, &s, &i);
            let dd_l = c.mul(dcap.clone(), dcap.clone());
            // endpoints
            let dd_w = c.mul(dd_l.clone(), w.clone()); // (D·D)·w
            let lhs3 = c.mul(p_pow.clone(), dd_w.clone()); // P·((D·D)·w)  = G_band S
            let p_dd = c.mul(p_pow.clone(), dd_l.clone()); // P·(D·D)
            let pdd_w = c.mul(p_dd.clone(), w.clone()); // (P·(D·D))·w
            let dd_p = c.mul(dd_l.clone(), p_pow.clone()); // (D·D)·P
            let ddp_w = c.mul(dd_p.clone(), w.clone()); // ((D·D)·P)·w
            let p_w = c.mul(p_pow.clone(), w.clone()); // P·w
            let rhs3 = c.mul(dd_l.clone(), p_w.clone()); // (D·D)·(P·w)  = G_pull S
                                                         // d1 : P·((D·D)·w) = (P·(D·D))·w   [symm (mul_assoc P (D·D) w)]
            let assoc1 = c.mul_assoc(p_pow.clone(), dd_l.clone(), w.clone()); // (P·(D·D))·w = P·((D·D)·w)
            let d1 = c.symm(pdd_w.clone(), lhs3.clone(), assoc1);
            // d2 : (P·(D·D))·w = ((D·D)·P)·w   [congr (·w) (mul_comm P (D·D))]
            let mc = c.mul_comm(p_pow.clone(), dd_l.clone()); // P·(D·D) = (D·D)·P
            let mot_w = c.mul_right_motive(&d, &w);
            let d2 = c.congr(p_dd.clone(), dd_p.clone(), mot_w, mc);
            // d3 : ((D·D)·P)·w = (D·D)·(P·w)   [mul_assoc (D·D) P w]
            let d3 = c.mul_assoc(dd_l.clone(), p_pow.clone(), w.clone());
            let r12 = c.trans(lhs3.clone(), pdd_w.clone(), ddp_w.clone(), d1, d2);
            let body = c.trans(lhs3.clone(), ddp_w.clone(), rhs3.clone(), r12, d3);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        let congr_band_pull = c.ssum_congr(&n, &g_band, &g_pull, pointwise_3);
        let leg3 = {
            let mot = c.mul_left_motive(&b, &dcap);
            c.congr(sum_band.clone(), sum_pull.clone(), mot, congr_band_pull)
        };
        let d_sum_pull = c.mul(dcap.clone(), sum_pull.clone());

        // (4) smul : Σ_S G_pull = (D·D)·Σ_S g_feed, lifted by D·
        let smul = c.ssum_smul(&n, &dd, &g_feed); // Σ_S (D·D)·(g_feed S) = (D·D)·Σ_S g_feed
        let dd_sum_feed = c.mul(dd.clone(), sum_feed.clone()); // (D·D)·Σ g
        let leg4 = {
            let mot = c.mul_left_motive(&b, &dcap);
            c.congr(sum_pull.clone(), dd_sum_feed.clone(), mot, smul)
        };
        let d_dd_sum_feed = c.mul(dcap.clone(), dd_sum_feed.clone()); // D·((D·D)·Σ)

        // (5) assoc : D·((D·D)·Σ) = (D·(D·D))·Σ   [symm (mul_assoc D (D·D) Σ)]
        let assoc5 = c.mul_assoc(dcap.clone(), dd.clone(), sum_feed.clone()); // (D·(D·D))·Σ = D·((D·D)·Σ)
        let leg5 = c.symm(rhs.clone(), d_dd_sum_feed.clone(), assoc5);

        // chain: W_i =[wsp] D·Σ_spec =[leg2] D·Σ_band =[leg3] D·Σ_pull
        //            =[leg4] D·((D·D)·Σ) =[leg5] (D·(D·D))·Σ = rhs
        let t1 = c.trans(
            lhs.clone(),
            d_sum_spec.clone(),
            d_sum_band.clone(),
            wsp,
            leg2,
        );
        let t2 = c.trans(
            lhs.clone(),
            d_sum_band.clone(),
            d_sum_pull.clone(),
            t1,
            leg3,
        );
        let t3 = c.trans(
            lhs.clone(),
            d_sum_pull.clone(),
            d_dd_sum_feed.clone(),
            t2,
            leg4,
        );
        c.trans(lhs.clone(), d_dd_sum_feed.clone(), rhs.clone(), t3, leg5)
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
    let e = bind(&b, i_id, c.fin_of(&n), tail);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, n_id, c.nat.clone(), e);
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
        env.register_dualhc_w_eq_band_form()
            .expect("register_dualhc_w_eq_band_form");
        env.register_dualhc_w_eq_band_form().expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
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

    #[test]
    fn test_dualhc_w_eq_band_form_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.dualhc_W_eq_band_form");
    }
}
