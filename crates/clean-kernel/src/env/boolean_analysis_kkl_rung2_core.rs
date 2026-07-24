// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **rung 2 combinatorial core** (`rung2-core`).
//!
//! The double-count + normalization half of rung 2: it scales the landed
//! double-count inequality `M_{1..k} ≤ DC-RHS`
//! ([`BoolAnalysis.lowband_double_count_le`]) by the positive factor `4·4^n`,
//! then transports the scaled RHS back through the normalization-reconciliation
//! ([`BoolAnalysis.deg_band_rhs_eq_pow4_mass`]) and the degree-band identity
//! ([`BoolAnalysis.summed_deriv_lowband_eq_weighted`] at `b := pm∘f`) to land
//!
//! ```text
//! BoolAnalysis.kkl_pow4_mass_le_summed_deriv :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     Rat.le
//!       (Rat.mul (Rat.mul 4 (Rat.powNat 4 n))
//!                (subsetSum n (fun S =>
//!                    ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                                  (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!                      · (f̂ S · f̂ S))))                                  -- (4·4^n)·M_{1..k}
//!       (Fin.sum n (fun i =>
//!           subsetSum n (fun S =>
//!               ind (Nat.ble (setSizeNat n S) k)
//!                 · (Acoeff n (D_i (pm∘f)) S · Acoeff n (D_i (pm∘f)) S)))) -- Σ_i W^{≤k}[D_i(pm∘f)]
//! ```
//!
//! i.e. `(4·4^n)·M_{1..k} ≤ Σ_i W^{≤k}[D_i(pm∘f)]`, where
//!   * `M_{1..k} := subsetSum n (fun S => ind(band)·(f̂·f̂))` is the non-empty
//!     low-degree Fourier mass (`f̂ := FourierCoefficient`, byte-identical to the
//!     keystone `m_lo_fn`), and
//!   * `D_i (pm∘f) := fun x => (pm∘f) x − (pm∘f) (hcFlip n x i)` is the derivative
//!     of `pm∘f` (which β-reduces to `fun x => pm(f x) − pm(f(hcFlip n x i))`, the
//!     `dualhc` aggregate's `deriv_lam`).
//!
//! This is the **double-count side** of rung 2: it converts the genuinely-`f̂`
//! low-band mass into the `Σ_i W^{≤k}` derivative form, exactly as O'Donnell's
//! §9.6 spectral double-count requires, with all `4`/`4^n` bookkeeping exact.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! Let `P := 4·4^n`, `M := M_{1..k}`, `DC := DC-RHS`,
//! `Σ := Σ_i W^{≤k}[D_i(pm∘f)]`, `R := deg-band RHS @ b:=pm∘f`.
//!
//! 1. `h_dc : M ≤ DC`     — `lowband_double_count_le n k f`.
//! 2. `h_P_nn : 0 ≤ P`    — `mul_nonneg 4 (4^n) (0≤4) (powNat_nonneg 4 n (0≤4))`.
//! 3. `h_scaled : P·M ≤ P·DC`  — `mul_le_mul_of_nonneg_left P M DC h_dc h_P_nn`.
//! 4. `h_recon : R = P·DC`     — `deg_band_rhs_eq_pow4_mass n k f`.
//! 5. `h_deg : Σ = R`          — `summed_deriv_lowband_eq_weighted n k (pm∘f)`.
//! 6. `h_eq : P·DC = Σ`        — `symm (trans h_deg h_recon)`.
//! 7. `Eq.subst (motive t => P·M ≤ t) h_eq h_scaled : P·M ≤ Σ`.
//!
//! Every leaf (`lowband_double_count_le`, `deg_band_rhs_eq_pow4_mass`,
//! `summed_deriv_lowband_eq_weighted`, `Rat.mul_le_mul_of_nonneg_left`,
//! `Rat.mul_nonneg`, `Rat.powNat_nonneg`, `Rat.le_of_ble_eq_true`, `Eq.*`) is
//! `Constructive` with empty admitted-axiom closure, so this rung is too. No axiom
//! added/removed. Idempotent. Gated behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the rung-2 combinatorial core. Carrier spellings byte-match
/// the consumed double-count / norm-reconcile / deg-band carriers.
struct Rung2CoreConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    pm: Expr,
    subset_sum: Expr,
    fourier: Expr,
    ind: Expr,
    set_size_nat: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    rat_zero: Expr,
    l1: Level,
}

impl Rung2CoreConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            pm: k("BoolAnalysis.pm"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            ind: k("BoolAnalysis.ind"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            rat_zero: k("Rat.zero"),
            l1,
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_one(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    /// `(4 : Rat) := mk(ofNat 4) 1` — byte-match deg-band / norm-reconcile `four`.
    fn four(&self) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(4)),
                self.nat_one(),
            ],
        )
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `4^n := powNat 4 n`.
    fn pow4(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.four(), n.clone()])
    }
    /// `P := 4·4^n`.
    fn p_factor(&self, n: &Expr) -> Expr {
        self.mul(self.four(), self.pow4(n))
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn x_sq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.nat_one(), m)
    }
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    /// the non-empty band `Bool.and (ble 1 |S|) (not (ble (k+1) |S|))`.
    fn band_bit(&self, n: &Expr, k: &Expr, s: &Expr) -> Expr {
        let m = self.set_size_nat_of(n, s);
        Expr::apps(
            self.bool_and.clone(),
            [
                self.ble1(m.clone()),
                Expr::app(self.bool_not.clone(), self.ble_succ_k(k, m)),
            ],
        )
    }
    /// `LE.le @Rat instLERat a b` — byte-match `lowband_double_count_le`'s `≤`.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }

    /// `M_{1..k} := subsetSum n (fun S => ind(band)·(f̂·f̂))` — the keystone
    /// non-empty low-band mass (byte-identical to `lowband_double_count_le`'s LHS).
    fn m_mass(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let body = self.mul(self.ind_of(self.band_bit(n, k, &s)), self.x_sq(n, f, &s));
        let g = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }
    /// `pm∘f := fun (x : HCPoint n) => pm (f x)` — the deg-band carrier `b`.
    fn pm_f(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    // ── Eq / nonneg plumbing ──────────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `Rat.le_of_ble_eq_true 0 v refl : 0 ≤ v` (native `ble` reduction idiom).
    fn zero_le_lit(&self, v: &Expr) -> Expr {
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [bool_c, btrue],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            [self.rat_zero.clone(), v.clone(), refl],
        )
    }
    /// `Rat.powNat_nonneg b k h : 0 ≤ b^k`.
    fn pow_nonneg(&self, b: Expr, e: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
            [b, e, h],
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a, b, ha, hb],
        )
    }
}

fn core_type(c: &Rung2CoreConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());

    let p = c.p_factor(&n);
    let m = c.m_mass(&b, &n, &k, &f);
    let lhs = c.mul(p, m);
    // Σ_i W^{≤k}[D_i(pm∘f)] := summed_deriv_lowband_eq_weighted LHS at b:=pm∘f.
    let sigma = summed_deriv_lhs(c, &b, &n, &k, &f);
    let concl = c.le(lhs, sigma);

    let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `Σ_i W^{≤k}[D_i(pm∘f)]` — byte-identical to
/// `summed_deriv_lowband_eq_weighted`'s LHS at `b := pm∘f`:
/// `Fin.sum n (fun i => subsetSum n (fun S =>
///     ind(ble |S| k) · (Acoeff n (D_i (pm∘f)) S · Acoeff n (D_i (pm∘f)) S)))`.
fn summed_deriv_lhs(
    c: &Rung2CoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    f: &Expr,
) -> Expr {
    let pm_f = c.pm_f(parent, n, f);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let fin_n = Expr::app(fin, n.clone());
    let mut ib = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = ib.fresh_local(fin_n.clone());
    // D_i (pm∘f) := fun x => Rat.sub ((pm∘f) x) ((pm∘f) (hcFlip n x i)).
    let deriv = {
        let mut xb = EnvDeclBuilder::child_of(&ib);
        let hcp = c.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let flip = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]),
            [n.clone(), x.clone(), i.clone()],
        );
        let body = Expr::apps(
            Expr::const_(Name::from_string("Rat.sub"), vec![]),
            [
                Expr::app(pm_f.clone(), x.clone()),
                Expr::app(pm_f.clone(), flip),
            ],
        );
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    };
    // inner S-sum : subsetSum n (fun S => ind(ble |S| k)·(A·A)),
    //   A := Acoeff n (D_i(pm∘f)) S := subsetSum n (fun y => (D_i(pm∘f)) y · chi n S y).
    let inner = {
        let mut sb = EnvDeclBuilder::child_of(&ib);
        let hcp = c.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let acoeff = {
            let mut yb = EnvDeclBuilder::child_of(&sb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let chi = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
                [n.clone(), s.clone(), y.clone()],
            );
            let body = c.mul(Expr::app(deriv.clone(), y.clone()), chi);
            let g = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            c.ssum(n, g)
        };
        let ble_bit = c.ble(c.set_size_nat_of(n, &s), k.clone());
        let body = c.mul(c.ind_of(ble_bit), c.mul(acoeff.clone(), acoeff));
        let g = sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body));
        c.ssum(n, g)
    };
    let lam = ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, inner));
    Expr::apps(
        Expr::const_(Name::from_string("Fin.sum"), vec![]),
        [n.clone(), lam],
    )
}

fn core_value(c: &Rung2CoreConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());

    let p = c.p_factor(&n);
    let m = c.m_mass(&b, &n, &k, &f);
    let sigma = summed_deriv_lhs(c, &b, &n, &k, &f);
    let pm_f = c.pm_f(&b, &n, &f);

    // DC-RHS := lowband_double_count_le's RHS = R/(4·4^n) =
    //   subsetSum n (fun S => ind(band)·(setSize n S·(f̂·f̂))).
    let dc_rhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let set_size = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            [n.clone(), s.clone()],
        );
        let xx = c.x_sq(&n, &f, &s);
        let body = c.mul(c.ind_of(c.band_bit(&n, &k, &s)), c.mul(set_size, xx));
        let g = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        c.ssum(&n, g)
    };

    // (1) h_dc : M ≤ DC.
    let h_dc = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.lowband_double_count_le"),
            vec![],
        ),
        [n.clone(), k.clone(), f.clone()],
    );

    // (2) h_P_nn : 0 ≤ P  = mul_nonneg 4 (4^n) (0≤4) (powNat_nonneg 4 n (0≤4)).
    let h_four_nn = c.zero_le_lit(&c.four());
    let h_pow4_nn = c.pow_nonneg(c.four(), n.clone(), c.zero_le_lit(&c.four()));
    let h_p_nn = c.mul_nonneg(c.four(), c.pow4(&n), h_four_nn, h_pow4_nn);

    // (3) h_scaled : P·M ≤ P·DC
    //   Rat.mul_le_mul_of_nonneg_left P M DC h_dc h_P_nn  (∀ a b c, b≤c → 0≤a → a·b ≤ a·c).
    let p_m = c.mul(p.clone(), m.clone());
    let p_dc = c.mul(p.clone(), dc_rhs.clone());
    let h_scaled = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
        [p.clone(), m.clone(), dc_rhs.clone(), h_dc, h_p_nn],
    );

    // (4) h_recon : R = P·DC   (deg_band_rhs_eq_pow4_mass n k f).
    //   R := deg-band RHS @ b:=pm∘f = summed_deriv RHS.
    let r = deg_band_rhs(c, &b, &n, &k, &f);
    let h_recon = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.deg_band_rhs_eq_pow4_mass"),
            vec![],
        ),
        [n.clone(), k.clone(), f.clone()],
    );

    // (5) h_deg : Σ = R   (summed_deriv_lowband_eq_weighted n k (pm∘f)).
    let h_deg = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.summed_deriv_lowband_eq_weighted"),
            vec![],
        ),
        [n.clone(), k.clone(), pm_f.clone()],
    );

    // (6) h_eq : P·DC = Σ   = symm (trans h_deg h_recon) : Σ = P·DC, symm.
    let sigma_eq_pdc = c.trans(sigma.clone(), r.clone(), p_dc.clone(), h_deg, h_recon);
    let h_eq = c.symm(sigma.clone(), p_dc.clone(), sigma_eq_pdc);

    // (7) Eq.subst (motive t => P·M ≤ t) (P·DC) Σ h_eq h_scaled : P·M ≤ Σ.
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.le(p_m.clone(), t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let proof = c.subst(motive, p_dc.clone(), sigma.clone(), h_eq, h_scaled);

    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, proof);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `R := deg-band RHS @ b:=pm∘f = (4·4^n)·DC-RHS`'s syntactic LHS, i.e.
/// `subsetSum n (fun S => setSize n S·(ind(ble |S| k)·(4·(A·A))))` with
/// `A := Acoeff n (pm∘f) S`. BYTE-IDENTICAL to `summed_deriv_lowband_eq_weighted`'s
/// RHS and `deg_band_rhs_eq_pow4_mass`'s LHS at `b := pm∘f`.
fn deg_band_rhs(
    c: &Rung2CoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    f: &Expr,
) -> Expr {
    let pm_f = c.pm_f(parent, n, f);
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let set_size = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
        [n.clone(), s.clone()],
    );
    // A := Acoeff n (pm∘f) S := subsetSum n (fun y => (pm∘f) y · chi n S y).
    let acoeff = {
        let mut yb = EnvDeclBuilder::child_of(&d);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let chi = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            [n.clone(), s.clone(), y.clone()],
        );
        let body = c.mul(Expr::app(pm_f.clone(), y.clone()), chi);
        let g = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
        c.ssum(n, g)
    };
    let aa = c.mul(acoeff.clone(), acoeff);
    let ble_bit = c.ble(c.set_size_nat_of(n, &s), k.clone());
    let four_aa = c.mul(c.four(), aa);
    let body = c.mul(set_size, c.mul(c.ind_of(ble_bit), four_aa));
    let g = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
    c.ssum(n, g)
}

impl Environment {
    /// Register `BoolAnalysis.kkl_pow4_mass_le_summed_deriv` — the rung-2
    /// combinatorial core `(4·4^n)·M_{1..k} ≤ Σ_i W^{≤k}[D_i(pm∘f)]`. See module
    /// docs. Kernel-checked, `Constructive`, empty admitted-axiom closure.
    /// Idempotent; no axiom added/removed.
    pub fn register_kkl_pow4_mass_le_summed_deriv(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_pow4_mass_le_summed_deriv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, chi, FourierCoefficient, ind, setSize, hcFlip
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_nonneg()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left, mul_nonneg
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true
        self.register_lowband_double_count_le()?;
        self.register_deg_band_rhs_eq_pow4_mass()?;
        self.register_summed_deriv_lowband_eq_weighted()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Rung2CoreConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: core_type(&c),
            value: core_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_kkl_pow4_mass_le_summed_deriv_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_pow4_mass_le_summed_deriv()
            .expect("register_kkl_pow4_mass_le_summed_deriv");
        let nm = Name::from_string("BoolAnalysis.kkl_pow4_mass_le_summed_deriv");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("rung-2 core proof must check: {e:?}"));
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

    #[test]
    fn test_rung2_core_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_kkl_pow4_mass_le_summed_deriv().expect("first");
        env.register_kkl_pow4_mass_le_summed_deriv()
            .expect("idempotent");
    }
}
