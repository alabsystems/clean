// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **rung 2 degree-weighted band identity** (`degree-weighted band`).
//!
//! Sums the per-coordinate derivative low-bands `W^{≤k}[D_i b]` over `i` and
//! lands the degree-weighted low-band of `b`'s own squared coefficients:
//!
//! ```text
//! BoolAnalysis.summed_deriv_lowband_eq_weighted : ∀ (n k : Nat) (b : HCPoint n → Rat),
//!   Fin.sum n (fun i =>
//!       subsetSum n (fun S =>
//!           ind (Nat.ble (setSizeNat n S) k)
//!             · (Acoeff n (D_i b) S · Acoeff n (D_i b) S)))                  -- Σ_i W^{≤k}[D_i b]
//!     = subsetSum n (fun S =>
//!         setSize n S
//!           · (ind (Nat.ble (setSizeNat n S) k)
//!               · (Rat.mul 4 (Acoeff n b S · Acoeff n b S))))                -- Σ_{|S|≤k} |S|·4·A_b(S)²
//! ```
//!
//! i.e. `Σ_i W^{≤k}[D_i b] = Σ_{|S|≤k} |S| · 4 · A_b(S)²`, where
//!   * `Acoeff n g S := subsetSum n (fun y => g y · chi n S y)` is the un-normalized
//!     `S`-Fourier coefficient (byte-identical to the level-restriction bridge's
//!     `a_coeff` and to `deriv_coeff_sq_eq`'s `Acoeff`),
//!   * `D_i b := fun x => b x − b (hcFlip n x i)` is the discrete `i`-derivative, and
//!   * `setSize n S := Fin.sum n (fun i => ind (S i))` is the `Rat`-cardinality `|S|`.
//!
//! This is the COMBINATORIAL heart of rung 2: it converts the per-coordinate
//! squared-derivative-coefficient rescale (`deriv_coeff_sq_eq`,
//! `A(D_i b,S)² = (4·ind(S i))·A(b,S)²`) plus the double-count
//! (`subsetSum_double_count`, `Σ_i ind(S i)·w S = setSize n S · w S`) into the
//! degree-weighting `|S|·4·A_b(S)²` on the low band.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! Write `p S := ind (ble |S| k)` (band), `q S i := ind (S i)`, `g S := A_b(S)²`,
//! `w S := p S · (4 · g S)`. Per-coordinate:
//!
//! 1. **per-S squared-deriv + monomial rearrange** — `deriv_coeff_sq_eq n b S i`
//!    gives `A(D_i b,S)² = (4 · q S i) · g S`; `congrArg (p S · ·)` of it then the
//!    pure-`Rat` rearrangement `monomial_swap` (built from `mul_assoc`/`mul_comm`)
//!    `p·((4·q)·g) = q·(p·(4·g))` chains
//!    `p S · (A(D_i b,S)²) = q S i · w S`.
//! 2. **per-i band = coord_fn** — `subsetSum_congr` over (1) rewrites
//!    `W^{≤k}[D_i b] = subsetSum n (fun S => p S · A(D_i b,S)²)` into
//!    `subsetSum n (fun S => q S i · w S)` (the double-count `coord_fn i`).
//! 3. **Fin.sum over i** — `Fin.sum_congr n LHS_i COORD_i (per_i)` lifts (2) to
//!    `Σ_i W^{≤k}[D_i b] = Σ_i subsetSum n (fun S => ind(S i)·w S)`.
//! 4. **double-count** — `subsetSum_double_count n w`:
//!    `Σ_i subsetSum n (fun S => ind(S i)·w S) = subsetSum n (fun S => setSize n S·w S)`.
//!    The RHS integrand `setSize n S · w S = setSize n S · (p S · (4·g S))` is the
//!    stated conclusion's RHS.
//!
//! `Eq.trans` of (3) and (4) closes. Every leaf (`deriv_coeff_sq_eq`,
//! `subsetSum_congr`, `subsetSum_double_count`, `Fin.sum_congr`, `Rat.mul_assoc`,
//! `Rat.mul_comm`, `congrArg`, `Eq.*`) is `Constructive` with empty admitted-axiom
//! closure, so this rung is too. No axiom is added or removed. Idempotent. Gated
//! behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the degree-weighted band identity. Carrier spellings
/// (`Acoeff`/`subsetSum`/`chi`, `hcFlip`, `ind`, `setSize`/`setSizeNat`,
/// `Nat.ble`, `Fin.sum`, `4 := mk(ofNat 4) 1`) byte-match the consumed carriers.
struct DegBandConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    fin: Expr,
    fin_sum: Expr,
    chi: Expr,
    hc_flip: Expr,
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    hcpoint: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    l1: Level,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    l0: Level,
}

impl DegBandConsts {
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
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            chi: k("BoolAnalysis.chi"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            ind: k("BoolAnalysis.ind"),
            set_size: k("BoolAnalysis.setSize"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            l1,
            #[cfg(test)]
            l0: Level::zero(),
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
    /// `(4 : Rat) := mk(ofNat 4) 1` (byte-match `deriv_coeff_sq_eq`'s `rat_numeral(4)`).
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
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn chi_(&self, n: &Expr, s: &Expr, y: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), y.clone()])
    }
    fn hc_flip_(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fin_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
    /// `Nat.ble (setSizeNat n S) k` — the low-band bit.
    fn band_bit(&self, n: &Expr, k: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.ble"), vec![]),
            [self.set_size_nat_of(n, s), k.clone()],
        )
    }
    /// `Acoeff n g S := subsetSum n (fun y => g y · chi n S y)`.
    fn acoeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), y.clone()), self.chi_(n, s, &y));
        let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
    /// `D_i b := fun x => b x − b (hcFlip n x i)`.
    fn deriv(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let body = Expr::apps(
            sub,
            [
                Expr::app(b.clone(), x.clone()),
                Expr::app(b.clone(), self.hc_flip_(n, &x, i)),
            ],
        );
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    // ── Eq plumbing ───────────────────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
    fn congr_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `congrArg (fun z => z·right) h : a·right = b·right`.
    fn congr_r(&self, parent: &EnvDeclBuilder, right: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }

    /// `monomial_swap p q g : p·((4·q)·g) = q·(p·(4·g))`. A pure-`Rat`
    /// rearrangement built from `mul_assoc`/`mul_comm`:
    /// ```text
    ///   p·((4·q)·g) = p·(4·(q·g))   congr (p··) (mul_assoc 4 q g)
    ///              [ 4·(q·g) = (4·q)·g = (q·4)·g = q·(4·g) ]
    ///              = p·(q·(4·g))    congr (p··) (that)
    ///              = (p·q)·(4·g)    symm (mul_assoc p q (4·g))
    ///              = (q·p)·(4·g)    congr (··(4·g)) (mul_comm p q)
    ///              = q·(p·(4·g))    mul_assoc q p (4·g)
    /// ```
    fn monomial_swap(&self, parent: &EnvDeclBuilder, p: &Expr, q: &Expr, g: &Expr) -> Expr {
        let four = self.four();
        let four_q = self.mul(four.clone(), q.clone()); // 4·q
        let four_g = self.mul(four.clone(), g.clone()); // 4·g
        let q_g = self.mul(q.clone(), g.clone()); // q·g

        // inner : 4·(q·g) = q·(4·g).
        //   s1 : 4·(q·g) = (4·q)·g   symm (mul_assoc 4 q g)
        let assoc_4qg = self.assoc(four.clone(), q.clone(), g.clone()); // (4·q)·g = 4·(q·g)
        let four_qg = self.mul(four.clone(), q_g.clone()); // 4·(q·g)
        let s1 = self.symm_rat(
            self.mul(four_q.clone(), g.clone()),
            four_qg.clone(),
            assoc_4qg,
        );
        //   s2 : (4·q)·g = (q·4)·g   congr (··g) (mul_comm 4 q)
        let q_4 = self.mul(q.clone(), four.clone()); // q·4
        let s2 = self.congr_r(
            parent,
            g,
            four_q.clone(),
            q_4.clone(),
            self.comm(four.clone(), q.clone()),
        );
        //   s3 : (q·4)·g = q·(4·g)   mul_assoc q 4 g
        let s3 = self.assoc(q.clone(), four.clone(), g.clone());
        let inner12 = self.trans_rat(
            four_qg.clone(),
            self.mul(four_q.clone(), g.clone()),
            self.mul(q_4.clone(), g.clone()),
            s1,
            s2,
        );
        let inner = self.trans_rat(
            four_qg.clone(),
            self.mul(q_4.clone(), g.clone()),
            self.mul(q.clone(), four_g.clone()),
            inner12,
            s3,
        ); // 4·(q·g) = q·(4·g)

        // a1 : p·((4·q)·g) = p·(4·(q·g))   congr (p··) (mul_assoc 4 q g)
        let p_4qg = self.mul(p.clone(), self.mul(four_q.clone(), g.clone()));
        let p_4_qg = self.mul(p.clone(), four_qg.clone());
        let a1 = self.congr_l(
            parent,
            p,
            self.mul(four_q.clone(), g.clone()),
            four_qg.clone(),
            self.assoc(four.clone(), q.clone(), g.clone()),
        );
        // a2 : p·(4·(q·g)) = p·(q·(4·g))   congr (p··) inner
        let p_q_4g = self.mul(p.clone(), self.mul(q.clone(), four_g.clone()));
        let a2 = self.congr_l(
            parent,
            p,
            four_qg.clone(),
            self.mul(q.clone(), four_g.clone()),
            inner,
        );
        // a3 : p·(q·(4·g)) = (p·q)·(4·g)   symm (mul_assoc p q (4·g))
        let pq = self.mul(p.clone(), q.clone());
        let pq_4g = self.mul(pq.clone(), four_g.clone());
        let a3 = self.symm_rat(
            pq_4g.clone(),
            p_q_4g.clone(),
            self.assoc(p.clone(), q.clone(), four_g.clone()),
        );
        // a4 : (p·q)·(4·g) = (q·p)·(4·g)   congr (··(4·g)) (mul_comm p q)
        let qp = self.mul(q.clone(), p.clone());
        let qp_4g = self.mul(qp.clone(), four_g.clone());
        let a4 = self.congr_r(
            parent,
            &four_g,
            pq.clone(),
            qp.clone(),
            self.comm(p.clone(), q.clone()),
        );
        // a5 : (q·p)·(4·g) = q·(p·(4·g))   mul_assoc q p (4·g)
        let q_p_4g = self.mul(q.clone(), self.mul(p.clone(), four_g.clone()));
        let a5 = self.assoc(q.clone(), p.clone(), four_g.clone());

        // chain a1..a5.
        let c12 = self.trans_rat(p_4qg.clone(), p_4_qg.clone(), p_q_4g.clone(), a1, a2);
        let c123 = self.trans_rat(p_4qg.clone(), p_q_4g.clone(), pq_4g.clone(), c12, a3);
        let c1234 = self.trans_rat(p_4qg.clone(), pq_4g.clone(), qp_4g.clone(), c123, a4);
        self.trans_rat(p_4qg, qp_4g, q_p_4g, c1234, a5)
    }
}

// ─────────────── the degree-weighted band identity (target) ───────────────────

/// `w_fn(b,k) := fun S => ind(ble |S| k) · (4 · (A_b(S)·A_b(S)))` — the
/// double-count weight `w S` (the band, scalar-4, squared coefficient).
fn w_fn(c: &DegBandConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, b: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let cap_a = c.acoeff(&d, n, b, &s);
    let g = c.mul(cap_a.clone(), cap_a);
    let body = c.mul(c.ind_of(c.band_bit(n, k, &s)), c.mul(c.four(), g));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `lhs_i(b,k) := fun i => subsetSum n (fun S => ind(ble |S| k) · (A(D_i b,S)·A(D_i b,S)))`
/// — `Σ_i` integrand `W^{≤k}[D_i b]`.
fn lhs_i_fn(c: &DegBandConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, b: &Expr) -> Expr {
    let mut ib = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = ib.fresh_local(fin_n.clone());
    let inner = {
        let mut d = EnvDeclBuilder::child_of(&ib);
        let hcp = c.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let db = c.deriv(&d, n, b, &i);
        let cap_ad = c.acoeff(&d, n, &db, &s);
        let body = c.mul(
            c.ind_of(c.band_bit(n, k, &s)),
            c.mul(cap_ad.clone(), cap_ad),
        );
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    };
    let body = c.ssum(n, inner);
    ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `coord_i(b,k) := fun i => subsetSum n (fun S => ind(S i) · w S)` — the
/// double-count `Σ_i` integrand.
fn coord_i_fn(c: &DegBandConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, b: &Expr) -> Expr {
    let mut ib = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = ib.fresh_local(fin_n.clone());
    let inner = {
        let mut d = EnvDeclBuilder::child_of(&ib);
        let hcp = c.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let q = c.ind_of(Expr::app(s.clone(), i.clone()));
        let cap_a = c.acoeff(&d, n, b, &s);
        let g = c.mul(cap_a.clone(), cap_a);
        let w = c.mul(c.ind_of(c.band_bit(n, k, &s)), c.mul(c.four(), g));
        let body = c.mul(q, w);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    };
    let body = c.ssum(n, inner);
    ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `size_w_fn := fun S => setSize n S · w S` — the double-count RHS integrand
/// (= the target conclusion's RHS integrand).
fn size_w_fn(c: &DegBandConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, b: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let cap_a = c.acoeff(&d, n, b, &s);
    let g = c.mul(cap_a.clone(), cap_a);
    let w = c.mul(c.ind_of(c.band_bit(n, k, &s)), c.mul(c.four(), g));
    let body = c.mul(c.set_size_of(n, &s), w);
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

fn deg_band_type(c: &DegBandConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());

    let lhs = c.fin_sum_of(&n, lhs_i_fn(c, &b, &n, &k, &bf));
    let rhs = c.ssum(&n, size_w_fn(c, &b, &n, &k, &bf));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn deg_band_value(c: &DegBandConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());

    let lhs_i = lhs_i_fn(c, &b, &n, &k, &bf);
    let coord_i = coord_i_fn(c, &b, &n, &k, &bf);
    let w = w_fn(c, &b, &n, &k, &bf);

    // per_i : ∀ (i : Fin n), (lhs_i i) = (coord_i i).
    //   = subsetSum_congr n LHS_INNER COORD_INNER per_s, where per_s S rewrites
    //     ind(ble |S| k)·A(D_i b,S)² into ind(S i)·w S via deriv_coeff_sq_eq +
    //     congr (band··) + monomial_swap.
    let per_i = {
        let mut ib = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ib.fresh_local(fin_n.clone());

        // LHS_INNER := fun S => ind(ble |S| k)·(A(D_i b,S)·A(D_i b,S)).
        let lhs_inner = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let db = c.deriv(&d, &n, &bf, &i);
            let cap_ad = c.acoeff(&d, &n, &db, &s);
            let body = c.mul(
                c.ind_of(c.band_bit(&n, &k, &s)),
                c.mul(cap_ad.clone(), cap_ad),
            );
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        // COORD_INNER := fun S => ind(S i)·w S.
        let coord_inner = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let q = c.ind_of(Expr::app(s.clone(), i.clone()));
            let cap_a = c.acoeff(&d, &n, &bf, &s);
            let g = c.mul(cap_a.clone(), cap_a);
            let ww = c.mul(c.ind_of(c.band_bit(&n, &k, &s)), c.mul(c.four(), g));
            let body = c.mul(q, ww);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };

        // per_s : ∀ S, LHS_INNER S = COORD_INNER S.
        let per_s = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());

            let db = c.deriv(&d, &n, &bf, &i);
            let cap_ad = c.acoeff(&d, &n, &db, &s);
            let ad_sq = c.mul(cap_ad.clone(), cap_ad.clone()); // A(D_i b,S)²
            let p = c.ind_of(c.band_bit(&n, &k, &s)); // band
            let q = c.ind_of(Expr::app(s.clone(), i.clone())); // ind(S i)
            let cap_a = c.acoeff(&d, &n, &bf, &s);
            let g = c.mul(cap_a.clone(), cap_a.clone()); // A_b(S)²
            let four_q = c.mul(c.four(), q.clone()); // 4·q
            let rhs_sq = c.mul(four_q.clone(), g.clone()); // (4·q)·g

            // dcs : A(D_i b,S)² = (4·ind(S i))·A_b(S)²   [deriv_coeff_sq_eq n b S i].
            let dcs = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.deriv_coeff_sq_eq"), vec![]),
                [n.clone(), bf.clone(), s.clone(), i.clone()],
            );
            // c1 : p·(A(D_i b,S)²) = p·((4·q)·g)   congr (p··) dcs.
            let p_adsq = c.mul(p.clone(), ad_sq.clone());
            let p_rhs = c.mul(p.clone(), rhs_sq.clone());
            let c1 = c.congr_l(&d, &p, ad_sq.clone(), rhs_sq.clone(), dcs);
            // c2 : p·((4·q)·g) = q·(p·(4·g))   monomial_swap p q g.
            let four_g = c.mul(c.four(), g.clone());
            let q_w = c.mul(q.clone(), c.mul(p.clone(), four_g.clone())); // q·(p·(4·g)) = q·w
            let c2 = c.monomial_swap(&d, &p, &q, &g);
            // chain : p·(A(D_i b,S)²) = q·w.
            let body = c.trans_rat(p_adsq, p_rhs, q_w, c1, c2);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };

        // subsetSum_congr n LHS_INNER COORD_INNER per_s.
        let body = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]),
            [n.clone(), lhs_inner, coord_inner, per_s],
        );
        ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    // step3 : Σ_i (lhs_i i) = Σ_i (coord_i i)   [Fin.sum_congr n lhs_i coord_i per_i].
    let lhs_sum = c.fin_sum_of(&n, lhs_i.clone());
    let coord_sum = c.fin_sum_of(&n, coord_i.clone());
    let step3 = Expr::apps(
        Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
        [n.clone(), lhs_i.clone(), coord_i.clone(), per_i],
    );

    // step4 : Σ_i subsetSum(fun S => ind(S i)·w S) = subsetSum(fun S => setSize·w S)
    //   [subsetSum_double_count n w].  Its LHS is `coord_sum` (coord_i ≡ the
    //   double-count's `fun i => subsetSum n (coord_fn i)` by β), RHS is the target.
    let rhs = c.ssum(&n, size_w_fn(c, &b, &n, &k, &bf));
    let step4 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_double_count"),
            vec![],
        ),
        [n.clone(), w.clone()],
    );

    // chain : Σ_i (lhs_i i) = Σ_i (coord_i i) = subsetSum(fun S => setSize·w S).
    let proof = c.trans_rat(lhs_sum, coord_sum, rhs, step3, step4);

    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, proof);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.summed_deriv_lowband_eq_weighted` — the
    /// degree-weighted band identity `Σ_i W^{≤k}[D_i b] = Σ_{|S|≤k} |S|·4·A_b(S)²`.
    /// See module docs. Kernel-checked, `Constructive`, empty admitted-axiom
    /// closure. Idempotent; no axiom added/removed.
    pub fn register_summed_deriv_lowband_eq_weighted(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.summed_deriv_lowband_eq_weighted");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // chi, ind, hcFlip, Acoeff carriers
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?; // Rat.mul_assoc, Rat.mul_comm, Rat.sub
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;
        self.register_subset_sum_double_count()?;
        self.register_deriv_coeff_sq_eq()?; // deriv_coeff_sq_eq (the squared rescale)
        self.init_fin_sum()?; // Fin.sum_congr

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = DegBandConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: deg_band_type(&c),
            value: deg_band_value(&c),
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
    fn test_summed_deriv_lowband_eq_weighted_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_summed_deriv_lowband_eq_weighted()
            .expect("register_summed_deriv_lowband_eq_weighted");
        let nm = Name::from_string("BoolAnalysis.summed_deriv_lowband_eq_weighted");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("degree-weighted band identity must check: {e:?}"));
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
    fn test_deg_band_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_summed_deriv_lowband_eq_weighted()
            .expect("first");
        env.register_summed_deriv_lowband_eq_weighted()
            .expect("idempotent");
    }
}
