// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **rung 2 normalization-reconciliation** (`norm-reconcile`).
//!
//! Connects the degree-weighted band identity
//! [`BoolAnalysis.summed_deriv_lowband_eq_weighted`] (un-normalized `A_b` carrier,
//! `b := pm∘f`) to the normalized low-degree Fourier mass `M_{1..k}` (the
//! `f̂`-carrier the double-count and variance rungs consume), with all
//! `4`/`4^n`/`setSize` bookkeeping tracked EXACTLY.
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.deg_band_rhs_eq_pow4_mass :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     subsetSum n (fun S =>
//!         setSize n S
//!           · (ind (Nat.ble (setSizeNat n S) k)
//!               · (Rat.mul 4 (A_S(pm∘f) · A_S(pm∘f)))))                 -- deg-band RHS @ b:=pm∘f
//!       = Rat.mul (Rat.mul 4 (Rat.powNat 4 n))
//!                 (subsetSum n (fun S =>
//!                     ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                                   (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!                       · (setSize n S · (f̂ S · f̂ S))))                -- (4·4^n)·DC-RHS
//! ```
//!
//! where `A_S(pm∘f) := subsetSum n (fun x => pm(f x)·χ_S x)` is the un-normalized
//! coefficient (byte-identical to `Acoeff n (fun x => pm(f x)) S`, which is the
//! deg-band integrand at `b := pm∘f`), and `f̂ S := FourierCoefficient n f S`.
//!
//! This is the **normalization bridge** of rung 2: the deg-band identity lives in
//! the un-normalized `A`-carrier (factor `4·A_b²`), the double-count /
//! variance-split rungs live in the normalized `f̂`-carrier (factor
//! `setSize·f̂²` on the `1≤|S|≤k` band). The squared Fourier-normalization bridge
//! `A_S(pm∘f)² = 4^n·f̂(S)²` ([`subsetSum_pm_sq_eq_pow4_fourier`], step-1-squared)
//! converts one to the other, the scalar `4·4^n` is pulled out via
//! `subsetSum_smul`, and the `|S|≤k` band collapses to the non-empty `1≤|S|≤k`
//! band (`setsize_band_mask_collapse`, since the `|S|=0` term carries `setSize=0`).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! Write `Z S := A_S(pm∘f)`, `X S := f̂(S)·f̂(S)`, `p S := ind (ble |S| k)`,
//! `q S := setSize n S`, `P4 := 4^n`.
//!
//! 1. **per-S normalize + reassociate** — for each `S`,
//!    ```text
//!      q·(p·(4·(Z·Z)))  =  q·(p·(4·(P4·X)))      congr, via step-1-squared (Z·Z = P4·X)
//!                       =  (4·P4)·(p·(q·X))       monomial_reshape (pure Rat assoc/comm)
//!    ```
//!    `monomial_reshape q p P4 X` is a pure-`Rat` rearrangement built from
//!    `mul_assoc`/`mul_comm` (no field facts).
//! 2. **subsetSum_congr** lifts (1): `deg-band RHS = subsetSum n (fun S => (4·P4)·(p·(q·X)))`.
//! 3. **subsetSum_smul** pulls the scalar: `= (4·P4)·subsetSum n (fun S => p·(q·X))`.
//! 4. **setsize_band_mask_collapse** at `g := X` rewrites the `|S|≤k` band to the
//!    non-empty `1≤|S|≤k` band: `subsetSum n (fun S => p·(q·X)) = DC-RHS`, so
//!    `congr ((4·P4)··)` lands `(4·P4)·DC-RHS`.
//!
//! `Eq.trans` of (2),(3),(4) closes. Every leaf (`subsetSum_pm_sq_eq_pow4_fourier`,
//! `subsetSum_congr`, `subsetSum_smul`, `setsize_band_mask_collapse`,
//! `Rat.mul_assoc`, `Rat.mul_comm`, `congrArg`, `Eq.*`) is `Constructive` with
//! empty admitted-axiom closure, so this brick is too. No axiom added/removed.
//! Idempotent. Gated behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the normalization-reconciliation. Carrier spellings
/// (`subsetSum`, `chi`, `pm`, `FourierCoefficient`, `powNat`, `setSize`,
/// `setSizeNat`, `ind`, the band masks, `4 := mk(ofNat 4) 1`) byte-match the
/// consumed deg-band / squared-bound / mask-collapse / double-count carriers.
struct ReconcileConsts {
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
    chi: Expr,
    pm: Expr,
    subset_sum: Expr,
    fourier: Expr,
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    l1: Level,
}

impl ReconcileConsts {
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
            chi: k("BoolAnalysis.chi"),
            pm: k("BoolAnalysis.pm"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            ind: k("BoolAnalysis.ind"),
            set_size: k("BoolAnalysis.setSize"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            l1,
        }
    }

    // ── Nat / Rat constructors ────────────────────────────────────────────────
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
    /// `(4 : Rat) := mk(ofNat 4) 1` (byte-match deg-band's `four`).
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
    /// `4^n := powNat 4 n` (byte-match step-1-squared's `pow4`).
    fn pow4(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.four(), n.clone()])
    }

    // ── BoolAnalysis carriers ─────────────────────────────────────────────────
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
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
    /// `Nat.ble (setSizeNat n S) k` — the `|S| ≤ k` low-band bit (deg-band band).
    fn low_bit(&self, n: &Expr, k: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            self.nat_ble.clone(),
            [self.set_size_nat_of(n, s), k.clone()],
        )
    }
    /// `Nat.ble a b`.
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    /// `Nat.ble (succ zero) m`.
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.nat_one(), m)
    }
    /// `Nat.ble (succ k) m`.
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    /// The non-empty band `Bool.and (ble 1 |S|) (not (ble (k+1) |S|))`.
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
    /// `pm∘f := fun (x : HCPoint n) => pm (f x)` — the deg-band carrier `b`.
    #[cfg(test)]
    fn pm_f(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `Z S := A_S(pm∘f) := subsetSum n (fun x => pm(f x)·χ_S x)` — BYTE-IDENTICAL
    /// to step-1-squared's `Z` and to `Acoeff n (pm∘f) S` (deg-band at `b:=pm∘f`).
    fn z_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let pm_fx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        let body = self.mul(pm_fx, self.chi_(n, s, &x));
        let g = d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }
    /// `f̂(S)·f̂(S)`.
    fn x_sq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }

    // ── Eq.{1} plumbing ───────────────────────────────────────────────────────
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
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
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

    /// Pure-`Rat` rearrangement
    /// `monomial_reshape q p P4 X : q·(p·(4·(P4·X))) = (4·P4)·(p·(q·X))`,
    /// built only from `mul_assoc`/`mul_comm` (NO field facts). The strategy:
    /// ```text
    ///   q·(p·(4·(P4·X)))
    ///     = q·(p·((4·P4)·X))     congr_l q (congr_l p (symm (mul_assoc 4 P4 X)))
    ///     = q·((4·P4)·(p·X))     congr_l q (reassoc_swap p (4·P4) X)
    ///     = (4·P4)·(q·(p·X))     reassoc_pull q (4·P4) (p·X)
    ///     = (4·P4)·(p·(q·X))     congr_l (4·P4) (reassoc_swap2 q p X)
    /// ```
    /// where the inner `reassoc_*` are themselves assoc/comm chains.
    fn monomial_reshape(
        &self,
        parent: &EnvDeclBuilder,
        q: &Expr,
        p: &Expr,
        p4: &Expr,
        xx: &Expr,
    ) -> Expr {
        let four = self.four();
        let four_p4 = self.mul(four.clone(), p4.clone()); // 4·P4
        let p4_x = self.mul(p4.clone(), xx.clone()); // P4·X
        let four_p4x = self.mul(four.clone(), p4_x.clone()); // 4·(P4·X)
        let fp4_x = self.mul(four_p4.clone(), xx.clone()); // (4·P4)·X
        let p_x = self.mul(p.clone(), xx.clone()); // p·X
        let q_x = self.mul(q.clone(), xx.clone()); // q·X

        // s1 : 4·(P4·X) = (4·P4)·X   symm (mul_assoc 4 P4 X)
        let s1 = self.symm(
            fp4_x.clone(),
            four_p4x.clone(),
            self.assoc(four.clone(), p4.clone(), xx.clone()),
        );

        // ── inner A : p·(4·(P4·X)) = (4·P4)·(p·X) ──
        //   pA1 : p·(4·(P4·X)) = p·((4·P4)·X)   congr_l p s1
        let p_4p4x = self.mul(p.clone(), four_p4x.clone());
        let p_fp4_x = self.mul(p.clone(), fp4_x.clone());
        let pa1 = self.congr_l(parent, p, four_p4x.clone(), fp4_x.clone(), s1.clone());
        //   pA2 : p·((4·P4)·X) = (p·(4·P4))·X   symm (mul_assoc p (4·P4) X)
        let p_fp4 = self.mul(p.clone(), four_p4.clone());
        let p_fp4_then_x = self.mul(p_fp4.clone(), xx.clone());
        let pa2 = self.symm(
            p_fp4_then_x.clone(),
            p_fp4_x.clone(),
            self.assoc(p.clone(), four_p4.clone(), xx.clone()),
        );
        //   pA3 : (p·(4·P4))·X = ((4·P4)·p)·X   congr_r X (mul_comm p (4·P4))
        let fp4_p = self.mul(four_p4.clone(), p.clone());
        let fp4_p_x = self.mul(fp4_p.clone(), xx.clone());
        let pa3 = self.congr_r(
            parent,
            xx,
            p_fp4.clone(),
            fp4_p.clone(),
            self.comm(p.clone(), four_p4.clone()),
        );
        //   pA4 : ((4·P4)·p)·X = (4·P4)·(p·X)   mul_assoc (4·P4) p X
        let fp4_px = self.mul(four_p4.clone(), p_x.clone());
        let pa4 = self.assoc(four_p4.clone(), p.clone(), xx.clone());
        // chain inner A
        let pa12 = self.trans(
            p_4p4x.clone(),
            p_fp4_x.clone(),
            p_fp4_then_x.clone(),
            pa1,
            pa2,
        );
        let pa123 = self.trans(
            p_4p4x.clone(),
            p_fp4_then_x.clone(),
            fp4_p_x.clone(),
            pa12,
            pa3,
        );
        let inner_a = self.trans(p_4p4x.clone(), fp4_p_x.clone(), fp4_px.clone(), pa123, pa4);

        // step1 : q·(p·(4·(P4·X))) = q·((4·P4)·(p·X))   congr_l q inner_a
        let q_p_4p4x = self.mul(q.clone(), p_4p4x.clone());
        let q_fp4_px = self.mul(q.clone(), fp4_px.clone());
        let step1 = self.congr_l(parent, q, p_4p4x.clone(), fp4_px.clone(), inner_a);

        // step2 : q·((4·P4)·(p·X)) = (q·(4·P4))·(p·X)   symm (mul_assoc q (4·P4) (p·X))
        let q_fp4 = self.mul(q.clone(), four_p4.clone());
        let q_fp4_then_px = self.mul(q_fp4.clone(), p_x.clone());
        let step2 = self.symm(
            q_fp4_then_px.clone(),
            q_fp4_px.clone(),
            self.assoc(q.clone(), four_p4.clone(), p_x.clone()),
        );
        // step3 : (q·(4·P4))·(p·X) = ((4·P4)·q)·(p·X)   congr_r (p·X) (mul_comm q (4·P4))
        let fp4_q = self.mul(four_p4.clone(), q.clone());
        let fp4_q_px = self.mul(fp4_q.clone(), p_x.clone());
        let step3 = self.congr_r(
            parent,
            &p_x,
            q_fp4.clone(),
            fp4_q.clone(),
            self.comm(q.clone(), four_p4.clone()),
        );
        // step4 : ((4·P4)·q)·(p·X) = (4·P4)·(q·(p·X))   mul_assoc (4·P4) q (p·X)
        let fp4_qpx = self.mul(four_p4.clone(), self.mul(q.clone(), p_x.clone()));
        let step4 = self.assoc(four_p4.clone(), q.clone(), p_x.clone());

        // ── inner B : q·(p·X) = p·(q·X) ──
        //   qB1 : q·(p·X) = (q·p)·X   symm (mul_assoc q p X)
        let qp = self.mul(q.clone(), p.clone());
        let qp_x = self.mul(qp.clone(), xx.clone());
        let q_px = self.mul(q.clone(), p_x.clone());
        let qb1 = self.symm(
            qp_x.clone(),
            q_px.clone(),
            self.assoc(q.clone(), p.clone(), xx.clone()),
        );
        //   qB2 : (q·p)·X = (p·q)·X   congr_r X (mul_comm q p)
        let pq = self.mul(p.clone(), q.clone());
        let pq_x = self.mul(pq.clone(), xx.clone());
        let qb2 = self.congr_r(
            parent,
            xx,
            qp.clone(),
            pq.clone(),
            self.comm(q.clone(), p.clone()),
        );
        //   qB3 : (p·q)·X = p·(q·X)   mul_assoc p q X
        let p_qx = self.mul(p.clone(), q_x.clone());
        let qb3 = self.assoc(p.clone(), q.clone(), xx.clone());
        let qb12 = self.trans(q_px.clone(), qp_x.clone(), pq_x.clone(), qb1, qb2);
        let inner_b = self.trans(q_px.clone(), pq_x.clone(), p_qx.clone(), qb12, qb3);

        // step5 : (4·P4)·(q·(p·X)) = (4·P4)·(p·(q·X))   congr_l (4·P4) inner_b
        let fp4_pqx = self.mul(four_p4.clone(), p_qx.clone());
        let step5 = self.congr_l(parent, &four_p4, q_px.clone(), p_qx.clone(), inner_b);

        // chain step1..step5
        let c12 = self.trans(
            q_p_4p4x.clone(),
            q_fp4_px.clone(),
            q_fp4_then_px.clone(),
            step1,
            step2,
        );
        let c123 = self.trans(
            q_p_4p4x.clone(),
            q_fp4_then_px.clone(),
            fp4_q_px.clone(),
            c12,
            step3,
        );
        let c1234 = self.trans(
            q_p_4p4x.clone(),
            fp4_q_px.clone(),
            fp4_qpx.clone(),
            c123,
            step4,
        );
        self.trans(q_p_4p4x, fp4_qpx, fp4_pqx, c1234, step5)
    }
}

// ───────────── the per-S / band-integrand lambdas (for subsetSum_congr) ─────────

/// `deg-band RHS integrand @ b:=pm∘f`:
/// `fun S => setSize n S · (ind(ble |S| k) · (4 · (Z·Z)))` where `Z = A_S(pm∘f)`.
fn rhs_in_fn(c: &ReconcileConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let z = c.z_coeff(&d, n, f, &s);
    let zz = c.mul(z.clone(), z);
    let body = c.mul(
        c.set_size_of(n, &s),
        c.mul(c.ind_of(c.low_bit(n, k, &s)), c.mul(c.four(), zz)),
    );
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// scaled middle integrand `fun S => (4·4^n) · (ind(ble |S| k) · (setSize·(f̂·f̂)))`.
fn mid_in_fn(c: &ReconcileConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let four_p4 = c.mul(c.four(), c.pow4(n));
    let xx = c.x_sq(n, f, &s);
    let p_qx = c.mul(
        c.ind_of(c.low_bit(n, k, &s)),
        c.mul(c.set_size_of(n, &s), xx),
    );
    let body = c.mul(four_p4, p_qx);
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// unscaled low-band integrand `fun S => ind(ble |S| k)·(setSize·(f̂·f̂))` —
/// BYTE-IDENTICAL to `setsize_band_mask_collapse`'s LOW form at `g := f̂·f̂`.
fn low_in_fn(c: &ReconcileConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let xx = c.x_sq(n, f, &s);
    let body = c.mul(
        c.ind_of(c.low_bit(n, k, &s)),
        c.mul(c.set_size_of(n, &s), xx),
    );
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// the `g := f̂·f̂` argument lambda for `setsize_band_mask_collapse`:
/// `fun S => f̂(S)·f̂(S)`.
fn g_x_fn(c: &ReconcileConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let body = c.x_sq(n, f, &s);
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// the non-empty-band DC-RHS integrand `fun S => ind(band)·(setSize·(f̂·f̂))` —
/// BYTE-IDENTICAL to `lowband_double_count_le`'s `m_lo_weighted_fn` and to
/// `setsize_band_mask_collapse`'s BAND form at `g := f̂·f̂`.
fn band_in_fn(c: &ReconcileConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let xx = c.x_sq(n, f, &s);
    let body = c.mul(
        c.ind_of(c.band_bit(n, k, &s)),
        c.mul(c.set_size_of(n, &s), xx),
    );
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

fn reconcile_type(c: &ReconcileConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());

    let lhs = c.ssum(&n, rhs_in_fn(c, &b, &n, &k, &f));
    let four_p4 = c.mul(c.four(), c.pow4(&n));
    let rhs = c.mul(four_p4, c.ssum(&n, band_in_fn(c, &b, &n, &k, &f)));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn reconcile_value(c: &ReconcileConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());

    let rhs_in = rhs_in_fn(c, &b, &n, &k, &f);
    let mid_in = mid_in_fn(c, &b, &n, &k, &f);
    let low_in = low_in_fn(c, &b, &n, &k, &f);
    let band_in = band_in_fn(c, &b, &n, &k, &f);

    let four_p4 = c.mul(c.four(), c.pow4(&n));
    let deg_rhs = c.ssum(&n, rhs_in.clone()); // LHS of conclusion
    let mid_sum = c.ssum(&n, mid_in.clone());
    let low_sum = c.ssum(&n, low_in.clone());
    let band_sum = c.ssum(&n, band_in.clone());
    let scaled_low = c.mul(four_p4.clone(), low_sum.clone());
    let scaled_band = c.mul(four_p4.clone(), band_sum.clone()); // RHS of conclusion

    // ── per-S : rhs_in S = mid_in S ──
    let per_s = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = d.fresh_local(hcp.clone());

        let z = c.z_coeff(&d, &n, &f, &s); // Z = A_S(pm∘f)
        let zz = c.mul(z.clone(), z.clone());
        let xx = c.x_sq(&n, &f, &s); // f̂·f̂
        let p4 = c.pow4(&n);
        let p4_x = c.mul(p4.clone(), xx.clone()); // P4·X
        let q = c.set_size_of(&n, &s);
        let p = c.ind_of(c.low_bit(&n, &k, &s));

        // h_sq : Z·Z = P4·X   (subsetSum_pm_sq_eq_pow4_fourier n f S).
        let h_sq = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_pm_sq_eq_pow4_fourier"),
                vec![],
            ),
            [n.clone(), f.clone(), s.clone()],
        );

        // h_norm : q·(p·(4·(Z·Z))) = q·(p·(4·(P4·X)))
        //   congr_l q (congr_l p (congr_l 4 h_sq)).
        let four = c.four();
        let inner = c.congr_l(&d, &four, zz.clone(), p4_x.clone(), h_sq);
        let four_zz = c.mul(four.clone(), zz.clone());
        let four_p4x = c.mul(four.clone(), p4_x.clone());
        let inner_p = c.congr_l(&d, &p, four_zz.clone(), four_p4x.clone(), inner);
        let p_4zz = c.mul(p.clone(), four_zz.clone());
        let p_4p4x = c.mul(p.clone(), four_p4x.clone());
        let h_norm = c.congr_l(&d, &q, p_4zz.clone(), p_4p4x.clone(), inner_p);

        // h_reshape : q·(p·(4·(P4·X))) = (4·P4)·(p·(q·X))   monomial_reshape.
        let h_reshape = c.monomial_reshape(&d, &q, &p, &p4, &xx);

        // chain : rhs_in S = mid_in S
        let lhs_term = c.mul(q.clone(), p_4zz.clone()); // q·(p·(4·(Z·Z)))
        let mid_term0 = c.mul(q.clone(), p_4p4x.clone()); // q·(p·(4·(P4·X)))
        let four_p4_s = c.mul(four.clone(), p4.clone());
        let p_qx = c.mul(p.clone(), c.mul(q.clone(), xx.clone()));
        let mid_term = c.mul(four_p4_s.clone(), p_qx.clone()); // (4·P4)·(p·(q·X))
        let body = c.trans(lhs_term, mid_term0, mid_term, h_norm, h_reshape);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    };

    // (1) eq1 : deg_rhs = mid_sum   subsetSum_congr n rhs_in mid_in per_s.
    let ss_congr = Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]);
    let eq1 = Expr::apps(ss_congr, [n.clone(), rhs_in.clone(), mid_in.clone(), per_s]);

    // (2) eq2 : mid_sum = (4·P4)·low_sum   subsetSum_smul n (4·P4) low_in.
    //   subsetSum_smul n cc g : subsetSum n (fun S => cc·(g S)) = cc·subsetSum n g.
    //   `mid_in` is `fun S => (4·P4)·(low_in S)` by β, so its sum is the smul LHS.
    let ss_smul = Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]);
    let eq2 = Expr::apps(ss_smul, [n.clone(), four_p4.clone(), low_in.clone()]);

    // (3) eq3 : low_sum = band_sum   setsize_band_mask_collapse n k (fun S => f̂·f̂).
    let g_x = g_x_fn(c, &b, &n, &f);
    let mask_collapse = Expr::const_(
        Name::from_string("BoolAnalysis.setsize_band_mask_collapse"),
        vec![],
    );
    let eq3 = Expr::apps(mask_collapse, [n.clone(), k.clone(), g_x]);
    //   congr ((4·P4)··) eq3 : (4·P4)·low_sum = (4·P4)·band_sum.
    let eq3_scaled = c.congr_l(&b, &four_p4, low_sum.clone(), band_sum.clone(), eq3);

    // chain : deg_rhs = mid_sum = (4·P4)·low_sum = (4·P4)·band_sum.
    let ch12 = c.trans(
        deg_rhs.clone(),
        mid_sum.clone(),
        scaled_low.clone(),
        eq1,
        eq2,
    );
    let proof = c.trans(deg_rhs, scaled_low, scaled_band, ch12, eq3_scaled);

    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, proof);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.deg_band_rhs_eq_pow4_mass` — the rung-2
    /// normalization-reconciliation:
    /// `deg-band RHS @ b:=pm∘f = (4·4^n)·(Σ_{1≤|S|≤k} setSize·f̂(S)²)`.
    /// See module docs. Kernel-checked, `Constructive`, empty admitted-axiom
    /// closure. Idempotent; no axiom added/removed.
    pub fn register_deg_band_rhs_eq_pow4_mass(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deg_band_rhs_eq_pow4_mass");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, chi, FourierCoefficient, ind, setSize
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?; // Rat.mul_assoc, Rat.mul_comm
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_subset_sum_pm_sq_eq_pow4_fourier()?; // step-1-squared
        self.register_setsize_band_mask_collapse()?; // mask collapse

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = ReconcileConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: reconcile_type(&c),
            value: reconcile_value(&c),
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
    fn test_deg_band_rhs_eq_pow4_mass_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_deg_band_rhs_eq_pow4_mass()
            .expect("register_deg_band_rhs_eq_pow4_mass");
        let nm = Name::from_string("BoolAnalysis.deg_band_rhs_eq_pow4_mass");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("norm-reconcile proof must check: {e:?}"));
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
    fn test_norm_reconcile_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_deg_band_rhs_eq_pow4_mass().expect("first");
        env.register_deg_band_rhs_eq_pow4_mass()
            .expect("idempotent");
    }
}
