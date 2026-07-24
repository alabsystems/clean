// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — STEP 3: the `Jᶜ`-MASKED degree-band
//! charging bound (faithful O'Donnell §9.6 L2 chain, banked toward retiring the
//! `friedgut_boolean(+_helper)` admitted axioms).
//!
//! Two theorems, both in the UN-normalized `Acoeff` world (byte-identical to the
//! unmasked degree-band identity `summed_deriv_lowband_eq_weighted`), masked by
//! the outside-`J` coordinate set `¬J i`:
//!
//! ```text
//! BoolAnalysis.summed_deriv_lowband_eq_weighted_masked :
//!   ∀ (n k : Nat) (b : HCPoint n → Rat) (J : HCPoint n),
//!     Fin.sum n (fun i =>
//!       ind (Bool.not (J i)) ·                                        -- mask i∉J
//!         subsetSum n (fun S =>
//!           ind (Nat.ble (setSizeNat n S) k)
//!             · (Acoeff n (D_i b) S · Acoeff n (D_i b) S)))           -- W^{≤k}[D_i b]
//!     = subsetSum n (fun S =>
//!         setSize n (fun i => Bool.and (S i) (Bool.not (J i)))        -- |S ∩ Jᶜ|
//!           · (ind (Nat.ble (setSizeNat n S) k)
//!               · (Rat.mul 4 (Acoeff n b S · Acoeff n b S))))         -- · 4·A_b(S)²
//!
//! BoolAnalysis.friedgut_masked_deg_band_charge :
//!   ∀ (n k : Nat) (b : HCPoint n → Rat) (J : HCPoint n),
//!     subsetSum n (fun S =>
//!       ind (notSubsetMask n S J)                                     -- S ⊄ J
//!         · (ind (Nat.ble (setSizeNat n S) k)
//!             · (Rat.mul 4 (Acoeff n b S · Acoeff n b S))))           -- · 4·A_b(S)²
//!     ≤
//!     Fin.sum n (fun i =>
//!       ind (Bool.not (J i)) ·
//!         subsetSum n (fun S =>
//!           ind (Nat.ble (setSizeNat n S) k)
//!             · (Acoeff n (D_i b) S · Acoeff n (D_i b) S)))           -- Σ_{i∉J} W^{≤k}[D_i b]
//! ```
//!
//! i.e. `Σ_{S⊄J, |S|≤k} 4·A_b(S)² ≤ Σ_{i∉J} W^{≤k}[D_i b]` — the masked
//! degree-band charging argument. Here
//!   * `Acoeff n g S := subsetSum n (fun y => g y · chi n S y)` is the
//!     un-normalized `S`-Fourier coefficient,
//!   * `D_i b := fun x => b x − b (hcFlip n x i)`,
//!   * `setSize n S := Fin.sum n (fun i => ind (S i))` is the `Rat`-cardinality,
//!   * `notSubsetMask n S J = Nat.ble 1 (setSizeNat n (fun i => S i ∧ ¬J i))`
//!     is the `S ⊄ J` (nonempty `S ∩ Jᶜ`) indicator (RUNG 1 carrier).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE the landed bricks
//!
//! ### EQUALITY (`summed_deriv_lowband_eq_weighted_masked`)
//!
//! Write `w S := ind(ble |S| k)·(4·A_b(S)²)` (the degree-band weight),
//! `D_J S := fun i => S i ∧ ¬J i` (the `S ∩ Jᶜ` indicator). The masked outer sum
//! is `Σ_i ind(¬J i)·W^{≤k}[D_i b]`. Per-`i`, `W^{≤k}[D_i b]` rewrites — by the
//! same `deriv_coeff_sq_eq` + `monomial_swap` step as the unmasked identity,
//! lifted by `subsetSum_congr` — into `subsetSum_S(ind(S i)·w S)`. So the masked
//! outer integrand equals `ind(¬J i)·subsetSum_S(ind(S i)·w S)`. The
//! `Jᶜ`-masked Fubini double-count (`restrict_double_count`, RUNG 4, instantiated
//! at the abstract weight `w`) then transposes/collapses
//! `Σ_i ind(¬J i)·subsetSum_S(ind(S i)·w S) = subsetSum_S(w S · setSize n (D_J S))`,
//! and `mul_comm` flips `w S · |S∩Jᶜ|` to `|S∩Jᶜ| · w S` (= the target RHS
//! integrand). NOTE `restrict_double_count` is generic in `w` only up to its
//! pinned `w S := f̂(S)·f̂(S)` instantiation, so STEP 3 re-derives the
//! `Jᶜ`-masked double count over the band weight `w` directly here
//! (`band_double_count`), reusing `Fin.sum_swap`/`_mul`/`_smul`/`_congr` +
//! `ind_and` exactly as RUNG 4 does.
//!
//! ### CHARGING (`friedgut_masked_deg_band_charge`)
//!
//! Termwise `subsetSum_le_of_pointwise` over the per-`S` bound
//! `ind(notSubsetMask n S J)·w S ≤ |S∩Jᶜ|·w S` — IDENTICAL in shape to RUNG 4's
//! `per_s_bound` but with the nonneg weight `w S` in place of `f̂(S)²`:
//!   * `ind(Nat.ble 1 (setSizeNat n (D_J S))) ≤ Rat.mk(ofNat(setSizeNat n (D_J S)))1`
//!     [`ind_ble_one_le_natCast`], cast to `setSize n (D_J S)`
//!     [`setSize_eq_natCast`], so `ind(notSubsetMask) ≤ |S∩Jᶜ|`;
//!   * `0 ≤ w S` because `w S = ind(band)·(4·A²)` is a product of nonnegatives
//!     (`ind_nonneg`, `4 ≥ 0`, `A·A ≥ 0` via `Rat.mul_self_nonneg`);
//!   * scale by `w S ≥ 0` on the right (`Rat.mul_le_mul_of_nonneg_right`) and
//!     `mul_comm` to match the equality's RHS integrand.
//!
//! Chain the `≤` with the EQUALITY via `Eq.subst`.
//!
//! Every leaf (`deriv_coeff_sq_eq`, `subsetSum_congr`/`_le_of_pointwise`,
//! `subsetSum`, `setSize`/`setSizeNat`/`setSize_eq_natCast`, `Fin.sum_swap`/
//! `_mul`/`_smul`/`_congr`, `ind`/`ind_nonneg`/`ind_and`/`ind_ble_one_le_natCast`,
//! `Nat.cast_le_of_ble`, `Rat.mul_self_nonneg`/`mul_le_mul_of_nonneg_right`/
//! `mul_comm`/`mul_assoc`/`mul_nonneg`, the `Eq`/`Bool.rec` built-ins) is itself a
//! landed `Constructive` empty-closure Theorem/reducible Definition, so both
//! theorems here are `ProofQuality::Constructive` with an EMPTY closure. NO
//! `sorry` / `add_decl_unchecked` / `add_decl_structural` / `native_decide` /
//! `unsafe` / `Real`. No axiom added or removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared carrier atoms for the masked degree-band charging. Carrier spellings
/// (`Acoeff`/`subsetSum`/`chi`, `hcFlip`, `ind`, `setSize`/`setSizeNat`,
/// `Nat.ble`, `Fin.sum`, `notSubsetMask`, `4 := mk(ofNat 4) 1`) byte-match the
/// consumed carriers (the unmasked deg-band identity + RUNG 4 + RUNG 1).
struct MaskedDegBandConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_and: Expr,
    bool_not: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_ble: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_swap: Expr,
    fin_sum_smul: Expr,
    fin_sum_mul: Expr,
    fin_sum_congr: Expr,
    chi: Expr,
    hc_flip: Expr,
    hc_decode: Expr,
    ind: Expr,
    ind_nonneg: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    set_size_eq_natcast: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_le_of_pointwise: Expr,
    not_subset_mask: Expr,
    deriv_coeff_sq_eq: Expr,
    ind_and: Expr,
    ind_ble_one_le_natcast: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
    mul_le_right: Expr,
    nat_pow: Expr,
    hcpoint: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    l1: Level,
    l0: Level,
}

impl MaskedDegBandConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_ble: k("Nat.ble"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_swap: k("Fin.sum_swap"),
            fin_sum_smul: k("Fin.sum_smul"),
            fin_sum_mul: k("Fin.sum_mul"),
            fin_sum_congr: k("Fin.sum_congr"),
            chi: k("BoolAnalysis.chi"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            ind: k("BoolAnalysis.ind"),
            ind_nonneg: k("BoolAnalysis.ind_nonneg"),
            set_size: k("BoolAnalysis.setSize"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            set_size_eq_natcast: k("BoolAnalysis.setSize_eq_natCast"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_le_of_pointwise: k("BoolAnalysis.subsetSum_le_of_pointwise"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            deriv_coeff_sq_eq: k("BoolAnalysis.deriv_coeff_sq_eq"),
            ind_and: k("BoolAnalysis.ind_and"),
            ind_ble_one_le_natcast: k("BoolAnalysis.ind_ble_one_le_natCast"),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_nonneg: k("Rat.mul_nonneg"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            nat_pow: k("Nat.pow"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            l1,
            l0: Level::zero(),
        }
    }

    // ── small constructors ──
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
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
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
    fn decode(&self, n: &Expr, jj: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), jj.clone()])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn band(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [a, b])
    }
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), a)
    }
    fn pow2(&self, n: &Expr) -> Expr {
        let two = self.succ(self.nat_one());
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
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
    fn not_subset_mask_of(&self, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.not_subset_mask.clone(),
            [n.clone(), s.clone(), j.clone()],
        )
    }
    /// `Nat.ble (setSizeNat n S) k` — the low-band bit.
    fn band_bit(&self, n: &Expr, k: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            self.nat_ble.clone(),
            [self.set_size_nat_of(n, s), k.clone()],
        )
    }
    /// `Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), m), self.nat_one()],
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
    /// `D_J S := fun (i : Fin n) => Bool.and (S i) (Bool.not (J i))` — the
    /// `S ∩ Jᶜ` coordinate set. BYTE-IDENTICAL to `notSubsetMask`'s inner lambda
    /// and to RUNG 4's `diff_point`.
    fn diff_point(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let j_i = Expr::app(j.clone(), i.clone());
        let body = self.band(s_i, self.bnot(j_i));
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    // ── Eq plumbing ──
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn refl_rat(&self, x: Expr) -> Expr {
        Expr::apps(self.order.eq_refl.clone(), [self.rat.clone(), x])
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, cc, h1, h2)
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_a)
    }
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `@congrArg Rat Rat a b motive h : motive a = motive b`.
    fn congr_rat(&self, a: Expr, b: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, motive, h],
        )
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
    fn congr_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_rat(a, b, f, h)
    }
    /// `congrArg (fun z => z·right) h : a·right = b·right`.
    fn congr_r(&self, parent: &EnvDeclBuilder, right: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_rat(a, b, f, h)
    }

    /// `monomial_swap p q g : p·((4·q)·g) = q·(p·(4·g))` — pure-`Rat` rearrange,
    /// byte-identical to the unmasked deg-band's `monomial_swap`.
    fn monomial_swap(&self, parent: &EnvDeclBuilder, p: &Expr, q: &Expr, g: &Expr) -> Expr {
        let four = self.four();
        let four_q = self.mul(four.clone(), q.clone());
        let four_g = self.mul(four.clone(), g.clone());
        let q_g = self.mul(q.clone(), g.clone());

        let assoc_4qg = self.assoc(four.clone(), q.clone(), g.clone());
        let four_qg = self.mul(four.clone(), q_g.clone());
        let s1 = self.symm_rat(
            self.mul(four_q.clone(), g.clone()),
            four_qg.clone(),
            assoc_4qg,
        );
        let q_4 = self.mul(q.clone(), four.clone());
        let s2 = self.congr_r(
            parent,
            g,
            four_q.clone(),
            q_4.clone(),
            self.comm(four.clone(), q.clone()),
        );
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
        );

        let p_4qg = self.mul(p.clone(), self.mul(four_q.clone(), g.clone()));
        let p_4_qg = self.mul(p.clone(), four_qg.clone());
        let a1 = self.congr_l(
            parent,
            p,
            self.mul(four_q.clone(), g.clone()),
            four_qg.clone(),
            self.assoc(four.clone(), q.clone(), g.clone()),
        );
        let p_q_4g = self.mul(p.clone(), self.mul(q.clone(), four_g.clone()));
        let a2 = self.congr_l(
            parent,
            p,
            four_qg.clone(),
            self.mul(q.clone(), four_g.clone()),
            inner,
        );
        let pq = self.mul(p.clone(), q.clone());
        let pq_4g = self.mul(pq.clone(), four_g.clone());
        let a3 = self.symm_rat(
            pq_4g.clone(),
            p_q_4g.clone(),
            self.assoc(p.clone(), q.clone(), four_g.clone()),
        );
        let qp = self.mul(q.clone(), p.clone());
        let qp_4g = self.mul(qp.clone(), four_g.clone());
        let a4 = self.congr_r(
            parent,
            &four_g,
            pq.clone(),
            qp.clone(),
            self.comm(p.clone(), q.clone()),
        );
        let q_p_4g = self.mul(q.clone(), self.mul(p.clone(), four_g.clone()));
        let a5 = self.assoc(q.clone(), p.clone(), four_g.clone());

        let c12 = self.trans_rat(p_4qg.clone(), p_4_qg.clone(), p_q_4g.clone(), a1, a2);
        let c123 = self.trans_rat(p_4qg.clone(), p_q_4g.clone(), pq_4g.clone(), c12, a3);
        let c1234 = self.trans_rat(p_4qg.clone(), pq_4g.clone(), qp_4g.clone(), c123, a4);
        self.trans_rat(p_4qg, qp_4g, q_p_4g, c1234, a5)
    }
}

// ─────────────── integrand builders ───────────────

/// `w_fn(b,k) := fun S => ind(ble |S| k) · (4 · (A_b(S)·A_b(S)))` — the
/// degree-band weight `w S` (byte-identical to the unmasked deg-band `w_fn`).
fn w_fn(c: &MaskedDegBandConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, b: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let cap_a = c.acoeff(&d, n, b, &s);
    let g = c.mul(cap_a.clone(), cap_a);
    let body = c.mul(c.ind_of(c.band_bit(n, k, &s)), c.mul(c.four(), g));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `lhs_i(b,k,J) := fun i => ind(¬J i) · subsetSum n (fun S => ind(ble |S| k)·(A(D_i b,S)·A(D_i b,S)))`
/// — the masked `Σ_i` integrand `ind(¬J i)·W^{≤k}[D_i b]`.
fn lhs_i_fn(
    c: &MaskedDegBandConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    b: &Expr,
    j: &Expr,
) -> Expr {
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
    let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
    let body = c.mul(mask, c.ssum(n, inner));
    ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `coord_i(b,k,J) := fun i => ind(¬J i) · subsetSum n (fun S => ind(S i) · w S)`
/// — the masked double-count `Σ_i` integrand.
fn coord_i_fn(
    c: &MaskedDegBandConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    b: &Expr,
    j: &Expr,
) -> Expr {
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
    let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
    let body = c.mul(mask, c.ssum(n, inner));
    ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `size_w_fn := fun S => setSize n (D_J S) · w S` — the masked double-count RHS
/// integrand (= the EQUALITY's RHS integrand).
fn size_w_fn(
    c: &MaskedDegBandConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    b: &Expr,
    j: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let cap_a = c.acoeff(&d, n, b, &s);
    let g = c.mul(cap_a.clone(), cap_a);
    let w = c.mul(c.ind_of(c.band_bit(n, k, &s)), c.mul(c.four(), g));
    let d_pt = c.diff_point(&d, n, &s, j);
    let body = c.mul(c.set_size_of(n, &d_pt), w);
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `mass_fn := fun S => ind(notSubsetMask n S J) · w S` — the CHARGING LHS
/// integrand `Σ_{S⊄J,|S|≤k} 4·A_b(S)²`.
fn mass_fn(
    c: &MaskedDegBandConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    b: &Expr,
    j: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let cap_a = c.acoeff(&d, n, b, &s);
    let g = c.mul(cap_a.clone(), cap_a);
    let w = c.mul(c.ind_of(c.band_bit(n, k, &s)), c.mul(c.four(), g));
    let mask = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let body = c.mul(mask, w);
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

// ─────────────── the EQUALITY: masked deg-band double count ───────────────

fn masked_eq_type(c: &MaskedDegBandConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let lhs = c.fin_sum_of(&n, lhs_i_fn(c, &b, &n, &k, &bf, &j));
    let rhs = c.ssum(&n, size_w_fn(c, &b, &n, &k, &bf, &j));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(j_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn masked_eq_value(c: &MaskedDegBandConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let lhs_i = lhs_i_fn(c, &b, &n, &k, &bf, &j);
    let coord_i = coord_i_fn(c, &b, &n, &k, &bf, &j);

    // ── step1 : Σ_i lhs_i = Σ_i coord_i   [Fin.sum_congr, per-i].
    // per_i : ∀ i, ind(¬J i)·W^{≤k}[D_i b] = ind(¬J i)·subsetSum_S(ind(S i)·w S).
    let per_i = {
        let mut ib = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ib.fresh_local(fin_n.clone());
        let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));

        // INNER_LHS := fun S => ind(ble |S| k)·(A(D_i b,S)·A(D_i b,S)).
        let inner_lhs = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let db = c.deriv(&d, &n, &bf, &i);
            let cap_ad = c.acoeff(&d, &n, &db, &s);
            let body = c.mul(
                c.ind_of(c.band_bit(&n, &k, &s)),
                c.mul(cap_ad.clone(), cap_ad),
            );
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        // INNER_COORD := fun S => ind(S i)·w S.
        let inner_coord = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let q = c.ind_of(Expr::app(s.clone(), i.clone()));
            let cap_a = c.acoeff(&d, &n, &bf, &s);
            let g = c.mul(cap_a.clone(), cap_a);
            let ww = c.mul(c.ind_of(c.band_bit(&n, &k, &s)), c.mul(c.four(), g));
            let body = c.mul(q, ww);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };

        // per_s : ∀ S, INNER_LHS S = INNER_COORD S   (deriv_coeff_sq_eq + monomial_swap).
        let per_s = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let db = c.deriv(&d, &n, &bf, &i);
            let cap_ad = c.acoeff(&d, &n, &db, &s);
            let ad_sq = c.mul(cap_ad.clone(), cap_ad.clone());
            let p = c.ind_of(c.band_bit(&n, &k, &s));
            let q = c.ind_of(Expr::app(s.clone(), i.clone()));
            let cap_a = c.acoeff(&d, &n, &bf, &s);
            let g = c.mul(cap_a.clone(), cap_a.clone());
            let four_q = c.mul(c.four(), q.clone());
            let rhs_sq = c.mul(four_q.clone(), g.clone());

            // dcs : A(D_i b,S)² = (4·ind(S i))·A_b(S)²   [deriv_coeff_sq_eq n b S i].
            let dcs = Expr::apps(
                c.deriv_coeff_sq_eq.clone(),
                [n.clone(), bf.clone(), s.clone(), i.clone()],
            );
            let p_adsq = c.mul(p.clone(), ad_sq.clone());
            let p_rhs = c.mul(p.clone(), rhs_sq.clone());
            // c1 : p·(A(D_i b,S)²) = p·((4·q)·g)   congr (p··) dcs.
            let c1 = c.congr_l(&d, &p, ad_sq.clone(), rhs_sq.clone(), dcs);
            // c2 : p·((4·q)·g) = q·(p·(4·g))   monomial_swap p q g.
            let four_g = c.mul(c.four(), g.clone());
            let q_w = c.mul(q.clone(), c.mul(p.clone(), four_g.clone()));
            let c2 = c.monomial_swap(&d, &p, &q, &g);
            let body = c.trans_rat(p_adsq, p_rhs, q_w, c1, c2);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        // ss_congr : subsetSum INNER_LHS = subsetSum INNER_COORD.
        let ss_congr = Expr::apps(
            c.subset_sum_congr.clone(),
            [n.clone(), inner_lhs.clone(), inner_coord.clone(), per_s],
        );
        // motive : fun z => ind(¬J i)·z.
        let motive = {
            let mut e = EnvDeclBuilder::child_of(&ib);
            let (z_id, z) = e.fresh_local(c.rat.clone());
            let body = c.mul(mask.clone(), z);
            e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        // body : ind(¬J i)·subsetSum INNER_LHS = ind(¬J i)·subsetSum INNER_COORD  (congr).
        let ss_lhs = c.ssum(&n, inner_lhs.clone());
        let ss_coord = c.ssum(&n, inner_coord.clone());
        let body = c.congr_rat(ss_lhs, ss_coord, motive, ss_congr);
        ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    let lhs_sum = c.fin_sum_of(&n, lhs_i.clone());
    let coord_sum = c.fin_sum_of(&n, coord_i.clone());
    let step1 = Expr::apps(
        c.fin_sum_congr.clone(),
        [n.clone(), lhs_i.clone(), coord_i.clone(), per_i],
    );

    // ── step2 : Σ_i coord_i = subsetSum_S(w S · setSize n (D_J S))   [band_double_count].
    let w = w_fn(c, &b, &n, &k, &bf);
    let step2 = band_double_count_value(c, &b, &n, &j, &w);
    // band_double_count RHS integrand: fun S => w S · setSize n (D_J S).
    let w_size_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let cap_a = c.acoeff(&d, &n, &bf, &s);
        let g = c.mul(cap_a.clone(), cap_a);
        let ww = c.mul(c.ind_of(c.band_bit(&n, &k, &s)), c.mul(c.four(), g));
        let d_pt = c.diff_point(&d, &n, &s, &j);
        let body = c.mul(ww, c.set_size_of(&n, &d_pt));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let w_size_sum = c.ssum(&n, w_size_fn.clone());

    // ── step3 : subsetSum_S(w S · |D_J S|) = subsetSum_S(|D_J S| · w S)  [subsetSum_congr, mul_comm].
    let per_s_comm = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let cap_a = c.acoeff(&d, &n, &bf, &s);
        let g = c.mul(cap_a.clone(), cap_a);
        let ww = c.mul(c.ind_of(c.band_bit(&n, &k, &s)), c.mul(c.four(), g));
        let d_pt = c.diff_point(&d, &n, &s, &j);
        let size = c.set_size_of(&n, &d_pt);
        let body = c.comm(ww, size);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let size_w_sum = c.ssum(&n, size_w_fn(c, &b, &n, &k, &bf, &j));
    let step3 = Expr::apps(
        c.subset_sum_congr.clone(),
        [
            n.clone(),
            w_size_fn.clone(),
            size_w_fn(c, &b, &n, &k, &bf, &j),
            per_s_comm,
        ],
    );

    // chain : lhs_sum =(step1) coord_sum =(step2) w_size_sum =(step3) size_w_sum.
    let t12 = c.trans_rat(
        lhs_sum.clone(),
        coord_sum.clone(),
        w_size_sum.clone(),
        step1,
        step2,
    );
    let proof = c.trans_rat(lhs_sum, w_size_sum, size_w_sum, t12, step3);

    let e = b.mk_lam(j_id, BinderInfo::Default, hcp, proof);
    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// The `Jᶜ`-masked Fubini double count over an ABSTRACT weight `w : HCPoint n → Rat`:
/// `Σ_i ind(¬J i)·subsetSum_S(ind(S i)·w S) = subsetSum_S(w S · setSize n (D_J S))`.
/// Returns the PROOF TERM (a closed proof at the given `n, J, w`). Byte-identical
/// structure to RUNG 4's `restrict_double_count_value` but at the abstract `w`.
fn band_double_count_value(
    c: &MaskedDegBandConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    j: &Expr,
    w: &Expr,
) -> Expr {
    let p2n = c.pow2(n);
    let hcp = c.hcpoint_of(n);

    // w_of(S) := w S.
    let w_of = |s: &Expr| Expr::app(w.clone(), s.clone());

    // coord_i := fun i => ind(¬J i)·subsetSum_S(ind(S i)·w S)  (= the LHS integrand).
    let coord_i = {
        let mut ci = EnvDeclBuilder::child_of(parent);
        let fin_n = c.fin_of(n);
        let (i_id, i) = ci.fresh_local(fin_n.clone());
        let inner = {
            let mut d = EnvDeclBuilder::child_of(&ci);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let body = c.mul(c.ind_of(Expr::app(s.clone(), i.clone())), w_of(&s));
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
        let body = c.mul(mask, c.ssum(n, inner));
        ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let lhs0 = c.fin_sum_of(n, coord_i.clone());

    // big_f : Fin n → Fin (2^n) → Rat, F i j := ind(¬J i)·(ind((dec jj) i)·w(dec jj)).
    let big_f = {
        let mut ci = EnvDeclBuilder::child_of(parent);
        let fin_n = c.fin_of(n);
        let (i_id, i) = ci.fresh_local(fin_n.clone());
        let inner = {
            let mut cj = EnvDeclBuilder::child_of(&ci);
            let fin_pow = c.fin_of(&p2n);
            let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
            let s = c.decode(n, &jj);
            let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask, c.mul(c.ind_of(s_i), w_of(&s)));
            cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
        };
        ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, inner))
    };

    // outer_i_F := fun i => Fin.sum (2^n) (fun jj => F i jj).
    let outer_i_f = {
        let mut ci = EnvDeclBuilder::child_of(parent);
        let fin_n = c.fin_of(n);
        let (i_id, i) = ci.fresh_local(fin_n.clone());
        let row = {
            let mut cj = EnvDeclBuilder::child_of(&ci);
            let fin_pow = c.fin_of(&p2n);
            let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
            let s = c.decode(n, &jj);
            let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask, c.mul(c.ind_of(s_i), w_of(&s)));
            cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
        };
        let body = c.fin_sum_of(&p2n, row);
        ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let sum_outer_i = c.fin_sum_of(n, outer_i_f.clone());

    // pointwise1 : ∀ i, coord_i i = outer_i_F i.
    let pointwise1 = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = c.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
        // Gi := fun jj => ind((dec jj) i)·w(dec jj).
        let gi = {
            let mut cj = EnvDeclBuilder::child_of(&d);
            let fin_pow = c.fin_of(&p2n);
            let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
            let s = c.decode(n, &jj);
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(c.ind_of(s_i), w_of(&s));
            cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
        };
        // Fin.sum_smul (2^n) mask Gi : Σ_jj (mask·Gi jj) = mask·Σ_jj Gi jj.
        let smul = Expr::apps(
            c.fin_sum_smul.clone(),
            [p2n.clone(), mask.clone(), gi.clone()],
        );
        let sumprod = {
            let mut cj = EnvDeclBuilder::child_of(&d);
            let fin_pow = c.fin_of(&p2n);
            let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
            let s = c.decode(n, &jj);
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask.clone(), c.mul(c.ind_of(s_i), w_of(&s)));
            cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
        };
        let sum_sumprod = c.fin_sum_of(&p2n, sumprod);
        let mask_ss = c.mul(mask.clone(), c.fin_sum_of(&p2n, gi.clone()));
        let body = c.symm_rat(sum_sumprod, mask_ss, smul);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let step1 = Expr::apps(
        c.fin_sum_congr.clone(),
        [n.clone(), coord_i.clone(), outer_i_f.clone(), pointwise1],
    );

    // step2 : Fin.sum_swap n (2^n) F.
    let step2 = Expr::apps(
        c.fin_sum_swap.clone(),
        [n.clone(), p2n.clone(), big_f.clone()],
    );
    let inner_swapped = {
        let mut cj = EnvDeclBuilder::child_of(parent);
        let fin_pow = c.fin_of(&p2n);
        let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
        let row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let s = c.decode(n, &jj);
            let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask, c.mul(c.ind_of(s_i), w_of(&s)));
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let body = c.fin_sum_of(n, row);
        cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
    };
    let sum_swapped = c.fin_sum_of(&p2n, inner_swapped.clone());

    // target_j := fun jj => w(dec jj)·setSize n (D_J (dec jj)).
    let target_j = {
        let mut cj = EnvDeclBuilder::child_of(parent);
        let fin_pow = c.fin_of(&p2n);
        let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
        let s = c.decode(n, &jj);
        let d_pt = c.diff_point(&cj, n, &s, j);
        let size = c.set_size_of(n, &d_pt);
        let body = c.mul(w_of(&s), size);
        cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
    };

    // per_j : ∀ jj, inner_swapped jj = target_j jj.
    let per_j = {
        let mut cj = EnvDeclBuilder::child_of(parent);
        let fin_pow = c.fin_of(&p2n);
        let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
        let s = c.decode(n, &jj);
        let d_pt = c.diff_point(&cj, n, &s, j);
        let w_s = w_of(&s);
        let size = c.set_size_of(n, &d_pt);

        let inner_row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask, c.mul(c.ind_of(s_i), w_s.clone()));
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let dw_row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let d_i = c.band(
                Expr::app(s.clone(), i.clone()),
                c.bnot(Expr::app(j.clone(), i.clone())),
            );
            let body = c.mul(c.ind_of(d_i), w_s.clone());
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let d_ind_row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let d_i = c.band(
                Expr::app(s.clone(), i.clone()),
                c.bnot(Expr::app(j.clone(), i.clone())),
            );
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, c.ind_of(d_i)))
        };

        // P_i : ind(¬J i)·(ind(S i)·w S) = ind(D_J S i)·w S.
        let pw = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let s_i = Expr::app(s.clone(), i.clone());
            let nj_i = c.bnot(Expr::app(j.clone(), i.clone()));
            let ind_si = c.ind_of(s_i.clone());
            let ind_nj = c.ind_of(nj_i.clone());

            let e0 = c.mul(ind_nj.clone(), c.mul(ind_si.clone(), w_s.clone()));
            let nj_si = c.mul(ind_nj.clone(), ind_si.clone());
            let e1 = c.mul(nj_si.clone(), w_s.clone());
            let assoc = c.assoc(ind_nj.clone(), ind_si.clone(), w_s.clone());
            let leg1 = c.symm_rat(e1.clone(), e0.clone(), assoc);

            let motive_r = {
                let mut e = EnvDeclBuilder::child_of(&ci);
                let (z_id, z) = e.fresh_local(c.rat.clone());
                let body = c.mul(z, w_s.clone());
                e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let si_nj = c.mul(ind_si.clone(), ind_nj.clone());
            let e2 = c.mul(si_nj.clone(), w_s.clone());
            let cmm = c.comm(ind_nj.clone(), ind_si.clone());
            let leg2 = c.congr_rat(nj_si.clone(), si_nj.clone(), motive_r.clone(), cmm);

            let d_i = c.band(s_i.clone(), nj_i.clone());
            let ind_d = c.ind_of(d_i.clone());
            let e3 = c.mul(ind_d.clone(), w_s.clone());
            let ind_and = Expr::apps(c.ind_and.clone(), [s_i.clone(), nj_i.clone()]);
            let ind_and_sym = c.symm_rat(ind_d.clone(), si_nj.clone(), ind_and);
            let leg3 = c.congr_rat(si_nj.clone(), ind_d.clone(), motive_r.clone(), ind_and_sym);

            let t1 = c.trans_rat(e0.clone(), e1.clone(), e2.clone(), leg1, leg2);
            let body = c.trans_rat(e0, e2, e3, t1, leg3);
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };

        let q1 = Expr::apps(
            c.fin_sum_congr.clone(),
            [n.clone(), inner_row.clone(), dw_row.clone(), pw],
        );
        let q2 = Expr::apps(
            c.fin_sum_mul.clone(),
            [n.clone(), d_ind_row.clone(), w_s.clone()],
        );
        let q3 = c.comm(size.clone(), w_s.clone());

        let sum_inner = c.fin_sum_of(n, inner_row.clone());
        let sum_dw = c.fin_sum_of(n, dw_row.clone());
        let size_w = c.mul(size.clone(), w_s.clone());
        let w_size = c.mul(w_s.clone(), size.clone());

        let t1 = c.trans_rat(sum_inner.clone(), sum_dw.clone(), size_w.clone(), q1, q2);
        let body = c.trans_rat(sum_inner, size_w, w_size, t1, q3);
        cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
    };

    let step3 = Expr::apps(
        c.fin_sum_congr.clone(),
        [p2n.clone(), inner_swapped.clone(), target_j.clone(), per_j],
    );

    // rhs := subsetSum_S(w S · setSize n (D_J S))  (≡ sum_target by δ).
    let rhs = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let d_pt = c.diff_point(&d, n, &s, j);
        let size = c.set_size_of(n, &d_pt);
        let body = c.mul(w_of(&s), size);
        let f = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body));
        c.ssum(n, f)
    };
    let sum_target = c.fin_sum_of(&p2n, target_j.clone());

    let t1 = c.trans_rat(
        lhs0.clone(),
        sum_outer_i.clone(),
        sum_swapped.clone(),
        step1,
        step2,
    );
    c.trans_rat(lhs0, sum_swapped.clone(), rhs.clone(), t1, {
        c.trans_rat(
            sum_swapped,
            sum_target,
            rhs.clone(),
            step3,
            c.refl_rat(rhs.clone()),
        )
    })
}

// ─────────────── the CHARGING bound (STEP 3 target) ───────────────

fn charge_type(c: &MaskedDegBandConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let lhs = c.ssum(&n, mass_fn(c, &b, &n, &k, &bf, &j));
    let rhs = c.fin_sum_of(&n, lhs_i_fn(c, &b, &n, &k, &bf, &j));
    let concl = c.rat_le(lhs, rhs);

    let e = b.mk_pi(j_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn charge_value(c: &MaskedDegBandConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    // EqR : subsetSum_S(|D_J S|·w S) = Σ_{i∉J} W^{≤k}[D_i b]  (symm of the masked eq).
    let masked_eq = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.summed_deriv_lowband_eq_weighted_masked"),
            vec![],
        ),
        [n.clone(), k.clone(), bf.clone(), j.clone()],
    );
    let lhs_sum = c.fin_sum_of(&n, lhs_i_fn(c, &b, &n, &k, &bf, &j));
    let size_w_sum = c.ssum(&n, size_w_fn(c, &b, &n, &k, &bf, &j));
    // masked_eq : lhs_sum = size_w_sum ; symm : size_w_sum = lhs_sum.
    let eq_r = c.symm_rat(lhs_sum.clone(), size_w_sum.clone(), masked_eq);

    // step_le : subsetSum_S(ind(notSubsetMask)·w S) ≤ subsetSum_S(|D_J S|·w S)
    //   [subsetSum_le_of_pointwise n mass_fn size_w_fn per_s].
    let per_s = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let body = per_s_bound(c, &d, &n, &k, &bf, &s, &j);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs_mass = c.ssum(&n, mass_fn(c, &b, &n, &k, &bf, &j));
    let step_le = Expr::apps(
        c.subset_sum_le_of_pointwise.clone(),
        [
            n.clone(),
            mass_fn(c, &b, &n, &k, &bf, &j),
            size_w_fn(c, &b, &n, &k, &bf, &j),
            per_s,
        ],
    );

    // proof : lhs_mass ≤ Σ_{i∉J} W^{≤k}[D_i b]
    //   := subst (motive t => lhs_mass ≤ t) size_w_sum lhs_sum EqR step_le.
    let motive_top = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = e.fresh_local(c.rat.clone());
        let body = c.rat_le(lhs_mass.clone(), t);
        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let proof = c.subst_rat(
        motive_top,
        size_w_sum.clone(),
        lhs_sum.clone(),
        eq_r,
        step_le,
    );

    let e = b.mk_lam(j_id, BinderInfo::Default, hcp, proof);
    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// Per-`S` bound `ind(notSubsetMask n S J)·w S ≤ |S∩Jᶜ| · w S` at a fixed `S`,
/// where `w S := ind(ble |S| k)·(4·A_b(S)²)`. Mirrors RUNG 4's `per_s_bound`,
/// with the nonneg weight `w S` (product of nonnegatives) in place of `f̂(S)²`.
fn per_s_bound(
    c: &MaskedDegBandConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    b: &Expr,
    s: &Expr,
    j: &Expr,
) -> Expr {
    let d_pt = c.diff_point(parent, n, s, j);
    let size = c.set_size_of(n, &d_pt); // setSize n (D_J S) = |S∩Jᶜ|
    let size_nat = c.set_size_nat_of(n, &d_pt); // setSizeNat n (D_J S)
    let cast = c.natcast(size_nat.clone());
    let mask = c.ind_of(c.not_subset_mask_of(n, s, j)); // ≡ ind(Nat.ble 1 (setSizeNat …))

    // w S := ind(ble |S| k)·(4·A²)  (the band weight).
    let cap_a = c.acoeff(parent, n, b, s);
    let g = c.mul(cap_a.clone(), cap_a.clone());
    let four_g = c.mul(c.four(), g.clone());
    let band = c.ind_of(c.band_bit(n, k, s));
    let w_s = c.mul(band.clone(), four_g.clone());

    // l2 : ind(Nat.ble 1 (setSizeNat n (D_J S))) ≤ mk(ofNat(setSizeNat …))1
    //   [ind_ble_one_le_natCast (setSizeNat n (D_J S))].  LHS ≡ ind(mask) (δ).
    let l2 = Expr::apps(c.ind_ble_one_le_natcast.clone(), [size_nat.clone()]);

    // bridge : setSize n (D_J S) = mk(ofNat(setSizeNat …))1  [setSize_eq_natCast];
    //   symm : mk … = setSize.
    let bridge = Expr::apps(c.set_size_eq_natcast.clone(), [n.clone(), d_pt.clone()]);
    let bridge_sym = c.symm_rat(size.clone(), cast.clone(), bridge);

    // ind_le_size : ind(mask) ≤ setSize n (D_J S)
    //   := subst (motive t => ind(mask) ≤ t) cast size bridge_sym l2.
    let motive_le = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = e.fresh_local(c.rat.clone());
        let body = c.rat_le(mask.clone(), t);
        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let ind_le_size = c.subst_rat(motive_le, cast.clone(), size.clone(), bridge_sym, l2);

    // hnn : 0 ≤ w S = ind(band)·(4·A²).
    //   hg : 0 ≤ A·A    [Rat.sq_nonneg A].
    let hg = Expr::app(c.sq_nonneg.clone(), cap_a.clone());
    //   h4g : 0 ≤ 4·(A·A)   [Rat.mul_nonneg 4 (A·A) (0≤4) hg].
    let four_nonneg = {
        // 0 ≤ 4 := Rat.le_of_ble_eq_true 0 4 (refl true).
        let bool_c = c.bool_.clone();
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let refl_btrue = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![c.l1.clone()]),
            [bool_c, btrue],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            [c.order.rat_zero.clone(), c.four(), refl_btrue],
        )
    };
    let h4g = Expr::apps(c.mul_nonneg.clone(), [c.four(), g.clone(), four_nonneg, hg]);
    //   hnn : 0 ≤ ind(band)·(4·(A·A))   [Rat.mul_nonneg ind(band) (4·A²) (ind_nonneg band) h4g].
    let ind_band_nonneg = Expr::app(c.ind_nonneg.clone(), c.band_bit(n, k, s));
    let hnn = Expr::apps(
        c.mul_nonneg.clone(),
        [band.clone(), four_g.clone(), ind_band_nonneg, h4g],
    );

    // mul_le : ind(mask)·w S ≤ setSize n (D_J S)·w S
    //   [Rat.mul_le_mul_of_nonneg_right (w S) (ind mask) (setSize) ind_le_size hnn].
    let mul_le = Expr::apps(
        c.mul_le_right.clone(),
        [w_s.clone(), mask.clone(), size.clone(), ind_le_size, hnn],
    );

    // final : ind(mask)·w S ≤ setSize n (D_J S)·w S  (= mass_fn S ≤ size_w_fn S).
    //   mass_fn S ≡ ind(mask)·w S and size_w_fn S ≡ setSize·w S definitionally, so
    //   the bound is exactly the per-S goal; no mul_comm flip is needed because the
    //   EQUALITY's RHS integrand is setSize·w (size_w_fn), matching mul_le's RHS.
    mul_le
}

impl Environment {
    /// Initialize Friedgut STEP 3 — the `Jᶜ`-masked degree-band charging. Registers
    /// `BoolAnalysis.summed_deriv_lowband_eq_weighted_masked` (the masked
    /// double-count equality) and `BoolAnalysis.friedgut_masked_deg_band_charge`
    /// (the charging inequality `Σ_{S⊄J,|S|≤k} 4·A_b² ≤ Σ_{i∉J} W^{≤k}[D_i b]`).
    /// Idempotent; kernel-checked, `Constructive`, EMPTY admitted-axiom closure.
    /// No axiom added or removed.
    pub fn init_boolean_analysis_friedgut_deg_band_masked(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis()?; // chi, ind, hcFlip, hcDecode, Acoeff carriers
        self.init_rat()?; // Rat.mul_assoc, Rat.mul_comm, Rat.sub
        self.init_rat_field_inst()?; // Rat.mul_nonneg, Rat.le_of_ble_eq_true
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_right, LE.le
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_le_of_pointwise()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;
        self.register_set_size_eq_natcast()?;
        self.register_deriv_coeff_sq_eq()?; // deriv_coeff_sq_eq + Rat.mul_self_nonneg
        self.register_fin_sum_swap_theorem()?; // Fin.sum_swap, Fin.sum_congr, Fin.sum_smul
        self.register_fin_sum_mul_theorem()?; // Fin.sum_mul
        self.register_ind_and()?; // BoolAnalysis.ind_and
        self.register_ind_ble_one_le_natcast()?; // BoolAnalysis.ind_ble_one_le_natCast
        self.init_boolean_analysis_friedgut_cheap_rungs()?; // notSubsetMask
        self.init_boolean_analysis_kkl_hcdual()?; // BoolAnalysis.ind_nonneg

        let name_eq = Name::from_string("BoolAnalysis.summed_deriv_lowband_eq_weighted_masked");
        if self.get_const(&name_eq).is_none() {
            let c = MaskedDegBandConsts::new();
            self.add_decl(Declaration::Theorem {
                name: name_eq,
                level_params: vec![],
                type_: masked_eq_type(&c),
                value: masked_eq_value(&c),
            })?;
        }
        let name_charge = Name::from_string("BoolAnalysis.friedgut_masked_deg_band_charge");
        if self.get_const(&name_charge).is_none() {
            let c = MaskedDegBandConsts::new();
            self.add_decl(Declaration::Theorem {
                name: name_charge,
                level_params: vec![],
                type_: charge_type(&c),
                value: charge_value(&c),
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_deg_band_masked()
            .expect("init_boolean_analysis_friedgut_deg_band_masked");
        env.init_boolean_analysis_friedgut_deg_band_masked()
            .expect("idempotent");
        env
    }

    fn assert_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
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
            "{name} closure must be foundational-only (empty), got {:?}",
            env.axiom_deps(&nm)
        );
    }

    #[test]
    fn test_summed_deriv_lowband_eq_weighted_masked_is_constructive_theorem() {
        assert_constructive(
            &env(),
            "BoolAnalysis.summed_deriv_lowband_eq_weighted_masked",
        );
    }

    #[test]
    fn test_friedgut_masked_deg_band_charge_is_constructive_theorem() {
        assert_constructive(&env(), "BoolAnalysis.friedgut_masked_deg_band_charge");
    }

    /// Guard: the charging statement's conclusion head is `LE.le` (a genuine ≤),
    /// not a vacuous restatement.
    #[test]
    fn test_charge_statement_is_a_genuine_le() {
        let env = env();
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.friedgut_masked_deg_band_charge",
            ))
            .expect("registered");
        let mut ty = &info.type_;
        for _ in 0..4 {
            match ty.kind() {
                crate::expr::ExprKind::Pi(_, _, body) => ty = body,
                other => panic!("expected Pi, got {other:?}"),
            }
        }
        let mut head = ty;
        while let crate::expr::ExprKind::App(g, _) = head.kind() {
            head = g;
        }
        match head.kind() {
            crate::expr::ExprKind::Const(name, _) => {
                assert_eq!(name.to_string(), "LE.le", "conclusion head must be LE.le")
            }
            other => panic!("conclusion head must be LE.le, got {other:?}"),
        }
    }
}
