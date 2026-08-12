// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — STEP 4a: the `Jᶜ`-MASKED noise-sum upper
//! bound (faithful O'Donnell §9.6 L2 chain, banked toward retiring the
//! `friedgut_boolean(+_helper)` admitted axioms).
//!
//! The OUTSIDE-`J`-masked variant of the landed rung-2 noise-sum bound
//! [`BoolAnalysis.kkl_summed_deriv_le_wnorm_sum`]: it sums the SAME per-coordinate
//! chain (level-restriction `lowband_le_noise_sum` + un-normalized spectral
//! identity `noise_spectral_unnorm_eq_pow4`) but over only the coordinates picked
//! out by the mask `m i := Bool.not (J i)` (`i ∉ J`), using the banked masked-sum
//! toolkit ([`masked_finSum_le`], [`masked_finSum_smul`]) instead of the bare
//! `Fin.sum_le` / `Fin.sum_smul`.
//!
//! ```text
//! BoolAnalysis.kkl_summed_deriv_le_wnorm_sum_masked :
//!   ∀ (n k : Nat) (f : BoolFn n) (J : HCPoint n),
//!     Rat.le
//!       (Fin.sum n (fun i => ind (Bool.not (J i)) · W^{≤k}[D_i (pm∘f)]))      -- Σ_{i∉J} W^{≤k}[D_i]
//!       (Rat.mul (Rat.powNat (Rat.ofNat 9) k)
//!                (Rat.mul (Rat.powNat 4 n)
//!                         (Fin.sum n (fun i => ind (Bool.not (J i)) · W_norm_i)))) -- 9^k·(4^n·Σ_{i∉J} W_norm_i)
//! ```
//!
//! with (`g_i := D_i (pm∘f) := fun x => pm(f x) − pm(f(hcFlip n x i))`)
//!   * `W^{≤k}[g_i] := subsetSum n (fun S => ind(ble |S| k)·(A_{g_i}·A_{g_i}))`,
//!     `A_g S := subsetSum n (fun x => g x·χ_S x)` (un-normalized coefficient);
//!   * `W_norm_i := (subsetSum n (fun y => (T_{1/3} g_i y)²))·inv(8^n)` (normalized
//!     two-norm, byte-identical to the masked dual-HC aggregate summand and R3a's
//!     RHS factor at `g := g_i`).
//!
//! The masked `Σ_i` integrand `fun i => ind(¬J i)·W^{≤k}[D_i (pm∘f)]` is BYTE-
//! IDENTICAL to STEP 3's `summed_deriv_lowband_eq_weighted_masked` LHS lambda at
//! `b := pm∘f`, so STEP 4 chains the two without any β/δ adjustment.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE the landed bricks
//!
//! Write `Q9 := 9^k`, `P4 := 4^n`, `L i := W^{≤k}[g_i]`,
//! `N i := ‖T_{1/3} g_i‖₂² = subsetSum n (fun S => levelWt(1/3) n S·(A_{g_i}·A_{g_i}))`,
//! `Wn i := W_norm_i`, `G i := Q9·(P4·(Wn i))`, `m i := ¬J i`.
//!
//! 1. `per_i : ∀ i, L i ≤ G i` — IDENTICAL to the unmasked rung's per-`i` bound:
//!    `lowband_le_noise_sum n k g_i : L i ≤ Q9·(N i)`,
//!    `noise_spectral_unnorm_eq_pow4 n g_i : N i = P4·(Wn i)`, and
//!    `Eq.subst (motive t => L i ≤ Q9·t) (that) (the bound)`.
//! 2. `h_mono : Σ_i ind(m i)·L i ≤ Σ_i ind(m i)·G i` —
//!    `masked_finSum_le n m L G per_i` (the banked UNCONDITIONAL masked
//!    monotonicity; `L i ≤ G i` holds for every `i`, no mask premise needed).
//! 3. `h_pull9 : Σ_i ind(m i)·(Q9·(P4·Wn i)) = Q9·Σ_i ind(m i)·(P4·Wn i)` —
//!    `masked_finSum_smul n m Q9 (fun i => P4·Wn i)`.  (`G ≡ fun i => Q9·(P4·Wn i)`
//!    by β, so `Σ_i ind(m i)·G i ≡ LHS` definitionally.)
//! 4. `h_pull4 : Σ_i ind(m i)·(P4·Wn i) = P4·Σ_i ind(m i)·Wn i` —
//!    `masked_finSum_smul n m P4 Wn`; `congr (Q9··) h_pull4`.
//! 5. `h_pull : Σ_i ind(m i)·G i = Q9·(P4·Σ_i ind(m i)·Wn i)` — `trans h_pull9 (that)`.
//! 6. `Eq.subst (motive t => Σ_i ind(m i)·L i ≤ t) h_pull h_mono`.
//!
//! Every leaf (`lowband_le_noise_sum`, `noise_spectral_unnorm_eq_pow4`,
//! `masked_finSum_le`, `masked_finSum_smul`, `congrArg`, `Eq.*`) is a landed
//! `Constructive` empty-closure Theorem, so this rung is too. NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural` / `native_decide` / `unsafe` /
//! `Real`. No axiom added/removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the masked rung-2 noise-sum bound. Carrier spellings
/// byte-match the consumed level-restriction (LR), R3a, masked-finSum, and STEP 3
/// carriers (`ind`, `Bool.not`, `hcFlip`, `pm`, `chi`, `noiseOp`, `levelWt`,
/// `setSizeNat`, `Nat.ble`, `Fin.sum`, `powNat`).
struct MaskedNoiseConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_of_nat: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_inv: Expr,
    pow_nat: Expr,
    fin: Expr,
    fin_sum: Expr,
    hcpoint: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    bool_: Expr,
    bool_not: Expr,
    bool_fn: Expr,
    pm: Expr,
    chi: Expr,
    hc_flip: Expr,
    noise_op: Expr,
    subset_sum: Expr,
    level_wt: Expr,
    set_size_nat: Expr,
    nat_ble: Expr,
    ind: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    masked_finsum_le: Expr,
    masked_finsum_smul: Expr,
    l1: Level,
}

impl MaskedNoiseConsts {
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
            rat_of_nat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            rat_inv: k("Rat.inv"),
            pow_nat: k("Rat.powNat"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            #[cfg(test)]
            bool_: k("Bool"),
            bool_not: k("Bool.not"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            pm: k("BoolAnalysis.pm"),
            chi: k("BoolAnalysis.chi"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            noise_op: k("BoolAnalysis.noiseOp"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            level_wt: k("BoolAnalysis.levelWt"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            nat_ble: k("Nat.ble"),
            ind: k("BoolAnalysis.ind"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            masked_finsum_le: k("BoolAnalysis.masked_finSum_le"),
            masked_finsum_smul: k("BoolAnalysis.masked_finSum_smul"),
            l1,
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    /// `Rat.mk (Int.ofNat v) 1`.
    fn rat_lit(&self, v: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(v)),
                self.one_nat(),
            ],
        )
    }
    /// `Rat.mk (Int.ofNat 1) 3` — the noise rate `1/3`.
    fn third(&self) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.one_nat()),
                self.nat_lit(3),
            ],
        )
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    /// `powNat (mk(ofNat v) 1) n` — `v^n`.
    fn pow_lit(&self, v: u64, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.rat_lit(v), n.clone()])
    }
    /// `9^k := powNat (Rat.ofNat 9) k` — BYTE-match LR's `9^k` (`Rat.ofNat` base!).
    fn pow9(&self, k: &Expr) -> Expr {
        Expr::apps(
            self.pow_nat.clone(),
            [
                Expr::app(self.rat_of_nat.clone(), self.nat_lit(9)),
                k.clone(),
            ],
        )
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fsum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), a)
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn level_wt_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.level_wt.clone(), [self.third(), n.clone(), s.clone()])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    /// `D_i (pm∘f) := fun x => Rat.sub (pm(f x)) (pm(f(hcFlip n x i)))` — BYTE-match
    /// rung2-noise's `deriv` and the masked dual-HC aggregate's `deriv_lam`.
    fn deriv(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        let flip = Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()]);
        let fflip = Expr::app(self.pm.clone(), Expr::app(f.clone(), flip));
        let body = Expr::apps(self.rat_sub.clone(), [fx, fflip]);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `A_g S := subsetSum n (fun x => g x · chi n S x)`.
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), x.clone()), self.chi_(n, s, &x));
        let lam = d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, lam)
    }
    /// `T_{1/3} g := noiseOp (1/3) n g` (partial).
    fn op(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(self.noise_op.clone(), [self.third(), n.clone(), g.clone()])
    }
    /// `W^{≤k}[g] := subsetSum n (fun S => ind(ble |S| k)·(A_g·A_g))`.
    fn low_band(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, g: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let a = self.a_coeff(&d, n, g, &s);
        let bit = self.ble(self.set_size_nat_of(n, &s), k.clone());
        let body = self.mul(self.ind_of(bit), self.mul(a.clone(), a));
        let lam = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        self.ssum(n, lam)
    }
    /// `N[g] := subsetSum n (fun S => levelWt(1/3) n S·(A_g·A_g))` — spectral two-norm.
    fn noise_norm(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let a = self.a_coeff(&d, n, g, &s);
        let body = self.mul(self.level_wt_of(n, &s), self.mul(a.clone(), a));
        let lam = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        self.ssum(n, lam)
    }
    /// `W_norm[g] := (subsetSum n (fun y => (T_{1/3} g y)²))·inv(8^n)`.
    fn w_norm(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let tg = self.op(n, g);
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let tgy = Expr::app(tg.clone(), y.clone());
        let body = self.mul(tgy.clone(), tgy);
        let lam = d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp, body));
        let w = self.ssum(n, lam);
        self.mul(w, self.inv(self.pow_lit(8, n)))
    }

    // ── Eq / le plumbing ──────────────────────────────────────────────────────
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
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
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
}

/// `m := fun (i : Fin n) => Bool.not (J i)` — the OUTSIDE-`J` Bool mask.
fn mask_fn(c: &MaskedNoiseConsts, parent: &EnvDeclBuilder, n: &Expr, j: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.bnot(Expr::app(j.clone(), i.clone()));
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `mL := fun (i : Fin n) => ind(¬J i) · W^{≤k}[D_i (pm∘f)]` — the masked `Σ_i`
/// integrand. BYTE-IDENTICAL to STEP 3's `lhs_i_fn` at `b := pm∘f`.
fn masked_l_fn(
    c: &MaskedNoiseConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let g = c.deriv(&b, n, f, &i);
    let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
    let body = c.mul(mask, c.low_band(&b, n, k, &g));
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `L := fun (i : Fin n) => W^{≤k}[D_i (pm∘f)]` — the UN-masked integrand (the
/// `masked_finSum_le` `g`-argument).
fn l_fn(c: &MaskedNoiseConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let g = c.deriv(&b, n, f, &i);
    let body = c.low_band(&b, n, k, &g);
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `Wn := fun (i : Fin n) => W_norm[D_i (pm∘f)]`.
fn wn_fn(c: &MaskedNoiseConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let g = c.deriv(&b, n, f, &i);
    let body = c.w_norm(&b, n, &g);
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `masked Wn := fun (i : Fin n) => ind(¬J i) · W_norm[D_i (pm∘f)]` — the masked
/// RHS integrand.
fn masked_wn_fn(
    c: &MaskedNoiseConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let g = c.deriv(&b, n, f, &i);
    let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
    let body = c.mul(mask, c.w_norm(&b, n, &g));
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `P4Wn := fun (i : Fin n) => 4^n · W_norm[D_i (pm∘f)]`.
fn p4wn_fn(c: &MaskedNoiseConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let g = c.deriv(&b, n, f, &i);
    let body = c.mul(c.pow_lit(4, n), c.w_norm(&b, n, &g));
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `G := fun (i : Fin n) => 9^k · (4^n · W_norm[D_i (pm∘f)])`.
fn g_fn(c: &MaskedNoiseConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let g = c.deriv(&b, n, f, &i);
    let body = c.mul(c.pow9(k), c.mul(c.pow_lit(4, n), c.w_norm(&b, n, &g)));
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

fn masked_noise_type(c: &MaskedNoiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let lhs = c.fsum(&n, masked_l_fn(c, &b, &n, &k, &f, &j));
    let mwn_sum = c.fsum(&n, masked_wn_fn(c, &b, &n, &f, &j));
    let rhs = c.mul(c.pow9(&k), c.mul(c.pow_lit(4, &n), mwn_sum));
    let concl = c.le(lhs, rhs);

    let e = b.mk_pi(j_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn masked_noise_value(c: &MaskedNoiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let m = mask_fn(c, &b, &n, &j);
    let l = l_fn(c, &b, &n, &k, &f);
    let g = g_fn(c, &b, &n, &k, &f);
    let wn = wn_fn(c, &b, &n, &f);
    let p4wn = p4wn_fn(c, &b, &n, &f);

    let q9 = c.pow9(&k);
    let p4 = c.pow_lit(4, &n);

    // The masked sums (= the theorem's LHS / RHS subterms).
    let masked_l_sum = c.fsum(&n, masked_l_fn(c, &b, &n, &k, &f, &j));
    // Σ_i ind(m i)·G i  (≡ masked_finSum_le's RHS sum; G≡fun i => q9·(p4·Wn i) by β).
    let masked_g_sum = {
        // build fun i => ind(m i)·G i directly to anchor types in the chain.
        let mut ib = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ib.fresh_local(fin_n.clone());
        let gi = c.deriv(&ib, &n, &f, &i);
        let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
        let body = c.mul(
            mask,
            c.mul(q9.clone(), c.mul(p4.clone(), c.w_norm(&ib, &n, &gi))),
        );
        let fn_ = ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        c.fsum(&n, fn_)
    };
    // Σ_i ind(m i)·(p4·Wn i).
    let masked_p4wn_sum = {
        let mut ib = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ib.fresh_local(fin_n.clone());
        let gi = c.deriv(&ib, &n, &f, &i);
        let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
        let body = c.mul(mask, c.mul(p4.clone(), c.w_norm(&ib, &n, &gi)));
        let fn_ = ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        c.fsum(&n, fn_)
    };
    let masked_wn_sum = c.fsum(&n, masked_wn_fn(c, &b, &n, &f, &j));
    let q9_masked_p4wn_sum = c.mul(q9.clone(), masked_p4wn_sum.clone()); // q9·Σ ind·(p4·Wn)
    let p4_masked_wn_sum = c.mul(p4.clone(), masked_wn_sum.clone()); // p4·Σ ind·Wn
    let q9_p4_masked_wn_sum = c.mul(q9.clone(), p4_masked_wn_sum.clone()); // RHS

    // (1) per_i : ∀ i, L i ≤ G i  (IDENTICAL to the unmasked rung's per-i).
    let per_i = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let gi = c.deriv(&d, &n, &f, &i); // g_i = D_i (pm∘f)
        let li = c.low_band(&d, &n, &k, &gi); // W^{≤k}[g_i]
        let ni = c.noise_norm(&d, &n, &gi); // ‖T g_i‖₂²
        let wni = c.w_norm(&d, &n, &gi); // W_norm_i
        let p4_wni = c.mul(p4.clone(), wni.clone()); // 4^n·W_norm_i

        let h_lr = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.lowband_le_noise_sum"),
                vec![],
            ),
            [n.clone(), k.clone(), gi.clone()],
        );
        let h_r3a = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.noise_spectral_unnorm_eq_pow4"),
                vec![],
            ),
            [n.clone(), gi.clone()],
        );
        let motive = {
            let mut mm = EnvDeclBuilder::child_of(&d);
            let (t_id, t) = mm.fresh_local(c.rat.clone());
            let body = c.le(li.clone(), c.mul(q9.clone(), t));
            mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let body = c.subst(motive, ni.clone(), p4_wni.clone(), h_r3a, h_lr);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    // (2) h_mono : Σ_i ind(m i)·L i ≤ Σ_i ind(m i)·G i
    //   := masked_finSum_le n m L G per_i.
    let h_mono = Expr::apps(
        c.masked_finsum_le.clone(),
        [n.clone(), m.clone(), l.clone(), g.clone(), per_i],
    );

    // (3) h_pull9 : Σ_i ind(m i)·(q9·(p4·Wn i)) = q9·Σ_i ind(m i)·(p4·Wn i)
    //   := masked_finSum_smul n m q9 P4Wn.
    let h_pull9 = Expr::apps(
        c.masked_finsum_smul.clone(),
        [n.clone(), m.clone(), q9.clone(), p4wn.clone()],
    );

    // (4) h_pull4 : Σ_i ind(m i)·(p4·Wn i) = p4·Σ_i ind(m i)·Wn i
    //   := masked_finSum_smul n m p4 Wn.
    let h_pull4 = Expr::apps(
        c.masked_finsum_smul.clone(),
        [n.clone(), m.clone(), p4.clone(), wn.clone()],
    );
    // congr (q9··) h_pull4 : q9·Σ ind·(p4·Wn) = q9·(p4·Σ ind·Wn).
    let h_pull4_scaled = c.congr_l(
        &b,
        &q9,
        masked_p4wn_sum.clone(),
        p4_masked_wn_sum.clone(),
        h_pull4,
    );

    // (5) h_pull : Σ_i ind(m i)·G i = q9·(p4·Σ_i ind(m i)·Wn i)  trans h_pull9 h_pull4_scaled.
    let h_pull = c.trans(
        masked_g_sum.clone(),
        q9_masked_p4wn_sum.clone(),
        q9_p4_masked_wn_sum.clone(),
        h_pull9,
        h_pull4_scaled,
    );

    // (6) Eq.subst (motive t => Σ_i ind(m i)·L i ≤ t) along h_pull onto h_mono.
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.le(masked_l_sum.clone(), t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let proof = c.subst(motive, masked_g_sum, q9_p4_masked_wn_sum, h_pull, h_mono);

    let e = b.mk_lam(j_id, BinderInfo::Default, hcp, proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.kkl_summed_deriv_le_wnorm_sum_masked` (STEP 4a) —
    /// the `Jᶜ`-masked rung-2 noise-sum bound
    /// `Σ_{i∉J} W^{≤k}[D_i(pm∘f)] ≤ 9^k·(4^n·Σ_{i∉J} W_norm_i)`. See module docs.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent;
    /// no axiom added/removed.
    pub fn init_boolean_analysis_friedgut_masked_noise(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_summed_deriv_le_wnorm_sum_masked");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, chi, hcFlip, noiseOp, levelWt, ind, setSizeNat, Bool.not
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_lowband_le_noise_sum()?;
        self.register_noise_spectral_unnorm_eq_pow4()?; // R3a
        self.init_boolean_analysis_friedgut_masked_finsum()?; // masked_finSum_le, masked_finSum_smul

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MaskedNoiseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: masked_noise_type(&c),
            value: masked_noise_value(&c),
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
    fn test_kkl_summed_deriv_le_wnorm_sum_masked_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_masked_noise()
            .expect("init_boolean_analysis_friedgut_masked_noise");
        let nm = Name::from_string("BoolAnalysis.kkl_summed_deriv_le_wnorm_sum_masked");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("masked rung-2 noise-sum proof must check: {e:?}"));
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
    fn test_masked_noise_idempotent() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_masked_noise()
            .expect("first");
        env.init_boolean_analysis_friedgut_masked_noise()
            .expect("idempotent");
    }
}
