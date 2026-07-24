// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **RUNG 2** (`rung2`): the assembled low-band ≤ noise-sum bound.
//!
//! Chains the two halves of rung 2 — the combinatorial core
//! [`BoolAnalysis.kkl_pow4_mass_le_summed_deriv`]
//! (`(4·4^n)·M_{1..k} ≤ Σ_i W^{≤k}[D_i]`) and the noise-sum bound
//! [`BoolAnalysis.kkl_summed_deriv_le_wnorm_sum`]
//! (`Σ_i W^{≤k}[D_i] ≤ 9^k·(4^n·Σ_i W_norm_i)`) — through `Rat.le_trans`, then
//! cancels the strictly-positive measure power `4^n` to land the crisp
//!
//! ```text
//! BoolAnalysis.kkl_lowband_le_wnorm_sum :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     Rat.le
//!       (Rat.mul 4 (subsetSum n (fun S =>
//!           ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                         (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!             · (f̂ S · f̂ S))))                                          -- 4·M_{1..k}
//!       (Rat.mul (Rat.powNat (Rat.ofNat 9) k)
//!                (Fin.sum n (fun i => W_norm_i)))                        -- 9^k·Σ_i W_norm_i
//! ```
//!
//! i.e. **`4·M_{1..k} ≤ 9^k·Σ_i W_norm_i`**, where `M_{1..k}` is the non-empty
//! low-degree Fourier mass of `f̂` and `W_norm_i := ‖T_{1/3} D_i (pm∘f)‖₂²` (the
//! normalized two-norm summand of the `dualhc` aggregate).
//!
//! This is **rung 2** of the KKL finish: the genuinely-`f̂` low-band Fourier mass,
//! bounded by the normalized two-norms of the coordinate derivatives. The
//! remaining step (rung 3) feeds the small-influence hypercontractive aggregate
//! `Σ_i W_norm_i ≤ 4·√ε·I[f]` (NNReal) — the genuinely-analytic content — to close
//! the conditional sharp KKL `I[f] ≥ c·k·Var`.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! Write `P4 := 4^n`, `M := M_{1..k}`, `W := Σ_i W_norm_i`, `Q9 := 9^k`,
//! `Σdv := Σ_i W^{≤k}[D_i]`.
//!
//! 1. `hA : (4·P4)·M ≤ Σdv`      — `kkl_pow4_mass_le_summed_deriv n k f`.
//! 2. `hB : Σdv ≤ Q9·(P4·W)`     — `kkl_summed_deriv_le_wnorm_sum n k f`.
//! 3. `hAB : (4·P4)·M ≤ Q9·(P4·W)` — `Rat.le_trans _ _ _ hA hB`.
//! 4. `eL : (4·P4)·M = P4·(4·M)`  — assoc/comm reshape (pure `Rat`).
//! 5. `eR : Q9·(P4·W) = P4·(Q9·W)` — assoc/comm reshape (pure `Rat`).
//! 6. transport (3) along `eL`,`eR`: `P4·(4·M) ≤ P4·(Q9·W)` (two `Eq.subst`s).
//! 7. `Rat.le_of_mul_le_mul_left_pos (4·M) (Q9·W) P4 (0<P4) (that) : 4·M ≤ Q9·W`,
//!    with `0 < P4 := Rat.powNat_pos 4 n (0<4)`.
//!
//! Every leaf (`kkl_pow4_mass_le_summed_deriv`, `kkl_summed_deriv_le_wnorm_sum`,
//! `Rat.le_trans`, `Rat.le_of_mul_le_mul_left_pos`, `Rat.powNat_pos`,
//! `Rat.mul_assoc`, `Rat.mul_comm`, `Eq.*`) is `Constructive` with empty
//! admitted-axiom closure, so rung 2 is too. No axiom added/removed. Idempotent.
//! Gated behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the rung-2 assembly. Carrier spellings byte-match the two
/// half-rung carriers (`rung2_core`'s `M`, `4·4^n`; `rung2_noise`'s `9^k`, `4^n`,
/// `W_norm`).
struct Rung2Consts {
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
    bool_fn: Expr,
    pm: Expr,
    chi: Expr,
    hc_flip: Expr,
    noise_op: Expr,
    subset_sum: Expr,
    fourier: Expr,
    set_size_nat: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    ind: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    l1: Level,
}

impl Rung2Consts {
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
            bool_fn: k("BoolAnalysis.BoolFn"),
            pm: k("BoolAnalysis.pm"),
            chi: k("BoolAnalysis.chi"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            noise_op: k("BoolAnalysis.noiseOp"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            ind: k("BoolAnalysis.ind"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
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
    fn rat_lit(&self, v: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(v)),
                self.one_nat(),
            ],
        )
    }
    fn four(&self) -> Expr {
        self.rat_lit(4)
    }
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
    fn pow_lit(&self, v: u64, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.rat_lit(v), n.clone()])
    }
    fn pow4(&self, n: &Expr) -> Expr {
        self.pow_lit(4, n)
    }
    /// `9^k := powNat (Rat.ofNat 9) k`.
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
        self.ble(self.one_nat(), m)
    }
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
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
    /// `M_{1..k} := subsetSum n (fun S => ind(band)·(f̂·f̂))`.
    fn m_mass(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let body = self.mul(self.ind_of(self.band_bit(n, k, &s)), self.x_sq(n, f, &s));
        let g = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }
    /// `D_i (pm∘f)` lambda (byte-match `rung2_noise` deriv / aggregate deriv_lam).
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
    /// `T_{1/3} g := noiseOp (1/3) n g`.
    fn op(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(self.noise_op.clone(), [self.third(), n.clone(), g.clone()])
    }
    /// `W_norm[g] := (subsetSum n (fun y => (T g y)²))·inv(8^n)`.
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
    /// `Wn := fun (i : Fin n) => W_norm[D_i (pm∘f)]`.
    fn wn_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let g = self.deriv(&b, n, f, &i);
        let body = self.w_norm(&b, n, &g);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    // ── Eq / le / ring plumbing ───────────────────────────────────────────────
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
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
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
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
    /// `0 < 4` := `@Int.NonNeg.mk 3` (the `Rat.lt 0 (mk(ofNat 4)1)` reduces idiom).
    fn four_pos(&self) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_lit(3),
        )
    }
}

fn rung2_type(c: &Rung2Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());

    let four_m = c.mul(c.four(), c.m_mass(&b, &n, &k, &f));
    let wn_sum = c.fsum(&n, c.wn_fn(&b, &n, &f));
    let q9_wn = c.mul(c.pow9(&k), wn_sum);
    let concl = c.le(four_m, q9_wn);

    let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `Σdv := Σ_i W^{≤k}[D_i (pm∘f)]` — the shared middle term of the two halves
/// (byte-identical to both `rung2_core`'s RHS and `rung2_noise`'s LHS).
fn sigma_deriv(c: &Rung2Consts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
    let mut ib = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = ib.fresh_local(fin_n.clone());
    let g = c.deriv(&ib, n, f, &i);
    let inner = {
        let mut sb = EnvDeclBuilder::child_of(&ib);
        let hcp = c.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let acoeff = {
            let mut yb = EnvDeclBuilder::child_of(&sb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let chi = Expr::apps(c.chi.clone(), [n.clone(), s.clone(), y.clone()]);
            let body = c.mul(Expr::app(g.clone(), y.clone()), chi);
            let lam = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            c.ssum(n, lam)
        };
        let bit = c.ble(c.set_size_nat_of(n, &s), k.clone());
        let body = c.mul(c.ind_of(bit), c.mul(acoeff.clone(), acoeff));
        let lam = sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body));
        c.ssum(n, lam)
    };
    let lam = ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n, inner));
    c.fsum(n, lam)
}

fn rung2_value(c: &Rung2Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());

    let m = c.m_mass(&b, &n, &k, &f);
    let wn_sum = c.fsum(&n, c.wn_fn(&b, &n, &f));
    let sigma = sigma_deriv(c, &b, &n, &k, &f);

    let p4 = c.pow4(&n);
    let q9 = c.pow9(&k);
    let four = c.four();
    let four_p4 = c.mul(four.clone(), p4.clone()); // 4·4^n
    let four_m = c.mul(four.clone(), m.clone()); // 4·M
    let q9_wn = c.mul(q9.clone(), wn_sum.clone()); // 9^k·ΣWn
    let p4_wn = c.mul(p4.clone(), wn_sum.clone()); // 4^n·ΣWn
    let lhs0 = c.mul(four_p4.clone(), m.clone()); // (4·4^n)·M
    let rhs0 = c.mul(q9.clone(), p4_wn.clone()); // 9^k·(4^n·ΣWn)
    let lhs1 = c.mul(p4.clone(), four_m.clone()); // 4^n·(4·M)
    let rhs1 = c.mul(p4.clone(), q9_wn.clone()); // 4^n·(9^k·ΣWn)

    // hA : (4·4^n)·M ≤ Σdv.
    let h_a = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.kkl_pow4_mass_le_summed_deriv"),
            vec![],
        ),
        [n.clone(), k.clone(), f.clone()],
    );
    // hB : Σdv ≤ 9^k·(4^n·ΣWn).
    let h_b = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.kkl_summed_deriv_le_wnorm_sum"),
            vec![],
        ),
        [n.clone(), k.clone(), f.clone()],
    );
    // hAB : (4·4^n)·M ≤ 9^k·(4^n·ΣWn)   Rat.le_trans lhs0 Σdv rhs0 hA hB.
    let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
    let h_ab = Expr::apps(
        le_trans,
        [lhs0.clone(), sigma.clone(), rhs0.clone(), h_a, h_b],
    );

    // eL : (4·4^n)·M = 4^n·(4·M).
    //   (4·4^n)·M = (4^n·4)·M   congr_r M (mul_comm 4 4^n)
    //            = 4^n·(4·M)    mul_assoc 4^n 4 M
    let p4_four = c.mul(p4.clone(), four.clone()); // 4^n·4
    let p4_four_m = c.mul(p4_four.clone(), m.clone()); // (4^n·4)·M
    let e_l1 = c.congr_r(
        &b,
        &m,
        four_p4.clone(),
        p4_four.clone(),
        c.comm(four.clone(), p4.clone()),
    );
    let e_l2 = c.assoc(p4.clone(), four.clone(), m.clone());
    let e_l = c.trans(lhs0.clone(), p4_four_m.clone(), lhs1.clone(), e_l1, e_l2);

    // eR : 9^k·(4^n·ΣWn) = 4^n·(9^k·ΣWn).
    //   9^k·(4^n·ΣWn) = (9^k·4^n)·ΣWn   symm (mul_assoc 9^k 4^n ΣWn)
    //               = (4^n·9^k)·ΣWn   congr_r ΣWn (mul_comm 9^k 4^n)
    //               = 4^n·(9^k·ΣWn)   mul_assoc 4^n 9^k ΣWn
    let q9_p4 = c.mul(q9.clone(), p4.clone()); // 9^k·4^n
    let q9_p4_wn = c.mul(q9_p4.clone(), wn_sum.clone()); // (9^k·4^n)·ΣWn
    let p4_q9 = c.mul(p4.clone(), q9.clone()); // 4^n·9^k
    let p4_q9_wn = c.mul(p4_q9.clone(), wn_sum.clone()); // (4^n·9^k)·ΣWn
    let e_r1 = c.symm(
        q9_p4_wn.clone(),
        rhs0.clone(),
        c.assoc(q9.clone(), p4.clone(), wn_sum.clone()),
    );
    let e_r2 = c.congr_r(
        &b,
        &wn_sum,
        q9_p4.clone(),
        p4_q9.clone(),
        c.comm(q9.clone(), p4.clone()),
    );
    let e_r3 = c.assoc(p4.clone(), q9.clone(), wn_sum.clone());
    let e_r12 = c.trans(rhs0.clone(), q9_p4_wn.clone(), p4_q9_wn.clone(), e_r1, e_r2);
    let e_r = c.trans(rhs0.clone(), p4_q9_wn.clone(), rhs1.clone(), e_r12, e_r3);

    // transport hAB along eL (LHS) and eR (RHS) → P4·(4·M) ≤ P4·(9^k·ΣWn).
    //   step1 : 4^n·(4·M) ≤ 9^k·(4^n·ΣWn)   subst (motive t => t ≤ rhs0) eL hAB.
    let motive_l = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.le(t, rhs0.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step1 = c.subst(motive_l, lhs0.clone(), lhs1.clone(), e_l, h_ab);
    //   step2 : 4^n·(4·M) ≤ 4^n·(9^k·ΣWn)   subst (motive t => lhs1 ≤ t) eR step1.
    let motive_r = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.le(lhs1.clone(), t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step2 = c.subst(motive_r, rhs0.clone(), rhs1.clone(), e_r, step1);

    // cancel : Rat.le_of_mul_le_mul_left_pos (4·M) (9^k·ΣWn) 4^n (0<4^n) step2.
    //   ∀ a b c, 0 < c → c·a ≤ c·b → a ≤ b ; a:=4·M, b:=9^k·ΣWn, c:=4^n.
    let four_pos = c.four_pos();
    let p4_pos = Expr::apps(
        Expr::const_(Name::from_string("Rat.powNat_pos"), vec![]),
        [four.clone(), n.clone(), four_pos],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_of_mul_le_mul_left_pos"), vec![]),
        [four_m.clone(), q9_wn.clone(), p4.clone(), p4_pos, step2],
    );

    let _ = c.eq_rat(p4.clone(), p4); // keep eq_rat referenced (doc parity)
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, proof);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.kkl_lowband_le_wnorm_sum` — **RUNG 2** of the KKL
    /// finish: `4·M_{1..k} ≤ 9^k·Σ_i W_norm_i`. See module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn register_kkl_lowband_le_wnorm_sum(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_lowband_le_wnorm_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_mul_base()?; // Rat.powNat_pos
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_rat_le_of_mul_le_mul_left_pos()?;
        self.register_kkl_pow4_mass_le_summed_deriv()?;
        self.register_kkl_summed_deriv_le_wnorm_sum()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Rung2Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: rung2_type(&c),
            value: rung2_value(&c),
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
    fn test_kkl_lowband_le_wnorm_sum_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_lowband_le_wnorm_sum()
            .expect("register_kkl_lowband_le_wnorm_sum");
        let nm = Name::from_string("BoolAnalysis.kkl_lowband_le_wnorm_sum");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("rung-2 proof must check: {e:?}"));
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
    fn test_rung2_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_kkl_lowband_le_wnorm_sum().expect("first");
        env.register_kkl_lowband_le_wnorm_sum().expect("idempotent");
    }
}
