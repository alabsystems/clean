// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Shared atoms for the H1 connect (`boolean_analysis_kkl_dualhc_h1connect.rs`).
// Every `D` / `third` / `four` / `w` / `noiseOp` / `D_i (pm∘f)` / `coord_w_band`
// spelling is byte-for-byte the landed `H1bConsts` (band-form),
// `LowBandExtractConsts` (RUNG A), `BandReconcileConsts` (mask swap),
// `BandRegroupConsts` (regroup) and `RungBConsts` (`coord_w_band_fn`) conventions
// so the consumed theorem instances stay def-eq to their endpoints.

/// Shared atoms for the H1 connect.
struct H1ConnectConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    pm: Expr,
    ind: Expr,
    nat_ble: Expr,
    bool_not: Expr,
    hc_flip: Expr,
    noise_op: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    fourier_coeff: Expr,
    #[cfg(test)]
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl H1ConnectConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            nat_ble: k("Nat.ble"),
            bool_not: k("Bool.not"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            noise_op: k("BoolAnalysis.noiseOp"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fourier_coeff: k("BoolAnalysis.FourierCoefficient"),
            #[cfg(test)]
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── numerals / types ─────────────────────────────────────────────────────
    fn rat(&self) -> Expr {
        self.rat.clone()
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
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    fn rat_lit(&self, k: u32) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..k {
            nat = self.succ(nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), nat), self.one_nat()],
        )
    }
    /// `D := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1 ≡ 2^n`.
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
        self.rat_lit(4)
    }
    /// `eight := Rat.mk (Int.ofNat 8) 1` — the `powNat 8 n` base (byte-identical
    /// to `dualhc_pow8_eq_two_pow_cube`'s `8`).
    fn eight(&self) -> Expr {
        self.rat_lit(8)
    }
    /// `nine := Rat.mk (Int.ofNat 9) 1` — the `powNat 9 k` base (byte-identical to
    /// `nine_third_third_eq_one`'s `9`).
    fn nine(&self) -> Expr {
        self.rat_lit(9)
    }
    /// `two_rat := Rat.mk (Int.ofNat 2) 1` — the `powNat_two_eq_ofNat_pow` base.
    fn two_rat(&self) -> Expr {
        self.rat_lit(2)
    }
    fn one(&self) -> Expr {
        self.rat_one.clone()
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    #[cfg(test)]
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    // ── term builders ────────────────────────────────────────────────────────
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn pow(&self, base: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [base.clone(), k.clone()])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    #[cfg(test)]
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.order.rat_zero.clone(), a)
    }
    fn pm_(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn ind_(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn hc_flip_(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn op(&self, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(self.noise_op.clone(), [rho.clone(), n.clone(), g.clone()])
    }
    fn set_size_nat(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fcoeff(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            self.fourier_coeff.clone(),
            [n.clone(), f.clone(), s.clone()],
        )
    }
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fcoeff(n, f, s);
        self.mul(c.clone(), c)
    }
    #[cfg(test)]
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
    /// `Eq.subst.{1} Rat motive a b h_eq h_ma : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h_ma],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), a)
    }
    /// `Rat.powNat_nonneg b n h : 0 ≤ powNat b n`.
    fn pow_nonneg(&self, base: &Expr, n: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
            [base.clone(), n.clone(), h],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (b≤c) (0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [a, b, cc, h_bc, h_0a],
        )
    }
    /// `Rat.powNat_mul_base a b k : (a·b)^k = a^k · b^k`.
    fn pow_mul_base(&self, a: &Expr, b: &Expr, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_mul_base"), vec![]),
            [a.clone(), b.clone(), k.clone()],
        )
    }
    /// `Rat.le_of_ble_eq_true a b (Eq.refl Bool.true) : a ≤ b`.
    fn le_of_ble_refl(&self, a: Expr, b: Expr) -> Expr {
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let refl = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [bool_c, btrue],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            [a, b, refl],
        )
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
    fn pow_k_motive(&self, parent: &EnvDeclBuilder, k: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.pow(&z, k);
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

    /// `w S := (4·ind(S i))·(f̂·f̂)` — the band feedstock weight (byte-for-byte
    /// `H1bConsts::w_s`).
    fn w_s(&self, n: &Expr, f: &Expr, s: &Expr, i: &Expr) -> Expr {
        let si = Expr::app(s.clone(), i.clone());
        let c4 = self.mul(self.four(), self.ind_(si));
        self.mul(c4, self.fsq(n, f, s))
    }
    /// `w := fun S => (4·ind(S i))·(f̂·f̂)` as a `HCPoint n → Rat` (the RUNG A /
    /// mask-swap integrand argument).
    fn w_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let body = self.w_s(n, f, &s, i);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `feed := subsetSum n (fun S => (third·third)^{|S|}·w S)` — band-form RHS
    /// feedstock sum (byte-for-byte `H1bConsts::g_feed_fn` lifted).
    fn feed_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let p_base = self.mul(self.third(), self.third());
        let p_pow = self.pow(&p_base, &self.set_size_nat(n, &s));
        let body = self.mul(p_pow, self.w_s(n, f, &s, i));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `Mble := fun S => ind(ble |S| k)·w S` — RUNG A's low-band mask integrand
    /// (byte-for-byte `LowBandExtractConsts::mask_fn` at `w := w`).
    fn mble_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let bit = self.ble(self.set_size_nat(n, &s), k.clone());
        let body = self.mul(self.ind_(bit), self.w_s(n, f, &s, i));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `not-ble mask integrand := fun S => ind(not(ble (k+1) |S|))·w S` — the
    /// mask-swap RHS (byte-for-byte `BandReconcileConsts::not_ble_mask_fn` at
    /// `w := w`, AND `BandRegroupConsts::lhs_fn`).
    fn notble_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let bit = self.bnot(self.ble(self.succ(k.clone()), self.set_size_nat(n, &s)));
        let body = self.mul(self.ind_(bit), self.w_s(n, f, &s, i));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `coord_w_band := fun S => ind(S i)·(ind(not(ble (k+1)|S|))·(4·(f̂·f̂)))` —
    /// byte-for-byte `RungBConsts::coord_w_band_fn` / `BandRegroupConsts::rhs_fn`.
    fn coord_w_band_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        k: &Expr,
        f: &Expr,
        i: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let si = Expr::app(s.clone(), i.clone());
        let b2 = self.bnot(self.ble(self.succ(k.clone()), self.set_size_nat(n, &s)));
        let w_band = self.mul(self.ind_(b2), self.mul(self.four(), self.fsq(n, f, &s)));
        let body = self.mul(self.ind_(si), w_band);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `W_i := subsetSum n (fun y => Tg y · Tg y)`, `Tg := noiseOp third n (D_i
    /// (pm∘f))` — byte-for-byte `dualhc_W_eq_band_form`'s LHS.
    fn w_i(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let bf = self.pm_f(parent, n, f);
        let db = self.deriv(parent, n, &bf, i);
        let tg = self.op(&self.third(), n, &db);
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let tgy = Expr::app(tg.clone(), y.clone());
        let body = self.mul(tgy.clone(), tgy);
        let yfn = d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, yfn)
    }
}
