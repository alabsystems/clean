// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Shared atoms for the per-coordinate dual-HC home stretch
// (`boolean_analysis_kkl_dualhc_percoord.rs`). Every `D` / `third` / `four` /
// `half` / `m` / `W_i` / `coord_w_band` / `Influence` spelling is byte-for-byte
// the landed `FinalConsts` (`dualhc_final_le`), `NormInflConsts`
// (`dualhc_m_pow2_eq_4pow_influence`) and `H1ConnectConsts` (`dualhc_h1`)
// conventions so the consumed theorem instances stay def-eq to their endpoints.

/// Shared atoms for the per-coordinate home stretch.
struct PercoordConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_inv: Expr,
    rat_two: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    pm: Expr,
    ind: Expr,
    nat_ble: Expr,
    bool_not: Expr,
    bool_and: Expr,
    total_influence: Expr,
    hc_flip: Expr,
    noise_op: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    fin_sum: Expr,
    fourier_coeff: Expr,
    influence: Expr,
    is_rpow32: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl PercoordConsts {
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
            rat_inv: k("Rat.inv"),
            rat_two: k("Rat.two"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            nat_ble: k("Nat.ble"),
            bool_not: k("Bool.not"),
            bool_and: k("Bool.and"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            noise_op: k("BoolAnalysis.noiseOp"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fin_sum: k("Fin.sum"),
            fourier_coeff: k("BoolAnalysis.FourierCoefficient"),
            influence: k("BoolAnalysis.Influence"),
            is_rpow32: k("BoolAnalysis.IsRpow32"),
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
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `D := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1 ≡ 2^n` (the `ofNat(2^n)` cast,
    /// byte-identical to `NormInflConsts::denom`).
    fn dcap(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    /// `Rat.mk (Int.ofNat k) 1`.
    fn rat_lit(&self, k: u32) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(k)),
                self.one_nat(),
            ],
        )
    }
    /// `third := Rat.mk (Int.ofNat 1) 3` — byte-for-byte `FinalConsts::rho_third`.
    fn third(&self) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.one_nat()),
                self.three_nat(),
            ],
        )
    }
    /// `four := Rat.mk (Int.ofNat 4) 1`.
    fn four(&self) -> Expr {
        self.rat_lit(4)
    }
    /// `two_rat := Rat.mk (Int.ofNat 2) 1` (the `powNat_two_eq_ofNat_pow` base).
    fn two_rat(&self) -> Expr {
        self.rat_lit(2)
    }
    fn nine(&self) -> Expr {
        self.rat_lit(9)
    }
    /// `half := Rat.inv Rat.two` — byte-for-byte `FinalConsts::half`.
    fn half(&self) -> Expr {
        Expr::app(self.rat_inv.clone(), self.rat_two.clone())
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
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }

    // ── term builders ────────────────────────────────────────────────────────
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.order.sub(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.order.rat_zero.clone(), a)
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
    fn fin_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
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
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn band(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [a, b])
    }
    /// `M_{1..k}[f] := subsetSum n (fun S => ind (and (ble 1 |S|)
    /// (not (ble (k+1) |S|))) · (f̂·f̂))` — byte-for-byte `AssemblyConsts::m_lo`.
    fn m_lo(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let g = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let ss = self.set_size_nat(n, &s);
            let one_nat = self.one_nat();
            let bb = self.band(
                self.ble(one_nat, ss.clone()),
                self.bnot(self.ble(self.succ(k.clone()), ss)),
            );
            let body = self.mul(self.ind_(bb), self.fsq(n, f, &s));
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        self.ssum(n, g)
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a, b, ha, hb],
        )
    }
    fn is_rpow32_of(&self, x: &Expr, r: &Expr) -> Expr {
        Expr::apps(self.is_rpow32.clone(), [x.clone(), r.clone()])
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
    /// `Rat.powNat_nonneg b n h : 0 ≤ powNat b n`.
    fn pow_nonneg(&self, base: &Expr, n: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
            [base.clone(), n.clone(), h],
        )
    }
    /// `Rat.le_of_ble_eq_true a b (Eq.refl Bool.true) : a ≤ b` — closes a literal
    /// numeric `≤` like `0 ≤ 2` / `0 ≤ 9` by `decide`-style ι.
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

    // ── BIG terms: byte-identical to the consumed endpoints ───────────────────

    /// `pm∘f := fun x => pm (f x)`.
    fn pm_f(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.pm_(Expr::app(f.clone(), x.clone()));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `D_i b := fun x => b x − b (hcFlip n x i)` — byte-for-byte the H1-connect
    /// `deriv`.
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

    /// `deriv_lam := fun x => pm (f x) − pm (f (hcFlip n x i))` — byte-for-byte
    /// `FinalConsts::deriv_lam` (the `m`-of-`dualhc_final_le` carrier).
    fn deriv_lam(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.hc_flip_(n, &x, i));
        let body = self.sub(self.pm_(fx), self.pm_(fflip));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// `W_i := subsetSum n (fun y => Tg y · Tg y)`, `Tg := noiseOp third n (D_i
    /// (pm∘f))` — byte-for-byte `H1ConnectConsts::w_i` and `dualhc_final_le`'s
    /// `W`.
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

    /// `m := subsetSum n (fun x => (g x · g x)·(half·half))`, `g := deriv_lam`
    /// — byte-for-byte `dualhc_final_le`'s `m` (the `IsRpow32 (m·2^n) r` hyp
    /// carrier). NOTE: `dualhc_m_pow2_eq_4pow_influence`'s `m_i` is def-eq to this
    /// (its `deriv n f x i ≡ pm(f x) − pm(f(hcFlip n x i))` per-x is the β-reduct
    /// of `deriv_lam x`).
    fn m(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let g = self.deriv_lam(parent, n, f, i);
        let half = self.half();
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let gx = Expr::app(g.clone(), x.clone());
        let body = self.mul(
            self.mul(gx.clone(), gx),
            self.mul(half.clone(), half.clone()),
        );
        let xfn = d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, xfn)
    }

    /// `coord_w_band := fun S => ind(S i)·(ind(not(ble (k+1)|S|))·(4·(f̂·f̂)))` —
    /// byte-for-byte `H1ConnectConsts::coord_w_band_fn` / the assembly's
    /// `sum_w_band` summand.
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

    /// `Wb := subsetSum n (coord_w_band_fn n k f i)` — the per-coord band sum.
    fn wb(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr, i: &Expr) -> Expr {
        self.ssum(n, self.coord_w_band_fn(parent, n, k, f, i))
    }
}
