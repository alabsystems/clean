// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by `boolean_analysis_noise_fn_succ.rs` — shared constants and
// smart-constructors for the `noiseFn_succ_{low,high}` operator-peel identities.

/// Shared kernel constants + smart-constructors for `noiseFn_succ`.
pub(super) struct NoiseFnSuccConsts {
    l1: Level,
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_add: Expr,
    two: Expr,
    fin: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_mul_one: Expr,
    rat_mul_neg: Expr,
    rat_neg_const: Expr,
    pm: Expr,
    bool_false: Expr,
    bool_true: Expr,
    fin_sum: Expr,
    fin_sum_add: Expr,
    fin_sum_smul: Expr,
    fin_sum_congr: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    noise_density: Expr,
    noise_fn: Expr,
    g_part: Expr,
    lift_h: Expr,
    extend_f: Expr,
    extend_t: Expr,
    cast_add: Expr,
    add_nat: Expr,
    keystone: Expr,
    pow_two_succ: Expr,
    eq_symm_nat: Expr,
    eq_ndrec_fin: Expr,
}

impl NoiseFnSuccConsts {
    pub(super) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        Self {
            l1: l1.clone(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            nat_succ,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            two,
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
            rat_mul_neg: Expr::const_(Name::from_string("Rat.mul_neg"), vec![]),
            rat_neg_const: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_add: Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            fin_sum_smul: Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            noise_fn: Expr::const_(Name::from_string("BoolAnalysis.noiseFn"), vec![]),
            g_part: Expr::const_(Name::from_string("BoolAnalysis.gPart"), vec![]),
            lift_h: Expr::const_(Name::from_string("BoolAnalysis.liftH"), vec![]),
            extend_f: Expr::const_(Name::from_string("BoolAnalysis.extendF"), vec![]),
            extend_t: Expr::const_(Name::from_string("BoolAnalysis.extendT"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            keystone: Expr::const_(
                Name::from_string("BoolAnalysis.peel_pointwise_keystone"),
                vec![],
            ),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_symm_nat: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1]),
        }
    }

    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn one(&self) -> Expr {
        self.rat_one.clone()
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint (n+1) → Rat` — the type of the input function `F`.
    fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.hcpoint_of(&self.succ(n)),
            self.rat(),
        )
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn pm_of(&self, b: &Expr) -> Expr {
        Expr::app(self.pm.clone(), b.clone())
    }
    /// `Fin.sum n f`.
    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), f])
    }
    /// `hcDecode m p`.
    fn decode(&self, m: &Expr, p: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [m.clone(), p.clone()])
    }
    /// `noiseDensityW ρ m x p`.
    fn density(&self, rho: &Expr, m: &Expr, x: &Expr, p: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), m.clone(), x.clone(), p.clone()],
        )
    }
    /// `noiseFn ρ m F jx`.
    fn noise_fn(&self, rho: &Expr, m: &Expr, f: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [rho.clone(), m.clone(), f.clone(), jx.clone()],
        )
    }
    /// `gPart n F`.
    fn g_part_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.g_part.clone(), [n.clone(), f.clone()])
    }
    /// `liftH n F`.
    fn lift_h_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.lift_h.clone(), [n.clone(), f.clone()])
    }
    /// `extend_b m p` for the chosen top bit.
    fn extend(&self, use_true: bool, m: &Expr, p: &Expr) -> Expr {
        let cst = if use_true {
            &self.extend_t
        } else {
            &self.extend_f
        };
        Expr::apps(cst.clone(), [m.clone(), p.clone()])
    }
    /// The appended bit (`Bool.false` / `Bool.true`).
    fn bit(&self, use_true: bool) -> &Expr {
        if use_true {
            &self.bool_true
        } else {
            &self.bool_false
        }
    }
    /// `@Eq Rat l r`.
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat(), l, r],
        )
    }
    /// `@Eq.trans Rat a b c h1 h2`.
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat(), a, b, cc, h1, h2],
        )
    }
    /// `@Eq.symm Rat a b h`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat(), a, b, h],
        )
    }
    /// `@congrArg α Rat from to f h` for a unary `f : α → Rat`.
    fn congr_to_rat(&self, alpha: Expr, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [alpha, self.rat(), from, to, f, h],
        )
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `Rat.mul_neg a b : a·(−b) = −(a·b)`.
    fn mul_neg(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_neg.clone(), [a, b])
    }
    /// `peel_pointwise_keystone p q d ρ`.
    fn keystone(&self, p: &Expr, q: &Expr, d: &Expr, rho: &Expr) -> Expr {
        Expr::apps(
            self.keystone.clone(),
            [p.clone(), q.clone(), d.clone(), rho.clone()],
        )
    }
    /// `Fin.sum_add n f g : Σ (f+g) = Σf + Σg`.
    fn sum_add(&self, n: &Expr, f: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum_add.clone(), [n.clone(), f, g])
    }
    /// `Fin.sum_smul n c f : Σ (c·f) = c·Σf`.
    fn sum_smul(&self, n: &Expr, cc: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum_smul.clone(), [n.clone(), cc, f])
    }
    /// `Fin.sum_congr n f g h : Σf = Σg`  (`h : ∀ i, f i = g i`).
    fn sum_congr(&self, n: &Expr, f: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_congr.clone(), [n.clone(), f, g, h])
    }

    /// `castP n M := @Eq.ndrec Nat (2^n+2^n) (fun m => Fin m) M (2^(n+1))
    ///                 (Eq.symm (Nat.pow_two_succ n))` — the split transport,
    /// byte-for-byte the `hcSumSplit` / bridge form.
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, mapped: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let sum_pow = self.nadd(p2n.clone(), p2n);
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm_nat.clone(),
            [self.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.nat.clone(), sum_pow, motive, mapped.clone(), p2sn, e],
        )
    }

    /// The split index `castP (idx_map k)` for the given half.
    fn split_index(&self, parent: &EnvDeclBuilder, half: Half, n: &Expr, k: &Expr) -> Expr {
        let idx_map = match half {
            Half::Low => &self.cast_add,
            Half::High => &self.add_nat,
        };
        let p2n = self.pow2(n);
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n, k.clone()]);
        self.cast_p(parent, n, &mapped)
    }
}
