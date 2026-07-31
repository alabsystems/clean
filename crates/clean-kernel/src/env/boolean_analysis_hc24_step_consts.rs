// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Cached constants + smart-constructors for the `hc24_core_step` proof.
// `include!`d into `boolean_analysis_hc24_step.rs`.

/// Plumbing for the induction-step proof term.
struct StepConsts {
    o: Hc24Consts,
    l1: Level,
    cast_add: Expr,
    add_nat: Expr,
    g_part: Expr,
    lift_h: Expr,
}

impl StepConsts {
    fn new() -> Self {
        Self {
            o: Hc24Consts::new(),
            l1: Level::succ(Level::zero()),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            g_part: Expr::const_(Name::from_string("BoolAnalysis.gPart"), vec![]),
            lift_h: Expr::const_(Name::from_string("BoolAnalysis.liftH"), vec![]),
        }
    }

    // ── atoms ────────────────────────────────────────────────────────────────
    fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    fn nat(&self) -> Expr {
        self.o.nat.clone()
    }
    fn one(&self) -> Expr {
        self.o.rat_one.clone()
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.o.rat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.sub"), vec![]), [a, b])
    }
    fn two(&self) -> Expr {
        self.add(self.one(), self.one())
    }
    fn three(&self) -> Expr {
        self.add(self.two(), self.one())
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.le(a, b)
    }
    fn add_c(&self) -> Expr {
        self.o.rat_add.clone()
    }
    fn mul_c(&self) -> Expr {
        self.o.rat_mul.clone()
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            n.clone(),
        )
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        self.o.fin_of(n)
    }
    fn pow2(&self, n: &Expr) -> Expr {
        self.o.pow2(n)
    }
    fn pow8(&self, n: &Expr) -> Expr {
        self.o.pow8(n)
    }
    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        self.o.sum(n, f)
    }
    fn sq(&self, x: &Expr) -> Expr {
        self.o.sq(x)
    }
    fn pow4(&self, x: &Expr) -> Expr {
        self.o.pow4(x)
    }
    fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        self.o.decode(n, k)
    }
    fn f_type(&self, n: &Expr) -> Expr {
        self.o.f_type(n)
    }
    #[cfg(test)]
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        self.o.hcpoint_of(n)
    }
    #[cfg(test)]
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        self.o.eq_rat(l, r)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.o.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.o.trans(a, b, cc, h1, h2)
    }

    fn noise_fn(&self, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        self.o.noise_fn(rho, n, f, jx)
    }
    /// `gPart n F` (partially applied).
    fn g_part_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.g_part.clone(), [n.clone(), f.clone()])
    }
    /// `liftH n F` (partially applied).
    fn lift_h_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.lift_h.clone(), [n.clone(), f.clone()])
    }

    // ── lemma instances ──────────────────────────────────────────────────────
    /// `noiseFn_succ_low ρ n F k`.
    fn nf_succ_low(&self, rho: &Expr, n: &Expr, f: &Expr, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseFn_succ_low"), vec![]),
            [rho.clone(), n.clone(), f.clone(), k.clone()],
        )
    }
    /// `noiseFn_succ_high ρ n F k`.
    fn nf_succ_high(&self, rho: &Expr, n: &Expr, f: &Expr, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseFn_succ_high"), vec![]),
            [rho.clone(), n.clone(), f.clone(), k.clone()],
        )
    }
    /// `fourth_power_rho_two_point_bound A B ρ h`.
    fn two_point(&self, a: &Expr, b: &Expr, rho: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Rat.fourth_power_rho_two_point_bound"),
                vec![],
            ),
            [a.clone(), b.clone(), rho.clone(), h],
        )
    }
    /// `Rat.add_sq_regroup A B : (A+B)·(A+B) = (A·A + B·B) + (1+1)·(A·B)`.
    fn add_sq_regroup(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.add_sq_regroup"), vec![]),
            [a.clone(), b.clone()],
        )
    }
    /// `Fin.sum_cauchy_schwarz n a b : (Σ ab)² ≤ (Σ a²)·(Σ b²)`.
    fn cauchy_schwarz(&self, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_cauchy_schwarz"), vec![]),
            [n.clone(), a.clone(), b.clone()],
        )
    }
    /// `Rat.le_of_sq_le_sq a b ha hb hsq : a ≤ b`.
    fn le_of_sq_le_sq(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr, hsq: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_sq_le_sq"), vec![]),
            [a.clone(), b.clone(), ha, hb, hsq],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_a : a·b ≤ a·c`.
    fn mll(&self, a: &Expr, b: &Expr, cc: &Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [a.clone(), b.clone(), cc.clone(), h_bc, h_a],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c h_bc h_a : b·a ≤ c·a`.
    fn mlr(&self, a: &Expr, b: &Expr, cc: &Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
            [a.clone(), b.clone(), cc.clone(), h_bc, h_a],
        )
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
            a.clone(),
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a.clone(), b.clone(), ha, hb],
        )
    }
    /// `Fin.sum_nonneg n f h : 0 ≤ Σ f`.
    fn sum_nonneg(&self, n: &Expr, f: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]),
            [n.clone(), f.clone(), h],
        )
    }
    /// `Fin.sum_le n f g h : Σ f ≤ Σ g`  (`h : ∀ i, f i ≤ g i`).
    fn sum_le(&self, n: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_le"), vec![]),
            [n.clone(), f.clone(), g.clone(), h],
        )
    }
    /// `Fin.sum_add n f g : Σ(f+g) = Σf + Σg`.
    fn sum_add(&self, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            [n.clone(), f.clone(), g.clone()],
        )
    }
    /// `Fin.sum_smul n c f : Σ(c·f) = c·Σf`.
    fn sum_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    /// `Fin.sum_congr n f g h : Σf = Σg`.
    fn sum_congr(&self, n: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            [n.clone(), f.clone(), g.clone(), h],
        )
    }
    /// `finSumPow2SuccSplit n F`.
    fn pow2_split(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.finSumPow2SuccSplit"),
                vec![],
            ),
            [n.clone(), f.clone()],
        )
    }
    /// `hc24Assemble p sg sh : p·sg² + (2·(p·(sg·sh)) + p·sh²) = p·(sg+sh)²`.
    fn assemble(&self, p: &Expr, sg: &Expr, sh: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hc24Assemble"), vec![]),
            [p.clone(), sg.clone(), sh.clone()],
        )
    }
    /// `hc24S7 n F : SG + SH = (1+1)·SF'`.
    fn s7(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hc24S7"), vec![]),
            [n.clone(), f.clone()],
        )
    }
    /// `Rat.powNat_succ ρ k : powNat ρ (k+1) = ρ · powNat ρ k`.
    fn pow_nat_succ(&self, base: &Expr, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_succ"), vec![]),
            [base.clone(), k.clone()],
        )
    }
    /// `Rat.left_distrib a b c : a·(b+c) = a·b + a·c`.
    #[cfg(test)]
    fn ldist(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn massoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mcomm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a.clone(), b.clone()],
        )
    }
    /// `Rat.le_trans a b c h_ab h_bc : a ≤ c`.
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a.clone(), b.clone(), cc.clone(), h_ab, h_bc],
        )
    }
    /// `Rat.eight_rat` — the rational `8` constant (matches Hc24Consts.eight_rat).
    fn eight_rat(&self) -> Expr {
        self.o.eight_rat()
    }

    /// `@congrArg Rat Rat from to f h`.
    fn congr_arg(&self, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat(), self.rat(), from, to, f, h],
        )
    }

    /// `(x op fixed) = (y op fixed)` from `h : x = y`.
    fn cong_left(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        x: Expr,
        y: Expr,
        fixed: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = ch.fresh_local(self.rat());
            let body = Expr::apps(op.clone(), [w, fixed]);
            ch.finish_child(ch.mk_lam(w_id, BinderInfo::Default, self.rat(), body))
        };
        self.congr_arg(x, y, f, h)
    }
    /// `(fixed op x) = (fixed op y)` from `h : x = y`.
    fn cong_right(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        x: Expr,
        y: Expr,
        fixed: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = ch.fresh_local(self.rat());
            let body = Expr::apps(op.clone(), [fixed, w]);
            ch.finish_child(ch.mk_lam(w_id, BinderInfo::Default, self.rat(), body))
        };
        self.congr_arg(x, y, f, h)
    }

    /// `subst` with motive `fun x => x ≤ r` along `h_eq : from = to`, given
    /// `h : from ≤ r`, producing `to ≤ r`.
    fn subst_le_left(
        &self,
        parent: &EnvDeclBuilder,
        r: Expr,
        from: Expr,
        to: Expr,
        h_eq: Expr,
        h: Expr,
    ) -> Expr {
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat());
            let body = self.le(x, r.clone());
            ch.finish_child(ch.mk_lam(x_id, BinderInfo::Default, self.rat(), body))
        };
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat(), motive, from, to, h_eq, h],
        )
    }
    /// `subst` with motive `fun x => l ≤ x` along `h_eq : from = to`, given
    /// `h : l ≤ from`, producing `l ≤ to`.
    fn subst_le_right(
        &self,
        parent: &EnvDeclBuilder,
        l: Expr,
        from: Expr,
        to: Expr,
        h_eq: Expr,
        h: Expr,
    ) -> Expr {
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat());
            let body = self.le(l.clone(), x);
            ch.finish_child(ch.mk_lam(x_id, BinderInfo::Default, self.rat(), body))
        };
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat(), motive, from, to, h_eq, h],
        )
    }
}
