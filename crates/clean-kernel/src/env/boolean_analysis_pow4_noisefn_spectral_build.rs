// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_pow4_spectral.rs — the type + proof builders for
// the `pow4_noisefn_spectral` chain (Tier 1+ of the build plan
// `designs/2026-06-13-pow4-noisefn-spectral-build-plan.md`).
//
// Tier 1: `Rat.mul8_regroup` — the 8-factor regroup
//   ((w1·g1)·(w2·g2))·((w3·g3)·(w4·g4)) = ((w1·w2)·(w3·w4))·((g1·g2)·(g3·g4))
// a TOWER of `Rat.mul_mul_mul_comm` (2-fold mmmc), the 4-fold analogue of
// `regroup_per_s`'s single mmmc. Pure `Rat` algebra; CHECKED Constructive,
// empty admitted-axiom closure.

/// Atoms for the `Rat.mul8_regroup` algebra leaf (pure `Rat`).
struct Mul8Consts {
    rat: Expr,
    rat_mul: Expr,
    rat_mmmc: Expr,
    eq1: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl Mul8Consts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_mmmc: Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `congrArg Rat Rat from to g h : g from = g to`.
    fn congr(&self, from: Expr, to: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, g, h],
        )
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mmmc.clone(), [a, b, cc, d])
    }
    /// `fun (z : Rat) => z · right`.
    fn mul_right_motive(&self, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = b.fresh_local(self.rat.clone());
        let body = self.mul(z, right.clone());
        b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `fun (z : Rat) => left · z`.
    fn mul_left_motive(&self, parent: &EnvDeclBuilder, left: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = b.fresh_local(self.rat.clone());
        let body = self.mul(left.clone(), z);
        b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

fn build_mul8_regroup_type(c: &Mul8Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w1_id, w1) = b.fresh_local(c.rat.clone());
    let (w2_id, w2) = b.fresh_local(c.rat.clone());
    let (w3_id, w3) = b.fresh_local(c.rat.clone());
    let (w4_id, w4) = b.fresh_local(c.rat.clone());
    let (g1_id, g1) = b.fresh_local(c.rat.clone());
    let (g2_id, g2) = b.fresh_local(c.rat.clone());
    let (g3_id, g3) = b.fresh_local(c.rat.clone());
    let (g4_id, g4) = b.fresh_local(c.rat.clone());

    // LHS: ((w1·g1)·(w2·g2)) · ((w3·g3)·(w4·g4)).
    let lblk = c.mul(c.mul(w1.clone(), g1.clone()), c.mul(w2.clone(), g2.clone()));
    let rblk = c.mul(c.mul(w3.clone(), g3.clone()), c.mul(w4.clone(), g4.clone()));
    let lhs = c.mul(lblk, rblk);
    // RHS: ((w1·w2)·(w3·w4)) · ((g1·g2)·(g3·g4)).
    let wblk = c.mul(c.mul(w1.clone(), w2.clone()), c.mul(w3.clone(), w4.clone()));
    let gblk = c.mul(c.mul(g1.clone(), g2.clone()), c.mul(g3.clone(), g4.clone()));
    let rhs = c.mul(wblk, gblk);

    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(g4_id, BinderInfo::Default, c.rat.clone(), concl);
    let ty = b.mk_pi(g3_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(g2_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(g1_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(w4_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(w3_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(w2_id, BinderInfo::Default, c.rat.clone(), ty);
    let ty = b.mk_pi(w1_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_mul8_regroup_value(c: &Mul8Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w1_id, w1) = b.fresh_local(c.rat.clone());
    let (w2_id, w2) = b.fresh_local(c.rat.clone());
    let (w3_id, w3) = b.fresh_local(c.rat.clone());
    let (w4_id, w4) = b.fresh_local(c.rat.clone());
    let (g1_id, g1) = b.fresh_local(c.rat.clone());
    let (g2_id, g2) = b.fresh_local(c.rat.clone());
    let (g3_id, g3) = b.fresh_local(c.rat.clone());
    let (g4_id, g4) = b.fresh_local(c.rat.clone());

    let w1g1 = c.mul(w1.clone(), g1.clone());
    let w2g2 = c.mul(w2.clone(), g2.clone());
    let w3g3 = c.mul(w3.clone(), g3.clone());
    let w4g4 = c.mul(w4.clone(), g4.clone());
    let w1w2 = c.mul(w1.clone(), w2.clone());
    let g1g2 = c.mul(g1.clone(), g2.clone());
    let w3w4 = c.mul(w3.clone(), w4.clone());
    let g3g4 = c.mul(g3.clone(), g4.clone());

    let lblk = c.mul(w1g1.clone(), w2g2.clone()); // (w1·g1)·(w2·g2)
    let rblk = c.mul(w3g3.clone(), w4g4.clone()); // (w3·g3)·(w4·g4)
    let lblk2 = c.mul(w1w2.clone(), g1g2.clone()); // (w1·w2)·(g1·g2)
    let rblk2 = c.mul(w3w4.clone(), g3g4.clone()); // (w3·w4)·(g3·g4)

    // e0 := lblk · rblk
    let e0 = c.mul(lblk.clone(), rblk.clone());
    // e1 := lblk2 · rblk    (rewrite left block via mmmc, under (· · rblk)).
    let e1 = c.mul(lblk2.clone(), rblk.clone());
    let mmmc_l = c.mmmc(w1.clone(), g1.clone(), w2.clone(), g2.clone()); // lblk = lblk2
    let leg1 = c.congr(
        lblk.clone(),
        lblk2.clone(),
        c.mul_right_motive(&b, &rblk),
        mmmc_l,
    );
    // e2 := lblk2 · rblk2   (rewrite right block via mmmc, under (lblk2 · ·)).
    let e2 = c.mul(lblk2.clone(), rblk2.clone());
    let mmmc_r = c.mmmc(w3.clone(), g3.clone(), w4.clone(), g4.clone()); // rblk = rblk2
    let leg2 = c.congr(
        rblk.clone(),
        rblk2.clone(),
        c.mul_left_motive(&b, &lblk2),
        mmmc_r,
    );
    // e3 := ((w1·w2)·(w3·w4)) · ((g1·g2)·(g3·g4))   (top mmmc).
    let wblk = c.mul(w1w2.clone(), w3w4.clone());
    let gblk = c.mul(g1g2.clone(), g3g4.clone());
    let e3 = c.mul(wblk, gblk);
    // mmmc (w1·w2) (g1·g2) (w3·w4) (g3·g4)
    //   : ((w1·w2)·(g1·g2))·((w3·w4)·(g3·g4)) = ((w1·w2)·(w3·w4))·((g1·g2)·(g3·g4)).
    let leg3 = c.mmmc(w1w2.clone(), g1g2.clone(), w3w4.clone(), g3g4.clone());

    // Chain: e0 = e1 = e2 = e3.
    let t1 = c.trans(e0.clone(), e1.clone(), e2.clone(), leg1, leg2);
    let proof = c.trans(e0, e2, e3, t1, leg3);

    let val = b.mk_lam(g4_id, BinderInfo::Default, c.rat.clone(), proof);
    let val = b.mk_lam(g3_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(g2_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(g1_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(w4_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(w3_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(w2_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(w1_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

// ════════════════════════════════════════════════════════════════════════════
// Tier-5 chain (Form A of the build plan, §2.1). Built as a ladder of
// registered Constructive intermediate Theorems, each `Eq.trans`-composable
// into the next. The first rung bridges the outer `Fin.sum (2^n)` of the
// `pow4_noisefn_fourfold` RHS into the `subsetSum n` / `HCPoint` convention so
// the rest of the chain stays in one convention (the build plan's "bridge the
// top sum ONCE" step). `subsetSum n G ≡ Fin.sum (2^n) (fun j => G (hcDecode n j))`
// is *reducible*, so each bridge is a def-eq re-presentation discharged by the
// `pow4_noisefn_fourfold` proof under `Eq.trans` with `Eq.refl`.
// ════════════════════════════════════════════════════════════════════════════

/// Atoms for the Tier-5 spectral chain. Self-contained (the `SpectralConsts`
/// 2-fold machinery lives in a sibling private module; we re-declare the atoms
/// we need — chi / weight / `g`==`A` carrier / subsetSum primitives — plus the
/// density/noiseFn atoms).
struct Pow4SpectralConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    chi: Expr,
    pow_nat: Expr,
    hc_decode: Expr,
    noise_fn: Expr,
    noise_density: Expr,
    pow4_fourfold: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_swap: Expr,
    subset_sum_smul: Expr,
    fin: Expr,
    nat_pow: Expr,
    two: Expr,
    fin_sum: Expr,
    fin_sum_nat: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl Pow4SpectralConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            nat_zero,
            nat_succ: nat_succ.clone(),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            noise_fn: Expr::const_(Name::from_string("BoolAnalysis.noiseFn"), vec![]),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            pow4_fourfold: Expr::const_(
                Name::from_string("BoolAnalysis.pow4_noisefn_fourfold"),
                vec![],
            ),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            subset_sum_swap: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_swap"), vec![]),
            subset_sum_smul: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two: Expr::app(nat_succ, nat_one),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_nat: Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn rat_ty(&self) -> Expr {
        self.rat.clone()
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn fin_pow(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), self.pow2(n))
    }
    fn sum_pow(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [self.pow2(n), g])
    }
    fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), k.clone()])
    }
    fn noise_fn(&self, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [rho.clone(), n.clone(), f.clone(), jx.clone()],
        )
    }
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `pow4 z := (z·z)·(z·z)` — the `pow4_of` shape used by the fourfold.
    fn pow4(&self, z: &Expr) -> Expr {
        let sq = self.mul(z.clone(), z.clone());
        self.mul(sq.clone(), sq)
    }

    // ── chi / weight / A carrier (mirrors SpectralConsts, self-contained) ──────

    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn pow(&self, rho: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [rho.clone(), k.clone()])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `indNat b = @Bool.rec.{1} (fun _ => Nat) 0 1 b` — per-bit popcount summand,
    /// byte-for-byte `SpectralConsts::ind_nat`.
    fn ind_nat(&self, s_i: Expr) -> Expr {
        let nat_one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        let bool_rec_nat = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(
            bool_rec_nat,
            [nat_motive, self.nat_zero.clone(), nat_one, s_i],
        )
    }
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — popcount `|S|`,
    /// byte-for-byte `SpectralConsts::popcount` (so `weight` is def-eq to the
    /// `noiseDensityW` weight).
    fn popcount(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(Expr::app(s.clone(), i.clone()));
        let pc_fn = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(self.fin_sum_nat.clone(), [n.clone(), pc_fn])
    }
    /// `w S = ρ^{pc n S}` — the per-subset ρ-weight.
    fn weight(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        self.pow(rho, &self.popcount(parent, n, s))
    }
    /// `A F S = subsetSum n (fun y => F y · χ_S y)` — the un-normalized Fourier
    /// coefficient (the `g`/A carrier of `noise_spectral_core` with `a := F`).
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(f.clone(), y.clone()), self.chi_(n, s, &y));
        let g_fn = b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g_fn)
    }

    // ── equality / congruence combinators (self-contained) ─────────────────────

    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `congrArg Rat Rat a b g h : g a = g b` from `h : a = b`.
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    /// `subsetSum_congr n G H h : subsetSum n G = subsetSum n H`.
    fn ss_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    /// `subsetSum_smul n c f : subsetSum n (fun S => c·f S) = c·subsetSum n f`.
    fn ss_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum_smul.clone(),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    /// `subsetSum_swap n f : Σ_S Σ_x f S x = Σ_x Σ_S f S x`.
    fn ss_swap(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.subset_sum_swap.clone(), [n.clone(), f.clone()])
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
    fn mul_left_congr(
        &self,
        parent: &EnvDeclBuilder,
        left: &Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = bb.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            bb.finish_child(bb.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, b, g, h)
    }
    fn trans3(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr, h3: Expr) -> Expr {
        let t1 = self.trans(a.clone(), b.clone(), cc.clone(), h1, h2);
        self.trans(a, cc, d, t1, h3)
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            [a, b, cc, d],
        )
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    /// `p·(w·q) = w·(p·q)` (assoc + comm + assoc), the `SpectralConsts::mul_left_comm`.
    fn mul_left_comm(&self, parent: &EnvDeclBuilder, p: &Expr, w: &Expr, q: &Expr) -> Expr {
        let p_wq = self.mul(p.clone(), self.mul(w.clone(), q.clone()));
        let pw_q = self.mul(self.mul(p.clone(), w.clone()), q.clone());
        let wp_q = self.mul(self.mul(w.clone(), p.clone()), q.clone());
        let w_pq = self.mul(w.clone(), self.mul(p.clone(), q.clone()));
        // leg1 : p·(w·q) = (p·w)·q   (symm of mul_assoc p w q).
        let assoc1 = self.mul_assoc(p.clone(), w.clone(), q.clone());
        let leg1 = self.symm(pw_q.clone(), p_wq.clone(), assoc1);
        // leg2 : (p·w)·q = (w·p)·q   (congr (·q) (mul_comm p w)).
        let g_rq = {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = bb.fresh_local(self.rat.clone());
            let body = self.mul(z, q.clone());
            bb.finish_child(bb.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let comm = self.mul_comm(p.clone(), w.clone());
        let leg2 = self.congr(
            self.mul(p.clone(), w.clone()),
            self.mul(w.clone(), p.clone()),
            g_rq,
            comm,
        );
        // leg3 : (w·p)·q = w·(p·q)   (mul_assoc w p q).
        let leg3 = self.mul_assoc(w.clone(), p.clone(), q.clone());
        self.trans3(p_wq, pw_q, wp_q, w_pq, leg1, leg2, leg3)
    }

    /// `gxd x := fun (jy : Fin (2^n)) => F(decode jy)·noiseDensityW ρ n x (decode jy)`
    /// — the `noiseFn` integrand with the OUTER coordinate as an explicit
    /// `HCPoint n` value `x` (rather than `decode jx`). At `x := decode jx` this
    /// is byte-for-byte `Pow4NoiseConsts::gx`.
    fn gxd(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_pow(n);
        let (jy_id, jy) = b.fresh_local(fin_p.clone());
        let y = self.decode(n, &jy);
        let f_y = Expr::app(f.clone(), y.clone());
        let dens = self.density(rho, n, x, &y);
        let body = self.mul(f_y, dens);
        b.finish_child(b.mk_lam(jy_id, BinderInfo::Default, fin_p, body))
    }

    /// The innermost quartic quad-sum over a fixed integrand `g : Fin (2^n) → Rat`,
    /// in the `(j1,j3,j2,j4)` order / `(g j1·g j2)·(g j3·g j4)` grouping that the
    /// `Fin.sum_pow4` RHS produces. Byte-for-byte `build_quad_rhs(&base,...,g)`.
    fn quad_rhs(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let pow2n = self.pow2(n);
        build_quad_rhs(&Pow4Consts::new(), parent, &pow2n, g)
    }

    /// `fun (x : HCPoint n) => quad_rhs (gxd x)` — the `subsetSum`-x integrand of
    /// the bridged fourfold RHS.
    fn bridge_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let g = self.gxd(&b, rho, n, f, &x);
        let body = self.quad_rhs(&b, n, &g);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// `fun (jx : Fin (2^n)) => pow4 (noiseFn ρ n F jx)` — the 4th-moment LHS
    /// integrand (matches `build_lhs_jx_fn`).
    fn lhs_jx_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_pow(n);
        let (jx_id, jx) = b.fresh_local(fin_p.clone());
        let nf = self.noise_fn(rho, n, f, &jx);
        let body = self.pow4(&nf);
        b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin_p, body))
    }
}

/// L1 type — `pow4_noisefn_subsetsum_x`:
/// `∀ ρ n F, Fin.sum (2^n) (fun jx => pow4 (noiseFn ρ n F jx))
///    = subsetSum n (fun x => Σ_{j1,j3,j2,j4} (gxd x j1·gxd x j2)·(gxd x j3·gxd x j4))`.
/// Bridges the outer `Fin.sum (2^n)` of the `pow4_noisefn_fourfold` RHS into
/// `subsetSum n`. RHS is def-eq to the fourfold RHS (`subsetSum` reducible).
fn build_subsetsum_x_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    let rhs = c.ssum(&n, c.bridge_x_fn(&b, &rho, &n, &f));
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

// ════════════════════════════════════════════════════════════════════════════
// L3 — `Fin.sum_prod4` : the 4-DISTINCT-function product expansion, the
// generic carrier converse of `Fin.sum_pow4` (which is the `f1=f2=f3=f4` case):
//   (Σf1·Σf2)·(Σf3·Σf4) = Σ_{j1}Σ_{j3}Σ_{j2}Σ_{j4} (f1 j1·f2 j2)·(f3 j3·f4 j4)
// Built from three `Fin.sum_mul_sum` (one per factor pair + one to glue), the
// exact skeleton of `build_sum_pow4_value` threaded with four distinct fns.
// Reused as `Eq.symm` to FOLD the density-unfolded quad-sum back into a product
// of four `noiseFn`-leg sums.
// ════════════════════════════════════════════════════════════════════════════

/// `fun (j2 : Fin n) => f1 a · f2 j2` — inner pair integrand at fixed `f1a := f1 a`.
fn prod4_pair_fn(c: &Pow4Consts, parent: &EnvDeclBuilder, n: &Expr, f1a: &Expr, f2: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j_id, j) = b.fresh_local(fin_n.clone());
    let body = c.mul(f1a.clone(), Expr::app(f2.clone(), j));
    b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_n, body))
}

/// `h12 := fun (j1 : Fin n) => Σ_{j2} f1 j1·f2 j2` — the `Fin.sum_mul_sum n n f1 f2`
/// RHS integrand.
fn prod4_h_fn(c: &Pow4Consts, parent: &EnvDeclBuilder, n: &Expr, f1: &Expr, f2: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j1_id, j1) = b.fresh_local(fin_n.clone());
    let f1a = Expr::app(f1.clone(), j1);
    let body = c.sum(n, prod4_pair_fn(c, &b, n, &f1a, f2));
    b.finish_child(b.mk_lam(j1_id, BinderInfo::Default, fin_n, body))
}

/// `fun (j4 : Fin n) => (f1 j1·f2 j2)·(f3 j3·f4 j4)` at fixed `left := f1 j1·f2 j2`,
/// `f3j3 := f3 j3`.
fn prod4_inner_j4_fn(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    left: &Expr,
    f3j3: &Expr,
    f4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j4_id, j4) = b.fresh_local(fin_n.clone());
    let right = c.mul(f3j3.clone(), Expr::app(f4.clone(), j4));
    let body = c.mul(left.clone(), right);
    b.finish_child(b.mk_lam(j4_id, BinderInfo::Default, fin_n, body))
}

/// `fun (j2 : Fin n) => Σ_{j4} (f1 j1·f2 j2)·(f3 j3·f4 j4)` at fixed `f1j1,f3j3`.
fn prod4_j2_fn(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f1j1: &Expr,
    f3j3: &Expr,
    f2: &Expr,
    f4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j2_id, j2) = b.fresh_local(fin_n.clone());
    let left = c.mul(f1j1.clone(), Expr::app(f2.clone(), j2));
    let inner = prod4_inner_j4_fn(c, &b, n, &left, f3j3, f4);
    b.finish_child(b.mk_lam(j2_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
}

/// `fun (j3 : Fin n) => Σ_{j2}Σ_{j4} (f1 j1·f2 j2)·(f3 j3·f4 j4)` at fixed `f1j1`.
fn prod4_j3_fn(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f1j1: &Expr,
    f2: &Expr,
    f3: &Expr,
    f4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j3_id, j3) = b.fresh_local(fin_n.clone());
    let f3j3 = Expr::app(f3.clone(), j3);
    let inner = prod4_j2_fn(c, &b, n, f1j1, &f3j3, f2, f4);
    b.finish_child(b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
}

/// `fun (j1 : Fin n) => Σ_{j3}Σ_{j2}Σ_{j4} (f1 j1·f2 j2)·(f3 j3·f4 j4)`.
fn prod4_j1_fn(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f1: &Expr,
    f2: &Expr,
    f3: &Expr,
    f4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j1_id, j1) = b.fresh_local(fin_n.clone());
    let f1j1 = Expr::app(f1.clone(), j1);
    let inner = prod4_j3_fn(c, &b, n, &f1j1, f2, f3, f4);
    b.finish_child(b.mk_lam(j1_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
}

/// The full quad RHS `Σ_{j1}Σ_{j3}Σ_{j2}Σ_{j4} (f1 j1·f2 j2)·(f3 j3·f4 j4)`.
fn prod4_quad_rhs(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f1: &Expr,
    f2: &Expr,
    f3: &Expr,
    f4: &Expr,
) -> Expr {
    c.sum(n, prod4_j1_fn(c, parent, n, f1, f2, f3, f4))
}

/// `Fin.sum_prod4` conclusion type.
fn build_prod4_type(c: &Pow4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.fin_to_rat(&n);
    let (f1_id, f1) = b.fresh_local(f_ty.clone());
    let (f2_id, f2) = b.fresh_local(f_ty.clone());
    let (f3_id, f3) = b.fresh_local(f_ty.clone());
    let (f4_id, f4) = b.fresh_local(f_ty.clone());

    let s1 = c.sum(&n, f1.clone());
    let s2 = c.sum(&n, f2.clone());
    let s3 = c.sum(&n, f3.clone());
    let s4 = c.sum(&n, f4.clone());
    let lhs = c.mul(c.mul(s1, s2), c.mul(s3, s4));
    let rhs = prod4_quad_rhs(c, &b, &n, &f1, &f2, &f3, &f4);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f4_id, BinderInfo::Default, f_ty.clone(), concl);
    let ty = b.mk_pi(f3_id, BinderInfo::Default, f_ty.clone(), ty);
    let ty = b.mk_pi(f2_id, BinderInfo::Default, f_ty.clone(), ty);
    let ty = b.mk_pi(f1_id, BinderInfo::Default, f_ty, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

/// `Fin.sum_prod4` proof — the `build_sum_pow4_value` skeleton with 4 distinct fns.
fn build_prod4_value(c: &Pow4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.fin_to_rat(&n);
    let (f1_id, f1) = b.fresh_local(f_ty.clone());
    let (f2_id, f2) = b.fresh_local(f_ty.clone());
    let (f3_id, f3) = b.fresh_local(f_ty.clone());
    let (f4_id, f4) = b.fresh_local(f_ty.clone());

    let s1 = c.sum(&n, f1.clone());
    let s2 = c.sum(&n, f2.clone());
    let s3 = c.sum(&n, f3.clone());
    let s4 = c.sum(&n, f4.clone());
    let s12 = c.mul(s1.clone(), s2.clone());
    let s34 = c.mul(s3.clone(), s4.clone());

    // h12 j1 := Σ_j2 f1 j1·f2 j2 ; D12 := Σ h12. h34 j3 := Σ_j4 f3 j3·f4 j4 ; D34 := Σ h34.
    let h12 = prod4_h_fn(c, &b, &n, &f1, &f2);
    let h34 = prod4_h_fn(c, &b, &n, &f3, &f4);
    let d12 = c.sum(&n, h12.clone());
    let d34 = c.sum(&n, h34.clone());

    // dms12 : (Σf1)·(Σf2) = D12 ; dms34 : (Σf3)·(Σf4) = D34.
    let dms12 = c.sum_mul_sum(&n, &f1, &f2);
    let dms34 = c.sum_mul_sum(&n, &f3, &f4);

    // legA1 : (s12)·(s34) = D12·(s34)  via congrArg (z => z·s34) dms12.
    let left_fn = {
        let mut lb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = lb.fresh_local(c.rat.clone());
        let body = c.mul(z, s34.clone());
        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let leg_a1 = c.congr(s12.clone(), d12.clone(), left_fn, dms12);
    let d12_s34 = c.mul(d12.clone(), s34.clone());
    // legA2 : D12·(s34) = D12·D34  via congrArg (z => D12·z) dms34.
    let right_fn = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = rb.fresh_local(c.rat.clone());
        let body = c.mul(d12.clone(), z);
        rb.finish_child(rb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let leg_a2 = c.congr(s34.clone(), d34.clone(), right_fn, dms34);
    let dd = c.mul(d12.clone(), d34.clone());
    let lhs = c.mul(s12.clone(), s34.clone());
    let leg_a = c.trans(lhs.clone(), d12_s34, dd.clone(), leg_a1, leg_a2);

    // legB : D12·D34 = Σ_{j1} Σ_{j3} h12 j1·h34 j3   (Fin.sum_mul_sum n n h12 h34).
    let leg_b = c.sum_mul_sum(&n, &h12, &h34);
    let e_mid = prod4_hh_double(c, &b, &n, &h12, &h34);

    // legC : e_mid = quad RHS  (Fin.sum_congr over j1 of over j3 of per-(j1,j3) sum_mul_sum).
    let leg_c = build_prod4_leg_c(c, &b, &n, &f1, &f2, &f3, &f4, &h12, &h34);
    let rhs = prod4_quad_rhs(c, &b, &n, &f1, &f2, &f3, &f4);

    let t1 = c.trans(lhs.clone(), dd.clone(), e_mid.clone(), leg_a, leg_b);
    let proof = c.trans(lhs, e_mid, rhs, t1, leg_c);

    let val = b.mk_lam(f4_id, BinderInfo::Default, f_ty.clone(), proof);
    let val = b.mk_lam(f3_id, BinderInfo::Default, f_ty.clone(), val);
    let val = b.mk_lam(f2_id, BinderInfo::Default, f_ty.clone(), val);
    let val = b.mk_lam(f1_id, BinderInfo::Default, f_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

/// `Σ_{j1} (fun j1 => Σ_{j3} h12 j1·h34 j3)` — the `D12·D34` expansion.
fn prod4_hh_double(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    h12: &Expr,
    h34: &Expr,
) -> Expr {
    c.sum(n, prod4_hh_double_fn(c, parent, n, h12, h34))
}

/// `fun (j1 : Fin n) => Σ_{j3} h12 j1·h34 j3`.
fn prod4_hh_double_fn(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    h12: &Expr,
    h34: &Expr,
) -> Expr {
    let mut j1b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j1_id, j1) = j1b.fresh_local(fin_n.clone());
    let hj1 = Expr::app(h12.clone(), j1);
    let inner = {
        let mut j3b = EnvDeclBuilder::child_of(&j1b);
        let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
        let body = c.mul(hj1.clone(), Expr::app(h34.clone(), j3));
        j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), body))
    };
    j1b.finish_child(j1b.mk_lam(j1_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
}

/// Leg C for `Fin.sum_prod4`.
#[allow(clippy::too_many_arguments)]
fn build_prod4_leg_c(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f1: &Expr,
    f2: &Expr,
    f3: &Expr,
    f4: &Expr,
    h12: &Expr,
    h34: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let before_j1 = prod4_hh_double_fn(c, parent, n, h12, h34);
    let after_j1 = prod4_j1_fn(c, parent, n, f1, f2, f3, f4);
    let h_j1 = {
        let mut j1b = EnvDeclBuilder::child_of(parent);
        let (j1_id, j1) = j1b.fresh_local(fin_n.clone());
        let f1j1 = Expr::app(f1.clone(), j1.clone());
        let hj1 = Expr::app(h12.clone(), j1);

        let before_j3 = {
            let mut j3b = EnvDeclBuilder::child_of(&j1b);
            let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
            let body = c.mul(hj1.clone(), Expr::app(h34.clone(), j3));
            j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), body))
        };
        let after_j3 = {
            let mut j3b = EnvDeclBuilder::child_of(&j1b);
            let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
            let f3j3 = Expr::app(f3.clone(), j3);
            let inner = prod4_j2_fn(c, &j3b, n, &f1j1, &f3j3, f2, f4);
            j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
        };
        let h_j3 = {
            let mut j3b = EnvDeclBuilder::child_of(&j1b);
            let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
            let f3j3 = Expr::app(f3.clone(), j3);
            // pj1 := fun j2 => f1 j1·f2 j2 (= h12 j1 body); pj3 := fun j4 => f3 j3·f4 j4 (= h34 j3 body).
            let pj1 = prod4_pair_fn(c, &j3b, n, &f1j1, f2);
            let pj3 = prod4_pair_fn(c, &j3b, n, &f3j3, f4);
            let body = c.sum_mul_sum(n, &pj1, &pj3);
            j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), body))
        };
        let cong = c.sum_congr(n, &before_j3, &after_j3, h_j3);
        j1b.finish_child(j1b.mk_lam(j1_id, BinderInfo::Default, fin_n.clone(), cong))
    };
    c.sum_congr(n, &before_j1, &after_j1, h_j1)
}

// ════════════════════════════════════════════════════════════════════════════
// L4 — `subsetSum_prod4` : the subsetSum-convention analogue of `Fin.sum_prod4`,
//   (Σ_S P1·Σ_S P2)·(Σ_S P3·Σ_S P4)
//     = Σ_S1 Σ_S2 Σ_S3 Σ_S4 (P1 S1·P2 S2)·(P3 S3·P4 S4)
// Derived from `Fin.sum_prod4 (2^n) (Pk∘decode)…` (both sides δ-unfold to the
// matching `Fin.sum` quad over decoded indices — the `subsetSum_swap`-style
// decode bridge). The S-pullout engine for the four spectral subset indices.
// ════════════════════════════════════════════════════════════════════════════

impl Pow4SpectralConsts {
    /// `fun (j : Fin (2^n)) => P (hcDecode n j)` — the subsetSum↔Fin.sum bridge.
    fn decoded_fn(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_pow(n);
        let (j_id, j) = b.fresh_local(fin_p.clone());
        let body = Expr::app(p.clone(), self.decode(n, &j));
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_p, body))
    }
}

/// `subsetSum_prod4` type — four `Pk : HCPoint n → Rat`.
fn build_ss_prod4_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let p_ty = c.f_type(&n);
    let (p1_id, p1) = b.fresh_local(p_ty.clone());
    let (p2_id, p2) = b.fresh_local(p_ty.clone());
    let (p3_id, p3) = b.fresh_local(p_ty.clone());
    let (p4_id, p4) = b.fresh_local(p_ty.clone());

    let s1 = c.ssum(&n, p1.clone());
    let s2 = c.ssum(&n, p2.clone());
    let s3 = c.ssum(&n, p3.clone());
    let s4 = c.ssum(&n, p4.clone());
    let lhs = c.mul(c.mul(s1, s2), c.mul(s3, s4));
    let rhs = ss_prod4_quad_rhs(c, &b, &n, &p1, &p2, &p3, &p4);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(p4_id, BinderInfo::Default, p_ty.clone(), concl);
    let ty = b.mk_pi(p3_id, BinderInfo::Default, p_ty.clone(), ty);
    let ty = b.mk_pi(p2_id, BinderInfo::Default, p_ty.clone(), ty);
    let ty = b.mk_pi(p1_id, BinderInfo::Default, p_ty, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

/// `Σ_S1 Σ_S2 Σ_S3 Σ_S4 (P1 S1·P2 S2)·(P3 S3·P4 S4)` — note the `(S1,S3,S2,S4)`
/// NESTING (outer→inner) to MATCH `Fin.sum_prod4`'s `(j1,j3,j2,j4)` order, so the
/// proof is a direct decode-bridge of `Fin.sum_prod4`.
fn ss_prod4_quad_rhs(
    c: &Pow4SpectralConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    p1: &Expr,
    p2: &Expr,
    p3: &Expr,
    p4: &Expr,
) -> Expr {
    c.ssum(n, ss_prod4_s1_fn(c, parent, n, p1, p2, p3, p4))
}

fn ss_prod4_s1_fn(
    c: &Pow4SpectralConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    p1: &Expr,
    p2: &Expr,
    p3: &Expr,
    p4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s1_id, s1) = b.fresh_local(hcp.clone());
    let p1s1 = Expr::app(p1.clone(), s1);
    let inner = ss_prod4_s3_fn(c, &b, n, &p1s1, p2, p3, p4);
    b.finish_child(b.mk_lam(s1_id, BinderInfo::Default, hcp, c.ssum(n, inner)))
}

fn ss_prod4_s3_fn(
    c: &Pow4SpectralConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    p1s1: &Expr,
    p2: &Expr,
    p3: &Expr,
    p4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s3_id, s3) = b.fresh_local(hcp.clone());
    let p3s3 = Expr::app(p3.clone(), s3);
    let inner = ss_prod4_s2_fn(c, &b, n, p1s1, &p3s3, p2, p4);
    b.finish_child(b.mk_lam(s3_id, BinderInfo::Default, hcp, c.ssum(n, inner)))
}

fn ss_prod4_s2_fn(
    c: &Pow4SpectralConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    p1s1: &Expr,
    p3s3: &Expr,
    p2: &Expr,
    p4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s2_id, s2) = b.fresh_local(hcp.clone());
    let left = c.mul(p1s1.clone(), Expr::app(p2.clone(), s2));
    let inner = ss_prod4_s4_fn(c, &b, n, &left, p3s3, p4);
    b.finish_child(b.mk_lam(s2_id, BinderInfo::Default, hcp, c.ssum(n, inner)))
}

fn ss_prod4_s4_fn(
    c: &Pow4SpectralConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    left: &Expr,
    p3s3: &Expr,
    p4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s4_id, s4) = b.fresh_local(hcp.clone());
    let right = c.mul(p3s3.clone(), Expr::app(p4.clone(), s4));
    let body = c.mul(left.clone(), right);
    b.finish_child(b.mk_lam(s4_id, BinderInfo::Default, hcp, body))
}

/// `subsetSum_prod4` proof — `Fin.sum_prod4 (2^n) (P1∘dec)(P2∘dec)(P3∘dec)(P4∘dec)`.
/// LHS δ-unfolds: `subsetSum n Pk ≡ Fin.sum (2^n)(Pk∘dec)`. RHS δ-unfolds to the
/// matching `Fin.sum_prod4` quad (the inner `(P1 S1·P2 S2)·(P3 S3·P4 S4)` with
/// `Sk := dec jk`). Def-eq bridge.
fn build_ss_prod4_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let p_ty = c.f_type(&n);
    let (p1_id, p1) = b.fresh_local(p_ty.clone());
    let (p2_id, p2) = b.fresh_local(p_ty.clone());
    let (p3_id, p3) = b.fresh_local(p_ty.clone());
    let (p4_id, p4) = b.fresh_local(p_ty.clone());

    let d1 = c.decoded_fn(&b, &n, &p1);
    let d2 = c.decoded_fn(&b, &n, &p2);
    let d3 = c.decoded_fn(&b, &n, &p3);
    let d4 = c.decoded_fn(&b, &n, &p4);
    let pow2n = c.pow2(&n);
    let prod4 = Expr::const_(Name::from_string("Fin.sum_prod4"), vec![]);
    let proof = Expr::apps(prod4, [pow2n, d1, d2, d3, d4]);

    let val = b.mk_lam(p4_id, BinderInfo::Default, p_ty.clone(), proof);
    let val = b.mk_lam(p3_id, BinderInfo::Default, p_ty.clone(), val);
    let val = b.mk_lam(p2_id, BinderInfo::Default, p_ty.clone(), val);
    let val = b.mk_lam(p1_id, BinderInfo::Default, p_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

/// `gxu x := fun (jy : Fin (2^n)) => F(decode jy)·(Σ_S ρ^|S|·(χ_S x·χ_S(decode jy)))`
/// — the `gxd` integrand with its `noiseDensityW` δ-unfolded to the explicit
/// `subsetSum` form. Def-eq to `gxd x` (`noiseDensityW` reducible), so the
/// quad-sum over `gxu` is def-eq to the quad-sum over `gxd`.
impl Pow4SpectralConsts {
    fn gxu(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_pow(n);
        let (jy_id, jy) = b.fresh_local(fin_p.clone());
        let y = self.decode(n, &jy);
        let f_y = Expr::app(f.clone(), y.clone());
        // wchi S = ρ^|S|·(χ_S x·χ_S y).
        let wchi_fn = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let hcp = self.hcpoint_of(n);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let w = self.weight(&sb, rho, n, &s);
            let body = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, &y)));
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        let dens = self.ssum(n, wchi_fn);
        let body = self.mul(f_y, dens);
        b.finish_child(b.mk_lam(jy_id, BinderInfo::Default, fin_p, body))
    }

    /// `fun (x : HCPoint n) => quad_rhs (gxu x)` — the density-unfolded x-integrand.
    fn unfold_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let g = self.gxu(&b, rho, n, f, &x);
        let body = self.quad_rhs(&b, n, &g);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

/// L2 type — `pow4_noisefn_density_unfold`:
/// same LHS as L1, RHS the density-UNFOLDED form
/// `subsetSum n (fun x => Σ_{j1,j3,j2,j4} (gxu x j1·gxu x j2)·(gxu x j3·gxu x j4))`.
/// `gxu` δ-unfolds each `noiseDensityW` to `Σ_S ρ^|S|·(χ_S x·χ_S y)`; def-eq to L1.
fn build_density_unfold_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    let rhs = c.ssum(&n, c.unfold_x_fn(&b, &rho, &n, &f));
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

/// L2 value — `pow4_noisefn_subsetsum_x ρ n F` directly: its stated RHS (gxd form)
/// is def-eq to the gxu form (`noiseDensityW` reducible), so the L1 proof checks
/// against the L2 type without an extra trans leg.
fn build_density_unfold_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let l1 = Expr::const_(
        Name::from_string("BoolAnalysis.pow4_noisefn_subsetsum_x"),
        vec![],
    );
    let proof = Expr::apps(l1, [rho.clone(), n.clone(), f.clone()]);

    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

/// L1 value — `Eq.trans (pow4_noisefn_fourfold ρ n F) Eq.refl`.
/// The fourfold gives `LHS = Σ_jx quad_rhs(gx jx)`; that RHS is def-eq to
/// `subsetSum n (fun x => quad_rhs(gxd x))` (subsetSum reducible, and
/// `gxd (decode jx) ≡ gx jx`), so the second leg is `Eq.refl` (here the bridged
/// RHS itself, which `Eq.trans` accepts because the middle term unifies up to
/// def-eq).
fn build_subsetsum_x_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    let rhs = c.ssum(&n, c.bridge_x_fn(&b, &rho, &n, &f));
    // pow4_noisefn_fourfold ρ n F : lhs = fourfoldRHS, where fourfoldRHS is
    // def-eq to `rhs` (subsetSum reducible). Eq.refl : rhs = rhs serves the
    // second leg; `Eq.trans` unifies the shared middle term up to def-eq.
    let fourfold = Expr::apps(c.pow4_fourfold.clone(), [rho.clone(), n.clone(), f.clone()]);
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let refl_rhs = Expr::apps(eq_refl, [c.rat.clone(), rhs.clone()]);
    let proof = c.trans(lhs, rhs.clone(), rhs, fourfold, refl_rhs);

    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

// ════════════════════════════════════════════════════════════════════════════
// L5 — `pow4_noisefn_M_form` : fold the density-unfolded quad back to a product
// of four identical bilinear legs, each rewritten to the spectral M-form.
//
//   Σ_jx pow4(noiseFn ρ n F jx) = subsetSum n (fun x => pow4 (M x))
//   M x := subsetSum n (fun S => (ρ^|S|·χ_S x)·A F S)
//   A F S := subsetSum n (fun y => F y·χ_S y)
//
// Built on L2 (density-unfold) via:
//   • `subsetSum_congr` over x of `Eq.symm (Fin.sum_prod4 (2^n)(gxu x)…)`
//     to fold the quad-sum back to `pow4(L x)`, L x = Σ_jy gxu x jy;
//   • `subsetSum_congr` over x of `congrArg pow4 (L x = M x)`, the per-x bridge.
// `L x` is def-eq to `subsetSum n (l_int x)`, `l_int x y = F y·W(x,y)`,
// `W(x,y) = subsetSum n (fun S => ρ^|S|·(χ_S x·χ_S y))` (noiseDensityW unfolded).
// ════════════════════════════════════════════════════════════════════════════

impl Pow4SpectralConsts {
    /// `W(x,y) = subsetSum n (fun S => ρ^|S|·(χ_S x·χ_S y))` — the unfolded density.
    fn wxy(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let w = self.weight(&sb, rho, n, &s);
        let body = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, y)));
        let f = sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
    /// `l_int x = fun (y : HCPoint n) => F y · W(x,y)` — the L-form integrand.
    /// `subsetSum n (l_int x) ≡ Σ_jy gxu x jy` (subsetSum reducible).
    fn l_int_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(f.clone(), y.clone()), self.wxy(&b, rho, n, x, &y));
        b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
    /// `t_term S x = (ρ^|S|·χ_S x)·A F S` — the M-form per-S integrand body.
    fn t_term(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s: &Expr,
        x: &Expr,
    ) -> Expr {
        let w = self.weight(parent, rho, n, s);
        let wcx = self.mul(w, self.chi_(n, s, x));
        let a_s = self.a_coeff(parent, n, f, s);
        self.mul(wcx, a_s)
    }
    /// `m_fn x = fun (S : HCPoint n) => t_term S x` — the M-form S-integrand.
    fn m_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.t_term(&b, rho, n, f, &s, x);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `M x = subsetSum n (m_fn x)`.
    fn m_form(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        self.ssum(n, self.m_fn(parent, rho, n, f, x))
    }

    /// Per-x bridge proof `L x = M x`.
    /// L x = subsetSum n (fun y => F y·W(x,y)); M x = subsetSum n (fun S => (w_S·χ_Sx)·A S).
    fn l_eq_m(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);

        // ── E0 = L x = subsetSum n (fun y => F y·(Σ_S w_S·(χ_Sx·χ_Sy))).
        let e0_fn = self.l_int_fn(parent, rho, n, f, x);
        let e0 = self.ssum(n, e0_fn.clone());

        // ── E1 = subsetSum n (fun y => Σ_S F y·(w_S·(χ_Sx·χ_Sy)))   [symm smul per-y].
        // scaled per-y integrand: fun S => F y·(w_S·(χ_Sx·χ_Sy)).
        let e1_fn = {
            let mut yb = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let fy = Expr::app(f.clone(), y.clone());
            let scaled = {
                let mut sb = EnvDeclBuilder::child_of(&yb);
                let (s_id, s) = sb.fresh_local(hcp.clone());
                let w = self.weight(&sb, rho, n, &s);
                let wchi = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, &y)));
                let body = self.mul(fy.clone(), wchi);
                sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
            };
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), self.ssum(n, scaled)))
        };
        let e1 = self.ssum(n, e1_fn.clone());
        // leg01 : E0 = E1   (ss_congr over y of symm (smul n (F y) wchi_y)).
        let leg01 = {
            let h = {
                let mut yb = EnvDeclBuilder::child_of(parent);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let fy = Expr::app(f.clone(), y.clone());
                // wchi_y : fun S => w_S·(χ_Sx·χ_Sy).
                let wchi_y = {
                    let mut sb = EnvDeclBuilder::child_of(&yb);
                    let (s_id, s) = sb.fresh_local(hcp.clone());
                    let w = self.weight(&sb, rho, n, &s);
                    let body = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, &y)));
                    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
                };
                let smul = self.ss_smul(n, &fy, &wchi_y);
                // smul : subsetSum (fun S => Fy·wchi) = Fy·subsetSum wchi.
                let fy_w = self.mul(fy.clone(), self.ssum(n, wchi_y.clone()));
                let scaled = {
                    let mut sb = EnvDeclBuilder::child_of(&yb);
                    let (s_id, s) = sb.fresh_local(hcp.clone());
                    let w = self.weight(&sb, rho, n, &s);
                    let wchi = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, &y)));
                    let body = self.mul(fy.clone(), wchi);
                    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
                };
                let pf = self.symm(self.ssum(n, scaled), fy_w, smul);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
            };
            self.ss_congr(n, &e0_fn, &e1_fn, h)
        };

        // ── E2 = subsetSum n (fun S => Σ_y F y·(w_S·(χ_Sx·χ_Sy)))   [ss_swap].
        // swap kernel : fun y S => F y·(w_S·(χ_Sx·χ_Sy)).
        let swap_kernel = {
            let mut yb = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let fy = Expr::app(f.clone(), y.clone());
            let inner = {
                let mut sb = EnvDeclBuilder::child_of(&yb);
                let (s_id, s) = sb.fresh_local(hcp.clone());
                let w = self.weight(&sb, rho, n, &s);
                let wchi = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, &y)));
                let body = self.mul(fy.clone(), wchi);
                sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
            };
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), inner))
        };
        let e2_fn = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let inner = {
                let mut yb = EnvDeclBuilder::child_of(&sb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let fy = Expr::app(f.clone(), y.clone());
                let w = self.weight(&yb, rho, n, &s);
                let wchi = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, &y)));
                let body = self.mul(fy, wchi);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), self.ssum(n, inner)))
        };
        let e2 = self.ssum(n, e2_fn.clone());
        let leg12 = self.ss_swap(n, &swap_kernel);

        // ── E3 = subsetSum n (fun S => Σ_y (w_S·χ_Sx)·(F y·χ_Sy))   [per-(S,y) regroup].
        let e3_fn = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let inner = {
                let mut yb = EnvDeclBuilder::child_of(&sb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let w = self.weight(&yb, rho, n, &s);
                let wcx = self.mul(w, self.chi_(n, &s, x));
                let fcy = self.mul(Expr::app(f.clone(), y.clone()), self.chi_(n, &s, &y));
                let body = self.mul(wcx, fcy);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), self.ssum(n, inner)))
        };
        let e3 = self.ssum(n, e3_fn.clone());
        // leg23 : E2 = E3  (ss_congr over S of ss_congr over y of the per-(S,y) regroup).
        let leg23 = {
            let h_s = {
                let mut sb = EnvDeclBuilder::child_of(parent);
                let (s_id, s) = sb.fresh_local(hcp.clone());
                let before_y = {
                    let mut yb = EnvDeclBuilder::child_of(&sb);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let fy = Expr::app(f.clone(), y.clone());
                    let w = self.weight(&yb, rho, n, &s);
                    let wchi = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, &y)));
                    let body = self.mul(fy, wchi);
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
                };
                let after_y = {
                    let mut yb = EnvDeclBuilder::child_of(&sb);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let w = self.weight(&yb, rho, n, &s);
                    let wcx = self.mul(w, self.chi_(n, &s, x));
                    let fcy = self.mul(Expr::app(f.clone(), y.clone()), self.chi_(n, &s, &y));
                    let body = self.mul(wcx, fcy);
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
                };
                let h_y = {
                    let mut yb = EnvDeclBuilder::child_of(&sb);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let pf = self.regroup_sy(&yb, rho, n, f, &s, x, &y);
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
                };
                let cong = self.ss_congr(n, &before_y, &after_y, h_y);
                sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), cong))
            };
            self.ss_congr(n, &e2_fn, &e3_fn, h_s)
        };

        // ── E4 = subsetSum n (fun S => (w_S·χ_Sx)·Σ_y (F y·χ_Sy)) = M x  [smul per-S].
        let m_fn = self.m_fn(parent, rho, n, f, x);
        let e4 = self.ssum(n, m_fn.clone());
        let leg34 = {
            let h_s = {
                let mut sb = EnvDeclBuilder::child_of(parent);
                let (s_id, s) = sb.fresh_local(hcp.clone());
                let w = self.weight(&sb, rho, n, &s);
                let wcx = self.mul(w, self.chi_(n, &s, x));
                let inner_y = {
                    let mut yb = EnvDeclBuilder::child_of(&sb);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let body = self.mul(Expr::app(f.clone(), y.clone()), self.chi_(n, &s, &y));
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
                };
                let pf = self.ss_smul(n, &wcx, &inner_y);
                sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), pf))
            };
            self.ss_congr(n, &e3_fn, &m_fn, h_s)
        };

        // Assemble E0 = E1 = E2 = E3 = E4(=M).
        let t1 = self.trans(e0.clone(), e1.clone(), e2.clone(), leg01, leg12);
        let t2 = self.trans(e0.clone(), e2.clone(), e3.clone(), t1, leg23);
        self.trans(e0, e3, e4, t2, leg34)
    }

    /// Per-(S,y) regroup: `F y·(w_S·(χ_Sx·χ_Sy)) = (w_S·χ_Sx)·(F y·χ_Sy)`.
    ///   • mul_left_comm Fy w (cx·cy)  : Fy·(w·(cx·cy)) = w·(Fy·(cx·cy));
    ///   • congr (w·) (mul_left_comm Fy cx cy) : w·(Fy·(cx·cy)) = w·(cx·(Fy·cy));
    ///   • symm (mul_assoc w cx (Fy·cy)) : w·(cx·(Fy·cy)) = (w·cx)·(Fy·cy).
    fn regroup_sy(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let fy = Expr::app(f.clone(), y.clone());
        let cx = self.chi_(n, s, x);
        let cy = self.chi_(n, s, y);
        let cxcy = self.mul(cx.clone(), cy.clone());
        let w = self.weight(parent, rho, n, s);
        // leg1 : Fy·(w·(cx·cy)) = w·(Fy·(cx·cy)).
        let leg1 = self.mul_left_comm(parent, &fy, &w, &cxcy);
        // inner : Fy·(cx·cy) = cx·(Fy·cy)   (mul_left_comm Fy cx cy).
        let inner = self.mul_left_comm(parent, &fy, &cx, &cy);
        let fy_cxcy = self.mul(fy.clone(), cxcy.clone());
        let cx_fycy = self.mul(cx.clone(), self.mul(fy.clone(), cy.clone()));
        // leg2 : w·(Fy·(cx·cy)) = w·(cx·(Fy·cy))   (congr (w·) inner).
        let leg2 = self.mul_left_congr(parent, &w, fy_cxcy.clone(), cx_fycy.clone(), inner);
        // leg3 : w·(cx·(Fy·cy)) = (w·cx)·(Fy·cy)   (symm mul_assoc w cx (Fy·cy)).
        let fycy = self.mul(fy.clone(), cy.clone());
        let assoc = self.mul_assoc(w.clone(), cx.clone(), fycy.clone());
        let wcx = self.mul(w.clone(), cx.clone());
        let leg3 = self.symm(
            self.mul(wcx.clone(), fycy.clone()),
            self.mul(w.clone(), cx_fycy.clone()),
            assoc,
        );
        // Chain: Fy·(w·(cx·cy)) = w·(Fy·(cx·cy)) = w·(cx·(Fy·cy)) = (w·cx)·(Fy·cy).
        let a = self.mul(fy.clone(), self.mul(w.clone(), cxcy.clone()));
        let b = self.mul(w.clone(), fy_cxcy);
        let cc = self.mul(w.clone(), cx_fycy);
        let d = self.mul(wcx, fycy);
        self.trans3(a, b, cc, d, leg1, leg2, leg3)
    }

    /// `congrArg (fun z => pow4 z) h : pow4 a = pow4 b` from `h : a = b`.
    fn pow4_congr(&self, parent: &EnvDeclBuilder, a: Expr, b: Expr, h: Expr) -> Expr {
        let g = {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = bb.fresh_local(self.rat.clone());
            let body = self.pow4(&z);
            bb.finish_child(bb.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, b, g, h)
    }

    /// `fun (jy : Fin (2^n)) => gxu x jy` — alias used as the four identical
    /// `Fin.sum_prod4` legs (same function ⇒ folds to `pow4(Σ gxu x)`).
    fn fin_sum_prod4_app(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        x: &Expr,
    ) -> Expr {
        let g = self.gxu(parent, rho, n, f, x);
        let pow2n = self.pow2(n);
        let prod4 = Expr::const_(Name::from_string("Fin.sum_prod4"), vec![]);
        Expr::apps(prod4, [pow2n, g.clone(), g.clone(), g.clone(), g])
    }
}

/// Probe — `fold` : `∀ ρ n F x, quad_rhs(gxu x) = pow4 (subsetSum n (l_int x))`
/// via `Eq.symm (Fin.sum_prod4 …)`. Isolates the L5 fold leg.
fn build_fold_probe_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let g = c.gxu(&b, &rho, &n, &f, &x);
    let quad = c.quad_rhs(&b, &n, &g);
    let l = c.ssum(&n, c.l_int_fn(&b, &rho, &n, &f, &x));
    let pow4_l = c.pow4(&l);
    let concl = c.eq_rat(quad, pow4_l);

    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, concl);
    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

fn build_fold_probe_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let g = c.gxu(&b, &rho, &n, &f, &x);
    let quad = c.quad_rhs(&b, &n, &g);
    let l = c.ssum(&n, c.l_int_fn(&b, &rho, &n, &f, &x));
    let pow4_l = c.pow4(&l);
    let prod4 = c.fin_sum_prod4_app(&b, &rho, &n, &f, &x);
    // prod4 : pow4_l(≡(Σg·Σg)·(Σg·Σg)) = quad ; symm gives quad = pow4_l.
    let pf = c.symm(pow4_l, quad, prod4);

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, pf);
    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

/// Probe — `gsum_eq_l` : `∀ ρ n F x, Fin.sum (2^n)(gxu x) = subsetSum n (l_int x)`,
/// proven by `Eq.refl` (confirms the subsetSum↔Fin.sum + β def-eq the L5 fold
/// relies on).
fn build_gsum_eq_l_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let g = c.gxu(&b, &rho, &n, &f, &x);
    let g_sum = c.sum_pow(&n, g);
    let l = c.ssum(&n, c.l_int_fn(&b, &rho, &n, &f, &x));
    let concl = c.eq_rat(g_sum, l);

    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, concl);
    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

fn build_gsum_eq_l_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let g = c.gxu(&b, &rho, &n, &f, &x);
    let g_sum = c.sum_pow(&n, g);
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let pf = Expr::apps(eq_refl, [c.rat.clone(), g_sum]);

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, pf);
    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

/// Probe type — `pow4_noisefn_l_eq_m` : `∀ ρ n F (x : HCPoint n), L x = M x`.
/// Standalone harness for the per-x bridge `l_eq_m`.
fn build_l_eq_m_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let l = c.ssum(&n, c.l_int_fn(&b, &rho, &n, &f, &x));
    let m = c.m_form(&b, &rho, &n, &f, &x);
    let concl = c.eq_rat(l, m);

    let ty = b.mk_pi(x_id, BinderInfo::Default, hcp, concl);
    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

fn build_l_eq_m_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let pf = c.l_eq_m(&b, &rho, &n, &f, &x);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, pf);
    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

/// L5 type — `pow4_noisefn_M_form`:
/// `Σ_jx pow4(noiseFn ρ n F jx) = subsetSum n (fun x => pow4 (M x))`,
/// `M x = subsetSum n (fun S => (ρ^|S|·χ_S x)·A F S)`, `A F S = subsetSum n (fun y => F y·χ_S y)`.
fn build_m_form_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    let rhs_fn = m_form_x_fn(c, &b, &rho, &n, &f);
    let rhs = c.ssum(&n, rhs_fn);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

/// `fun (x : HCPoint n) => pow4 (M x)` — the L5 RHS x-integrand.
fn m_form_x_fn(
    c: &Pow4SpectralConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let m = c.m_form(&b, rho, n, f, &x);
    let body = c.pow4(&m);
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

/// L5 value — `Eq.trans (density_unfold ρ n F) (ss_congr over x of fold+bridge)`.
fn build_m_form_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    // E_mid = density_unfold RHS = subsetSum n (unfold_x_fn) = subsetSum n (fun x => quad_rhs(gxu x)).
    let e_mid_fn = c.unfold_x_fn(&b, &rho, &n, &f);
    let e_mid = c.ssum(&n, e_mid_fn.clone());
    // RHS = subsetSum n (fun x => pow4(M x)).
    let rhs_fn = m_form_x_fn(c, &b, &rho, &n, &f);
    let rhs = c.ssum(&n, rhs_fn.clone());

    // leg1 : lhs = e_mid  (density_unfold ρ n F).
    let density = Expr::const_(
        Name::from_string("BoolAnalysis.pow4_noisefn_density_unfold"),
        vec![],
    );
    let leg1 = Expr::apps(density, [rho.clone(), n.clone(), f.clone()]);

    // leg2 : e_mid = rhs  (ss_congr over x of: quad_rhs(gxu x) = pow4(M x)).
    let leg2 = {
        let h = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            // fold : quad_rhs(gxu x) = pow4(L x)  via symm Fin.sum_prod4.
            //   Fin.sum_prod4 (2^n)(g)(g)(g)(g) : (Σg·Σg)·(Σg·Σg) = quad_rhs(g),
            //   and (Σg·Σg)·(Σg·Σg) = pow4(Σg) ≡ pow4(L x) (Σg ≡ L x def-eq). We
            //   state the symm target as pow4(L x) so the trans middle is literally
            //   pow4(L x) (matching `bridge`'s source) — the kernel discharges the
            //   pow4(Σg) ≡ pow4(L) def-eq against `prod4`'s LHS.
            let m = c.m_form(&xb, &rho, &n, &f, &x);
            let l = c.ssum(&n, c.l_int_fn(&xb, &rho, &n, &f, &x));
            let pow4_l = c.pow4(&l);
            let pow4_m = c.pow4(&m);
            let g = c.gxu(&xb, &rho, &n, &f, &x);
            let quad = c.quad_rhs(&xb, &n, &g);
            let prod4 = c.fin_sum_prod4_app(&xb, &rho, &n, &f, &x);
            // prod4 : pow4_l(≡(Σg·Σg)·(Σg·Σg)) = quad ; symm gives quad = pow4_l.
            let fold = c.symm(pow4_l.clone(), quad.clone(), prod4);
            // bridge : pow4(L x) = pow4(M x)  via congrArg pow4 (l_eq_m).
            let l_eq_m = c.l_eq_m(&xb, &rho, &n, &f, &x);
            let bridge = c.pow4_congr(&xb, l.clone(), m.clone(), l_eq_m);
            // chain : quad_rhs = pow4(L) = pow4(M).
            let pf = c.trans(quad, pow4_l, pow4_m.clone(), fold, bridge);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, pf))
        };
        c.ss_congr(&n, &e_mid_fn, &rhs_fn, h)
    };

    let proof = c.trans(lhs, e_mid, rhs, leg1, leg2);
    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

// ════════════════════════════════════════════════════════════════════════════
// L6 — `pow4_noisefn_spectral` : the TOP rung (Form A, §2.1).
//
// From L5 (`Σ_jx pow4(noiseFn) = Σ_x pow4(M x)`) to the §2.1 RHS:
//   subsetSum n (S1 => subsetSum n (S2 => subsetSum n (S3 => subsetSum n (S4 =>
//     ((ρ^|S1|·ρ^|S2|)·(ρ^|S3|·ρ^|S4|))
//      · (((A S1·A S2)·(A S3·A S4)) · subsetSum n (x => (χ_S1 x·χ_S2 x)·(χ_S3 x·χ_S4 x)))))))
//
// Chain (subsetSum convention throughout):
//   E0 = Σ_x pow4(M x).
//   E1 = Σ_x Σ_S1Σ_S2Σ_S3Σ_S4 (T1·T2)·(T3·T4)   [ss_congr x of subsetSum_prod4 (m_fn x)⁴],
//        Tk = (ρ^|Sk|·χ_Sk x)·A(Sk), nested (S1,S3,S2,S4).
//   E2 = Σ_S1Σ_S3Σ_S2Σ_S4 Σ_x (T1·T2)·(T3·T4)   [4 nested subsetSum_swap moving Σ_x in].
//   E3 = §2.1 RHS, nested (S1,S3,S2,S4)            [per-(S1..S4) regroup of Σ_x (T1·T2)·(T3·T4)].
//
// NOTE on nesting order: we keep the (S1,S3,S2,S4) order that `subsetSum_prod4`
// produces, and state the §2.1 target type in THAT order (the build plan's
// "freeze the stated type to the leg order" guidance — a final cosmetic
// canonicalization to (S1,S2,S3,S4) is deferred to the downstream consumer).
// ════════════════════════════════════════════════════════════════════════════

impl Pow4SpectralConsts {
    /// `wk = ρ^|Sk|`, weight at a given subset value `s`.
    fn w_of(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        self.weight(parent, rho, n, s)
    }
    /// `T S x = (ρ^|S|·χ_S x)·A F S` — the M-form term (= `t_term`).
    fn t_of(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s: &Expr,
        x: &Expr,
    ) -> Expr {
        self.t_term(parent, rho, n, f, s, x)
    }
    /// `Σ_x (T1·T2)·(T3·T4)` at fixed S1..S4 — the per-quad inner x-sum (E2 body).
    fn xsum_tt(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let t1 = self.t_of(&xb, rho, n, f, s1, &x);
        let t2 = self.t_of(&xb, rho, n, f, s2, &x);
        let t3 = self.t_of(&xb, rho, n, f, s3, &x);
        let t4 = self.t_of(&xb, rho, n, f, s4, &x);
        let body = self.mul(self.mul(t1, t2), self.mul(t3, t4));
        let g = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }
    /// `Σ_x (χ_S1 x·χ_S2 x)·(χ_S3 x·χ_S4 x)` — the §2.1 explicit inner character
    /// correlation (kept un-collapsed).
    fn xsum_chi4(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let c1 = self.chi_(n, s1, &x);
        let c2 = self.chi_(n, s2, &x);
        let c3 = self.chi_(n, s3, &x);
        let c4 = self.chi_(n, s4, &x);
        let body = self.mul(self.mul(c1, c2), self.mul(c3, c4));
        let g = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }
    /// The §2.1 per-(S1,S2,S3,S4) RHS body:
    /// `((w1·w2)·(w3·w4)) · (((A1·A2)·(A3·A4)) · Σ_x (χ1·χ2)·(χ3·χ4))`.
    fn spectral_body(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let w1 = self.w_of(parent, rho, n, s1);
        let w2 = self.w_of(parent, rho, n, s2);
        let w3 = self.w_of(parent, rho, n, s3);
        let w4 = self.w_of(parent, rho, n, s4);
        let a1 = self.a_coeff(parent, n, f, s1);
        let a2 = self.a_coeff(parent, n, f, s2);
        let a3 = self.a_coeff(parent, n, f, s3);
        let a4 = self.a_coeff(parent, n, f, s4);
        let wblk = self.mul(self.mul(w1, w2), self.mul(w3, w4));
        let ablk = self.mul(self.mul(a1, a2), self.mul(a3, a4));
        let chi4 = self.xsum_chi4(parent, n, s1, s2, s3, s4);
        self.mul(wblk, self.mul(ablk, chi4))
    }
}

/// Which inner body to place at the bottom of the 4-deep S-nesting.
enum SBody {
    /// E1 body: `(T1·T2)·(T3·T4)` at a FIXED outer `x` (carried in the variant).
    TtAtX(Expr),
    /// E2 body: `Σ_x (T1·T2)·(T3·T4)`.
    XsumTt,
    /// §2.1 body: the spectral_body.
    Spectral,
}

impl Pow4SpectralConsts {
    /// `(T1·T2)·(T3·T4)` at fixed `x`, Tk = t_term Sk x.
    fn tt_at_x(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
        x: &Expr,
    ) -> Expr {
        let t1 = self.t_of(parent, rho, n, f, s1, x);
        let t2 = self.t_of(parent, rho, n, f, s2, x);
        let t3 = self.t_of(parent, rho, n, f, s3, x);
        let t4 = self.t_of(parent, rho, n, f, s4, x);
        self.mul(self.mul(t1, t2), self.mul(t3, t4))
    }
    fn s_inner(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
        body: &SBody,
    ) -> Expr {
        match body {
            SBody::TtAtX(x) => self.tt_at_x(parent, rho, n, f, s1, s2, s3, s4, x),
            SBody::XsumTt => self.xsum_tt(parent, rho, n, f, s1, s2, s3, s4),
            SBody::Spectral => self.spectral_body(parent, rho, n, f, s1, s2, s3, s4),
        }
    }
    /// `fun S2 => <inner>` (deepest binder; nesting order has S2 innermost-but-one,
    /// S4 innermost — matching (S1,S3,S2,S4)).
    #[allow(clippy::too_many_arguments)]
    fn s4_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        body: &SBody,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s4_id, s4) = b.fresh_local(hcp.clone());
        let inner = self.s_inner(&b, rho, n, f, s1, s2, s3, &s4, body);
        b.finish_child(b.mk_lam(s4_id, BinderInfo::Default, hcp, inner))
    }
    #[allow(clippy::too_many_arguments)]
    fn s2_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s3: &Expr,
        body: &SBody,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s2_id, s2) = b.fresh_local(hcp.clone());
        let inner = self.s4_fn(&b, rho, n, f, s1, &s2, s3, body);
        b.finish_child(b.mk_lam(s2_id, BinderInfo::Default, hcp, self.ssum(n, inner)))
    }
    fn s3_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        body: &SBody,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s3_id, s3) = b.fresh_local(hcp.clone());
        let inner = self.s2_fn(&b, rho, n, f, s1, &s3, body);
        b.finish_child(b.mk_lam(s3_id, BinderInfo::Default, hcp, self.ssum(n, inner)))
    }
    fn s1_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, body: &SBody) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s1_id, s1) = b.fresh_local(hcp.clone());
        let inner = self.s3_fn(&b, rho, n, f, &s1, body);
        b.finish_child(b.mk_lam(s1_id, BinderInfo::Default, hcp, self.ssum(n, inner)))
    }
    /// `Σ_S1 Σ_S3 Σ_S2 Σ_S4 <body>` — the 4-deep S nesting.
    fn s_nest(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        body: &SBody,
    ) -> Expr {
        self.ssum(n, self.s1_fn(parent, rho, n, f, body))
    }

    /// `Σ_{s_next} … Σ_{s_last} (T1·T2)·(T3·T4)` at fixed `x` — the remaining
    /// peel-order S-nest (after the `|fixed|` already-bound S's) with `TtAtX`
    /// at the bottom. For `fixed = []` this is byte-identical to
    /// `s_nest(TtAtX(x))` (so `a_at([])` matches the E1 RHS).
    fn remaining_s_then_tt(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        fixed: &[Expr],
        x: &Expr,
    ) -> Expr {
        if fixed.len() == 4 {
            let (s1, s3, s2, s4) = (&fixed[0], &fixed[1], &fixed[2], &fixed[3]);
            // peel order [S1,S3,S2,S4] ⇒ tt_at_x args (S1,S2,S3,S4).
            return self.tt_at_x(parent, rho, n, f, s1, s2, s3, s4, x);
        }
        let hcp = self.hcpoint_of(n);
        let lam = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let mut sv = fixed.to_vec();
            sv.push(s.clone());
            let inner = self.remaining_s_then_tt(&b, rho, n, f, &sv, x);
            b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, inner))
        };
        self.ssum(n, lam)
    }
}

impl Pow4SpectralConsts {
    /// E1 = `subsetSum n (fun x => Σ_S1Σ_S3Σ_S2Σ_S4 (T1·T2)·(T3·T4))` — Σ_x outer,
    /// the four S-sums inner (Tk at fixed x). The `subsetSum_prod4` expansion of
    /// `pow4(M x)` summed over x.
    fn e1_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = SBody::TtAtX(x.clone());
        let inner = self.s_nest(&xb, rho, n, f, &body);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, inner))
    }
    fn e1(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        self.ssum(n, self.e1_x_fn(parent, rho, n, f))
    }

    /// leg E0→E1 : `subsetSum_congr` over x of `subsetSum_prod4 n (m_fn x)⁴`.
    ///   subsetSum_prod4 n P P P P : (ΣP·ΣP)·(ΣP·ΣP) = Σ_S1Σ_S3Σ_S2Σ_S4 (P S1·P S2)·(P S3·P S4)
    ///   with P = m_fn x ; LHS = pow4(M x), RHS = TtAtX nesting (m_fn x S ≡ t_term S x).
    fn leg_e0_e1(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        // before x-integrand : fun x => pow4(M x) (= m_form_x_fn body).
        let before = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let m = self.m_form(&xb, rho, n, f, &x);
            let body = self.pow4(&m);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
        };
        let after = self.e1_x_fn(parent, rho, n, f);
        let h = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let p = self.m_fn(&xb, rho, n, f, &x);
            let prod4 = Expr::const_(Name::from_string("BoolAnalysis.subsetSum_prod4"), vec![]);
            let pf = Expr::apps(prod4, [n.clone(), p.clone(), p.clone(), p.clone(), p]);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, pf))
        };
        self.ss_congr(n, &before, &after, h)
    }
}

/// Partial top type — `pow4_noisefn_spectral_e1` (E0→E1 committed milestone):
/// `Σ_jx pow4(noiseFn ρ n F jx) = subsetSum n (fun x => Σ_S1Σ_S3Σ_S2Σ_S4 (T1·T2)·(T3·T4))`.
fn build_spectral_e1_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    let rhs = c.e1(&b, &rho, &n, &f);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

fn build_spectral_e1_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    // E0 = Σ_x pow4(M x) = M_form RHS.
    let e0_fn = m_form_x_fn(c, &b, &rho, &n, &f);
    let e0 = c.ssum(&n, e0_fn);
    let e1 = c.e1(&b, &rho, &n, &f);

    let mform = Expr::const_(
        Name::from_string("BoolAnalysis.pow4_noisefn_M_form"),
        vec![],
    );
    let leg0 = Expr::apps(mform, [rho.clone(), n.clone(), f.clone()]);
    let leg1 = c.leg_e0_e1(&b, &rho, &n, &f);
    let proof = c.trans(lhs, e0, e1, leg0, leg1);

    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

// ════════════════════════════════════════════════════════════════════════════
// E1→E2 Fubini (unified, consistency-by-construction).
//
// `fubini_pull(fixed)` proves `A(fixed) = B(fixed)` where, at a context with the
// `|fixed|` peel-order S-indices already bound:
//   A(fixed) = Σ_x [ Σ_{s_next} … Σ_{s_last} TT(x) ]   (x just inside `fixed`)
//   B(fixed) = Σ_{s_next} … Σ_{s_last} [ Σ_x TT(x) ]   (x fully pulled to bottom)
// The SAME `a_at`/`b_at` builders feed both the `Eq.trans`/`ss_congr` endpoints
// and the swap, so the kernel sees identical term trees.
// ════════════════════════════════════════════════════════════════════════════

impl Pow4SpectralConsts {
    /// `A(fixed)` : `Σ_x [remaining_s_then_tt(fixed, x)]` (x just inside `fixed`).
    fn a_at(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        fixed: &[Expr],
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let inner = self.remaining_s_then_tt(&xb, rho, n, f, fixed, &x);
        let g = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, inner));
        self.ssum(n, g)
    }
    /// `B(fixed)` : `Σ_{s_next} … Σ_{s_last} [Σ_x TT(x)]` — x fully pulled to the
    /// bottom of the remaining S-nest. (= the s_nest tail with `xsum_tt` at base,
    /// over the remaining peel-order indices.)
    fn b_at(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        fixed: &[Expr],
    ) -> Expr {
        if fixed.len() == 4 {
            // no remaining S: just Σ_x TT.
            let (s1, s3, s2, s4) = (&fixed[0], &fixed[1], &fixed[2], &fixed[3]);
            return self.xsum_tt(parent, rho, n, f, s1, s2, s3, s4);
        }
        let hcp = self.hcpoint_of(n);
        let lam = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let mut sv = fixed.to_vec();
            sv.push(s.clone());
            let inner = self.b_at(&sb, rho, n, f, &sv);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, inner))
        };
        self.ssum(n, lam)
    }

    /// Proof `A(fixed) = B(fixed)`.
    fn fubini_pull(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        fixed: &[Expr],
    ) -> Expr {
        if fixed.len() == 4 {
            // A = B = Σ_x TT (x already at the bottom); reflexivity.
            let a = self.a_at(parent, rho, n, f, fixed);
            let eq_refl = Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            );
            return Expr::apps(eq_refl, [self.rat.clone(), a]);
        }
        let hcp = self.hcpoint_of(n);
        // Step 1 (swap): A(fixed) = Σ_x Σ_{s} R = Σ_{s} Σ_x R =: C, via symm(swap).
        //   swap kernel g s x := R(s,x) = remaining_s_then_tt(fixed++[s], x).
        let kernel = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let inner = {
                let mut xb = EnvDeclBuilder::child_of(&sb);
                let (x_id, x) = xb.fresh_local(hcp.clone());
                let mut sv = fixed.to_vec();
                sv.push(s.clone());
                let r = self.remaining_s_then_tt(&xb, rho, n, f, &sv, &x);
                xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), r))
            };
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), inner))
        };
        let swap = self.ss_swap(n, &kernel); // : Σ_s Σ_x R = Σ_x Σ_s R
        let a = self.a_at(parent, rho, n, f, fixed); // Σ_x Σ_s R (x outer)
                                                     // C = Σ_s [Σ_x R]  (s pulled out, x just below it).
        let c = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let inner = {
                let mut xb = EnvDeclBuilder::child_of(&sb);
                let (x_id, x) = xb.fresh_local(hcp.clone());
                let mut sv = fixed.to_vec();
                sv.push(s.clone());
                let r = self.remaining_s_then_tt(&xb, rho, n, f, &sv, &x);
                xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), r))
            };
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), self.ssum(n, inner)))
        };
        let c_sum = self.ssum(n, c);
        // swap : C = A ; symm(A, C, swap)?  swap : (Σ_s Σ_x)=(Σ_x Σ_s)=A. So swap : C = A.
        let step1 = self.symm(c_sum.clone(), a.clone(), swap); // : A = C
                                                               // Step 2 (recurse under ss_congr over s): C = B(fixed).
                                                               //   B(fixed) = Σ_s [B(fixed++[s])] ; C = Σ_s [A(fixed++[s])].
                                                               //   per-s : A(fixed++[s]) = B(fixed++[s])  (recursion).
        let before_s = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let mut sv = fixed.to_vec();
            sv.push(s.clone());
            let inner = self.a_at(&sb, rho, n, f, &sv);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), inner))
        };
        let after_s = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let mut sv = fixed.to_vec();
            sv.push(s.clone());
            let inner = self.b_at(&sb, rho, n, f, &sv);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), inner))
        };
        let h = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let mut sv = fixed.to_vec();
            sv.push(s.clone());
            let pf = self.fubini_pull(&sb, rho, n, f, &sv);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), pf))
        };
        let step2 = self.ss_congr(n, &before_s, &after_s, h); // : C = B
        let b = self.b_at(parent, rho, n, f, fixed);
        self.trans(a, c_sum, b, step1, step2)
    }
}

/// Probe — `pow4_noisefn_spectral_e2` : `Σ_jx pow4(noiseFn) = E2`
/// (E2 = Σ_S1Σ_S3Σ_S2Σ_S4 Σ_x (T1·T2)·(T3·T4)). Chains E1 then the Fubini pull.
fn build_spectral_e2_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    let rhs = c.b_at(&b, &rho, &n, &f, &[]);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

fn build_spectral_e2_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    // E1 = A([]) = Σ_x [Σ_S1Σ_S3Σ_S2Σ_S4 TT].
    let e1 = c.a_at(&b, &rho, &n, &f, &[]);
    let e2 = c.b_at(&b, &rho, &n, &f, &[]);
    let e1_thm = Expr::const_(
        Name::from_string("BoolAnalysis.pow4_noisefn_spectral_e1"),
        vec![],
    );
    let leg_to_e1 = Expr::apps(e1_thm, [rho.clone(), n.clone(), f.clone()]);
    let fubini = c.fubini_pull(&b, &rho, &n, &f, &[]);
    let proof = c.trans(lhs, e1, e2, leg_to_e1, fubini);

    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

// ════════════════════════════════════════════════════════════════════════════
// E2→E3 — the per-quad regroup to §2.1 Form A (the final rung).
//
// Per (S1,S3,S2,S4): `Σ_x (T1·T2)·(T3·T4) = spectral_body`, Tk = (wk·χk)·Ak.
//   • per-x: Tk = Uk·χk (Uk := wk·Ak, x-independent); mul8_regroup gives
//       (T1·T2)·(T3·T4) = ((U1·χ1)·(U2·χ2))·((U3·χ3)·(U4·χ4))
//                       = ((U1·U2)·(U3·U4))·((χ1·χ2)·(χ3·χ4)) = Ublk·χ4(x).
//   • subsetSum_smul: Σ_x Ublk·χ4(x) = Ublk·Σ_x χ4 (Ublk x-independent).
//   • mul8_regroup again: Ublk = (w1·A1)(w2·A2)·… = ((w1·w2)(w3·w4))·((A1·A2)(A3·A4))
//                               = wblk·ablk.
//   • mul_assoc: (wblk·ablk)·Σχ = wblk·(ablk·Σχ) = spectral_body.
// ════════════════════════════════════════════════════════════════════════════

impl Pow4SpectralConsts {
    fn mul8(
        &self,
        w1: Expr,
        w2: Expr,
        w3: Expr,
        w4: Expr,
        g1: Expr,
        g2: Expr,
        g3: Expr,
        g4: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul8_regroup"), vec![]),
            [w1, w2, w3, w4, g1, g2, g3, g4],
        )
    }
    /// `Uk = wk·Ak` — the x-independent part of `Tk`.
    fn u_of(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let w = self.weight(parent, rho, n, s);
        let a = self.a_coeff(parent, n, f, s);
        self.mul(w, a)
    }
    /// per-x `Tk = (wk·χk)·Ak = Uk·χk`  (assoc + comm + assoc = mul_left_comm-style).
    ///   (wk·χk)·Ak =[assoc] wk·(χk·Ak) =[congr wk·(comm χk Ak)] wk·(Ak·χk)
    ///             =[symm assoc] (wk·Ak)·χk.
    fn t_to_uchi(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s: &Expr,
        x: &Expr,
    ) -> Expr {
        let w = self.weight(parent, rho, n, s);
        let chi = self.chi_(n, s, x);
        let a = self.a_coeff(parent, n, f, s);
        let wchi = self.mul(w.clone(), chi.clone());
        // leg1 : (w·χ)·A = w·(χ·A)   (mul_assoc w χ A).
        let leg1 = self.mul_assoc(w.clone(), chi.clone(), a.clone());
        // leg2 : w·(χ·A) = w·(A·χ)   (congr (w·) (mul_comm χ A)).
        let chi_a = self.mul(chi.clone(), a.clone());
        let a_chi = self.mul(a.clone(), chi.clone());
        let comm = self.mul_comm(chi.clone(), a.clone());
        let leg2 = self.mul_left_congr(parent, &w, chi_a.clone(), a_chi.clone(), comm);
        // leg3 : w·(A·χ) = (w·A)·χ   (symm mul_assoc w A χ).
        let wa = self.mul(w.clone(), a.clone());
        let assoc3 = self.mul_assoc(w.clone(), a.clone(), chi.clone());
        let leg3 = self.symm(
            self.mul(wa.clone(), chi.clone()),
            self.mul(w.clone(), a_chi.clone()),
            assoc3,
        );
        // chain: (w·χ)·A = w·(χ·A) = w·(A·χ) = (w·A)·χ.
        let lhs = self.mul(wchi.clone(), a.clone());
        let m1 = self.mul(w.clone(), chi_a);
        let m2 = self.mul(w.clone(), a_chi);
        let rhs = self.mul(wa, chi);
        self.trans3(lhs, m1, m2, rhs, leg1, leg2, leg3)
    }

    /// per-x : `(T1·T2)·(T3·T4) = Ublk·((χ1·χ2)·(χ3·χ4))`.
    ///   • congr each Tk → Uk·χk under the (·)·(·)·(·)·(·) shape (4 congr legs);
    ///   • mul8_regroup U1 U2 U3 U4 χ1 χ2 χ3 χ4.
    fn perx_tt_to_ublk(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
        x: &Expr,
    ) -> Expr {
        // Tk and Uk·χk.
        let t1 = self.t_of(parent, rho, n, f, s1, x);
        let t2 = self.t_of(parent, rho, n, f, s2, x);
        let t3 = self.t_of(parent, rho, n, f, s3, x);
        let t4 = self.t_of(parent, rho, n, f, s4, x);
        let u1 = self.u_of(parent, rho, n, f, s1);
        let u2 = self.u_of(parent, rho, n, f, s2);
        let u3 = self.u_of(parent, rho, n, f, s3);
        let u4 = self.u_of(parent, rho, n, f, s4);
        let c1 = self.chi_(n, s1, x);
        let c2 = self.chi_(n, s2, x);
        let c3 = self.chi_(n, s3, x);
        let c4 = self.chi_(n, s4, x);
        let uc1 = self.mul(u1.clone(), c1.clone());
        let uc2 = self.mul(u2.clone(), c2.clone());
        let uc3 = self.mul(u3.clone(), c3.clone());
        let uc4 = self.mul(u4.clone(), c4.clone());
        // pf_k : Tk = Uk·χk.
        let p1 = self.t_to_uchi(parent, rho, n, f, s1, x);
        let p2 = self.t_to_uchi(parent, rho, n, f, s2, x);
        let p3 = self.t_to_uchi(parent, rho, n, f, s3, x);
        let p4 = self.t_to_uchi(parent, rho, n, f, s4, x);
        // Rewrite (T1·T2)·(T3·T4) → ((U1χ1)·(U2χ2))·((U3χ3)·(U4χ4)) by congr on each Tk.
        // Use congrArg with a 2-hole motive realized as 4 successive single-hole congrs.
        // Step a: T1 → U1χ1 under (· ·T2)·(T3·T4): congr (fun z => (z·T2)·(T3·T4)) p1.
        let e0 = self.mul(
            self.mul(t1.clone(), t2.clone()),
            self.mul(t3.clone(), t4.clone()),
        );
        let ea = self.mul(
            self.mul(uc1.clone(), t2.clone()),
            self.mul(t3.clone(), t4.clone()),
        );
        let mot_a = self.hole_motive(parent, |z| {
            self.mul(self.mul(z, t2.clone()), self.mul(t3.clone(), t4.clone()))
        });
        let la = self.congr(t1.clone(), uc1.clone(), mot_a, p1);
        let eb = self.mul(
            self.mul(uc1.clone(), uc2.clone()),
            self.mul(t3.clone(), t4.clone()),
        );
        let mot_b = self.hole_motive(parent, |z| {
            self.mul(self.mul(uc1.clone(), z), self.mul(t3.clone(), t4.clone()))
        });
        let lb = self.congr(t2.clone(), uc2.clone(), mot_b, p2);
        let ec = self.mul(
            self.mul(uc1.clone(), uc2.clone()),
            self.mul(uc3.clone(), t4.clone()),
        );
        let mot_c = self.hole_motive(parent, |z| {
            self.mul(self.mul(uc1.clone(), uc2.clone()), self.mul(z, t4.clone()))
        });
        let lc = self.congr(t3.clone(), uc3.clone(), mot_c, p3);
        let ed = self.mul(
            self.mul(uc1.clone(), uc2.clone()),
            self.mul(uc3.clone(), uc4.clone()),
        );
        let mot_d = self.hole_motive(parent, |z| {
            self.mul(self.mul(uc1.clone(), uc2.clone()), self.mul(uc3.clone(), z))
        });
        let ld = self.congr(t4.clone(), uc4.clone(), mot_d, p4);
        // chain e0 = ea = eb = ec = ed.
        let t_a = self.trans(e0.clone(), ea.clone(), eb.clone(), la, lb);
        let t_b = self.trans(e0.clone(), eb.clone(), ec.clone(), t_a, lc);
        let congr_all = self.trans(e0.clone(), ec.clone(), ed.clone(), t_b, ld);
        // mul8 : ((U1·χ1)·(U2·χ2))·((U3·χ3)·(U4·χ4)) = ((U1·U2)·(U3·U4))·((χ1·χ2)·(χ3·χ4)).
        let mul8 = self.mul8(
            u1.clone(),
            u2.clone(),
            u3.clone(),
            u4.clone(),
            c1.clone(),
            c2.clone(),
            c3.clone(),
            c4.clone(),
        );
        let ublk = self.mul(self.mul(u1, u2), self.mul(u3, u4));
        let chi4 = self.mul(self.mul(c1, c2), self.mul(c3, c4));
        let rhs_mul8 = self.mul(ublk, chi4);
        self.trans(e0, ed, rhs_mul8, congr_all, mul8)
    }

    /// Build `fun (z : Rat) => body(z)` via a Rust closure (single-hole motive).
    fn hole_motive<G: Fn(Expr) -> Expr>(&self, parent: &EnvDeclBuilder, g: G) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = b.fresh_local(self.rat.clone());
        let body = g(z);
        b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

impl Pow4SpectralConsts {
    /// `fun (x : HCPoint n) => Ublk·((χ1·χ2)·(χ3·χ4))` — the smul integrand for the
    /// per-quad x-sum (Ublk constant in x).
    #[allow(clippy::too_many_arguments)]
    fn ublk_chi4_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
        ublk: &Expr,
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let c1 = self.chi_(n, s1, &x);
        let c2 = self.chi_(n, s2, &x);
        let c3 = self.chi_(n, s3, &x);
        let c4 = self.chi_(n, s4, &x);
        let chi4 = self.mul(self.mul(c1, c2), self.mul(c3, c4));
        let body = self.mul(ublk.clone(), chi4);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => (χ1·χ2)·(χ3·χ4)` — the bare χ4 integrand.
    fn chi4_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let c1 = self.chi_(n, s1, &x);
        let c2 = self.chi_(n, s2, &x);
        let c3 = self.chi_(n, s3, &x);
        let c4 = self.chi_(n, s4, &x);
        let body = self.mul(self.mul(c1, c2), self.mul(c3, c4));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => (T1·T2)·(T3·T4)` — the E2 per-quad x-integrand.
    #[allow(clippy::too_many_arguments)]
    fn tt_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.tt_at_x(&xb, rho, n, f, s1, s2, s3, s4, &x);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// Per-quad regroup proof `Σ_x (T1·T2)·(T3·T4) = spectral_body`.
    #[allow(clippy::too_many_arguments)]
    fn perquad_regroup(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let w1 = self.weight(parent, rho, n, s1);
        let w2 = self.weight(parent, rho, n, s2);
        let w3 = self.weight(parent, rho, n, s3);
        let w4 = self.weight(parent, rho, n, s4);
        let a1 = self.a_coeff(parent, n, f, s1);
        let a2 = self.a_coeff(parent, n, f, s2);
        let a3 = self.a_coeff(parent, n, f, s3);
        let a4 = self.a_coeff(parent, n, f, s4);
        let u1 = self.mul(w1.clone(), a1.clone());
        let u2 = self.mul(w2.clone(), a2.clone());
        let u3 = self.mul(w3.clone(), a3.clone());
        let u4 = self.mul(w4.clone(), a4.clone());
        let ublk = self.mul(self.mul(u1, u2), self.mul(u3, u4));
        let wblk = self.mul(
            self.mul(w1.clone(), w2.clone()),
            self.mul(w3.clone(), w4.clone()),
        );
        let ablk = self.mul(
            self.mul(a1.clone(), a2.clone()),
            self.mul(a3.clone(), a4.clone()),
        );

        let e2_x = self.ssum(n, self.tt_fn(parent, rho, n, f, s1, s2, s3, s4)); // Σ_x (T1·T2)·(T3·T4)
        let mid1 = self.ssum(
            n,
            self.ublk_chi4_fn(parent, rho, n, f, s1, s2, s3, s4, &ublk),
        ); // Σ_x Ublk·χ4
        let sx_chi4 = self.ssum(n, self.chi4_fn(parent, n, s1, s2, s3, s4)); // Σ_x χ4
        let ublk_sx = self.mul(ublk.clone(), sx_chi4.clone()); // Ublk·Σχ
        let wa_sx = self.mul(self.mul(wblk.clone(), ablk.clone()), sx_chi4.clone()); // (wblk·ablk)·Σχ
        let spectral = self.mul(wblk.clone(), self.mul(ablk.clone(), sx_chi4.clone())); // wblk·(ablk·Σχ)

        // leg1 : Σ_x (T1·T2)·(T3·T4) = Σ_x Ublk·χ4  (ss_congr over x of perx_tt_to_ublk).
        let h = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let pf = self.perx_tt_to_ublk(&xb, rho, n, f, s1, s2, s3, s4, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, pf))
        };
        let leg1 = self.ss_congr(
            n,
            &self.tt_fn(parent, rho, n, f, s1, s2, s3, s4),
            &self.ublk_chi4_fn(parent, rho, n, f, s1, s2, s3, s4, &ublk),
            h,
        );
        // leg2 : Σ_x Ublk·χ4 = Ublk·Σ_x χ4  (subsetSum_smul n Ublk chi4_fn).
        let chi4_fn = self.chi4_fn(parent, n, s1, s2, s3, s4);
        let leg2 = self.ss_smul(n, &ublk, &chi4_fn);
        // leg3 : Ublk·Σχ = (wblk·ablk)·Σχ  (congr (·Σχ) (mul8 w1..w4 A1..A4 : Ublk = wblk·ablk)).
        let mul8 = self.mul8(w1, w2, w3, w4, a1, a2, a3, a4);
        let mot = {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = bb.fresh_local(self.rat.clone());
            let body = self.mul(z, sx_chi4.clone());
            bb.finish_child(bb.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let wblk_ablk = self.mul(wblk.clone(), ablk.clone());
        let leg3 = self.congr(ublk.clone(), wblk_ablk.clone(), mot, mul8);
        // leg4 : (wblk·ablk)·Σχ = wblk·(ablk·Σχ)  (mul_assoc wblk ablk Σχ).
        let leg4 = self.mul_assoc(wblk, ablk, sx_chi4);

        // chain: E2_x = Σ Ublk·χ4 = Ublk·Σχ = (wblk·ablk)·Σχ = wblk·(ablk·Σχ).
        let t1 = self.trans(e2_x.clone(), mid1.clone(), ublk_sx.clone(), leg1, leg2);
        let t2 = self.trans(e2_x.clone(), ublk_sx.clone(), wa_sx.clone(), t1, leg3);
        self.trans(e2_x, wa_sx, spectral, t2, leg4)
    }
}

impl Pow4SpectralConsts {
    /// E2→E3 leg: `ss_congr` 4-deep over (S1,S3,S2,S4) of `perquad_regroup`
    /// (`Σ_x TT = spectral_body`), turning E2 = s_nest(XsumTt) into
    /// E3 = s_nest(Spectral). `svals` carries the bound S-values in peel order.
    fn leg_e2_e3(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        svals: &[Expr],
    ) -> Expr {
        if svals.len() == 4 {
            // peel order [S1,S3,S2,S4] ⇒ perquad args (S1,S2,S3,S4).
            let (s1, s3, s2, s4) = (&svals[0], &svals[1], &svals[2], &svals[3]);
            return self.perquad_regroup(parent, rho, n, f, s1, s2, s3, s4);
        }
        let hcp = self.hcpoint_of(n);
        // before/after S-integrands at this level (the s_nest tail with the two bodies).
        let before = self.s_tail_fn(parent, rho, n, f, svals, &SBody::XsumTt);
        let after = self.s_tail_fn(parent, rho, n, f, svals, &SBody::Spectral);
        let h = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let mut sv = svals.to_vec();
            sv.push(s.clone());
            let pf = self.leg_e2_e3(&sb, rho, n, f, &sv);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, pf))
        };
        self.ss_congr(n, &before, &after, h)
    }

    /// `fun s => <remaining s_nest tail with `body` at the bottom>` — the
    /// integrand of the level-`|svals|` `subsetSum` in the (S1,S3,S2,S4) nesting.
    fn s_tail_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        svals: &[Expr],
        body: &SBody,
    ) -> Expr {
        let hcp = self.hcpoint_of(n);
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let mut sv = svals.to_vec();
        sv.push(s.clone());
        let inner = self.s_tail_body(&sb, rho, n, f, &sv, body);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, inner))
    }
    /// The body at depth `|sv|`: if all 4 bound, emit `body`; else `Σ_s' tail`.
    fn s_tail_body(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        sv: &[Expr],
        body: &SBody,
    ) -> Expr {
        if sv.len() == 4 {
            let (s1, s3, s2, s4) = (&sv[0], &sv[1], &sv[2], &sv[3]);
            return self.s_inner(parent, rho, n, f, s1, s2, s3, s4, body);
        }
        self.ssum(n, self.s_tail_fn(parent, rho, n, f, sv, body))
    }
}

/// §2.1 top type — `pow4_noisefn_spectral` (Form A).
fn build_spectral_type(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    let rhs = c.s_nest(&b, &rho, &n, &f, &SBody::Spectral);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

fn build_spectral_value(c: &Pow4SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.sum_pow(&n, c.lhs_jx_fn(&b, &rho, &n, &f));
    let e2 = c.b_at(&b, &rho, &n, &f, &[]); // E2 = s-nest(XsumTt) (= b_at([])).
    let e3 = c.s_nest(&b, &rho, &n, &f, &SBody::Spectral); // §2.1 RHS.

    let e2_thm = Expr::const_(
        Name::from_string("BoolAnalysis.pow4_noisefn_spectral_e2"),
        vec![],
    );
    let leg_to_e2 = Expr::apps(e2_thm, [rho.clone(), n.clone(), f.clone()]);
    let leg_e2_e3 = c.leg_e2_e3(&b, &rho, &n, &f, &[]);
    let proof = c.trans(lhs, e2, e3, leg_to_e2, leg_e2_e3);

    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}
