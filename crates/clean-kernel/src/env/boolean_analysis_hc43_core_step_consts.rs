// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Cached constants + smart-constructors + the leaf-hypothesis (`h_cm`, `h_tp`)
// type builders for `BoolAnalysis.hc43_core_step`. `include!`d into
// `boolean_analysis_hc43_core_step.rs`. No new globals.

/// Plumbing for the `(4/3,4)` induction-step proof term. Wraps the shared
/// `Hc43Consts` (statement surface) with the extra step-only constructors
/// (`gPart`/`liftH`, the `finSum_ofRat`/`finSum_le`/`finSum_cube_split` bridges,
/// the `cube_superadd`/`norm43_card_succ` closers).
pub(super) struct Hc43StepConsts {
    pub(super) o: Hc43Consts,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl Hc43StepConsts {
    pub(super) fn new() -> Self {
        Self {
            o: Hc43Consts::new(),
        }
    }

    // ── atoms ────────────────────────────────────────────────────────────────
    pub(super) fn nat(&self) -> Expr {
        self.o.nat.clone()
    }
    pub(super) fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    pub(super) fn nnreal(&self) -> Expr {
        self.o.nnreal.clone()
    }
    pub(super) fn succ(&self, n: &Expr) -> Expr {
        self.o.succ(n)
    }
    pub(super) fn pow2(&self, n: &Expr) -> Expr {
        self.o.pow2(n)
    }
    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        self.o.fin_of(n)
    }
    pub(super) fn f_type(&self, n: &Expr) -> Expr {
        self.o.f_type(n)
    }

    // ── gPart / liftH (the folded even/odd legs) ─────────────────────────────
    pub(super) fn g_part_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.gPart"), vec![]),
            [n.clone(), f.clone()],
        )
    }
    pub(super) fn lift_h_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.liftH"), vec![]),
            [n.clone(), f.clone()],
        )
    }

    // ── NNReal helpers (forwarded) ───────────────────────────────────────────
    pub(super) fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.nnle(a, b)
    }
    pub(super) fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.nnadd(a, b)
    }
    pub(super) fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.nnmul(a, b)
    }
    /// `(t·t)·t` — the left-nested NNReal cube.
    pub(super) fn nncube(&self, t: &Expr) -> Expr {
        self.o.nnmul(&self.o.nnmul(t, t), t)
    }
    pub(super) fn ofrat(&self, x: &Expr, hx: &Expr) -> Expr {
        self.o.ofrat(x, hx)
    }
    pub(super) fn finsum(&self, m: &Expr, f: &Expr) -> Expr {
        self.o.finsum(m, f)
    }
    pub(super) fn pow4n(&self, n: &Expr) -> Expr {
        self.o.pow4n(n)
    }
    pub(super) fn four_rat(&self) -> Expr {
        self.o.four_rat()
    }
    #[cfg(test)]
    pub(super) fn contribution(&self, f: &Expr, s: &Expr, r: &Expr, hs: &Expr, x: &Expr) -> Expr {
        self.o.contribution(f, s, r, hs, x)
    }
    pub(super) fn norm43_cubed_app(
        &self,
        n: &Expr,
        f: &Expr,
        s: &Expr,
        r: &Expr,
        hs: &Expr,
    ) -> Expr {
        self.o.norm43_cubed_app(n, f, s, r, hs)
    }

    // ── Eq.{1} plumbing over NNReal (forwarded) ──────────────────────────────
    pub(super) fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.eq_nn(a, b)
    }
    pub(super) fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        self.o.trans_nn(a, b, cc, h1, h2)
    }
    pub(super) fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        self.o.symm_nn(a, b, h)
    }
    pub(super) fn congr_arg_nn(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        self.o.congr_arg_nn(from, to, f, h)
    }
    pub(super) fn subst_nn_prop(
        &self,
        motive: Expr,
        a: &Expr,
        b: &Expr,
        h_eq: Expr,
        h: Expr,
    ) -> Expr {
        self.o.subst_nn_prop(motive, a, b, h_eq, h)
    }

    // ── NNReal order/transitivity leaves (landed) ────────────────────────────
    /// `NNReal.le.trans a b c hab hbc : NNReal.le a c`.
    #[cfg(test)]
    pub(super) fn nnle_trans(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.le.trans"), vec![]),
            [a.clone(), b.clone(), cc.clone(), hab, hbc],
        )
    }
    /// `NNReal.le.refl a : NNReal.le a a`.
    #[cfg(test)]
    pub(super) fn nnle_refl(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("NNReal.le.refl"), vec![]),
            a.clone(),
        )
    }
    /// `NNReal.add_le_add a b c d hab hcd : add a c ≤ add b d`.
    #[cfg(test)]
    pub(super) fn add_le_add(
        &self,
        a: &Expr,
        b: &Expr,
        cc: &Expr,
        d: &Expr,
        hab: Expr,
        hcd: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.add_le_add"), vec![]),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `NNReal.mul_le_mul a b c d hab hcd : mul a c ≤ mul b d`.
    #[cfg(test)]
    pub(super) fn mul_le_mul(
        &self,
        a: &Expr,
        b: &Expr,
        cc: &Expr,
        d: &Expr,
        hab: Expr,
        hcd: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.mul_le_mul"), vec![]),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }

    // ── finSum bridges (landed) ──────────────────────────────────────────────
    /// `NNReal.finSum_le n f g h : finSum n f ≤ finSum n g`.
    #[cfg(test)]
    pub(super) fn finsum_le(&self, n: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.finSum_le"), vec![]),
            [n.clone(), f.clone(), g.clone(), h],
        )
    }
    /// `NNReal.finSum_add n f g : finSum n (f+g) = finSum n f + finSum n g`.
    pub(super) fn finsum_add(&self, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.finSum_add"), vec![]),
            [n.clone(), f.clone(), g.clone()],
        )
    }
    /// `NNReal.finSum_congr n f g h : finSum n f = finSum n g`.
    #[cfg(test)]
    pub(super) fn finsum_congr(&self, n: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.finSum_congr"), vec![]),
            [n.clone(), f.clone(), g.clone(), h],
        )
    }
    /// `NNReal.finSum_ofRat n g hg hsum : finSum n (ofRat∘g) = ofRat (Fin.sum n g)`.
    pub(super) fn finsum_ofrat(&self, n: &Expr, g: &Expr, hg: &Expr, hsum: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.finSum_ofRat"), vec![]),
            [n.clone(), g.clone(), hg.clone(), hsum.clone()],
        )
    }

    // ── Rat-level split / noiseFn leaves (landed) ────────────────────────────
    /// `BoolAnalysis.finSumPow2SuccSplit n F`.
    pub(super) fn pow2_split(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.finSumPow2SuccSplit"),
                vec![],
            ),
            [n.clone(), f.clone()],
        )
    }
    /// `BoolAnalysis.noiseFn_succ_low ρ n F k`.
    pub(super) fn nf_succ_low(&self, rho: &Expr, n: &Expr, f: &Expr, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseFn_succ_low"), vec![]),
            [rho.clone(), n.clone(), f.clone(), k.clone()],
        )
    }
    /// `BoolAnalysis.noiseFn_succ_high ρ n F k`.
    pub(super) fn nf_succ_high(&self, rho: &Expr, n: &Expr, f: &Expr, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseFn_succ_high"), vec![]),
            [rho.clone(), n.clone(), f.clone(), k.clone()],
        )
    }
    /// `BoolAnalysis.norm43_card_succ m Φ : finSum (m+1) Φ = finSum m (Φ∘castSucc) + Φ(last m)`.
    #[cfg(test)]
    pub(super) fn norm43_card_succ(&self, m: &Expr, phi: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.norm43_card_succ"), vec![]),
            [m.clone(), phi.clone()],
        )
    }
    /// `BoolAnalysis.finSum_cube_split n A B`.
    #[cfg(test)]
    pub(super) fn finsum_cube_split(&self, n: &Expr, a: &Expr, bv: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.finSum_cube_split"), vec![]),
            [n.clone(), a.clone(), bv.clone()],
        )
    }
    /// `NNReal.cube_superadd u v : u³ + v³ ≤ (u+v)³`.
    #[cfg(test)]
    pub(super) fn cube_superadd(&self, u: &Expr, v: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.cube_superadd"), vec![]),
            [u.clone(), v.clone()],
        )
    }

    // ── Rat-level Fin.sum surface (for the S1 noiseFn split) ─────────────────
    /// `Fin.sum n f`.
    pub(super) fn fin_sum(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum"), vec![]),
            [n.clone(), f.clone()],
        )
    }
    /// `Fin.sum_congr n f g h : Fin.sum n f = Fin.sum n g`.
    pub(super) fn fin_sum_congr(&self, n: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            [n.clone(), f.clone(), g.clone(), h],
        )
    }
    /// `Rat.add a b`.
    pub(super) fn rat_add(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.rat_add(a, b)
    }
    /// `Rat.sub a b`.
    pub(super) fn rat_sub(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.rat_sub(a, b)
    }
    /// `Rat.mul a b`.
    pub(super) fn rmul(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.rmul(a, b)
    }
    /// `pow4 x := (x·x)·(x·x)`.
    pub(super) fn pow4(&self, x: &Expr) -> Expr {
        self.o.pow4(x)
    }
    pub(super) fn rle(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.rle(a, b)
    }
    pub(super) fn rat_zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    pub(super) fn noise_fn(&self, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        self.o.noise_fn(rho, n, f, jx)
    }
    #[cfg(test)]
    pub(super) fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        self.o.decode(n, k)
    }
    #[cfg(test)]
    pub(super) fn eq_rat(&self, a: &Expr, b: &Expr) -> Expr {
        self.o.eq_rat(a, b)
    }
    pub(super) fn trans_rat(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        self.o.trans_rat(a, b, cc, h1, h2)
    }
    #[cfg(test)]
    pub(super) fn symm_rat(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        self.o.symm_rat(a, b, h)
    }
    pub(super) fn congr_arg_rat(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        self.o.congr_arg_rat(from, to, f, h)
    }

    // ── Rat nonneg leaves (for the ofRat lift witnesses) ─────────────────────
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    pub(super) fn sq_nonneg(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
            a.clone(),
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    pub(super) fn mul_nonneg(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a.clone(), b.clone(), ha, hb],
        )
    }
    /// `0 ≤ pow4 x` — `pow4 x = (x·x)·(x·x)`, so `mul_nonneg (sq_nonneg x)(sq_nonneg x)`.
    pub(super) fn pow4_nonneg(&self, x: &Expr) -> Expr {
        let xx = self.rmul(x, x);
        self.mul_nonneg(&xx, &xx, self.sq_nonneg(x), self.sq_nonneg(x))
    }
    /// `Fin.sum_nonneg n f h : 0 ≤ Fin.sum n f`.
    pub(super) fn fin_sum_nonneg(&self, n: &Expr, f: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]),
            [n.clone(), f.clone(), h],
        )
    }
    /// `NNReal.finSum_ofRat`-style consts already added above; here the inverse
    /// `Fin.sum_add n f g : Fin.sum n (fun i => f i + g i) = Fin.sum n f + Fin.sum n g`.
    #[cfg(test)]
    pub(super) fn fin_sum_add(&self, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            [n.clone(), f.clone(), g.clone()],
        )
    }
    /// `NNReal.ofRat_add a b ha hb hab : ofRat a ha + ofRat b hb = ofRat (a+b) hab`.
    pub(super) fn ofrat_add(&self, a: &Expr, bv: &Expr, ha: &Expr, hb: &Expr, hab: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.ofRat_add"), vec![]),
            [a.clone(), bv.clone(), ha.clone(), hb.clone(), hab.clone()],
        )
    }
    /// `NNReal.finSum_ofRat n g hg hsum` (already added; re-exposed for symmetry).
    pub(super) fn l1(&self) -> crate::level::Level {
        self.o.l1.clone()
    }
    /// `ofRat a ha = ofRat b hb` from `h : a = b` — proof-irrelevant transport of
    /// `NNReal.ofRat`'s dependent nonneg arg via `Eq.ndrec` (replicates the base
    /// proof's `ofrat_transport`; no new global).
    pub(super) fn ofrat_transport(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        ha: &Expr,
        hb: &Expr,
        h: Expr,
    ) -> Expr {
        let le0 = |w: &Expr| self.rle(&self.rat_zero(), w);
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.rat());
            let inner = {
                let mut d2 = EnvDeclBuilder::child_of(&d);
                let (hw_id, hw) = d2.fresh_local(le0(&w));
                let body = self.eq_nn(&self.ofrat(a, ha), &self.ofrat(&w, &hw));
                d2.finish_child(d2.mk_pi(hw_id, BinderInfo::Default, le0(&w), body))
            };
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat(), inner))
        };
        let base = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (hw_id, _hw) = d.fresh_local(le0(a));
            let refl = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![self.l1()]),
                [self.nnreal(), self.ofrat(a, ha)],
            );
            d.finish_child(d.mk_lam(hw_id, BinderInfo::Default, le0(a), refl))
        };
        let ndrec = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.ndrec"),
                vec![crate::level::Level::zero(), self.l1()],
            ),
            [self.rat(), a.clone(), motive, base, b.clone(), h],
        );
        Expr::app(ndrec, hb.clone())
    }
    /// `@congrArg Rat NNReal from to f h`.
    #[cfg(test)]
    pub(super) fn congr_arg_rat_nn(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![self.l1(), self.l1()]),
            [self.rat(), self.nnreal(), from.clone(), to.clone(), f, h],
        )
    }
}
