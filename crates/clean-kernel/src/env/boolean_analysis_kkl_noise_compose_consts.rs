// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose.rs — the `ComposeConsts` term
// atoms / helpers (cube, chi, popcount, A-coeff, the consumed-lemma applicators,
// the congr-motive builders). Split out only for the 500-line-per-file
// convention; not a standalone module.

impl ComposeConsts {
    pub(super) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            pow_nat: k("Rat.powNat"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            chi: k("BoolAnalysis.chi"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            eigen: k("BoolAnalysis.noiseDensity_apply_chi_eigen"),
            semigroup_third: k("BoolAnalysis.noise_semigroup_third"),
            self_adjoint_sq: k("BoolAnalysis.noise_self_adjoint_sq"),
            two_norm_eq_pairing: k("BoolAnalysis.noise_two_norm_eq_pairing"),
            noise_op: k("BoolAnalysis.noiseOp"),
            bool_: k("Bool"),
            fin_sum_nat: k("Fin.sumNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_swap: k("BoolAnalysis.subsetSum_swap"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_congr: k("Fin.sum_congr"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one_nat())
    }
    pub(super) fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `cube n := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1` — the `2^n` numeral the
    /// eigen lemma / chi bricks produce.
    pub(super) fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    pub(super) fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    pub(super) fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    pub(super) fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    pub(super) fn fsum(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, g])
    }
    pub(super) fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    pub(super) fn pow(&self, rho: &Expr, kk: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [rho.clone(), kk.clone()])
    }
    pub(super) fn set_size(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    pub(super) fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    /// `noiseDensityW ρ n a b`.
    pub(super) fn dens(&self, rho: &Expr, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), a.clone(), b.clone()],
        )
    }
    pub(super) fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    pub(super) fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    pub(super) fn symm(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), l, r, h])
    }
    /// `@congrArg.{1,1} Rat Rat from to motive h : motive from = motive to`.
    pub(super) fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `subsetSum_congr n G H hyp : subsetSum n G = subsetSum n H`.
    pub(super) fn ss_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    /// `subsetSum_smul n cc f : subsetSum n (fun S => cc·f S) = cc·subsetSum n f`.
    pub(super) fn ss_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum_smul.clone(),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    /// `subsetSum_swap n f : Σ_S Σ_z f S z = Σ_z Σ_S f S z`
    /// for `f : HCPoint n → HCPoint n → Rat`.
    pub(super) fn ss_swap(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.subset_sum_swap.clone(), [n.clone(), f.clone()])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    pub(super) fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    pub(super) fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `Fin.sum_congr m f g h : Σ_m f = Σ_m g` from `h : ∀ i, f i = g i`.
    pub(super) fn fsum_congr(&self, m: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.fin_sum_congr.clone(),
            [m.clone(), f.clone(), g.clone(), h],
        )
    }
    /// `Rat.mk (Int.ofNat 1) d` — the literal `1/d`, byte-for-byte the
    /// `DualSemigroupConsts::one_over` / `DualBTwoNormConsts::one_over` build (so
    /// the `1/3` density argument matches the eigen lemma and the `(1/9)` endpoint
    /// matches `noise_semigroup_third`).
    pub(super) fn one_over(&self, d: u32) -> Expr {
        let mut d_nat = self.nat_zero.clone();
        for _ in 0..d {
            d_nat = Expr::app(self.nat_succ.clone(), d_nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), self.one_nat()), d_nat],
        )
    }
    /// `noiseDensity_apply_chi_eigen ρ n jS y :
    ///   subsetSum n (fun z => noiseDensityW ρ n z y · χ_{hcDecode jS}(z))
    ///   = (cube n · ρ^{|hcDecode jS|}) · χ_{hcDecode jS}(y)`.
    pub(super) fn eigen_at(&self, rho: &Expr, n: &Expr, js: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.eigen.clone(),
            [rho.clone(), n.clone(), js.clone(), y.clone()],
        )
    }
    /// `noise_semigroup_third k : (1/3)^k·(1/3)^k = (1/9)^k`.
    pub(super) fn semigroup_at(&self, k: &Expr) -> Expr {
        Expr::app(self.semigroup_third.clone(), k.clone())
    }

    /// `fun (t : Rat) => left·t` — a left-multiply `congrArg` motive, built as a
    /// CHILD of `parent` so any outer FVars captured in `left` stay properly
    /// scoped (closed by the parent's `finish`).
    pub(super) fn mul_left_motive(&self, parent: &EnvDeclBuilder, left: &Expr) -> Expr {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = e.fresh_local(self.rat.clone());
        let body = self.mul(left.clone(), t);
        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `fun (t : Rat) => t·right` — a right-multiply `congrArg` motive, built as a
    /// CHILD of `parent`.
    pub(super) fn mul_right_motive(&self, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = e.fresh_local(self.rat.clone());
        let body = self.mul(t, right.clone());
        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
    }

    /// `indNat (S i) = @Bool.rec.{1} (fun _ => Nat) 0 1 (S i)` — byte-for-byte the
    /// B3a / `SpectralConsts` per-bit popcount summand.
    pub(super) fn ind_nat(&self, s_i: Expr) -> Expr {
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
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — the popcount `|S|`,
    /// byte-for-byte the B3a `popcount` build (so the rung-1 spectral weight
    /// `(1/3)^{pc n S}` is def-eq to `noise_two_norm_eq_pairing`'s).
    pub(super) fn popcount_inline(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(Expr::app(s.clone(), i.clone()));
        let pc_fn = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(self.fin_sum_nat.clone(), [n.clone(), pc_fn])
    }
    /// `A g S = subsetSum n (fun x => g x · χ_S x)` — byte-for-byte the B3a
    /// `a_coeff` build (the un-normalized Fourier coefficient).
    pub(super) fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), x.clone()), self.chi_(n, s, &x));
        let f = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
    /// `noiseOp ρ n g a` (folded; `is_reducible`).
    pub(super) fn op_apply(&self, rho: &Expr, n: &Expr, g: &Expr, a: &Expr) -> Expr {
        Expr::apps(
            self.noise_op.clone(),
            [rho.clone(), n.clone(), g.clone(), a.clone()],
        )
    }
    /// `noise_self_adjoint_sq ρ n g`.
    pub(super) fn self_adjoint_sq_at(&self, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            self.self_adjoint_sq.clone(),
            [rho.clone(), n.clone(), g.clone()],
        )
    }
    /// `noise_two_norm_eq_pairing n g` (B3a).
    pub(super) fn two_norm_pairing_at(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(self.two_norm_eq_pairing.clone(), [n.clone(), g.clone()])
    }
    /// `noiseOp_compose_third n g x`.
    pub(super) fn op_compose_at(&self, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.noiseOp_compose_third"),
                vec![],
            ),
            [n.clone(), g.clone(), x.clone()],
        )
    }
}
