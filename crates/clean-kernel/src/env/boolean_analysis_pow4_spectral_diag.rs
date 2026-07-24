// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RUNG 2 of the sharp-KKL roadmap — `pow4_noisefn_spectral_diag`.
//!
//! Pure composition of RUNG 1 (`subsetSum_chi_quad_diag`,
//! `boolean_analysis_chi_quad_diag.rs`) and the on-branch top rung
//! `pow4_noisefn_spectral` (`boolean_analysis_pow4_spectral.rs:467`, RHS built
//! by `build_spectral_type`). The top rung proves
//!
//!   `Σ_jx pow4(noiseFn ρ n F jx) = s_nest(Spectral)`,
//!
//! where the innermost `spectral_body` at fixed `(S1,S2,S3,S4)` is
//!
//!   `wblk · (ablk · Σ_x (χ_{S1} x·χ_{S2} x)·(χ_{S3} x·χ_{S4} x))`,
//!
//! `wblk = (ρ^|S1|·ρ^|S2|)·(ρ^|S3|·ρ^|S4|)`,
//! `ablk = (A S1·A S2)·(A S3·A S4)`, `A F S = subsetSum n (y => F y·χ_S y)`,
//! and the inner `Σ_x ∏χ` kept EXPLICIT (un-collapsed).
//!
//! RUNG 2 rewrites that explicit inner character correlation, under the 4-deep
//! `subsetSum_congr` S-nesting, via RUNG 1's
//! `subsetSum_chi_quad_diag n S1 S2 S3 S4`
//!   `: Σ_x (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4})
//!        = 2^n · ind((S1 Δ S2) Δ (S3 Δ S4) = ∅)`,
//! collapsing the spectral body all the way to its DIAGONAL VALUE form
//!
//!   `wblk · (ablk · (2^n · ind((S1 Δ S2) Δ (S3 Δ S4) = ∅)))`,
//!
//! where `2^n` is `Rat.mk (Int.ofNat (2^n)) 1` and `ind(U = ∅)` is the
//! codebase-native `ind (Nat.beq (setSizeNat n U) 0)` (the same encoding RUNG 1
//! and `variance_eq_nonempty_mass` use).
//!
//! The full statement (`build_diag_type`) is therefore
//!
//!   `Σ_jx pow4(noiseFn ρ n F jx) = s_nest(SpectralDiag)`,
//!
//! reached by `Eq.trans (pow4_noisefn_spectral …) (congr-rewrite of the inner
//! sum)`. The congr-rewrite is `subsetSum_congr` 4-deep over the per-quad
//! `congrArg (wblk·_) (congrArg (ablk·_) (subsetSum_chi_quad_diag …))`.
//! This is the genuine 4-fold χ-orthogonality DIAGONAL EVALUATION (no
//! masquerade): the inner per-x character integral is replaced by its closed
//! `2^n`-or-`0` value via RUNG 1, removing the explicit per-x χ-product
//! integral AND the residual single-character sum in one composition step.
//! Constructive, empty admitted-axiom closure. Idempotent.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Self-contained constants for the diagonal rung. Mirrors the atoms shared by
/// `Pow4SpectralConsts` (spectral body shape) and `QuadConsts` (symmetric
/// difference / single-character shape) so the rewrite types by defeq against
/// both `pow4_noisefn_spectral`'s RHS and `subsetSum_chi_quad_orthogonality`.
struct DiagConsts {
    nat: Expr,
    rat: Expr,
    bool_xor: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat_mul: Expr,
    rat_mk: Expr,
    int_of_nat: Expr,
    nat_beq: Expr,
    ind: Expr,
    set_size_nat: Expr,
    hcpoint: Expr,
    chi: Expr,
    pow_nat: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_nat: Expr,
    nat_pow: Expr,
    two: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    chi_quad_diag: Expr,
    pow4_noisefn_spectral: Expr,
    eq1: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl DiagConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            nat_zero,
            nat_succ: nat_succ.clone(),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_beq: Expr::const_(Name::from_string("Nat.beq"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_nat: Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two: Expr::app(nat_succ, nat_one),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            chi_quad_diag: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_chi_quad_diag"),
                vec![],
            ),
            pow4_noisefn_spectral: Expr::const_(
                Name::from_string("BoolAnalysis.pow4_noisefn_spectral"),
                vec![],
            ),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── shared atoms ───────────────────────────────────────────────────────────

    fn rat_ty(&self) -> Expr {
        self.rat.clone()
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn sum_pow(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [self.pow2(n), g])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `congrArg Rat Rat a b g h : g a = g b` from `h : a = b`.
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
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

    // ── LHS (= pow4_noisefn_spectral LHS) ──────────────────────────────────────

    /// `fun (jx : Fin (2^n)) => pow4 (noiseFn ρ n F jx)` — the `Fin.sum` summand
    /// (byte-identical to `Pow4SpectralConsts::lhs_jx_fn`).
    fn lhs_jx_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_pow = self.fin_of(&self.pow2(n));
        let (jx_id, jx) = b.fresh_local(fin_pow.clone());
        let nf = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseFn"), vec![]),
            [rho.clone(), n.clone(), f.clone(), jx],
        );
        let sq = self.mul(nf.clone(), nf);
        let p4 = self.mul(sq.clone(), sq);
        b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin_pow, p4))
    }
    fn lhs(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        self.sum_pow(n, self.lhs_jx_fn(parent, rho, n, f))
    }

    // ── spectral-body factors (mirror Pow4SpectralConsts) ──────────────────────

    fn pow(&self, rho: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [rho.clone(), k.clone()])
    }
    /// `indNat b = @Bool.rec.{1} (fun _ => Nat) 0 1 b`.
    fn ind_nat(&self, s_i: Expr) -> Expr {
        let nat_one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let nat_motive = Expr::lam(BinderInfo::Default, bool_ty, self.nat.clone());
        let bool_rec_nat = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(
            bool_rec_nat,
            [nat_motive, self.nat_zero.clone(), nat_one, s_i],
        )
    }
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — popcount `|S|`.
    fn popcount(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(Expr::app(s.clone(), i.clone()));
        let pc_fn = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(self.fin_sum_nat.clone(), [n.clone(), pc_fn])
    }
    /// `w S = ρ^{pc n S}`.
    fn weight(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        self.pow(rho, &self.popcount(parent, n, s))
    }
    /// `A F S = subsetSum n (fun y => F y · χ_S y)`.
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(f.clone(), y.clone()), self.chi_(n, s, &y));
        let g_fn = b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g_fn)
    }
    /// `wblk = (w1·w2)·(w3·w4)`.
    fn wblk(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let w1 = self.weight(parent, rho, n, s1);
        let w2 = self.weight(parent, rho, n, s2);
        let w3 = self.weight(parent, rho, n, s3);
        let w4 = self.weight(parent, rho, n, s4);
        self.mul(self.mul(w1, w2), self.mul(w3, w4))
    }
    /// `ablk = (A1·A2)·(A3·A4)`.
    fn ablk(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let a1 = self.a_coeff(parent, n, f, s1);
        let a2 = self.a_coeff(parent, n, f, s2);
        let a3 = self.a_coeff(parent, n, f, s3);
        let a4 = self.a_coeff(parent, n, f, s4);
        self.mul(self.mul(a1, a2), self.mul(a3, a4))
    }

    // ── character sums (explicit vs diagonal) ──────────────────────────────────

    /// `fun (i : Fin n) => Bool.xor (S i) (T i)` — `S Δ T` as `HCPoint n`
    /// (byte-identical to `QuadConsts::symm_diff_fn`, so the diagonal subset
    /// β-matches `subsetSum_chi_quad_orthogonality`'s RHS subset).
    fn symm_diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = Expr::apps(
            self.bool_xor.clone(),
            [Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i)],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `(S1 Δ S2) Δ (S3 Δ S4)` as an `HCPoint n`.
    fn sd4(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let sd12 = self.symm_diff_fn(parent, n, s1, s2);
        let sd34 = self.symm_diff_fn(parent, n, s3, s4);
        self.symm_diff_fn(parent, n, &sd12, &sd34)
    }
    /// `Σ_x (χ_{S1} x·χ_{S2} x)·(χ_{S3} x·χ_{S4} x)` — explicit inner correlation
    /// (byte-identical to `Pow4SpectralConsts::xsum_chi4` and to the LHS subset of
    /// `subsetSum_chi_quad_orthogonality`).
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
    // ── diagonal-VALUE atoms (2^n · ind) — byte-match subsetSum_chi_quad_diag RHS ─

    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    /// `Rat.mk (Int.ofNat (2^n)) 1` — the rational `2^n` (byte-identical to
    /// `DiagConsts::cube` in `boolean_analysis_chi_quad_diag.rs`).
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    /// `Nat.beq m Nat.zero`.
    fn beq0(&self, m: Expr) -> Expr {
        Expr::apps(self.nat_beq.clone(), [m, self.nat_zero.clone()])
    }
    /// `setSizeNat n U`.
    fn ss_nat(&self, n: &Expr, u: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), u.clone()])
    }
    /// `ind (Nat.beq (setSizeNat n U) 0)` — the empty-set indicator `ind(U=∅)`.
    fn empty_ind(&self, n: &Expr, u: &Expr) -> Expr {
        Expr::app(self.ind.clone(), self.beq0(self.ss_nat(n, u)))
    }
    /// `2^n · ind ((S1 Δ S2) Δ (S3 Δ S4) = ∅)` — the DIAGONAL VALUE of the inner
    /// character correlation (byte-identical to `subsetSum_chi_quad_diag`'s RHS).
    fn xsum_diag_value(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let sd = self.sd4(parent, n, s1, s2, s3, s4);
        self.mul(self.cube(n), self.empty_ind(n, &sd))
    }

    /// Spectral body at fixed `(S1,S2,S3,S4)`: explicit form (`pow4_noisefn_spectral`
    /// RHS) when `diag=false`, diagonal form when `diag=true`.
    #[allow(clippy::too_many_arguments)]
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
        diag: bool,
    ) -> Expr {
        let wblk = self.wblk(parent, rho, n, s1, s2, s3, s4);
        let ablk = self.ablk(parent, n, f, s1, s2, s3, s4);
        let chi = if diag {
            self.xsum_diag_value(parent, n, s1, s2, s3, s4)
        } else {
            self.xsum_chi4(parent, n, s1, s2, s3, s4)
        };
        self.mul(wblk, self.mul(ablk, chi))
    }

    /// Per-quad rewrite proof
    /// `wblk·(ablk·xsum_chi4) = wblk·(ablk·xsum_diag_value)`:
    /// `congrArg (wblk·_) (congrArg (ablk·_) (subsetSum_chi_quad_diag …))`.
    /// RUNG 1's `subsetSum_chi_quad_diag` collapses the explicit inner correlation
    /// `Σ_x (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4})` straight to its `2^n`-or-`0` diagonal
    /// VALUE `2^n · ind((S1 Δ S2) Δ (S3 Δ S4) = ∅)`.
    #[allow(clippy::too_many_arguments)]
    fn perquad_diag(
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
        let wblk = self.wblk(parent, rho, n, s1, s2, s3, s4);
        let ablk = self.ablk(parent, n, f, s1, s2, s3, s4);
        let chi4 = self.xsum_chi4(parent, n, s1, s2, s3, s4);
        let diag = self.xsum_diag_value(parent, n, s1, s2, s3, s4);
        // quad_diag : Σ_x (χ1·χ2)·(χ3·χ4) = 2^n · ind((S1ΔS2)Δ(S3ΔS4) = ∅).
        let quad_diag = Expr::apps(
            self.chi_quad_diag.clone(),
            [n.clone(), s1.clone(), s2.clone(), s3.clone(), s4.clone()],
        );
        // inner : ablk·chi4 = ablk·diag.
        let inner = self.mul_left_congr(parent, &ablk, chi4, diag.clone(), quad_diag);
        // outer : wblk·(ablk·chi4) = wblk·(ablk·diag).
        let a_chi4 = self.mul(ablk.clone(), self.xsum_chi4(parent, n, s1, s2, s3, s4));
        let a_diag = self.mul(ablk, diag);
        self.mul_left_congr(parent, &wblk, a_chi4, a_diag, inner)
    }

    // ── 4-deep S-nesting: body (type side) and congr proof (value side) ────────

    /// `s_nest(diag)`: `Σ_{S1} Σ_{S3} Σ_{S2} Σ_{S4} <spectral_body diag>`
    /// (the (S1,S3,S2,S4) peel order of `pow4_noisefn_spectral`'s RHS).
    fn s_nest(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr, diag: bool) -> Expr {
        // fixed peel order [S1, S3, S2, S4]; spectral_body takes (S1,S2,S3,S4).
        let s1_fn = {
            let mut b1 = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (s1_id, s1) = b1.fresh_local(hcp.clone());
            let s3_fn = {
                let mut b3 = EnvDeclBuilder::child_of(&b1);
                let (s3_id, s3) = b3.fresh_local(hcp.clone());
                let s2_fn = {
                    let mut b2 = EnvDeclBuilder::child_of(&b3);
                    let (s2_id, s2) = b2.fresh_local(hcp.clone());
                    let s4_fn = {
                        let mut b4 = EnvDeclBuilder::child_of(&b2);
                        let (s4_id, s4) = b4.fresh_local(hcp.clone());
                        let body = self.spectral_body(&b4, rho, n, f, &s1, &s2, &s3, &s4, diag);
                        b4.finish_child(b4.mk_lam(s4_id, BinderInfo::Default, hcp.clone(), body))
                    };
                    b2.finish_child(b2.mk_lam(
                        s2_id,
                        BinderInfo::Default,
                        hcp.clone(),
                        self.ssum(n, s4_fn),
                    ))
                };
                b3.finish_child(b3.mk_lam(
                    s3_id,
                    BinderInfo::Default,
                    hcp.clone(),
                    self.ssum(n, s2_fn),
                ))
            };
            b1.finish_child(b1.mk_lam(s1_id, BinderInfo::Default, hcp, self.ssum(n, s3_fn)))
        };
        self.ssum(n, s1_fn)
    }

    /// The 4-deep `subsetSum_congr` proof `s_nest(explicit) = s_nest(diag)`.
    /// At each level we wrap the next-level integrands (before/after) in a
    /// `subsetSum_congr`; the bottom hypothesis is `perquad_diag`.
    fn nest_congr(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        // helper: integrand `fun S => <remaining nest>` for a given peel prefix.
        // depth: 0=>S1, 1=>S3, 2=>S2, 3=>S4. svals holds peel-order bound values.
        // We special-case explicitly for the 4 levels to keep binder ids correct.
        // before/after integrands at the OUTERMOST level:
        let before = self.s1_integrand(parent, rho, n, f, &hcp, false);
        let after = self.s1_integrand(parent, rho, n, f, &hcp, true);
        let h = {
            let mut b1 = EnvDeclBuilder::child_of(parent);
            let (s1_id, s1) = b1.fresh_local(hcp.clone());
            let pf = self.s3_congr(&b1, rho, n, f, &hcp, &s1);
            b1.finish_child(b1.mk_lam(s1_id, BinderInfo::Default, hcp.clone(), pf))
        };
        self.ss_congr(n, &before, &after, h)
    }

    /// `subsetSum_congr n G H h`.
    fn ss_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }

    /// `fun S1 => Σ_{S3} Σ_{S2} Σ_{S4} <body diag?>` — outermost integrand.
    fn s1_integrand(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        diag: bool,
    ) -> Expr {
        let mut b1 = EnvDeclBuilder::child_of(parent);
        let (s1_id, s1) = b1.fresh_local(hcp.clone());
        let inner = self.s3_body(&b1, rho, n, f, hcp, &s1, diag);
        b1.finish_child(b1.mk_lam(s1_id, BinderInfo::Default, hcp.clone(), self.ssum(n, inner)))
    }
    /// `fun S3 => Σ_{S2} Σ_{S4} <body>` at fixed S1.
    fn s3_body(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        s1: &Expr,
        diag: bool,
    ) -> Expr {
        let mut b3 = EnvDeclBuilder::child_of(parent);
        let (s3_id, s3) = b3.fresh_local(hcp.clone());
        let inner = self.s2_body(&b3, rho, n, f, hcp, s1, &s3, diag);
        b3.finish_child(b3.mk_lam(s3_id, BinderInfo::Default, hcp.clone(), self.ssum(n, inner)))
    }
    /// `fun S2 => Σ_{S4} <body>` at fixed (S1,S3).
    fn s2_body(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        s1: &Expr,
        s3: &Expr,
        diag: bool,
    ) -> Expr {
        let mut b2 = EnvDeclBuilder::child_of(parent);
        let (s2_id, s2) = b2.fresh_local(hcp.clone());
        let inner = self.s4_body(&b2, rho, n, f, hcp, s1, &s2, s3, diag);
        b2.finish_child(b2.mk_lam(s2_id, BinderInfo::Default, hcp.clone(), self.ssum(n, inner)))
    }
    /// `fun S4 => <spectral_body>` at fixed (S1,S3,S2).
    #[allow(clippy::too_many_arguments)]
    fn s4_body(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        diag: bool,
    ) -> Expr {
        let mut b4 = EnvDeclBuilder::child_of(parent);
        let (s4_id, s4) = b4.fresh_local(hcp.clone());
        let body = self.spectral_body(&b4, rho, n, f, s1, s2, s3, &s4, diag);
        b4.finish_child(b4.mk_lam(s4_id, BinderInfo::Default, hcp.clone(), body))
    }

    /// `subsetSum_congr` over S3 (level 1), proof for fixed S1.
    fn s3_congr(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        s1: &Expr,
    ) -> Expr {
        let before = self.s3_integrand(parent, rho, n, f, hcp, s1, false);
        let after = self.s3_integrand(parent, rho, n, f, hcp, s1, true);
        let h = {
            let mut b3 = EnvDeclBuilder::child_of(parent);
            let (s3_id, s3) = b3.fresh_local(hcp.clone());
            let pf = self.s2_congr(&b3, rho, n, f, hcp, s1, &s3);
            b3.finish_child(b3.mk_lam(s3_id, BinderInfo::Default, hcp.clone(), pf))
        };
        self.ss_congr(n, &before, &after, h)
    }
    /// `fun S3 => Σ_{S2} Σ_{S4} <body diag?>` at fixed S1.
    fn s3_integrand(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        s1: &Expr,
        diag: bool,
    ) -> Expr {
        let mut b3 = EnvDeclBuilder::child_of(parent);
        let (s3_id, s3) = b3.fresh_local(hcp.clone());
        let inner = self.s2_body(&b3, rho, n, f, hcp, s1, &s3, diag);
        b3.finish_child(b3.mk_lam(s3_id, BinderInfo::Default, hcp.clone(), self.ssum(n, inner)))
    }

    /// `subsetSum_congr` over S2 (level 2), proof for fixed (S1,S3).
    fn s2_congr(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        s1: &Expr,
        s3: &Expr,
    ) -> Expr {
        let before = self.s2_integrand(parent, rho, n, f, hcp, s1, s3, false);
        let after = self.s2_integrand(parent, rho, n, f, hcp, s1, s3, true);
        let h = {
            let mut b2 = EnvDeclBuilder::child_of(parent);
            let (s2_id, s2) = b2.fresh_local(hcp.clone());
            let pf = self.s4_congr(&b2, rho, n, f, hcp, s1, &s2, s3);
            b2.finish_child(b2.mk_lam(s2_id, BinderInfo::Default, hcp.clone(), pf))
        };
        self.ss_congr(n, &before, &after, h)
    }
    /// `fun S2 => Σ_{S4} <body diag?>` at fixed (S1,S3).
    fn s2_integrand(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        s1: &Expr,
        s3: &Expr,
        diag: bool,
    ) -> Expr {
        let mut b2 = EnvDeclBuilder::child_of(parent);
        let (s2_id, s2) = b2.fresh_local(hcp.clone());
        let inner = self.s4_body(&b2, rho, n, f, hcp, s1, &s2, s3, diag);
        b2.finish_child(b2.mk_lam(s2_id, BinderInfo::Default, hcp.clone(), self.ssum(n, inner)))
    }

    /// `subsetSum_congr` over S4 (level 3, bottom), proof for fixed (S1,S2,S3).
    #[allow(clippy::too_many_arguments)]
    fn s4_congr(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        hcp: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
    ) -> Expr {
        let before = self.s4_body(parent, rho, n, f, hcp, s1, s2, s3, false);
        let after = self.s4_body(parent, rho, n, f, hcp, s1, s2, s3, true);
        let h = {
            let mut b4 = EnvDeclBuilder::child_of(parent);
            let (s4_id, s4) = b4.fresh_local(hcp.clone());
            // peel order (S1,S3,S2,S4); perquad_diag takes (S1,S2,S3,S4).
            let pf = self.perquad_diag(&b4, rho, n, f, s1, s2, s3, &s4);
            b4.finish_child(b4.mk_lam(s4_id, BinderInfo::Default, hcp.clone(), pf))
        };
        self.ss_congr(n, &before, &after, h)
    }
}

/// `∀ (ρ : Rat) (n : Nat) (F : HCPoint n → Rat),
///   Fin.sum (2^n) (fun jx => pow4 (noiseFn ρ n F jx)) = s_nest(SpectralDiag)`.
fn build_diag_type(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.lhs(&b, &rho, &n, &f);
    let rhs = c.s_nest(&b, &rho, &n, &f, true);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat_ty(), ty);
    b.finish(ty)
}

fn build_diag_value(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat_ty());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.f_type(&n));

    let lhs = c.lhs(&b, &rho, &n, &f);
    let mid = c.s_nest(&b, &rho, &n, &f, false); // pow4_noisefn_spectral RHS (explicit).
    let rhs = c.s_nest(&b, &rho, &n, &f, true); // diagonal RHS.

    // leg1 : LHS = s_nest(explicit)  (pow4_noisefn_spectral ρ n F).
    let leg1 = Expr::apps(
        c.pow4_noisefn_spectral.clone(),
        [rho.clone(), n.clone(), f.clone()],
    );
    // leg2 : s_nest(explicit) = s_nest(diag)  (4-deep subsetSum_congr).
    let leg2 = c.nest_congr(&b, &rho, &n, &f);
    let proof = c.trans(lhs, mid, rhs, leg1, leg2);

    let val = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat_ty(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.pow4_noisefn_spectral_diag` — RUNG 2 of the
    /// sharp-KKL roadmap. Composes `pow4_noisefn_spectral` (explicit inner
    /// χ-correlation) with RUNG 1's `subsetSum_chi_quad_diag`, rewriting the
    /// explicit `Σ_x (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4})` to its closed diagonal
    /// VALUE `2^n · ind((S1 Δ S2) Δ (S3 Δ S4) = ∅)` under the 4-deep
    /// `subsetSum_congr` S-nesting. `Eq.trans` of the top rung and a 4-deep
    /// congruence whose bottom hypothesis is
    /// `congrArg (wblk·_) (congrArg (ablk·_) (subsetSum_chi_quad_diag …))`.
    /// Constructive, empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_pow4_noisefn_spectral_diag_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_spectral_diag");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_chi_quad_diag()?;
        self.register_pow4_noisefn_spectral_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = DiagConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_diag_type(&c),
            value: build_diag_value(&c),
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
    fn test_pow4_noisefn_spectral_diag_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_pow4_noisefn_spectral_diag_theorem()
            .expect("register_pow4_noisefn_spectral_diag_theorem");
        env.register_pow4_noisefn_spectral_diag_theorem()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_spectral_diag");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("pow4_noisefn_spectral_diag must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "pow4_noisefn_spectral_diag must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }
}
