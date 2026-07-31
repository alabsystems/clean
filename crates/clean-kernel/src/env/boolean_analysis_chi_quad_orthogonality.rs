// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! 4-fold character orthogonality in UN-NORMALIZED (subsetSum) form — the
//! 4-fold analogue of the on-branch 2-fold `chi_pair_subsetSum_eq_symmDiff`
//! (`boolean_analysis_chi_xside_proof.rs:345`).
//!
//! The character group law `χ_S·χ_T = χ_{S Δ T}` (`chi_mul_chi_symmDiff`,
//! `boolean_analysis_chi_symm_diff_proof.rs:408`) iterated TWICE collapses the
//! 4-fold product `(χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4})` to the single character
//! `χ_{(S1 Δ S2) Δ (S3 Δ S4)}`. Summed over the cube this reduces the 4-fold
//! character sum to a SINGLE-character sum, the exact form rung 2 of the
//! sharp-KKL roadmap consumes under `subsetSum_congr`:
//!
//!   • POINTWISE (`chi_quad_fold`):
//!       `(χ_{S1} x·χ_{S2} x)·(χ_{S3} x·χ_{S4} x) = χ_{(S1 Δ S2) Δ (S3 Δ S4)} x`.
//!     `Eq.trans` of three `chi_mul_chi_symmDiff` applications:
//!       (a) `χ_{S1} x·χ_{S2} x = χ_{S1 Δ S2} x`           (left fold, congrArg)
//!       (b) `χ_{S3} x·χ_{S4} x = χ_{S3 Δ S4} x`           (right fold, congrArg)
//!       (c) `χ_{S1 Δ S2} x·χ_{S3 Δ S4} x = χ_{(S1 Δ S2) Δ (S3 Δ S4)} x` (outer).
//!
//!   • SUM-LEVEL (`subsetSum_chi_quad_orthogonality`):
//!       `subsetSum n (fun x => (χ_{S1} x·χ_{S2} x)·(χ_{S3} x·χ_{S4} x))
//!          = subsetSum n (fun x => χ_{(S1 Δ S2) Δ (S3 Δ S4)} x)`.
//!     `subsetSum_congr` over the per-point `chi_quad_fold`.
//!
//! Both are kernel-checked `ProofQuality::Constructive` (closure ⊆
//! {`chi_mul_chi_symmDiff`, `subsetSum_congr`} ∪ Eq/congrArg built-ins, all
//! admitted-axiom-free).

#[cfg(test)]
use super::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use super::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for the 4-fold character orthogonality lemmas.
#[cfg(test)]
struct QuadConsts {
    nat: Expr,
    rat: Expr,
    bool_xor: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    chi: Expr,
    fin: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    chi_mul_chi_symm_diff: Expr,
    eq1: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

#[cfg(test)]
impl QuadConsts {
    #[cfg(test)]
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            chi_mul_chi_symm_diff: Expr::const_(
                Name::from_string("BoolAnalysis.chi_mul_chi_symmDiff"),
                vec![],
            ),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    #[cfg(test)]
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    #[cfg(test)]
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    #[cfg(test)]
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    #[cfg(test)]
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    #[cfg(test)]
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    #[cfg(test)]
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    #[cfg(test)]
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `congrArg (g : Rat -> Rat) (h : a = b) : g a = g b`.
    #[cfg(test)]
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }

    /// `fun (i : Fin n) => Bool.xor (S i) (T i)` — the symmetric difference
    /// `S Δ T` as an `HCPoint n` (matches `chi_mul_chi_symmDiff`'s RHS subset).
    #[cfg(test)]
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

    /// `chi_mul_chi_symmDiff n S T x : χ_S(x)·χ_T(x) = χ_{S Δ T}(x)`.
    #[cfg(test)]
    fn fold(&self, n: &Expr, s: &Expr, t: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            self.chi_mul_chi_symm_diff.clone(),
            [n.clone(), s.clone(), t.clone(), x.clone()],
        )
    }

    /// `congrArg (fun z => z·right) h : a·right = b·right` — rewrite the LEFT
    /// factor of a `Rat.mul` under the proof `h : a = b`.
    #[cfg(test)]
    fn mul_right_congr(
        &self,
        parent: &EnvDeclBuilder,
        right: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }

    /// `congrArg (fun z => left·z) h : left·a = left·b` — rewrite the RIGHT
    /// factor of a `Rat.mul` under the proof `h : a = b`.
    #[cfg(test)]
    fn mul_left_congr(
        &self,
        parent: &EnvDeclBuilder,
        left: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
}

// ===========================================================================
// chi_quad_fold — the pointwise 4-fold character merge.
// ===========================================================================

/// `∀ (n : Nat) (S1 S2 S3 S4 x : HCPoint n),
///   (χ_{S1}(x)·χ_{S2}(x))·(χ_{S3}(x)·χ_{S4}(x))
///     = χ_{(S1 Δ S2) Δ (S3 Δ S4)}(x)`.
#[cfg(test)]
fn fold_type(c: &QuadConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s1_id, s1) = b.fresh_local(hcp.clone());
    let (s2_id, s2) = b.fresh_local(hcp.clone());
    let (s3_id, s3) = b.fresh_local(hcp.clone());
    let (s4_id, s4) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    let lhs = c.mul(
        c.mul(c.chi_(&n, &s1, &x), c.chi_(&n, &s2, &x)),
        c.mul(c.chi_(&n, &s3, &x), c.chi_(&n, &s4, &x)),
    );
    let sd12 = c.symm_diff_fn(&b, &n, &s1, &s2);
    let sd34 = c.symm_diff_fn(&b, &n, &s3, &s4);
    let sd = c.symm_diff_fn(&b, &n, &sd12, &sd34);
    let rhs = c.chi_(&n, &sd, &x);
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(x_id, BinderInfo::Default, hcp.clone(), concl);
    let r = b.mk_pi(s4_id, BinderInfo::Default, hcp.clone(), r);
    let r = b.mk_pi(s3_id, BinderInfo::Default, hcp.clone(), r);
    let r = b.mk_pi(s2_id, BinderInfo::Default, hcp.clone(), r);
    let r = b.mk_pi(s1_id, BinderInfo::Default, hcp, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

#[cfg(test)]
fn fold_value(c: &QuadConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s1_id, s1) = b.fresh_local(hcp.clone());
    let (s2_id, s2) = b.fresh_local(hcp.clone());
    let (s3_id, s3) = b.fresh_local(hcp.clone());
    let (s4_id, s4) = b.fresh_local(hcp.clone());
    let (x_id, x) = b.fresh_local(hcp.clone());

    let chi1 = c.chi_(&n, &s1, &x);
    let chi2 = c.chi_(&n, &s2, &x);
    let chi3 = c.chi_(&n, &s3, &x);
    let chi4 = c.chi_(&n, &s4, &x);

    let sd12 = c.symm_diff_fn(&b, &n, &s1, &s2);
    let sd34 = c.symm_diff_fn(&b, &n, &s3, &s4);
    let sd = c.symm_diff_fn(&b, &n, &sd12, &sd34);

    let chi12 = c.chi_(&n, &sd12, &x); // χ_{S1 Δ S2}(x)
    let chi34 = c.chi_(&n, &sd34, &x); // χ_{S3 Δ S4}(x)

    let lhs = c.mul(
        c.mul(chi1.clone(), chi2.clone()),
        c.mul(chi3.clone(), chi4.clone()),
    );
    let mid_left = c.mul(chi12.clone(), c.mul(chi3.clone(), chi4.clone())); // χ12·(χ3·χ4)
    let mid_both = c.mul(chi12.clone(), chi34.clone()); // χ12·χ34
    let rhs = c.chi_(&n, &sd, &x); // χ_{(S1ΔS2)Δ(S3ΔS4)}(x)

    // step1 : (χ1·χ2)·(χ3·χ4) = χ12·(χ3·χ4)   — rewrite LEFT factor.
    let h12 = c.fold(&n, &s1, &s2, &x); // χ1·χ2 = χ12
    let step1 = c.mul_right_congr(
        &b,
        &c.mul(chi3.clone(), chi4.clone()),
        c.mul(chi1.clone(), chi2.clone()),
        chi12.clone(),
        h12,
    );
    // step2 : χ12·(χ3·χ4) = χ12·χ34            — rewrite RIGHT factor.
    let h34 = c.fold(&n, &s3, &s4, &x); // χ3·χ4 = χ34
    let step2 = c.mul_left_congr(
        &b,
        &chi12,
        c.mul(chi3.clone(), chi4.clone()),
        chi34.clone(),
        h34,
    );
    // step3 : χ12·χ34 = χ_{(S1ΔS2)Δ(S3ΔS4)}    — outer fold.
    //   chi_mul_chi_symmDiff n (S1ΔS2) (S3ΔS4) x. Its RHS subset
    //   `fun i => xor (sd12 i) (sd34 i)` β-matches `sd`, so it retypes by defeq.
    let step3 = c.fold(&n, &sd12, &sd34, &x);

    // trans chain: lhs = mid_left = mid_both = rhs.
    let t1 = c.trans(
        lhs.clone(),
        mid_left.clone(),
        mid_both.clone(),
        step1,
        step2,
    );
    let proof = c.trans(lhs, mid_both, rhs, t1, step3);

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s4_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s3_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s2_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s1_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

// ===========================================================================
// subsetSum_chi_quad_orthogonality — the sum-level 4-fold orthogonality.
// ===========================================================================

/// `fun (x : HCPoint n) => (χ_{S1}(x)·χ_{S2}(x))·(χ_{S3}(x)·χ_{S4}(x))`.
#[cfg(test)]
fn quad_product_fn(
    c: &QuadConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    s1: &Expr,
    s2: &Expr,
    s3: &Expr,
    s4: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let body = c.mul(
        c.mul(c.chi_(n, s1, &x), c.chi_(n, s2, &x)),
        c.mul(c.chi_(n, s3, &x), c.chi_(n, s4, &x)),
    );
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

/// `fun (x : HCPoint n) => χ_{U}(x)` — the single-character integrand at `U`.
#[cfg(test)]
fn chi_single_fn(c: &QuadConsts, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let body = c.chi_(n, u, &x);
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

/// `∀ (n : Nat) (S1 S2 S3 S4 : HCPoint n),
///   subsetSum n (fun x => (χ_{S1}(x)·χ_{S2}(x))·(χ_{S3}(x)·χ_{S4}(x)))
///     = subsetSum n (fun x => χ_{(S1 Δ S2) Δ (S3 Δ S4)}(x))`.
#[cfg(test)]
fn ortho_type(c: &QuadConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s1_id, s1) = b.fresh_local(hcp.clone());
    let (s2_id, s2) = b.fresh_local(hcp.clone());
    let (s3_id, s3) = b.fresh_local(hcp.clone());
    let (s4_id, s4) = b.fresh_local(hcp.clone());

    let lhs = c.ssum(&n, quad_product_fn(c, &b, &n, &s1, &s2, &s3, &s4));
    let sd12 = c.symm_diff_fn(&b, &n, &s1, &s2);
    let sd34 = c.symm_diff_fn(&b, &n, &s3, &s4);
    let sd = c.symm_diff_fn(&b, &n, &sd12, &sd34);
    let rhs = c.ssum(&n, chi_single_fn(c, &b, &n, &sd));
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(s4_id, BinderInfo::Default, hcp.clone(), concl);
    let r = b.mk_pi(s3_id, BinderInfo::Default, hcp.clone(), r);
    let r = b.mk_pi(s2_id, BinderInfo::Default, hcp.clone(), r);
    let r = b.mk_pi(s1_id, BinderInfo::Default, hcp, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

#[cfg(test)]
fn ortho_value(c: &QuadConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s1_id, s1) = b.fresh_local(hcp.clone());
    let (s2_id, s2) = b.fresh_local(hcp.clone());
    let (s3_id, s3) = b.fresh_local(hcp.clone());
    let (s4_id, s4) = b.fresh_local(hcp.clone());

    let quad_fn = quad_product_fn(c, &b, &n, &s1, &s2, &s3, &s4);
    let sd12 = c.symm_diff_fn(&b, &n, &s1, &s2);
    let sd34 = c.symm_diff_fn(&b, &n, &s3, &s4);
    let sd = c.symm_diff_fn(&b, &n, &sd12, &sd34);
    let chi_fn = chi_single_fn(c, &b, &n, &sd);

    // subsetSum_congr n (quad product) (χ_{(S1ΔS2)Δ(S3ΔS4)})
    //   (fun x => chi_quad_fold n S1 S2 S3 S4 x)
    //   per-point: (χ1·χ2)·(χ3·χ4) = χ_{(S1ΔS2)Δ(S3ΔS4)}. The two integrands
    //   β-match the subsetSum arguments exactly (chi_single_fn's subset = sd =
    //   chi_quad_fold's RHS subset), so the congruence proof retypes by defeq.
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi_quad_fold"), vec![]),
            [n.clone(), s1.clone(), s2.clone(), s3.clone(), s4.clone(), x],
        );
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let proof = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), quad_fn, chi_fn, pointwise],
    );

    let val = b.mk_lam(s4_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s3_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s2_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s1_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

#[cfg(test)]
impl Environment {
    /// Register `BoolAnalysis.chi_quad_fold`: the pointwise 4-fold character
    /// merge `(χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4}) = χ_{(S1 Δ S2) Δ (S3 Δ S4)}`.
    ///
    /// `Eq.trans` of three `chi_mul_chi_symmDiff` applications: fold the left
    /// pair, fold the right pair (each lifted through `Rat.mul` by `congrArg`),
    /// then fold the two symmetric differences together. Constructive, empty
    /// admitted-axiom closure. Idempotent.
    #[cfg(test)]
    pub(crate) fn register_chi_quad_fold(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_quad_fold");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // chi, Bool.xor, chi_mul_chi_symmDiff
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_chi_symm_diff_theorem()?;

        let c = QuadConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: fold_type(&c),
            value: fold_value(&c),
        })
    }

    /// Register `BoolAnalysis.subsetSum_chi_quad_orthogonality`: the 4-fold
    /// character orthogonality in un-normalized (subsetSum) form,
    /// `∀ n S1 S2 S3 S4, subsetSum n (fun x => (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4}))
    ///    = subsetSum n (fun x => χ_{(S1 Δ S2) Δ (S3 Δ S4)})`.
    ///
    /// `subsetSum_congr` over the proven per-point `chi_quad_fold`. The 4-fold
    /// analogue of `chi_pair_subsetSum_eq_symmDiff`: it collapses the 4-fold
    /// character product sum to a SINGLE-character sum at `(S1 Δ S2) Δ (S3 Δ S4)`,
    /// which the single-character orthogonality (`chi_diag_subsetSum_cube` /
    /// `chi_offdiag_subsetSum_zero`) then evaluates to `2^n` or `0`. This is the
    /// genuine 4-fold symmetric-difference fold + diagonal-extraction reduction
    /// (rung 1 of the sharp-KKL roadmap), consumed under `subsetSum_congr` by the
    /// `pow4_noisefn_spectral_diag` rung. Constructive, empty admitted-axiom
    /// closure. Idempotent.
    #[cfg(test)]
    pub(crate) fn register_subset_sum_chi_quad_orthogonality(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_quad_orthogonality");
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
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_chi_quad_fold()?;

        let c = QuadConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ortho_type(&c),
            value: ortho_value(&c),
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
    fn test_chi_quad_fold_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_chi_quad_fold()
            .expect("register_chi_quad_fold");
        env.register_chi_quad_fold().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_quad_fold");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_quad_fold must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_quad_fold must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_subset_sum_chi_quad_orthogonality_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_subset_sum_chi_quad_orthogonality()
            .expect("register_subset_sum_chi_quad_orthogonality");
        env.register_subset_sum_chi_quad_orthogonality()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_quad_orthogonality");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("subsetSum_chi_quad_orthogonality must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "subsetSum_chi_quad_orthogonality must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }
}
