// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — the **4th-moment (`pow4`) spectral expansion** chain
//! (`pow4_noisefn_spectral`, run "pow4spectral").
//!
//! See `designs/2026-06-12-kkl-levelsplit-4norm-spectral-inversion.md` (residual
//! item 3, the genuine 4-norm↔spectral inversion). `hc24_at_third`'s LHS is the
//! 4th moment `Σ_jx pow4(noiseFn (1/3) n F jx)`; this module supplies the
//! **4-fold Fubini analogue** of `noise_spectral_core`'s 2-fold expansion, the
//! `‖T_ρ F‖₄⁴` spectral expansion the inversion pivots through.
//!
//! ## Rung 1 — `Fin.sum_pow4` (the generic 4-fold-product expansion)
//!
//! ```text
//! Fin.sum_pow4 : ∀ (n : Nat) (f : Fin n → Rat),
//!   Rat.mul (Rat.mul (Fin.sum n f) (Fin.sum n f))
//!           (Rat.mul (Fin.sum n f) (Fin.sum n f))
//!     = Fin.sum n (fun j1 => Fin.sum n (fun j3 =>
//!         Fin.sum n (fun j2 => Fin.sum n (fun j4 =>
//!           Rat.mul (Rat.mul (f j1) (f j2)) (Rat.mul (f j3) (f j4))))))
//! ```
//!
//! i.e. `pow4(Σ f) = Σ_{j1}Σ_{j3}Σ_{j2}Σ_{j4} (f j1·f j2)·(f j3·f j4)` — the
//! 4-fold-product expansion of the 4th power of a finite sum (`pow4 x =
//! (x·x)·(x·x)`). This is the generic carrier-level brick; instantiating at
//! `f := fun jy => F(decode jy)·noiseDensityW ρ n (decode jx)(decode jy)` (the
//! `noiseFn` integrand) and summing over `jx` gives the operator-side 4th moment.
//!
//! PROOF (no induction — three `Fin.sum_mul_sum` applications glued by
//! `Fin.sum_congr` + `congrArg` + `Eq.trans`):
//!
//! Let `S := Fin.sum n f`. `Fin.sum_mul_sum n n f f` gives the double-sum
//! `D := Fin.sum n (fun j1 => Fin.sum n (fun j2 => f j1·f j2))` with `S·S = D`.
//! `D` is itself a `Fin.sum n h` with `h j1 := Fin.sum n (fun j2 => f j1·f j2)`,
//! so a SECOND `Fin.sum_mul_sum n n h h` gives `D·D = Fin.sum n (fun j1 =>
//! Fin.sum n (fun j3 => h j1·h j3))`. Inside, each `h j1·h j3 = (Σ_{j2} f j1·f j2)
//! ·(Σ_{j4} f j3·f j4)` expands by a THIRD `Fin.sum_mul_sum n n (g j1)(g j3)` to
//! `Σ_{j2}Σ_{j4} (f j1·f j2)·(f j3·f j4)` — folded in under nested
//! `Fin.sum_congr`. Finally `pow4(S) = (S·S)·(S·S) = D·D` by `congrArg`²
//! (rewriting each `S·S` factor to `D`), and `D·D` chains to the RHS.
//!
//! ## Soundness
//!
//! Every leaf is CHECKED `Constructive` with an empty admitted-axiom closure
//! (`Fin.sum_mul_sum`, `Fin.sum_congr`, `congrArg`, `Eq.trans`/`Eq.symm`,
//! `Rat.mul`). No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

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

/// Shared atoms for the `pow4` spectral expansion bricks.
#[cfg(test)]
struct Pow4Consts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    rat_mul: Expr,
    fin_sum: Expr,
    fin_sum_mul_sum: Expr,
    fin_sum_congr: Expr,
    eq1: Expr,
    eq_trans: Expr,
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    eq_symm: Expr,
    congr_arg: Expr,
}

#[cfg(test)]
impl Pow4Consts {
    #[cfg(test)]
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_mul_sum: Expr::const_(Name::from_string("Fin.sum_mul_sum"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    #[cfg(test)]
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    #[cfg(test)]
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    #[cfg(test)]
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    #[cfg(test)]
    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), f])
    }
    #[cfg(test)]
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    #[cfg(test)]
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `congrArg (β:=Rat) (α:=Rat) a b g h` : `g a = g b` from `h : a = b`.
    #[cfg(test)]
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    /// `Fin.sum_mul_sum m n F G` : `(Σ_m F)·(Σ_n G) = Σ_m (fun i => Σ_n (fun j => F i·G j))`.
    #[cfg(test)]
    fn sum_mul_sum(&self, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            self.fin_sum_mul_sum.clone(),
            [n.clone(), n.clone(), f.clone(), g.clone()],
        )
    }
    /// `Fin.sum_congr n f g h` : `Σ_n f = Σ_n g` from `h : ∀ i, f i = g i`.
    #[cfg(test)]
    fn sum_congr(&self, n: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.fin_sum_congr.clone(),
            [n.clone(), f.clone(), g.clone(), h],
        )
    }

    // ── integrand builders ──────────────────────────────────────────────────

    /// `fun (j2 : Fin n) => Rat.mul (f a) (f j2)` — the inner pair integrand at
    /// fixed left index value `fa := f a`.
    #[cfg(test)]
    fn pair_fn(&self, parent: &EnvDeclBuilder, n: &Expr, fa: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (j_id, j) = b.fresh_local(fin_n.clone());
        let body = self.mul(fa.clone(), Expr::app(f.clone(), j));
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_n, body))
    }

    /// `h := fun (j1 : Fin n) => Fin.sum n (fun j2 => f j1·f j2)` — the double-sum
    /// integrand `D = Fin.sum n h` (the `Fin.sum_mul_sum n n f f` RHS).
    #[cfg(test)]
    fn h_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (j1_id, j1) = b.fresh_local(fin_n.clone());
        let fa = Expr::app(f.clone(), j1);
        let body = self.sum(n, self.pair_fn(&b, n, &fa, f));
        b.finish_child(b.mk_lam(j1_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (j4 : Fin n) => Rat.mul (Rat.mul (f j1) (f j2)) (Rat.mul (f j3) (f j4))`
    /// — the innermost quartic integrand at fixed `j1,j2,j3` (values supplied as
    /// `f j1·f j2 =: left`, `f j3 =: fj3`).
    #[cfg(test)]
    fn quartic_inner_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        left: &Expr,
        fj3: &Expr,
        f: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (j4_id, j4) = b.fresh_local(fin_n.clone());
        let right = self.mul(fj3.clone(), Expr::app(f.clone(), j4));
        let body = self.mul(left.clone(), right);
        b.finish_child(b.mk_lam(j4_id, BinderInfo::Default, fin_n, body))
    }
}

include!("boolean_analysis_pow4_spectral_build.rs");
include!("boolean_analysis_pow4_noisefn_build.rs");
include!("boolean_analysis_pow4_noisefn_spectral_build.rs");

#[cfg(test)]
impl Environment {
    /// Register `Fin.sum_pow4` — the generic 4-fold-product expansion
    /// `pow4(Σ f) = Σ_{j1}Σ_{j3}Σ_{j2}Σ_{j4} (f j1·f j2)·(f j3·f j4)` (rung 1 of
    /// the `pow4_noisefn_spectral` chain). Three `Fin.sum_mul_sum` applications
    /// glued by `Fin.sum_congr`. CHECKED `Constructive` (empty closure).
    /// Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_fin_sum_pow4_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_pow4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.register_fin_sum_mul_sum_theorem()?;
        // `Fin.sum_congr` is registered by `init_fin_sum`.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_sum_pow4_type(&c),
            value: build_sum_pow4_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_fourfold` — the `noiseFn`-specialized
    /// 4-fold-product expansion of the operator-side 4th moment:
    /// `Σ_jx pow4(noiseFn ρ n F jx) = Σ_jx Σ_{j1}Σ_{j3}Σ_{j2}Σ_{j4}
    ///   (gx jx j1·gx jx j2)·(gx jx j3·gx jx j4)`, where `gx jx jy :=
    /// F(decode jy)·noiseDensityW ρ n (decode jx)(decode jy)`. `Fin.sum_congr`
    /// over `jx` of the pointwise `Fin.sum_pow4 (2^n) (gx jx)` (its LHS
    /// `pow4(Fin.sum (2^n) (gx jx))` is def-eq to `pow4(noiseFn ρ n F jx)` because
    /// `noiseFn` δ-unfolds to that sum). CHECKED `Constructive` (empty closure).
    /// Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_fourfold_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_fourfold");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_boolean_analysis()?; // hcDecode
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_noise_density_w()?;
        self.register_noise_fn()?;
        self.register_fin_sum_pow4_theorem()?;
        // `register_noise_fn`'s `init_boolean_analysis` pass may register this.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4NoiseConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_fourfold_type(&c),
            value: build_fourfold_value(&c),
        })
    }

    /// Register `Rat.mul8_regroup` — the 8-factor regroup
    /// `((w1·g1)·(w2·g2))·((w3·g3)·(w4·g4)) = ((w1·w2)·(w3·w4))·((g1·g2)·(g3·g4))`,
    /// a TOWER of `Rat.mul_mul_mul_comm` (the 4-fold analogue of `regroup_per_s`'s
    /// single mmmc): two block-rewrites under `congrArg` + one top-level mmmc,
    /// glued by `Eq.trans`. Tier 1 of the `pow4_noisefn_spectral` build.
    /// CHECKED `Constructive` (empty closure). Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_rat_mul8_regroup_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul8_regroup");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        // `Rat.mul_mul_mul_comm`'s proof references `Rat.mul_assoc`/`Rat.mul_comm`
        // directly (the idempotent quotient structural lemmas).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        self.register_rat_mul_mul_mul_comm_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Mul8Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_mul8_regroup_type(&c),
            value: build_mul8_regroup_value(&c),
        })
    }

    /// Register `Fin.sum_prod4` — the generic 4-DISTINCT-function product
    /// expansion `(Σf1·Σf2)·(Σf3·Σf4) = Σ_{j1,j3,j2,j4} (f1 j1·f2 j2)·(f3 j3·f4 j4)`,
    /// the carrier converse of `Fin.sum_pow4` (its `f1=f2=f3=f4` case). Three
    /// `Fin.sum_mul_sum` glued by `Fin.sum_congr`. CHECKED `Constructive` (empty
    /// closure). Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_fin_sum_prod4_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_prod4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.register_fin_sum_mul_sum_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_prod4_type(&c),
            value: build_prod4_value(&c),
        })
    }

    /// Register `BoolAnalysis.subsetSum_prod4` — the subsetSum-convention
    /// analogue of `Fin.sum_prod4`:
    /// `(Σ_S P1·Σ_S P2)·(Σ_S P3·Σ_S P4) = Σ_S1Σ_S2Σ_S3Σ_S4 (P1 S1·P2 S2)·(P3 S3·P4 S4)`.
    /// Derived from `Fin.sum_prod4 (2^n) (Pk∘decode)…` (def-eq decode bridge, the
    /// `subsetSum_swap` pattern). CHECKED `Constructive` (empty closure).
    /// Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_subset_sum_prod4_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_prod4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        self.register_fin_sum_prod4_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_ss_prod4_type(&c),
            value: build_ss_prod4_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_subsetsum_x` — Tier-5 rung L1: the
    /// outer-sum bridge of the `pow4_noisefn_fourfold` RHS from `Fin.sum (2^n)`
    /// into `subsetSum n` / `HCPoint` convention (the build plan's "bridge the
    /// top sum ONCE" step):
    /// `Σ_jx pow4(noiseFn ρ n F jx) = subsetSum n (fun x => Σ_{j1,j3,j2,j4}
    ///   (gxd x j1·gxd x j2)·(gxd x j3·gxd x j4))`, `gxd x jy :=
    /// F(decode jy)·noiseDensityW ρ n x (decode jy)`. `Eq.trans` of
    /// `pow4_noisefn_fourfold` with the reducible `subsetSum`↔`Fin.sum` def-eq.
    /// CHECKED `Constructive` (empty closure). Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_subsetsum_x_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_subsetsum_x");
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
        self.register_noise_density_w()?;
        self.register_noise_fn()?;
        self.register_pow4_noisefn_fourfold_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_subsetsum_x_type(&c),
            value: build_subsetsum_x_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_density_unfold` — Tier-5 rung L2: the
    /// density-unfolded form of L1's RHS, each `noiseDensityW ρ n x y` δ-unfolded
    /// to `subsetSum n (fun S => ρ^|S|·(χ_S x·χ_S y))`:
    /// `Σ_jx pow4(noiseFn ρ n F jx) = subsetSum n (fun x => Σ_{j1,j3,j2,j4}
    ///   (gxu x j1·gxu x j2)·(gxu x j3·gxu x j4))`. Proven directly by L1 (def-eq
    /// RHS, `noiseDensityW` reducible). CHECKED `Constructive` (empty closure).
    /// Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_density_unfold_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_density_unfold");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_pow4_noisefn_subsetsum_x_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_density_unfold_type(&c),
            value: build_density_unfold_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_fold_probe` — fold-leg probe
    /// `∀ ρ n F x, quad_rhs(gxu x) = pow4(subsetSum n (l_int x))`.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_fold_probe_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_fold_probe");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        self.register_fin_sum_prod4_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_fold_probe_type(&c),
            value: build_fold_probe_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_spectral_e1` — Tier-5 E0→E1 milestone:
    /// `Σ_jx pow4(noiseFn ρ n F jx) = subsetSum n (fun x => Σ_S1Σ_S3Σ_S2Σ_S4
    ///   (T1·T2)·(T3·T4))`, `Tk = (ρ^|Sk|·χ_Sk x)·A F Sk`. L5 then `subsetSum_congr`
    /// over x of `subsetSum_prod4 n (m_fn x)⁴` (expands `pow4(M x)`). CHECKED
    /// `Constructive` (empty closure). Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_spectral_e1_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_spectral_e1");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_pow4_noisefn_m_form_theorem()?;
        self.register_subset_sum_prod4_theorem()?;
        self.register_subset_sum_congr()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_spectral_e1_type(&c),
            value: build_spectral_e1_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_spectral_e2` — Tier-5 E1→E2 (Fubini):
    /// moves `Σ_x` from outermost to innermost past the four spectral S-sums via a
    /// recursive `subsetSum_swap`/`subsetSum_congr` pull:
    /// `Σ_jx pow4(noiseFn) = subsetSum n (S1 => … S4 => subsetSum n (x =>
    ///   (T1·T2)·(T3·T4)))`. CHECKED `Constructive` (empty closure). Idempotent.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_spectral_e2_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_spectral_e2");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_pow4_noisefn_spectral_e1_theorem()?;
        self.register_subset_sum_swap_theorem()?;
        self.register_subset_sum_congr()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_spectral_e2_type(&c),
            value: build_spectral_e2_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_spectral` — THE TOP RUNG (Form A, §2.1):
    /// `Σ_jx pow4(noiseFn ρ n F jx) = subsetSum n (S1 => S3 => S2 => S4 =>
    ///   ((ρ^|S1|·ρ^|S2|)·(ρ^|S3|·ρ^|S4|)) · (((A S1·A S2)·(A S3·A S4))
    ///     · subsetSum n (x => (χ_S1 x·χ_S2 x)·(χ_S3 x·χ_S4 x))))`,
    /// `A F S = subsetSum n (y => F y·χ_S y)`, inner Σ_x ∏χ kept EXPLICIT
    /// (un-collapsed; nesting (S1,S3,S2,S4) per the leg-peel order). The full
    /// `‖T_ρ F‖₄⁴` spectral expansion: E2 (Fubini) then `ss_congr`-4-deep of the
    /// per-quad regroup (two `Rat.mul8_regroup` + `subsetSum_smul` pull-out).
    /// CHECKED `Constructive` (empty closure). Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_spectral_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_spectral");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_pow4_noisefn_spectral_e2_theorem()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_rat_mul8_regroup_theorem()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_spectral_type(&c),
            value: build_spectral_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_gsum_eq_l` — def-eq probe
    /// `∀ ρ n F x, Fin.sum (2^n)(gxu x) = subsetSum n (l_int x)` by `Eq.refl`.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_gsum_eq_l_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_gsum_eq_l");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_gsum_eq_l_type(&c),
            value: build_gsum_eq_l_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_l_eq_m` — the per-x bridge probe
    /// `∀ ρ n F x, L x = M x` (harness for `l_eq_m`). CHECKED `Constructive`.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_l_eq_m_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_l_eq_m");
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
        self.register_subset_sum_smul_theorem()?;
        self.register_subset_sum_swap_theorem()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_l_eq_m_type(&c),
            value: build_l_eq_m_value(&c),
        })
    }

    /// Register `BoolAnalysis.pow4_noisefn_M_form` — Tier-5 rung L5: folds L2's
    /// density-unfolded quad back to a product of four identical bilinear legs
    /// and rewrites each to the spectral M-form:
    /// `Σ_jx pow4(noiseFn ρ n F jx) = subsetSum n (fun x => pow4 (M x))`,
    /// `M x = subsetSum n (fun S => (ρ^|S|·χ_S x)·A F S)`,
    /// `A F S = subsetSum n (fun y => F y·χ_S y)`. Built from L2 via
    /// `subsetSum_congr` over x of [`Eq.symm Fin.sum_prod4` (fold quad→pow4) then
    /// `congrArg pow4` of the per-x `L x = M x` bridge (5-leg `subsetSum`
    /// smul/swap/regroup chain)]. CHECKED `Constructive` (empty closure).
    /// Idempotent. No axiom added/removed.
    #[cfg(test)]
    pub(crate) fn register_pow4_noisefn_m_form_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pow4_noisefn_M_form");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_pow4_noisefn_density_unfold_theorem()?;
        self.register_fin_sum_prod4_theorem()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_subset_sum_swap_theorem()?;
        // `Rat.mul_mul_mul_comm` / assoc / comm structural lemmas for the regroup.
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow4SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_m_form_type(&c),
            value: build_m_form_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn checked_constructive_theorem(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty"
        );
    }

    #[test]
    fn test_fin_sum_pow4_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_pow4_theorem()
            .expect("register_fin_sum_pow4_theorem");
        checked_constructive_theorem(&env, "Fin.sum_pow4");
    }

    #[test]
    fn test_fin_sum_pow4_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_pow4_theorem().expect("first");
        env.register_fin_sum_pow4_theorem().expect("idempotent");
        checked_constructive_theorem(&env, "Fin.sum_pow4");
    }

    #[test]
    fn test_pow4_noisefn_fourfold_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_fourfold_theorem()
            .expect("register_pow4_noisefn_fourfold_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_fourfold");
    }

    #[test]
    fn test_pow4_noisefn_fourfold_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_fourfold_theorem().expect("first");
        env.register_pow4_noisefn_fourfold_theorem()
            .expect("idempotent");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_fourfold");
    }

    #[test]
    fn test_rat_mul8_regroup_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_rat_mul8_regroup_theorem()
            .expect("register_rat_mul8_regroup_theorem");
        checked_constructive_theorem(&env, "Rat.mul8_regroup");
    }

    #[test]
    fn test_rat_mul8_regroup_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_rat_mul8_regroup_theorem().expect("first");
        env.register_rat_mul8_regroup_theorem().expect("idempotent");
        checked_constructive_theorem(&env, "Rat.mul8_regroup");
    }

    #[test]
    fn test_fin_sum_prod4_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_prod4_theorem()
            .expect("register_fin_sum_prod4_theorem");
        checked_constructive_theorem(&env, "Fin.sum_prod4");
    }

    #[test]
    fn test_fin_sum_prod4_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_prod4_theorem().expect("first");
        env.register_fin_sum_prod4_theorem().expect("idempotent");
        checked_constructive_theorem(&env, "Fin.sum_prod4");
    }

    #[test]
    fn test_subset_sum_prod4_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_prod4_theorem()
            .expect("register_subset_sum_prod4_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.subsetSum_prod4");
    }

    #[test]
    fn test_subset_sum_prod4_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_prod4_theorem().expect("first");
        env.register_subset_sum_prod4_theorem().expect("idempotent");
        checked_constructive_theorem(&env, "BoolAnalysis.subsetSum_prod4");
    }

    #[test]
    fn test_pow4_noisefn_subsetsum_x_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_subsetsum_x_theorem()
            .expect("register_pow4_noisefn_subsetsum_x_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_subsetsum_x");
    }

    #[test]
    fn test_pow4_noisefn_subsetsum_x_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_subsetsum_x_theorem()
            .expect("first");
        env.register_pow4_noisefn_subsetsum_x_theorem()
            .expect("idempotent");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_subsetsum_x");
    }

    #[test]
    fn test_pow4_noisefn_density_unfold_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_density_unfold_theorem()
            .expect("register_pow4_noisefn_density_unfold_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_density_unfold");
    }

    #[test]
    fn test_pow4_noisefn_density_unfold_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_density_unfold_theorem()
            .expect("first");
        env.register_pow4_noisefn_density_unfold_theorem()
            .expect("idempotent");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_density_unfold");
    }

    #[test]
    fn test_pow4_noisefn_spectral_e1_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_spectral_e1_theorem()
            .expect("register_pow4_noisefn_spectral_e1_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_spectral_e1");
    }

    #[test]
    fn test_pow4_noisefn_spectral_e2_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_spectral_e2_theorem()
            .expect("register_pow4_noisefn_spectral_e2_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_spectral_e2");
    }

    #[test]
    fn test_pow4_noisefn_spectral_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_spectral_theorem()
            .expect("register_pow4_noisefn_spectral_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_spectral");
    }

    #[test]
    fn test_pow4_noisefn_spectral_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_spectral_theorem().expect("first");
        env.register_pow4_noisefn_spectral_theorem()
            .expect("idempotent");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_spectral");
    }

    #[test]
    fn test_pow4_noisefn_fold_probe_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_fold_probe_theorem()
            .expect("register_pow4_noisefn_fold_probe_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_fold_probe");
    }

    #[test]
    fn test_pow4_noisefn_gsum_eq_l_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_gsum_eq_l_theorem()
            .expect("register_pow4_noisefn_gsum_eq_l_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_gsum_eq_l");
    }

    #[test]
    fn test_pow4_noisefn_l_eq_m_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_l_eq_m_theorem()
            .expect("register_pow4_noisefn_l_eq_m_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_l_eq_m");
    }

    #[test]
    fn test_pow4_noisefn_m_form_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_m_form_theorem()
            .expect("register_pow4_noisefn_m_form_theorem");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_M_form");
    }

    #[test]
    fn test_pow4_noisefn_m_form_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_pow4_noisefn_m_form_theorem().expect("first");
        env.register_pow4_noisefn_m_form_theorem()
            .expect("idempotent");
        checked_constructive_theorem(&env, "BoolAnalysis.pow4_noisefn_M_form");
    }
}
