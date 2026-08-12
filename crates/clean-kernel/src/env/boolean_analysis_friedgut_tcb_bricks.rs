// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut TCB→3 close — three bounded, self-contained kernel bricks toward the
//! final `friedgut_boolean` assembly. Each is a genuine `Declaration::Theorem`,
//! `Constructive`, with an EMPTY admitted-axiom closure. Hand-constructed `Expr`
//! (no tactics). Idempotent. Gated behind `cfg(any(test, feature = "math-overlays"))`.
//!
//! # BRICK 1 — `BoolAnalysis.friedgut_empty_junta_mass_le_total`
//!
//! ```text
//! ∀ (n : Nat) (f : BoolFn n),
//!   subsetSum n (fun S => ind(notSubsetMask n S ∅) · (f̂ S · f̂ S))
//!     ≤ subsetSum n (fun S => f̂ S · f̂ S)
//! ```
//!
//! where `∅ := fun (_ : Fin n) => Bool.false`. This is the masked Fourier mass
//! `Σ_{S⊄∅} f̂² = Σ_{S≠∅} f̂²` bounded by the TOTAL mass `Σ_all f̂²`. Proved by
//! `subsetSum_le_of_pointwise`: per-`S`, `ind(bit)·X ≤ 1·X = X` with
//! `X := f̂·f̂ ≥ 0` (`sq_nonneg`) and `ind(bit) ≤ 1` (`ind_le_one`) — the
//! `friedgut_high_mask_drop` per-`S` template.
//!
//! NORMALIZATION GAP (honest): the stronger `≤ 1` form additionally needs
//! `Σ_all f̂² = E[f²] = 1`. The landed `subsetSum_parseval_core` proves the
//! UNNORMALIZED Plancherel `Σ_S (Σ_x a·χ_Sx)² = 2^n · Σ_x a·a` over a raw
//! coefficient field `a : HCPoint n → Rat` (NOT in terms of
//! `FourierCoefficient`), and `E[f²] = 1` (`Expect_one`) is for `±1`-valued `f`;
//! bridging those to `Σ_S FourierCoefficient(S)² = 1` is a separate (heavier)
//! assembly. This brick banks the monotonicity half (`≤ Σ_all f̂²`), which is the
//! piece the final close consumes once the `= 1` normalization lands separately.
//!
//! # BRICK 2 — `BoolAnalysis.thresholdJ` (+ two membership lemmas)
//!
//! ```text
//! BoolAnalysis.thresholdJ (n : Nat) (f : BoolFn n) (tau : Rat) : HCPoint n
//!   := fun (i : Fin n) => Rat.ble tau (Influence n f i)
//! ```
//!
//! The threshold junta witness: `i ∈ J ⟺ tau ≤ Inf_i`. Two membership lemmas the
//! final close needs:
//!
//! `BoolAnalysis.thresholdJ_mem_le`:
//! `∀ n f tau i, thresholdJ n f tau i = Bool.true → tau ≤ Influence n f i`
//! (the `influence_threshold_card_le` `hb` direction, via
//! `Rat.le_of_ble_eq_true`).
//!
//! `BoolAnalysis.thresholdJ_not_mem_le`:
//! `∀ n f tau i, Bool.not (thresholdJ n f tau i) = Bool.true → Influence n f i ≤ tau`
//! (the `friedgut_l2_core` `h1m` outside-`J` direction, via
//! `Bool.not b = true ⟹ b = false`, then `Rat.lt_of_ble_eq_false` + `Rat.le_of_lt`).
//!
//! `tau` is kept ABSTRACT (NOT instantiated to `dr²`); that coupling is the
//! assembly's job.
//!
//! # BRICK 3 — `BoolAnalysis.friedgut_low_budget_cancel`
//!
//! ```text
//! ∀ (d : Nat) (K eps I : Rat),
//!   0 < K → 0 < eps → 0 ≤ I → I ≤ K →
//!     natCast(9^d) · (lowDr d K eps · I) ≤ eps / 2
//! ```
//!
//! where `lowDr d K eps := eps / (2 · (natCast(9^d) · K))`. The symbolic LOW-band
//! cancellation: `9^d` cancels WITHOUT materializing — `a · (eps/(2·a·K)) = eps/(2K)`
//! with `a := natCast(9^d) > 0`, then `(eps/(2K))·I ≤ (eps/(2K))·K = eps/2`. `a`
//! stays a symbolic atom (`Nat.pow_pos`-positive); never reduced.
//!
//! NO `sorry` / `sorryAx` / `add_decl_unchecked` / `add_decl_structural` /
//! `native_decide` / `unsafe` / `Real` / `Rat.dist` / new `Axiom`. No axiom added
//! or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared carrier atoms for the three TCB bricks. Spellings byte-match the
/// banked friedgut bricks (`L2Consts`, `CheapRungConsts`, the LOW band).
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
struct TcbConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    bool_not: Expr,
    #[cfg(test)]
    nat_zero: Expr,
    #[cfg(test)]
    nat_succ: Expr,
    rat_mul: Expr,
    #[cfg(test)]
    rat_zero: Expr,
    rat_one: Expr,
    rat_ble: Expr,
    fin: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fourier: Expr,
    subset_sum: Expr,
    ind: Expr,
    not_subset_mask: Expr,
    influence: Expr,
    l0: Level,
    l1: Level,
}

impl TcbConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            bool_not: k("Bool.not"),
            #[cfg(test)]
            nat_zero: k("Nat.zero"),
            #[cfg(test)]
            nat_succ: k("Nat.succ"),
            rat_mul: k("Rat.mul"),
            #[cfg(test)]
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_ble: k("Rat.ble"),
            fin: k("Fin"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            ind: k("BoolAnalysis.ind"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            influence: k("BoolAnalysis.Influence"),
            l0,
            l1,
        }
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
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_ble.clone(), [a, b])
    }
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), a)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S)·f̂(S)`.
    fn x_sq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn not_subset_mask_of(&self, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.not_subset_mask.clone(),
            [n.clone(), s.clone(), j.clone()],
        )
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `LE.le.{0} Rat instLERat a b` — the `Rat`-order conclusion spelling shared
    /// with the banked bricks.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            [
                self.rat.clone(),
                Expr::const_(Name::from_string("instLERat"), vec![]),
                a,
                b,
            ],
        )
    }
    /// `Eq.{2} Bool a b`.
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.bool_.clone(), a, b],
        )
    }
    /// `Eq.refl.{2} Bool a`.
    fn refl_bool(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [self.bool_.clone(), a],
        )
    }
    /// `Eq.subst.{2} Rat motive a b h_eq h_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `congrArg.{1,1} A B a b f h : f a = f b`.
    fn congr_arg(&self, dom: Expr, cod: Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [dom, cod, a, b, f, h],
        )
    }
    /// `∅ : HCPoint n := fun (_ : Fin n) => Bool.false`.
    fn empty_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, self.bool_false.clone()))
    }
}

// ════════════════════ BRICK 1: empty-junta masked mass ≤ total mass ════════════

/// `fun S => ind(notSubsetMask n S ∅)·(f̂·f̂)` — the masked-mass integrand at
/// `J := ∅`.
fn empty_masked_fn(c: &TcbConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let empty = c.empty_fn(&b, n);
    let r = c.ind_of(c.not_subset_mask_of(n, &s, &empty));
    let body = c.mul(r, c.x_sq(n, f, &s));
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `fun S => f̂·f̂` — the total-mass integrand `Σ_all f̂²`.
fn total_mass_fn(c: &TcbConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let body = c.x_sq(n, f, &s);
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

impl Environment {
    /// `BoolAnalysis.friedgut_empty_junta_mass_le_total :
    ///   ∀ (n : Nat) (f : BoolFn n),
    ///     subsetSum n (fun S => ind(notSubsetMask n S ∅)·(f̂·f̂))
    ///       ≤ subsetSum n (fun S => f̂·f̂)`
    ///
    /// The masked Fourier mass `Σ_{S⊄∅} f̂²` is bounded by the total mass
    /// `Σ_all f̂²` (the monotonicity half of `Σ_{S≠∅} f̂² ≤ 1`; the `= 1`
    /// normalization is a separate assembly — see module doc). Proved by
    /// `subsetSum_le_of_pointwise` with per-`S` `ind(bit)·X ≤ 1·X = X`
    /// (`ind_le_one`, `sq_nonneg`, `mul_le_mul_of_nonneg_right`, `one_mul`).
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_friedgut_empty_junta_mass_le_total(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_empty_junta_mass_le_total");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // BoolFn, FourierCoefficient, ind, HCPoint
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_right, sq_nonneg
        self.init_rat_field_inst()?; // Rat.one_mul
        self.init_boolean_analysis_friedgut_masked_finsum()?; // ind_le_one
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_le_of_pointwise()?;
        self.register_not_subset_mask()?;

        let c = TcbConsts::new();
        let mul_le_right =
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]);
        let sq_nonneg = Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]);
        let ind_le_one = Expr::const_(Name::from_string("BoolAnalysis.ind_le_one"), vec![]);
        let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
        let subset_sum_le = Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise"),
            vec![],
        );

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());

            let masked = empty_masked_fn(&c, &b, &n, &f);
            let total = total_mass_fn(&c, &b, &n, &f);
            let ss_masked = c.ssum(&n, masked.clone());
            let ss_total = c.ssum(&n, total.clone());

            if !for_value {
                let concl = c.le(ss_masked, ss_total);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, concl);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            // per_s : ∀ S, masked S ≤ total S.
            //   masked S ≡ R·X, total S ≡ X, R := ind(notSubsetMask n S ∅),
            //   X := f̂·f̂.
            //   X ≥ 0 : sq_nonneg f̂.
            //   R ≤ 1 : ind_le_one (notSubsetMask n S ∅).
            //   mul_le_right X R 1 (ind_le_one R) (X≥0) : R·X ≤ 1·X.
            //   one_mul X : 1·X = X ⟹ subst RHS to X.
            let per_s = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = e.fresh_local(hcp.clone());
                let empty = c.empty_fn(&e, &n);
                let r_bit = c.not_subset_mask_of(&n, &s, &empty);
                let rr = c.ind_of(r_bit.clone()); // R
                let coeff = c.fourier_of(&n, &f, &s);
                let xx = c.mul(coeff.clone(), coeff.clone()); // X = f̂·f̂
                let rx = c.mul(rr.clone(), xx.clone()); // R·X = masked S
                let one_x = c.mul(c.rat_one.clone(), xx.clone()); // 1·X

                // X ≥ 0.
                let x_nonneg = Expr::app(sq_nonneg.clone(), coeff.clone());
                // R ≤ 1.
                let r_le_one = Expr::app(ind_le_one.clone(), r_bit.clone());
                // R·X ≤ 1·X.
                let bound = Expr::apps(
                    mul_le_right.clone(),
                    [
                        xx.clone(),
                        rr.clone(),
                        c.rat_one.clone(),
                        r_le_one,
                        x_nonneg,
                    ],
                );
                // 1·X = X.
                let one_mul_x = Expr::app(one_mul.clone(), xx.clone());
                // subst (motive t => R·X ≤ t) along (1·X → X).
                let motive = {
                    let mut g = EnvDeclBuilder::child_of(&e);
                    let (t_id, t) = g.fresh_local(c.rat.clone());
                    let body = c.le(rx.clone(), t);
                    g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let body = c.subst_rat(motive, one_x, xx.clone(), one_mul_x, bound);
                e.finish_child(e.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };

            // subsetSum_le_of_pointwise n masked total per_s.
            let body = Expr::apps(
                subset_sum_le.clone(),
                [n.clone(), masked.clone(), total.clone(), per_s],
            );
            let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, body);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

// ════════════════════ BRICK 2: thresholdJ witness + membership lemmas ══════════

/// `fun (i : Fin n) => Rat.ble tau (Influence n f i)` — the threshold membership
/// predicate at coordinate `i`.
fn threshold_body_fn(
    c: &TcbConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    tau: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.ble(tau.clone(), c.influence_of(n, f, &i));
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

impl Environment {
    /// Register all of BRICK 2: `thresholdJ` (the threshold-junta witness, a
    /// reducible `Definition`) and its two membership lemmas. Idempotent.
    pub fn init_boolean_analysis_friedgut_threshold_j(&mut self) -> Result<(), EnvError> {
        self.register_threshold_j()?;
        self.register_threshold_j_mem_le()?;
        self.register_threshold_j_not_mem_le()?;
        Ok(())
    }

    /// `BoolAnalysis.thresholdJ (n : Nat) (f : BoolFn n) (tau : Rat) : HCPoint n
    ///   := fun (i : Fin n) => Rat.ble tau (Influence n f i)`.
    ///
    /// The threshold junta: `i ∈ J ⟺ tau ≤ Inf_i`. Reducible
    /// `Declaration::Definition` over the reducible `Rat.ble` / `Influence`
    /// carriers, so theorems over it stay `Constructive` with an empty closure.
    /// Idempotent.
    pub fn register_threshold_j(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.thresholdJ");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        self.init_boolean_analysis()?; // BoolFn, Influence, HCPoint, Fin
        self.register_rat_minmax_proofs()?; // Rat.ble

        let c = TcbConsts::new();
        let hcp = |n: &Expr| c.hcpoint_of(n);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, _f) = b.fresh_local(bf_ty.clone());
            let (tau_id, _tau) = b.fresh_local(c.rat.clone());
            let r = b.mk_pi(tau_id, BinderInfo::Default, c.rat.clone(), hcp(&n));
            let r = b.mk_pi(f_id, BinderInfo::Default, bf_ty, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let (tau_id, tau) = b.fresh_local(c.rat.clone());
            let body = threshold_body_fn(&c, &b, &n, &f, &tau);
            let r = b.mk_lam(tau_id, BinderInfo::Default, c.rat.clone(), body);
            let r = b.mk_lam(f_id, BinderInfo::Default, bf_ty, r);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.thresholdJ_mem_le :
    ///   ∀ (n : Nat) (f : BoolFn n) (tau : Rat) (i : Fin n),
    ///     Eq Bool (thresholdJ n f tau i) Bool.true → Rat.le tau (Influence n f i)`.
    ///
    /// The membership direction: `i ∈ J ⟹ tau ≤ Inf_i`. `thresholdJ n f tau i`
    /// δ-reduces to `Rat.ble tau (Inf_i)`, so the hypothesis is
    /// `Rat.ble tau Inf_i = true` and `Rat.le_of_ble_eq_true` discharges it
    /// directly. This is the `hb` data the level-Markov bound
    /// `influence_threshold_card_le` consumes at `b := thresholdJ n f tau`.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_threshold_j_mem_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.thresholdJ_mem_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_rat_minmax_proofs()?; // Rat.ble, Rat.le_of_ble_eq_true
        self.register_threshold_j()?;

        let c = TcbConsts::new();
        let le_of_ble = Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]);
        let threshold_j = Expr::const_(Name::from_string("BoolAnalysis.thresholdJ"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let (tau_id, tau) = b.fresh_local(c.rat.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, i) = b.fresh_local(fin_n.clone());

            // thresholdJ n f tau i  (δ-reduces to Rat.ble tau (Inf_i)).
            let mem = Expr::apps(
                threshold_j.clone(),
                [n.clone(), f.clone(), tau.clone(), i.clone()],
            );
            let inf_i = c.influence_of(&n, &f, &i);
            let prem = c.eq_bool(mem.clone(), c.bool_true.clone());
            // Conclusion in the `LE.le Rat instLERat` spelling `influence_threshold_card_le`'s
            // `hb` expects (def-eq to the bare `Rat.le` the proof term produces).
            let concl = c.le(tau.clone(), inf_i.clone());

            if !for_value {
                let e = Expr::pi(BinderInfo::Default, prem, concl);
                let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, e);
                let e = b.mk_pi(tau_id, BinderInfo::Default, c.rat.clone(), e);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            let (h_id, h) = b.fresh_local(prem.clone());
            // h : thresholdJ n f tau i = true, which is def-eq to
            //     Rat.ble tau Inf_i = true. Rat.le_of_ble_eq_true tau Inf_i h.
            let body = Expr::apps(le_of_ble.clone(), [tau.clone(), inf_i.clone(), h]);
            let e = b.mk_lam(h_id, BinderInfo::Default, prem, body);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
            let e = b.mk_lam(tau_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.thresholdJ_not_mem_le :
    ///   ∀ (n : Nat) (f : BoolFn n) (tau : Rat) (i : Fin n),
    ///     Eq Bool (Bool.not (thresholdJ n f tau i)) Bool.true
    ///       → Rat.le (Influence n f i) tau`.
    ///
    /// The OUTSIDE-`J` direction `i ∉ J ⟹ Inf_i ≤ tau` (the `h1m` data
    /// `friedgut_l2_core` / `friedgut_restricted_mass_le` consume at the
    /// threshold junta). `thresholdJ n f tau i` δ-reduces to `Rat.ble tau Inf_i`;
    /// from `Bool.not (Rat.ble tau Inf_i) = true` we derive
    /// `Rat.ble tau Inf_i = false` (`Bool.casesOn` eq-thread + `Bool.noConfusion`
    /// for the impossible `true` branch), then `Rat.lt_of_ble_eq_false tau Inf_i`
    /// gives `Inf_i < tau`, and `Rat.le_of_lt` gives `Inf_i ≤ tau`.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_threshold_j_not_mem_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.thresholdJ_not_mem_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?; // Bool.casesOn, Bool.noConfusion, Bool.not
        self.init_boolean_analysis()?;
        self.init_algebra_nnreal_sqrt_strict()?; // Rat.ble, Rat.lt_of_ble_eq_false
        self.init_algebra_rat_inv_pos()?; // Rat.le_of_lt
        self.register_threshold_j()?;

        let c = TcbConsts::new();
        let threshold_j = Expr::const_(Name::from_string("BoolAnalysis.thresholdJ"), vec![]);
        let lt_of_ble_false = Expr::const_(Name::from_string("Rat.lt_of_ble_eq_false"), vec![]);
        let le_of_lt = Expr::const_(Name::from_string("Rat.le_of_lt"), vec![]);
        let no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]);
        let bool_cases = Expr::const_(Name::from_string("Bool.casesOn"), vec![c.l0.clone()]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let (tau_id, tau) = b.fresh_local(c.rat.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, i) = b.fresh_local(fin_n.clone());

            // mem := thresholdJ n f tau i ≡ Rat.ble tau Inf_i (def-eq).
            let mem = Expr::apps(
                threshold_j.clone(),
                [n.clone(), f.clone(), tau.clone(), i.clone()],
            );
            let inf_i = c.influence_of(&n, &f, &i);
            let ble = c.ble(tau.clone(), inf_i.clone()); // Rat.ble tau Inf_i
            let prem = c.eq_bool(c.bnot(mem.clone()), c.bool_true.clone());
            // Conclusion in the `LE.le Rat instLERat` spelling `friedgut_l2_core`'s
            // `h1m` expects (def-eq to the bare `Rat.le` the proof term produces).
            let concl = c.le(inf_i.clone(), tau.clone());

            if !for_value {
                let e = Expr::pi(BinderInfo::Default, prem, concl);
                let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, e);
                let e = b.mk_pi(tau_id, BinderInfo::Default, c.rat.clone(), e);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            let (h_id, h) = b.fresh_local(prem.clone());
            // h : Bool.not mem = true ≡ Bool.not (Rat.ble tau Inf_i) = true.

            // Step A: derive  ble = false  from h.
            //   Bool.casesOn on `ble` with motive
            //     fun (bb : Bool) => (ble = bb) → (ble = false)   (eq-threaded).
            //   - bb = false: heq : ble = false ⟹ goal heq.
            //   - bb = true : heq : ble = true ⟹ Bool.not ble ≡ Bool.not true ≡ false,
            //       but h : Bool.not ble = true transported along heq gives
            //       `false = true`, so Bool.noConfusion discharges the goal.
            // The `h` is captured by the closure (the motive's premise is on `ble`).
            let ble_eq_false = {
                let goal_eq = |bb: Expr| c.eq_bool(ble.clone(), bb);
                // motive : fun (bb : Bool) => (ble = bb) → (ble = false).
                let motive = {
                    let mut e = EnvDeclBuilder::child_of(&b);
                    let (bb_id, bb) = e.fresh_local(c.bool_.clone());
                    let prem2 = c.eq_bool(ble.clone(), bb.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        prem2,
                        c.eq_bool(ble.clone(), c.bool_false.clone()),
                    );
                    e.finish_child(e.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body))
                };
                let _ = goal_eq; // documentation alias

                // false branch : (ble = false) → (ble = false) := id.
                let false_branch = {
                    let mut e = EnvDeclBuilder::child_of(&b);
                    let prem2 = c.eq_bool(ble.clone(), c.bool_false.clone());
                    let (hf_id, hf) = e.fresh_local(prem2.clone());
                    e.finish_child(e.mk_lam(hf_id, BinderInfo::Default, prem2, hf))
                };

                // true branch : (ble = true) → (ble = false).
                //   congrArg Bool.not heq : Bool.not ble = Bool.not true.
                //   Bool.not true ≡ false (def-eq). h : Bool.not ble = true.
                //   trans? Build  false = true  := trans (symm congr) h, then
                //   noConfusion.  Actually: h : Bool.not ble = true ; congr :
                //   Bool.not ble = Bool.not true(≡false). symm congr : false_lit?
                //   We assemble  bad : Bool.not true = true  via subst of h along
                //   congr, where Bool.not true ≡ false def-eq ⟹ `false = true`.
                let true_branch = {
                    let mut e = EnvDeclBuilder::child_of(&b);
                    let prem2 = c.eq_bool(ble.clone(), c.bool_true.clone());
                    let (ht_id, ht) = e.fresh_local(prem2.clone());
                    // f_not := fun (z : Bool) => Bool.not z.
                    let f_not = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (z_id, z) = g.fresh_local(c.bool_.clone());
                        let body = c.bnot(z);
                        g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.bool_.clone(), body))
                    };
                    // congr : Bool.not ble = Bool.not true.
                    let congr = c.congr_arg(
                        c.bool_.clone(),
                        c.bool_.clone(),
                        ble.clone(),
                        c.bool_true.clone(),
                        f_not,
                        ht,
                    );
                    // subst (motive z => z = true) along congr applied to h:
                    //   h : Bool.not ble = true ; congr : Bool.not ble = Bool.not true.
                    //   subst with a := Bool.not ble, b := Bool.not true gives
                    //   `Bool.not true = true`, and Bool.not true ≡ Bool.false
                    //   def-eq ⟹ kernel sees `Bool.false = Bool.true`.
                    let motive_eq = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (z_id, z) = g.fresh_local(c.bool_.clone());
                        let body = c.eq_bool(z, c.bool_true.clone());
                        g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.bool_.clone(), body))
                    };
                    // Eq.subst.{2} Bool motive a b h_eq h_a.
                    let bad = Expr::apps(
                        Expr::const_(Name::from_string("Eq.subst"), vec![c.l1.clone()]),
                        [
                            c.bool_.clone(),
                            motive_eq,
                            c.bnot(ble.clone()),
                            c.bnot(c.bool_true.clone()),
                            congr,
                            h.clone(),
                        ],
                    );
                    // bad : Bool.not true = true ≡ Bool.false = Bool.true.
                    //   @Bool.noConfusion.{0} (ble = false) false true bad.
                    let goal = c.eq_bool(ble.clone(), c.bool_false.clone());
                    let body = Expr::apps(
                        no_conf.clone(),
                        [goal, c.bool_false.clone(), c.bool_true.clone(), bad],
                    );
                    e.finish_child(e.mk_lam(ht_id, BinderInfo::Default, prem2, body))
                };

                // @Bool.casesOn motive ble false_branch true_branch (Eq.refl ble) : ble = false.
                Expr::apps(
                    bool_cases.clone(),
                    [
                        motive,
                        ble.clone(),
                        false_branch,
                        true_branch,
                        c.refl_bool(ble.clone()),
                    ],
                )
            };

            // Step B: Rat.lt_of_ble_eq_false tau Inf_i (ble_eq_false) : Inf_i < tau.
            let lt = Expr::apps(
                lt_of_ble_false.clone(),
                [tau.clone(), inf_i.clone(), ble_eq_false],
            );
            // Step C: Rat.le_of_lt Inf_i tau lt : Inf_i ≤ tau.
            let body = Expr::apps(le_of_lt.clone(), [inf_i.clone(), tau.clone(), lt]);

            let e = b.mk_lam(h_id, BinderInfo::Default, prem, body);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
            let e = b.mk_lam(tau_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

// ════════════════════ BRICK 3: LOW-band symbolic cancellation ══════════════════

/// Extra atoms for BRICK 3 (division / inverse / Nat-pow positivity).
struct Brick3Consts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_two: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    nat: Expr,
    nat_zero: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    nat_pow: Expr,
    l1: Level,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl Brick3Consts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_two: k("Rat.two"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            nat_pow: k("Nat.pow"),
            l1: Level::succ(Level::zero()),
        }
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(succ.clone(), e);
        }
        e
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    /// `9^d := Nat.pow 9 d`.
    fn pow9_nat(&self, d: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(9), d.clone()])
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.nat_lit(1),
            ],
        )
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [a, b])
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    #[cfg(test)]
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [self.rat.clone(), a],
        )
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `congrArg.{1,1} Rat Rat a b f h : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
    fn mul_one(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
            a.clone(),
        )
    }
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_pos"), vec![]),
            [a, b, ha, hb],
        )
    }
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h_le: Expr, h0: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [a, b, cc, h_le, h0],
        )
    }
    /// `Rat.le_of_lt a b h : Rat.le a b`.
    fn le_of_lt(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_lt"), vec![]),
            [a, b, h],
        )
    }
    /// `Rat.le_trans a b c h1 h2 : a ≤ c`.
    #[cfg(test)]
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `Rat.div_mul_cancel_pos a b (0<b) : (a/b)·b = a`.
    fn div_mul_cancel_pos(&self, a: Expr, b: Expr, hpos: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.div_mul_cancel_pos"), vec![]),
            [a, b, hpos],
        )
    }
}

impl Environment {
    /// Register the BRICK 3 bundle: the `0 < 2` and `2·Y = eps → Y = eps/2`
    /// helpers and `friedgut_low_budget_cancel`. Idempotent.
    pub fn init_boolean_analysis_friedgut_low_budget(&mut self) -> Result<(), EnvError> {
        self.register_rat_zero_lt_two()?;
        self.register_rat_eq_half_of_two_mul()?;
        self.register_friedgut_low_budget_cancel()?;
        Ok(())
    }

    /// `Rat.zero_lt_two : Rat.lt Rat.zero Rat.two`.
    ///
    /// `0 < 2` via `Rat.lt_trans 0 1 2 zero_lt_one one_lt_two`, with
    /// `one_lt_two : 1 < 2` built from `add_lt_add_left 0 1 1 zero_lt_one`
    /// (`1+0 < 1+1 ≡ 1 < 2`) transported along `add_zero 1`. Mirrors the
    /// `Rat.two_ne_zero` sub-build. Kernel-checked, `Constructive`, empty
    /// closure. Idempotent.
    pub fn register_rat_zero_lt_two(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_lt_two");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_algebra_rat_halves()?; // Rat.two
        self.init_rat_field_inst()?; // Rat.add_zero
        self.init_rat_linear_order()?; // Rat.zero_lt_one, Rat.lt_trans
        self.init_algebra_nnreal_add_laws()?; // Rat.add_lt_add_left

        let c = Brick3Consts::new();
        let add = |a: Expr, b: Expr| {
            Expr::apps(Expr::const_(Name::from_string("Rat.add"), vec![]), [a, b])
        };
        let zero = c.rat_zero.clone();
        let one = c.rat_one.clone();
        let two = c.rat_two.clone();
        let zero_lt_one = Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]);
        let add_lt_add_left = Expr::const_(Name::from_string("Rat.add_lt_add_left"), vec![]);
        let add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
        let lt_trans = Expr::const_(Name::from_string("Rat.lt_trans"), vec![]);

        let ty = c.lt(zero.clone(), two.clone());

        // one_lt_two : 1 < 2 (≡ 1 < 1+1).
        //   step : (1+0) < (1+1)  := add_lt_add_left 0 1 1 zero_lt_one.
        //   transport along add_zero 1 : 1+0 = 1   (motive t => t < two).
        let one_plus_zero = add(one.clone(), zero.clone());
        let step = Expr::apps(
            add_lt_add_left.clone(),
            [zero.clone(), one.clone(), one.clone(), zero_lt_one.clone()],
        );
        let motive_lt = {
            let mut mb = EnvDeclBuilder::new();
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, two.clone());
            mb.finish(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let one_lt_two = c.subst_rat(
            motive_lt,
            one_plus_zero,
            one.clone(),
            Expr::app(add_zero.clone(), one.clone()),
            step,
        );
        // 0 < 2.
        let value = Expr::apps(
            lt_trans,
            [
                zero.clone(),
                one.clone(),
                two.clone(),
                zero_lt_one,
                one_lt_two,
            ],
        );

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.eq_half_of_two_mul : ∀ (eps Y : Rat),
    ///   Eq Rat (Rat.mul Rat.two Y) eps → Eq Rat Y (Rat.div eps Rat.two)`.
    ///
    /// From `2·Y = eps`, conclude `Y = eps/2`. `eps/2 ≡ eps·2⁻¹` (reducible).
    /// Chain: `eps/2 =[congr (·/2) (symm h)] (2·Y)/2 ≡ (2·Y)·2⁻¹
    ///        =[mul_assoc 2 Y 2⁻¹ ; comm] Y·(2·2⁻¹) =[mul_inv_cancel 2] Y·1
    ///        =[mul_one] Y`, then `symm`. Uses `Rat.mul_inv_cancel` (`2 ≠ 0`
    ///  from `Rat.two_ne_zero`) — NO `0 < 2` needed. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_rat_eq_half_of_two_mul(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.eq_half_of_two_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_algebra_rat_halves()?; // Rat.two, Rat.two_ne_zero
        self.init_rat_field_inst()?; // Rat.mul_assoc, Rat.mul_comm, Rat.mul_one
        self.init_algebra_rat_inv_pos()?; // Rat.div, Rat.inv surface
        self.init_algebra_rat_div_mul_cancel()?; // Rat.div reducible carrier
        self.init_rat_quotient_poc()?; // Rat.mul_inv_cancel (quotient payoff)

        let c = Brick3Consts::new();
        let two = c.rat_two.clone();
        let inv = |a: Expr| Expr::app(Expr::const_(Name::from_string("Rat.inv"), vec![]), a);
        let two_inv = inv(two.clone());
        let mul_inv_cancel = Expr::const_(Name::from_string("Rat.mul_inv_cancel"), vec![]);
        let two_ne_zero = Expr::const_(Name::from_string("Rat.two_ne_zero"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let two_y = c.mul(two.clone(), y.clone());
            let prem = c.eq_rat(two_y.clone(), eps.clone());
            let half = c.div(eps.clone(), two.clone()); // eps/2 ≡ eps·2⁻¹
            let concl = c.eq_rat(y.clone(), half.clone());

            if !for_value {
                let e = Expr::pi(BinderInfo::Default, prem, concl);
                let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
                return b.finish(b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e));
            }

            let (h_id, h) = b.fresh_local(prem.clone());
            // Build `half = Y` then symm.
            //   s0 : eps/2 = (2·Y)/2     congr (fun z => z/2) (symm h : eps = 2·Y).
            let two_y_half = c.div(two_y.clone(), two.clone()); // (2·Y)/2 ≡ (2·Y)·2⁻¹
            let f_div2 = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = g.fresh_local(c.rat.clone());
                let body = c.div(z, two.clone());
                g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let symm_h = c.symm_rat(two_y.clone(), eps.clone(), h);
            let s0 = c.congr_arg(eps.clone(), two_y.clone(), f_div2, symm_h);
            // (2·Y)/2 ≡ (2·Y)·2⁻¹ (def-eq). s1 : (2·Y)·2⁻¹ = Y·(2·2⁻¹).
            //   = mul_assoc 2 Y 2⁻¹ : (2·Y)·2⁻¹ = 2·(Y·2⁻¹) ; then comm chain.
            // We instead go: (2·Y)·2⁻¹
            //   =[mul_assoc 2 Y 2⁻¹]      2·(Y·2⁻¹)
            //   =[congr (2·_) (mul_comm Y 2⁻¹)] 2·(2⁻¹·Y)
            //   =[symm mul_assoc 2 2⁻¹ Y]  (2·2⁻¹)·Y
            //   =[congr (_·Y) (mul_inv_cancel 2)] 1·Y
            //   =[mul_comm 1 Y ; mul_one Y]  Y.
            let two_y_invr = c.mul(two_y.clone(), two_inv.clone()); // (2·Y)·2⁻¹
            let y_invr = c.mul(y.clone(), two_inv.clone()); // Y·2⁻¹
            let invr_y = c.mul(two_inv.clone(), y.clone()); // 2⁻¹·Y
            let two_yinvr = c.mul(two.clone(), y_invr.clone()); // 2·(Y·2⁻¹)
            let two_invry = c.mul(two.clone(), invr_y.clone()); // 2·(2⁻¹·Y)
            let twoinv_mul = c.mul(two.clone(), two_inv.clone()); // 2·2⁻¹
            let twoinv_y = c.mul(twoinv_mul.clone(), y.clone()); // (2·2⁻¹)·Y
            let one_y = c.mul(c.rat_one.clone(), y.clone()); // 1·Y
            let y_one = c.mul(y.clone(), c.rat_one.clone()); // Y·1

            // a1 : (2·Y)·2⁻¹ = 2·(Y·2⁻¹).
            let a1 = c.mul_assoc(two.clone(), y.clone(), two_inv.clone());
            // a2 : 2·(Y·2⁻¹) = 2·(2⁻¹·Y)   congr (2·_) (mul_comm Y 2⁻¹).
            let f_two_l = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = g.fresh_local(c.rat.clone());
                let body = c.mul(two.clone(), z);
                g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let a2 = c.congr_arg(
                y_invr.clone(),
                invr_y.clone(),
                f_two_l,
                c.mul_comm(y.clone(), two_inv.clone()),
            );
            // a3 : 2·(2⁻¹·Y) = (2·2⁻¹)·Y   symm (mul_assoc 2 2⁻¹ Y).
            let a3 = c.symm_rat(
                twoinv_y.clone(),
                two_invry.clone(),
                c.mul_assoc(two.clone(), two_inv.clone(), y.clone()),
            );
            // a4 : (2·2⁻¹)·Y = 1·Y   congr (_·Y) (mul_inv_cancel 2 two_ne_zero).
            let f_r_y = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = g.fresh_local(c.rat.clone());
                let body = c.mul(z, y.clone());
                g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let tw_inv_one = Expr::apps(mul_inv_cancel.clone(), [two.clone(), two_ne_zero.clone()]);
            let a4 = c.congr_arg(twoinv_mul.clone(), c.rat_one.clone(), f_r_y, tw_inv_one);
            // a5 : 1·Y = Y·1   mul_comm 1 Y.
            let a5 = c.mul_comm(c.rat_one.clone(), y.clone());
            // a6 : Y·1 = Y   mul_one Y.
            let a6 = c.mul_one(&y);

            // Chain (2·Y)·2⁻¹ = Y :
            let t1 = c.trans_rat(
                two_y_invr.clone(),
                two_yinvr.clone(),
                two_invry.clone(),
                a1,
                a2,
            );
            let t2 = c.trans_rat(
                two_y_invr.clone(),
                two_invry.clone(),
                twoinv_y.clone(),
                t1,
                a3,
            );
            let t3 = c.trans_rat(two_y_invr.clone(), twoinv_y.clone(), one_y.clone(), t2, a4);
            let t4 = c.trans_rat(two_y_invr.clone(), one_y.clone(), y_one.clone(), t3, a5);
            let two_y_invr_eq_y = c.trans_rat(two_y_invr.clone(), y_one.clone(), y.clone(), t4, a6);
            // half = (2·Y)/2 ≡ (2·Y)·2⁻¹ (def-eq) = Y. Compose s0 with the chain:
            //   s0 : eps/2 = (2·Y)/2 ;  two_y_invr_eq_y : (2·Y)·2⁻¹ = Y (def-eq LHS).
            let half_eq_y = c.trans_rat(
                half.clone(),
                two_y_half.clone(),
                y.clone(),
                s0,
                two_y_invr_eq_y,
            );
            // Y = eps/2.
            let body = c.symm_rat(half.clone(), y.clone(), half_eq_y);

            let e = b.mk_lam(h_id, BinderInfo::Default, prem, body);
            let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.friedgut_low_budget_cancel :
    ///   ∀ (d : Nat) (K eps I : Rat),
    ///     Rat.lt 0 K → Rat.lt 0 eps → Rat.le 0 I → Rat.le I K →
    ///       Rat.le (Rat.mul (natCast (Nat.pow 9 d))
    ///                       (Rat.mul (lowDr d K eps) I))
    ///              (Rat.div eps Rat.two)`
    ///
    /// where `lowDr d K eps := Rat.div eps (Rat.mul Rat.two
    ///   (Rat.mul (natCast (Nat.pow 9 d)) K))` (= `eps/(2·a·K)`, `a := 9^d`).
    ///
    /// The symbolic LOW-band cancellation: `a := natCast(9^d)` stays a positive
    /// atom (`0 < a` via `natCast_nonneg` + `natCast_ne_zero_of_pos ∘ pow≥1`,
    /// `lt_iff_le_not_le`), and `9^d` cancels WITHOUT materializing:
    ///   `a·(lowDr·I) ≤ a·(lowDr·K)`   (`mul_le_mul_of_nonneg_left`, `I≤K`, `0≤a·lowDr`),
    ///   `a·(lowDr·K) = lowDr·(a·K)`   (comm/assoc),
    ///   `2·(lowDr·(a·K)) = lowDr·B = eps`  (`div_mul_cancel_pos`, `B := 2·(a·K)`),
    ///   so `lowDr·(a·K) = eps/2`   (`Rat.eq_half_of_two_mul`).
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_friedgut_low_budget_cancel(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_low_budget_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_nat()?;
        self.init_algebra_rat_halves()?; // Rat.two
        self.init_rat_field_inst()?; // mul_assoc, mul_comm, mul_one
        self.init_rat_linear_order()?; // mul_pos, le_antisymm, lt_iff_le_not_le, lt_trans, zero_lt_one
        self.init_algebra_rat_div_mul_cancel()?; // div_mul_cancel_pos, Rat.div
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.init_algebra_rat_inv_pos()?; // Rat.le_of_lt
        self.register_expect_one_theorems()?; // Nat.one_le_two_pow, Rat.natCast_ne_zero_of_pos
        self.register_natcast_nonneg()?; // BoolAnalysis.natCast_nonneg
        self.register_nat_pow_le_pow_right_proof()?; // Nat.pow_le_pow_right
        self.register_rat_zero_lt_two()?;
        self.register_rat_eq_half_of_two_mul()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = Brick3Consts::new();
        let natcast_nonneg = Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]);
        let natcast_ne_zero = Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]);
        let pow_le_pow_right = Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]);
        let le_antisymm = Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]);
        let lt_iff = Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]);
        let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let zero_lt_two = Expr::const_(Name::from_string("Rat.zero_lt_two"), vec![]);
        let eq_half = Expr::const_(Name::from_string("Rat.eq_half_of_two_mul"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        let nat_zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
        let _false_c = Expr::const_(Name::from_string("False"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (k_id, kk) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (i_id, ii) = b.fresh_local(c.rat.clone());

            let a = c.natcast(&c.pow9_nat(&d)); // a := natCast(9^d)
            let a_k = c.mul(a.clone(), kk.clone()); // a·K
            let big_den = c.mul(c.rat_two.clone(), a_k.clone()); // B := 2·(a·K)
            let low_dr = c.div(eps.clone(), big_den.clone()); // lowDr = eps/B
            let lhs = c.mul(a.clone(), c.mul(low_dr.clone(), ii.clone())); // a·(lowDr·I)
            let half = c.div(eps.clone(), c.rat_two.clone()); // eps/2

            let hk_ty = c.lt(c.rat_zero.clone(), kk.clone());
            let heps_ty = c.lt(c.rat_zero.clone(), eps.clone());
            let hi0_ty = c.le(c.rat_zero.clone(), ii.clone());
            let hik_ty = c.le(ii.clone(), kk.clone());
            let concl = c.le(lhs.clone(), half.clone());

            if !for_value {
                let (hk_id, _) = b.fresh_local(hk_ty.clone());
                let (heps_id, _) = b.fresh_local(heps_ty.clone());
                let (hi0_id, _) = b.fresh_local(hi0_ty.clone());
                let (hik_id, _) = b.fresh_local(hik_ty.clone());
                let e = b.mk_pi(hik_id, BinderInfo::Default, hik_ty, concl);
                let e = b.mk_pi(hi0_id, BinderInfo::Default, hi0_ty, e);
                let e = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, e);
                let e = b.mk_pi(hk_id, BinderInfo::Default, hk_ty, e);
                let e = b.mk_pi(i_id, BinderInfo::Default, c.rat.clone(), e);
                let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
                let e = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), e);
                return b.finish(b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e));
            }

            let (hk_id, hk) = b.fresh_local(hk_ty.clone());
            let (heps_id, heps) = b.fresh_local(heps_ty.clone());
            // `0 ≤ I` is part of the contract but not needed by this proof
            // (`I ≤ K` + `0 ≤ a·lowDr` suffice); its binder is still introduced.
            let (hi0_id, _hi0) = b.fresh_local(hi0_ty.clone());
            let (hik_id, hik) = b.fresh_local(hik_ty.clone());

            // ── 0 < a := natCast(9^d) ──
            // one_le_9pow : Nat.le 1 (9^d) := Nat.pow_le_pow_right 9 0 d (1≤9) (0≤d).
            //   (pow 9 0 ≡ 1 def-eq, so the result type is Nat.le 1 (9^d).)
            let one = c.nat_lit(1);
            // 1 ≤ 9 := Nat.le.step^8 (Nat.le.refl 1).
            let mut h_1le9 = Expr::app(nat_le_refl.clone(), one.clone());
            {
                let mut cur = one.clone();
                for _ in 0..8 {
                    let nxt = Expr::app(
                        Expr::const_(Name::from_string("Nat.succ"), vec![]),
                        cur.clone(),
                    );
                    h_1le9 = Expr::apps(nat_le_step.clone(), [one.clone(), cur.clone(), h_1le9]);
                    cur = nxt;
                }
            }
            let zero_le_d = Expr::app(nat_zero_le.clone(), d.clone());
            let one_le_9pow = Expr::apps(
                pow_le_pow_right.clone(),
                [
                    c.nat_lit(9),
                    c.nat_zero.clone(),
                    d.clone(),
                    h_1le9,
                    zero_le_d,
                ],
            );
            // 0 ≤ a.
            let h0a = Expr::app(natcast_nonneg.clone(), c.pow9_nat(&d));
            // a ≠ 0 := natCast_ne_zero_of_pos (9^d) one_le_9pow.
            let ha_ne = Expr::apps(natcast_ne_zero.clone(), [c.pow9_nat(&d), one_le_9pow]);
            // not_a_le_0 : ¬(a ≤ 0) := fun hle => ha_ne (le_antisymm a 0 hle h0a).
            let not_a_le0 = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let a_le0_ty = c.le(a.clone(), c.rat_zero.clone());
                let (hle_id, hle) = g.fresh_local(a_le0_ty.clone());
                let a_eq0 = Expr::apps(
                    le_antisymm.clone(),
                    [a.clone(), c.rat_zero.clone(), hle, h0a.clone()],
                );
                let body = Expr::app(ha_ne.clone(), a_eq0);
                g.finish_child(g.mk_lam(hle_id, BinderInfo::Default, a_le0_ty, body))
            };
            // ha_pos : 0 < a := Iff.mpr (lt_iff_le_not_le 0 a) (And.intro h0a not_a_le0).
            let lt0a = c.lt(c.rat_zero.clone(), a.clone());
            let le0a = c.le(c.rat_zero.clone(), a.clone());
            let not_le_a0 = Expr::app(not_c.clone(), c.le(a.clone(), c.rat_zero.clone()));
            let and_pair = Expr::apps(
                and_intro.clone(),
                [le0a.clone(), not_le_a0.clone(), h0a.clone(), not_a_le0],
            );
            let iff_la = Expr::apps(lt_iff.clone(), [c.rat_zero.clone(), a.clone()]);
            let and_ty = Expr::apps(
                Expr::const_(Name::from_string("And"), vec![]),
                [le0a, not_le_a0],
            );
            let ha_pos = Expr::apps(
                iff_mpr.clone(),
                [lt0a.clone(), and_ty.clone(), iff_la, and_pair],
            );

            // ── 0 < B := 2·(a·K) ──
            let h_ak_pos = c.mul_pos(a.clone(), kk.clone(), ha_pos.clone(), hk.clone());
            let hb_pos = c.mul_pos(
                c.rat_two.clone(),
                a_k.clone(),
                zero_lt_two.clone(),
                h_ak_pos,
            );

            // ── lowDr·B = eps   (div_mul_cancel_pos eps B hb_pos) ──
            let lowdr_b = c.mul(low_dr.clone(), big_den.clone());
            let lowdr_b_eq_eps = c.div_mul_cancel_pos(eps.clone(), big_den.clone(), hb_pos);

            // ── 2·(lowDr·(a·K)) = eps ──
            // lowDr·B = lowDr·(2·(a·K)).  reassoc to 2·(lowDr·(a·K)):
            //   r1 : lowDr·(2·(a·K)) = (lowDr·2)·(a·K)   symm (mul_assoc lowDr 2 (a·K)).
            //   r2 : (lowDr·2)·(a·K) = (2·lowDr)·(a·K)   congr (_·(a·K)) (mul_comm lowDr 2).
            //   r3 : (2·lowDr)·(a·K) = 2·(lowDr·(a·K))   mul_assoc 2 lowDr (a·K).
            let lowdr_2 = c.mul(low_dr.clone(), c.rat_two.clone()); // lowDr·2
            let two_lowdr = c.mul(c.rat_two.clone(), low_dr.clone()); // 2·lowDr
            let lowdr_ak = c.mul(low_dr.clone(), a_k.clone()); // lowDr·(a·K) = Y
            let lowdr2_ak = c.mul(lowdr_2.clone(), a_k.clone()); // (lowDr·2)·(a·K)
            let twolowdr_ak = c.mul(two_lowdr.clone(), a_k.clone()); // (2·lowDr)·(a·K)
            let two_lowdr_ak = c.mul(c.rat_two.clone(), lowdr_ak.clone()); // 2·(lowDr·(a·K))

            let r1 = c.symm_rat(
                lowdr2_ak.clone(),
                lowdr_b.clone(),
                c.mul_assoc(low_dr.clone(), c.rat_two.clone(), a_k.clone()),
            );
            let f_r_ak = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = g.fresh_local(c.rat.clone());
                let body = c.mul(z, a_k.clone());
                g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let r2 = c.congr_arg(
                lowdr_2.clone(),
                two_lowdr.clone(),
                f_r_ak,
                c.mul_comm(low_dr.clone(), c.rat_two.clone()),
            );
            let r3 = c.mul_assoc(c.rat_two.clone(), low_dr.clone(), a_k.clone());
            // chain : lowDr·B = 2·(lowDr·(a·K)).
            let cc1 = c.trans_rat(
                lowdr_b.clone(),
                lowdr2_ak.clone(),
                twolowdr_ak.clone(),
                r1,
                r2,
            );
            let lowdrb_eq_2y = c.trans_rat(
                lowdr_b.clone(),
                twolowdr_ak.clone(),
                two_lowdr_ak.clone(),
                cc1,
                r3,
            );
            // 2·(lowDr·(a·K)) = eps   := trans (symm lowdrb_eq_2y) lowdr_b_eq_eps.
            let two_y_eq_eps = c.trans_rat(
                two_lowdr_ak.clone(),
                lowdr_b.clone(),
                eps.clone(),
                c.symm_rat(lowdr_b.clone(), two_lowdr_ak.clone(), lowdrb_eq_2y),
                lowdr_b_eq_eps,
            );

            // ── lowDr·(a·K) = eps/2   (eq_half_of_two_mul eps (lowDr·(a·K)) two_y_eq_eps) ──
            let y_eq_half = Expr::apps(
                eq_half.clone(),
                [eps.clone(), lowdr_ak.clone(), two_y_eq_eps],
            );

            // ── a·(lowDr·K) = lowDr·(a·K)   (comm/assoc) ──
            // a·(lowDr·K)
            //   =[mul_assoc a lowDr K]? no — a·(lowDr·K); want lowDr·(a·K).
            //   q1 : a·(lowDr·K) = (a·lowDr)·K     symm (mul_assoc a lowDr K).
            //   q2 : (a·lowDr)·K = (lowDr·a)·K     congr (_·K) (mul_comm a lowDr).
            //   q3 : (lowDr·a)·K = lowDr·(a·K)     mul_assoc lowDr a K.
            let low_k = c.mul(low_dr.clone(), kk.clone()); // lowDr·K
            let a_lowk = c.mul(a.clone(), low_k.clone()); // a·(lowDr·K)
            let a_lowdr = c.mul(a.clone(), low_dr.clone()); // a·lowDr
            let lowdr_a = c.mul(low_dr.clone(), a.clone()); // lowDr·a
            let a_lowdr_k = c.mul(a_lowdr.clone(), kk.clone()); // (a·lowDr)·K
            let lowdr_a_k = c.mul(lowdr_a.clone(), kk.clone()); // (lowDr·a)·K

            let q1 = c.symm_rat(
                a_lowdr_k.clone(),
                a_lowk.clone(),
                c.mul_assoc(a.clone(), low_dr.clone(), kk.clone()),
            );
            let f_r_k = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = g.fresh_local(c.rat.clone());
                let body = c.mul(z, kk.clone());
                g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let q2 = c.congr_arg(
                a_lowdr.clone(),
                lowdr_a.clone(),
                f_r_k,
                c.mul_comm(a.clone(), low_dr.clone()),
            );
            let q3 = c.mul_assoc(low_dr.clone(), a.clone(), kk.clone());
            let qc1 = c.trans_rat(a_lowk.clone(), a_lowdr_k.clone(), lowdr_a_k.clone(), q1, q2);
            let a_lowk_eq_y =
                c.trans_rat(a_lowk.clone(), lowdr_a_k.clone(), lowdr_ak.clone(), qc1, q3);
            // a·(lowDr·K) = eps/2  := trans a_lowk_eq_y y_eq_half.
            let a_lowk_eq_half = c.trans_rat(
                a_lowk.clone(),
                lowdr_ak.clone(),
                half.clone(),
                a_lowk_eq_y,
                y_eq_half,
            );

            // ── a·(lowDr·I) ≤ a·(lowDr·K) ──
            // 0 < lowDr := Rat.div_pos eps B heps hB   (rebuild 0<B; hb_pos was consumed).
            let div_pos = Expr::const_(Name::from_string("Rat.div_pos"), vec![]);
            let hb_pos2 = c.mul_pos(
                c.rat_two.clone(),
                a_k.clone(),
                zero_lt_two.clone(),
                c.mul_pos(a.clone(), kk.clone(), ha_pos.clone(), hk.clone()),
            );
            let h_lowdr_pos = Expr::apps(
                div_pos,
                [eps.clone(), big_den.clone(), heps.clone(), hb_pos2],
            );
            // 0 ≤ lowDr := Rat.le_of_lt 0 lowDr h_lowdr_pos.
            let h0_lowdr = c.le_of_lt(c.rat_zero.clone(), low_dr.clone(), h_lowdr_pos);
            // lowDr·I ≤ lowDr·K := mul_le_left lowDr I K hik (0≤lowDr).
            let low_i = c.mul(low_dr.clone(), ii.clone()); // lowDr·I
            let inner_le = c.mul_le_left(
                low_dr.clone(),
                ii.clone(),
                kk.clone(),
                hik.clone(),
                h0_lowdr,
            );
            // a·(lowDr·I) ≤ a·(lowDr·K) := mul_le_left a (lowDr·I) (lowDr·K) inner_le (0≤a).
            let outer_le = c.mul_le_left(
                a.clone(),
                low_i.clone(),
                low_k.clone(),
                inner_le,
                h0a.clone(),
            );
            // outer_le : a·(lowDr·I) ≤ a·(lowDr·K). Transport RHS to eps/2 via
            //   subst (motive t => a·(lowDr·I) ≤ t) along a_lowk_eq_half.
            let motive_le = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.le(lhs.clone(), t);
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let proof = c.subst_rat(
                motive_le,
                a_lowk.clone(),
                half.clone(),
                a_lowk_eq_half,
                outer_le,
            );

            let e = b.mk_lam(hik_id, BinderInfo::Default, hik_ty, proof);
            let e = b.mk_lam(hi0_id, BinderInfo::Default, hi0_ty, e);
            let e = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, e);
            let e = b.mk_lam(hk_id, BinderInfo::Default, hk_ty, e);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_friedgut_empty_junta_mass_le_total_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_empty_junta_mass_le_total()
            .expect("register_friedgut_empty_junta_mass_le_total");
        env.register_friedgut_empty_junta_mass_le_total()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_empty_junta_mass_le_total");
    }

    #[test]
    fn test_threshold_j_is_reducible_definition_empty_closure() {
        let mut env = Environment::with_prelude();
        env.register_threshold_j().expect("register_threshold_j");
        env.register_threshold_j().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.thresholdJ");
        let info = env.get_const(&nm).expect("thresholdJ registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "thresholdJ must be a Definition"
        );
        assert!(
            info.is_reducible,
            "thresholdJ must be a reducible Definition"
        );
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("thresholdJ must kernel-check: {e:?}"));
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "thresholdJ closure must be empty, got {:?}",
            env.axiom_deps(&nm)
        );
    }

    #[test]
    fn test_threshold_j_mem_le_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_threshold_j_mem_le()
            .expect("register_threshold_j_mem_le");
        env.register_threshold_j_mem_le().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.thresholdJ_mem_le");
    }

    #[test]
    fn test_threshold_j_not_mem_le_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_threshold_j_not_mem_le()
            .expect("register_threshold_j_not_mem_le");
        env.register_threshold_j_not_mem_le().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.thresholdJ_not_mem_le");
    }

    #[test]
    fn test_rat_zero_lt_two_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_zero_lt_two()
            .expect("register_rat_zero_lt_two");
        env.register_rat_zero_lt_two().expect("idempotent");
        check_constructive(&env, "Rat.zero_lt_two");
    }

    #[test]
    fn test_rat_eq_half_of_two_mul_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_eq_half_of_two_mul()
            .expect("register_rat_eq_half_of_two_mul");
        env.register_rat_eq_half_of_two_mul().expect("idempotent");
        check_constructive(&env, "Rat.eq_half_of_two_mul");
    }

    #[test]
    fn test_friedgut_low_budget_cancel_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_low_budget_cancel()
            .expect("register_friedgut_low_budget_cancel");
        env.register_friedgut_low_budget_cancel()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_low_budget_cancel");
    }
}
