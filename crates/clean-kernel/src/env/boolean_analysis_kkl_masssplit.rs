// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL conditional-bound keystone — the **variance level-split** identity.
//!
//! The sharp-KKL roadmap (`designs/2026-06-13-sharp-kkl-max-influence-roadmap.md`,
//! warning header) replaced the FALSE `deriv_level_mass_lower` (R4) / `hc_dual_sharp`
//! (R6) with the **conditional edge-isoperimetric bound**
//! `max_i Inf_i ≤ 2^{-k} → I[f] ≥ c·k·Var`. That argument (O'Donnell §9.6 /
//! Thm 9.28) splits the variance into LOW-degree (`1 ≤ |S| ≤ k`) and HIGH-degree
//! (`|S| > k`) Fourier mass: the high mass is controlled by `kkl_threshold_mass_le`
//! (`(k+1)·M_{>k} ≤ I[f]`), and the low mass is charged to the influences under the
//! small-influence hypothesis. The structural keystone the chain was missing is the
//! exact decomposition itself — proven here as a level-band complement identity.
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.variance_high_mass_complement :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     Rat.sub (Variance n f)
//!             (subsetSum n (fun S =>
//!                 ind (Nat.ble (Nat.succ k) (setSizeNat n S)) · (f̂ S · f̂ S)))
//!       = subsetSum n (fun S =>
//!           ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                         (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!               · (f̂ S · f̂ S))
//! ```
//!
//! i.e. `Var − M_{>k} = M_{1..k}`, where (writing `w S := f̂(S)²`)
//!   * `M_{>k} := Σ_{|S| ≥ k+1} w S` is the strictly-above-level-`k` Fourier mass, and
//!   * `M_{1..k} := Σ_{1 ≤ |S| ≤ k} w S` is the non-empty-but-low-degree mass
//!     (the genuine indicator `[1 ≤ |S|] ∧ ¬[k+1 ≤ |S|]`, a real level-band set).
//!
//! Maximised at `k = 0`, `M_{>0} = M_{≥1} = Var` and `M_{1..0} = 0` (the empty band);
//! at large `k ≥ n`, `M_{>k} = 0` and `M_{1..k} = M_{≥1} = Var`. The identity is the
//! exact glue that lets `kkl_threshold_mass_le`'s high-band bound and an influence
//! charge of the low band combine into the conditional bound. It does NOT assert any
//! hypercontractive inequality — it is a sound, unconditional partition of the
//! non-empty Fourier mass, refute-checked against the dictator/parity battery.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! 1. `variance_eq_nonempty_mass n f` (LANDED): `Var = M_{≥1} =
//!    subsetSum n (fun S => ind(ble 1 |S|)·w)`.
//! 2. `ind_not_complement c a` (this module): `a − ind c · a = ind (not c) · a`,
//!    a single `Bool.rec` on `c` (`c=false`: `a − 0·a = a = 1·a`; `c=true`:
//!    `a − 1·a = a − a = 0 = 0·a`). The level-complement at a fixed bit.
//! 3. `high_mass_complement_pointwise k m a` (this module): the level-band
//!    complement `ind(ble 1 m)·a − ind(ble (k+1) m)·a = ind(and (ble 1 m)
//!    (not (ble (k+1) m)))·a`. A `Nat.casesOn m` — at `m = 0` both `ble`s are
//!    `false` (so the goal reduces to a `Rat` identity); at `m = succ m'`,
//!    `ble 1 (succ m') ι-reduces to `Bool.true`, so `and Bool.true _ = _` and
//!    the band mask collapses to `not (ble (k+1) (succ m'))`, closing via (2) at
//!    `c := ble (k+1) (succ m')`. No implication hypothesis is needed — the
//!    `1 ≤ m` half of `k+1 ≤ m ⟹ 1 ≤ m` holds *definitionally* in each `Nat` case.
//! 4. `subsetSum_sub n M_ge1_fn M_hi_fn` (LANDED) splits the cube sum:
//!    `Σ_S (ind(ble 1 |S|)·w − ind(ble (k+1) |S|)·w) = M_{≥1} − M_{>k}`.
//!    `subsetSum_congr` over (3) rewrites the LHS integrand to the band mask, giving
//!    `M_{≥1} − M_{>k} = M_{1..k}`.
//! 5. `Eq.subst` transports `Var = M_{≥1}` (1) into the subtraction's left endpoint,
//!    chaining `Var − M_{>k} = M_{≥1} − M_{>k} = M_{1..k}`.
//!
//! Every leaf (`variance_eq_nonempty_mass`, `subsetSum_sub`, `subsetSum_congr`,
//! `Bool.rec`, `Nat.casesOn`, Eq/congr built-ins) is `Constructive` with empty
//! closure, so this rung is too. No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the variance level-split rung. Spellings are byte-identical
/// to the on-branch `EmptyConsts` / `DyadicConsts` carriers so all terms stay
/// def-eq to the infrastructure they reuse.
struct MassSplitConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    ind: Expr,
    fourier: Expr,
    variance: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_sub: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    congr_arg: Expr,
    u1: Level,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl MassSplitConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            rat_one: k("Rat.one"),
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            ind: k("BoolAnalysis.ind"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            variance: k("BoolAnalysis.Variance"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_sub: k("BoolAnalysis.subsetSum_sub"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            u1: l1,
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S) · f̂(S)`.
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn ss_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `Nat.ble a b`.
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    /// `Nat.ble (succ zero) m` — the `|S| ≥ 1` bit.
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.one_nat(), m)
    }
    /// `Nat.ble (succ k) m` — the `|S| ≥ k+1` (= `|S| > k`) bit.
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    /// `Bool.and b c`.
    fn band(&self, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [b, c])
    }
    /// `Bool.not b`.
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    /// `@Eq Rat l r`.
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.rat.clone(), l, r],
        )
    }
    /// `@Eq Bool l r`.
    #[cfg(test)]
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), l, r],
        )
    }
    /// `Eq.trans.{1} Rat a b c h1 h2 : a = c`.
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `Eq.symm.{1} Rat a b h : b = a`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_a : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `@congrArg.{1,1} Rat Rat x y g h : g x = g y` (for `g : Rat → Rat`).
    fn congr_rat(&self, x: Expr, y: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), x, y, g, h],
        )
    }
    #[cfg(test)]
    fn bool_true(&self) -> Expr {
        Expr::const_(Name::from_string("Bool.true"), vec![])
    }

    // ── integrand builders (all over `S : HCPoint n`) ──

    /// `fun S => ind (ble 1 |S|) · (f̂·f̂)` — the `M_{≥1}` integrand
    /// (byte-identical to `variance_eq_nonempty_mass`'s RHS integrand).
    fn m_ge1_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let bit = self.ble1(self.ss_nat_of(n, &s));
        let body = self.mul(self.ind_of(bit), self.fsq(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => ind (ble (k+1) |S|) · (f̂·f̂)` — the `M_{>k}` integrand.
    fn m_hi_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let bit = self.ble_succ_k(k, self.ss_nat_of(n, &s));
        let body = self.mul(self.ind_of(bit), self.fsq(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => ind (and (ble 1 |S|) (not (ble (k+1) |S|))) · (f̂·f̂)` —
    /// the `M_{1..k}` band integrand (the genuine `1 ≤ |S| ≤ k` set).
    fn m_lo_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.ss_nat_of(n, &s);
        let band = self.band(self.ble1(ss.clone()), self.bnot(self.ble_succ_k(k, ss)));
        let body = self.mul(self.ind_of(band), self.fsq(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => (ind(ble 1 |S|)·w) − (ind(ble (k+1) |S|)·w)` — the `subsetSum_sub`
    /// integrand (its `Σ` equals `M_{≥1} − M_{>k}`).
    fn diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.ss_nat_of(n, &s);
        let w = self.fsq(n, f, &s);
        let lo = self.mul(self.ind_of(self.ble1(ss.clone())), w.clone());
        let hi = self.mul(self.ind_of(self.ble_succ_k(k, ss)), w);
        let body = self.sub(lo, hi);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register the variance level-split chain. Idempotent.
    pub fn init_boolean_analysis_kkl_masssplit(&mut self) -> Result<(), EnvError> {
        self.register_ind_not_complement()?;
        self.register_high_mass_complement_pointwise()?;
        self.register_variance_high_mass_complement()?;
        Ok(())
    }

    /// `BoolAnalysis.ind_not_complement : ∀ (c : Bool) (a : Rat),
    ///   Rat.sub a (Rat.mul (ind c) a) = Rat.mul (ind (Bool.not c)) a`.
    ///
    /// The complement of a fixed-bit indicator scaled by `a`:
    /// `a − ind c · a = ind (¬c) · a`. `Bool.rec` on `c` (Prop motive):
    /// - `c = false`: `ind false ≡ 0`, `ind (not false) ≡ ind true ≡ 1`, so
    ///   `a − 0·a = a − 0 = a = 1·a` (`Rat.zero_mul`, `Rat.sub_zero`, `Rat.one_mul`);
    /// - `c = true`: `ind true ≡ 1`, `ind (not true) ≡ ind false ≡ 0`, so
    ///   `a − 1·a = a − a = 0 = 0·a` (`Rat.one_mul`, `Rat.sub_self`, `Rat.zero_mul`).
    ///
    /// The two minors mirror `mass_complement_pointwise` exactly (with `not c`
    /// replacing the `ble 1`/`beq 0` complement). Kernel-checked, `Constructive`,
    /// empty closure. Idempotent.
    pub fn register_ind_not_complement(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.ind_not_complement");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_rat()?; // Rat.one_mul, Rat.zero_mul, Rat.sub_self, Rat.mul
        self.init_boolean_analysis()?; // ind
        self.register_rat_sub_zero()?;

        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MassSplitConsts::new();
        let rat = c.rat.clone();
        let bool_ty = c.bool_.clone();
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
        let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
        let sub_self = Expr::const_(Name::from_string("Rat.sub_self"), vec![]);
        let sub_zero = Expr::const_(Name::from_string("Rat.sub_zero"), vec![]);

        // goal_at bit a : sub a (ind bit · a) = ind (not bit) · a
        let goal_at = |bit: Expr, a: &Expr| {
            c.eq_rat(
                c.sub(a.clone(), c.mul(c.ind_of(bit.clone()), a.clone())),
                c.mul(c.ind_of(c.bnot(bit)), a.clone()),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bit_id, bit) = b.fresh_local(bool_ty.clone());
            let (a_id, a) = b.fresh_local(rat.clone());
            let concl = goal_at(bit.clone(), &a);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), concl);
            let e = b.mk_pi(bit_id, BinderInfo::Default, bool_ty.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bit_id, bit) = b.fresh_local(bool_ty.clone());
            let (a_id, a) = b.fresh_local(rat.clone());

            // motive : fun (z : Bool) => goal_at z a
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = d.fresh_local(bool_ty.clone());
                let body = goal_at(z, &a);
                d.finish_child(d.mk_lam(z_id, BinderInfo::Default, bool_ty.clone(), body))
            };

            // false case: goal_at false a  (def-eq to  sub a (0·a) = 1·a)
            //   chain: sub a (0·a) = sub a 0   [congr (sub a ·) (zero_mul a)]
            //                       = a        [sub_zero a]
            //                       = 1·a      [symm (one_mul a)]
            let false_case = {
                let zero_mul_a = Expr::app(zero_mul.clone(), a.clone()); // 0·a = 0
                let sub_a_fn = {
                    let mut g = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = g.fresh_local(rat.clone());
                    let body = c.sub(a.clone(), t);
                    g.finish_child(g.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
                };
                let zero_a = c.mul(c.rat_zero.clone(), a.clone());
                // h1 : sub a (0·a) = sub a 0
                let h1 = c.congr_rat(zero_a.clone(), c.rat_zero.clone(), sub_a_fn, zero_mul_a);
                // h2 : sub a 0 = a
                let h2 = Expr::app(sub_zero.clone(), a.clone());
                // h3 : a = 1·a   (symm (one_mul a))
                let one_mul_a = Expr::app(one_mul.clone(), a.clone()); // 1·a = a
                let one_a = c.mul(c.rat_one.clone(), a.clone());
                let h3 = c.symm(one_a.clone(), a.clone(), one_mul_a);
                let h12 = c.trans(
                    c.sub(a.clone(), zero_a.clone()),
                    c.sub(a.clone(), c.rat_zero.clone()),
                    a.clone(),
                    h1,
                    h2,
                );
                c.trans(c.sub(a.clone(), zero_a), a.clone(), one_a, h12, h3)
            };

            // true case: goal_at true a  (def-eq to  sub a (1·a) = 0·a)
            //   chain: sub a (1·a) = sub a a   [congr (sub a ·) (one_mul a)]
            //                       = 0        [sub_self a]
            //                       = 0·a      [symm (zero_mul a)]
            let true_case = {
                let one_mul_a = Expr::app(one_mul.clone(), a.clone()); // 1·a = a
                let sub_a_fn = {
                    let mut g = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = g.fresh_local(rat.clone());
                    let body = c.sub(a.clone(), t);
                    g.finish_child(g.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
                };
                let one_a = c.mul(c.rat_one.clone(), a.clone());
                // h1 : sub a (1·a) = sub a a
                let h1 = c.congr_rat(one_a.clone(), a.clone(), sub_a_fn, one_mul_a);
                // h2 : sub a a = 0
                let h2 = Expr::app(sub_self.clone(), a.clone());
                // h3 : 0 = 0·a   (symm (zero_mul a))
                let zero_mul_a = Expr::app(zero_mul.clone(), a.clone()); // 0·a = 0
                let zero_a = c.mul(c.rat_zero.clone(), a.clone());
                let h3 = c.symm(zero_a.clone(), c.rat_zero.clone(), zero_mul_a);
                let h12 = c.trans(
                    c.sub(a.clone(), one_a.clone()),
                    c.sub(a.clone(), a.clone()),
                    c.rat_zero.clone(),
                    h1,
                    h2,
                );
                c.trans(c.sub(a.clone(), one_a), c.rat_zero.clone(), zero_a, h12, h3)
            };

            // @Bool.rec.{0} motive false_case true_case bit : motive bit
            let body = Expr::apps(
                bool_rec0.clone(),
                [motive, false_case, true_case, bit.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), body);
            let e = b.mk_lam(bit_id, BinderInfo::Default, bool_ty.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
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

    /// `BoolAnalysis.high_mass_complement_pointwise : ∀ (k m : Nat) (a : Rat),
    ///   Rat.sub (Rat.mul (ind (Nat.ble 1 m)) a)
    ///           (Rat.mul (ind (Nat.ble (Nat.succ k) m)) a)
    ///     = Rat.mul (ind (Bool.and (Nat.ble 1 m)
    ///                              (Bool.not (Nat.ble (Nat.succ k) m)))) a`.
    ///
    /// The pointwise level-band complement: the `[|S| ≥ 1]`-mass minus the
    /// `[|S| ≥ k+1]`-mass equals the `[1 ≤ |S| ≤ k]`-band mass, scaled by `a`.
    /// `Nat.casesOn m`:
    /// - `m = 0`: `ble 1 0 ≡ ble (succ 0) 0 ≡ false` and `ble (succ k) 0 ≡ false`
    ///   (`Nat.ble (succ _) zero` ι-reduces to `false` for symbolic `k`), so the
    ///   goal reduces to `sub (0·a) (0·a) = 0·a` (the band bit `and false _ ≡
    ///   false`). Closed by `Rat.sub_self (0·a)` then `symm (Rat.zero_mul a)`.
    /// - `m = succ m'`: `ble 1 (succ m') ≡ ble 0 m' ≡ true`, so the first term is
    ///   `1·a` and the band bit `and true Y ≡ Y` collapses to `not (ble (succ k)
    ///   (succ m'))`. `ind_not_complement (ble (succ k) (succ m')) a` gives
    ///   `sub a (ind c'·a) = ind(not c')·a`; `congrArg (fun t => sub t (ind c'·a))
    ///   (Rat.one_mul a)` bridges `sub (1·a) (ind c'·a) = sub a (ind c'·a)`, and
    ///   `Eq.trans` chains them to the band form.
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_high_mass_complement_pointwise(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.high_mass_complement_pointwise");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_rat()?; // Rat.one_mul, Rat.zero_mul, Rat.sub_self, Rat.mul
        self.init_boolean_analysis()?; // ind
        self.register_ind_not_complement()?;

        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MassSplitConsts::new();
        let nat = c.nat.clone();
        let rat = c.rat.clone();
        let nat_cases_on = Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]);
        let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
        let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
        let sub_self = Expr::const_(Name::from_string("Rat.sub_self"), vec![]);
        let ind_not_complement =
            Expr::const_(Name::from_string("BoolAnalysis.ind_not_complement"), vec![]);

        // goal_at k m a : sub (ind(ble 1 m)·a) (ind(ble (succ k) m)·a)
        //                   = ind(and (ble 1 m) (not (ble (succ k) m)))·a
        let goal_at = |k: &Expr, m: Expr, a: &Expr| {
            let lo = c.mul(c.ind_of(c.ble1(m.clone())), a.clone());
            let hi = c.mul(c.ind_of(c.ble_succ_k(k, m.clone())), a.clone());
            let band = c.band(c.ble1(m.clone()), c.bnot(c.ble_succ_k(k, m)));
            c.eq_rat(c.sub(lo, hi), c.mul(c.ind_of(band), a.clone()))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let (m_id, m) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(rat.clone());
            let concl = goal_at(&k, m.clone(), &a);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(nat.clone());
            let (m_id, m) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(rat.clone());

            // motive : fun (mm : Nat) => goal_at k mm a
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = d.fresh_local(nat.clone());
                let body = goal_at(&k, mm, &a);
                d.finish_child(d.mk_lam(mm_id, BinderInfo::Default, nat.clone(), body))
            };

            // zero case: goal_at k 0 a  (def-eq to  sub (0·a) (0·a) = 0·a)
            //   chain: sub (0·a) (0·a) = 0       [Rat.sub_self (0·a)]
            //                          = 0·a     [symm (Rat.zero_mul a)]
            let zero_case = {
                let zero_a = c.mul(c.rat_zero.clone(), a.clone());
                // h1 : sub (0·a) (0·a) = 0
                let h1 = Expr::app(sub_self.clone(), zero_a.clone());
                // h2 : 0 = 0·a   (symm (zero_mul a))
                let zero_mul_a = Expr::app(zero_mul.clone(), a.clone()); // 0·a = 0
                let h2 = c.symm(zero_a.clone(), c.rat_zero.clone(), zero_mul_a);
                c.trans(
                    c.sub(zero_a.clone(), zero_a.clone()),
                    c.rat_zero.clone(),
                    zero_a,
                    h1,
                    h2,
                )
            };

            // succ case: fun (m' : Nat) => goal_at k (succ m') a
            //   def-eq to  sub (1·a) (ind c'·a) = ind (not c')·a
            //   where c' := ble (succ k) (succ m').
            let succ_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mp_id, mp) = d.fresh_local(nat.clone());
                let c_prime = c.ble_succ_k(&k, c.succ(mp.clone()));
                let ind_c = c.ind_of(c_prime.clone());
                let ind_c_a = c.mul(ind_c.clone(), a.clone());
                let one_a = c.mul(c.rat_one.clone(), a.clone());

                // h_lemma : sub a (ind c'·a) = ind (not c')·a
                let h_lemma = Expr::apps(ind_not_complement.clone(), [c_prime.clone(), a.clone()]);
                // sub_t_fn := fun (t : Rat) => sub t (ind c'·a)
                let sub_t_fn = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (t_id, t) = g.fresh_local(rat.clone());
                    let body = c.sub(t, ind_c_a.clone());
                    g.finish_child(g.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
                };
                // h_lhs : sub (1·a) (ind c'·a) = sub a (ind c'·a)
                //   congrArg sub_t_fn (one_mul a : 1·a = a)
                let one_mul_a = Expr::app(one_mul.clone(), a.clone()); // 1·a = a
                let h_lhs = c.congr_rat(one_a.clone(), a.clone(), sub_t_fn, one_mul_a);
                // body : sub (1·a) (ind c'·a) = ind (not c')·a   (trans h_lhs h_lemma)
                let ind_not_c_a = c.mul(c.ind_of(c.bnot(c_prime)), a.clone());
                let body = c.trans(
                    c.sub(one_a, ind_c_a.clone()),
                    c.sub(a.clone(), ind_c_a),
                    ind_not_c_a,
                    h_lhs,
                    h_lemma,
                );
                d.finish_child(d.mk_lam(mp_id, BinderInfo::Default, nat.clone(), body))
            };

            // @Nat.casesOn.{0} motive m zero_case succ_case : motive m = goal_at k m a
            let body = Expr::apps(
                nat_cases_on.clone(),
                [motive, m.clone(), zero_case, succ_case],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
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

    /// `BoolAnalysis.variance_high_mass_complement : ∀ (n k : Nat) (f : BoolFn n),
    ///   Rat.sub (Variance n f)
    ///           (subsetSum n (fun S => ind (Nat.ble (Nat.succ k) (setSizeNat n S))
    ///                                      · (f̂ S · f̂ S)))
    ///     = subsetSum n (fun S =>
    ///         ind (Bool.and (Nat.ble 1 (setSizeNat n S))
    ///                       (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
    ///             · (f̂ S · f̂ S))`.
    ///
    /// The **variance level-split**: `Var − M_{>k} = M_{1..k}` (the high-degree
    /// Fourier mass removed from the variance leaves exactly the low-degree band).
    /// See the module docs for the full chain. Kernel-checked, `Constructive`,
    /// empty admitted-axiom closure. Idempotent.
    pub fn register_variance_high_mass_complement(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.variance_high_mass_complement");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Variance, FourierCoefficient
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_sub_theorem()?;
        self.register_set_size_nat()?;
        self.register_variance_eq_nonempty_mass()?;
        self.register_high_mass_complement_pointwise()?;

        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MassSplitConsts::new();
        let nat = c.nat.clone();
        let variance_eq_mass = Expr::const_(
            Name::from_string("BoolAnalysis.variance_eq_nonempty_mass"),
            vec![],
        );
        let high_complement = Expr::const_(
            Name::from_string("BoolAnalysis.high_mass_complement_pointwise"),
            vec![],
        );

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let var = c.variance_of(&n, &f);
            let m_hi = c.subset_sum_of(&n, c.m_hi_fn(&b, &n, &k, &f));
            let m_lo = c.subset_sum_of(&n, c.m_lo_fn(&b, &n, &k, &f));
            let concl = c.eq_rat(c.sub(var, m_hi), m_lo);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let var = c.variance_of(&n, &f);
            let m_ge1_fn = c.m_ge1_fn(&b, &n, &f);
            let m_hi_fn = c.m_hi_fn(&b, &n, &k, &f);
            let m_lo_fn = c.m_lo_fn(&b, &n, &k, &f);
            let m_ge1 = c.subset_sum_of(&n, m_ge1_fn.clone());
            let m_hi = c.subset_sum_of(&n, m_hi_fn.clone());
            let m_lo = c.subset_sum_of(&n, m_lo_fn.clone());
            let diff_fn = c.diff_fn(&b, &n, &k, &f);
            let diff = c.subset_sum_of(&n, diff_fn.clone());

            // h_var : Variance n f = M_{≥1}   (variance_eq_nonempty_mass n f)
            let h_var = Expr::apps(variance_eq_mass.clone(), [n.clone(), f.clone()]);

            // h_sub : subsetSum n diff_fn = sub M_{≥1} M_{>k}
            //   (subsetSum_sub n m_ge1_fn m_hi_fn).
            let h_sub = Expr::apps(
                c.subset_sum_sub.clone(),
                [n.clone(), m_ge1_fn.clone(), m_hi_fn.clone()],
            );

            // per_s : ∀ S, diff_fn S = m_lo_fn S
            //   high_mass_complement_pointwise k (setSizeNat n S) (f̂ S · f̂ S).
            let per_s = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = d.fresh_local(hcp.clone());
                let ss = c.ss_nat_of(&n, &s);
                let w = c.fsq(&n, &f, &s);
                let body = Expr::apps(high_complement.clone(), [k.clone(), ss, w]);
                d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };
            // h_congr : subsetSum n diff_fn = subsetSum n m_lo_fn   (= M_{1..k})
            //   subsetSum_congr n diff_fn m_lo_fn per_s.
            let h_congr = Expr::apps(
                c.subset_sum_congr.clone(),
                [n.clone(), diff_fn, m_lo_fn, per_s],
            );

            // h1 : sub M_{≥1} M_{>k} = subsetSum n diff_fn   (symm h_sub)
            let sub_ge1_hi = c.sub(m_ge1.clone(), m_hi.clone());
            let h1 = c.symm(diff.clone(), sub_ge1_hi.clone(), h_sub);
            // h2 : sub M_{≥1} M_{>k} = M_{1..k}   (trans h1 h_congr)
            let h2 = c.trans(sub_ge1_hi.clone(), diff, m_lo.clone(), h1, h_congr);

            // h_var_symm : M_{≥1} = Variance n f   (symm h_var)
            let h_var_symm = c.symm(var.clone(), m_ge1.clone(), h_var);
            // motive : fun (t : Rat) => sub t M_{>k} = M_{1..k}
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.eq_rat(c.sub(t, m_hi.clone()), m_lo.clone());
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // body : sub (Variance n f) M_{>k} = M_{1..k}
            //   Eq.subst motive M_{≥1} (Variance n f) h_var_symm h2.
            let body = c.subst(motive, m_ge1, var, h_var_symm, h2);

            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
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

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_masssplit()
            .expect("init_boolean_analysis_kkl_masssplit");
        env.init_boolean_analysis_kkl_masssplit()
            .expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
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
            "{name} closure must be empty"
        );
    }

    #[test]
    fn test_ind_not_complement_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.ind_not_complement");
    }

    #[test]
    fn test_high_mass_complement_pointwise_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.high_mass_complement_pointwise");
    }

    #[test]
    fn test_variance_high_mass_complement_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.variance_high_mass_complement");
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// refute the variance level-split — it is a sound, unconditional partition of
    /// the non-empty Fourier mass — when probed over the canonical Boolean-function
    /// battery (constants + the dictators, the functions that killed the false
    /// `deriv_level_mass_lower`). A refutation would mean the statement is FALSE and
    /// must not be built.
    #[test]
    fn test_variance_high_mass_complement_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.variance_high_mass_complement",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the variance level-split is a true identity; it must NOT refute on \
             the dictator/constant battery"
        );
    }
}
