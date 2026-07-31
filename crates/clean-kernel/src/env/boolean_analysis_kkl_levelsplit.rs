// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL level-split — the 4-norm ↔ spectral inversion machinery (run "levelsplit").
//!
//! See `designs/2026-06-12-kkl-levelsplit-4norm-spectral-inversion.md`. This
//! module owns the level-`k` split bricks that let `hc24_core`'s 4-norm operator
//! upper bound talk to the spectral level masses `Σ_S ρ^{2|S|}·Â(S)²`.
//!
//! ## Deliverables
//!
//! ```text
//! BoolAnalysis.levelWt_factor_eq_powNat_indNat :                   -- (helper)
//!   ∀ (ρ : Rat) (b : Bool),
//!     @Bool.rec (fun _ => Rat) Rat.one (Rat.mul ρ ρ) b
//!       = Rat.powNat (Rat.mul ρ ρ) (indNat b)
//!
//! BoolAnalysis.levelWt_eq_powNat :                                 -- (item 1)
//!   ∀ (ρ : Rat) (n : Nat) (S : HCPoint n),
//!     levelWt ρ n S = Rat.powNat (Rat.mul ρ ρ) (setSizeNat n S)
//! ```
//!
//! ### `levelWt_factor_eq_powNat_indNat` (the per-coordinate factor)
//!
//! `levelWt`'s factor is `@Bool.rec (fun _ => Rat) 1 (ρ·ρ) b`. Its value:
//! `false ↦ 1`, `true ↦ ρ·ρ`. `indNat b = @Bool.rec (fun _ => Nat) 0 1 b`:
//! `false ↦ 0`, `true ↦ 1`. We must show factor `b = powNat (ρ·ρ) (indNat b)`:
//! - `false`: `1 = powNat (ρ·ρ) 0` — `Eq.symm (powNat_zero (ρ·ρ))` (RHS ι-reduces
//!   `indNat false ≡ 0`, then `powNat_zero`). Built as `powNat_zero` reversed.
//! - `true`: `ρ·ρ = powNat (ρ·ρ) 1` — `powNat (ρ·ρ) 1 = (ρ·ρ)·powNat (ρ·ρ) 0`
//!   (`powNat_succ`) `= (ρ·ρ)·1` (`powNat_zero` under congr) `= ρ·ρ` (`mul_one`).
//!
//! A `Bool.rec` (Prop-motive) case-split on `b` glues the two branches; the
//! motive is `fun b => factor b = powNat (ρ·ρ) (indNat b)`.
//!
//! ### `levelWt_eq_powNat` (the `Fin.prod` ↔ `powNat` bridge, K0 deferred relation)
//!
//! `Nat.rec` induction on `n`, motive `fun k => ∀ S, levelWt ρ k S = powNat (ρ·ρ)
//! (setSizeNat k S)`:
//! - **base `n = 0`:** `levelWt ρ 0 S ≡ Fin.prod 0 _ ≡ Rat.one`; `setSizeNat 0 S
//!   ≡ Fin.sumNat 0 _ ≡ 0`, so `powNat (ρ·ρ) 0 ≡ Rat.one`. Both sides ι-reduce to
//!   `Rat.one` — `Eq.refl`.
//! - **step `n = m+1`:** Goal `levelWt ρ (m+1) S = powNat (ρ·ρ) (setSizeNat (m+1) S)`.
//!   - LHS `= Fin.prod (m+1) factor` →[`Fin.prod_succ`]
//!     `Fin.prod m (factor∘castSucc) · factor (S last)`. The prefix
//!     `Fin.prod m (factor∘castSucc)` is def-eq to `levelWt ρ m (restrict S)`
//!     (both `Fin.prod m (fun i => Bool.rec 1 (ρ·ρ) ((restrict S) i))`).
//!   - RHS `= powNat (ρ·ρ) (setSizeNat (m+1) S)`. `setSizeNat (m+1) S ≡ pc (m+1) S`
//!     →[`popcount_succ_split`] `setSizeNat m (restrict S) + indNat (S last)`, so
//!     RHS →[congr] `powNat (ρ·ρ) (setSizeNat m (restrict S) + indNat (S last))`
//!     →[`powNat_add`] `powNat (ρ·ρ) (setSizeNat m (restrict S)) · powNat (ρ·ρ)
//!     (indNat (S last))`.
//!   - IH at `restrict S`: prefix `= powNat (ρ·ρ) (setSizeNat m (restrict S))`.
//!   - factor helper at `S last`: `factor (S last) = powNat (ρ·ρ) (indNat (S last))`.
//!   - congr into `Rat.mul` glues prefix + factor; `Eq.trans` chains the legs.
//!
//! ## Soundness
//!
//! Every leaf is CHECKED `Constructive` with an empty admitted-axiom closure
//! (`Fin.prod_succ`, `popcount_succ_split`, `powNat_add/zero/succ`, `Rat.mul_one`,
//! `Nat.rec`, `Bool.rec`, Eq built-ins). No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the level-split bricks. The `Bool.rec` factor / `indNat` /
/// `setSizeNat` / `Fin.prod` builds are byte-for-byte the `levelWt` /
/// `setSizeNat` / `popcount_succ_split` shapes so all terms stay def-eq to the
/// carriers they rewrite.
struct LevelSplitConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    fin: Expr,
    hcpoint: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    pow_nat: Expr,
    #[cfg(test)]
    fin_prod: Expr,
    level_wt: Expr,
    set_size_nat: Expr,
    bool_rec1: Expr,
    eq1: Expr,
    eq_refl1: Expr,
}

impl LevelSplitConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            #[cfg(test)]
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            level_wt: Expr::const_(Name::from_string("BoolAnalysis.levelWt"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            bool_rec1: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
        }
    }

    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rho_sq(&self, rho: &Expr) -> Expr {
        self.mul(rho.clone(), rho.clone())
    }
    fn pow(&self, base: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [base.clone(), k.clone()])
    }
    fn level_wt(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.level_wt.clone(), [rho.clone(), n.clone(), s.clone()])
    }
    fn set_size_nat(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn nadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            [a.clone(), b.clone()],
        )
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn refl_rat(&self, e: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), e])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        let eq_trans = Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_trans, [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm_rat(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        let eq_symm = Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_symm, [self.rat.clone(), l, r, h])
    }
    /// `congrArg.{1,1} Rat Rat from to motive h`.
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        Expr::apps(
            congr_arg,
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    /// `congrArg.{1,1} Nat Rat from to motive h` — lift a `Nat`-equality up
    /// through a `Nat → Rat` motive (e.g. `powNat (ρ·ρ) ·`).
    fn congr_nat_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        Expr::apps(
            congr_arg,
            [self.nat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.mul_one"), vec![]), [a])
    }
    /// `Rat.powNat_add base a b : base^(a+b) = base^a · base^b`.
    fn pow_add(&self, base: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_add"), vec![]),
            [base.clone(), a.clone(), b.clone()],
        )
    }
    /// `Rat.powNat_zero base : base^0 = 1`.
    fn pow_zero(&self, base: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_zero"), vec![]),
            [base.clone()],
        )
    }
    /// `Rat.powNat_succ base k : base^(k+1) = base · base^k`.
    fn pow_succ(&self, base: &Expr, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_succ"), vec![]),
            [base.clone(), k.clone()],
        )
    }
    /// The `levelWt` factor `@Bool.rec (fun _ => Rat) Rat.one (ρ·ρ) b`.
    fn factor(&self, rho: &Expr, b: &Expr) -> Expr {
        let motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.rat.clone());
        Expr::apps(
            self.bool_rec1.clone(),
            [motive, self.rat_one.clone(), self.rho_sq(rho), b.clone()],
        )
    }
    /// `indNat b = @Bool.rec (fun _ => Nat) 0 1 b`.
    fn ind_nat(&self, b: &Expr) -> Expr {
        let motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        Expr::apps(
            self.bool_rec1.clone(),
            [motive, self.nat_zero.clone(), self.nat_one(), b.clone()],
        )
    }
    /// `fun (i : Fin n) => S (Fin.castSucc n i)` — restrict an `HCPoint (n+1)` to
    /// its first `n` coordinates (byte-for-byte the `popcount`/`Fin.prod_succ`
    /// restrict).
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let cs = Expr::apps(
            Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            [n.clone(), i],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, Expr::app(s.clone(), cs)))
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.last"), vec![]),
            [n.clone()],
        )
    }
    /// `popcount_succ_split n S : setSizeNat (n+1) S = setSizeNat n (restrict S) +
    /// indNat (S last)` (def-eq, the `Fin.sumNat` ι-step).
    fn popcount_split(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.popcount_succ_split"),
                vec![],
            ),
            [n.clone(), s.clone()],
        )
    }
    /// `Fin.prod_succ n g : Fin.prod (n+1) g = Fin.prod n (g∘castSucc) · g (last n)`.
    fn fin_prod_succ(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.prod_succ"), vec![]),
            [n.clone(), g.clone()],
        )
    }
    /// The `levelWt` factor function `fun (i : Fin n) => @Bool.rec _ 1 (ρ·ρ) (S i)`
    /// — exactly the argument `Fin.prod` is applied to inside `levelWt ρ n S`.
    fn level_wt_factor_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let s_i = Expr::app(s.clone(), i);
        let body = self.factor(rho, &s_i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    // ── item-2 (noise_spectral_level) spectral atoms ────────────────────────

    /// `HCPoint n → Rat` — the coefficient function type `a`.
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    /// `subsetSum n g`.
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            [n.clone(), g],
        )
    }
    /// `chi n S x` — the parity character.
    fn chi(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            [n.clone(), s.clone(), x.clone()],
        )
    }
    /// `noiseDensityW ρ n x y` — the correlated noise density.
    fn noise_density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `A a S = subsetSum n (fun x => a x · χ_S x)` — the un-normalized Fourier
    /// coefficient `Â_a(S)`. Byte-for-byte the `noise_spectral_core` inner sum
    /// (`g_fn`/`rhs_s_fn`).
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(a.clone(), x.clone()), self.chi(n, s, &x));
        let g = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }
    /// LHS `x`-integrand `fun x => Σ_y (a x·a y)·noiseDensityW ρ n x y`, the
    /// `noise_spectral_core` LHS shape (`lhs_x_fn`).
    fn lhs_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let ax_ay = self.mul(
                Expr::app(a.clone(), x.clone()),
                Expr::app(a.clone(), y.clone()),
            );
            let body = self.mul(ax_ay, self.noise_density(rho, n, &x, &y));
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, y_sum))
    }
    /// RHS `S`-integrand with the **`setSizeNat`-indexed `powNat (ρ·ρ)` weight**:
    /// `fun S => powNat (ρ·ρ) (setSizeNat n S) · (A a S · A a S)`. Def-eq to the
    /// `noise_spectral_core (ρ·ρ)` RHS integrand (whose weight uses the byte-for-byte
    /// equal popcount `pc n S ≡ setSizeNat n S`).
    fn rhs_pow_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let w = self.pow(&self.rho_sq(rho), &self.set_size_nat(n, &s));
        let inner = self.a_coeff(&b, n, a, &s);
        let body = self.mul(w, self.mul(inner.clone(), inner));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// RHS `S`-integrand with the **`levelWt` weight**:
    /// `fun S => levelWt ρ n S · (A a S · A a S)`.
    fn rhs_lvl_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let w = self.level_wt(rho, n, &s);
        let inner = self.a_coeff(&b, n, a, &s);
        let body = self.mul(w, self.mul(inner.clone(), inner));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `levelWt_eq_powNat ρ n S : levelWt ρ n S = powNat (ρ·ρ) (setSizeNat n S)`.
    fn levelwt_eq_pownat(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.levelWt_eq_powNat"), vec![]),
            [rho.clone(), n.clone(), s.clone()],
        )
    }
    /// `subsetSum_congr n G H hyp : subsetSum n G = subsetSum n H`.
    fn ssum_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
}

// ===========================================================================
// (helper) levelWt_factor_eq_powNat_indNat
//
//   ∀ (ρ : Rat) (b : Bool),
//     @Bool.rec (fun _ => Rat) 1 (ρ·ρ) b = powNat (ρ·ρ) (indNat b)
//
// `Bool.rec` (Prop motive) case-split on `b`. The motive is
//   fun b => factor ρ b = powNat (ρ·ρ) (indNat b).
// - false branch: `factor ρ false ≡ 1`, `indNat false ≡ 0`, so goal is
//   `1 = powNat (ρ·ρ) 0`; close with `Eq.symm (powNat_zero (ρ·ρ))`.
// - true branch: `factor ρ true ≡ ρ·ρ`, `indNat true ≡ 1`, so goal is
//   `ρ·ρ = powNat (ρ·ρ) 1`; close with the chain
//   `ρ·ρ =[mul_one⁻¹] (ρ·ρ)·1 =[congr powNat_zero⁻¹] (ρ·ρ)·powNat (ρ·ρ) 0
//        =[powNat_succ⁻¹] powNat (ρ·ρ) 1`.
// Kernel-checked, constructive (EMPTY closure).
// ===========================================================================

fn build_factor_type(c: &LevelSplitConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (b_id, bv) = b.fresh_local(c.bool_.clone());
    let lhs = c.factor(&rho, &bv);
    let rhs = c.pow(&c.rho_sq(&rho), &c.ind_nat(&bv));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(b_id, BinderInfo::Default, c.bool_.clone(), concl);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

fn build_factor_value(c: &LevelSplitConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());

    let base = c.rho_sq(&rho); // ρ·ρ

    // motive : fun (b : Bool) => factor ρ b = powNat (ρ·ρ) (indNat b)
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (mb_id, mb) = d.fresh_local(c.bool_.clone());
        let lhs = c.factor(&rho, &mb);
        let rhs = c.pow(&base, &c.ind_nat(&mb));
        let concl = c.eq_rat(lhs, rhs);
        d.finish_child(d.mk_lam(mb_id, BinderInfo::Default, c.bool_.clone(), concl))
    };

    // false branch: goal `1 = powNat (ρ·ρ) 0`.
    //   `Eq.symm (powNat_zero (ρ·ρ))` : 1 = powNat (ρ·ρ) 0
    let false_proof = {
        let pz = c.pow_zero(&base); // powNat (ρ·ρ) 0 = 1
        let pow0 = c.pow(&base, &c.nat_zero);
        c.symm_rat(pow0, c.rat_one.clone(), pz)
    };

    // true branch: goal `ρ·ρ = powNat (ρ·ρ) 1`.
    // Chain forward `powNat (ρ·ρ) 1 = ρ·ρ` then symm:
    //   powNat (ρ·ρ) 1 =[powNat_succ (ρ·ρ) 0] (ρ·ρ)·powNat (ρ·ρ) 0
    //                  =[congr (powNat_zero)] (ρ·ρ)·1
    //                  =[mul_one] ρ·ρ
    let true_proof = {
        let pow1 = c.pow(&base, &c.nat_one()); // powNat (ρ·ρ) 1
        let pow0 = c.pow(&base, &c.nat_zero); // powNat (ρ·ρ) 0
        let rr_pow0 = c.mul(base.clone(), pow0.clone()); // (ρ·ρ)·powNat (ρ·ρ) 0
        let rr_one = c.mul(base.clone(), c.rat_one.clone()); // (ρ·ρ)·1
                                                             // leg1 : powNat (ρ·ρ) 1 = (ρ·ρ)·powNat (ρ·ρ) 0
        let leg1 = c.pow_succ(&base, &c.nat_zero);
        // leg2 : (ρ·ρ)·powNat (ρ·ρ) 0 = (ρ·ρ)·1  via congr on powNat_zero
        let leg2 = {
            // motive for congr: fun (t : Rat) => (ρ·ρ)·t
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let mlam = d.finish_child(d.mk_lam(
                t_id,
                BinderInfo::Default,
                c.rat.clone(),
                c.mul(base.clone(), t),
            ));
            c.congr_rat(pow0.clone(), c.rat_one.clone(), mlam, c.pow_zero(&base))
        };
        // leg3 : (ρ·ρ)·1 = ρ·ρ  via mul_one
        let leg3 = c.mul_one(base.clone());
        // forward : powNat (ρ·ρ) 1 = ρ·ρ
        let t12 = c.trans_rat(pow1.clone(), rr_pow0, rr_one.clone(), leg1, leg2);
        let forward = c.trans_rat(pow1.clone(), rr_one, base.clone(), t12, leg3);
        // symm : ρ·ρ = powNat (ρ·ρ) 1
        c.symm_rat(pow1, base.clone(), forward)
    };

    // @Bool.rec.{0} motive false_proof true_proof b
    // (Prop-valued motive ⇒ recursor at level 0.)
    let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let (bv_id, bv) = b.fresh_local(c.bool_.clone());
    let rec_app = Expr::apps(bool_rec0, [motive, false_proof, true_proof, bv]);
    let val = b.mk_lam(bv_id, BinderInfo::Default, c.bool_.clone(), rec_app);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

// ===========================================================================
// (item 1) levelWt_eq_powNat
//
//   ∀ (ρ : Rat) (n : Nat) (S : HCPoint n),
//     levelWt ρ n S = powNat (ρ·ρ) (setSizeNat n S)
//
// `Nat.rec.{1}` induction on `n` (ρ fixed), motive
//   fun k => ∀ (S : HCPoint k), levelWt ρ k S = powNat (ρ·ρ) (setSizeNat k S).
// base = Eq.refl (both sides ι-reduce to Rat.one at n=0).
// step = build_step (see below).
// ===========================================================================

fn build_eq_pow_nat_type(c: &LevelSplitConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let lhs = c.level_wt(&rho, &n, &s);
    let rhs = c.pow(&c.rho_sq(&rho), &c.set_size_nat(&n, &s));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

/// motive for the `Nat.rec` over `k` (ρ captured): `fun k => ∀ S, levelWt ρ k S
/// = powNat (ρ·ρ) (setSizeNat k S)`.
fn eq_pow_nat_motive(c: &LevelSplitConsts, parent: &EnvDeclBuilder, rho: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = d.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&k);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let lhs = c.level_wt(rho, &k, &s);
    let rhs = c.pow(&c.rho_sq(rho), &c.set_size_nat(&k, &s));
    let concl = c.eq_rat(lhs, rhs);
    let body = d.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
}

/// step : ∀ (m : Nat), motive m → motive (m+1).
fn build_eq_pow_nat_step(c: &LevelSplitConsts, parent: &EnvDeclBuilder, rho: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = b.fresh_local(c.nat.clone());

    // ih : ∀ S : HCPoint m, levelWt ρ m S = powNat (ρ·ρ) (setSizeNat m S)
    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&m);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let lhs = c.level_wt(rho, &m, &s);
        let rhs = c.pow(&c.rho_sq(rho), &c.set_size_nat(&m, &s));
        let concl = c.eq_rat(lhs, rhs);
        d.finish_child(d.mk_pi(s_id, BinderInfo::Default, hcp, concl))
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    // S : HCPoint (m+1)
    let sm = c.succ(&m);
    let hcp_sm = c.hcpoint_of(&sm);
    let (s_id, s) = b.fresh_local(hcp_sm.clone());

    let base = c.rho_sq(rho); // ρ·ρ
    let restrict_s = c.restrict(&b, &m, &s);
    let s_last = Expr::app(s.clone(), c.last(&m)); // S (last m)

    // ── Terms ──
    // LHS  : levelWt ρ (m+1) S  (≡ Fin.prod (m+1) (factor_fn ρ (m+1) S))
    let lhs = c.level_wt(rho, &sm, &s);
    // factor_fn ρ (m+1) S — the function Fin.prod is applied to in levelWt.
    let factor_fn = c.level_wt_factor_fn(&b, rho, &sm, &s);
    // Fin.prod m (factor_fn ∘ castSucc) — the Fin.prod_succ prefix.
    // It is def-eq to `levelWt ρ m (restrict S)`.
    let prefix_lwt = c.level_wt(rho, &m, &restrict_s);
    // factor at last : factor ρ (S last)
    let factor_last = c.factor(rho, &s_last);
    // LHS_succ := prefix_lwt · factor_last  (the Fin.prod_succ RHS, def-eq)
    let lhs_succ = c.mul(prefix_lwt.clone(), factor_last.clone());

    // setSizeNat (m+1) S
    let ssn_sm = c.set_size_nat(&sm, &s);
    // setSizeNat m (restrict S)
    let ssn_restrict = c.set_size_nat(&m, &restrict_s);
    // indNat (S last)
    let ind_last = c.ind_nat(&s_last);
    // setSizeNat m (restrict S) + indNat (S last)
    let split_nat = c.nadd(&ssn_restrict, &ind_last);
    // powNat (ρ·ρ) (setSizeNat (m+1) S)  — the goal RHS
    let rhs = c.pow(&base, &ssn_sm);
    // powNat (ρ·ρ) (split_nat)
    let pow_split = c.pow(&base, &split_nat);
    // powNat (ρ·ρ) (setSizeNat m restrict) · powNat (ρ·ρ) (indNat (S last))
    let pow_prefix = c.pow(&base, &ssn_restrict);
    let pow_ind = c.pow(&base, &ind_last);
    let pow_prod = c.mul(pow_prefix.clone(), pow_ind.clone());

    // ── Legs (forward chain lhs = rhs) ──
    // Strategy: prove `lhs = lhs_succ` (Fin.prod_succ), then `lhs_succ = pow_prod`
    // (IH + factor helper, congr into mul), then `pow_prod = rhs` (powNat_add⁻¹ +
    // popcount_split congr⁻¹). Chain by Eq.trans.

    // leg A : lhs = lhs_succ
    //   Fin.prod_succ m factor_fn : Fin.prod (m+1) factor_fn
    //     = Fin.prod m (factor_fn∘castSucc) · factor_fn (last m).
    //   `lhs` is def-eq to `Fin.prod (m+1) factor_fn`; `lhs_succ` is def-eq to
    //   the RHS (prefix_lwt ≡ Fin.prod m (factor_fn∘castSucc),
    //   factor_last ≡ factor_fn (last m)). So `Fin.prod_succ` retyped at the
    //   def-eq endpoints proves `lhs = lhs_succ`. First arg is `m`
    //   (`Fin.prod_succ m g : Fin.prod (m+1) g = …`), `g := factor_fn`.
    let leg_a = c.fin_prod_succ(&m, &factor_fn);

    // leg B : lhs_succ = pow_prod
    //   = congr on mul of (IH at restrict S) and (factor helper at S last).
    //   prefix:  levelWt ρ m (restrict S) = powNat (ρ·ρ) (setSizeNat m restrict)
    //              = ih (restrict S)
    //   factor:  factor ρ (S last) = powNat (ρ·ρ) (indNat (S last))
    //              = levelWt_factor_eq_powNat_indNat ρ (S last)
    //   glue both via congr into Rat.mul (two-step: congr left, congr right).
    let ih_restrict = Expr::app(ih.clone(), restrict_s.clone());
    let factor_eq = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.levelWt_factor_eq_powNat_indNat"),
            vec![],
        ),
        [rho.clone(), s_last.clone()],
    );
    // congr left: prefix_lwt · factor_last = pow_prefix · factor_last
    let leg_b1 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let mlam = d.finish_child(d.mk_lam(
            t_id,
            BinderInfo::Default,
            c.rat.clone(),
            c.mul(t, factor_last.clone()),
        ));
        c.congr_rat(prefix_lwt.clone(), pow_prefix.clone(), mlam, ih_restrict)
    };
    // congr right: pow_prefix · factor_last = pow_prefix · pow_ind
    let leg_b2 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let mlam = d.finish_child(d.mk_lam(
            t_id,
            BinderInfo::Default,
            c.rat.clone(),
            c.mul(pow_prefix.clone(), t),
        ));
        c.congr_rat(factor_last.clone(), pow_ind.clone(), mlam, factor_eq)
    };
    let mid_b = c.mul(pow_prefix.clone(), factor_last.clone());
    let leg_b = c.trans_rat(lhs_succ.clone(), mid_b, pow_prod.clone(), leg_b1, leg_b2);

    // leg C : pow_prod = rhs
    //   pow_prod = powNat (ρ·ρ) split_nat  via Eq.symm (powNat_add (ρ·ρ) ssn_restrict ind_last)
    //   powNat (ρ·ρ) split_nat = powNat (ρ·ρ) (setSizeNat (m+1) S)  via congr on
    //     Eq.symm (popcount_succ_split m S) (a Nat equality lifted by powNat (ρ·ρ) ·)
    let leg_c1 = {
        // powNat_add : (ρ·ρ)^(a+b) = (ρ·ρ)^a · (ρ·ρ)^b ; symm gives pow_prod = pow_split
        let padd = c.pow_add(&base, &ssn_restrict, &ind_last);
        c.symm_rat(pow_split.clone(), pow_prod.clone(), padd)
    };
    let leg_c2 = {
        // popcount_succ_split m S : setSizeNat (m+1) S = split_nat
        //   symm : split_nat = setSizeNat (m+1) S
        let split_eq = c.popcount_split(&m, &s); // ssn_sm = split_nat
        let split_eq_sym = {
            let eq_symm = Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            );
            Expr::apps(
                eq_symm,
                [c.nat.clone(), ssn_sm.clone(), split_nat.clone(), split_eq],
            )
        };
        // motive for congr_nat_rat : fun (t : Nat) => powNat (ρ·ρ) t
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.nat.clone());
        let mlam =
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), c.pow(&base, &t)));
        // congr : powNat (ρ·ρ) split_nat = powNat (ρ·ρ) (setSizeNat (m+1) S)
        c.congr_nat_rat(split_nat.clone(), ssn_sm.clone(), mlam, split_eq_sym)
    };
    let leg_c = c.trans_rat(
        pow_prod.clone(),
        pow_split.clone(),
        rhs.clone(),
        leg_c1,
        leg_c2,
    );

    // ── Chain : lhs = lhs_succ = pow_prod = rhs ──
    let t_ab = c.trans_rat(
        lhs.clone(),
        lhs_succ.clone(),
        pow_prod.clone(),
        leg_a,
        leg_b,
    );
    let proof = c.trans_rat(lhs.clone(), pow_prod.clone(), rhs.clone(), t_ab, leg_c);

    // wrap: fun (m) (ih) (S) => proof
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp_sm, proof);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, val);
    b.finish_child(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), val))
}

fn build_eq_pow_nat_value(c: &LevelSplitConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());

    let motive = eq_pow_nat_motive(c, &b, &rho);

    // base : motive 0 = ∀ S : HCPoint 0, levelWt ρ 0 S = powNat (ρ·ρ) (setSizeNat 0 S)
    //   both sides ι-reduce to Rat.one; close with fun S => Eq.refl Rat.one.
    let base = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp0 = c.hcpoint_of(&c.nat_zero);
        let (s_id, s) = d.fresh_local(hcp0.clone());
        // levelWt ρ 0 S — refl on the LHS, kernel collapses both to Rat.one.
        let lhs0 = c.level_wt(&rho, &c.nat_zero, &s);
        let refl = c.refl_rat(lhs0);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp0, refl))
    };

    let step = build_eq_pow_nat_step(c, &b, &rho);

    // Prop-valued motive (`fun k => ∀ S, Eq …`) ⇒ recursor at universe level 0.
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let body = Expr::apps(nat_rec, [motive, base, step, n.clone()]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val))
}

// ===========================================================================
// (item 2) noise_spectral_level — the level-weighted spectral mass in
// KKL-usable form.
//
//   ∀ (ρ : Rat) (n : Nat) (a : HCPoint n → Rat),
//     subsetSum n (fun x => subsetSum n (fun y =>
//         (a x · a y) · noiseDensityW (ρ·ρ) n x y))
//       = subsetSum n (fun S => levelWt ρ n S · (A a S · A a S))
//
// (`A a S = Σ_x a x·χ_S x`.) Instantiate `noise_spectral_core` at the SQUARED
// weight `ρ → ρ·ρ`; its RHS weight is `powNat (ρ·ρ) (pc n S)` ≡
// `powNat (ρ·ρ) (setSizeNat n S)` (pc ≡ setSizeNat, byte-for-byte), which
// `levelWt_eq_powNat` rewrites to `levelWt ρ n S` under `subsetSum_congr`.
//
//   proof = Eq.trans (noise_spectral_core (ρ·ρ) n a)
//                    (subsetSum_congr n G_pow G_lvl hyp)
//   hyp S = congrArg (fun w => w·(A·A)) (Eq.symm (levelWt_eq_powNat ρ n S))
//
// The middle endpoint `subsetSum n G_pow` (with the setSizeNat-indexed weight)
// is def-eq to `noise_spectral_core (ρ·ρ)`'s RHS, so the `Eq.trans` typechecks.
// Kernel-checked, constructive (leaves: noise_spectral_core, subsetSum_congr,
// levelWt_eq_powNat, congrArg/Eq.symm/Eq.trans — all Constructive, empty closure).
// ===========================================================================

fn build_spectral_level_type(c: &LevelSplitConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());
    let rho_sq = c.rho_sq(&rho);
    let lhs = c.ssum(&n, c.lhs_x_fn(&b, &rho_sq, &n, &a));
    let rhs = c.ssum(&n, c.rhs_lvl_fn(&b, &rho, &n, &a));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(a_id, BinderInfo::Default, a_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

fn build_spectral_level_value(c: &LevelSplitConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());

    let rho_sq = c.rho_sq(&rho);

    // LHS = subsetSum n (lhs_x_fn (ρ·ρ)); G_pow / G_lvl integrands.
    let lhs = c.ssum(&n, c.lhs_x_fn(&b, &rho_sq, &n, &a));
    let g_pow = c.rhs_pow_fn(&b, &rho, &n, &a);
    let g_lvl = c.rhs_lvl_fn(&b, &rho, &n, &a);
    let mid = c.ssum(&n, g_pow.clone());
    let rhs = c.ssum(&n, g_lvl.clone());

    // nsc : LHS = subsetSum n G_pow  (noise_spectral_core (ρ·ρ) n a; its actual
    // RHS weight `powNat (ρ·ρ) (pc n S)` is def-eq to G_pow's setSizeNat weight).
    let nsc = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.noise_spectral_core"),
            vec![],
        ),
        [rho_sq.clone(), n.clone(), a.clone()],
    );

    // hyp : ∀ S, G_pow S = G_lvl S
    //   = fun S => congrArg (fun w => w·(A·A)) (Eq.symm (levelWt_eq_powNat ρ n S))
    let hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let inner = c.a_coeff(&d, &n, &a, &s);
        let aa = c.mul(inner.clone(), inner); // A·A
        let w_pow = c.pow(&rho_sq, &c.set_size_nat(&n, &s));
        let w_lvl = c.level_wt(&rho, &n, &s);
        // levelWt_eq_powNat ρ n S : w_lvl = w_pow ; symm : w_pow = w_lvl
        let lep = c.levelwt_eq_pownat(&rho, &n, &s);
        let lep_sym = c.symm_rat(w_lvl.clone(), w_pow.clone(), lep);
        // motive : fun (w : Rat) => w·(A·A)
        let mlam = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (t_id, t) = e.fresh_local(c.rat.clone());
            e.finish_child(e.mk_lam(
                t_id,
                BinderInfo::Default,
                c.rat.clone(),
                c.mul(t, aa.clone()),
            ))
        };
        // congrArg : (w_pow·(A·A)) = (w_lvl·(A·A))  i.e. G_pow S = G_lvl S
        let body = c.congr_rat(w_pow, w_lvl, mlam, lep_sym);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    };

    // congr : subsetSum n G_pow = subsetSum n G_lvl
    let congr = c.ssum_congr(&n, &g_pow, &g_lvl, hyp);

    // proof : LHS = subsetSum n G_lvl
    let proof = c.trans_rat(lhs, mid, rhs, nsc, congr);

    let val = b.mk_lam(a_id, BinderInfo::Default, a_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val))
}

impl Environment {
    /// Register `BoolAnalysis.levelWt_factor_eq_powNat_indNat` — the per-coordinate
    /// factor identity `Bool.rec 1 (ρ·ρ) b = powNat (ρ·ρ) (indNat b)`. CHECKED
    /// `Constructive` (empty closure). Idempotent.
    pub(crate) fn register_levelwt_factor_eq_pow_nat_ind_nat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.levelWt_factor_eq_powNat_indNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?; // Rat.powNat + powNat_zero/succ + Rat.mul_one
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_zero_theorem()?;
        self.register_rat_pow_nat_succ_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = LevelSplitConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_factor_type(&c),
            value: build_factor_value(&c),
        })
    }

    /// Register `BoolAnalysis.levelWt_eq_powNat` — the K0 `Fin.prod ↔ powNat`
    /// bridge `levelWt ρ n S = powNat (ρ·ρ) (setSizeNat n S)`. `Nat.rec` induction
    /// on `n`. CHECKED `Constructive` (empty closure). Idempotent.
    pub(crate) fn register_levelwt_eq_pow_nat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.levelWt_eq_powNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_zero_theorem()?;
        self.register_rat_pow_nat_succ_theorem()?;
        self.register_rat_pow_nat_add_theorem()?;
        self.register_fin_prod_succ_theorem()?;
        self.register_popcount_succ_split_theorem()?;
        self.register_levelwt_factor_eq_pow_nat_ind_nat()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = LevelSplitConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_eq_pow_nat_type(&c),
            value: build_eq_pow_nat_value(&c),
        })
    }

    /// Register `BoolAnalysis.noise_spectral_level` — the level-weighted spectral
    /// mass `Σ_x Σ_y (a x·a y)·noiseDensityW (ρ·ρ) n x y
    /// = Σ_S levelWt ρ n S·(A a S·A a S)` (item 2, the spectral-side interface the
    /// 4-norm↔spectral inversion pivots through). `noise_spectral_core` at the
    /// squared weight `ρ·ρ`, with the per-`S` weight rewritten `powNat (ρ·ρ) |S|
    /// → levelWt ρ n S` via `levelWt_eq_powNat` under `subsetSum_congr`. CHECKED
    /// `Constructive` (empty closure). Idempotent.
    pub(crate) fn register_noise_spectral_level(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_spectral_level");
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
        self.register_noise_spectral_core_theorem()?;
        self.register_subset_sum_congr()?;
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_levelwt_eq_pow_nat()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = LevelSplitConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_spectral_level_type(&c),
            value: build_spectral_level_value(&c),
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
    fn test_levelwt_factor_eq_pow_nat_ind_nat_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_levelwt_factor_eq_pow_nat_ind_nat()
            .expect("register_levelwt_factor_eq_pow_nat_ind_nat");
        checked_constructive_theorem(&env, "BoolAnalysis.levelWt_factor_eq_powNat_indNat");
    }

    #[test]
    fn test_levelwt_factor_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_levelwt_factor_eq_pow_nat_ind_nat()
            .expect("first");
        env.register_levelwt_factor_eq_pow_nat_ind_nat()
            .expect("idempotent");
    }

    #[test]
    fn test_levelwt_eq_pow_nat_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_levelwt_eq_pow_nat()
            .expect("register_levelwt_eq_pow_nat");
        checked_constructive_theorem(&env, "BoolAnalysis.levelWt_eq_powNat");
    }

    #[test]
    fn test_levelwt_eq_pow_nat_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_levelwt_eq_pow_nat().expect("first");
        env.register_levelwt_eq_pow_nat().expect("idempotent");
    }

    #[test]
    fn test_noise_spectral_level_is_constructive() {
        let mut env = Environment::with_prelude();
        env.register_noise_spectral_level()
            .expect("register_noise_spectral_level");
        checked_constructive_theorem(&env, "BoolAnalysis.noise_spectral_level");
    }

    #[test]
    fn test_noise_spectral_level_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_noise_spectral_level().expect("first");
        env.register_noise_spectral_level().expect("idempotent");
    }
}
