// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — RUNG 4: the clean charging bound
//! `restrictMass_le_outside_influence`.
//!
//! ```text
//! BoolAnalysis.restrictMass_le_outside_influence :
//!   ∀ (n : Nat) (f : BoolFn n) (J : HCPoint n),
//!     subsetSum n (fun S =>
//!         ind (notSubsetMask n S J)
//!           · (FourierCoefficient n f S · FourierCoefficient n f S))     -- Σ_{S⊄J} f̂(S)²
//!       ≤
//!     Fin.sum n (fun i =>
//!         ind (Bool.not (J i)) · Influence n f i)                        -- Σ_{i∉J} Inf_i[f]
//! ```
//!
//! i.e. `Σ_{S⊄J} f̂(S)² ≤ Σ_{i∉J} Inf_i[f]` — the Fourier mass on the subsets `S`
//! NOT contained in `J` is bounded by the total influence of the coordinates
//! OUTSIDE `J`. This is the clean charging argument of the Friedgut junta
//! theorem (O'Donnell, *Analysis of Boolean Functions*, §9.6), and it is
//! ENTIRELY crux-independent — no hypercontractivity, no `kkl`/`deriv_level`
//! surface. It is rung 4 of `designs/2026-06-13-friedgut-junta-theorem-roadmap.md`.
//!
//! ## Proof skeleton (constructive, empty admitted-axiom closure)
//!
//! Write `w(S) := f̂(S)·f̂(S) ≥ 0` and `D_J(S) := fun i => S i ∧ ¬J i` (the `S\J`
//! coordinate indicator, an `HCPoint n`). Note
//! `notSubsetMask n S J ≡ Nat.ble 1 (setSizeNat n (D_J S))` definitionally, and
//! `setSize n (D_J S) = Σ_i ind (S i ∧ ¬J i)` is the `Rat`-valued `|S\J|`.
//!
//! 1. **`influence_fourier`** rewrites the outside-influence side
//!    `Σ_i ind(¬J i)·Inf_i = Σ_i ind(¬J i)·subsetSum_S(ind(S i)·w S)`.
//! 2. **B4a — the J^c-masked double-count** (this module, `restrict_double_count`):
//!    `Σ_i ind(¬J i)·subsetSum_S(ind(S i)·w S) = subsetSum_S(w S · setSize n (D_J S))`.
//!    Proven from `Fin.sum_smul` (pull the per-`i` mask into the inner subsetSum),
//!    `Fin.sum_swap` (the finite Fubini transpose `Fin n × Fin 2^n`), the
//!    `ind_and` product identity, `Fin.sum_mul`/`Fin.sum_congr` (factor `w(S)`
//!    out of the inner `i`-sum), and `Rat.mul_comm`.
//! 3. **Termwise monotonicity** (`subsetSum_le_of_pointwise`, `w(S) ≥ 0` via
//!    `fourier_sq_nonneg`): `subsetSum_S(ind(notSubsetMask n S J)·w S)
//!      ≤ subsetSum_S(w S · setSize n (D_J S))`, by the per-`S` bound
//!    `ind(Nat.ble 1 (setSizeNat n (D_J S)))·w S ≤ w S · setSize n (D_J S)`. The
//!    indicator-`≤`-count crux is the standalone Nat lemma
//!    `ind(Nat.ble 1 m) ≤ Rat.mk (Int.ofNat m) 1` (`ind_ble_one_le_natCast`,
//!    `Bool.casesOn` + `Nat.cast_le_of_ble`), cast to `setSize` via
//!    `setSize_eq_natCast`, then scaled by `w(S) ≥ 0` with
//!    `Rat.mul_le_mul_of_nonneg_right`.
//! 4. **Chain:** `LHS = (3-LHS) ≤ (3-RHS) =[symm B4a] =[symm step1] RHS`.
//!
//! Every dependency (`influence_fourier`, `Fin.sum_swap`/`_smul`/`_mul`/`_congr`,
//! `subsetSum`/`_smul`/`_le_of_pointwise`, `setSize`/`setSizeNat`/
//! `setSize_eq_natCast`, `Nat.cast_le_of_ble`, `fourier_sq_nonneg`,
//! `Rat.mul_le_mul_of_nonneg_right`, `Rat.mul_comm`/`_assoc`, the `Eq`/`Bool.rec`
//! built-ins) is itself `Constructive` with an empty admitted-axiom closure, so
//! every Theorem here is `ProofQuality::Constructive` with an empty closure. NO
//! `sorry` / `sorryAx` / `trustedArith` / `trustedAy` / `add_decl_unchecked` /
//! `add_decl_structural` / `native_decide` / `unsafe` / `Rat.dist` / `Real`. No
//! axiom added or removed.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared carrier atoms for the RUNG 4 charging bound. Embeds `OrderConsts`
/// for the `LE.le @Rat instLERat` order spelling shared with `Fin.sum_le`,
/// `subsetSum_le_of_pointwise`, `Nat.cast_le_of_ble`, and `fourier_sq_nonneg`.
struct Rung4Consts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    bool_and: Expr,
    bool_not: Expr,
    fin: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    influence: Expr,
    fourier: Expr,
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    not_subset_mask: Expr,
    fin_sum: Expr,
    fin_sum_swap: Expr,
    fin_sum_smul: Expr,
    fin_sum_mul: Expr,
    fin_sum_congr: Expr,
    subset_sum_le_of_pointwise: Expr,
    influence_fourier: Expr,
    fourier_sq_nonneg: Expr,
    set_size_eq_natcast: Expr,
    nat_cast_le_of_ble: Expr,
    mul_le_right: Expr,
    rat_mul: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_ble: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    hc_decode: Expr,
    bool_cases_on: Expr,
    eq_bool: Expr,
    eq_refl_bool: Expr,
    congr_arg: Expr,
}

impl Rung4Consts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            fin: k("Fin"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            influence: k("BoolAnalysis.Influence"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            ind: k("BoolAnalysis.ind"),
            set_size: k("BoolAnalysis.setSize"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            fin_sum: k("Fin.sum"),
            fin_sum_swap: k("Fin.sum_swap"),
            fin_sum_smul: k("Fin.sum_smul"),
            fin_sum_mul: k("Fin.sum_mul"),
            fin_sum_congr: k("Fin.sum_congr"),
            subset_sum_le_of_pointwise: k("BoolAnalysis.subsetSum_le_of_pointwise"),
            influence_fourier: k("BoolAnalysis.influence_fourier"),
            fourier_sq_nonneg: k("BoolAnalysis.fourier_sq_nonneg"),
            set_size_eq_natcast: k("BoolAnalysis.setSize_eq_natCast"),
            nat_cast_le_of_ble: k("Nat.cast_le_of_ble"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_mul: k("Rat.mul"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_ble: k("Nat.ble"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            bool_cases_on: Expr::const_(Name::from_string("Bool.casesOn"), vec![l0]),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── small constructors ──
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
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
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn band(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [a, b])
    }
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), a)
    }
    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn ble1(&self, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [self.one_nat(), m])
    }
    fn pow2(&self, n: &Expr) -> Expr {
        let one = self.one_nat();
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    fn decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    /// `Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), m), self.one_nat()],
        )
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `w(S) := f̂(S)·f̂(S)` — the (nonnegative) Fourier mass weight.
    fn w_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn not_subset_mask_of(&self, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.not_subset_mask.clone(),
            [n.clone(), s.clone(), j.clone()],
        )
    }
    fn fin_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn refl_rat(&self, x: Expr) -> Expr {
        Expr::apps(self.order.eq_refl.clone(), [self.rat.clone(), x])
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn trans_rat(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, c, h1, h2)
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_a)
    }
    /// `@congrArg Rat Rat a b motive h : motive a = motive b`.
    fn congr_rat(&self, a: Expr, b: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, motive, h],
        )
    }
    /// `@Eq Bool a b`.
    fn eq_bool_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_bool.clone(), [self.bool_.clone(), a, b])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, c])
    }

    /// `D_J S := fun (i : Fin n) => Bool.and (S i) (Bool.not (J i))` — the `S\J`
    /// coordinate set, an `HCPoint n`. This is BYTE-IDENTICAL to the lambda
    /// inside `notSubsetMask`'s body, so `notSubsetMask n S J ≡
    /// Nat.ble 1 (setSizeNat n (D_J S))` definitionally.
    fn diff_point(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let j_i = Expr::app(j.clone(), i.clone());
        let body = self.band(s_i, self.bnot(j_i));
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
}

// ===========================================================================
// L1 — `BoolAnalysis.ind_and : ∀ (a b : Bool), ind (Bool.and a b) = ind a · ind b`.
//
// Single `Bool.casesOn` on `a`:
//   a = false: `Bool.and false b ≡ false`, so `ind false ≡ 0 = 0·ind b ≡
//     ind false · ind b`  via `symm (Rat.zero_mul (ind b))`.
//   a = true:  `Bool.and true b ≡ b`, so `ind b = 1·ind b ≡ ind true · ind b`
//     via `symm (Rat.one_mul (ind b))`.
// Kernel-checked, constructive.
// ===========================================================================

fn ind_and_type(c: &Rung4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.bool_.clone());
    let (bb_id, bb) = b.fresh_local(c.bool_.clone());
    let lhs = c.ind_of(c.band(a.clone(), bb.clone()));
    let rhs = c.mul(c.ind_of(a.clone()), c.ind_of(bb.clone()));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(bb_id, BinderInfo::Default, c.bool_.clone(), concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.bool_.clone(), e);
    b.finish(e)
}

fn ind_and_value(c: &Rung4Consts) -> Expr {
    let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
    let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.bool_.clone());
    let (bb_id, bb) = b.fresh_local(c.bool_.clone());

    let ind_b = c.ind_of(bb.clone());
    // goal at bit value `aa`: ind (Bool.and aa b) = ind aa · ind b.
    let goal_at = |aa: Expr| {
        c.eq_rat(
            c.ind_of(c.band(aa.clone(), bb.clone())),
            c.mul(c.ind_of(aa), ind_b.clone()),
        )
    };

    // motive : fun (aa : Bool) => ind (Bool.and aa b) = ind aa · ind b
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (aa_id, aa) = m.fresh_local(c.bool_.clone());
        let body = goal_at(aa.clone());
        m.finish_child(m.mk_lam(aa_id, BinderInfo::Default, c.bool_.clone(), body))
    };

    // false branch : ind (Bool.and false b) = ind false · ind b.
    //   LHS ≡ ind false ≡ 0 ; RHS ≡ ind false · ind b ≡ Rat.zero · ind b.
    //   `Rat.zero_mul (ind b) : Rat.zero · ind b = Rat.zero`; symm gives the goal
    //   (both endpoints def-eq to the goal sides).
    let false_branch = {
        let zb = c.mul(c.order.rat_zero.clone(), ind_b.clone());
        let h = Expr::app(zero_mul, ind_b.clone()); // Rat.zero · ind b = Rat.zero
        c.symm_rat(zb, c.order.rat_zero.clone(), h)
    };

    // true branch : ind (Bool.and true b) = ind true · ind b.
    //   LHS ≡ ind b ; RHS ≡ ind true · ind b ≡ Rat.one · ind b.
    //   `Rat.one_mul (ind b) : Rat.one · ind b = ind b`; symm gives the goal.
    let true_branch = {
        let ob = c.mul(c.order.rat_one.clone(), ind_b.clone());
        let h = Expr::app(one_mul, ind_b.clone()); // Rat.one · ind b = ind b
        c.symm_rat(ob, ind_b.clone(), h)
    };

    // @Bool.casesOn motive a false_branch true_branch
    let body = Expr::apps(
        c.bool_cases_on.clone(),
        [motive, a.clone(), false_branch, true_branch],
    );

    let e = b.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.bool_.clone(), e);
    b.finish(e)
}

// ===========================================================================
// L2 — `BoolAnalysis.ind_ble_one_le_natCast :
//   ∀ (m : Nat), ind (Nat.ble 1 m) ≤ Rat.mk (Int.ofNat m) 1`.
//
// Eq-threaded `Bool.casesOn` on `Nat.ble 1 m`:
//   false: `ind false ≡ 0 ≡ mk (ofNat 0) 1`; `Nat.cast_le_of_ble 0 m (refl true)`
//     (`Nat.ble 0 m ≡ true`) gives `mk (ofNat 0) 1 ≤ mk (ofNat m) 1`.
//   true:  `ind true ≡ 1 ≡ mk (ofNat 1) 1`; `Nat.cast_le_of_ble 1 m he` gives
//     `mk (ofNat 1) 1 ≤ mk (ofNat m) 1`, with `he : Nat.ble 1 m = true`.
// Kernel-checked, constructive (closure via `Nat.cast_le_of_ble`).
// ===========================================================================

fn ind_ble_le_type(c: &Rung4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let lhs = c.ind_of(c.ble1(m.clone()));
    let rhs = c.natcast(m.clone());
    let concl = c.rat_le(lhs, rhs);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), concl);
    b.finish(e)
}

fn ind_ble_le_value(c: &Rung4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());

    let ble = c.ble1(m.clone());
    let cast_m = c.natcast(m.clone());

    // motive : fun (bb : Bool) => (Nat.ble 1 m = bb) → ind bb ≤ mk (ofNat m) 1
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (bb_id, bb) = mb.fresh_local(c.bool_.clone());
        let prem = c.eq_bool_of(ble.clone(), bb.clone());
        let concl = c.rat_le(c.ind_of(bb.clone()), cast_m.clone());
        let body = Expr::pi(BinderInfo::Default, prem, concl);
        mb.finish_child(mb.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body))
    };

    // false branch : (Nat.ble 1 m = false) → ind false ≤ mk (ofNat m) 1.
    //   `Nat.cast_le_of_ble 0 m (Eq.refl Bool true)` : mk (ofNat 0) 1 ≤ mk (ofNat m) 1,
    //   def-eq to `ind false ≤ mk (ofNat m) 1` (ind false ≡ 0 ≡ mk (ofNat 0) 1,
    //   Nat.ble 0 m ≡ true).
    let false_branch = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let prem = c.eq_bool_of(ble.clone(), c.bool_false.clone());
        let (he_id, _he) = d.fresh_local(prem.clone());
        let ble0 = Expr::apps(c.nat_ble.clone(), [c.nat_zero.clone(), m.clone()]);
        let refl_true = Expr::apps(c.eq_refl_bool.clone(), [c.bool_.clone(), ble0]);
        let body = Expr::apps(
            c.nat_cast_le_of_ble.clone(),
            [c.nat_zero.clone(), m.clone(), refl_true],
        );
        d.finish_child(d.mk_lam(he_id, BinderInfo::Default, prem, body))
    };

    // true branch : (Nat.ble 1 m = true) → ind true ≤ mk (ofNat m) 1.
    //   `Nat.cast_le_of_ble 1 m he` : mk (ofNat 1) 1 ≤ mk (ofNat m) 1, def-eq to
    //   `ind true ≤ mk (ofNat m) 1` (ind true ≡ 1 ≡ mk (ofNat 1) 1).
    let true_branch = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let prem = c.eq_bool_of(ble.clone(), c.bool_true.clone());
        let (he_id, he) = d.fresh_local(prem.clone());
        let body = Expr::apps(c.nat_cast_le_of_ble.clone(), [c.one_nat(), m.clone(), he]);
        d.finish_child(d.mk_lam(he_id, BinderInfo::Default, prem, body))
    };

    // @Bool.casesOn motive (Nat.ble 1 m) false_branch true_branch (Eq.refl Bool (Nat.ble 1 m))
    let refl_ble = Expr::apps(c.eq_refl_bool.clone(), [c.bool_.clone(), ble.clone()]);
    let body = Expr::apps(
        c.bool_cases_on.clone(),
        [motive, ble, false_branch, true_branch, refl_ble],
    );

    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(e)
}

impl Rung4Consts {
    // ── integrand builders for B4a (the masked double-count) ──

    /// `fun (S : HCPoint n) => Rat.mul (ind (S i)) (w S)` — the per-coordinate
    /// inner subsetSum integrand (the `influence_fourier` RHS shape with `w`).
    fn coord_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let body = self.mul(self.ind_of(s_i), self.w_of(n, f, &s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `fun (i : Fin n) => ind (Bool.not (J i)) · subsetSum n (coord_fn i)` — the
    /// masked outer-`i` integrand on the influence side (B4a LHS integrand).
    fn masked_outer_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let mask = self.ind_of(self.bnot(Expr::app(j.clone(), i.clone())));
        let inner = self.subset_sum_of(n, self.coord_fn(&ch, n, f, &i));
        let body = self.mul(mask, inner);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (i : Fin n) => ind (Bool.not (J i)) · Influence n f i` — the masked
    /// outside-influence integrand (RHS of the top theorem; the `influence_fourier`
    /// pre-image of `masked_outer_fn`).
    fn masked_infl_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let mask = self.ind_of(self.bnot(Expr::app(j.clone(), i.clone())));
        let body = self.mul(mask, self.influence_of(n, f, &i));
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `F i j := ind(¬J i)·(ind((hcDecode n j) i)·w(hcDecode n j))` of type
    /// `Fin n → Fin (2^n) → Rat` — the integrand of `Fin.sum_swap`.
    fn swap_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr) -> Expr {
        let mut ci = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ci.fresh_local(fin_n.clone());
        let inner = {
            let mut cj = EnvDeclBuilder::child_of(&ci);
            let fin_pow = self.fin_of(&self.pow2(n));
            let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
            let s = self.decode(n, &jj);
            let mask = self.ind_of(self.bnot(Expr::app(j.clone(), i.clone())));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = self.mul(mask, self.mul(self.ind_of(s_i), self.w_of(n, f, &s)));
            cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
        };
        ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, inner))
    }

    /// `fun (S : HCPoint n) => Rat.mul (w S) (setSize n (D_J S))` — the B4a RHS
    /// integrand (`w(S)·|S\J|`).
    fn rhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let d = self.diff_point(&ch, n, &s, j);
        let size = self.set_size_of(n, &d);
        let body = self.mul(self.w_of(n, f, &s), size);
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

// ===========================================================================
// B4a — `BoolAnalysis.restrict_double_count :
//   ∀ (n) (f : BoolFn n) (J : HCPoint n),
//     Fin.sum n (fun i => ind(¬J i)·subsetSum_S(ind(S i)·w S))
//       = subsetSum_S(w S · setSize n (D_J S))`.
//
// The J^c-masked Fubini double-count. (We carry the concrete weight
// `w S = f̂ S · f̂ S` rather than an abstract `w` — the only property used is the
// pure algebra below, but pinning `w` keeps every term aligned with the top
// theorem so the chain composes by `Eq.refl` at the boundaries.)
// ===========================================================================

fn restrict_double_count_type(c: &Rung4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let lhs = c.fin_sum_of(&n, c.masked_outer_fn(&b, &n, &f, &j));
    let rhs = c.subset_sum_of(&n, c.rhs_fn(&b, &n, &f, &j));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(j_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn restrict_double_count_value(c: &Rung4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let p2n = c.pow2(&n);
    let big_f = c.swap_fn(&b, &n, &f, &j);

    // ── stage 1: rewrite the masked outer integrand to `Fin.sum (2^n) (F i ·)`.
    let lhs0 = c.fin_sum_of(&n, c.masked_outer_fn(&b, &n, &f, &j));

    // `outer_i_F := fun (i : Fin n) => Fin.sum (2^n) (fun j => F i j)` — Fin.sum_swap LHS.
    let outer_i_f = {
        let mut ci = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ci.fresh_local(fin_n.clone());
        let row = {
            let mut cj = EnvDeclBuilder::child_of(&ci);
            let fin_pow = c.fin_of(&p2n);
            let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
            let s = c.decode(&n, &jj);
            let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask, c.mul(c.ind_of(s_i), c.w_of(&n, &f, &s)));
            cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
        };
        let body = c.fin_sum_of(&p2n, row);
        ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let sum_outer_i = c.fin_sum_of(&n, outer_i_f.clone());

    // pointwise1 : ∀ i, masked_outer i = (outer_i_F i).
    let pointwise1 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
        // Gi := fun (jj : Fin (2^n)) => ind((dec jj) i)·w(dec jj)
        let gi = {
            let mut cj = EnvDeclBuilder::child_of(&d);
            let fin_pow = c.fin_of(&p2n);
            let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
            let s = c.decode(&n, &jj);
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(c.ind_of(s_i), c.w_of(&n, &f, &s));
            cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
        };
        // Fin.sum_smul (2^n) mask Gi : Σ_jj (mask·Gi jj) = mask·Σ_jj Gi jj.
        let smul = Expr::apps(
            c.fin_sum_smul.clone(),
            [p2n.clone(), mask.clone(), gi.clone()],
        );
        // sumprod := Σ_jj (mask·Gi jj) ≡ Fin.sum (2^n) (fun j => F i j)  (= outer_i_F i, δ).
        let sumprod = {
            let mut cj = EnvDeclBuilder::child_of(&d);
            let fin_pow = c.fin_of(&p2n);
            let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
            let s = c.decode(&n, &jj);
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask.clone(), c.mul(c.ind_of(s_i), c.w_of(&n, &f, &s)));
            cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
        };
        let sum_sumprod = c.fin_sum_of(&p2n, sumprod);
        // mask·subsetSum ≡ mask·Σ_jj Gi jj (subsetSum reducible).
        let mask_ss = c.mul(mask.clone(), c.fin_sum_of(&p2n, gi.clone()));
        // smul : Eq sum_sumprod mask_ss  (Fin.sum_smul LHS = Σ_jj (mask·Gi jj) = sum_sumprod,
        //   RHS = mask·Σ_jj Gi jj = mask_ss). We want the goal `mask·subsetSum = Σ_jj (mask·Gi)`
        //   ≡ Eq mask_ss sum_sumprod, i.e. Eq.symm of smul.
        let body = c.symm_rat(sum_sumprod, mask_ss, smul);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    // step1 : Fin.sum n (masked_outer) = Fin.sum n (outer_i_F)
    //   [Fin.sum_congr n masked_outer outer_i_F pointwise1].
    let step1 = Expr::apps(
        c.fin_sum_congr.clone(),
        [
            n.clone(),
            c.masked_outer_fn(&b, &n, &f, &j),
            outer_i_f.clone(),
            pointwise1,
        ],
    );

    // ── stage 2: Fin.sum_swap n (2^n) F : Σ_i Σ_j F = Σ_j Σ_i F.
    let step2 = Expr::apps(
        c.fin_sum_swap.clone(),
        [n.clone(), p2n.clone(), big_f.clone()],
    );
    // swapped := Σ_j (Σ_i F i j) — RHS of sum_swap.
    let inner_swapped = {
        let mut cj = EnvDeclBuilder::child_of(&b);
        let fin_pow = c.fin_of(&p2n);
        let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
        let row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let s = c.decode(&n, &jj);
            let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask, c.mul(c.ind_of(s_i), c.w_of(&n, &f, &s)));
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let body = c.fin_sum_of(&n, row);
        cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
    };
    let sum_swapped = c.fin_sum_of(&p2n, inner_swapped.clone());

    // ── stage 3: per-j (per S = dec j) collapse to `w S · setSize n (D_J S)`.
    // target_j := fun j => w(dec j) · setSize n (D_J (dec j)).
    let target_j = {
        let mut cj = EnvDeclBuilder::child_of(&b);
        let fin_pow = c.fin_of(&p2n);
        let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
        let s = c.decode(&n, &jj);
        let d = c.diff_point(&cj, &n, &s, &j);
        let size = c.set_size_of(&n, &d);
        let body = c.mul(c.w_of(&n, &f, &s), size);
        cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
    };

    // per_j : fun (j : Fin (2^n)) => (inner_swapped j) = (target_j j).
    let per_j = {
        let mut cj = EnvDeclBuilder::child_of(&b);
        let fin_pow = c.fin_of(&p2n);
        let (jj_id, jj) = cj.fresh_local(fin_pow.clone());
        let s = c.decode(&n, &jj);
        let d_pt = c.diff_point(&cj, &n, &s, &j);
        let w_s = c.w_of(&n, &f, &s);
        let size = c.set_size_of(&n, &d_pt);

        // inner_row := fun (i : Fin n) => ind(¬J i)·(ind(S i)·w S)  (= inner_swapped j).
        let inner_row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = c.mul(mask, c.mul(c.ind_of(s_i), w_s.clone()));
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        // dw_row := fun (i : Fin n) => ind(D_J S i)·w S  (= ind(S i ∧ ¬J i)·w S).
        let dw_row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let d_i = c.band(
                Expr::app(s.clone(), i.clone()),
                c.bnot(Expr::app(j.clone(), i.clone())),
            );
            let body = c.mul(c.ind_of(d_i), w_s.clone());
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        // d_ind_row := fun (i : Fin n) => ind(D_J S i)  (= the setSize integrand).
        let d_ind_row = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let d_i = c.band(
                Expr::app(s.clone(), i.clone()),
                c.bnot(Expr::app(j.clone(), i.clone())),
            );
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, c.ind_of(d_i)))
        };

        // P_i : ind(¬J i)·(ind(S i)·w S) = ind(D_J S i)·w S.
        //   = (ind(¬J i)·ind(S i))·w S          [symm mul_assoc]
        //   = (ind(S i)·ind(¬J i))·w S          [congr (·w S) (mul_comm)]
        //   = ind(S i ∧ ¬J i)·w S               [congr (·w S) (symm ind_and)]
        let pw = {
            let mut ci = EnvDeclBuilder::child_of(&cj);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let s_i = Expr::app(s.clone(), i.clone());
            let nj_i = c.bnot(Expr::app(j.clone(), i.clone()));
            let ind_si = c.ind_of(s_i.clone());
            let ind_nj = c.ind_of(nj_i.clone());

            // e0 := ind(¬J i)·(ind(S i)·w S)
            let e0 = c.mul(ind_nj.clone(), c.mul(ind_si.clone(), w_s.clone()));
            // e1 := (ind(¬J i)·ind(S i))·w S
            let nj_si = c.mul(ind_nj.clone(), ind_si.clone());
            let e1 = c.mul(nj_si.clone(), w_s.clone());
            // leg1 : e0 = e1   := symm (mul_assoc ind(¬J i) ind(S i) (w S))
            let assoc = c.mul_assoc(ind_nj.clone(), ind_si.clone(), w_s.clone());
            let leg1 = c.symm_rat(e1.clone(), e0.clone(), assoc);

            // motive_r : fun (z : Rat) => z · w S
            let motive_r = {
                let mut e = EnvDeclBuilder::child_of(&ci);
                let (z_id, z) = e.fresh_local(c.rat.clone());
                let body = c.mul(z, w_s.clone());
                e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // e2 := (ind(S i)·ind(¬J i))·w S
            let si_nj = c.mul(ind_si.clone(), ind_nj.clone());
            let e2 = c.mul(si_nj.clone(), w_s.clone());
            // leg2 : e1 = e2  := congr (·w S) (mul_comm ind(¬J i) ind(S i))
            let cmm = c.mul_comm(ind_nj.clone(), ind_si.clone());
            let leg2 = c.congr_rat(nj_si.clone(), si_nj.clone(), motive_r.clone(), cmm);

            // e3 := ind(S i ∧ ¬J i)·w S   (= dw_row i)
            let d_i = c.band(s_i.clone(), nj_i.clone());
            let ind_d = c.ind_of(d_i.clone());
            let e3 = c.mul(ind_d.clone(), w_s.clone());
            // ind_and (S i)(¬J i) : ind(S i ∧ ¬J i) = ind(S i)·ind(¬J i)
            let ind_and = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.ind_and"), vec![]),
                [s_i.clone(), nj_i.clone()],
            );
            // ind_and : Eq ind_d si_nj (ind(S i ∧ ¬J i) = ind(S i)·ind(¬J i)).
            // symm : ind(S i)·ind(¬J i) = ind(S i ∧ ¬J i)  := Eq.symm of ind_and.
            let ind_and_sym = c.symm_rat(ind_d.clone(), si_nj.clone(), ind_and);
            // leg3 : e2 = e3  := congr (·w S) (ind_and_sym)
            let leg3 = c.congr_rat(si_nj.clone(), ind_d.clone(), motive_r.clone(), ind_and_sym);

            // chain e0 = e1 = e2 = e3.
            let t1 = c.trans_rat(e0.clone(), e1.clone(), e2.clone(), leg1, leg2);
            let body = c.trans_rat(e0, e2, e3, t1, leg3);
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };

        // q1 : Σ_i ind(¬J i)·(ind(S i)·w S) = Σ_i ind(D_J S i)·w S
        //   [Fin.sum_congr n inner_row dw_row pw]
        let q1 = Expr::apps(
            c.fin_sum_congr.clone(),
            [n.clone(), inner_row.clone(), dw_row.clone(), pw],
        );
        // q2 : Σ_i ind(D_J S i)·w S = (Σ_i ind(D_J S i)) · w S
        //   [Fin.sum_mul n d_ind_row (w S)].  RHS ≡ setSize n (D_J S) · w S (δ).
        let q2 = Expr::apps(
            c.fin_sum_mul.clone(),
            [n.clone(), d_ind_row.clone(), w_s.clone()],
        );
        // q3 : setSize n (D_J S) · w S = w S · setSize n (D_J S)  [mul_comm]
        let q3 = c.mul_comm(size.clone(), w_s.clone());

        // endpoints.
        let sum_inner = c.fin_sum_of(&n, inner_row.clone()); // = inner_swapped j (δ)
        let sum_dw = c.fin_sum_of(&n, dw_row.clone());
        let size_w = c.mul(size.clone(), w_s.clone()); // (Σ ind(D))·w S ≡ setSize·w S
        let w_size = c.mul(w_s.clone(), size.clone()); // = target_j j

        // chain: sum_inner = sum_dw (q1) = size·w (q2) = w·size (q3).
        let t1 = c.trans_rat(sum_inner.clone(), sum_dw.clone(), size_w.clone(), q1, q2);
        let body = c.trans_rat(sum_inner, size_w, w_size, t1, q3);
        cj.finish_child(cj.mk_lam(jj_id, BinderInfo::Default, fin_pow, body))
    };

    // step3 : Σ_j (Σ_i F i j) = Σ_j (w(dec j)·setSize n (D_J(dec j)))
    //   [Fin.sum_congr (2^n) inner_swapped target_j per_j].
    let step3 = Expr::apps(
        c.fin_sum_congr.clone(),
        [p2n.clone(), inner_swapped.clone(), target_j.clone(), per_j],
    );

    // ── chain: lhs0 =(step1) sum_outer_i =(step2) sum_swapped =(step3) rhs.
    let sum_target = c.fin_sum_of(&p2n, target_j.clone());
    let rhs = c.subset_sum_of(&n, c.rhs_fn(&b, &n, &f, &j));

    let t1 = c.trans_rat(
        lhs0.clone(),
        sum_outer_i.clone(),
        sum_swapped.clone(),
        step1,
        step2,
    );
    let proof = c.trans_rat(lhs0, sum_swapped.clone(), rhs.clone(), t1, {
        // step3 : sum_swapped = sum_target ; sum_target ≡ rhs (δ). Retype via refl.
        c.trans_rat(
            sum_swapped,
            sum_target,
            rhs.clone(),
            step3,
            c.refl_rat(rhs.clone()),
        )
    });

    let e = b.mk_lam(j_id, BinderInfo::Default, hcp, proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// ===========================================================================
// TOP — `BoolAnalysis.restrictMass_le_outside_influence`.
// ===========================================================================

impl Rung4Consts {
    /// `fun (S : HCPoint n) => ind (notSubsetMask n S J) · w S` — the LHS
    /// (restricted-mass) subsetSum integrand `Σ_{S⊄J} f̂(S)²`.
    fn mass_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let mask = self.ind_of(self.not_subset_mask_of(n, &s, j));
        let body = self.mul(mask, self.w_of(n, f, &s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// Per-`S` bound `ind(notSubsetMask n S J)·w S ≤ w S · setSize n (D_J S)`.
    fn per_s_bound(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr, j: &Expr) -> Expr {
        let d = self.diff_point(parent, n, s, j);
        let size = self.set_size_of(n, &d); // setSize n (D_J S)
        let size_nat = self.set_size_nat_of(n, &d); // setSizeNat n (D_J S)
        let cast = self.natcast(size_nat.clone()); // mk (ofNat (setSizeNat …)) 1
        let mask = self.ind_of(self.not_subset_mask_of(n, s, j)); // ≡ ind(Nat.ble 1 (setSizeNat …))
        let w_s = self.w_of(n, f, s);

        // l2 : ind(Nat.ble 1 (setSizeNat n (D_J S))) ≤ mk (ofNat (setSizeNat …)) 1
        //   [ind_ble_one_le_natCast (setSizeNat n (D_J S))].  LHS ≡ ind(mask) (δ).
        let l2 = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.ind_ble_one_le_natCast"),
                vec![],
            ),
            [size_nat.clone()],
        );

        // bridge : setSize n (D_J S) = mk (ofNat (setSizeNat …)) 1
        //   [setSize_eq_natCast n (D_J S)] ; symm : mk … = setSize.
        let bridge = Expr::apps(self.set_size_eq_natcast.clone(), [n.clone(), d.clone()]);
        let bridge_sym = self.symm_rat(size.clone(), cast.clone(), bridge);

        // ind_le_size : ind(mask) ≤ setSize n (D_J S)
        //   := subst (motive t => ind(mask) ≤ t) cast size bridge_sym l2.
        let motive_le = {
            let mut e = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = e.fresh_local(self.rat.clone());
            let body = self.rat_le(mask.clone(), t);
            e.finish_child(e.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let ind_le_size = self.subst_rat(motive_le, cast.clone(), size.clone(), bridge_sym, l2);

        // hnn : 0 ≤ w S   [fourier_sq_nonneg n f S].
        let hnn = Expr::apps(
            self.fourier_sq_nonneg.clone(),
            [n.clone(), f.clone(), s.clone()],
        );

        // mul_le : ind(mask)·w S ≤ setSize n (D_J S)·w S
        //   [Rat.mul_le_mul_of_nonneg_right (w S) (ind mask) (setSize) ind_le_size hnn].
        let mul_le = Expr::apps(
            self.mul_le_right.clone(),
            [w_s.clone(), mask.clone(), size.clone(), ind_le_size, hnn],
        );

        // comm : setSize n (D_J S)·w S = w S · setSize n (D_J S)  [mul_comm].
        let size_w = self.mul(size.clone(), w_s.clone());
        let w_size = self.mul(w_s.clone(), size.clone());
        let comm = self.mul_comm(size.clone(), w_s.clone());

        // final : ind(mask)·w S ≤ w S · setSize n (D_J S)
        //   := subst (motive t => ind(mask)·w S ≤ t) size_w w_size comm mul_le.
        let mask_w = self.mul(mask.clone(), w_s.clone());
        let motive_le2 = {
            let mut e = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = e.fresh_local(self.rat.clone());
            let body = self.rat_le(mask_w.clone(), t);
            e.finish_child(e.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst_rat(motive_le2, size_w, w_size, comm, mul_le)
    }
}

fn top_type(c: &Rung4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let lhs = c.subset_sum_of(&n, c.mass_fn(&b, &n, &f, &j)); // Σ_{S⊄J} f̂²
    let rhs = c.fin_sum_of(&n, c.masked_infl_fn(&b, &n, &f, &j)); // Σ_{i∉J} Inf_i
    let concl = c.rat_le(lhs, rhs);

    let e = b.mk_pi(j_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn top_value(c: &Rung4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    // ── EqR : subsetSum_S(w S · setSize n (D_J S)) = Fin.sum n (ind(¬J i)·Inf_i).
    // B4a : Σ_i ind(¬J i)·subsetSum_S(ind(S i)·w S) = subsetSum_S(w S·setSize).
    let b4a = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.restrict_double_count"),
            vec![],
        ),
        [n.clone(), f.clone(), j.clone()],
    );
    let masked_outer_sum = c.fin_sum_of(&n, c.masked_outer_fn(&b, &n, &f, &j));
    let subset_w_size = c.subset_sum_of(&n, c.rhs_fn(&b, &n, &f, &j));
    // symm B4a : subsetSum_S(w S·setSize) = Σ_i ind(¬J i)·subsetSum_S(ind(S i)·w S).
    let b4a_sym = c.symm_rat(masked_outer_sum.clone(), subset_w_size.clone(), b4a);

    // Qcongr : Fin.sum n (ind(¬J i)·Inf_i) = Fin.sum n (ind(¬J i)·subsetSum_S(ind(S i)·w S))
    //   [Fin.sum_congr n masked_infl masked_outer Q].
    let qpw = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
        let inf = c.influence_of(&n, &f, &i);
        let ss = c.subset_sum_of(&n, c.coord_fn(&d, &n, &f, &i));
        // influence_fourier n f i : Inf_i = subsetSum_S(ind(S i)·w S).
        let infl_eq = Expr::apps(
            c.influence_fourier.clone(),
            [n.clone(), f.clone(), i.clone()],
        );
        // motive : fun (z : Rat) => mask · z.
        let motive = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (z_id, z) = e.fresh_local(c.rat.clone());
            let body = c.mul(mask.clone(), z);
            e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        // Q_i : mask·Inf_i = mask·subsetSum_S(...)  := congr (mask·) infl_eq.
        let body = c.congr_rat(inf, ss, motive, infl_eq);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let masked_infl_sum = c.fin_sum_of(&n, c.masked_infl_fn(&b, &n, &f, &j)); // = RHS
    let qcongr = Expr::apps(
        c.fin_sum_congr.clone(),
        [
            n.clone(),
            c.masked_infl_fn(&b, &n, &f, &j),
            c.masked_outer_fn(&b, &n, &f, &j),
            qpw,
        ],
    );
    // symm Qcongr : Σ_i ind(¬J i)·subsetSum_S(...) = Σ_i ind(¬J i)·Inf_i (= RHS).
    let qcongr_sym = c.symm_rat(masked_infl_sum.clone(), masked_outer_sum.clone(), qcongr);

    // EqR : subsetSum_S(w S·setSize) = RHS   := trans b4a_sym qcongr_sym.
    let eq_r = c.trans_rat(
        subset_w_size.clone(),
        masked_outer_sum.clone(),
        masked_infl_sum.clone(),
        b4a_sym,
        qcongr_sym,
    );

    // ── step3_le : subsetSum_S(ind(mask)·w S) ≤ subsetSum_S(w S·setSize)
    //   [subsetSum_le_of_pointwise n mass_fn rhs_fn per_s].
    let per_s = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let body = c.per_s_bound(&d, &n, &f, &s, &j);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs_mass = c.subset_sum_of(&n, c.mass_fn(&b, &n, &f, &j));
    let step3_le = Expr::apps(
        c.subset_sum_le_of_pointwise.clone(),
        [
            n.clone(),
            c.mass_fn(&b, &n, &f, &j),
            c.rhs_fn(&b, &n, &f, &j),
            per_s,
        ],
    );

    // proof : lhs_mass ≤ RHS
    //   := subst (motive t => lhs_mass ≤ t) subset_w_size RHS EqR step3_le.
    let motive_top = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = e.fresh_local(c.rat.clone());
        let body = c.rat_le(lhs_mass.clone(), t);
        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let proof = c.subst_rat(
        motive_top,
        subset_w_size.clone(),
        masked_infl_sum.clone(),
        eq_r,
        step3_le,
    );

    let e = b.mk_lam(j_id, BinderInfo::Default, hcp, proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Initialize Friedgut RUNG 4. Registers `BoolAnalysis.ind_and`,
    /// `BoolAnalysis.ind_ble_one_le_natCast`, `BoolAnalysis.restrict_double_count`,
    /// and the top theorem `BoolAnalysis.restrictMass_le_outside_influence`.
    /// Idempotent. No axiom added or removed.
    pub fn init_boolean_analysis_friedgut_rung4(&mut self) -> Result<(), EnvError> {
        self.register_ind_and()?;
        self.register_ind_ble_one_le_natcast()?;
        self.register_restrict_double_count()?;
        self.register_restrict_mass_le_outside_influence()?;
        Ok(())
    }

    /// L1: `BoolAnalysis.ind_and : ∀ (a b : Bool), ind (Bool.and a b) = ind a · ind b`.
    pub fn register_ind_and(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.ind_and");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_field_inst()?; // Rat.zero_mul / Rat.one_mul
        self.init_bool()?; // Bool.casesOn, Bool.and
        self.init_boolean_analysis()?; // BoolAnalysis.ind

        let c = Rung4Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ind_and_type(&c),
            value: ind_and_value(&c),
        })
    }

    /// L2: `BoolAnalysis.ind_ble_one_le_natCast :
    ///   ∀ (m : Nat), ind (Nat.ble 1 m) ≤ Rat.mk (Int.ofNat m) 1`.
    pub fn register_ind_ble_one_le_natcast(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.ind_ble_one_le_natCast");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?; // Bool.casesOn
        self.init_nat_cmp()?; // Nat.ble
        self.init_boolean_analysis()?; // BoolAnalysis.ind
        self.register_nat_cast_le_of_ble()?; // Nat.cast_le_of_ble (+ Rat order surface)

        let c = Rung4Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ind_ble_le_type(&c),
            value: ind_ble_le_value(&c),
        })
    }

    /// B4a: `BoolAnalysis.restrict_double_count :
    ///   ∀ (n) (f : BoolFn n) (J : HCPoint n),
    ///     Fin.sum n (fun i => ind(¬J i)·subsetSum_S(ind(S i)·(f̂·f̂)))
    ///       = subsetSum_S((f̂·f̂)·setSize n (D_J S))`.
    /// The J^c-masked Fubini double-count. Kernel-checked, constructive,
    /// empty closure. Idempotent.
    pub fn register_restrict_double_count(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.restrict_double_count");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // BoolFn, HCPoint, ind, FourierCoefficient
        self.register_subset_sum()?; // subsetSum (reducible)
        self.register_set_size()?; // setSize (reducible)
        self.register_fin_sum_swap_theorem()?; // Fin.sum_swap, Fin.sum_congr, Fin.sum_smul
        self.register_fin_sum_mul_theorem()?; // Fin.sum_mul
        self.register_ind_and()?; // BoolAnalysis.ind_and (L1)

        let c = Rung4Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: restrict_double_count_type(&c),
            value: restrict_double_count_value(&c),
        })
    }

    /// TOP: `BoolAnalysis.restrictMass_le_outside_influence :
    ///   ∀ (n) (f : BoolFn n) (J : HCPoint n),
    ///     subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂·f̂))
    ///       ≤ Fin.sum n (fun i => ind(¬J i)·Influence n f i)`.
    /// The clean Friedgut charging bound `Σ_{S⊄J} f̂² ≤ Σ_{i∉J} Inf_i`.
    /// Kernel-checked, constructive, empty closure. Idempotent.
    pub fn register_restrict_mass_le_outside_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.restrictMass_le_outside_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Influence, influence_fourier, notSubsetMask deps
        self.init_boolean_analysis_friedgut_cheap_rungs()?; // notSubsetMask
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_right
        self.register_fourier_sq_nonneg()?; // fourier_sq_nonneg (0 ≤ f̂²)
        self.register_set_size_eq_natcast()?; // setSize_eq_natCast
        self.register_subset_sum_le_of_pointwise()?; // subsetSum monotonicity
        self.register_restrict_double_count()?; // B4a
        self.register_ind_ble_one_le_natcast()?; // L2

        let c = Rung4Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: top_type(&c),
            value: top_value(&c),
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
        env.init_boolean_analysis_friedgut_rung4()
            .expect("init_boolean_analysis_friedgut_rung4");
        env.init_boolean_analysis_friedgut_rung4()
            .expect("idempotent");
        env
    }

    /// Assert `name` is a kernel-checked `Theorem` with an EMPTY admitted-axiom
    /// closure (`ProofQuality::Constructive`).
    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("value present");
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
            "{name} closure must be foundational-only (empty), got {:?}",
            env.axiom_deps(&nm)
        );
    }

    #[test]
    fn test_ind_and_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "BoolAnalysis.ind_and");
    }

    #[test]
    fn test_ind_ble_one_le_natcast_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "BoolAnalysis.ind_ble_one_le_natCast");
    }

    #[test]
    fn test_restrict_double_count_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "BoolAnalysis.restrict_double_count");
    }

    #[test]
    fn test_restrict_mass_le_outside_influence_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "BoolAnalysis.restrictMass_le_outside_influence");
    }

    /// The top theorem's STATEMENT is exactly the charging bound
    /// `Σ_{S⊄J} f̂(S)² ≤ Σ_{i∉J} Inf_i[f]` — an `LE.le @Rat instLERat` whose LHS is
    /// `subsetSum n (fun S => ind (notSubsetMask n S J) · (f̂ S · f̂ S))` and whose
    /// RHS is `Fin.sum n (fun i => ind (Bool.not (J i)) · Influence n f i)`. Guard
    /// against a vacuous/masquerade restatement by re-deriving the type and
    /// matching it structurally, and by asserting the conclusion head is `LE.le`.
    #[test]
    fn test_top_statement_is_the_genuine_charging_bound() {
        let env = env();
        let c = Rung4Consts::new();
        let expected = top_type(&c);
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.restrictMass_le_outside_influence",
            ))
            .expect("registered");
        assert_eq!(
            info.type_, expected,
            "registered type must be the genuine charging bound"
        );
        // peel the three Pi binders (n, f, J), then assert the conclusion head is LE.le.
        let mut ty = &info.type_;
        for _ in 0..3 {
            match ty.kind() {
                crate::expr::ExprKind::Pi(_, _, body) => ty = body,
                other => panic!("expected Pi, got {other:?}"),
            }
        }
        let mut head = ty;
        while let crate::expr::ExprKind::App(g, _) = head.kind() {
            head = g;
        }
        match head.kind() {
            crate::expr::ExprKind::Const(name, _) => assert_eq!(
                name.to_string(),
                "LE.le",
                "conclusion head must be LE.le (a genuine ≤), got {name}"
            ),
            other => panic!("conclusion head must be the LE.le const, got {other:?}"),
        }
    }
}
