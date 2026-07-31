// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **rung 2 mask-collapse** (`mask-collapse`).
//!
//! On a `setSize`-weighted integrand the two band masks coincide: the low-band
//! mask `ind(ble |S| k)` (`|S| ≤ k`, INCLUDING `|S| = 0`) and the punctured-band
//! mask `ind(and (ble 1 |S|) (not (ble (k+1) |S|)))` (`1 ≤ |S| ≤ k`) differ ONLY
//! at `|S| = 0`, where the shared factor `setSize n S = 0` vanishes — so the two
//! masked integrands are pointwise equal. This is the brick that lets rung 2
//! reconcile the double-count bridge's band mask
//! (`lowband_double_count_le`'s RHS) with the level-restriction bridge's low-band
//! mask (`lowband_le_noise_sum`'s `W^{≤k}` integrand) on the degree-weighted band.
//!
//! ## What this proves
//!
//! 1. [`Environment::register_nat_not_ble_succ_eq_ble`] — the Nat-level
//!    complement reflection
//!    ```text
//!    Nat.not_ble_succ_eq_ble : ∀ (k m : Nat),
//!      Bool.not (Nat.ble (Nat.succ k) m) = Nat.ble m k
//!    ```
//!    (`¬(k < m) ↔ m ≤ k`, reflected at the boolean level).
//!
//! 2. [`Environment::register_mask_collapse_term`] — the per-`S` masked-term
//!    identity (generic in the weight `w`, with the `|S|=0 ⟹ w=0` escape):
//!    ```text
//!    BoolAnalysis.mask_collapse_term : ∀ (k m : Nat) (w : Rat),
//!      (Eq Nat m Nat.zero → Eq Rat w Rat.zero) →
//!        Rat.mul (ind (Nat.ble m k)) w
//!          = Rat.mul (ind (Bool.and (Nat.ble 1 m)
//!                                   (Bool.not (Nat.ble (Nat.succ k) m)))) w
//!    ```
//!
//! 3. [`Environment::register_setsize_band_mask_collapse`] — the lifted cube-sum
//!    identity on a `setSize`-weighted integrand `g`:
//!    ```text
//!    BoolAnalysis.setsize_band_mask_collapse : ∀ (n k : Nat) (g : HCPoint n → Rat),
//!      subsetSum n (fun S => ind (Nat.ble (setSizeNat n S) k)
//!                              · (setSize n S · g S))
//!        = subsetSum n (fun S => ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                                              (Bool.not (Nat.ble (Nat.succ k)
//!                                                                 (setSizeNat n S))))
//!                              · (setSize n S · g S))
//!    ```
//!
//! ## Proofs (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! ### `Nat.not_ble_succ_eq_ble` — `Nat.rec` on `m`, motive `P m := ∀ k, …`
//!
//! Using `ble 0 _ ≡ true`, `ble (succ _) 0 ≡ false`, `ble (succ a)(succ b) ≡ ble a b`,
//! `not false ≡ true`, `not true ≡ false`:
//! - `m = 0`: `not (ble (succ k) 0) ≡ not false ≡ true`, `ble 0 k ≡ true`;
//!   `Eq.refl true` (after ι-reduction). `∀ k` by a `k`-lambda.
//! - `m = succ m'`, ih `∀ k, not(ble (succ k) m') = ble m' k`: goal
//!   `∀ k, not(ble (succ k)(succ m')) = ble (succ m') k`; LHS ι-reduces to
//!   `not(ble k m')`. `Nat.casesOn k`:
//!   * `k = 0`: `not(ble 0 m') ≡ not true ≡ false`, `ble (succ m') 0 ≡ false`; `refl`.
//!   * `k = succ k'`: `not(ble (succ k') m')` ; `ble (succ m')(succ k') ≡ ble m' k'`;
//!     close by `ih k'`.
//!
//! ### `mask_collapse_term` — `Nat.casesOn m`, motive carries the hyp → goal
//!
//! - `m = 0`: `ble 0 k ≡ true` so `ind(ble 0 k) ≡ ind true ≡ Rat.one`; the band
//!   `and (ble 1 0) _ ≡ and false _ ≡ false` so `ind(band) ≡ Rat.zero`. With
//!   `hw := hyp Eq.refl : w = 0`, chain `1·w = w` (`one_mul`) `= 0` (`hw`)
//!   `= 0·w` (`symm zero_mul`).
//! - `m = succ m'`: `ble 1 (succ m') ≡ true`, so the band
//!   `and true (not (ble (succ k)(succ m'))) ≡ not(ble (succ k)(succ m'))`, and by
//!   `not_ble_succ_eq_ble k (succ m') : not(ble (succ k)(succ m')) = ble (succ m') k`
//!   the band mask EQUALS the low-band mask `ble (succ m') k`. `congrArg
//!   (fun bit => ind bit · w)` of (the symm of) that, gives the goal directly.
//!
//! ### `setsize_band_mask_collapse` — `subsetSum_congr` over the per-`S` term
//!
//! `subsetSum_congr n LOW BAND per_s` with
//! `per_s S := mask_collapse_term k (setSizeNat n S) (setSize n S · g S) h0`, where
//! `h0 : setSizeNat n S = 0 → setSize n S · g S = 0` is built from
//! `setSize_eq_natCast` (`setSize n S = natCast (setSizeNat n S)`): subst the
//! `|S|=0` hypothesis into it to get `setSize n S = natCast 0 ≡ 0`, then
//! `congrArg (· · g S)` + `zero_mul` ⟹ `setSize n S · g S = 0`.
//!
//! Every leaf (`Nat.rec`/`Nat.casesOn`, `Bool.and`/`Bool.not` ι, `Rat.one_mul`,
//! `Rat.zero_mul`, `setSize_eq_natCast`, `subsetSum_congr`, `congrArg`, `Eq.*`) is
//! `Constructive` with empty admitted-axiom closure, so all three deliverables are
//! too. No axiom is added or removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the mask-collapse bricks. Spellings byte-match the consumed
/// carriers (`Nat.ble`, `Bool.and`/`Bool.not`, `ind`, `setSize`, `setSizeNat`,
/// `subsetSum`, `Rat.mul`).
struct MaskConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    bool_true: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    hcpoint: Expr,
    // levels.
    l1: Level,
    l0: Level,
}

impl MaskConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            bool_true: k("Bool.true"),
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            ind: k("BoolAnalysis.ind"),
            set_size: k("BoolAnalysis.setSize"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            l1,
            l0: Level::zero(),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_one(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `Nat.ble a b`.
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    /// `Nat.ble 1 m`.
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.nat_one(), m)
    }
    /// `Nat.ble (succ k) m`.
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    fn band(&self, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [b, c])
    }
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    /// The punctured-band mask `and (ble 1 m) (not (ble (succ k) m))`.
    fn band_mask(&self, k: &Expr, m: Expr) -> Expr {
        self.band(self.ble1(m.clone()), self.bnot(self.ble_succ_k(k, m)))
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }

    // ── Eq plumbing ───────────────────────────────────────────────────────────
    fn eq_at(&self, lvl: &Level, ty: Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![lvl.clone()]),
            [ty, a, b],
        )
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        self.eq_at(&self.l1, self.rat.clone(), a, b)
    }
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        self.eq_at(&self.l1, self.bool_.clone(), a, b)
    }
    fn eq_nat(&self, a: Expr, b: Expr) -> Expr {
        self.eq_at(&self.l1, self.nat.clone(), a, b)
    }
    fn refl_at(&self, lvl: &Level, ty: Expr, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![lvl.clone()]),
            [ty, a],
        )
    }
    #[cfg(test)]
    fn refl_rat(&self, a: Expr) -> Expr {
        self.refl_at(&self.l1, self.rat.clone(), a)
    }
    fn refl_bool(&self, a: Expr) -> Expr {
        self.refl_at(&self.l1, self.bool_.clone(), a)
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
    /// `@Eq.subst.{1} Nat motive a b h_eq h_a : motive b`.
    #[cfg(test)]
    fn subst_nat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.nat.clone(), motive, a, b, h_eq, h_a],
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
    /// `congrArg (fun (bit : Bool) => ind bit · w) h : ind a · w = ind b · w`.
    fn congr_mask(&self, parent: &EnvDeclBuilder, w: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.bool_.clone());
            let body = self.mul(self.ind_of(z), w.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.bool_.clone(), body))
        };
        self.congr_arg(self.bool_.clone(), self.rat.clone(), a, b, f, h)
    }
    /// `congrArg (fun (z : Rat) => z · g) h : a·g = b·g`.
    fn congr_mul_r(&self, parent: &EnvDeclBuilder, g: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, g.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_arg(self.rat.clone(), self.rat.clone(), a, b, f, h)
    }
}

// ───────────────── Nat.not_ble_succ_eq_ble : not(ble (succ k) m) = ble m k ─────

/// `P m := ∀ k, not (ble (succ k) m) = ble m k`.
fn nbse_motive_body(c: &MaskConsts, m: &Expr, parent: &EnvDeclBuilder) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = d.fresh_local(c.nat.clone());
    let lhs = c.bnot(c.ble_succ_k(&k, m.clone()));
    let rhs = c.ble(m.clone(), k.clone());
    let body = c.eq_bool(lhs, rhs);
    d.finish_child(d.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body))
}

fn nbse_type(c: &MaskConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let lhs = c.bnot(c.ble_succ_k(&k, m.clone()));
    let rhs = c.ble(m.clone(), k.clone());
    let concl = c.eq_bool(lhs, rhs);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), concl);
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e))
}

fn nbse_value(c: &MaskConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    // motive : fun (mm : Nat) => ∀ k, not(ble (succ k) mm) = ble mm k
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (mm_id, mm) = d.fresh_local(c.nat.clone());
        let body = nbse_motive_body(c, &mm, &d);
        d.finish_child(d.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // zero case : ∀ k, not(ble (succ k) 0) = ble 0 k.
    //   not(ble (succ k) 0) ≡ not false ≡ true ; ble 0 k ≡ true ⟹ refl true.
    let zero_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, _k) = d.fresh_local(c.nat.clone());
        let body = c.refl_bool(c.bool_true.clone());
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // succ case : fun (m' : Nat) (ih : P m') => fun (k : Nat) =>
    //   Nat.casesOn k (zero-of-k) (succ-of-k)
    //   goal : not(ble (succ k)(succ m')) = ble (succ m') k.
    let succ_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (mp_id, mp) = d.fresh_local(c.nat.clone());
        let ih_ty = nbse_motive_body(c, &mp, &d);
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());

        // inner k-lambda.
        let k_lambda = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (k_id, k) = e.fresh_local(c.nat.clone());

            // k-motive : fun (kk : Nat) => not(ble (succ kk)(succ m')) = ble (succ m') kk.
            let k_motive = {
                let mut g = EnvDeclBuilder::child_of(&e);
                let (kk_id, kk) = g.fresh_local(c.nat.clone());
                let lhs = c.bnot(c.ble_succ_k(&kk, c.succ(mp.clone())));
                let rhs = c.ble(c.succ(mp.clone()), kk.clone());
                let body = c.eq_bool(lhs, rhs);
                g.finish_child(g.mk_lam(kk_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // k=0 case : not(ble (succ 0)(succ m')) = ble (succ m') 0.
            //   LHS ≡ not(ble 0 m') ≡ not true ≡ false ; RHS ≡ ble (succ m') 0 ≡ false ⟹ refl false.
            let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
            let kzero = c.refl_bool(bfalse);

            // k=succ k' case : fun (k' : Nat) => ih k'.
            //   goal : not(ble (succ (succ k'))(succ m')) = ble (succ m')(succ k').
            //   LHS ι : not(ble (succ k') m') ; RHS ι : ble m' k' ; ih k' : not(ble (succ k') m') = ble m' k'.
            let ksucc = {
                let mut g = EnvDeclBuilder::child_of(&e);
                let (kp_id, kp) = g.fresh_local(c.nat.clone());
                let body = Expr::app(ih.clone(), kp.clone());
                g.finish_child(g.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), body))
            };

            let nat_cases = Expr::const_(Name::from_string("Nat.casesOn"), vec![c.l0.clone()]);
            let body = Expr::apps(nat_cases, [k_motive, k.clone(), kzero, ksucc]);
            e.finish_child(e.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
        };

        let e = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, k_lambda);
        d.finish_child(d.mk_lam(mp_id, BinderInfo::Default, c.nat.clone(), e))
    };

    // value : fun (k m : Nat) => Nat.rec motive zero_case succ_case m k.
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![c.l0.clone()]);
    // Nat.rec motive zero_case succ_case m : P m = (∀ k, …).  Then apply at k.
    let rec = Expr::apps(nat_rec, [motive, zero_case, succ_case, m.clone()]);
    let body = Expr::app(rec, k.clone());
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e))
}

// ─────────────── mask_collapse_term : per-S masked-term identity ───────────────

fn mct_type(c: &MaskConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (w_id, w) = b.fresh_local(c.rat.clone());

    // hyp : Eq Nat m 0 → Eq Rat w 0.
    let hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ante = c.eq_nat(m.clone(), c.nat_zero.clone());
        let (a_id, _a) = d.fresh_local(ante.clone());
        let cons = c.eq_rat(w.clone(), c.rat_zero.clone());
        d.finish_child(d.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };
    let (h_id, _h) = b.fresh_local(hyp.clone());

    let lhs = c.mul(c.ind_of(c.ble(m.clone(), k.clone())), w.clone());
    let rhs = c.mul(c.ind_of(c.band_mask(&k, m.clone())), w.clone());
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e))
}

fn mct_value(c: &MaskConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (w_id, w) = b.fresh_local(c.rat.clone());

    // hyp type (Eq Nat mm 0 → Eq Rat w 0) parametrized in mm — for the motive.
    let hyp_ty_of = |mm: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let ante = c.eq_nat(mm.clone(), c.nat_zero.clone());
        let (a_id, _a) = d.fresh_local(ante.clone());
        let cons = c.eq_rat(w.clone(), c.rat_zero.clone());
        d.finish_child(d.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };
    // goal(mm) := ind(ble mm k)·w = ind(band mm)·w.
    let goal_of = |mm: &Expr| {
        let lhs = c.mul(c.ind_of(c.ble(mm.clone(), k.clone())), w.clone());
        let rhs = c.mul(c.ind_of(c.band_mask(&k, mm.clone())), w.clone());
        c.eq_rat(lhs, rhs)
    };

    // motive : fun (mm : Nat) => (Eq Nat mm 0 → Eq Rat w 0) → goal(mm).
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (mm_id, mm) = d.fresh_local(c.nat.clone());
        let thr = hyp_ty_of(&mm, &d);
        let (h_id, _h) = d.fresh_local(thr.clone());
        let imp = d.mk_pi(h_id, BinderInfo::Default, thr, goal_of(&mm));
        d.finish_child(d.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), imp))
    };

    // zero case : fun (hyp : Eq Nat 0 0 → Eq Rat w 0) =>
    //   goal(0) ≡ ind true · w = ind false · w ≡ Rat.one·w = Rat.zero·w.
    //   hw := hyp (Eq.refl Nat 0) : w = 0.
    //   chain : 1·w = w (one_mul) ; w = 0 (hw) ; 0 = 0·w (symm zero_mul).
    let zero_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let thr0 = hyp_ty_of(&c.nat_zero.clone(), &d);
        let (h_id, h) = d.fresh_local(thr0.clone());

        let refl0 = c.refl_at(&c.l1, c.nat.clone(), c.nat_zero.clone());
        let hw = Expr::app(h.clone(), refl0); // w = 0

        let one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let one_w = c.mul(one, w.clone());
        let zero_w = c.mul(c.rat_zero.clone(), w.clone());
        // one_mul w : 1·w = w.
        let one_mul = Expr::app(
            Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            w.clone(),
        );
        // zero_mul w : 0·w = 0.
        let zero_mul = Expr::app(
            Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
            w.clone(),
        );
        // symm : 0 = 0·w.
        let zero_eq_zw = c.symm_rat(zero_w.clone(), c.rat_zero.clone(), zero_mul);
        // 1·w = w = 0.
        let c1 = c.trans_rat(one_w.clone(), w.clone(), c.rat_zero.clone(), one_mul, hw);
        // 1·w = 0 = 0·w.
        let body = c.trans_rat(one_w, c.rat_zero.clone(), zero_w, c1, zero_eq_zw);
        d.finish_child(d.mk_lam(h_id, BinderInfo::Default, thr0, body))
    };

    // succ case : fun (m' : Nat) (hyp : …) =>
    //   goal(succ m') ≡ ind(ble (succ m') k)·w = ind(and true (not(ble (succ k)(succ m'))))·w.
    //   band ≡ not(ble (succ k)(succ m')) ; complement: not(ble (succ k)(succ m')) = ble (succ m') k.
    //   congr_mask (symm complement) : ind(ble (succ m') k)·w = ind(not(ble (succ k)(succ m')))·w.
    let succ_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (mp_id, mp) = d.fresh_local(c.nat.clone());
        let thr = hyp_ty_of(&c.succ(mp.clone()), &d);
        let (h_id, _h) = d.fresh_local(thr.clone());

        let lo_bit = c.ble(c.succ(mp.clone()), k.clone()); // ble (succ m') k
        let band_bit = c.band_mask(&k, c.succ(mp.clone())); // and (ble 1 (succ m')) (not (ble (succ k)(succ m')))
                                                            // complement k (succ m') : not(ble (succ k)(succ m')) = ble (succ m') k.
        let compl = Expr::apps(
            Expr::const_(Name::from_string("Nat.not_ble_succ_eq_ble"), vec![]),
            [k.clone(), c.succ(mp.clone())],
        );
        let not_bit = c.bnot(c.ble_succ_k(&k, c.succ(mp.clone()))); // not(ble (succ k)(succ m'))
                                                                    // symm : ble (succ m') k = not(ble (succ k)(succ m')).
        let compl_symm = Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![c.l1.clone()]),
            [c.bool_.clone(), not_bit.clone(), lo_bit.clone(), compl],
        );
        // congr_mask : ind(ble (succ m') k)·w = ind(not(...))·w.
        //   the goal RHS `ind(band_bit)·w` is def-eq to `ind(not_bit)·w` (and true X ≡ X),
        //   so the kernel accepts this congr proof against the stated goal.
        let body = c.congr_mask(&d, &w, lo_bit.clone(), not_bit.clone(), compl_symm);
        let _ = band_bit;
        let e = d.mk_lam(h_id, BinderInfo::Default, thr, body);
        d.finish_child(d.mk_lam(mp_id, BinderInfo::Default, c.nat.clone(), e))
    };

    // hyp binder, then Nat.casesOn m motive (apply hyp last).
    let hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ante = c.eq_nat(m.clone(), c.nat_zero.clone());
        let (a_id, _a) = d.fresh_local(ante.clone());
        let cons = c.eq_rat(w.clone(), c.rat_zero.clone());
        d.finish_child(d.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };
    let (h_id, h) = b.fresh_local(hyp.clone());

    let nat_cases = Expr::const_(Name::from_string("Nat.casesOn"), vec![c.l0.clone()]);
    // Nat.casesOn motive m zero_case succ_case : (Eq Nat m 0 → …) → goal(m).
    let rec = Expr::apps(nat_cases, [motive, m.clone(), zero_case, succ_case]);
    let body = Expr::app(rec, h.clone());

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e))
}

// ───────────── setsize_band_mask_collapse : lifted cube-sum identity ───────────

/// `LOW(g) := fun S => ind (ble |S| k) · (setSize n S · g S)`.
fn low_fn(c: &MaskConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, g: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let m = c.set_size_nat_of(n, &s);
    let w = c.mul(c.set_size_of(n, &s), Expr::app(g.clone(), s.clone()));
    let body = c.mul(c.ind_of(c.ble(m, k.clone())), w);
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `BAND(g) := fun S => ind (band |S|) · (setSize n S · g S)`.
fn band_fn(c: &MaskConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, g: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let m = c.set_size_nat_of(n, &s);
    let w = c.mul(c.set_size_of(n, &s), Expr::app(g.clone(), s.clone()));
    let body = c.mul(c.ind_of(c.band_mask(k, m)), w);
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

fn collapse_type(c: &MaskConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());

    let lhs = c.ssum(&n, low_fn(c, &b, &n, &k, &g));
    let rhs = c.ssum(&n, band_fn(c, &b, &n, &k, &g));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn collapse_value(c: &MaskConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());

    let low = low_fn(c, &b, &n, &k, &g);
    let band = band_fn(c, &b, &n, &k, &g);

    // per_s : ∀ S, LOW S = BAND S.
    let per_s = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let m = c.set_size_nat_of(&n, &s);
        let gs = Expr::app(g.clone(), s.clone());
        let size = c.set_size_of(&n, &s);
        let w = c.mul(size.clone(), gs.clone());

        // h0 : Eq Nat (setSizeNat n S) 0 → Eq Rat (setSize n S · g S) 0.
        //   from setSize_eq_natCast: setSize n S = natCast (setSizeNat n S).
        //   subst the |S|=0 hyp into it ⟹ setSize n S = natCast 0 ≡ 0 ; congr (·g) ; zero_mul.
        let h0 = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let ante = c.eq_nat(m.clone(), c.nat_zero.clone());
            let (hz_id, hz) = e.fresh_local(ante.clone());

            // size_eq : setSize n S = natCast (setSizeNat n S).
            let size_eq = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.setSize_eq_natCast"), vec![]),
                [n.clone(), s.clone()],
            );
            // natCast m := mk (ofNat m) 1.
            let natcast = |mm: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Rat.mk"), vec![]),
                    [
                        Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), mm),
                        c.nat_one(),
                    ],
                )
            };
            let cast_m = natcast(m.clone());
            let cast_zero = natcast(c.nat_zero.clone());
            // subst (motive mm => natCast mm = natCast 0) along hz (m = 0) at (natCast m)?
            // We instead transport `setSize = natCast m` into `setSize = natCast 0` by
            // congrArg natCast hz, then trans, then note natCast 0 ≡ Rat.zero (def-eq).
            // step: cast_eq : natCast m = natCast 0   (congrArg natCast hz).
            let natcast_fn = {
                let mut g2 = EnvDeclBuilder::child_of(&e);
                let (mm_id, mm) = g2.fresh_local(c.nat.clone());
                let body = natcast(mm);
                g2.finish_child(g2.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let cast_eq = c.congr_arg(
                c.nat.clone(),
                c.rat.clone(),
                m.clone(),
                c.nat_zero.clone(),
                natcast_fn,
                hz,
            );
            // size_eq_zero : setSize n S = natCast 0   (trans size_eq cast_eq).
            let size_eq_zero = c.trans_rat(
                size.clone(),
                cast_m.clone(),
                cast_zero.clone(),
                size_eq,
                cast_eq,
            );
            // natCast 0 ≡ Rat.zero def-eq; restate endpoint as Rat.zero.
            //   size_eq_z0 : setSize n S = Rat.zero   (cast_zero is def-eq to Rat.zero,
            //   so the kernel accepts size_eq_zero typed against this).
            // congr (·g) : setSize·g = (natCast 0)·g.
            let size_g = c.mul(size.clone(), gs.clone());
            let castzero_g = c.mul(cast_zero.clone(), gs.clone());
            let congr_g = c.congr_mul_r(&e, &gs, size.clone(), cast_zero.clone(), size_eq_zero);
            // zero_mul g : 0·g = 0  (cast_zero ≡ Rat.zero, so (natCast 0)·g ≡ 0·g).
            let zero_mul_g = Expr::app(
                Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
                gs.clone(),
            );
            // (natCast 0)·g = 0 — zero_mul_g is typed `0·g = 0`; def-eq base lets it apply.
            // chain : setSize·g = (natCast 0)·g = 0.
            let body = c.trans_rat(size_g, castzero_g, c.rat_zero.clone(), congr_g, zero_mul_g);
            e.finish_child(e.mk_lam(hz_id, BinderInfo::Default, ante, body))
        };

        // mask_collapse_term k (setSizeNat n S) (setSize n S · g S) h0.
        let term = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.mask_collapse_term"), vec![]),
            [k.clone(), m.clone(), w.clone(), h0],
        );
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, term))
    };

    // subsetSum_congr n LOW BAND per_s.
    let body = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]),
        [n.clone(), low, band, per_s],
    );

    let e = b.mk_lam(g_id, BinderInfo::Default, g_ty, body);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `Nat.not_ble_succ_eq_ble : ∀ (k m : Nat),
    /// `Bool.not (Nat.ble (Nat.succ k) m) = Nat.ble m k`. The boolean-level
    /// complement reflection `¬(k < m) ↔ m ≤ k`. See module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_nat_not_ble_succ_eq_ble(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.not_ble_succ_eq_ble");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?; // Bool.not, Nat.ble

        let c = MaskConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: nbse_type(&c),
            value: nbse_value(&c),
        })
    }

    /// Register `BoolAnalysis.mask_collapse_term` — the per-`S` masked-term
    /// identity `ind(ble m k)·w = ind(band m)·w` under the `m=0 ⟹ w=0` escape.
    /// See module docs. Kernel-checked, `Constructive`, empty admitted-axiom
    /// closure. Idempotent.
    pub fn register_mask_collapse_term(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.mask_collapse_term");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_rat()?; // Rat.one, Rat.one_mul, Rat.zero_mul
        self.init_boolean_analysis()?; // ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_nat_not_ble_succ_eq_ble()?;

        let c = MaskConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: mct_type(&c),
            value: mct_value(&c),
        })
    }

    /// Register `BoolAnalysis.setsize_band_mask_collapse` — the lifted cube-sum
    /// identity: on a `setSize`-weighted integrand the low-band and punctured-band
    /// masks give equal `subsetSum`s. See module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_setsize_band_mask_collapse(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.setsize_band_mask_collapse");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_rat()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;
        self.register_set_size_eq_natcast()?;
        self.register_mask_collapse_term()?;

        let c = MaskConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: collapse_type(&c),
            value: collapse_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "Nat.not_ble_succ_eq_ble",
        "BoolAnalysis.mask_collapse_term",
        "BoolAnalysis.setsize_band_mask_collapse",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_setsize_band_mask_collapse()
            .expect("register_setsize_band_mask_collapse");
        env
    }

    #[test]
    fn test_mask_collapse_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
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
    }

    #[test]
    fn test_mask_collapse_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_setsize_band_mask_collapse().expect("first");
        env.register_setsize_band_mask_collapse()
            .expect("idempotent");
    }
}
