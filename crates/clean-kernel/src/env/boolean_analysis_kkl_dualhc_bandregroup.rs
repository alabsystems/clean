// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC connect — H1 STEP 2c: the per-`S` BAND REGROUP, lifted to a
//! `subsetSum`-level identity.
//!
//! ## What this proves
//!
//! After RUNG A (`subsetSum_low_band_extract`) at `b = 1/9` and the mask swap
//! (`subsetSum_mask_ble_eq_not_ble`), the low-band-extracted per-`S` integrand is
//! `ind (not (ble (k+1) |S|)) · w S`, with the dual-HC feedstock weight
//! `w S = (4 · ind (S i)) · (f̂(S) · f̂(S))` (the `dualhc_W_eq_band_form` `w`). The
//! assembly's `h_dual` term (`kkl_lowband_mass_of_dual_hc` ∘ RUNG B
//! `coord_w_band_fn`) instead spells the SAME band integrand as
//! `ind (S i) · (ind (not (ble (k+1) |S|)) · (4 · (f̂(S) · f̂(S))))`. This module
//! supplies the `subsetSum`-lifted regroup that reconciles the two spellings:
//!
//! ```text
//! BoolAnalysis.dualhc_band_regroup :
//!   ∀ (n k : Nat) (f : BoolFn n) (i : Fin n),
//!     @Eq Rat
//!       (subsetSum n (fun S =>
//!          Rat.mul (ind (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!                  (Rat.mul (Rat.mul 4 (ind (S i)))
//!                           (FourierCoefficient n f S · FourierCoefficient n f S))))
//!       (subsetSum n (fun S =>
//!          Rat.mul (ind (S i))
//!                  (Rat.mul (ind (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!                           (Rat.mul 4
//!                                    (FourierCoefficient n f S
//!                                     · FourierCoefficient n f S)))))
//! ```
//!
//! The RHS integrand is byte-for-byte `RungBConsts::coord_w_band_fn` (the
//! `kkl_derivative_lowband_link` / `kkl_lowband_mass_of_dual_hc` `sum_w_band`
//! summand). `4 := Rat.mk (Int.ofNat 4) 1` (byte-identical to RUNG B's `four`).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Per `S`, with atoms `a := m2 := ind (not (ble (k+1) |S|))`, `b := 4`,
//! `c := ii := ind (S i)`, `d := fsq := f̂·f̂`, the goal is `a·((b·c)·d) =
//! c·(a·(b·d))`. Both sides collapse to the normal form `N := (c·a)·(b·d)`:
//!
//! ```text
//! LHS = a·((b·c)·d)
//!     = a·(b·(c·d))        [congr (a·) (mul_assoc b c d)]
//!     = (a·b)·(c·d)        [symm (mul_assoc a b (c·d))]
//!     = (a·c)·(b·d)        [mul_mul_mul_comm a b c d]
//!     = (c·a)·(b·d) = N    [congr (·(b·d)) (mul_comm a c)]
//! N   = (c·a)·(b·d)
//!     = c·(a·(b·d)) = RHS  [mul_assoc c a (b·d)]
//! ```
//!
//! lifted across `subsetSum` by `subsetSum_congr`. Every leaf (`Rat.mul_assoc`,
//! `Rat.mul_comm`, `Rat.mul_mul_mul_comm`, `subsetSum_congr`,
//! `Eq.refl/symm/trans/congrArg`) is a landed `Constructive` Theorem with empty
//! closure, so this is too. NO axiom is added or removed. NOT wired into the
//! always-on `init_boolean_analysis` aggregate (reachable via
//! `register_dualhc_band_regroup`). Idempotent.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the per-`S` band regroup. All `ind` / `Nat.ble` /
/// `setSizeNat` / `FourierCoefficient` / `4` spellings are byte-for-byte the
/// landed `RungBConsts` / `AssemblyConsts` conventions so the lifted identity is
/// def-eq to the assembly's `sum_w_band` summand and the band-form `w`.
struct BandRegroupConsts {
    nat: Expr,
    rat: Expr,
    bool_fn: Expr,
    fin: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_ble: Expr,
    bool_not: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    ind: Expr,
    fourier: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    rat_mmmc: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl BandRegroupConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_ble: k("Nat.ble"),
            bool_not: k("Bool.not"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            ind: k("BoolAnalysis.ind"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mmmc: k("Rat.mul_mul_mul_comm"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    /// `four := Rat.mk (Int.ofNat 4) 1` — byte-identical to `RungBConsts::four`.
    fn four(&self) -> Expr {
        let four_nat = self.succ(self.succ(self.succ(self.succ(self.nat_zero.clone()))));
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), four_nat), self.one_nat()],
        )
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
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn ssum_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn congr(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mmmc.clone(), [a, b, cc, d])
    }
    fn mul_left_motive(&self, parent: &EnvDeclBuilder, left: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(left.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    fn mul_right_motive(&self, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(z, right.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }

    /// `m2 S := ind (not (ble (k+1) |S|))`.
    fn m2(&self, n: &Expr, k: &Expr, s: &Expr) -> Expr {
        let ss = self.set_size_nat_of(n, s);
        self.ind_of(self.bnot(self.ble(self.succ(k.clone()), ss)))
    }

    /// LHS integrand `fun S => m2 · ((4·ind(S i))·fsq)` — the RUNG-A + mask-swap
    /// output with `w S = (4·ind(S i))·(f̂·f̂)`.
    fn lhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let m2 = self.m2(n, k, &s);
        let ii = self.ind_of(Expr::app(s.clone(), i.clone()));
        let four_ii = self.mul(self.four(), ii);
        let fsq = self.fsq(n, f, &s);
        let w = self.mul(four_ii, fsq); // (4·ind(S i))·fsq
        let body = self.mul(m2, w);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// RHS integrand `fun S => ind(S i)·(m2·(4·fsq))` — byte-for-byte
    /// `RungBConsts::coord_w_band_fn`.
    fn rhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ii = self.ind_of(Expr::app(s.clone(), i.clone()));
        let m2 = self.m2(n, k, &s);
        let fsq = self.fsq(n, f, &s);
        let four_fsq = self.mul(self.four(), fsq);
        let w_band = self.mul(m2, four_fsq); // m2·(4·fsq)
        let body = self.mul(ii, w_band);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// `BoolAnalysis.nine_third_third_eq_one :
    ///   @Eq Rat (Rat.mul nine (Rat.mul third third)) Rat.one`,
    /// with `nine := Rat.mk (Int.ofNat 9) 1`, `third := Rat.mk (Int.ofNat 1) 3`.
    ///
    /// The dual-HC `9·(1/9) = 1` clear-out constant (the `b = 1/9`, base `= 9`
    /// reciprocal). The live `Rat` is a QUOTIENT carrier whose `Rat.mul` reduces
    /// reps WITHOUT gcd-reduction (`9·((1/3)·(1/3))` lands on the non-canonical
    /// rep `9/9`, NOT `1/1`), so this is NOT `Eq.refl`-closable. It is closed by
    /// `Rat.le_antisymm` of the two concrete `Rat.ble` directions: both
    /// `Rat.ble (9·(third·third)) 1` and `Rat.ble 1 (9·(third·third))`
    /// native-reduce to `true` (the raw `ble` compares the cross-products
    /// `9·1 ≤ 1·9` and `1·9 ≤ 9·1`, both `9 ≤ 9`), so each side is
    /// `Rat.le_of_ble_eq_true … (Eq.refl Bool.true)`. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_nine_third_third_eq_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.nine_third_third_eq_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.register_rat_order_proofs()?; // Rat.le_of_ble_eq_true surface
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true
        self.rat_quotient_payoff_into_live()?; // Rat.le_antisymm (quotient theorem)
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BandRegroupConsts::new();

        let rat = c.rat.clone();
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        // nine := Rat.mk (Int.ofNat 9) 1
        let nine = {
            let mut nine_nat = c.nat_zero.clone();
            for _ in 0..9 {
                nine_nat = c.succ(nine_nat);
            }
            Expr::apps(
                c.rat_mk.clone(),
                [Expr::app(c.int_of_nat.clone(), nine_nat), c.one_nat()],
            )
        };
        // third := Rat.mk (Int.ofNat 1) 3
        let third = {
            let three_nat = c.succ(c.succ(c.one_nat()));
            Expr::apps(
                c.rat_mk.clone(),
                [Expr::app(c.int_of_nat.clone(), c.one_nat()), three_nat],
            )
        };
        let prod = c.mul(nine.clone(), c.mul(third.clone(), third.clone()));
        let ty = c.eq_rat(prod.clone(), rat_one.clone());

        // h_le : prod ≤ 1 ; h_ge : 1 ≤ prod  via Rat.le_of_ble_eq_true.
        let le_of_ble = Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let refl_true = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [bool_c, btrue],
        );
        let h_le = Expr::apps(
            le_of_ble.clone(),
            [prod.clone(), rat_one.clone(), refl_true.clone()],
        );
        let h_ge = Expr::apps(
            le_of_ble.clone(),
            [rat_one.clone(), prod.clone(), refl_true],
        );
        // Rat.le_antisymm prod 1 h_le h_ge : prod = 1
        let value = Expr::apps(
            Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]),
            [prod, rat_one, h_le, h_ge],
        );
        let _ = rat;

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.dualhc_band_regroup` — see the module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_band_regroup(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_band_regroup");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // ind, FourierCoefficient
        self.init_nat()?;
        self.init_bool()?;
        self.init_nat_cmp()?; // Nat.ble
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_set_size_nat()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BandRegroupConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_band_regroup(&c, false),
            value: build_band_regroup(&c, true),
        })
    }
}

fn build_band_regroup(c: &BandRegroupConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs_fn = c.lhs_fn(&b, &n, &k, &f, &i);
    let rhs_fn = c.rhs_fn(&b, &n, &k, &f, &i);
    let lhs = c.ssum(&n, lhs_fn.clone());
    let rhs = c.ssum(&n, rhs_fn.clone());
    let concl = c.eq_rat(lhs.clone(), rhs.clone());

    let tail = if for_value {
        // pointwise : ∀ S, a·((b·c)·d) = c·(a·(b·d))
        //   a=m2, b=4, c=ii, d=fsq ; normal form N := (c·a)·(b·d).
        let pointwise = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());

            let a = c.m2(&n, &k, &s); // m2
            let bb = c.four(); // 4
            let cc = c.ind_of(Expr::app(s.clone(), i.clone())); // ii
            let dd = c.fsq(&n, &f, &s); // fsq

            // endpoints
            let bc = c.mul(bb.clone(), cc.clone()); // b·c
            let cd = c.mul(cc.clone(), dd.clone()); // c·d
            let bd = c.mul(bb.clone(), dd.clone()); // b·d
            let lhs_s = c.mul(a.clone(), c.mul(bc.clone(), dd.clone())); // a·((b·c)·d)
            let a_bcd = c.mul(a.clone(), c.mul(bb.clone(), cd.clone())); // a·(b·(c·d))
            let ab = c.mul(a.clone(), bb.clone()); // a·b
            let ab_cd = c.mul(ab.clone(), cd.clone()); // (a·b)·(c·d)
            let ac = c.mul(a.clone(), cc.clone()); // a·c
            let ac_bd = c.mul(ac.clone(), bd.clone()); // (a·c)·(b·d)
            let ca = c.mul(cc.clone(), a.clone()); // c·a
            let norm = c.mul(ca.clone(), bd.clone()); // (c·a)·(b·d)  = N
            let a_bd = c.mul(a.clone(), bd.clone()); // a·(b·d)
            let rhs_s = c.mul(cc.clone(), a_bd.clone()); // c·(a·(b·d))

            // step1 : a·((b·c)·d) = a·(b·(c·d))   [congr (a·) (mul_assoc b c d)]
            let assoc_bcd = c.mul_assoc(bb.clone(), cc.clone(), dd.clone()); // (b·c)·d = b·(c·d)
            let step1 = {
                let mot = c.mul_left_motive(&d, &a);
                c.congr(
                    c.mul(bc.clone(), dd.clone()),
                    c.mul(bb.clone(), cd.clone()),
                    mot,
                    assoc_bcd,
                )
            };
            // step2 : a·(b·(c·d)) = (a·b)·(c·d)   [symm (mul_assoc a b (c·d))]
            let assoc_abcd = c.mul_assoc(a.clone(), bb.clone(), cd.clone()); // (a·b)·(c·d) = a·(b·(c·d))
            let step2 = c.symm(ab_cd.clone(), a_bcd.clone(), assoc_abcd);
            // step3 : (a·b)·(c·d) = (a·c)·(b·d)   [mmmc a b c d]
            let step3 = c.mmmc(a.clone(), bb.clone(), cc.clone(), dd.clone());
            // step4 : (a·c)·(b·d) = (c·a)·(b·d)   [congr (·(b·d)) (mul_comm a c)]
            let mc = c.mul_comm(a.clone(), cc.clone()); // a·c = c·a
            let step4 = {
                let mot = c.mul_right_motive(&d, &bd);
                c.congr(ac.clone(), ca.clone(), mot, mc)
            };
            // step5 : (c·a)·(b·d) = c·(a·(b·d))   [mul_assoc c a (b·d)]
            let step5 = c.mul_assoc(cc.clone(), a.clone(), bd.clone());

            // chain LHS → a_bcd → ab_cd → ac_bd → norm → rhs_s
            let t1 = c.trans(lhs_s.clone(), a_bcd.clone(), ab_cd.clone(), step1, step2);
            let t2 = c.trans(lhs_s.clone(), ab_cd.clone(), ac_bd.clone(), t1, step3);
            let t3 = c.trans(lhs_s.clone(), ac_bd.clone(), norm.clone(), t2, step4);
            let body = c.trans(lhs_s.clone(), norm.clone(), rhs_s.clone(), t3, step5);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        c.ssum_congr(&n, &lhs_fn, &rhs_fn, pointwise)
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, i_id, c.fin_of(&n), tail);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_dualhc_band_regroup()
            .expect("register_dualhc_band_regroup");
        env.register_dualhc_band_regroup().expect("idempotent");
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
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_dualhc_band_regroup_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.dualhc_band_regroup");
    }

    #[test]
    fn test_nine_third_third_eq_one_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_nine_third_third_eq_one()
            .expect("register_nine_third_third_eq_one");
        env.register_nine_third_third_eq_one().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.nine_third_third_eq_one");
    }
}
