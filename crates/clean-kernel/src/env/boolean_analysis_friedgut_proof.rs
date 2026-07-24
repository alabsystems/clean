// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem — the `friedgut_boolean` Axiom→Theorem proof
//! (the LAST domain axiom; TCB 4→3).
//!
//! `friedgut_boolean : ∀ n f K eps, friedgut_boolean_helper n f K eps`, where the
//! reducible helper (`Environment::friedgut_l2_faithful_body_v2`) δ-unfolds to
//!
//! ```text
//! fun (n f K eps) =>
//!   I[f] ≤ K → 0 ≤ eps →
//!   ∀ (e : Nat),
//!     (2^e·eps ≤ K) ∧ (K ≤ 2^(e+1)·eps) →
//!       ∃ (J : HCPoint n),
//!         (setSizeNat n J ≤ Nat.pow 2 (15·2^e)) ∧
//!         (subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂ S·f̂ S)) ≤ eps)
//! ```
//!
//! The proof Nat-cases on `Nat.ble n B` where `B := Nat.pow 2 (15·2^e)` is the
//! v2 junta-cardinality budget. THIS MODULE BANKS **CASE n ≤ B** — the trivial
//! full-set witness — as a kernel-checked, constructive, empty-closure family of
//! sub-lemmas (`notSubsetMask_full`, `setSizeNat_le_card`,
//! `friedgut_full_mass_zero`).
//!
//! ## CASE n ≤ B (this module)
//!
//! Take `J := (fun (_ : Fin n) => Bool.true)`, the FULL coordinate set. Then:
//!
//! - **SIZE** `setSizeNat n J ≤ B`: `setSizeNat n J ≤ n` always
//!   (`Fin.sumNat_le_card` + `indNat_le_one`, the generic
//!   `setSizeNat_le_card`), and `n ≤ B` is the case hypothesis
//!   (`Nat.le_of_ble_eq_true` of `Nat.ble n B = true`); chain by `Nat.le_trans`.
//! - **MASS** `subsetSum n (mass J) ≤ eps`: for the full `J`, every masked term
//!   vanishes — `notSubsetMask n S J = false` (`notSubsetMask_full`: the
//!   set-difference `S \ J = ∅`, so its popcount is `0`, so `Nat.ble 1 0 ≡ false`),
//!   hence `ind(false)·w ≡ 0·w = 0` and `subsetSum n (mass J) = 0`
//!   (`friedgut_full_mass_zero`); rewrite the goal `0 ≤ eps`, which is the
//!   hypothesis `heps`.
//!
//! Pure carrier reduction + landed constructive bricks. NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural` / `native_decide` / `unsafe` /
//! `Real`. No axiom added or removed by these sub-lemmas. Idempotent. Gated
//! behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms — carrier spellings byte-match the helper's `mass_fn`
/// (`friedgut_l2_faithful_body_v2`), `setSizeNat`, and `notSubsetMask`.
struct ProofConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_ble: Expr,
    fin: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fourier: Expr,
    subset_sum: Expr,
    ind: Expr,
    set_size_nat: Expr,
    not_subset_mask: Expr,
    bool_and: Expr,
    bool_not: Expr,
    l0: Level,
    l1: Level,
}

impl ProofConsts {
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
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_ble: k("Nat.ble"),
            fin: k("Fin"),
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            ind: k("BoolAnalysis.ind"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            l0,
            l1,
        }
    }

    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
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
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn band(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [a, b])
    }
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), a)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_nat_of(&self, n: &Expr, s: Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s])
    }
    fn not_subset_mask_of(&self, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.not_subset_mask.clone(),
            [n.clone(), s.clone(), j.clone()],
        )
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S)·f̂(S)`.
    fn x_sq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let cf = self.fourier_of(n, f, s);
        self.mul(cf.clone(), cf)
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `indNat b = @Bool.rec (fun _ => Nat) 0 1 b` (the inlined Nat indicator, the
    /// summand of `setSizeNat`).
    fn ind_nat_of(&self, bit: Expr) -> Expr {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![self.l1.clone()]);
        let motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        Expr::apps(
            bool_rec,
            [motive, self.nat_zero.clone(), self.one_nat(), bit],
        )
    }
    /// `fun (_ : Fin n) => Bool.true : HCPoint n` — the full coordinate set.
    fn full_point(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = ch.fresh_local(fin_n.clone());
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, self.bool_true.clone()))
    }
    /// `fun (S : HCPoint n) => ind(notSubsetMask n S J)·(f̂ S·f̂ S)` — the helper's
    /// masked-mass integrand (BYTE-IDENTICAL to `friedgut_l2_faithful_body_v2`'s
    /// `mass_fn` and `friedgut_l2_core`'s `full_fn`).
    fn mass_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let r = self.ind_of(self.not_subset_mask_of(n, &s, j));
        let body = self.mul(r, self.x_sq(n, f, &s));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (_ : HCPoint n) => Rat.zero`.
    fn zero_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, _s) = b.fresh_local(hcp.clone());
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, self.rat_zero.clone()))
    }

    fn eq_at(&self, ty: Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [ty, a, b],
        )
    }
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        self.eq_at(self.bool_.clone(), a, b)
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        self.eq_at(self.rat.clone(), a, b)
    }
    fn trans(&self, ty: Expr, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [ty, a, b, cc, h1, h2],
        )
    }
    fn symm(&self, ty: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [ty, a, b, h],
        )
    }
    fn subst(&self, ty: Expr, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [ty, motive, a, b, h_eq, h_a],
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
    fn le_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b])
    }
    fn le_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("LE.le"), vec![self.l0.clone()]),
            [
                self.rat.clone(),
                Expr::const_(Name::from_string("instLERat"), vec![]),
                a,
                b,
            ],
        )
    }
    /// `And P Q`.
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
    }
    /// `And.intro P Q hp hq : And P Q`.
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [p, q, hp, hq],
        )
    }
}

impl Environment {
    /// `BoolAnalysis.setSizeNat_le_card : ∀ (n : Nat) (S : HCPoint n),
    ///   Nat.le (setSizeNat n S) n`.
    ///
    /// The popcount of any cube point is at most the dimension: `setSizeNat n S
    /// ≡ Fin.sumNat n (fun i => indNat (S i))`, each summand `indNat (S i) ≤ 1`
    /// (`indNat_le_one`), so `Fin.sumNat_le_card` gives `≤ n`. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent. No axiom
    /// added/removed.
    pub fn register_set_size_nat_le_card(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.setSizeNat_le_card");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_set_size_nat()?;
        self.register_fin_sum_nat_le_card()?; // Fin.sumNat_le_card
        self.register_ind_nat_le_one()?; // BoolAnalysis.indNat_le_one
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ProofConsts::new();
        let fin_sum_nat_le_card = Expr::const_(Name::from_string("Fin.sumNat_le_card"), vec![]);
        let ind_nat_le_one = Expr::const_(Name::from_string("BoolAnalysis.indNat_le_one"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());

            // setSizeNat n S ≡ Fin.sumNat n (fun i => indNat (S i)).
            let concl = c.le_nat(c.set_size_nat_of(&n, s.clone()), n.clone());

            if !for_value {
                let e = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            // summand : fun (i : Fin n) => indNat (S i).
            let summand = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = e.fresh_local(fin_n.clone());
                let body = c.ind_nat_of(Expr::app(s.clone(), i));
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            // h_each : ∀ (i : Fin n), Nat.le (indNat (S i)) 1
            //   := fun i => indNat_le_one (S i).
            let h_each = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = e.fresh_local(fin_n.clone());
                let body = Expr::app(ind_nat_le_one.clone(), Expr::app(s.clone(), i));
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            // Fin.sumNat_le_card n summand h_each
            //   : Nat.le (Fin.sumNat n summand) n ≡ Nat.le (setSizeNat n S) n.
            let body = Expr::apps(fin_sum_nat_le_card.clone(), [n.clone(), summand, h_each]);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp, body);
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

    /// `BoolAnalysis.notSubsetMask_full : ∀ (n : Nat) (S : HCPoint n),
    ///   Eq Bool (notSubsetMask n S (fun (_ : Fin n) => Bool.true)) Bool.false`.
    ///
    /// For the FULL coordinate set `J := (fun _ => true)`, the set-difference
    /// `S \ J` is empty: every coordinate `Bool.and (S i) (Bool.not true)
    /// = Bool.and (S i) false = Bool.and false (S i) ≡ false` (`Bool.and_comm`,
    /// then the first-argument `false` reduces), so `indNat (…) ≡ 0`,
    /// `setSizeNat n (…) = 0` (`Fin.sumNat_const_zero_of`), and
    /// `notSubsetMask n S J ≡ Nat.ble 1 0 ≡ Bool.false`. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent. No axiom added/removed.
    pub fn register_not_subset_mask_full(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.notSubsetMask_full");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_not_subset_mask()?;
        self.register_set_size_nat()?;
        self.register_fin_sum_nat_const_zero_of()?; // Fin.sumNat_const_zero_of
        self.register_bool_comm_proofs()?; // Bool.and_comm
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ProofConsts::new();
        let bool_and_comm = Expr::const_(Name::from_string("Bool.and_comm"), vec![]);
        let const_zero_of = Expr::const_(Name::from_string("Fin.sumNat_const_zero_of"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());

            let full = c.full_point(&b, &n);
            // notSubsetMask n S full
            //   ≡ Nat.ble 1 (setSizeNat n (fun i => Bool.and (S i) (Bool.not (full i))))
            //   ≡ Nat.ble 1 (setSizeNat n diff), diff i := Bool.and (S i) (Bool.not true).
            let not_mask = c.not_subset_mask_of(&n, &s, &full);
            let concl = c.eq_bool(not_mask.clone(), c.bool_false.clone());

            if !for_value {
                let e = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            // diff : fun (i : Fin n) => Bool.and (S i) (Bool.not (full i)).
            //   This is the setSizeNat summand-arg inside notSubsetMask.
            let diff = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = e.fresh_local(fin_n.clone());
                let s_i = Expr::app(s.clone(), i.clone());
                let full_i = Expr::app(full.clone(), i.clone());
                let body = c.band(s_i, c.bnot(full_i));
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            // ind_nat_diff : fun (i : Fin n) => indNat (diff i).
            //   setSizeNat n diff ≡ Fin.sumNat n ind_nat_diff.
            let ind_nat_diff = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = e.fresh_local(fin_n.clone());
                let body = c.ind_nat_of(Expr::app(diff.clone(), i));
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };

            // pw : ∀ (i : Fin n), Eq Nat (ind_nat_diff i) 0.
            //   ind_nat_diff i ≡ indNat (Bool.and (S i) (Bool.not true))
            //                 ≡ indNat (Bool.and (S i) Bool.false).
            //   Bool.and_comm (S i) false : Bool.and (S i) false = Bool.and false (S i).
            //   congrArg indNat that : indNat (and (S i) false) = indNat (and false (S i)).
            //   RHS ≡ indNat false ≡ 0 (and false x ≡ false reduces). So the eq's RHS
            //   side is def-eq to 0, closing `ind_nat_diff i = 0`.
            let pw = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = e.fresh_local(fin_n.clone());
                let s_i = Expr::app(s.clone(), i.clone());
                let and_sf = c.band(s_i.clone(), c.bool_false.clone()); // and (S i) false
                let and_fs = c.band(c.bool_false.clone(), s_i.clone()); // and false (S i)
                                                                        // comm : and (S i) false = and false (S i).
                let comm = Expr::apps(bool_and_comm.clone(), [s_i.clone(), c.bool_false.clone()]);
                // ind_fn : fun (z : Bool) => indNat z.
                let ind_fn = {
                    let mut g = EnvDeclBuilder::child_of(&e);
                    let (z_id, z) = g.fresh_local(c.bool_.clone());
                    let body = c.ind_nat_of(z);
                    g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.bool_.clone(), body))
                };
                let ind_comm = c.congr_arg(
                    c.bool_.clone(),
                    c.nat.clone(),
                    and_sf.clone(),
                    and_fs.clone(),
                    ind_fn,
                    comm,
                );
                // ind_comm : indNat (and (S i) false) = indNat (and false (S i)).
                //   LHS is def-eq to `ind_nat_diff i` (Bool.not true ≡ false). RHS is
                //   def-eq to 0. So ind_comm has type (def-eq) `ind_nat_diff i = 0`.
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, ind_comm))
            };

            // ssz : Fin.sumNat n ind_nat_diff = 0  (≡ setSizeNat n diff = 0).
            let ssz = Expr::apps(const_zero_of.clone(), [n.clone(), ind_nat_diff.clone(), pw]);
            // notSubsetMask n S full ≡ Nat.ble 1 (setSizeNat n diff)
            //   ≡ Nat.ble 1 (Fin.sumNat n ind_nat_diff).
            // Rewrite the inner sum to 0 via ssz, landing on Nat.ble 1 0 ≡ false.
            //   motive : fun (m : Nat) => Eq Bool (Nat.ble 1 m) Bool.false.
            //   At m := 0, Nat.ble 1 0 ≡ false, so the proof is Eq.refl Bool false.
            let motive = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = e.fresh_local(c.nat.clone());
                let body = c.eq_bool(c.ble(c.one_nat(), m), c.bool_false.clone());
                e.finish_child(e.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // base : Eq Bool (Nat.ble 1 0) false  := Eq.refl Bool false (def-eq).
            let base = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![c.l1.clone()]),
                [c.bool_.clone(), c.bool_false.clone()],
            );
            let sum_diff = c.set_size_nat_of(&n, diff.clone()); // ≡ Fin.sumNat n ind_nat_diff
                                                                // symm : 0 = setSizeNat n diff.
            let ssz_symm = c.symm(c.nat.clone(), sum_diff.clone(), c.nat_zero.clone(), ssz);
            // subst motive (a := 0) (b := setSizeNat n diff) ssz_symm base
            //   : Eq Bool (Nat.ble 1 (setSizeNat n diff)) false ≡ goal.
            let body = c.subst(
                c.nat.clone(),
                motive,
                c.nat_zero.clone(),
                sum_diff,
                ssz_symm,
                base,
            );

            let e = b.mk_lam(s_id, BinderInfo::Default, hcp, body);
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

    /// `BoolAnalysis.friedgut_full_mass_zero : ∀ (n : Nat) (f : BoolFn n),
    ///   Eq Rat
    ///     (subsetSum n (fun S => ind(notSubsetMask n S (fun _ => true))·(f̂ S·f̂ S)))
    ///     Rat.zero`.
    ///
    /// The masked Fourier mass against the FULL junta vanishes: each term has
    /// `ind(false)·w ≡ 0·w = 0` (`notSubsetMask_full` + `Rat.zero_mul`), so the
    /// whole `subsetSum` collapses to `subsetSum n (fun _ => 0) = 0`
    /// (`subsetSum_congr` then `Fin.sum_zero_fn`). Kernel-checked, `Constructive`,
    /// empty closure. Idempotent. No axiom added/removed.
    pub fn register_friedgut_full_mass_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_full_mass_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_rat_field_inst()?; // Rat.zero_mul
        self.init_fin_sum()?; // Fin.sum_zero_fn
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_not_subset_mask()?;
        self.register_not_subset_mask_full()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ProofConsts::new();
        let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
        let not_subset_mask_full =
            Expr::const_(Name::from_string("BoolAnalysis.notSubsetMask_full"), vec![]);
        let subset_sum_congr =
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]);
        let fin_sum_zero_fn = Expr::const_(Name::from_string("Fin.sum_zero_fn"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let two_nat = Expr::app(c.nat_succ.clone(), c.one_nat());

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());

            let full = c.full_point(&b, &n);
            let mass = c.mass_fn(&b, &n, &f, &full);
            let ss_mass = c.ssum(&n, mass.clone());
            let concl = c.eq_rat(ss_mass.clone(), c.rat_zero.clone());

            if !for_value {
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, concl);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            let zero_fn = c.zero_fn(&b, &n);
            let ss_zero = c.ssum(&n, zero_fn.clone());

            // per_s : ∀ (S : HCPoint n), mass S = 0.
            //   mass S ≡ ind(notSubsetMask n S full)·w, w := f̂ S·f̂ S.
            //   step1 : ind(notSubsetMask n S full)·w = ind(false)·w
            //     := congrArg (fun bit => ind bit · w) (notSubsetMask_full n S).
            //   ind(false)·w ≡ 0·w (ind false ≡ 0). zero_mul w : 0·w = 0.
            //   trans step1 (zero_mul w) : mass S = 0.
            let per_s = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = e.fresh_local(hcp.clone());
                let w = c.x_sq(&n, &f, &s);
                let not_mask = c.not_subset_mask_of(&n, &s, &full);
                let lhs = c.mul(c.ind_of(not_mask.clone()), w.clone()); // mass S
                let ind_false_w = c.mul(c.ind_of(c.bool_false.clone()), w.clone()); // ind(false)·w
                                                                                    // nm_eq : notSubsetMask n S full = false.
                let nm_eq = Expr::apps(not_subset_mask_full.clone(), [n.clone(), s.clone()]);
                // f_bit : fun (bit : Bool) => ind bit · w.
                let f_bit = {
                    let mut g = EnvDeclBuilder::child_of(&e);
                    let (z_id, z) = g.fresh_local(c.bool_.clone());
                    let body = c.mul(c.ind_of(z), w.clone());
                    g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.bool_.clone(), body))
                };
                let step1 = c.congr_arg(
                    c.bool_.clone(),
                    c.rat.clone(),
                    not_mask.clone(),
                    c.bool_false.clone(),
                    f_bit,
                    nm_eq,
                );
                // step2 : ind(false)·w = 0. ind false ≡ 0, so ind(false)·w ≡ 0·w;
                //   Rat.zero_mul w : 0·w = 0 (typed at the 0·w spelling, def-eq).
                let step2 = Expr::app(zero_mul.clone(), w.clone());
                let body = c.trans(
                    c.rat.clone(),
                    lhs,
                    ind_false_w,
                    c.rat_zero.clone(),
                    step1,
                    step2,
                );
                e.finish_child(e.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };

            // step_congr : subsetSum n mass = subsetSum n (fun _ => 0).
            let step_congr = Expr::apps(
                subset_sum_congr.clone(),
                [n.clone(), mass.clone(), zero_fn.clone(), per_s],
            );
            // step_zero : subsetSum n (fun _ => 0) = 0.
            //   subsetSum n (fun _ => 0) ≡ Fin.sum (2^n) (fun _ => 0) (def-unfold +
            //   β at the discarded hcDecode), so Fin.sum_zero_fn (2^n) closes it.
            let pow2n = Expr::apps(nat_pow.clone(), [two_nat.clone(), n.clone()]);
            let step_zero = Expr::app(fin_sum_zero_fn.clone(), pow2n);
            // chain : subsetSum n mass = 0.
            let body = c.trans(
                c.rat.clone(),
                ss_mass,
                ss_zero,
                c.rat_zero.clone(),
                step_congr,
                step_zero,
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

    /// `BoolAnalysis.friedgut_boolean_case_le : ∀ (n : Nat) (f : BoolFn n)
    ///   (eps : Rat) (B : Nat),
    ///     Nat.le n B →                       -- the n ≤ B case hypothesis
    ///     Rat.le Rat.zero eps →              -- 0 ≤ eps
    ///       Exists (fun (J : HCPoint n) =>
    ///         And (Nat.le (setSizeNat n J) B)
    ///             (Rat.le (subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂ S·f̂ S)))
    ///                     eps))`.
    ///
    /// The **fully assembled `n ≤ B` branch** of `friedgut_boolean` (the case
    /// where the v2 junta budget `B := 2^(15·2^e)` already covers all `n`
    /// coordinates). The witness is the FULL coordinate set
    /// `J := (fun _ => Bool.true)`:
    ///
    /// - SIZE `setSizeNat n J ≤ B`: `Nat.le_trans` of `setSizeNat n J ≤ n`
    ///   (`setSizeNat_le_card`) and `n ≤ B` (the case hypothesis).
    /// - MASS `subsetSum n (mass J) ≤ eps`: `friedgut_full_mass_zero` gives
    ///   `subsetSum n (mass J) = 0`, which `Eq.subst` transports `0 ≤ eps` (the
    ///   hypothesis) back to the masked sum.
    ///
    /// The existential's predicate is BYTE-IDENTICAL to the helper's
    /// (`friedgut_l2_faithful_body_v2`), so this lemma slots directly into the
    /// `Bool.casesOn (Nat.ble n B)` of the full `friedgut_boolean` proof.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    /// No axiom added or removed.
    pub fn register_friedgut_boolean_case_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_boolean_case_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_boolean_analysis_order_toolkit()?; // LE.le/instLERat surface
        self.register_set_size_nat()?;
        self.register_not_subset_mask()?;
        self.register_subset_sum()?;
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.register_set_size_nat_le_card()?;
        self.register_not_subset_mask_full()?;
        self.register_friedgut_full_mass_zero()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ProofConsts::new();
        let u1 = c.l1.clone();
        let set_size_nat_le_card =
            Expr::const_(Name::from_string("BoolAnalysis.setSizeNat_le_card"), vec![]);
        let full_mass_zero = Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_full_mass_zero"),
            vec![],
        );
        let nat_le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
        let exists_intro = Expr::const_(Name::from_string("Exists.intro"), vec![u1.clone()]);
        let exists_c = Expr::const_(Name::from_string("Exists"), vec![u1.clone()]);

        // Shared existential predicate builder (byte-matches the helper):
        //   fun (J : HCPoint n) => And (Nat.le (setSizeNat n J) B)
        //                              (Rat.le (subsetSum n (mass J)) eps).
        let pred_of = |b: &EnvDeclBuilder, n: &Expr, f: &Expr, eps: &Expr, big_b: &Expr| -> Expr {
            let mut g = EnvDeclBuilder::child_of(b);
            let hcp = c.hcpoint_of(n);
            let (j_id, j) = g.fresh_local(hcp.clone());
            let size_concl = c.le_nat(c.set_size_nat_of(n, j.clone()), big_b.clone());
            let mass = c.mass_fn(&g, n, f, &j);
            let mass_concl = c.le_rat(c.ssum(n, mass), eps.clone());
            let and = c.and(size_concl, mass_concl);
            g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcp, and))
        };

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (bb_id, big_b) = b.fresh_local(c.nat.clone());

            let hn_ty = c.le_nat(n.clone(), big_b.clone()); // n ≤ B
            let heps_ty = c.le_rat(c.rat_zero.clone(), eps.clone()); // 0 ≤ eps

            let hcp = c.hcpoint_of(&n);
            let pred = pred_of(&b, &n, &f, &eps, &big_b);
            let exists_goal = Expr::apps(exists_c.clone(), [hcp.clone(), pred.clone()]);

            let (hn_id, hn) = b.fresh_local(hn_ty.clone());
            let (heps_id, heps) = b.fresh_local(heps_ty.clone());

            if !for_value {
                let e = b.mk_pi(heps_id, BinderInfo::Default, heps_ty.clone(), exists_goal);
                let e = b.mk_pi(hn_id, BinderInfo::Default, hn_ty.clone(), e);
                let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
                let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            // full := fun (_ : Fin n) => Bool.true : HCPoint n.
            let full = c.full_point(&b, &n);

            // SIZE : Nat.le (setSizeNat n full) B.
            //   size_le_n : setSizeNat n full ≤ n := setSizeNat_le_card n full.
            //   Nat.le_trans (setSizeNat n full) n B size_le_n hn : ≤ B.
            let size_full = c.set_size_nat_of(&n, full.clone());
            let size_le_n = Expr::apps(set_size_nat_le_card.clone(), [n.clone(), full.clone()]);
            let size_proof = Expr::apps(
                nat_le_trans.clone(),
                [size_full.clone(), n.clone(), big_b.clone(), size_le_n, hn],
            );

            // MASS : Rat.le (subsetSum n (mass full)) eps.
            //   mz : subsetSum n (mass full) = 0 := friedgut_full_mass_zero n f.
            //   motive : fun (t : Rat) => Rat.le t eps.
            //   symm mz : 0 = subsetSum n (mass full).
            //   subst motive (a := 0) (b := subsetSum n (mass full)) (symm mz) heps
            //     : Rat.le (subsetSum n (mass full)) eps.
            let mass = c.mass_fn(&b, &n, &f, &full);
            let ss_mass = c.ssum(&n, mass.clone());
            let mz = Expr::apps(full_mass_zero.clone(), [n.clone(), f.clone()]);
            let motive = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = e.fresh_local(c.rat.clone());
                let body = c.le_rat(t, eps.clone());
                e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let mz_symm = c.symm(c.rat.clone(), ss_mass.clone(), c.rat_zero.clone(), mz);
            let mass_proof = c.subst(
                c.rat.clone(),
                motive,
                c.rat_zero.clone(),
                ss_mass.clone(),
                mz_symm,
                heps,
            );

            // And.intro size_concl mass_concl size_proof mass_proof.
            let size_concl = c.le_nat(size_full, big_b.clone());
            let mass_concl = c.le_rat(ss_mass, eps.clone());
            let and_proof = c.and_intro(size_concl, mass_concl, size_proof, mass_proof);

            // Exists.intro (HCPoint n) pred full and_proof.
            let intro = Expr::apps(
                exists_intro.clone(),
                [hcp.clone(), pred.clone(), full, and_proof],
            );

            let e = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, intro);
            let e = b.mk_lam(hn_id, BinderInfo::Default, hn_ty, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
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

    /// Register the Case-1 (`n ≤ B`) Friedgut sub-lemmas and the assembled
    /// `n ≤ B` existential branch. Idempotent. No axiom added or removed.
    pub fn init_boolean_analysis_friedgut_proof(&mut self) -> Result<(), EnvError> {
        self.register_set_size_nat_le_card()?;
        self.register_not_subset_mask_full()?;
        self.register_friedgut_full_mass_zero()?;
        self.register_friedgut_boolean_case_le()?;
        Ok(())
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
    fn test_set_size_nat_le_card_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_set_size_nat_le_card()
            .expect("register_set_size_nat_le_card");
        env.register_set_size_nat_le_card().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.setSizeNat_le_card");
    }

    #[test]
    fn test_not_subset_mask_full_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_not_subset_mask_full()
            .expect("register_not_subset_mask_full");
        env.register_not_subset_mask_full().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.notSubsetMask_full");
    }

    #[test]
    fn test_friedgut_full_mass_zero_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_full_mass_zero()
            .expect("register_friedgut_full_mass_zero");
        env.register_friedgut_full_mass_zero().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_full_mass_zero");
    }

    #[test]
    fn test_friedgut_boolean_case_le_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_boolean_case_le()
            .expect("register_friedgut_boolean_case_le");
        env.register_friedgut_boolean_case_le().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_boolean_case_le");
    }
}
