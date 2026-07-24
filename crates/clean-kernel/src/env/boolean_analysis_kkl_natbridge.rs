// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K2b Nat-bridge: instantiate the abstract threshold lift at
//! the real popcount.
//!
//! The K2b threshold lift (`boolean_analysis_kkl_k2b.rs`) proves the tail bound
//! with an *abstract* indicator `b : HCPoint n → Bool` and an abstract
//! threshold-correctness hypothesis `∀ S, b S = true → k ≤ setSize n S`. KKL
//! assembly instantiates `b S := Nat.ble kNat (setSizeNat n S)` at the genuine
//! Nat-valued popcount. This module supplies the Nat↔Rat bridges that discharge
//! that hypothesis constructively (empty domain-axiom closure):
//!
//! ```text
//! BoolAnalysis.setSizeNat (n : Nat) (S : HCPoint n) : Nat                 -- (a)
//!   := Fin.sumNat n (fun i => indNat (S i))
//!
//! BoolAnalysis.setSize_eq_natCast :                                       -- (b)
//!   ∀ (n) (S), setSize n S = Rat.mk (Int.ofNat (setSizeNat n S)) 1
//!
//! Nat.cast_le_of_ble :                                                    -- (c)
//!   ∀ (k m : Nat), Nat.ble k m = true
//!     → Rat.mk (Int.ofNat k) 1 ≤ Rat.mk (Int.ofNat m) 1
//!
//! BoolAnalysis.subsetSum_threshold_le_nat :                               -- (d)
//!   ∀ (n) (kNat : Nat) (w : HCPoint n → Rat),
//!     (∀ S, 0 ≤ w S) → (∀ S, 0 ≤ setSize n S)
//!       → Rat.mk (Int.ofNat kNat) 1
//!           · subsetSum n (fun S => ind (Nat.ble kNat (setSizeNat n S)) · w S)
//!         ≤ subsetSum n (fun S => setSize n S · w S)
//! ```
//!
//! ## (b) the cast equality — fold alignment
//!
//! `setSize` folds the *Rat* indicator `ind (S i)` over `Fin.sum`; `setSizeNat`
//! folds the *Nat* indicator `indNat (S i)` over `Fin.sumNat`. Both folds share
//! the identical `Nat.rec` shape (`Fin.sumNat`'s defining equations mirror
//! `Fin.sum`'s, peeling via `Fin.castSucc`/`Fin.last`). The bridge is proven in
//! two constructive steps that mirror `Fin.sum_const_one`:
//!
//! 1. `Rat.add_natCast a b : Rat.mk (ofNat (a+b)) 1
//!       = Rat.add (Rat.mk (ofNat a) 1) (Rat.mk (ofNat b) 1)` — the Rat-level
//!    natCast-additivity (one `Quot.sound`; the same Raw mechanics as
//!    `Rat.add_natCast_one`, generalized from `+1` to `+b`).
//! 2. `Fin.sum_natCast n g : Fin.sum n (fun i => Rat.mk (ofNat (g i)) 1)
//!       = Rat.mk (ofNat (Fin.sumNat n g)) 1` — `Nat.rec` over `n`; base by
//!    `refl` (both sides ≡ `mk (ofNat 0) 1`), step peels `Fin.sum_succ`/the
//!    `Fin.sumNat` ι-reduction and closes with `Rat.add_natCast`.
//!
//! `setSize_eq_natCast` then folds the per-coordinate `ind b = mk (ofNat (indNat b)) 1`
//! (`Bool.rec`) through `Fin.sum_congr` and chains `Fin.sum_natCast` at
//! `g := fun i => indNat (S i)`.
//!
//! ## (c) the order bridge
//!
//! `Nat.le_of_ble_eq_true` (constructive, `algebra_nat_ble_le_proof.rs`) turns
//! `Nat.ble k m = true` into `Nat.le k m`. `Int.ofNat_le_ofNat_of_le` lifts that
//! to `Int.le (ofNat k) (ofNat m)` by `Nat.le.rec` (base: `NonNeg (ofNat 0)`
//! after `Int.sub_self`; step: shift the `NonNeg` witness by one). The Rat
//! conclusion `Rat.mk (ofNat k) 1 ≤ Rat.mk (ofNat m) 1` is *definitionally*
//! `Int.le (ofNat k · ofNat 1) (ofNat m · ofNat 1)`; `Int.mul_one` (twice)
//! collapses both products, so the lifted `Int.le` inhabits it after two
//! `Eq.subst` transports.
//!
//! ## (d) the instantiated tail bound
//!
//! `subsetSum_threshold_le` at `k := Rat.mk (ofNat kNat) 1`,
//! `b := fun S => Nat.ble kNat (setSizeNat n S)`, discharging `hyp3` with the
//! composite `fun S h => (b)+(c)`: from `Nat.ble kNat (setSizeNat n S) = true`,
//! `(c)` gives `mk (ofNat kNat) 1 ≤ mk (ofNat (setSizeNat n S)) 1`, and `(b)`
//! rewrites the RHS to `setSize n S`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the Nat-bridge construction.
struct NatBridgeConsts {
    nat: Expr,
    int: Expr,
    rat: Expr,
    bool_: Expr,
    fin: Expr,
    // Eq.{1} toolkit.
    eq1: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    // Rat / Quot machinery.
    rat_mk: Expr,
    rat_add: Expr,
    rat_one: Expr,
    fin_sum: Expr,
    fin_sum_nat: Expr,
    fin_sum_congr: Expr,
    fin_sum_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    rat_add_natcast: Expr,
    raw: Expr,
    raw_mk: Expr,
    raw_equiv: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    // Int.
    int_of_nat: Expr,
    int_mul: Expr,
    int_add: Expr,
    int_mul_one: Expr,
    // Nat.
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_rec: Expr,
    // Int / Nat order toolkit (for the (c) ble-order bridge).
    int_le: Expr,
    int_le_refl: Expr,
    int_le_trans: Expr,
    int_le_self_add_one: Expr,
    nat_le: Expr,
    nat_le_rec: Expr,
    nat_le_of_ble: Expr,
    nat_ble: Expr,
    bool_true: Expr,
    eq_bool: Expr,
    // BoolAnalysis carriers.
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    bool_rec: Expr,
    bool_rec0: Expr,
    hcpoint: Expr,
}

impl NatBridgeConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            int: Expr::const_(Name::from_string("Int"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_nat: Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            fin_sum_succ: Expr::const_(Name::from_string("Fin.sum_succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            rat_add_natcast: Expr::const_(Name::from_string("Rat.add_natCast"), vec![]),
            raw: Expr::const_(Name::from_string("Rat.Raw"), vec![]),
            raw_mk: Expr::const_(Name::from_string("Rat.Raw.mk"), vec![]),
            raw_equiv: Expr::const_(Name::from_string("Rat.Raw.Equiv"), vec![]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_mul_one: Expr::const_(Name::from_string("Int.mul_one"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_le_refl: Expr::const_(Name::from_string("Int.le_refl"), vec![]),
            int_le_trans: Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            int_le_self_add_one: Expr::const_(Name::from_string("Int.le_self_add_one"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            nat_le_of_ble: Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]),
            nat_ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size: Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            bool_rec: Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            bool_rec0: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
        }
    }

    // ── small constructors ──
    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn imul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [a, b])
    }
    fn iadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_add.clone(), [a, b])
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn rat_mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mk.clone(), [n, d])
    }
    /// `Rat.mk (Int.ofNat n) 1`.
    fn natcast(&self, n: Expr) -> Expr {
        self.rat_mk(self.of_nat(n), self.nat_one())
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn raw_mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.raw_mk.clone(), [n, d])
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), l],
        )
    }
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), a, b, h],
        )
    }
    fn eq_rat(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), x, y])
    }
    fn eq_int(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.int.clone(), x, y])
    }
    fn refl_rat(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), x])
    }
    fn refl_int(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int.clone(), x])
    }
    fn trans_rat(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), x, y, z, h1, h2])
    }
    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.int.clone(), x, y, z, h1, h2])
    }
    /// `@congrArg Rat Rat a b f h`.
    fn congr_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `@congrArg Int Int a b f h`.
    fn congr_int(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int.clone(), self.int.clone(), a, b, f, h],
        )
    }
    /// `Int.mul_one a : Int.mul a (Int.ofNat 1) = a`.
    fn imul_one(&self, a: Expr) -> Expr {
        Expr::app(self.int_mul_one.clone(), a)
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn fin_to_nat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.nat.clone())
    }
    fn sum(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, g])
    }
    fn sum_nat(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum_nat.clone(), [n, g])
    }
    /// `Fin.sum_congr n f g h : Fin.sum n f = Fin.sum n g`.
    fn sum_congr(&self, n: Expr, f: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_congr.clone(), [n, f, g, h])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    /// `indNat b = @Bool.rec (fun _=>Nat) 0 1 b` (inlined; matches the popcount
    /// machinery in `fourier_weight_parseval_proof.rs`).
    fn ind_nat_of(&self, bit: Expr) -> Expr {
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        Expr::apps(
            self.bool_rec.clone(),
            [nat_motive, self.nat_zero.clone(), self.nat_one(), bit],
        )
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    /// `@Eq.symm Rat x y h : Eq Rat y x`.
    fn symm_rat(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), x, y, h])
    }
    /// `Fin.sum_succ n f : Fin.sum (succ n) f = Rat.add (Fin.sum n (f∘castSucc)) (f (last n))`.
    fn sum_succ(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum_succ.clone(), [n, f])
    }
    /// `Fin.castSucc n i : Fin (n+1)`.
    fn cast_succ(&self, n: &Expr, i: Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i])
    }
    /// `Fin.last n : Fin (n+1)`.
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    /// `Rat.add_natCast a b : mk (ofNat (a+b)) 1 = add (mk (ofNat a) 1) (mk (ofNat b) 1)`.
    fn add_natcast(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_natcast.clone(), [a, b])
    }
    /// `fun (i : Fin n) => Rat.mk (Int.ofNat (g i)) 1` — the natCast of a
    /// Nat-valued summand `g`.
    fn castfn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = self.natcast(Expr::app(g.clone(), i));
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `g ∘ Fin.castSucc k : Fin k → Nat := fun i => g (Fin.castSucc k i)`.
    fn compose_cast(&self, parent: &EnvDeclBuilder, k: &Expr, g: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_k = self.fin_of(k);
        let (i_id, i) = ch.fresh_local(fin_k.clone());
        let body = Expr::app(g.clone(), self.cast_succ(k, i));
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_k, body))
    }

    // ── (c) order-bridge helpers ──
    /// `Int.le a b`.
    fn int_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [a, b])
    }
    /// `Nat.le a b`.
    fn nle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Int.le_refl a : Int.le a a`.
    fn int_le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.int_le_refl.clone(), a)
    }
    /// `Int.le_trans a b c h1 h2 : Int.le a c`.
    fn int_le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.int_le_trans.clone(), [a, b, cc, h1, h2])
    }
    /// `@Eq Bool x y` (for the `ble = true` antecedent).
    fn eq_bool(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_bool.clone(), [self.bool_.clone(), x, y])
    }
    /// `Nat.ble k m`.
    fn ble(&self, k: Expr, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [k, m])
    }
    /// `@Eq.subst Rat motive a b h_eq h_motive_a`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
}

impl Environment {
    /// `BoolAnalysis.setSizeNat (n : Nat) (S : HCPoint n) : Nat`
    /// `:= Fin.sumNat n (fun i => indNat (S i))` — the Nat-valued popcount `|S|`.
    ///
    /// The Nat twin of the reducible `setSize` carrier; `indNat b` is the inlined
    /// `@Bool.rec (fun _=>Nat) 0 1 b` used by the popcount machinery. Reducible
    /// `Declaration::Definition`; closure bottoms out in reducible `Fin.sumNat` /
    /// `Bool.rec`, so theorems over it stay `Constructive`. Idempotent.
    pub(crate) fn register_set_size_nat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.setSizeNat");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        self.init_boolean_analysis_foundations()?; // HCPoint, Fin.sumNat
        self.init_bool()?; // Bool.rec

        let c = NatBridgeConsts::new();

        // Type: (n : Nat) -> HCPoint n -> Nat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let s_type = c.hcpoint_of(&n);
            let (s_id, _s) = b.fresh_local(s_type.clone());
            let r = b.mk_pi(s_id, BinderInfo::Default, s_type, c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n) (S) => Fin.sumNat n (fun (i : Fin n) => indNat (S i))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let s_type = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(s_type.clone());

            let summand = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let body = c.ind_nat_of(Expr::app(s.clone(), i));
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            let body = c.sum_nat(n.clone(), summand);
            let r = b.mk_lam(s_id, BinderInfo::Default, s_type, body);
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
}

// ── (b1) Rat.add_natCast : mk (ofNat (a+b)) 1 = add (mk (ofNat a) 1) (mk (ofNat b) 1) ──

/// Type `∀ (a b : Nat), Rat.mk (ofNat (a+b)) 1 = Rat.add (mk (ofNat a) 1) (mk (ofNat b) 1)`.
fn add_natcast_type(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (b_id, bv) = b.fresh_local(c.nat.clone());
    let lhs = c.natcast(c.nadd(a.clone(), bv.clone()));
    let rhs = c.radd(c.natcast(a.clone()), c.natcast(bv.clone()));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(b_id, BinderInfo::Default, c.nat.clone(), concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Value for `Rat.add_natCast` — one `Quot.sound`, mirroring `Rat.add_natCast_one`
/// but with general `b` in place of `1`.
///
/// `Rat.add (mk (ofNat a) 1) (mk (ofNat b) 1)` reduces (Rat.add lift, both
/// effDenoms ≡ ofNat 1) to the class of
///   `Raw.mk ((ofNat a · ofNat 1) + (ofNat b · ofNat 1)) (Nat.mul 1 1)`,
/// and `Rat.mk (ofNat (a+b)) 1` is the class of `Raw.mk (ofNat (a+b)) 1`.
/// `Quot.sound` closes the goal once we exhibit the unfolded
///   `Eq Int (ofNat (a+b) · ofNat 1) ((ofNat a · 1 + ofNat b · 1) · ofNat 1)`.
/// Numerator identity `Rnum = Lnum` reversed:
///   `(ofNat a · 1) + (ofNat b · 1) =[mul_one ×2] ofNat a + ofNat b ≡ ofNat (a+b)`.
fn add_natcast_value(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (b_id, bv) = b.fresh_local(c.nat.clone());

    let o1 = c.of_nat(c.nat_one()); // ofNat 1
    let of_a = c.of_nat(a.clone());
    let of_b = c.of_nat(bv.clone());
    let ab = c.nadd(a.clone(), bv.clone());
    let of_ab = c.of_nat(ab.clone()); // ofNat (a+b) ≡ ofNat a + ofNat b (defeq)

    // Lnum := (ofNat a · ofNat 1) + (ofNat b · ofNat 1) — the reduced add numerator.
    let l_a = c.imul(of_a.clone(), o1.clone());
    let l_b = c.imul(of_b.clone(), o1.clone());
    let l_num = c.iadd(l_a.clone(), l_b.clone());

    // mid := ofNat a + ofNat b  (after collapsing both products by mul_one).
    let mid = c.iadd(of_a.clone(), of_b.clone());

    // s1 : (ofNat a · 1) + (ofNat b · 1) = ofNat a + (ofNat b · 1)
    //   via congrArg (· + (ofNat b · 1)) (Int.mul_one (ofNat a)).
    let add_right_lb = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = d.fresh_local(c.int.clone());
        let body = c.iadd(w, l_b.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body))
    };
    let mid_a = c.iadd(of_a.clone(), l_b.clone()); // ofNat a + (ofNat b · 1)
    let s1 = c.congr_int(
        l_a.clone(),
        of_a.clone(),
        add_right_lb,
        c.imul_one(of_a.clone()),
    );

    // s2 : ofNat a + (ofNat b · 1) = ofNat a + ofNat b
    //   via congrArg (ofNat a + ·) (Int.mul_one (ofNat b)).
    let add_left_ofa = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = d.fresh_local(c.int.clone());
        let body = c.iadd(of_a.clone(), w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body))
    };
    let s2 = c.congr_int(
        l_b.clone(),
        of_b.clone(),
        add_left_ofa,
        c.imul_one(of_b.clone()),
    );

    // num_eq_partial : Lnum = mid    (s1 ; s2)
    let num_eq_partial = c.trans_int(l_num.clone(), mid_a.clone(), mid.clone(), s1, s2);
    // mid ≡ ofNat (a+b) definitionally; retype via refl (ofNat (a+b)).
    let mid_to_ab = c.refl_int(of_ab.clone()); // : mid = ofNat (a+b)  (defeq)
    let num_eq = c.trans_int(
        l_num.clone(),
        mid.clone(),
        of_ab.clone(),
        num_eq_partial,
        mid_to_ab,
    );
    // We need Rnum = Lnum, i.e. ofNat (a+b) = Lnum: symm of num_eq.
    let num_eq_rev = Expr::apps(
        c.eq_symm.clone(),
        [c.int.clone(), l_num.clone(), of_ab.clone(), num_eq],
    );

    // equiv : Eq Int (ofNat (a+b) · ofNat 1) (Lnum · ofNat 1)
    //   via congrArg (· * ofNat 1) num_eq_rev. DEFEQ to the unfolded
    //   `Rat.Raw.Equiv (Raw.mk (ofNat (a+b)) 1) (Raw.mk Lnum (1·1))`.
    let mul_right_o1 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = d.fresh_local(c.int.clone());
        let body = c.imul(w, o1.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body))
    };
    let equiv = c.congr_int(of_ab.clone(), l_num.clone(), mul_right_o1, num_eq_rev);

    // Raw representatives.
    let nat_one = c.nat_one();
    let raw_l = c.raw_mk(of_ab.clone(), nat_one.clone()); // RHS-target class
    let raw_r = c.raw_mk(
        l_num.clone(),
        Expr::apps(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            [nat_one.clone(), nat_one.clone()],
        ),
    );

    // Quot.sound raw_l raw_r equiv : Quot.mk raw_l = Quot.mk raw_r.
    //   Quot.mk raw_l ≡ Rat.mk (ofNat (a+b)) 1   (LHS goal)
    //   Quot.mk raw_r ≡ Rat.add (mk (ofNat a) 1) (mk (ofNat b) 1)  (RHS goal)
    let sound = c.quot_sound(raw_l.clone(), raw_r.clone(), equiv);

    // Retarget to user-facing goal via trans against refls (both sides defeq).
    let lhs_goal = c.natcast(ab.clone());
    let rhs_goal = c.radd(c.natcast(a.clone()), c.natcast(bv.clone()));
    let quot_l = c.quot_mk(raw_l);
    let quot_r = c.quot_mk(raw_r);
    let to_quot_l = c.refl_rat(lhs_goal.clone()); // : lhs_goal = quot_l
    let from_quot_r = c.refl_rat(rhs_goal.clone()); // : quot_r = rhs_goal
    let step1 = c.trans_rat(
        lhs_goal.clone(),
        quot_l.clone(),
        quot_r.clone(),
        to_quot_l,
        sound,
    );
    let proof = c.trans_rat(
        lhs_goal.clone(),
        quot_r.clone(),
        rhs_goal.clone(),
        step1,
        from_quot_r,
    );

    let e = b.mk_lam(b_id, BinderInfo::Default, c.nat.clone(), proof);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Rat.add_natCast` (b1). Idempotent, constructive, empty closure.
    pub(crate) fn register_rat_add_natcast(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_natCast");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.mk, Rat.add, Quot machinery
        self.register_int_mul_one_proof()?; // gates the numerator collapse

        let c = NatBridgeConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: add_natcast_type(&c),
            value: add_natcast_value(&c),
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
        let tc = TypeChecker::with_mode(env, env.mode());
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
        );
    }

    #[test]
    fn test_set_size_nat_is_definition() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_set_size_nat().expect("register_set_size_nat");
        env.register_set_size_nat().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.setSizeNat");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "setSizeNat is a Definition"
        );
    }

    #[test]
    fn test_rat_add_natcast_is_constructive() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_rat_add_natcast()
            .expect("register_rat_add_natcast");
        env.register_rat_add_natcast().expect("idempotent");
        check_constructive(&env, "Rat.add_natCast");
    }
}

// ── (b2) Fin.sum_natCast : Σ (mk (ofNat (g i)) 1) = mk (ofNat (Σ_Nat g)) 1 ──

/// Type `∀ (n : Nat) (g : Fin n → Nat),
///   Fin.sum n (fun i => mk (ofNat (g i)) 1) = mk (ofNat (Fin.sumNat n g)) 1`.
fn sum_natcast_type(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.fin_to_nat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let lhs = c.sum(n.clone(), c.castfn(&b, &n, &g));
    let rhs = c.natcast(c.sum_nat(n.clone(), g.clone()));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Motive `fun (n : Nat) => ∀ (g : Fin n → Nat),
///   Fin.sum n (castfn g) = mk (ofNat (Fin.sumNat n g)) 1`.
fn sum_natcast_motive_body(c: &NatBridgeConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let g_ty = c.fin_to_nat(n);
    let (g_id, g) = ch.fresh_local(g_ty.clone());
    let lhs = c.sum(n.clone(), c.castfn(&ch, n, &g));
    let rhs = c.natcast(c.sum_nat(n.clone(), g.clone()));
    let body = c.eq_rat(lhs, rhs);
    ch.finish_child(ch.mk_pi(g_id, BinderInfo::Default, g_ty, body))
}

fn sum_natcast_value(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();

    // motive : fun (n : Nat) => ∀ g, Fin.sum n (castfn g) = mk (ofNat (Fin.sumNat n g)) 1
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = d.fresh_local(c.nat.clone());
        let body = sum_natcast_motive_body(c, &d, &n);
        d.finish_child(d.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // base : motive 0 = fun (g : Fin 0 → Nat) =>
    //   refl (mk (ofNat 0) 1).
    //   Fin.sum 0 (castfn g) ≡ Rat.zero ≡ mk (ofNat 0) 1, and
    //   Fin.sumNat 0 g ≡ Nat.zero, so RHS ≡ mk (ofNat 0) 1; closes by refl.
    let base = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let g_ty = c.fin_to_nat(&c.nat_zero);
        let (g_id, _g) = d.fresh_local(g_ty.clone());
        let body = c.refl_rat(c.natcast(c.nat_zero.clone()));
        d.finish_child(d.mk_lam(g_id, BinderInfo::Default, g_ty, body))
    };

    // step : fun (k) (ih : motive k) (g : Fin (k+1) → Nat) =>
    //   chain closing Fin.sum (k+1) (castfn g) = mk (ofNat (Fin.sumNat (k+1) g)) 1.
    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let ih_ty = sum_natcast_motive_body(c, &d, &k);
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());
        let sk = c.succ(k.clone());
        let g_ty = c.fin_to_nat(&sk);
        let (g_id, g) = d.fresh_local(g_ty.clone());

        // G := castfn g : Fin (k+1) → Rat.
        let big_g = c.castfn(&d, &sk, &g);
        // g' := g ∘ castSucc : Fin k → Nat.
        let g_prime = c.compose_cast(&d, &k, &g);
        // G ∘ castSucc = castfn g'   (definitionally: both are
        //   fun i => mk (ofNat (g (castSucc i))) 1). We use castfn g' as the
        //   prefix function; Fin.sum_succ produces (G ∘ castSucc).
        let cast_g_prime = c.castfn(&d, &k, &g_prime);

        // sum_k_prime := Fin.sum k (castfn g')  — the IH LHS.
        let sum_k_prime = c.sum(k.clone(), cast_g_prime.clone());
        // sumNat_k_prime := Fin.sumNat k g'.
        let sumnat_k_prime = c.sum_nat(k.clone(), g_prime.clone());
        // g_last := g (last k) : Nat.
        let g_last = Expr::app(g.clone(), c.last(&k));

        // e1 : Fin.sum (k+1) G = Rat.add (Fin.sum k (G∘castSucc)) (G (last k))
        //   [Fin.sum_succ (k) (G)].  (G∘castSucc ≡ castfn g', G (last k) ≡ mk (ofNat g_last) 1.)
        let lhs0 = c.sum(sk.clone(), big_g.clone());
        let glast_cast = c.natcast(g_last.clone()); // mk (ofNat g_last) 1
        let add_prefix_last = c.radd(sum_k_prime.clone(), glast_cast.clone());
        let e1 = c.sum_succ(k.clone(), big_g.clone());

        // ih_app : Fin.sum k (castfn g') = mk (ofNat (Fin.sumNat k g')) 1  [ih g'].
        let ih_app = Expr::app(ih.clone(), g_prime.clone());
        let natcast_sumnat_kp = c.natcast(sumnat_k_prime.clone());

        // e2 : Rat.add (Fin.sum k (castfn g')) (mk (ofNat g_last) 1)
        //      = Rat.add (mk (ofNat (Fin.sumNat k g')) 1) (mk (ofNat g_last) 1)
        //   via congrArg (· + (mk (ofNat g_last) 1)) ih_app.
        let add_right_glast = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (w_id, w) = e.fresh_local(c.rat.clone());
            let body = c.radd(w, glast_cast.clone());
            e.finish_child(e.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let add_natcast_kp_glast = c.radd(natcast_sumnat_kp.clone(), glast_cast.clone());
        let e2 = c.congr_rat(
            sum_k_prime.clone(),
            natcast_sumnat_kp.clone(),
            add_right_glast,
            ih_app,
        );

        // e3 : Rat.add (mk (ofNat (Fin.sumNat k g')) 1) (mk (ofNat g_last) 1)
        //      = mk (ofNat (Nat.add (Fin.sumNat k g') g_last)) 1
        //   via symm of (Rat.add_natCast (Fin.sumNat k g') g_last).
        let nat_sum_full = c.nadd(sumnat_k_prime.clone(), g_last.clone());
        let natcast_full = c.natcast(nat_sum_full.clone());
        let add_natcast_thm = c.add_natcast(sumnat_k_prime.clone(), g_last.clone());
        let e3 = c.symm_rat(
            natcast_full.clone(),
            add_natcast_kp_glast.clone(),
            add_natcast_thm,
        );

        // chain: lhs0 = add_prefix_last (e1) = add_natcast_kp_glast (e2) = natcast_full (e3).
        // natcast_full ≡ mk (ofNat (Fin.sumNat (k+1) g)) 1  (Fin.sumNat ι-step defeq).
        let t1 = c.trans_rat(
            lhs0.clone(),
            add_prefix_last.clone(),
            add_natcast_kp_glast.clone(),
            e1,
            e2,
        );
        let proof = c.trans_rat(
            lhs0.clone(),
            add_natcast_kp_glast,
            natcast_full.clone(),
            t1,
            e3,
        );

        let e = d.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
        let e = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e))
    };

    // fun (n : Nat) => @Nat.rec.{0} motive base step n
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
}

// ── (b) BoolAnalysis.setSize_eq_natCast : setSize n S = mk (ofNat (setSizeNat n S)) 1 ──

/// `ind_eq_natCast_indNat b : ind b = mk (ofNat (indNat b)) 1` via `Bool.rec`.
/// Both branches close by `refl`: `ind false ≡ Rat.zero ≡ mk (ofNat 0) 1`
/// (`indNat false ≡ 0`), `ind true ≡ Rat.one ≡ mk (ofNat 1) 1`
/// (`indNat true ≡ 1`).
fn ind_eq_natcast_per_bit(c: &NatBridgeConsts, bit: &Expr) -> Expr {
    // motive : fun (bb : Bool) => ind bb = mk (ofNat (indNat bb)) 1
    let motive = {
        let mut m = EnvDeclBuilder::new();
        let (bb_id, bb) = m.fresh_local(c.bool_.clone());
        let lhs = c.ind_of(bb.clone());
        let rhs = c.natcast(c.ind_nat_of(bb.clone()));
        let body = c.eq_rat(lhs, rhs);
        m.finish(m.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
    // false-case : ind false = mk (ofNat (indNat false)) 1 := refl (mk (ofNat 0) 1)
    //   ind false ≡ Rat.zero ≡ mk (ofNat 0) 1; indNat false ≡ 0.
    let false_case = c.refl_rat(c.natcast(c.ind_nat_of(bool_false)));
    // true-case : ind true = mk (ofNat (indNat true)) 1 := refl (mk (ofNat 1) 1)
    let true_case = c.refl_rat(c.natcast(c.ind_nat_of(bool_true)));
    // Prop-valued motive (`Eq Rat ...`) ⇒ Bool.rec.{0}.
    Expr::apps(
        c.bool_rec0.clone(),
        [motive, false_case, true_case, bit.clone()],
    )
}

/// Type `∀ (n : Nat) (S : HCPoint n),
///   setSize n S = mk (ofNat (setSizeNat n S)) 1`.
fn set_size_eq_natcast_type(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let s_ty = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(s_ty.clone());
    let lhs = c.set_size_of(&n, &s);
    let rhs = c.natcast(c.set_size_nat_of(&n, &s));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(s_id, BinderInfo::Default, s_ty, concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn set_size_eq_natcast_value(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let s_ty = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(s_ty.clone());

    // indFn := fun (i : Fin n) => ind (S i)   — the setSize integrand.
    let ind_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.ind_of(Expr::app(s.clone(), i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    // indNatFn := fun (i : Fin n) => indNat (S i)  — the setSizeNat summand (Nat).
    let ind_nat_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.ind_nat_of(Expr::app(s.clone(), i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    // castIndNatFn := fun (i : Fin n) => mk (ofNat (indNat (S i))) 1 — castfn of indNatFn.
    let cast_ind_nat_fn = c.castfn(&b, &n, &ind_nat_fn);

    // pointwise : ∀ (i : Fin n), ind (S i) = mk (ofNat (indNat (S i))) 1.
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let bit = Expr::app(s.clone(), i);
        let body = ind_eq_natcast_per_bit(c, &bit);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    // e1 : Fin.sum n indFn = Fin.sum n castIndNatFn  [Fin.sum_congr n indFn castIndNatFn pointwise].
    //   LHS ≡ setSize n S (reducible setSize).
    let sum_ind = c.sum(n.clone(), ind_fn.clone());
    let sum_cast = c.sum(n.clone(), cast_ind_nat_fn.clone());
    let e1 = c.sum_congr(
        n.clone(),
        ind_fn.clone(),
        cast_ind_nat_fn.clone(),
        pointwise,
    );

    // e2 : Fin.sum n castIndNatFn = mk (ofNat (Fin.sumNat n indNatFn)) 1
    //   [Fin.sum_natCast n indNatFn].  RHS ≡ mk (ofNat (setSizeNat n S)) 1 (reducible setSizeNat).
    let sumnat = c.sum_nat(n.clone(), ind_nat_fn.clone());
    let natcast_sumnat = c.natcast(sumnat.clone());
    let e2 = Expr::apps(
        Expr::const_(Name::from_string("Fin.sum_natCast"), vec![]),
        [n.clone(), ind_nat_fn.clone()],
    );

    // proof : setSize n S = mk (ofNat (setSizeNat n S)) 1  (trans e1 e2; both ends defeq).
    let proof = c.trans_rat(sum_ind, sum_cast, natcast_sumnat, e1, e2);

    let e = b.mk_lam(s_id, BinderInfo::Default, s_ty, proof);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Fin.sum_natCast` (b2) and `BoolAnalysis.setSize_eq_natCast` (b).
    /// Idempotent, constructive, empty closure.
    pub(crate) fn register_set_size_eq_natcast(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?; // Fin.sum, Fin.sumNat, ind
        self.init_fin_sum()?; // Fin.sum_congr, Fin.sum_succ
        self.register_set_size()?; // BoolAnalysis.setSize
        self.register_set_size_nat()?; // BoolAnalysis.setSizeNat
        self.register_rat_add_natcast()?; // (b1)

        let c = NatBridgeConsts::new();
        if self
            .get_const(&Name::from_string("Fin.sum_natCast"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Fin.sum_natCast"),
                level_params: vec![],
                type_: sum_natcast_type(&c),
                value: sum_natcast_value(&c),
            })?;
        }
        if self
            .get_const(&Name::from_string("BoolAnalysis.setSize_eq_natCast"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.setSize_eq_natCast"),
                level_params: vec![],
                type_: set_size_eq_natcast_type(&c),
                value: set_size_eq_natcast_value(&c),
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests_bridge {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        let tc = TypeChecker::with_mode(env, env.mode());
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
        );
    }

    #[test]
    fn test_fin_sum_natcast_is_constructive() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_set_size_eq_natcast()
            .expect("register_set_size_eq_natcast");
        check_constructive(&env, "Fin.sum_natCast");
    }

    #[test]
    fn test_set_size_eq_natcast_is_constructive() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_set_size_eq_natcast()
            .expect("register_set_size_eq_natcast");
        env.register_set_size_eq_natcast().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.setSize_eq_natCast");
    }
}

// ── (c) Nat.cast_le_of_ble : Nat.ble k m = true → mk (ofNat k) 1 ≤ mk (ofNat m) 1 ──

/// Type `∀ (k m : Nat), Int.le (Int.ofNat k) (Int.ofNat m)` premised on `Nat.le k m`.
/// `Int.ofNat_le_ofNat_of_le k m h : Int.le (ofNat k) (ofNat m)`.
fn ofnat_le_type(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let h_ty = c.nle(k.clone(), m.clone());
    let (h_id, _h) = b.fresh_local(h_ty.clone());
    let concl = c.int_le(c.of_nat(k.clone()), c.of_nat(m.clone()));
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Value for `Int.ofNat_le_ofNat_of_le` — `Nat.le.rec` on the witness, parameter `k`.
fn ofnat_le_value(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let h_ty = c.nle(k.clone(), m.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let of_k = c.of_nat(k.clone());

    // motive : fun (t : Nat) (_ : Nat.le k t) => Int.le (ofNat k) (ofNat t)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat.clone());
        let le_kt = c.nle(k.clone(), t.clone());
        let (ht_id, _ht) = mb.fresh_local(le_kt.clone());
        let body = c.int_le(of_k.clone(), c.of_nat(t.clone()));
        let lam = mb.mk_lam(ht_id, BinderInfo::Default, le_kt, body);
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam);
        mb.finish_child(lam)
    };

    // refl_case : Int.le (ofNat k) (ofNat k) := Int.le_refl (ofNat k)
    let refl_case = c.int_le_refl(of_k.clone());

    // step_case : fun {t} (_ : Nat.le k t) (ih : Int.le (ofNat k) (ofNat t)) =>
    //   Int.le_trans (ofNat k) (ofNat t) (ofNat (succ t)) ih
    //                (Int.le_self_add_one (ofNat t))
    //   — Int.le_self_add_one (ofNat t) : Int.le (ofNat t) (add (ofNat t) (ofNat 1)),
    //     and ofNat (succ t) ≡ add (ofNat t) (ofNat 1) (Int.ofNat additive defeq),
    //     so this inhabits the motive at succ t.
    let step_case = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = sb.fresh_local(c.nat.clone());
        let le_kt = c.nle(k.clone(), t.clone());
        let (ht_id, _ht) = sb.fresh_local(le_kt.clone());
        let ih_ty = c.int_le(of_k.clone(), c.of_nat(t.clone()));
        let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

        let of_t = c.of_nat(t.clone());
        let of_succ_t = c.of_nat(c.succ(t.clone()));
        let self_add_one = Expr::app(c.int_le_self_add_one.clone(), of_t.clone());
        let body = c.int_le_trans(of_k.clone(), of_t.clone(), of_succ_t, ih, self_add_one);

        let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
        let lam = sb.mk_lam(ht_id, BinderInfo::Default, le_kt, lam);
        let lam = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), lam);
        sb.finish_child(lam)
    };

    // @Nat.le.rec.{0} k motive refl_case step_case m h : Int.le (ofNat k) (ofNat m)
    let rec_app = Expr::apps(
        c.nat_le_rec.clone(),
        [
            k.clone(),
            motive,
            refl_case,
            step_case,
            m.clone(),
            h.clone(),
        ],
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, rec_app);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Type `∀ (k m : Nat), Nat.ble k m = true → mk (ofNat k) 1 ≤ mk (ofNat m) 1`
/// (the `≤` is `Rat.le` via `instLERat`, written through `LE.le`).
fn cast_le_of_ble_type(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let ante = c.eq_bool(c.ble(k.clone(), m.clone()), c.bool_true.clone());
    let (h_id, _h) = b.fresh_local(ante.clone());
    let concl = rat_le_via_le(c, c.natcast(k.clone()), c.natcast(m.clone()));
    let e = b.mk_pi(h_id, BinderInfo::Default, ante, concl);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `@LE.le Rat instLERat a b` — the surface `a ≤ b` the KKL threshold lift uses.
fn rat_le_via_le(c: &NatBridgeConsts, a: Expr, b: Expr) -> Expr {
    let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
    let inst = Expr::const_(Name::from_string("instLERat"), vec![]);
    Expr::apps(le_le, [c.rat.clone(), inst, a, b])
}

fn cast_le_of_ble_value(c: &NatBridgeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let ante = c.eq_bool(c.ble(k.clone(), m.clone()), c.bool_true.clone());
    let (h_id, h) = b.fresh_local(ante.clone());

    let of_k = c.of_nat(k.clone());
    let of_m = c.of_nat(m.clone());
    let o1 = c.of_nat(c.nat_one());

    // h_nat : Nat.le k m := Nat.le_of_ble_eq_true k m h
    let h_nat = Expr::apps(c.nat_le_of_ble.clone(), [k.clone(), m.clone(), h]);
    // h_int : Int.le (ofNat k) (ofNat m) := Int.ofNat_le_ofNat_of_le k m h_nat
    let h_int = Expr::apps(
        Expr::const_(Name::from_string("Int.ofNat_le_ofNat_of_le"), vec![]),
        [k.clone(), m.clone(), h_nat],
    );

    // Goal (delta): Int.le (mul (ofNat k) (ofNat 1)) (mul (ofNat m) (ofNat 1)).
    // Transport h_int along (ofNat k = mul (ofNat k) (ofNat 1)) and likewise for m,
    // each via symm (Int.mul_one ·). We subst at the Int level into the motive
    //   left  : fun x => Int.le x (ofNat m)            [a := ofNat k, target := mul (ofNat k) 1]
    //   right : fun y => Int.le (mul (ofNat k) 1) y    [a := ofNat m, target := mul (ofNat m) 1]
    let mul_k1 = c.imul(of_k.clone(), o1.clone());
    let mul_m1 = c.imul(of_m.clone(), o1.clone());

    // e_k : ofNat k = mul (ofNat k) (ofNat 1)  := symm (Int.mul_one (ofNat k))
    let e_k = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int.clone(),
            mul_k1.clone(),
            of_k.clone(),
            c.imul_one(of_k.clone()),
        ],
    );
    // e_m : ofNat m = mul (ofNat m) (ofNat 1)  := symm (Int.mul_one (ofNat m))
    let e_m = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int.clone(),
            mul_m1.clone(),
            of_m.clone(),
            c.imul_one(of_m.clone()),
        ],
    );

    // subst the left operand: motive_left x := Int.le x (ofNat m)
    let motive_left = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(c.int.clone());
        let body = c.int_le(x, of_m.clone());
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body))
    };
    // step1 : Int.le (mul (ofNat k) 1) (ofNat m)
    let step1 = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int.clone(),
            motive_left,
            of_k.clone(),
            mul_k1.clone(),
            e_k,
            h_int,
        ],
    );

    // subst the right operand: motive_right y := Int.le (mul (ofNat k) 1) y
    let motive_right = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = d.fresh_local(c.int.clone());
        let body = c.int_le(mul_k1.clone(), y);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body))
    };
    // step2 : Int.le (mul (ofNat k) 1) (mul (ofNat m) 1)
    //   ≡ Rat.le (mk (ofNat k) 1) (mk (ofNat m) 1) ≡ (mk (ofNat k) 1) ≤ (mk (ofNat m) 1).
    let step2 = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int.clone(),
            motive_right,
            of_m.clone(),
            mul_m1.clone(),
            e_m,
            step1,
        ],
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, ante, step2);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Int.ofNat_le_ofNat_of_le` and `Nat.cast_le_of_ble` (c).
    /// Idempotent, constructive, empty closure.
    pub(crate) fn register_nat_cast_le_of_ble(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_rat()?; // Rat.le, instLERat, Rat.mk
        self.init_int_ord()?; // Int.le, Int.NonNeg
        self.register_int_le_refl_proof()?;
        self.register_int_le_trans_proof()?;
        self.register_int_le_self_add_one_proof()?;
        self.register_int_mul_one_proof()?;
        self.register_nat_ble_le_lemmas()?; // Nat.le_of_ble_eq_true

        let c = NatBridgeConsts::new();
        if self
            .get_const(&Name::from_string("Int.ofNat_le_ofNat_of_le"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Int.ofNat_le_ofNat_of_le"),
                level_params: vec![],
                type_: ofnat_le_type(&c),
                value: ofnat_le_value(&c),
            })?;
        }
        if self
            .get_const(&Name::from_string("Nat.cast_le_of_ble"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.cast_le_of_ble"),
                level_params: vec![],
                type_: cast_le_of_ble_type(&c),
                value: cast_le_of_ble_value(&c),
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests_order {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        let tc = TypeChecker::with_mode(env, env.mode());
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
        );
    }

    #[test]
    fn test_ofnat_le_ofnat_of_le_is_constructive() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_nat_cast_le_of_ble()
            .expect("register_nat_cast_le_of_ble");
        check_constructive(&env, "Int.ofNat_le_ofNat_of_le");
    }

    #[test]
    fn test_nat_cast_le_of_ble_is_constructive() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_nat_cast_le_of_ble()
            .expect("register_nat_cast_le_of_ble");
        env.register_nat_cast_le_of_ble().expect("idempotent");
        check_constructive(&env, "Nat.cast_le_of_ble");
    }
}

// ── (d) BoolAnalysis.subsetSum_threshold_le_nat — instantiated tail bound ──

/// Shared atoms for the (d) instantiation.
struct ThresholdNatAtoms {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    hcpoint: Expr,
    rat_mul: Expr,
    nat_ble: Expr,
    rat_zero: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    eq_bool: Expr,
    u1: Level,
}

impl ThresholdNatAtoms {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size: Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            nat_ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq_symm: Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            eq_subst: Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            u1: Level::succ(Level::zero()),
        }
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    /// `Rat.mk (Int.ofNat n) 1`.
    fn natcast(&self, n: &Expr) -> Expr {
        let of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(of_nat, n.clone()), nat_one],
        )
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn ble(&self, k: Expr, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [k, m])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `fun (S : HCPoint n) => b S` where `b S := Nat.ble kNat (setSizeNat n S)`.
    fn bfn(&self, parent: &EnvDeclBuilder, n: &Expr, knat: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = self.ble(knat.clone(), self.set_size_nat_of(n, &s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (S : HCPoint n) => (mk (ofNat kNat) 1) · (ind (b S) · w S)` — LHS integrand.
    fn lhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, knat: &Expr, w: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let bit = self.ble(knat.clone(), self.set_size_nat_of(n, &s));
        let body = self.mul(
            self.natcast(knat),
            self.mul(self.ind_of(bit), Expr::app(w.clone(), s)),
        );
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (S : HCPoint n) => setSize n S · w S` — RHS integrand.
    fn rhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, w: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = self.mul(self.set_size_of(n, &s), Expr::app(w.clone(), s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    fn forall_s(&self, parent: &EnvDeclBuilder, n: &Expr, body_of: impl Fn(&Expr) -> Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = body_of(&s);
        ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
    }
}

/// Type of `BoolAnalysis.subsetSum_threshold_le_nat`.
fn threshold_le_nat_type(a: &ThresholdNatAtoms) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(a.nat.clone());
    let (kn_id, knat) = b.fresh_local(a.nat.clone());
    let w_ty = a.hcpoint_to_rat(&n);
    let (w_id, w) = b.fresh_local(w_ty.clone());

    let hyp1 = a.forall_s(&b, &n, |s| {
        a.rat_le(a.rat_zero.clone(), Expr::app(w.clone(), s.clone()))
    });
    let hyp2 = a.forall_s(&b, &n, |s| {
        a.rat_le(a.rat_zero.clone(), a.set_size_of(&n, s))
    });

    let lhs = a.subset_sum_of(&n, a.lhs_fn(&b, &n, &knat, &w));
    let rhs = a.subset_sum_of(&n, a.rhs_fn(&b, &n, &w));
    let concl = a.rat_le(lhs, rhs);

    let (h1_id, _) = b.fresh_local(hyp1.clone());
    let (h2_id, _) = b.fresh_local(hyp2.clone());
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp2, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp1, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, w_ty, e);
    let e = b.mk_pi(kn_id, BinderInfo::Default, a.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, a.nat.clone(), e);
    b.finish(e)
}

/// Build the proof: instantiate `subsetSum_threshold_le` and discharge `hyp3`
/// via `(b)`+`(c)`.
fn threshold_le_nat_value(a: &ThresholdNatAtoms) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(a.nat.clone());
    let (kn_id, knat) = b.fresh_local(a.nat.clone());
    let w_ty = a.hcpoint_to_rat(&n);
    let (w_id, w) = b.fresh_local(w_ty.clone());

    let hyp1 = a.forall_s(&b, &n, |s| {
        a.rat_le(a.rat_zero.clone(), Expr::app(w.clone(), s.clone()))
    });
    let hyp2 = a.forall_s(&b, &n, |s| {
        a.rat_le(a.rat_zero.clone(), a.set_size_of(&n, s))
    });
    let (h1_id, h1) = b.fresh_local(hyp1.clone());
    let (h2_id, h2) = b.fresh_local(hyp2.clone());

    let k_rat = a.natcast(&knat);
    let bf = a.bfn(&b, &n, &knat);

    // hyp3 := fun (S) (h : Nat.ble kNat (setSizeNat n S) = true) =>
    //   subst (motive y => k_rat ≤ y) (mk (ofNat (setSizeNat n S)) 1) (setSize n S)
    //         (symm (setSize_eq_natCast n S))
    //         (Nat.cast_le_of_ble kNat (setSizeNat n S) h)
    //   : k_rat ≤ setSize n S.
    let hyp3 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = a.hcpoint_of(&n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ssn = a.set_size_nat_of(&n, &s);
        let ante = Expr::apps(
            a.eq_bool.clone(),
            [
                a.bool_.clone(),
                a.ble(knat.clone(), ssn.clone()),
                a.bool_true.clone(),
            ],
        );
        let (h_id, h) = d.fresh_local(ante.clone());

        let natcast_ssn = a.natcast(&ssn); // mk (ofNat (setSizeNat n S)) 1
        let set_size_s = a.set_size_of(&n, &s);

        // c_le : k_rat ≤ mk (ofNat (setSizeNat n S)) 1
        let c_le = Expr::apps(
            Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]),
            [knat.clone(), ssn.clone(), h],
        );
        // bridge : setSize n S = mk (ofNat (setSizeNat n S)) 1  [setSize_eq_natCast n S]
        let bridge = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.setSize_eq_natCast"), vec![]),
            [n.clone(), s.clone()],
        );
        // symm : mk (ofNat (setSizeNat n S)) 1 = setSize n S
        let bridge_sym = Expr::apps(
            a.eq_symm.clone(),
            [
                a.rat.clone(),
                set_size_s.clone(),
                natcast_ssn.clone(),
                bridge,
            ],
        );
        // motive y := k_rat ≤ y
        let motive = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (y_id, y) = e.fresh_local(a.rat.clone());
            let body = a.rat_le(k_rat.clone(), y);
            e.finish_child(e.mk_lam(y_id, BinderInfo::Default, a.rat.clone(), body))
        };
        // subst : k_rat ≤ setSize n S
        let body = Expr::apps(
            a.eq_subst.clone(),
            [
                a.rat.clone(),
                motive,
                natcast_ssn,
                set_size_s,
                bridge_sym,
                c_le,
            ],
        );
        let lam = d.mk_lam(h_id, BinderInfo::Default, ante, body);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, lam))
    };

    // subsetSum_threshold_le n k_rat w bf h1 h2 hyp3
    let body = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_threshold_le"),
            vec![],
        ),
        [
            n.clone(),
            k_rat.clone(),
            w.clone(),
            bf,
            h1.clone(),
            h2.clone(),
            hyp3,
        ],
    );

    let e = b.mk_lam(h2_id, BinderInfo::Default, hyp2, body);
    let e = b.mk_lam(h1_id, BinderInfo::Default, hyp1, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, w_ty, e);
    let e = b.mk_lam(kn_id, BinderInfo::Default, a.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, a.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_threshold_le_nat` (d) — the K2b threshold
    /// tail bound instantiated at the real Nat popcount indicator
    /// `b S := Nat.ble kNat (setSizeNat n S)`. Idempotent, constructive, empty
    /// closure.
    pub fn register_subset_sum_threshold_le_nat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_threshold_le_nat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_kkl_k2b()?; // subsetSum_threshold_le
        self.register_set_size_eq_natcast()?; // (b)
        self.register_nat_cast_le_of_ble()?; // (c)
        self.register_set_size_nat()?;

        let a = ThresholdNatAtoms::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: threshold_le_nat_type(&a),
            value: threshold_le_nat_value(&a),
        })
    }
}

#[cfg(test)]
mod tests_threshold_nat {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_subset_sum_threshold_le_nat_is_constructive() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_threshold_le_nat()
            .expect("register_subset_sum_threshold_le_nat");
        env.register_subset_sum_threshold_le_nat()
            .expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.subsetSum_threshold_le_nat");
        let info = env.get_const(&nm).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("proof present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("threshold_le_nat must kernel-check: {e:?}"));
        assert_eq!(env.proof_quality(&nm), Some(ProofQuality::Constructive));
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
        );
    }
}
