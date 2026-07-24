// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive prelude proof of the **universal half-ulp rounding bound**.
//!
//! `Nat.roundHalfEvenMod N V` rounds `N` to the nearest multiple of `V`, ties
//! to the even grid index. The two headlines prove the two-sided half-step
//! bound (`2 * |round - N| <= V`, written without an `abs`):
//!
//!   `Nat.round_half_even_mod_bound : ∀ (V N : Nat), Nat.lt 0 V ->
//!        And (Nat.le (Nat.mul 2 (Nat.sub (Nat.roundHalfEvenMod N V) N)) V)
//!            (Nat.le (Nat.mul 2 (Nat.sub N (Nat.roundHalfEvenMod N V))) V)`
//!
//!   `Nat.ulp_universal_bound : ∀ (e N : Nat),
//!        And (Nat.le (Nat.mul 2 (Nat.sub (Nat.roundHalfEvenMod N (Nat.pow 2 e)) N)) (Nat.pow 2 e))
//!            (Nat.le (Nat.mul 2 (Nat.sub N (Nat.roundHalfEvenMod N (Nat.pow 2 e)))) (Nat.pow 2 e))`
//!
//! Both are proven down to the foundational axioms only: `env.axiom_deps` is
//! EMPTY for each.
//!
//! This is a hand-translation of the validated Lean module
//! (Lean namespace `UlpUniv`; validated against the Lean 4 development). The def
//! `roundHalfEvenMod` is promoted to the public `Nat.roundHalfEvenMod`; the
//! supporting lemmas register under the private `Nat.ulpRound.` namespace. The
//! whole development sits on top of `Nat.div_add_mod` / `Nat.mod_lt`
//! (`init_nat_div_mod_lemmas`, the dependency we call at the top).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Bundle of the constants and small term-builders the ulp proofs need.
///
/// Everything Nat-valued is monomorphic, so `Eq`/`Eq.refl`/`Eq.symm`/
/// `Eq.trans`/`Eq.subst`/`congrArg` are pre-specialized to `Sort 1` (Nat lives
/// in `Type = Sort 1`); `False.elim` to `Sort 0` (Prop goals). The round
/// function dispatches via `@Bool.rec`, so we also keep `Bool`-spelled
/// `Eq`/`Eq.refl` and both `Bool.rec.{0}` (Prop-valued threaded motives) and
/// `Bool.rec.{1}` (Nat-valued case-splits).
struct Ulp {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    add: Expr,
    mul: Expr,
    sub: Expr,
    pred: Expr,
    div: Expr,
    nmod: Expr,
    pow: Expr,
    beq: Expr,
    ble: Expr,
    le: Expr,
    lt: Expr,
    two: Expr, // succ (succ zero)
    bool: Expr,
    btrue: Expr,
    bfalse: Expr,
    and: Expr,
    // `fun _ : Bool => Nat` — the Bool.rec motive for the Nat-valued round def.
    nat_const_motive: Expr,
    rec0: Expr,       // Nat.rec.{0}
    rec1: Expr,       // Nat.rec.{1}
    brec0: Expr,      // Bool.rec.{0}
    brec1: Expr,      // Bool.rec.{1}
    eq: Expr,         // @Eq.{1}
    eq_refl: Expr,    // @Eq.refl.{1}
    eq_symm: Expr,    // @Eq.symm.{1}
    eq_trans: Expr,   // @Eq.trans.{1}
    eq_subst: Expr,   // @Eq.subst.{1}
    congr_arg: Expr,  // @congrArg.{1,1}
    false_elim: Expr, // @False.elim.{0}
    and_intro: Expr,  // And.intro
    noconf0: Expr,    // Bool.noConfusion.{0}
}

impl Ulp {
    fn new() -> Self {
        let n = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l1 = Level::succ(Level::zero());
        let nat = n("Nat");
        let bool_ = n("Bool");
        let zero = n("Nat.zero");
        let succ = n("Nat.succ");
        let two = Expr::app(succ.clone(), Expr::app(succ.clone(), zero.clone()));
        // Bool.rec motive for a Nat-valued case split: `fun _ : Bool => Nat`.
        let nat_const_motive = Expr::lam(BinderInfo::Default, bool_.clone(), nat.clone());
        Self {
            zero,
            succ,
            add: n("Nat.add"),
            mul: n("Nat.mul"),
            sub: n("Nat.sub"),
            pred: n("Nat.pred"),
            div: n("Nat.div"),
            nmod: n("Nat.mod"),
            pow: n("Nat.pow"),
            beq: n("Nat.beq"),
            ble: n("Nat.ble"),
            le: n("Nat.le"),
            lt: n("Nat.lt"),
            two,
            btrue: n("Bool.true"),
            bfalse: n("Bool.false"),
            and: n("And"),
            nat_const_motive,
            rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            rec1: Expr::const_(Name::from_string("Nat.rec"), vec![l1.clone()]),
            brec0: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            brec1: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            eq: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            and_intro: Expr::const_(Name::from_string("And.intro"), vec![]),
            noconf0: Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]),
            bool: bool_,
            nat,
        }
    }

    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }
    fn add_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add.clone(), [a, b])
    }
    fn mul_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul.clone(), [a, b])
    }
    fn sub_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [a, b])
    }
    fn div_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.div.clone(), [a, b])
    }
    fn mod_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nmod.clone(), [a, b])
    }
    fn pow_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.pow.clone(), [a, b])
    }
    fn beq_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.beq.clone(), [a, b])
    }
    fn ble_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.ble.clone(), [a, b])
    }
    /// `@Nat.le a b : Prop`
    fn le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.le.clone(), [a, b])
    }
    /// `@Nat.lt a b : Prop`  (defeq `Nat.le (succ a) b`)
    fn lt_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.lt.clone(), [a, b])
    }
    /// `Nat.mul 2 x`
    fn two_mul_of(&self, x: Expr) -> Expr {
        self.mul_of(self.two.clone(), x)
    }
    /// `@Eq.{1} Nat lhs rhs : Prop`
    fn eq_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.nat.clone(), lhs, rhs])
    }
    /// `@Eq.{1} Bool lhs rhs : Prop`
    fn eq_bool_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.bool.clone(), lhs, rhs])
    }
    /// `@And lhs rhs : Prop`
    fn and_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.and.clone(), [lhs, rhs])
    }
    /// `@Eq.refl.{1} Nat x : @Eq Nat x x`
    fn refl(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.nat.clone(), x])
    }
    /// `@Eq.refl.{1} Bool x : @Eq Bool x x`
    fn refl_bool(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.bool.clone(), x])
    }
    /// `@Eq.symm.{1} Nat a b h : @Eq Nat b a`   (h : @Eq Nat a b)
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.nat.clone(), a, b, h])
    }
    /// `@Eq.symm.{1} Bool a b h : @Eq Bool b a`
    fn symm_bool(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.bool.clone(), a, b, h])
    }
    /// `@Eq.trans.{1} Nat a b c h1 h2 : @Eq Nat a c`
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.nat.clone(), a, b, c, h1, h2])
    }
    /// `@Eq.subst.{1} Nat motive a b h h2 : motive b`
    ///   motive : Nat → Prop, h : @Eq Nat a b, h2 : motive a.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.nat.clone(), motive, a, b, h, h2],
        )
    }
    /// `@congrArg.{1,1} Nat Nat a1 a2 f h : @Eq Nat (f a1) (f a2)`
    fn congr_arg(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat.clone(), self.nat.clone(), a1, a2, f, h],
        )
    }
    /// `@congrArg.{1,1} Nat Nat a1 a2 Nat.pred h`
    fn congr_pred(&self, a1: Expr, a2: Expr, h: Expr) -> Expr {
        self.congr_arg(a1, a2, self.pred.clone(), h)
    }
    /// `@congrArg.{1,1} Nat Nat a1 a2 Nat.succ h`
    fn congr_succ(&self, a1: Expr, a2: Expr, h: Expr) -> Expr {
        self.congr_arg(a1, a2, self.succ.clone(), h)
    }
    /// `@False.elim.{0} C h : C`   (C : Prop)
    fn false_elim(&self, c: Expr, h: Expr) -> Expr {
        Expr::apps(self.false_elim.clone(), [c, h])
    }
    /// `@And.intro A B pa pb : And A B`
    fn and_intro(&self, a: Expr, b: Expr, pa: Expr, pb: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [a, b, pa, pb])
    }
    /// `@Bool.noConfusion.{0} P a b h`
    fn noconf(&self, p: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.noconf0.clone(), [p, a, b, h])
    }
    /// `@Nat.rec.{0} motive base step major`  (Prop motive)
    fn rec0(&self, motive: Expr, base: Expr, step: Expr, major: Expr) -> Expr {
        Expr::apps(self.rec0.clone(), [motive, base, step, major])
    }
    /// `@Nat.rec.{1} motive base step major`  (Sort 1 / Nat motive)
    #[allow(dead_code)]
    fn rec1(&self, motive: Expr, base: Expr, step: Expr, major: Expr) -> Expr {
        Expr::apps(self.rec1.clone(), [motive, base, step, major])
    }
    /// `@Bool.rec.{0} motive fcase tcase major`  (Prop motive)
    fn brec0(&self, motive: Expr, fcase: Expr, tcase: Expr, major: Expr) -> Expr {
        Expr::apps(self.brec0.clone(), [motive, fcase, tcase, major])
    }
    /// `@Bool.rec.{1} (fun _ => Nat) fcase tcase major` — Nat-valued case split.
    fn bool_rec_nat(&self, fcase: Expr, tcase: Expr, major: Expr) -> Expr {
        Expr::apps(
            self.brec1.clone(),
            [self.nat_const_motive.clone(), fcase, tcase, major],
        )
    }

    fn const_(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }
}

/// Names of the def + private helper lemmas (under `Nat.ulpRound.`).
mod names {
    pub(super) const SUCC_SUB_SUCC: &str = "Nat.ulpRound.succ_sub_succ";
    pub(super) const ZERO_SUB: &str = "Nat.ulpRound.zero_sub";
    pub(super) const NMUL_ZERO_LEFT: &str = "Nat.ulpRound.nmul_zero_left";
    pub(super) const ONE_MUL: &str = "Nat.ulpRound.one_mul";
    pub(super) const TWO_MUL: &str = "Nat.ulpRound.two_mul";
    pub(super) const ADD_SUB_SELF_RIGHT: &str = "Nat.ulpRound.add_sub_self_right";
    pub(super) const ADD_SUB_CANCEL_LEFT: &str = "Nat.ulpRound.add_sub_cancel_left";
    pub(super) const SUB_ADD_ADD_RIGHT: &str = "Nat.ulpRound.sub_add_add_right";
    pub(super) const SUB_ADD_ADD_LEFT: &str = "Nat.ulpRound.sub_add_add_left";
    pub(super) const SUB_EQ_ZERO_OF_LE: &str = "Nat.ulpRound.sub_eq_zero_of_le";
    pub(super) const SUB_ADD_CANCEL: &str = "Nat.ulpRound.sub_add_cancel";
    pub(super) const LE_OF_ADD_LE_ADD_RIGHT: &str = "Nat.ulpRound.le_of_add_le_add_right";
    pub(super) const BLE_SUCC_FALSE_LE: &str = "Nat.ulpRound.ble_succ_false_le";
    pub(super) const N_SUB_DOWN: &str = "Nat.ulpRound.N_sub_down";
    pub(super) const DOWN_LE_N: &str = "Nat.ulpRound.down_le_N";
    pub(super) const DOWN_SUB_N: &str = "Nat.ulpRound.down_sub_N";
    pub(super) const UP_SUB_N: &str = "Nat.ulpRound.up_sub_N";
    pub(super) const N_LE_UP: &str = "Nat.ulpRound.N_le_up";
    pub(super) const N_SUB_UP: &str = "Nat.ulpRound.N_sub_up";
    pub(super) const UP_CONJ1_ARITH: &str = "Nat.ulpRound.up_conj1_arith";
    pub(super) const DOWN_BOUND: &str = "Nat.ulpRound.down_bound";
    pub(super) const UP_BOUND: &str = "Nat.ulpRound.up_bound";
    pub(super) const NMUL_POS: &str = "Nat.ulpRound.nmul_pos";
    pub(super) const TWO_POW_POS: &str = "Nat.ulpRound.two_pow_pos";
    // public headlines
    pub(super) const ROUND: &str = "Nat.roundHalfEvenMod";
    pub(super) const ROUND_BOUND: &str = "Nat.round_half_even_mod_bound";
    pub(super) const ULP_BOUND: &str = "Nat.ulp_universal_bound";
}

impl Environment {
    /// Register `Nat.roundHalfEvenMod` and the universal half-ulp bound
    /// (`Nat.round_half_even_mod_bound`, `Nat.ulp_universal_bound`) as
    /// constructive, axiom-free prelude declarations, plus the supporting
    /// helper lemmas under the private `Nat.ulpRound.` namespace.
    ///
    /// # Contract
    ///
    /// REQUIRES: a full `with_prelude()` foundation — in particular
    ///   `Nat.div_add_mod` / `Nat.mod_lt` (registered by the dependency call at
    ///   the top), the Nat ordering/arith lemmas, `Bool`/`Bool.rec`/
    ///   `Bool.noConfusion`, `And`/`And.intro`, `Eq.*`, `congrArg`, `False.elim`.
    /// ENSURES: On success the two headlines are `Declaration::Theorem`s with
    ///   empty (foundational-only) axiom closures, and `Nat.roundHalfEvenMod` is
    ///   a reducible `Declaration::Definition`.
    /// ENSURES: Idempotent — early-returns if `Nat.ulp_universal_bound` exists.
    pub(crate) fn init_nat_ulp_round_lemmas(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::ULP_BOUND))
            .is_some()
        {
            return Ok(());
        }

        // Headlines rest on the euclidean identity + modulus bound.
        self.init_nat_div_mod_lemmas()?;

        let c = Ulp::new();

        self.register_round_def(&c)?;
        self.register_succ_sub_succ(&c)?;
        self.register_zero_sub(&c)?;
        self.register_nmul_zero_left(&c)?;
        self.register_one_mul(&c)?;
        self.register_two_mul(&c)?;
        self.register_add_sub_self_right(&c)?;
        self.register_add_sub_cancel_left(&c)?;
        self.register_sub_add_add_right(&c)?;
        self.register_sub_add_add_left(&c)?;
        self.register_sub_eq_zero_of_le(&c)?;
        self.register_sub_add_cancel(&c)?;
        self.register_le_of_add_le_add_right(&c)?;
        self.register_ble_succ_false_le(&c)?;
        self.register_n_sub_down(&c)?;
        self.register_down_le_n(&c)?;
        self.register_down_sub_n(&c)?;
        self.register_up_sub_n(&c)?;
        self.register_n_le_up(&c)?;
        self.register_n_sub_up(&c)?;
        self.register_up_conj1_arith(&c)?;
        self.register_down_bound(&c)?;
        self.register_up_bound(&c)?;
        self.register_nmul_pos(&c)?;
        self.register_two_pow_pos(&c)?;
        self.register_round_bound(&c)?;
        self.register_ulp_universal_bound(&c)?;

        Ok(())
    }

    /// `def Nat.roundHalfEvenMod (N V : Nat) : Nat := <nested Bool.rec>`
    ///
    /// Registered `is_reducible` so Trust can def-eq-reduce it on concrete
    /// inputs. EXACTLY the round used by Trust's float model:
    /// ```text
    /// @Bool.rec (fun _ => Nat)
    ///   (@Bool.rec (fun _ => Nat)
    ///     (@Bool.rec (fun _ => Nat) (mul (succ q) V) (mul q V) (beq (mod q 2) 0))
    ///     (mul (succ q) V)
    ///     (ble (succ V) (mul 2 r)))
    ///   (mul q V)
    ///   (ble (succ (mul 2 r)) V)
    /// ```
    /// where `q := N/V`, `r := N%V`.
    fn register_round_def(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::ROUND);
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Type: ∀ (N V : Nat), Nat
        let mut b = EnvDeclBuilder::new();
        let (n_id, _n) = b.fresh_local(c.nat.clone());
        let (v_id, _v) = b.fresh_local(c.nat.clone());
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), c.nat.clone());
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let body = c.round_term(&vn, &vv);
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })
    }
}

impl Ulp {
    /// `q := N / V`
    fn q_of(&self, n: &Expr, v: &Expr) -> Expr {
        self.div_of(n.clone(), v.clone())
    }
    /// `r := N % V`
    fn r_of(&self, n: &Expr, v: &Expr) -> Expr {
        self.mod_of(n.clone(), v.clone())
    }
    /// `down := q * V`
    fn down_of(&self, n: &Expr, v: &Expr) -> Expr {
        self.mul_of(self.q_of(n, v), v.clone())
    }
    /// `up := (q+1) * V`
    fn up_of(&self, n: &Expr, v: &Expr) -> Expr {
        self.mul_of(self.succ_of(self.q_of(n, v)), v.clone())
    }
    /// `twoR := 2 * r`
    fn two_r_of(&self, n: &Expr, v: &Expr) -> Expr {
        self.two_mul_of(self.r_of(n, v))
    }

    /// The body of `Nat.roundHalfEvenMod N V` — the nested `@Bool.rec` term.
    fn round_term(&self, n: &Expr, v: &Expr) -> Expr {
        let down = self.down_of(n, v);
        let up = self.up_of(n, v);
        // qEven scrutinee: beq (mod q 2) 0
        let q_even = self.beq_of(
            self.mod_of(self.q_of(n, v), self.two.clone()),
            self.zero.clone(),
        );
        // inner EVEN split: false => up, true => down
        let even_rec = self.bool_rec_nat(up.clone(), down.clone(), q_even);
        // MIDDLE split on  ble (succ V) twoR : false => even_rec, true => up
        let hi_scrut = self.ble_of(self.succ_of(v.clone()), self.two_r_of(n, v));
        let mid_rec = self.bool_rec_nat(even_rec, up, hi_scrut);
        // OUTER split on  ble (succ twoR) V : false => mid_rec, true => down
        let lo_scrut = self.ble_of(self.succ_of(self.two_r_of(n, v)), v.clone());
        self.bool_rec_nat(mid_rec, down, lo_scrut)
    }

    /// `Nat.roundHalfEvenMod N V` as a const application.
    fn round_app(&self, n: &Expr, v: &Expr) -> Expr {
        Expr::apps(Ulp::const_(names::ROUND), [n.clone(), v.clone()])
    }

    /// The EVEN-split term `@Bool.rec (fun _=>Nat) up down (beq (mod q 2) 0)`.
    fn even_rec(&self, n: &Expr, v: &Expr) -> Expr {
        let q_even = self.beq_of(
            self.mod_of(self.q_of(n, v), self.two.clone()),
            self.zero.clone(),
        );
        self.bool_rec_nat(self.up_of(n, v), self.down_of(n, v), q_even)
    }

    /// MIDDLE-nest with the inner even-split concrete but EVEN scrutinee replaced
    /// by `bEv`: `@Bool.rec (fun _=>Nat) up down bEv`.
    fn even_rec_with(&self, n: &Expr, v: &Expr, b_ev: Expr) -> Expr {
        self.bool_rec_nat(self.up_of(n, v), self.down_of(n, v), b_ev)
    }

    /// MIDDLE-nest term `@Bool.rec (fun _=>Nat) even_rec up (ble (succ V) twoR)`.
    fn mid_rec(&self, n: &Expr, v: &Expr) -> Expr {
        let hi = self.ble_of(self.succ_of(v.clone()), self.two_r_of(n, v));
        self.bool_rec_nat(self.even_rec(n, v), self.up_of(n, v), hi)
    }

    /// MIDDLE-nest with HI scrutinee replaced by `bHi`:
    /// `@Bool.rec (fun _=>Nat) even_rec up bHi`.
    fn mid_rec_with(&self, n: &Expr, v: &Expr, b_hi: Expr) -> Expr {
        self.bool_rec_nat(self.even_rec(n, v), self.up_of(n, v), b_hi)
    }

    /// OUTER round term with the LO scrutinee replaced by `bLo`:
    /// `@Bool.rec (fun _=>Nat) mid_rec down bLo`.
    fn round_with_lo(&self, n: &Expr, v: &Expr, b_lo: Expr) -> Expr {
        self.bool_rec_nat(self.mid_rec(n, v), self.down_of(n, v), b_lo)
    }

    /// `And (conj1 w) (conj2 w)` for a candidate round result `w`.
    fn bound_and(&self, w: Expr, n: &Expr, v: &Expr) -> Expr {
        let p1 = self.le_of(
            self.two_mul_of(self.sub_of(w.clone(), n.clone())),
            v.clone(),
        );
        let p2 = self.le_of(
            self.two_mul_of(self.sub_of(n.clone(), w.clone())),
            v.clone(),
        );
        self.and_of(p1, p2)
    }
}

impl Environment {
    /// `theorem succ_sub_succ (x m : Nat) : sub (succ x) (succ m) = sub x m`
    fn register_succ_sub_succ(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUCC_SUB_SUCC);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Type: ∀ (x m : Nat), @Eq Nat (sub (succ x) (succ m)) (sub x m)
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.nat.clone());
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            c.sub_of(c.succ_of(x.clone()), c.succ_of(m.clone())),
            c.sub_of(x.clone(), m.clone()),
        );
        let ty = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(x_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vx_id, vx) = vb.fresh_local(c.nat.clone());
            let (vm_id, vm) = vb.fresh_local(c.nat.clone());
            // motive: fun k => @Eq Nat (sub (succ x) (succ k)) (sub x k)
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(
                    c.sub_of(c.succ_of(vx.clone()), c.succ_of(k.clone())),
                    c.sub_of(vx.clone(), k.clone()),
                );
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let base = c.refl(c.sub_of(vx.clone(), c.zero.clone()));
            // step: fun (j ih) => congrArg Nat.pred (sub (succ x)(succ j)) (sub x j) ih
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (j_id, j) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.eq_of(
                    c.sub_of(c.succ_of(vx.clone()), c.succ_of(j.clone())),
                    c.sub_of(vx.clone(), j.clone()),
                );
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let body = c.congr_pred(
                    c.sub_of(c.succ_of(vx.clone()), c.succ_of(j.clone())),
                    c.sub_of(vx.clone(), j.clone()),
                    ih,
                );
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                sb.finish_child(sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, vm.clone());
            let lam = vb.mk_lam(vm_id, BinderInfo::Default, c.nat.clone(), rec);
            let lam = vb.mk_lam(vx_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem zero_sub (m : Nat) : sub 0 m = 0`
    fn register_zero_sub(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::ZERO_SUB);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(c.sub_of(c.zero.clone(), m.clone()), c.zero.clone());
        let ty = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), concl);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vm_id, vm) = vb.fresh_local(c.nat.clone());
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(c.sub_of(c.zero.clone(), k.clone()), c.zero.clone());
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let base = c.refl(c.sub_of(c.zero.clone(), c.zero.clone()));
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (j_id, j) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.eq_of(c.sub_of(c.zero.clone(), j.clone()), c.zero.clone());
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let body = c.congr_pred(c.sub_of(c.zero.clone(), j.clone()), c.zero.clone(), ih);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                sb.finish_child(sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, vm.clone());
            let lam = vb.mk_lam(vm_id, BinderInfo::Default, c.nat.clone(), rec);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem nmul_zero_left (n : Nat) : @Eq Nat (mul 0 n) 0`
    ///   `@Nat.rec (fun k => @Eq Nat (mul 0 k) 0) rfl (fun _ ih => ih) n`.
    fn register_nmul_zero_left(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::NMUL_ZERO_LEFT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(c.mul_of(c.zero.clone(), n.clone()), c.zero.clone());
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(c.mul_of(c.zero.clone(), k.clone()), c.zero.clone());
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let base = c.refl(c.mul_of(c.zero.clone(), c.zero.clone()));
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (j_id, _j) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.eq_of(c.mul_of(c.zero.clone(), _j.clone()), c.zero.clone());
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, ih);
                sb.finish_child(sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, vn.clone());
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), rec);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem one_mul' (x : Nat) : @Eq Nat (mul (succ 0) x) x`
    /// ```text
    /// @Eq.trans Nat (mul (succ 0) x) (add x (mul 0 x)) x
    ///   (Nat.succ_mul 0 x)
    ///   (@Eq.subst Nat (fun z => @Eq Nat (add x z) x) 0 (mul 0 x)
    ///      (Eq.symm (nmul_zero_left x)) (@Eq.refl Nat x))
    /// ```
    fn register_one_mul(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::ONE_MUL);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let succ_mul = Ulp::const_("Nat.succ_mul");
        let nmul_zero_left = Ulp::const_(names::NMUL_ZERO_LEFT);
        let one = c.succ_of(c.zero.clone());

        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(c.mul_of(one.clone(), x.clone()), x.clone());
        let ty = b.mk_pi(x_id, BinderInfo::Default, c.nat.clone(), concl);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vx_id, vx) = vb.fresh_local(c.nat.clone());
            // succ_mul 0 x : @Eq Nat (mul (succ 0) x) (add x (mul 0 x))
            let sm = Expr::apps(succ_mul.clone(), [c.zero.clone(), vx.clone()]);
            // motive: fun z => @Eq Nat (add x z) x
            let subst_motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.eq_of(c.add_of(vx.clone(), z.clone()), vx.clone());
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // nmul_zero_left x : @Eq Nat (mul 0 x) 0 ; Eq.symm : @Eq Nat 0 (mul 0 x)
            let nzl = Expr::app(nmul_zero_left.clone(), vx.clone());
            let nzl_sym = c.symm(c.mul_of(c.zero.clone(), vx.clone()), c.zero.clone(), nzl);
            let refl_x = c.refl(vx.clone());
            let inner = c.subst(
                subst_motive,
                c.zero.clone(),
                c.mul_of(c.zero.clone(), vx.clone()),
                nzl_sym,
                refl_x,
            );
            let body = c.trans(
                c.mul_of(one.clone(), vx.clone()),
                c.add_of(vx.clone(), c.mul_of(c.zero.clone(), vx.clone())),
                vx.clone(),
                sm,
                inner,
            );
            let lam = vb.mk_lam(vx_id, BinderInfo::Default, c.nat.clone(), body);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem two_mul (x : Nat) : @Eq Nat (mul 2 x) (add x x)`
    /// ```text
    /// @Eq.trans Nat (mul 2 x) (add x (mul (succ 0) x)) (add x x)
    ///   (Nat.succ_mul (succ 0) x)
    ///   (@Eq.subst Nat (fun z => @Eq Nat (add x z) (add x x))
    ///      x (mul (succ 0) x) (Eq.symm (one_mul' x)) (@Eq.refl Nat (add x x)))
    /// ```
    fn register_two_mul(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::TWO_MUL);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let succ_mul = Ulp::const_("Nat.succ_mul");
        let one_mul = Ulp::const_(names::ONE_MUL);
        let one = c.succ_of(c.zero.clone());

        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(c.two_mul_of(x.clone()), c.add_of(x.clone(), x.clone()));
        let ty = b.mk_pi(x_id, BinderInfo::Default, c.nat.clone(), concl);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vx_id, vx) = vb.fresh_local(c.nat.clone());
            // succ_mul (succ 0) x : @Eq Nat (mul 2 x) (add x (mul (succ 0) x))
            //   (2 = succ (succ 0) = succ (succ 0))
            let sm = Expr::apps(succ_mul.clone(), [one.clone(), vx.clone()]);
            // motive: fun z => @Eq Nat (add x z) (add x x)
            let subst_motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.eq_of(
                    c.add_of(vx.clone(), z.clone()),
                    c.add_of(vx.clone(), vx.clone()),
                );
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // one_mul' x : @Eq Nat (mul (succ 0) x) x ; Eq.symm : @Eq Nat x (mul (succ 0) x)
            let om = Expr::app(one_mul.clone(), vx.clone());
            let om_sym = c.symm(c.mul_of(one.clone(), vx.clone()), vx.clone(), om);
            let refl_xx = c.refl(c.add_of(vx.clone(), vx.clone()));
            let inner = c.subst(
                subst_motive,
                vx.clone(),
                c.mul_of(one.clone(), vx.clone()),
                om_sym,
                refl_xx,
            );
            let body = c.trans(
                c.two_mul_of(vx.clone()),
                c.add_of(vx.clone(), c.mul_of(one.clone(), vx.clone())),
                c.add_of(vx.clone(), vx.clone()),
                sm,
                inner,
            );
            let lam = vb.mk_lam(vx_id, BinderInfo::Default, c.nat.clone(), body);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem add_sub_self_right (b a : Nat) : @Eq Nat (sub (add b a) a) b`
    /// ```text
    /// @Nat.rec (fun k => @Eq Nat (sub (add b k) k) b) (@Eq.refl Nat b)
    ///   (fun k ih => @Eq.trans Nat (sub (add b (succ k)) (succ k)) (sub (add b k) k) b
    ///       (succ_sub_succ (add b k) k) ih) a
    /// ```
    fn register_add_sub_self_right(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::ADD_SUB_SELF_RIGHT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let succ_sub_succ = Ulp::const_(names::SUCC_SUB_SUCC);

        let mut b = EnvDeclBuilder::new();
        let (bb_id, bv) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            c.sub_of(c.add_of(bv.clone(), a.clone()), a.clone()),
            bv.clone(),
        );
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vb2_id, vbv) = vb.fresh_local(c.nat.clone());
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            // motive: fun k => @Eq Nat (sub (add b k) k) b
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(
                    c.sub_of(c.add_of(vbv.clone(), k.clone()), k.clone()),
                    vbv.clone(),
                );
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let base = c.refl(vbv.clone());
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.eq_of(
                    c.sub_of(c.add_of(vbv.clone(), k.clone()), k.clone()),
                    vbv.clone(),
                );
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                // succ_sub_succ (add b k) k : @Eq Nat (sub (add b (succ k))(succ k)) (sub (add b k) k)
                let sss = Expr::apps(
                    succ_sub_succ.clone(),
                    [c.add_of(vbv.clone(), k.clone()), k.clone()],
                );
                let body = c.trans(
                    c.sub_of(
                        c.add_of(vbv.clone(), c.succ_of(k.clone())),
                        c.succ_of(k.clone()),
                    ),
                    c.sub_of(c.add_of(vbv.clone(), k.clone()), k.clone()),
                    vbv.clone(),
                    sss,
                    ih,
                );
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, va.clone());
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), rec);
            let lam = vb.mk_lam(vb2_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem add_sub_cancel_left (a b : Nat) : @Eq Nat (sub (add a b) a) b`
    /// ```text
    /// @Eq.subst Nat (fun z => @Eq Nat (sub z a) b) (add b a) (add a b)
    ///   (Nat.add_comm b a) (add_sub_self_right b a)
    /// ```
    fn register_add_sub_cancel_left(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::ADD_SUB_CANCEL_LEFT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let add_comm = Ulp::const_("Nat.add_comm");
        let add_sub_self_right = Ulp::const_(names::ADD_SUB_SELF_RIGHT);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bv) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            c.sub_of(c.add_of(a.clone(), bv.clone()), a.clone()),
            bv.clone(),
        );
        let ty = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vb2_id, vbv) = vb.fresh_local(c.nat.clone());
            // motive: fun z => @Eq Nat (sub z a) b
            let subst_motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.eq_of(c.sub_of(z.clone(), va.clone()), vbv.clone());
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // add_comm b a : @Eq Nat (add b a) (add a b)
            let comm = Expr::apps(add_comm.clone(), [vbv.clone(), va.clone()]);
            // add_sub_self_right b a : @Eq Nat (sub (add b a) a) b
            let assr = Expr::apps(add_sub_self_right.clone(), [vbv.clone(), va.clone()]);
            let body = c.subst(
                subst_motive,
                c.add_of(vbv.clone(), va.clone()),
                c.add_of(va.clone(), vbv.clone()),
                comm,
                assr,
            );
            let lam = vb.mk_lam(vb2_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem sub_add_add_right (x y c : Nat) : @Eq Nat (sub (add x c) (add y c)) (sub x y)`
    /// Induction on `c`; step transports along `succ_sub_succ`.
    fn register_sub_add_add_right(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUB_ADD_ADD_RIGHT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let succ_sub_succ = Ulp::const_(names::SUCC_SUB_SUCC);

        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.nat.clone());
        let (y_id, y) = b.fresh_local(c.nat.clone());
        let (cc_id, cv) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            c.sub_of(
                c.add_of(x.clone(), cv.clone()),
                c.add_of(y.clone(), cv.clone()),
            ),
            c.sub_of(x.clone(), y.clone()),
        );
        let ty = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(x_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vx_id, vx) = vb.fresh_local(c.nat.clone());
            let (vy_id, vy) = vb.fresh_local(c.nat.clone());
            let (vc_id, vcv) = vb.fresh_local(c.nat.clone());
            // motive: fun k => @Eq Nat (sub (add x k) (add y k)) (sub x y)
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(
                    c.sub_of(
                        c.add_of(vx.clone(), k.clone()),
                        c.add_of(vy.clone(), k.clone()),
                    ),
                    c.sub_of(vx.clone(), vy.clone()),
                );
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let base = c.refl(c.sub_of(vx.clone(), vy.clone()));
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.eq_of(
                    c.sub_of(
                        c.add_of(vx.clone(), k.clone()),
                        c.add_of(vy.clone(), k.clone()),
                    ),
                    c.sub_of(vx.clone(), vy.clone()),
                );
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                // succ_sub_succ (add x k) (add y k)
                //   : @Eq Nat (sub (add x (succ k))(add y (succ k))) (sub (add x k)(add y k))
                let sss = Expr::apps(
                    succ_sub_succ.clone(),
                    [
                        c.add_of(vx.clone(), k.clone()),
                        c.add_of(vy.clone(), k.clone()),
                    ],
                );
                let body = c.trans(
                    c.sub_of(
                        c.add_of(vx.clone(), c.succ_of(k.clone())),
                        c.add_of(vy.clone(), c.succ_of(k.clone())),
                    ),
                    c.sub_of(
                        c.add_of(vx.clone(), k.clone()),
                        c.add_of(vy.clone(), k.clone()),
                    ),
                    c.sub_of(vx.clone(), vy.clone()),
                    sss,
                    ih,
                );
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, vcv.clone());
            let lam = vb.mk_lam(vc_id, BinderInfo::Default, c.nat.clone(), rec);
            let lam = vb.mk_lam(vy_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vx_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem sub_add_add_left (c x y : Nat) : @Eq Nat (sub (add c x) (add c y)) (sub x y)`
    /// ```text
    /// @Eq.subst Nat (fun z => @Eq Nat (sub z (add c y)) (sub x y))
    ///   (add x c) (add c x) (Nat.add_comm x c)
    ///   (@Eq.subst Nat (fun z => @Eq Nat (sub (add x c) z) (sub x y))
    ///     (add y c) (add c y) (Nat.add_comm y c) (sub_add_add_right x y c))
    /// ```
    fn register_sub_add_add_left(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUB_ADD_ADD_LEFT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let add_comm = Ulp::const_("Nat.add_comm");
        let sub_add_add_right = Ulp::const_(names::SUB_ADD_ADD_RIGHT);

        let mut b = EnvDeclBuilder::new();
        let (cc_id, cv) = b.fresh_local(c.nat.clone());
        let (x_id, x) = b.fresh_local(c.nat.clone());
        let (y_id, y) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            c.sub_of(
                c.add_of(cv.clone(), x.clone()),
                c.add_of(cv.clone(), y.clone()),
            ),
            c.sub_of(x.clone(), y.clone()),
        );
        let ty = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(x_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vc_id, vcv) = vb.fresh_local(c.nat.clone());
            let (vx_id, vx) = vb.fresh_local(c.nat.clone());
            let (vy_id, vy) = vb.fresh_local(c.nat.clone());
            // inner motive: fun z => @Eq Nat (sub (add x c) z) (sub x y)
            let inner_motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.eq_of(
                    c.sub_of(c.add_of(vx.clone(), vcv.clone()), z.clone()),
                    c.sub_of(vx.clone(), vy.clone()),
                );
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // add_comm y c : @Eq Nat (add y c) (add c y)
            let comm_yc = Expr::apps(add_comm.clone(), [vy.clone(), vcv.clone()]);
            // sub_add_add_right x y c : @Eq Nat (sub (add x c)(add y c)) (sub x y)
            let saar = Expr::apps(
                sub_add_add_right.clone(),
                [vx.clone(), vy.clone(), vcv.clone()],
            );
            let inner = c.subst(
                inner_motive,
                c.add_of(vy.clone(), vcv.clone()),
                c.add_of(vcv.clone(), vy.clone()),
                comm_yc,
                saar,
            );
            // outer motive: fun z => @Eq Nat (sub z (add c y)) (sub x y)
            let outer_motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.eq_of(
                    c.sub_of(z.clone(), c.add_of(vcv.clone(), vy.clone())),
                    c.sub_of(vx.clone(), vy.clone()),
                );
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // add_comm x c : @Eq Nat (add x c) (add c x)
            let comm_xc = Expr::apps(add_comm.clone(), [vx.clone(), vcv.clone()]);
            let body = c.subst(
                outer_motive,
                c.add_of(vx.clone(), vcv.clone()),
                c.add_of(vcv.clone(), vx.clone()),
                comm_xc,
                inner,
            );
            let lam = vb.mk_lam(vy_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(vx_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vc_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem sub_eq_zero_of_le (a b : Nat) (h : Nat.le a b) : @Eq Nat (sub a b) 0`
    /// Double induction: outer on `a` generalized over `b`; inner on `b`.
    fn register_sub_eq_zero_of_le(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUB_EQ_ZERO_OF_LE);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero_sub = Ulp::const_(names::ZERO_SUB);
        let succ_sub_succ = Ulp::const_(names::SUCC_SUB_SUCC);
        let not_succ_le_zero = Ulp::const_("Nat.not_succ_le_zero");
        let le_of_succ_le_succ = Ulp::const_("Nat.le_of_succ_le_succ");

        // Type: ∀ (a b : Nat), Nat.le a b -> @Eq Nat (sub a b) 0
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bv) = b.fresh_local(c.nat.clone());
        let h_ty = c.le_of(a.clone(), bv.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.eq_of(c.sub_of(a.clone(), bv.clone()), c.zero.clone());
        let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let ty = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vb2_id, vbv) = vb.fresh_local(c.nat.clone());
            let (vh_id, vh) = vb.fresh_local(c.le_of(va.clone(), vbv.clone()));

            // outer motive: fun k => ∀ (m : Nat), Nat.le k m -> @Eq Nat (sub k m) 0
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let inner = {
                    let mut ib = EnvDeclBuilder::child_of(&mb);
                    let (m_id, m) = ib.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(k.clone(), m.clone()),
                        c.eq_of(c.sub_of(k.clone(), m.clone()), c.zero.clone()),
                    );
                    ib.finish_child(ib.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // base (k=0): fun (m : Nat) (_hm : le 0 m) => zero_sub m
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (m_id, m) = bb.fresh_local(c.nat.clone());
                let hm_ty = c.le_of(c.zero.clone(), m.clone());
                let (hm_id, _hm) = bb.fresh_local(hm_ty.clone());
                let body = Expr::app(zero_sub.clone(), m.clone());
                let lam = bb.mk_lam(hm_id, BinderInfo::Default, hm_ty, body);
                bb.finish_child(bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // step (k=succ a'): fun (a' : Nat) (ih : motive a') => fun (m : Nat) =>
            //   @Nat.rec inner_motive izcase iscase m
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (ap_id, ap) = sb.fresh_local(c.nat.clone());
                let ih_ty = {
                    let mut ihb = EnvDeclBuilder::child_of(&sb);
                    let (m_id, m) = ihb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(ap.clone(), m.clone()),
                        c.eq_of(c.sub_of(ap.clone(), m.clone()), c.zero.clone()),
                    );
                    ihb.finish_child(ihb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (m_id, m) = sb.fresh_local(c.nat.clone());

                // inner motive: fun mm => le (succ a') mm -> @Eq Nat (sub (succ a') mm) 0
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (mm_id, mm) = imb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(c.succ_of(ap.clone()), mm.clone()),
                        c.eq_of(c.sub_of(c.succ_of(ap.clone()), mm.clone()), c.zero.clone()),
                    );
                    imb.finish_child(imb.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // izcase (mm=0): fun (h0 : le (succ a') 0) =>
                //   @False.elim (@Eq Nat (sub (succ a') 0) 0) (Nat.not_succ_le_zero a' h0)
                let izcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let h0_ty = c.le_of(c.succ_of(ap.clone()), c.zero.clone());
                    let (h0_id, h0) = zb.fresh_local(h0_ty.clone());
                    let goal = c.eq_of(
                        c.sub_of(c.succ_of(ap.clone()), c.zero.clone()),
                        c.zero.clone(),
                    );
                    let false_pf = Expr::apps(not_succ_le_zero.clone(), [ap.clone(), h0]);
                    let body = c.false_elim(goal, false_pf);
                    zb.finish_child(zb.mk_lam(h0_id, BinderInfo::Default, h0_ty, body))
                };

                // iscase (mm=succ m'): fun (m' : Nat) (_ihm : inner_motive m')
                //     (hm : le (succ a')(succ m')) =>
                //   @Eq.subst Nat (fun z => @Eq Nat z 0)
                //     (sub a' m') (sub (succ a')(succ m')) (Eq.symm (succ_sub_succ a' m'))
                //     (ih m' (Nat.le_of_succ_le_succ a' m' hm))
                let iscase = {
                    let mut nb = EnvDeclBuilder::child_of(&sb);
                    let (mp_id, mp) = nb.fresh_local(c.nat.clone());
                    let ihm_ty = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(c.succ_of(ap.clone()), mp.clone()),
                        c.eq_of(c.sub_of(c.succ_of(ap.clone()), mp.clone()), c.zero.clone()),
                    );
                    let (ihm_id, _ihm) = nb.fresh_local(ihm_ty.clone());
                    let hm_ty = c.le_of(c.succ_of(ap.clone()), c.succ_of(mp.clone()));
                    let (hm_id, hm) = nb.fresh_local(hm_ty.clone());
                    // motive: fun z => @Eq Nat z 0
                    let eqz_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&nb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.eq_of(z.clone(), c.zero.clone());
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // succ_sub_succ a' m' : @Eq Nat (sub (succ a')(succ m')) (sub a' m')
                    let sss = Expr::apps(succ_sub_succ.clone(), [ap.clone(), mp.clone()]);
                    let sss_sym = c.symm(
                        c.sub_of(c.succ_of(ap.clone()), c.succ_of(mp.clone())),
                        c.sub_of(ap.clone(), mp.clone()),
                        sss,
                    );
                    // le_of_succ_le_succ a' m' hm : le a' m'
                    let loss = Expr::apps(le_of_succ_le_succ.clone(), [ap.clone(), mp.clone(), hm]);
                    // ih m' loss : @Eq Nat (sub a' m') 0
                    let ih_app = Expr::apps(ih.clone(), [mp.clone(), loss]);
                    let body = c.subst(
                        eqz_motive,
                        c.sub_of(ap.clone(), mp.clone()),
                        c.sub_of(c.succ_of(ap.clone()), c.succ_of(mp.clone())),
                        sss_sym,
                        ih_app,
                    );
                    let lam = nb.mk_lam(hm_id, BinderInfo::Default, hm_ty, body);
                    let lam = nb.mk_lam(ihm_id, BinderInfo::Default, ihm_ty, lam);
                    nb.finish_child(nb.mk_lam(mp_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                let inner_rec = c.rec0(inner_motive, izcase, iscase, m.clone());
                let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), inner_rec);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // @Nat.rec.{0} motive base step a  then apply  b  then  h
            let rec = c.rec0(motive, base, step, va.clone());
            let body = Expr::apps(rec, [vbv.clone(), vh.clone()]);
            let lam = vb.mk_lam(
                vh_id,
                BinderInfo::Default,
                c.le_of(va.clone(), vbv.clone()),
                body,
            );
            let lam = vb.mk_lam(vb2_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem sub_add_cancel (a n : Nat) (h : Nat.le n a) : @Eq Nat (add (sub a n) n) a`
    /// Double induction: outer on `n` generalized over `a`; inner on `a`.
    fn register_sub_add_cancel(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUB_ADD_CANCEL);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let succ_sub_succ = Ulp::const_(names::SUCC_SUB_SUCC);
        let not_succ_le_zero = Ulp::const_("Nat.not_succ_le_zero");
        let le_of_succ_le_succ = Ulp::const_("Nat.le_of_succ_le_succ");

        // Type: ∀ (a n : Nat), Nat.le n a -> @Eq Nat (add (sub a n) n) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let h_ty = c.le_of(n.clone(), a.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.eq_of(
            c.add_of(c.sub_of(a.clone(), n.clone()), n.clone()),
            a.clone(),
        );
        let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vh_id, vh) = vb.fresh_local(c.le_of(vn.clone(), va.clone()));

            // outer motive: fun k => ∀ (m : Nat), Nat.le k m -> @Eq Nat (add (sub m k) k) m
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let inner = {
                    let mut ib = EnvDeclBuilder::child_of(&mb);
                    let (m_id, m) = ib.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(k.clone(), m.clone()),
                        c.eq_of(
                            c.add_of(c.sub_of(m.clone(), k.clone()), k.clone()),
                            m.clone(),
                        ),
                    );
                    ib.finish_child(ib.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // base (k=0): fun (m : Nat) (_hm : Nat.le 0 m) => @Eq.refl Nat m
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (m_id, m) = bb.fresh_local(c.nat.clone());
                let hm_ty = c.le_of(c.zero.clone(), m.clone());
                let (hm_id, _hm) = bb.fresh_local(hm_ty.clone());
                let body = c.refl(m.clone());
                let lam = bb.mk_lam(hm_id, BinderInfo::Default, hm_ty, body);
                bb.finish_child(bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // step (k=succ n'): fun (n' : Nat) (ih : motive n') => fun (m : Nat) =>
            //   @Nat.rec inner_motive izcase iscase m
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (np_id, np) = sb.fresh_local(c.nat.clone());
                let ih_ty = {
                    let mut ihb = EnvDeclBuilder::child_of(&sb);
                    let (m_id, m) = ihb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(np.clone(), m.clone()),
                        c.eq_of(
                            c.add_of(c.sub_of(m.clone(), np.clone()), np.clone()),
                            m.clone(),
                        ),
                    );
                    ihb.finish_child(ihb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (m_id, m) = sb.fresh_local(c.nat.clone());

                // inner motive: fun mm => le (succ n') mm ->
                //   @Eq Nat (add (sub mm (succ n'))(succ n')) mm
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (mm_id, mm) = imb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(c.succ_of(np.clone()), mm.clone()),
                        c.eq_of(
                            c.add_of(
                                c.sub_of(mm.clone(), c.succ_of(np.clone())),
                                c.succ_of(np.clone()),
                            ),
                            mm.clone(),
                        ),
                    );
                    imb.finish_child(imb.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // izcase (mm=0): fun (h0 : le (succ n') 0) =>
                //   @False.elim (@Eq Nat (add (sub 0 (succ n'))(succ n')) 0)
                //     (Nat.not_succ_le_zero n' h0)
                let izcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let h0_ty = c.le_of(c.succ_of(np.clone()), c.zero.clone());
                    let (h0_id, h0) = zb.fresh_local(h0_ty.clone());
                    let goal = c.eq_of(
                        c.add_of(
                            c.sub_of(c.zero.clone(), c.succ_of(np.clone())),
                            c.succ_of(np.clone()),
                        ),
                        c.zero.clone(),
                    );
                    let false_pf = Expr::apps(not_succ_le_zero.clone(), [np.clone(), h0]);
                    let body = c.false_elim(goal, false_pf);
                    zb.finish_child(zb.mk_lam(h0_id, BinderInfo::Default, h0_ty, body))
                };

                // iscase (mm=succ a'): fun (a' : Nat) (_iha : inner_motive a')
                //     (ha' : le (succ n')(succ a')) =>
                //   @Eq.subst Nat (fun z => @Eq Nat (add z (succ n')) (succ a'))
                //     (sub a' n') (sub (succ a')(succ n')) (Eq.symm (succ_sub_succ a' n'))
                //     (congrArg succ (ih a' (Nat.le_of_succ_le_succ n' a' ha')))
                let iscase = {
                    let mut ab = EnvDeclBuilder::child_of(&sb);
                    let (ap_id, ap) = ab.fresh_local(c.nat.clone());
                    let iha_ty = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(c.succ_of(np.clone()), ap.clone()),
                        c.eq_of(
                            c.add_of(
                                c.sub_of(ap.clone(), c.succ_of(np.clone())),
                                c.succ_of(np.clone()),
                            ),
                            ap.clone(),
                        ),
                    );
                    let (iha_id, _iha) = ab.fresh_local(iha_ty.clone());
                    let ha_ty = c.le_of(c.succ_of(np.clone()), c.succ_of(ap.clone()));
                    let (ha_id, ha) = ab.fresh_local(ha_ty.clone());

                    let subst_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&ab);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.eq_of(
                            c.add_of(z.clone(), c.succ_of(np.clone())),
                            c.succ_of(ap.clone()),
                        );
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // le_of_succ_le_succ n' a' ha' : le n' a'
                    let loss = Expr::apps(le_of_succ_le_succ.clone(), [np.clone(), ap.clone(), ha]);
                    // ih a' loss : @Eq Nat (add (sub a' n') n') a'
                    let ih_app = Expr::apps(ih.clone(), [ap.clone(), loss]);
                    // congrArg succ : @Eq Nat (succ (add (sub a' n') n')) (succ a')
                    let cg = c.congr_succ(
                        c.add_of(c.sub_of(ap.clone(), np.clone()), np.clone()),
                        ap.clone(),
                        ih_app,
                    );
                    let sss = Expr::apps(succ_sub_succ.clone(), [ap.clone(), np.clone()]);
                    let sss_sym = c.symm(
                        c.sub_of(c.succ_of(ap.clone()), c.succ_of(np.clone())),
                        c.sub_of(ap.clone(), np.clone()),
                        sss,
                    );
                    let body = c.subst(
                        subst_motive,
                        c.sub_of(ap.clone(), np.clone()),
                        c.sub_of(c.succ_of(ap.clone()), c.succ_of(np.clone())),
                        sss_sym,
                        cg,
                    );
                    let lam = ab.mk_lam(ha_id, BinderInfo::Default, ha_ty, body);
                    let lam = ab.mk_lam(iha_id, BinderInfo::Default, iha_ty, lam);
                    ab.finish_child(ab.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                let inner_rec = c.rec0(inner_motive, izcase, iscase, m.clone());
                let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), inner_rec);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // @Nat.rec.{0} motive base step n  then apply  a  then  h
            let rec = c.rec0(motive, base, step, vn.clone());
            let body = Expr::apps(rec, [va.clone(), vh.clone()]);
            let lam = vb.mk_lam(
                vh_id,
                BinderInfo::Default,
                c.le_of(vn.clone(), va.clone()),
                body,
            );
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem le_of_add_le_add_right (a b k : Nat) (h : le (add a k) (add b k)) : le a b`
    /// ```text
    /// @Nat.rec (fun kk => Nat.le (add a kk) (add b kk) -> Nat.le a b)
    ///   (fun h0 => h0)
    ///   (fun k' ih => fun hs => ih (Nat.le_of_succ_le_succ (add a k') (add b k') hs))
    ///   k h
    /// ```
    fn register_le_of_add_le_add_right(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::LE_OF_ADD_LE_ADD_RIGHT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let le_of_succ_le_succ = Ulp::const_("Nat.le_of_succ_le_succ");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bv) = b.fresh_local(c.nat.clone());
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let h_ty = c.le_of(
            c.add_of(a.clone(), k.clone()),
            c.add_of(bv.clone(), k.clone()),
        );
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.le_of(a.clone(), bv.clone());
        let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let ty = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vb2_id, vbv) = vb.fresh_local(c.nat.clone());
            let (vk_id, vk) = vb.fresh_local(c.nat.clone());
            let (vh_id, vh) = vb.fresh_local(c.le_of(
                c.add_of(va.clone(), vk.clone()),
                c.add_of(vbv.clone(), vk.clone()),
            ));

            // motive: fun kk => Nat.le (add a kk) (add b kk) -> Nat.le a b
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (kk_id, kk) = mb.fresh_local(c.nat.clone());
                let body = Expr::pi(
                    BinderInfo::Default,
                    c.le_of(
                        c.add_of(va.clone(), kk.clone()),
                        c.add_of(vbv.clone(), kk.clone()),
                    ),
                    c.le_of(va.clone(), vbv.clone()),
                );
                mb.finish_child(mb.mk_lam(kk_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base (kk=0): fun (h0 : le (add a 0)(add b 0)) => h0
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let h0_ty = c.le_of(
                    c.add_of(va.clone(), c.zero.clone()),
                    c.add_of(vbv.clone(), c.zero.clone()),
                );
                let (h0_id, h0) = bb.fresh_local(h0_ty.clone());
                bb.finish_child(bb.mk_lam(h0_id, BinderInfo::Default, h0_ty, h0))
            };

            // step (kk=succ k'): fun (k' : Nat) (_ih : motive k') =>
            //   fun (hs : le (add a (succ k'))(add b (succ k'))) =>
            //     _ih (Nat.le_of_succ_le_succ (add a k') (add b k') hs)
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (kp_id, kp) = sb.fresh_local(c.nat.clone());
                let ih_ty = Expr::pi(
                    BinderInfo::Default,
                    c.le_of(
                        c.add_of(va.clone(), kp.clone()),
                        c.add_of(vbv.clone(), kp.clone()),
                    ),
                    c.le_of(va.clone(), vbv.clone()),
                );
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let hs_ty = c.le_of(
                    c.add_of(va.clone(), c.succ_of(kp.clone())),
                    c.add_of(vbv.clone(), c.succ_of(kp.clone())),
                );
                let (hs_id, hs) = sb.fresh_local(hs_ty.clone());
                // le_of_succ_le_succ (add a k') (add b k') hs : le (add a k')(add b k')
                //   (succ (add a k') ≡ add a (succ k') ; same for b)
                let loss = Expr::apps(
                    le_of_succ_le_succ.clone(),
                    [
                        c.add_of(va.clone(), kp.clone()),
                        c.add_of(vbv.clone(), kp.clone()),
                        hs,
                    ],
                );
                let body = Expr::app(ih.clone(), loss);
                let lam = sb.mk_lam(hs_id, BinderInfo::Default, hs_ty, body);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            let rec = c.rec0(motive, base, step, vk.clone());
            let body = Expr::app(rec, vh.clone());
            let lam = vb.mk_lam(
                vh_id,
                BinderInfo::Default,
                c.le_of(
                    c.add_of(va.clone(), vk.clone()),
                    c.add_of(vbv.clone(), vk.clone()),
                ),
                body,
            );
            let lam = vb.mk_lam(vk_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vb2_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem ble_succ_false_le (a b : Nat) (h : @Eq Bool (ble (succ a) b) Bool.false) : Nat.le b a`
    /// Double induction: outer on `b` generalized over `a`; inner on `a`.
    /// ```text
    /// @Nat.rec (fun bb => ∀ (aa : Nat), @Eq Bool (ble (succ aa) bb) Bool.false -> Nat.le bb aa)
    ///   (fun aa _h0 => Nat.zero_le aa)
    ///   (fun b' ih => fun aa =>
    ///     @Nat.rec (fun aaa => @Eq Bool (ble (succ aaa)(succ b')) Bool.false -> Nat.le (succ b') aaa)
    ///       (fun hcon => @False.elim (Nat.le (succ b') 0)
    ///           (@Bool.noConfusion False (ble 0 b') Bool.false hcon))
    ///       (fun a' _iha ha => Nat.succ_le_succ b' a' (ih a' ha))
    ///       aa)
    ///   b a h
    /// ```
    fn register_ble_succ_false_le(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::BLE_SUCC_FALSE_LE);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero_le = Ulp::const_("Nat.zero_le");
        let succ_le_succ = Ulp::const_("Nat.succ_le_succ");
        let false_c = Ulp::const_("False");

        // Type: ∀ (a b : Nat), @Eq Bool (ble (succ a) b) Bool.false -> Nat.le b a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bv) = b.fresh_local(c.nat.clone());
        let h_ty = c.eq_bool_of(c.ble_of(c.succ_of(a.clone()), bv.clone()), c.bfalse.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.le_of(bv.clone(), a.clone());
        let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let ty = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vb2_id, vbv) = vb.fresh_local(c.nat.clone());
            let (vh_id, vh) = vb.fresh_local(c.eq_bool_of(
                c.ble_of(c.succ_of(va.clone()), vbv.clone()),
                c.bfalse.clone(),
            ));

            // outer motive: fun bb => ∀ (aa : Nat),
            //   @Eq Bool (ble (succ aa) bb) Bool.false -> Nat.le bb aa
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (bk_id, bk) = mb.fresh_local(c.nat.clone());
                let inner = {
                    let mut ib = EnvDeclBuilder::child_of(&mb);
                    let (aa_id, aa) = ib.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.eq_bool_of(
                            c.ble_of(c.succ_of(aa.clone()), bk.clone()),
                            c.bfalse.clone(),
                        ),
                        c.le_of(bk.clone(), aa.clone()),
                    );
                    ib.finish_child(ib.mk_pi(aa_id, BinderInfo::Default, c.nat.clone(), body))
                };
                mb.finish_child(mb.mk_lam(bk_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // base (bb=0): fun (aa : Nat) (_h0 : ...) => Nat.zero_le aa
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (aa_id, aa) = bb.fresh_local(c.nat.clone());
                let h0_ty = c.eq_bool_of(
                    c.ble_of(c.succ_of(aa.clone()), c.zero.clone()),
                    c.bfalse.clone(),
                );
                let (h0_id, _h0) = bb.fresh_local(h0_ty.clone());
                let body = Expr::app(zero_le.clone(), aa.clone());
                let lam = bb.mk_lam(h0_id, BinderInfo::Default, h0_ty, body);
                bb.finish_child(bb.mk_lam(aa_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // step (bb=succ b'): fun (b' : Nat) (ih : motive b') => fun (aa : Nat) =>
            //   @Nat.rec inner_motive izcase iscase aa
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (bp_id, bp) = sb.fresh_local(c.nat.clone());
                let ih_ty = {
                    let mut ihb = EnvDeclBuilder::child_of(&sb);
                    let (aa_id, aa) = ihb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.eq_bool_of(
                            c.ble_of(c.succ_of(aa.clone()), bp.clone()),
                            c.bfalse.clone(),
                        ),
                        c.le_of(bp.clone(), aa.clone()),
                    );
                    ihb.finish_child(ihb.mk_pi(aa_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (aa_id, aa) = sb.fresh_local(c.nat.clone());

                // inner motive: fun aaa =>
                //   @Eq Bool (ble (succ aaa)(succ b')) Bool.false -> Nat.le (succ b') aaa
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (aaa_id, aaa) = imb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.eq_bool_of(
                            c.ble_of(c.succ_of(aaa.clone()), c.succ_of(bp.clone())),
                            c.bfalse.clone(),
                        ),
                        c.le_of(c.succ_of(bp.clone()), aaa.clone()),
                    );
                    imb.finish_child(imb.mk_lam(aaa_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // izcase (aaa=0): fun (hcon : @Eq Bool (ble (succ 0)(succ b')) false) =>
                //   @False.elim (Nat.le (succ b') 0)
                //     (@Bool.noConfusion False (ble 0 b') Bool.false hcon)
                let izcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let hcon_ty = c.eq_bool_of(
                        c.ble_of(c.succ_of(c.zero.clone()), c.succ_of(bp.clone())),
                        c.bfalse.clone(),
                    );
                    let (hcon_id, hcon) = zb.fresh_local(hcon_ty.clone());
                    let goal = c.le_of(c.succ_of(bp.clone()), c.zero.clone());
                    // @Bool.noConfusion.{0} False (ble 0 b') Bool.false hcon
                    //   (ble (succ 0)(succ b') ≡ ble 0 b' ≡ true ; noConfusionType ⇒ False)
                    let nc = c.noconf(
                        false_c.clone(),
                        c.ble_of(c.zero.clone(), bp.clone()),
                        c.bfalse.clone(),
                        hcon,
                    );
                    let body = c.false_elim(goal, nc);
                    zb.finish_child(zb.mk_lam(hcon_id, BinderInfo::Default, hcon_ty, body))
                };

                // iscase (aaa=succ a'): fun (a' : Nat) (_iha : inner_motive a')
                //     (ha : @Eq Bool (ble (succ (succ a'))(succ b')) false) =>
                //   Nat.succ_le_succ b' a' (ih a' ha)
                let iscase = {
                    let mut ab = EnvDeclBuilder::child_of(&sb);
                    let (ap_id, ap) = ab.fresh_local(c.nat.clone());
                    let iha_ty = Expr::pi(
                        BinderInfo::Default,
                        c.eq_bool_of(
                            c.ble_of(c.succ_of(ap.clone()), c.succ_of(bp.clone())),
                            c.bfalse.clone(),
                        ),
                        c.le_of(c.succ_of(bp.clone()), ap.clone()),
                    );
                    let (iha_id, _iha) = ab.fresh_local(iha_ty.clone());
                    let ha_ty = c.eq_bool_of(
                        c.ble_of(c.succ_of(c.succ_of(ap.clone())), c.succ_of(bp.clone())),
                        c.bfalse.clone(),
                    );
                    let (ha_id, ha) = ab.fresh_local(ha_ty.clone());
                    // ih a' ha : Nat.le b' a'   (ble (succ a')(succ b') ≡ ble (succ(succ a'))... ? )
                    //   The Lean term is `ih a' ha`; ha's type is the inner_motive-shaped
                    //   hyp ble (succ (succ a'))(succ b') = false, which ih a' expects as
                    //   ble (succ a') b' = false. These are defeq (ble succ-succ ≡ ble).
                    let ih_app = Expr::apps(ih.clone(), [ap.clone(), ha]);
                    let body = Expr::apps(succ_le_succ.clone(), [bp.clone(), ap.clone(), ih_app]);
                    let lam = ab.mk_lam(ha_id, BinderInfo::Default, ha_ty, body);
                    let lam = ab.mk_lam(iha_id, BinderInfo::Default, iha_ty, lam);
                    ab.finish_child(ab.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                let inner_rec = c.rec0(inner_motive, izcase, iscase, aa.clone());
                let lam = sb.mk_lam(aa_id, BinderInfo::Default, c.nat.clone(), inner_rec);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(bp_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // @Nat.rec.{0} motive base step b  then apply  a  then  h
            let rec = c.rec0(motive, base, step, vbv.clone());
            let body = Expr::apps(rec, [va.clone(), vh.clone()]);
            let lam = vb.mk_lam(
                vh_id,
                BinderInfo::Default,
                c.eq_bool_of(
                    c.ble_of(c.succ_of(va.clone()), vbv.clone()),
                    c.bfalse.clone(),
                ),
                body,
            );
            let lam = vb.mk_lam(vb2_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem N_sub_down (N V : Nat) : @Eq Nat (sub N (mul (div N V) V)) (mod N V)`
    /// ```text
    /// @Eq.subst Nat (fun z => @Eq Nat (sub z (mul (div N V) V)) (mod N V))
    ///   (add (mul (div N V) V) (mod N V)) N
    ///   (Nat.div_add_mod N V)
    ///   (add_sub_cancel_left (mul (div N V) V) (mod N V))
    /// ```
    fn register_n_sub_down(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::N_SUB_DOWN);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let div_add_mod = Ulp::const_("Nat.div_add_mod");
        let add_sub_cancel_left = Ulp::const_(names::ADD_SUB_CANCEL_LEFT);

        let mut b = EnvDeclBuilder::new();
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(c.sub_of(nn.clone(), c.down_of(&nn, &v)), c.r_of(&nn, &v));
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let down = c.down_of(&vn, &vv);
            let r = c.r_of(&vn, &vv);
            // motive: fun z => @Eq Nat (sub z down) r
            let subst_motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.eq_of(c.sub_of(z.clone(), down.clone()), r.clone());
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // div_add_mod N V : @Eq Nat (add down r) N
            let dam = Expr::apps(div_add_mod.clone(), [vn.clone(), vv.clone()]);
            // add_sub_cancel_left down r : @Eq Nat (sub (add down r) down) r
            let ascl = Expr::apps(add_sub_cancel_left.clone(), [down.clone(), r.clone()]);
            let body = c.subst(
                subst_motive,
                c.add_of(down.clone(), r.clone()),
                vn.clone(),
                dam,
                ascl,
            );
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem down_le_N (N V : Nat) : Nat.le (mul (div N V) V) N`
    /// ```text
    /// @Eq.subst Nat (fun z => Nat.le (mul (div N V) V) z)
    ///   (add (mul (div N V) V) (mod N V)) N (Nat.div_add_mod N V)
    ///   (Nat.le_add_right (mul (div N V) V) (mod N V))
    /// ```
    fn register_down_le_n(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::DOWN_LE_N);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let div_add_mod = Ulp::const_("Nat.div_add_mod");
        let le_add_right = Ulp::const_("Nat.le_add_right");

        let mut b = EnvDeclBuilder::new();
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let concl = c.le_of(c.down_of(&nn, &v), nn.clone());
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let down = c.down_of(&vn, &vv);
            let r = c.r_of(&vn, &vv);
            let subst_motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.le_of(down.clone(), z.clone());
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let dam = Expr::apps(div_add_mod.clone(), [vn.clone(), vv.clone()]);
            // le_add_right down r : Nat.le down (add down r)
            let lar = Expr::apps(le_add_right.clone(), [down.clone(), r.clone()]);
            let body = c.subst(
                subst_motive,
                c.add_of(down.clone(), r.clone()),
                vn.clone(),
                dam,
                lar,
            );
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem down_sub_N (N V : Nat) : @Eq Nat (sub (mul (div N V) V) N) 0`
    ///   `:= sub_eq_zero_of_le (mul (div N V) V) N (down_le_N N V)`
    fn register_down_sub_n(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::DOWN_SUB_N);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let sub_eq_zero_of_le = Ulp::const_(names::SUB_EQ_ZERO_OF_LE);
        let down_le_n = Ulp::const_(names::DOWN_LE_N);

        let mut b = EnvDeclBuilder::new();
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(c.sub_of(c.down_of(&nn, &v), nn.clone()), c.zero.clone());
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let down = c.down_of(&vn, &vv);
            let dle = Expr::apps(down_le_n.clone(), [vn.clone(), vv.clone()]);
            let body = Expr::apps(sub_eq_zero_of_le.clone(), [down.clone(), vn.clone(), dle]);
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem up_sub_N (N V : Nat) : @Eq Nat (sub (mul (succ (div N V)) V) N) (sub V (mod N V))`
    /// (the chained-subst proof from the Lean source).
    fn register_up_sub_n(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::UP_SUB_N);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let succ_mul = Ulp::const_("Nat.succ_mul");
        let add_comm = Ulp::const_("Nat.add_comm");
        let div_add_mod = Ulp::const_("Nat.div_add_mod");
        let sub_add_add_left = Ulp::const_(names::SUB_ADD_ADD_LEFT);

        let mut b = EnvDeclBuilder::new();
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            c.sub_of(c.up_of(&nn, &v), nn.clone()),
            c.sub_of(v.clone(), c.r_of(&nn, &v)),
        );
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let q = c.q_of(&vn, &vv);
            let down = c.down_of(&vn, &vv); // mul q V
            let up = c.up_of(&vn, &vv); // mul (succ q) V
            let r = c.r_of(&vn, &vv);
            let target_rhs = c.sub_of(vv.clone(), r.clone());

            // innermost: @Eq.subst Nat (fun z => @Eq Nat (sub (add down V) z) (sub V r))
            //   (add down r) N (Nat.div_add_mod N V)
            //   (sub_add_add_left down V r)
            let innermost = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.eq_of(
                        c.sub_of(c.add_of(down.clone(), vv.clone()), z.clone()),
                        target_rhs.clone(),
                    );
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let dam = Expr::apps(div_add_mod.clone(), [vn.clone(), vv.clone()]);
                // sub_add_add_left down V r : @Eq Nat (sub (add down V)(add down r)) (sub V r)
                let saal = Expr::apps(
                    sub_add_add_left.clone(),
                    [down.clone(), vv.clone(), r.clone()],
                );
                c.subst(
                    motive,
                    c.add_of(down.clone(), r.clone()),
                    vn.clone(),
                    dam,
                    saal,
                )
            };

            // middle: @Eq.subst Nat (fun z => @Eq Nat (sub z N) (sub V r))
            //   (add down V) (add V down) (Nat.add_comm down V) innermost
            let middle = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.eq_of(c.sub_of(z.clone(), vn.clone()), target_rhs.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let comm = Expr::apps(add_comm.clone(), [down.clone(), vv.clone()]);
                c.subst(
                    motive,
                    c.add_of(down.clone(), vv.clone()),
                    c.add_of(vv.clone(), down.clone()),
                    comm,
                    innermost,
                )
            };

            // outer: @Eq.subst Nat (fun z => @Eq Nat (sub z N) (sub V r))
            //   (add V down) up (Eq.symm (Nat.succ_mul q V)) middle
            let body = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.eq_of(c.sub_of(z.clone(), vn.clone()), target_rhs.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                // succ_mul q V : @Eq Nat (mul (succ q) V) (add V (mul q V)) = @Eq Nat up (add V down)
                let sm = Expr::apps(succ_mul.clone(), [q.clone(), vv.clone()]);
                let sm_sym = c.symm(up.clone(), c.add_of(vv.clone(), down.clone()), sm);
                c.subst(
                    motive,
                    c.add_of(vv.clone(), down.clone()),
                    up.clone(),
                    sm_sym,
                    middle,
                )
            };

            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem N_le_up (N V : Nat) (hr : Nat.le (mod N V) V) : Nat.le N (mul (succ (div N V)) V)`
    fn register_n_le_up(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::N_LE_UP);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let succ_mul = Ulp::const_("Nat.succ_mul");
        let add_comm = Ulp::const_("Nat.add_comm");
        let div_add_mod = Ulp::const_("Nat.div_add_mod");
        let add_le_add_left = Ulp::const_("Nat.add_le_add_left");

        let mut b = EnvDeclBuilder::new();
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let hr_ty = c.le_of(c.r_of(&nn, &v), v.clone());
        let (hr_id, _hr) = b.fresh_local(hr_ty.clone());
        let concl = c.le_of(nn.clone(), c.up_of(&nn, &v));
        let ty = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, concl);
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let hr_ty2 = c.le_of(c.r_of(&vn, &vv), vv.clone());
            let (vhr_id, vhr) = vb.fresh_local(hr_ty2.clone());
            let q = c.q_of(&vn, &vv);
            let down = c.down_of(&vn, &vv);
            let up = c.up_of(&vn, &vv);
            let r = c.r_of(&vn, &vv);

            // inner: @Eq.subst Nat (fun z => Nat.le z (add down V))
            //   (add down r) N (Nat.div_add_mod N V)
            //   (Nat.add_le_add_left r V hr down)
            let inner = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(z.clone(), c.add_of(down.clone(), vv.clone()));
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let dam = Expr::apps(div_add_mod.clone(), [vn.clone(), vv.clone()]);
                // add_le_add_left r V hr down : Nat.le (add down r) (add down V)
                let alal = Expr::apps(
                    add_le_add_left.clone(),
                    [r.clone(), vv.clone(), vhr.clone(), down.clone()],
                );
                c.subst(
                    motive,
                    c.add_of(down.clone(), r.clone()),
                    vn.clone(),
                    dam,
                    alal,
                )
            };

            // outer subst h: @Eq.trans Nat (add down V) (add V down) up
            //   (Nat.add_comm down V) (Eq.symm (Nat.succ_mul q V))
            let trans_h = {
                let comm = Expr::apps(add_comm.clone(), [down.clone(), vv.clone()]);
                let sm = Expr::apps(succ_mul.clone(), [q.clone(), vv.clone()]);
                let sm_sym = c.symm(up.clone(), c.add_of(vv.clone(), down.clone()), sm);
                c.trans(
                    c.add_of(down.clone(), vv.clone()),
                    c.add_of(vv.clone(), down.clone()),
                    up.clone(),
                    comm,
                    sm_sym,
                )
            };

            // @Eq.subst Nat (fun z => Nat.le N z) (add down V) up trans_h inner
            let motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.le_of(vn.clone(), z.clone());
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let body = c.subst(
                motive,
                c.add_of(down.clone(), vv.clone()),
                up.clone(),
                trans_h,
                inner,
            );
            let lam = vb.mk_lam(vhr_id, BinderInfo::Default, hr_ty2, body);
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem N_sub_up (N V : Nat) (hr : Nat.le (mod N V) V) : @Eq Nat (sub N (mul (succ (div N V)) V)) 0`
    ///   `:= sub_eq_zero_of_le N up (N_le_up N V hr)`
    fn register_n_sub_up(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::N_SUB_UP);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let sub_eq_zero_of_le = Ulp::const_(names::SUB_EQ_ZERO_OF_LE);
        let n_le_up = Ulp::const_(names::N_LE_UP);

        let mut b = EnvDeclBuilder::new();
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let hr_ty = c.le_of(c.r_of(&nn, &v), v.clone());
        let (hr_id, _hr) = b.fresh_local(hr_ty.clone());
        let concl = c.eq_of(c.sub_of(nn.clone(), c.up_of(&nn, &v)), c.zero.clone());
        let ty = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, concl);
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let hr_ty2 = c.le_of(c.r_of(&vn, &vv), vv.clone());
            let (vhr_id, vhr) = vb.fresh_local(hr_ty2.clone());
            let up = c.up_of(&vn, &vv);
            let nleup = Expr::apps(n_le_up.clone(), [vn.clone(), vv.clone(), vhr.clone()]);
            let body = Expr::apps(sub_eq_zero_of_le.clone(), [vn.clone(), up.clone(), nleup]);
            let lam = vb.mk_lam(vhr_id, BinderInfo::Default, hr_ty2, body);
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem up_conj1_arith (V r : Nat) (hVr : Nat.le r V) (hV2r : Nat.le V (mul 2 r))
    ///   : Nat.le (mul 2 (sub V r)) V`
    /// ```text
    /// @Eq.subst Nat (fun z => Nat.le z V) (add (sub V r)(sub V r)) (mul 2 (sub V r))
    ///   (Eq.symm (two_mul (sub V r)))
    ///   (@Eq.subst Nat (fun z => Nat.le (add (sub V r)(sub V r)) z) (add (sub V r) r) V
    ///     (sub_add_cancel V r hVr)
    ///     (Nat.add_le_add_left (sub V r) r
    ///       (le_of_add_le_add_right (sub V r) r r
    ///         (@Eq.subst Nat (fun z => Nat.le (add (sub V r) r) z) (mul 2 r) (add r r) (two_mul r)
    ///           (@Eq.subst Nat (fun z => Nat.le z (mul 2 r))
    ///             V (add (sub V r) r) (Eq.symm (sub_add_cancel V r hVr)) hV2r)))
    ///       (sub V r)))
    /// ```
    fn register_up_conj1_arith(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::UP_CONJ1_ARITH);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let two_mul = Ulp::const_(names::TWO_MUL);
        let sub_add_cancel = Ulp::const_(names::SUB_ADD_CANCEL);
        let le_of_add_le_add_right = Ulp::const_(names::LE_OF_ADD_LE_ADD_RIGHT);
        let add_le_add_left = Ulp::const_("Nat.add_le_add_left");

        let mut b = EnvDeclBuilder::new();
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let (r_id, r) = b.fresh_local(c.nat.clone());
        let hvr_ty = c.le_of(r.clone(), v.clone());
        let (hvr_id, _hvr) = b.fresh_local(hvr_ty.clone());
        let hv2r_ty = c.le_of(v.clone(), c.two_mul_of(r.clone()));
        let (hv2r_id, _hv2r) = b.fresh_local(hv2r_ty.clone());
        let concl = c.le_of(c.two_mul_of(c.sub_of(v.clone(), r.clone())), v.clone());
        let ty = b.mk_pi(hv2r_id, BinderInfo::Default, hv2r_ty, concl);
        let ty = b.mk_pi(hvr_id, BinderInfo::Default, hvr_ty, ty);
        let ty = b.mk_pi(r_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let (vr_id, vr) = vb.fresh_local(c.nat.clone());
            let hvr_ty2 = c.le_of(vr.clone(), vv.clone());
            let (vhvr_id, vhvr) = vb.fresh_local(hvr_ty2.clone());
            let hv2r_ty2 = c.le_of(vv.clone(), c.two_mul_of(vr.clone()));
            let (vhv2r_id, vhv2r) = vb.fresh_local(hv2r_ty2.clone());

            let svr = c.sub_of(vv.clone(), vr.clone()); // sub V r
            let twor = c.two_mul_of(vr.clone()); // mul 2 r
                                                 // sub_add_cancel V r hVr : @Eq Nat (add (sub V r) r) V
            let sac = Expr::apps(
                sub_add_cancel.clone(),
                [vv.clone(), vr.clone(), vhvr.clone()],
            );

            // innermost-2: @Eq.subst Nat (fun z => Nat.le z (mul 2 r)) V (add (sub V r) r)
            //   (Eq.symm sac) hV2r
            let lvl5 = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(z.clone(), twor.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let sac_sym = c.symm(c.add_of(svr.clone(), vr.clone()), vv.clone(), sac.clone());
                c.subst(
                    motive,
                    vv.clone(),
                    c.add_of(svr.clone(), vr.clone()),
                    sac_sym,
                    vhv2r.clone(),
                )
            };

            // lvl4: @Eq.subst Nat (fun z => Nat.le (add (sub V r) r) z) (mul 2 r) (add r r)
            //   (two_mul r) lvl5
            let lvl4 = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(c.add_of(svr.clone(), vr.clone()), z.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let tmr = Expr::app(two_mul.clone(), vr.clone()); // @Eq Nat (mul 2 r) (add r r)
                c.subst(
                    motive,
                    twor.clone(),
                    c.add_of(vr.clone(), vr.clone()),
                    tmr,
                    lvl5,
                )
            };

            // lvl3: le_of_add_le_add_right (sub V r) r r lvl4 : Nat.le (sub V r) r
            let lvl3 = Expr::apps(
                le_of_add_le_add_right.clone(),
                [svr.clone(), vr.clone(), vr.clone(), lvl4],
            );

            // lvl2: Nat.add_le_add_left (sub V r) r lvl3 (sub V r)
            //   : Nat.le (add (sub V r)(sub V r)) (add (sub V r) r)
            let lvl2 = Expr::apps(
                add_le_add_left.clone(),
                [svr.clone(), vr.clone(), lvl3, svr.clone()],
            );

            // lvl1: @Eq.subst Nat (fun z => Nat.le (add (sub V r)(sub V r)) z) (add (sub V r) r) V
            //   sac lvl2
            let lvl1 = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(c.add_of(svr.clone(), svr.clone()), z.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                c.subst(
                    motive,
                    c.add_of(svr.clone(), vr.clone()),
                    vv.clone(),
                    sac.clone(),
                    lvl2,
                )
            };

            // outer: @Eq.subst Nat (fun z => Nat.le z V)
            //   (add (sub V r)(sub V r)) (mul 2 (sub V r)) (Eq.symm (two_mul (sub V r))) lvl1
            let body = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(z.clone(), vv.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let tmsvr = Expr::app(two_mul.clone(), svr.clone()); // @Eq Nat (mul 2 (sub V r)) (add (sub V r)(sub V r))
                let tmsvr_sym = c.symm(
                    c.two_mul_of(svr.clone()),
                    c.add_of(svr.clone(), svr.clone()),
                    tmsvr,
                );
                c.subst(
                    motive,
                    c.add_of(svr.clone(), svr.clone()),
                    c.two_mul_of(svr.clone()),
                    tmsvr_sym,
                    lvl1,
                )
            };

            let lam = vb.mk_lam(vhv2r_id, BinderInfo::Default, hv2r_ty2, body);
            let lam = vb.mk_lam(vhvr_id, BinderInfo::Default, hvr_ty2, lam);
            let lam = vb.mk_lam(vr_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// The two-sided bound when the result is `down = q*V`.
    /// ```text
    /// theorem down_bound (N V : Nat) (hTwoRleV : Nat.le (mul 2 (mod N V)) V) :
    ///   And (Nat.le (mul 2 (sub down N)) V) (Nat.le (mul 2 (sub N down)) V)
    /// ```
    fn register_down_bound(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::DOWN_BOUND);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let down_sub_n = Ulp::const_(names::DOWN_SUB_N);
        let n_sub_down = Ulp::const_(names::N_SUB_DOWN);
        let zero_le = Ulp::const_("Nat.zero_le");

        // helper: conj predicates for a candidate w.
        let conj1 = |c: &Ulp, w: &Expr, nn: &Expr, v: &Expr| {
            c.le_of(c.two_mul_of(c.sub_of(w.clone(), nn.clone())), v.clone())
        };
        let conj2 = |c: &Ulp, w: &Expr, nn: &Expr, v: &Expr| {
            c.le_of(c.two_mul_of(c.sub_of(nn.clone(), w.clone())), v.clone())
        };

        let mut b = EnvDeclBuilder::new();
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let h_ty = c.le_of(c.two_mul_of(c.r_of(&nn, &v)), v.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let down = c.down_of(&nn, &v);
        let concl = c.and_of(conj1(c, &down, &nn, &v), conj2(c, &down, &nn, &v));
        let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let h_ty2 = c.le_of(c.two_mul_of(c.r_of(&vn, &vv)), vv.clone());
            let (vh_id, vh) = vb.fresh_local(h_ty2.clone());
            let down = c.down_of(&vn, &vv);
            let r = c.r_of(&vn, &vv);
            let p1 = conj1(c, &down, &vn, &vv);
            let p2 = conj2(c, &down, &vn, &vv);

            // conj1: @Eq.subst Nat (fun z => Nat.le (mul 2 z) V) 0 (sub down N)
            //   (Eq.symm (down_sub_N N V)) (Nat.zero_le V)
            let pf1 = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(c.two_mul_of(z.clone()), vv.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let dsn = Expr::apps(down_sub_n.clone(), [vn.clone(), vv.clone()]);
                let dsn_sym = c.symm(c.sub_of(down.clone(), vn.clone()), c.zero.clone(), dsn);
                let zle = Expr::app(zero_le.clone(), vv.clone());
                c.subst(
                    motive,
                    c.zero.clone(),
                    c.sub_of(down.clone(), vn.clone()),
                    dsn_sym,
                    zle,
                )
            };

            // conj2: @Eq.subst Nat (fun z => Nat.le (mul 2 z) V) (mod N V) (sub N down)
            //   (Eq.symm (N_sub_down N V)) hTwoRleV
            let pf2 = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(c.two_mul_of(z.clone()), vv.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let nsd = Expr::apps(n_sub_down.clone(), [vn.clone(), vv.clone()]);
                let nsd_sym = c.symm(c.sub_of(vn.clone(), down.clone()), r.clone(), nsd);
                c.subst(
                    motive,
                    r.clone(),
                    c.sub_of(vn.clone(), down.clone()),
                    nsd_sym,
                    vh.clone(),
                )
            };

            let body = c.and_intro(p1, p2, pf1, pf2);
            let lam = vb.mk_lam(vh_id, BinderInfo::Default, h_ty2, body);
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// The two-sided bound when the result is `up = (q+1)*V`.
    /// ```text
    /// theorem up_bound (N V : Nat) (hr : Nat.le (mod N V) V) (hVleTwoR : Nat.le V (mul 2 (mod N V))) :
    ///   And (Nat.le (mul 2 (sub up N)) V) (Nat.le (mul 2 (sub N up)) V)
    /// ```
    fn register_up_bound(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::UP_BOUND);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let up_sub_n = Ulp::const_(names::UP_SUB_N);
        let n_sub_up = Ulp::const_(names::N_SUB_UP);
        let up_conj1_arith = Ulp::const_(names::UP_CONJ1_ARITH);
        let zero_le = Ulp::const_("Nat.zero_le");

        let conj1 = |c: &Ulp, w: &Expr, nn: &Expr, v: &Expr| {
            c.le_of(c.two_mul_of(c.sub_of(w.clone(), nn.clone())), v.clone())
        };
        let conj2 = |c: &Ulp, w: &Expr, nn: &Expr, v: &Expr| {
            c.le_of(c.two_mul_of(c.sub_of(nn.clone(), w.clone())), v.clone())
        };

        let mut b = EnvDeclBuilder::new();
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let hr_ty = c.le_of(c.r_of(&nn, &v), v.clone());
        let (hr_id, _hr) = b.fresh_local(hr_ty.clone());
        let hv_ty = c.le_of(v.clone(), c.two_mul_of(c.r_of(&nn, &v)));
        let (hv_id, _hv) = b.fresh_local(hv_ty.clone());
        let up = c.up_of(&nn, &v);
        let concl = c.and_of(conj1(c, &up, &nn, &v), conj2(c, &up, &nn, &v));
        let ty = b.mk_pi(hv_id, BinderInfo::Default, hv_ty, concl);
        let ty = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, ty);
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let hr_ty2 = c.le_of(c.r_of(&vn, &vv), vv.clone());
            let (vhr_id, vhr) = vb.fresh_local(hr_ty2.clone());
            let hv_ty2 = c.le_of(vv.clone(), c.two_mul_of(c.r_of(&vn, &vv)));
            let (vhv_id, vhv) = vb.fresh_local(hv_ty2.clone());
            let up = c.up_of(&vn, &vv);
            let r = c.r_of(&vn, &vv);
            let p1 = conj1(c, &up, &vn, &vv);
            let p2 = conj2(c, &up, &vn, &vv);

            // conj1: @Eq.subst Nat (fun z => Nat.le (mul 2 z) V) (sub V r) (sub up N)
            //   (Eq.symm (up_sub_N N V)) (up_conj1_arith V r hr hVleTwoR)
            let pf1 = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(c.two_mul_of(z.clone()), vv.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let usn = Expr::apps(up_sub_n.clone(), [vn.clone(), vv.clone()]);
                let usn_sym = c.symm(
                    c.sub_of(up.clone(), vn.clone()),
                    c.sub_of(vv.clone(), r.clone()),
                    usn,
                );
                let arith = Expr::apps(
                    up_conj1_arith.clone(),
                    [vv.clone(), r.clone(), vhr.clone(), vhv.clone()],
                );
                c.subst(
                    motive,
                    c.sub_of(vv.clone(), r.clone()),
                    c.sub_of(up.clone(), vn.clone()),
                    usn_sym,
                    arith,
                )
            };

            // conj2: @Eq.subst Nat (fun z => Nat.le (mul 2 z) V) 0 (sub N up)
            //   (Eq.symm (N_sub_up N V hr)) (Nat.zero_le V)
            let pf2 = {
                let motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(c.two_mul_of(z.clone()), vv.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let nsu = Expr::apps(n_sub_up.clone(), [vn.clone(), vv.clone(), vhr.clone()]);
                let nsu_sym = c.symm(c.sub_of(vn.clone(), up.clone()), c.zero.clone(), nsu);
                let zle = Expr::app(zero_le.clone(), vv.clone());
                c.subst(
                    motive,
                    c.zero.clone(),
                    c.sub_of(vn.clone(), up.clone()),
                    nsu_sym,
                    zle,
                )
            };

            let body = c.and_intro(p1, p2, pf1, pf2);
            let lam = vb.mk_lam(vhv_id, BinderInfo::Default, hv_ty2, body);
            let lam = vb.mk_lam(vhr_id, BinderInfo::Default, hr_ty2, lam);
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem nmul_pos (a b : Nat) (ha : Nat.lt 0 a) (hb : Nat.lt 0 b) : Nat.lt 0 (mul a b)`
    /// ```text
    /// @Nat.rec (fun k => Nat.lt 0 k -> Nat.lt 0 (mul a k))
    ///   (fun h0 => @False.elim (Nat.lt 0 (mul a 0)) (Nat.lt_irrefl 0 h0))
    ///   (fun j _ih _hsj =>
    ///     Nat.le_trans 1 (succ (mul a j)) (add (mul a j) a)
    ///       (Nat.succ_le_succ 0 (mul a j) (Nat.zero_le (mul a j)))
    ///       (Nat.add_le_add_left 1 a ha (mul a j)))
    ///   b hb
    /// ```
    fn register_nmul_pos(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::NMUL_POS);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let lt_irrefl = Ulp::const_("Nat.lt_irrefl");
        let le_trans = Ulp::const_("Nat.le_trans");
        let succ_le_succ = Ulp::const_("Nat.succ_le_succ");
        let zero_le = Ulp::const_("Nat.zero_le");
        let add_le_add_left = Ulp::const_("Nat.add_le_add_left");
        let one = c.succ_of(c.zero.clone());

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bv) = b.fresh_local(c.nat.clone());
        let ha_ty = c.lt_of(c.zero.clone(), a.clone());
        let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
        let hb_ty = c.lt_of(c.zero.clone(), bv.clone());
        let (hb_id, _hb) = b.fresh_local(hb_ty.clone());
        let concl = c.lt_of(c.zero.clone(), c.mul_of(a.clone(), bv.clone()));
        let ty = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
        let ty = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, ty);
        let ty = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vb2_id, vbv) = vb.fresh_local(c.nat.clone());
            let ha_ty2 = c.lt_of(c.zero.clone(), va.clone());
            let (vha_id, vha) = vb.fresh_local(ha_ty2.clone());
            let hb_ty2 = c.lt_of(c.zero.clone(), vbv.clone());
            let (vhb_id, vhb) = vb.fresh_local(hb_ty2.clone());

            // motive: fun k => Nat.lt 0 k -> Nat.lt 0 (mul a k)
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = Expr::pi(
                    BinderInfo::Default,
                    c.lt_of(c.zero.clone(), k.clone()),
                    c.lt_of(c.zero.clone(), c.mul_of(va.clone(), k.clone())),
                );
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base (k=0): fun (h0 : lt 0 0) =>
            //   @False.elim (Nat.lt 0 (mul a 0)) (Nat.lt_irrefl 0 h0)
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let h0_ty = c.lt_of(c.zero.clone(), c.zero.clone());
                let (h0_id, h0) = bb.fresh_local(h0_ty.clone());
                let goal = c.lt_of(c.zero.clone(), c.mul_of(va.clone(), c.zero.clone()));
                let li = Expr::apps(lt_irrefl.clone(), [c.zero.clone(), h0]);
                let body = c.false_elim(goal, li);
                bb.finish_child(bb.mk_lam(h0_id, BinderInfo::Default, h0_ty, body))
            };

            // step (k=succ j): fun (j : Nat) (_ih : motive j) (_hsj : lt 0 (succ j)) =>
            //   Nat.le_trans 1 (succ (mul a j)) (add (mul a j) a)
            //     (Nat.succ_le_succ 0 (mul a j) (Nat.zero_le (mul a j)))
            //     (Nat.add_le_add_left 1 a ha (mul a j))
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (j_id, j) = sb.fresh_local(c.nat.clone());
                let ih_ty = Expr::pi(
                    BinderInfo::Default,
                    c.lt_of(c.zero.clone(), j.clone()),
                    c.lt_of(c.zero.clone(), c.mul_of(va.clone(), j.clone())),
                );
                let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
                let hsj_ty = c.lt_of(c.zero.clone(), c.succ_of(j.clone()));
                let (hsj_id, _hsj) = sb.fresh_local(hsj_ty.clone());

                let maj = c.mul_of(va.clone(), j.clone());
                // Nat.succ_le_succ 0 (mul a j) (Nat.zero_le (mul a j)) : le 1 (succ (mul a j))
                let zle = Expr::app(zero_le.clone(), maj.clone());
                let sls = Expr::apps(succ_le_succ.clone(), [c.zero.clone(), maj.clone(), zle]);
                // Nat.add_le_add_left 1 a ha (mul a j) : le (add (mul a j) 1) (add (mul a j) a)
                //   ≡ le (succ (mul a j)) (add (mul a j) a)
                let alal = Expr::apps(
                    add_le_add_left.clone(),
                    [one.clone(), va.clone(), vha.clone(), maj.clone()],
                );
                // Nat.le_trans 1 (succ (mul a j)) (add (mul a j) a) sls alal : le 1 (add (mul a j) a)
                //   ≡ lt 0 (mul a (succ j))
                let body = Expr::apps(
                    le_trans.clone(),
                    [
                        one.clone(),
                        c.succ_of(maj.clone()),
                        c.add_of(maj.clone(), va.clone()),
                        sls,
                        alal,
                    ],
                );
                let lam = sb.mk_lam(hsj_id, BinderInfo::Default, hsj_ty, body);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            let rec = c.rec0(motive, base, step, vbv.clone());
            let body = Expr::app(rec, vhb.clone());
            let lam = vb.mk_lam(vhb_id, BinderInfo::Default, hb_ty2, body);
            let lam = vb.mk_lam(vha_id, BinderInfo::Default, ha_ty2, lam);
            let lam = vb.mk_lam(vb2_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem two_pow_pos (e : Nat) : Nat.lt 0 (pow 2 e)`
    /// ```text
    /// @Nat.rec (fun k => Nat.lt 0 (pow 2 k))
    ///   (Nat.le_refl 1)
    ///   (fun k ih => nmul_pos (pow 2 k) 2 ih (Nat.succ_le_succ 0 1 (Nat.zero_le 1)))
    ///   e
    /// ```
    fn register_two_pow_pos(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::TWO_POW_POS);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let le_refl = Ulp::const_("Nat.le_refl");
        let succ_le_succ = Ulp::const_("Nat.succ_le_succ");
        let zero_le = Ulp::const_("Nat.zero_le");
        let nmul_pos = Ulp::const_(names::NMUL_POS);
        let one = c.succ_of(c.zero.clone());

        let mut b = EnvDeclBuilder::new();
        let (e_id, e) = b.fresh_local(c.nat.clone());
        let concl = c.lt_of(c.zero.clone(), c.pow_of(c.two.clone(), e.clone()));
        let ty = b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), concl);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (ve_id, ve) = vb.fresh_local(c.nat.clone());

            // motive: fun k => Nat.lt 0 (pow 2 k)
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.lt_of(c.zero.clone(), c.pow_of(c.two.clone(), k.clone()));
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // base: Nat.le_refl 1 : lt 0 (pow 2 0) = le 1 1
            let base = Expr::app(le_refl.clone(), one.clone());
            // step: fun (k : Nat) (ih : motive k) =>
            //   nmul_pos (pow 2 k) 2 ih (Nat.succ_le_succ 0 1 (Nat.zero_le 1))
            //   (pow 2 (succ k) ≡ mul (pow 2 k) 2)
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.lt_of(c.zero.clone(), c.pow_of(c.two.clone(), k.clone()));
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let pk = c.pow_of(c.two.clone(), k.clone());
                // Nat.zero_le 1 : le 0 1
                let zle = Expr::app(zero_le.clone(), one.clone());
                // Nat.succ_le_succ 0 1 (zero_le 1) : le 1 2 = lt 0 2
                let two_pos = Expr::apps(succ_le_succ.clone(), [c.zero.clone(), one.clone(), zle]);
                let body = Expr::apps(nmul_pos.clone(), [pk.clone(), c.two.clone(), ih, two_pos]);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            let rec = c.rec0(motive, base, step, ve.clone());
            let lam = vb.mk_lam(ve_id, BinderInfo::Default, c.nat.clone(), rec);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// THE GENERAL HEADLINE.
    /// ```text
    /// theorem round_half_even_mod_bound (V N : Nat) (hV : Nat.lt 0 V) :
    ///   And (Nat.le (mul 2 (sub (roundHalfEvenMod N V) N)) V)
    ///       (Nat.le (mul 2 (sub N (roundHalfEvenMod N V))) V)
    /// ```
    /// Three-way `@Bool.rec` casework, each scrutinee threaded back as an Eq.
    fn register_round_bound(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::ROUND_BOUND);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let mod_lt = Ulp::const_("Nat.mod_lt");
        let le_of_lt = Ulp::const_("Nat.le_of_lt");
        let le_of_ble_eq_true = Ulp::const_("Nat.le_of_ble_eq_true");
        let ble_succ_false_le = Ulp::const_(names::BLE_SUCC_FALSE_LE);
        let down_bound = Ulp::const_(names::DOWN_BOUND);
        let up_bound = Ulp::const_(names::UP_BOUND);

        // Type: ∀ (V N : Nat), Nat.lt 0 V -> And (conj1 round) (conj2 round)
        let mut b = EnvDeclBuilder::new();
        let (v_id, v) = b.fresh_local(c.nat.clone());
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let hv_ty = c.lt_of(c.zero.clone(), v.clone());
        let (hv_id, _hv) = b.fresh_local(hv_ty.clone());
        let round = c.round_app(&nn, &v);
        let concl = c.bound_and(round.clone(), &nn, &v);
        let ty = b.mk_pi(hv_id, BinderInfo::Default, hv_ty, concl);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vv_id, vv) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let hv_ty2 = c.lt_of(c.zero.clone(), vv.clone());
            let (vhv_id, vhv) = vb.fresh_local(hv_ty2.clone());

            let r = c.r_of(&vn, &vv);
            let twor = c.two_r_of(&vn, &vv);
            let lo_scrut = c.ble_of(c.succ_of(twor.clone()), vv.clone());
            let hi_scrut = c.ble_of(c.succ_of(vv.clone()), twor.clone());
            let q_even = c.beq_of(c.mod_of(c.q_of(&vn, &vv), c.two.clone()), c.zero.clone());

            // hr : le (mod N V) V  ::=  Nat.le_of_lt r V (Nat.mod_lt N V hV)
            let hrlt = Expr::apps(mod_lt.clone(), [vn.clone(), vv.clone(), vhv.clone()]);
            let hr = Expr::apps(le_of_lt.clone(), [r.clone(), vv.clone(), hrlt]);

            // OUTER motive: fun bLo => (@Eq Bool lo_scrut bLo) -> bound_and (round_with_lo bLo)
            let outer_motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (blo_id, blo) = mb.fresh_local(c.bool.clone());
                let round_w = c.round_with_lo(&vn, &vv, blo.clone());
                let body = Expr::pi(
                    BinderInfo::Default,
                    c.eq_bool_of(lo_scrut.clone(), blo.clone()),
                    c.bound_and(round_w, &vn, &vv),
                );
                mb.finish_child(mb.mk_lam(blo_id, BinderInfo::Default, c.bool.clone(), body))
            };

            // OUTER false-minor: fun (hLoF : @Eq Bool lo_scrut false) =>
            //   (fun (hVleTwoR : le V twoR) => <MIDDLE bool.rec> )
            //     (ble_succ_false_le twoR V hLoF)
            let outer_fcase = {
                let mut fb = EnvDeclBuilder::child_of(&vb);
                let hlof_ty = c.eq_bool_of(lo_scrut.clone(), c.bfalse.clone());
                let (hlof_id, hlof) = fb.fresh_local(hlof_ty.clone());

                // hVleTwoR : le V twoR  (we inline-let via a lambda applied)
                // Build the MIDDLE bool.rec as a function of hVleTwoR.
                // hVleTwoR binder:
                let hvletwor_ty = c.le_of(vv.clone(), twor.clone());

                // MIDDLE motive: fun bHi => (@Eq Bool hi_scrut bHi) ->
                //   bound_and (mid_rec_with bHi)
                let mid_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&fb);
                    let (bhi_id, bhi) = mb.fresh_local(c.bool.clone());
                    let mid_w = c.mid_rec_with(&vn, &vv, bhi.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.eq_bool_of(hi_scrut.clone(), bhi.clone()),
                        c.bound_and(mid_w, &vn, &vv),
                    );
                    mb.finish_child(mb.mk_lam(bhi_id, BinderInfo::Default, c.bool.clone(), body))
                };

                // We need hVleTwoR available inside both mid minors; bind it as a
                // lambda param `hvletwor` whose body is the MIDDLE bool.rec.
                let mut body_with_hv = EnvDeclBuilder::child_of(&fb);
                let (hvletwor_id, hvletwor) = body_with_hv.fresh_local(hvletwor_ty.clone());

                // MIDDLE false-minor: fun (hHiF : @Eq Bool hi_scrut false) =>
                //   <EVEN bool.rec>
                let mid_fcase = {
                    let mut mfb = EnvDeclBuilder::child_of(&body_with_hv);
                    let hhif_ty = c.eq_bool_of(hi_scrut.clone(), c.bfalse.clone());
                    let (hhif_id, hhif) = mfb.fresh_local(hhif_ty.clone());

                    // EVEN motive: fun bEv => bound_and (even_rec_with bEv)
                    let even_motive = {
                        let mut eb = EnvDeclBuilder::child_of(&mfb);
                        let (bev_id, bev) = eb.fresh_local(c.bool.clone());
                        let even_w = c.even_rec_with(&vn, &vv, bev.clone());
                        let body = c.bound_and(even_w, &vn, &vv);
                        eb.finish_child(eb.mk_lam(
                            bev_id,
                            BinderInfo::Default,
                            c.bool.clone(),
                            body,
                        ))
                    };
                    // EVEN false-minor: up_bound N V hr hVleTwoR
                    let even_fcase = Expr::apps(
                        up_bound.clone(),
                        [vn.clone(), vv.clone(), hr.clone(), hvletwor.clone()],
                    );
                    // EVEN true-minor: down_bound N V (ble_succ_false_le V twoR hHiF)
                    let bsfl =
                        Expr::apps(ble_succ_false_le.clone(), [vv.clone(), twor.clone(), hhif]);
                    let even_tcase = Expr::apps(down_bound.clone(), [vn.clone(), vv.clone(), bsfl]);
                    // @Bool.rec.{0} even_motive even_fcase even_tcase q_even
                    let body = c.brec0(even_motive, even_fcase, even_tcase, q_even.clone());
                    mfb.finish_child(mfb.mk_lam(hhif_id, BinderInfo::Default, hhif_ty, body))
                };

                // MIDDLE true-minor: fun (_hHiT : @Eq Bool hi_scrut true) =>
                //   up_bound N V hr hVleTwoR
                let mid_tcase = {
                    let mut mtb = EnvDeclBuilder::child_of(&body_with_hv);
                    let hhit_ty = c.eq_bool_of(hi_scrut.clone(), c.btrue.clone());
                    let (hhit_id, _hhit) = mtb.fresh_local(hhit_ty.clone());
                    let body = Expr::apps(
                        up_bound.clone(),
                        [vn.clone(), vv.clone(), hr.clone(), hvletwor.clone()],
                    );
                    mtb.finish_child(mtb.mk_lam(hhit_id, BinderInfo::Default, hhit_ty, body))
                };

                // @Bool.rec.{0} mid_motive mid_fcase mid_tcase hi_scrut
                //   (@Eq.refl Bool hi_scrut)
                let mid_rec_app = c.brec0(mid_motive, mid_fcase, mid_tcase, hi_scrut.clone());
                let mid_applied = Expr::app(mid_rec_app, c.refl_bool(hi_scrut.clone()));
                // close hvletwor lambda
                let hv_lam = body_with_hv.finish_child(body_with_hv.mk_lam(
                    hvletwor_id,
                    BinderInfo::Default,
                    hvletwor_ty,
                    mid_applied,
                ));
                // apply (ble_succ_false_le twoR V hLoF) : le V twoR
                let hvletwor_val =
                    Expr::apps(ble_succ_false_le.clone(), [twor.clone(), vv.clone(), hlof]);
                let applied = Expr::app(hv_lam, hvletwor_val);
                fb.finish_child(fb.mk_lam(hlof_id, BinderInfo::Default, hlof_ty, applied))
            };

            // OUTER true-minor: fun (hLoT : @Eq Bool lo_scrut true) =>
            //   down_bound N V (Nat.le_of_lt twoR V (Nat.le_of_ble_eq_true (succ twoR) V hLoT))
            let outer_tcase = {
                let mut tb = EnvDeclBuilder::child_of(&vb);
                let hlot_ty = c.eq_bool_of(lo_scrut.clone(), c.btrue.clone());
                let (hlot_id, hlot) = tb.fresh_local(hlot_ty.clone());
                // le_of_ble_eq_true (succ twoR) V hLoT : le (succ twoR) V = lt twoR V
                let lobet = Expr::apps(
                    le_of_ble_eq_true.clone(),
                    [c.succ_of(twor.clone()), vv.clone(), hlot],
                );
                // le_of_lt twoR V lobet : le twoR V
                let twor_le_v = Expr::apps(le_of_lt.clone(), [twor.clone(), vv.clone(), lobet]);
                let body = Expr::apps(down_bound.clone(), [vn.clone(), vv.clone(), twor_le_v]);
                tb.finish_child(tb.mk_lam(hlot_id, BinderInfo::Default, hlot_ty, body))
            };

            // @Bool.rec.{0} outer_motive outer_fcase outer_tcase lo_scrut
            //   (@Eq.refl Bool lo_scrut)
            let outer_rec = c.brec0(outer_motive, outer_fcase, outer_tcase, lo_scrut.clone());
            let body = Expr::app(outer_rec, c.refl_bool(lo_scrut.clone()));

            let lam = vb.mk_lam(vhv_id, BinderInfo::Default, hv_ty2, body);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vv_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// THE UNIVERSAL HEADLINE.
    /// ```text
    /// theorem ulp_universal_bound (e N : Nat) :
    ///   And (Nat.le (mul 2 (sub (roundHalfEvenMod N (pow 2 e)) N)) (pow 2 e))
    ///       (Nat.le (mul 2 (sub N (roundHalfEvenMod N (pow 2 e)))) (pow 2 e))
    ///   := round_half_even_mod_bound (pow 2 e) N (two_pow_pos e)
    /// ```
    fn register_ulp_universal_bound(&mut self, c: &Ulp) -> Result<(), EnvError> {
        let name = Name::from_string(names::ULP_BOUND);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let round_bound = Ulp::const_(names::ROUND_BOUND);
        let two_pow_pos = Ulp::const_(names::TWO_POW_POS);

        // Type: ∀ (e N : Nat), And (conj1 round@(pow 2 e)) (conj2 ...)
        let mut b = EnvDeclBuilder::new();
        let (e_id, e) = b.fresh_local(c.nat.clone());
        let (nn_id, nn) = b.fresh_local(c.nat.clone());
        let pe = c.pow_of(c.two.clone(), e.clone());
        let round = c.round_app(&nn, &pe);
        let concl = c.bound_and(round.clone(), &nn, &pe);
        let ty = b.mk_pi(nn_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (ve_id, ve) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let vpe = c.pow_of(c.two.clone(), ve.clone());
            // two_pow_pos e : lt 0 (pow 2 e)
            let tpp = Expr::app(two_pow_pos.clone(), ve.clone());
            // round_bound (pow 2 e) N (two_pow_pos e)
            let body = Expr::apps(round_bound.clone(), [vpe.clone(), vn.clone(), tpp]);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(ve_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;

    /// `with_prelude()` carries the two ulp headlines (each a `Theorem` with an
    /// EMPTY foundational-only axiom closure) and the reducible round def.
    #[test]
    fn ulp_round_headlines_proven_to_foundations() {
        let env = Environment::with_prelude();
        for n in [
            "Nat.ulp_universal_bound",
            "Nat.round_half_even_mod_bound",
            "Nat.roundHalfEvenMod",
        ] {
            let name = Name::from_string(n);
            assert!(env.get_const(&name).is_some(), "{n} missing");
        }
        for n in ["Nat.ulp_universal_bound", "Nat.round_half_even_mod_bound"] {
            let name = Name::from_string(n);
            let info = env.get_const(&name).unwrap();
            assert_eq!(info.kind, ConstantKind::Theorem, "{n} must be a Theorem");
            let deps = env
                .axiom_deps(&name)
                .unwrap_or_else(|| panic!("{n}: axiom_deps None"));
            assert!(deps.is_empty(), "{n} rests on {deps:?}");
        }
        // The round primitive is a reducible Definition.
        let rci = env
            .get_const(&Name::from_string("Nat.roundHalfEvenMod"))
            .unwrap();
        assert_eq!(rci.kind, ConstantKind::Definition);
        assert!(rci.is_reducible, "round def must be reducible");
    }

    /// Every registered `Nat.ulpRound.*` helper is also axiom-free.
    #[test]
    fn ulp_round_helpers_axiom_free() {
        let env = Environment::with_prelude();
        for short in [
            names::SUCC_SUB_SUCC,
            names::ZERO_SUB,
            names::NMUL_ZERO_LEFT,
            names::ONE_MUL,
            names::TWO_MUL,
            names::ADD_SUB_SELF_RIGHT,
            names::ADD_SUB_CANCEL_LEFT,
            names::SUB_ADD_ADD_RIGHT,
            names::SUB_ADD_ADD_LEFT,
            names::SUB_EQ_ZERO_OF_LE,
            names::SUB_ADD_CANCEL,
            names::LE_OF_ADD_LE_ADD_RIGHT,
            names::BLE_SUCC_FALSE_LE,
            names::N_SUB_DOWN,
            names::DOWN_LE_N,
            names::DOWN_SUB_N,
            names::UP_SUB_N,
            names::N_LE_UP,
            names::N_SUB_UP,
            names::UP_CONJ1_ARITH,
            names::DOWN_BOUND,
            names::UP_BOUND,
            names::NMUL_POS,
            names::TWO_POW_POS,
        ] {
            let name = Name::from_string(short);
            assert!(env.get_const(&name).is_some(), "{short} must be registered");
            let deps = env
                .axiom_deps(&name)
                .unwrap_or_else(|| panic!("{short}: axiom_deps None"));
            assert!(deps.is_empty(), "{short} rests on {deps:?}");
        }
    }

    /// The headline types are symbolic in `e` (no reduction of `2^e`), so the
    /// `∀ … And (Nat.le …) (Nat.le …)` statement shape is exactly as advertised.
    #[test]
    fn ulp_universal_bound_statement_shape_symbolic() {
        let env = Environment::with_prelude();
        let ci = env
            .get_const(&Name::from_string("Nat.ulp_universal_bound"))
            .unwrap();
        let s = format!("{}", ci.type_);
        // symbolic: the exponent `n` survives inside `Nat.pow 2 n`, unreduced.
        assert!(s.contains("And "), "missing And: {s}");
        assert!(s.contains("Nat.roundHalfEvenMod"), "missing round: {s}");
        assert!(
            s.contains("Nat.pow"),
            "missing Nat.pow (must stay symbolic): {s}"
        );
    }
}
