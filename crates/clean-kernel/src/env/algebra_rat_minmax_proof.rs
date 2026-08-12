// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! WS-B: genuine, kernel-checked elimination of the opaque `Rat.min` / `Rat.max`
//! axioms (and their characterizing equations + the six lattice lemmas) over the
//! QUOTIENT `Rat := @Quot.{1} Rat.Raw Rat.Raw.Equiv` carrier.
//!
//! This is the quotient-carrier mirror of the constructive `Int.min` / `Int.max`
//! elimination in `algebra_int_minmax_proof.rs` /
//! `algebra_int_minmax_def_prime_proof.rs`. The structure is:
//!
//! 1. `Rat.ble : Rat → Rat → Bool` — a DECIDABLE boolean order, a binary
//!    `Quot.lift` of
//!    `raw_ble p q := Int.ble (num p · eff q) (num q · eff p)`
//!    into `Bool`. The two `Rat.Raw.Equiv`-respect obligations are `@Eq Bool`,
//!    discharged via a general `Int.ble` congruence lemma
//!    `Int.ble_eq_of_le_iff` fed the two `Int.le` implications that the
//!    cross-multiplication transitivity `Int.le_cross_trans` proves (the same
//!    implications the live `Rat.le` lift uses, reconstructed here).
//!
//! 2. `Rat.ble_eq_true_of_le` / `Rat.le_of_ble_eq_true` — the two directions of
//!    `Rat.ble a b = true ↔ Rat.le a b`, by `Quot.ind` reducing to the Int
//!    reflections `Int.ble_eq_true_of_le` / `Int.le_of_ble_eq_true` on
//!    representatives.
//!
//! 3. `Rat.min a b := @Bool.rec (fun _ => Rat) b a (Rat.ble a b)` and
//!    `Rat.max a b := @Bool.rec (fun _ => Rat) a b (Rat.ble a b)` — reducible
//!    `Declaration::Definition`s replacing the bodyless `Declaration::Axiom`s.
//!
//! 4. `Rat.min_def` / `Rat.max_def` (`Rat.le a b → …`) and `Rat.min_def'` /
//!    `Rat.max_def'` (`Rat.le b a → …`) by transporting `@Eq.refl` across the
//!    `Rat.ble` reflection (a dependent `Bool.rec` split, as in
//!    `algebra_int_minmax_def_prime_proof.rs`), the primed versions using the
//!    landed quotient `Rat.le_antisymm`.
//!
//! 5. The six lattice lemmas `Rat.le_max_left` / `le_max_right` /
//!    `min_le_left` / `min_le_right` / `max_le` / `le_min` by case-splitting on
//!    `Rat.ble` and discharging each branch with the landed quotient
//!    `Rat.le_refl` / `Rat.le_total` / `Rat.le_trans` (plus the `Rat.ble`
//!    reflections to turn the discriminant into the needed `Rat.le` fact).
//!
//! Every delegate is either kernel machinery (`Quot.*`, `Bool.rec`, `Eq.*`),
//! foundational (`propext`, `Quot.sound` — reached only through the live
//! `Rat.le` / `Rat.le_antisymm` definitions), or a constructive Int/Rat
//! `Declaration::Theorem`, so each registered theorem is
//! `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across the WS-B proof terms.
struct RatMinMaxConsts {
    // Sorts.
    bool_t: Expr,
    bool_true: Expr,
    bool_false: Expr,
    // Int / Nat.
    int: Expr,
    int_mul: Expr,
    int_le: Expr,
    int_of_nat: Expr,
    nat_pred: Expr,
    // Int decidable-order reflections (landed constructive Theorems).
    int_ble: Expr,
    int_ble_eq_true_of_le: Expr,
    int_le_of_ble_eq_true: Expr,
    int_le_cross_trans: Expr,
    int_le_refl: Expr,
    // Raw carrier + quotient.
    raw: Expr,
    raw_num: Expr,
    raw_denom: Expr,
    raw_eff_denom: Expr,
    raw_equiv: Expr,
    ratq: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
    /// `Quot.lift.{1,1}` (α = Rat.Raw : Sort 1, β = Bool : Sort 1).
    quot_lift_bool: Expr,
    // Rat order (live quotient Definitions / landed Theorems).
    rat_le: Expr,
    rat_ble: Expr,
    rat_min: Expr,
    rat_max: Expr,
    rat_le_refl: Expr,
    rat_le_total: Expr,
    rat_le_antisymm: Expr,
    rat_ble_eq_true_of_le: Expr,
    rat_le_of_ble_eq_true: Expr,
    // Eq machinery.
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    eq_c_int: Expr,
    eq_c_bool: Expr,
    eq_c_rat: Expr,
    eq_refl_bool: Expr,
    eq_refl_rat: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst_bool: Expr,
    eq_subst_int: Expr,
    // Bool.rec into Rat (Sort 1) / Prop (Sort 0).
    bool_rec_rat: Expr,
    bool_rec_prop: Expr,
    bool_rec_disc: Expr,
    // Logic.
    or_c: Expr,
    or_rec: Expr,
    true_c: Expr,
    false_c: Expr,
    true_intro: Expr,
    /// `False.elim.{0}` — every goal we discharge by `False.elim` is a Prop.
    false_elim: Expr,
}

impl RatMinMaxConsts {
    fn new() -> Self {
        let t1 = Level::succ(Level::zero());
        Self {
            bool_t: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            int: Expr::const_(Name::from_string("Int"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_pred: Expr::const_(Name::from_string("Nat.pred"), vec![]),
            int_ble: Expr::const_(Name::from_string("Int.ble"), vec![]),
            int_ble_eq_true_of_le: Expr::const_(Name::from_string("Int.ble_eq_true_of_le"), vec![]),
            int_le_of_ble_eq_true: Expr::const_(Name::from_string("Int.le_of_ble_eq_true"), vec![]),
            int_le_cross_trans: Expr::const_(Name::from_string("Int.le_cross_trans"), vec![]),
            int_le_refl: Expr::const_(Name::from_string("Int.le_refl"), vec![]),
            raw: Expr::const_(Name::from_string("Rat.Raw"), vec![]),
            raw_num: Expr::const_(Name::from_string("Rat.Raw.num"), vec![]),
            raw_denom: Expr::const_(Name::from_string("Rat.Raw.denom"), vec![]),
            raw_eff_denom: Expr::const_(Name::from_string("Rat.Raw.effDenom"), vec![]),
            raw_equiv: Expr::const_(Name::from_string("Rat.Raw.Equiv"), vec![]),
            ratq: Expr::const_(Name::from_string("Rat"), vec![]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![t1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![t1.clone()]),
            quot_lift_bool: Expr::const_(
                Name::from_string("Quot.lift"),
                vec![t1.clone(), t1.clone()],
            ),
            rat_le: Expr::const_(Name::from_string("Rat.le"), vec![]),
            rat_ble: Expr::const_(Name::from_string("Rat.ble"), vec![]),
            rat_min: Expr::const_(Name::from_string("Rat.min"), vec![]),
            rat_max: Expr::const_(Name::from_string("Rat.max"), vec![]),
            rat_le_refl: Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            rat_le_total: Expr::const_(Name::from_string("Rat.le_total"), vec![]),
            rat_le_antisymm: Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]),
            rat_ble_eq_true_of_le: Expr::const_(Name::from_string("Rat.ble_eq_true_of_le"), vec![]),
            rat_le_of_ble_eq_true: Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            #[cfg(test)]
            eq_c_int: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            eq_c_bool: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            eq_c_rat: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![t1.clone()]),
            eq_refl_rat: Expr::const_(Name::from_string("Eq.refl"), vec![t1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![t1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![t1.clone()]),
            eq_subst_bool: Expr::const_(Name::from_string("Eq.subst"), vec![t1.clone()]),
            eq_subst_int: Expr::const_(Name::from_string("Eq.subst"), vec![t1.clone()]),
            bool_rec_rat: Expr::const_(Name::from_string("Bool.rec"), vec![t1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            // The True/False discriminator's motive lands in Prop : Sort 1.
            bool_rec_disc: Expr::const_(Name::from_string("Bool.rec"), vec![t1]),
            or_c: Expr::const_(Name::from_string("Or"), vec![]),
            // `Or.rec` eliminating an `Or` of Props into a Prop goal carries no
            // universe params in this kernel (mirrors `algebra_rat_le_trans_proof`).
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            true_c: Expr::const_(Name::from_string("True"), vec![]),
            false_c: Expr::const_(Name::from_string("False"), vec![]),
            true_intro: Expr::const_(Name::from_string("True.intro"), vec![]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        }
    }

    // ── Int / Nat / Raw smart-constructors (mirror the private quotient ones) ─

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [x, y])
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn num(&self, p: Expr) -> Expr {
        Expr::app(self.raw_num.clone(), p)
    }
    /// `Int.ofNat (Rat.Raw.effDenom p)` — definitionally
    /// `Int.ofNat (Nat.succ (Nat.pred (denom p)))`, the positive eff denom.
    fn eff(&self, p: Expr) -> Expr {
        self.of_nat(Expr::app(self.raw_eff_denom.clone(), p))
    }
    /// `kd x := Nat.pred (Rat.Raw.denom x)` — the `n` with `eff x ≡ ofNat (succ n)`.
    fn kd(&self, x: &Expr) -> Expr {
        Expr::app(
            self.nat_pred.clone(),
            Expr::app(self.raw_denom.clone(), x.clone()),
        )
    }
    fn equiv(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.raw_equiv.clone(), [p, q])
    }
    fn int_le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }
    fn int_ble(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_ble.clone(), [x, y])
    }
    /// `@Quot.mk.{1} Rat.Raw Rat.Raw.Equiv l : Rat`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), l],
        )
    }

    /// `raw_le p q := Int.le (num p · eff q) (num q · eff p)`.
    fn raw_le(&self, p: &Expr, q: &Expr) -> Expr {
        self.int_le(
            self.mul(self.num(p.clone()), self.eff(q.clone())),
            self.mul(self.num(q.clone()), self.eff(p.clone())),
        )
    }
    /// `raw_ble p q := Int.ble (num p · eff q) (num q · eff p)`.
    fn raw_ble(&self, p: &Expr, q: &Expr) -> Expr {
        self.int_ble(
            self.mul(self.num(p.clone()), self.eff(q.clone())),
            self.mul(self.num(q.clone()), self.eff(p.clone())),
        )
    }

    // ── Eq smart-constructors ───────────────────────────────────────────────

    fn eq_bool(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_c_bool.clone(), [self.bool_t.clone(), x, y])
    }
    fn eq_rat(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_c_rat.clone(), [self.ratq.clone(), x, y])
    }
    fn refl_bool(&self, v: Expr) -> Expr {
        Expr::apps(self.eq_refl_bool.clone(), [self.bool_t.clone(), v])
    }
    fn refl_rat(&self, v: Expr) -> Expr {
        Expr::apps(self.eq_refl_rat.clone(), [self.ratq.clone(), v])
    }
    /// `@Eq.symm.{1} Bool x y h`.
    fn symm_bool(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.bool_t.clone(), x, y, h])
    }
    /// `@Eq.symm.{1} Int x y h`.
    fn symm_int(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int.clone(), x, y, h])
    }
    /// `@Eq.symm.{1} Rat x y h`.
    fn symm_rat(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.ratq.clone(), x, y, h])
    }
    /// `@Eq.trans.{1} Bool x y z h1 h2`.
    fn trans_bool(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.bool_t.clone(), x, y, z, h1, h2],
        )
    }

    /// `@Eq.subst.{1} Int (fun z => Int.le a z) a b h_eq (Int.le_refl a) : Int.le a b`.
    fn le_of_eq(&self, parent: &EnvDeclBuilder, a: &Expr, bb: &Expr, h_eq: &Expr) -> Expr {
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = ch.fresh_local(self.int.clone());
            let body = self.int_le(a.clone(), z);
            let lam = ch.mk_lam(z_id, BinderInfo::Default, self.int.clone(), body);
            ch.finish_child(lam)
        };
        let seed = Expr::app(self.int_le_refl.clone(), a.clone());
        Expr::apps(
            self.eq_subst_int.clone(),
            [
                self.int.clone(),
                motive,
                a.clone(),
                bb.clone(),
                h_eq.clone(),
                seed,
            ],
        )
    }

    /// `Int.le_cross_trans na nb nc da db dc h1 h2`.
    #[allow(clippy::too_many_arguments)]
    fn le_cross_trans(
        &self,
        na: Expr,
        nb: Expr,
        nc: Expr,
        da: Expr,
        db: Expr,
        dc: Expr,
        h1: Expr,
        h2: Expr,
    ) -> Expr {
        Expr::apps(
            self.int_le_cross_trans.clone(),
            [na, nb, nc, da, db, dc, h1, h2],
        )
    }

    /// `@Bool.rec.{1} (fun _ => Rat) f t scrut` — Rat-valued case split.
    fn bool_rec_rat(&self, f: Expr, t: Expr, scrut: Expr) -> Expr {
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(self.bool_t.clone());
            let e = b.mk_lam(
                x_id,
                BinderInfo::Default,
                self.bool_t.clone(),
                self.ratq.clone(),
            );
            b.finish(e)
        };
        Expr::apps(self.bool_rec_rat.clone(), [motive, f, t, scrut])
    }

    fn rat_le_app(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [x, y])
    }
    fn rat_ble_app(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_ble.clone(), [x, y])
    }
    fn rat_min_app(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_min.clone(), [x, y])
    }
    fn rat_max_app(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_max.clone(), [x, y])
    }

    /// `Int.ble_eq_of_le_iff` const applied to its four Int args + fwd/bwd.
    fn ble_eq_of_le_iff(
        &self,
        a: Expr,
        bv: Expr,
        a2: Expr,
        b2: Expr,
        fwd: Expr,
        bwd: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Int.ble_eq_of_le_iff"), vec![]),
            [a, bv, a2, b2, fwd, bwd],
        )
    }

    // ── First/second-argument Int.le implications under Equiv (the raw lift
    //    respect, reconstructed from `Int.le_cross_trans`) ────────────────────

    /// `raw_le p q → raw_le p q'` from `hq : Equiv q q'` (≡ `nq·eff q' = nq2·eff q`).
    fn le_impl_right(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        q2: &Expr,
        hq: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let pre = self.raw_le(p, q);
        let (hle_id, hle) = ch.fresh_local(pre.clone());
        let nq_effq2 = self.mul(self.num(q.clone()), self.eff(q2.clone()));
        let nq2_effq = self.mul(self.num(q2.clone()), self.eff(q.clone()));
        let h2 = self.le_of_eq(&ch, &nq_effq2, &nq2_effq, hq);
        let body = self.le_cross_trans(
            self.num(p.clone()),
            self.num(q.clone()),
            self.num(q2.clone()),
            self.kd(p),
            self.kd(q),
            self.kd(q2),
            hle,
            h2,
        );
        let lam = ch.mk_lam(hle_id, BinderInfo::Default, pre, body);
        ch.finish_child(lam)
    }

    /// `raw_le p q → raw_le p' q` from `hp : Equiv p p'` (≡ `np·eff p' = np2·eff p`).
    fn le_impl_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        p2: &Expr,
        q: &Expr,
        hp: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let pre = self.raw_le(p, q);
        let (hle_id, hle) = ch.fresh_local(pre.clone());
        let np2_effp = self.mul(self.num(p2.clone()), self.eff(p.clone()));
        let np_effp2 = self.mul(self.num(p.clone()), self.eff(p2.clone()));
        let hp_symm = self.symm_int(np_effp2.clone(), np2_effp.clone(), hp.clone());
        let h1 = self.le_of_eq(&ch, &np2_effp, &np_effp2, &hp_symm);
        let body = self.le_cross_trans(
            self.num(p2.clone()),
            self.num(p.clone()),
            self.num(q.clone()),
            self.kd(p2),
            self.kd(p),
            self.kd(q),
            h1,
            hle,
        );
        let lam = ch.mk_lam(hle_id, BinderInfo::Default, pre, body);
        ch.finish_child(lam)
    }

    /// `fun (z : Bool) => @Bool.rec.{1} (fun _ => Prop) True False z`
    ///   — `True` on `false`, `False` on `true`.
    fn bool_disc(&self, parent: &EnvDeclBuilder) -> Expr {
        let prop = Expr::prop();
        let mut db = EnvDeclBuilder::child_of(parent);
        let prop_motive = {
            let mut pb = EnvDeclBuilder::child_of(&db);
            let (w_id, _w) = pb.fresh_local(self.bool_t.clone());
            let lam = pb.mk_lam(w_id, BinderInfo::Default, self.bool_t.clone(), prop.clone());
            pb.finish_child(lam)
        };
        let (z_id, z) = db.fresh_local(self.bool_t.clone());
        let rec_app = Expr::apps(
            self.bool_rec_disc.clone(),
            [
                prop_motive,
                self.true_c.clone(),
                self.false_c.clone(),
                z.clone(),
            ],
        );
        let lam = db.mk_lam(z_id, BinderInfo::Default, self.bool_t.clone(), rec_app);
        db.finish_child(lam)
    }

    /// `False` from `h_ft : Eq Bool false true` via the True/False discriminator:
    /// `@Eq.subst.{1} Bool bdisc false true h_ft True.intro`.
    fn false_of_false_eq_true(&self, parent: &EnvDeclBuilder, h_ft: Expr) -> Expr {
        let bdisc = self.bool_disc(parent);
        Expr::apps(
            self.eq_subst_bool.clone(),
            [
                self.bool_t.clone(),
                bdisc,
                self.bool_false.clone(),
                self.bool_true.clone(),
                h_ft,
                self.true_intro.clone(),
            ],
        )
    }
}

impl Environment {
    /// WS-B entry: register the `Rat.ble` decidable order + reflections, flip
    /// `Rat.min` / `Rat.max` to reducible Definitions, and register the four
    /// characterizing equations + six lattice lemmas as constructive
    /// `Declaration::Theorem`s — eliminating the 12 opaque `Rat.*` min/max
    /// axioms.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid `Environment`.
    /// ENSURES: Idempotent — any target already present is left untouched, and
    ///          each builder guards on `get_const`.
    pub(crate) fn register_rat_minmax_proofs(&mut self) -> Result<(), EnvError> {
        // Dependencies: the live quotient `Rat`, `Rat.le`, the landed quotient
        // order Theorems (`Rat.le_refl`/`le_total`/`le_antisymm`), the Int
        // decidable-order reflections, Bool, Or, and Eq.
        self.init_rat_ord()?; // Rat, Rat.le, Rat.Raw.*, Int.le_cross_trans
        self.init_bool()?; // Bool, Bool.true/false, Bool.rec
        self.init_eq()?; // Eq, Eq.refl, Eq.symm, Eq.trans, Eq.subst
        self.init_or()?; // Or, Or.elim (for le_total case-splits)
        self.init_true_false()?; // True/True.intro/False/False.elim
        self.register_int_minmax_proofs()?; // Int.ble, Int.ble_eq_true_of_le
        self.register_int_minmax_def_prime()?; // Int.le_of_ble_eq_true
        self.rat_quotient_payoff_into_live()?; // Rat.le_antisymm
        {
            // Rat.le_refl / Rat.le_total / Rat.le_trans (quotient Theorems).
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_order_lemmas(&qc)?;
        }

        let c = RatMinMaxConsts::new();

        self.register_int_ble_eq_of_le_iff(&c)?;
        self.register_rat_ble(&c)?;
        self.register_rat_ble_eq_true_of_le(&c)?;
        self.register_rat_le_of_ble_eq_true(&c)?;
        self.register_rat_min(&c)?;
        self.register_rat_max(&c)?;
        self.register_rat_minmax_def(&c, "Rat.min_def", true)?;
        self.register_rat_minmax_def(&c, "Rat.max_def", false)?;
        self.register_rat_minmax_def_prime(&c, "Rat.min_def'", true)?;
        self.register_rat_minmax_def_prime(&c, "Rat.max_def'", false)?;
        self.register_rat_lattice_lemma(&c, "Rat.le_max_left", LatticeKind::LeMaxLeft)?;
        self.register_rat_lattice_lemma(&c, "Rat.le_max_right", LatticeKind::LeMaxRight)?;
        self.register_rat_lattice_lemma(&c, "Rat.min_le_left", LatticeKind::MinLeLeft)?;
        self.register_rat_lattice_lemma(&c, "Rat.min_le_right", LatticeKind::MinLeRight)?;
        self.register_rat_lattice_lemma(&c, "Rat.max_le", LatticeKind::MaxLe)?;
        self.register_rat_lattice_lemma(&c, "Rat.le_min", LatticeKind::LeMin)?;
        Ok(())
    }

    /// `Int.ble_eq_of_le_iff : ∀ a b a' b' : Int,
    ///    (Int.le a b → Int.le a' b') → (Int.le a' b' → Int.le a b) →
    ///    Eq Bool (Int.ble a b) (Int.ble a' b')`.
    ///
    /// Bool-extensionality from the two `Int.le` directions, via the landed Int
    /// reflections. Outer `@Bool.rec.{0}` on `ble a b` with a dependent
    /// discriminant motive (as in `Int.min_def'`):
    ///   * `true` branch: `le a b` (le_of_ble), `le a' b'` (fwd),
    ///     `ble a' b' = true` (ble_eq_true); goal `Eq Bool true (ble a' b')`
    ///     closed by `Eq.symm`.
    ///   * `false` branch: inner `@Bool.rec.{0}` on `ble a' b'`; the `false`
    ///     sub-branch is `Eq.refl false`; the `true` sub-branch derives
    ///     `le a' b'`→`le a b`→`ble a b = true`, contradicting the outer
    ///     `ble a b = false` via the `True`/`False` discriminator.
    fn register_int_ble_eq_of_le_iff(&mut self, c: &RatMinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Int.ble_eq_of_le_iff");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let build = |is_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bv_id, bv) = b.fresh_local(c.int.clone());
            let (a2_id, a2) = b.fresh_local(c.int.clone());
            let (b2_id, b2) = b.fresh_local(c.int.clone());
            let fwd_ty = Expr::pi(
                BinderInfo::Default,
                c.int_le(a.clone(), bv.clone()),
                c.int_le(a2.clone(), b2.clone()),
            );
            let bwd_ty = Expr::pi(
                BinderInfo::Default,
                c.int_le(a2.clone(), b2.clone()),
                c.int_le(a.clone(), bv.clone()),
            );
            let (fwd_id, fwd) = b.fresh_local(fwd_ty.clone());
            let (bwd_id, bwd) = b.fresh_local(bwd_ty.clone());

            let ble = c.int_ble(a.clone(), bv.clone());
            let ble2 = c.int_ble(a2.clone(), b2.clone());
            let concl = c.eq_bool(ble.clone(), ble2.clone());

            let result = if !is_value {
                concl
            } else {
                // Outer dependent motive on `ble a b`:
                //   fun (x:Bool) => Eq Bool (ble a b) x → Eq Bool x (ble a' b').
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = mb.fresh_local(c.bool_t.clone());
                    let heq_ty = c.eq_bool(ble.clone(), x.clone());
                    let (heq_id, _) = mb.fresh_local(heq_ty.clone());
                    let body = c.eq_bool(x.clone(), ble2.clone());
                    let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, body);
                    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.bool_t.clone(), body);
                    mb.finish_child(lam)
                };

                // false minor: fun (h : ble a b = false) => Eq Bool false (ble a' b').
                let false_minor = {
                    let mut fb = EnvDeclBuilder::child_of(&b);
                    let h_ty = c.eq_bool(ble.clone(), c.bool_false.clone());
                    let (h_id, h) = fb.fresh_local(h_ty.clone());

                    // Inner dependent motive on `ble a' b'`:
                    //   fun (y:Bool) => Eq Bool (ble a' b') y → Eq Bool false y.
                    let inner_motive = {
                        let mut ib = EnvDeclBuilder::child_of(&fb);
                        let (y_id, y) = ib.fresh_local(c.bool_t.clone());
                        let heq_ty = c.eq_bool(ble2.clone(), y.clone());
                        let (heq_id, _) = ib.fresh_local(heq_ty.clone());
                        let body = c.eq_bool(c.bool_false.clone(), y.clone());
                        let body = ib.mk_pi(heq_id, BinderInfo::Default, heq_ty, body);
                        let lam = ib.mk_lam(y_id, BinderInfo::Default, c.bool_t.clone(), body);
                        ib.finish_child(lam)
                    };
                    let inner_false = {
                        let mut yb = EnvDeclBuilder::child_of(&fb);
                        let heq_ty = c.eq_bool(ble2.clone(), c.bool_false.clone());
                        let (heq_id, _) = yb.fresh_local(heq_ty.clone());
                        let refl = c.refl_bool(c.bool_false.clone());
                        let lam = yb.mk_lam(heq_id, BinderInfo::Default, heq_ty, refl);
                        yb.finish_child(lam)
                    };
                    let inner_true = {
                        let mut yb = EnvDeclBuilder::child_of(&fb);
                        let heq_ty = c.eq_bool(ble2.clone(), c.bool_true.clone());
                        let (heq_id, heq2) = yb.fresh_local(heq_ty.clone());
                        // le a' b' := le_of_ble a' b' heq2; le a b := bwd; ble a b = true.
                        let le2 = Expr::apps(
                            c.int_le_of_ble_eq_true.clone(),
                            [a2.clone(), b2.clone(), heq2.clone()],
                        );
                        let le_ab = Expr::app(bwd.clone(), le2);
                        let ble_true = Expr::apps(
                            c.int_ble_eq_true_of_le.clone(),
                            [a.clone(), bv.clone(), le_ab],
                        );
                        // false_eq_true : Eq Bool false true
                        //   := Eq.trans (Eq.symm h) ble_true.
                        let h_symm = c.symm_bool(ble.clone(), c.bool_false.clone(), h.clone());
                        let false_eq_true = c.trans_bool(
                            c.bool_false.clone(),
                            ble.clone(),
                            c.bool_true.clone(),
                            h_symm,
                            ble_true,
                        );
                        let false_proof = c.false_of_false_eq_true(&yb, false_eq_true);
                        let goal = c.eq_bool(c.bool_false.clone(), c.bool_true.clone());
                        let elim = Expr::apps(c.false_elim.clone(), [goal, false_proof]);
                        let lam = yb.mk_lam(heq_id, BinderInfo::Default, heq_ty, elim);
                        yb.finish_child(lam)
                    };
                    let inner_rec = Expr::apps(
                        c.bool_rec_prop.clone(),
                        [inner_motive, inner_false, inner_true, ble2.clone()],
                    );
                    let applied = Expr::app(inner_rec, c.refl_bool(ble2.clone()));
                    let lam = fb.mk_lam(h_id, BinderInfo::Default, h_ty, applied);
                    fb.finish_child(lam)
                };

                // true minor: fun (h : ble a b = true) => Eq Bool true (ble a' b').
                let true_minor = {
                    let mut tb = EnvDeclBuilder::child_of(&b);
                    let h_ty = c.eq_bool(ble.clone(), c.bool_true.clone());
                    let (h_id, h) = tb.fresh_local(h_ty.clone());
                    let le_ab = Expr::apps(
                        c.int_le_of_ble_eq_true.clone(),
                        [a.clone(), bv.clone(), h.clone()],
                    );
                    let le2 = Expr::app(fwd.clone(), le_ab);
                    let ble2_true = Expr::apps(
                        c.int_ble_eq_true_of_le.clone(),
                        [a2.clone(), b2.clone(), le2],
                    );
                    // Eq.symm ble2_true : Eq Bool true (ble a' b').
                    let body = c.symm_bool(ble2.clone(), c.bool_true.clone(), ble2_true);
                    let lam = tb.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                    tb.finish_child(lam)
                };

                let outer_rec = Expr::apps(
                    c.bool_rec_prop.clone(),
                    [motive, false_minor, true_minor, ble.clone()],
                );
                Expr::app(outer_rec, c.refl_bool(ble.clone()))
            };

            let bind = |b: &EnvDeclBuilder, id, ty, body| {
                if is_value {
                    b.mk_lam(id, BinderInfo::Default, ty, body)
                } else {
                    b.mk_pi(id, BinderInfo::Default, ty, body)
                }
            };
            let e = bind(&b, bwd_id, bwd_ty, result);
            let e = bind(&b, fwd_id, fwd_ty, e);
            let e = bind(&b, b2_id, c.int.clone(), e);
            let e = bind(&b, a2_id, c.int.clone(), e);
            let e = bind(&b, bv_id, c.int.clone(), e);
            let e = bind(&b, a_id, c.int.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// `Rat.ble : Rat → Rat → Bool`, the binary `Quot.lift` of
    /// `raw_ble p q := Int.ble (num p · eff q) (num q · eff p)` into `Bool`.
    fn register_rat_ble(&mut self, c: &RatMinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ble");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ble_type = Expr::pi(
            BinderInfo::Default,
            c.ratq.clone(),
            Expr::pi(BinderInfo::Default, c.ratq.clone(), c.bool_t.clone()),
        );

        let ble_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());

            let inner_lift = |parent: &EnvDeclBuilder, first: &Expr, bb: &Expr| -> Expr {
                let g = {
                    let mut bi = EnvDeclBuilder::child_of(parent);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let body = c.raw_ble(first, &q);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bi.finish_child(lam)
                };
                let h = {
                    let mut bi = EnvDeclBuilder::child_of(parent);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let (q2_id, q2) = bi.fresh_local(c.raw.clone());
                    let hh = c.equiv(q.clone(), q2.clone());
                    let (hq_id, hq) = bi.fresh_local(hh.clone());
                    let fwd = c.le_impl_right(&bi, first, &q, &q2, &hq);
                    let nq_effq2 = c.mul(c.num(q.clone()), c.eff(q2.clone()));
                    let nq2_effq = c.mul(c.num(q2.clone()), c.eff(q.clone()));
                    let hq_symm = c.symm_int(nq_effq2, nq2_effq, hq.clone());
                    let bwd = c.le_impl_right(&bi, first, &q2, &q, &hq_symm);
                    let a_lhs = c.mul(c.num(first.clone()), c.eff(q.clone()));
                    let a_rhs = c.mul(c.num(q.clone()), c.eff(first.clone()));
                    let a2_lhs = c.mul(c.num(first.clone()), c.eff(q2.clone()));
                    let a2_rhs = c.mul(c.num(q2.clone()), c.eff(first.clone()));
                    let body = c.ble_eq_of_le_iff(a_lhs, a_rhs, a2_lhs, a2_rhs, fwd, bwd);
                    let lam = bi.mk_lam(hq_id, BinderInfo::Default, hh, body);
                    let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.raw.clone(), lam);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bi.finish_child(lam)
                };
                Expr::apps(
                    c.quot_lift_bool.clone(),
                    [
                        c.raw.clone(),
                        c.raw_equiv.clone(),
                        c.bool_t.clone(),
                        g,
                        h,
                        bb.clone(),
                    ],
                )
            };

            let outer_f = {
                let mut bo = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bo.fresh_local(c.raw.clone());
                let body = inner_lift(&bo, &p, &bv);
                let lam = bo.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bo.finish_child(lam)
            };

            let outer_h = {
                let mut bh = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bh.fresh_local(c.raw.clone());
                let (p2_id, p2) = bh.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), p2.clone());
                let (hp_id, hp) = bh.fresh_local(hyp.clone());

                let beta = {
                    let mut bm = EnvDeclBuilder::child_of(&bh);
                    let (bb_id, bb) = bm.fresh_local(c.ratq.clone());
                    let lhs = inner_lift(&bm, &p, &bb);
                    let rhs = inner_lift(&bm, &p2, &bb);
                    let body = c.eq_bool(lhs, rhs);
                    let lam = bm.mk_lam(bb_id, BinderInfo::Default, c.ratq.clone(), body);
                    bm.finish_child(lam)
                };

                let minor = {
                    let mut bn = EnvDeclBuilder::child_of(&bh);
                    let (q_id, q) = bn.fresh_local(c.raw.clone());
                    let fwd = c.le_impl_left(&bn, &p, &p2, &q, &hp);
                    let np_effp2 = c.mul(c.num(p.clone()), c.eff(p2.clone()));
                    let np2_effp = c.mul(c.num(p2.clone()), c.eff(p.clone()));
                    let hp_symm = c.symm_int(np_effp2, np2_effp, hp.clone());
                    let bwd = c.le_impl_left(&bn, &p2, &p, &q, &hp_symm);
                    let a_lhs = c.mul(c.num(p.clone()), c.eff(q.clone()));
                    let a_rhs = c.mul(c.num(q.clone()), c.eff(p.clone()));
                    let a2_lhs = c.mul(c.num(p2.clone()), c.eff(q.clone()));
                    let a2_rhs = c.mul(c.num(q.clone()), c.eff(p2.clone()));
                    let body = c.ble_eq_of_le_iff(a_lhs, a_rhs, a2_lhs, a2_rhs, fwd, bwd);
                    let lam = bn.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bn.finish_child(lam)
                };

                let ind = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta, minor, bv.clone()],
                );
                let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
                let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.raw.clone(), lam);
                let lam = bh.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), lam);
                bh.finish_child(lam)
            };

            let body = Expr::apps(
                c.quot_lift_bool.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    c.bool_t.clone(),
                    outer_f,
                    outer_h,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ble_type,
            value: ble_value,
            is_reducible: true,
        })
    }

    /// `Rat.ble_eq_true_of_le : ∀ a b : Rat, Rat.le a b → Eq Bool (Rat.ble a b) true`.
    /// Double `Quot.ind`; on reps the goal ≡ `Int.ble_eq_true_of_le (np·eq)(nq·ep)`.
    fn register_rat_ble_eq_true_of_le(&mut self, c: &RatMinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ble_eq_true_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let goal_at = |a: &Expr, bv: &Expr, c: &RatMinMaxConsts| -> Expr {
            Expr::pi(
                BinderInfo::Default,
                c.rat_le_app(a.clone(), bv.clone()),
                c.eq_bool(c.rat_ble_app(a.clone(), bv.clone()), c.bool_true.clone()),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let body = goal_at(&a, &bv, c);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        let value = self.rat_ble_iff_value(c, &goal_at, true);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.le_of_ble_eq_true : ∀ a b : Rat, Eq Bool (Rat.ble a b) true → Rat.le a b`.
    /// Double `Quot.ind`; on reps the goal ≡ `Int.le_of_ble_eq_true (np·eq)(nq·ep)`.
    fn register_rat_le_of_ble_eq_true(&mut self, c: &RatMinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_ble_eq_true");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let goal_at = |a: &Expr, bv: &Expr, c: &RatMinMaxConsts| -> Expr {
            Expr::pi(
                BinderInfo::Default,
                c.eq_bool(c.rat_ble_app(a.clone(), bv.clone()), c.bool_true.clone()),
                c.rat_le_app(a.clone(), bv.clone()),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let body = goal_at(&a, &bv, c);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        let value = self.rat_ble_iff_value(c, &goal_at, false);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Shared double-`Quot.ind` builder for the two `Rat.ble`↔`Rat.le`
    /// directions. `forward = true` builds the `le → ble = true` direction
    /// (`Rat.ble_eq_true_of_le`), `false` the reverse. On reps `p,q` the goal
    /// ι-reduces to the corresponding `Int` reflection at the cross-products.
    fn rat_ble_iff_value(
        &self,
        c: &RatMinMaxConsts,
        goal_at: &dyn Fn(&Expr, &Expr, &RatMinMaxConsts) -> Expr,
        forward: bool,
    ) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());

        let beta_a = {
            let mut bm = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = bm.fresh_local(c.ratq.clone());
            let body = {
                let mut bb = EnvDeclBuilder::child_of(&bm);
                let (y_id, y) = bb.fresh_local(c.ratq.clone());
                let g = goal_at(&x, &y, c);
                let e = bb.mk_pi(y_id, BinderInfo::Default, c.ratq.clone(), g);
                bb.finish_child(e)
            };
            let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
            bm.finish_child(lam)
        };

        let minor_a = {
            let mut bp = EnvDeclBuilder::child_of(&b);
            let (p_id, p) = bp.fresh_local(c.raw.clone());
            let mk_p = c.quot_mk(p.clone());

            let beta_b = {
                let mut bmb = EnvDeclBuilder::child_of(&bp);
                let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                let body = goal_at(&mk_p, &y, c);
                let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                bmb.finish_child(lam)
            };

            let minor_b = {
                let mut bq = EnvDeclBuilder::child_of(&bp);
                let (q_id, q) = bq.fresh_local(c.raw.clone());
                let lhs = c.mul(c.num(p.clone()), c.eff(q.clone()));
                let rhs = c.mul(c.num(q.clone()), c.eff(p.clone()));
                let body = if forward {
                    Expr::apps(c.int_ble_eq_true_of_le.clone(), [lhs, rhs])
                } else {
                    Expr::apps(c.int_le_of_ble_eq_true.clone(), [lhs, rhs])
                };
                let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                bq.finish_child(lam)
            };

            let ind_b = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
            );
            let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
            bp.finish_child(lam)
        };

        let ind_a = Expr::apps(
            c.quot_ind.clone(),
            [
                c.raw.clone(),
                c.raw_equiv.clone(),
                beta_a,
                minor_a,
                a.clone(),
            ],
        );
        let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
        b.finish(e)
    }

    /// `Rat.min a b := @Bool.rec (fun _ => Rat) b a (Rat.ble a b)` (a if a≤b else b).
    fn register_rat_min(&mut self, c: &RatMinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.min");
        if self.get_const(&name).map(|i| i.kind)
            == Some(crate::env::types::ConstantKind::Definition)
        {
            return Ok(());
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.ratq.clone(),
            Expr::pi(BinderInfo::Default, c.ratq.clone(), c.ratq.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let body = c.bool_rec_rat(bv.clone(), a.clone(), c.rat_ble_app(a.clone(), bv.clone()));
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Rat.max a b := @Bool.rec (fun _ => Rat) a b (Rat.ble a b)` (b if a≤b else a).
    fn register_rat_max(&mut self, c: &RatMinMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.max");
        if self.get_const(&name).map(|i| i.kind)
            == Some(crate::env::types::ConstantKind::Definition)
        {
            return Ok(());
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.ratq.clone(),
            Expr::pi(BinderInfo::Default, c.ratq.clone(), c.ratq.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let body = c.bool_rec_rat(a.clone(), bv.clone(), c.rat_ble_app(a.clone(), bv.clone()));
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Rat.min_def : ∀ a b, Rat.le a b → Eq Rat (Rat.min a b) a` (is_min=true) and
    /// `Rat.max_def : ∀ a b, Rat.le a b → Eq Rat (Rat.max a b) b` (is_min=false).
    /// Transports `@Eq.refl Rat rhs` across `Rat.ble a b = true` (the `Rat.ble`
    /// reflection of `h : Rat.le a b`), collapsing the `Bool.rec`.
    fn register_rat_minmax_def(
        &mut self,
        c: &RatMinMaxConsts,
        name: &str,
        is_min: bool,
    ) -> Result<(), EnvError> {
        let nm = Name::from_string(name);
        if self.get_const(&nm).map(|i| i.kind) == Some(crate::env::types::ConstantKind::Theorem) {
            return Ok(());
        }
        if self.get_const(&nm).is_some() {
            return Ok(());
        }
        let target = if is_min { &c.rat_min } else { &c.rat_max };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let le_ab = c.rat_le_app(a.clone(), bv.clone());
            let (h_id, _h) = b.fresh_local(le_ab.clone());
            let lhs = Expr::apps(target.clone(), [a.clone(), bv.clone()]);
            let rhs = if is_min { a.clone() } else { bv.clone() };
            let concl = c.eq_rat(lhs, rhs);
            let e = b.mk_pi(h_id, BinderInfo::Default, le_ab, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let le_ab = c.rat_le_app(a.clone(), bv.clone());
            let (h_id, h) = b.fresh_local(le_ab.clone());

            // min: Bool.rec b a x, rhs a.  max: Bool.rec a b x, rhs b.
            let (f_case, t_case, rhs) = if is_min {
                (bv.clone(), a.clone(), a.clone())
            } else {
                (a.clone(), bv.clone(), bv.clone())
            };

            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = mb.fresh_local(c.bool_t.clone());
                let lhs = c.bool_rec_rat(f_case.clone(), t_case.clone(), x);
                let body = c.eq_rat(lhs, rhs.clone());
                let lam = mb.mk_lam(x_id, BinderInfo::Default, c.bool_t.clone(), body);
                mb.finish_child(lam)
            };
            let h_true = Expr::apps(c.rat_ble_eq_true_of_le.clone(), [a.clone(), bv.clone(), h]);
            let h_symm = c.symm_bool(
                c.rat_ble_app(a.clone(), bv.clone()),
                c.bool_true.clone(),
                h_true,
            );
            let refl = c.refl_rat(rhs.clone());
            let body = Expr::apps(
                c.eq_subst_bool.clone(),
                [
                    c.bool_t.clone(),
                    motive,
                    c.bool_true.clone(),
                    c.rat_ble_app(a.clone(), bv.clone()),
                    h_symm,
                    refl,
                ],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, le_ab, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.min_def' : ∀ a b, Rat.le b a → Eq Rat (Rat.min a b) b` (is_min=true) and
    /// `Rat.max_def' : ∀ a b, Rat.le b a → Eq Rat (Rat.max a b) a` (is_min=false).
    /// Dependent `Bool.rec` split on `Rat.ble a b`: false branch is `Eq.refl`;
    /// true branch derives `Rat.le a b` (via `Rat.le_of_ble_eq_true`) and combines
    /// with the incoming `Rat.le b a` through the landed `Rat.le_antisymm`.
    fn register_rat_minmax_def_prime(
        &mut self,
        c: &RatMinMaxConsts,
        name: &str,
        is_min: bool,
    ) -> Result<(), EnvError> {
        let nm = Name::from_string(name);
        if self.get_const(&nm).map(|i| i.kind) == Some(crate::env::types::ConstantKind::Theorem) {
            return Ok(());
        }
        if self.get_const(&nm).is_some() {
            return Ok(());
        }
        let target = if is_min { &c.rat_min } else { &c.rat_max };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let le_ba = c.rat_le_app(bv.clone(), a.clone());
            let (h_id, _h) = b.fresh_local(le_ba.clone());
            let lhs = Expr::apps(target.clone(), [a.clone(), bv.clone()]);
            let rhs = if is_min { bv.clone() } else { a.clone() };
            let concl = c.eq_rat(lhs, rhs);
            let e = b.mk_pi(h_id, BinderInfo::Default, le_ba, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let le_ba = c.rat_le_app(bv.clone(), a.clone());
            let (h_id, h) = b.fresh_local(le_ba.clone());

            // min: f=b, t=a, rhs=b.  max: f=a, t=b, rhs=a.
            let (f_case, t_case, rhs) = if is_min {
                (bv.clone(), a.clone(), bv.clone())
            } else {
                (a.clone(), bv.clone(), a.clone())
            };

            let ble = c.rat_ble_app(a.clone(), bv.clone());
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = mb.fresh_local(c.bool_t.clone());
                let heq_ty = c.eq_bool(ble.clone(), x.clone());
                let (heq_id, _) = mb.fresh_local(heq_ty.clone());
                let lhs = c.bool_rec_rat(f_case.clone(), t_case.clone(), x.clone());
                let body = c.eq_rat(lhs, rhs.clone());
                let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, body);
                let lam = mb.mk_lam(x_id, BinderInfo::Default, c.bool_t.clone(), body);
                mb.finish_child(lam)
            };

            let false_minor = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(ble.clone(), c.bool_false.clone());
                let (heq_id, _) = fb.fresh_local(heq_ty.clone());
                let refl = c.refl_rat(rhs.clone());
                let lam = fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, refl);
                fb.finish_child(lam)
            };

            let true_minor = {
                let mut tb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(ble.clone(), c.bool_true.clone());
                let (heq_id, heq) = tb.fresh_local(heq_ty.clone());
                let le_ab = Expr::apps(
                    c.rat_le_of_ble_eq_true.clone(),
                    [a.clone(), bv.clone(), heq.clone()],
                );
                let eq_ab = Expr::apps(
                    c.rat_le_antisymm.clone(),
                    [a.clone(), bv.clone(), le_ab, h.clone()],
                );
                // min: goal Eq Rat a b (t=a,rhs=b) — use eq_ab.
                // max: goal Eq Rat b a (t=b,rhs=a) — symm eq_ab.
                let body = if is_min {
                    eq_ab
                } else {
                    c.symm_rat(a.clone(), bv.clone(), eq_ab)
                };
                let lam = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
                tb.finish_child(lam)
            };

            let rec_app = Expr::apps(
                c.bool_rec_prop.clone(),
                [motive, false_minor, true_minor, ble.clone()],
            );
            let applied = Expr::app(rec_app, c.refl_bool(ble.clone()));

            let e = b.mk_lam(h_id, BinderInfo::Default, le_ba, applied);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Shared lattice-lemma registrar (idempotent / skip-if-already-Theorem).
    fn register_rat_lattice_lemma(
        &mut self,
        c: &RatMinMaxConsts,
        name: &str,
        kind: LatticeKind,
    ) -> Result<(), EnvError> {
        let nm = Name::from_string(name);
        if self.get_const(&nm).map(|i| i.kind) == Some(crate::env::types::ConstantKind::Theorem) {
            return Ok(());
        }
        if self.get_const(&nm).is_some() {
            return Ok(());
        }
        let (ty, value) = kind.build(c);
        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Which lattice lemma a `register_rat_lattice_lemma` call builds.
#[derive(Clone, Copy)]
enum LatticeKind {
    LeMaxLeft,
    LeMaxRight,
    MinLeLeft,
    MinLeRight,
    MaxLe,
    LeMin,
}

impl LatticeKind {
    fn build(self, c: &RatMinMaxConsts) -> (Expr, Expr) {
        match self {
            LatticeKind::LeMaxLeft => build_le_max(c, true),
            LatticeKind::LeMaxRight => build_le_max(c, false),
            LatticeKind::MinLeLeft => build_min_le(c, true),
            LatticeKind::MinLeRight => build_min_le(c, false),
            LatticeKind::MaxLe => build_max_le(c),
            LatticeKind::LeMin => build_le_min(c),
        }
    }
}

/// `Rat.le_max_left : ∀ a b, Rat.le a (Rat.max a b)` (left=true) /
/// `Rat.le_max_right : ∀ a b, Rat.le b (Rat.max a b)` (left=false).
///
/// `Rat.max a b ≡ Bool.rec a b (Rat.ble a b)`; dependent split on `Rat.ble a b`.
fn build_le_max(c: &RatMinMaxConsts, left: bool) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());
        let (bv_id, bv) = b.fresh_local(c.ratq.clone());
        let lhs = if left { a.clone() } else { bv.clone() };
        let body = c.rat_le_app(lhs, c.rat_max_app(a.clone(), bv.clone()));
        let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
        b.finish(e)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());
        let (bv_id, bv) = b.fresh_local(c.ratq.clone());
        let ble = c.rat_ble_app(a.clone(), bv.clone());
        let lhs = if left { a.clone() } else { bv.clone() };

        // motive := fun (x:Bool) => Eq Bool (ble a b) x → Rat.le lhs (Bool.rec a b x).
        let motive = c.lattice_motive(&b, &ble, |x| {
            c.rat_le_app(lhs.clone(), c.bool_rec_rat(a.clone(), bv.clone(), x))
        });

        // false minor: Bool.rec a b false ≡ a.
        let false_minor = {
            let mut fb = EnvDeclBuilder::child_of(&b);
            let heq_ty = c.eq_bool(ble.clone(), c.bool_false.clone());
            let (heq_id, heq) = fb.fresh_local(heq_ty.clone());
            let body = if left {
                Expr::app(c.rat_le_refl.clone(), a.clone()) // a ≤ a
            } else {
                c.le_from_total_false(&fb, &a, &bv, &heq) // b ≤ a
            };
            let lam = fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
            fb.finish_child(lam)
        };
        // true minor: Bool.rec a b true ≡ b.
        let true_minor = {
            let mut tb = EnvDeclBuilder::child_of(&b);
            let heq_ty = c.eq_bool(ble.clone(), c.bool_true.clone());
            let (heq_id, heq) = tb.fresh_local(heq_ty.clone());
            let body = if left {
                Expr::apps(
                    c.rat_le_of_ble_eq_true.clone(),
                    [a.clone(), bv.clone(), heq],
                ) // a ≤ b
            } else {
                Expr::app(c.rat_le_refl.clone(), bv.clone()) // b ≤ b
            };
            let lam = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
            tb.finish_child(lam)
        };

        let applied = c.lattice_apply(motive, false_minor, true_minor, &ble);
        let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), applied);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
        b.finish(e)
    };
    (ty, value)
}

/// `Rat.min_le_left : ∀ a b, Rat.le (Rat.min a b) a` (left=true) /
/// `Rat.min_le_right : ∀ a b, Rat.le (Rat.min a b) b` (left=false).
///
/// `Rat.min a b ≡ Bool.rec b a (Rat.ble a b)`; dependent split on `Rat.ble a b`.
fn build_min_le(c: &RatMinMaxConsts, left: bool) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());
        let (bv_id, bv) = b.fresh_local(c.ratq.clone());
        let rhs = if left { a.clone() } else { bv.clone() };
        let body = c.rat_le_app(c.rat_min_app(a.clone(), bv.clone()), rhs);
        let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
        b.finish(e)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());
        let (bv_id, bv) = b.fresh_local(c.ratq.clone());
        let ble = c.rat_ble_app(a.clone(), bv.clone());
        let rhs = if left { a.clone() } else { bv.clone() };

        // motive := fun (x:Bool) => Eq Bool (ble a b) x → Rat.le (Bool.rec b a x) rhs.
        let motive = c.lattice_motive(&b, &ble, |x| {
            c.rat_le_app(c.bool_rec_rat(bv.clone(), a.clone(), x), rhs.clone())
        });
        // false minor: Bool.rec b a false ≡ b.
        let false_minor = {
            let mut fb = EnvDeclBuilder::child_of(&b);
            let heq_ty = c.eq_bool(ble.clone(), c.bool_false.clone());
            let (heq_id, heq) = fb.fresh_local(heq_ty.clone());
            let body = if left {
                c.le_from_total_false(&fb, &a, &bv, &heq) // b ≤ a
            } else {
                Expr::app(c.rat_le_refl.clone(), bv.clone()) // b ≤ b
            };
            let lam = fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
            fb.finish_child(lam)
        };
        // true minor: Bool.rec b a true ≡ a.
        let true_minor = {
            let mut tb = EnvDeclBuilder::child_of(&b);
            let heq_ty = c.eq_bool(ble.clone(), c.bool_true.clone());
            let (heq_id, heq) = tb.fresh_local(heq_ty.clone());
            let body = if left {
                Expr::app(c.rat_le_refl.clone(), a.clone()) // a ≤ a
            } else {
                Expr::apps(
                    c.rat_le_of_ble_eq_true.clone(),
                    [a.clone(), bv.clone(), heq],
                ) // a ≤ b
            };
            let lam = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
            tb.finish_child(lam)
        };

        let applied = c.lattice_apply(motive, false_minor, true_minor, &ble);
        let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), applied);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
        b.finish(e)
    };
    (ty, value)
}

/// `Rat.max_le : ∀ a b c, Rat.le a c → Rat.le b c → Rat.le (Rat.max a b) c`.
/// `Rat.max a b ≡ Bool.rec a b (Rat.ble a b)`; non-dependent split:
///   false → max ≡ a, goal `a ≤ c` = h1 ; true → max ≡ b, goal `b ≤ c` = h2.
fn build_max_le(c: &RatMinMaxConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());
        let (bv_id, bv) = b.fresh_local(c.ratq.clone());
        let (cc_id, cc) = b.fresh_local(c.ratq.clone());
        let h1_ty = c.rat_le_app(a.clone(), cc.clone());
        let h2_ty = c.rat_le_app(bv.clone(), cc.clone());
        let (h1_id, _) = b.fresh_local(h1_ty.clone());
        let (h2_id, _) = b.fresh_local(h2_ty.clone());
        let concl = c.rat_le_app(c.rat_max_app(a.clone(), bv.clone()), cc.clone());
        let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
        let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
        let e = b.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), e);
        let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
        b.finish(e)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());
        let (bv_id, bv) = b.fresh_local(c.ratq.clone());
        let (cc_id, cc) = b.fresh_local(c.ratq.clone());
        let h1_ty = c.rat_le_app(a.clone(), cc.clone());
        let h2_ty = c.rat_le_app(bv.clone(), cc.clone());
        let (h1_id, h1) = b.fresh_local(h1_ty.clone());
        let (h2_id, h2) = b.fresh_local(h2_ty.clone());
        let ble = c.rat_ble_app(a.clone(), bv.clone());

        let motive = c.lattice_motive_nondep(&b, |x| {
            c.rat_le_app(c.bool_rec_rat(a.clone(), bv.clone(), x), cc.clone())
        });
        let applied = Expr::apps(
            c.bool_rec_prop.clone(),
            [motive, h1.clone(), h2.clone(), ble.clone()],
        );

        let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, applied);
        let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
        let e = b.mk_lam(cc_id, BinderInfo::Default, c.ratq.clone(), e);
        let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), e);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
        b.finish(e)
    };
    (ty, value)
}

/// `Rat.le_min : ∀ a b c, Rat.le c a → Rat.le c b → Rat.le c (Rat.min a b)`.
/// `Rat.min a b ≡ Bool.rec b a (Rat.ble a b)`; non-dependent split:
///   false → min ≡ b, goal `c ≤ b` = h2 ; true → min ≡ a, goal `c ≤ a` = h1.
fn build_le_min(c: &RatMinMaxConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());
        let (bv_id, bv) = b.fresh_local(c.ratq.clone());
        let (cc_id, cc) = b.fresh_local(c.ratq.clone());
        let h1_ty = c.rat_le_app(cc.clone(), a.clone());
        let h2_ty = c.rat_le_app(cc.clone(), bv.clone());
        let (h1_id, _) = b.fresh_local(h1_ty.clone());
        let (h2_id, _) = b.fresh_local(h2_ty.clone());
        let concl = c.rat_le_app(cc.clone(), c.rat_min_app(a.clone(), bv.clone()));
        let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
        let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
        let e = b.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), e);
        let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
        b.finish(e)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.ratq.clone());
        let (bv_id, bv) = b.fresh_local(c.ratq.clone());
        let (cc_id, cc) = b.fresh_local(c.ratq.clone());
        let h1_ty = c.rat_le_app(cc.clone(), a.clone());
        let h2_ty = c.rat_le_app(cc.clone(), bv.clone());
        let (h1_id, h1) = b.fresh_local(h1_ty.clone());
        let (h2_id, h2) = b.fresh_local(h2_ty.clone());
        let ble = c.rat_ble_app(a.clone(), bv.clone());

        let motive = c.lattice_motive_nondep(&b, |x| {
            c.rat_le_app(cc.clone(), c.bool_rec_rat(bv.clone(), a.clone(), x))
        });
        let applied = Expr::apps(
            c.bool_rec_prop.clone(),
            [motive, h2.clone(), h1.clone(), ble.clone()],
        );

        let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, applied);
        let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
        let e = b.mk_lam(cc_id, BinderInfo::Default, c.ratq.clone(), e);
        let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), e);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
        b.finish(e)
    };
    (ty, value)
}

impl RatMinMaxConsts {
    /// Dependent lattice motive `fun (x:Bool) => Eq Bool ble x → <body(x)>`.
    fn lattice_motive(
        &self,
        parent: &EnvDeclBuilder,
        ble: &Expr,
        body_of: impl Fn(Expr) -> Expr,
    ) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(self.bool_t.clone());
        let heq_ty = self.eq_bool(ble.clone(), x.clone());
        let (heq_id, _) = mb.fresh_local(heq_ty.clone());
        let body = body_of(x.clone());
        let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, body);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, self.bool_t.clone(), body);
        mb.finish_child(lam)
    }

    /// Non-dependent lattice motive `fun (x:Bool) => <body(x)>`.
    fn lattice_motive_nondep(
        &self,
        parent: &EnvDeclBuilder,
        body_of: impl Fn(Expr) -> Expr,
    ) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(self.bool_t.clone());
        let body = body_of(x.clone());
        let lam = mb.mk_lam(x_id, BinderInfo::Default, self.bool_t.clone(), body);
        mb.finish_child(lam)
    }

    /// `@Bool.rec.{0} motive false_minor true_minor ble @ @Eq.refl Bool ble`.
    fn lattice_apply(&self, motive: Expr, false_minor: Expr, true_minor: Expr, ble: &Expr) -> Expr {
        let rec_app = Expr::apps(
            self.bool_rec_prop.clone(),
            [motive, false_minor, true_minor, ble.clone()],
        );
        Expr::app(rec_app, self.refl_bool(ble.clone()))
    }

    /// In a `Rat.ble a b = false` context (`heq`), derive `Rat.le b a` from
    /// `Rat.le_total a b` via `Or.rec`: the `a ≤ b` disjunct contradicts `heq`
    /// (since `a ≤ b → ble a b = true`), discharged via the `True`/`False` bool
    /// discriminator; the `b ≤ a` disjunct is the goal.
    fn le_from_total_false(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        bv: &Expr,
        heq: &Expr,
    ) -> Expr {
        let goal = self.rat_le_app(bv.clone(), a.clone());
        let le_ab = self.rat_le_app(a.clone(), bv.clone());
        let le_ba = self.rat_le_app(bv.clone(), a.clone());
        let total = Expr::apps(self.rat_le_total.clone(), [a.clone(), bv.clone()]);
        // motive := fun (_ : Or (a≤b) (b≤a)) => Rat.le b a.
        let or_motive = {
            let mut om = EnvDeclBuilder::child_of(parent);
            let or_ty = Expr::apps(self.or_c.clone(), [le_ab.clone(), le_ba.clone()]);
            let (hh_id, _hh) = om.fresh_local(or_ty.clone());
            let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ty, goal.clone());
            om.finish_child(lam)
        };
        let left_fn = {
            let mut lb = EnvDeclBuilder::child_of(parent);
            let (hab_id, hab) = lb.fresh_local(le_ab.clone());
            let ble_true = Expr::apps(
                self.rat_ble_eq_true_of_le.clone(),
                [a.clone(), bv.clone(), hab],
            );
            let ble = self.rat_ble_app(a.clone(), bv.clone());
            let heq_symm = self.symm_bool(ble.clone(), self.bool_false.clone(), heq.clone());
            let false_eq_true = self.trans_bool(
                self.bool_false.clone(),
                ble.clone(),
                self.bool_true.clone(),
                heq_symm,
                ble_true,
            );
            let false_proof = self.false_of_false_eq_true(&lb, false_eq_true);
            let elim = Expr::apps(self.false_elim.clone(), [goal.clone(), false_proof]);
            let lam = lb.mk_lam(hab_id, BinderInfo::Default, le_ab.clone(), elim);
            lb.finish_child(lam)
        };
        let right_fn = {
            let mut rb = EnvDeclBuilder::child_of(parent);
            let (hba_id, hba) = rb.fresh_local(le_ba.clone());
            let lam = rb.mk_lam(hba_id, BinderInfo::Default, le_ba.clone(), hba);
            rb.finish_child(lam)
        };
        // @Or.rec (a≤b) (b≤a) motive left right total.
        Expr::apps(
            self.or_rec.clone(),
            [le_ab, le_ba, or_motive, left_fn, right_fn, total],
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};

    fn env() -> Environment {
        let mut env = Environment::new();
        env.register_rat_minmax_proofs()
            .expect("register_rat_minmax_proofs should succeed");
        env
    }

    #[test]
    fn test_rat_ble_is_reducible_definition() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.ble"))
            .expect("Rat.ble registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        assert!(info.value.is_some());
    }

    #[test]
    fn test_rat_min_max_are_reducible_definitions() {
        let env = env();
        for name in ["Rat.min", "Rat.max"] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a reducible Definition, got {:?}",
                info.kind
            );
            assert!(info.value.is_some(), "{name} must have a body");
        }
    }

    #[test]
    fn test_rat_minmax_theorems_constructive() {
        let env = env();
        for name in [
            "Int.ble_eq_of_le_iff",
            "Rat.ble_eq_true_of_le",
            "Rat.le_of_ble_eq_true",
            "Rat.min_def",
            "Rat.max_def",
            "Rat.min_def'",
            "Rat.max_def'",
            "Rat.le_max_left",
            "Rat.le_max_right",
            "Rat.min_le_left",
            "Rat.min_le_right",
            "Rat.max_le",
            "Rat.le_min",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be a Theorem, got {:?}",
                info.kind
            );
            let q = env
                .proof_quality(&Name::from_string(name))
                .expect("proof_quality");
            assert!(
                matches!(q, ProofQuality::Constructive),
                "{name} must be Constructive, got {q:?}"
            );
        }
    }

    #[test]
    fn test_rat_minmax_axiom_deps_empty() {
        let env = env();
        for name in [
            "Rat.min_def",
            "Rat.max_def",
            "Rat.min_def'",
            "Rat.max_def'",
            "Rat.le_max_left",
            "Rat.le_max_right",
            "Rat.min_le_left",
            "Rat.min_le_right",
            "Rat.max_le",
            "Rat.le_min",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered, axiom_deps should return Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{name} must have empty axiom closure, got {domain_deps:?}"
            );
        }
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.register_rat_minmax_proofs().expect("first");
        env.register_rat_minmax_proofs().expect("second idempotent");
    }
}
