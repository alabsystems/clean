// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of the symmetric `Int.min` / `Int.max` characterizing
//! equations:
//!
//! ```text
//! Int.min_def' : ∀ a b : Int, Int.le b a → Eq Int (Int.min a b) b
//! Int.max_def' : ∀ a b : Int, Int.le b a → Eq Int (Int.max a b) a
//! ```
//!
//! These replace the prior `Declaration::Axiom` registrations of
//! `Int.min_def'` / `Int.max_def'` in
//! `algebra_abs_int.rs::init_int_minmax`. Registering them here as
//! `Declaration::Theorem`s before `init_int_minmax` runs means the two
//! `Declaration::Axiom` blocks are skipped (this proof guards both names with a
//! `get_const` check; `init_int_minmax` does *not* guard them, so this register
//! function MUST run first — see the integration note below).
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b   := Int.NonNeg (Int.sub b a)                          -- reducible
//! Int.isNonNeg := @Int.rec (fun _ => Bool) (fun _ => true) (fun _ => false)
//! Int.ble a b  := Int.isNonNeg (Int.sub b a)                        -- reducible
//! Int.min a b  := @Bool.rec (fun _ => Int) b a (Int.ble a b)        -- reducible
//! Int.max a b  := @Bool.rec (fun _ => Int) a b (Int.ble a b)        -- reducible
//! inductive Int.NonNeg : Int → Prop where | mk (n : Nat) : NonNeg (ofNat n)
//! ```
//!
//! So `Int.min` is `b` when `Int.ble a b ≡ Bool.false` and `a` when
//! `Int.ble a b ≡ Bool.true`; `Int.max` is dual.
//!
//! # Reverse reflection — `Int.le_of_ble_eq_true`
//!
//! `Int.le_of_ble_eq_true : ∀ a b, Eq Bool (Int.ble a b) Bool.true → Int.le a b`
//! is the converse of the landed `Int.ble_eq_true_of_le`. It is built from a
//! genuinely general inversion lemma `Int.isNonNeg_eq_true_NonNeg`:
//!
//! ```text
//! ∀ i : Int, Eq Bool (Int.isNonNeg i) Bool.true → Int.NonNeg i
//! ```
//!
//! proved by `@Int.rec.{0}` on `i` (implication-valued motive threading the
//! hypothesis):
//!
//! * `Int.ofNat n` branch: `Int.isNonNeg (ofNat n) ≡ Bool.true`, so the goal
//!   `NonNeg (ofNat n)` is closed by `@Int.NonNeg.mk n` (ignoring the now-trivial
//!   `true = true` hypothesis).
//! * `Int.negSucc n` branch: `Int.isNonNeg (negSucc n) ≡ Bool.false`, so the
//!   threaded hypothesis is `Eq Bool Bool.false Bool.true`. A `Bool` discriminator
//!   `bdisc := @Bool.rec.{1} (fun _ => Prop) True False` (`True` on `false`,
//!   `False` on `true`) turns it into `False` via
//!   `@Eq.subst.{1} … bdisc false true h True.intro : False`, discharged by
//!   `@False.elim.{0}`.
//!
//! Then `Int.le_of_ble_eq_true a b := Int.isNonNeg_eq_true_NonNeg (Int.sub b a)`,
//! because `Int.ble a b ≡ Int.isNonNeg (Int.sub b a)` and
//! `Int.le a b ≡ Int.NonNeg (Int.sub b a)`.
//!
//! # `Int.min_def'` / `Int.max_def'`
//!
//! Case-split on `Int.ble a b` via `@Bool.rec.{0}` (the motive lands in the
//! `Prop`-valued goal) with a *dependent* motive carrying the discriminant
//! equation:
//!
//! ```text
//! fun (x : Bool) => Eq Bool (Int.ble a b) x → Eq Int (@Bool.rec (fun _=>Int) f t x) rhs
//! ```
//!
//! applied to `Int.ble a b` and `@Eq.refl Bool (Int.ble a b)`.
//!
//! * `false` minor: `@Bool.rec (fun _=>Int) f t false ≡ f`. For `min` `f = b`,
//!   `rhs = b`; for `max` `f = a`, `rhs = a`. Either way the goal reduces to a
//!   reflexivity (`@Eq.refl Int rhs`), ignoring the discriminant hypothesis.
//! * `true` minor: `@Bool.rec (fun _=>Int) f t true ≡ t`. The discriminant
//!   hypothesis is `heq : Int.ble a b = Bool.true`; `Int.le_of_ble_eq_true a b heq`
//!   gives `Int.le a b`, and combined with the incoming `h : Int.le b a` the
//!   landed constructive `Int.le_antisymm a b` yields `Eq Int a b`. For `min`
//!   (`t = a`, `rhs = b`) the goal is `Eq Int a b` — use it directly. For `max`
//!   (`t = b`, `rhs = a`) the goal is `Eq Int b a` — apply `@Eq.symm`.
//!
//! # Axiom closure
//!
//! Mentions only `Int`, `Int.ble`, `Int.isNonNeg`, `Int.sub`, `Int.le`,
//! `Int.min`, `Int.max`, `Int.ofNat`, `Int.NonNeg`, `Int.NonNeg.mk`, `Int.rec`,
//! `Bool`, `Bool.true`, `Bool.false`, `Bool.rec`, `Nat`, `True`, `True.intro`,
//! `False`, `False.elim`, the constructive `Int.le_antisymm`, and the
//! foundational `Eq` family (`Eq.refl`, `Eq.symm`, `Eq.subst`). None is a
//! `Declaration::Axiom`, so each registered theorem is `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across the proof terms.
struct MinMaxPrimeConsts {
    int: Expr,
    nat: Expr,
    bool_t: Expr,
    bool_true: Expr,
    bool_false: Expr,
    prop: Expr,
    int_rec_0: Expr,
    bool_rec_0: Expr,
    bool_rec_1: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub: Expr,
    int_le: Expr,
    int_min: Expr,
    int_max: Expr,
    int_nonneg: Expr,
    nonneg_mk: Expr,
    is_nonneg: Expr,
    ble: Expr,
    le_antisymm: Expr,
    is_nonneg_inv: Expr,
    le_of_ble: Expr,
    true_const: Expr,
    true_intro: Expr,
    false_const: Expr,
    false_elim: Expr,
    eq_c: Expr,
    eq_c_bool: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_subst_bool: Expr,
}

impl MinMaxPrimeConsts {
    fn new() -> Self {
        let t1 = Level::succ(Level::zero());
        Self {
            int: Expr::const_(Name::from_string("Int"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_t: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            prop: Expr::prop(),
            // Int.rec producing a Prop (Sort 0) proof.
            int_rec_0: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            // Bool.rec into a Prop (Sort 0) motive — used for the dependent
            // discriminant-equation case split in min_def'/max_def'.
            bool_rec_0: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            // Bool.rec into Int / Prop : Sort 1.
            bool_rec_1: Expr::const_(Name::from_string("Bool.rec"), vec![t1.clone()]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_min: Expr::const_(Name::from_string("Int.min"), vec![]),
            int_max: Expr::const_(Name::from_string("Int.max"), vec![]),
            int_nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            is_nonneg: Expr::const_(Name::from_string("Int.isNonNeg"), vec![]),
            ble: Expr::const_(Name::from_string("Int.ble"), vec![]),
            le_antisymm: Expr::const_(Name::from_string("Int.le_antisymm"), vec![]),
            is_nonneg_inv: Expr::const_(Name::from_string("Int.isNonNeg_eq_true_NonNeg"), vec![]),
            le_of_ble: Expr::const_(Name::from_string("Int.le_of_ble_eq_true"), vec![]),
            true_const: Expr::const_(Name::from_string("True"), vec![]),
            true_intro: Expr::const_(Name::from_string("True.intro"), vec![]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            // The goal closed by False.elim is `NonNeg _ : Prop` (Sort 0).
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            // Eq over Int : Type 0 → Eq.{1}.
            eq_c: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            // Eq over Bool : Type 0 → Eq.{1}.
            eq_c_bool: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![t1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![t1.clone()]),
            // Eq.subst over Bool indices.
            eq_subst_bool: Expr::const_(Name::from_string("Eq.subst"), vec![t1]),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_sub.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [a, b])
    }
    fn ble_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.ble.clone(), [a, b])
    }
    fn is_nonneg_of(&self, i: Expr) -> Expr {
        Expr::app(self.is_nonneg.clone(), i)
    }
    fn nonneg_of(&self, i: Expr) -> Expr {
        Expr::app(self.int_nonneg.clone(), i)
    }
    /// `Eq Int x y`.
    fn eq_int(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_c.clone(), [self.int.clone(), x, y])
    }
    /// `Eq Bool x y`.
    fn eq_bool(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_c_bool.clone(), [self.bool_t.clone(), x, y])
    }
    /// `@Eq.refl.{1} Int v`.
    fn refl_int(&self, v: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int.clone(), v])
    }
    /// `@Bool.rec.{1} (fun _ => Int) f t scrut`.
    fn bool_rec_int(&self, f: Expr, t: Expr, scrut: Expr) -> Expr {
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(self.bool_t.clone());
            let e = b.mk_lam(
                x_id,
                BinderInfo::Default,
                self.bool_t.clone(),
                self.int.clone(),
            );
            b.finish(e)
        };
        Expr::apps(self.bool_rec_1.clone(), [motive, f, t, scrut])
    }
}

impl Environment {
    /// Register `Int.isNonNeg_eq_true_NonNeg`, `Int.le_of_ble_eq_true`,
    /// `Int.min_def'` and `Int.max_def'` as kernel-checked
    /// `Declaration::Theorem`s.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid `Environment`.
    /// ENSURES: On success, `Int.min_def'` and `Int.max_def'` are
    ///          `Declaration::Theorem`s with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — any target already present (with any declaration
    ///          kind) is left untouched.
    pub(crate) fn register_int_minmax_def_prime(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Dependencies: Int.min/max/ble/isNonNeg (and their reducible bodies),
        // Int.le/NonNeg, Int.sub, Bool, Eq, True/False, and Int.le_antisymm.
        self.register_int_minmax_proofs()?; // Int.min/max/ble/isNonNeg defs
        self.init_int_ord()?; // Int.le, Int.NonNeg(.mk/.rec), Int.sub, Int.rec
        self.init_bool()?; // Bool, Bool.true/false, Bool.rec
        self.init_eq()?; // Eq, Eq.refl, Eq.symm, Eq.subst
        self.init_true_false()?; // True, True.intro, False, False.elim
        self.register_int_le_antisymm_proof()?; // constructive Int.le_antisymm

        let c = MinMaxPrimeConsts::new();

        self.register_is_nonneg_inv(&c)?;
        self.register_le_of_ble_eq_true(&c)?;
        // Int.min_def' : ∀ a b, Int.le b a → Eq Int (Int.min a b) b
        self.register_minmax_prime(&c, "Int.min_def'", true)?;
        // Int.max_def' : ∀ a b, Int.le b a → Eq Int (Int.max a b) a
        self.register_minmax_prime(&c, "Int.max_def'", false)?;

        Ok(())
    }

    /// `Int.isNonNeg_eq_true_NonNeg :
    ///    ∀ i : Int, Eq Bool (Int.isNonNeg i) Bool.true → Int.NonNeg i`.
    fn register_is_nonneg_inv(&mut self, c: &MinMaxPrimeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Int.isNonNeg_eq_true_NonNeg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Type: ∀ i, Eq Bool (isNonNeg i) true → NonNeg i
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.int.clone());
            let h_ty = c.eq_bool(c.is_nonneg_of(i.clone()), c.bool_true.clone());
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = c.nonneg_of(i.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(i_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        // Value: fun (i : Int) => @Int.rec.{0} motive ofNat_case negSucc_case i.
        let value = {
            let mut b = EnvDeclBuilder::new();

            // motive := fun (x : Int) => Eq Bool (isNonNeg x) true → NonNeg x
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = mb.fresh_local(c.int.clone());
                let h_ty = c.eq_bool(c.is_nonneg_of(x.clone()), c.bool_true.clone());
                let (h_id, _h) = mb.fresh_local(h_ty.clone());
                let body = c.nonneg_of(x.clone());
                let body = mb.mk_pi(h_id, BinderInfo::Default, h_ty, body);
                let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                mb.finish_child(lam)
            };

            // ofNat case: fun (n : Nat) (_ : Eq Bool true true) => @Int.NonNeg.mk n
            //   goal `NonNeg (ofNat n)` ≡ `Int.NonNeg.mk n` since isNonNeg(ofNat n) ≡ true.
            let of_nat_case = {
                let mut ob = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ob.fresh_local(c.nat.clone());
                let h_ty = c.eq_bool(c.is_nonneg_of(c.of_nat(n.clone())), c.bool_true.clone());
                let (h_id, _h) = ob.fresh_local(h_ty.clone());
                let mk = Expr::app(c.nonneg_mk.clone(), n.clone());
                let lam = ob.mk_lam(h_id, BinderInfo::Default, h_ty, mk);
                let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                ob.finish_child(lam)
            };

            // negSucc case: fun (n : Nat) (h : Eq Bool false true) =>
            //   @False.elim.{0} (NonNeg (negSucc n)) (bdisc-derived False)
            let neg_succ_case = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = nb.fresh_local(c.nat.clone());
                let neg_succ_n = c.neg_succ(n.clone());
                let h_ty = c.eq_bool(c.is_nonneg_of(neg_succ_n.clone()), c.bool_true.clone());
                let (h_id, h) = nb.fresh_local(h_ty.clone());

                // bdisc := fun (x : Bool) => @Bool.rec.{1} (fun _ => Prop) True False x
                //   bdisc false ≡ True, bdisc true ≡ False.
                let bdisc = {
                    let mut db = EnvDeclBuilder::child_of(&nb);
                    let prop_motive = {
                        let mut pb = EnvDeclBuilder::child_of(&db);
                        let (y_id, _y) = pb.fresh_local(c.bool_t.clone());
                        let lam =
                            pb.mk_lam(y_id, BinderInfo::Default, c.bool_t.clone(), c.prop.clone());
                        pb.finish_child(lam)
                    };
                    let (x_id, x) = db.fresh_local(c.bool_t.clone());
                    // The motive maps each Bool to `Prop`, a type living in
                    // `Sort 1`, so the discriminator recursor is `Bool.rec.{1}`.
                    let rec_app = Expr::apps(
                        c.bool_rec_1.clone(),
                        [
                            prop_motive,
                            c.true_const.clone(),
                            c.false_const.clone(),
                            x.clone(),
                        ],
                    );
                    let lam = db.mk_lam(x_id, BinderInfo::Default, c.bool_t.clone(), rec_app);
                    db.finish_child(lam)
                };

                // false_proof : False
                //   := @Eq.subst.{1} Bool bdisc Bool.false Bool.true h True.intro
                //   (h : false = true ; bdisc false ≡ True (True.intro) ; result bdisc true ≡ False)
                let false_proof = Expr::apps(
                    c.eq_subst_bool.clone(),
                    [
                        c.bool_t.clone(),
                        bdisc,
                        c.bool_false.clone(),
                        c.bool_true.clone(),
                        h.clone(),
                        c.true_intro.clone(),
                    ],
                );

                // goal: NonNeg (negSucc n)
                let goal = c.nonneg_of(neg_succ_n.clone());
                let elim = Expr::apps(c.false_elim.clone(), [goal, false_proof]);

                let lam = nb.mk_lam(h_id, BinderInfo::Default, h_ty, elim);
                let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                nb.finish_child(lam)
            };

            // fun (i : Int) => @Int.rec.{0} motive ofNat_case negSucc_case i
            let (i_id, i) = b.fresh_local(c.int.clone());
            let rec_app = Expr::apps(
                c.int_rec_0.clone(),
                [motive, of_nat_case, neg_succ_case, i.clone()],
            );
            let lam = b.mk_lam(i_id, BinderInfo::Default, c.int.clone(), rec_app);
            b.finish(lam)
        };

        // SOUNDNESS: Real kernel-checked proof term. `@Int.rec.{0}` on `i` with an
        // implication-valued motive splits on the constructor: `ofNat n` closes
        // `NonNeg (ofNat n)` directly via `@Int.NonNeg.mk n` (the threaded
        // `isNonNeg (ofNat n) ≡ true` hypothesis is discarded); `negSucc n` has
        // `isNonNeg (negSucc n) ≡ false`, so the threaded `false = true` hypothesis
        // is transported by the `True`/`False` `Bool` discriminator
        // (`@Bool.rec.{1}` + `@Eq.subst.{1}` + `True.intro`) to `False` and
        // discharged with `@False.elim.{0}`. No `sorry`, no self-reference, no
        // domain-axiom dependency.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Int.le_of_ble_eq_true :
    ///    ∀ a b : Int, Eq Bool (Int.ble a b) Bool.true → Int.le a b`.
    fn register_le_of_ble_eq_true(&mut self, c: &MinMaxPrimeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Int.le_of_ble_eq_true");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Type: ∀ a b, Eq Bool (ble a b) true → Int.le a b
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bv_id, bv) = b.fresh_local(c.int.clone());
            let h_ty = c.eq_bool(c.ble_app(a.clone(), bv.clone()), c.bool_true.clone());
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = c.le(a.clone(), bv.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        // Value: fun a b h => Int.isNonNeg_eq_true_NonNeg (Int.sub b a) h
        //   (ble a b ≡ isNonNeg (sub b a) ; le a b ≡ NonNeg (sub b a)).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bv_id, bv) = b.fresh_local(c.int.clone());
            let h_ty = c.eq_bool(c.ble_app(a.clone(), bv.clone()), c.bool_true.clone());
            let (h_id, h) = b.fresh_local(h_ty.clone());
            let sub_ba = c.sub(bv.clone(), a.clone());
            let body = Expr::apps(c.is_nonneg_inv.clone(), [sub_ba, h.clone()]);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: Real kernel-checked proof term. `Int.ble a b` delta-reduces
        // to `Int.isNonNeg (Int.sub b a)` and `Int.le a b` to
        // `Int.NonNeg (Int.sub b a)`, so the constructive inversion lemma
        // `Int.isNonNeg_eq_true_NonNeg (Int.sub b a) h` inhabits the goal directly.
        // No `sorry`, no self-reference, no domain-axiom dependency.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Shared builder for `Int.min_def'` (`is_min = true`, conclusion
    /// `min a b = b`) and `Int.max_def'` (`is_min = false`, conclusion
    /// `max a b = a`). Both take `h : Int.le b a`.
    fn register_minmax_prime(
        &mut self,
        c: &MinMaxPrimeConsts,
        name: &str,
        is_min: bool,
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let target = if is_min { &c.int_min } else { &c.int_max };

        // Type: ∀ a b, Int.le b a → Eq Int (target a b) rhs
        //   min: rhs = b ; max: rhs = a.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bv_id, bv) = b.fresh_local(c.int.clone());
            let le_ba = c.le(bv.clone(), a.clone());
            let (h_id, _h) = b.fresh_local(le_ba.clone());
            let lhs = Expr::apps(target.clone(), [a.clone(), bv.clone()]);
            let rhs = if is_min { bv.clone() } else { a.clone() };
            let concl = c.eq_int(lhs, rhs);
            let e = b.mk_pi(h_id, BinderInfo::Default, le_ba, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bv_id, bv) = b.fresh_local(c.int.clone());
            let le_ba = c.le(bv.clone(), a.clone());
            let (h_id, h) = b.fresh_local(le_ba.clone());

            // min a b = Bool.rec b a (ble a b) ; max a b = Bool.rec a b (ble a b).
            // min: f = b, t = a, rhs = b.   max: f = a, t = b, rhs = a.
            let (f_case, t_case, rhs) = if is_min {
                (bv.clone(), a.clone(), bv.clone())
            } else {
                (a.clone(), bv.clone(), a.clone())
            };

            // motive := fun (x : Bool) =>
            //   Eq Bool (ble a b) x → Eq Int (Bool.rec f t x) rhs
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = mb.fresh_local(c.bool_t.clone());
                let heq_ty = c.eq_bool(c.ble_app(a.clone(), bv.clone()), x.clone());
                let (heq_id, _heq) = mb.fresh_local(heq_ty.clone());
                let lhs = c.bool_rec_int(f_case.clone(), t_case.clone(), x.clone());
                let body = c.eq_int(lhs, rhs.clone());
                let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, body);
                let lam = mb.mk_lam(x_id, BinderInfo::Default, c.bool_t.clone(), body);
                mb.finish_child(lam)
            };

            // false minor: fun (_ : Eq Bool (ble a b) false) => @Eq.refl Int rhs
            //   Bool.rec f t false ≡ f ; min f=b=rhs, max f=a=rhs → refl.
            let false_minor = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(c.ble_app(a.clone(), bv.clone()), c.bool_false.clone());
                let (heq_id, _heq) = fb.fresh_local(heq_ty.clone());
                let refl = c.refl_int(rhs.clone());
                let lam = fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, refl);
                fb.finish_child(lam)
            };

            // true minor: fun (heq : Eq Bool (ble a b) true) => proof of Eq Int t rhs
            let true_minor = {
                let mut tb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(c.ble_app(a.clone(), bv.clone()), c.bool_true.clone());
                let (heq_id, heq) = tb.fresh_local(heq_ty.clone());
                // le_ab : Int.le a b := Int.le_of_ble_eq_true a b heq
                let le_ab = Expr::apps(c.le_of_ble.clone(), [a.clone(), bv.clone(), heq.clone()]);
                // eq_ab : Eq Int a b := Int.le_antisymm a b le_ab h
                let eq_ab = Expr::apps(
                    c.le_antisymm.clone(),
                    [a.clone(), bv.clone(), le_ab, h.clone()],
                );
                // min: goal Eq Int a b — use eq_ab directly (t = a, rhs = b).
                // max: goal Eq Int b a — symm eq_ab (t = b, rhs = a).
                let body = if is_min {
                    eq_ab
                } else {
                    Expr::apps(
                        c.eq_symm.clone(),
                        [c.int.clone(), a.clone(), bv.clone(), eq_ab],
                    )
                };
                let lam = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
                tb.finish_child(lam)
            };

            // @Bool.rec.{0} motive false_minor true_minor (ble a b)
            //   : Eq Bool (ble a b) (ble a b) → Eq Int (min/max a b) rhs
            //   (the motive lands in Prop : Sort 0, so the recursor is .{0}).
            let rec_app = Expr::apps(
                c.bool_rec_0.clone(),
                [
                    motive,
                    false_minor,
                    true_minor,
                    c.ble_app(a.clone(), bv.clone()),
                ],
            );
            // apply to @Eq.refl Bool (ble a b)
            let refl_ble = Expr::apps(
                c.eq_refl.clone(),
                [c.bool_t.clone(), c.ble_app(a.clone(), bv.clone())],
            );
            let applied = Expr::app(rec_app, refl_ble);

            let e = b.mk_lam(h_id, BinderInfo::Default, le_ba, applied);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: Real kernel-checked proof term. `@Bool.rec.{0}` case-splits on
        // `Int.ble a b` with a dependent (Prop-valued) motive carrying the
        // discriminant equation;
        // applied to `@Eq.refl Bool (Int.ble a b)`. The `false` minor closes the
        // reduced goal with `@Eq.refl Int`; the `true` minor derives `Int.le a b`
        // from the discriminant via the constructive inversion
        // `Int.le_of_ble_eq_true` and combines it with the incoming `Int.le b a`
        // through the constructive `Int.le_antisymm` (plus `@Eq.symm` for `max`).
        // No `sorry`, no self-reference, no domain-axiom dependency. Replaces the
        // prior `Declaration::Axiom` in `algebra_abs_int.rs::init_int_minmax`.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};

    fn env() -> Environment {
        let mut env = Environment::new();
        env.register_int_minmax_def_prime()
            .expect("register_int_minmax_def_prime should succeed");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a kernel-checked Theorem, got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "{name} Theorem must retain its proof value"
        );
        let q = env
            .proof_quality(&Name::from_string(name))
            .expect("proof_quality should be reported");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "{name} must be Constructive (no domain axiom in closure), got {q:?}"
        );
    }

    #[test]
    fn test_int_min_def_prime_is_constructive_theorem() {
        let env = env();
        assert_constructive_theorem(&env, "Int.min_def'");
    }

    #[test]
    fn test_int_max_def_prime_is_constructive_theorem() {
        let env = env();
        assert_constructive_theorem(&env, "Int.max_def'");
    }

    #[test]
    fn test_int_minmax_prime_helpers_constructive() {
        let env = env();
        assert_constructive_theorem(&env, "Int.isNonNeg_eq_true_NonNeg");
        assert_constructive_theorem(&env, "Int.le_of_ble_eq_true");
    }

    #[test]
    fn test_int_minmax_def_prime_axiom_deps_empty() {
        let env = env();
        for name in [
            "Int.min_def'",
            "Int.max_def'",
            "Int.le_of_ble_eq_true",
            "Int.isNonNeg_eq_true_NonNeg",
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
    fn test_int_minmax_def_prime_idempotent() {
        let mut env = Environment::new();
        env.register_int_minmax_def_prime().expect("first");
        env.register_int_minmax_def_prime()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.min_def'"))
            .expect("Int.min_def' should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }
}
