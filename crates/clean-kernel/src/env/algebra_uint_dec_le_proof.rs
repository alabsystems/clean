// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `≤` / `<` order for the single-constructor `Nat`-wrapper types
//! `UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize`/`Float` — real kernel terms
//! (NO `sorry`, NO axiom). These back the `instLE<T>` / `instLT<T>` and the
//! axiom-free `instDecidable<T>Le` / `instDecidable<T>Lt` instances so
//! `if ((x : UInt8) ≤ y)` / `if ((x : UInt8) < y)` / `decide` over a wrapper
//! ordering resolve their `[LE <T>]` / `[Decidable …]` arguments and fire
//! instead of emitting a synthetic `sorry` at elaboration time.
//!
//! Each `<T>` is `structure <T> where val : Nat` — i.e. `<T>.mk : Nat → <T>`,
//! reducible projection `<T>.val : <T> → Nat` with `<T>.val (<T>.mk n) ≡ n` (ι).
//! Order on `<T>` is therefore order on the underlying `Nat`, decided through
//! the (axiom-free) `Nat.decLe` / `Nat.decLt` decision procedures
//! (`algebra_nat_dec_le_proof.rs`).
//!
//! # Definitions (all reducible, axiom-free)
//!
//! ```text
//! <T>.le : <T> → <T> → Prop := fun a b => Nat.le (<T>.val a) (<T>.val b)
//! <T>.lt : <T> → <T> → Prop := fun a b => Nat.lt (<T>.val a) (<T>.val b)
//! instLE<T> : LE <T> := @LE.mk.{0} <T> <T>.le
//! instLT<T> : LT <T> := @LT.mk.{0} <T> <T>.lt
//!
//! <T>.decLe : (a b : <T>) → Decidable (<T>.le a b) :=
//!   fun (a b : <T>) => Nat.decLe (<T>.val a) (<T>.val b)
//! <T>.decLt : (a b : <T>) → Decidable (<T>.lt a b) :=
//!   fun (a b : <T>) => Nat.decLt (<T>.val a) (<T>.val b)
//! ```
//!
//! `<T>.decLe`'s declared result `Decidable (<T>.le a b)` δ-unfolds `<T>.le` and
//! β-reduces to `Decidable (Nat.le (<T>.val a) (<T>.val b))`, which is exactly
//! the type of `Nat.decLe (<T>.val a) (<T>.val b)` — so the body is def-eq to
//! the declared type and the kernel accepts the `Definition` (NO axiom). The
//! `Nat.lt` case is identical via `Nat.decLt`. This is the wrapper analogue of
//! how `instDecidableEq<T>` wraps `Nat.decEq` on the `<T>.val` projections.
//!
//! # Decidable instances (typeclass form)
//!
//! ```text
//! instDecidable<T>Le : (a b : <T>) → Decidable (@LE.le.{0} <T> instLE<T> a b)
//!   := <T>.decLe
//! instDecidable<T>Lt : (a b : <T>) → Decidable (@LT.lt.{0} <T> instLT<T> a b)
//!   := <T>.decLt
//! ```
//!
//! `@LE.le.{0} <T> instLE<T> a b` reduces (`LE.le` projects field 0 of
//! `instLE<T> ≡ LE.mk <T> <T>.le`, i.e. `<T>.le`, then applies `a b`) to
//! `<T>.le a b`, def-eq to `Nat.le (<T>.val a) (<T>.val b)`. So `<T>.decLe`'s
//! value type-checks at the typeclass-form `instDecidable<T>Le` type. `LT` is
//! identical.
//!
//! # Axiom closure
//!
//! The terms mention only `<T>`, `<T>.val`, `Nat`, `Nat.le`/`Nat.lt`,
//! `Nat.decLe`/`Nat.decLt` (axiom-free, `algebra_nat_dec_le_proof.rs`),
//! `LE`/`LT`(`.mk`/`.le`/`.lt`), `Decidable` — all constructive (generated
//! recursors / reducible definitions / axiom-free decision procedures). So
//! `env.axiom_deps("<T>.decLe")` / `…("<T>.decLt")` and the four instances are
//! empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register the full `≤`/`<` order stack for a single-constructor
    /// `Nat`-wrapper structure `<name>` (`<name>.mk : Nat → <name>`, reducible
    /// `<name>.val`): `<name>.le`, `<name>.lt`, `instLE<name>`, `instLT<name>`,
    /// `<name>.decLe`, `<name>.decLt`, `instDecidable<name>Le`,
    /// `instDecidable<name>Lt` — all kernel-checked `Definition`s, axiom-free,
    /// and registered as `LE`/`LT`/`Decidable` class instances.
    ///
    /// # Contract
    ///
    /// REQUIRES: `<name>` + `<name>.val`, `Nat`, `Nat.le`/`Nat.lt`,
    ///           `Nat.decLe`/`Nat.decLt`, `LE`/`LT`(+ `.mk`/`.le`/`.lt`),
    ///           `Decidable` are registered (auto-initialized here).
    /// ENSURES: On success, every listed constant is a `Definition` (never an
    ///          `Axiom`) whose value type-checks at its declared type and whose
    ///          axiom closure is empty; the four instances are resolvable under
    ///          `LE`/`LT`/`Decidable`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_wrapper_dec_le_lt_proof(&mut self, name: &str) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // if this wrapper's carrier stub was import-suppressed (Fin-carrier
        // UInt8..64/USize/Float — see init_uint8..64), its dec-proof web is
        // suppressed with it; the genuine v4.31 declarations import instead.
        // Wrappers whose carriers remain (Char/String/Int default lanes)
        // register as before.
        if self.suppress_lossy_structure_stubs && self.get_const(&Name::from_string(name)).is_none()
        {
            return Ok(());
        }
        self.register_wrapper_dec_le_lt_proof_carrier(name, super::uint_wrapper_carrier(name))
    }

    /// Register the `≤`/`<` order stack for a single-constructor wrapper with an
    /// explicit `carrier`. For a `Nat` carrier the underlying value is `<T>.val`
    /// (`: <T> → Nat`); for a `Fin <T>.size` carrier it is
    /// `Fin.val (<T>.val ·)` (`: <T> → Nat`). In both cases order is `Nat.le`/
    /// `Nat.lt` on the underlying `Nat`, decided by axiom-free `Nat.decLe`/`Nat.decLt`.
    pub(crate) fn register_wrapper_dec_le_lt_proof_carrier(
        &mut self,
        name: &str,
        carrier: super::WrapperCarrier,
    ) -> Result<(), EnvError> {
        // v4.30 BitVec carrier (UInt8/16/32/64/USize): the order/decidability
        // stack is `BitVec`-shaped and transcribed against the oracle in a
        // dedicated builder.
        if let super::WrapperCarrier::BitVec(width) = &carrier {
            return self.register_wrapper_dec_le_lt_bitvec(name, width.clone());
        }
        let dec_le_name = format!("{name}.decLe");
        let dec_lt_name = format!("{name}.decLt");
        let inst_le_name = format!("instLE{name}");
        let inst_lt_name = format!("instLT{name}");
        let inst_dec_le_name = format!("instDecidable{name}Le");
        let inst_dec_lt_name = format!("instDecidable{name}Lt");

        // Dependencies.
        self.init_nat()?;
        self.init_le()?; // LE / LE.le / LE.mk / Nat.le
        self.init_lt()?; // LT / LT.lt / LT.mk / Nat.lt
        self.init_decidable()?;
        #[cfg(test)]
        if matches!(carrier, super::WrapperCarrier::Fin(_)) {
            self.init_fin()?; // Fin.val projection
        }
        // The axiom-free `Nat` decision procedures backing the leaves.
        self.register_nat_dec_le_lt_proof()?;

        // ----- shared constants -----
        let zero_lvl = Level::zero();
        let _nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let ty_c = Expr::const_(Name::from_string(name), vec![]);
        let val_c = Expr::const_(Name::from_string(&format!("{name}.val")), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let nat_dec_le = Expr::const_(Name::from_string("Nat.decLe"), vec![]);
        let nat_dec_lt = Expr::const_(Name::from_string("Nat.decLt"), vec![]);
        let prop = Expr::sort(Level::zero());
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let le_c = Expr::const_(Name::from_string("LE"), vec![zero_lvl.clone()]);
        let lt_c = Expr::const_(Name::from_string("LT"), vec![zero_lvl.clone()]);
        let le_mk = Expr::const_(Name::from_string("LE.mk"), vec![zero_lvl.clone()]);
        let lt_mk = Expr::const_(Name::from_string("LT.mk"), vec![zero_lvl.clone()]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![zero_lvl.clone()]);
        let lt_lt = Expr::const_(Name::from_string("LT.lt"), vec![zero_lvl.clone()]);
        #[cfg(test)]
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);

        // Underlying `Nat` of `x : <T>`:
        //  - Nat carrier:  `<T>.val x`
        //  - Fin carrier:  `@Fin.val <T>.size (<T>.val x)`
        let val = |x: Expr| -> Expr {
            let v = Expr::app(val_c.clone(), x);
            match &carrier {
                super::WrapperCarrier::Nat => v,
                #[cfg(test)]
                super::WrapperCarrier::Fin(size_lit) => {
                    Expr::apps(fin_val.clone(), [size_lit.clone(), v])
                }
                // BitVec is dispatched to `register_wrapper_dec_le_lt_bitvec`
                // at the top of the outer fn — this closure never runs for it.
                super::WrapperCarrier::BitVec(_) => unreachable!("BitVec carrier handled earlier"),
            }
        };

        // ── <name>.le / <name>.lt : <T> → <T> → Prop ──
        // value: fun (a b : <T>) => Nat.{le,lt} (<T>.val a) (<T>.val b)
        let order_def = |rel: &Expr| -> (Expr, Expr) {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _a) = b.fresh_local(ty_c.clone());
                let (bv_id, _bv) = b.fresh_local(ty_c.clone());
                let e = b.mk_pi(bv_id, BinderInfo::Default, ty_c.clone(), prop.clone());
                let e = b.mk_pi(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let body = Expr::apps(rel.clone(), [val(a.clone()), val(bv.clone())]);
                let e = b.mk_lam(bv_id, BinderInfo::Default, ty_c.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            (ty, value)
        };

        if self
            .get_const(&Name::from_string(&format!("{name}.le")))
            .is_none()
        {
            let (type_, value) = order_def(&nat_le);
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&format!("{name}.le")),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }
        if self
            .get_const(&Name::from_string(&format!("{name}.lt")))
            .is_none()
        {
            let (type_, value) = order_def(&nat_lt);
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&format!("{name}.lt")),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        let le_rel = Expr::const_(Name::from_string(&format!("{name}.le")), vec![]);
        let lt_rel = Expr::const_(Name::from_string(&format!("{name}.lt")), vec![]);

        // ── instLE<name> : LE <T> := @LE.mk.{0} <T> <T>.le ──
        let inst_le_type = Expr::app(le_c.clone(), ty_c.clone());
        let inst_lt_type = Expr::app(lt_c.clone(), ty_c.clone());
        if self.get_const(&Name::from_string(&inst_le_name)).is_none() {
            let value = Expr::apps(le_mk.clone(), [ty_c.clone(), le_rel.clone()]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_le_name),
                level_params: vec![],
                type_: inst_le_type.clone(),
                value,
                is_reducible: true,
            })?;
        }
        if self.get_const(&Name::from_string(&inst_lt_name)).is_none() {
            let value = Expr::apps(lt_mk.clone(), [ty_c.clone(), lt_rel.clone()]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_lt_name),
                level_params: vec![],
                type_: inst_lt_type.clone(),
                value,
                is_reducible: true,
            })?;
        }

        // ── <name>.decLe : (a b : <T>) → Decidable (<T>.le a b) ──
        //   := fun (a b : <T>) => Nat.decLe (<T>.val a) (<T>.val b)
        // ── <name>.decLt : (a b : <T>) → Decidable (<T>.lt a b) ──
        //   := fun (a b : <T>) => Nat.decLt (<T>.val a) (<T>.val b)
        let dec_def = |rel: &Expr, nat_dec: &Expr| -> (Expr, Expr) {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let concl = Expr::app(
                    dec.clone(),
                    Expr::apps(rel.clone(), [a.clone(), bv.clone()]),
                );
                let e = b.mk_pi(bv_id, BinderInfo::Default, ty_c.clone(), concl);
                let e = b.mk_pi(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let body = Expr::apps(nat_dec.clone(), [val(a.clone()), val(bv.clone())]);
                let e = b.mk_lam(bv_id, BinderInfo::Default, ty_c.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            (ty, value)
        };

        if self.get_const(&Name::from_string(&dec_le_name)).is_none() {
            let (type_, value) = dec_def(&le_rel, &nat_dec_le);
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&dec_le_name),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }
        if self.get_const(&Name::from_string(&dec_lt_name)).is_none() {
            let (type_, value) = dec_def(&lt_rel, &nat_dec_lt);
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&dec_lt_name),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // ── instDecidable<name>Le : (a b : <T>) → Decidable (@LE.le <T> instLE<T> a b) ──
        //   := <name>.decLe
        // ── instDecidable<name>Lt : (a b : <T>) → Decidable (@LT.lt <T> instLT<T> a b) ──
        //   := <name>.decLt
        // The typeclass-form result `@LE.le <T> instLE<T> a b` reduces to
        // `<T>.le a b`, def-eq to the `<T>.decLe` result, so the body checks.
        let inst_le_const = Expr::const_(Name::from_string(&inst_le_name), vec![]);
        let inst_lt_const = Expr::const_(Name::from_string(&inst_lt_name), vec![]);
        // `@LE.le.{0} <T> instLE<T> a b` / `@LT.lt.{0} <T> instLT<T> a b`
        let le_tc = |a: Expr, bv: Expr| {
            Expr::apps(le_le.clone(), [ty_c.clone(), inst_le_const.clone(), a, bv])
        };
        let lt_tc = |a: Expr, bv: Expr| {
            Expr::apps(lt_lt.clone(), [ty_c.clone(), inst_lt_const.clone(), a, bv])
        };

        let inst_dec_def = |tc: &dyn Fn(Expr, Expr) -> Expr, dec_const: Expr| -> (Expr, Expr) {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let concl = Expr::app(dec.clone(), tc(a.clone(), bv.clone()));
                let e = b.mk_pi(bv_id, BinderInfo::Default, ty_c.clone(), concl);
                let e = b.mk_pi(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            (ty, dec_const)
        };

        let (inst_dec_le_ty, inst_dec_le_val) = inst_dec_def(
            &le_tc,
            Expr::const_(Name::from_string(&dec_le_name), vec![]),
        );
        if self
            .get_const(&Name::from_string(&inst_dec_le_name))
            .is_none()
        {
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_dec_le_name),
                level_params: vec![],
                type_: inst_dec_le_ty.clone(),
                value: inst_dec_le_val,
                is_reducible: true,
            })?;
        }
        let (inst_dec_lt_ty, inst_dec_lt_val) = inst_dec_def(
            &lt_tc,
            Expr::const_(Name::from_string(&dec_lt_name), vec![]),
        );
        if self
            .get_const(&Name::from_string(&inst_dec_lt_name))
            .is_none()
        {
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_dec_lt_name),
                level_params: vec![],
                type_: inst_dec_lt_ty.clone(),
                value: inst_dec_lt_val,
                is_reducible: true,
            })?;
        }

        // ── Register the class instances ──
        // LE <T> / LT <T> so `≤`/`<` resolve their `[LE <T>]`/`[LT <T>]` args.
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(&inst_le_name),
            class_name: Name::from_string("LE"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_le_type),
            value: Some(Expr::const_(Name::from_string(&inst_le_name), vec![])),
        });
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(&inst_lt_name),
            class_name: Name::from_string("LT"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_lt_type),
            value: Some(Expr::const_(Name::from_string(&inst_lt_name), vec![])),
        });
        // Decidable — stripping the two explicit `<T>` binders leaves
        // `Decidable (@LE.le <T> instLE<T> ?a ?b)` (resp. `LT.lt`), exactly the
        // goal `resolve_decidable` constructs for `if ((x : <T>) ≤ y)`.
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(&inst_dec_le_name),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_dec_le_ty),
            value: Some(Expr::const_(Name::from_string(&inst_dec_le_name), vec![])),
        });
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(&inst_dec_lt_name),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_dec_lt_ty),
            value: Some(Expr::const_(Name::from_string(&inst_dec_lt_name), vec![])),
        });

        Ok(())
    }

    /// Register the v4.30 `≤`/`<`/`decLe`/`decLt` stack for a `BitVec`-carrier
    /// UInt/USize `<name>` (`<name>.toBitVec : <name> → BitVec <width>`):
    /// ```text
    /// <T>.le a b := @LE.le (BitVec w) (instLEBitVec w) a.toBitVec b.toBitVec
    /// <T>.lt a b := @LT.lt (BitVec w) (instLTBitVec w) a.toBitVec b.toBitVec
    /// <T>.decLe a b := dite (Nat.ble a.toNat b.toNat = true) (isTrue …) (isFalse …)
    /// <T>.decLt a b := dite (Nat.ble a.toNat.succ b.toNat = true) (isTrue …) (isFalse …)
    /// ```
    /// All value-def-eq to the oracle (the `Decidable` proof arguments are
    /// proof-irrelevant; the `Nat.ble`/`instDecidableEqBool` discriminants and
    /// `LE.le`/`instLEBitVec` structure match). Axiom-free.
    fn register_wrapper_dec_le_lt_bitvec(
        &mut self,
        name: &str,
        width: Expr,
    ) -> Result<(), EnvError> {
        let inst_le_name = format!("instLE{name}");
        let inst_lt_name = format!("instLT{name}");
        let inst_dec_le_name = format!("instDecidable{name}Le");
        let inst_dec_lt_name = format!("instDecidable{name}Lt");

        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_decidable()?;
        self.init_dite()?; // dite
        self.init_bitvec()?; // BitVec.toNat, instLEBitVec, instLTBitVec
        self.register_nat_ble_le_lemmas()?; // Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le

        let zero = Level::zero();
        let one = Level::succ(Level::zero());
        let _nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let ty_c = Expr::const_(Name::from_string(name), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bitvec_w = Expr::app(
            Expr::const_(Name::from_string("BitVec"), vec![]),
            width.clone(),
        );
        let to_bitvec = Expr::const_(Name::from_string(&format!("{name}.toBitVec")), vec![]);
        let bitvec_to_nat = Expr::const_(Name::from_string("BitVec.toNat"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_ble = Expr::const_(Name::from_string("Nat.ble"), vec![]);
        let dite = Expr::const_(Name::from_string("dite"), vec![one.clone()]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let inst_dec_eq_bool = Expr::const_(Name::from_string("instDecidableEqBool"), vec![]);
        let eq_bool = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [bool_c.clone(), l, r],
            )
        };
        let not_ = |p: Expr| {
            Expr::pi(
                BinderInfo::Default,
                p,
                Expr::const_(Name::from_string("False"), vec![]),
            )
        };
        let le_of_ble = Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]);
        let ble_eq_true_of_le = Expr::const_(Name::from_string("Nat.ble_eq_true_of_le"), vec![]);

        // a.toNat := @BitVec.toNat width (@<T>.toBitVec a)
        let to_nat = |a: &Expr| -> Expr {
            Expr::apps(
                bitvec_to_nat.clone(),
                [width.clone(), Expr::app(to_bitvec.clone(), a.clone())],
            )
        };
        let to_bv = |a: &Expr| -> Expr { Expr::app(to_bitvec.clone(), a.clone()) };

        // ── <T>.le / <T>.lt : <T> → <T> → Prop ──
        let prop = Expr::sort(Level::zero());
        for (suffix, rel, inst) in [
            ("le", "LE.le", "instLEBitVec"),
            ("lt", "LT.lt", "instLTBitVec"),
        ] {
            if self
                .get_const(&Name::from_string(&format!("{name}.{suffix}")))
                .is_some()
            {
                continue;
            }
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _a) = b.fresh_local(ty_c.clone());
                let (bv_id, _bv) = b.fresh_local(ty_c.clone());
                let e = b.mk_pi(bv_id, BinderInfo::Default, ty_c.clone(), prop.clone());
                let e = b.mk_pi(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let body = Expr::apps(
                    Expr::const_(Name::from_string(rel), vec![zero.clone()]),
                    [
                        bitvec_w.clone(),
                        Expr::app(Expr::const_(Name::from_string(inst), vec![]), width.clone()),
                        to_bv(&a),
                        to_bv(&bv),
                    ],
                );
                let e = b.mk_lam(bv_id, BinderInfo::Default, ty_c.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&format!("{name}.{suffix}")),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // ── instLE<T> / instLT<T> ──
        let le_rel = Expr::const_(Name::from_string(&format!("{name}.le")), vec![]);
        let lt_rel = Expr::const_(Name::from_string(&format!("{name}.lt")), vec![]);
        let inst_le_type = Expr::app(
            Expr::const_(Name::from_string("LE"), vec![zero.clone()]),
            ty_c.clone(),
        );
        let inst_lt_type = Expr::app(
            Expr::const_(Name::from_string("LT"), vec![zero.clone()]),
            ty_c.clone(),
        );
        if self.get_const(&Name::from_string(&inst_le_name)).is_none() {
            let value = Expr::apps(
                Expr::const_(Name::from_string("LE.mk"), vec![zero.clone()]),
                [ty_c.clone(), le_rel.clone()],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_le_name),
                level_params: vec![],
                type_: inst_le_type.clone(),
                value,
                is_reducible: true,
            })?;
        }
        if self.get_const(&Name::from_string(&inst_lt_name)).is_none() {
            let value = Expr::apps(
                Expr::const_(Name::from_string("LT.mk"), vec![zero.clone()]),
                [ty_c.clone(), lt_rel.clone()],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_lt_name),
                level_params: vec![],
                type_: inst_lt_type.clone(),
                value,
                is_reducible: true,
            })?;
        }

        // ── <T>.decLe / <T>.decLt : the dite forms ──
        // `succ_lhs = false` builds decLe (`ble a.toNat b.toNat`); `true` builds
        // decLt (`ble a.toNat.succ b.toNat` ≡ `Nat.lt a.toNat b.toNat`).
        let build_dec = |succ_lhs: bool| -> (Expr, Expr) {
            let rel_const = if succ_lhs {
                lt_rel.clone()
            } else {
                le_rel.clone()
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let concl = Expr::app(
                    dec.clone(),
                    Expr::apps(rel_const.clone(), [a.clone(), bv.clone()]),
                );
                let e = b.mk_pi(bv_id, BinderInfo::Default, ty_c.clone(), concl);
                let e = b.mk_pi(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let lhs = if succ_lhs {
                    Expr::app(nat_succ.clone(), to_nat(&a))
                } else {
                    to_nat(&a)
                };
                let rhs = to_nat(&bv);
                // Nat.le lhs rhs  (the decided Prop; ≡ <T>.le/lt a b)
                let le_prop = Expr::apps(nat_le.clone(), [lhs.clone(), rhs.clone()]);
                let alpha = Expr::app(dec.clone(), le_prop.clone());
                // c := Eq Bool (Nat.ble lhs rhs) Bool.true
                let ble = Expr::apps(nat_ble.clone(), [lhs.clone(), rhs.clone()]);
                let cond = eq_bool(ble.clone(), bool_true.clone());
                let inst = Expr::apps(inst_dec_eq_bool.clone(), [ble.clone(), bool_true.clone()]);
                // then: fun (h : c) => Decidable.isTrue le_prop (Nat.le_of_ble_eq_true lhs rhs h)
                let then_b = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(cond.clone());
                    let proof = Expr::apps(le_of_ble.clone(), [lhs.clone(), rhs.clone(), h]);
                    let body = Expr::apps(is_true.clone(), [le_prop.clone(), proof]);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, cond.clone(), body))
                };
                // else: fun (h : ¬c) => Decidable.isFalse le_prop
                //         (fun (hle : Nat.le lhs rhs) => h (Nat.ble_eq_true_of_le lhs rhs hle))
                let else_b = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(not_(cond.clone()));
                    let disproof = {
                        let mut g = EnvDeclBuilder::child_of(&c);
                        let (hle_id, hle) = g.fresh_local(le_prop.clone());
                        let ble_true =
                            Expr::apps(ble_eq_true_of_le.clone(), [lhs.clone(), rhs.clone(), hle]);
                        let body = Expr::app(h.clone(), ble_true);
                        g.finish_child(g.mk_lam(hle_id, BinderInfo::Default, le_prop.clone(), body))
                    };
                    let body = Expr::apps(is_false.clone(), [le_prop.clone(), disproof]);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, not_(cond.clone()), body))
                };
                let dite_e = Expr::apps(dite.clone(), [alpha, cond, inst, then_b, else_b]);
                let e = b.mk_lam(bv_id, BinderInfo::Default, ty_c.clone(), dite_e);
                let e = b.mk_lam(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            (ty, value)
        };

        let dec_le_name = format!("{name}.decLe");
        let dec_lt_name = format!("{name}.decLt");
        if self.get_const(&Name::from_string(&dec_le_name)).is_none() {
            let (type_, value) = build_dec(false);
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&dec_le_name),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }
        if self.get_const(&Name::from_string(&dec_lt_name)).is_none() {
            let (type_, value) = build_dec(true);
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&dec_lt_name),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // ── instDecidable<T>Le / instDecidable<T>Lt : typeclass form ──
        let inst_le_const = Expr::const_(Name::from_string(&inst_le_name), vec![]);
        let inst_lt_const = Expr::const_(Name::from_string(&inst_lt_name), vec![]);
        let inst_dec_def = |le: bool| -> (Expr, Expr) {
            let (rel, inst_const) = if le {
                ("LE.le", inst_le_const.clone())
            } else {
                ("LT.lt", inst_lt_const.clone())
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let tc = Expr::apps(
                    Expr::const_(Name::from_string(rel), vec![zero.clone()]),
                    [ty_c.clone(), inst_const.clone(), a.clone(), bv.clone()],
                );
                let concl = Expr::app(dec.clone(), tc);
                let e = b.mk_pi(bv_id, BinderInfo::Default, ty_c.clone(), concl);
                let e = b.mk_pi(a_id, BinderInfo::Default, ty_c.clone(), e);
                b.finish(e)
            };
            let val = Expr::const_(
                Name::from_string(&format!("{name}.{}", if le { "decLe" } else { "decLt" })),
                vec![],
            );
            (ty, val)
        };
        let (inst_dec_le_ty, inst_dec_le_val) = inst_dec_def(true);
        if self
            .get_const(&Name::from_string(&inst_dec_le_name))
            .is_none()
        {
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_dec_le_name),
                level_params: vec![],
                type_: inst_dec_le_ty.clone(),
                value: inst_dec_le_val,
                is_reducible: true,
            })?;
        }
        let (inst_dec_lt_ty, inst_dec_lt_val) = inst_dec_def(false);
        if self
            .get_const(&Name::from_string(&inst_dec_lt_name))
            .is_none()
        {
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_dec_lt_name),
                level_params: vec![],
                type_: inst_dec_lt_ty.clone(),
                value: inst_dec_lt_val,
                is_reducible: true,
            })?;
        }

        // ── Register the class instances ──
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(&inst_le_name),
            class_name: Name::from_string("LE"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_le_type),
            value: Some(Expr::const_(Name::from_string(&inst_le_name), vec![])),
        });
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(&inst_lt_name),
            class_name: Name::from_string("LT"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_lt_type),
            value: Some(Expr::const_(Name::from_string(&inst_lt_name), vec![])),
        });
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(&inst_dec_le_name),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_dec_le_ty),
            value: Some(Expr::const_(Name::from_string(&inst_dec_le_name), vec![])),
        });
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(&inst_dec_lt_name),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_dec_lt_ty),
            value: Some(Expr::const_(Name::from_string(&inst_dec_lt_name), vec![])),
        });

        Ok(())
    }

    /// Register the wrapper `≤`/`<` order stack for every `Nat`-wrapper width
    /// (`UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize`/`Float`). Idempotent.
    ///
    /// Mirrors `init_nat_decidable_ord`: it requires the wrapper structures and
    /// their `.val` projections to be registered (run by `with_prelude`), then
    /// wires the order stack + instances so `if ((x : UIntN) ≤ y)` resolves.
    pub(crate) fn init_uint_decidable_ord(&mut self) -> Result<(), EnvError> {
        if self.uint_decidable_ord_init {
            return Ok(());
        }
        self.init_uint_types()?;
        self.init_usize()?;
        self.init_float()?;
        for name in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"] {
            self.register_wrapper_dec_le_lt_proof(name)?;
        }
        self.uint_decidable_ord_init = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    const WRAPPERS: &[&str] = &["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"];

    fn env_with(name: &str) -> Environment {
        let mut env = Environment::with_prelude();
        env.register_wrapper_dec_le_lt_proof(name)
            .expect("register");
        env
    }

    /// Every constant in the stack registers as a `Definition` (never an Axiom),
    /// idempotently, and `tc.infer_type` of the const succeeds — proving the
    /// whole term type-checks at its declared type. This is the soundness gate:
    /// `<T>.decLe` / `<T>.le` infer_type pass.
    #[test]
    fn test_wrapper_dec_le_lt_registered_and_type_checks() {
        for &name in WRAPPERS {
            let mut env = env_with(name);
            // idempotent
            env.register_wrapper_dec_le_lt_proof(name)
                .expect("idempotent re-registration");

            let tc = TypeChecker::with_mode(&env, env.mode());
            for suffix in [
                format!("{name}.le"),
                format!("{name}.lt"),
                format!("{name}.decLe"),
                format!("{name}.decLt"),
                format!("instLE{name}"),
                format!("instLT{name}"),
                format!("instDecidable{name}Le"),
                format!("instDecidable{name}Lt"),
            ] {
                let info = env
                    .get_const(&Name::from_string(&suffix))
                    .unwrap_or_else(|| panic!("{suffix} should be registered"));
                assert_eq!(
                    info.kind,
                    ConstantKind::Definition,
                    "{suffix} must be a Definition (not Axiom)"
                );
                assert!(info.value.is_some(), "{suffix} must retain its value");
                let _ = tc
                    .infer_type(&Expr::const_(Name::from_string(&suffix), vec![]))
                    .unwrap_or_else(|e| panic!("{suffix} should type-check: {e:?}"));
            }
        }
    }

    /// Axiom closure is empty for every constant in the stack — the sorry/axiom
    /// guard. (`reduce_native` is untrusted; these are real kernel terms.)
    #[test]
    fn test_wrapper_dec_le_lt_axiom_closure_empty() {
        for &name in WRAPPERS {
            let env = env_with(name);
            for suffix in [
                format!("{name}.le"),
                format!("{name}.lt"),
                format!("{name}.decLe"),
                format!("{name}.decLt"),
                format!("instLE{name}"),
                format!("instLT{name}"),
                format!("instDecidable{name}Le"),
                format!("instDecidable{name}Lt"),
            ] {
                let n = Name::from_string(&suffix);
                let deps = env
                    .axiom_deps(&n)
                    .unwrap_or_else(|| panic!("{suffix} registered"));
                let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
                assert!(
                    !names.iter().any(|s| s == "sorry" || s == "sorryAx"),
                    "{suffix} must not depend on sorry/sorryAx; closure = {names:?}"
                );
                assert!(
                    names.is_empty(),
                    "{suffix} must have empty axiom closure, got {names:?}"
                );
            }
        }
    }

    /// SYMBOLIC soundness: instantiate `<T>.decLe` / `<T>.decLt` on two fresh
    /// fvars `a b : <T>` and infer the type of the application — proving the
    /// `Nat.decLe`-on-`<T>.val` wrapper actually checks inside the kernel for
    /// symbolic args (not just concrete literals reduced by a native reducer).
    #[test]
    fn test_wrapper_dec_le_lt_symbolic_application_checks() {
        for &name in WRAPPERS {
            let env = env_with(name);
            let ty_c = Expr::const_(Name::from_string(name), vec![]);
            for dec in [format!("{name}.decLe"), format!("{name}.decLt")] {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(ty_c.clone());
                let (bv_id, bv) = b.fresh_local(ty_c.clone());
                let app = Expr::apps(Expr::const_(Name::from_string(&dec), vec![]), [a, bv]);
                let e = b.mk_lam(bv_id, BinderInfo::Default, ty_c.clone(), app);
                let e = b.mk_lam(a_id, BinderInfo::Default, ty_c.clone(), e);
                let term = b.finish(e);
                let tc = TypeChecker::with_mode(&env, env.mode());
                let _ = tc.infer_type(&term).unwrap_or_else(|err| {
                    panic!("symbolic application of {dec} should type-check: {err:?}")
                });
            }
        }
    }

    /// `init_uint_decidable_ord` (run by `with_prelude`) registers each
    /// `instLE<T>`/`instLT<T>` as a resolvable `LE`/`LT` instance and each
    /// `instDecidable<T>Le`/`Lt` under `Decidable` — backed by the real
    /// axiom-free terms. Each instance Definition also type-checks (no axiom).
    #[test]
    fn test_inst_le_lt_registered_as_class_instances() {
        let env = Environment::with_prelude();
        let le_insts = env.get_class_instances(&Name::from_string("LE"));
        let lt_insts = env.get_class_instances(&Name::from_string("LT"));
        let dec_insts = env.get_class_instances(&Name::from_string("Decidable"));
        let tc = TypeChecker::with_mode(&env, env.mode());
        for &name in WRAPPERS {
            let inst_le = format!("instLE{name}");
            let inst_lt = format!("instLT{name}");
            let inst_dec_le = format!("instDecidable{name}Le");
            let inst_dec_lt = format!("instDecidable{name}Lt");
            assert!(
                le_insts
                    .iter()
                    .any(|i| i.name == Name::from_string(&inst_le)),
                "{inst_le} must be a registered LE instance"
            );
            assert!(
                lt_insts
                    .iter()
                    .any(|i| i.name == Name::from_string(&inst_lt)),
                "{inst_lt} must be a registered LT instance"
            );
            assert!(
                dec_insts
                    .iter()
                    .any(|i| i.name == Name::from_string(&inst_dec_le)),
                "{inst_dec_le} must be a registered Decidable instance"
            );
            assert!(
                dec_insts
                    .iter()
                    .any(|i| i.name == Name::from_string(&inst_dec_lt)),
                "{inst_dec_lt} must be a registered Decidable instance"
            );
            for inst in [&inst_le, &inst_lt, &inst_dec_le, &inst_dec_lt] {
                let info = env
                    .get_const(&Name::from_string(inst))
                    .unwrap_or_else(|| panic!("{inst} should be a registered Definition"));
                assert_eq!(
                    info.kind,
                    ConstantKind::Definition,
                    "{inst} must be a Definition (not Axiom)"
                );
                let _ = tc
                    .infer_type(&Expr::const_(Name::from_string(inst), vec![]))
                    .unwrap_or_else(|e| panic!("{inst} should type-check: {e:?}"));
                let deps = env
                    .axiom_deps(&Name::from_string(inst))
                    .unwrap_or_else(|| panic!("{inst} registered"));
                let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
                assert!(names.is_empty(), "{inst} must be axiom-free, got {names:?}");
            }
        }
    }
}
