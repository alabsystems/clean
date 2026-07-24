// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `List` instances of `GetElem` / `GetElem?` (Brick 4 — `xs[i]`
//! end-to-end), plus the `List.get` accessor they are built on.
//!
//! Registers, as fully kernel-checked Definitions (no axioms, no sorry):
//!
//! ```text
//! def List.get {α : Type u} : (as : List α) → Fin as.length → α
//!   | cons a _,  ⟨0, _⟩ => a
//!   | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩
//!
//! instance : GetElem (List α) Nat α fun as i => i < as.length where
//!   getElem as i h := as.get ⟨i, h⟩
//!
//! instance : GetElem? (List α) Nat α fun as i => i < as.length where
//!   getElem? as i := as.get?Internal i
//!   getElem! as i := as.get!Internal i
//! ```
//!
//! Lean sources (toolchain `v4.30.0-rc2`):
//! - `Init/Prelude.lean:3059` — `List.get` (Fin-indexed, total by the bound;
//!   its `List.rec` construction lives in `data_list_get.rs`)
//! - `Init/GetElem.lean:293` — the `GetElem (List α) Nat α` instance
//!   (generated name `List.instGetElemNatLtLength`)
//! - `Init/GetElem.lean:339` — the `GetElem? (List α) Nat α` instance
//!   (generated name `List.instGetElem?NatLtLength`)
//!
//! The `valid` out-param is spelled `fun as i => @LT.lt Nat instLTNat i
//! (List.length as)` — the elaboration of Lean's `fun as i => i < as.length`
//! — so a source hypothesis `h : i < xs.length` is syntactically the pinned
//! proof obligation (`assumption` closes it without defeq search).
//!
//! Documented deviations (defeq-preserving spellings, not semantics):
//! - `getElem?` field := `List.get?` (Clean's prelude accessor; identical
//!   recursion to Lean's `List.get?Internal`: nil → `none`, `(a::_)[0]?` →
//!   `some a`, `(_::as)[i+1]?` → `as[i]?`).
//! - `getElem!` field := `fun [Inhabited α] as i => Option.rec default
//!   (fun e => e) (as.get? i)` — Lean's override `get!Internal` panics on the
//!   miss branch, and `panic!`/`outOfBounds` is definitionally `default`
//!   (`Init/GetElem.lean:20 outOfBounds_eq_default … := rfl`), so both
//!   spellings reduce to the same value on every ground input.

use crate::env::data_list_get::ListGetElemConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `List.get` and the `List` instances of `GetElem`/`GetElem?`
    /// (`List.instGetElemNatLtLength`, `List.instGetElem?NatLtLength`), all as
    /// fully-checked Definitions with empty axiom closures.
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld. These carry
    /// the genuine upstream names but Clean-native value spellings
    /// (`List.get?` for `get?Internal`, `Option.rec default` for
    /// `get!Internal`), so pre-seeding would make the import dedup filter DROP
    /// the genuine olean values (the `Nat.min`-overlay masking class — see
    /// `init_prelude_core`). They also wrap `List.get?`/`Fin.isLt`, which the
    /// import prelude withholds. The default proof-execution lane is
    /// unchanged.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.getelem_list_instances_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_getelem_list_instances(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.getelem_list_instances_init {
            return Ok(());
        }

        // Dependencies (all idempotent): the classes, List + List.length,
        // List.get? (getElem? field), Fin (+ Fin.val/Fin.isLt via the default
        // lane), LT/Nat.lt/instLTNat, Option, Inhabited, and the two Nat
        // ordering leaf lemmas the `List.get` minors eliminate with.
        self.init_getelem_classes()?;
        self.init_list()?; // List, List.length
        self.init_list_ops()?; // List.get?
        self.init_fin()?; // Fin, Fin.mk, Fin.val, Fin.isLt
        self.init_lt()?; // LT.lt, Nat.lt, instLTNat
        self.init_option()?;
        self.init_inhabited()?; // Inhabited.default, instInhabitedNat
        self.register_nat_not_succ_le_zero_theorem()?;
        self.register_nat_le_of_succ_le_succ_theorem()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let k = ListGetElemConsts::new(&u_level);

        self.register_list_get(&u, &k)?;
        self.register_list_getelem_instance(&u, &k)?;
        self.register_list_getelem_opt_instance(&u, &k)?;
        // The `Array` GetElem instance reuses the same `List` accessor (through
        // `Array.data`) and shared consts; guarded on the Array substrate, which
        // inits before this point in the full prelude.
        self.register_array_getelem_instance(&u, &k)?;
        // The `Array` GetElem? instance (arr[i]? / arr[i]!); reuses List.get?
        // through Array.data. Same substrate guard as the parent instance;
        // MUST run after it (toGetElem = Array.instGetElemNatLtSize).
        self.register_array_getelem_opt_instance(&u, &k)?;

        self.getelem_list_instances_init = true;
        Ok(())
    }

    /// `List.instGetElemNatLtLength : GetElem (List α) Nat α
    /// (fun as i => i < as.length) := ⟨fun as i h => as.get ⟨i, h⟩⟩`
    /// (`Init/GetElem.lean:293`; generated instance name verified against the
    /// pinned toolchain's `Init/GetElem.olean`).
    fn register_list_getelem_instance(
        &mut self,
        u: &Name,
        k: &ListGetElemConsts,
    ) -> Result<(), EnvError> {
        let inst_name = Name::from_string("List.instGetElemNatLtLength");
        if self.get_const(&inst_name).is_none() {
            // GetElem.{u, 0, u}: coll = List α : Type u, idx = Nat : Type 0,
            // elem = α : Type u.
            let levels = vec![k.u.clone(), Level::zero(), k.u.clone()];
            let getelem_const = Expr::const_(Name::from_string("GetElem"), levels.clone());
            let getelem_mk = Expr::const_(Name::from_string("GetElem.mk"), levels);
            let list_get = Expr::const_(Name::from_string("List.get"), vec![k.u.clone()]);

            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
                let list_alpha = Expr::app(k.list.clone(), alpha.clone());
                let valid = k.valid_pred(&b, &alpha);
                let r = Expr::apps(
                    getelem_const,
                    [list_alpha, k.nat.clone(), alpha.clone(), valid],
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, k.type_u.clone(), r);
                b.finish(r)
            };

            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
                let list_alpha = Expr::app(k.list.clone(), alpha.clone());
                let valid = k.valid_pred(&b, &alpha);

                // getElem field: fun (as : List α) (i : Nat) (h : valid as i) =>
                //   List.get as (Fin.mk (List.length as) i h)
                // Well-typed: `valid as i` β-reduces to `LT.lt Nat instLTNat i
                // (length as)`, which δι-reduces to `Nat.lt i (length as)` —
                // exactly `Fin.mk`'s bound.
                let field = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (as_id, as_) = c.fresh_local(list_alpha.clone());
                    let (i_id, i) = c.fresh_local(k.nat.clone());
                    let h_ty = Expr::apps(valid.clone(), [as_.clone(), i.clone()]);
                    let (h_id, h) = c.fresh_local(h_ty.clone());
                    let len_as = k.len(&alpha, &as_);
                    let fin_i = Expr::apps(k.fin_mk.clone(), [len_as, i.clone(), h]);
                    let body = Expr::apps(list_get.clone(), [alpha.clone(), as_.clone(), fin_i]);
                    let r = c.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                    let r = c.mk_lam(i_id, BinderInfo::Default, k.nat.clone(), r);
                    let r = c.mk_lam(as_id, BinderInfo::Default, list_alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    getelem_mk,
                    [list_alpha, k.nat.clone(), alpha.clone(), valid, field],
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, k.type_u.clone(), body);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: inst_name.clone(),
                level_params: vec![u.clone()],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;
        }

        self.register_instance(KernelInstanceInfo {
            name: inst_name,
            class_name: Name::from_string("GetElem"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// `Array.instGetElemNatLtSize : GetElem (Array α) Nat α
    /// (fun as i => i < as.size) := ⟨fun as i h => (as.data).get ⟨i, h⟩⟩`
    /// (`Init/GetElem.lean` / `Init/Data/Array/Basic.lean`; the `Array` analog
    /// of the `List` instance above — WITHOUT it, `arr[i]` on an `Array` has no
    /// `GetElem` instance, so `valid` stays a metavariable, the bounds goal is
    /// never ground [`decide` sees a metavar-headed "counterexample"], and the
    /// unsolved index proof surfaces at `add_decl` as "contains free variables").
    ///
    /// `valid` is `fun as i => i < Array.size as`; the element accessor threads
    /// through the `List` carrier: `List.get α (Array.data as) ⟨i, h⟩` — sound
    /// because `Array.size as` is def-eq `List.length (Array.data as)`, so `h :
    /// i < Array.size as` fits `Fin.mk (Array.size as) i h` and `List.get`
    /// consumes that `Fin` at the def-eq `List.length` bound. Guarded on the
    /// `Array` carrier + accessors being present (they init before this in the
    /// full prelude; a bare init skips it).
    fn register_array_getelem_instance(
        &mut self,
        u: &Name,
        k: &ListGetElemConsts,
    ) -> Result<(), EnvError> {
        let inst_name = Name::from_string("Array.instGetElemNatLtSize");
        // Carrier + accessor gate: skip if the Array substrate is absent.
        if self.get_const(&Name::from_string("Array")).is_none()
            || self.get_const(&Name::from_string("Array.size")).is_none()
            || self.get_const(&Name::from_string("Array.data")).is_none()
            || self.get_const(&Name::from_string("List.get")).is_none()
        {
            return Ok(());
        }

        if self.get_const(&inst_name).is_none() {
            let levels = vec![k.u.clone(), Level::zero(), k.u.clone()];
            let getelem_const = Expr::const_(Name::from_string("GetElem"), levels.clone());
            let getelem_mk = Expr::const_(Name::from_string("GetElem.mk"), levels);
            let list_get = Expr::const_(Name::from_string("List.get"), vec![k.u.clone()]);
            let array_c = Expr::const_(Name::from_string("Array"), vec![k.u.clone()]);
            let array_size = Expr::const_(Name::from_string("Array.size"), vec![k.u.clone()]);
            let array_data = Expr::const_(Name::from_string("Array.data"), vec![k.u.clone()]);

            // valid : fun (as : Array α) (i : Nat) => @LT.lt Nat instLTNat i
            //         (Array.size α as)
            let array_valid = |parent: &EnvDeclBuilder, alpha: &Expr| -> Expr {
                let array_alpha = Expr::app(array_c.clone(), alpha.clone());
                let mut c = EnvDeclBuilder::child_of(parent);
                let (as_id, as_) = c.fresh_local(array_alpha.clone());
                let (i_id, i) = c.fresh_local(k.nat.clone());
                let size_as = Expr::apps(array_size.clone(), [alpha.clone(), as_.clone()]);
                let body = Expr::apps(
                    k.lt_lt.clone(),
                    [k.nat.clone(), k.inst_lt_nat.clone(), i.clone(), size_as],
                );
                let r = c.mk_lam(i_id, BinderInfo::Default, k.nat.clone(), body);
                let r = c.mk_lam(as_id, BinderInfo::Default, array_alpha.clone(), r);
                c.finish_child(r)
            };

            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
                let array_alpha = Expr::app(array_c.clone(), alpha.clone());
                let valid = array_valid(&b, &alpha);
                let r = Expr::apps(
                    getelem_const,
                    [array_alpha, k.nat.clone(), alpha.clone(), valid],
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, k.type_u.clone(), r);
                b.finish(r)
            };

            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
                let array_alpha = Expr::app(array_c.clone(), alpha.clone());
                let valid = array_valid(&b, &alpha);

                // getElem field: fun (as : Array α) (i : Nat) (h : valid as i) =>
                //   List.get α (Array.data α as) (Fin.mk (Array.size α as) i h)
                let field = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (as_id, as_) = c.fresh_local(array_alpha.clone());
                    let (i_id, i) = c.fresh_local(k.nat.clone());
                    let h_ty = Expr::apps(valid.clone(), [as_.clone(), i.clone()]);
                    let (h_id, h) = c.fresh_local(h_ty.clone());
                    let size_as = Expr::apps(array_size.clone(), [alpha.clone(), as_.clone()]);
                    let data_as = Expr::apps(array_data.clone(), [alpha.clone(), as_.clone()]);
                    let fin_i = Expr::apps(k.fin_mk.clone(), [size_as, i.clone(), h]);
                    let body = Expr::apps(list_get.clone(), [alpha.clone(), data_as, fin_i]);
                    let r = c.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                    let r = c.mk_lam(i_id, BinderInfo::Default, k.nat.clone(), r);
                    let r = c.mk_lam(as_id, BinderInfo::Default, array_alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    getelem_mk,
                    [array_alpha, k.nat.clone(), alpha.clone(), valid, field],
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, k.type_u.clone(), body);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: inst_name.clone(),
                level_params: vec![u.clone()],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;
        }

        self.register_instance(KernelInstanceInfo {
            name: inst_name,
            class_name: Name::from_string("GetElem"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// `Array.instGetElem?NatLtSize : GetElem? (Array α) Nat α
    /// (fun as i => i < as.size)` — the `Array` analog of
    /// `List.instGetElem?NatLtLength`. `toGetElem := Array.instGetElemNatLtSize`;
    /// the `getElem?`/`getElem!` fields thread through the `List` carrier via
    /// `Array.data`. Unlike the `List` instance (where `@List.get? α` already has
    /// the field type and is passed bare), the `Array` `getElem?` field type is
    /// `Array α → Nat → Option α`, so the accessor is eta-expanded through
    /// `Array.data` (same pattern as `Array.getD` over `List.getD`). `List.get?`
    /// takes a raw `Nat`, so no bound proof / `Array.size` def-eq is needed here.
    /// Guarded on the same `Array` substrate as the parent instance (registered
    /// immediately before), plus the parent instance and `List.get?` themselves.
    fn register_array_getelem_opt_instance(
        &mut self,
        u: &Name,
        k: &ListGetElemConsts,
    ) -> Result<(), EnvError> {
        let inst_name = Name::from_string("Array.instGetElem?NatLtSize");
        if self.get_const(&Name::from_string("Array")).is_none()
            || self.get_const(&Name::from_string("Array.size")).is_none()
            || self.get_const(&Name::from_string("Array.data")).is_none()
            || self
                .get_const(&Name::from_string("Array.instGetElemNatLtSize"))
                .is_none()
            || self.get_const(&Name::from_string("List.get?")).is_none()
        {
            return Ok(());
        }

        if self.get_const(&inst_name).is_none() {
            let levels = vec![k.u.clone(), Level::zero(), k.u.clone()];
            let getelem_opt_const = Expr::const_(Name::from_string("GetElem?"), levels.clone());
            let getelem_opt_mk = Expr::const_(Name::from_string("GetElem?.mk"), levels);
            let parent_inst = Expr::const_(
                Name::from_string("Array.instGetElemNatLtSize"),
                vec![k.u.clone()],
            );
            let list_get_opt = Expr::const_(Name::from_string("List.get?"), vec![k.u.clone()]);
            let option_rec = Expr::const_(
                Name::from_string("Option.rec"),
                vec![Level::succ(k.u.clone()), k.u.clone()],
            );
            let option_const = Expr::const_(Name::from_string("Option"), vec![k.u.clone()]);
            let inhabited_const = Expr::const_(
                Name::from_string("Inhabited"),
                vec![Level::succ(k.u.clone())],
            );
            let inhabited_default = Expr::const_(
                Name::from_string("Inhabited.default"),
                vec![Level::succ(k.u.clone())],
            );
            let array_c = Expr::const_(Name::from_string("Array"), vec![k.u.clone()]);
            let array_size = Expr::const_(Name::from_string("Array.size"), vec![k.u.clone()]);
            let array_data = Expr::const_(Name::from_string("Array.data"), vec![k.u.clone()]);

            // valid : fun (as : Array α) (i : Nat) => @LT.lt Nat instLTNat i (Array.size α as)
            // — byte-for-byte the parent instance's predicate.
            let array_valid = |parent: &EnvDeclBuilder, alpha: &Expr| -> Expr {
                let array_alpha = Expr::app(array_c.clone(), alpha.clone());
                let mut c = EnvDeclBuilder::child_of(parent);
                let (as_id, as_) = c.fresh_local(array_alpha.clone());
                let (i_id, i) = c.fresh_local(k.nat.clone());
                let size_as = Expr::apps(array_size.clone(), [alpha.clone(), as_.clone()]);
                let body = Expr::apps(
                    k.lt_lt.clone(),
                    [k.nat.clone(), k.inst_lt_nat.clone(), i.clone(), size_as],
                );
                let r = c.mk_lam(i_id, BinderInfo::Default, k.nat.clone(), body);
                let r = c.mk_lam(as_id, BinderInfo::Default, array_alpha.clone(), r);
                c.finish_child(r)
            };

            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
                let array_alpha = Expr::app(array_c.clone(), alpha.clone());
                let valid = array_valid(&b, &alpha);
                let r = Expr::apps(
                    getelem_opt_const,
                    [array_alpha, k.nat.clone(), alpha.clone(), valid],
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, k.type_u.clone(), r);
                b.finish(r)
            };

            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
                let array_alpha = Expr::app(array_c.clone(), alpha.clone());
                let option_alpha = Expr::app(option_const.clone(), alpha.clone());
                let valid = array_valid(&b, &alpha);

                // getElem? field: fun (as : Array α) (i : Nat) =>
                //   List.get? α (Array.data α as) i
                let opt_field = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (as_id, as_) = c.fresh_local(array_alpha.clone());
                    let (i_id, i) = c.fresh_local(k.nat.clone());
                    let data_as = Expr::apps(array_data.clone(), [alpha.clone(), as_.clone()]);
                    let body =
                        Expr::apps(list_get_opt.clone(), [alpha.clone(), data_as, i.clone()]);
                    let r = c.mk_lam(i_id, BinderInfo::Default, k.nat.clone(), body);
                    let r = c.mk_lam(as_id, BinderInfo::Default, array_alpha.clone(), r);
                    c.finish_child(r)
                };

                // getElem! field: fun [inst : Inhabited α] (as : Array α) (i : Nat) =>
                //   Option.rec (fun _ => α) (Inhabited.default α inst) (fun e => e)
                //              (List.get? α (Array.data α as) i)
                let bang_field = {
                    let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (inst_id, inst) = c.fresh_local(inhabited_alpha.clone());
                    let (as_id, as_) = c.fresh_local(array_alpha.clone());
                    let (i_id, i) = c.fresh_local(k.nat.clone());
                    let motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (o_id, _o) = d.fresh_local(option_alpha.clone());
                        let r = d.mk_lam(
                            o_id,
                            BinderInfo::Default,
                            option_alpha.clone(),
                            alpha.clone(),
                        );
                        d.finish_child(r)
                    };
                    let none_case =
                        Expr::apps(inhabited_default.clone(), [alpha.clone(), inst.clone()]);
                    let some_case = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (e_id, e) = d.fresh_local(alpha.clone());
                        let r = d.mk_lam(e_id, BinderInfo::Default, alpha.clone(), e);
                        d.finish_child(r)
                    };
                    let data_as = Expr::apps(array_data.clone(), [alpha.clone(), as_.clone()]);
                    let scrutinee =
                        Expr::apps(list_get_opt.clone(), [alpha.clone(), data_as, i.clone()]);
                    let body = Expr::apps(
                        option_rec.clone(),
                        [alpha.clone(), motive, none_case, some_case, scrutinee],
                    );
                    let r = c.mk_lam(i_id, BinderInfo::Default, k.nat.clone(), body);
                    let r = c.mk_lam(as_id, BinderInfo::Default, array_alpha.clone(), r);
                    let r = c.mk_lam(inst_id, BinderInfo::InstImplicit, inhabited_alpha, r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    getelem_opt_mk,
                    [
                        array_alpha.clone(),
                        k.nat.clone(),
                        alpha.clone(),
                        valid,
                        Expr::app(parent_inst.clone(), alpha.clone()), // toGetElem
                        opt_field,                                     // getElem?
                        bang_field,                                    // getElem!
                    ],
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, k.type_u.clone(), body);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: inst_name.clone(),
                level_params: vec![u.clone()],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;
        }

        self.register_instance(KernelInstanceInfo {
            name: inst_name,
            class_name: Name::from_string("GetElem?"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// `List.instGetElem?NatLtLength : GetElem? (List α) Nat α
    /// (fun as i => i < as.length)` (`Init/GetElem.lean:339`), with
    /// `toGetElem := List.instGetElemNatLtLength`, `getElem? := List.get?`,
    /// and `getElem!` as the `Option.rec default` spelling (see module docs
    /// for the two documented deviations).
    fn register_list_getelem_opt_instance(
        &mut self,
        u: &Name,
        k: &ListGetElemConsts,
    ) -> Result<(), EnvError> {
        let inst_name = Name::from_string("List.instGetElem?NatLtLength");
        if self.get_const(&inst_name).is_none() {
            let levels = vec![k.u.clone(), Level::zero(), k.u.clone()];
            let getelem_opt_const = Expr::const_(Name::from_string("GetElem?"), levels.clone());
            let getelem_opt_mk = Expr::const_(Name::from_string("GetElem?.mk"), levels);
            let parent_inst = Expr::const_(
                Name::from_string("List.instGetElemNatLtLength"),
                vec![k.u.clone()],
            );
            let list_get_opt = Expr::const_(Name::from_string("List.get?"), vec![k.u.clone()]);
            // Option.rec universes are [motive-elim, type] = [succ u, u]; the
            // motive `fun _ => α` returns Type u = Sort (succ u).
            let option_rec = Expr::const_(
                Name::from_string("Option.rec"),
                vec![Level::succ(k.u.clone()), k.u.clone()],
            );
            let option_const = Expr::const_(Name::from_string("Option"), vec![k.u.clone()]);
            // α : Type u = Sort (succ u), so Inhabited is instantiated at succ u.
            let inhabited_const = Expr::const_(
                Name::from_string("Inhabited"),
                vec![Level::succ(k.u.clone())],
            );
            let inhabited_default = Expr::const_(
                Name::from_string("Inhabited.default"),
                vec![Level::succ(k.u.clone())],
            );

            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
                let list_alpha = Expr::app(k.list.clone(), alpha.clone());
                let valid = k.valid_pred(&b, &alpha);
                let r = Expr::apps(
                    getelem_opt_const,
                    [list_alpha, k.nat.clone(), alpha.clone(), valid],
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, k.type_u.clone(), r);
                b.finish(r)
            };

            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
                let list_alpha = Expr::app(k.list.clone(), alpha.clone());
                let option_alpha = Expr::app(option_const.clone(), alpha.clone());
                let valid = k.valid_pred(&b, &alpha);

                // getElem! field: fun [inst : Inhabited α] (as : List α) (i : Nat) =>
                //   Option.rec (fun _ => α) (Inhabited.default α inst) (fun e => e)
                //              (List.get? as i)
                let bang_field = {
                    let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (inst_id, inst) = c.fresh_local(inhabited_alpha.clone());
                    let (as_id, as_) = c.fresh_local(list_alpha.clone());
                    let (i_id, i) = c.fresh_local(k.nat.clone());
                    let motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (o_id, _o) = d.fresh_local(option_alpha.clone());
                        let r = d.mk_lam(
                            o_id,
                            BinderInfo::Default,
                            option_alpha.clone(),
                            alpha.clone(),
                        );
                        d.finish_child(r)
                    };
                    let none_case =
                        Expr::apps(inhabited_default.clone(), [alpha.clone(), inst.clone()]);
                    let some_case = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (e_id, e) = d.fresh_local(alpha.clone());
                        let r = d.mk_lam(e_id, BinderInfo::Default, alpha.clone(), e);
                        d.finish_child(r)
                    };
                    let scrutinee = Expr::apps(
                        list_get_opt.clone(),
                        [alpha.clone(), as_.clone(), i.clone()],
                    );
                    let body = Expr::apps(
                        option_rec.clone(),
                        [alpha.clone(), motive, none_case, some_case, scrutinee],
                    );
                    let r = c.mk_lam(i_id, BinderInfo::Default, k.nat.clone(), body);
                    let r = c.mk_lam(as_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(inst_id, BinderInfo::InstImplicit, inhabited_alpha, r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    getelem_opt_mk,
                    [
                        list_alpha,
                        k.nat.clone(),
                        alpha.clone(),
                        valid,
                        Expr::app(parent_inst.clone(), alpha.clone()),
                        Expr::app(list_get_opt.clone(), alpha.clone()),
                        bang_field,
                    ],
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, k.type_u.clone(), body);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: inst_name.clone(),
                level_params: vec![u.clone()],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;
        }

        self.register_instance(KernelInstanceInfo {
            name: inst_name,
            class_name: Name::from_string("GetElem?"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }
}
