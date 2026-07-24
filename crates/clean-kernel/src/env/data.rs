// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic data type initialization for Environment
//!
//! This module contains init_* and has_* functions for:
//! - Unit type
//! - PLift type
//! - Fin type
//! - Array type
//!
//! See also:
//! - `data_collection_ops.rs` for Option/List operations
//! - `data_typeclasses.rs` for Inhabited, DecidableEq
//! - `data_typeclasses_beq.rs` for BEq typeclass and instances
//! - `data_typeclasses_hashable.rs` for Hashable typeclass and instances
//! - `data_monad.rs` for IO, StateT, StateM, Id, monad classes

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Unit type as a reducible abbreviation for `PUnit.{1}`.
    ///
    /// In Lean 4, `Unit` is defined as:
    /// ```text
    /// abbrev Unit : Type := PUnit.{1}
    /// ```
    /// so that `Unit` is *definitionally* equal to `PUnit.{1}`.
    ///
    /// This is critical for `StateT.set` whose return type is `m PUnit` —
    /// when the user writes `MySem Unit`, the kernel must be able to reduce
    /// `Unit` to `PUnit.{1}` during definitional equality checks (#3418).
    ///
    /// This adds:
    /// - Unit : Type := PUnit.{1}          (reducible definition)
    /// - Unit.unit : Unit := PUnit.unit.{1} (reducible definition)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.unit_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_unit(&mut self) -> Result<(), EnvError> {
        if self.unit_init {
            return Ok(());
        }

        // PUnit must exist first — Unit is defined in terms of it.
        self.init_punit()?;

        // Unit : Type := PUnit.{1}
        // PUnit.{u} : Sort u, so PUnit.{1} : Sort 1 = Type
        let type0 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
        let punit_1 = Expr::const_(Name::from_string("PUnit"), vec![Level::succ(Level::zero())]);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Unit"),
            level_params: vec![],
            type_: type0,
            value: punit_1,
            is_reducible: true,
        })?;

        // Unit.unit : Unit := PUnit.unit.{1}
        let unit_const = Expr::const_(Name::from_string("Unit"), vec![]);
        let punit_unit_1 = Expr::const_(
            Name::from_string("PUnit.unit"),
            vec![Level::succ(Level::zero())],
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Unit.unit"),
            level_params: vec![],
            type_: unit_const,
            value: punit_unit_1,
            is_reducible: true,
        })?;

        self.unit_init = true;
        Ok(())
    }

    /// Check if Unit has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_unit` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_unit(&self) -> bool {
        self.unit_init
    }

    /// Initialize PUnit (universe-polymorphic unit type).
    ///
    /// In Lean 4, `PUnit.{u} : Type u` is the universe-polymorphic version of `Unit`.
    /// It has a single constructor `PUnit.unit.{u} : PUnit.{u}`.
    ///
    /// Required by `StateT.set` which returns `m PUnit.{u}` (the "no meaningful value"
    /// return type at any universe level).
    pub fn init_punit(&mut self) -> Result<(), EnvError> {
        if self.punit_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        // PUnit.{u} : Sort u (NOT Type u — Lean 4's PUnit lives in Sort u)
        let punit_type = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let punit_const = Expr::const_(Name::from_string("PUnit"), vec![u_level]);

        // PUnit.unit.{u} : PUnit.{u}
        let punit_unit_type = punit_const;

        let punit_decl = InductiveDecl {
            level_params: vec![u],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("PUnit"),
                type_: punit_type,
                constructors: vec![Constructor {
                    name: Name::from_string("PUnit.unit"),
                    type_: punit_unit_type,
                }],
            }],
        };

        self.add_inductive(punit_decl)?;
        self.punit_init = true;
        Ok(())
    }

    /// Check if PUnit has been initialized
    pub(crate) fn has_punit(&self) -> bool {
        self.punit_init
    }

    /// Initialize the PLift type (Prop to Type lifting)
    ///
    /// PLift lifts a Prop to a Type, similar to ULift but from Prop:
    /// ```text
    /// structure PLift (α : Prop) : Type where
    ///   | up : α → PLift α
    /// ```
    ///
    /// This adds:
    /// - PLift : Prop → Type
    /// - PLift.up : {α : Prop} → α → PLift α
    /// - PLift.down : {α : Prop} → PLift α → α
    /// - PLift.rec
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.plift_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_plift(&mut self) -> Result<(), EnvError> {
        if self.plift_init {
            return Ok(());
        }

        // PLift : Prop → Type
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        // PLift.{} : Prop → Type
        let plift_type = Expr::pi(BinderInfo::Default, prop.clone(), type_.clone());

        let plift_const = Expr::const_(Name::from_string("PLift"), vec![]);

        // PLift.up : {α : Prop} → α → PLift α
        let plift_up_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(prop.clone()); // α : Prop
            let (a_id, _a) = b.fresh_local(alpha.clone()); // a : α
            let r = Expr::app(plift_const.clone(), alpha.clone()); // PLift α
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let plift_decl = InductiveDecl {
            level_params: vec![],
            num_params: 1, // α is a parameter
            types: vec![InductiveType {
                name: Name::from_string("PLift"),
                type_: plift_type,
                constructors: vec![Constructor {
                    name: Name::from_string("PLift.up"),
                    type_: plift_up_type,
                }],
            }],
        };

        self.add_inductive(plift_decl)?;

        // Register structure fields for PLift
        self.register_structure_fields(
            Name::from_string("PLift"),
            vec![Name::from_string("down")],
        )?;

        // PLift.down : {α : Prop} → PLift α → α
        let plift_down_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(prop.clone()); // α : Prop
            let (x_id, _x) = b.fresh_local(Expr::app(plift_const.clone(), alpha.clone())); // x : PLift α
            let r = alpha.clone();
            let r = b.mk_pi(
                x_id,
                BinderInfo::Default,
                Expr::app(plift_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        // PLift.down value: λ {α} (x : PLift α) => PLift.rec.{0} α motive case x
        let plift_down_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(prop.clone()); // α : Prop
            let (x_id, x) = b.fresh_local(Expr::app(plift_const.clone(), alpha.clone())); // x : PLift α

            // motive: λ (_ : PLift α) => α
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(Expr::app(plift_const.clone(), alpha.clone()));
                let r = alpha.clone();
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(plift_const.clone(), alpha.clone()),
                    r,
                );
                c.finish_child(r)
            };

            // case for up: λ (a : α) => a
            let case_up = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let r = a;
                let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };

            let plift_rec = Expr::const_(Name::from_string("PLift.rec"), vec![Level::zero()]);
            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(plift_rec, alpha.clone()), motive),
                    case_up,
                ),
                x,
            );
            let r = b.mk_lam(
                x_id,
                BinderInfo::Default,
                Expr::app(plift_const.clone(), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("PLift.down"),
            level_params: vec![],
            type_: plift_down_type,
            value: plift_down_value,
            is_reducible: true,
        })?;

        self.plift_init = true;
        Ok(())
    }

    /// Check if PLift has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_plift` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_plift(&self) -> bool {
        self.plift_init
    }

    /// Initialize the Fin type (bounded natural numbers)
    ///
    /// Fin n is the type of natural numbers less than n:
    /// ```text
    /// structure Fin (n : Nat) : Type where
    ///   val : Nat
    ///   isLt : val < n
    /// ```
    ///
    /// For simplicity, we represent Fin as a subtype of Nat with a proof obligation.
    /// This is actually a structure with two fields.
    ///
    /// This adds:
    /// - Fin : Nat → Type
    /// - Fin.mk : {n : Nat} → (val : Nat) → val < n → Fin n
    /// - Fin.val : {n : Nat} → Fin n → Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.fin_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_fin(&mut self) -> Result<(), EnvError> {
        if self.fin_init {
            return Ok(());
        }

        // Ensure Nat is initialized
        self.init_nat()?;
        // FAITHFUL CARRIER: `Fin.mk`'s `isLt` field is a PROOF of `Nat.lt val n`
        // (not a bare `Prop` value), so `Fin n` is inhabited ONLY by genuinely
        // in-range indices. `init_lt` registers `Nat.lt` (reducible to
        // `Nat.le (Nat.succ val) n`); it has no `Fin` dependency, so no init cycle.
        self.init_lt()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);

        // Fin : Nat → Type
        let fin_type = Expr::pi(BinderInfo::Default, nat_const.clone(), type_.clone());

        let fin_const = Expr::const_(Name::from_string("Fin"), vec![]);

        // Fin.mk : {n : Nat} → (val : Nat) → (isLt : Nat.lt val n) → Fin n
        let fin_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n : Nat
            let (val_id, val) = b.fresh_local(nat_const.clone()); // val : Nat
                                                                  // isLt : Nat.lt val n  (a PROOF that `val < n`, the faithful bound)
            let islt_ty = Expr::app(Expr::app(nat_lt.clone(), val.clone()), n.clone());
            let (islt_id, _islt) = b.fresh_local(islt_ty.clone());
            let r = Expr::app(fin_const.clone(), n); // Fin n
            let r = b.mk_pi(islt_id, BinderInfo::Default, islt_ty, r);
            let r = b.mk_pi(val_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        let fin_decl = InductiveDecl {
            level_params: vec![],
            num_params: 1, // n is a parameter
            types: vec![InductiveType {
                name: Name::from_string("Fin"),
                type_: fin_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Fin.mk"),
                    type_: fin_mk_type,
                }],
            }],
        };

        self.add_inductive(fin_decl)?;

        // Register structure fields
        self.register_structure_fields(
            Name::from_string("Fin"),
            vec![Name::from_string("val"), Name::from_string("isLt")],
        )?;

        // Add Fin.val : {n : Nat} → Fin n → Nat
        let fin_rec = Expr::const_(
            Name::from_string("Fin.rec"),
            vec![Level::succ(Level::zero())],
        );

        // Fin.val : {n : Nat} → Fin n → Nat
        let fin_val_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let (x_id, _x) = b.fresh_local(Expr::app(fin_const.clone(), n.clone()));
            let r = nat_const.clone();
            let r = b.mk_pi(
                x_id,
                BinderInfo::Default,
                Expr::app(fin_const.clone(), n.clone()),
                r,
            );
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        // Fin.val value: λ {n} (x : Fin n) => Fin.rec n motive mk_case x
        let fin_val_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let (x_id, x) = b.fresh_local(Expr::app(fin_const.clone(), n.clone()));

            // motive: λ (_ : Fin n) => Nat
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(Expr::app(fin_const.clone(), n.clone()));
                let r = nat_const.clone();
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(fin_const.clone(), n.clone()),
                    r,
                );
                c.finish_child(r)
            };

            // case for mk: λ (val : Nat) (_ : Nat.lt val n) => val
            // The minor premise binds the constructor's fields; the second field
            // is now the faithful `isLt : Nat.lt val n` proof (ignored by `val`).
            let mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (val_id, val) = c.fresh_local(nat_const.clone());
                let islt_ty = Expr::app(Expr::app(nat_lt.clone(), val.clone()), n.clone());
                let (proof_id, _proof) = c.fresh_local(islt_ty.clone());
                let r = val;
                let r = c.mk_lam(proof_id, BinderInfo::Default, islt_ty, r);
                let r = c.mk_lam(val_id, BinderInfo::Default, nat_const.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(fin_rec.clone(), n.clone()), motive),
                    mk_case,
                ),
                x,
            );
            let r = b.mk_lam(
                x_id,
                BinderInfo::Default,
                Expr::app(fin_const.clone(), n.clone()),
                body,
            );
            let r = b.mk_lam(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.val"),
            level_params: vec![],
            type_: fin_val_type,
            value: fin_val_value,
            is_reducible: true,
        })?;

        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): Clean's `Fin.isLt` states the bound with RAW `Nat.lt`
        // while genuine v4.31 states `@LT.lt Nat instLTNat (Fin.val self) n`
        // (statement-shape drift), and Clean's `Fin.ofNat` below pins the
        // LEAN v4.8 SIGNATURE `{n} (a : Nat) : Fin (Nat.succ n)` — v4.31
        // changed it to `(n : Nat) → [NeZero n] → Nat → Fin n` (explicit n,
        // NeZero instance, target `Fin n`): signature-level drift that jams
        // the genuine Fin ⊤/OfNat instance chains (Fin.top_eq_last's 27-decl
        // Order cluster) and drags Clean's fuel-based `Nat.mod` into terms.
        // In import mode skip both so the genuine v4.31 declarations import
        // through the checked path (caller-graph closure verified: nothing
        // else in the import prelude references either name). The Fin
        // inductive, Fin.mk, and Fin.val stay in both lanes.
        let seed_fin_derived_ops = !self.suppress_lossy_structure_stubs;

        // Fin.isLt : {n : Nat} → (x : Fin n) → Nat.lt (Fin.val x) n
        //
        // The dependent projection of the faithful bound proof. It recurses with
        // `Fin.rec` into Prop with motive `λ x => Nat.lt (Fin.val x) n`; the `mk`
        // minor returns the `isLt` field. This is well-typed because
        // `Fin.val (Fin.mk val p) ≡ val` (ι), so the motive at the constructor is
        // `Nat.lt val n`, which is exactly the field's type.
        let fin_val_c = Expr::const_(Name::from_string("Fin.val"), vec![]);
        // The recursor lands in Prop here, so its motive universe is `0`.
        let fin_rec_prop = Expr::const_(Name::from_string("Fin.rec"), vec![Level::zero()]);

        let fin_islt_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let fin_n = Expr::app(fin_const.clone(), n.clone());
            let (x_id, x) = b.fresh_local(fin_n.clone());
            // Nat.lt (@Fin.val n x) n
            let val_x = Expr::app(Expr::app(fin_val_c.clone(), n.clone()), x);
            let r = Expr::app(Expr::app(nat_lt.clone(), val_x), n.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, fin_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        // Fin.isLt value: λ {n} (x : Fin n) => Fin.rec n motive mk_case x
        let fin_islt_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let fin_n = Expr::app(fin_const.clone(), n.clone());
            let (x_id, x) = b.fresh_local(fin_n.clone());

            // motive: λ (w : Fin n) => Nat.lt (@Fin.val n w) n
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(fin_n.clone());
                let val_w = Expr::app(Expr::app(fin_val_c.clone(), n.clone()), w);
                let r = Expr::app(Expr::app(nat_lt.clone(), val_w), n.clone());
                let r = c.mk_lam(w_id, BinderInfo::Default, fin_n.clone(), r);
                c.finish_child(r)
            };

            // case for mk: λ (val : Nat) (isLt : Nat.lt val n) => isLt
            // Well-typed: the motive at `Fin.mk val isLt` is
            // `Nat.lt (@Fin.val n (Fin.mk val isLt)) n ≡ Nat.lt val n` (ι).
            let mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (val_id, val) = c.fresh_local(nat_const.clone());
                let islt_ty = Expr::app(Expr::app(nat_lt.clone(), val.clone()), n.clone());
                let (proof_id, proof) = c.fresh_local(islt_ty.clone());
                let r = proof;
                let r = c.mk_lam(proof_id, BinderInfo::Default, islt_ty, r);
                let r = c.mk_lam(val_id, BinderInfo::Default, nat_const.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(fin_rec_prop.clone(), n.clone()), motive),
                    mk_case,
                ),
                x,
            );
            let r = b.mk_lam(x_id, BinderInfo::Default, fin_n, body);
            let r = b.mk_lam(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        if seed_fin_derived_ops {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Fin.isLt"),
                level_params: vec![],
                type_: fin_islt_type,
                value: fin_islt_value,
                is_reducible: true,
            })?;
        }

        // Fin.ofNat {n : Nat} (a : Nat) : Fin (Nat.succ n) :=
        //   ⟨a % (Nat.succ n), Nat.mod_lt a (Nat.zero_lt_succ n)⟩
        //
        // LEAN 4.8.0 FIDELITY (`Init/Data/Fin/Basic.lean`):
        //   protected def Fin.ofNat {n} (a : Nat) : Fin n.succ :=
        //     ⟨a % n.succ, Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
        //
        // Registered here (not as an axiom) so `UInt<w>.ofNat n := ⟨Fin.ofNat n⟩`
        // — the real olean `UInt<w>.ofNat`/`instOfNatUInt<w>` — re-verifies
        // against the prelude's Fin-carrier `UInt<w>.mk`. Depends on `Nat.mod`
        // (from `init_nat`), the axiom-free `Nat.mod_lt` (pulled in idempotently),
        // and `Nat.zero_lt_succ`.
        if seed_fin_derived_ops && self.get_const(&Name::from_string("Fin.ofNat")).is_none() {
            // `Fin.ofNat` needs `Nat.mod` (init_nat), `Nat.zero_lt_succ`
            // (init_nat_top_level_ordering), and the axiom-free `Nat.mod_lt`
            // (init_nat_div_mod_lemmas). `init_nat_div_mod_lemmas` in turn needs
            // the full Nat-ordering leaf-lemma set (`Nat.not_succ_le_zero`,
            // `Nat.le_of_succ_le_succ`, `Nat.le_trans`, `Nat.sub_le`,
            // `Nat.add_assoc`/`_comm`, `Nat.zero_add`, `Nat.zero_le`, …). Because
            // `init_fin` runs EARLY in the prelude (before those are otherwise
            // wired), pull the complete chain here explicitly. Every call is
            // idempotent and self-contained (transitively rooted at
            // `init_nat`/`init_eq`; none depends on `Fin`, so no init cycle).
            self.init_nat_top_level_ordering()?; // Nat.zero_lt_succ, succ_le_succ, le_refl, le_of_succ_le_succ chain
            self.register_nat_not_succ_le_zero_theorem()?; // Nat.not_succ_le_zero
            self.register_nat_le_of_succ_le_succ_theorem()?; // Nat.le_of_succ_le_succ
            self.register_nat_le_trans_proof()?; // Nat.le_trans
            self.register_nat_arith_order_proofs()?; // Nat.add_le_add_left, Nat.sub_le
            self.register_nat_ble_le_lemmas()?; // Nat.zero_le (+ ble↔le bridge)
            self.register_nat_add_assoc_proof()?; // Nat.add_assoc
            self.register_nat_add_comm_proof()?; // Nat.add_comm
            self.register_nat_zero_add_proof()?; // Nat.zero_add
            self.init_nat_div_mod_lemmas()?; // Nat.mod_lt (needs all of the above)

            let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            let nat_mod = Expr::const_(Name::from_string("Nat.mod"), vec![]);
            let nat_mod_lt = Expr::const_(Name::from_string("Nat.mod_lt"), vec![]);
            let nat_zero_lt_succ = Expr::const_(Name::from_string("Nat.zero_lt_succ"), vec![]);
            let fin_mk_c = Expr::const_(Name::from_string("Fin.mk"), vec![]);

            // type: {n : Nat} → (a : Nat) → Fin (Nat.succ n)
            let of_nat_type = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let (a_id, _a) = b.fresh_local(nat_const.clone());
                let succ_n = Expr::app(nat_succ.clone(), n.clone());
                let r = Expr::app(fin_const.clone(), succ_n);
                let r = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), r);
                let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), r);
                b.finish(r)
            };

            // value: λ {n} (a) =>
            //   Fin.mk (Nat.succ n) (Nat.mod a (Nat.succ n))
            //          (Nat.mod_lt a (Nat.succ n) (Nat.zero_lt_succ n))
            let of_nat_value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let (a_id, a) = b.fresh_local(nat_const.clone());
                let succ_n = Expr::app(nat_succ.clone(), n.clone());
                let a_mod = Expr::apps(nat_mod.clone(), [a.clone(), succ_n.clone()]);
                let pos = Expr::app(nat_zero_lt_succ.clone(), n.clone());
                let modlt = Expr::apps(nat_mod_lt.clone(), [a.clone(), succ_n.clone(), pos]);
                // @Fin.mk (Nat.succ n) (a % (Nat.succ n)) modlt
                let body = Expr::apps(fin_mk_c.clone(), [succ_n, a_mod, modlt]);
                let r = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), body);
                let r = b.mk_lam(n_id, BinderInfo::Implicit, nat_const.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Fin.ofNat"),
                level_params: vec![],
                type_: of_nat_type,
                value: of_nat_value,
                is_reducible: true,
            })?;
        }

        self.fin_init = true;
        Ok(())
    }

    /// Check if Fin has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_fin` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_fin(&self) -> bool {
        self.fin_init
    }

    /// Initialize the Array type
    ///
    /// Array is a polymorphic array type backed by List for now:
    /// ```text
    /// structure Array (α : Type u) : Type u where
    ///   data : List α
    /// ```
    ///
    /// This adds:
    /// - Array : Type u → Type u
    /// - Array.mk : {α : Type u} → List α → Array α
    /// - Array.data : {α : Type u} → Array α → List α
    /// - Array.size : {α : Type u} → Array α → Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.array_init == true`
    /// ENSURES: On success, required dependencies (`list`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_array(&mut self) -> Result<(), EnvError> {
        if self.array_init {
            return Ok(());
        }

        // Ensure List is initialized
        self.init_list()?;

        let u = Name::from_string("u");
        let level_u = Level::param(u.clone());

        // α : Type u
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(level_u.clone())));

        // Array : Type u → Type u
        let array_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

        let array_const = Expr::const_(Name::from_string("Array"), vec![level_u.clone()]);
        let list_const = Expr::const_(Name::from_string("List"), vec![level_u.clone()]);

        // Array.mk : {α : Type u} → List α → Array α
        let array_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (d_id, _d) = b.fresh_local(Expr::app(list_const.clone(), alpha.clone()));
            let r = Expr::app(array_const.clone(), alpha.clone());
            let r = b.mk_pi(
                d_id,
                BinderInfo::Default,
                Expr::app(list_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let array_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1, // α is a parameter
            types: vec![InductiveType {
                name: Name::from_string("Array"),
                type_: array_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Array.mk"),
                    type_: array_mk_type,
                }],
            }],
        };

        self.add_inductive(array_decl)?;

        // Register structure fields
        self.register_structure_fields(
            Name::from_string("Array"),
            vec![Name::from_string("data")],
        )?;

        let array_rec = Expr::const_(
            Name::from_string("Array.rec"),
            vec![Level::succ(level_u.clone()), level_u.clone()],
        );

        // Array.data : {α : Type u} → Array α → List α
        let array_data_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (arr_id, _arr) = b.fresh_local(Expr::app(array_const.clone(), alpha.clone()));
            let r = Expr::app(list_const.clone(), alpha.clone());
            let r = b.mk_pi(
                arr_id,
                BinderInfo::Default,
                Expr::app(array_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Array.data value: λ {α} (arr) => Array.rec α motive mk_case arr
        let array_data_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (arr_id, arr) = b.fresh_local(Expr::app(array_const.clone(), alpha.clone()));

            // motive: λ (_ : Array α) => List α
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(Expr::app(array_const.clone(), alpha.clone()));
                let r = Expr::app(list_const.clone(), alpha.clone());
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(array_const.clone(), alpha.clone()),
                    r,
                );
                c.finish_child(r)
            };

            // case for mk: λ (data : List α) => data
            let mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (d_id, d) = c.fresh_local(Expr::app(list_const.clone(), alpha.clone()));
                let r = d;
                let r = c.mk_lam(
                    d_id,
                    BinderInfo::Default,
                    Expr::app(list_const.clone(), alpha.clone()),
                    r,
                );
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(array_rec.clone(), alpha.clone()), motive),
                    mk_case,
                ),
                arr,
            );
            let r = b.mk_lam(
                arr_id,
                BinderInfo::Default,
                Expr::app(array_const.clone(), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Array.data"),
            level_params: vec![u.clone()],
            type_: array_data_type,
            value: array_data_value,
            is_reducible: true,
        })?;

        // Array.toList : {α : Type u} → Array α → List α := fun {α} a => Array.data α a
        //
        // R145: the modern Lean 4 accessor for an array's backing list — an
        // alias for `Array.data` (upstream renamed the `Array.data` field to
        // `Array.toList`). `a.toList` is far more common in real Lean 4 code
        // than `a.data`; without a registered `Array.toList`, dot-notation
        // `a.toList` failed LOUD with `UnknownProjectionField` (Array's only
        // field is `data`, and dot notation's namespace-function fallback —
        // the same path that resolves `a.size`/`a.push` — had nothing to find).
        // Reducible + axiom-free (delegates to `Array.data`). Withheld in
        // import mode like `Array.size`: the genuine olean `Array.toList`
        // imports through the checked path.
        if !self.suppress_lossy_structure_stubs
            && self.get_const(&Name::from_string("Array.toList")).is_none()
        {
            let array_tolist_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (arr_id, _arr) = b.fresh_local(Expr::app(array_const.clone(), alpha.clone()));
                let r = Expr::app(list_const.clone(), alpha.clone());
                let r = b.mk_pi(
                    arr_id,
                    BinderInfo::Default,
                    Expr::app(array_const.clone(), alpha.clone()),
                    r,
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            let array_tolist_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (arr_id, arr) = b.fresh_local(Expr::app(array_const.clone(), alpha.clone()));
                let array_data_const =
                    Expr::const_(Name::from_string("Array.data"), vec![level_u.clone()]);
                let body = Expr::app(Expr::app(array_data_const, alpha.clone()), arr);
                let r = b.mk_lam(
                    arr_id,
                    BinderInfo::Default,
                    Expr::app(array_const.clone(), alpha.clone()),
                    body,
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Array.toList"),
                level_params: vec![u.clone()],
                type_: array_tolist_type,
                value: array_tolist_value,
                is_reducible: true,
            })?;
        }

        // List.toArray : {α : Type u} → List α → Array α := fun {α} l => Array.mk α l
        //
        // R146: the standard Lean 4 conversion `l.toArray` — wraps a list in the
        // single-field Array constructor (Array.mk {α} (data : List α)), the
        // inverse of Array.toList/Array.data. Without it, `l.toArray` failed LOUD
        // with UnknownIdent (no List.toArray in the namespace). Reducible +
        // axiom-free; l.toArray.toList reduces back to l (proj-of-mk iota).
        // Withheld in import mode: the genuine olean List.toArray imports through
        // the checked path.
        if !self.suppress_lossy_structure_stubs
            && self.get_const(&Name::from_string("List.toArray")).is_none()
        {
            let list_toarray_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (l_id, _l) = b.fresh_local(Expr::app(list_const.clone(), alpha.clone()));
                let r = Expr::app(array_const.clone(), alpha.clone());
                let r = b.mk_pi(
                    l_id,
                    BinderInfo::Default,
                    Expr::app(list_const.clone(), alpha.clone()),
                    r,
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let list_toarray_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (l_id, l) = b.fresh_local(Expr::app(list_const.clone(), alpha.clone()));
                let array_mk = Expr::const_(Name::from_string("Array.mk"), vec![level_u.clone()]);
                let body = Expr::app(Expr::app(array_mk, alpha.clone()), l);
                let r = b.mk_lam(
                    l_id,
                    BinderInfo::Default,
                    Expr::app(list_const.clone(), alpha.clone()),
                    body,
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.toArray"),
                level_params: vec![u.clone()],
                type_: list_toarray_type,
                value: list_toarray_value,
                is_reducible: true,
            })?;
        }

        // Array.mkEmpty : {α : Type u} → Nat → Array α := fun {α} _c => Array.mk α List.nil
        //
        // R148: Lean 4's `Array.mkEmpty (capacity : Nat)` builds an empty array
        // (the capacity is only a runtime preallocation hint — the logical value
        // is `#[]` for any capacity). Registered as a reducible axiom-free
        // wrapper that ignores its Nat argument and returns `Array.mk List.nil`.
        // Without it, `Array.mkEmpty n` failed LOUD with UnknownIdent. Withheld
        // in import mode like the R145-R147 accessors; guarded against double-
        // registration.
        if !self.suppress_lossy_structure_stubs
            && self
                .get_const(&Name::from_string("Array.mkEmpty"))
                .is_none()
        {
            let nat_c = Expr::const_(Name::from_string("Nat"), vec![]);
            let list_nil = Expr::const_(Name::from_string("List.nil"), vec![level_u.clone()]);
            let array_mk_u = Expr::const_(Name::from_string("Array.mk"), vec![level_u.clone()]);
            let array_mkempty_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (c_id, _c) = b.fresh_local(nat_c.clone());
                let r = Expr::app(array_const.clone(), alpha.clone());
                let r = b.mk_pi(c_id, BinderInfo::Default, nat_c.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let array_mkempty_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (c_id, _c) = b.fresh_local(nat_c.clone());
                let nil_a = Expr::app(list_nil.clone(), alpha.clone());
                let body = Expr::apps(array_mk_u.clone(), [alpha.clone(), nil_a]);
                let e = b.mk_lam(c_id, BinderInfo::Default, nat_c.clone(), body);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Array.mkEmpty"),
                level_params: vec![u.clone()],
                type_: array_mkempty_type,
                value: array_mkempty_value,
                is_reducible: true,
            })?;
        }

        // Array.size : {α : Type u} → Array α → Nat
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): `Array.size` wraps the import-gated `List.length` seed
        // (absent at init time — Lean v4.30 stores List.length as a brecOn
        // tower, so the direct List.rec seed fails the value-defeq dedup), so
        // it is gated with the List.* recursion cluster (see
        // data_collection_ops.rs). The genuine olean `Array.size` imports
        // through the checked path; its name-keyed native reducer still fires.
        if !self.suppress_lossy_structure_stubs {
            let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
            let list_length = Expr::const_(Name::from_string("List.length"), vec![level_u.clone()]);
            let array_data_const =
                Expr::const_(Name::from_string("Array.data"), vec![level_u.clone()]);

            let array_size_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (arr_id, _arr) = b.fresh_local(Expr::app(array_const.clone(), alpha.clone()));
                let r = nat_const.clone();
                let r = b.mk_pi(
                    arr_id,
                    BinderInfo::Default,
                    Expr::app(array_const.clone(), alpha.clone()),
                    r,
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            let array_size_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (arr_id, arr) = b.fresh_local(Expr::app(array_const.clone(), alpha.clone()));
                let body = Expr::app(
                    Expr::app(list_length, alpha.clone()),
                    Expr::app(Expr::app(array_data_const, alpha.clone()), arr),
                );
                let r = b.mk_lam(
                    arr_id,
                    BinderInfo::Default,
                    Expr::app(array_const.clone(), alpha.clone()),
                    body,
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Array.size"),
                level_params: vec![u.clone()],
                type_: array_size_type,
                value: array_size_value,
                is_reducible: true,
            })?;

            // Common Array combinators, defined compositionally over `Array.data`
            // exactly like `Array.size = List.length ∘ Array.data`. These are the
            // no-`start`/`stop` forms that everyday `as.foldl`/`as.map`/`as.push`
            // use; the genuine olean versions (with the optional range args) import
            // through the checked path in import mode, so — like `Array.size` — they
            // are registered only in prelude-only mode. Each is a real, kernel-checked
            // definition (zero axioms); the kernel re-checks the value against the
            // declared type at `add_decl`, so a malformed shape fails loudly here.
            //
            // These depend on `List.foldl` / `List.map`, which are registered by a
            // separate init pass (`init_list_ops` / the List recursion cluster) — not
            // by `init_list()` above. In the full `with_prelude()` build those run
            // first, so the guard holds; a *bare* `init_array()` (as some unit tests
            // call it) has only the List basics, so we skip these combinators there
            // rather than fail `add_decl` on an unknown `List.foldl` / `List.map`.
            if self.get_const(&Name::from_string("List.foldl")).is_some()
                && self.get_const(&Name::from_string("List.map")).is_some()
            {
                let w = Name::from_string("w");
                let level_w = Level::param(w.clone());
                let type_w = Expr::from_kind(ExprKind::Sort(Level::succ(level_w.clone())));
                let array_data_u =
                    Expr::const_(Name::from_string("Array.data"), vec![level_u.clone()]);

                // Array.foldl {α : Type u} {β : Type w} (f : β → α → β) (init : β)
                //     (as : Array α) : β  :=  List.foldl β α f init (Array.data as)
                // (α = element universe u [matches Array]; β = accumulator universe w).
                let list_foldl = Expr::const_(
                    Name::from_string("List.foldl"),
                    vec![level_w.clone(), level_u.clone()],
                );
                let array_foldl_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (beta_id, beta) = b.fresh_local(type_w.clone());
                    let f_ty = Expr::pi(
                        BinderInfo::Default,
                        beta.clone(),
                        Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone()),
                    );
                    let (f_id, _f) = b.fresh_local(f_ty.clone());
                    let (init_id, _init) = b.fresh_local(beta.clone());
                    let arr_ty = Expr::app(array_const.clone(), alpha.clone());
                    let (as_id, _as) = b.fresh_local(arr_ty.clone());
                    let e = beta.clone();
                    let e = b.mk_pi(as_id, BinderInfo::Default, arr_ty.clone(), e);
                    let e = b.mk_pi(init_id, BinderInfo::Default, beta.clone(), e);
                    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
                    let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_w.clone(), e);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let array_foldl_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (beta_id, beta) = b.fresh_local(type_w.clone());
                    let f_ty = Expr::pi(
                        BinderInfo::Default,
                        beta.clone(),
                        Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone()),
                    );
                    let (f_id, f) = b.fresh_local(f_ty.clone());
                    let (init_id, init) = b.fresh_local(beta.clone());
                    let arr_ty = Expr::app(array_const.clone(), alpha.clone());
                    let (as_id, as_v) = b.fresh_local(arr_ty.clone());
                    let data_app = Expr::apps(array_data_u.clone(), [alpha.clone(), as_v.clone()]);
                    let body = Expr::apps(
                        list_foldl.clone(),
                        [
                            beta.clone(),
                            alpha.clone(),
                            f.clone(),
                            init.clone(),
                            data_app,
                        ],
                    );
                    let e = b.mk_lam(as_id, BinderInfo::Default, arr_ty.clone(), body);
                    let e = b.mk_lam(init_id, BinderInfo::Default, beta.clone(), e);
                    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
                    let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_w.clone(), e);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("Array.foldl"),
                    level_params: vec![u.clone(), w.clone()],
                    type_: array_foldl_type,
                    value: array_foldl_value,
                    is_reducible: true,
                })?;

                // Array.map {α : Type u} {β : Type w} (f : α → β) (as : Array α)
                //     : Array β  :=  Array.mk (List.map f (Array.data as))
                let list_map = Expr::const_(
                    Name::from_string("List.map"),
                    vec![level_u.clone(), level_w.clone()],
                );
                let array_mk_w = Expr::const_(Name::from_string("Array.mk"), vec![level_w.clone()]);
                let array_const_w = Expr::const_(Name::from_string("Array"), vec![level_w.clone()]);
                let array_map_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (beta_id, beta) = b.fresh_local(type_w.clone());
                    let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
                    let (f_id, _f) = b.fresh_local(f_ty.clone());
                    let arr_a = Expr::app(array_const.clone(), alpha.clone());
                    let arr_b = Expr::app(array_const_w.clone(), beta.clone());
                    let (as_id, _as) = b.fresh_local(arr_a.clone());
                    let e = arr_b;
                    let e = b.mk_pi(as_id, BinderInfo::Default, arr_a.clone(), e);
                    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
                    let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_w.clone(), e);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let array_map_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (beta_id, beta) = b.fresh_local(type_w.clone());
                    let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
                    let (f_id, f) = b.fresh_local(f_ty.clone());
                    let arr_a = Expr::app(array_const.clone(), alpha.clone());
                    let (as_id, as_v) = b.fresh_local(arr_a.clone());
                    let data_app = Expr::apps(array_data_u.clone(), [alpha.clone(), as_v.clone()]);
                    let mapped = Expr::apps(
                        list_map.clone(),
                        [alpha.clone(), beta.clone(), f.clone(), data_app],
                    );
                    let body = Expr::apps(array_mk_w.clone(), [beta.clone(), mapped]);
                    let e = b.mk_lam(as_id, BinderInfo::Default, arr_a.clone(), body);
                    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
                    let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_w.clone(), e);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("Array.map"),
                    level_params: vec![u.clone(), w.clone()],
                    type_: array_map_type,
                    value: array_map_value,
                    is_reducible: true,
                })?;
            } // end List.foldl/List.map availability guard

            // Array.foldr {α : Type u} {β : Type w} (f : α → β → β) (init : β)
            //     (as : Array α) : β  :=  List.foldr f init (Array.data as)
            // (mirrors Array.foldl; `List.foldr α β` binds element-first). Guarded
            // on List.foldr like the foldl/map block — see that block's comment.
            if self.get_const(&Name::from_string("List.foldr")).is_some() {
                let w = Name::from_string("w");
                let level_w = Level::param(w.clone());
                let type_w = Expr::from_kind(ExprKind::Sort(Level::succ(level_w.clone())));
                let array_data_u =
                    Expr::const_(Name::from_string("Array.data"), vec![level_u.clone()]);
                let list_foldr = Expr::const_(
                    Name::from_string("List.foldr"),
                    vec![level_u.clone(), level_w.clone()],
                );
                let array_foldr_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (beta_id, beta) = b.fresh_local(type_w.clone());
                    let f_ty = Expr::pi(
                        BinderInfo::Default,
                        alpha.clone(),
                        Expr::pi(BinderInfo::Default, beta.clone(), beta.clone()),
                    );
                    let (f_id, _f) = b.fresh_local(f_ty.clone());
                    let (init_id, _init) = b.fresh_local(beta.clone());
                    let arr_ty = Expr::app(array_const.clone(), alpha.clone());
                    let (as_id, _as) = b.fresh_local(arr_ty.clone());
                    let e = beta.clone();
                    let e = b.mk_pi(as_id, BinderInfo::Default, arr_ty.clone(), e);
                    let e = b.mk_pi(init_id, BinderInfo::Default, beta.clone(), e);
                    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
                    let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_w.clone(), e);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let array_foldr_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (beta_id, beta) = b.fresh_local(type_w.clone());
                    let f_ty = Expr::pi(
                        BinderInfo::Default,
                        alpha.clone(),
                        Expr::pi(BinderInfo::Default, beta.clone(), beta.clone()),
                    );
                    let (f_id, f) = b.fresh_local(f_ty.clone());
                    let (init_id, init) = b.fresh_local(beta.clone());
                    let arr_ty = Expr::app(array_const.clone(), alpha.clone());
                    let (as_id, as_v) = b.fresh_local(arr_ty.clone());
                    let data_app = Expr::apps(array_data_u.clone(), [alpha.clone(), as_v.clone()]);
                    let body = Expr::apps(
                        list_foldr.clone(),
                        [
                            alpha.clone(),
                            beta.clone(),
                            f.clone(),
                            init.clone(),
                            data_app,
                        ],
                    );
                    let e = b.mk_lam(as_id, BinderInfo::Default, arr_ty.clone(), body);
                    let e = b.mk_lam(init_id, BinderInfo::Default, beta.clone(), e);
                    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
                    let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_w.clone(), e);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("Array.foldr"),
                    level_params: vec![u.clone(), w.clone()],
                    type_: array_foldr_type,
                    value: array_foldr_value,
                    is_reducible: true,
                })?;
            } // end List.foldr availability guard

            // Array.push {α : Type u} (as : Array α) (a : α) : Array α
            //     := Array.mk (List.append (Array.data as) (List.cons a List.nil))
            // i.e. `as.data ++ [a]`, wrapped back into an Array. Guarded on
            // List.append (List.cons/nil are the List constructors, always present).
            if self.get_const(&Name::from_string("List.append")).is_some() {
                let array_data_u =
                    Expr::const_(Name::from_string("Array.data"), vec![level_u.clone()]);
                let array_mk_u = Expr::const_(Name::from_string("Array.mk"), vec![level_u.clone()]);
                let list_append =
                    Expr::const_(Name::from_string("List.append"), vec![level_u.clone()]);
                let list_cons = Expr::const_(Name::from_string("List.cons"), vec![level_u.clone()]);
                let list_nil = Expr::const_(Name::from_string("List.nil"), vec![level_u.clone()]);
                let array_push_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let arr_ty = Expr::app(array_const.clone(), alpha.clone());
                    let (as_id, _as) = b.fresh_local(arr_ty.clone());
                    let (a_id, _a) = b.fresh_local(alpha.clone());
                    let e = arr_ty.clone();
                    let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
                    let e = b.mk_pi(as_id, BinderInfo::Default, arr_ty.clone(), e);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let array_push_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let arr_ty = Expr::app(array_const.clone(), alpha.clone());
                    let (as_id, as_v) = b.fresh_local(arr_ty.clone());
                    let (a_id, a) = b.fresh_local(alpha.clone());
                    let data_app = Expr::apps(array_data_u.clone(), [alpha.clone(), as_v.clone()]);
                    // [a] = List.cons α a (List.nil α)
                    let nil_app = Expr::app(list_nil.clone(), alpha.clone());
                    let singleton =
                        Expr::apps(list_cons.clone(), [alpha.clone(), a.clone(), nil_app]);
                    // (Array.data as) ++ [a]
                    let appended =
                        Expr::apps(list_append.clone(), [alpha.clone(), data_app, singleton]);
                    let body = Expr::apps(array_mk_u.clone(), [alpha.clone(), appended]);
                    let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
                    let e = b.mk_lam(as_id, BinderInfo::Default, arr_ty.clone(), e);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("Array.push"),
                    level_params: vec![u.clone()],
                    type_: array_push_type,
                    value: array_push_value,
                    is_reducible: true,
                })?;
            } // end List.append availability guard
        } // end import-mode Array.size suppression

        // instOfNatFin : {n i : Nat} → OfNat (Fin (Nat.succ n)) i
        //   := OfNat.mk (Fin (Nat.succ n)) i (Fin.ofNat i)
        // Makes numeric literals at a `Fin (n+1)` type elaborate — `(3 : Fin 5)` —
        // by wrapping the existing `Fin.ofNat` (which reduces `i % (n+1)`). Guarded
        // on Fin.ofNat + OfNat.mk being present (both are registered earlier in the
        // full prelude; a bare init_array may lack them) and on the instance not
        // already existing. Registered as an OfNat instance so synthesis finds it.
        if self.get_const(&Name::from_string("instOfNatFin")).is_none()
            && self.get_const(&Name::from_string("Fin.ofNat")).is_some()
            && self.get_const(&Name::from_string("OfNat.mk")).is_some()
        {
            let nat_c = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            let fin_c = Expr::const_(Name::from_string("Fin"), vec![]);
            let ofnat_c = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
            let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);
            let fin_ofnat = Expr::const_(Name::from_string("Fin.ofNat"), vec![]);

            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_c.clone());
                let (i_id, i) = b.fresh_local(nat_c.clone());
                let fin_succ_n = Expr::app(fin_c.clone(), Expr::app(nat_succ.clone(), n.clone()));
                let e = Expr::apps(ofnat_c.clone(), [fin_succ_n, i.clone()]);
                let e = b.mk_pi(i_id, BinderInfo::Implicit, nat_c.clone(), e);
                let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_c.clone(), e);
                b.finish(e)
            };
            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_c.clone());
                let (i_id, i) = b.fresh_local(nat_c.clone());
                let fin_succ_n = Expr::app(fin_c.clone(), Expr::app(nat_succ.clone(), n.clone()));
                // @Fin.ofNat n i : Fin (Nat.succ n)
                let val = Expr::apps(fin_ofnat.clone(), [n.clone(), i.clone()]);
                // OfNat.mk (Fin (succ n)) i val
                let body = Expr::apps(ofnat_mk.clone(), [fin_succ_n, i.clone(), val]);
                let e = b.mk_lam(i_id, BinderInfo::Implicit, nat_c.clone(), body);
                let e = b.mk_lam(n_id, BinderInfo::Implicit, nat_c.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instOfNatFin"),
                level_params: vec![],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;
            self.register_instance(crate::env::KernelInstanceInfo {
                name: Name::from_string("instOfNatFin"),
                class_name: Name::from_string("OfNat"),
                priority: 100,
                type_: None,
                value: None,
            });
        }

        // List.getD {α : Type u} (l : List α) (i : Nat) (fallback : α) : α
        //   = (List.rec (motive := fun _ : List α => Nat → α)
        //        (fun _ : Nat => fallback)
        //        (fun hd _tl ih => fun i => Nat.rec (motive := fun _ : Nat => α)
        //           hd (fun i' _ => ih i') i)
        //        l) i
        // The TOTAL index-with-explicit-default (no `Inhabited`): a left-to-right
        // walk down the list, decrementing the index, falling back on nil. Built
        // from `List.rec` (into a `Nat → α` step function) with an inner `Nat.rec`;
        // `List.rec.{succ u, u}` (motive returns `Nat → α : Type u`), `Nat.rec.{succ
        // u}` (motive returns `α : Type u`). Guarded on List.rec + Nat.rec — both are
        // fundamental, but a bare `init_array()` (some unit tests) may lack Nat.rec,
        // so skip there rather than fail. Zero axioms; kernel-checked at add_decl.
        if self.get_const(&Name::from_string("List.getD")).is_none()
            && self.get_const(&Name::from_string("List.rec")).is_some()
            && self.get_const(&Name::from_string("Nat.rec")).is_some()
        {
            let nat_c = Expr::const_(Name::from_string("Nat"), vec![]);
            let list_c = Expr::const_(Name::from_string("List"), vec![level_u.clone()]);
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(level_u.clone()), level_u.clone()],
            );
            let nat_rec = Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(level_u.clone())],
            );

            let getd_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_a = Expr::app(list_c.clone(), alpha.clone());
                let (l_id, _l) = b.fresh_local(list_a.clone());
                let (i_id, _i) = b.fresh_local(nat_c.clone());
                let (fb_id, _fb) = b.fresh_local(alpha.clone());
                let e = alpha.clone();
                let e = b.mk_pi(fb_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(i_id, BinderInfo::Default, nat_c.clone(), e);
                let e = b.mk_pi(l_id, BinderInfo::Default, list_a.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let getd_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_a = Expr::app(list_c.clone(), alpha.clone());
                let nat_to_a = Expr::pi(BinderInfo::Default, nat_c.clone(), alpha.clone());
                let (l_id, l) = b.fresh_local(list_a.clone());
                let (i_id, i) = b.fresh_local(nat_c.clone());
                let (fb_id, fb) = b.fresh_local(alpha.clone());

                // motive: fun (_ : List α) => Nat → α
                let (mw_id, _mw) = b.fresh_local(list_a.clone());
                let motive = b.mk_lam(mw_id, BinderInfo::Default, list_a.clone(), nat_to_a.clone());

                // nil case: fun (_ : Nat) => fallback
                let (nn_id, _nn) = b.fresh_local(nat_c.clone());
                let nil_case = b.mk_lam(nn_id, BinderInfo::Default, nat_c.clone(), fb.clone());

                // cons case: fun (hd : α) (_tl : List α) (ih : Nat → α) =>
                //   fun (j : Nat) => Nat.rec (fun _ : Nat => α) hd (fun i' _ => ih i') j
                let (hd_id, hd) = b.fresh_local(alpha.clone());
                let (tl_id, _tl) = b.fresh_local(list_a.clone());
                let (ih_id, ih) = b.fresh_local(nat_to_a.clone());
                let (im_id, _im) = b.fresh_local(nat_c.clone());
                let inner_motive =
                    b.mk_lam(im_id, BinderInfo::Default, nat_c.clone(), alpha.clone());
                let (ip_id, ip) = b.fresh_local(nat_c.clone());
                let (iacc_id, _iacc) = b.fresh_local(alpha.clone());
                let ih_ip = Expr::app(ih.clone(), ip.clone());
                let succ_case = b.mk_lam(iacc_id, BinderInfo::Default, alpha.clone(), ih_ip);
                let succ_case = b.mk_lam(ip_id, BinderInfo::Default, nat_c.clone(), succ_case);
                let (j_id, j) = b.fresh_local(nat_c.clone());
                let natrec_app = Expr::apps(
                    nat_rec.clone(),
                    [inner_motive, hd.clone(), succ_case, j.clone()],
                );
                let cons_inner = b.mk_lam(j_id, BinderInfo::Default, nat_c.clone(), natrec_app);
                let cons_case = b.mk_lam(ih_id, BinderInfo::Default, nat_to_a.clone(), cons_inner);
                let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_a.clone(), cons_case);
                let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

                // (List.rec α motive nil_case cons_case l) i
                let listrec_app = Expr::apps(
                    list_rec.clone(),
                    [alpha.clone(), motive, nil_case, cons_case, l.clone()],
                );
                let body = Expr::app(listrec_app, i.clone());
                let e = b.mk_lam(fb_id, BinderInfo::Default, alpha.clone(), body);
                let e = b.mk_lam(i_id, BinderInfo::Default, nat_c.clone(), e);
                let e = b.mk_lam(l_id, BinderInfo::Default, list_a.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.getD"),
                level_params: vec![u.clone()],
                type_: getd_type,
                value: getd_value,
                is_reducible: true,
            })?;

            // ---- List.headD ----
            // R149: `l.headD default` — the head of a list, or the default on the
            // empty list. A simple `List.rec` fold with motive `fun _ => α`:
            // nil ↦ default, cons hd _ _ ↦ hd. Reducible + axiom-free. Without
            // it, `l.headD d` failed LOUD with UnknownIdent (dot notation's
            // namespace-function fallback had no List.headD). Withheld in import
            // mode like the R145-R148 accessors; guarded against double-register.
            if !self.suppress_lossy_structure_stubs
                && self.get_const(&Name::from_string("List.headD")).is_none()
            {
                let headd_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let (l_id, _l) = b.fresh_local(list_a.clone());
                    let (d_id, _d) = b.fresh_local(alpha.clone());
                    let e = alpha.clone();
                    let e = b.mk_pi(d_id, BinderInfo::Default, alpha.clone(), e);
                    let e = b.mk_pi(l_id, BinderInfo::Default, list_a.clone(), e);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let headd_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let (l_id, l) = b.fresh_local(list_a.clone());
                    let (d_id, d) = b.fresh_local(alpha.clone());
                    // motive: fun (_ : List α) => α
                    let (mw_id, _mw) = b.fresh_local(list_a.clone());
                    let motive =
                        b.mk_lam(mw_id, BinderInfo::Default, list_a.clone(), alpha.clone());
                    // nil case: default
                    let nil_case = d.clone();
                    // cons case: fun (hd : α) (_tl : List α) (_ih : α) => hd
                    let (hd_id, hd) = b.fresh_local(alpha.clone());
                    let (tl_id, _tl) = b.fresh_local(list_a.clone());
                    let (ih_id, _ih) = b.fresh_local(alpha.clone());
                    let cons_case = b.mk_lam(ih_id, BinderInfo::Default, alpha.clone(), hd.clone());
                    let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_a.clone(), cons_case);
                    let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);
                    // List.rec α motive nil_case cons_case l
                    let body = Expr::apps(
                        list_rec.clone(),
                        [alpha.clone(), motive, nil_case, cons_case, l.clone()],
                    );
                    let e = b.mk_lam(d_id, BinderInfo::Default, alpha.clone(), body);
                    let e = b.mk_lam(l_id, BinderInfo::Default, list_a.clone(), e);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("List.headD"),
                    level_params: vec![u.clone()],
                    type_: headd_type,
                    value: headd_value,
                    is_reducible: true,
                })?;
            }

            // ---- List.head? ----
            // R150: `l.head?` — the head of a list as an `Option` (none on the
            // empty list). Like List.headD but Option-valued: a `List.rec` fold
            // with motive `fun _ => Option α` (nil ↦ Option.none, cons hd _ _ ↦
            // Option.some hd). Reducible + axiom-free, no native reducer to
            // coexist with. Without it, `l.head?` failed LOUD with UnknownIdent.
            // Withheld in import mode like the R145-R149 accessors.
            if !self.suppress_lossy_structure_stubs
                && self.get_const(&Name::from_string("List.head?")).is_none()
            {
                // R150 references Option/Option.none/Option.some below; ensure
                // the Option inductive is registered on this path (idempotent),
                // matching the init_option() convention used by the getelem and
                // lazy-control registrations.
                self.init_option()?;
                let option_c = Expr::const_(Name::from_string("Option"), vec![level_u.clone()]);
                let head_opt_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let opt_a = Expr::app(option_c.clone(), alpha.clone());
                    let (l_id, _l) = b.fresh_local(list_a.clone());
                    let e = b.mk_pi(l_id, BinderInfo::Default, list_a.clone(), opt_a);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let head_opt_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let opt_a = Expr::app(option_c.clone(), alpha.clone());
                    let (l_id, l) = b.fresh_local(list_a.clone());
                    // motive: fun (_ : List α) => Option α
                    let (mw_id, _mw) = b.fresh_local(list_a.clone());
                    let motive =
                        b.mk_lam(mw_id, BinderInfo::Default, list_a.clone(), opt_a.clone());
                    // nil case: Option.none α
                    let option_none =
                        Expr::const_(Name::from_string("Option.none"), vec![level_u.clone()]);
                    let nil_case = Expr::app(option_none, alpha.clone());
                    // cons case: fun (hd : α) (_tl : List α) (_ih : Option α) => Option.some α hd
                    let option_some =
                        Expr::const_(Name::from_string("Option.some"), vec![level_u.clone()]);
                    let (hd_id, hd) = b.fresh_local(alpha.clone());
                    let (tl_id, _tl) = b.fresh_local(list_a.clone());
                    let (ih_id, _ih) = b.fresh_local(opt_a.clone());
                    let some_hd = Expr::apps(option_some, [alpha.clone(), hd.clone()]);
                    let cons_case = b.mk_lam(ih_id, BinderInfo::Default, opt_a.clone(), some_hd);
                    let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_a.clone(), cons_case);
                    let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);
                    let body = Expr::apps(
                        list_rec.clone(),
                        [alpha.clone(), motive, nil_case, cons_case, l.clone()],
                    );
                    let e = b.mk_lam(l_id, BinderInfo::Default, list_a.clone(), body);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("List.head?"),
                    level_params: vec![u.clone()],
                    type_: head_opt_type,
                    value: head_opt_value,
                    is_reducible: true,
                })?;
            }

            // ---- List.getLastD ----
            // R151: `l.getLastD d` — the last element of a list, or the default
            // on the empty list. Composed from the already-registered List.headD
            // (R149) and List.reverse: `List.getLastD l d := List.headD
            // (List.reverse l) d`. Reducible + axiom-free, no Inhabited, no
            // native reducer (unlike List.getLast!, which is why this is the
            // clean sibling). Without it, `l.getLastD d` failed LOUD with
            // UnknownIdent. Withheld in import mode like the R145-R150 accessors.
            if !self.suppress_lossy_structure_stubs
                && self
                    .get_const(&Name::from_string("List.getLastD"))
                    .is_none()
            {
                // R151 composes List.headD with List.reverse; ensure the list
                // operations (List.reverse et al.) are registered on this path
                // (idempotent), as for the R150 Option prerequisite.
                self.init_list_ops()?;
                let getlastd_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let (l_id, _l) = b.fresh_local(list_a.clone());
                    let (d_id, _d) = b.fresh_local(alpha.clone());
                    let e = alpha.clone();
                    let e = b.mk_pi(d_id, BinderInfo::Default, alpha.clone(), e);
                    let e = b.mk_pi(l_id, BinderInfo::Default, list_a.clone(), e);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let getlastd_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let (l_id, l) = b.fresh_local(list_a.clone());
                    let (d_id, d) = b.fresh_local(alpha.clone());
                    let list_headd =
                        Expr::const_(Name::from_string("List.headD"), vec![level_u.clone()]);
                    let list_reverse =
                        Expr::const_(Name::from_string("List.reverse"), vec![level_u.clone()]);
                    // List.reverse α l
                    let rev = Expr::apps(list_reverse, [alpha.clone(), l]);
                    // List.headD α (List.reverse α l) d
                    let body = Expr::apps(list_headd, [alpha.clone(), rev, d]);
                    let e = b.mk_lam(d_id, BinderInfo::Default, alpha.clone(), body);
                    let e = b.mk_lam(l_id, BinderInfo::Default, list_a.clone(), e);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("List.getLastD"),
                    level_params: vec![u.clone()],
                    type_: getlastd_type,
                    value: getlastd_value,
                    is_reducible: true,
                })?;
            }

            // ---- List.getLast? ----
            // R152: `l.getLast?` — the last element of a list as an `Option`
            // (none on empty). The Option-valued sibling of List.getLastD,
            // composed from List.head? (R150) and List.reverse: `List.getLast? l
            // := List.head? (List.reverse l)`. Reducible + axiom-free, no
            // Inhabited, no native reducer. Without it, `l.getLast?` failed LOUD
            // with UnknownIdent. Withheld in import mode like the R145-R151
            // accessors.
            if !self.suppress_lossy_structure_stubs
                && self
                    .get_const(&Name::from_string("List.getLast?"))
                    .is_none()
            {
                // R152 composes List.head? with List.reverse; ensure Option and
                // the list operations are registered on this path (idempotent).
                self.init_option()?;
                self.init_list_ops()?;
                let option_c = Expr::const_(Name::from_string("Option"), vec![level_u.clone()]);
                let getlast_opt_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let opt_a = Expr::app(option_c.clone(), alpha.clone());
                    let (l_id, _l) = b.fresh_local(list_a.clone());
                    let e = b.mk_pi(l_id, BinderInfo::Default, list_a.clone(), opt_a);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let getlast_opt_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let (l_id, l) = b.fresh_local(list_a.clone());
                    let list_head_opt =
                        Expr::const_(Name::from_string("List.head?"), vec![level_u.clone()]);
                    let list_reverse =
                        Expr::const_(Name::from_string("List.reverse"), vec![level_u.clone()]);
                    // List.reverse α l
                    let rev = Expr::apps(list_reverse, [alpha.clone(), l]);
                    // List.head? α (List.reverse α l)
                    let body = Expr::apps(list_head_opt, [alpha.clone(), rev]);
                    let e = b.mk_lam(l_id, BinderInfo::Default, list_a.clone(), body);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("List.getLast?"),
                    level_params: vec![u.clone()],
                    type_: getlast_opt_type,
                    value: getlast_opt_value,
                    is_reducible: true,
                })?;
            }

            // ---- List.head! ----
            // R153: `l.head!` — the head of a list, or the Inhabited default on
            // the empty list. Defined via the already-registered List.headD:
            // `List.head! l := List.headD l (Inhabited.default)`. `Inhabited` /
            // `Inhabited.default` are instantiated at `Level::succ u` (α : Type
            // u), and the instance argument is an `InstImplicit` binder — the
            // same threading as Array.get! (this block). Reducible, axiom-free,
            // no native reducer. Without it, `l.head!` failed LOUD with
            // UnknownIdent. Withheld in import mode like the R145-R152 accessors.
            if !self.suppress_lossy_structure_stubs
                && self.get_const(&Name::from_string("List.head!")).is_none()
                && self
                    .get_const(&Name::from_string("Inhabited.default"))
                    .is_some()
            {
                // α : Type u = Sort (succ u), so Inhabited / Inhabited.default
                // are instantiated at `Level::succ u` (same as the Array.get!
                // block). Inhabited.default is registered by init_inhabited,
                // which runs before init_array (guarded above for safety).
                let inhabited_const = Expr::const_(
                    Name::from_string("Inhabited"),
                    vec![Level::succ(level_u.clone())],
                );
                let inhabited_default = Expr::const_(
                    Name::from_string("Inhabited.default"),
                    vec![Level::succ(level_u.clone())],
                );
                let head_bang_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let (inst_id, _inst) = b.fresh_local(inhabited_alpha.clone());
                    let (l_id, _l) = b.fresh_local(list_a.clone());
                    let e = alpha.clone();
                    let e = b.mk_pi(l_id, BinderInfo::Default, list_a.clone(), e);
                    let e = b.mk_pi(
                        inst_id,
                        BinderInfo::InstImplicit,
                        inhabited_alpha.clone(),
                        e,
                    );
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let head_bang_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                    let list_a = Expr::app(list_c.clone(), alpha.clone());
                    let (inst_id, inst) = b.fresh_local(inhabited_alpha.clone());
                    let (l_id, l) = b.fresh_local(list_a.clone());
                    let list_headd =
                        Expr::const_(Name::from_string("List.headD"), vec![level_u.clone()]);
                    // Inhabited.default α inst
                    let default_val =
                        Expr::apps(inhabited_default.clone(), [alpha.clone(), inst.clone()]);
                    // List.headD α l (Inhabited.default α inst)
                    let body = Expr::apps(list_headd, [alpha.clone(), l, default_val]);
                    let e = b.mk_lam(l_id, BinderInfo::Default, list_a.clone(), body);
                    let e = b.mk_lam(
                        inst_id,
                        BinderInfo::InstImplicit,
                        inhabited_alpha.clone(),
                        e,
                    );
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("List.head!"),
                    level_params: vec![u.clone()],
                    type_: head_bang_type,
                    value: head_bang_value,
                    is_reducible: true,
                })?;
            }

            // Array.getD {α : Type u} (as : Array α) (i : Nat) (fallback : α) : α
            //   := List.getD (Array.data as) i fallback
            let array_data_u = Expr::const_(Name::from_string("Array.data"), vec![level_u.clone()]);
            let list_getd = Expr::const_(Name::from_string("List.getD"), vec![level_u.clone()]);
            let a_getd_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let arr_a = Expr::app(array_const.clone(), alpha.clone());
                let (as_id, _as) = b.fresh_local(arr_a.clone());
                let (i_id, _i) = b.fresh_local(nat_c.clone());
                let (fb_id, _fb) = b.fresh_local(alpha.clone());
                let e = alpha.clone();
                let e = b.mk_pi(fb_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(i_id, BinderInfo::Default, nat_c.clone(), e);
                let e = b.mk_pi(as_id, BinderInfo::Default, arr_a.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let a_getd_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let arr_a = Expr::app(array_const.clone(), alpha.clone());
                let (as_id, as_v) = b.fresh_local(arr_a.clone());
                let (i_id, i) = b.fresh_local(nat_c.clone());
                let (fb_id, fb) = b.fresh_local(alpha.clone());
                let data_app = Expr::apps(array_data_u.clone(), [alpha.clone(), as_v.clone()]);
                let body = Expr::apps(
                    list_getd.clone(),
                    [alpha.clone(), data_app, i.clone(), fb.clone()],
                );
                let e = b.mk_lam(fb_id, BinderInfo::Default, alpha.clone(), body);
                let e = b.mk_lam(i_id, BinderInfo::Default, nat_c.clone(), e);
                let e = b.mk_lam(as_id, BinderInfo::Default, arr_a.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Array.getD"),
                level_params: vec![u.clone()],
                type_: a_getd_type,
                value: a_getd_value,
                is_reducible: true,
            })?;
        } // end List.getD/Array.getD (List.rec + Nat.rec availability guard)

        // List.get! {α : Type u} [inst : Inhabited α] (l : List α) (i : Nat) : α
        //   := @List.getD α l i (@Inhabited.default α inst)
        // Array.get! {α : Type u} [inst : Inhabited α] (as : Array α) (i : Nat) : α
        //   := @List.get! α inst (Array.data as) i
        // The `Inhabited`-defaulted partial index accessors: `get!` = `getD` with the
        // fallback taken from the `Inhabited` instance (`get!` returns `default` on
        // out-of-bounds). `α : Type u = Sort (succ u)`, so `Inhabited` / `Inhabited.
        // default` are instantiated at `Level::succ u`; the instance argument is an
        // `InstImplicit` binder. Guarded on List.getD (from the block above) and
        // Inhabited.default (registered by init_inhabited, which runs before
        // init_array in the full prelude, absent in bare init_array — guard skips).
        // Zero axioms; kernel-checked at add_decl.
        if self.get_const(&Name::from_string("List.get!")).is_none()
            && self.get_const(&Name::from_string("List.getD")).is_some()
            && self
                .get_const(&Name::from_string("Inhabited.default"))
                .is_some()
        {
            let nat_c = Expr::const_(Name::from_string("Nat"), vec![]);
            let inhabited_const = Expr::const_(
                Name::from_string("Inhabited"),
                vec![Level::succ(level_u.clone())],
            );
            let inhabited_default = Expr::const_(
                Name::from_string("Inhabited.default"),
                vec![Level::succ(level_u.clone())],
            );
            let list_getd = Expr::const_(Name::from_string("List.getD"), vec![level_u.clone()]);

            // ---- List.get! ----
            let get_bang_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                let list_a = Expr::app(list_const.clone(), alpha.clone());
                let (inst_id, _inst) = b.fresh_local(inhabited_alpha.clone());
                let (l_id, _l) = b.fresh_local(list_a.clone());
                let (i_id, _i) = b.fresh_local(nat_c.clone());
                let e = alpha.clone();
                let e = b.mk_pi(i_id, BinderInfo::Default, nat_c.clone(), e);
                let e = b.mk_pi(l_id, BinderInfo::Default, list_a.clone(), e);
                let e = b.mk_pi(
                    inst_id,
                    BinderInfo::InstImplicit,
                    inhabited_alpha.clone(),
                    e,
                );
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let get_bang_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                let list_a = Expr::app(list_const.clone(), alpha.clone());
                let (inst_id, inst) = b.fresh_local(inhabited_alpha.clone());
                let (l_id, l) = b.fresh_local(list_a.clone());
                let (i_id, i) = b.fresh_local(nat_c.clone());
                let default_val =
                    Expr::apps(inhabited_default.clone(), [alpha.clone(), inst.clone()]);
                let body = Expr::apps(
                    list_getd.clone(),
                    [alpha.clone(), l.clone(), i.clone(), default_val],
                );
                let e = b.mk_lam(i_id, BinderInfo::Default, nat_c.clone(), body);
                let e = b.mk_lam(l_id, BinderInfo::Default, list_a.clone(), e);
                let e = b.mk_lam(
                    inst_id,
                    BinderInfo::InstImplicit,
                    inhabited_alpha.clone(),
                    e,
                );
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.get!"),
                level_params: vec![u.clone()],
                type_: get_bang_type,
                value: get_bang_value,
                is_reducible: true,
            })?;

            // ---- Array.get! ----
            let list_get_bang = Expr::const_(Name::from_string("List.get!"), vec![level_u.clone()]);
            let array_data_u = Expr::const_(Name::from_string("Array.data"), vec![level_u.clone()]);
            let a_get_bang_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                let arr_a = Expr::app(array_const.clone(), alpha.clone());
                let (inst_id, _inst) = b.fresh_local(inhabited_alpha.clone());
                let (as_id, _as) = b.fresh_local(arr_a.clone());
                let (i_id, _i) = b.fresh_local(nat_c.clone());
                let e = alpha.clone();
                let e = b.mk_pi(i_id, BinderInfo::Default, nat_c.clone(), e);
                let e = b.mk_pi(as_id, BinderInfo::Default, arr_a.clone(), e);
                let e = b.mk_pi(
                    inst_id,
                    BinderInfo::InstImplicit,
                    inhabited_alpha.clone(),
                    e,
                );
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let a_get_bang_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                let arr_a = Expr::app(array_const.clone(), alpha.clone());
                let (inst_id, inst) = b.fresh_local(inhabited_alpha.clone());
                let (as_id, as_v) = b.fresh_local(arr_a.clone());
                let (i_id, i) = b.fresh_local(nat_c.clone());
                let data_app = Expr::apps(array_data_u.clone(), [alpha.clone(), as_v.clone()]);
                let body = Expr::apps(
                    list_get_bang.clone(),
                    [alpha.clone(), inst.clone(), data_app, i.clone()],
                );
                let e = b.mk_lam(i_id, BinderInfo::Default, nat_c.clone(), body);
                let e = b.mk_lam(as_id, BinderInfo::Default, arr_a.clone(), e);
                let e = b.mk_lam(
                    inst_id,
                    BinderInfo::InstImplicit,
                    inhabited_alpha.clone(),
                    e,
                );
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Array.get!"),
                level_params: vec![u.clone()],
                type_: a_get_bang_type,
                value: a_get_bang_value,
                is_reducible: true,
            })?;

            // ---- Array.back ----
            // R147: `a.back` — the last element of an array (Inhabited default on
            // empty). Defined as `Array.get! a (a.size - 1)` over the just-
            // registered Array.get! / Array.size, so it is a thin reducible
            // wrapper (no new recursion, zero axioms): on a literal array the
            // chain reduces `size ↦ n`, `Nat.sub n 1`, `get! (n-1)`. Without it,
            // `a.back` failed LOUD (UnknownIdent — dot notation's namespace-fn
            // fallback had no Array.back). Withheld in import mode like the
            // R145/R146 accessors; guarded against double-registration.
            if !self.suppress_lossy_structure_stubs
                && self.get_const(&Name::from_string("Array.back")).is_none()
            {
                let array_back_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                    let arr_a = Expr::app(array_const.clone(), alpha.clone());
                    let (inst_id, _inst) = b.fresh_local(inhabited_alpha.clone());
                    let (as_id, _as) = b.fresh_local(arr_a.clone());
                    let e = alpha.clone();
                    let e = b.mk_pi(as_id, BinderInfo::Default, arr_a.clone(), e);
                    let e = b.mk_pi(
                        inst_id,
                        BinderInfo::InstImplicit,
                        inhabited_alpha.clone(),
                        e,
                    );
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let array_back_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let inhabited_alpha = Expr::app(inhabited_const.clone(), alpha.clone());
                    let arr_a = Expr::app(array_const.clone(), alpha.clone());
                    let (inst_id, inst) = b.fresh_local(inhabited_alpha.clone());
                    let (as_id, as_v) = b.fresh_local(arr_a.clone());
                    let array_get_bang =
                        Expr::const_(Name::from_string("Array.get!"), vec![level_u.clone()]);
                    let array_size_u =
                        Expr::const_(Name::from_string("Array.size"), vec![level_u.clone()]);
                    let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
                    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
                    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
                    let one = Expr::app(nat_succ, nat_zero);
                    let size_app = Expr::apps(array_size_u, [alpha.clone(), as_v.clone()]);
                    let idx = Expr::apps(nat_sub, [size_app, one]);
                    let body = Expr::apps(
                        array_get_bang,
                        [alpha.clone(), inst.clone(), as_v.clone(), idx],
                    );
                    let e = b.mk_lam(as_id, BinderInfo::Default, arr_a.clone(), body);
                    let e = b.mk_lam(
                        inst_id,
                        BinderInfo::InstImplicit,
                        inhabited_alpha.clone(),
                        e,
                    );
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Definition {
                    name: Name::from_string("Array.back"),
                    level_params: vec![u.clone()],
                    type_: array_back_type,
                    value: array_back_value,
                    is_reducible: true,
                })?;
            }
        } // end List.get!/Array.get! (List.getD + Inhabited.default availability guard)

        self.array_init = true;
        Ok(())
    }

    /// Check if Array has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_array` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_array(&self) -> bool {
        self.array_init
    }
}
