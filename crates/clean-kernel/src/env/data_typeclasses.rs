// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typeclass initialization for Environment
//!
//! This module contains:
//! - Inhabited typeclass and instances
//! - DecidableEq typeclass
//!
//! See also:
//! - `data_typeclasses_beq.rs` for BEq typeclass and instances
//! - `data_typeclasses_hashable.rs` for Hashable typeclass and instances

use super::algebra_uint_dec_eq_proof::WrapperCarrier;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// The wrapper carrier for a UInt-family width name. `UInt8/16/32/64` carry
/// `BitVec <width>` and `USize` carries `BitVec System.Platform.numBits`
/// (genuine v4.30 fidelity); every other wrapper (`Float`, `Char`) carries
/// `Nat`. The width is the OfNat-wrapped literal the oracle uses.
pub(crate) fn uint_wrapper_carrier(name: &str) -> WrapperCarrier {
    match name {
        "UInt8" => Environment::bitvec_carrier_width(8),
        "UInt16" => Environment::bitvec_carrier_width(16),
        "UInt32" => Environment::bitvec_carrier_width(32),
        "UInt64" => Environment::bitvec_carrier_width(64),
        "USize" => WrapperCarrier::BitVec(Expr::const_(
            Name::from_string("System.Platform.numBits"),
            vec![],
        )),
        _ => WrapperCarrier::Nat,
    }
}

impl Environment {
    /// Initialize the Inhabited typeclass
    ///
    /// Inhabited is a typeclass that provides a default value for a type:
    /// ```lean
    /// class Inhabited (α : Sort u) where
    ///   default : α
    /// ```
    ///
    /// This also adds basic instances for:
    /// - Inhabited Nat (default := 0)
    /// - Inhabited Bool (default := false)
    /// - Inhabited Unit (default := ())
    /// - Inhabited PUnit (default := PUnit.unit)
    /// - Inhabited (Option α) (default := none)
    /// - Inhabited (List α) (default := [])
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.inhabited_init == true`
    /// ENSURES: On success, required dependencies (`nat`, `bool`, `unit`, `punit`, `option`, `list`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_inhabited(&mut self) -> Result<(), EnvError> {
        if self.inhabited_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;
        self.init_bool()?;
        self.init_unit()?;
        self.init_option()?;
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());

        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));

        // Inhabited.mk : {α : Sort u} → α → Inhabited α
        let inhabited_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (x_id, _x) = b.fresh_local(alpha.clone());
            let r = Expr::app(
                Expr::const_(Name::from_string("Inhabited"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let r = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        let inhabited_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Inhabited"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    sort_u.clone(),
                    // Lean fidelity: `Inhabited (α : Sort u) : Sort (max 1 u)` —
                    // `max`, NOT `imax`. `imax 1 u` collapses to 0 at u=0, which is
                    // not provably nonzero, so the [R1] elim gate would flip
                    // Inhabited (single ctor with a non-Prop field `default : α`)
                    // to Prop-only elimination and strip `Inhabited.rec`'s fresh
                    // elim level. `max 1 u` is provably nonzero, preserving large
                    // elimination and the 2-level `Inhabited.rec@{elim, u}`.
                    Expr::from_kind(ExprKind::Sort(Level::max(
                        Level::succ(Level::zero()),
                        u_level.clone(),
                    ))),
                ),
                constructors: vec![Constructor {
                    name: Name::from_string("Inhabited.mk"),
                    type_: inhabited_mk_type,
                }],
            }],
        };

        self.add_inductive(inhabited_ind)?;

        // Register `Inhabited`'s structure field table (`{ default : α }`) so
        // `structure X extends Inhabited α` — the Mathlib base shape (`Unique
        // extends Inhabited`, and much of the hierarchy) — can find its subobject
        // field via `get_structure_field_names`. Without this, the surface
        // elaborator's `extends` path rejects `Inhabited` with `UnknownStruct`
        // even though it is a single-constructor structure, so those declarations
        // (and everything downstream) never elaborate. This mirrors what the
        // `.olean` import path does for imported structures
        // (`register_structure_fields_from_projections`); it is metadata only —
        // it records field names, changes no checking decision, and every
        // declaration built on `Inhabited` is still fully kernel-re-checked.
        self.register_structure_fields(
            Name::from_string("Inhabited"),
            vec![Name::from_string("default")],
        )?;

        let inhabited_const = |u: Level| Expr::const_(Name::from_string("Inhabited"), vec![u]);
        let inhabited_rec =
            |u1: Level, u2: Level| Expr::const_(Name::from_string("Inhabited.rec"), vec![u1, u2]);

        // Inhabited.default : {α : Sort u} → [inst : Inhabited α] → α
        let default_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(inhabited_const(u_level.clone()), alpha.clone()));
            let r = alpha.clone();
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(inhabited_const(u_level.clone()), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // default value: λ {α} [inst] => Inhabited.rec α motive minor inst
        let default_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(inhabited_const(u_level.clone()), alpha.clone()));

            // motive: λ (_ : Inhabited α) => α
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) =
                    c.fresh_local(Expr::app(inhabited_const(u_level.clone()), alpha.clone()));
                let r = alpha.clone();
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(inhabited_const(u_level.clone()), alpha.clone()),
                    r,
                );
                c.finish_child(r)
            };

            // minor: λ (x : α) => x
            let minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(alpha.clone());
                let r = x;
                let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            inhabited_rec(u_level.clone(), u_level.clone()),
                            alpha.clone(),
                        ),
                        motive,
                    ),
                    minor,
                ),
                inst,
            );
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(inhabited_const(u_level.clone()), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Inhabited.default"),
            level_params: vec![u.clone()],
            type_: default_type,
            value: default_value,
            is_reducible: true,
        })?;

        // Add instances

        // instInhabitedNat : Inhabited Nat := ⟨0⟩
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let inhabited_nat_type = Expr::app(
            inhabited_const(Level::succ(Level::zero())),
            Expr::const_(Name::from_string("Nat"), vec![]),
        );
        let inhabited_nat_value = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Inhabited.mk"),
                    vec![Level::succ(Level::zero())],
                ),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            nat_zero,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instInhabitedNat"),
            level_params: vec![],
            type_: inhabited_nat_type,
            value: inhabited_nat_value,
            is_reducible: true,
        })?;

        // instInhabitedBool : Inhabited Bool := ⟨false⟩
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let inhabited_bool_type = Expr::app(
            inhabited_const(Level::succ(Level::zero())),
            Expr::const_(Name::from_string("Bool"), vec![]),
        );
        let inhabited_bool_value = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Inhabited.mk"),
                    vec![Level::succ(Level::zero())],
                ),
                Expr::const_(Name::from_string("Bool"), vec![]),
            ),
            bool_false,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instInhabitedBool"),
            level_params: vec![],
            type_: inhabited_bool_type,
            value: inhabited_bool_value,
            is_reducible: true,
        })?;

        // instInhabitedUnit : Inhabited Unit := ⟨()⟩
        let unit_unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
        let inhabited_unit_type = Expr::app(
            inhabited_const(Level::succ(Level::zero())),
            Expr::const_(Name::from_string("Unit"), vec![]),
        );
        let inhabited_unit_value = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Inhabited.mk"),
                    vec![Level::succ(Level::zero())],
                ),
                Expr::const_(Name::from_string("Unit"), vec![]),
            ),
            unit_unit,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instInhabitedUnit"),
            level_params: vec![],
            type_: inhabited_unit_type,
            value: inhabited_unit_value,
            is_reducible: true,
        })?;

        // instInhabitedOption : {α : Type u} → Inhabited (Option α)
        // default is Option.none
        let option_const = |u: Level| Expr::const_(Name::from_string("Option"), vec![u]);
        let option_none = |u: Level| Expr::const_(Name::from_string("Option.none"), vec![u]);

        let type_su = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let inhabited_option_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_su.clone());
            let r = Expr::app(
                inhabited_const(Level::succ(u_level.clone())),
                Expr::app(option_const(u_level.clone()), alpha.clone()),
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_su.clone(), r);
            b.finish(r)
        };

        let inhabited_option_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_su.clone());
            let r = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Inhabited.mk"),
                        vec![Level::succ(u_level.clone())],
                    ),
                    Expr::app(option_const(u_level.clone()), alpha.clone()),
                ),
                Expr::app(option_none(u_level.clone()), alpha.clone()),
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_su.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instInhabitedOption"),
            level_params: vec![u.clone()],
            type_: inhabited_option_type,
            value: inhabited_option_value,
            is_reducible: true,
        })?;

        // instInhabitedList : {α : Type u} → Inhabited (List α)
        // default is List.nil
        let list_const = |u: Level| Expr::const_(Name::from_string("List"), vec![u]);
        let list_nil = |u: Level| Expr::const_(Name::from_string("List.nil"), vec![u]);

        let inhabited_list_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_su.clone());
            let r = Expr::app(
                inhabited_const(Level::succ(u_level.clone())),
                Expr::app(list_const(u_level.clone()), alpha.clone()),
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_su.clone(), r);
            b.finish(r)
        };

        let inhabited_list_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_su.clone());
            let r = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Inhabited.mk"),
                        vec![Level::succ(u_level.clone())],
                    ),
                    Expr::app(list_const(u_level.clone()), alpha.clone()),
                ),
                Expr::app(list_nil(u_level.clone()), alpha.clone()),
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_su.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instInhabitedList"),
            level_params: vec![u.clone()],
            type_: inhabited_list_type,
            value: inhabited_list_value,
            is_reducible: true,
        })?;

        // instInhabitedOrdering : Inhabited Ordering := ⟨Ordering.lt⟩
        // FIDELITY: Lean's `deriving Inhabited` picks the FIRST constructor, so
        // v4.30's `instInhabitedOrdering.default = Ordering.lt` (not `.eq`). The
        // olean twin delta-unfolds to `Inhabited.mk Ordering.lt`; a `.eq` seed is
        // a distinct constructor and correctly fails the value-defeq dedup
        // (census root: Init.Data.Ord.Basic).
        self.init_ordering()?;
        let ordering_lt = Expr::const_(Name::from_string("Ordering.lt"), vec![]);
        let inhabited_ordering_type = Expr::app(
            inhabited_const(Level::succ(Level::zero())),
            Expr::const_(Name::from_string("Ordering"), vec![]),
        );
        let inhabited_ordering_value = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Inhabited.mk"),
                    vec![Level::succ(Level::zero())],
                ),
                Expr::const_(Name::from_string("Ordering"), vec![]),
            ),
            ordering_lt,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instInhabitedOrdering"),
            level_params: vec![],
            type_: inhabited_ordering_type,
            value: inhabited_ordering_value,
            is_reducible: true,
        })?;

        // Register `Inhabited` as a typeclass and its prelude instances so
        // instance synthesis (`Inhabited.default`, `default`, and derived
        // `Inhabited` instances for user structures) can find them. Mirrors the
        // `init_beq` pattern: `init_inhabited` previously added the instance
        // *definitions* but never registered them with the class/instance
        // registry, so `resolve_instance (Inhabited T)` always failed and the
        // elaborator's InstanceTable (seeded from `env.classes()` /
        // `env.get_class_instances()`) was empty for `Inhabited`. Inhabited has
        // one parameter (α : Sort u) and no output parameters.
        self.register_class(KernelClassInfo {
            name: Name::from_string("Inhabited"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });
        for inst_name in [
            "instInhabitedNat",
            "instInhabitedBool",
            "instInhabitedUnit",
            "instInhabitedOption",
            "instInhabitedList",
            "instInhabitedOrdering",
        ] {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string(inst_name),
                class_name: Name::from_string("Inhabited"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        self.inhabited_init = true;
        Ok(())
    }

    /// Check if Inhabited typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_inhabited` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_inhabited(&self) -> bool {
        self.inhabited_init
    }

    /// Initialize DecidableEq typeclass
    ///
    /// abbrev DecidableEq (α : Sort u) := (a b : α) → Decidable (Eq a b)
    ///
    /// DecidableEq provides a decision procedure for equality.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.decidable_eq_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `decidable`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_decidable_eq(&mut self) -> Result<(), EnvError> {
        if self.decidable_eq_init {
            return Ok(());
        }

        // Initialize dependencies. `init_true_false` must precede
        // `init_decidable` so `Decidable.isFalse` carries the real `(p → False)`
        // negation type rather than the impredicative `∀ q, q` fallback — the
        // concrete `Nat.decEq` instance (below) discharges its `isFalse` branches
        // against the real `False`.
        self.init_eq()?;
        self.init_true_false()?;
        self.init_decidable()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));

        // DecidableEq : Sort u → Sort(max(u, 1))
        // DecidableEq α := (a b : α) → Decidable (Eq a b)
        // Since Decidable p : Type (Sort 1), the result lives in Sort(max(u, 1)).
        let decidable_const = Expr::const_(Name::from_string("Decidable"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![u_level.clone()]);

        // The type of DecidableEq: Sort u → Sort(max(u, 1)).
        // Decidable p : Type (Sort 1), so (a b : α) → Decidable (Eq a b)
        // lives in Sort(imax(u, imax(u, 1))) = Sort(max(u, 1)).
        let decidable_eq_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(sort_u.clone());
            let r = Expr::sort(Level::max(u_level.clone(), Level::succ(Level::zero())));
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // DecidableEq α := ∀ (a b : α), Decidable (Eq α a b)
        // Value: λ α => (a b : α) → Decidable (Eq α a b)
        let decidable_eq_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let (b_id2, b_var) = c.fresh_local(alpha.clone());
                let eq_a_b = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), a),
                    b_var,
                );
                let r = Expr::app(decidable_const.clone(), eq_a_b);
                let r = c.mk_pi(b_id2, BinderInfo::Default, alpha.clone(), r);
                let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), inner);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("DecidableEq"),
            level_params: vec![u.clone()],
            type_: decidable_eq_type.clone(),
            value: decidable_eq_value,
            is_reducible: true,
        })?;

        // decEq : {α : Sort u} → [DecidableEq α] → (a b : α) → Decidable (Eq a b)
        // This is just the identity function that extracts the DecidableEq instance
        let dec_eq_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let dec_eq_alpha = Expr::app(
                Expr::const_(Name::from_string("DecidableEq"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(dec_eq_alpha.clone());
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let (b_id2, b_var) = c.fresh_local(alpha.clone());
                let eq_a_b = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), a),
                    b_var,
                );
                let r = Expr::app(decidable_const.clone(), eq_a_b);
                let r = c.mk_pi(b_id2, BinderInfo::Default, alpha.clone(), r);
                let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, dec_eq_alpha, inner);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // decEq {α} [inst] a b := inst a b
        let dec_eq_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let dec_eq_alpha = Expr::app(
                Expr::const_(Name::from_string("DecidableEq"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(dec_eq_alpha.clone());
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let (b_id2, b_var) = c.fresh_local(alpha.clone());
                let r = Expr::app(Expr::app(inst.clone(), a), b_var);
                let r = c.mk_lam(b_id2, BinderInfo::Default, alpha.clone(), r);
                let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, dec_eq_alpha, inner);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("decEq"),
            level_params: vec![u.clone()],
            type_: dec_eq_type,
            value: dec_eq_value,
            is_reducible: true,
        })?;

        // Register `Decidable` as a resolvable class. Previously `Decidable`
        // carried no class registration, so the elaborator's `resolve_decidable`
        // (used by `if`/`decide` over a `Prop` condition) found no instance and
        // fell back to a synthetic `sorry`. Registering it lets concrete
        // decision procedures (below) resolve.
        self.register_class(KernelClassInfo {
            name: Name::from_string("Decidable"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Sound `Nat.decEq : (a b : Nat) → Decidable (Eq a b)` — a real kernel
        // term (NO sorry/axiom; see `algebra_nat_dec_eq_proof.rs`). Registered as
        // a `Decidable` instance: stripping its two explicit `Nat` binders leaves
        // `Decidable (@Eq Nat ?a ?b)`, which the resolver unifies against
        // `Decidable (@Eq Nat lhs rhs)` goals — making `if (a = b)` / `decide`
        // over `Nat` equalities elaborate without a `sorry`.
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Clean's `Nat.decEq`
        // overlay (and the concrete leaf decEq terms below that dispatch on it)
        // is WITHHELD — see `register_nat_dec_eq_proof` /
        // `register_nat_succ_inj_proof` for the full rationale. The genuine
        // Lean 4 `Init` `Nat.decEq` + `instDecidableEqNat` (and the genuine
        // `Int`/`Char`/`String`/`UInt`/`Float` decEq instances) come from the
        // import closure, so the `decide`/`if a=b` path is served by the real
        // constants. The generic `DecidableEq` class + `decEq` bridge below stay
        // registered in BOTH modes (they are non-divergent and the elaborator
        // needs them to resolve `Decidable (Eq T a b)`).
        if !self.suppress_lossy_structure_stubs {
            self.register_nat_dec_eq_proof()?;
            // Register with an explicit `value` of the bare `Nat.decEq` constant
            // (not `None`) so the elaborator's instance expression is `Nat.decEq`
            // — applied to the two operands it yields `Nat.decEq lhs rhs`. With
            // `value: None` the fallback inlines `Nat.decEq`'s entire recursive
            // lambda body at every use site, bloating elaborated `if (a = b)`
            // terms.
            let nat_dec_eq_ty = self
                .get_const(&Name::from_string("Nat.decEq"))
                .expect("register_nat_dec_eq_proof just registered Nat.decEq")
                .type_
                .clone();
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("Nat.decEq"),
                class_name: Name::from_string("Decidable"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: Some(nat_dec_eq_ty),
                value: Some(Expr::const_(Name::from_string("Nat.decEq"), vec![])),
            });
        }

        // GENERAL bridge: make `Decidable (Eq T a b)` resolvable for ANY type `T`
        // carrying a `DecidableEq T` instance — Nat below, plus every
        // `deriving DecidableEq` enum/struct. Two pieces:
        //
        //  (1) Register `DecidableEq` as a resolvable class. The derive handlers
        //      and the leaf below register instances under it, but without a class
        //      registration `resolve_instance` bailed before consulting them.
        //
        //  (2) Register the existing `decEq : {α} → [DecidableEq α] →
        //      (a b : α) → Decidable (Eq a b)` as a `Decidable`-class instance.
        //      Stripping its binders leaves `Decidable (Eq ?α ?a ?b)` with a
        //      *pending* `[DecidableEq ?α]`; unifying the goal pins `?α := T`, and
        //      the pending sub-goal resolves to the concrete `DecidableEq T`
        //      instance. So one bridge serves all decidable-equality types.
        //
        self.register_class(KernelClassInfo {
            name: Name::from_string("DecidableEq"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("decEq"),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // instDecidableEqNat : DecidableEq Nat := Nat.decEq — backs the bridge for
        // Nat. `DecidableEq.{1} Nat` reducibly unfolds to `(a b : Nat) → Decidable
        // (Eq a b)`, which is exactly `Nat.decEq`'s type, so this type-checks.
        //
        // IMPORT MODE: withheld with the `Nat.decEq` overlay above (its `value`
        // references the gated `Nat.decEq`); the genuine `Init` `instDecidableEqNat`
        // imports from the closure.
        if !self.suppress_lossy_structure_stubs {
            let dec_eq_nat_ty = Expr::app(
                Expr::const_(
                    Name::from_string("DecidableEq"),
                    vec![Level::succ(Level::zero())],
                ),
                Expr::const_(Name::from_string("Nat"), vec![]),
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instDecidableEqNat"),
                level_params: vec![],
                type_: dec_eq_nat_ty,
                value: Expr::const_(Name::from_string("Nat.decEq"), vec![]),
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instDecidableEqNat"),
                class_name: Name::from_string("DecidableEq"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // instDecidableEqBool : DecidableEq Bool := Bool.decEq — Bool-equality leaf
        // for the bridge (sound 2×2 `Bool.rec` term, `algebra_bool_dec_eq_proof.rs`).
        self.register_bool_dec_eq_proof()?;
        let dec_eq_bool_ty = Expr::app(
            Expr::const_(
                Name::from_string("DecidableEq"),
                vec![Level::succ(Level::zero())],
            ),
            Expr::const_(Name::from_string("Bool"), vec![]),
        );
        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableEqBool"),
            level_params: vec![],
            type_: dec_eq_bool_ty,
            value: Expr::const_(Name::from_string("Bool.decEq"), vec![]),
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDecidableEqBool"),
            class_name: Name::from_string("DecidableEq"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // instDecidableEqInt : DecidableEq Int := Int.decEq — Int-equality leaf
        // for the bridge. `Int` is the 2-constructor `ofNat`/`negSucc` inductive
        // (see `init_int`); `register_int_dec_eq_proof` builds an axiom-free,
        // sorry-free `Int.decEq : (a b : Int) → Decidable (Eq a b)` via a 2×2
        // `Int.rec`/`Int.rec` split dispatching on `Nat.decEq` of the carriers
        // (see `algebra_int_dec_eq_proof.rs`). Wiring the instance makes
        // `decide ((m : Int) = n)` resolve a real instance instead of the
        // synthetic `Decidable`-sorry fallback in `infer/elab_app.rs` — e.g.
        // trust-ir's `Value.eqBasic` `decide (w1 = w2 ∧ n1 = n2)` over `Int`
        // operands. Guarded on `Int` being present so a sparser env skips
        // cleanly. IMPORT MODE: withheld — `Int.decEq`'s body dispatches on the
        // gated `Nat.decEq` overlay (its 2×2 split decides the carriers via
        // `Nat.decEq`), so the genuine `Int.decEq`/`instDecidableEqInt` import
        // from the closure instead.
        if !self.suppress_lossy_structure_stubs
            && self.get_const(&Name::from_string("Int")).is_some()
        {
            self.register_int_dec_eq_proof()?;
            let dec_eq_int_ty = Expr::app(
                Expr::const_(
                    Name::from_string("DecidableEq"),
                    vec![Level::succ(Level::zero())],
                ),
                Expr::const_(Name::from_string("Int"), vec![]),
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instDecidableEqInt"),
                level_params: vec![],
                type_: dec_eq_int_ty,
                value: Expr::const_(Name::from_string("Int.decEq"), vec![]),
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instDecidableEqInt"),
                class_name: Name::from_string("DecidableEq"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // instDecidableEqChar : DecidableEq Char := Char.decEq.
        //
        // clean's `Char` is now the GENUINE v4.30 2-field structure
        // (`Char.mk (val : UInt32) (valid : val.isValidChar)`, `Char.val : Char →
        // UInt32`; carrier-parity design P2), so `register_char_dec_eq_proof`
        // builds an axiom-free, sorry-free `Char.decEq : (a b : Char) → Decidable
        // (Eq a b)` by `Char.rec`-destructuring both operands and dispatching on
        // `UInt32.decEq` of the underlying `val`s (isTrue lifted via `Eq.rec` +
        // proof irrelevance of the `valid` field, isFalse via `congrArg
        // Char.val`). Wiring the instance makes `decide ((c : Char) = d)` resolve
        // a real instance instead of the synthetic `Decidable`-sorry fallback.
        // Guarded on `Char` present so a sparser env skips cleanly. IMPORT MODE:
        // withheld — the genuine `Char.decEq`/`instDecidableEqChar` import from
        // the closure.
        if !self.suppress_lossy_structure_stubs
            && self.get_const(&Name::from_string("Char")).is_some()
        {
            self.register_char_dec_eq_proof()?;
            let dec_eq_char_ty = Expr::app(
                Expr::const_(
                    Name::from_string("DecidableEq"),
                    vec![Level::succ(Level::zero())],
                ),
                Expr::const_(Name::from_string("Char"), vec![]),
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instDecidableEqChar"),
                level_params: vec![],
                type_: dec_eq_char_ty,
                value: Expr::const_(Name::from_string("Char.decEq"), vec![]),
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instDecidableEqChar"),
                class_name: Name::from_string("DecidableEq"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // instDecidableEqString : DecidableEq String := String.decEq.
        //
        // `String.decEq : (a b : String) → Decidable (Eq a b)` is now a
        // CONSTRUCTIVE, axiom-free `Declaration::Definition` over the FAITHFUL
        // `String` carrier (`String.mk : List Char → String`, projection
        // `String.data`, recursor `String.rec`): see
        // `algebra_string_dec_eq_proof.rs`. It destructures `a`/`b` via
        // `String.rec` and dispatches on the (axiom-free, recursive)
        // `ListChar.decEq` of the underlying `List Char`s — `isTrue` lifts via
        // `congrArg String.mk`, `isFalse` refutes via `congrArg String.data`.
        // The former foundational representation axiom is RETIRED (census −1).
        // The native `String.decEq` reducer (`native_reducers.rs`) still fires on
        // equal string literals (Nat.decEq precedent — fast-path coexistence).
        //
        // `DecidableEq.{1} String` reducibly unfolds to
        // `(a b : String) → Decidable (Eq a b)`, which is exactly `String.decEq`'s
        // type, so `instDecidableEqString := String.decEq` type-checks. Guarded on
        // `String` being present so a sparser env skips cleanly. IMPORT MODE:
        // withheld — `String.decEq` dispatches on `ListChar.decEq` → `Char.decEq`
        // → the gated `Nat.decEq`; the genuine `String.decEq`/
        // `instDecidableEqString` import from the closure.
        if !self.suppress_lossy_structure_stubs
            && self.get_const(&Name::from_string("String")).is_some()
        {
            let string_c = Expr::const_(Name::from_string("String"), vec![]);
            // Build the constructive `String.decEq` Definition (idempotent).
            self.register_string_dec_eq_proof()?;
            let dec_eq_string_ty = Expr::app(
                Expr::const_(
                    Name::from_string("DecidableEq"),
                    vec![Level::succ(Level::zero())],
                ),
                string_c.clone(),
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instDecidableEqString"),
                level_params: vec![],
                type_: dec_eq_string_ty,
                value: Expr::const_(Name::from_string("String.decEq"), vec![]),
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instDecidableEqString"),
                class_name: Name::from_string("DecidableEq"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // DecidableEq leaves for the single-constructor `Nat`-wrapper types
        // (`UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize`/`Float`). Each is backed by a
        // real, axiom-free `<T>.decEq` term (see `algebra_uint_dec_eq_proof.rs`):
        // `<T>.rec`-destructure both operands, dispatch on `Nat.decEq` of the
        // underlying `.val`s, lift `isTrue` via `congrArg <T>.mk` and discharge
        // `isFalse` via `congrArg <T>.val`. Registering each `instDecidableEq<T>`
        // makes `if ((x : <T>) = y)` / `decide` resolve an instance (and, for
        // concrete literals, fire the sound native `<T>.decEq` reducer) instead of
        // emitting a synthetic `sorry`. The types are initialized earlier in
        // `init_prelude_extended` (`init_uint_types`/`init_usize`/`init_float`).
        //
        // IMPORT MODE: the whole loop is withheld — each `<T>.decEq` dispatches
        // on the gated `Nat.decEq` of the underlying `.val`s, and the genuine
        // `<T>.decEq`/`instDecidableEq<T>` import from the closure.
        for wrapper in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"] {
            // Only wire the instance when the underlying type is present in this
            // env (it always is under `with_prelude`, but `init_decidable_eq` may be
            // invoked on a sparser env — skip cleanly rather than fail).
            if self.suppress_lossy_structure_stubs
                || self.get_const(&Name::from_string(wrapper)).is_none()
            {
                continue;
            }
            // UInt8/16/32/64/USize now carry `Fin <T>.size` (Lean 4.8.0); Float
            // remains a `Nat` wrapper. Dispatch `<T>.decEq` on the matching carrier.
            self.register_wrapper_dec_eq_proof_carrier(wrapper, uint_wrapper_carrier(wrapper))?;
            let dec_eq_const = format!("{wrapper}.decEq");
            let inst_name = format!("instDecidableEq{wrapper}");
            // `DecidableEq.{1} <T>` reducibly unfolds to `(a b : <T>) → Decidable
            // (Eq a b)`, which is exactly `<T>.decEq`'s type, so this type-checks.
            let dec_eq_ty = Expr::app(
                Expr::const_(
                    Name::from_string("DecidableEq"),
                    vec![Level::succ(Level::zero())],
                ),
                Expr::const_(Name::from_string(wrapper), vec![]),
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_name),
                level_params: vec![],
                type_: dec_eq_ty,
                value: Expr::const_(Name::from_string(&dec_eq_const), vec![]),
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string(&inst_name),
                class_name: Name::from_string("DecidableEq"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // `instDecidableNot : {p} → [Decidable p] → Decidable (Not p)` — so
        // `if (a ≠ b)` / `decide (¬p)` resolve (and reduce soundly: the term
        // reuses the inner decision's real proof, never a sorry).
        self.register_decidable_not_instance()?;

        // `instDecidableAnd`/`instDecidableOr` — the compound combinators so
        // `if (p ∧ q)` / `if (p ∨ q)` resolve a `Decidable` instance from the
        // sub-`Decidable`s rather than emitting a synthetic sorry. Both terms
        // are real `Decidable.rec`-based proofs (no axiom, no sorry) that reuse
        // the inner decisions' witnesses, mirroring the native reducers in
        // `native_reducers_decidable_ext.rs`.
        self.register_decidable_and_instance()?;
        self.register_decidable_or_instance()?;

        // `Nat.ble`↔`Nat.le` bridge lemmas — back the SOUND `Nat.le`/`Nat.lt`
        // native-decide reducers (replacing `mk_dec_is_true_sorry`/`sorryAx`).
        self.register_nat_ble_le_lemmas()?;

        // `Nat.beq`→`=` soundness (`Nat.eq_of_beq_eq_true : ∀ a b, Nat.beq a b =
        // true → a = b`). Companion to the `ble`/`le` bridge above: it backs the
        // sound `DecidableEq Nat` decision AND is the soundness lemma the Trust
        // spec-elab equality certified monitor cites (a `== ` ensures-clause
        // monitor emits `Nat.beq`, certified `monitor = true → a = b`). Already a
        // kernel-checked, axiom-free constructive theorem; idempotent. Registered
        // here so it is present in the default prelude by construction rather than
        // only when a boolean-analysis proof pulls it in. Import mode withholds
        // `Nat.beq`, so it must withhold this dependent theorem as well.
        if !self.suppress_lossy_structure_stubs {
            self.register_nat_eq_of_beq_eq_true()?;
        }

        // Parametric `instBEqOfDecidableEq : [DecidableEq α] → BEq α` bridge, so
        // `==` (BEq.beq) resolves on any `deriving DecidableEq` type that does
        // not also `deriving BEq` (e.g. trust-ir's `ValueId`/`AllocId`). Runs
        // last: it needs `BEq`/`BEq.mk` (from `init_beq`, which `with_prelude`
        // runs before this) plus `Eq`/`Decidable`/`decide`/`DecidableEq`/`decEq`
        // (registered above). Guarded inside, so a sparser env skips cleanly.
        self.init_beq_of_decidable_eq()?;

        self.decidable_eq_init = true;
        Ok(())
    }

    /// Build + register the sound `instDecidableNot` and make it a resolvable
    /// `Decidable` instance.
    ///
    /// ```text
    /// instDecidableNot {p : Prop} [inst : Decidable p] : Decidable (Not p) :=
    ///   @Decidable.rec p (fun _ => Decidable (Not p))
    ///     (fun (h : ¬p) => Decidable.isTrue  (Not p) h)                 -- isFalse minor
    ///     (fun (h : p)  => Decidable.isFalse (Not p) (fun hnp => hnp h)) -- isTrue minor
    ///     inst
    /// ```
    /// No `sorry`, no axiom — reuses the underlying decision's witness.
    fn register_decidable_not_instance(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("instDecidableNot"))
            .is_some()
        {
            return Ok(());
        }
        self.init_true_false()?; // `Not`/`False`

        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(
            Name::from_string("Decidable.rec"),
            vec![Level::succ(Level::zero())],
        );
        let dec_of = |q: Expr| Expr::app(dec.clone(), q);
        let not_of = |q: Expr| Expr::app(not_c.clone(), q);

        // ----- type: {p : Prop} → [inst : Decidable p] → Decidable (Not p) -----
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (inst_id, _inst) = b.fresh_local(dec_of(p.clone()));
            let concl = dec_of(not_of(p.clone()));
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, dec_of(p.clone()), concl);
            let e = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(e)
        };

        // ----- value -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (inst_id, inst) = b.fresh_local(dec_of(p.clone()));

            // motive : fun (_ : Decidable p) => Decidable (Not p)
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (d_id, _d) = c.fresh_local(dec_of(p.clone()));
                c.finish_child(c.mk_lam(
                    d_id,
                    BinderInfo::Default,
                    dec_of(p.clone()),
                    dec_of(not_of(p.clone())),
                ))
            };
            // ¬p as `p → False`
            let neg_p = Expr::pi(BinderInfo::Default, p.clone(), false_c.clone());
            // isFalse minor: fun (h : ¬p) => @Decidable.isTrue (Not p) h
            let is_false_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(neg_p.clone());
                let body = Expr::apps(is_true.clone(), [not_of(p.clone()), h]);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, neg_p.clone(), body))
            };
            // isTrue minor: fun (h : p) => @Decidable.isFalse (Not p) (fun (hnp : Not p) => hnp h)
            let is_true_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(p.clone());
                let disproof = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hnp_id, hnp) = d.fresh_local(not_of(p.clone()));
                    let body = Expr::app(hnp, h.clone());
                    d.finish_child(d.mk_lam(hnp_id, BinderInfo::Default, not_of(p.clone()), body))
                };
                let body = Expr::apps(is_false.clone(), [not_of(p.clone()), disproof]);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, p.clone(), body))
            };

            let rec_app = Expr::apps(
                dec_rec.clone(),
                [p.clone(), motive, is_false_min, is_true_min, inst.clone()],
            );
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                dec_of(p.clone()),
                rec_app,
            );
            let e = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableNot"),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDecidableNot"),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Build + register the sound `instDecidableAnd` and make it a resolvable
    /// `Decidable` instance.
    ///
    /// ```text
    /// instDecidableAnd {p q : Prop} [dp : Decidable p] [dq : Decidable q]
    ///     : Decidable (And p q) :=
    ///   @Decidable.rec p (fun _ => Decidable (And p q))
    ///     -- dp = isFalse (hnp : ¬p):  And p q is false (its left fails)
    ///     (fun (hnp : ¬p) =>
    ///        @Decidable.isFalse (And p q) (fun (h : And p q) => hnp (And.left p q h)))
    ///     -- dp = isTrue (hp : p):  recurse on dq
    ///     (fun (hp : p) =>
    ///        @Decidable.rec q (fun _ => Decidable (And p q))
    ///          (fun (hnq : ¬q) =>
    ///             @Decidable.isFalse (And p q) (fun (h : And p q) => hnq (And.right p q h)))
    ///          (fun (hq : q) =>
    ///             @Decidable.isTrue (And p q) (And.intro p q hp hq))
    ///          dq)
    ///     dp
    /// ```
    /// No `sorry`, no axiom — reuses the underlying decisions' witnesses.
    fn register_decidable_and_instance(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("instDecidableAnd"))
            .is_some()
        {
            return Ok(());
        }
        self.init_and()?; // `And`/`And.intro`/`And.left`/`And.right`
        self.init_true_false()?; // `Not`/`False`

        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let and_c = Expr::const_(Name::from_string("And"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        // `Decidable (And p q) : Type`, so `Decidable.rec`'s motive returns into
        // `Sort 1` — its only level argument is `Succ Zero` (as in the Not term).
        let dec_rec = Expr::const_(
            Name::from_string("Decidable.rec"),
            vec![Level::succ(Level::zero())],
        );
        let dec_of = |q: Expr| Expr::app(dec.clone(), q);
        let and_of = |a: Expr, b: Expr| Expr::apps(and_c.clone(), [a, b]);

        // ----- type: {p q} → [Decidable p] → [Decidable q] → Decidable (And p q) -----
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (q_id, q) = b.fresh_local(prop.clone());
            let (dp_id, _dp) = b.fresh_local(dec_of(p.clone()));
            let (dq_id, _dq) = b.fresh_local(dec_of(q.clone()));
            let concl = dec_of(and_of(p.clone(), q.clone()));
            let e = b.mk_pi(dq_id, BinderInfo::InstImplicit, dec_of(q.clone()), concl);
            let e = b.mk_pi(dp_id, BinderInfo::InstImplicit, dec_of(p.clone()), e);
            let e = b.mk_pi(q_id, BinderInfo::Implicit, prop.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(e)
        };

        // ----- value -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (q_id, q) = b.fresh_local(prop.clone());
            let (dp_id, dp) = b.fresh_local(dec_of(p.clone()));
            let (dq_id, dq) = b.fresh_local(dec_of(q.clone()));

            let and_pq = and_of(p.clone(), q.clone());
            let neg_p = Expr::pi(BinderInfo::Default, p.clone(), false_c.clone());
            let neg_q = Expr::pi(BinderInfo::Default, q.clone(), false_c.clone());

            // motive : fun (_ : Decidable p) => Decidable (And p q)  [also reused for q]
            let mk_motive = |inner_ty: Expr, b: &EnvDeclBuilder| {
                let mut c = EnvDeclBuilder::child_of(b);
                let (d_id, _d) = c.fresh_local(inner_ty.clone());
                c.finish_child(c.mk_lam(
                    d_id,
                    BinderInfo::Default,
                    inner_ty,
                    dec_of(and_pq.clone()),
                ))
            };

            // dp = isFalse minor: fun (hnp : ¬p) =>
            //   @Decidable.isFalse (And p q) (fun (h : And p q) => hnp (And.left p q h))
            let dp_is_false_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hnp_id, hnp) = c.fresh_local(neg_p.clone());
                let disproof = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (h_id, h) = d.fresh_local(and_pq.clone());
                    let left = Expr::apps(and_left.clone(), [p.clone(), q.clone(), h]);
                    let body = Expr::app(hnp.clone(), left);
                    d.finish_child(d.mk_lam(h_id, BinderInfo::Default, and_pq.clone(), body))
                };
                let body = Expr::apps(is_false.clone(), [and_pq.clone(), disproof]);
                c.finish_child(c.mk_lam(hnp_id, BinderInfo::Default, neg_p.clone(), body))
            };

            // dp = isTrue minor: fun (hp : p) => @Decidable.rec q motive_q (…) (…) dq
            let dp_is_true_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hp_id, hp) = c.fresh_local(p.clone());

                // dq = isFalse minor: fun (hnq : ¬q) =>
                //   @Decidable.isFalse (And p q) (fun (h : And p q) => hnq (And.right p q h))
                let dq_is_false_min = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hnq_id, hnq) = d.fresh_local(neg_q.clone());
                    let disproof = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (h_id, h) = e.fresh_local(and_pq.clone());
                        let right = Expr::apps(and_right.clone(), [p.clone(), q.clone(), h]);
                        let body = Expr::app(hnq.clone(), right);
                        e.finish_child(e.mk_lam(h_id, BinderInfo::Default, and_pq.clone(), body))
                    };
                    let body = Expr::apps(is_false.clone(), [and_pq.clone(), disproof]);
                    d.finish_child(d.mk_lam(hnq_id, BinderInfo::Default, neg_q.clone(), body))
                };

                // dq = isTrue minor: fun (hq : q) =>
                //   @Decidable.isTrue (And p q) (And.intro p q hp hq)
                let dq_is_true_min = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hq_id, hq) = d.fresh_local(q.clone());
                    let pf = Expr::apps(and_intro.clone(), [p.clone(), q.clone(), hp.clone(), hq]);
                    let body = Expr::apps(is_true.clone(), [and_pq.clone(), pf]);
                    d.finish_child(d.mk_lam(hq_id, BinderInfo::Default, q.clone(), body))
                };

                let inner_rec = Expr::apps(
                    dec_rec.clone(),
                    [
                        q.clone(),
                        mk_motive(dec_of(q.clone()), &c),
                        dq_is_false_min,
                        dq_is_true_min,
                        dq.clone(),
                    ],
                );
                c.finish_child(c.mk_lam(hp_id, BinderInfo::Default, p.clone(), inner_rec))
            };

            let rec_app = Expr::apps(
                dec_rec.clone(),
                [
                    p.clone(),
                    mk_motive(dec_of(p.clone()), &b),
                    dp_is_false_min,
                    dp_is_true_min,
                    dp.clone(),
                ],
            );
            let e = b.mk_lam(dq_id, BinderInfo::InstImplicit, dec_of(q.clone()), rec_app);
            let e = b.mk_lam(dp_id, BinderInfo::InstImplicit, dec_of(p.clone()), e);
            let e = b.mk_lam(q_id, BinderInfo::Implicit, prop.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableAnd"),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDecidableAnd"),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Build + register the sound `instDecidableOr` and make it a resolvable
    /// `Decidable` instance.
    ///
    /// ```text
    /// instDecidableOr {p q : Prop} [dp : Decidable p] [dq : Decidable q]
    ///     : Decidable (Or p q) :=
    ///   @Decidable.rec p (fun _ => Decidable (Or p q))
    ///     -- dp = isFalse (hnp : ¬p):  recurse on dq
    ///     (fun (hnp : ¬p) =>
    ///        @Decidable.rec q (fun _ => Decidable (Or p q))
    ///          (fun (hnq : ¬q) =>
    ///             @Decidable.isFalse (Or p q)
    ///               (fun (h : Or p q) => @Or.rec p q (fun _ => False) hnp hnq h))
    ///          (fun (hq : q) => @Decidable.isTrue (Or p q) (Or.inr p q hq))
    ///          dq)
    ///     -- dp = isTrue (hp : p):  Or holds via the left injection
    ///     (fun (hp : p) => @Decidable.isTrue (Or p q) (Or.inl p q hp))
    ///     dp
    /// ```
    /// No `sorry`, no axiom — reuses the underlying decisions' witnesses.
    fn register_decidable_or_instance(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("instDecidableOr"))
            .is_some()
        {
            return Ok(());
        }
        self.init_or()?; // `Or`/`Or.inl`/`Or.inr`/`Or.rec`
        self.init_true_false()?; // `Not`/`False`

        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let or_c = Expr::const_(Name::from_string("Or"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let or_inl = Expr::const_(Name::from_string("Or.inl"), vec![]);
        let or_inr = Expr::const_(Name::from_string("Or.inr"), vec![]);
        // `Or` lives in `Prop`, so its recursor is the large-elimination-free
        // `Prop` recursor: it carries NO universe level parameter (motive eliminates
        // into `False : Prop`).
        let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
        let dec_rec = Expr::const_(
            Name::from_string("Decidable.rec"),
            vec![Level::succ(Level::zero())],
        );
        let dec_of = |q: Expr| Expr::app(dec.clone(), q);
        let or_of = |a: Expr, b: Expr| Expr::apps(or_c.clone(), [a, b]);

        // ----- type: {p q} → [Decidable p] → [Decidable q] → Decidable (Or p q) -----
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (q_id, q) = b.fresh_local(prop.clone());
            let (dp_id, _dp) = b.fresh_local(dec_of(p.clone()));
            let (dq_id, _dq) = b.fresh_local(dec_of(q.clone()));
            let concl = dec_of(or_of(p.clone(), q.clone()));
            let e = b.mk_pi(dq_id, BinderInfo::InstImplicit, dec_of(q.clone()), concl);
            let e = b.mk_pi(dp_id, BinderInfo::InstImplicit, dec_of(p.clone()), e);
            let e = b.mk_pi(q_id, BinderInfo::Implicit, prop.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(e)
        };

        // ----- value -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (q_id, q) = b.fresh_local(prop.clone());
            let (dp_id, dp) = b.fresh_local(dec_of(p.clone()));
            let (dq_id, dq) = b.fresh_local(dec_of(q.clone()));

            let or_pq = or_of(p.clone(), q.clone());
            let neg_p = Expr::pi(BinderInfo::Default, p.clone(), false_c.clone());
            let neg_q = Expr::pi(BinderInfo::Default, q.clone(), false_c.clone());

            let mk_motive = |inner_ty: Expr, b: &EnvDeclBuilder| {
                let mut c = EnvDeclBuilder::child_of(b);
                let (d_id, _d) = c.fresh_local(inner_ty.clone());
                c.finish_child(c.mk_lam(d_id, BinderInfo::Default, inner_ty, dec_of(or_pq.clone())))
            };

            // dp = isFalse minor: fun (hnp : ¬p) => @Decidable.rec q motive_q (…) (…) dq
            let dp_is_false_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hnp_id, hnp) = c.fresh_local(neg_p.clone());

                // dq = isFalse minor: fun (hnq : ¬q) =>
                //   @Decidable.isFalse (Or p q)
                //     (fun (h : Or p q) => @Or.rec p q (fun _ => False) hnp hnq h)
                let dq_is_false_min = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hnq_id, hnq) = d.fresh_local(neg_q.clone());
                    let disproof = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (h_id, h) = e.fresh_local(or_pq.clone());
                        // @Or.rec p q (fun _ : Or p q => False) hnp hnq h : False
                        let or_motive = {
                            let mut f = EnvDeclBuilder::child_of(&e);
                            let (m_id, _m) = f.fresh_local(or_pq.clone());
                            f.finish_child(f.mk_lam(
                                m_id,
                                BinderInfo::Default,
                                or_pq.clone(),
                                false_c.clone(),
                            ))
                        };
                        let body = Expr::apps(
                            or_rec.clone(),
                            [p.clone(), q.clone(), or_motive, hnp.clone(), hnq.clone(), h],
                        );
                        e.finish_child(e.mk_lam(h_id, BinderInfo::Default, or_pq.clone(), body))
                    };
                    let body = Expr::apps(is_false.clone(), [or_pq.clone(), disproof]);
                    d.finish_child(d.mk_lam(hnq_id, BinderInfo::Default, neg_q.clone(), body))
                };

                // dq = isTrue minor: fun (hq : q) =>
                //   @Decidable.isTrue (Or p q) (Or.inr p q hq)
                let dq_is_true_min = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hq_id, hq) = d.fresh_local(q.clone());
                    let pf = Expr::apps(or_inr.clone(), [p.clone(), q.clone(), hq]);
                    let body = Expr::apps(is_true.clone(), [or_pq.clone(), pf]);
                    d.finish_child(d.mk_lam(hq_id, BinderInfo::Default, q.clone(), body))
                };

                let inner_rec = Expr::apps(
                    dec_rec.clone(),
                    [
                        q.clone(),
                        mk_motive(dec_of(q.clone()), &c),
                        dq_is_false_min,
                        dq_is_true_min,
                        dq.clone(),
                    ],
                );
                c.finish_child(c.mk_lam(hnp_id, BinderInfo::Default, neg_p.clone(), inner_rec))
            };

            // dp = isTrue minor: fun (hp : p) =>
            //   @Decidable.isTrue (Or p q) (Or.inl p q hp)
            let dp_is_true_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hp_id, hp) = c.fresh_local(p.clone());
                let pf = Expr::apps(or_inl.clone(), [p.clone(), q.clone(), hp]);
                let body = Expr::apps(is_true.clone(), [or_pq.clone(), pf]);
                c.finish_child(c.mk_lam(hp_id, BinderInfo::Default, p.clone(), body))
            };

            let rec_app = Expr::apps(
                dec_rec.clone(),
                [
                    p.clone(),
                    mk_motive(dec_of(p.clone()), &b),
                    dp_is_false_min,
                    dp_is_true_min,
                    dp.clone(),
                ],
            );
            let e = b.mk_lam(dq_id, BinderInfo::InstImplicit, dec_of(q.clone()), rec_app);
            let e = b.mk_lam(dp_id, BinderInfo::InstImplicit, dec_of(p.clone()), e);
            let e = b.mk_lam(q_id, BinderInfo::Implicit, prop.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDecidableOr"),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDecidableOr"),
            class_name: Name::from_string("Decidable"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Check if DecidableEq typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_decidable_eq` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_decidable_eq(&self) -> bool {
        self.decidable_eq_init
    }
}
