// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algebraic substructure and miscellaneous type initialization for Environment
//!
//! This module contains:
//! - Subgroup, Subring, Subfield, Submonoid
//! - Fact, Odd, Nat.card
//! - RingHom, IsEmpty, Finite

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Subgroup structure and related declarations
    ///
    /// Subgroup G is a structure containing:
    /// - carrier : Set G (the underlying set)
    /// - one_mem' : 1 ∈ carrier
    /// - mul_mem' : ∀ a b, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
    /// - inv_mem' : ∀ a, a ∈ carrier → a⁻¹ ∈ carrier
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.subgroup_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_subgroup(&mut self) -> Result<(), EnvError> {
        if self.subgroup_init {
            return Ok(());
        }

        self.init_group()?;
        self.init_set_theory()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Add Subgroup axiom stubs
        for name in &[
            // Core Subgroup structure
            "Subgroup",
            "Subgroup.carrier",
            "Subgroup.one_mem'",
            "Subgroup.mul_mem'",
            "Subgroup.inv_mem'",
            // Subgroup operations
            "Subgroup.mk",
            "Subgroup.toSubmonoid",
            "Subgroup.copy",
            // Subgroup properties
            "Subgroup.Normal",
            "Subgroup.normal",
            "Subgroup.FiniteIndex",
            "Subgroup.index",
            "Subgroup.relindex",
            // Subgroup lattice operations
            "Subgroup.sup",
            "Subgroup.inf",
            "Subgroup.top",
            "Subgroup.bot",
            "Subgroup.closure",
            "Subgroup.normalClosure",
            // Complement and cosets
            "Subgroup.IsComplement",
            "Subgroup.LeftCoset",
            "Subgroup.RightCoset",
            // IsSimpleGroup typeclass
            "IsSimpleGroup",
            // Min/Max properties
            "IsMin",
            "IsMax",
            // ncard (cardinality for Set with Nat result)
            "Set.ncard",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.subgroup_init = true;
        Ok(())
    }

    /// Check if Subgroup has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.subgroup_init == true`
    pub(crate) fn has_subgroup(&self) -> bool {
        self.subgroup_init
    }

    /// Initialize Subring structure and related declarations
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.subring_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_subring(&mut self) -> Result<(), EnvError> {
        if self.subring_init {
            return Ok(());
        }

        self.init_ring()?;
        self.init_set_theory()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        for name in &[
            "Subring",
            "Subring.carrier",
            "Subring.zero_mem'",
            "Subring.one_mem'",
            "Subring.add_mem'",
            "Subring.mul_mem'",
            "Subring.neg_mem'",
            "Subring.mk",
            "Subring.toSubsemiring",
            "Subring.closure",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.subring_init = true;
        Ok(())
    }

    /// Check if Subring has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.subring_init == true`
    pub(crate) fn has_subring(&self) -> bool {
        self.subring_init
    }

    /// Initialize Subfield structure and related declarations
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.subfield_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_subfield(&mut self) -> Result<(), EnvError> {
        if self.subfield_init {
            return Ok(());
        }

        self.init_field()?;
        self.init_set_theory()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        for name in &[
            "Subfield",
            "Subfield.carrier",
            "Subfield.zero_mem'",
            "Subfield.one_mem'",
            "Subfield.add_mem'",
            "Subfield.mul_mem'",
            "Subfield.neg_mem'",
            "Subfield.inv_mem'",
            "Subfield.mk",
            "Subfield.toSubring",
            "Subfield.closure",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.subfield_init = true;
        Ok(())
    }

    /// Check if Subfield has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.subfield_init == true`
    pub(crate) fn has_subfield(&self) -> bool {
        self.subfield_init
    }

    /// Initialize Submonoid structure
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.submonoid_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_submonoid(&mut self) -> Result<(), EnvError> {
        if self.submonoid_init {
            return Ok(());
        }

        self.init_monoid()?;
        self.init_set_theory()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        for name in &[
            "Submonoid",
            "Submonoid.carrier",
            "Submonoid.one_mem'",
            "Submonoid.mul_mem'",
            "Submonoid.mk",
            "Submonoid.closure",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.submonoid_init = true;
        Ok(())
    }

    /// Check if Submonoid has been initialized.
    pub(crate) fn has_submonoid(&self) -> bool {
        self.submonoid_init
    }

    /// Initialize Fact typeclass (for registering facts as instances)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.fact_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_fact(&mut self) -> Result<(), EnvError> {
        if self.fact_init {
            return Ok(());
        }

        let prop = Expr::sort(Level::zero());
        let fact = Expr::const_(Name::from_string("Fact"), vec![]);

        // Fact : Prop → Prop (typeclass for carrying propositions)
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Fact"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
        })?;

        // Fact.out : {p : Prop} → [Fact p] → p
        let fact_out_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p_var) = b.fresh_local(prop.clone());
            let fact_p = Expr::app(fact.clone(), p_var.clone());
            let (inst_id, _) = b.fresh_local(fact_p.clone());

            let result = p_var;
            let result = b.mk_pi(inst_id, BinderInfo::InstImplicit, fact_p, result);
            let result = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), result);
            b.finish(result)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Fact.out"),
            level_params: vec![],
            type_: fact_out_type,
        })?;

        // Fact.mk : {p : Prop} → p → Fact p
        let fact_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p_var) = b.fresh_local(prop.clone());
            let (proof_id, _) = b.fresh_local(p_var.clone());

            let result = Expr::app(fact.clone(), p_var.clone());
            let result = b.mk_pi(proof_id, BinderInfo::Default, p_var, result);
            let result = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), result);
            b.finish(result)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Fact.mk"),
            level_params: vec![],
            type_: fact_mk_type,
        })?;

        self.fact_init = true;
        Ok(())
    }

    /// Check if Fact has been initialized.
    pub(crate) fn has_fact(&self) -> bool {
        self.fact_init
    }

    /// Initialize Odd predicate
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.odd_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_odd(&mut self) -> Result<(), EnvError> {
        if self.odd_init {
            return Ok(());
        }

        self.init_nat()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Odd : Nat → Prop
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Odd"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::from_kind(ExprKind::Sort(Level::zero())),
            ),
        })?;

        // Nat.odd_iff : Odd n ↔ n % 2 = 1
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.odd_iff"),
            level_params: vec![u.clone()],
            type_: type_u.clone(),
        })?;

        self.odd_init = true;
        Ok(())
    }

    /// Check if Odd has been initialized.
    pub(crate) fn has_odd(&self) -> bool {
        self.odd_init
    }

    /// Initialize Nat.card (cardinality for finite types)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_card_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_nat_card(&mut self) -> Result<(), EnvError> {
        if self.nat_card_init {
            return Ok(());
        }

        self.init_nat()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Nat.card : Type* → Nat
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.card"),
            level_params: vec![u.clone()],
            type_: Expr::pi(
                BinderInfo::Default,
                type_u.clone(),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
        })?;

        // Nat.Primes : Set Nat (= Nat → Prop, no universe params)
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Primes"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::sort(Level::zero()),
            ),
        })?;

        self.nat_card_init = true;
        Ok(())
    }

    /// Check if Nat.card has been initialized.
    pub(crate) fn has_nat_card(&self) -> bool {
        self.nat_card_init
    }

    /// Initialize RingHom structure
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ring_hom_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ring_hom(&mut self) -> Result<(), EnvError> {
        if self.ring_hom_init {
            return Ok(());
        }

        self.init_ring()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        for name in &[
            "RingHom",
            "RingHom.toFun",
            "RingHom.map_one'",
            "RingHom.map_mul'",
            "RingHom.map_add'",
            "RingHom.map_zero'",
            "RingHom.mk",
            "RingHom.id",
            "RingHom.comp",
            "RingHom.ker",
            "RingHom.range",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone(), v.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.ring_hom_init = true;
        Ok(())
    }

    /// Check if RingHom has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.ring_hom_init == true`
    pub(crate) fn has_ring_hom(&self) -> bool {
        self.ring_hom_init
    }

    /// Initialize IsEmpty typeclass
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.is_empty_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_is_empty(&mut self) -> Result<(), EnvError> {
        if self.is_empty_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // IsEmpty : Sort u → Prop
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsEmpty"),
            level_params: vec![u.clone()],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(u_level.clone())),
                Expr::from_kind(ExprKind::Sort(Level::zero())),
            ),
        })?;

        // IsEmpty.false : {α : Sort u} → [IsEmpty α] → α → False
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsEmpty.false"),
            level_params: vec![u.clone()],
            type_: type_u.clone(),
        })?;

        self.is_empty_init = true;
        Ok(())
    }

    /// Check if IsEmpty has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.is_empty_init == true`
    pub(crate) fn has_is_empty(&self) -> bool {
        self.is_empty_init
    }

    /// Initialize Finite typeclass and related declarations
    /// This is idempotent and checks if declarations already exist
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.finite_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_finite(&mut self) -> Result<(), EnvError> {
        if self.finite_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // WS17: the hand-rolled `Finite` stub seeded the class with the WRONG
        // argument type. Genuine Lean `class Finite (α : Sort*) : Prop` is
        // `Finite.{u} : Sort u → Prop` (domain `Sort u`), but the stub used
        // `type_u = Sort (u+1) = Type u` as the domain — a spurious `Succ`. For a
        // `Type`-valued carrier (e.g. `Ideal.{u} a _ : Type u = Sort (u+1)`),
        // `Ideal.instFinite` applies `Finite.{Succ u_5}`, whose stub domain is
        // `Sort (u_5+2)`, while the carrier is `Sort (u_5+1)`; the type's own
        // `infer_sort` then raises `TypeMismatch { expected: Sort(Succ(Succ u_5)),
        // inferred: Sort(Succ u_5) }`. Registered unconditionally, the ill-formed
        // stub also shadows the genuine olean `Finite` (dedup-by-name,
        // registered-first wins). Gate the stub behind
        // `suppress_lossy_structure_stubs` (mirrors `Trans`/`Preorder`/`Semigroup`)
        // so in import-verification mode the genuine, correctly-universed Mathlib
        // `Finite` registers through the checked import path. No TCB change — this
        // removes a wrong stub rather than adding a term; the kernel now accepts
        // the faithful olean object it could not before.
        if !self.suppress_lossy_structure_stubs {
            // Only add Finite if not already defined (e.g., by init_module_algebra_all)
            self.add_init_axiom_if_absent("Finite", std::slice::from_ref(&u), || {
                Expr::pi(
                    BinderInfo::Default,
                    type_u.clone(),
                    Expr::from_kind(ExprKind::Sort(Level::zero())),
                )
            })?;
        }

        // .Finite namespace (for Set.Finite, Module.Finite, etc.)
        self.add_init_axiom_if_absent(".Finite", std::slice::from_ref(&u), || type_u.clone())?;

        // .FiniteType (for Algebra.FiniteType, etc.)
        self.add_init_axiom_if_absent(".FiniteType", std::slice::from_ref(&u), || type_u.clone())?;

        self.finite_init = true;
        Ok(())
    }

    /// Check if Finite has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.finite_init == true`
    pub(crate) fn has_finite(&self) -> bool {
        self.finite_init
    }
}
