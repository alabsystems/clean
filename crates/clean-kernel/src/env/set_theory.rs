// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Set theory structures for Environment
//!
//! This module provides axioms and structures for axiomatic set theory:
//! - Cardinal numbers and cardinal arithmetic
//! - Ordinal numbers and transfinite operations
//! - Well-orderings and well-founded relations
//! - Zorn's lemma and equivalents (axiom of choice)
//! - Transfinite induction and recursion
//! - Continuum hypothesis and large cardinals
//! - Models of set theory (ZFC, NBG, etc.)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Set Theory module
    ///
    /// Set theory provides the foundational framework for all of mathematics.
    /// This module formalizes cardinal and ordinal numbers, well-orderings,
    /// and the axioms governing infinite sets.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.set_theory_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_set_theory(&mut self) -> Result<(), EnvError> {
        if self.set_theory_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Set theory constants
        for name in &[
            // ================================================================
            // Ordinal numbers - basics
            // ================================================================
            "SetTheory.Ordinal",       // type of ordinals
            "SetTheory.OrdinalZero",   // zero ordinal (empty set)
            "SetTheory.OrdinalSucc",   // successor ordinal
            "SetTheory.OrdinalLimit",  // limit ordinal predicate
            "SetTheory.OrdinalIsSucc", // is a successor ordinal
            "SetTheory.OrdinalLt",     // ordinal less than (<)
            "SetTheory.OrdinalLe",     // ordinal less or equal (≤)
            "SetTheory.Mathverse",     // first infinite ordinal ω
            "SetTheory.MathverseOne",  // first uncountable ordinal ω₁
            "SetTheory.Epsilon0",      // ε₀ = ω^ω^ω^...
            // ================================================================
            // Ordinal arithmetic
            // ================================================================
            "SetTheory.OrdinalAdd",            // ordinal addition α + β
            "SetTheory.OrdinalMul",            // ordinal multiplication α · β
            "SetTheory.OrdinalExp",            // ordinal exponentiation α^β
            "SetTheory.OrdinalAddAssoc",       // (α + β) + γ = α + (β + γ)
            "SetTheory.OrdinalMulDistrib",     // α · (β + γ) = α·β + α·γ
            "SetTheory.OrdinalExpAdd",         // α^(β+γ) = α^β · α^γ
            "SetTheory.OrdinalNotCommutative", // addition/multiplication not commutative
            "SetTheory.CantorNormalForm",      // Cantor normal form theorem
            // ================================================================
            // Ordinal operations
            // ================================================================
            "SetTheory.OrdinalSup",        // supremum of ordinal set
            "SetTheory.OrdinalInf",        // infimum of ordinal set
            "SetTheory.OrdinalUnion",      // union of ordinal set
            "SetTheory.OrdinalCofinality", // cofinality cf(α)
            "SetTheory.Regular",           // regular ordinal (cf(α) = α)
            "SetTheory.Singular",          // singular ordinal (cf(α) < α)
            // ================================================================
            // Cardinal numbers - basics
            // ================================================================
            "SetTheory.Cardinal",            // type of cardinals
            "SetTheory.CardinalZero",        // zero cardinal (empty set)
            "SetTheory.CardinalOne",         // one (singleton)
            "SetTheory.CardinalFinite",      // finite cardinal
            "SetTheory.CardinalInfinite",    // infinite cardinal
            "SetTheory.CardinalCountable",   // countable (≤ ℵ₀)
            "SetTheory.CardinalUncountable", // uncountable (> ℵ₀)
            "SetTheory.CardinalLt",          // cardinal less than
            "SetTheory.CardinalLe",          // cardinal less or equal
            "SetTheory.CardinalEq",          // cardinal equality (bijection)
            "SetTheory.Cardinality",         // |A| - cardinality function
            // ================================================================
            // Cardinal arithmetic
            // ================================================================
            "SetTheory.CardinalAdd",         // cardinal addition |A| + |B|
            "SetTheory.CardinalMul",         // cardinal multiplication |A| · |B|
            "SetTheory.CardinalExp",         // cardinal exponentiation |A|^|B|
            "SetTheory.CardinalAddInfinite", // κ + λ = max(κ, λ) for infinite
            "SetTheory.CardinalMulInfinite", // κ · λ = max(κ, λ) for infinite
            "SetTheory.CardinalPower",       // 2^κ = power set cardinality
            "SetTheory.KoenigsTheorem",      // König's theorem: Σκᵢ < Πλᵢ
            // ================================================================
            // Aleph numbers (infinite cardinals)
            // ================================================================
            "SetTheory.Aleph",         // ℵ function (ℵ_α)
            "SetTheory.Aleph0",        // ℵ₀ = |ℕ| (first infinite)
            "SetTheory.Aleph1",        // ℵ₁ (first uncountable)
            "SetTheory.AlephSucc",     // ℵ_{α+1}
            "SetTheory.AlephLimit",    // ℵ_λ for limit λ
            "SetTheory.AlephFixed",    // fixed point: ℵ_α = α
            "SetTheory.AlephMonotone", // α < β → ℵ_α < ℵ_β
            // ================================================================
            // Beth numbers (power set hierarchy)
            // ================================================================
            "SetTheory.Beth",        // ב function (ב_α)
            "SetTheory.Beth0",       // ב₀ = ℵ₀
            "SetTheory.BethSucc",    // ב_{α+1} = 2^{ב_α}
            "SetTheory.BethLimit",   // ב_λ for limit λ
            "SetTheory.BethLeAleph", // ℵ_α ≤ ב_α
            // ================================================================
            // Continuum and GCH
            // ================================================================
            "SetTheory.Continuum",           // c = 2^ℵ₀ = |ℝ|
            "SetTheory.ContinuumHypothesis", // CH: 2^ℵ₀ = ℵ₁
            "SetTheory.GeneralizedCH",       // GCH: 2^ℵ_α = ℵ_{α+1}
            "SetTheory.CHIndependent",       // CH independent of ZFC
            "SetTheory.GCHImpliesAC",        // GCH implies AC
            // ================================================================
            // Well-orderings
            // ================================================================
            "SetTheory.WellOrder",           // well-ordering relation
            "SetTheory.WellFounded",         // well-founded relation
            "SetTheory.IsWellOrder",         // predicate for well-order
            "SetTheory.WellOrderIso",        // well-order isomorphism
            "SetTheory.OrderType",           // order type (ordinal of well-order)
            "SetTheory.InitialSegment",      // initial segment
            "SetTheory.WellOrderingTheorem", // every set can be well-ordered (AC)
            "SetTheory.HartogNumber",        // Hartogs number H(A)
            // ================================================================
            // Axiom of Choice and equivalents
            // ================================================================
            "SetTheory.AxiomOfChoice", // AC: every family has choice function
            "SetTheory.WellOrderingPrinciple", // WO: every set well-orderable (≡ AC)
            "SetTheory.ZornsLemma",    // every chain-complete poset has maximal
            "SetTheory.ZornsLemmaEquivAC", // Zorn ↔ AC
            "SetTheory.TychonoffTheorem", // product of compact spaces (≡ AC)
            "SetTheory.MaximalIdealTheorem", // every ring has maximal ideal
            "SetTheory.BasisTheorem",  // every vector space has basis
            "SetTheory.CountableChoice", // AC for countable families
            "SetTheory.DependentChoice", // DC: dependent choice axiom
            "SetTheory.BooleanPrimeIdeal", // BPI: Boolean algebras have ultrafilters
            // ================================================================
            // Transfinite induction and recursion
            // ================================================================
            "SetTheory.TransfiniteInduction", // proof by transfinite induction
            "SetTheory.TransfiniteRecursion", // definition by transfinite recursion
            "SetTheory.OrdinalInduction",     // induction on ordinals
            "SetTheory.WellFoundedInduction", // induction on well-founded relations
            "SetTheory.NoethianInduction",    // ascending chain condition
            "SetTheory.BuraliForti",          // Burali-Forti paradox (no set of all ordinals)
            // ================================================================
            // ZFC axioms (formalized)
            // ================================================================
            "SetTheory.AxiomExtensionality", // sets equal iff same members
            "SetTheory.AxiomEmptySet",       // empty set exists
            "SetTheory.AxiomPairing",        // {a, b} exists
            "SetTheory.AxiomUnion",          // ∪A exists
            "SetTheory.AxiomPowerSet",       // P(A) exists
            "SetTheory.AxiomInfinity",       // infinite set exists
            "SetTheory.AxiomSeparation",     // {x ∈ A : φ(x)} exists (schema)
            "SetTheory.AxiomReplacement",    // F[A] exists for functional F (schema)
            "SetTheory.AxiomRegularity",     // ∈ is well-founded
            "SetTheory.ZF",                  // Zermelo-Fraenkel
            "SetTheory.ZFC",                 // ZF + Choice
            // ================================================================
            // Other set theory axiom systems
            // ================================================================
            "SetTheory.NBG", // von Neumann-Bernays-Gödel
            "SetTheory.MK",  // Morse-Kelley
            "SetTheory.NF",  // New Foundations (Quine)
            "SetTheory.NFU", // NF with urelements
            "SetTheory.KP",  // Kripke-Platek
            "SetTheory.Z",   // Zermelo (no replacement)
            // ================================================================
            // Large cardinals (weak)
            // ================================================================
            "SetTheory.Inaccessible",         // inaccessible cardinal
            "SetTheory.WeaklyInaccessible",   // weakly inaccessible
            "SetTheory.StronglyInaccessible", // strongly inaccessible
            "SetTheory.Mahlo",                // Mahlo cardinal
            "SetTheory.WeaklyMahlo",          // weakly Mahlo
            "SetTheory.Hyperinaccessible",    // hyperinaccessible
            "SetTheory.InaccessibleLimit",    // limit of inaccessibles
            // ================================================================
            // Large cardinals (strong)
            // ================================================================
            "SetTheory.Measurable",             // measurable cardinal
            "SetTheory.Ramsey",                 // Ramsey cardinal
            "SetTheory.Erdos",                  // Erdős cardinal
            "SetTheory.Jonsson",                // Jónsson cardinal
            "SetTheory.Rowbottom",              // Rowbottom cardinal
            "SetTheory.Strongly Compact",       // strongly compact
            "SetTheory.Supercompact",           // supercompact cardinal
            "SetTheory.Extendible",             // extendible cardinal
            "SetTheory.Vopenka",                // Vopěnka's principle
            "SetTheory.Huge",                   // huge cardinal
            "SetTheory.Superhuge",              // superhuge
            "SetTheory.Rank Into Rank",         // rank-into-rank (I0-I3)
            "SetTheory.Reinhardt",              // Reinhardt cardinal (inconsistent w/AC)
            "SetTheory.LargeCardinalHierarchy", // the hierarchy of large cardinals
            // ================================================================
            // Inner models and consistency
            // ================================================================
            "SetTheory.ConstructibleUniverse", // L = Gödel's constructible universe
            "SetTheory.AxiomOfConstructibility", // V = L
            "SetTheory.VEqualsL",              // V = L axiom
            "SetTheory.RelativeConsistency",   // Con(T) → Con(S)
            "SetTheory.GoedelConsistency",     // Con(ZF) → Con(ZFC + GCH)
            "SetTheory.CohenForcing",          // forcing method
            "SetTheory.GenericExtension",      // generic extension V[G]
            "SetTheory.IndependenceProofs",    // CH, AC independence
            // ================================================================
            // Descriptive set theory
            // ================================================================
            "SetTheory.BorelSet",              // Borel sets
            "SetTheory.AnalyticSet",           // analytic (Σ¹₁) sets
            "SetTheory.CoAnalyticSet",         // co-analytic (Π¹₁) sets
            "SetTheory.ProjectiveSet",         // projective hierarchy
            "SetTheory.Sigma1n",               // Σ¹ₙ sets
            "SetTheory.Pi1n",                  // Π¹ₙ sets
            "SetTheory.Delta1n",               // Δ¹ₙ sets
            "SetTheory.Determined",            // determined set (game)
            "SetTheory.AxiomOfDeterminacy",    // AD: all sets determined
            "SetTheory.ProjectiveDeterminacy", // PD: projective sets determined
            "SetTheory.PerfectSetProperty",    // uncountable → contains perfect set
            "SetTheory.LebesgueMeasurable",    // Lebesgue measurable sets
            "SetTheory.BaireProperty",         // Baire property
            // ================================================================
            // Combinatorial set theory
            // ================================================================
            "SetTheory.RamseyTheorem",      // infinite Ramsey theorem
            "SetTheory.PartitionCalculus",  // partition calculus κ → (λ)^n_m
            "SetTheory.ArrowNotation",      // Erdős-Rado arrow notation
            "SetTheory.TreeProperty",       // κ-tree property
            "SetTheory.AronszajnTree",      // Aronszajn tree
            "SetTheory.SouslinTree",        // Souslin tree
            "SetTheory.KurepaTree",         // Kurepa tree
            "SetTheory.ClubFilter",         // club filter
            "SetTheory.StationarySet",      // stationary set
            "SetTheory.FodorsLemma",        // pressing down lemma
            "SetTheory.DiamondPrinciple",   // ◇ diamond principle
            "SetTheory.SquarePrinciple",    // □ square principle
            "SetTheory.MartinsAxiom",       // MA: Martin's axiom
            "SetTheory.ProperForcingAxiom", // PFA
            "SetTheory.MartinsMaximum",     // MM: Martin's maximum
            // ================================================================
            // Set operations and basic properties
            // ================================================================
            "SetTheory.Equipotent",         // |A| = |B| (same cardinality)
            "SetTheory.Dominate",           // |A| ≤ |B| (injection exists)
            "SetTheory.SchroederBernstein", // |A|≤|B| ∧ |B|≤|A| → |A|=|B|
            "SetTheory.CantorTheorem",      // |A| < |P(A)|
            "SetTheory.CantorDiagonal",     // diagonal argument
            "SetTheory.PowerSetInequality", // 2^κ > κ
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.set_theory_init = true;
        Ok(())
    }

    /// Check if Set Theory module has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_set_theory` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_set_theory(&self) -> bool {
        self.set_theory_init
    }

    /// Initialize basic Set type (Mathlib compatible)
    ///
    /// Set α := α → Prop (indicator function / predicate)
    ///
    /// This is the basic Set type used in Mathlib, distinct from the axiomatic
    /// set theory constants above. It adds:
    /// - Set : Type u → Type u
    /// - Membership : Type u → Type v → Type (max u v)
    /// - instMembershipSet : Membership α (Set α)
    /// - Set.mem : {α : Type u} → Set α → α → Prop
    /// - setOf : {α : Type u} → (α → Prop) → Set α
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.set_init == true`
    /// ENSURES: On success, required dependencies (`eq`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_set(&mut self) -> Result<(), EnvError> {
        if self.set_init {
            return Ok(());
        }

        self.init_eq()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let prop = Expr::sort(Level::zero());

        // ================================================================
        // Set : Type u → Type u  :=  fun α => α → Prop   (reducible)
        // ================================================================
        // Lean 4/Mathlib (`#print Set`):
        //   @[reducible] def Set.{u} : Type u → Type u := fun α => α → Prop
        //
        // Clean previously registered `Set` as an OPAQUE axiom
        // `Set : Type u → Type u` with no value. Because that `Set` never
        // δ-reduces, a `Set α` value could not whnf to its underlying predicate
        // type `α → Prop`, so any proof that APPLIES a `Set α` as a predicate
        // (e.g. `Function.cantor_surjective.match_1`, membership via `s a`,
        // `setOf`) hit the kernel arg-check "Expected function type, got Set" and
        // was rejected. This is FOUNDATIONAL: it latently blocks membership /
        // predicate-application proofs corpus-wide.
        //
        // Registering `Set` as the real Lean reducible DEFINITION
        // `fun (α : Type u) => α → Prop` (SAME type `Type u → Type u`, unchanged)
        // lets `unfold_definition` δ-reduce `Set α` to `α → Prop`, so
        // `Set`-as-predicate applications type-check exactly as Lean's kernel
        // does. This is STRICTLY ADDITIVE (Set gains a reducible value; its type
        // is identical): it can only let MORE well-typed proofs reduce, never
        // break one. A prelude-DATA correction to MATCH Lean — NOT an is_def_eq /
        // whnf relaxation. `add_decl` re-checks the value against the (unchanged)
        // type; the axiom closure stays empty.
        let set_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

        // value = fun (α : Type u) => (α → Prop)
        let set_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // body: α → Prop — build the inner Pi in a child scope to avoid
            // fvar-id collision with the outer λ-binder.
            let arrow = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = cb.fresh_local(alpha.clone());
                let inner = cb.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop.clone());
                cb.finish_child(inner)
            };
            let r = b.mk_lam(alpha_id, BinderInfo::Default, type_u.clone(), arrow);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Set"),
            level_params: vec![u.clone()],
            type_: set_type,
            value: set_value,
            is_reducible: true,
        })?;

        let set_const = Expr::const_(Name::from_string("Set"), vec![u_level.clone()]);

        // ================================================================
        // Membership : Type u → Type v → Type (max u v)  (single-field class)
        // ================================================================
        // Lean 4 v4.30 (`Init/Prelude.lean:1744-1746`):
        //   class Membership (α : outParam (Type u)) (γ : Type v) where
        //     mem : γ → α → Prop
        //
        // FIELD ORDER FIDELITY (residual-to-zero campaign, 2026-07-03): the
        // field is COLLECTION-first (`mem : γ → α → Prop`) since Lean v4.9;
        // Clean previously seeded the pre-4.9 ELEMENT-first shape
        // (`mem : α → γ → Prop`). Because the `.olean` loader dedups by name,
        // the transposed seed SHADOWED the genuine class for every stamped
        // closure, so every `∈`-mentioning olean declaration failed its kernel
        // check (`ForIn'.mk` "expected FVar(8), got FVar(7)"; the
        // `instMembershipOfBEqOfHashable`/`instDecidableMem` cascade in
        // Std/Data/DHashMap/Raw). Corrected to Lean's exact field order; every
        // seeded construction/use site below (instances, `Membership.mem`
        // projection, `∈`-form lemmas) applies arguments collection-first, and
        // the kernel re-checks all of them.
        //
        // Clean previously also registered `Membership` and `Membership.mem` as
        // bare axioms. With no `Membership.mk` constructor and no projection
        // body, a genuine Mathlib `@Membership.mem α γ inst s a` (where `inst`
        // is a concrete instance such as `List.instMembership`) could NEVER
        // reduce to the underlying relation (e.g. `List.Mem a s`), so every
        // real-math proof that compares `a ∈ s` against the carrier relation
        // mis-matched ("List.Mem vs Membership.mem") and was rejected. Building
        // `Membership` as the real Lean single-field structure —
        // `Membership.mk` constructor + `Membership.mem` reducible projection —
        // lets the kernel delta+proj-reduce
        // `Membership.mem ... (Membership.mk ... rel) s a` to `rel s a` exactly
        // as Lean's kernel does. This is a prelude-SHAPE correction to MATCH
        // Lean (same type signature, same field), NOT an is_def_eq relaxation:
        // the kernel re-checks the projection body and every instance below.
        let max_uv = Level::max(u_level.clone(), v_level.clone());
        let type_max_uv = Expr::sort(Level::succ(max_uv.clone()));

        let membership_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(),
            Expr::pi(BinderInfo::Default, type_v.clone(), type_max_uv.clone()),
        );

        let membership_const = Expr::const_(
            Name::from_string("Membership"),
            vec![u_level.clone(), v_level.clone()],
        );

        // Membership.mk : {α : Type u} → {γ : Type v} → (γ → α → Prop) → Membership α γ
        let membership_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (gamma_id, gamma) = b.fresh_local(type_v.clone());
            // mem field : γ → α → Prop  (collection-first, Lean v4.30
            // Init/Prelude.lean:1746)
            let mem_field_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (s_id, _s) = c.fresh_local(gamma.clone());
                let (a_id, _a) = c.fresh_local(alpha.clone());
                let r = prop.clone();
                let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                let r = c.mk_pi(s_id, BinderInfo::Default, gamma.clone(), r);
                c.finish_child(r)
            };
            let (field_id, _field) = b.fresh_local(mem_field_ty.clone());
            let r = Expr::app(
                Expr::app(membership_const.clone(), alpha.clone()),
                gamma.clone(),
            );
            let r = b.mk_pi(field_id, BinderInfo::Default, mem_field_ty, r);
            let r = b.mk_pi(gamma_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let membership_ind = InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2, // α and γ are parameters
            types: vec![InductiveType {
                name: Name::from_string("Membership"),
                type_: membership_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Membership.mk"),
                    type_: membership_mk_type,
                }],
            }],
        };

        self.add_inductive(membership_ind)?;

        // Register the structure field for `Expr::proj` support.
        self.register_structure_fields(
            Name::from_string("Membership"),
            vec![Name::from_string("mem")],
        )?;

        // Register Membership as a type class (α is an outParam in Lean).
        self.register_class(KernelClassInfo {
            name: Name::from_string("Membership"),
            num_params: 2,
            out_params: vec![0],
            semi_out_params: vec![],
        });

        // ================================================================
        // Membership.mem : {α : Type u} → {γ : Type v} → [Membership α γ] → γ → α → Prop
        // ================================================================
        // The membership projection, COLLECTION-first exactly as Lean v4.30
        // (`Init/Prelude.lean:1746`, field `mem : γ → α → Prop`; `a ∈ s`
        // desugars to `Membership.mem s a`). Reducible identity-via-projection
        // so the kernel unfolds it to `(Membership.mk-stored relation) s a`.
        let mem_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (gamma_id, gamma) = b.fresh_local(type_v.clone());
            let membership_app = Expr::app(
                Expr::app(membership_const.clone(), alpha.clone()),
                gamma.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(membership_app.clone());
            let (s_id, _s) = b.fresh_local(gamma.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let e = prop.clone();
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, gamma.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, membership_app, e);
            let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Membership.mem value =
        //   λ {α} {γ} [inst : Membership α γ] (s : γ) (a : α) =>
        //     (Expr::proj("Membership", 0, inst)) s a
        let mem_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (gamma_id, gamma) = b.fresh_local(type_v.clone());
            let membership_app = Expr::app(
                Expr::app(membership_const.clone(), alpha.clone()),
                gamma.clone(),
            );
            let (inst_id, inst) = b.fresh_local(membership_app.clone());
            let (s_id, s) = b.fresh_local(gamma.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let body = Expr::app(
                Expr::app(Expr::proj(Name::from_string("Membership"), 0, inst), s),
                a,
            );
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(s_id, BinderInfo::Default, gamma.clone(), r);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, membership_app, r);
            let r = b.mk_lam(gamma_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Membership.mem"),
            level_params: vec![u.clone(), v.clone()],
            type_: mem_type,
            value: mem_value,
            is_reducible: true,
        })?;

        // ================================================================
        // Set.mem : {α : Type u} → Set α → α → Prop
        // ================================================================
        // Direct membership check for Set. COLLECTION-first, mirroring
        // Mathlib's `Set.Mem (s : Set α) (a : α) : Prop` after the Lean v4.9
        // `Membership` field flip — the carrier relation must have the field
        // type `γ → α → Prop` so `instMembershipSet` below stays a bare
        // `Membership.mk` application, exactly like Mathlib's
        // `instance : Membership α (Set α) := ⟨Set.Mem⟩`.
        let set_mem_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let set_alpha = Expr::app(set_const.clone(), alpha.clone());
            let (s_id, _s) = b.fresh_local(set_alpha.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let e = prop.clone();
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, set_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Set.mem"),
            level_params: vec![u.clone()],
            type_: set_mem_type,
        })?;

        // ================================================================
        // instMembershipSet : {α : Type u} → Membership α (Set α)
        //   := Membership.mk α (Set α) Set.mem
        // ================================================================
        // A genuine `Membership.mk`-based definition (NOT an axiom) so that
        // `Membership.mem α (Set α) instMembershipSet s a` proj-reduces to
        // `Set.mem s a`. Built AFTER `Set.mem` so the body resolves. The kernel
        // re-checks the body; `Set.mem` is itself an axiom (the carrier relation),
        // matching how Set is modeled.
        let inst_membership_set_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let membership_uu = Expr::const_(
                Name::from_string("Membership"),
                vec![u_level.clone(), u_level.clone()],
            );
            let e = Expr::app(
                Expr::app(membership_uu, alpha.clone()),
                Expr::app(set_const.clone(), alpha.clone()),
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let inst_membership_set_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let set_alpha = Expr::app(set_const.clone(), alpha.clone());
            // Membership.mk.{u,u} α (Set α) Set.mem
            let membership_mk = Expr::const_(
                Name::from_string("Membership.mk"),
                vec![u_level.clone(), u_level.clone()],
            );
            let set_mem = Expr::const_(Name::from_string("Set.mem"), vec![u_level.clone()]);
            // Set.mem α : Set α → α → Prop  (the collection-first field relation)
            let set_mem_alpha = Expr::app(set_mem, alpha.clone());
            let body = Expr::apps(membership_mk, [alpha.clone(), set_alpha, set_mem_alpha]);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("instMembershipSet"),
            level_params: vec![u.clone()],
            type_: inst_membership_set_type,
            value: inst_membership_set_value,
            is_reducible: true,
        })?;
        // Register it as a `Membership` instance so `a ∈ s` (Set) resolves.
        self.register_instance(crate::env::KernelInstanceInfo {
            name: Name::from_string("instMembershipSet"),
            class_name: Name::from_string("Membership"),
            priority: crate::env::DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // ================================================================
        // setOf : {α : Type u} → (α → Prop) → Set α
        // ================================================================
        // Set builder notation: {x | p x}
        let setof_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // p : α → Prop — build inner Pi with child to avoid fvar collision
            let p_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = cb.fresh_local(alpha.clone());
                let inner = cb.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop.clone());
                cb.finish_child(inner)
            };
            let (p_id, _p) = b.fresh_local(p_type.clone());
            let e = Expr::app(set_const.clone(), alpha.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, p_type, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("setOf"),
            level_params: vec![u.clone()],
            type_: setof_type,
        })?;

        // ================================================================
        // Set operations: union, inter, diff, compl
        // ================================================================
        // Set.union : {α : Type u} → Set α → Set α → Set α
        let set_binop_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let set_alpha = Expr::app(set_const.clone(), alpha.clone());
            let (s1_id, _s1) = b.fresh_local(set_alpha.clone());
            let (s2_id, _s2) = b.fresh_local(set_alpha.clone());
            let e = set_alpha.clone();
            let e = b.mk_pi(s2_id, BinderInfo::Default, set_alpha.clone(), e);
            let e = b.mk_pi(s1_id, BinderInfo::Default, set_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        for name in &["Set.union", "Set.inter", "Set.diff", "Set.symmDiff"] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: set_binop_type.clone(),
            })?;
        }

        // Set.compl : {α : Type u} → Set α → Set α
        let set_compl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let set_alpha = Expr::app(set_const.clone(), alpha.clone());
            let (s_id, _s) = b.fresh_local(set_alpha.clone());
            let e = set_alpha.clone();
            let e = b.mk_pi(s_id, BinderInfo::Default, set_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Set.compl"),
            level_params: vec![u.clone()],
            type_: set_compl_type,
        })?;

        // ================================================================
        // Set.empty : {α : Type u} → Set α
        // ================================================================
        let set_empty_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let e = Expr::app(set_const.clone(), alpha.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Set.empty"),
            level_params: vec![u.clone()],
            type_: set_empty_type.clone(),
        })?;

        // ================================================================
        // Set.univ : {α : Type u} → Set α
        // ================================================================
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Set.univ"),
            level_params: vec![u.clone()],
            type_: set_empty_type.clone(),
        })?;

        // ================================================================
        // Set.singleton : {α : Type u} → α → Set α
        // ================================================================
        let set_singleton_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (x_id, _x) = b.fresh_local(alpha.clone());
            let e = Expr::app(set_const.clone(), alpha.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Set.singleton"),
            level_params: vec![u.clone()],
            type_: set_singleton_type,
        })?;

        // ================================================================
        // Set.insert : {α : Type u} → α → Set α → Set α
        // ================================================================
        let set_insert_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (x_id, _x) = b.fresh_local(alpha.clone());
            let set_alpha = Expr::app(set_const.clone(), alpha.clone());
            let (s_id, _s) = b.fresh_local(set_alpha.clone());
            let e = set_alpha.clone();
            let e = b.mk_pi(s_id, BinderInfo::Default, set_alpha, e);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Set.insert"),
            level_params: vec![u.clone()],
            type_: set_insert_type,
        })?;

        // ================================================================
        // Set.Subset : {α : Type u} → Set α → Set α → Prop
        // ================================================================
        let set_subset_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let set_alpha = Expr::app(set_const.clone(), alpha.clone());
            let (s1_id, _s1) = b.fresh_local(set_alpha.clone());
            let (s2_id, _s2) = b.fresh_local(set_alpha.clone());
            let e = prop.clone();
            let e = b.mk_pi(s2_id, BinderInfo::Default, set_alpha.clone(), e);
            let e = b.mk_pi(s1_id, BinderInfo::Default, set_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Set.Subset"),
            level_params: vec![u.clone()],
            type_: set_subset_type,
        })?;

        self.set_init = true;
        Ok(())
    }

    /// Check if basic Set type has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_set` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_set(&self) -> bool {
        self.set_init
    }
}

#[cfg(test)]
mod set_reducible_def_tests {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::env::{ConstantKind, Environment, Reducibility};
    use crate::expr::{BinderInfo, Expr};
    use crate::level::Level;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env_with_set() -> Environment {
        let mut env = Environment::new();
        env.init_set().expect("Set should initialize");
        env
    }

    /// `Set` is now the real Lean reducible DEFINITION (not an opaque axiom),
    /// with the type unchanged at `Type u → Type u`.
    #[test]
    fn test_set_is_reducible_definition_with_arrow_type() {
        let env = env_with_set();
        let info = env
            .get_const(&Name::from_string("Set"))
            .expect("Set should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "Set must be a Definition (was Axiom): matches Lean `def Set`"
        );
        assert_eq!(
            info.reducibility,
            Reducibility::Reducible,
            "Set must be @[reducible], matching Lean"
        );
        assert!(
            info.value.is_some(),
            "Set must carry a value body `fun α => α → Prop`"
        );

        // Type must stay exactly `Type u → Type u`.
        let u = Level::param(Name::from_string("u"));
        let type_u = Expr::sort(Level::succ(u.clone()));
        let expected_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        let tc = TypeChecker::new(&env);
        assert!(
            tc.is_def_eq(&info.type_, &expected_type),
            "Set type must remain `Type u → Type u`"
        );
    }

    /// `Set α` δ-reduces (reducibly) to the predicate type `α → Prop`.
    #[test]
    fn test_set_alpha_reduces_to_predicate_type() {
        let env = env_with_set();
        let tc = TypeChecker::new(&env);

        let u = Level::param(Name::from_string("u"));
        let type_u = Expr::sort(Level::succ(u.clone()));
        let prop = Expr::sort(Level::zero());

        // Work under a binder `{α : Type u}` so reduction happens under a real
        // free-variable telescope (the faithful verify context).
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());

        // lhs = Set α
        let set_alpha = Expr::app(
            Expr::const_(Name::from_string("Set"), vec![u.clone()]),
            alpha.clone(),
        );
        // rhs = α → Prop
        let arrow = {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let (x_id, _x) = cb.fresh_local(alpha.clone());
            let inner = cb.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop.clone());
            cb.finish_child(inner)
        };

        let lhs = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), set_alpha);
        let rhs = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), arrow);
        let lhs = b.finish(lhs);
        let rhs = b.finish(rhs);

        assert!(tc.is_def_eq(&lhs, &rhs), "Set α must δ-reduce to α → Prop");
    }

    /// A `Set α` value can be APPLIED as a predicate: `@s a : Prop`. Before the
    /// fix (opaque `Set` axiom) this failed the kernel arg-check with "Expected
    /// function type, got Set" — the root cause this change removes.
    #[test]
    fn test_set_value_applies_as_predicate() {
        let env = env_with_set();
        let tc = TypeChecker::new(&env);

        let u = Level::param(Name::from_string("u"));
        let type_u = Expr::sort(Level::succ(u.clone()));

        // fun {α : Type u} (s : Set α) (a : α) => s a
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let set_alpha = Expr::app(
            Expr::const_(Name::from_string("Set"), vec![u.clone()]),
            alpha.clone(),
        );
        let (s_id, s) = b.fresh_local(set_alpha.clone());
        let (a_id, a) = b.fresh_local(alpha.clone());
        // s a — only type-checks if `Set α` reduces to a function type.
        let body = Expr::app(s.clone(), a.clone());
        let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
        let r = b.mk_lam(s_id, BinderInfo::Default, set_alpha, r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
        let term = b.finish(r);

        let ty = tc
            .infer_type(&term)
            .expect("applying a `Set α` value as a predicate must type-check");

        // Result type is `{α} → Set α → α → Prop`; just confirm inference
        // succeeded and produced a Pi (function) type.
        assert!(
            matches!(ty.kind(), crate::expr::ExprKind::Pi(..)),
            "predicate-application lambda should infer a Pi type, got {ty:?}"
        );
    }
}
