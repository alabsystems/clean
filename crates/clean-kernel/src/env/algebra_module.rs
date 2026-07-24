// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module and Algebra structures for Environment
//!
//! This module contains algebraic structure initialization:
//! - Module R M: R-module structure on M
//! - Algebra R A: R-algebra structure on A (extends Module)
//! - Ideal R: Ideal in a ring R
//! - Submodule R M: Submodule of an R-module M
//!
//! These are required for FATE-X elaboration which uses Mathlib's algebraic hierarchy.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Module R M typeclass
    ///
    /// Module R M is an R-module structure on the abelian group M, where R is a ring.
    ///
    /// class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] where
    ///   smul : R → M → M
    ///   one_smul : ∀ x, 1 • x = x
    ///   mul_smul : ∀ r s x, (r * s) • x = r • (s • x)
    ///   smul_zero : ∀ r, r • 0 = 0
    ///   smul_add : ∀ r x y, r • (x + y) = r • x + r • y
    ///   add_smul : ∀ r s x, (r + s) • x = r • x + s • x
    ///   zero_smul : ∀ x, 0 • x = 0
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.module_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_module(&mut self) -> Result<(), EnvError> {
        if self.module_init {
            return Ok(());
        }

        self.init_eq()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let _type_v = Expr::sort(Level::succ(v_level.clone()));

        // Module typeclass and related declarations
        for name in &[
            // Core Module structure
            "Module",           // Module R M typeclass
            "Module.smul",      // (•) : R → M → M
            "Module.one_smul",  // ∀ x, 1 • x = x
            "Module.mul_smul",  // ∀ r s x, (r * s) • x = r • (s • x)
            "Module.smul_zero", // ∀ r, r • 0 = 0
            "Module.smul_add",  // ∀ r x y, r • (x + y) = r • x + r • y
            "Module.add_smul",  // ∀ r s x, (r + s) • x = r • x + s • x
            "Module.zero_smul", // ∀ x, 0 • x = 0
            // SMul operator
            "SMul",        // SMul α β - scalar multiplication typeclass
            "SMul.smul",   // smul : α → β → β
            "HSMul",       // Heterogeneous scalar multiplication
            "HSMul.hSMul", // hSMul : α → β → γ
            "instHSMul",   // Default HSMul from SMul
            // Module properties
            "Module.Free",       // Free R M - M is a free R-module
            "Module.Finite",     // Finite R M - M is finitely generated
            "Module.rank",       // rank of a module (cardinal)
            "Module.Projective", // Projective R P - P is projective
            // Module instances
            "instModuleSelf", // Module R R - R is a module over itself
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone(), v.clone()],
                type_: type_u.clone(), // Simplified; actual type is more complex
            })?;
        }

        self.module_init = true;
        Ok(())
    }

    /// Check if Module typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.module_init == true`
    pub fn has_module(&self) -> bool {
        self.module_init
    }

    /// Initialize Algebra R A typeclass
    ///
    /// Algebra R A extends Module R A with a ring homomorphism R →+* A.
    ///
    /// class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends Module R A where
    ///   algebraMap : R →+* A
    ///   commutes : ∀ r x, algebraMap r * x = x * algebraMap r
    ///   smul_def : ∀ r x, r • x = algebraMap r * x
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.algebra_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_algebra(&mut self) -> Result<(), EnvError> {
        if self.algebra_init {
            return Ok(());
        }

        self.init_module()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Algebra typeclass and related declarations
        for name in &[
            // Core Algebra structure
            "Algebra",            // Algebra R A typeclass
            "Algebra.toModule",   // Algebra → Module
            "Algebra.algebraMap", // algebraMap : R →+* A
            "Algebra.commutes",   // ∀ r x, algebraMap r * x = x * algebraMap r
            "Algebra.smul_def",   // ∀ r x, r • x = algebraMap r * x
            "algebraMap",         // Top-level algebraMap function
            // Algebra operations
            "Algebra.adjoin", // Algebra.adjoin R S - subalgebra generated by S
            "Algebra.adjoin.powerSet", // Power set of adjoin
            "Algebra.adjoin.mono", // Monotonicity of adjoin
            // Subalgebra
            "Subalgebra",                // Subalgebra R A - subalgebra of A
            "Subalgebra.toSubring",      // Subalgebra → Subring
            "Subalgebra.carrier",        // Underlying set
            "Subalgebra.algebraMap_mem", // algebraMap r ∈ S
            "Subalgebra.mul_mem",        // Closed under multiplication
            "Subalgebra.add_mem",        // Closed under addition
            // Algebra instances
            "instAlgebraSelf", // Algebra R R
            "Algebra.id",      // Algebra R R identity
            // Intermediate fields (for field extensions)
            "IntermediateField",        // Intermediate field in extension
            "IntermediateField.adjoin", // Adjoin element to get intermediate field
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone(), v.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.algebra_init = true;
        Ok(())
    }

    /// Check if Algebra typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.algebra_init == true`
    pub fn has_algebra(&self) -> bool {
        self.algebra_init
    }

    /// Initialize Ideal R type
    ///
    /// Ideal R is defined as Submodule R R - a submodule of R viewed as a module over itself.
    ///
    /// def Ideal (R : Type u) [Semiring R] := Submodule R R
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ideal_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ideal(&mut self) -> Result<(), EnvError> {
        if self.ideal_init {
            return Ok(());
        }

        self.init_submodule()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Ideal : Type u → Type u (takes a ring type, returns its ideal type)
        // Lean 4: `def Ideal (R : Type u) [Semiring R] := Submodule R R`
        // Simplified stub without the [Semiring R] instance argument.
        let ideal_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Ideal"),
            level_params: vec![u.clone()],
            type_: ideal_type,
        })?;

        // Ideal-related declarations (all typed as Type u stubs)
        for name in &[
            "Ideal.span",     // Ideal.span S - ideal generated by S
            "Ideal.mem_span", // a ∈ span S ↔ ...
            "Ideal.span_le",  // span S ≤ I ↔ S ⊆ I
            // Ideal operations
            "Ideal.add", // I + J - sum of ideals
            "Ideal.mul", // I * J - product of ideals
            "Ideal.pow", // I^n - power of ideal
            "Ideal.sup", // I ⊔ J - supremum
            "Ideal.inf", // I ⊓ J - infimum
            // Ideal properties
            "Ideal.IsPrime",     // Prime ideal
            "Ideal.IsMaximal",   // Maximal ideal
            "Ideal.IsPrincipal", // Principal ideal
            "Ideal.IsRadical",   // Radical ideal
            "Ideal.IsCoprime",   // Coprime ideals
            // Quotient rings
            "Ideal.Quotient",      // R ⧸ I quotient ring
            "Ideal.Quotient.mk",   // Quotient map
            "Ideal.Quotient.lift", // Universal property
            // Principal ideal domain - declared in algebra_advanced/factorization.rs
            // "IsPrincipalIdealRing", // All ideals are principal - ALREADY EXISTS
            // Localization
            "LocalizedModule",         // Localized module
            "LocalizedModule.AtPrime", // Localization at prime ideal
            "Localization",            // Localization of ring
            "Localization.AtPrime",    // Localization at prime
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.ideal_init = true;
        Ok(())
    }

    /// Check if Ideal type has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.ideal_init == true`
    pub fn has_ideal(&self) -> bool {
        self.ideal_init
    }

    /// Initialize Submodule R M type
    ///
    /// Submodule R M represents a submodule of M as an R-module.
    ///
    /// structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
    ///   extends AddSubmonoid M where
    ///   smul_mem' : ∀ c {x}, x ∈ carrier → c • x ∈ carrier
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.submodule_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_submodule(&mut self) -> Result<(), EnvError> {
        if self.submodule_init {
            return Ok(());
        }

        self.init_module()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Submodule structure and related declarations
        for name in &[
            // Core Submodule structure
            "Submodule",          // Submodule R M type
            "Submodule.carrier",  // Underlying set
            "Submodule.zero_mem", // 0 ∈ N
            "Submodule.add_mem",  // a ∈ N → b ∈ N → a + b ∈ N
            "Submodule.smul_mem", // a ∈ N → c • a ∈ N
            // Submodule operations
            "Submodule.span",     // Submodule.span R S - submodule generated by S
            "Submodule.mem_span", // Membership in span
            "Submodule.span_le",  // span_le lemma
            "Submodule.sup",      // N ⊔ P - supremum
            "Submodule.inf",      // N ⊓ P - infimum
            "Submodule.map",      // f(N) - image under linear map
            "Submodule.comap",    // f⁻¹(N) - preimage under linear map
            // Submodule properties
            "Submodule.FG",          // Finitely generated
            "Submodule.IsPrincipal", // Principal submodule
            // Top and bot
            "Submodule.top", // ⊤ - whole module
            "Submodule.bot", // ⊥ - zero submodule
            // Quotient modules
            "Submodule.Quotient", // M ⧸ N quotient module
            "Submodule.mkQ",      // Quotient map
            // SetLike
            "SetLike",            // SetLike typeclass
            "SetLike.coe",        // Coercion to set
            "SetLike.GradedSMul", // Graded scalar multiplication
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone(), v.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.submodule_init = true;
        Ok(())
    }

    /// Check if Submodule type has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.submodule_init == true`
    pub fn has_submodule(&self) -> bool {
        self.submodule_init
    }

    /// Initialize all module algebra structures
    ///
    /// Convenience method to initialize Module, Algebra, Ideal, and Submodule together.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.module_algebra_all_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_module_algebra_all(&mut self) -> Result<(), EnvError> {
        self.init_module()?;
        self.init_algebra()?;
        self.init_submodule()?;
        self.init_ideal()?;
        self.init_domain_types()?;
        Ok(())
    }

    /// Initialize domain-related types
    ///
    /// Types for integral domains and related structures used in FATE-X.
    /// Separates Prop-valued predicates (which take a type and return Prop)
    /// from Type constructors (which are themselves types).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.domain_types_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_domain_types(&mut self) -> Result<(), EnvError> {
        if self.domain_types_init {
            return Ok(());
        }

        // Ensure Ring is available for typeclass constraints
        self.init_ring()?;
        // Ensure Nat is available for Ext/Tor which use ℕ as the degree parameter
        self.init_nat()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::sort(Level::zero()); // Prop = Sort 0

        // Ring class: Ring : {α : Type u} → Sort u
        let ring_class = |lvl: Level| Expr::const_(Name::from_string("Ring"), vec![lvl]);

        // Prop predicates on types with Ring: {α : Type u} → [Ring α] → Prop
        // These are typeclasses that classify rings with additional properties
        let prop_pred_with_ring_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(ring_class(u_level.clone()), alpha.clone()));
            let e = prop.clone();
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(ring_class(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_init_axioms_if_absent(
            &[
                "IsDomain",           // IsDomain α - no zero divisors (integral domain)
                "NoZeroDivisors",     // NoZeroDivisors α - a * b = 0 → a = 0 ∨ b = 0
                "IsNoetherianRing",   // Noetherian ring (ACC on ideals)
                "IsArtinianRing",     // Artinian ring (DCC on ideals)
                "IsGorensteinRing",   // Gorenstein ring
                "IsLocalRing",        // Local ring (unique maximal ideal)
                "IsRegularLocalRing", // Regular local ring
                "IsCohenMacaulay",    // Cohen-Macaulay ring
                "EuclideanDomain",    // Euclidean domain
            ],
            std::slice::from_ref(&u),
            &prop_pred_with_ring_type,
        )?;

        // Simple Prop predicates: (α : Type u) → Prop
        // These don't require Ring constraints
        // Uses BinderInfo::Default (explicit) to match Lean 4's actual signatures
        // (e.g., `class Finite (α : Sort*) : Prop`)
        let simple_prop_pred_type = Expr::pi(BinderInfo::Default, type_u.clone(), prop.clone());

        // NOTE: `Fintype` is intentionally NOT in this opaque-Prop batch. It is a
        // real Type-valued data structure (`{ elems : Finset α, complete : … }`),
        // registered by `init_fintype` (see data_types_finset.rs). We materialize
        // it here so callers of `init_domain_types` get the genuine structure
        // rather than a wrong-sort `(α : Type u) → Prop` axiom.
        self.init_fintype()?;

        self.add_init_axioms_if_absent(
            &[
                "Finite",    // Finite type
                "CharZero",  // Characteristic zero
                "IsMaximal", // Generic maximality predicate
            ],
            std::slice::from_ref(&u),
            &simple_prop_pred_type,
        )?;

        // Type constants: Type u
        // These are actual types that don't take type arguments (or their arguments
        // are values, not types). NOTE: Type constructors like AlgHom, ChainComplex, etc.
        // are declared below with proper Pi types (#788).
        self.add_init_axioms_if_absent(
            &[
                // Chain complexes (accessors and predicates, not the type constructor)
                "ChainComplex.d",       // Differential map
                "ChainComplex.X",       // Objects at each degree
                "ChainComplex.Acyclic", // Acyclic complex
                // ModuleCat helpers (not the type constructor)
                "ModuleCat.of", // Construct ModuleCat object
                // Direct sum decomposition (not the type constructor)
                "DirectSum.Decomposition", // Decomposition into direct summands
                // Category theory notions for modules
                "CategoryTheory.Limits.IsZero", // Zero object
                "CategoryTheory.HasExt",        // Ext functor exists
                // Multivariate polynomial helpers (not the type constructor)
                "MvPolynomial.homogeneousSubmodule", // Homogeneous component
                // Euclidean norm
                "EuclideanNormNat", // Euclidean norm to Nat
                // Algebra homomorphism helpers (not the type constructors)
                "AlgHom.toRingHom",  // Underlying ring hom
                "AlgHom.comp",       // Composition
                "AlgHom.id",         // Identity
                "AlgEquiv.toAlgHom", // AlgEquiv → AlgHom
                "AlgEquiv.symm",     // Inverse
                "AlgEquiv.trans",    // Composition of equivs
                // Dimension theory (P2 - used in ~19% of FATE-X)
                "KrullDimension",                     // Krull dimension of ring
                "ringKrullDim",                       // Ring Krull dimension function
                "Ideal.height",                       // Height of prime ideal
                "FiniteDimensional",                  // Finite dimensional over field
                "Module.finrank",                     // Finite rank
                "FiniteDimensional.of_fintype_basis", // From finite basis
                // Maximal ideals (P2 - used in ~30% of FATE-X)
                "MaximalIdeal",     // Maximal ideal predicate/type
                "IsMaximal.ne_top", // Maximal ideals are not top
                // Prime elements and predicates
                "Prime.ne_zero", // p ≠ 0
                "Prime.ne_one",  // p ≠ 1
                // Regular sequence and depth
                "RegularSequence", // Regular sequence
                "depth",           // Depth of module
                // Tensor product helpers (not the type constructor)
                "TensorProduct.tmul",  // a ⊗ b
                "TensorProduct.lift",  // Universal property
                "TensorProduct.assoc", // (M ⊗ N) ⊗ P ≃ M ⊗ (N ⊗ P)
                // Flat modules (P3 - used in ~5% of FATE-X)
                "Module.Flat",               // Flat module
                "Module.Flat.of_free",       // Free modules are flat
                "Module.Flat.of_projective", // Projective modules are flat
                // Local rings (batch 2)
                "LocalRing",              // LocalRing R - R is a local ring
                "LocalRing.maximalIdeal", // The unique maximal ideal
                "LocalRing.closed_point", // Closed point of Spec R
                // Characteristic (batch 2)
                "CharP",              // Characteristic p ring
                "CharP.cast_eq_zero", // p = 0 in R
                // Finite types helpers (batch 2)
                "Finite.intro",      // Construct Finite
                "Finite.of_fintype", // From Fintype
                // Dual number helper (not the type constructor)
                "DualNumber.eps", // The ε element
            ],
            std::slice::from_ref(&u),
            &type_u,
        )?;

        // ===== Type Constructors (function types that return types) =====
        // These take type arguments and must have Pi types, not just Type u.
        // See factorization.rs:2618-2630 for the correct pattern.

        let v = Name::from_string("v");
        let v_level = Level::param(v.clone());
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let type_max_uv = Expr::sort(Level::succ(Level::max(u_level.clone(), v_level.clone())));

        // MvPolynomial : (σ : Type u) → (R : Type v) → Type (max u v)
        // Multivariate polynomial ring R[σ]
        let mvpoly_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // (σ : Type u)
            Expr::pi(
                BinderInfo::Default,
                type_v.clone(),      // (R : Type v)
                type_max_uv.clone(), // → Type (max u v)
            ),
        );
        self.add_init_axiom_if_absent("MvPolynomial", &[u.clone(), v.clone()], || mvpoly_type)?;

        // TensorProduct : (M : Type u) → (N : Type v) → Type (max u v)
        // Tensor product M ⊗ N (simplified, actual has R parameter and instances)
        let tensor_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // (M : Type u)
            Expr::pi(
                BinderInfo::Default,
                type_v.clone(),      // (N : Type v)
                type_max_uv.clone(), // → Type (max u v)
            ),
        );
        self.add_init_axiom_if_absent("TensorProduct", &[u.clone(), v.clone()], || tensor_type)?;

        // DirectSum : (ι : Type u) → (M : ι → Type v) → Type (max u v)
        // Direct sum ⨁ᵢ Mᵢ
        let directsum_type = {
            let mut b = EnvDeclBuilder::new();
            let (iota_id, iota) = b.fresh_local(type_u.clone()); // ι : Type u
                                                                 // M : ι → Type v
            let (m_dummy_id, _m_dummy) = b.fresh_local(iota.clone());
            let m_domain_type = b.mk_pi(
                m_dummy_id,
                BinderInfo::Default,
                iota.clone(),
                type_v.clone(),
            );
            let (m_id, _m) = b.fresh_local(m_domain_type.clone());
            let e = type_max_uv.clone();
            let e = b.mk_pi(m_id, BinderInfo::Default, m_domain_type, e);
            let e = b.mk_pi(iota_id, BinderInfo::Default, type_u.clone(), e);
            b.finish(e)
        };
        self.add_init_axiom_if_absent("DirectSum", &[u.clone(), v.clone()], || directsum_type)?;

        // DualNumber : (R : Type u) → Type u
        // Dual numbers R[ε] where ε² = 0
        let dualnumber_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // (R : Type u)
            type_u.clone(), // → Type u
        );
        self.add_init_axiom_if_absent("DualNumber", std::slice::from_ref(&u), || dualnumber_type)?;

        // FractionRing : (R : Type u) → Type u
        // Localization of R at non-zero-divisors (field of fractions generalization)
        // Used in FATE-X: 3 occurrences
        let fraction_ring_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // (R : Type u)
            type_u.clone(), // → Type u
        );
        self.add_init_axiom_if_absent("FractionRing", std::slice::from_ref(&u), || {
            fraction_ring_type
        })?;

        // RatFunc : (K : Type u) → Type u
        // Field of fractions for K[X], i.e., K(X) rational functions
        // Used in FATE-X: 2 occurrences
        let ratfunc_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // (K : Type u)
            type_u.clone(), // → Type u
        );
        self.add_init_axiom_if_absent("RatFunc", std::slice::from_ref(&u), || ratfunc_type)?;

        // ===== Algebra Homomorphism and Equivalence Type Constructors (#788) =====
        // AlgHom : (R : Type u) → (A : Type v) → (B : Type w) → Type (max u v w)
        // Algebra homomorphism A →ₐ[R] B
        let w = Name::from_string("w");
        let w_level = Level::param(w.clone());
        let type_w = Expr::sort(Level::succ(w_level.clone()));
        let type_max_uvw = Expr::sort(Level::succ(Level::max(
            u_level.clone(),
            Level::max(v_level.clone(), w_level.clone()),
        )));

        let alghom_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // (R : Type u)
            Expr::pi(
                BinderInfo::Default,
                type_v.clone(), // (A : Type v)
                Expr::pi(
                    BinderInfo::Default,
                    type_w.clone(),       // (B : Type w)
                    type_max_uvw.clone(), // → Type (max u v w)
                ),
            ),
        );
        self.add_init_axiom_if_absent("AlgHom", &[u.clone(), v.clone(), w.clone()], || {
            alghom_type.clone()
        })?;

        // AlgEquiv : (R : Type u) → (A : Type v) → (B : Type w) → Type (max u v w)
        // Algebra isomorphism A ≃ₐ[R] B
        self.add_init_axiom_if_absent("AlgEquiv", &[u.clone(), v.clone(), w.clone()], || {
            alghom_type
        })?;

        // ===== Module Category Type Constructor (#788) =====
        // ModuleCat : (R : Type u) → Type (u + 1)
        // Category of R-modules
        let type_u_succ = Expr::sort(Level::succ(Level::succ(u_level.clone())));
        let modulecat_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(),      // (R : Type u)
            type_u_succ.clone(), // → Type (u + 1)
        );
        self.add_init_axiom_if_absent("ModuleCat", std::slice::from_ref(&u), || modulecat_type)?;

        // ===== Chain Complex Type Constructor (#788) =====
        // ChainComplex : (V : Type u) → (c : Type v) → Type (max u v)
        // Chain complex in category V with index type c (typically ℕ or ℤ)
        let chaincomplex_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // (V : Type u)
            Expr::pi(
                BinderInfo::Default,
                type_v.clone(),      // (c : Type v)
                type_max_uv.clone(), // → Type (max u v)
            ),
        );
        self.add_init_axiom_if_absent("ChainComplex", &[u.clone(), v.clone()], || {
            chaincomplex_type
        })?;

        // ===== Homological Functors Type Constructors (#788) =====
        // Ext : (M : Type u) → (N : Type v) → ℕ → Type (max u v)
        // Ext functor Ext^n(M, N)
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let ext_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // (M : Type u)
            Expr::pi(
                BinderInfo::Default,
                type_v.clone(), // (N : Type v)
                Expr::pi(
                    BinderInfo::Default,
                    nat_const.clone(),   // (n : ℕ)
                    type_max_uv.clone(), // → Type (max u v)
                ),
            ),
        );
        self.add_init_axiom_if_absent("Ext", &[u.clone(), v.clone()], || ext_type.clone())?;

        // Tor : (M : Type u) → (N : Type v) → ℕ → Type (max u v)
        // Tor functor Tor_n(M, N)
        self.add_init_axiom_if_absent("Tor", &[u.clone(), v.clone()], || ext_type)?;

        // Additional Prop predicates on Ring for FATE-X compatibility
        // These require Ring constraint
        // Note: IsCohenMacaulay already defined above, FATE-X uses the same name
        self.add_init_axioms_if_absent(
            &[
                "IsReduced",      // Ring with no nilpotent elements (FATE-X: 2 occurrences)
                "IsAdicComplete", // Ring complete in adic topology (FATE-X: 2 occurrences)
            ],
            std::slice::from_ref(&u),
            &prop_pred_with_ring_type,
        )?;

        self.domain_types_init = true;
        Ok(())
    }

    /// Check if domain types have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.domain_types_init == true`
    pub fn has_domain_types(&self) -> bool {
        self.domain_types_init
    }
}
