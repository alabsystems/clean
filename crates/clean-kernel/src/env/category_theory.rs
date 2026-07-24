// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Category theory structures for Environment
//!
//! This module contains category theory initialization:
//! - Category: objects and morphisms with composition
//! - Functor: structure-preserving maps between categories
//! - NaturalTransformation: morphisms between functors
//! - Adjunction: pairs of adjoint functors
//! - Limit/Colimit: universal constructions
//! - Monad: endofunctors with unit and multiplication
//! - Yoneda: representable functors and Yoneda embedding

use crate::env::{EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize CategoryTheory module
    ///
    /// Category theory is the abstract study of mathematical structures
    /// and the relationships between them. It provides:
    /// - A unifying language for mathematics
    /// - Foundation for algebraic topology and algebraic geometry
    /// - Basis for type theory and functional programming
    /// - Framework for understanding universal constructions
    ///
    /// This module provides axioms for:
    /// - Categories, functors, and natural transformations
    /// - Adjunctions and universal properties
    /// - Limits, colimits, and (co)products
    /// - Monads and Kleisli categories
    /// - Yoneda lemma and representable functors
    /// - Abelian categories and homological algebra
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.category_theory_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `prod`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_category_theory(&mut self) -> Result<(), EnvError> {
        if self.category_theory_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_prod()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Category theory constants
        self.add_init_axioms(
            &[
                // ================================================================
                // Categories
                // ================================================================
                "CategoryTheory.Category", // Category C - category structure
                "CategoryTheory.Hom",      // Hom X Y - morphisms from X to Y
                "CategoryTheory.id",       // id X : Hom X X - identity morphism
                "CategoryTheory.comp",     // f ≫ g : Hom X Z - composition
                "CategoryTheory.id_comp",  // id ≫ f = f
                "CategoryTheory.comp_id",  // f ≫ id = f
                "CategoryTheory.assoc",    // (f ≫ g) ≫ h = f ≫ (g ≫ h)
                // ================================================================
                // Morphism Properties
                // ================================================================
                "CategoryTheory.Mono",        // f is monic (left cancellable)
                "CategoryTheory.Epi",         // f is epic (right cancellable)
                "CategoryTheory.Iso",         // f is isomorphism (has inverse)
                "CategoryTheory.iso_inv",     // inverse of isomorphism
                "CategoryTheory.iso_hom_inv", // f ≫ f⁻¹ = id
                "CategoryTheory.iso_inv_hom", // f⁻¹ ≫ f = id
                "CategoryTheory.Section",     // right inverse (s ≫ f = id)
                "CategoryTheory.Retraction",  // left inverse (f ≫ r = id)
                "CategoryTheory.SplitMono",   // mono with retraction
                "CategoryTheory.SplitEpi",    // epi with section
                // ================================================================
                // Special Objects
                // ================================================================
                "CategoryTheory.Initial", // initial object (unique morphism to any)
                "CategoryTheory.Terminal", // terminal object (unique morphism from any)
                "CategoryTheory.ZeroObject", // zero object (both initial and terminal)
                "CategoryTheory.initial_unique", // morphism from initial is unique
                "CategoryTheory.terminal_unique", // morphism to terminal is unique
                // ================================================================
                // Functors
                // ================================================================
                "CategoryTheory.Functor", // Functor C D - functor between categories
                "CategoryTheory.Functor.obj", // F.obj : C → D - object mapping
                "CategoryTheory.Functor.map", // F.map : Hom X Y → Hom (F.obj X) (F.obj Y)
                "CategoryTheory.Functor.map_id", // F.map id = id
                "CategoryTheory.Functor.map_comp", // F.map (f ≫ g) = F.map f ≫ F.map g
                "CategoryTheory.Functor.comp", // G ∘ F - functor composition
                "CategoryTheory.Functor.id", // identity functor
                // ================================================================
                // Functor Properties
                // ================================================================
                "CategoryTheory.Faithful", // F is faithful (injective on homs)
                "CategoryTheory.Full",     // F is full (surjective on homs)
                "CategoryTheory.FullyFaithful", // F is fully faithful
                "CategoryTheory.Essentially_Surjective", // essentially surjective
                "CategoryTheory.Equivalence", // equivalence of categories
                "CategoryTheory.equiv_inverse", // quasi-inverse functor
                // ================================================================
                // Natural Transformations
                // ================================================================
                "CategoryTheory.NatTrans", // NatTrans F G - natural transformation
                "CategoryTheory.NatTrans.app", // α.app X : F.obj X ⟶ G.obj X
                "CategoryTheory.NatTrans.naturality", // naturality square commutes
                "CategoryTheory.NatTrans.id", // identity natural transformation
                "CategoryTheory.NatTrans.vcomp", // vertical composition
                "CategoryTheory.NatTrans.hcomp", // horizontal composition
                "CategoryTheory.NatIso",   // natural isomorphism
                // ================================================================
                // Adjunctions
                // ================================================================
                "CategoryTheory.Adjunction",        // L ⊣ R - adjunction
                "CategoryTheory.Adjunction.unit",   // η : Id → R ∘ L
                "CategoryTheory.Adjunction.counit", // ε : L ∘ R → Id
                "CategoryTheory.Adjunction.homEquiv", // Hom(L X, Y) ≅ Hom(X, R Y)
                "CategoryTheory.triangle_left",     // (ε L) ∘ (L η) = id
                "CategoryTheory.triangle_right",    // (R ε) ∘ (η R) = id
                "CategoryTheory.adjoint_unique",    // right adjoint is unique up to iso
                // ================================================================
                // Limits
                // ================================================================
                "CategoryTheory.Cone",            // cone over a diagram
                "CategoryTheory.Cone.pt",         // apex of cone
                "CategoryTheory.Limit",           // limit of a diagram
                "CategoryTheory.Limit.cone",      // limiting cone
                "CategoryTheory.Limit.lift",      // universal property
                "CategoryTheory.Limit.fac",       // factorization through limit
                "CategoryTheory.Limit.unique",    // uniqueness of factorization
                "CategoryTheory.HasLimits",       // category has all limits
                "CategoryTheory.HasFiniteLimits", // has finite limits
                // ================================================================
                // Products and Equalizers
                // ================================================================
                "CategoryTheory.Product",      // X × Y - categorical product
                "CategoryTheory.product_fst",  // π₁ : X × Y → X
                "CategoryTheory.product_snd",  // π₂ : X × Y → Y
                "CategoryTheory.product_lift", // universal property
                "CategoryTheory.Equalizer",    // equalizer of f, g
                "CategoryTheory.equalizer_fork", // e : E → X with f ∘ e = g ∘ e
                "CategoryTheory.Pullback",     // pullback/fiber product
                "CategoryTheory.pullback_fst", // first projection
                "CategoryTheory.pullback_snd", // second projection
                "CategoryTheory.pullback_condition", // commutativity condition
                // ================================================================
                // Colimits
                // ================================================================
                "CategoryTheory.Cocone",            // cocone under a diagram
                "CategoryTheory.Colimit",           // colimit of a diagram
                "CategoryTheory.Colimit.cocone",    // colimiting cocone
                "CategoryTheory.Colimit.desc",      // universal property
                "CategoryTheory.HasColimits",       // category has all colimits
                "CategoryTheory.HasFiniteColimits", // has finite colimits
                // ================================================================
                // Coproducts and Coequalizers
                // ================================================================
                "CategoryTheory.Coproduct", // X ⊔ Y - categorical coproduct
                "CategoryTheory.coproduct_inl", // ι₁ : X → X ⊔ Y
                "CategoryTheory.coproduct_inr", // ι₂ : Y → X ⊔ Y
                "CategoryTheory.coproduct_desc", // universal property
                "CategoryTheory.Coequalizer", // coequalizer of f, g
                "CategoryTheory.Pushout",   // pushout/amalgamated sum
                // ================================================================
                // Monads
                // ================================================================
                "CategoryTheory.Monad",            // monad on a category
                "CategoryTheory.Monad.T",          // underlying endofunctor T
                "CategoryTheory.Monad.η",          // unit η : Id → T
                "CategoryTheory.Monad.μ",          // multiplication μ : T² → T
                "CategoryTheory.Monad.assoc",      // μ ∘ Tμ = μ ∘ μT (associativity)
                "CategoryTheory.Monad.left_unit",  // μ ∘ ηT = id
                "CategoryTheory.Monad.right_unit", // μ ∘ Tη = id
                "CategoryTheory.Monad.Algebra",    // Eilenberg-Moore algebra
                "CategoryTheory.Kleisli",          // Kleisli category
                // ================================================================
                // Comonads
                // ================================================================
                "CategoryTheory.Comonad",   // comonad on a category
                "CategoryTheory.Comonad.W", // underlying endofunctor W
                "CategoryTheory.Comonad.ε", // counit ε : W → Id
                "CategoryTheory.Comonad.δ", // comultiplication δ : W → W²
                "CategoryTheory.Coalgebra", // coalgebra for a comonad
                // ================================================================
                // Yoneda Lemma
                // ================================================================
                "CategoryTheory.yoneda", // Yoneda embedding y : C → [C^op, Set]
                "CategoryTheory.yoneda_obj", // y(X) = Hom(-, X)
                "CategoryTheory.yoneda_map", // y(f) = - ≫ f
                "CategoryTheory.yoneda_faithful", // Yoneda is faithful
                "CategoryTheory.yoneda_full", // Yoneda is full
                "CategoryTheory.yoneda_lemma", // Nat(y(X), F) ≅ F(X)
                "CategoryTheory.Representable", // representable functor
                "CategoryTheory.representing_object", // object representing functor
                // ================================================================
                // Presheaves
                // ================================================================
                "CategoryTheory.Presheaf", // presheaf = functor C^op → Set
                "CategoryTheory.Presheaf.restrict", // restriction along morphism
                "CategoryTheory.Presheaf.sections", // sections over an object
                // ================================================================
                // Comma Categories
                // ================================================================
                "CategoryTheory.Comma",   // comma category (F ↓ G)
                "CategoryTheory.Slice",   // slice category C/X
                "CategoryTheory.Coslice", // coslice category X/C
                "CategoryTheory.Arrow",   // arrow category (morphisms as objects)
                // ================================================================
                // Kan Extensions
                // ================================================================
                "CategoryTheory.LeftKanExtension", // left Kan extension Lan_F G
                "CategoryTheory.RightKanExtension", // right Kan extension Ran_F G
                "CategoryTheory.kan_universal",    // universal property of Kan extension
                "CategoryTheory.pointwise_kan",    // pointwise Kan extension
                // ================================================================
                // Abelian Categories
                // ================================================================
                "CategoryTheory.Preadditive", // category enriched over Ab
                "CategoryTheory.Additive",    // additive category (biproducts)
                "CategoryTheory.Abelian",     // abelian category
                "CategoryTheory.Kernel",      // kernel of morphism
                "CategoryTheory.Cokernel",    // cokernel of morphism
                "CategoryTheory.Image",       // image of morphism
                "CategoryTheory.Coimage",     // coimage of morphism
                "CategoryTheory.Exact",       // exact sequence
                "CategoryTheory.ShortExact",  // short exact sequence
                // ================================================================
                // Derived Functors
                // ================================================================
                "CategoryTheory.LeftDerived",  // left derived functor
                "CategoryTheory.RightDerived", // right derived functor
                "CategoryTheory.Projective",   // projective object
                "CategoryTheory.Injective",    // injective object
                "CategoryTheory.Resolution",   // resolution of an object
                // ================================================================
                // Enriched Categories
                // ================================================================
                "CategoryTheory.Enriched",        // V-enriched category
                "CategoryTheory.EnrichedFunctor", // V-functor
                "CategoryTheory.EnrichedNat",     // V-natural transformation
                // ================================================================
                // 2-Categories
                // ================================================================
                "CategoryTheory.Bicategory", // bicategory (weak 2-category)
                "CategoryTheory.TwoMorphism", // 2-morphism (morphism between morphisms)
                "CategoryTheory.horizontal_comp_2", // horizontal composition
                "CategoryTheory.vertical_comp_2", // vertical composition
                "CategoryTheory.interchange", // interchange law
                // ================================================================
                // Important Examples
                // ================================================================
                "CategoryTheory.TypeCat", // category of types (Set)
                "CategoryTheory.Grp",     // category of groups
                "CategoryTheory.Ring_",   // category of rings
                "CategoryTheory.Module_", // category of R-modules
                "CategoryTheory.Top",     // category of topological spaces
                "CategoryTheory.forget",  // forgetful functor
                "CategoryTheory.free",    // free functor
            ],
            &[u.clone(), v.clone()],
            &type_u,
        )?;

        self.category_theory_init = true;
        Ok(())
    }

    /// Check if CategoryTheory has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_category_theory` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_category_theory(&self) -> bool {
        self.category_theory_init
    }
}
