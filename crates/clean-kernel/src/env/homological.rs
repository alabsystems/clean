// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Homological algebra structures for Environment
//!
//! This module contains homological algebra initialization:
//! - ChainComplex: complexes of objects with differentials
//! - Homology: derived functors measuring "failure of exactness"
//! - DerivedCategory: localization of chain complexes at quasi-isomorphisms
//! - Spectral sequences: computational tools for homology
//! - Ext/Tor: fundamental derived functors

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize HomologicalAlgebra module
    ///
    /// Homological algebra is the study of homology in a general algebraic
    /// setting. It is a tool used in many branches of mathematics:
    /// - Algebraic topology (singular/cellular homology)
    /// - Algebraic geometry (sheaf cohomology)
    /// - Group theory (group cohomology)
    /// - Commutative algebra (Ext, Tor)
    /// - Representation theory (Lie algebra cohomology)
    ///
    /// This module provides axioms for:
    /// - Chain complexes and their morphisms
    /// - Homology and cohomology functors
    /// - Derived categories and triangulated structure
    /// - Spectral sequences for computation
    /// - Classical derived functors (Ext, Tor, etc.)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.homological_algebra_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_homological_algebra(&mut self) -> Result<(), EnvError> {
        if self.homological_algebra_init {
            return Ok(());
        }

        // Dependencies
        self.init_category_theory()?;
        self.init_algebra_linear()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Homological algebra constants
        for name in &[
            // ================================================================
            // Chain Complexes
            // ================================================================
            "HomologicalAlgebra.ChainComplex", // chain complex C_• with d_n : C_n → C_{n-1}
            "HomologicalAlgebra.CochainComplex", // cochain complex C^• with d^n : C^n → C^{n+1}
            "HomologicalAlgebra.differential", // d : C_n → C_{n-1} (boundary map)
            "HomologicalAlgebra.d_squared_zero", // d ∘ d = 0 (fundamental property)
            "HomologicalAlgebra.ChainComplex.component", // C_n - the n-th component
            "HomologicalAlgebra.BoundedAbove", // complex with C_n = 0 for n >> 0
            "HomologicalAlgebra.BoundedBelow", // complex with C_n = 0 for n << 0
            "HomologicalAlgebra.Bounded",      // bounded both above and below
            // ================================================================
            // Chain Maps
            // ================================================================
            "HomologicalAlgebra.ChainMap", // morphism f : C_• → D_• of chain complexes
            "HomologicalAlgebra.ChainMap.component", // f_n : C_n → D_n
            "HomologicalAlgebra.ChainMap.comm", // f_{n-1} ∘ d_C = d_D ∘ f_n
            "HomologicalAlgebra.ChainMap.id", // identity chain map
            "HomologicalAlgebra.ChainMap.comp", // composition of chain maps
            // ================================================================
            // Chain Homotopy
            // ================================================================
            "HomologicalAlgebra.ChainHomotopy", // homotopy h : f ≃ g between chain maps
            "HomologicalAlgebra.homotopy_component", // h_n : C_n → D_{n+1}
            "HomologicalAlgebra.homotopy_formula", // f - g = d_D ∘ h + h ∘ d_C
            "HomologicalAlgebra.homotopy_equiv", // homotopy equivalence relation
            "HomologicalAlgebra.HomotopyEquiv", // homotopy equivalence C_• ≃_h D_•
            "HomologicalAlgebra.null_homotopic", // f is null-homotopic (≃ 0)
            // ================================================================
            // Homology
            // ================================================================
            "HomologicalAlgebra.Cycles",     // Z_n = ker(d_n) - cycles
            "HomologicalAlgebra.Boundaries", // B_n = im(d_{n+1}) - boundaries
            "HomologicalAlgebra.Homology",   // H_n = Z_n / B_n - n-th homology
            "HomologicalAlgebra.homology_functor", // H_n is a functor
            "HomologicalAlgebra.induced_map", // f_* : H_n(C) → H_n(D)
            "HomologicalAlgebra.homotopy_invariance", // homotopic maps induce same homology
            // ================================================================
            // Cohomology
            // ================================================================
            "HomologicalAlgebra.Cocycles", // Z^n = ker(d^n) - cocycles
            "HomologicalAlgebra.Coboundaries", // B^n = im(d^{n-1}) - coboundaries
            "HomologicalAlgebra.Cohomology", // H^n = Z^n / B^n - n-th cohomology
            // ================================================================
            // Short Exact Sequences
            // ================================================================
            "HomologicalAlgebra.ShortExact",      // 0 → A → B → C → 0
            "HomologicalAlgebra.ses_inject",      // A ↪ B is injective
            "HomologicalAlgebra.ses_surject",     // B ↠ C is surjective
            "HomologicalAlgebra.ses_exact",       // im(A → B) = ker(B → C)
            "HomologicalAlgebra.SplitShortExact", // split short exact sequence
            "HomologicalAlgebra.splitting_lemma", // split SES ↔ direct sum
            // ================================================================
            // Long Exact Sequences
            // ================================================================
            "HomologicalAlgebra.LongExactSequence", // ... → H_n(A) → H_n(B) → H_n(C) → H_{n-1}(A) → ...
            "HomologicalAlgebra.connecting_homomorphism", // δ : H_n(C) → H_{n-1}(A)
            "HomologicalAlgebra.snake_lemma",       // construction of connecting homomorphism
            "HomologicalAlgebra.les_exactness",     // LES is exact
            // ================================================================
            // Quasi-isomorphisms
            // ================================================================
            "HomologicalAlgebra.QuasiIsomorphism", // f : C_• → D_• inducing iso on H_*
            "HomologicalAlgebra.qis_comp",         // composition of quasi-isos
            "HomologicalAlgebra.qis_two_of_three", // 2-of-3 property
            // ================================================================
            // Derived Category
            // ================================================================
            "HomologicalAlgebra.DerivedCategory", // D(A) - derived category of A
            "HomologicalAlgebra.DboundedAbove",   // D^-(A) - bounded above
            "HomologicalAlgebra.DboundedBelow",   // D^+(A) - bounded below
            "HomologicalAlgebra.Dbounded",        // D^b(A) - bounded both
            "HomologicalAlgebra.localization",    // D(A) = K(A)[qis^{-1}]
            "HomologicalAlgebra.roof",            // morphism in D(A) as roof
            // ================================================================
            // Triangulated Structure
            // ================================================================
            "HomologicalAlgebra.DistinguishedTriangle", // A → B → C → A[1]
            "HomologicalAlgebra.shift",                 // [1] : D(A) → D(A) shift functor
            "HomologicalAlgebra.cone",                  // mapping cone C(f)
            "HomologicalAlgebra.cocone",                // mapping cocone
            "HomologicalAlgebra.triangle_rotation",     // rotation of triangles
            "HomologicalAlgebra.octahedral_axiom",      // TR4 - octahedral axiom
            // ================================================================
            // t-structures
            // ================================================================
            "HomologicalAlgebra.tStructure", // t-structure on triangulated category
            "HomologicalAlgebra.tStructure.Dle0", // D^{≤0} - objects in degrees ≤ 0
            "HomologicalAlgebra.tStructure.Dge0", // D^{≥0} - objects in degrees ≥ 0
            "HomologicalAlgebra.Heart",      // heart A ∩ D^{≤0} ∩ D^{≥0}
            "HomologicalAlgebra.truncation_le", // τ^{≤n} - truncation functor
            "HomologicalAlgebra.truncation_ge", // τ^{≥n} - truncation functor
            "HomologicalAlgebra.perverse",   // perverse t-structure
            // ================================================================
            // Projective/Injective Resolutions
            // ================================================================
            "HomologicalAlgebra.ProjectiveResolution", // P_• → M → 0
            "HomologicalAlgebra.InjectiveResolution",  // 0 → M → I^•
            "HomologicalAlgebra.resolution_exists",    // enough projectives/injectives
            "HomologicalAlgebra.resolution_unique",    // unique up to homotopy
            "HomologicalAlgebra.comparison_theorem",   // comparison of resolutions
            "HomologicalAlgebra.horseshoe_lemma",      // constructing resolutions
            // ================================================================
            // Ext Functor
            // ================================================================
            "HomologicalAlgebra.Ext",             // Ext^n(M, N) - extensions
            "HomologicalAlgebra.Ext.zero",        // Ext^0 = Hom
            "HomologicalAlgebra.Ext.les",         // long exact sequence for Ext
            "HomologicalAlgebra.Ext.bifunctor",   // Ext is bifunctor
            "HomologicalAlgebra.Ext.composition", // Yoneda product
            "HomologicalAlgebra.ext_vanishing",   // Ext^n = 0 for n > dim
            // ================================================================
            // Tor Functor
            // ================================================================
            "HomologicalAlgebra.Tor",           // Tor_n(M, N) - torsion
            "HomologicalAlgebra.Tor.zero",      // Tor_0 = ⊗
            "HomologicalAlgebra.Tor.les",       // long exact sequence for Tor
            "HomologicalAlgebra.Tor.symmetric", // Tor_n(M,N) ≅ Tor_n(N,M)
            "HomologicalAlgebra.flat_module",   // M is flat ↔ Tor_n(M,-) = 0
            // ================================================================
            // Homological Dimension
            // ================================================================
            "HomologicalAlgebra.ProjectiveDimension", // pd(M) - projective dimension
            "HomologicalAlgebra.InjectiveDimension",  // id(M) - injective dimension
            "HomologicalAlgebra.FlatDimension",       // fd(M) - flat dimension
            "HomologicalAlgebra.GlobalDimension",     // gl.dim(R) - global dimension
            "HomologicalAlgebra.dimension_bounds",    // dimension inequalities
            // ================================================================
            // Spectral Sequences
            // ================================================================
            "HomologicalAlgebra.SpectralSequence", // {E_r^{p,q}, d_r}
            "HomologicalAlgebra.ss_page",          // r-th page E_r
            "HomologicalAlgebra.ss_differential",  // d_r : E_r^{p,q} → E_r^{p+r,q-r+1}
            "HomologicalAlgebra.ss_convergence",   // E_∞^{p,q} ⇒ H^{p+q}
            "HomologicalAlgebra.ss_collapse",      // spectral sequence collapses
            "HomologicalAlgebra.filtration_ss",    // SS from filtration
            // ================================================================
            // Standard Spectral Sequences
            // ================================================================
            "HomologicalAlgebra.LeraySpectralSeq", // for fibrations
            "HomologicalAlgebra.GrothendieckSS",   // composition of derived functors
            "HomologicalAlgebra.HochschildSerre",  // for group extensions
            "HomologicalAlgebra.LyndonHS",         // Lyndon-Hochschild-Serre
            "HomologicalAlgebra.AdamsSpectralSeq", // for stable homotopy
            // ================================================================
            // Double Complexes
            // ================================================================
            "HomologicalAlgebra.DoubleComplex", // C_{p,q} with horizontal and vertical d
            "HomologicalAlgebra.TotalComplex",  // Tot(C) - total complex
            "HomologicalAlgebra.total_direct_sum", // Tot^⊕
            "HomologicalAlgebra.total_product", // Tot^∏
            "HomologicalAlgebra.acyclic_assembly", // acyclic assembly lemma
            // ================================================================
            // Derived Functors
            // ================================================================
            "HomologicalAlgebra.LeftDerived", // L^n F - left derived functor
            "HomologicalAlgebra.RightDerived", // R^n F - right derived functor
            "HomologicalAlgebra.DerivedTensor", // - ⊗^L - - derived tensor
            "HomologicalAlgebra.DerivedHom",  // RHom - derived Hom
            "HomologicalAlgebra.derived_comp", // composition of derived functors
            // ================================================================
            // Koszul Complex
            // ================================================================
            "HomologicalAlgebra.KoszulComplex",  // K(x_1,...,x_n)
            "HomologicalAlgebra.koszul_regular", // regular sequence ↔ H_i = 0
            "HomologicalAlgebra.depth",          // depth via Koszul homology
            "HomologicalAlgebra.cohen_macaulay", // Cohen-Macaulay property
            // ================================================================
            // Group Cohomology
            // ================================================================
            "HomologicalAlgebra.GroupCohomology", // H^n(G, M) - group cohomology
            "HomologicalAlgebra.BarResolution",   // bar resolution for groups
            "HomologicalAlgebra.cocycle_group",   // cocycle in group cohomology
            "HomologicalAlgebra.group_extension", // H^2 classifies extensions
            "HomologicalAlgebra.inflation",       // inflation map
            "HomologicalAlgebra.restriction",     // restriction map
            "HomologicalAlgebra.transfer",        // transfer/corestriction map
            // ================================================================
            // Lie Algebra Cohomology
            // ================================================================
            "HomologicalAlgebra.LieCohomology", // H^n(g, M) - Lie algebra cohomology
            "HomologicalAlgebra.ChevalleyEilenberg", // Chevalley-Eilenberg complex
            "HomologicalAlgebra.lie_deformation", // H^2 classifies deformations
            "HomologicalAlgebra.whitehead_lemmas", // Whitehead's lemmas
            // ================================================================
            // Hochschild Cohomology
            // ================================================================
            "HomologicalAlgebra.HochschildHomology", // HH_n(A, M)
            "HomologicalAlgebra.HochschildCohomology", // HH^n(A, M)
            "HomologicalAlgebra.HochschildComplex",  // bar complex for algebras
            "HomologicalAlgebra.deformation_theory", // HH^2 classifies deformations
            "HomologicalAlgebra.Gerstenhaber",       // Gerstenhaber bracket
            // ================================================================
            // Cyclic Homology
            // ================================================================
            "HomologicalAlgebra.CyclicHomology", // HC_n(A) - cyclic homology
            "HomologicalAlgebra.CyclicCohomology", // HC^n(A) - cyclic cohomology
            "HomologicalAlgebra.ConnesOperator", // B : HH_n → HH_{n+1}
            "HomologicalAlgebra.SBI_sequence",   // ... → HH → HC → HC[-2] → ...
            "HomologicalAlgebra.PeriodicCyclic", // HP_* - periodic cyclic
            "HomologicalAlgebra.NegativeCyclic", // HN_* - negative cyclic
            // ================================================================
            // A-infinity and DG Categories
            // ================================================================
            "HomologicalAlgebra.DGCategory", // differential graded category
            "HomologicalAlgebra.DGFunctor",  // DG functor
            "HomologicalAlgebra.DGModule",   // DG module over DG algebra
            "HomologicalAlgebra.AInfinityAlgebra", // A_∞ algebra
            "HomologicalAlgebra.AInfinityMorphism", // A_∞ morphism
            "HomologicalAlgebra.minimal_model", // minimal A_∞ model
            // ================================================================
            // Derived Categories - Advanced
            // ================================================================
            "HomologicalAlgebra.DerivedTensorProduct", // ⊗^L in D(A)
            "HomologicalAlgebra.DerivedHomFunctor",    // RHom in D(A)
            "HomologicalAlgebra.DualityFunctor",       // duality D : D^b(A)^op → D^b(A)
            "HomologicalAlgebra.SerreFunctor",         // Serre functor S
            "HomologicalAlgebra.TiltingObject",        // tilting object
            "HomologicalAlgebra.ExceptionalCollection", // exceptional collection
            // ================================================================
            // Sheaf Cohomology
            // ================================================================
            "HomologicalAlgebra.SheafCohomology", // H^n(X, F)
            "HomologicalAlgebra.CechCohomology",  // Čech cohomology
            "HomologicalAlgebra.cech_to_derived", // Čech → derived comparison
            "HomologicalAlgebra.hypercohomology", // ℍ^n(X, K^•) - hypercohomology
            "HomologicalAlgebra.Leray_sheaf",     // Leray spectral sequence
            // ================================================================
            // Grothendieck Duality
            // ================================================================
            "HomologicalAlgebra.DualizingComplex",    // ω^•
            "HomologicalAlgebra.GrothendieckDuality", // Rf_! ⊣ Rf^!
            "HomologicalAlgebra.LocalDuality",        // local duality theorem
            "HomologicalAlgebra.VerdierDuality",      // Verdier duality
            // ================================================================
            // Stability Conditions
            // ================================================================
            "HomologicalAlgebra.StabilityCondition", // Bridgeland stability
            "HomologicalAlgebra.central_charge",     // Z : K(D) → ℂ
            "HomologicalAlgebra.semistable",         // semistable objects
            "HomologicalAlgebra.HarderNarasimhan",   // HN filtration
            "HomologicalAlgebra.stability_manifold", // Stab(D) space
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone(), v.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.homological_algebra_init = true;
        Ok(())
    }

    /// Check if HomologicalAlgebra has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.homological_algebra_init == true`
    pub(crate) fn has_homological_algebra(&self) -> bool {
        self.homological_algebra_init
    }
}
