// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algebraic geometry structures for Environment
//!
//! This module provides a compact collection of algebraic geometry axioms:
//! - Affine and projective varieties
//! - Schemes and morphisms of schemes
//! - Sheaves and cohomology
//! - Divisors and line bundles
//! - Algebraic curves and surfaces
//! - Intersection theory and Chern classes

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize AlgebraicGeometry module
    ///
    /// Algebraic geometry studies zeros of polynomial equations using
    /// geometric and algebraic methods. It unifies algebra, geometry,
    /// and number theory through the language of schemes.
    ///
    /// This module provides axioms for:
    /// - Varieties: affine, projective, quasi-projective
    /// - Schemes: affine, projective, general schemes
    /// - Morphisms: proper, flat, smooth, étale
    /// - Sheaves: coherent, quasi-coherent, locally free
    /// - Divisors and line bundles
    /// - Cohomology: sheaf, de Rham, étale
    /// - Intersection theory
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.algebraic_geometry_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_algebraic_geometry(&mut self) -> Result<(), EnvError> {
        if self.algebraic_geometry_init {
            return Ok(());
        }

        // Dependencies
        self.init_category_theory()?;
        self.init_homological_algebra()?;
        self.init_topology_scheme()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Algebraic geometry constants
        for name in &[
            // ================================================================
            // Affine varieties
            // ================================================================
            "AlgebraicGeometry.AffineVariety", // affine algebraic variety
            "AlgebraicGeometry.AffineSpace",   // affine n-space A^n
            "AlgebraicGeometry.CoordinateRing", // coordinate ring k[V]
            "AlgebraicGeometry.RadicalIdeal",  // radical ideals
            "AlgebraicGeometry.VanishingIdeal", // I(V) vanishing ideal
            "AlgebraicGeometry.ZeroLocus",     // V(I) zero locus
            "AlgebraicGeometry.Nullstellensatz", // Hilbert Nullstellensatz
            "AlgebraicGeometry.IrreducibleVariety", // irreducible varieties
            "AlgebraicGeometry.AffineHypersurface", // hypersurface in A^n
            "AlgebraicGeometry.AffineCurve",   // affine curve
            // ================================================================
            // Projective varieties
            // ================================================================
            "AlgebraicGeometry.ProjectiveVariety", // projective variety
            "AlgebraicGeometry.ProjectiveSpace",   // projective n-space P^n
            "AlgebraicGeometry.HomogeneousCoordinate", // homogeneous coordinates
            "AlgebraicGeometry.HomogeneousIdeal",  // homogeneous ideals
            "AlgebraicGeometry.ProjectiveHypersurface", // hypersurface in P^n
            "AlgebraicGeometry.ProjectiveCurve",   // projective curve
            "AlgebraicGeometry.ProjectiveClosure", // projective closure
            "AlgebraicGeometry.VeroneseEmbedding", // Veronese embedding
            "AlgebraicGeometry.SegreEmbedding",    // Segre embedding
            "AlgebraicGeometry.GrassmannVariety",  // Grassmannian Gr(k,n)
            "AlgebraicGeometry.FlagVariety",       // flag varieties
            "AlgebraicGeometry.QuadricHypersurface", // quadric hypersurfaces
            // ================================================================
            // Quasi-projective varieties
            // ================================================================
            "AlgebraicGeometry.QuasiProjectiveVariety", // quasi-projective variety
            "AlgebraicGeometry.OpenSubvariety",         // open subvarieties
            "AlgebraicGeometry.ClosedSubvariety",       // closed subvarieties
            "AlgebraicGeometry.LocallyClosedSubvariety", // locally closed
            // ================================================================
            // Dimension theory
            // ================================================================
            "AlgebraicGeometry.Dimension",      // dimension of variety
            "AlgebraicGeometry.Codimension",    // codimension
            "AlgebraicGeometry.KrullDimension", // Krull dimension
            "AlgebraicGeometry.TranscendenceDegree", // transcendence degree
            "AlgebraicGeometry.DimensionFormula", // dimension of fibers
            "AlgebraicGeometry.Equidimensional", // equidimensional varieties
            // ================================================================
            // Morphisms of varieties
            // ================================================================
            "AlgebraicGeometry.RegularMap", // regular/morphism of varieties
            "AlgebraicGeometry.RationalMap", // rational map
            "AlgebraicGeometry.BirationalMap", // birational equivalence
            "AlgebraicGeometry.DominantMorphism", // dominant morphism
            "AlgebraicGeometry.FiniteMorphism", // finite morphism
            "AlgebraicGeometry.ClosedImmersion", // closed immersion
            "AlgebraicGeometry.OpenImmersion", // open immersion
            "AlgebraicGeometry.Embedding",  // embedding (immersion)
            "AlgebraicGeometry.Isomorphism", // isomorphism of varieties
            // ================================================================
            // Schemes - basic
            // ================================================================
            "AlgebraicGeometry.Scheme",              // scheme
            "AlgebraicGeometry.AffineScheme",        // Spec R
            "AlgebraicGeometry.StructureSheaf",      // O_X structure sheaf
            "AlgebraicGeometry.LocalRing",           // local ring O_{X,x}
            "AlgebraicGeometry.ResidueField",        // residue field k(x)
            "AlgebraicGeometry.FunctionField",       // function field K(X)
            "AlgebraicGeometry.SchemePoint",         // points of schemes
            "AlgebraicGeometry.GenericPoint",        // generic point
            "AlgebraicGeometry.ClosedPoint",         // closed points
            "AlgebraicGeometry.SpecializationOrder", // specialization order
            // ================================================================
            // Schemes - types
            // ================================================================
            "AlgebraicGeometry.NoetherianScheme", // Noetherian scheme
            "AlgebraicGeometry.ReducedScheme",    // reduced scheme
            "AlgebraicGeometry.IntegralScheme",   // integral scheme
            "AlgebraicGeometry.NormalScheme",     // normal scheme
            "AlgebraicGeometry.RegularScheme",    // regular scheme
            "AlgebraicGeometry.SmoothScheme",     // smooth scheme
            "AlgebraicGeometry.SingularLocus",    // singular locus
            "AlgebraicGeometry.NormalizationScheme", // normalization
            // ================================================================
            // Scheme morphisms - basic
            // ================================================================
            "AlgebraicGeometry.SchemeMorphism", // morphism of schemes
            "AlgebraicGeometry.AffineOpenCover", // affine open cover
            "AlgebraicGeometry.BaseChange",     // base change
            "AlgebraicGeometry.FiberProduct",   // fiber product X ×_S Y
            "AlgebraicGeometry.Fiber",          // fiber of morphism
            "AlgebraicGeometry.Image",          // scheme-theoretic image
            "AlgebraicGeometry.StructuralMorphism", // structure morphism X → S
            // ================================================================
            // Scheme morphisms - properties
            // ================================================================
            "AlgebraicGeometry.QuasiCompactMorphism", // quasi-compact
            "AlgebraicGeometry.QuasiSeparatedMorphism", // quasi-separated
            "AlgebraicGeometry.SeparatedMorphism",    // separated morphism
            "AlgebraicGeometry.ProperMorphism",       // proper morphism
            "AlgebraicGeometry.ProjectiveMorphism",   // projective morphism
            "AlgebraicGeometry.QuasiProjectiveMorphism", // quasi-projective
            "AlgebraicGeometry.FlatMorphism",         // flat morphism
            "AlgebraicGeometry.SmoothMorphism",       // smooth morphism
            "AlgebraicGeometry.EtaleMorphism",        // étale morphism
            "AlgebraicGeometry.UnramifiedMorphism",   // unramified morphism
            "AlgebraicGeometry.FiniteTypeMorphism",   // finite type
            "AlgebraicGeometry.LocallyFiniteType",    // locally of finite type
            "AlgebraicGeometry.FinitePresentation",   // finite presentation
            "AlgebraicGeometry.AffinelyMorphism",     // affine morphism
            // ================================================================
            // Projective schemes
            // ================================================================
            "AlgebraicGeometry.Proj",                // Proj of graded ring
            "AlgebraicGeometry.ProjectiveScheme",    // projective scheme
            "AlgebraicGeometry.TwistingSheaf",       // O(1) twisting sheaf
            "AlgebraicGeometry.AmpleSheaf",          // ample line bundle
            "AlgebraicGeometry.VeryAmple",           // very ample
            "AlgebraicGeometry.SerreTwist",          // Serre twist O(n)
            "AlgebraicGeometry.LinearSystem",        // linear system |D|
            "AlgebraicGeometry.ProjectiveEmbedding", // projective embedding
            // ================================================================
            // Sheaves on schemes
            // ================================================================
            "AlgebraicGeometry.Sheaf",    // sheaf on topological space
            "AlgebraicGeometry.Presheaf", // presheaf
            "AlgebraicGeometry.Sheafification", // sheafification functor
            "AlgebraicGeometry.SheafMorphism", // morphism of sheaves
            "AlgebraicGeometry.StalkSheaf", // stalk of sheaf
            "AlgebraicGeometry.SectionsGlobal", // global sections Γ(X, F)
            "AlgebraicGeometry.SectionsLocal", // sections over open U
            "AlgebraicGeometry.Restriction", // restriction map
            // ================================================================
            // Coherent and quasi-coherent sheaves
            // ================================================================
            "AlgebraicGeometry.QuasiCoherentSheaf", // quasi-coherent sheaf
            "AlgebraicGeometry.CoherentSheaf",      // coherent sheaf
            "AlgebraicGeometry.LocallyFreeSheaf",   // locally free sheaf
            "AlgebraicGeometry.VectorBundle",       // vector bundle
            "AlgebraicGeometry.LineBundle",         // line bundle
            "AlgebraicGeometry.TangentBundle",      // tangent bundle
            "AlgebraicGeometry.CotangentBundle",    // cotangent bundle
            "AlgebraicGeometry.CanonicalBundle",    // canonical bundle ω_X
            "AlgebraicGeometry.Tilde",              // tilde construction M̃
            "AlgebraicGeometry.PushforwardSheaf",   // f_* pushforward
            "AlgebraicGeometry.PullbackSheaf",      // f^* pullback
            "AlgebraicGeometry.IdealSheaf",         // ideal sheaf
            "AlgebraicGeometry.TensorProductSheaf", // tensor product of sheaves
            "AlgebraicGeometry.HomSheaf",           // Hom sheaf
            "AlgebraicGeometry.DualSheaf",          // dual sheaf F^∨
            // ================================================================
            // Divisors
            // ================================================================
            "AlgebraicGeometry.WeilDivisor",          // Weil divisor
            "AlgebraicGeometry.CartierDivisor",       // Cartier divisor
            "AlgebraicGeometry.PrincipalDivisor",     // principal divisor (f)
            "AlgebraicGeometry.EffectiveDivisor",     // effective divisor
            "AlgebraicGeometry.DivisorClass",         // divisor class Cl(X)
            "AlgebraicGeometry.PicardGroup",          // Picard group Pic(X)
            "AlgebraicGeometry.DivisorLinearEquiv",   // linear equivalence
            "AlgebraicGeometry.DivisorNumerEquiv",    // numerical equivalence
            "AlgebraicGeometry.DivisorAlgEquiv",      // algebraic equivalence
            "AlgebraicGeometry.NefDivisor",           // nef divisor
            "AlgebraicGeometry.BigDivisor",           // big divisor
            "AlgebraicGeometry.SampleDivisor",        // sample divisor
            "AlgebraicGeometry.AnticanonicalDivisor", // anti-canonical -K_X
            // ================================================================
            // Sheaf cohomology
            // ================================================================
            "AlgebraicGeometry.SheafCohomology",     // H^i(X, F)
            "AlgebraicGeometry.CechCohomology",      // Čech cohomology
            "AlgebraicGeometry.SheafExt",            // Ext^i(F, G)
            "AlgebraicGeometry.HigherDirectImage",   // R^i f_*
            "AlgebraicGeometry.LeraySpectralSeq",    // Leray spectral sequence
            "AlgebraicGeometry.SheafEulerChar",      // Euler characteristic χ(F)
            "AlgebraicGeometry.HilbertPolynomial",   // Hilbert polynomial
            "AlgebraicGeometry.VanishingTheorem",    // vanishing theorems
            "AlgebraicGeometry.KodairaVanishing",    // Kodaira vanishing
            "AlgebraicGeometry.SerreVanishing",      // Serre vanishing
            "AlgebraicGeometry.SerreDuality",        // Serre duality
            "AlgebraicGeometry.GrothendieckDuality", // Grothendieck duality
            // ================================================================
            // Algebraic curves
            // ================================================================
            "AlgebraicGeometry.Curve",                 // algebraic curve
            "AlgebraicGeometry.SmoothCurve",           // smooth curve
            "AlgebraicGeometry.Genus",                 // genus g(C)
            "AlgebraicGeometry.RiemannRoch",           // Riemann-Roch theorem
            "AlgebraicGeometry.RiemannHurwitz",        // Riemann-Hurwitz formula
            "AlgebraicGeometry.CanonicalDivisorCurve", // canonical divisor on curve
            "AlgebraicGeometry.Jacobian",              // Jacobian variety Jac(C)
            "AlgebraicGeometry.AbelJacobiMap",         // Abel-Jacobi map
            "AlgebraicGeometry.AbelianVariety",        // abelian variety
            "AlgebraicGeometry.ModuliCurve",           // moduli of curves M_g
            "AlgebraicGeometry.HyperellipticCurve",    // hyperelliptic curves
            "AlgebraicGeometry.PlaneCurve",            // plane curves
            "AlgebraicGeometry.Gonality",              // gonality
            "AlgebraicGeometry.BrillNoether",          // Brill-Noether theory
            // ================================================================
            // Algebraic surfaces
            // ================================================================
            "AlgebraicGeometry.Surface",          // algebraic surface
            "AlgebraicGeometry.SmoothSurface",    // smooth surface
            "AlgebraicGeometry.MinimalModel",     // minimal model
            "AlgebraicGeometry.KodairaDimension", // Kodaira dimension κ
            "AlgebraicGeometry.SurfaceClassification", // Enriques-Kodaira classification
            "AlgebraicGeometry.RuledSurface",     // ruled surface
            "AlgebraicGeometry.RationalSurface",  // rational surface
            "AlgebraicGeometry.K3Surface",        // K3 surface
            "AlgebraicGeometry.EnriquesSurface",  // Enriques surface
            "AlgebraicGeometry.AbelianSurface",   // abelian surface
            "AlgebraicGeometry.GeneralTypeSurface", // surface of general type
            "AlgebraicGeometry.NoetherFormula",   // Noether formula
            "AlgebraicGeometry.HodgeIndex",       // Hodge index theorem
            // ================================================================
            // Intersection theory
            // ================================================================
            "AlgebraicGeometry.IntersectionNumber", // intersection number
            "AlgebraicGeometry.IntersectionProduct", // intersection product
            "AlgebraicGeometry.ChowRing",           // Chow ring A(X)
            "AlgebraicGeometry.ChowGroup",          // Chow group A_k(X)
            "AlgebraicGeometry.RationalEquivalence", // rational equivalence
            "AlgebraicGeometry.ProperPushforward",  // proper pushforward
            "AlgebraicGeometry.FlatPullback",       // flat pullback
            "AlgebraicGeometry.ExcessIntersection", // excess intersection
            "AlgebraicGeometry.BezoutTheorem",      // Bézout's theorem
            "AlgebraicGeometry.ProjectionFormula",  // projection formula
            "AlgebraicGeometry.MovingLemma",        // moving lemma
            // ================================================================
            // Characteristic classes
            // ================================================================
            "AlgebraicGeometry.ChernClass",      // Chern classes c_i
            "AlgebraicGeometry.TotalChernClass", // total Chern class c(E)
            "AlgebraicGeometry.ChernCharacter",  // Chern character ch(E)
            "AlgebraicGeometry.ToddClass",       // Todd class td(E)
            "AlgebraicGeometry.EulerClass",      // Euler class
            "AlgebraicGeometry.SegrepClass",     // Segre classes s_i
            "AlgebraicGeometry.GRR",             // Grothendieck-Riemann-Roch
            "AlgebraicGeometry.HRR",             // Hirzebruch-Riemann-Roch
            // ================================================================
            // Blowups and birational geometry
            // ================================================================
            "AlgebraicGeometry.Blowup",              // blowup at subscheme
            "AlgebraicGeometry.ExceptionalDivisor",  // exceptional divisor
            "AlgebraicGeometry.StrictTransform",     // strict transform
            "AlgebraicGeometry.Resolution",          // resolution of singularities
            "AlgebraicGeometry.Hironaka",            // Hironaka's theorem
            "AlgebraicGeometry.BirationalEquiv",     // birational equivalence
            "AlgebraicGeometry.BiratInvariant",      // birational invariant
            "AlgebraicGeometry.MinimalModelProgram", // MMP
            "AlgebraicGeometry.Flip",                // flip
            "AlgebraicGeometry.Flop",                // flop
            "AlgebraicGeometry.Contraction",         // extremal contraction
            "AlgebraicGeometry.MoriCone",            // cone of curves NE(X)
            "AlgebraicGeometry.NefCone",             // nef cone Nef(X)
            // ================================================================
            // Moduli theory
            // ================================================================
            "AlgebraicGeometry.ModuliSpace",         // moduli space
            "AlgebraicGeometry.ModuliFunctor",       // moduli functor
            "AlgebraicGeometry.FineModuli",          // fine moduli space
            "AlgebraicGeometry.CoarseModuli",        // coarse moduli space
            "AlgebraicGeometry.UniversalFamily",     // universal family
            "AlgebraicGeometry.HilbertScheme",       // Hilbert scheme Hilb(X)
            "AlgebraicGeometry.QuotScheme",          // Quot scheme
            "AlgebraicGeometry.ModuliVectorBundles", // moduli of vector bundles
            "AlgebraicGeometry.GeometricInvariantTheory", // GIT
            "AlgebraicGeometry.Stability",           // stability condition
            "AlgebraicGeometry.SemistablePoint",     // semistable point
            "AlgebraicGeometry.StablePoint",         // stable point
            "AlgebraicGeometry.GITQuotient",         // GIT quotient X//G
            // ================================================================
            // Étale topology and cohomology
            // ================================================================
            "AlgebraicGeometry.EtaleCover",        // étale cover
            "AlgebraicGeometry.EtaleSite",         // étale site
            "AlgebraicGeometry.EtaleSheaf",        // étale sheaf
            "AlgebraicGeometry.EtaleCohomology",   // H^i_et(X, F)
            "AlgebraicGeometry.LadicCohomology",   // l-adic cohomology
            "AlgebraicGeometry.FrobeniusAction",   // Frobenius action
            "AlgebraicGeometry.WeilConjectures",   // Weil conjectures
            "AlgebraicGeometry.ZetaFunction",      // zeta function Z(X, t)
            "AlgebraicGeometry.ComparisonTheorem", // comparison theorem
            "AlgebraicGeometry.ProperBaseChange",  // proper base change
            "AlgebraicGeometry.SmoothBaseChange",  // smooth base change
            "AlgebraicGeometry.Poincare",          // Poincaré duality
            // ================================================================
            // Derived algebraic geometry
            // ================================================================
            "AlgebraicGeometry.DerivedScheme",    // derived scheme
            "AlgebraicGeometry.DerivedStack",     // derived stack
            "AlgebraicGeometry.CotangentComplex", // cotangent complex L_X
            "AlgebraicGeometry.DerivedCategory",  // D(X) derived category
            "AlgebraicGeometry.PerfectComplex",   // perfect complex
            "AlgebraicGeometry.DerivedTensor",    // derived tensor product
            "AlgebraicGeometry.DerivedHom",       // RHom
            // ================================================================
            // Stacks
            // ================================================================
            "AlgebraicGeometry.AlgebraicStack", // algebraic stack
            "AlgebraicGeometry.DeligneMumfordStack", // DM stack
            "AlgebraicGeometry.ArtinStack",     // Artin stack
            "AlgebraicGeometry.Gerbe",          // gerbe
            "AlgebraicGeometry.QuotientStack",  // quotient stack [X/G]
            "AlgebraicGeometry.InertiaStack",   // inertia stack
            "AlgebraicGeometry.CoarseModuliStack", // coarse moduli space of stack
            // ================================================================
            // Toric geometry
            // ================================================================
            "AlgebraicGeometry.ToricVariety",  // toric variety
            "AlgebraicGeometry.Fan",           // fan
            "AlgebraicGeometry.Cone",          // cone in lattice
            "AlgebraicGeometry.Polytope",      // polytope
            "AlgebraicGeometry.TorusDivisor",  // T-invariant divisor
            "AlgebraicGeometry.ToricMorphism", // toric morphism
            "AlgebraicGeometry.OrbitCone",     // orbit-cone correspondence
            // ================================================================
            // Special varieties
            // ================================================================
            "AlgebraicGeometry.CalabiYau",   // Calabi-Yau manifold
            "AlgebraicGeometry.FanoVariety", // Fano variety
            "AlgebraicGeometry.GeneralTypeVariety", // variety of general type
            "AlgebraicGeometry.RationalVariety", // rational variety
            "AlgebraicGeometry.UnirationalVariety", // unirational variety
            "AlgebraicGeometry.RationallyConnected", // rationally connected
            "AlgebraicGeometry.HyperkahlerVariety", // hyperkähler variety
            // ================================================================
            // Motives
            // ================================================================
            "AlgebraicGeometry.Motive",            // motive
            "AlgebraicGeometry.ChowMotive",        // Chow motive
            "AlgebraicGeometry.PureMotive",        // pure motive
            "AlgebraicGeometry.MixedMotive",       // mixed motive
            "AlgebraicGeometry.MotivicCohomology", // motivic cohomology
            "AlgebraicGeometry.TateMotive",        // Tate motive
            "AlgebraicGeometry.LefschtezMotive",   // Lefschetz motive
            "AlgebraicGeometry.MotiveRealisation", // realization functor
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone(), v.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.algebraic_geometry_init = true;
        Ok(())
    }

    /// Check if AlgebraicGeometry has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.algebraic_geometry_init == true`
    pub(crate) fn has_algebraic_geometry(&self) -> bool {
        self.algebraic_geometry_init
    }
}
