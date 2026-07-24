// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Number theory structures for Environment
//!
//! This module provides a compact collection of number-theoretic axioms:
//! - Primes and their distribution
//! - Modular arithmetic and local fields
//! - Algebraic number theory (ideals, class groups, units)
//! - Galois theory and class field theory
//! - Modular forms, elliptic curves, and L-functions
//! - Diophantine geometry and height theory

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize NumberTheory module
    ///
    /// Number theory sits at the crossroads of algebra, analysis, and geometry.
    /// This module captures major objects and conjectures used across the
    /// project, especially for arithmetic geometry and cryptography.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.number_theory_init == true`
    /// ENSURES: On success, required dependencies (`algebra_linear`, `category_theory`, `topology_scheme`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_number_theory(&mut self) -> Result<(), EnvError> {
        if self.number_theory_init {
            return Ok(());
        }

        // Dependencies
        self.init_algebra_linear()?;
        self.init_category_theory()?;
        self.init_topology_scheme()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Number theory constants
        for name in &[
            // ================================================================
            // Primes and distribution
            // ================================================================
            "NumberTheory.Prime",                       // prime numbers
            "NumberTheory.InfinitelyManyPrimes",        // Euclid's theorem
            "NumberTheory.PrimesArithmeticProgression", // Dirichlet theorem
            "NumberTheory.PrimesShortIntervals",        // primes in short intervals
            "NumberTheory.TwinPrimeConjecture",         // twin prime conjecture
            "NumberTheory.GoldbachConjecture",          // Goldbach conjecture
            "NumberTheory.CramersConjecture",           // Cramér conjecture
            "NumberTheory.GreenTao",                    // primes in long AP
            "NumberTheory.LinnikTheorem",               // bound on least prime in AP
            "NumberTheory.PrimeCounting",               // π(x) prime counting function
            "NumberTheory.PrimeNumberTheorem",          // π(x) ~ x / log x
            "NumberTheory.ChebyshevTheta",              // θ(x)
            "NumberTheory.ChebyshevPsi",                // ψ(x)
            "NumberTheory.BombieriVinogradov",          // average error term
            "NumberTheory.BrunTitchmarsh",              // Brun-Titchmarsh inequality
            "NumberTheory.MaynardTao",                  // bounded prime gaps
            "NumberTheory.SieveOfEratosthenes",         // classical sieve
            "NumberTheory.SelbergSieve",                // Selberg sieve
            "NumberTheory.LargeSieve",                  // large sieve inequality
            "NumberTheory.PrimeGaps",                   // bounds on prime gaps
            // ================================================================
            // Analytic number theory and L-functions
            // ================================================================
            "NumberTheory.RiemannZeta",                  // ζ(s)
            "NumberTheory.CompletedZeta",                // completed zeta Λ(s)
            "NumberTheory.RiemannHypothesis",            // RH conjecture
            "NumberTheory.GeneralizedRiemannHypothesis", // GRH conjecture
            "NumberTheory.LandauSiegelZero",             // exceptional zeros
            "NumberTheory.EulerProduct",                 // Euler product expansions
            "NumberTheory.FunctionalEquation",           // functional equations
            "NumberTheory.AnalyticContinuation",         // analytic continuation
            "NumberTheory.CriticalStrip",                // 0 < Re(s) < 1
            "NumberTheory.ZeroFreeRegion",               // zero-free regions
            "NumberTheory.SpecialValue",                 // special value formulas
            // ================================================================
            // Arithmetic functions and multiplicative theory
            // ================================================================
            "NumberTheory.MobiusMu",        // Möbius μ(n)
            "NumberTheory.LiouvilleLambda", // Liouville λ(n)
            "NumberTheory.VonMangoldt",     // Λ(n)
            "NumberTheory.DivisorFunction", // d_k(n)
            "NumberTheory.SigmaFunction",   // σ_k(n)
            "NumberTheory.TauFunction",     // τ(n)
            "NumberTheory.MertensFunction", // M(x)
            "NumberTheory.EulerPhi",        // Euler totient φ(n)
            // ================================================================
            // Congruences and local methods
            // ================================================================
            "NumberTheory.CongruentMod",         // a ≡ b (mod n)
            "NumberTheory.ResidueClass",         // residue classes modulo n
            "NumberTheory.ModularArithmetic",    // modular arithmetic laws
            "NumberTheory.FermatLittle",         // a^p ≡ a mod p
            "NumberTheory.EulerTheorem",         // a^φ(n) ≡ 1 mod n
            "NumberTheory.CarmichaelLambda",     // Carmichael function λ(n)
            "NumberTheory.ChineseRemainder",     // CRT
            "NumberTheory.QuadraticReciprocity", // quadratic reciprocity
            "NumberTheory.LegendreSymbol",       // (a/p)
            "NumberTheory.JacobiSymbol",         // Jacobi symbol
            "NumberTheory.HenselLemma",          // Hensel lifting
            "NumberTheory.HilbertSymbol",        // Hilbert symbol
            "NumberTheory.PAdicNumbers",         // ℚ_p
            "NumberTheory.PAdicIntegers",        // ℤ_p
            "NumberTheory.PAdicValuation",       // v_p
            "NumberTheory.PAdicNorm",            // |·|_p
            "NumberTheory.LocalField",           // local fields
            "NumberTheory.Completion",           // completions K_v
            "NumberTheory.DiscreteValuation",    // discrete valuations
            "NumberTheory.Uniformizer",          // uniformizer π
            // ================================================================
            // Algebraic number theory: fields and ideals
            // ================================================================
            "NumberTheory.AlgebraicNumber",      // algebraic over ℚ
            "NumberTheory.AlgebraicInteger",     // algebraic integers
            "NumberTheory.NumberField",          // finite extension of ℚ
            "NumberTheory.FieldExtension",       // L/K field extensions
            "NumberTheory.SeparableExtension",   // separable extensions
            "NumberTheory.NormalExtension",      // normal extensions
            "NumberTheory.Discriminant",         // discriminant Δ_K
            "NumberTheory.Trace",                // field trace
            "NumberTheory.Norm",                 // field norm
            "NumberTheory.IntegralBasis",        // integral basis
            "NumberTheory.DedekindDomain",       // Dedekind domains
            "NumberTheory.RingOfIntegers",       // O_K
            "NumberTheory.Order",                // orders in number fields
            "NumberTheory.MaximalOrder",         // maximal order
            "NumberTheory.Ideal",                // (fractional) ideals
            "NumberTheory.FractionalIdeal",      // fractional ideals
            "NumberTheory.IdealSum",             // I + J
            "NumberTheory.IdealProduct",         // I * J
            "NumberTheory.IdealPrime",           // prime ideals
            "NumberTheory.IdealFactorization",   // unique factorization of ideals
            "NumberTheory.ClassGroup",           // Cl(K)
            "NumberTheory.ClassNumber",          // h_K
            "NumberTheory.UnitGroup",            // O_K^×
            "NumberTheory.DirichletUnitTheorem", // Dirichlet unit theorem
            "NumberTheory.Regulator",            // regulator R_K
            "NumberTheory.MinkowskiBound",       // Minkowski bound
            "NumberTheory.SUnit",                // S-units
            "NumberTheory.SUnitEquation",        // S-unit equation
            // ================================================================
            // Ramification and decomposition
            // ================================================================
            "NumberTheory.RamificationIndex",  // e(𝔭|p)
            "NumberTheory.ResidueDegree",      // f(𝔭|p)
            "NumberTheory.DecompositionGroup", // decomposition group
            "NumberTheory.InertiaGroup",       // inertia group
            "NumberTheory.FrobeniusElement",   // Frobenius element
            "NumberTheory.Unramified",         // unramified primes
            "NumberTheory.TamelyRamified",     // tame ramification
            "NumberTheory.WildlyRamified",     // wild ramification
            "NumberTheory.DecompositionField", // decomposition field
            "NumberTheory.HilbertClassField",  // Hilbert class field
            "NumberTheory.RayClassField",      // ray class field
            "NumberTheory.ClassFieldTheory",   // class field theory axioms
            "NumberTheory.ArtinMap",           // Artin reciprocity
            "NumberTheory.LocalArtinMap",      // local reciprocity
            "NumberTheory.GlobalArtinMap",     // global reciprocity
            "NumberTheory.ChebotarevDensity",  // Chebotarev density theorem
            "NumberTheory.GrunwaldWang",       // Grunwald-Wang phenomenon
            "NumberTheory.HasseNormTheorem",   // Hasse norm theorem
            // ================================================================
            // Global and local fields
            // ================================================================
            "NumberTheory.GlobalField", // global fields (number/function)
            "NumberTheory.FunctionField", // global function fields
            "NumberTheory.LocalFieldStructure", // structure theorem for locals
            "NumberTheory.AdeleRing",   // adele ring A_K
            "NumberTheory.IdeleGroup",  // idele group I_K
            "NumberTheory.IdeleClassGroup", // C_K
            "NumberTheory.WeilRestriction", // restriction of scalars
            // ================================================================
            // Galois theory
            // ================================================================
            "NumberTheory.GaloisExtension", // Galois extensions
            "NumberTheory.GaloisGroup",     // Gal(L/K)
            "NumberTheory.FixedField",      // fixed field
            "NumberTheory.SplittingField",  // splitting fields
            "NumberTheory.FundamentalTheoremGalois", // fundamental theorem
            "NumberTheory.AbelianExtension", // abelian extensions
            "NumberTheory.CyclotomicField", // cyclotomic fields
            "NumberTheory.CyclotomicPolynomial", // Φ_n(x)
            "NumberTheory.KroneckerWeber",  // Kronecker-Weber theorem
            "NumberTheory.KummerExtension", // Kummer theory
            "NumberTheory.ArtinSchreier",   // Artin-Schreier theory
            "NumberTheory.LocalKroneckerWeber", // local class field theory
            "NumberTheory.TotallyReal",     // totally real fields
            "NumberTheory.CMField",         // CM fields
            "NumberTheory.ComplexMultiplication", // complex multiplication
            "NumberTheory.LubinTate",       // Lubin-Tate formal modules
            "NumberTheory.GaloisRepresentation", // ℓ-adic Galois representations
            "NumberTheory.GaloisDeformation", // deformation theory
            // ================================================================
            // Modular forms and automorphic objects
            // ================================================================
            "NumberTheory.ModularForm",             // modular forms
            "NumberTheory.CuspForm",                // cusp forms
            "NumberTheory.EisensteinSeries",        // Eisenstein series
            "NumberTheory.Newform",                 // newforms
            "NumberTheory.HeckeOperator",           // T_n
            "NumberTheory.HeckeEigenform",          // eigenforms
            "NumberTheory.HeckeEigenvalue",         // eigenvalues a_n
            "NumberTheory.qExpansion",              // q-expansion
            "NumberTheory.PeterssonInnerProduct",   // Petersson inner product
            "NumberTheory.ModularCurve",            // modular curves X(N)
            "NumberTheory.X0N",                     // X_0(N)
            "NumberTheory.X1N",                     // X_1(N)
            "NumberTheory.AtkinLehner",             // Atkin-Lehner operators
            "NumberTheory.LevelStructure",          // level structures
            "NumberTheory.RamanujanTau",            // Ramanujan τ(n)
            "NumberTheory.SatoTate",                // Sato-Tate conjecture
            "NumberTheory.ModularityTheorem",       // modularity of elliptic curves
            "NumberTheory.RibetLevelLowering",      // Ribet level lowering
            "NumberTheory.SerreConjecture",         // Serre conjecture
            "NumberTheory.LanglandsCorrespondence", // Langlands philosophy
            // ================================================================
            // Elliptic curves and arithmetic geometry
            // ================================================================
            "NumberTheory.EllipticCurve",          // elliptic curves
            "NumberTheory.WeierstrassModel",       // Weierstrass equations
            "NumberTheory.MinimalModel",           // minimal models
            "NumberTheory.Conductor",              // conductor N_E
            "NumberTheory.jInvariant",             // j-invariant
            "NumberTheory.TorsionSubgroup",        // torsion subgroup
            "NumberTheory.MordellWeilGroup",       // Mordell-Weil group
            "NumberTheory.Rank",                   // rank of E(ℚ)
            "NumberTheory.RankBound",              // bounds on rank
            "NumberTheory.HeightPairing",          // canonical heights
            "NumberTheory.LutzNagell",             // Lutz-Nagell theorem
            "NumberTheory.Descent",                // descent methods
            "NumberTheory.SelmerGroup",            // Selmer groups
            "NumberTheory.TateShafarevich",        // Tate-Shafarevich group
            "NumberTheory.BSDConjecture",          // Birch-Swinnerton-Dyer
            "NumberTheory.TateModule",             // Tate module
            "NumberTheory.EllipticCurveLFunction", // L(E, s)
            "NumberTheory.GaloisRepresentationElliptic", // Galois rep of E
            "NumberTheory.ModularParametrization", // modular parametrization
            "NumberTheory.NeronModel",             // Néron models
            "NumberTheory.ReductionType",          // reduction types
            "NumberTheory.GoodReduction",          // good reduction
            "NumberTheory.BadReduction",           // bad reduction
            "NumberTheory.MultiplicativeReduction", // multiplicative reduction
            "NumberTheory.AdditiveReduction",      // additive reduction
            // ================================================================
            // Diophantine equations and height methods
            // ================================================================
            "NumberTheory.DiophantineEquation", // general Diophantine problems
            "NumberTheory.FermatLastTheorem",   // Fermat's Last Theorem
            "NumberTheory.CatalanMihailescu",   // Catalan-Mihăilescu theorem
            "NumberTheory.PellEquation",        // Pell's equation
            "NumberTheory.MordellEquation",     // y^2 = x^3 + k
            "NumberTheory.ThueEquation",        // Thue equations
            "NumberTheory.HyperellipticCurve",  // hyperelliptic curves
            "NumberTheory.SiegelTheorem",       // finiteness of integral points
            "NumberTheory.FaltingsTheorem",     // Mordell conjecture
            "NumberTheory.MordellLang",         // Mordell-Lang conjecture
            "NumberTheory.HeightFunction",      // height functions
            "NumberTheory.NorthcottProperty",   // Northcott finiteness
            "NumberTheory.ArakelovDivisor",     // Arakelov divisors
            "NumberTheory.ArakelovClassGroup",  // Arakelov class group
            "NumberTheory.ArithmeticSurface",   // arithmetic surfaces
            "NumberTheory.ArithmeticScheme",    // arithmetic schemes
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone(), v.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.number_theory_init = true;
        Ok(())
    }

    /// Check if NumberTheory has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_number_theory` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_number_theory(&self) -> bool {
        self.number_theory_init
    }
}
