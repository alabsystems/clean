// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real and Complex Analysis for Environment
//!
//! This module contains axioms for real and complex analysis:
//! - Real numbers (construction, completeness, ordering)
//! - Complex numbers (algebraic and topological structure)
//! - Limits and continuity
//! - Differentiation and integration
//! - Sequences and series
//! - Complex analysis (holomorphic functions, Cauchy's theorem)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Build `@cmp.{0} Real inst a b` for a comparison operator (LE.le or LT.lt).
fn mk_real_cmp(cmp: &str, real: &Expr, inst: &Expr, a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string(cmp), vec![Level::zero()]),
                    real.clone(),
                ),
                inst.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

impl Environment {
    /// Initialize Real and Complex Analysis module
    ///
    /// Real and Complex Analysis provides the foundational axioms for:
    /// - Real number construction (Dedekind cuts or Cauchy sequences)
    /// - Completeness axioms (supremum, infimum, nested intervals)
    /// - Real functions (limits, continuity, differentiability, integrability)
    /// - Complex numbers (C as algebraic closure of R, polar form)
    /// - Complex analysis (holomorphic functions, Cauchy integral formula)
    /// - Sequences and series (convergence, power series, Taylor/Laurent)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.real_complex_analysis_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_real_complex_analysis(&mut self) -> Result<(), EnvError> {
        if self.real_complex_analysis_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_rat()?;
        self.init_metric_space()?;
        self.init_topological_space()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // ================================================================
        // Real : Type 0 (fixed universe, not polymorphic)
        // ================================================================
        // Real numbers are at a fixed universe level in Lean 4
        // Real : Type 0 where Type 0 = Sort 1 = Sort(Succ(Zero))
        let type_0 = Expr::sort(Level::succ(Level::zero()));
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real"),
            level_params: vec![],
            type_: type_0,
        })?;

        // Real and Complex Analysis constants (universe polymorphic stubs)
        for name in &[
            // ================================================================
            // Real Number Construction
            // ================================================================
            // Note: Real is declared separately with Type 0 above
            "Real.ofRat", // ℚ ↪ ℝ embedding
            // Note: Real.ofNat is added separately with proper Nat → Real type below
            // Note: Real.ofInt is added separately with proper Int → Real type below
            // Dedekind construction
            "Real.DedekindCut",         // Dedekind cut representation
            "Real.Cut.lower",           // Lower set of cut
            "Real.Cut.upper",           // Upper set of cut
            "Real.Cut.inhabited_lower", // Lower set nonempty
            "Real.Cut.inhabited_upper", // Upper set nonempty
            "Real.Cut.rounded_lower",   // No greatest element in lower
            "Real.Cut.rounded_upper",   // No least element in upper
            "Real.Cut.disjoint",        // Lower ∩ upper = ∅
            // Cauchy sequence construction
            "Real.CauchySeq",        // Cauchy sequence of rationals
            "Real.CauchySeq.mk",     // Constructor
            "Real.CauchySeq.cauchy", // Cauchy property
            "Real.CauchySeq.equiv",  // Equivalence relation
            "Real.CauchySeq.lift",   // Lift to quotient
            // ================================================================
            // Real Number Properties
            // ================================================================
            // Note: Real.add, Real.mul, Real.neg, Real.inv, Real.sub, Real.div,
            // Real.abs, Real.sqrt, Real.pow are added below with proper types
            // Note: Real.le and Real.lt are added separately with proper types below
            // Field axioms
            "Real.add_assoc",   // (a + b) + c = a + (b + c)
            "Real.add_zero",    // a + 0 = a
            "Real.add_neg",     // a + (-a) = 0
            "Real.mul_comm",    // a * b = b * a
            "Real.mul_assoc",   // (a * b) * c = a * (b * c)
            "Real.mul_one",     // a * 1 = a
            "Real.mul_inv",     // a * a⁻¹ = 1 (a ≠ 0)
            "Real.zero_ne_one", // 0 ≠ 1
            // Ordering axioms
            // Note: Real.le_refl, Real.le_antisymm, Real.le_trans, Real.le_total
            // are added in init_real_linear_order() with proper function types
            // Note: Real.add_{le,lt}_add_{left,right} in init_real_additive_order_axioms()
            "Real.mul_pos", // 0 < a → 0 < b → 0 < a*b
            // ================================================================
            // Completeness Axioms
            // ================================================================
            "Real.sup",                      // Supremum (lub)
            "Real.inf",                      // Infimum (glb)
            "Real.sup_is_lub",               // sup is least upper bound
            "Real.inf_is_glb",               // inf is greatest lower bound
            "Real.completeness",             // Every bounded nonempty set has sup
            "Real.archimedean",              // ∀ x : ℝ, ∃ n : ℕ, x < n
            "Real.density_of_rationals",     // Between any two reals is a rational
            "Real.nested_interval_property", // Nested closed intervals have nonempty intersection
            "Real.bolzano_weierstrass",      // Bounded sequence has convergent subsequence
            "Real.heine_borel",              // Closed bounded ⊂ ℝ is compact
            "Real.monotone_convergence",     // Bounded monotone sequence converges
            // ================================================================
            // Limits and Continuity
            // ================================================================
            "Real.Limit",                // lim_{x → a} f(x) = L
            "Real.Limit.def",            // ε-δ definition
            "Real.Limit.unique",         // Limits are unique
            "Real.Limit.add",            // lim(f + g) = lim f + lim g
            "Real.Limit.mul",            // lim(f * g) = lim f * lim g
            "Real.Limit.comp",           // lim(f ∘ g) = f(lim g) if f continuous
            "Real.LimitAtInfinity",      // lim_{x → ∞} f(x) = L
            "Real.LimitInfinity",        // lim_{x → a} f(x) = ∞
            "Real.Continuous",           // Continuity at a point
            "Real.Continuous.def",       // ε-δ definition
            "Real.ContinuousOn",         // Continuity on a set
            "Real.ContinuousOnInterval", // Continuity on [a,b]
            "Real.UniformlyContinuous",  // Uniform continuity
            "Real.Lipschitz",            // Lipschitz continuity
            // Continuity theorems
            "Real.Continuous.add",  // f, g continuous → f + g continuous
            "Real.Continuous.mul",  // f, g continuous → f * g continuous
            "Real.Continuous.comp", // f, g continuous → f ∘ g continuous
            "Real.IVT",             // Intermediate value theorem
            "Real.EVT",             // Extreme value theorem
            "Real.UniformContinuousOnCompact", // Continuous on compact → uniformly continuous
            // ================================================================
            // Sequences and Series
            // ================================================================
            "Real.Seq",                             // Sequence ℕ → ℝ
            "Real.Seq.Convergent",                  // Sequence converges
            "Real.Seq.Limit",                       // Limit of sequence
            "Real.Seq.Cauchy",                      // Cauchy sequence property
            "Real.Seq.CauchyComplete",              // ℝ is Cauchy complete
            "Real.Seq.Bounded",                     // Bounded sequence
            "Real.Seq.Monotone",                    // Monotone sequence
            "Real.Seq.Subsequence",                 // Subsequence definition
            "Real.Seq.limsup",                      // Limit superior
            "Real.Seq.liminf",                      // Limit inferior
            "Real.Series",                          // Infinite series ∑ aₙ
            "Real.Series.Convergent",               // Series converges
            "Real.Series.AbsolutelyConvergent",     // ∑|aₙ| converges
            "Real.Series.ConditionallyConvergent",  // Converges but not absolutely
            "Real.Series.ComparisonTest",           // Comparison test
            "Real.Series.RatioTest",                // Ratio test
            "Real.Series.RootTest",                 // Root test
            "Real.Series.IntegralTest",             // Integral test
            "Real.Series.AlternatingTest",          // Leibniz criterion
            "Real.Series.AbsImpliesConvergent",     // Absolute convergence → convergence
            "Real.PowerSeries",                     // Power series ∑ aₙxⁿ
            "Real.PowerSeries.RadiusOfConvergence", // Radius of convergence
            "Real.PowerSeries.UniformConvergence",  // Uniform convergence inside radius
            // ================================================================
            // Differentiation
            // ================================================================
            "Real.Differentiable",                  // f differentiable at a
            "Real.Derivative",                      // f'(a) definition
            "Real.Derivative.def",                  // lim_{h→0} (f(a+h) - f(a))/h
            "Real.DifferentiableOn",                // Differentiable on set
            "Real.Derivative.add",                  // (f + g)' = f' + g'
            "Real.Derivative.mul",                  // (f * g)' = f'g + fg' (product rule)
            "Real.Derivative.chain",                // (f ∘ g)' = (f' ∘ g) * g' (chain rule)
            "Real.Derivative.inv",                  // (1/f)' = -f'/f²
            "Real.Derivative.quot",                 // (f/g)' = (f'g - fg')/g² (quotient rule)
            "Real.Derivative.const",                // (c)' = 0
            "Real.Derivative.id",                   // (x)' = 1
            "Real.Derivative.pow",                  // (xⁿ)' = n*xⁿ⁻¹
            "Real.DifferentiableImpliesContinuous", // Differentiable → continuous
            "Real.MVT",                             // Mean value theorem
            "Real.Rolle",                           // Rolle's theorem
            "Real.Taylor",                          // Taylor's theorem
            "Real.LHopital",                        // L'Hôpital's rule
            "Real.CriticalPoint",                   // f'(a) = 0
            "Real.LocalMax",                        // Local maximum definition
            "Real.LocalMin",                        // Local minimum definition
            "Real.SecondDerivativeTest",            // Concavity test for extrema
            "Real.HigherDerivative",                // f⁽ⁿ⁾ higher derivatives
            "Real.SmoothFunction",                  // C^∞ function
            "Real.AnalyticFunction",                // Real analytic function
            // ================================================================
            // Integration
            // ================================================================
            "Real.Integral",                    // Definite integral ∫[a,b] f
            "Real.RiemannIntegrable",           // Riemann integrability
            "Real.RiemannSum",                  // Riemann sum definition
            "Real.DarbouxIntegral",             // Darboux integral (upper/lower)
            "Real.Integral.linearity",          // ∫(af + bg) = a∫f + b∫g
            "Real.Integral.additive",           // ∫[a,c] = ∫[a,b] + ∫[b,c]
            "Real.Integral.monotone",           // f ≤ g → ∫f ≤ ∫g
            "Real.Integral.abs",                // |∫f| ≤ ∫|f|
            "Real.FTC1",                        // d/dx ∫[a,x] f = f(x) (FTC part 1)
            "Real.FTC2",                        // ∫[a,b] f' = f(b) - f(a) (FTC part 2)
            "Real.IntegrationByParts",          // ∫f'g = fg - ∫fg'
            "Real.Substitution",                // ∫f(g(x))g'(x)dx = ∫f(u)du
            "Real.ImproperIntegral",            // Improper integrals
            "Real.ImproperIntegral.Convergent", // Convergence of improper integrals
            "Real.IntegralComparison",          // Comparison test for integrals
            // ================================================================
            // Complex Numbers
            // ================================================================
            "Complex",        // The complex numbers ℂ
            "Complex.re",     // Real part
            "Complex.im",     // Imaginary part
            "Complex.mk",     // a + bi constructor
            "Complex.I",      // Imaginary unit i
            "Complex.I_sq",   // i² = -1
            "Complex.ofReal", // ℝ ↪ ℂ embedding
            "Complex.conj",   // Complex conjugate
            "Complex.abs",    // |z| = √(x² + y²)
            "Complex.arg",    // Argument (angle)
            // Complex field operations
            "Complex.add", // Addition
            "Complex.mul", // Multiplication
            "Complex.neg", // Negation
            "Complex.inv", // Multiplicative inverse
            "Complex.sub", // Subtraction
            "Complex.div", // Division
            // Field axioms (ℂ is a field)
            "Complex.field",                // ℂ is a field
            "Complex.algebraically_closed", // ℂ is algebraically closed
            // Polar form
            "Complex.polar",   // z = r*e^(iθ)
            "Complex.abs_mul", // |zw| = |z||w|
            "Complex.arg_mul", // arg(zw) = arg(z) + arg(w)
            // Topology of ℂ
            "Complex.isometry", // ℂ ≅ ℝ² as metric spaces
            "Complex.complete", // ℂ is complete
            // ================================================================
            // Complex Exponential and Trigonometric Functions
            // ================================================================
            "Complex.exp",            // e^z
            "Complex.log",            // log(z) (principal branch)
            "Complex.exp_def",        // e^z = ∑ zⁿ/n!
            "Complex.exp_add",        // e^(z+w) = e^z * e^w
            "Complex.exp_conj",       // exp(z̄) = exp(z)̄
            "Complex.sin",            // sin(z) = (e^(iz) - e^(-iz))/(2i)
            "Complex.cos",            // cos(z) = (e^(iz) + e^(-iz))/2
            "Complex.sinh",           // sinh(z)
            "Complex.cosh",           // cosh(z)
            "Complex.tan",            // tan(z) = sin(z)/cos(z)
            "Complex.euler_formula",  // e^(ix) = cos(x) + i*sin(x)
            "Complex.euler_identity", // e^(iπ) + 1 = 0
            "Complex.de_moivre",      // (cos θ + i sin θ)ⁿ = cos(nθ) + i sin(nθ)
            // ================================================================
            // Complex Analysis - Holomorphic Functions
            // ================================================================
            "Complex.Holomorphic",       // Holomorphic (complex differentiable)
            "Complex.Holomorphic.def",   // Limit definition
            "Complex.Holomorphic.Open",  // Holomorphic on open set
            "Complex.CauchyRiemann",     // Cauchy-Riemann equations
            "Complex.CauchyRiemann.iff", // f holomorphic ↔ CR satisfied + partial derivatives continuous
            "Complex.Analytic",          // Complex analytic function
            "Complex.HolomorphicImpliesAnalytic", // Holomorphic → analytic
            "Complex.AnalyticImpliesHolomorphic", // Analytic → holomorphic
            "Complex.EntireFunction",    // Entire (holomorphic on all ℂ)
            "Complex.Meromorphic",       // Meromorphic function
            "Complex.Singularity",       // Types of singularities
            "Complex.Singularity.Removable", // Removable singularity
            "Complex.Singularity.Pole",  // Pole (order n)
            "Complex.Singularity.Essential", // Essential singularity
            // ================================================================
            // Complex Integration
            // ================================================================
            "Complex.ContourIntegral",               // ∮_γ f(z) dz
            "Complex.Contour",                       // Contour (piecewise smooth curve)
            "Complex.Contour.Length",                // Length of contour
            "Complex.ContourIntegral.linearity",     // Linearity
            "Complex.ContourIntegral.concatenation", // ∮_{γ₁+γ₂} = ∮_{γ₁} + ∮_{γ₂}
            "Complex.ContourIntegral.reversal",      // ∮_{-γ} = -∮_γ
            "Complex.CauchyTheorem",                 // ∮_γ f = 0 for f holomorphic inside γ
            "Complex.CauchyIntegralFormula",         // f(a) = (1/2πi) ∮_γ f(z)/(z-a) dz
            "Complex.CauchyIntegralFormula.deriv",   // f⁽ⁿ⁾(a) = (n!/2πi) ∮_γ f(z)/(z-a)^(n+1) dz
            "Complex.ResidueTheorem",                // ∮_γ f = 2πi ∑ Res(f, aₖ)
            "Complex.Residue",                       // Residue at a point
            "Complex.Residue.simple_pole",           // Res(f, a) = lim_{z→a} (z-a)f(z)
            "Complex.Residue.higher_pole",           // Formula for higher order poles
            "Complex.ArgumentPrinciple",             // Winding number formula
            "Complex.Rouche",                        // Rouché's theorem
            "Complex.OpenMappingTheorem",            // Open mapping theorem
            "Complex.InverseFunctionTheorem",        // Inverse function theorem
            // ================================================================
            // Series in Complex Analysis
            // ================================================================
            "Complex.PowerSeries",             // ∑ aₙ(z-z₀)ⁿ
            "Complex.LaurentSeries",           // ∑_{n=-∞}^{∞} aₙ(z-z₀)ⁿ
            "Complex.TaylorExpansion",         // Taylor series of holomorphic function
            "Complex.LaurentExpansion",        // Laurent expansion around singularity
            "Complex.RadiusOfConvergence",     // R = 1/limsup|aₙ|^(1/n)
            "Complex.Abel",                    // Abel's theorem
            "Complex.IdentityTheorem",         // Zeros of analytic functions
            "Complex.MaximumModulusPrinciple", // |f| has no interior max
            "Complex.MinimumModulusPrinciple", // |f| (f≠0) has no interior min
            "Complex.SchwarzLemma",            // Schwarz lemma
            "Complex.Liouville",               // Bounded entire → constant
            "Complex.FTA",                     // Fundamental theorem of algebra
            // ================================================================
            // Conformal Mappings
            // ================================================================
            "Complex.ConformalMap", // Conformal (angle-preserving) map
            "Complex.HolomorphicImpliesConformal", // Holomorphic with f'≠0 → conformal
            "Complex.BiholomorphicMap", // Biholomorphic (holomorphic bijection)
            "Complex.RiemannMappingTheorem", // Simply connected ≠ ℂ ≅ disk
            "Complex.MobiusTransformation", // (az+b)/(cz+d) transformations
            "Complex.Mobius.composition", // Möbius compose to Möbius
            "Complex.Mobius.inverse", // Inverse of Möbius
            "Complex.Mobius.cross_ratio", // Cross-ratio invariance
            "Complex.Mobius.circle_preservation", // Maps circles/lines to circles/lines
            // Standard conformal maps
            "Complex.Map.exp",       // Strip → punctured plane
            "Complex.Map.log",       // Punctured plane → strip
            "Complex.Map.sqrt",      // Plane → half-plane
            "Complex.Map.joukowski", // Joukowski transformation
            // ================================================================
            // Special Functions
            // ================================================================
            "Real.exp",                           // Real exponential e^x
            "Real.log",                           // Natural logarithm ln(x)
            "Real.exp_def",                       // e^x = ∑ xⁿ/n!
            "Real.log_def",                       // ln(x) = ∫[1,x] 1/t dt
            "Real.exp_add",                       // e^(x+y) = e^x * e^y
            "Real.exp_log",                       // e^(ln x) = x
            "Real.log_exp",                       // ln(e^x) = x
            "Real.sin",                           // Sine function
            "Real.cos",                           // Cosine function
            "Real.tan",                           // Tangent function
            "Real.sin_def",                       // sin(x) = ∑ (-1)ⁿx^(2n+1)/(2n+1)!
            "Real.cos_def",                       // cos(x) = ∑ (-1)ⁿx^(2n)/(2n)!
            "Real.sin_cos_sq",                    // sin²x + cos²x = 1
            "Real.sin_add",                       // sin(x+y) addition formula
            "Real.cos_add",                       // cos(x+y) addition formula
            "Real.Gamma",                         // Gamma function Γ(s)
            "Real.Gamma.def",                     // Γ(s) = ∫₀^∞ t^(s-1)e^(-t) dt
            "Real.Gamma.functional",              // Γ(s+1) = sΓ(s)
            "Real.Gamma.factorial",               // Γ(n+1) = n!
            "Real.Beta",                          // Beta function B(a,b)
            "Real.Beta.def",                      // B(a,b) = ∫₀¹ t^(a-1)(1-t)^(b-1) dt
            "Real.Beta.gamma_relation",           // B(a,b) = Γ(a)Γ(b)/Γ(a+b)
            "Complex.Zeta",                       // Riemann zeta function ζ(s)
            "Complex.Zeta.def",                   // ζ(s) = ∑ n^(-s) for Re(s) > 1
            "Complex.Zeta.euler_product",         // ζ(s) = ∏ (1-p^(-s))^(-1)
            "Complex.Zeta.functional_equation",   // ζ(s) = 2^s π^(s-1) sin(πs/2) Γ(1-s) ζ(1-s)
            "Complex.Zeta.analytic_continuation", // Meromorphic on ℂ with pole at s=1
            // ================================================================
            // Advanced Topics
            // ================================================================
            "Real.UniformConvergence", // Uniform convergence of functions
            "Real.UniformLimit",       // Uniform limit preserves continuity
            "Real.UniformIntegrable",  // Uniform integrability
            "Real.ArzelaAscoli",       // Arzelà-Ascoli theorem
            "Real.StoneWeierstrass",   // Stone-Weierstrass approximation
            "Real.WeierstrassApproximation", // Polynomials dense in C[a,b]
            "Complex.WeierstrassFactorization", // Factorization of entire functions
            "Complex.MittagLeffler",   // Mittag-Leffler theorem
            "Complex.Picard",          // Picard theorems (little and great)
            "Complex.Casorati.Weierstrass", // Near essential singularity, f(U) dense
            "Complex.MonodromeTheorem", // Monodromy theorem
            "Complex.SchwarzReflection", // Schwarz reflection principle
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Real Arithmetic Operations with Proper Types
        // ================================================================
        // These need proper function types (Real → Real → Real, etc.)
        // rather than the generic Sort u stubs above
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Binary ops: Real → Real → Real
        let real_binop_type = Expr::pi(
            BinderInfo::Default,
            real_const.clone(),
            Expr::pi(BinderInfo::Default, real_const.clone(), real_const.clone()),
        );

        for name in ["Real.add", "Real.mul", "Real.sub", "Real.div"] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: real_binop_type.clone(),
            })?;
        }

        // Unary ops: Real → Real
        let real_unop_type = Expr::pi(BinderInfo::Default, real_const.clone(), real_const.clone());

        for name in ["Real.neg", "Real.inv", "Real.abs", "Real.sqrt"] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: real_unop_type.clone(),
            })?;
        }
        // Power: Real → Nat → Real
        let real_pow_type = Expr::pi(
            BinderInfo::Default,
            real_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), real_const.clone()),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.pow"),
            level_params: vec![],
            type_: real_pow_type,
        })?;

        // ================================================================
        // Real.le : Real → Real → Prop (ordering relation)
        // Real.lt : Real → Real → Prop (strict ordering relation)
        // ================================================================
        // These are used by instLEReal and instLTReal to provide LE and LT instances
        // (real_const and nat_const already defined above)
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let real_le_type = Expr::pi(
            BinderInfo::Default,
            real_const.clone(),
            Expr::pi(BinderInfo::Default, real_const.clone(), prop.clone()),
        );
        let real_lt_type = real_le_type.clone();

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.le"),
            level_params: vec![],
            type_: real_le_type,
        })?;

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.lt"),
            level_params: vec![],
            type_: real_lt_type,
        })?;

        // ================================================================
        // Real.ofNat : Nat → Real (proper coercion function)
        // ================================================================
        // This allows Nat literals to be coerced to Real during elaboration
        // (nat_const already defined above)
        let ofnat_type = Expr::pi(BinderInfo::Default, nat_const.clone(), real_const.clone());

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.ofNat"),
            level_params: vec![],
            type_: ofnat_type.clone(),
        })?;
        self.init_real_ofint()?;
        self.init_real_replay_axioms()?;
        self.real_complex_analysis_init = true;
        Ok(())
    }

    /// Initialize Real.ofInt : Int → Real (proper coercion function).
    ///
    /// Enables negative Real constants in proof reconstruction. Without
    /// this, negative Real constants (e.g., -3) translate to Int.negSucc
    /// which has type Int, not Real — causing type errors in chain proofs.
    fn init_real_ofint(&mut self) -> Result<(), EnvError> {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let ofint_type = Expr::pi(BinderInfo::Default, int_const, real_const);

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.ofInt"),
            level_params: vec![],
            type_: ofint_type,
        })
    }

    /// Initialize Real.add_right_cancel : ∀ (a b c : Real), a + b = c + b → a = c.
    ///
    /// Convention: shared cancel term is `b` (2nd param), matching Nat/Int/Rat.
    /// Enables the cancellation bridge for Real-carrier linear combination
    /// proof reconstruction (#2635).
    fn init_real_add_right_cancel(&mut self) -> Result<(), EnvError> {
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let real_add = Expr::const_(Name::from_string("Real.add"), vec![]);
        let mut bd = EnvDeclBuilder::new();
        let (a_id, a) = bd.fresh_local(real_const.clone());
        let (b_id, b) = bd.fresh_local(real_const.clone());
        let (c_id, c) = bd.fresh_local(real_const.clone());
        let lhs = Expr::app(Expr::app(real_add.clone(), a.clone()), b.clone());
        let rhs = Expr::app(Expr::app(real_add, c.clone()), b.clone());
        let mk_real_eq = |l: Expr, r: Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        real_const.clone(),
                    ),
                    l,
                ),
                r,
            )
        };
        let premise = mk_real_eq(lhs, rhs);
        let conclusion = mk_real_eq(a, c);
        let (h_id, _h) = bd.fresh_local(premise.clone());
        let e = bd.mk_pi(h_id, BinderInfo::Default, premise, conclusion);
        let e = bd.mk_pi(c_id, BinderInfo::Default, real_const.clone(), e);
        let e = bd.mk_pi(b_id, BinderInfo::Default, real_const.clone(), e);
        let e = bd.mk_pi(a_id, BinderInfo::Default, real_const.clone(), e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.add_right_cancel"),
            level_params: vec![],
            type_: bd.finish(e),
        })
    }

    /// Initialize the typed Real theorem surface needed by bounded proof replay.
    fn init_real_replay_axioms(&mut self) -> Result<(), EnvError> {
        self.init_real_add_comm()?;
        self.init_real_distrib()?;
        self.init_real_add_right_cancel()?;
        self.init_real_mul_left_cancel_of_nat_succ()
    }

    /// Initialize Real.add_comm : ∀ (a b : Real), a + b = b + a.
    fn init_real_add_comm(&mut self) -> Result<(), EnvError> {
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let real_add = Expr::const_(Name::from_string("Real.add"), vec![]);
        let mut bd = EnvDeclBuilder::new();
        let (a_id, a) = bd.fresh_local(real_const.clone());
        let (b_id, b) = bd.fresh_local(real_const.clone());
        let lhs = Expr::app(Expr::app(real_add.clone(), a.clone()), b.clone());
        let rhs = Expr::app(Expr::app(real_add, b.clone()), a.clone());
        let eq_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    real_const.clone(),
                ),
                lhs,
            ),
            rhs,
        );
        let e = bd.mk_pi(b_id, BinderInfo::Default, real_const.clone(), eq_ty);
        let e = bd.mk_pi(a_id, BinderInfo::Default, real_const.clone(), e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.add_comm"),
            level_params: vec![],
            type_: bd.finish(e),
        })
    }

    /// Initialize Real.distrib : ∀ (a b c : Real), a * (b + c) = a*b + a*c.
    fn init_real_distrib(&mut self) -> Result<(), EnvError> {
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let real_add = Expr::const_(Name::from_string("Real.add"), vec![]);
        let real_mul = Expr::const_(Name::from_string("Real.mul"), vec![]);
        let mut bd = EnvDeclBuilder::new();
        let (a_id, a) = bd.fresh_local(real_const.clone());
        let (b_id, b) = bd.fresh_local(real_const.clone());
        let (c_id, c) = bd.fresh_local(real_const.clone());
        let sum = Expr::app(Expr::app(real_add.clone(), b.clone()), c.clone());
        let lhs = Expr::app(Expr::app(real_mul.clone(), a.clone()), sum);
        let rhs = Expr::app(
            Expr::app(
                real_add,
                Expr::app(Expr::app(real_mul.clone(), a.clone()), b.clone()),
            ),
            Expr::app(Expr::app(real_mul, a.clone()), c.clone()),
        );
        let eq_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    real_const.clone(),
                ),
                lhs,
            ),
            rhs,
        );
        let e = bd.mk_pi(c_id, BinderInfo::Default, real_const.clone(), eq_ty);
        let e = bd.mk_pi(b_id, BinderInfo::Default, real_const.clone(), e);
        let e = bd.mk_pi(a_id, BinderInfo::Default, real_const.clone(), e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.distrib"),
            level_params: vec![],
            type_: bd.finish(e),
        })
    }

    /// Initialize Real.mul_left_cancel_ofNat_succ :
    /// ∀ (n : Nat) (a b : Real),
    ///   (Real.ofInt (Int.ofNat (Nat.succ n))) * a =
    ///   (Real.ofInt (Int.ofNat (Nat.succ n))) * b → a = b.
    fn init_real_mul_left_cancel_of_nat_succ(&mut self) -> Result<(), EnvError> {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let real_mul = Expr::const_(Name::from_string("Real.mul"), vec![]);
        let real_of_int = Expr::const_(Name::from_string("Real.ofInt"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let mut bd = EnvDeclBuilder::new();
        let (n_id, n) = bd.fresh_local(nat_const);
        let (a_id, a) = bd.fresh_local(real_const.clone());
        let (b_id, b) = bd.fresh_local(real_const.clone());
        let succ_n = Expr::app(nat_succ, n.clone());
        let scale = Expr::app(real_of_int, Expr::app(int_of_nat, succ_n));
        let lhs = Expr::app(Expr::app(real_mul.clone(), scale.clone()), a.clone());
        let rhs = Expr::app(Expr::app(real_mul, scale), b.clone());
        let premise = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    real_const.clone(),
                ),
                lhs,
            ),
            rhs,
        );
        let conclusion = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    real_const.clone(),
                ),
                a,
            ),
            b,
        );
        let (h_id, _h) = bd.fresh_local(premise.clone());
        let e = bd.mk_pi(h_id, BinderInfo::Default, premise, conclusion);
        let e = bd.mk_pi(b_id, BinderInfo::Default, real_const.clone(), e);
        let e = bd.mk_pi(a_id, BinderInfo::Default, real_const.clone(), e);
        let e = bd.mk_pi(
            n_id,
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            e,
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.mul_left_cancel_ofNat_succ"),
            level_params: vec![],
            type_: bd.finish(e),
        })
    }

    /// Check if Real and Complex Analysis has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.real_complex_analysis_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_real_complex_analysis(&self) -> bool {
        self.real_complex_analysis_init
    }

    /// Initialize Real ordering operations
    ///
    /// This adds:
    /// - instLEReal : LE Real
    /// - instLTReal : LT Real
    ///
    /// Uses the Real.le and Real.lt axioms from init_real_complex_analysis().
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.real_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_real_ord(&mut self) -> Result<(), EnvError> {
        if self.real_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_real_complex_analysis()?; // Provides Real, Real.le, Real.lt
        self.init_le()?; // Provides LE typeclass
        self.init_lt()?; // Provides LT typeclass

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);

        // ========================================
        // instLEReal : LE Real := ⟨Real.le⟩
        // ========================================
        // Real is at universe level 0 (Type), so LE is instantiated at Level::zero()
        let inst_le_real_type = Expr::app(
            Expr::const_(Name::from_string("LE"), vec![Level::zero()]),
            real_const.clone(),
        );

        let real_le_def = Expr::const_(Name::from_string("Real.le"), vec![]);

        // LE.mk @Real Real.le
        let inst_le_real_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LE.mk"), vec![Level::zero()]),
                real_const.clone(),
            ),
            real_le_def,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLEReal"),
            level_params: vec![],
            type_: inst_le_real_type,
            value: inst_le_real_value,
            is_reducible: true,
        })?;

        // Register instLEReal instance
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instLEReal"),
            class_name: Name::from_string("LE"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // ========================================
        // instLTReal : LT Real := ⟨Real.lt⟩
        // ========================================
        // Real is at universe level 0 (Type), so LT is instantiated at Level::zero()
        let inst_lt_real_type = Expr::app(
            Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
            real_const.clone(),
        );

        let real_lt_def = Expr::const_(Name::from_string("Real.lt"), vec![]);

        // LT.mk @Real Real.lt
        let inst_lt_real_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LT.mk"), vec![Level::zero()]),
                real_const.clone(),
            ),
            real_lt_def,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLTReal"),
            level_params: vec![],
            type_: inst_lt_real_type,
            value: inst_lt_real_value,
            is_reducible: true,
        })?;

        // Register instLTReal instance
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instLTReal"),
            class_name: Name::from_string("LT"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.real_ord_init = true;
        Ok(())
    }

    /// Check if Real ordering has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.real_ord_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_real_ord(&self) -> bool {
        self.real_ord_init
    }

    /// Initialize LinearOrder instance for Real
    ///
    /// This adds:
    /// - Real.le_refl, Real.le_trans, Real.le_antisymm (axioms - already in init_real_complex_analysis)
    /// - Real.lt_iff_le_not_le (axiom)
    /// - instPreorderReal : Preorder Real
    /// - instPartialOrderReal : PartialOrder Real
    /// - instLinearOrderReal : LinearOrder Real
    ///
    /// Requires: init_real_ord() for instLEReal, instLTReal
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.real_linear_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_real_linear_order(&mut self) -> Result<(), EnvError> {
        if self.real_linear_order_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_real_ord()?; // Provides instLEReal, instLTReal
        self.init_preorder()?; // Provides Preorder typeclass
        self.init_partial_order()?; // Provides PartialOrder typeclass
        self.init_linear_order()?; // Provides LinearOrder typeclass

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let or_const = Expr::const_(Name::from_string("Or"), vec![]);
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);

        // Use typeclass-based LE.le/LT.lt form for compatibility with Preorder.mk
        let inst_le_real = Expr::const_(Name::from_string("instLEReal"), vec![]);
        let inst_lt_real = Expr::const_(Name::from_string("instLTReal"), vec![]);

        // Helper: LE.le.{0} Real instLEReal a b
        let le_le = |a: &Expr, b: &Expr| -> Expr {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                            real_const.clone(),
                        ),
                        inst_le_real.clone(),
                    ),
                    a.clone(),
                ),
                b.clone(),
            )
        };

        // Helper: LT.lt.{0} Real instLTReal a b
        let lt_lt = |a: &Expr, b: &Expr| -> Expr {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                            real_const.clone(),
                        ),
                        inst_lt_real.clone(),
                    ),
                    a.clone(),
                ),
                b.clone(),
            )
        };

        // Ordering axioms using LE.le/LT.lt typeclass form
        // Real.le_refl : ∀ a : Real, LE.le Real instLEReal a a
        let le_refl_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let body = le_le(&a, &a);
            let e = b.mk_pi(a_id, BinderInfo::Default, real_const.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.le_refl"),
            level_params: vec![],
            type_: le_refl_type,
        })?;

        // Real.le_trans : ∀ a b c : Real, LE.le a b → LE.le b c → LE.le a c
        let le_trans_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let (bv_id, bv) = b.fresh_local(real_const.clone());
            let (c_id, c) = b.fresh_local(real_const.clone());
            let hab_ty = le_le(&a, &bv);
            let (hab_id, _hab) = b.fresh_local(hab_ty.clone());
            let hbc_ty = le_le(&bv, &c);
            let (hbc_id, _hbc) = b.fresh_local(hbc_ty.clone());
            let body = le_le(&a, &c);
            let e = b.mk_pi(hbc_id, BinderInfo::Default, hbc_ty, body);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_pi(c_id, BinderInfo::Default, real_const.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, real_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, real_const.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.le_trans"),
            level_params: vec![],
            type_: le_trans_type,
        })?;

        // Real.le_antisymm : ∀ a b : Real, LE.le a b → LE.le b a → @Eq Real a b
        let le_antisymm_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let (bv_id, bv) = b.fresh_local(real_const.clone());
            let hab_ty = le_le(&a, &bv);
            let (hab_id, _hab) = b.fresh_local(hab_ty.clone());
            let hba_ty = le_le(&bv, &a);
            let (hba_id, _hba) = b.fresh_local(hba_ty.clone());
            // Eq.{1} Real a b — Real : Type 0 = Sort 1, so Eq universe is Succ(Zero)
            let eq_real = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let body = Expr::app(
                Expr::app(Expr::app(eq_real, real_const.clone()), a.clone()),
                bv.clone(),
            );
            let e = b.mk_pi(hba_id, BinderInfo::Default, hba_ty, body);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, real_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, real_const.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.le_antisymm"),
            level_params: vec![],
            type_: le_antisymm_type,
        })?;

        // Real.le_total : ∀ a b : Real, Or (LE.le a b) (LE.le b a)
        let le_total_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let (bv_id, bv) = b.fresh_local(real_const.clone());
            let body = Expr::app(Expr::app(or_const.clone(), le_le(&a, &bv)), le_le(&bv, &a));
            let e = b.mk_pi(bv_id, BinderInfo::Default, real_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, real_const.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.le_total"),
            level_params: vec![],
            type_: le_total_type,
        })?;

        // ========================================
        // Real.lt_iff_le_not_le : ∀ a b : Real, Iff (LT.lt a b) (And (LE.le a b) (Not (LE.le b a)))
        // ========================================
        let lt_iff_le_not_le_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let (b_id, bv) = b.fresh_local(real_const.clone());
            let body = Expr::app(
                Expr::app(iff_const.clone(), lt_lt(&a, &bv)),
                Expr::app(
                    Expr::app(and_const.clone(), le_le(&a, &bv)),
                    Expr::app(not_const.clone(), le_le(&bv, &a)),
                ),
            );
            let e = b.mk_pi(b_id, BinderInfo::Default, real_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, real_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.lt_iff_le_not_le"),
            level_params: vec![],
            type_: lt_iff_le_not_le_type,
        })?;
        self.init_real_strict_order_axioms()?;

        // ========================================
        // instPreorderReal : Preorder Real
        // ========================================
        let inst_preorder_real_type = Expr::app(
            Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
            real_const.clone(),
        );

        // le_refl for Preorder: λ a : Real => Real.le_refl a
        let preorder_le_refl = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let body = Expr::app(Expr::const_(Name::from_string("Real.le_refl"), vec![]), a);
            let e = b.mk_lam(a_id, BinderInfo::Default, real_const.clone(), body);
            b.finish(e)
        };

        // le_trans for Preorder
        let preorder_le_trans = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let (bv_id, bv) = b.fresh_local(real_const.clone());
            let (c_id, c) = b.fresh_local(real_const.clone());
            let hab_ty = le_le(&a, &bv);
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());
            let hbc_ty = le_le(&bv, &c);
            let (hbc_id, hbc) = b.fresh_local(hbc_ty.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("Real.le_trans"), vec![]),
                                a.clone(),
                            ),
                            bv.clone(),
                        ),
                        c.clone(),
                    ),
                    hab,
                ),
                hbc,
            );
            let e = b.mk_lam(hbc_id, BinderInfo::Default, hbc_ty, body);
            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_lam(c_id, BinderInfo::Default, real_const.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, real_const.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, real_const.clone(), e);
            b.finish(e)
        };

        // Build Preorder.mk @Real @instLEReal @instLTReal le_refl le_trans
        let preorder_mk = Expr::const_(Name::from_string("Preorder.mk"), vec![Level::zero()]);
        let inst_le_real = Expr::const_(Name::from_string("instLEReal"), vec![]);
        let inst_lt_real = Expr::const_(Name::from_string("instLTReal"), vec![]);

        let inst_preorder_real_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(preorder_mk.clone(), real_const.clone()),
                        inst_le_real.clone(),
                    ),
                    inst_lt_real.clone(),
                ),
                preorder_le_refl.clone(),
            ),
            preorder_le_trans.clone(),
        );

        // instPreorderReal is the checked base for the PartialOrder/LinearOrder
        // typeclass hierarchy definitions below.
        self.add_decl(Declaration::Definition {
            name: Name::from_string("instPreorderReal"),
            level_params: vec![],
            type_: inst_preorder_real_type,
            value: inst_preorder_real_value,
            is_reducible: true,
        })?;

        // ========================================
        // instPartialOrderReal : PartialOrder Real
        // ========================================
        let inst_partial_order_real_type = Expr::app(
            Expr::const_(Name::from_string("PartialOrder"), vec![Level::zero()]),
            real_const.clone(),
        );

        // le_antisymm for PartialOrder
        let partial_order_le_antisymm = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let (bv_id, bv) = b.fresh_local(real_const.clone());
            let hab_ty = le_le(&a, &bv);
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());
            let hba_ty = le_le(&bv, &a);
            let (hba_id, hba) = b.fresh_local(hba_ty.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Real.le_antisymm"), vec![]),
                            a.clone(),
                        ),
                        bv.clone(),
                    ),
                    hab,
                ),
                hba,
            );
            let e = b.mk_lam(hba_id, BinderInfo::Default, hba_ty, body);
            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, real_const.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, real_const.clone(), e);
            b.finish(e)
        };

        // Checked against instPreorderReal; LinearOrder below follows the
        // same hierarchy path via instPartialOrderReal.
        let partial_order_mk =
            Expr::const_(Name::from_string("PartialOrder.mk"), vec![Level::zero()]);
        let inst_preorder_real = Expr::const_(Name::from_string("instPreorderReal"), vec![]);

        let inst_partial_order_real_value = Expr::app(
            Expr::app(
                Expr::app(partial_order_mk.clone(), real_const.clone()),
                inst_preorder_real.clone(),
            ),
            partial_order_le_antisymm.clone(),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instPartialOrderReal"),
            level_params: vec![],
            type_: inst_partial_order_real_type,
            value: inst_partial_order_real_value,
            is_reducible: true,
        })?;

        // ========================================
        // instLinearOrderReal : LinearOrder Real
        // ========================================
        let inst_linear_order_real_type = Expr::app(
            Expr::const_(Name::from_string("LinearOrder"), vec![Level::zero()]),
            real_const.clone(),
        );

        // le_total for LinearOrder
        let linear_order_le_total = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_const.clone());
            let (bv_id, bv) = b.fresh_local(real_const.clone());
            let body = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Real.le_total"), vec![]), a),
                bv,
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, real_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, real_const.clone(), e);
            b.finish(e)
        };

        // Checked via the same hierarchy path as Rat: LinearOrder.mk consumes
        // instPartialOrderReal and Real.le_total in LE.le @Real instLEReal form.
        let linear_order_mk =
            Expr::const_(Name::from_string("LinearOrder.mk"), vec![Level::zero()]);
        let inst_partial_order_real =
            Expr::const_(Name::from_string("instPartialOrderReal"), vec![]);

        let inst_linear_order_real_value = Expr::app(
            Expr::app(
                Expr::app(linear_order_mk.clone(), real_const.clone()),
                inst_partial_order_real.clone(),
            ),
            linear_order_le_total.clone(),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLinearOrderReal"),
            level_params: vec![],
            type_: inst_linear_order_real_type,
            value: inst_linear_order_real_value,
            is_reducible: true,
        })?;

        self.real_linear_order_init = true;
        Ok(())
    }

    /// Check if Real LinearOrder has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.real_linear_order_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_real_linear_order(&self) -> bool {
        self.real_linear_order_init
    }

    /// Initialize strict ordering axioms for Real: lt_trans, lt_of_le_of_lt,
    /// lt_of_lt_of_le, lt_irrefl. Called by `init_real_linear_order`.
    fn init_real_strict_order_axioms(&mut self) -> Result<(), EnvError> {
        let real = Expr::const_(Name::from_string("Real"), vec![]);
        let inst_le = Expr::const_(Name::from_string("instLEReal"), vec![]);
        let inst_lt = Expr::const_(Name::from_string("instLTReal"), vec![]);
        let mk_le = |a: &Expr, b: &Expr| mk_real_cmp("LE.le", &real, &inst_le, a, b);
        let mk_lt = |a: &Expr, b: &Expr| mk_real_cmp("LT.lt", &real, &inst_lt, a, b);

        self.add_real_trans_axiom("Real.lt_trans", &real, &mk_lt, &mk_lt, &mk_lt)?;
        self.add_real_trans_axiom("Real.lt_of_le_of_lt", &real, &mk_le, &mk_lt, &mk_lt)?;
        self.add_real_trans_axiom("Real.lt_of_lt_of_le", &real, &mk_lt, &mk_le, &mk_lt)?;

        // Real.lt_irrefl : ∀ a : Real, LT.lt Real instLTReal a a → False
        let lt_irrefl_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real.clone());
            let lt_aa = mk_lt(&a, &a);
            let (h_id, _) = b.fresh_local(lt_aa.clone());
            let false_ty = Expr::const_(Name::from_string("False"), vec![]);
            let e = b.mk_pi(h_id, BinderInfo::Default, lt_aa, false_ty);
            let e = b.mk_pi(a_id, BinderInfo::Default, real.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.lt_irrefl"),
            level_params: vec![],
            type_: lt_irrefl_type,
        })?;

        self.init_real_ofnat_bridge_axioms()?;
        self.init_real_ofint_bridge_axioms()?;
        self.init_real_additive_order_axioms()?;
        self.init_real_int_downcast_axioms()
    }

    /// Additive monotonicity axioms for Real ordering.
    ///
    /// Adds:
    /// - Real.add_le_add_left : ∀ a b : Real, LE.le a b → ∀ c : Real, LE.le (Real.add c a) (Real.add c b)
    /// - Real.add_le_add_right : ∀ a b : Real, LE.le a b → ∀ c : Real, LE.le (Real.add a c) (Real.add b c)
    /// - Real.add_lt_add_left : ∀ a b : Real, LT.lt a b → ∀ c : Real, LT.lt (Real.add c a) (Real.add c b)
    /// - Real.add_lt_add_right : ∀ a b : Real, LT.lt a b → ∀ c : Real, LT.lt (Real.add a c) (Real.add b c)
    ///
    /// Required by bridge LRA Farkas additive proof reconstruction (#302).
    fn init_real_additive_order_axioms(&mut self) -> Result<(), EnvError> {
        let real = Expr::const_(Name::from_string("Real"), vec![]);
        let inst_le = Expr::const_(Name::from_string("instLEReal"), vec![]);
        let inst_lt = Expr::const_(Name::from_string("instLTReal"), vec![]);
        let real_add = Expr::const_(Name::from_string("Real.add"), vec![]);

        let mk_le = |a: &Expr, b: &Expr| mk_real_cmp("LE.le", &real, &inst_le, a, b);
        let mk_lt = |a: &Expr, b: &Expr| mk_real_cmp("LT.lt", &real, &inst_lt, a, b);
        let mk_add =
            |a: &Expr, b: &Expr| Expr::app(Expr::app(real_add.clone(), a.clone()), b.clone());

        // Real.add_le_add_left : ∀ a b, LE.le a b → ∀ c, LE.le (add c a) (add c b)
        self.add_real_additive_axiom("Real.add_le_add_left", &real, &mk_le, &mk_le, &mk_add, true)?;
        // Real.add_le_add_right : ∀ a b, LE.le a b → ∀ c, LE.le (add a c) (add b c)
        self.add_real_additive_axiom(
            "Real.add_le_add_right",
            &real,
            &mk_le,
            &mk_le,
            &mk_add,
            false,
        )?;
        // Real.add_lt_add_left : ∀ a b, LT.lt a b → ∀ c, LT.lt (add c a) (add c b)
        self.add_real_additive_axiom("Real.add_lt_add_left", &real, &mk_lt, &mk_lt, &mk_add, true)?;
        // Real.add_lt_add_right : ∀ a b, LT.lt a b → ∀ c, LT.lt (add a c) (add b c)
        self.add_real_additive_axiom(
            "Real.add_lt_add_right",
            &real,
            &mk_lt,
            &mk_lt,
            &mk_add,
            false,
        )
    }

    /// Helper to declare additive monotonicity axioms:
    /// ∀ a b : Real, hyp_cmp(a,b) → ∀ c : Real, concl_cmp(add_form(a,c), add_form(b,c))
    ///
    /// `left`: if true, conclusion is `cmp(add(c,a), add(c,b))`;
    ///         if false, conclusion is `cmp(add(a,c), add(b,c))`.
    fn add_real_additive_axiom(
        &mut self,
        name: &str,
        real_ty: &Expr,
        hyp_cmp: &dyn Fn(&Expr, &Expr) -> Expr,
        concl_cmp: &dyn Fn(&Expr, &Expr) -> Expr,
        mk_add: &dyn Fn(&Expr, &Expr) -> Expr,
        left: bool,
    ) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_ty.clone());
            let (bv_id, bv) = b.fresh_local(real_ty.clone());
            let hab_ty = hyp_cmp(&a, &bv);
            let (h_id, _) = b.fresh_local(hab_ty.clone());
            let (c_id, c) = b.fresh_local(real_ty.clone());
            let (lhs, rhs) = if left {
                (mk_add(&c, &a), mk_add(&c, &bv))
            } else {
                (mk_add(&a, &c), mk_add(&bv, &c))
            };
            let body = concl_cmp(&lhs, &rhs);
            let e = b.mk_pi(c_id, BinderInfo::Default, real_ty.clone(), body);
            let e = b.mk_pi(h_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, real_ty.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, real_ty.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// Bridge axioms connecting Real ordering to Nat.ble for concrete closing.
    ///
    /// Enables kernel-verified False derivation for Real chains with
    /// non-negative concrete endpoints, eliminating trustedArith.
    fn init_real_ofnat_bridge_axioms(&mut self) -> Result<(), EnvError> {
        // Bridge axioms reference Nat.ble, Bool.false, Bool.true in the axiom type.
        // init_nat_cmp() declares Nat.ble/beq/blt and calls init_bool() internally.
        // Missing this caused "Unknown constant: Bool/Nat.ble" in non-prelude paths
        // (#2422 Phase D.5 finding from [P1]849).
        self.init_nat_cmp()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let real = Expr::const_(Name::from_string("Real"), vec![]);
        let real_ofnat = Expr::const_(Name::from_string("Real.ofNat"), vec![]);
        let nat_ble = Expr::const_(Name::from_string("Nat.ble"), vec![]);

        // ble(m,n)=false → le(ofNat m)(ofNat n) → False
        self.add_real_ofnat_bridge_axiom(
            "Real.not_ofNat_le_of_ble_false",
            &nat,
            &real,
            &real_ofnat,
            &nat_ble,
            false,
            "Bool.false",
            "LE.le",
            "instLEReal",
        )?;
        // ble(n,m)=true → lt(ofNat m)(ofNat n) → False
        self.add_real_ofnat_bridge_axiom(
            "Real.not_ofNat_lt_of_ble_true",
            &nat,
            &real,
            &real_ofnat,
            &nat_ble,
            true,
            "Bool.true",
            "LT.lt",
            "instLTReal",
        )
    }

    /// Build and declare a single Real.ofNat bridge axiom:
    /// ∀ m n : Nat, @Eq Bool (Nat.ble <a> <b>) <bool_val> →
    ///   @<cmp> Real <inst> (Real.ofNat m) (Real.ofNat n) → False
    #[allow(clippy::too_many_arguments)]
    fn add_real_ofnat_bridge_axiom(
        &mut self,
        name: &str,
        nat: &Expr,
        real: &Expr,
        real_ofnat: &Expr,
        nat_ble: &Expr,
        ble_args_reversed: bool,
        bool_val: &str,
        cmp_name: &str,
        cmp_inst_name: &str,
    ) -> Result<(), EnvError> {
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let false_ty = Expr::const_(Name::from_string("False"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let cmp_inst = Expr::const_(Name::from_string(cmp_inst_name), vec![]);

        let bridge_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat.clone());
            let (n_id, n) = b.fresh_local(nat.clone());
            let (ble_first, ble_second) = if ble_args_reversed {
                (n.clone(), m.clone())
            } else {
                (m.clone(), n.clone())
            };
            let ble_app = Expr::app(Expr::app(nat_ble.clone(), ble_first), ble_second);
            let bool_val_expr = Expr::const_(Name::from_string(bool_val), vec![]);
            let eq_type = Expr::app(Expr::app(Expr::app(eq, bool_ty), ble_app), bool_val_expr);
            let (h_eq_id, _) = b.fresh_local(eq_type.clone());
            let ofnat_m = Expr::app(real_ofnat.clone(), m);
            let ofnat_n = Expr::app(real_ofnat.clone(), n);
            let cmp_expr = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string(cmp_name), vec![Level::zero()]),
                            real.clone(),
                        ),
                        cmp_inst,
                    ),
                    ofnat_m,
                ),
                ofnat_n,
            );
            let (h_cmp_id, _) = b.fresh_local(cmp_expr.clone());
            let e = b.mk_pi(h_cmp_id, BinderInfo::Default, cmp_expr, false_ty);
            let e = b.mk_pi(h_eq_id, BinderInfo::Default, eq_type, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: bridge_type,
        })
    }

    /// Bridge axioms connecting Real.ofInt ordering to Int-level ordering.
    ///
    /// Enables kernel-verified False derivation for Real chains with negative
    /// integer endpoints. The approach: the axiom connects a Real-level ordering
    /// to an Int-level ordering, and the caller provides an Int-level proof of
    /// False (via NonNeg.casesOn) as evidence.
    ///
    /// `Real.not_ofInt_le`: ∀ a b : Int, (Int.le a b → False) →
    ///   LE.le Real instLEReal (Real.ofInt a) (Real.ofInt b) → False
    /// `Real.not_ofInt_lt`: ∀ a b : Int, (Int.lt a b → False) →
    ///   LT.lt Real instLTReal (Real.ofInt a) (Real.ofInt b) → False
    fn init_real_ofint_bridge_axioms(&mut self) -> Result<(), EnvError> {
        let int = Expr::const_(Name::from_string("Int"), vec![]);
        let real = Expr::const_(Name::from_string("Real"), vec![]);
        let real_ofint = Expr::const_(Name::from_string("Real.ofInt"), vec![]);
        let inst_le_real = Expr::const_(Name::from_string("instLEReal"), vec![]);
        let inst_lt_real = Expr::const_(Name::from_string("instLTReal"), vec![]);

        // Real.not_ofInt_le
        self.add_real_ofint_bridge_axiom(
            "Real.not_ofInt_le",
            &int,
            &real,
            &real_ofint,
            "LE.le",
            &inst_le_real,
            "Int.le",
        )?;
        // Real.not_ofInt_lt
        self.add_real_ofint_bridge_axiom(
            "Real.not_ofInt_lt",
            &int,
            &real,
            &real_ofint,
            "LT.lt",
            &inst_lt_real,
            "Int.lt",
        )
    }

    /// Build and declare a single Real.ofInt bridge axiom:
    /// ∀ a b : Int, (int_cmp a b → False) →
    ///   @<real_cmp> Real <inst> (Real.ofInt a) (Real.ofInt b) → False
    #[allow(clippy::too_many_arguments)]
    fn add_real_ofint_bridge_axiom(
        &mut self,
        name: &str,
        int_ty: &Expr,
        real_ty: &Expr,
        real_ofint: &Expr,
        real_cmp_name: &str,
        real_cmp_inst: &Expr,
        int_cmp_name: &str,
    ) -> Result<(), EnvError> {
        let false_ty = Expr::const_(Name::from_string("False"), vec![]);

        let bridge_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_ty.clone());
            let (bv_id, bv) = b.fresh_local(int_ty.clone());
            // Int-level ordering: int_cmp a b (e.g., Int.le a b)
            let int_cmp_expr = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string(int_cmp_name), vec![]),
                    a.clone(),
                ),
                bv.clone(),
            );
            // Hypothesis: (int_cmp a b → False)
            let not_int_cmp = Expr::pi(BinderInfo::Default, int_cmp_expr.clone(), false_ty.clone());
            let (h_not_id, _) = b.fresh_local(not_int_cmp.clone());
            // Real-level ordering: @real_cmp Real inst (Real.ofInt a) (Real.ofInt b)
            let ofint_a = Expr::app(real_ofint.clone(), a);
            let ofint_b = Expr::app(real_ofint.clone(), bv);
            let real_cmp_expr = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string(real_cmp_name), vec![Level::zero()]),
                            real_ty.clone(),
                        ),
                        real_cmp_inst.clone(),
                    ),
                    ofint_a,
                ),
                ofint_b,
            );
            let (h_real_id, _) = b.fresh_local(real_cmp_expr.clone());
            let e = b.mk_pi(h_real_id, BinderInfo::Default, real_cmp_expr, false_ty);
            let e = b.mk_pi(h_not_id, BinderInfo::Default, not_int_cmp, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, int_ty.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_ty.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: bridge_type,
        })
    }

    /// Downcast axioms for converting Real-level ordering to Int-level ordering.
    ///
    /// Enables the Real additive path to build its chain at the Int level (where
    /// `mk_int_concrete_false` already works) instead of requiring `Eq.subst`
    /// folding of `Real.add` trees.
    ///
    /// Axioms:
    /// - `Real.ofNat_eq_ofInt : ∀ n : Nat, Eq Real (Real.ofNat n) (Real.ofInt (Int.ofNat n))`
    /// - `Real.ofInt_le_to_Int : ∀ a b : Int, LE.le Real instLEReal (Real.ofInt a) (Real.ofInt b) → Int.le a b`
    /// - `Real.ofInt_lt_to_Int : ∀ a b : Int, LT.lt Real instLTReal (Real.ofInt a) (Real.ofInt b) → Int.lt a b`
    ///
    /// Required by bridge LRA Farkas additive proof reconstruction (#302).
    fn init_real_int_downcast_axioms(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let int = Expr::const_(Name::from_string("Int"), vec![]);
        let real = Expr::const_(Name::from_string("Real"), vec![]);
        let real_ofnat = Expr::const_(Name::from_string("Real.ofNat"), vec![]);
        let real_ofint = Expr::const_(Name::from_string("Real.ofInt"), vec![]);
        let int_ofnat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let inst_le = Expr::const_(Name::from_string("instLEReal"), vec![]);
        let inst_lt = Expr::const_(Name::from_string("instLTReal"), vec![]);

        // Real.ofNat_eq_ofInt : ∀ n : Nat, Eq Real (Real.ofNat n) (Real.ofInt (Int.ofNat n))
        {
            let eq_real = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let lhs = Expr::app(real_ofnat, n.clone());
            let rhs = Expr::app(real_ofint.clone(), Expr::app(int_ofnat, n));
            let body = Expr::app(Expr::app(Expr::app(eq_real, real.clone()), lhs), rhs);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat, body);
            let type_ = b.finish(e);
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Real.ofNat_eq_ofInt"),
                level_params: vec![],
                type_,
            })?;
        }

        // Real.ofInt_le_to_Int : ∀ a b : Int,
        //   @LE.le Real instLEReal (Real.ofInt a) (Real.ofInt b) → Int.le a b
        self.add_real_ofint_downcast_axiom(
            "Real.ofInt_le_to_Int",
            &int,
            &real,
            &real_ofint,
            "LE.le",
            &inst_le,
            "Int.le",
        )?;

        // Real.ofInt_lt_to_Int : ∀ a b : Int,
        //   @LT.lt Real instLTReal (Real.ofInt a) (Real.ofInt b) → Int.lt a b
        self.add_real_ofint_downcast_axiom(
            "Real.ofInt_lt_to_Int",
            &int,
            &real,
            &real_ofint,
            "LT.lt",
            &inst_lt,
            "Int.lt",
        )?;

        // Real.ofInt_add: cast-movement axiom for additive downcast (#2599)
        self.add_real_ofint_add_axiom(&int, &real, &real_ofint)
    }

    /// `Real.ofInt_add : ∀ m n : Int, Eq Real (Real.ofInt (Int.add m n)) (Real.add (Real.ofInt m) (Real.ofInt n))`
    ///
    /// Cast-movement axiom enabling normalization of `Real.add(Real.ofInt m, Real.ofInt n)`
    /// to `Real.ofInt(Int.add m n)` for the Int downcast path (#2599).
    fn add_real_ofint_add_axiom(
        &mut self,
        int_ty: &Expr,
        real_ty: &Expr,
        real_ofint: &Expr,
    ) -> Result<(), EnvError> {
        let eq_real = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let real_add = Expr::const_(Name::from_string("Real.add"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(int_ty.clone());
        let (n_id, n) = b.fresh_local(int_ty.clone());
        let lhs = Expr::app(
            real_ofint.clone(),
            Expr::app(Expr::app(int_add, m.clone()), n.clone()),
        );
        let rhs = Expr::app(
            Expr::app(real_add, Expr::app(real_ofint.clone(), m)),
            Expr::app(real_ofint.clone(), n),
        );
        let body = Expr::app(Expr::app(Expr::app(eq_real, real_ty.clone()), lhs), rhs);
        let e = b.mk_pi(n_id, BinderInfo::Default, int_ty.clone(), body);
        let e = b.mk_pi(m_id, BinderInfo::Default, int_ty.clone(), e);
        let type_ = b.finish(e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Real.ofInt_add"),
            level_params: vec![],
            type_,
        })
    }

    /// Build and declare a single Real.ofInt downcast axiom:
    /// ∀ a b : Int, @<real_cmp> Real <inst> (Real.ofInt a) (Real.ofInt b) → int_cmp a b
    #[allow(clippy::too_many_arguments)]
    fn add_real_ofint_downcast_axiom(
        &mut self,
        name: &str,
        int_ty: &Expr,
        real_ty: &Expr,
        real_ofint: &Expr,
        real_cmp_name: &str,
        real_cmp_inst: &Expr,
        int_cmp_name: &str,
    ) -> Result<(), EnvError> {
        let dc_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_ty.clone());
            let (bv_id, bv) = b.fresh_local(int_ty.clone());

            // Real-level ordering: @real_cmp Real inst (Real.ofInt a) (Real.ofInt b)
            let ofint_a = Expr::app(real_ofint.clone(), a.clone());
            let ofint_b = Expr::app(real_ofint.clone(), bv.clone());
            let real_cmp_expr = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string(real_cmp_name), vec![Level::zero()]),
                            real_ty.clone(),
                        ),
                        real_cmp_inst.clone(),
                    ),
                    ofint_a,
                ),
                ofint_b,
            );
            let (h_real_id, _) = b.fresh_local(real_cmp_expr.clone());

            // Int-level ordering: int_cmp a b
            let int_cmp_expr = Expr::app(
                Expr::app(Expr::const_(Name::from_string(int_cmp_name), vec![]), a),
                bv,
            );

            let e = b.mk_pi(h_real_id, BinderInfo::Default, real_cmp_expr, int_cmp_expr);
            let e = b.mk_pi(bv_id, BinderInfo::Default, int_ty.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_ty.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: dc_type,
        })
    }

    /// Add a transitivity axiom: ∀ a b c : Real, op_ab(a,b) → op_bc(b,c) → op_ac(a,c)
    fn add_real_trans_axiom(
        &mut self,
        name: &str,
        real_ty: &Expr,
        op_ab: &dyn Fn(&Expr, &Expr) -> Expr,
        op_bc: &dyn Fn(&Expr, &Expr) -> Expr,
        op_ac: &dyn Fn(&Expr, &Expr) -> Expr,
    ) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(real_ty.clone());
            let (bv_id, bv) = b.fresh_local(real_ty.clone());
            let (c_id, c) = b.fresh_local(real_ty.clone());
            let hab_ty = op_ab(&a, &bv);
            let (hab_id, _) = b.fresh_local(hab_ty.clone());
            let hbc_ty = op_bc(&bv, &c);
            let (hbc_id, _) = b.fresh_local(hbc_ty.clone());
            let body = op_ac(&a, &c);
            let e = b.mk_pi(hbc_id, BinderInfo::Default, hbc_ty, body);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_pi(c_id, BinderInfo::Default, real_ty.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, real_ty.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, real_ty.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// Initialize instHAddReal : HAdd Real Real Real
    ///
    /// ```text
    /// instance instHAddReal : HAdd Real Real Real where
    ///   hAdd := Real.add
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.real_hadd_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_real_hadd_inst(&mut self) -> Result<(), EnvError> {
        if self.real_hadd_inst_init {
            return Ok(());
        }

        self.init_hadd()?;
        self.init_real_complex_analysis()?;

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let real_add = Expr::const_(Name::from_string("Real.add"), vec![]);
        // Real lives in Type 0 (Sort 1), so universe parameter is 0
        // HAdd.{u v w} : Type u → Type v → Type w → Type (max u v w)
        // For Real (Type 0), u=v=w=0
        let hadd_mk = Expr::const_(
            Name::from_string("HAdd.mk"),
            vec![
                Level::zero(), // Real universe (Type 0)
                Level::zero(), // Real universe (Type 0)
                Level::zero(), // Real universe (result, Type 0)
            ],
        );

        // instHAddReal : HAdd Real Real Real := HAdd.mk Real.add
        let inst_type = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("HAdd"),
                        vec![Level::zero(), Level::zero(), Level::zero()],
                    ),
                    real_const.clone(),
                ),
                real_const.clone(),
            ),
            real_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(Expr::app(hadd_mk, real_const.clone()), real_const.clone()),
                real_const,
            ),
            real_add,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instHAddReal"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        // Register the instance with the kernel
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHAddReal"),
            class_name: Name::from_string("HAdd"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.real_hadd_inst_init = true;
        Ok(())
    }

    /// Initialize instHMulReal : HMul Real Real Real
    ///
    /// ```text
    /// instance instHMulReal : HMul Real Real Real where
    ///   hMul := Real.mul
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.real_hmul_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_real_hmul_inst(&mut self) -> Result<(), EnvError> {
        if self.real_hmul_inst_init {
            return Ok(());
        }

        self.init_hmul()?;
        self.init_real_complex_analysis()?;

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let real_mul = Expr::const_(Name::from_string("Real.mul"), vec![]);
        let hmul_mk = Expr::const_(
            Name::from_string("HMul.mk"),
            vec![Level::zero(), Level::zero(), Level::zero()],
        );

        let inst_type = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("HMul"),
                        vec![Level::zero(), Level::zero(), Level::zero()],
                    ),
                    real_const.clone(),
                ),
                real_const.clone(),
            ),
            real_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(Expr::app(hmul_mk, real_const.clone()), real_const.clone()),
                real_const,
            ),
            real_mul,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instHMulReal"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHMulReal"),
            class_name: Name::from_string("HMul"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.real_hmul_inst_init = true;
        Ok(())
    }

    /// Initialize instNegReal : Neg Real
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.real_neg_inst_init == true`
    /// ENSURES: On success, required dependencies (`neg`, `real_complex_analysis`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_real_neg_inst(&mut self) -> Result<(), EnvError> {
        if self.real_neg_inst_init {
            return Ok(());
        }

        self.init_neg()?;
        self.init_real_complex_analysis()?;

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let real_neg = Expr::const_(Name::from_string("Real.neg"), vec![]);
        let neg_mk = Expr::const_(Name::from_string("Neg.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Neg"), vec![Level::zero()]),
            real_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(neg_mk, real_const), real_neg);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instNegReal"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.real_neg_inst_init = true;
        Ok(())
    }

    /// Check if Real HAdd instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.real_hadd_inst_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_real_hadd_inst(&self) -> bool {
        self.real_hadd_inst_init
    }

    /// Check if Real HMul instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.real_hmul_inst_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_real_hmul_inst(&self) -> bool {
        self.real_hmul_inst_init
    }

    /// Check if Real Neg instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.real_neg_inst_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_real_neg_inst(&self) -> bool {
        self.real_neg_inst_init
    }

    /// Initialize instHPowRealNat : HPow Real Nat Real
    ///
    /// ```text
    /// instance instHPowRealNat : HPow Real Nat Real where
    ///   hPow := Real.pow
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.real_hpow_nat_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_real_hpow_nat_inst(&mut self) -> Result<(), EnvError> {
        if self.real_hpow_nat_inst_init {
            return Ok(());
        }

        self.init_hpow()?;
        self.init_real_complex_analysis()?;
        self.init_nat()?;

        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let real_pow = Expr::const_(Name::from_string("Real.pow"), vec![]);
        // Real and Nat both live in Type 0 (Sort 1), so universe parameter is 0
        // HPow.{u v w} : Type u → Type v → Type w → Type (max u v w)
        // For Real (Type 0) and Nat (Type 0), u=v=w=0
        let hpow_mk = Expr::const_(
            Name::from_string("HPow.mk"),
            vec![
                Level::zero(), // Real universe (Type 0)
                Level::zero(), // Nat universe (Type 0)
                Level::zero(), // Real universe (result, Type 0)
            ],
        );

        // instHPowRealNat : HPow Real Nat Real := HPow.mk Real.pow
        let inst_type = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("HPow"),
                        vec![Level::zero(), Level::zero(), Level::zero()],
                    ),
                    real_const.clone(),
                ),
                nat_const.clone(),
            ),
            real_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(Expr::app(hpow_mk, real_const.clone()), nat_const),
                real_const,
            ),
            real_pow,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instHPowRealNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        // Register the instance with the kernel
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHPowRealNat"),
            class_name: Name::from_string("HPow"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.real_hpow_nat_inst_init = true;
        Ok(())
    }

    /// Check if Real HPow Nat instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.real_hpow_nat_inst_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_real_hpow_nat_inst(&self) -> bool {
        self.real_hpow_nat_inst_init
    }

    /// Initialize OfNat instance for Real
    ///
    /// ```text
    /// instance (n : Nat) : OfNat Real n where
    ///   ofNat := Real.ofNat n
    /// ```
    ///
    /// This enables numeric literals like `0`, `1`, `42` to be used where Real is expected.
    /// The coercion uses Real.ofNat to convert the Nat literal to Real.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ofnat_real_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ofnat_real(&mut self) -> Result<(), EnvError> {
        if self.ofnat_real_inst_init {
            return Ok(());
        }

        // Dependencies
        self.init_ofnat()?;
        self.init_real_complex_analysis()?; // Ensures Real and Real.ofNat exist

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let real_const = Expr::const_(Name::from_string("Real"), vec![]);
        let real_ofnat = Expr::const_(Name::from_string("Real.ofNat"), vec![]);
        let ofnat_const = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
        let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);

        // instOfNatReal : (n : Nat) → OfNat Real n
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(Expr::app(ofnat_const.clone(), real_const.clone()), n);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        // value: λ n : Nat => OfNat.mk (Real.ofNat n)
        // OfNat.mk {α} {n} (ofNat : α) : OfNat α n
        // We need: OfNat.mk Real n (Real.ofNat n)
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(Expr::app(ofnat_mk.clone(), real_const.clone()), n.clone()),
                Expr::app(real_ofnat.clone(), n),
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instOfNatReal"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        // Register the instance with the kernel
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instOfNatReal"),
            class_name: Name::from_string("OfNat"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.ofnat_real_inst_init = true;
        Ok(())
    }

    /// Check if OfNat Real instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.ofnat_real_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_ofnat_real(&self) -> bool {
        self.ofnat_real_inst_init
    }
}
