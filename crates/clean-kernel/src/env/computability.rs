// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Computability theory structures for Environment
//!
//! This module provides axioms and structures for computability theory:
//! - Turing machines and computability
//! - Decidability and semi-decidability
//! - Recursive and recursively enumerable sets
//! - Complexity theory (P, NP, PSPACE, etc.)
//! - Reductions and completeness
//! - Kolmogorov complexity
//! - Lambda calculus and combinatory logic

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Computability module
    ///
    /// Computability theory is the study of what can be computed and how
    /// efficiently. It provides foundations for understanding the limits
    /// of computation and formal systems.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.computability_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `list`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_computability(&mut self) -> Result<(), EnvError> {
        if self.computability_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Computability theory constants
        for name in &[
            // ================================================================
            // Turing machines and basic computability
            // ================================================================
            "Computability.TuringMachine", // abstract Turing machine
            "Computability.TMState",       // machine state
            "Computability.TMTape",        // tape configuration
            "Computability.TMTransition",  // transition function
            "Computability.TMComputes",    // M computes function f
            "Computability.TMHalts",       // machine halts on input
            "Computability.TMAccepts",     // machine accepts input
            "Computability.TMRejects",     // machine rejects input
            "Computability.TMDiverges",    // machine runs forever
            "Computability.UniversalTM",   // universal Turing machine
            "Computability.TMEncoding",    // encoding of TM as natural
            "Computability.InputEncoding", // encoding of inputs
            // ================================================================
            // Computability and decidability
            // ================================================================
            "Computability.Computable",         // computable function
            "Computability.PartialComputable",  // partial computable (partial recursive)
            "Computability.TotalComputable",    // total computable function
            "Computability.Decidable",          // decidable predicate/set
            "Computability.SemiDecidable",      // semi-decidable (r.e.)
            "Computability.Undecidable",        // undecidable
            "Computability.CoSemiDecidable",    // co-semi-decidable (co-r.e.)
            "Computability.ComputableReal",     // computable real number
            "Computability.ComputableSequence", // computable sequence
            // ================================================================
            // Recursive functions and sets
            // ================================================================
            "Computability.PrimitiveRecursive", // primitive recursive function
            "Computability.MuRecursive",        // mu-recursive (general recursive)
            "Computability.RecursiveSet",       // recursive (decidable) set
            "Computability.RecursivelyEnumerable", // recursively enumerable set
            "Computability.Creative",           // creative set
            "Computability.ProductiveFunction", // productive function
            "Computability.Simple",             // simple set
            "Computability.Immune",             // immune set
            "Computability.HyperimmuneSet",     // hyperimmune set
            "Computability.Cylinder",           // cylinder set
            // ================================================================
            // Fundamental theorems
            // ================================================================
            "Computability.ChurchTuringThesis", // Church-Turing thesis (axiom)
            "Computability.HaltingProblem",     // halting problem
            "Computability.HaltingUndecidable", // halting is undecidable
            "Computability.RicesTheorem",       // non-trivial properties undecidable
            "Computability.PostsTheorem",       // Post's theorem (arithmetic hierarchy)
            "Computability.SmnTheorem",         // s-m-n theorem (parameterization)
            "Computability.RecursionTheorem",   // Kleene's recursion theorem
            "Computability.FixedPointTheorem",  // fixed point theorem
            "Computability.EnumerationTheorem", // enumeration theorem
            // ================================================================
            // Reductions and degrees
            // ================================================================
            "Computability.ManyOneReducible", // A ≤_m B (many-one reduction)
            "Computability.TuringReducible",  // A ≤_T B (Turing reduction)
            "Computability.TruthTableReducible", // A ≤_tt B (truth-table reduction)
            "Computability.WeakTruthTableReducible", // A ≤_wtt B
            "Computability.ManyOneEquivalent", // A ≡_m B
            "Computability.TuringEquivalent", // A ≡_T B
            "Computability.TuringDegree",     // Turing degree
            "Computability.ManyOneDegree",    // many-one degree
            "Computability.JumpOperator",     // Turing jump X'
            "Computability.DoubleJump",       // double jump X''
            "Computability.MathverseJump",    // ω-jump
            "Computability.DegreeZero",       // degree of computable sets
            "Computability.DegreeZeroPrime",  // degree of halting problem
            // ================================================================
            // Completeness
            // ================================================================
            "Computability.ManyOneComplete", // m-complete for a class
            "Computability.TuringComplete",  // T-complete for a class
            "Computability.REComplete",      // complete for r.e. sets
            "Computability.CoREComplete",    // complete for co-r.e. sets
            // ================================================================
            // Arithmetic hierarchy
            // ================================================================
            "Computability.Sigma0",              // Σ⁰ₙ sets
            "Computability.Pi0",                 // Π⁰ₙ sets
            "Computability.Delta0",              // Δ⁰ₙ sets
            "Computability.ArithmeticHierarchy", // the full hierarchy
            "Computability.SigmaComplete",       // Σ-complete
            "Computability.PiComplete",          // Π-complete
            // ================================================================
            // Complexity theory - time
            // ================================================================
            "Computability.TIME",       // TIME(f(n)) class
            "Computability.DTIME",      // deterministic time
            "Computability.NTIME",      // nondeterministic time
            "Computability.P",          // polynomial time
            "Computability.NP",         // nondeterministic polynomial
            "Computability.coNP",       // complement of NP
            "Computability.EXP",        // exponential time
            "Computability.NEXP",       // nondeterministic exponential
            "Computability.EXPTIME",    // 2^poly(n) time
            "Computability.DOUBLE_EXP", // 2^2^poly(n) time
            // ================================================================
            // Complexity theory - space
            // ================================================================
            "Computability.SPACE",    // SPACE(f(n)) class
            "Computability.DSPACE",   // deterministic space
            "Computability.NSPACE",   // nondeterministic space
            "Computability.L",        // logarithmic space
            "Computability.NL",       // nondeterministic log space
            "Computability.PSPACE",   // polynomial space
            "Computability.NPSPACE",  // nondeterministic poly space
            "Computability.EXPSPACE", // exponential space
            // ================================================================
            // Complexity relationships
            // ================================================================
            "Computability.PvsNP",               // P vs NP problem (open)
            "Computability.NPComplete",          // NP-complete problems
            "Computability.NPHard",              // NP-hard problems
            "Computability.PSPACEComplete",      // PSPACE-complete
            "Computability.NLComplete",          // NL-complete
            "Computability.PolynomialReduction", // polynomial-time reduction
            "Computability.LogSpaceReduction",   // log-space reduction
            "Computability.CookLevinTheorem",    // SAT is NP-complete
            "Computability.SavitchTheorem",      // NSPACE(s) ⊆ DSPACE(s²)
            "Computability.ImmermanSzelepcsenyiTheorem", // NSPACE closed under complement
            "Computability.SpaceHierarchy",      // space hierarchy theorem
            "Computability.TimeHierarchy",       // time hierarchy theorem
            // ================================================================
            // Randomized complexity
            // ================================================================
            "Computability.BPP",  // bounded-error probabilistic poly
            "Computability.RP",   // randomized polynomial
            "Computability.coRP", // complement of RP
            "Computability.ZPP",  // zero-error probabilistic poly
            "Computability.PP",   // probabilistic polynomial
            "Computability.BPL",  // bounded-error prob log space
            // ================================================================
            // Circuit complexity
            // ================================================================
            "Computability.BooleanCircuit", // Boolean circuit
            "Computability.CircuitSize",    // circuit size
            "Computability.CircuitDepth",   // circuit depth
            "Computability.AC0",            // constant-depth circuits
            "Computability.NC",             // Nick's class
            "Computability.NC1",            // log-depth circuits
            "Computability.TC0",            // threshold circuits
            "Computability.PoverPoly",      // P/poly (non-uniform)
            // ================================================================
            // Kolmogorov complexity
            // ================================================================
            "Computability.KolmogorovComplexity",  // K(x)
            "Computability.ConditionalComplexity", // K(x|y)
            "Computability.PrefixComplexity",      // prefix-free complexity
            "Computability.Incompressible",        // random string
            "Computability.InvariantTheorem",      // K is machine-independent (up to O(1))
            "Computability.IncompressibleStrings", // most strings are random
            // ================================================================
            // Lambda calculus (computability connection)
            // ================================================================
            "Computability.LambdaTerm",       // lambda term
            "Computability.BetaReduction",    // β-reduction
            "Computability.BetaNormalForm",   // β-normal form
            "Computability.ChurchNumeral",    // Church encoding of naturals
            "Computability.ChurchBoolean",    // Church encoding of booleans
            "Computability.YCombinator",      // fixed point combinator
            "Computability.LambdaComputable", // λ-definable = computable
            "Computability.SKCombinator",     // S, K combinators
            "Computability.CombinatoryLogic", // combinatory logic
            // ================================================================
            // Oracle machines
            // ================================================================
            "Computability.OracleTM",               // oracle Turing machine
            "Computability.RelativizedComputation", // computation relative to oracle
            "Computability.OracleP",                // P^A (P with oracle A)
            "Computability.OracleNP",               // NP^A
            "Computability.BakerGillSolovay",       // relativization barrier
            // ================================================================
            // Interactive proofs
            // ================================================================
            "Computability.IP",             // interactive proofs
            "Computability.AM",             // Arthur-Merlin
            "Computability.MA",             // Merlin-Arthur
            "Computability.IPequalsPSPACE", // IP = PSPACE theorem
            "Computability.PCP",            // probabilistically checkable proofs
            "Computability.PCPTheorem",     // PCP theorem
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.computability_init = true;
        Ok(())
    }

    /// Check if Computability module has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_computability` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_computability(&self) -> bool {
        self.computability_init
    }
}
