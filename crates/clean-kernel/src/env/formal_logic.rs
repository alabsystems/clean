// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Formal logic structures for Environment
//!
//! This module provides axioms and structures for mathematical logic:
//! - Propositional logic (syntax, semantics, proof systems)
//! - First-order logic (terms, formulas, quantifiers, models)
//! - Proof theory (natural deduction, sequent calculus, cut elimination)
//! - Model theory (structures, satisfaction, completeness, compactness)
//! - Modal logic (necessity, possibility, Kripke semantics)
//! - Non-classical logics (intuitionistic, linear, temporal)
//!
//! This module provides foundations for verifying SAT/SMT solvers and
//! understanding the metatheory of the theorem prover itself.

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Formal Logic module
    ///
    /// Mathematical logic studies formal systems and their properties.
    /// It provides the foundations for theorem proving and verification.
    ///
    /// Key areas:
    /// - Propositional logic: formulas built from atoms and connectives
    /// - First-order logic: adds quantifiers and predicates over domains
    /// - Proof theory: formal proof systems and their metatheory
    /// - Model theory: semantic structures and satisfaction relations
    /// - Modal logic: necessity, possibility, and accessibility
    ///
    /// Applications:
    /// - SAT/SMT solver verification
    /// - Proof assistant metatheory
    /// - Program verification foundations
    /// - Database query language semantics
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.formal_logic_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `bool`, `list`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_formal_logic(&mut self) -> Result<(), EnvError> {
        if self.formal_logic_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Formal logic constants
        for name in &[
            // ================================================================
            // Propositional Logic - Syntax
            // ================================================================
            "FormalLogic.PropFormula",      // propositional formula type
            "FormalLogic.PropVar",          // propositional variable
            "FormalLogic.PropTop",          // ⊤ (true constant)
            "FormalLogic.PropBot",          // ⊥ (false constant)
            "FormalLogic.PropNeg",          // ¬ (negation)
            "FormalLogic.PropAnd",          // ∧ (conjunction)
            "FormalLogic.PropOr",           // ∨ (disjunction)
            "FormalLogic.PropImpl",         // → (implication)
            "FormalLogic.PropIff",          // ↔ (biconditional)
            "FormalLogic.PropNand",         // ↑ (Sheffer stroke)
            "FormalLogic.PropNor",          // ↓ (Peirce arrow)
            "FormalLogic.PropXor",          // ⊕ (exclusive or)
            "FormalLogic.PropSubformula",   // subformula relation
            "FormalLogic.PropFormulaSize",  // size of formula
            "FormalLogic.PropFormulaDepth", // depth of formula tree
            // ================================================================
            // Propositional Logic - Semantics
            // ================================================================
            "FormalLogic.PropValuation",     // assignment: Var → Bool
            "FormalLogic.PropEval",          // evaluation under valuation
            "FormalLogic.PropSatisfies",     // v ⊨ φ (v satisfies φ)
            "FormalLogic.PropTautology",     // ⊨ φ (valid in all valuations)
            "FormalLogic.PropContradiction", // unsatisfiable formula
            "FormalLogic.PropSatisfiable",   // ∃v. v ⊨ φ
            "FormalLogic.PropEquivalent",    // φ ≡ ψ (logically equivalent)
            "FormalLogic.PropEntails",       // Γ ⊨ φ (semantic entailment)
            "FormalLogic.PropModel",         // model of formula set
            "FormalLogic.PropTruthTable",    // truth table representation
            // ================================================================
            // Propositional Logic - Normal Forms
            // ================================================================
            "FormalLogic.NNF",                 // negation normal form
            "FormalLogic.CNF",                 // conjunctive normal form
            "FormalLogic.DNF",                 // disjunctive normal form
            "FormalLogic.Clause",              // clause (disjunction of literals)
            "FormalLogic.Literal",             // literal (var or negated var)
            "FormalLogic.ClauseSet",           // clause set
            "FormalLogic.TseitinTransform",    // Tseitin transformation to CNF
            "FormalLogic.NNFTransform",        // NNF transformation
            "FormalLogic.CNFPreservesEquisat", // CNF preserves equisatisfiability
            "FormalLogic.DNFPreservesEquiv",   // DNF preserves equivalence
            // ================================================================
            // Propositional Logic - Proof Systems
            // ================================================================
            "FormalLogic.PropHilbert",          // Hilbert system axioms
            "FormalLogic.PropModusPonens",      // MP: φ, φ→ψ ⊢ ψ
            "FormalLogic.PropDeduction",        // deduction theorem: Γ,φ⊢ψ ↔ Γ⊢φ→ψ
            "FormalLogic.PropNaturalDeduction", // natural deduction system
            "FormalLogic.PropNDAndIntro",       // ∧-intro: Γ⊢φ, Γ⊢ψ → Γ⊢φ∧ψ
            "FormalLogic.PropNDAndElim1",       // ∧-elim1: Γ⊢φ∧ψ → Γ⊢φ
            "FormalLogic.PropNDAndElim2",       // ∧-elim2: Γ⊢φ∧ψ → Γ⊢ψ
            "FormalLogic.PropNDOrIntro1",       // ∨-intro1: Γ⊢φ → Γ⊢φ∨ψ
            "FormalLogic.PropNDOrIntro2",       // ∨-intro2: Γ⊢ψ → Γ⊢φ∨ψ
            "FormalLogic.PropNDOrElim",         // ∨-elim: Γ⊢φ∨ψ, Γ,φ⊢χ, Γ,ψ⊢χ → Γ⊢χ
            "FormalLogic.PropNDImplIntro",      // →-intro: Γ,φ⊢ψ → Γ⊢φ→ψ
            "FormalLogic.PropNDImplElim",       // →-elim: Γ⊢φ→ψ, Γ⊢φ → Γ⊢ψ
            "FormalLogic.PropNDNegIntro",       // ¬-intro: Γ,φ⊢⊥ → Γ⊢¬φ
            "FormalLogic.PropNDNegElim",        // ¬-elim: Γ⊢φ, Γ⊢¬φ → Γ⊢⊥
            "FormalLogic.PropNDBotElim",        // ⊥-elim: Γ⊢⊥ → Γ⊢φ
            "FormalLogic.PropNDRAA",            // RAA: Γ,¬φ⊢⊥ → Γ⊢φ (classical)
            // ================================================================
            // Propositional Logic - Sequent Calculus
            // ================================================================
            "FormalLogic.PropSequent",         // Γ ⊢ Δ (sequent)
            "FormalLogic.PropLK",              // classical sequent calculus LK
            "FormalLogic.PropLJ",              // intuitionistic sequent calculus LJ
            "FormalLogic.PropSequentAxiom",    // axiom: φ ⊢ φ
            "FormalLogic.PropSequentCut",      // cut: Γ⊢Δ,φ and φ,Γ'⊢Δ' → Γ,Γ'⊢Δ,Δ'
            "FormalLogic.PropSequentWeaken",   // weakening
            "FormalLogic.PropSequentContract", // contraction
            "FormalLogic.PropSequentExchange", // exchange
            "FormalLogic.PropCutElimination",  // cut elimination theorem (Hauptsatz)
            "FormalLogic.PropSubformulaProp",  // subformula property
            // ================================================================
            // Propositional Logic - SAT
            // ================================================================
            "FormalLogic.SAT",                  // SAT decision problem
            "FormalLogic.UNSAT",                // unsatisfiability
            "FormalLogic.SATNPComplete",        // SAT is NP-complete (Cook-Levin)
            "FormalLogic.DPLL",                 // DPLL algorithm schema
            "FormalLogic.UnitPropagation",      // unit propagation
            "FormalLogic.PureLiteralElim",      // pure literal elimination
            "FormalLogic.CDCL",                 // conflict-driven clause learning
            "FormalLogic.LearnedClause",        // learned clause
            "FormalLogic.ResolutionRefutation", // resolution refutation
            "FormalLogic.Resolution",           // resolution rule: C∨x, D∨¬x ⊢ C∨D
            "FormalLogic.ResolutionComplete",   // resolution completeness
            "FormalLogic.ResolutionSound",      // resolution soundness
            // ================================================================
            // First-Order Logic - Syntax
            // ================================================================
            "FormalLogic.FOTerm",            // first-order term
            "FormalLogic.FOVariable",        // variable
            "FormalLogic.FOConstant",        // constant symbol
            "FormalLogic.FOFunction",        // function symbol
            "FormalLogic.FOFormula",         // first-order formula
            "FormalLogic.FOPredicate",       // predicate symbol
            "FormalLogic.FOEquality",        // equality predicate =
            "FormalLogic.FOForall",          // ∀ (universal quantifier)
            "FormalLogic.FOExists",          // ∃ (existential quantifier)
            "FormalLogic.FONeg",             // ¬ (negation)
            "FormalLogic.FOAnd",             // ∧ (conjunction)
            "FormalLogic.FOOr",              // ∨ (disjunction)
            "FormalLogic.FOImpl",            // → (implication)
            "FormalLogic.FOSignature",       // signature (sorts, funcs, preds)
            "FormalLogic.FOFreeVars",        // free variables of formula
            "FormalLogic.FOBoundVars",       // bound variables of formula
            "FormalLogic.FOSentence",        // sentence (closed formula)
            "FormalLogic.FOSubstitution",    // substitution [t/x]
            "FormalLogic.FOCaptureAvoiding", // capture-avoiding substitution
            // ================================================================
            // First-Order Logic - Semantics
            // ================================================================
            "FormalLogic.FOStructure",      // first-order structure (model)
            "FormalLogic.FODomain",         // domain (universe) of structure
            "FormalLogic.FOInterpretation", // interpretation of symbols
            "FormalLogic.FOAssignment",     // variable assignment
            "FormalLogic.FOTermEval",       // term evaluation [[t]]
            "FormalLogic.FOSatisfaction",   // M,σ ⊨ φ (satisfaction)
            "FormalLogic.FOValid",          // ⊨ φ (valid in all structures)
            "FormalLogic.FOSatisfiable",    // ∃M. M ⊨ φ
            "FormalLogic.FOEntails",        // Γ ⊨ φ (semantic consequence)
            "FormalLogic.FOEquivalent",     // φ ≡ ψ (logically equivalent)
            "FormalLogic.FOTheory",         // theory = set of sentences
            "FormalLogic.FOModelOf",        // M is model of theory T
            // ================================================================
            // First-Order Logic - Normal Forms
            // ================================================================
            "FormalLogic.FOPrenexNormalForm", // prenex normal form (Q₁x₁...Qₙxₙ.φ)
            "FormalLogic.FOSkolemization",    // Skolemization (eliminate ∃)
            "FormalLogic.FOSkolemFunction",   // Skolem function
            "FormalLogic.FOHerbrandUniverse", // Herbrand universe
            "FormalLogic.FOHerbrandBase",     // Herbrand base (ground atoms)
            "FormalLogic.FOHerbrandInterpretation", // Herbrand interpretation
            "FormalLogic.HerbrandTheorem",    // Herbrand's theorem
            // ================================================================
            // First-Order Logic - Proof Theory
            // ================================================================
            "FormalLogic.FOHilbert",          // Hilbert-style proof system
            "FormalLogic.FONaturalDeduction", // natural deduction for FOL
            "FormalLogic.FONDForallIntro",    // ∀-intro: Γ⊢φ(x), x not free in Γ → Γ⊢∀x.φ
            "FormalLogic.FONDForallElim",     // ∀-elim: Γ⊢∀x.φ → Γ⊢φ[t/x]
            "FormalLogic.FONDExistsIntro",    // ∃-intro: Γ⊢φ[t/x] → Γ⊢∃x.φ
            "FormalLogic.FONDExistsElim",     // ∃-elim (with eigenvar condition)
            "FormalLogic.FOSequentLK",        // sequent calculus LK for FOL
            "FormalLogic.FOCutElimination",   // cut elimination for FOL
            // ================================================================
            // First-Order Logic - Metatheory
            // ================================================================
            "FormalLogic.FOSoundness",          // soundness: Γ⊢φ → Γ⊨φ
            "FormalLogic.FOCompleteness",       // completeness: Γ⊨φ → Γ⊢φ (Gödel)
            "FormalLogic.FOCompactness",        // compactness theorem
            "FormalLogic.FOLowenheimSkolem",    // Löwenheim-Skolem theorem
            "FormalLogic.FOUpwardLS",           // upward Löwenheim-Skolem
            "FormalLogic.FODownwardLS",         // downward Löwenheim-Skolem
            "FormalLogic.FOLindstrom",          // Lindström's theorem (characterization)
            "FormalLogic.FOCraigInterpolation", // Craig interpolation
            "FormalLogic.FOBethDefinability",   // Beth definability theorem
            // ================================================================
            // First-Order Logic - Decidability
            // ================================================================
            "FormalLogic.FOUndecidable",   // FOL validity is undecidable
            "FormalLogic.FOSemiDecidable", // FOL validity is semi-decidable
            "FormalLogic.FOMonadicDecidable", // monadic FOL is decidable
            "FormalLogic.FOBernaysSchonfinkel", // ∃*∀* fragment decidable
            "FormalLogic.FOAckermannClass", // Ackermann class decidable
            // ================================================================
            // First-Order Logic - Equality
            // ================================================================
            "FormalLogic.FOEqualityAxioms", // equality axioms (refl, symm, trans)
            "FormalLogic.FOCongruence",     // congruence (substitutivity)
            "FormalLogic.FOUnification",    // unification problem
            "FormalLogic.FOMGU",            // most general unifier
            "FormalLogic.FOUnificationDecidable", // first-order unification is decidable
            "FormalLogic.FOOccursCheck",    // occurs check
            // ================================================================
            // Model Theory - Basic Concepts
            // ================================================================
            "FormalLogic.MTElementaryEquiv", // elementary equivalence M ≡ N
            "FormalLogic.MTIsomorphism",     // isomorphism M ≅ N
            "FormalLogic.MTElementarySubstr", // elementary substructure M ≺ N
            "FormalLogic.MTDiagram",         // diagram of structure
            "FormalLogic.MTAtomicDiagram",   // atomic diagram
            "FormalLogic.MTElementaryDiagram", // elementary diagram
            "FormalLogic.MTType",            // type (set of formulas)
            "FormalLogic.MTCompleteType",    // complete type
            "FormalLogic.MTRealizedType",    // realized type
            "FormalLogic.MTOmittedType",     // omitted type
            "FormalLogic.MTSaturated",       // saturated model
            "FormalLogic.MTHomogeneous",     // homogeneous model
            "FormalLogic.MTAtomic",          // atomic model
            "FormalLogic.MTPrime",           // prime model
            // ================================================================
            // Model Theory - Theories
            // ================================================================
            "FormalLogic.MTComplete",               // complete theory
            "FormalLogic.MTCategorical",            // categorical theory
            "FormalLogic.MTUncountablyCategorical", // uncountably categorical
            "FormalLogic.MTKappaCategorical",       // κ-categorical
            "FormalLogic.MTModelComplete",          // model complete theory
            "FormalLogic.MTModelCompanion",         // model companion
            "FormalLogic.MTQuantifierElim",         // admits quantifier elimination
            "FormalLogic.MTStable",                 // stable theory
            "FormalLogic.MTOMinimal",               // o-minimal theory
            "FormalLogic.MTMorleyRank",             // Morley rank
            // ================================================================
            // Model Theory - Constructions
            // ================================================================
            "FormalLogic.MTUltraproduct",  // ultraproduct construction
            "FormalLogic.MTLosTheorem",    // Łoś theorem for ultraproducts
            "FormalLogic.MTChainUnion",    // union of elementary chain
            "FormalLogic.MTDirectedUnion", // directed union of structures
            "FormalLogic.MTOmittingTypes", // omitting types theorem
            "FormalLogic.MTRamseyTheory",  // Ramsey theory in model theory
            // ================================================================
            // Modal Logic - Syntax
            // ================================================================
            "FormalLogic.ModalFormula",   // modal formula type
            "FormalLogic.ModalBox",       // □ (necessity/always)
            "FormalLogic.ModalDiamond",   // ◇ (possibility/sometimes)
            "FormalLogic.ModalAt",        // @ (actually/named worlds)
            "FormalLogic.ModalNominal",   // nominal (world name)
            "FormalLogic.ModalDownArrow", // ↓ (binder in hybrid logic)
            // ================================================================
            // Modal Logic - Kripke Semantics
            // ================================================================
            "FormalLogic.KripkeFrame",        // frame (W, R)
            "FormalLogic.KripkeModel",        // model (F, V)
            "FormalLogic.Accessibility",      // accessibility relation R
            "FormalLogic.KripkeSatisfaction", // M,w ⊨ φ
            "FormalLogic.KripkeValidity",     // valid in frame/class
            "FormalLogic.KripkeFrameClass",   // class of frames
            // ================================================================
            // Modal Logic - Standard Systems
            // ================================================================
            "FormalLogic.ModalK",      // basic modal logic K
            "FormalLogic.ModalKAxiom", // K: □(p→q) → (□p → □q)
            "FormalLogic.ModalNec",    // necessitation: ⊢φ → ⊢□φ
            "FormalLogic.ModalT",      // T: □p → p (reflexivity)
            "FormalLogic.ModalD",      // D: □p → ◇p (seriality)
            "FormalLogic.Modal4",      // 4: □p → □□p (transitivity)
            "FormalLogic.Modal5",      // 5: ◇p → □◇p (Euclidean)
            "FormalLogic.ModalB",      // B: p → □◇p (symmetry)
            "FormalLogic.ModalS4",     // S4 = KT4 (preorder)
            "FormalLogic.ModalS5",     // S5 = KT45 (equivalence)
            "FormalLogic.ModalGL",     // GL: □(□p→p) → □p (Löb)
            "FormalLogic.ModalGrz",    // Grz: □(□(p→□p)→p) → p
            // ================================================================
            // Modal Logic - Frame Correspondence
            // ================================================================
            "FormalLogic.ModalCorrespondence", // correspondence theory
            "FormalLogic.FrameReflexive",      // T corresponds to reflexivity
            "FormalLogic.FrameTransitive",     // 4 corresponds to transitivity
            "FormalLogic.FrameSymmetric",      // B corresponds to symmetry
            "FormalLogic.FrameSerial",         // D corresponds to seriality
            "FormalLogic.FrameEuclidean",      // 5 corresponds to Euclidean
            "FormalLogic.SahlqvistCorr",       // Sahlqvist correspondence theorem
            // ================================================================
            // Modal Logic - Decidability and Complexity
            // ================================================================
            "FormalLogic.ModalKDecidable",  // K is decidable
            "FormalLogic.ModalS5Decidable", // S5 is decidable
            "FormalLogic.ModalPSPACE",      // modal logic PSPACE-complete
            "FormalLogic.ModalFMP",         // finite model property
            // ================================================================
            // Temporal Logic
            // ================================================================
            "FormalLogic.LTL",               // linear temporal logic
            "FormalLogic.LTLNext",           // X (next)
            "FormalLogic.LTLUntil",          // U (until)
            "FormalLogic.LTLGlobally",       // G (globally/always)
            "FormalLogic.LTLFinally",        // F (finally/eventually)
            "FormalLogic.LTLRelease",        // R (release)
            "FormalLogic.LTLWeak",           // W (weak until)
            "FormalLogic.LTLSemantics",      // LTL trace semantics
            "FormalLogic.CTL",               // computation tree logic
            "FormalLogic.CTLStar",           // CTL* (full branching time)
            "FormalLogic.CTLPathQuantifier", // A (all paths), E (exists path)
            "FormalLogic.LTLModelCheck",     // LTL model checking
            "FormalLogic.CTLModelCheck",     // CTL model checking
            "FormalLogic.BuchiAutomaton",    // Büchi automaton
            "FormalLogic.LTLToBuchi",        // LTL to Büchi translation
            // ================================================================
            // Intuitionistic Logic
            // ================================================================
            "FormalLogic.IntLogic",          // intuitionistic logic
            "FormalLogic.IntKripkeModel",    // Kripke model for IL
            "FormalLogic.IntPersistence",    // persistence (monotonicity)
            "FormalLogic.IntDoubleNegTrans", // double negation translation
            "FormalLogic.IntGlivenko",       // Glivenko's theorem
            "FormalLogic.IntBHK",            // BHK interpretation
            "FormalLogic.IntCurryHoward",    // Curry-Howard correspondence
            "FormalLogic.IntDisjProp",       // disjunction property
            "FormalLogic.IntExistProp",      // existence property
            // ================================================================
            // Linear Logic
            // ================================================================
            "FormalLogic.LinearLogic",          // linear logic
            "FormalLogic.LinearTensor",         // ⊗ (multiplicative conjunction)
            "FormalLogic.LinearPar",            // ⅋ (multiplicative disjunction)
            "FormalLogic.LinearWith",           // & (additive conjunction)
            "FormalLogic.LinearPlus",           // ⊕ (additive disjunction)
            "FormalLogic.LinearBang",           // ! (of course, exponential)
            "FormalLogic.LinearWhyNot",         // ? (why not, exponential)
            "FormalLogic.LinearOne",            // 1 (multiplicative unit)
            "FormalLogic.LinearBottom",         // ⊥ (multiplicative false)
            "FormalLogic.LinearTop",            // ⊤ (additive unit)
            "FormalLogic.LinearZero",           // 0 (additive false)
            "FormalLogic.LinearNegation",       // (·)⊥ (linear negation)
            "FormalLogic.LinearSequent",        // linear sequent calculus
            "FormalLogic.LinearCutElim",        // cut elimination for LL
            "FormalLogic.LinearPhaseSemantics", // phase semantics
            // ================================================================
            // Many-Valued and Fuzzy Logic
            // ================================================================
            "FormalLogic.ThreeValuedLogic", // Kleene/Łukasiewicz 3-valued
            "FormalLogic.FuzzyLogic",       // fuzzy logic [0,1]-valued
            "FormalLogic.FuzzyTNorm",       // t-norm conjunction
            "FormalLogic.FuzzyResiduum",    // residuum implication
            "FormalLogic.GodelLogic",       // Gödel logic (min t-norm)
            "FormalLogic.LukasiewiczLogic", // Łukasiewicz logic
            "FormalLogic.ProductLogic",     // product logic
            // ================================================================
            // Automated Theorem Proving
            // ================================================================
            "FormalLogic.ATPResolution",       // resolution for FOL
            "FormalLogic.ATPParamodulation",   // paramodulation (equality)
            "FormalLogic.ATPSuperposition",    // superposition calculus
            "FormalLogic.ATPOrderedRes",       // ordered resolution
            "FormalLogic.ATPSetOfSupport",     // set of support strategy
            "FormalLogic.ATPHyperresolution",  // hyperresolution
            "FormalLogic.ATPTableaux",         // analytic tableaux
            "FormalLogic.ATPConnectionMethod", // connection method
            "FormalLogic.ATPLeanCop",          // lean connection prover principles
        ] {
            let name_obj = Name::from_string(name);
            let decl = Declaration::Axiom {
                name: name_obj.clone(),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.formal_logic_init = true;
        Ok(())
    }

    /// Check if FormalLogic module has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_formal_logic` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_formal_logic(&self) -> bool {
        self.formal_logic_init
    }
}
