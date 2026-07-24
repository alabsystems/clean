// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT proof DAG types.
//!
//! clean's internal representation of SMT-level proofs, independent of ay's
//! data structures. Can be populated from ay's `Proof` via `ay_bridge` or
//! from Alethe text via `alethe_parser`.

use std::collections::BTreeMap;

/// A term in the SMT proof DAG.
///
/// clean's representation of SMT-LIB terms, independent of ay's TermStore.
/// Uses arena allocation for efficient DAG sharing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SmtTerm {
    /// Named variable with sort.
    Var(String, SmtSort),
    /// Boolean constant.
    Bool(bool),
    /// Integer constant.
    Int(i64),
    /// Rational constant (numerator, denominator).
    Rational(i64, i64),
    /// Bitvector constant (value, width).
    BitVec(u64, u32),
    /// String constant.
    Str(String),
    /// Function application: (f arg1 arg2 ...).
    App(SmtSymbol, Vec<SmtTermId>),
    /// Negation: (not t).
    Not(SmtTermId),
    /// If-then-else: (ite c t e).
    Ite(SmtTermId, SmtTermId, SmtTermId),
    /// Let binding: (let ((x v)) body).
    Let(Vec<(String, SmtTermId)>, SmtTermId),
    /// Universal quantification: (forall ((x S)) body).
    Forall(Vec<(String, SmtSort)>, SmtTermId),
    /// Existential quantification: (exists ((x S)) body).
    Exists(Vec<(String, SmtSort)>, SmtTermId),
}

/// Term identifier (index into arena).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmtTermId(pub u32);

/// SMT sort.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SmtSort {
    Bool,
    Int,
    Real,
    BitVec(u32),
    Array(Box<SmtSort>, Box<SmtSort>),
    String,
    /// User-defined or uninterpreted sort.
    Named(String),
}

/// Function symbol (possibly indexed).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SmtSymbol {
    Named(String),
    Indexed(String, Vec<u32>),
}

/// A proof step in the SMT proof DAG.
#[derive(Debug, Clone)]
pub enum SmtProofStep {
    /// Input assertion from the problem.
    Assume(SmtTermId),

    /// Resolution inference.
    Resolution {
        clause: Vec<SmtTermId>,
        premises: Vec<SmtStepId>,
        pivot: Option<SmtTermId>,
    },

    /// Theory lemma with metadata.
    TheoryLemma {
        theory: SmtTheory,
        kind: TheoryLemmaDetail,
        clause: Vec<SmtTermId>,
    },

    /// Generic Alethe rule step.
    Step {
        rule: AletheRuleKind,
        clause: Vec<SmtTermId>,
        premises: Vec<SmtStepId>,
        args: Vec<SmtTermId>,
    },

    /// Subproof anchor.
    Anchor {
        end_step: SmtStepId,
        variables: Vec<(String, SmtSort)>,
    },
}

/// Step identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmtStepId(pub u32);

/// Theory classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SmtTheory {
    Core,
    Euf,
    Lra,
    Lia,
    Nra,
    Nia,
    Bv,
    Arrays,
    Datatypes,
    Fp,
    Strings,
}

impl std::fmt::Display for SmtTheory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtTheory::Core => write!(f, "Core"),
            SmtTheory::Euf => write!(f, "EUF"),
            SmtTheory::Lra => write!(f, "LRA"),
            SmtTheory::Lia => write!(f, "LIA"),
            SmtTheory::Nra => write!(f, "NRA"),
            SmtTheory::Nia => write!(f, "NIA"),
            SmtTheory::Bv => write!(f, "BV"),
            SmtTheory::Arrays => write!(f, "Arrays"),
            SmtTheory::Datatypes => write!(f, "Datatypes"),
            SmtTheory::Fp => write!(f, "FP"),
            SmtTheory::Strings => write!(f, "Strings"),
        }
    }
}

/// Detailed theory lemma kind (matches ay_core::TheoryLemmaKind).
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum TheoryLemmaDetail {
    EufTransitive,
    EufCongruent,
    EufCongruentPred,
    LraFarkas {
        /// (numerator, denominator) Farkas coefficients.
        coefficients: Vec<(i64, i64)>,
    },
    LiaGeneric {
        annotation: LiaDetail,
        /// Optional integer Farkas coefficients.
        /// When present, `check_lia_generic` uses these; otherwise it tries
        /// unit coefficients or structurally accepts.
        coefficients: Option<Vec<i64>>,
    },
    BvBitBlast {
        gate_type: Option<String>,
        width: Option<u32>,
    },
    ArraySelectStore {
        index_eq: bool,
    },
    ArrayExtensionality,
    FpToBv {
        operation: String,
    },
    /// General floating-point theory lemma (concrete IEEE 754 evaluation).
    FpGeneric,
    StringLength,
    StringContent,
    StringNormalForm,
    /// General EUF lemma checked via congruence closure.
    EufGeneric,
    /// Datatypes constructor injectivity: C(a..) = C(b..) -> ai = bi.
    DatatypesInjectivity,
    /// Datatypes constructor distinctness: C1(..) != C2(..).
    DatatypesDistinctness,
    /// Datatypes selector reduction: sel_i(C(a..)) = ai.
    DatatypesSelector,
    /// Datatypes tester reduction: is_C(C(..)) = true, is_C(D(..)) = false.
    DatatypesTester,
    /// Datatypes acyclicity: no term equals a proper subterm of itself.
    DatatypesAcyclicity,
    /// General datatypes lemma (try all axiom schemas).
    DatatypesGeneric,
    /// Non-linear real arithmetic witness (Positivstellensatz / SOS certificate).
    NraWitness(super::nra::NraWitness),
    /// Non-linear integer arithmetic witness (ideal membership / Psatz).
    NiaWitness(super::nra::NraWitness),
    /// Trust fallback.
    Generic,
}

/// LIA proof annotation.
#[derive(Debug, Clone)]
pub enum LiaDetail {
    BoundsGap,
    Divisibility,
    CuttingPlane {
        divisor: i64,
    },
    /// No annotation -- fall back to Farkas.
    FarkasOnly,
}

/// Alethe rule kind classification.
///
/// Covers the Alethe proof format rules. Not all are semantically checked
/// in Phase 1; unchecked rules are structurally accepted or trusted.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AletheRuleKind {
    // Boolean rules
    True,
    False,
    NotTrue,
    NotFalse,
    AndPos(u32),
    AndNeg,
    OrPos,
    OrNeg(u32),
    ImpliesPos,
    ImpliesNeg1,
    ImpliesNeg2,
    EquivPos1,
    EquivPos2,
    EquivNeg1,
    EquivNeg2,
    ItePos1,
    ItePos2,
    IteNeg1,
    IteNeg2,
    Contraction,

    // Resolution
    Resolution,
    ThResolution,

    // EUF step rules
    Refl,
    Symm,
    Trans,
    Cong,

    // EUF theory lemma step rules
    EqReflexive,
    EqTransitive,
    EqCongruent,
    EqCongruentPred,

    // LRA rules
    LaGeneric,
    LaTautology,
    LaDisequality,
    LaTotality,

    // LIA
    LiaGeneric,

    // BV
    BvBitblast,

    // Array
    ReadOverWritePos,
    ReadOverWriteNeg,
    Extensionality,

    // FP
    FpToBv,

    // String
    StringLength,
    StringDecompose,
    StringCodeInj,

    // Quantifier
    ForallInst,
    Skolem,

    // Subproof
    Subproof,
    Bind,

    // Simplification (structural)
    AllSimplify,
    BoolSimplify,
    ArithSimplify,

    // Trust / hole
    Trust,
    Hole,

    // DRUP
    Drup,

    /// Unknown or user-defined rule.
    Other(String),
}

impl std::fmt::Display for AletheRuleKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AletheRuleKind::True => write!(f, "true"),
            AletheRuleKind::False => write!(f, "false"),
            AletheRuleKind::Resolution => write!(f, "resolution"),
            AletheRuleKind::ThResolution => write!(f, "th_resolution"),
            AletheRuleKind::Refl => write!(f, "refl"),
            AletheRuleKind::Symm => write!(f, "symm"),
            AletheRuleKind::Trans => write!(f, "trans"),
            AletheRuleKind::Cong => write!(f, "cong"),
            AletheRuleKind::EqReflexive => write!(f, "eq_reflexive"),
            AletheRuleKind::EqTransitive => write!(f, "eq_transitive"),
            AletheRuleKind::EqCongruent => write!(f, "eq_congruent"),
            AletheRuleKind::EqCongruentPred => write!(f, "eq_congruent_pred"),
            AletheRuleKind::LaGeneric => write!(f, "la_generic"),
            AletheRuleKind::LaTautology => write!(f, "la_tautology"),
            AletheRuleKind::Trust => write!(f, "trust"),
            AletheRuleKind::Hole => write!(f, "hole"),
            AletheRuleKind::Other(name) => write!(f, "{name}"),
            _ => write!(f, "{self:?}"),
        }
    }
}

/// The complete proof DAG.
#[derive(Debug, Clone)]
pub struct SmtProofDag {
    /// Arena of terms.
    pub(crate) terms: Vec<SmtTerm>,
    /// Proof steps in topological order.
    pub(crate) steps: Vec<SmtProofStep>,
    /// Symbol declarations from the problem.
    pub(crate) declarations: BTreeMap<String, SmtSort>,
}

impl SmtProofDag {
    /// Create a new empty proof DAG.
    #[must_use]
    pub fn new() -> Self {
        Self {
            terms: Vec::new(),
            steps: Vec::new(),
            declarations: BTreeMap::new(),
        }
    }

    /// Add a term to the arena and return its ID.
    pub fn add_term(&mut self, term: SmtTerm) -> SmtTermId {
        let id = SmtTermId(self.terms.len() as u32);
        self.terms.push(term);
        id
    }

    /// Add a proof step and return its ID.
    pub fn add_step(&mut self, step: SmtProofStep) -> SmtStepId {
        let id = SmtStepId(self.steps.len() as u32);
        self.steps.push(step);
        id
    }

    /// Declare a symbol with its sort.
    pub fn declare(&mut self, name: String, sort: SmtSort) {
        self.declarations.insert(name, sort);
    }

    /// Look up a term by ID.
    #[must_use]
    pub fn term(&self, id: SmtTermId) -> Option<&SmtTerm> {
        self.terms.get(id.0 as usize)
    }

    /// Look up a step by ID.
    #[must_use]
    pub fn step(&self, id: SmtStepId) -> Option<&SmtProofStep> {
        self.steps.get(id.0 as usize)
    }

    /// Number of terms in the arena.
    #[must_use]
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Number of proof steps.
    #[must_use]
    pub fn num_steps(&self) -> usize {
        self.steps.len()
    }

    /// Extract the clause from a proof step, if applicable.
    #[must_use]
    pub fn step_clause(&self, id: SmtStepId) -> Option<&[SmtTermId]> {
        match self.step(id)? {
            SmtProofStep::Assume(t) => Some(std::slice::from_ref(t)),
            SmtProofStep::Resolution { clause, .. } => Some(clause),
            SmtProofStep::TheoryLemma { clause, .. } => Some(clause),
            SmtProofStep::Step { clause, .. } => Some(clause),
            SmtProofStep::Anchor { .. } => None,
        }
    }

    /// Check if two term IDs refer to terms that are negations of each other.
    ///
    /// Returns `true` if one is `Not(other)` or they are `Bool(true)` vs `Bool(false)`.
    #[must_use]
    pub fn are_complementary(&self, a: SmtTermId, b: SmtTermId) -> bool {
        let term_a = match self.term(a) {
            Some(t) => t,
            None => return false,
        };
        let term_b = match self.term(b) {
            Some(t) => t,
            None => return false,
        };

        match (term_a, term_b) {
            (SmtTerm::Not(inner), _) if *inner == b => true,
            (_, SmtTerm::Not(inner)) if *inner == a => true,
            (SmtTerm::Bool(v1), SmtTerm::Bool(v2)) => v1 != v2,
            _ => false,
        }
    }

    /// Check if a term ID represents an equality: `(= lhs rhs)`.
    ///
    /// Returns `Some((lhs, rhs))` if so.
    #[must_use]
    pub fn as_equality(&self, id: SmtTermId) -> Option<(SmtTermId, SmtTermId)> {
        match self.term(id)? {
            SmtTerm::App(SmtSymbol::Named(name), args) if name == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Check if a term is a negated equality: `(not (= lhs rhs))`.
    ///
    /// Returns `Some((lhs, rhs))` if so.
    #[must_use]
    pub fn as_negated_equality(&self, id: SmtTermId) -> Option<(SmtTermId, SmtTermId)> {
        match self.term(id)? {
            SmtTerm::Not(inner) => self.as_equality(*inner),
            _ => None,
        }
    }
}

impl Default for SmtProofDag {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dag_add_term_returns_sequential_ids() {
        let mut dag = SmtProofDag::new();
        let id0 = dag.add_term(SmtTerm::Bool(true));
        let id1 = dag.add_term(SmtTerm::Bool(false));
        assert_eq!(id0, SmtTermId(0));
        assert_eq!(id1, SmtTermId(1));
        assert_eq!(dag.num_terms(), 2);
    }

    #[test]
    fn test_dag_add_step_returns_sequential_ids() {
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let s0 = dag.add_step(SmtProofStep::Assume(t));
        let s1 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0],
            pivot: None,
        });
        assert_eq!(s0, SmtStepId(0));
        assert_eq!(s1, SmtStepId(1));
        assert_eq!(dag.num_steps(), 2);
    }

    #[test]
    fn test_dag_term_lookup() {
        let mut dag = SmtProofDag::new();
        let id = dag.add_term(SmtTerm::Int(42));
        assert_eq!(dag.term(id), Some(&SmtTerm::Int(42)));
        assert_eq!(dag.term(SmtTermId(999)), None);
    }

    #[test]
    fn test_dag_complementary_terms() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        assert!(dag.are_complementary(a, not_a));
        assert!(dag.are_complementary(not_a, a));

        let t = dag.add_term(SmtTerm::Bool(true));
        let f = dag.add_term(SmtTerm::Bool(false));
        assert!(dag.are_complementary(t, f));
        assert!(!dag.are_complementary(t, t));
    }

    #[test]
    fn test_dag_as_equality() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let eq = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        assert_eq!(dag.as_equality(eq), Some((a, b)));
        assert_eq!(dag.as_equality(a), None);
    }

    #[test]
    fn test_dag_as_negated_equality() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let eq = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        let neq = dag.add_term(SmtTerm::Not(eq));
        assert_eq!(dag.as_negated_equality(neq), Some((a, b)));
        assert_eq!(dag.as_negated_equality(eq), None);
    }

    #[test]
    fn test_dag_step_clause_extraction() {
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let assume_id = dag.add_step(SmtProofStep::Assume(t));

        let clause = dag.step_clause(assume_id);
        assert!(clause.is_some());
        assert_eq!(clause.unwrap().len(), 1);
        assert_eq!(clause.unwrap()[0], t);
    }

    #[test]
    fn test_dag_declare() {
        let mut dag = SmtProofDag::new();
        dag.declare("f".to_string(), SmtSort::Int);
        assert!(dag.declarations.contains_key("f"));
    }

    #[test]
    fn test_smt_theory_display() {
        assert_eq!(SmtTheory::Euf.to_string(), "EUF");
        assert_eq!(SmtTheory::Lra.to_string(), "LRA");
        assert_eq!(SmtTheory::Core.to_string(), "Core");
    }
}
