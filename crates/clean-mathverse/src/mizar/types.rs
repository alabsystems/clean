// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mizar internal AST types.
//!
//! These types represent the structural content of Mizar's `mizar-items` XML
//! export. Mizar uses first-order logic with a soft typing system (modes,
//! adjectives, structures) quite different from dependent type theory, so
//! we preserve the full Mizar structure before translation.

use serde::{Deserialize, Serialize};

// ════════════════════════════════════════════════════════════════════════════
// Formulas
// ════════════════════════════════════════════════════════════════════════════

/// Mizar formula (first-order logic).
///
/// Mizar's logic is classical FOL with extensions for soft typing (`Is`),
/// thesis reference in proofs (`Thesis`), and explicit `Contradiction`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizFormula {
    /// Predicate application: `P[t1, ..., tn]`.
    Pred { name: String, args: Vec<MizTerm> },
    /// Negation: `not phi`.
    Not(Box<MizFormula>),
    /// Conjunction: `phi1 & phi2 & ...`.
    And(Vec<MizFormula>),
    /// Disjunction: `phi1 or phi2 or ...`.
    Or(Vec<MizFormula>),
    /// Implication: `phi1 implies phi2`.
    Implies(Box<MizFormula>, Box<MizFormula>),
    /// Biconditional: `phi1 iff phi2`.
    Iff(Box<MizFormula>, Box<MizFormula>),
    /// Universal quantification: `for x being T holds phi`.
    ForAll {
        var: String,
        ty: MizType,
        body: Box<MizFormula>,
    },
    /// Existential quantification: `ex x being T st phi`.
    Exists {
        var: String,
        ty: MizType,
        body: Box<MizFormula>,
    },
    /// Type judgment: `t is T`.
    Is { term: MizTerm, ty: MizType },
    /// Logical falsum.
    Contradiction,
    /// Current thesis in a proof block.
    Thesis,
}

// ════════════════════════════════════════════════════════════════════════════
// Terms
// ════════════════════════════════════════════════════════════════════════════

/// Mizar term.
///
/// Terms in Mizar include variables, numerals, functor applications,
/// aggregate constructors (for structures), selectors (field projections),
/// definite descriptions (`the`), Fraenkel set-builder terms, and `it`
/// (the definiendum in definitions).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizTerm {
    /// Variable reference.
    Var(String),
    /// Integer numeral.
    Numeral(i64),
    /// Functor application: `F(t1, ..., tn)`.
    Functor { name: String, args: Vec<MizTerm> },
    /// Aggregate constructor: `StructName(# f1, ..., fn)`.
    Aggregate {
        struct_name: String,
        fields: Vec<MizTerm>,
    },
    /// Selector (field projection): `the field of t`.
    Selector { field: String, arg: Box<MizTerm> },
    /// Definite description: `the T` (iota operator).
    The { ty: MizType },
    /// Fraenkel set-builder: `{ t where x1 is T1, ... : phi }`.
    Fraenkel {
        term: Box<MizTerm>,
        vars: Vec<(String, MizType)>,
        formula: Box<MizFormula>,
    },
    /// The definiendum in a definition (`it`).
    It,
}

// ════════════════════════════════════════════════════════════════════════════
// Types (soft typing system)
// ════════════════════════════════════════════════════════════════════════════

/// Mizar type (soft typing system).
///
/// Mizar types are not dependent types. Instead, they are "modes" (soft types)
/// that can be parameterized and decorated with adjectives (attributes).
/// Every Mizar object ultimately has type `set` at the foundation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizType {
    /// Mode type: `M of t1, ..., tn` (e.g., `Element of NAT`).
    Mode { name: String, args: Vec<MizTerm> },
    /// Structure type: `S over t1, ..., tn`.
    Struct { name: String, args: Vec<MizTerm> },
    /// Clustered type: `adj1 adj2 ... M` (mode with adjective cluster).
    Clustered {
        adjectives: Vec<MizAdjective>,
        base: Box<MizType>,
    },
    /// The universal type `set`.
    Set,
}

/// An adjective (attribute) in a cluster.
///
/// Adjectives are Mizar's way of expressing properties that are attached to
/// types. They can be negated (e.g., `non empty`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MizAdjective {
    pub name: String,
    pub negated: bool,
    pub args: Vec<MizTerm>,
}

// ════════════════════════════════════════════════════════════════════════════
// Article items
// ════════════════════════════════════════════════════════════════════════════

/// Mizar article item (top-level declaration).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizItem {
    Definition(MizDefinition),
    Theorem(MizTheorem),
    Scheme(MizScheme),
    Registration(MizRegistration),
    Notation(MizNotation),
}

/// A theorem with its label and optional proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizTheorem {
    pub label: String,
    pub proposition: MizFormula,
    pub proof: Option<MizProof>,
}

/// Definition block: mode, functor, predicate, or attribute.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizDefinition {
    /// Mode definition: `define M -> ...`.
    ModeDef {
        name: String,
        params: Vec<(String, MizType)>,
        expansion: Option<MizType>,
    },
    /// Functor definition: `define F(x) -> ...`.
    FunctorDef {
        name: String,
        params: Vec<(String, MizType)>,
        result_ty: MizType,
        value: Option<MizTerm>,
    },
    /// Predicate definition: `define P[x] means ...`.
    PredicateDef {
        name: String,
        params: Vec<(String, MizType)>,
        meaning: Option<MizFormula>,
    },
    /// Attribute definition: `define attr -> ...`.
    AttributeDef {
        name: String,
        params: Vec<(String, MizType)>,
        meaning: Option<MizFormula>,
    },
    /// Structure definition.
    StructDef {
        name: String,
        ancestors: Vec<String>,
        fields: Vec<(String, MizType)>,
    },
}

/// Scheme (second-order theorem with function/predicate parameters).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizScheme {
    pub name: String,
    pub premises: Vec<MizFormula>,
    pub conclusion: MizFormula,
}

/// Registration block: cluster registrations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizRegistration {
    /// Existential registration: `cluster adj1 adj2 ... for M`.
    Existential {
        adjectives: Vec<MizAdjective>,
        ty: MizType,
    },
    /// Conditional registration: `cluster adj1 -> adj2 for M`.
    Conditional {
        antecedent: Vec<MizAdjective>,
        consequent: Vec<MizAdjective>,
        ty: MizType,
    },
    /// Functorial registration: `cluster F(x) -> adj`.
    Functorial {
        term: MizTerm,
        adjectives: Vec<MizAdjective>,
    },
}

/// Notation declaration (synonyms, antonyms).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizNotation {
    Synonym { new_name: String, original: String },
    Antonym { new_name: String, original: String },
}

// ════════════════════════════════════════════════════════════════════════════
// Proofs
// ════════════════════════════════════════════════════════════════════════════

/// A Mizar proof block.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizProof {
    pub steps: Vec<MizProofStep>,
}

/// Individual proof steps.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizProofStep {
    /// `let x be T` (universal introduction).
    Let { var: String, ty: MizType },
    /// `assume phi` (implication introduction).
    Assume(MizFormula),
    /// `thus phi` (thesis refinement / conclusion step).
    Thus(MizFormula),
    /// `consider x being T such that phi` (witness).
    Consider {
        var: String,
        ty: MizType,
        condition: MizFormula,
    },
    /// `take t` (existential introduction).
    Take(MizTerm),
    /// `set x = t` (local definition).
    Set { var: String, value: MizTerm },
    /// `reconsider x as T` (type coercion).
    Reconsider { var: String, ty: MizType },
    /// Nested sub-proof block.
    SubProof(MizProof),
    /// Reference justification: `by label1, label2, ...`.
    ByRef(Vec<String>),
    /// `hereby` block (implicit diffuse reasoning).
    Hereby(Vec<MizProofStep>),
    /// `per cases` case split.
    PerCases {
        cases: Vec<(MizFormula, Vec<MizProofStep>)>,
    },
}

// ════════════════════════════════════════════════════════════════════════════
// Notation metadata
// ════════════════════════════════════════════════════════════════════════════

/// Kind of notation declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizNotationKind {
    /// A synonym maps a new name to an existing constructor.
    Synonym,
    /// An antonym maps a new name to the negation of an existing constructor.
    Antonym,
}

/// Cluster registration classification.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MizClusterType {
    /// Existential registration: asserts existence of an object with given adjectives.
    Existential,
    /// Conditional registration: if antecedent adjectives hold, then consequent adjectives hold.
    Conditional,
    /// Functorial registration: a functor application has given adjectives.
    Functorial,
}

// ════════════════════════════════════════════════════════════════════════════
// Parsed notation with metadata
// ════════════════════════════════════════════════════════════════════════════

/// A fully annotated notation declaration with kind, pattern, and origin.
///
/// This extends [`MizNotation`] with richer metadata for downstream tools
/// that need to understand the nature and provenance of notation mappings.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizAnnotatedNotation {
    /// What kind of notation this is (synonym or antonym).
    pub kind: MizNotationKind,
    /// The new pattern introduced by this notation.
    pub pattern: String,
    /// The original constructor or symbol this notation maps to.
    pub origin: String,
    /// The article that originally defined this notation (empty if local).
    pub source_article: String,
}

// ════════════════════════════════════════════════════════════════════════════
// Annotated registration with cluster type
// ════════════════════════════════════════════════════════════════════════════

/// A registration annotated with its cluster classification.
///
/// Wraps [`MizRegistration`] with a discriminant enum for dispatch and
/// any additional conditions (adjectives) used in the registration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizAnnotatedRegistration {
    /// The cluster type classification.
    pub cluster_type: MizClusterType,
    /// The adjective conditions appearing in this registration.
    pub conditions: Vec<MizAdjective>,
    /// The underlying registration data.
    pub registration: MizRegistration,
}

// ════════════════════════════════════════════════════════════════════════════
// Scheme metadata
// ════════════════════════════════════════════════════════════════════════════

/// Extended scheme representation with argument signatures.
///
/// Mizar schemes are second-order theorems parameterized by
/// function/predicate arguments. This struct augments [`MizScheme`]
/// with explicit argument type signatures for import fidelity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizSchemeSignature {
    /// Name of the scheme.
    pub name: String,
    /// Function arguments with arity information.
    pub func_args: Vec<MizSchemeFuncArg>,
    /// Predicate arguments with arity information.
    pub pred_args: Vec<MizSchemePredArg>,
    /// Premises of the scheme.
    pub premises: Vec<MizFormula>,
    /// Conclusion of the scheme.
    pub conclusion: MizFormula,
}

/// A function argument to a scheme (second-order function parameter).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizSchemeFuncArg {
    /// Name of this function parameter.
    pub name: String,
    /// Types of the input arguments.
    pub arg_types: Vec<MizType>,
    /// Return type.
    pub result_type: MizType,
}

/// A predicate argument to a scheme (second-order predicate parameter).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizSchemePredArg {
    /// Name of this predicate parameter.
    pub name: String,
    /// Types of the input arguments.
    pub arg_types: Vec<MizType>,
}

// ════════════════════════════════════════════════════════════════════════════
// Article and environment
// ════════════════════════════════════════════════════════════════════════════

/// A complete Mizar article (one `.miz` file).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizArticle {
    pub name: String,
    pub environ: MizEnviron,
    pub items: Vec<MizItem>,
}

impl MizArticle {
    /// Count items of each kind.
    #[must_use]
    pub fn item_counts(&self) -> MizArticleItemCounts {
        let mut counts = MizArticleItemCounts::default();
        for item in &self.items {
            match item {
                MizItem::Theorem(_) => counts.theorems += 1,
                MizItem::Definition(_) => counts.definitions += 1,
                MizItem::Scheme(_) => counts.schemes += 1,
                MizItem::Registration(_) => counts.registrations += 1,
                MizItem::Notation(_) => counts.notations += 1,
            }
        }
        counts
    }

    /// Whether this article has no items.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Number of environment dependencies (union of all directive lists).
    #[must_use]
    pub fn dependency_count(&self) -> usize {
        self.environ.all_dependencies().len()
    }
}

/// Item counts for a Mizar article.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizArticleItemCounts {
    pub theorems: usize,
    pub definitions: usize,
    pub schemes: usize,
    pub registrations: usize,
    pub notations: usize,
}

impl MizArticleItemCounts {
    /// Total number of items.
    #[must_use]
    pub fn total(&self) -> usize {
        self.theorems + self.definitions + self.schemes + self.registrations + self.notations
    }
}

/// Environment declarations (the `environ` block at the top of a Mizar article).
///
/// Lists the external articles and libraries that this article depends on.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MizEnviron {
    pub vocabularies: Vec<String>,
    pub notations: Vec<String>,
    pub constructors: Vec<String>,
    pub registrations: Vec<String>,
    pub requirements: Vec<String>,
    pub definitions: Vec<String>,
    pub equalities: Vec<String>,
    pub expansions: Vec<String>,
    pub schemes: Vec<String>,
    pub theorems: Vec<String>,
}

impl MizEnviron {
    /// Collect all unique dependency article names across all directives.
    #[must_use]
    pub fn all_dependencies(&self) -> Vec<String> {
        let mut deps: Vec<String> = Vec::new();
        let all_lists = [
            &self.vocabularies,
            &self.notations,
            &self.constructors,
            &self.registrations,
            &self.requirements,
            &self.definitions,
            &self.equalities,
            &self.expansions,
            &self.schemes,
            &self.theorems,
        ];
        for list in all_lists {
            for name in list {
                if !deps.contains(name) {
                    deps.push(name.clone());
                }
            }
        }
        deps
    }

    /// Whether this environment has any dependencies at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.vocabularies.is_empty()
            && self.notations.is_empty()
            && self.constructors.is_empty()
            && self.registrations.is_empty()
            && self.requirements.is_empty()
            && self.definitions.is_empty()
            && self.equalities.is_empty()
            && self.expansions.is_empty()
            && self.schemes.is_empty()
            && self.theorems.is_empty()
    }
}
