// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type definitions for proof certificates.
//!
//! Contains the core certificate types (`ProofCert`, `DefEqStep`, `CertError`)
//! and their helper display functions.

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId, Literal, MDataMap};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::name::Name;

use serde::{Deserialize, Serialize};

/// A proof certificate witnessing a typing derivation.
///
/// The certificate structure mirrors the expression structure but includes
/// all intermediate types needed for verification.
///
/// Certificates are serializable for proof archives and can be verified
/// independently by a certificate verifier.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[must_use = "proof certificates should be verified or stored"]
pub enum ProofCert {
    /// Certificate for Sort(l) : Sort(succ(l))
    Sort {
        /// Universe level of the Sort
        level: Level,
    },

    /// Certificate for `BVar` (de Bruijn index)
    /// Includes the expected type from context
    BVar {
        /// De Bruijn index
        idx: u32,
        /// Expected type from the typing context
        expected_type: Box<Expr>,
    },

    /// Certificate for `FVar` (free variable)
    /// Includes the type from local context
    FVar {
        /// Free variable identifier
        id: FVarId,
        /// Type of the free variable from local context
        type_: Box<Expr>,
    },

    /// Certificate for Const (constant reference)
    /// Includes instantiated type
    Const {
        /// Constant name
        name: Name,
        /// Universe level instantiation
        levels: Vec<Level>,
        /// Instantiated type of the constant
        type_: Box<Expr>,
    },

    /// Certificate for App: f a : B[a/x]
    /// Records: function cert, arg cert, and the instantiated result type
    App {
        /// Certificate for the function expression
        fn_cert: Box<ProofCert>,
        /// The Pi type of the function
        fn_type: Box<Expr>,
        /// Certificate for the argument expression
        arg_cert: Box<ProofCert>,
        /// Result type after substitution: B[a/x]
        result_type: Box<Expr>,
    },

    /// Certificate for Lam: λ (x : A). b : (x : A) → B
    /// Records: arg type cert, body cert (in extended context)
    Lam {
        /// Binder information (implicit, explicit, etc.)
        binder_info: BinderInfo,
        /// Certificate proving A : Sort(l)
        arg_type_cert: Box<ProofCert>,
        /// Certificate proving b : B in extended context
        body_cert: Box<ProofCert>,
        /// The resulting Pi type
        result_type: Box<Expr>,
    },

    /// Certificate for Pi: (x : A) → B : Sort(imax(l1, l2))
    Pi {
        /// Binder information (implicit, explicit, etc.)
        binder_info: BinderInfo,
        /// Certificate proving A : Sort(l1)
        arg_type_cert: Box<ProofCert>,
        /// Universe level l1 of the domain
        arg_level: Level,
        /// Certificate proving B : Sort(l2) in extended context
        body_type_cert: Box<ProofCert>,
        /// Universe level l2 of the codomain
        body_level: Level,
    },

    /// Certificate for Let: let x : A := v in b : B[v/x]
    Let {
        /// Certificate proving A : Sort(l)
        type_cert: Box<ProofCert>,
        /// Certificate proving v : A
        value_cert: Box<ProofCert>,
        /// Certificate proving b : B in extended context
        body_cert: Box<ProofCert>,
        /// Result type after substitution: B[v/x]
        result_type: Box<Expr>,
    },

    /// Certificate for Literal values
    Lit {
        /// The literal value
        lit: Literal,
        /// Type of the literal (Nat or String)
        type_: Box<Expr>,
    },

    /// Certificate for definitional equality check
    /// Used when checking e : T reduces to checking e : T' where T ≡ T'
    DefEq {
        /// Certificate for the inner expression
        inner: Box<ProofCert>,
        /// Expected type from context
        expected_type: Box<Expr>,
        /// Actual inferred type
        actual_type: Box<Expr>,
        /// Steps needed to show equivalence (for debugging/verification)
        eq_steps: Vec<DefEqStep>,
    },

    /// Certificate for `MData` (metadata wrapper)
    /// `MData` is transparent - the type is the type of the inner expression
    MData {
        /// Metadata map attached to the expression
        metadata: MDataMap,
        /// Certificate for the inner expression
        inner_cert: Box<ProofCert>,
        /// Result type (same as inner expression's type)
        result_type: Box<Expr>,
    },

    /// Certificate for Proj (projection from structure)
    /// Records the struct name, field index, and the type of the projected field
    Proj {
        /// Name of the structure type
        struct_name: Name,
        /// Field index in the structure
        idx: u32,
        /// Certificate for the expression being projected
        expr_cert: Box<ProofCert>,
        /// Type of the expression being projected
        expr_type: Box<Expr>,
        /// Type of the projected field
        field_type: Box<Expr>,
    },

    // ════════════════════════════════════════════════════════════════════════
    // Mode-specific certificates (Cubical, Classical, SetTheoretic)
    // ════════════════════════════════════════════════════════════════════════
    /// Certificate for CubicalInterval : Type (Sort 1)
    /// The interval type I has two elements (i0, i1) in Cubical type theory
    CubicalInterval,

    /// Certificate for CubicalI0 : I and CubicalI1 : I
    /// The endpoints of the interval
    CubicalEndpoint {
        /// true for I1, false for I0
        is_one: bool,
    },

    /// Certificate for CubicalPath { ty, left, right } : Sort(l)
    /// Path A a b is a type when A : Sort(l), a : A, b : A
    CubicalPath {
        /// Certificate for the type family A
        ty_cert: Box<ProofCert>,
        /// Universe level of the type family
        ty_level: Level,
        /// Certificate for the left endpoint a
        left_cert: Box<ProofCert>,
        /// Certificate for the right endpoint b
        right_cert: Box<ProofCert>,
    },

    /// Certificate for CubicalPathLam { body } : Path A (body[0/i]) (body[1/i])
    /// Path abstraction `<i> e` where i : I
    CubicalPathLam {
        /// Certificate for the path body expression
        body_cert: Box<ProofCert>,
        /// The type of the body (before abstracting interval var)
        body_type: Box<Expr>,
        /// The resulting Path type
        result_type: Box<Expr>,
    },

    /// Certificate for CubicalPathApp { path, arg } : A
    /// Path application p @ i where p : Path A a b and i : I
    CubicalPathApp {
        /// Certificate for the path expression being applied
        path_cert: Box<ProofCert>,
        /// Certificate for the interval argument
        arg_cert: Box<ProofCert>,
        /// The Path type of the path expression
        path_type: Box<Expr>,
        /// The result type (the type parameter A from Path A a b)
        result_type: Box<Expr>,
    },

    /// Certificate for CubicalHComp { ty, phi, u, base } : ty
    /// Homogeneous composition in Cubical type theory
    CubicalHComp {
        /// Certificate for the type parameter
        ty_cert: Box<ProofCert>,
        /// Certificate for the face formula φ : F
        phi_cert: Box<ProofCert>,
        /// Certificate for the partial element u : (i : I) → Partial φ A
        u_cert: Box<ProofCert>,
        /// Certificate for the base element a₀ : A
        base_cert: Box<ProofCert>,
        /// The result type A
        result_type: Box<Expr>,
    },

    /// Certificate for CubicalTransp { ty, phi, base } : ty[1/i]
    /// Transport along a path in Cubical type theory
    CubicalTransp {
        /// Certificate for the type family A : I → Type
        ty_cert: Box<ProofCert>,
        /// Certificate for the face formula φ : F
        phi_cert: Box<ProofCert>,
        /// Certificate for the base element a₀ : A(0)
        base_cert: Box<ProofCert>,
        /// The result type A(1)
        result_type: Box<Expr>,
    },

    /// Certificate for CubicalCoe { ty, r, s, base } : ty s
    /// Generalized coercion `coe^{r→s}` in Cubical type theory
    CubicalCoe {
        /// Certificate for the type-family line A : I → Sort u
        ty_cert: Box<ProofCert>,
        /// Certificate for the source endpoint r : I
        r_cert: Box<ProofCert>,
        /// Certificate for the target endpoint s : I
        s_cert: Box<ProofCert>,
        /// Certificate for the base element base : A r
        base_cert: Box<ProofCert>,
        /// The result type A s
        result_type: Box<Expr>,
    },

    /// Certificate for ZFCSet expressions : Set
    /// Various set constructions in ZFC
    ZFCSet {
        /// The specific set construction
        kind: ZFCSetCertKind,
        /// Always Set (the type of sets)
        result_type: Box<Expr>,
    },

    /// Certificate for ZFCMem { elem, set } : Prop
    /// Set membership ∈
    ZFCMem {
        /// Certificate for the element expression
        elem_cert: Box<ProofCert>,
        /// Certificate for the set expression
        set_cert: Box<ProofCert>,
    },

    /// Certificate for ZFCComprehension { var_ty, pred } : Set
    /// Set comprehension { x : A | P(x) }
    ZFCComprehension {
        /// Certificate for the variable type A
        var_ty_cert: Box<ProofCert>,
        /// Certificate for the predicate P : A → Prop
        pred_cert: Box<ProofCert>,
        /// The result type Set
        result_type: Box<Expr>,
    },

    // ════════════════════════════════════════════════════════════════════════
    // Impredicative mode certificates
    // ════════════════════════════════════════════════════════════════════════
    /// Certificate for SProp : Type 1
    /// SProp is the sort of strict propositions (always proof-irrelevant)
    SProp,

    /// Certificate for Squash A : SProp (when A : Sort u)
    /// Squash (propositional truncation) - all proofs are definitionally equal
    Squash {
        /// Certificate for the inner type being squashed
        inner_cert: Box<ProofCert>,
    },
}

/// Certificate variants for ZFC set expressions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ZFCSetCertKind {
    /// Empty set ∅
    Empty,
    /// Singleton {a}
    Singleton(Box<ProofCert>),
    /// Unordered pair {a, b}
    Pair(Box<ProofCert>, Box<ProofCert>),
    /// Union ⋃A
    Union(Box<ProofCert>),
    /// Power set P(A)
    PowerSet(Box<ProofCert>),
    /// Separation {x ∈ A | φ(x)}
    Separation {
        /// Certificate for the base set A
        set_cert: Box<ProofCert>,
        /// Certificate for the predicate φ
        pred_cert: Box<ProofCert>,
    },
    /// Replacement {F(x) | x ∈ A}
    Replacement {
        /// Certificate for the base set A
        set_cert: Box<ProofCert>,
        /// Certificate for the function F
        func_cert: Box<ProofCert>,
    },
    /// Infinity ω
    Infinity,
    /// Choice (AC)
    Choice(Box<ProofCert>),
}

/// A step in a definitional equality proof.
///
/// These steps record how the verifier establishes definitional equality
/// between types, useful for debugging and proof reconstruction.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DefEqStep {
    /// Reflexivity: e ≡ e
    Refl,
    /// Symmetry: e1 ≡ e2 implies e2 ≡ e1
    Symm(Box<DefEqStep>),
    /// Transitivity: e1 ≡ e2 and e2 ≡ e3 implies e1 ≡ e3
    Trans(Box<DefEqStep>, Box<DefEqStep>),
    /// Beta reduction: (λx.b) a ≡ b[a/x]
    Beta,
    /// Delta reduction: unfold constant definition
    Delta(Name),
    /// Zeta reduction: unfold let binding
    Zeta,
    /// Iota reduction: recursor computation rule
    Iota,
    /// Structural: congruence through constructors
    Struct(String, Vec<DefEqStep>),
}

/// Error during certificate verification
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum CertError {
    /// Type mismatch during verification
    #[error("Type mismatch at {location}: expected {expected:?}, got {actual:?}")]
    TypeMismatch {
        /// The expected type in this context.
        expected: Box<Expr>,
        /// The actual type found.
        actual: Box<Expr>,
        /// Description of where the mismatch occurred.
        location: String,
    },
    /// Unknown constant reference
    #[error("Unknown constant: {0:?}")]
    UnknownConst(Name),
    /// Unknown free variable
    #[error("Unknown free variable: {0:?}")]
    UnknownFVar(FVarId),
    /// Invalid de Bruijn index
    #[error("Invalid bound variable index: {0}")]
    InvalidBVar(u32),
    /// Certificate structure doesn't match expression
    #[error("Structure mismatch: expected {expected}, got {actual}")]
    StructureMismatch {
        /// The expected certificate structure.
        expected: String,
        /// The actual certificate structure.
        actual: String,
    },
    /// Definitional equality check failed
    #[error("Definitional equality failed: {left:?} ≢ {right:?}")]
    DefEqFailed {
        /// The left-hand side of the equality.
        left: Box<Expr>,
        /// The right-hand side of the equality.
        right: Box<Expr>,
    },
    /// Sort level mismatch
    #[error("Level mismatch: expected {expected:?}, got {actual:?}")]
    LevelMismatch {
        /// The expected universe level.
        expected: Level,
        /// The actual universe level.
        actual: Level,
    },
    /// Invalid certificate structure
    #[error("Invalid certificate: {0}")]
    InvalidCert(String),
    /// Mode-specific feature requires a different mode
    #[error(
        "Feature '{feature}' requires {required_mode} mode, but current mode is {current_mode}"
    )]
    ModeRequired {
        /// The feature that was attempted.
        feature: String,
        /// The mode required to use this feature.
        required_mode: CleanMode,
        /// The current mode that doesn't support the feature.
        current_mode: CleanMode,
    },
}

/// Get a descriptive name for certificate variant
pub fn cert_name(cert: &ProofCert) -> String {
    match cert {
        ProofCert::Sort { .. } => "Sort".to_string(),
        ProofCert::BVar { .. } => "BVar".to_string(),
        ProofCert::FVar { .. } => "FVar".to_string(),
        ProofCert::Const { .. } => "Const".to_string(),
        ProofCert::App { .. } => "App".to_string(),
        ProofCert::Lam { .. } => "Lam".to_string(),
        ProofCert::Pi { .. } => "Pi".to_string(),
        ProofCert::Let { .. } => "Let".to_string(),
        ProofCert::Lit { .. } => "Lit".to_string(),
        ProofCert::DefEq { .. } => "DefEq".to_string(),
        ProofCert::MData { .. } => "MData".to_string(),
        ProofCert::Proj { .. } => "Proj".to_string(),
        ProofCert::CubicalInterval => "CubicalInterval".to_string(),
        ProofCert::CubicalEndpoint { .. } => "CubicalEndpoint".to_string(),
        ProofCert::CubicalPath { .. } => "CubicalPath".to_string(),
        ProofCert::CubicalPathLam { .. } => "CubicalPathLam".to_string(),
        ProofCert::CubicalPathApp { .. } => "CubicalPathApp".to_string(),
        ProofCert::CubicalHComp { .. } => "CubicalHComp".to_string(),
        ProofCert::CubicalTransp { .. } => "CubicalTransp".to_string(),
        ProofCert::CubicalCoe { .. } => "CubicalCoe".to_string(),
        ProofCert::ZFCSet { .. } => "ZFCSet".to_string(),
        ProofCert::ZFCMem { .. } => "ZFCMem".to_string(),
        ProofCert::ZFCComprehension { .. } => "ZFCComprehension".to_string(),
        ProofCert::SProp => "SProp".to_string(),
        ProofCert::Squash { .. } => "Squash".to_string(),
    }
}

/// Get a descriptive name for expression variant
pub fn expr_name(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::BVar(_) => "BVar".to_string(),
        ExprKind::FVar(_) => "FVar".to_string(),
        ExprKind::Sort(_) => "Sort".to_string(),
        ExprKind::Const(_, _) => "Const".to_string(),
        ExprKind::App(_, _) => "App".to_string(),
        ExprKind::Lam(_, _, _) => "Lam".to_string(),
        ExprKind::Pi(_, _, _) => "Pi".to_string(),
        ExprKind::Let(_, _, _, _, _) => "Let".to_string(),
        ExprKind::Lit(_) => "Lit".to_string(),
        ExprKind::Proj(_, _, _) => "Proj".to_string(),
        ExprKind::MData(_, _) => "MData".to_string(),
        ExprKind::CubicalInterval => "CubicalInterval".to_string(),
        ExprKind::CubicalI0 => "CubicalI0".to_string(),
        ExprKind::CubicalI1 => "CubicalI1".to_string(),
        ExprKind::CubicalPath { .. } => "CubicalPath".to_string(),
        ExprKind::CubicalPathLam { .. } => "CubicalPathLam".to_string(),
        ExprKind::CubicalPathApp { .. } => "CubicalPathApp".to_string(),
        ExprKind::CubicalHComp { .. } => "CubicalHComp".to_string(),
        ExprKind::CubicalTransp { .. } => "CubicalTransp".to_string(),
        ExprKind::CubicalCoe { .. } => "CubicalCoe".to_string(),
        ExprKind::ZFCSet(_) => "ZFCSet".to_string(),
        ExprKind::ZFCMem { .. } => "ZFCMem".to_string(),
        ExprKind::ZFCComprehension { .. } => "ZFCComprehension".to_string(),
        ExprKind::SProp => "SProp".to_string(),
        ExprKind::Squash(_) => "Squash".to_string(),
    }
}
