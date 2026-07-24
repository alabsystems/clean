// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core HOL types representing the shared type theory of HOL Light, HOL4,
//! HOL Zero, and Isabelle/HOL.
//!
//! HOL is a simple (non-dependent) type theory with:
//! - Base types: `bool`, `ind` (individuals), and user-defined type operators
//! - Type operators: `fun` (function space), applied to type arguments
//! - Terms: variables, constants, applications, and lambda abstractions
//! - Three axioms: extensionality, choice (Hilbert epsilon), infinity
//!
//! Reference: John Harrison, "HOL Light: An Overview" (2009).

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A HOL type (simple type theory, no dependent types).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HolType {
    /// Type variable: `'a`, `'b`, etc.
    TyVar(String),
    /// Type operator application: `op(args...)`.
    /// Base types are nullary: `bool = TyOp("bool", [])`, `ind = TyOp("ind", [])`.
    /// Function types: `A -> B = TyOp("fun", [A, B])`.
    TyOp(String, Vec<HolType>),
}

impl HolType {
    /// Convenience constructor for `bool`.
    #[must_use]
    pub fn bool() -> Self {
        Self::TyOp("bool".to_owned(), Vec::new())
    }

    /// Convenience constructor for `ind` (individuals / infinity type).
    #[must_use]
    pub fn ind() -> Self {
        Self::TyOp("ind".to_owned(), Vec::new())
    }

    /// Convenience constructor for function types `A -> B`.
    #[must_use]
    pub fn fun(domain: Self, codomain: Self) -> Self {
        Self::TyOp("fun".to_owned(), vec![domain, codomain])
    }

    /// Returns `true` if this is the `bool` type.
    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::TyOp(name, args) if name == "bool" && args.is_empty())
    }

    /// Returns `true` if this is a function type.
    #[must_use]
    pub fn is_fun(&self) -> bool {
        matches!(self, Self::TyOp(name, args) if name == "fun" && args.len() == 2)
    }

    /// If this is a function type, return `(domain, codomain)`.
    #[must_use]
    pub fn dest_fun(&self) -> Option<(&HolType, &HolType)> {
        match self {
            Self::TyOp(name, args) if name == "fun" && args.len() == 2 => {
                Some((&args[0], &args[1]))
            }
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

/// A HOL term (Church-style simply-typed lambda calculus).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HolTerm {
    /// Variable with name and type.
    Var(String, HolType),
    /// Constant with name and type (possibly polymorphic, instantiated).
    Const(String, HolType),
    /// Application: `f a`.
    App(Box<HolTerm>, Box<HolTerm>),
    /// Lambda abstraction: `\x:ty. body`.
    Abs(String, HolType, Box<HolTerm>),
}

impl HolTerm {
    /// Infer the HOL type of this term.
    ///
    /// Returns `None` if the term is ill-typed (e.g., application of a
    /// non-function).
    #[must_use]
    pub fn ty(&self) -> Option<HolType> {
        match self {
            Self::Var(_, ty) | Self::Const(_, ty) => Some(ty.clone()),
            Self::Abs(_, var_ty, body) => {
                let body_ty = body.ty()?;
                Some(HolType::fun(var_ty.clone(), body_ty))
            }
            Self::App(f, _) => {
                let f_ty = f.ty()?;
                let (_, codomain) = f_ty.dest_fun()?;
                Some(codomain.clone())
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Theorems & axioms
// ---------------------------------------------------------------------------

/// A HOL theorem: a sequent `hyps |- concl`.
///
/// In the LCF tradition, theorems can only be constructed by the kernel
/// inference rules. Here we represent them as data for import purposes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolThm {
    /// Hypotheses (assumptions).
    pub hyps: Vec<HolTerm>,
    /// Conclusion.
    pub concl: HolTerm,
}

/// The three standard HOL axioms shared by all HOL family systems.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HolAxiom {
    /// Extensionality: `|- (f = g) <=> (!x. f x = g x)`.
    Extensionality,
    /// Choice (Hilbert epsilon): `|- P x ==> P ((@) P)`.
    Choice,
    /// Infinity: `|- ?f:ind->ind. ONE_ONE f /\ ~ONTO f`.
    Infinity,
}

/// Result of importing a collection of HOL theorems.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HolImportResult {
    /// Source system (HolLight, Hol4, or Isabelle).
    pub source_name: String,
    /// Total number of theorems.
    pub theorem_count: usize,
    /// Number of theorems successfully translated.
    pub translated_count: usize,
    /// Which standard axioms are used.
    pub axioms_used: Vec<HolAxiom>,
    /// Axiom profile for the import.
    pub axiom_profile: crate::types::AxiomProfile,
    /// Trust level.
    pub trust_level: crate::types::TrustLevel,
    /// Provenance record.
    pub provenance: crate::types::Provenance,
    /// Diagnostics and warnings.
    pub diagnostics: Vec<String>,
}
