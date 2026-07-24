// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isabelle internal AST types.
//!
//! These types represent Isabelle's internal term language as exported by
//! `isabelle export`. The type system mirrors Isabelle/Pure's simply-typed
//! higher-order logic with type variables and type constructors.
//!
//! Reference: Isabelle/Pure kernel, `Pure/term.ML`
//! URL: https://isabelle.in.tum.de/repos/isabelle/file/tip/src/Pure/term.ML

use serde::{Deserialize, Serialize};

/// Isabelle type expression.
///
/// Isabelle's type system is based on rank-1 polymorphism with sort constraints
/// (type classes). Types are either free type variables, schematic type variables,
/// or type constructor applications.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum IsaType {
    /// Free type variable with sort constraints.
    /// Example: `'a::linorder` has name `'a` and sort `["linorder"]`.
    TFree { name: String, sort: Vec<String> },
    /// Schematic (unification) type variable with index and sort constraints.
    /// Example: `?'a.0::{}` has name `'a`, index 0, empty sort.
    TVar {
        name: String,
        index: u32,
        sort: Vec<String>,
    },
    /// Type constructor application.
    /// Example: `nat list` is `Type { name: "List.list", args: [Type { name: "Nat.nat", args: [] }] }`.
    /// Nullary type constructors have empty args: `bool`, `nat`, `prop`.
    Type { name: String, args: Vec<IsaType> },
}

impl IsaType {
    /// Create a nullary type constructor (e.g., `bool`, `nat`, `prop`).
    #[must_use]
    pub fn nullary(name: &str) -> Self {
        Self::Type {
            name: name.to_owned(),
            args: Vec::new(),
        }
    }

    /// Create a function type `a => b` (Isabelle's `fun` type constructor).
    #[must_use]
    pub fn fun(domain: IsaType, codomain: IsaType) -> Self {
        Self::Type {
            name: "fun".to_owned(),
            args: vec![domain, codomain],
        }
    }

    /// Create a free type variable with no sort constraints.
    #[must_use]
    pub fn tfree(name: &str) -> Self {
        Self::TFree {
            name: name.to_owned(),
            sort: Vec::new(),
        }
    }

    /// Returns `true` if this is a function type (`fun` constructor with 2 args).
    #[must_use]
    pub fn is_fun(&self) -> bool {
        matches!(self, Self::Type { name, args } if name == "fun" && args.len() == 2)
    }
}

/// Isabelle term expression.
///
/// Terms follow the simply-typed lambda calculus with de Bruijn indices for
/// bound variables. This matches Isabelle/Pure's `term` datatype in `term.ML`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum IsaTerm {
    /// De Bruijn index referencing a lambda-bound variable.
    /// Index 0 is the innermost binder.
    Bound(u32),
    /// Free variable with name and type.
    Free { name: String, ty: IsaType },
    /// Schematic (unification) variable with name, index, and type.
    Var {
        name: String,
        index: u32,
        ty: IsaType,
    },
    /// Named constant with its type instantiation.
    Const { name: String, ty: IsaType },
    /// Lambda abstraction: `\<name>::<ty>. <body>`.
    /// The bound variable uses de Bruijn indexing in `body`.
    Abs {
        name: String,
        ty: IsaType,
        body: Box<IsaTerm>,
    },
    /// Function application: `fun $ arg`.
    App {
        fun: Box<IsaTerm>,
        arg: Box<IsaTerm>,
    },
}

impl IsaTerm {
    /// Create a simple constant with a nullary type.
    #[must_use]
    pub fn const_of(name: &str, ty: IsaType) -> Self {
        Self::Const {
            name: name.to_owned(),
            ty,
        }
    }

    /// Create a function application.
    #[must_use]
    pub fn app(fun: IsaTerm, arg: IsaTerm) -> Self {
        Self::App {
            fun: Box::new(fun),
            arg: Box::new(arg),
        }
    }

    /// Create a lambda abstraction.
    #[must_use]
    pub fn abs(name: &str, ty: IsaType, body: IsaTerm) -> Self {
        Self::Abs {
            name: name.to_owned(),
            ty,
            body: Box::new(body),
        }
    }

    /// Returns `true` if this term is a function application.
    #[must_use]
    pub fn is_app(&self) -> bool {
        matches!(self, Self::App { .. })
    }

    /// Returns `true` if this term is a lambda abstraction.
    #[must_use]
    pub fn is_abs(&self) -> bool {
        matches!(self, Self::Abs { .. })
    }
}

/// Proof status of an Isabelle theorem.
///
/// Isabelle uses the LCF architecture where proofs are opaque. When exporting,
/// some theorems have full proof terms while others are axiomatized (the proof
/// is erased during export).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofStatus {
    /// Theorem was proved within Isabelle's kernel (LCF-style).
    Proved,
    /// Proof was erased during export (LCF opaque proof, not reconstructible).
    Axiomatized,
}

/// An exported Isabelle theorem.
///
/// Contains the theorem name, its propositions (hypotheses + conclusion as a
/// list of terms), and whether the proof was retained or axiomatized.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IsaTheorem {
    /// Fully qualified theorem name (e.g., `HOL.TrueI`, `Nat.Suc_not_Zero`).
    pub name: String,
    /// Propositions: hypotheses followed by the conclusion.
    /// In Isabelle, a theorem `[| P1; P2 |] ==> Q` has props `[P1, P2, Q]`.
    pub props: Vec<IsaTerm>,
    /// Whether this theorem's proof was retained or axiomatized on export.
    pub proof_status: ProofStatus,
}

/// A complete Isabelle theory export.
///
/// Represents the contents of one `.yxml` theory export file, including
/// type declarations, constant declarations, theorems, and inter-theory
/// dependencies.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IsaTheoryExport {
    /// Theory name (e.g., `HOL.HOL`, `Nat.Nat`, `Main.Main`).
    pub theory_name: String,
    /// Type declarations: `(name, kind)` where kind is the type constructor's
    /// arity type (encoded as an `IsaType`).
    pub types: Vec<(String, IsaType)>,
    /// Constant declarations: `(name, type)`.
    pub consts: Vec<(String, IsaType)>,
    /// Exported theorems.
    pub theorems: Vec<IsaTheorem>,
    /// Theory dependencies (parent theory names).
    pub dependencies: Vec<String>,
}

impl IsaTheoryExport {
    /// Create an empty theory export with the given name.
    #[must_use]
    pub fn new(theory_name: &str) -> Self {
        Self {
            theory_name: theory_name.to_owned(),
            types: Vec::new(),
            consts: Vec::new(),
            theorems: Vec::new(),
            dependencies: Vec::new(),
        }
    }
}
