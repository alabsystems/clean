// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! JSON-facing HOL Light proof-object AST.

use serde::{Deserialize, Serialize};

/// HOL Light type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum HolType {
    /// A schematic HOL type variable.
    Var { name: String },
    /// HOL's proposition type.
    Bool,
    /// Simple function type.
    Fun {
        domain: Box<HolType>,
        codomain: Box<HolType>,
    },
    /// A named HOL type operator.
    TyOp { name: String, args: Vec<HolType> },
}

impl HolType {
    #[must_use]
    pub fn bool() -> Self {
        Self::Bool
    }

    #[must_use]
    pub fn fun(domain: HolType, codomain: HolType) -> Self {
        Self::Fun {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }
}

/// Named HOL variable (used by binders and substitutions).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HolVar {
    pub name: String,
    pub ty: HolType,
}

impl HolVar {
    #[must_use]
    pub fn new(name: impl Into<String>, ty: HolType) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }
}

/// HOL Light term.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum HolTerm {
    /// Variable reference.
    Var { name: String, ty: HolType },
    /// Constant reference.
    Const { name: String, ty: HolType },
    /// Function application.
    App {
        func: Box<HolTerm>,
        arg: Box<HolTerm>,
    },
    /// Lambda abstraction.
    Abs { binder: HolVar, body: Box<HolTerm> },
}

impl HolTerm {
    #[must_use]
    pub fn var(name: impl Into<String>, ty: HolType) -> Self {
        Self::Var {
            name: name.into(),
            ty,
        }
    }

    #[must_use]
    pub fn const_(name: impl Into<String>, ty: HolType) -> Self {
        Self::Const {
            name: name.into(),
            ty,
        }
    }

    #[must_use]
    pub fn app(func: HolTerm, arg: HolTerm) -> Self {
        Self::App {
            func: Box::new(func),
            arg: Box::new(arg),
        }
    }

    #[must_use]
    pub fn abs(binder: HolVar, body: HolTerm) -> Self {
        Self::Abs {
            binder,
            body: Box::new(body),
        }
    }

    /// Build the HOL equality term `lhs = rhs`.
    #[must_use]
    pub fn eq(lhs: HolTerm, rhs: HolTerm, lhs_ty: HolType) -> Self {
        let eq_ty = HolType::fun(lhs_ty.clone(), HolType::fun(lhs_ty, HolType::Bool));
        Self::app(Self::app(Self::const_("=", eq_ty), lhs), rhs)
    }

    #[must_use]
    pub fn as_var(&self) -> Option<HolVar> {
        match self {
            Self::Var { name, ty } => Some(HolVar {
                name: name.clone(),
                ty: ty.clone(),
            }),
            _ => None,
        }
    }
}

/// Term substitution for HOL INST.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolTermSubstitution {
    pub variable: HolVar,
    pub replacement: HolTerm,
}

/// Type substitution for HOL INST_TYPE.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolTypeSubstitution {
    pub variable: String,
    pub replacement: HolType,
}

/// HOL Light proof object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "rule", rename_all = "snake_case")]
pub enum HolProof {
    /// REFL.
    Refl { term: HolTerm },
    /// TRANS.
    Trans {
        left: Box<HolProof>,
        right: Box<HolProof>,
    },
    /// MK_COMB.
    MkComb {
        function: Box<HolProof>,
        argument: Box<HolProof>,
    },
    /// ABS.
    Abs {
        binder: HolVar,
        proof: Box<HolProof>,
    },
    /// BETA.
    Beta {
        binder: HolVar,
        body: HolTerm,
        argument: HolTerm,
    },
    /// ASSUME.
    Assume { proposition: HolTerm },
    /// EQ_MP.
    EqMp {
        equality: Box<HolProof>,
        proof: Box<HolProof>,
    },
    /// DEDUCT_ANTISYM_RULE.
    DeductAntisym {
        left: Box<HolProof>,
        right: Box<HolProof>,
    },
    /// INST.
    Inst {
        proof: Box<HolProof>,
        substitutions: Vec<HolTermSubstitution>,
    },
    /// INST_TYPE.
    InstType {
        proof: Box<HolProof>,
        substitutions: Vec<HolTypeSubstitution>,
    },
}

/// Top-level named HOL Light theorem proof object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolProofObject {
    pub name: String,
    pub proof: HolProof,
}
