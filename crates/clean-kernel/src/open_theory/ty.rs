// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory simple types and type operators.

use super::name::OtName;
use std::hash::{Hash, Hasher};

/// Identity for article-defined symbols.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OtSymbolId(pub u64);

/// Provenance of a type operator or constant.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OtSymbolOrigin {
    Primitive,
    External,
    Defined(OtSymbolId),
}

/// OpenTheory type operator object.
#[derive(Clone, Debug)]
pub struct OtTypeOperator {
    pub name: OtName,
    pub origin: OtSymbolOrigin,
    pub arity: Option<usize>,
}

impl OtTypeOperator {
    #[must_use]
    pub fn primitive_bool() -> Self {
        Self {
            name: OtName::global("bool"),
            origin: OtSymbolOrigin::Primitive,
            arity: Some(0),
        }
    }

    #[must_use]
    pub fn primitive_arrow() -> Self {
        Self {
            name: OtName::global("->"),
            origin: OtSymbolOrigin::Primitive,
            arity: Some(2),
        }
    }

    #[must_use]
    pub fn from_name(name: OtName) -> Self {
        if name == OtName::global("bool") {
            return Self::primitive_bool();
        }
        if name == OtName::global("->") {
            return Self::primitive_arrow();
        }
        Self {
            name,
            origin: OtSymbolOrigin::External,
            arity: None,
        }
    }

    #[must_use]
    pub fn defined(name: OtName, arity: usize, id: OtSymbolId) -> Self {
        Self {
            name,
            origin: OtSymbolOrigin::Defined(id),
            arity: Some(arity),
        }
    }

    #[must_use]
    pub fn with_arity(&self, arity: usize) -> Self {
        let mut out = self.clone();
        out.arity = Some(arity);
        out
    }

    #[must_use]
    pub fn is_primitive_bool(&self) -> bool {
        self.origin == OtSymbolOrigin::Primitive && self.name == OtName::global("bool")
    }

    #[must_use]
    pub fn is_primitive_arrow(&self) -> bool {
        self.origin == OtSymbolOrigin::Primitive && self.name == OtName::global("->")
    }
}

impl PartialEq for OtTypeOperator {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.origin == other.origin
    }
}

impl Eq for OtTypeOperator {}

impl Hash for OtTypeOperator {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.origin.hash(state);
    }
}

/// OpenTheory simple types.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OtType {
    Var(OtName),
    Bool,
    Function {
        domain: Box<OtType>,
        codomain: Box<OtType>,
    },
    App {
        op: OtTypeOperator,
        args: Vec<OtType>,
    },
}

impl OtType {
    #[must_use]
    pub fn bool() -> Self {
        Self::Bool
    }

    #[must_use]
    pub fn function(domain: OtType, codomain: OtType) -> Self {
        Self::Function {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    #[must_use]
    pub fn apply(op: OtTypeOperator, args: Vec<OtType>) -> Self {
        if op.is_primitive_bool() && args.is_empty() {
            Self::Bool
        } else if op.is_primitive_arrow() && args.len() == 2 {
            Self::function(args[0].clone(), args[1].clone())
        } else {
            Self::App {
                op: op.with_arity(args.len()),
                args,
            }
        }
    }

    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    #[must_use]
    pub fn as_function(&self) -> Option<(&OtType, &OtType)> {
        match self {
            Self::Function { domain, codomain } => Some((domain, codomain)),
            _ => None,
        }
    }

    #[must_use]
    pub fn substitute_types(&self, substitutions: &[(OtName, OtType)]) -> Self {
        match self {
            Self::Var(name) => substitutions
                .iter()
                .find(|(var, _)| var == name)
                .map(|(_, replacement)| replacement.clone())
                .unwrap_or_else(|| self.clone()),
            Self::Bool => Self::Bool,
            Self::Function { domain, codomain } => Self::function(
                domain.substitute_types(substitutions),
                codomain.substitute_types(substitutions),
            ),
            Self::App { op, args } => Self::App {
                op: op.clone(),
                args: args
                    .iter()
                    .map(|arg| arg.substitute_types(substitutions))
                    .collect(),
            },
        }
    }

    #[must_use]
    pub fn free_type_vars(&self) -> Vec<OtName> {
        let mut vars = Vec::new();
        self.collect_free_type_vars(&mut vars);
        vars
    }

    fn collect_free_type_vars(&self, vars: &mut Vec<OtName>) {
        match self {
            Self::Var(name) => {
                if !vars.contains(name) {
                    vars.push(name.clone());
                }
            }
            Self::Bool => {}
            Self::Function { domain, codomain } => {
                domain.collect_free_type_vars(vars);
                codomain.collect_free_type_vars(vars);
            }
            Self::App { args, .. } => {
                for arg in args {
                    arg.collect_free_type_vars(vars);
                }
            }
        }
    }
}
