// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory terms, constants, variables, and theorems.

use super::name::OtName;
use super::ty::{OtSymbolId, OtSymbolOrigin, OtType};
use super::{OpenTheoryError, OpenTheoryResult};
use std::hash::{Hash, Hasher};

/// OpenTheory constant object.
#[derive(Clone, Debug)]
pub struct OtConstant {
    pub name: OtName,
    pub origin: OtSymbolOrigin,
    pub principal_type: Option<OtType>,
}

impl OtConstant {
    #[must_use]
    pub fn primitive_eq(principal_type: Option<OtType>) -> Self {
        Self {
            name: OtName::global("="),
            origin: OtSymbolOrigin::Primitive,
            principal_type,
        }
    }

    #[must_use]
    pub fn from_name(name: OtName) -> Self {
        if name == OtName::global("=") {
            return Self::primitive_eq(None);
        }
        Self {
            name,
            origin: OtSymbolOrigin::External,
            principal_type: None,
        }
    }

    #[must_use]
    pub fn defined(name: OtName, principal_type: OtType, id: OtSymbolId) -> Self {
        Self {
            name,
            origin: OtSymbolOrigin::Defined(id),
            principal_type: Some(principal_type),
        }
    }

    #[must_use]
    pub fn with_principal_type(&self, principal_type: OtType) -> Self {
        let mut out = self.clone();
        out.principal_type = Some(principal_type);
        out
    }

    #[must_use]
    pub fn is_primitive_eq(&self) -> bool {
        self.origin == OtSymbolOrigin::Primitive && self.name == OtName::global("=")
    }
}

impl PartialEq for OtConstant {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.origin == other.origin
    }
}

impl Eq for OtConstant {}

impl Hash for OtConstant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.origin.hash(state);
    }
}

/// OpenTheory term variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OtVariable {
    pub name: OtName,
    pub ty: OtType,
}

impl OtVariable {
    #[must_use]
    pub fn new(name: OtName, ty: OtType) -> Self {
        Self { name, ty }
    }

    fn freshened(&self, disallowed: &[OtVariable]) -> Self {
        let base = self.name.component.clone();
        for idx in 1.. {
            let candidate = Self {
                name: self.name.with_component(format!("{base}#{idx}")),
                ty: self.ty.clone(),
            };
            if !disallowed.contains(&candidate) {
                return candidate;
            }
        }
        unreachable!("fresh variable search should always terminate")
    }
}

/// OpenTheory terms.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OtTerm {
    Var(OtVariable),
    Const {
        constant: OtConstant,
        ty: OtType,
    },
    App {
        func: Box<OtTerm>,
        arg: Box<OtTerm>,
    },
    Abs {
        binder: OtVariable,
        body: Box<OtTerm>,
    },
}

impl OtTerm {
    #[must_use]
    pub fn var(variable: OtVariable) -> Self {
        Self::Var(variable)
    }

    #[must_use]
    pub fn const_(constant: OtConstant, ty: OtType) -> Self {
        Self::Const { constant, ty }
    }

    pub fn app(func: OtTerm, arg: OtTerm) -> OpenTheoryResult<Self> {
        let func_ty = func.ty()?;
        let (domain, _) =
            func_ty
                .as_function()
                .ok_or_else(|| OpenTheoryError::ExpectedFunctionType {
                    ty: func_ty.clone(),
                })?;
        let arg_ty = arg.ty()?;
        if domain != &arg_ty {
            return Err(OpenTheoryError::TypeMismatch {
                expected: domain.clone(),
                actual: arg_ty,
            });
        }
        Ok(Self::App {
            func: Box::new(func),
            arg: Box::new(arg),
        })
    }

    #[must_use]
    pub fn abs(binder: OtVariable, body: OtTerm) -> Self {
        Self::Abs {
            binder,
            body: Box::new(body),
        }
    }

    pub fn eq(lhs: OtTerm, rhs: OtTerm) -> OpenTheoryResult<Self> {
        let lhs_ty = lhs.ty()?;
        let rhs_ty = rhs.ty()?;
        if lhs_ty != rhs_ty {
            return Err(OpenTheoryError::TypeMismatch {
                expected: lhs_ty,
                actual: rhs_ty,
            });
        }
        let eq_ty = OtType::function(
            lhs_ty.clone(),
            OtType::function(lhs_ty.clone(), OtType::bool()),
        );
        let eq_const = OtConstant::primitive_eq(Some(eq_ty.clone()));
        let eq_term = Self::const_(eq_const, eq_ty);
        let eq_term = Self::app(eq_term, lhs)?;
        Self::app(eq_term, rhs)
    }

    /// Alpha-equivalence comparison.
    ///
    /// Two terms are alpha-equivalent if they are identical up to consistent
    /// renaming of bound variables. For example, `\x. x` and `\y. y` are
    /// alpha-equivalent. Free variables must match by name and type.
    #[must_use]
    pub fn alpha_eq(&self, other: &Self) -> bool {
        self.alpha_eq_inner(other, &mut Vec::new(), &mut Vec::new())
    }

    fn alpha_eq_inner(
        &self,
        other: &Self,
        left_env: &mut Vec<OtVariable>,
        right_env: &mut Vec<OtVariable>,
    ) -> bool {
        match (self, other) {
            (Self::Var(v1), Self::Var(v2)) => {
                let left_idx = left_env.iter().rev().position(|v| v == v1);
                let right_idx = right_env.iter().rev().position(|v| v == v2);
                match (left_idx, right_idx) {
                    (Some(li), Some(ri)) => li == ri,
                    (None, None) => v1 == v2,
                    _ => false,
                }
            }
            (
                Self::Const {
                    constant: c1,
                    ty: t1,
                },
                Self::Const {
                    constant: c2,
                    ty: t2,
                },
            ) => c1 == c2 && t1 == t2,
            (Self::App { func: f1, arg: a1 }, Self::App { func: f2, arg: a2 }) => {
                f1.alpha_eq_inner(f2, left_env, right_env)
                    && a1.alpha_eq_inner(a2, left_env, right_env)
            }
            (
                Self::Abs {
                    binder: b1,
                    body: body1,
                },
                Self::Abs {
                    binder: b2,
                    body: body2,
                },
            ) => {
                if b1.ty != b2.ty {
                    return false;
                }
                left_env.push(b1.clone());
                right_env.push(b2.clone());
                let result = body1.alpha_eq_inner(body2, left_env, right_env);
                left_env.pop();
                right_env.pop();
                result
            }
            _ => false,
        }
    }

    /// Check whether any term in the slice is alpha-equivalent to `self`.
    #[must_use]
    pub fn alpha_mem(&self, haystack: &[OtTerm]) -> bool {
        haystack.iter().any(|t| self.alpha_eq(t))
    }

    pub fn ty(&self) -> OpenTheoryResult<OtType> {
        match self {
            Self::Var(variable) => Ok(variable.ty.clone()),
            Self::Const { ty, .. } => Ok(ty.clone()),
            Self::App { func, .. } => {
                let func_ty = func.ty()?;
                let (_, codomain) =
                    func_ty
                        .as_function()
                        .ok_or_else(|| OpenTheoryError::ExpectedFunctionType {
                            ty: func_ty.clone(),
                        })?;
                Ok(codomain.clone())
            }
            Self::Abs { binder, body } => Ok(OtType::function(binder.ty.clone(), body.ty()?)),
        }
    }

    #[must_use]
    pub fn dest_eq(&self) -> Option<(&OtTerm, &OtTerm)> {
        let Self::App { func, arg: rhs } = self else {
            return None;
        };
        let Self::App { func, arg: lhs } = func.as_ref() else {
            return None;
        };
        match func.as_ref() {
            Self::Const { constant, .. } if constant.is_primitive_eq() => Some((lhs, rhs)),
            _ => None,
        }
    }

    #[must_use]
    pub fn free_vars(&self) -> Vec<OtVariable> {
        let mut vars = Vec::new();
        self.collect_free_vars(&mut Vec::new(), &mut vars);
        vars
    }

    fn collect_free_vars(&self, bound: &mut Vec<OtVariable>, free: &mut Vec<OtVariable>) {
        match self {
            Self::Var(variable) => {
                if !bound.contains(variable) && !free.contains(variable) {
                    free.push(variable.clone());
                }
            }
            Self::Const { .. } => {}
            Self::App { func, arg } => {
                func.collect_free_vars(bound, free);
                arg.collect_free_vars(bound, free);
            }
            Self::Abs { binder, body } => {
                bound.push(binder.clone());
                body.collect_free_vars(bound, free);
                let _ = bound.pop();
            }
        }
    }

    #[must_use]
    pub fn substitute_types(&self, substitutions: &[(OtName, OtType)]) -> Self {
        match self {
            Self::Var(variable) => Self::Var(OtVariable {
                name: variable.name.clone(),
                ty: variable.ty.substitute_types(substitutions),
            }),
            Self::Const { constant, ty } => Self::Const {
                constant: OtConstant {
                    name: constant.name.clone(),
                    origin: constant.origin.clone(),
                    principal_type: constant
                        .principal_type
                        .as_ref()
                        .map(|principal_type| principal_type.substitute_types(substitutions)),
                },
                ty: ty.substitute_types(substitutions),
            },
            Self::App { func, arg } => Self::App {
                func: Box::new(func.substitute_types(substitutions)),
                arg: Box::new(arg.substitute_types(substitutions)),
            },
            Self::Abs { binder, body } => Self::Abs {
                binder: OtVariable {
                    name: binder.name.clone(),
                    ty: binder.ty.substitute_types(substitutions),
                },
                body: Box::new(body.substitute_types(substitutions)),
            },
        }
    }

    #[must_use]
    pub fn substitute_terms(&self, substitutions: &[(OtVariable, OtTerm)]) -> Self {
        match self {
            Self::Var(variable) => substitutions
                .iter()
                .find(|(target, _)| target == variable)
                .map(|(_, replacement)| replacement.clone())
                .unwrap_or_else(|| self.clone()),
            Self::Const { .. } => self.clone(),
            Self::App { func, arg } => Self::App {
                func: Box::new(func.substitute_terms(substitutions)),
                arg: Box::new(arg.substitute_terms(substitutions)),
            },
            Self::Abs { binder, body } => {
                let filtered = substitutions
                    .iter()
                    .filter(|(target, _)| target != binder)
                    .cloned()
                    .collect::<Vec<_>>();
                if filtered.is_empty() {
                    return self.clone();
                }

                let mut binder_out = binder.clone();
                let mut body_out = (**body).clone();
                let mut disallowed = body_out.free_vars();
                for (_, replacement) in &filtered {
                    for free_var in replacement.free_vars() {
                        if !disallowed.contains(&free_var) {
                            disallowed.push(free_var);
                        }
                    }
                }
                if filtered
                    .iter()
                    .any(|(_, replacement)| replacement.free_vars().contains(&binder_out))
                {
                    let fresh = binder_out.freshened(&disallowed);
                    body_out = body_out.rename_bound_var(&binder_out, &fresh);
                    binder_out = fresh;
                }

                Self::Abs {
                    binder: binder_out,
                    body: Box::new(body_out.substitute_terms(&filtered)),
                }
            }
        }
    }

    fn rename_bound_var(&self, from: &OtVariable, to: &OtVariable) -> Self {
        match self {
            Self::Var(variable) if variable == from => Self::Var(to.clone()),
            Self::Var(_) | Self::Const { .. } => self.clone(),
            Self::App { func, arg } => Self::App {
                func: Box::new(func.rename_bound_var(from, to)),
                arg: Box::new(arg.rename_bound_var(from, to)),
            },
            Self::Abs { binder, body } if binder == from => Self::Abs {
                binder: binder.clone(),
                body: body.clone(),
            },
            Self::Abs { binder, body } => Self::Abs {
                binder: binder.clone(),
                body: Box::new(body.rename_bound_var(from, to)),
            },
        }
    }
}

/// OpenTheory theorem.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OtTheorem {
    pub hypotheses: Vec<OtTerm>,
    pub conclusion: OtTerm,
}

impl OtTheorem {
    #[must_use]
    pub fn new(hypotheses: Vec<OtTerm>, conclusion: OtTerm) -> Self {
        Self {
            hypotheses: dedup_terms(hypotheses),
            conclusion,
        }
    }

    #[must_use]
    pub fn union_hypotheses(left: &[OtTerm], right: &[OtTerm]) -> Vec<OtTerm> {
        let mut out = left.to_vec();
        for term in right {
            if !term.alpha_mem(&out) {
                out.push(term.clone());
            }
        }
        out
    }

    #[must_use]
    pub fn without_hypothesis(hypotheses: &[OtTerm], target: &OtTerm) -> Vec<OtTerm> {
        hypotheses
            .iter()
            .filter(|term| !term.alpha_eq(target))
            .cloned()
            .collect()
    }

    #[must_use]
    pub fn as_equality(&self) -> Option<(&OtTerm, &OtTerm)> {
        self.conclusion.dest_eq()
    }

    #[must_use]
    pub fn substitute_types(&self, substitutions: &[(OtName, OtType)]) -> Self {
        Self::new(
            self.hypotheses
                .iter()
                .map(|hypothesis| hypothesis.substitute_types(substitutions))
                .collect(),
            self.conclusion.substitute_types(substitutions),
        )
    }

    #[must_use]
    pub fn substitute_terms(&self, substitutions: &[(OtVariable, OtTerm)]) -> Self {
        Self::new(
            self.hypotheses
                .iter()
                .map(|hypothesis| hypothesis.substitute_terms(substitutions))
                .collect(),
            self.conclusion.substitute_terms(substitutions),
        )
    }
}

fn dedup_terms(terms: Vec<OtTerm>) -> Vec<OtTerm> {
    let mut out = Vec::new();
    for term in terms {
        if !term.alpha_mem(&out) {
            out.push(term);
        }
    }
    out
}
