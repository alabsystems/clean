// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation from OpenTheory types and terms to Lean kernel expressions.

use super::name::OtName;
use super::term::{OtTerm, OtVariable};
use super::ty::OtType;
use super::{OpenTheoryError, OpenTheoryResult};
use crate::{BinderInfo, Expr, Level, Name as LeanName};

#[derive(Clone, Debug, PartialEq, Eq)]
enum ScopeBinder {
    TypeVar(OtName),
    TermVar(OtVariable),
}

/// Translation scope for OpenTheory free variables.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OtTranslationContext {
    binders: Vec<ScopeBinder>,
}

impl OtTranslationContext {
    #[must_use]
    pub fn with_type_vars(type_vars: impl IntoIterator<Item = OtName>) -> Self {
        Self {
            binders: type_vars.into_iter().map(ScopeBinder::TypeVar).collect(),
        }
    }

    #[must_use]
    pub fn with_binders(
        type_vars: impl IntoIterator<Item = OtName>,
        term_vars: impl IntoIterator<Item = OtVariable>,
    ) -> Self {
        let mut binders = type_vars
            .into_iter()
            .map(ScopeBinder::TypeVar)
            .collect::<Vec<_>>();
        binders.extend(term_vars.into_iter().map(ScopeBinder::TermVar));
        Self { binders }
    }

    fn extend_term(&self, variable: OtVariable) -> Self {
        let mut binders = self.binders.clone();
        binders.push(ScopeBinder::TermVar(variable));
        Self { binders }
    }

    fn lookup_type_var(&self, name: &OtName) -> Option<u32> {
        self.binders
            .iter()
            .rposition(|binder| matches!(binder, ScopeBinder::TypeVar(var) if var == name))
            .map(|position| (self.binders.len() - 1 - position) as u32)
    }

    fn lookup_term_var(&self, variable: &OtVariable) -> Option<u32> {
        self.binders
            .iter()
            .rposition(|binder| matches!(binder, ScopeBinder::TermVar(var) if var == variable))
            .map(|position| (self.binders.len() - 1 - position) as u32)
    }
}

/// Translate an OpenTheory type into a Lean kernel `Expr`.
pub fn translate_type(ty: &OtType) -> OpenTheoryResult<Expr> {
    translate_type_with_context(ty, &OtTranslationContext::default())
}

/// Translate an OpenTheory type using a caller-provided scope.
pub fn translate_type_with_context(
    ty: &OtType,
    context: &OtTranslationContext,
) -> OpenTheoryResult<Expr> {
    match ty {
        OtType::Var(name) => context
            .lookup_type_var(name)
            .map(Expr::bvar)
            .ok_or_else(|| OpenTheoryError::UnboundTypeVariable { name: name.clone() }),
        OtType::Bool => Ok(Expr::prop()),
        OtType::Function { domain, codomain } => Ok(Expr::arrow(
            translate_type_with_context(domain, context)?,
            translate_type_with_context(codomain, context)?,
        )),
        OtType::App { op, args } => {
            let args = args
                .iter()
                .map(|arg| translate_type_with_context(arg, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::apps(
                Expr::const_(type_op_decl_name(&op.name), Vec::new()),
                args,
            ))
        }
    }
}

/// Translate an OpenTheory term into a Lean kernel `Expr`.
pub fn translate_term(term: &OtTerm) -> OpenTheoryResult<Expr> {
    translate_term_with_context(term, &OtTranslationContext::default())
}

/// Translate an OpenTheory term using a caller-provided scope.
pub fn translate_term_with_context(
    term: &OtTerm,
    context: &OtTranslationContext,
) -> OpenTheoryResult<Expr> {
    if let Some((lhs, rhs)) = term.dest_eq() {
        return Ok(eq_expr(
            translate_type_with_context(&lhs.ty()?, context)?,
            translate_term_with_context(lhs, context)?,
            translate_term_with_context(rhs, context)?,
        ));
    }

    match term {
        OtTerm::Var(variable) => context
            .lookup_term_var(variable)
            .map(Expr::bvar)
            .ok_or_else(|| OpenTheoryError::UnboundTermVariable {
                name: variable.name.clone(),
                ty: variable.ty.clone(),
            }),
        OtTerm::Const { constant, ty } if constant.is_primitive_eq() => {
            translate_eq_constant(ty, context)
        }
        OtTerm::Const { constant, ty } => {
            let type_args = ty
                .free_type_vars()
                .into_iter()
                .map(|var| translate_type_with_context(&OtType::Var(var), context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::apps(
                Expr::const_(const_decl_name(&constant.name), Vec::new()),
                type_args,
            ))
        }
        OtTerm::App { func, arg } => Ok(Expr::app(
            translate_term_with_context(func, context)?,
            translate_term_with_context(arg, context)?,
        )),
        OtTerm::Abs { binder, body } => {
            let binder_ty = translate_type_with_context(&binder.ty, context)?;
            let extended = context.extend_term(binder.clone());
            Ok(Expr::lam(
                BinderInfo::Default,
                binder_ty,
                translate_term_with_context(body, &extended)?,
            ))
        }
    }
}

pub(crate) fn type_op_decl_name(name: &OtName) -> LeanName {
    prefixed_name(["OpenTheory", "TypeOp"], name)
}

pub(crate) fn const_decl_name(name: &OtName) -> LeanName {
    prefixed_name(["OpenTheory", "Const"], name)
}

fn translate_eq_constant(ty: &OtType, context: &OtTranslationContext) -> OpenTheoryResult<Expr> {
    let OtType::Function { domain, codomain } = ty else {
        return Err(OpenTheoryError::ExpectedFunctionType { ty: ty.clone() });
    };
    let OtType::Function {
        domain: rhs_domain,
        codomain,
    } = codomain.as_ref()
    else {
        return Err(OpenTheoryError::ExpectedFunctionType { ty: ty.clone() });
    };
    if domain.as_ref() != rhs_domain.as_ref() || !codomain.is_bool() {
        return Err(OpenTheoryError::MalformedObject {
            command: "translateTerm",
            detail: "primitive equality constant had unexpected type".to_string(),
        });
    }
    Ok(Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::zero()]),
        [translate_type_with_context(domain, context)?],
    ))
}

fn eq_expr(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::zero()]),
        [ty, lhs, rhs],
    )
}

fn prefixed_name<const N: usize>(prefix: [&str; N], name: &OtName) -> LeanName {
    let mut out = LeanName::anon();
    for segment in prefix {
        out = out.str(segment);
    }
    for segment in &name.namespace {
        out = out.str(segment);
    }
    out.str(&name.component)
}
