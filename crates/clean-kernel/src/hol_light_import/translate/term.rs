// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HOL term/type translation helpers.

use super::super::{
    HolLightImportError, HolTerm, HolTermSubstitution, HolType, HolTypeSubstitution, HolVar,
};
use super::context::{
    const_name, type_op_name, ConstSymbol, Scope, ScopeBinderKind, SymbolCollector, TypeOpSymbol,
};
use crate::{BinderInfo, Declaration, Expr};

pub(super) struct TermTranslator<'a> {
    symbols: &'a mut SymbolCollector,
}

impl<'a> TermTranslator<'a> {
    pub(super) fn new(symbols: &'a mut SymbolCollector) -> Self {
        Self { symbols }
    }

    pub(super) fn infer_type(&self, term: &HolTerm) -> Result<HolType, HolLightImportError> {
        match term {
            HolTerm::Var { ty, .. } | HolTerm::Const { ty, .. } => Ok(ty.clone()),
            HolTerm::App { func, arg } => {
                let func_ty = self.infer_type(func)?;
                let arg_ty = self.infer_type(arg)?;
                match func_ty {
                    HolType::Fun { domain, codomain } => {
                        if *domain != arg_ty {
                            return Err(HolLightImportError::TypeMismatch {
                                expected: *domain,
                                actual: arg_ty,
                            });
                        }
                        Ok(*codomain)
                    }
                    ty => Err(HolLightImportError::ExpectedFunctionType { ty }),
                }
            }
            HolTerm::Abs { binder, body } => {
                Ok(HolType::fun(binder.ty.clone(), self.infer_type(body)?))
            }
        }
    }

    pub(super) fn translate_type(
        &mut self,
        scope: &Scope,
        ty: &HolType,
    ) -> Result<Expr, HolLightImportError> {
        match ty {
            HolType::Var { name } => {
                let position = scope.lookup_type(name).ok_or_else(|| {
                    HolLightImportError::UnboundTypeVariable { name: name.clone() }
                })?;
                Ok(Expr::bvar((scope.len() - 1 - position) as u32))
            }
            HolType::Bool => Ok(Expr::prop()),
            HolType::Fun { domain, codomain } => {
                // `A → B` is `Pi(_, A, B)`: the codomain lives UNDER the arrow's
                // binder, so any de Bruijn indices it carries (e.g. bound HOL
                // type variables) must be shifted up by one. Without this lift,
                // `a → b` mistranslates to a dependent Pi whose body refers to
                // the arrow binder instead of `b`, and the kernel rejects it
                // with `ExpectedSort { ty: FVar(_) }`.
                let dom = self.translate_type(scope, domain)?;
                let cod = self.translate_type(scope, codomain)?.lift(1);
                Ok(Expr::arrow(dom, cod))
            }
            HolType::TyOp { name, args } => {
                self.symbols.note_type_op(name, args.len());
                let translated_args = args
                    .iter()
                    .map(|arg| self.translate_type(scope, arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Expr::apps(
                    Expr::const_(
                        type_op_name(&TypeOpSymbol {
                            name: name.clone(),
                            arity: args.len(),
                        }),
                        Vec::new(),
                    ),
                    translated_args,
                ))
            }
        }
    }

    pub(super) fn translate_term(
        &mut self,
        scope: &Scope,
        term: &HolTerm,
    ) -> Result<Expr, HolLightImportError> {
        if let Some((lhs, rhs)) = dest_eq(term) {
            let lhs_ty = self.infer_type(lhs)?;
            let ty = self.translate_type(scope, &lhs_ty)?;
            return Ok(eq_prop(
                ty,
                self.translate_term(scope, lhs)?,
                self.translate_term(scope, rhs)?,
            ));
        }
        match term {
            HolTerm::Var { name, ty } => {
                let var = HolVar::new(name.clone(), ty.clone());
                let position = scope.lookup_term(&var).ok_or_else(|| {
                    HolLightImportError::UnboundTermVariable {
                        name: name.clone(),
                        ty: ty.clone(),
                    }
                })?;
                Ok(Expr::bvar((scope.len() - 1 - position) as u32))
            }
            HolTerm::Const { name, ty } => {
                self.symbols.note_const(name, ty);
                let symbol = ConstSymbol {
                    name: name.clone(),
                    ty: ty.clone(),
                };
                let type_args = free_type_vars(ty)
                    .into_iter()
                    .map(|var_name| self.translate_type(scope, &HolType::Var { name: var_name }))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Expr::apps(
                    Expr::const_(const_name(&symbol), Vec::new()),
                    type_args,
                ))
            }
            HolTerm::App { func, arg } => Ok(Expr::app(
                self.translate_term(scope, func)?,
                self.translate_term(scope, arg)?,
            )),
            HolTerm::Abs { binder, body } => {
                let binder_ty = self.translate_type(scope, &binder.ty)?;
                let extended = scope.extend_term(binder, binder_ty.clone());
                Ok(Expr::lam(
                    BinderInfo::Default,
                    binder_ty,
                    self.translate_term(&extended, body)?,
                ))
            }
        }
    }
}

pub(super) fn dest_eq(term: &HolTerm) -> Option<(&HolTerm, &HolTerm)> {
    let HolTerm::App { func, arg: rhs } = term else {
        return None;
    };
    let HolTerm::App { func, arg: lhs } = func.as_ref() else {
        return None;
    };
    match func.as_ref() {
        HolTerm::Const { name, .. } if name == "=" => Some((lhs.as_ref(), rhs.as_ref())),
        _ => None,
    }
}

pub(super) fn free_type_vars(ty: &HolType) -> Vec<String> {
    let mut vars = Vec::new();
    collect_free_type_vars(ty, &mut vars);
    vars
}

pub(super) fn note_type_ops(symbols: &mut SymbolCollector, ty: &HolType) {
    match ty {
        HolType::Var { .. } | HolType::Bool => {}
        HolType::Fun { domain, codomain } => {
            note_type_ops(symbols, domain);
            note_type_ops(symbols, codomain);
        }
        HolType::TyOp { name, args } => {
            symbols.note_type_op(name, args.len());
            for arg in args {
                note_type_ops(symbols, arg);
            }
        }
    }
}

fn collect_free_type_vars(ty: &HolType, vars: &mut Vec<String>) {
    match ty {
        HolType::Var { name } => {
            if !vars.contains(name) {
                vars.push(name.clone());
            }
        }
        HolType::Bool => {}
        HolType::Fun { domain, codomain } => {
            collect_free_type_vars(domain, vars);
            collect_free_type_vars(codomain, vars);
        }
        HolType::TyOp { args, .. } => {
            for arg in args {
                collect_free_type_vars(arg, vars);
            }
        }
    }
}

pub(super) fn eq_prop(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![crate::Level::succ(crate::Level::zero())]),
        [ty, lhs, rhs],
    )
}

pub(super) fn substitute_term(
    term: &HolTerm,
    substitutions: &[HolTermSubstitution],
    bound: &mut Vec<HolVar>,
) -> HolTerm {
    match term {
        HolTerm::Var { name, ty } => {
            let var = HolVar::new(name.clone(), ty.clone());
            if bound.contains(&var) {
                term.clone()
            } else {
                substitutions
                    .iter()
                    .find(|substitution| substitution.variable == var)
                    .map(|substitution| substitution.replacement.clone())
                    .unwrap_or_else(|| term.clone())
            }
        }
        HolTerm::Const { .. } => term.clone(),
        HolTerm::App { func, arg } => HolTerm::app(
            substitute_term(func, substitutions, bound),
            substitute_term(arg, substitutions, bound),
        ),
        HolTerm::Abs { binder, body } => {
            bound.push(binder.clone());
            let result = HolTerm::abs(binder.clone(), substitute_term(body, substitutions, bound));
            bound.pop();
            result
        }
    }
}

pub(super) fn substitute_type_in_type(
    ty: &HolType,
    substitutions: &[HolTypeSubstitution],
) -> HolType {
    match ty {
        HolType::Var { name } => substitutions
            .iter()
            .find(|substitution| substitution.variable == *name)
            .map(|substitution| substitution.replacement.clone())
            .unwrap_or_else(|| ty.clone()),
        HolType::Bool => HolType::Bool,
        HolType::Fun { domain, codomain } => HolType::fun(
            substitute_type_in_type(domain, substitutions),
            substitute_type_in_type(codomain, substitutions),
        ),
        HolType::TyOp { name, args } => HolType::TyOp {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| substitute_type_in_type(arg, substitutions))
                .collect(),
        },
    }
}

pub(super) fn substitute_type_in_term(
    term: &HolTerm,
    substitutions: &[HolTypeSubstitution],
) -> HolTerm {
    match term {
        HolTerm::Var { name, ty } => {
            HolTerm::var(name.clone(), substitute_type_in_type(ty, substitutions))
        }
        HolTerm::Const { name, ty } => {
            HolTerm::const_(name.clone(), substitute_type_in_type(ty, substitutions))
        }
        HolTerm::App { func, arg } => HolTerm::app(
            substitute_type_in_term(func, substitutions),
            substitute_type_in_term(arg, substitutions),
        ),
        HolTerm::Abs { binder, body } => HolTerm::abs(
            HolVar::new(
                binder.name.clone(),
                substitute_type_in_type(&binder.ty, substitutions),
            ),
            substitute_type_in_term(body, substitutions),
        ),
    }
}

pub(super) fn support_declarations(
    symbols: &mut SymbolCollector,
) -> Result<Vec<Declaration>, HolLightImportError> {
    let mut declarations = Vec::new();
    let type_ops = symbols.type_ops().to_vec();
    let consts = symbols.consts().to_vec();
    for symbol in &type_ops {
        let mut ty = Expr::type_();
        for _ in 0..symbol.arity {
            ty = Expr::pi(BinderInfo::Implicit, Expr::type_(), ty);
        }
        declarations.push(Declaration::Axiom {
            name: type_op_name(symbol),
            level_params: Vec::new(),
            type_: ty,
        });
    }
    for symbol in &consts {
        let type_vars = free_type_vars(&symbol.ty);
        let scope = Scope::with_type_vars(&type_vars);
        let mut scratch = SymbolCollector::default();
        let mut translator = TermTranslator::new(&mut scratch);
        let mut ty = translator.translate_type(&scope, &symbol.ty)?;
        for binder in scope.binders().iter().rev() {
            debug_assert_eq!(binder.kind, ScopeBinderKind::TypeVar);
            ty = Expr::pi(BinderInfo::Implicit, binder.lean_ty.clone(), ty);
        }
        declarations.push(Declaration::Axiom {
            name: const_name(symbol),
            level_params: Vec::new(),
            type_: ty,
        });
    }
    Ok(declarations)
}
