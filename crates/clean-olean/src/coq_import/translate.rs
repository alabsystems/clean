// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation from Coq Gallina terms to clean kernel expressions.

use super::ast::{
    CaseBranch, CaseInfo, Constr, ConstructRef, CoqName, CoqSort, UniverseInstance, UniverseLevel,
};
use super::{CoqImportError, CoqImportResult};
use clean_kernel::{BinderInfo, Expr, Level, LevelVec, Name};

/// Translation environment for Coq `Rel` binders.
#[derive(Debug, Clone, Default)]
pub struct TranslationContext {
    locals: Vec<Option<String>>,
}

impl TranslationContext {
    #[must_use]
    pub fn with_locals(locals: impl IntoIterator<Item = Option<String>>) -> Self {
        Self {
            locals: locals.into_iter().collect(),
        }
    }

    #[must_use]
    pub fn locals(&self) -> &[Option<String>] {
        &self.locals
    }
}

/// Translate a Coq term into a Lean kernel `Expr`.
pub fn translate_term(term: &Constr) -> CoqImportResult<Expr> {
    translate_term_with_context(term, &TranslationContext::default())
}

/// Translate a Coq term using a caller-provided binder context.
pub fn translate_term_with_context(
    term: &Constr,
    context: &TranslationContext,
) -> CoqImportResult<Expr> {
    let mut translator = Translator {
        locals: context.locals.clone(),
    };
    translator.translate(term)
}

struct Translator {
    locals: Vec<Option<String>>,
}

impl Translator {
    fn translate(&mut self, term: &Constr) -> CoqImportResult<Expr> {
        match term {
            Constr::Rel(index) => self.translate_rel(*index),
            Constr::Var(name) => Ok(Expr::const_(translate_name(name), LevelVec::new())),
            Constr::Meta(_) => Err(CoqImportError::UnsupportedNode { node: "Meta" }),
            Constr::Evar { .. } => Err(CoqImportError::UnsupportedNode { node: "Evar" }),
            Constr::Sort(sort) => translate_sort(sort),
            Constr::Cast { term, .. } => self.translate(term),
            Constr::Prod { binder, body } => {
                let binder_ty = self.translate(&binder.ty)?;
                self.locals.push(binder.name.clone());
                let body = self.translate(body)?;
                let _ = self.locals.pop();
                Ok(Expr::pi(BinderInfo::from(binder.info), binder_ty, body))
            }
            Constr::Lambda { binder, body } => {
                let binder_ty = self.translate(&binder.ty)?;
                self.locals.push(binder.name.clone());
                let body = self.translate(body)?;
                let _ = self.locals.pop();
                Ok(Expr::lam(BinderInfo::from(binder.info), binder_ty, body))
            }
            Constr::LetIn {
                name,
                type_,
                value,
                body,
            } => {
                let type_ = self.translate(type_)?;
                let value = self.translate(value)?;
                self.locals.push(name.clone());
                let body = self.translate(body)?;
                let _ = self.locals.pop();
                Ok(Expr::let_named(
                    name.as_deref().map_or_else(Name::anon, Name::from_string),
                    type_,
                    value,
                    body,
                    false,
                ))
            }
            Constr::App { func, args } => {
                if args.is_empty() {
                    return Err(CoqImportError::EmptyApplication);
                }
                let func = self.translate(func)?;
                let args = args
                    .iter()
                    .map(|arg| self.translate(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Expr::apps(func, args))
            }
            Constr::Const { name, universes } => Ok(Expr::const_(
                translate_name(name),
                translate_universe_instance(universes)?,
            )),
            Constr::Ind(reference) => Ok(Expr::const_(
                translate_name(&reference.name),
                translate_universe_instance(&reference.universes)?,
            )),
            Constr::Construct(reference) => Ok(Expr::const_(
                translate_construct_name(reference),
                translate_universe_instance(&reference.universes)?,
            )),
            Constr::Case(case_info) => self.translate_case(case_info),
            Constr::Fix(_) => Err(CoqImportError::UnsupportedNode { node: "Fix" }),
            Constr::CoFix(_) => Err(CoqImportError::UnsupportedNode { node: "CoFix" }),
        }
    }

    fn translate_rel(&self, index: u32) -> CoqImportResult<Expr> {
        if index == 0 {
            return Err(CoqImportError::InvalidRelIndex { index });
        }
        let slot = usize::try_from(index - 1).expect("u32 fits in usize");
        if slot >= self.locals.len() {
            return Err(CoqImportError::UnboundRel {
                index,
                depth: self.locals.len(),
            });
        }
        Ok(Expr::bvar(index - 1))
    }

    fn translate_case(&mut self, case_info: &CaseInfo) -> CoqImportResult<Expr> {
        let Some(eliminator) = &case_info.eliminator else {
            return Err(CoqImportError::MissingCaseEliminator);
        };
        let motive = self.translate(&case_info.motive)?;
        let scrutinee = self.translate(&case_info.scrutinee)?;
        let mut args = vec![motive, scrutinee];
        for branch in &case_info.branches {
            args.push(self.translate_case_branch(branch)?);
        }
        Ok(Expr::apps(
            Expr::const_(
                translate_name(eliminator),
                translate_universe_instance(&case_info.universes)?,
            ),
            args,
        ))
    }

    fn translate_case_branch(&mut self, branch: &CaseBranch) -> CoqImportResult<Expr> {
        let mut binders = Vec::with_capacity(branch.binders.len());
        for binder in &branch.binders {
            let ty = self.translate(&binder.ty)?;
            self.locals.push(binder.name.clone());
            binders.push((binder.info, ty));
        }
        let body = self.translate(&branch.body)?;
        for _ in &branch.binders {
            let _ = self.locals.pop();
        }
        Ok(wrap_lambdas(body, binders))
    }
}

fn wrap_lambdas(mut body: Expr, binders: Vec<(super::ast::CoqBinderKind, Expr)>) -> Expr {
    for (info, ty) in binders.into_iter().rev() {
        body = Expr::lam(BinderInfo::from(info), ty, body);
    }
    body
}

fn translate_name(name: &CoqName) -> Name {
    Name::from_string(&name.as_dotted())
}

fn translate_construct_name(reference: &ConstructRef) -> Name {
    match &reference.constructor_name {
        Some(name) => Name::append(&translate_name(&reference.inductive), name),
        None => translate_name(&reference.inductive).num(u64::from(reference.constructor_index)),
    }
}

fn translate_sort(sort: &CoqSort) -> CoqImportResult<Expr> {
    match sort {
        CoqSort::Prop => Ok(Expr::prop()),
        CoqSort::Set => Ok(Expr::type_()),
        CoqSort::SProp => Err(CoqImportError::UnsupportedSort { sort: "SProp" }),
        CoqSort::Type(level) => Ok(Expr::sort(Level::succ(translate_level(level)?))),
    }
}

fn translate_universe_instance(instance: &UniverseInstance) -> CoqImportResult<LevelVec> {
    let mut levels = LevelVec::new();
    for level in &instance.levels {
        levels.push(translate_level(level)?);
    }
    Ok(levels)
}

fn translate_level(level: &UniverseLevel) -> CoqImportResult<Level> {
    match level {
        UniverseLevel::Zero => Ok(Level::zero()),
        UniverseLevel::Succ(inner) => Ok(Level::succ(translate_level(inner)?)),
        UniverseLevel::Max(levels) => {
            let mut iter = levels.iter();
            let Some(first) = iter.next() else {
                return Err(CoqImportError::EmptyMaxUniverse);
            };
            let mut out = translate_level(first)?;
            for level in iter {
                out = Level::max(out, translate_level(level)?);
            }
            Ok(out)
        }
        UniverseLevel::IMax(left, right) => {
            Ok(Level::imax(translate_level(left)?, translate_level(right)?))
        }
        UniverseLevel::Param(name) => Ok(Level::param(Name::from_string(name))),
    }
}
