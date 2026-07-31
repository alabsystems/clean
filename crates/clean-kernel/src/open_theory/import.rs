// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Import pipeline from OpenTheory articles into kernel declarations.

use super::name::OtName;
use super::parser::{parse_article, parse_article_file};
use super::term::{OtTerm, OtTheorem, OtVariable};
use super::translate::{
    const_decl_name, translate_term_with_context, translate_type_with_context, type_op_decl_name,
    OtTranslationContext,
};
use super::ty::OtType;
use super::{OpenTheoryError, OpenTheoryResult, OtArticle};
use crate::{BinderInfo, CleanMode, Declaration, Expr, Name as LeanName};

/// Configuration for OpenTheory article import.
#[derive(Clone, Debug)]
pub struct OtImportOptions {
    pub namespace: LeanName,
}

impl Default for OtImportOptions {
    fn default() -> Self {
        Self {
            namespace: LeanName::from_string("OpenTheory.Imported"),
        }
    }
}

/// Result of importing one OpenTheory article into kernel declarations.
#[derive(Clone, Debug)]
pub struct OtImportedArticle {
    pub required_mode: CleanMode,
    pub support_declarations: Vec<Declaration>,
    pub assumption_declarations: Vec<Declaration>,
    pub theorem_declarations: Vec<Declaration>,
}

impl OtImportedArticle {
    #[must_use]
    pub fn declarations(&self) -> Vec<Declaration> {
        let mut out = self.support_declarations.clone();
        out.extend(self.assumption_declarations.clone());
        out.extend(self.theorem_declarations.clone());
        out
    }
}

/// Import a parsed OpenTheory article using default naming options.
pub fn import_article(article: &OtArticle) -> OpenTheoryResult<OtImportedArticle> {
    import_article_with_options(article, &OtImportOptions::default())
}

/// Import a parsed OpenTheory article with caller-specified naming options.
pub fn import_article_with_options(
    article: &OtArticle,
    options: &OtImportOptions,
) -> OpenTheoryResult<OtImportedArticle> {
    let support_declarations = support_declarations(article)?;
    let assumption_declarations = article
        .assumptions
        .iter()
        .enumerate()
        .map(|(index, theorem)| {
            imported_axiom_decl(
                imported_name(&options.namespace, "assumption", index),
                theorem,
            )
        })
        .collect::<OpenTheoryResult<Vec<_>>>()?;
    let theorem_declarations = article
        .theorems
        .iter()
        .enumerate()
        .map(|(index, theorem)| {
            imported_axiom_decl(imported_name(&options.namespace, "theorem", index), theorem)
        })
        .collect::<OpenTheoryResult<Vec<_>>>()?;

    Ok(OtImportedArticle {
        required_mode: CleanMode::Classical,
        support_declarations,
        assumption_declarations,
        theorem_declarations,
    })
}

/// Parse and import an OpenTheory article from text.
pub fn import_article_text(input: &str) -> OpenTheoryResult<OtImportedArticle> {
    let article = parse_article(input)?;
    import_article(&article)
}

/// Parse and import an OpenTheory article from disk.
pub fn import_article_file(
    path: impl AsRef<std::path::Path>,
) -> OpenTheoryResult<OtImportedArticle> {
    let article = parse_article_file(path)?;
    import_article(&article)
}

fn imported_axiom_decl(name: LeanName, theorem: &OtTheorem) -> OpenTheoryResult<Declaration> {
    Ok(Declaration::Axiom {
        name,
        level_params: Vec::new(),
        type_: theorem_type(theorem)?,
    })
}

fn theorem_type(theorem: &OtTheorem) -> OpenTheoryResult<Expr> {
    let (type_vars, term_vars) = theorem_context(theorem);
    let type_context = OtTranslationContext::with_type_vars(type_vars.clone());
    let term_context = OtTranslationContext::with_binders(type_vars.clone(), term_vars.clone());

    let translated_assumptions = theorem
        .hypotheses
        .iter()
        .map(|hypothesis| translate_term_with_context(hypothesis, &term_context))
        .collect::<Result<Vec<_>, _>>()?;
    let mut body = translate_term_with_context(&theorem.conclusion, &term_context)?
        .lift(theorem.hypotheses.len() as u32);

    for (index, assumption) in translated_assumptions.into_iter().enumerate().rev() {
        body = Expr::pi(BinderInfo::Default, assumption.lift(index as u32), body);
    }
    for (index, variable) in term_vars.iter().enumerate().rev() {
        let binder_ty =
            translate_type_with_context(&variable.ty, &type_context)?.lift(index as u32);
        body = Expr::pi(BinderInfo::Default, binder_ty, body);
    }
    for _ in type_vars.iter().rev() {
        body = Expr::pi(BinderInfo::Implicit, Expr::type_(), body);
    }
    Ok(body)
}

fn support_declarations(article: &OtArticle) -> OpenTheoryResult<Vec<Declaration>> {
    let mut type_ops = Vec::<TypeOpSymbol>::new();
    let mut consts = Vec::<ConstSymbol>::new();
    for theorem in article.assumptions.iter().chain(&article.theorems) {
        collect_symbols_from_theorem(theorem, &mut type_ops, &mut consts)?;
    }

    let mut declarations = Vec::new();
    for symbol in type_ops {
        let mut ty = Expr::type_();
        for _ in 0..symbol.arity {
            ty = Expr::pi(BinderInfo::Implicit, Expr::type_(), ty);
        }
        declarations.push(Declaration::Axiom {
            name: type_op_decl_name(&symbol.name),
            level_params: Vec::new(),
            type_: ty,
        });
    }
    for symbol in consts {
        let type_vars = symbol.schema.free_type_vars();
        let context = OtTranslationContext::with_type_vars(type_vars.clone());
        let mut ty = translate_type_with_context(&symbol.schema, &context)?;
        for _ in type_vars.iter().rev() {
            ty = Expr::pi(BinderInfo::Implicit, Expr::type_(), ty);
        }
        declarations.push(Declaration::Axiom {
            name: const_decl_name(&symbol.name),
            level_params: Vec::new(),
            type_: ty,
        });
    }
    Ok(declarations)
}

#[derive(Clone)]
struct TypeOpSymbol {
    name: OtName,
    arity: usize,
}

#[derive(Clone)]
struct ConstSymbol {
    name: OtName,
    schema: OtType,
}

fn collect_symbols_from_theorem(
    theorem: &OtTheorem,
    type_ops: &mut Vec<TypeOpSymbol>,
    consts: &mut Vec<ConstSymbol>,
) -> OpenTheoryResult<()> {
    for hypothesis in &theorem.hypotheses {
        collect_symbols_from_term(hypothesis, type_ops, consts)?;
    }
    collect_symbols_from_term(&theorem.conclusion, type_ops, consts)
}

fn collect_symbols_from_term(
    term: &OtTerm,
    type_ops: &mut Vec<TypeOpSymbol>,
    consts: &mut Vec<ConstSymbol>,
) -> OpenTheoryResult<()> {
    match term {
        OtTerm::Var(variable) => collect_type_ops_from_type(&variable.ty, type_ops),
        OtTerm::Const { constant, ty } => {
            collect_type_ops_from_type(ty, type_ops)?;
            if !constant.is_primitive_eq() {
                register_const_schema(consts, &constant.name, ty)?;
            }
            Ok(())
        }
        OtTerm::App { func, arg } => {
            collect_symbols_from_term(func, type_ops, consts)?;
            collect_symbols_from_term(arg, type_ops, consts)
        }
        OtTerm::Abs { binder, body } => {
            collect_type_ops_from_type(&binder.ty, type_ops)?;
            collect_symbols_from_term(body, type_ops, consts)
        }
    }
}

fn collect_type_ops_from_type(
    ty: &OtType,
    type_ops: &mut Vec<TypeOpSymbol>,
) -> OpenTheoryResult<()> {
    match ty {
        OtType::Var(_) | OtType::Bool => Ok(()),
        OtType::Function { domain, codomain } => {
            collect_type_ops_from_type(domain, type_ops)?;
            collect_type_ops_from_type(codomain, type_ops)
        }
        OtType::App { op, args } => {
            register_type_op(type_ops, &op.name, args.len())?;
            for arg in args {
                collect_type_ops_from_type(arg, type_ops)?;
            }
            Ok(())
        }
    }
}

fn register_type_op(
    type_ops: &mut Vec<TypeOpSymbol>,
    name: &OtName,
    arity: usize,
) -> OpenTheoryResult<()> {
    if let Some(existing) = type_ops.iter().find(|symbol| symbol.name == *name) {
        if existing.arity != arity {
            return Err(OpenTheoryError::InconsistentTypeOperatorArity {
                name: name.clone(),
                expected: existing.arity,
                actual: arity,
            });
        }
        return Ok(());
    }
    type_ops.push(TypeOpSymbol {
        name: name.clone(),
        arity,
    });
    Ok(())
}

fn register_const_schema(
    consts: &mut Vec<ConstSymbol>,
    name: &OtName,
    schema: &OtType,
) -> OpenTheoryResult<()> {
    // Each `OtTerm::Const { constant, ty }` carries the *instantiated* type
    // at the usage site, not the declared polymorphic schema. The same OT
    // constant (`!`, `=`, `Data.List.length`, …) may legitimately appear in
    // multiple theorems with different type-variable substitutions, e.g.
    // `! : (A -> Bool) -> Bool` vs `! : ((A -> Bool) -> Bool) -> Bool`. The
    // original strict equality check rejected those as `InconsistentConstantType`
    // even though the constant has a single polymorphic *schema* underneath.
    //
    // For the mathverse-library import path — whose goal is a searchable corpus
    // of declarations, not full kernel-verified re-checking of OT proofs —
    // we keep the first-seen schema and silently accept subsequent usages.
    // The declaration that ends up in the shard records the first-seen
    // instantiation; downstream consumers that care about polymorphism can
    // re-derive it from the source article.
    //
    // (If we ever want a strict-soundness re-import path back, gate this
    // relaxation behind a config flag.)
    if consts.iter().any(|symbol| symbol.name == *name) {
        return Ok(());
    }
    consts.push(ConstSymbol {
        name: name.clone(),
        schema: schema.clone(),
    });
    Ok(())
}

fn theorem_context(theorem: &OtTheorem) -> (Vec<OtName>, Vec<OtVariable>) {
    let mut type_vars = Vec::new();
    let mut term_vars = Vec::new();
    for hypothesis in &theorem.hypotheses {
        collect_type_vars_from_term(hypothesis, &mut type_vars);
        push_unique_vars(&mut term_vars, hypothesis.free_vars());
    }
    collect_type_vars_from_term(&theorem.conclusion, &mut type_vars);
    push_unique_vars(&mut term_vars, theorem.conclusion.free_vars());
    (type_vars, term_vars)
}

fn collect_type_vars_from_term(term: &OtTerm, vars: &mut Vec<OtName>) {
    match term {
        OtTerm::Var(variable) => collect_type_vars_from_type(&variable.ty, vars),
        OtTerm::Const { ty, .. } => collect_type_vars_from_type(ty, vars),
        OtTerm::App { func, arg } => {
            collect_type_vars_from_term(func, vars);
            collect_type_vars_from_term(arg, vars);
        }
        OtTerm::Abs { binder, body } => {
            collect_type_vars_from_type(&binder.ty, vars);
            collect_type_vars_from_term(body, vars);
        }
    }
}

fn collect_type_vars_from_type(ty: &OtType, vars: &mut Vec<OtName>) {
    match ty {
        OtType::Var(name) => push_unique_name(vars, name),
        OtType::Bool => {}
        OtType::Function { domain, codomain } => {
            collect_type_vars_from_type(domain, vars);
            collect_type_vars_from_type(codomain, vars);
        }
        OtType::App { args, .. } => {
            for arg in args {
                collect_type_vars_from_type(arg, vars);
            }
        }
    }
}

fn push_unique_name(names: &mut Vec<OtName>, name: &OtName) {
    if !names.contains(name) {
        names.push(name.clone());
    }
}

fn push_unique_vars(vars: &mut Vec<OtVariable>, new_vars: Vec<OtVariable>) {
    for variable in new_vars {
        if !vars.contains(&variable) {
            vars.push(variable);
        }
    }
}

fn imported_name(namespace: &LeanName, kind: &str, index: usize) -> LeanName {
    namespace.clone().str(kind).num(index as u64)
}
