// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq term lowering into kernel expressions.

use super::context::TranslationContext;
use super::support::{
    sanitize_name_component, translate_coq_name, translate_sort, translate_universe_instance,
};
use super::TranslatedGlobalDecl;
use crate::inductive::{
    Constructor as KernelConstructor, InductiveDecl as KernelInductiveDecl,
    InductiveType as KernelInductiveType,
};
use crate::{
    coq_import::{
        Binder, CaseBranch, CaseInfo, ConstantDecl, ConstantDeclKind, Constr, ConstructRef,
        CoqBinderKind, CoqImportError, CoqImportResult, FixBody, GlobalDecl, InductiveKind,
        InductiveRef, MutualInductiveDecl, ProjectionRef,
    },
    BinderInfo, Declaration, Expr, LevelVec, Name,
};

#[derive(Debug, Clone)]
struct TranslatedBinder {
    info: CoqBinderKind,
    ty: Expr,
}

struct Translator<'a> {
    context: &'a TranslationContext,
    locals: Vec<Option<String>>,
}

impl<'a> Translator<'a> {
    fn new(context: &'a TranslationContext) -> Self {
        Self {
            context,
            locals: context.locals().to_vec(),
        }
    }

    fn translate(&mut self, term: &Constr) -> CoqImportResult<Expr> {
        match term {
            Constr::Rel(index) => self.translate_rel(*index),
            Constr::Var(name) => Ok(self.translate_var(name)),
            Constr::Meta(_) => Err(CoqImportError::UnsupportedNode { node: "Meta" }),
            Constr::Evar { .. } => Err(CoqImportError::UnsupportedNode { node: "Evar" }),
            Constr::Sort(sort) => translate_sort(sort),
            Constr::Cast { term, .. } => self.translate(term),
            Constr::Prod { binder, body } => self.translate_binder_node(binder, body, true),
            Constr::Lambda { binder, body } => self.translate_binder_node(binder, body, false),
            Constr::LetIn {
                name,
                type_,
                value,
                body,
            } => self.translate_let(name, type_, value, body),
            Constr::App { func, args } => self.translate_app(func, args),
            Constr::Const { name, universes } => Ok(Expr::const_(
                self.translate_global_name(name),
                translate_universe_instance(universes)?,
            )),
            Constr::Ind(reference) => Ok(Expr::const_(
                self.translate_inductive_ref(reference),
                translate_universe_instance(&reference.universes)?,
            )),
            Constr::Construct(reference) => Ok(Expr::const_(
                self.translate_construct_name(reference),
                translate_universe_instance(&reference.universes)?,
            )),
            Constr::Case(case_info) => self.translate_case(case_info),
            Constr::Fix(fix_term) => {
                self.translate_fix_like(&fix_term.bodies, fix_term.index, false)
            }
            Constr::CoFix(cofix_term) => {
                self.translate_fix_like(&cofix_term.bodies, cofix_term.index, true)
            }
            Constr::Proj { projection, term } => self.translate_proj(projection, term),
        }
    }

    fn translate_binder_node(
        &mut self,
        binder: &Binder,
        body: &Constr,
        is_pi: bool,
    ) -> CoqImportResult<Expr> {
        let binder_ty = self.translate(&binder.ty)?;
        self.locals.push(binder.name.clone());
        let body = self.translate(body)?;
        let _ = self.locals.pop();
        let info = BinderInfo::from(binder.info);
        Ok(if is_pi {
            Expr::pi(info, binder_ty, body)
        } else {
            Expr::lam(info, binder_ty, body)
        })
    }

    fn translate_let(
        &mut self,
        name: &Option<String>,
        type_: &Constr,
        value: &Constr,
        body: &Constr,
    ) -> CoqImportResult<Expr> {
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

    fn translate_app(&mut self, func: &Constr, args: &[Constr]) -> CoqImportResult<Expr> {
        if args.is_empty() {
            return Err(CoqImportError::EmptyApplication);
        }
        let func = self.translate(func)?;
        let args = args
            .iter()
            .map(|arg| self.translate(arg))
            .collect::<CoqImportResult<Vec<_>>>()?;
        Ok(Expr::apps(func, args))
    }

    fn translate_binder_prefix(
        &mut self,
        binders: &[Binder],
    ) -> CoqImportResult<Vec<TranslatedBinder>> {
        let mut out = Vec::with_capacity(binders.len());
        for binder in binders {
            let ty = self.translate(&binder.ty)?;
            self.locals.push(binder.name.clone());
            out.push(TranslatedBinder {
                info: binder.info,
                ty,
            });
        }
        Ok(out)
    }

    fn pop_locals(&mut self, count: usize) {
        for _ in 0..count {
            let _ = self.locals.pop();
        }
    }

    fn translate_rel(&self, index: u32) -> CoqImportResult<Expr> {
        if index == 0 {
            return Err(CoqImportError::InvalidRelIndex { index });
        }
        // Coq Rel indices are 1-based; the 0-based slot must name a local.
        // A failed usize conversion means the index is out of range too.
        match usize::try_from(index - 1) {
            Ok(slot) if slot < self.locals.len() => Ok(Expr::bvar(index - 1)),
            _ => Err(CoqImportError::UnboundRel {
                index,
                depth: self.locals.len(),
            }),
        }
    }

    fn translate_var(&self, name: &crate::coq_import::CoqName) -> Expr {
        if let Some(last) = name.segments().last() {
            if let Some(idx) = self
                .locals
                .iter()
                .rev()
                .position(|local| local.as_ref() == Some(last))
            {
                // Binder depth is bounded far below u32::MAX; if the
                // conversion ever failed, fall through to the global
                // constant translation instead of panicking.
                if let Ok(rel) = u32::try_from(idx) {
                    return Expr::bvar(rel);
                }
            }
        }
        Expr::const_(self.translate_global_name(name), LevelVec::new())
    }

    fn translate_case(&mut self, case_info: &CaseInfo) -> CoqImportResult<Expr> {
        // Lean-faithful casesOn order: params → motive → indices → major
        // (scrutinee) → minors (branches).
        let mut args = Vec::new();
        for parameter in &case_info.parameters {
            args.push(self.translate(parameter)?);
        }
        args.push(self.translate(&case_info.motive)?);
        for index in &case_info.indices {
            args.push(self.translate(index)?);
        }
        args.push(self.translate(&case_info.scrutinee)?);
        for branch in &case_info.branches {
            args.push(self.translate_case_branch(branch)?);
        }

        Ok(Expr::apps(
            Expr::const_(
                self.translate_cases_on_name(case_info),
                translate_universe_instance(&case_info.universes)?,
            ),
            args,
        ))
    }

    fn translate_case_branch(&mut self, branch: &CaseBranch) -> CoqImportResult<Expr> {
        let binders = self.translate_binder_prefix(&branch.binders)?;
        let body = self.translate(&branch.body)?;
        self.pop_locals(binders.len());
        Ok(wrap_lambdas(body, &binders))
    }

    fn translate_proj(
        &mut self,
        projection: &ProjectionRef,
        term: &Constr,
    ) -> CoqImportResult<Expr> {
        Ok(Expr::proj(
            self.translate_inductive_name(&projection.inductive),
            projection.projection_index,
            self.translate(term)?,
        ))
    }

    fn translate_fix_like(
        &mut self,
        bodies: &[FixBody],
        index: usize,
        is_cofix: bool,
    ) -> CoqImportResult<Expr> {
        if index >= bodies.len() {
            return Err(CoqImportError::InvalidFixIndex {
                index,
                len: bodies.len(),
            });
        }

        // `index < bodies.len()` was checked above; an in-memory body count
        // always fits into u64, so a failed conversion is an invalid index.
        let index_lit = u64::try_from(index).map_err(|_| CoqImportError::InvalidFixIndex {
            index,
            len: bodies.len(),
        })?;
        let mut args = vec![
            Expr::nat_lit(index_lit),
            self.translate_fix_annotation(&bodies[index].ty),
        ];
        for (body_idx, body) in bodies.iter().enumerate() {
            // Same bound as `index_lit` above: body indices come from
            // enumerating an in-memory slice.
            let body_idx_lit =
                u64::try_from(body_idx).map_err(|_| CoqImportError::InvalidFixIndex {
                    index: body_idx,
                    len: bodies.len(),
                })?;
            let body_name = body
                .name
                .as_deref()
                .map_or_else(|| format!("body{body_idx}"), sanitize_name_component);
            let placeholder = Expr::const_(
                Name::from_string(&format!(
                    "CoqImport.{}.{}",
                    if is_cofix { "cofix" } else { "fix" },
                    body_name
                )),
                LevelVec::new(),
            );
            let body_expr = Expr::apps(
                Expr::const_(self.context.fix_body_skeleton.clone(), LevelVec::new()),
                [
                    Expr::nat_lit(body_idx_lit),
                    Expr::nat_lit(u64::from(body.recursive_arg)),
                    self.translate_fix_annotation(&body.ty),
                    placeholder,
                ],
            );
            args.push(body_expr);
        }

        Ok(Expr::apps(
            Expr::const_(
                if is_cofix {
                    self.context.cofix_skeleton.clone()
                } else {
                    self.context.fix_skeleton.clone()
                },
                LevelVec::new(),
            ),
            args,
        ))
    }

    fn translate_fix_annotation(&mut self, term: &Constr) -> Expr {
        self.translate(term).unwrap_or_else(|_| Expr::type_())
    }

    fn translate_global_name(&self, name: &crate::coq_import::CoqName) -> Name {
        self.context
            .lookup_global(name)
            .cloned()
            .unwrap_or_else(|| translate_coq_name(name))
    }

    fn translate_inductive_name(&self, name: &crate::coq_import::CoqName) -> Name {
        self.context
            .lookup_inductive(name)
            .map(|mapping| mapping.inductive.clone())
            .unwrap_or_else(|| self.translate_global_name(name))
    }

    fn translate_inductive_ref(&self, reference: &InductiveRef) -> Name {
        self.translate_inductive_name(&reference.name)
    }

    fn translate_cases_on_name(&self, case_info: &CaseInfo) -> Name {
        if let Some(eliminator) = &case_info.eliminator {
            return self.translate_global_name(eliminator);
        }
        if let Some(mapping) = self.context.lookup_inductive(&case_info.inductive) {
            return mapping.cases_on.clone();
        }
        Name::from_string(&format!(
            "{}.casesOn",
            self.translate_inductive_name(&case_info.inductive)
        ))
    }

    fn translate_construct_name(&self, reference: &ConstructRef) -> Name {
        if let Some(mapping) = self.context.lookup_inductive(&reference.inductive) {
            if reference.constructor_index > 0 {
                // A failed usize conversion is treated like an out-of-range
                // constructor index: fall through to name-based translation.
                if let Some(name) = usize::try_from(reference.constructor_index - 1)
                    .ok()
                    .and_then(|idx| mapping.constructors.get(idx))
                {
                    return name.clone();
                }
            }
        }

        if let Some(name) = &reference.constructor_name {
            return Name::append(&self.translate_inductive_name(&reference.inductive), name);
        }

        self.translate_inductive_name(&reference.inductive)
            .num(u64::from(reference.constructor_index))
    }
}

/// Translate one Coq term into a Lean kernel `Expr`.
pub fn translate_term(term: &Constr) -> CoqImportResult<Expr> {
    translate_term_with_context(term, &TranslationContext::default())
}

/// Translate a Coq term using an explicit translation context.
pub fn translate_term_with_context(
    term: &Constr,
    context: &TranslationContext,
) -> CoqImportResult<Expr> {
    let mut translator = Translator::new(context);
    translator.translate(term)
}

/// Translate one Coq constant declaration into a kernel declaration.
pub fn translate_constant_decl(
    decl: &ConstantDecl,
    context: &TranslationContext,
) -> CoqImportResult<Declaration> {
    let name = context
        .lookup_global(&decl.name)
        .cloned()
        .unwrap_or_else(|| translate_coq_name(&decl.name));
    let level_params = decl
        .universe_params
        .iter()
        .map(|param| Name::from_string(param))
        .collect::<Vec<_>>();
    let type_ = translate_term_with_context(&decl.type_, context)?;
    let value = decl
        .value
        .as_ref()
        .map(|value| translate_term_with_context(value, context))
        .transpose()?;

    match decl.kind {
        ConstantDeclKind::Axiom => Ok(Declaration::Axiom {
            name,
            level_params,
            type_,
        }),
        ConstantDeclKind::Definition => Ok(Declaration::Definition {
            name,
            level_params,
            type_,
            value: value.ok_or(CoqImportError::MissingField {
                context: "definition declaration",
                field: "value",
            })?,
            is_reducible: false,
        }),
        ConstantDeclKind::Theorem => Ok(Declaration::Theorem {
            name,
            level_params,
            type_,
            value: value.ok_or(CoqImportError::MissingField {
                context: "theorem declaration",
                field: "value",
            })?,
        }),
        ConstantDeclKind::Opaque => Ok(Declaration::Opaque {
            name,
            level_params,
            type_,
            value: value.ok_or(CoqImportError::MissingField {
                context: "opaque declaration",
                field: "value",
            })?,
        }),
    }
}

/// Translate one Coq inductive block into a kernel inductive declaration.
pub fn translate_inductive_decl(
    decl: &MutualInductiveDecl,
    context: &TranslationContext,
) -> CoqImportResult<KernelInductiveDecl> {
    // Fail closed on CoInductive blocks: the kernel has no greatest-fixpoint
    // primitive, so the only thing this lane could produce is the least-fixpoint
    // reinterpretation — a different type (often empty) that would also receive
    // an induction principle the coinductive must not have. The SerAPI lane
    // (clean-mathverse alpha) handles coinductives via its own documented
    // reconstruction; this lane rejects them rather than silently converting.
    if decl.kind == InductiveKind::CoInductive {
        let name = decl
            .bodies
            .first()
            .map(|body| body.name.as_dotted())
            .unwrap_or_else(|| "<empty block>".to_string());
        return Err(CoqImportError::CoinductiveUnsupported { name });
    }

    let mut translator = Translator::new(context);
    let shared_params = translator.translate_binder_prefix(&decl.params)?;
    let mut types = Vec::with_capacity(decl.bodies.len());

    for body in &decl.bodies {
        let type_ = wrap_pis(translator.translate(&body.type_)?, &shared_params);
        let constructors = body
            .constructors
            .iter()
            .map(|ctor| {
                Ok(KernelConstructor {
                    name: translator.translate_global_name(&ctor.name),
                    type_: wrap_pis(translator.translate(&ctor.type_)?, &shared_params),
                })
            })
            .collect::<CoqImportResult<Vec<_>>>()?;

        types.push(KernelInductiveType {
            name: translator.translate_inductive_name(&body.name),
            type_,
            constructors,
        });
    }

    translator.pop_locals(shared_params.len());

    Ok(KernelInductiveDecl {
        level_params: decl
            .universe_params
            .iter()
            .map(|param| Name::from_string(param))
            .collect(),
        num_params: decl.num_params,
        types,
    })
}

/// Translate one top-level Coq declaration.
pub fn translate_global_decl(
    decl: &GlobalDecl,
    context: &TranslationContext,
) -> CoqImportResult<TranslatedGlobalDecl> {
    match decl {
        GlobalDecl::Constant(constant) => Ok(TranslatedGlobalDecl::Constant(
            translate_constant_decl(constant, context)?,
        )),
        GlobalDecl::Inductive(inductive) => Ok(TranslatedGlobalDecl::Inductive(
            translate_inductive_decl(inductive, context)?,
        )),
    }
}

fn wrap_pis(mut body: Expr, binders: &[TranslatedBinder]) -> Expr {
    for binder in binders.iter().rev() {
        body = Expr::pi(BinderInfo::from(binder.info), binder.ty.clone(), body);
    }
    body
}

fn wrap_lambdas(mut body: Expr, binders: &[TranslatedBinder]) -> Expr {
    for binder in binders.iter().rev() {
        body = Expr::lam(BinderInfo::from(binder.info), binder.ty.clone(), body);
    }
    body
}
