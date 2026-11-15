// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact captured-context adapter to the existing IR data model. This is
//! diagnostic pre-RC IR, not an executable ABI/library/refinement certificate.
//! Unknown layouts, eliminators and body dependencies remain explicit rows.

use super::typing::{Budget, Typing};
use super::{RuntimeContext, RuntimeLimits, RuntimeLowerError as Error, RuntimeRowOrigin};
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use crate::lcnf::{Arg, Code, Decl, DeclValue, LetValue, Param};
use clean_kernel::{Expr, ExprKind, FVarId, Level, Multiplicity, Name};
use clean_olean::import::runtime::RuntimeFamily;
use clean_olean::module::ConstantKind;
use std::collections::{BTreeMap, BTreeSet, HashSet};

#[derive(Clone, Debug)]
pub enum RuntimeIrStatus {
    /// Exact source body plus any explicit, typed lambda-lifted functions.
    Lowered(Vec<IRDecl>),
    /// A type former is retained as a row; it is not an executable function.
    TypeFormer,
    /// Captured family metadata, structurally cross-checked by dependency_closure
    /// but not a standalone header-typing/admission token. A consuming definition
    /// separately checks all reachable headers before using a layout.
    CapturedFamilyMetadata,
    Refused(Error),
}
#[derive(Clone, Debug)]
pub struct RuntimeIrRow {
    pub origin: RuntimeRowOrigin,
    pub status: RuntimeIrStatus,
    pub specializations: Vec<RuntimeIrSpecialization>,
}
#[derive(Clone, Debug)]
pub struct RuntimeIrSpecialization {
    pub generated_name: Name,
    pub source: RuntimeRowOrigin,
    pub wrapper: RuntimeRowOrigin,
    pub recursor: RuntimeRowOrigin,
    pub family: RuntimeRowOrigin,
    pub level_arguments: Vec<Level>,
    pub motive: Expr,
}
#[derive(Clone, Debug)]
pub struct RuntimeIrOutput {
    pub root: Name,
    pub rows: Vec<RuntimeIrRow>,
}

pub(super) fn lower(
    context: &RuntimeContext,
    root: &Name,
    limits: RuntimeLimits,
) -> Result<RuntimeIrOutput, Error> {
    let closure = context.dependency_closure(root, limits)?;
    let mut rows = Vec::with_capacity(closure.len());
    for origin in closure {
        let row = context.declaration(&origin.name)?;
        let mut specializations = Vec::new();
        let status = match row.kind {
            ConstantKind::Inductive | ConstantKind::Constructor => {
                RuntimeIrStatus::CapturedFamilyMetadata
            }
            ConstantKind::Definition => {
                // Validate all source binders/bodies before even reporting an
                // erased type former. This keeps Zero/One and malformed context
                // refusals ahead of every erasure decision.
                match context.lower_definition(&origin.name, limits) {
                    Err(error) => RuntimeIrStatus::Refused(error),
                    Ok(output) => {
                        if type_former(row.type_.as_ref().map_err(|e| Error::Capture(e.clone()))?) {
                            RuntimeIrStatus::TypeFormer
                        } else {
                            let mut compiler = Compiler {
                                context,
                                budget: Budget::new(limits),
                                levels: row.level_params.clone(),
                                generated: Vec::new(),
                                specializations: Vec::new(),
                                names: context.catalog.keys().cloned().collect(),
                                next_name: 0,
                                owner: origin.name.clone(),
                            };
                            match compiler.declaration(&output.declaration) {
                                Ok(decl) => {
                                    let mut decls = vec![decl];
                                    decls.extend(compiler.generated);
                                    specializations = compiler.specializations;
                                    RuntimeIrStatus::Lowered(decls)
                                }
                                Err(error) => RuntimeIrStatus::Refused(error),
                            }
                        }
                    }
                }
            }
            _ => RuntimeIrStatus::Refused(Error::Unsupported("runtime eliminator/body lowering")),
        };
        rows.push(RuntimeIrRow {
            origin,
            status,
            specializations,
        });
    }
    Ok(RuntimeIrOutput {
        root: root.clone(),
        rows,
    })
}

fn type_former(ty: &Expr) -> bool {
    let mut ty = ty;
    while let ExprKind::Pi(_, _, body) = ty.kind() {
        ty = body;
    }
    matches!(ty.kind(), ExprKind::Sort(_))
}

#[derive(Default)]
struct Locals {
    types: BTreeMap<FVarId, Expr>,
    values: BTreeMap<FVarId, IRArg>,
    next: u32,
}
impl Locals {
    fn value(&self, id: FVarId) -> Result<IRArg, Error> {
        self.values.get(&id).cloned().ok_or(Error::UnboundVariable)
    }
    fn fresh(&mut self, id: FVarId, ty: Expr, layout: &IRType) -> Result<IRArg, Error> {
        if self.types.insert(id, ty).is_some() {
            return Err(Error::Unsupported("duplicate LCNF local"));
        }
        let value = if *layout == IRType::Erased {
            IRArg::Erased
        } else {
            let var = VarId(self.next);
            self.next = self
                .next
                .checked_add(1)
                .ok_or(Error::Resource("IR local"))?;
            IRArg::Var(var)
        };
        self.values.insert(id, value.clone());
        Ok(value)
    }
}
struct Compiler<'a> {
    context: &'a RuntimeContext,
    budget: Budget,
    levels: Vec<Name>,
    owner: Name,
    names: BTreeSet<Name>,
    next_name: u64,
    generated: Vec<IRDecl>,
    specializations: Vec<RuntimeIrSpecialization>,
}
impl Compiler<'_> {
    fn typing<'b>(&'b mut self, locals: &Locals) -> Result<Typing<'b, 'b>, Error> {
        let mut typing = Typing::new(self.context, &self.levels, &mut self.budget)?;
        typing.seed_locals(&locals.types)?;
        Ok(typing)
    }
    fn layout(&mut self, ty: &Expr, locals: &Locals, depth: usize) -> Result<IRType, Error> {
        self.budget.step(depth)?;
        let ty = self.typing(locals)?.whnf(ty, depth + 1)?;
        if type_former(&ty) {
            return Ok(IRType::Erased);
        }
        match ty.kind() {
            ExprKind::Const(name, levels) => {
                let row = self.context.declaration(name)?;
                if !matches!(row.family, RuntimeFamily::Inductive { .. }) {
                    return Err(Error::Unsupported("non-family runtime layout"));
                }
                let sort = self.typing(locals)?.constant_type(name, levels)?;
                let ExprKind::Sort(level) = sort.kind() else {
                    return Err(Error::ExpectedSort(sort));
                };
                // Exact boxed-data policy, not a fallback for arbitrary names,
                // proofs, metavariables or an unknown dependent result type.
                if !matches!(level.normalize(), Level::Succ(_)) {
                    return Err(Error::Unsupported(
                        "proof or unresolved universe runtime layout",
                    ));
                }
                Ok(IRType::Object)
            }
            ExprKind::Pi(binder, domain, body) => {
                if binder.mult != Multiplicity::Many {
                    return Err(Error::Unsupported("runtime binder multiplicity"));
                }
                self.layout(domain, locals, depth + 1)?;
                // Initial closures require a nondependent, exactly resolved
                // result. A free motive is not replaced with Object.
                self.layout(body, locals, depth + 1)?;
                Ok(IRType::Object)
            }
            _ => Err(Error::Unsupported("unresolved runtime layout")),
        }
    }
    fn parameters(
        &mut self,
        params: &[Param],
        locals: &mut Locals,
        depth: usize,
    ) -> Result<Vec<(VarId, IRType)>, Error> {
        let mut result = Vec::new();
        for param in params {
            let layout = self.layout(&param.ty, locals, depth + 1)?;
            if let IRArg::Var(var) = locals.fresh(param.fvar_id, param.ty.clone(), &layout)? {
                result.push((var, layout));
            }
        }
        Ok(result)
    }
    fn declaration(&mut self, decl: &Decl) -> Result<IRDecl, Error> {
        let mut locals = Locals::default();
        let params = self.parameters(&decl.params, &mut locals, 0)?;
        let return_type = self.layout(&decl.ty, &locals, 0)?;
        if return_type == IRType::Erased {
            return Err(Error::Unsupported("erased runtime root result"));
        }
        let DeclValue::Code(code) = &decl.body else {
            return Err(Error::Unsupported("runtime extern body"));
        };
        let body = self.code(code, &mut locals, 0)?;
        Ok(IRDecl {
            name: decl.name.clone(),
            params,
            return_type,
            body,
        })
    }
    fn ctor(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Arg],
        locals: &Locals,
        depth: usize,
    ) -> Result<IRExpr, Error> {
        let row = self.context.declaration(name)?;
        let RuntimeFamily::Constructor {
            index,
            num_params,
            num_fields,
            ..
        } = &row.family
        else {
            return Err(Error::Unsupported("non-constructor allocation"));
        };
        if *num_params != 0 || args.len() != *num_fields as usize {
            return Err(Error::Unsupported("runtime constructor field arity"));
        }
        let tag = *index;
        let mut ty = self.typing(locals)?.constant_type(name, levels)?;
        let mut values = Vec::new();
        let mut field_types = Vec::new();
        for arg in args {
            self.budget.step(depth)?;
            let ExprKind::Pi(_, domain, body) = ty.kind() else {
                return Err(Error::ExpectedFunction(ty));
            };
            let layout = self.layout(domain, locals, depth + 1)?;
            if layout != IRType::Object {
                return Err(Error::Unsupported("non-object runtime constructor field"));
            }
            let Arg::FVar(id) = arg else {
                return Err(Error::Unsupported("erased runtime constructor field"));
            };
            let value = locals.value(*id)?;
            if value == IRArg::Erased {
                return Err(Error::Unsupported("erased object field"));
            }
            values.push(value);
            field_types.push(layout);
            ty = body.instantiate(&Expr::fvar(*id));
        }
        self.layout(&ty, locals, depth + 1)?;
        Ok(IRExpr::Ctor {
            info: CtorInfo {
                name: name.clone(),
                tag,
                num_scalars: 0,
                num_objects: u32::try_from(field_types.len())
                    .map_err(|_| Error::Resource("constructor fields"))?,
                field_types,
            },
            args: values,
        })
    }
    fn call(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Arg],
        locals: &Locals,
        depth: usize,
    ) -> Result<IRExpr, Error> {
        let mut ty = self.typing(locals)?.constant_type(name, levels)?;
        let mut values = Vec::new();
        let mut source_binders = 0usize;
        for arg in args {
            self.budget.step(depth)?;
            source_binders = source_binders
                .checked_add(1)
                .ok_or(Error::Resource("runtime call arity"))?;
            let signature = self.typing(locals)?.whnf(&ty, depth + 1)?;
            let ExprKind::Pi(_, domain, body) = signature.kind() else {
                return Err(Error::ExpectedFunction(signature));
            };
            let layout = self.layout(domain, locals, depth + 1)?;
            let expr = match arg {
                Arg::Type(expr) if layout == IRType::Erased => expr.clone(),
                Arg::FVar(id) => {
                    let value = locals.value(*id)?;
                    if (layout == IRType::Erased) != (value == IRArg::Erased) {
                        return Err(Error::Unsupported("runtime argument erasure mismatch"));
                    }
                    if value != IRArg::Erased {
                        values.push(value);
                    }
                    Expr::fvar(*id)
                }
                _ => return Err(Error::Unsupported("runtime argument outside typed spine")),
            };
            ty = body.instantiate(&expr);
        }
        let mut remaining = 0usize;
        loop {
            ty = self.typing(locals)?.whnf(&ty, depth + 1)?;
            let ExprKind::Pi(_, domain, body) = ty.kind() else {
                break;
            };
            self.budget.step(depth)?;
            if self.layout(domain, locals, depth + 1)? == IRType::Erased {
                return Err(Error::Unsupported(
                    "unspecialized type argument in runtime closure",
                ));
            }
            remaining = remaining
                .checked_add(1)
                .ok_or(Error::Resource("runtime call arity"))?;
            ty = body.as_ref().clone();
        }
        // Header arity alone does not describe a definition that returns a
        // closure without taking those parameters itself. That needs a staged
        // call/result application; never manufacture its ABI from the Pi type.
        source_binders = source_binders
            .checked_add(remaining)
            .ok_or(Error::Resource("runtime call arity"))?;
        let row = self.context.declaration(name)?;
        let clean_olean::import::runtime::RuntimeBody::Stored(Ok(body)) = &row.body else {
            return Err(Error::Unsupported(
                "runtime call needs stored definition ABI",
            ));
        };
        let mut body = body;
        let mut leading = 0usize;
        while let ExprKind::Lam(_, _, rest) = body.kind() {
            self.budget.step(depth)?;
            leading = leading
                .checked_add(1)
                .ok_or(Error::Resource("runtime call arity"))?;
            body = rest;
        }
        if leading != source_binders {
            return Err(Error::Unsupported(
                "runtime function-value ABI needs staged application",
            ));
        }
        self.layout(&ty, locals, depth + 1)?;
        if remaining == 0 {
            if let [Arg::Type(motive), Arg::FVar(_), Arg::FVar(_), Arg::FVar(_)] = args {
                if values.len() == 3 {
                    if let Some(plan) = super::matcher::derive(
                        self.context,
                        name,
                        levels,
                        motive,
                        &mut self.budget,
                    )? {
                        let specialized = self.matcher(plan, depth + 1)?;
                        return Ok(IRExpr::Apply {
                            fn_id: FnId(specialized),
                            args: values,
                        });
                    }
                }
            }
            Ok(IRExpr::Apply {
                fn_id: FnId(name.clone()),
                args: values,
            })
        } else {
            Ok(IRExpr::PartialApply {
                fn_id: FnId(name.clone()),
                arity: u16::try_from(values.len() + remaining)
                    .map_err(|_| Error::Resource("runtime call arity"))?,
                args: values,
            })
        }
    }

    fn fresh_name(&mut self, component: &str, depth: usize) -> Result<Name, Error> {
        loop {
            self.budget.step(depth)?;
            let candidate = self.owner.clone().str(component).num(self.next_name);
            self.next_name = self
                .next_name
                .checked_add(1)
                .ok_or(Error::Resource("generated name"))?;
            if self.names.insert(candidate.clone()) {
                return Ok(candidate);
            }
        }
    }

    fn matcher(&mut self, plan: super::matcher::Plan, depth: usize) -> Result<Name, Error> {
        let unit_value = if matches!(
            &self.context.declaration(&plan.unit)?.family,
            RuntimeFamily::Constructor { .. }
        ) {
            self.ctor(&plan.unit, &[], &[], &Locals::default(), depth + 1)?
        } else {
            self.call(&plan.unit, &[], &[], &Locals::default(), depth + 1)?
        };
        let name = self.fresh_name("__runtime_match", depth)?;
        let zero = CtorInfo {
            name: plan.zero,
            tag: 0,
            num_scalars: 0,
            num_objects: 0,
            field_types: vec![],
        };
        let succ = CtorInfo {
            name: plan.succ,
            tag: 1,
            num_scalars: 0,
            num_objects: 1,
            field_types: vec![IRType::Object],
        };
        // L5IR variable identities are unique across the whole function, not
        // merely branch-local. Keep the two alternatives' definitions disjoint.
        let closure_call = |closure, argument, result| IRBody::VDecl {
            var: VarId(result),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(closure)),
                args: vec![IRArg::Var(VarId(argument))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(result)))),
        };
        let zero_body = IRBody::VDecl {
            var: VarId(3),
            ty: IRType::Object,
            value: unit_value,
            rest: Box::new(closure_call(1, 3, 4)),
        };
        let succ_body = IRBody::VDecl {
            var: VarId(5),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(closure_call(2, 5, 6)),
        };
        self.generated.push(IRDecl {
            name: name.clone(),
            params: (0..3).map(|i| (VarId(i), IRType::Object)).collect(),
            return_type: IRType::Object,
            body: IRBody::Case {
                scrutinee: VarId(0),
                alts: vec![
                    IRAlt {
                        ctor: zero,
                        body: Box::new(zero_body),
                    },
                    IRAlt {
                        ctor: succ,
                        body: Box::new(succ_body),
                    },
                ],
                default: None,
            },
        });
        self.specializations.push(RuntimeIrSpecialization {
            generated_name: name.clone(),
            source: plan.source,
            wrapper: plan.wrapper,
            recursor: plan.recursor,
            family: plan.family,
            level_arguments: plan.levels,
            motive: plan.motive,
        });
        Ok(name)
    }
    fn code(&mut self, code: &Code, locals: &mut Locals, depth: usize) -> Result<IRBody, Error> {
        self.budget.step(depth)?;
        match code {
            Code::Return(id) => Ok(IRBody::Ret(locals.value(*id)?)),
            Code::Let(decl, rest) => {
                let layout = self.layout(&decl.ty, locals, depth + 1)?;
                if layout == IRType::Erased {
                    return Err(Error::Unsupported("unlowered type-value computation"));
                }
                let value = match &decl.value {
                    LetValue::Ctor { name, levels, args } => {
                        self.ctor(name, levels, args, locals, depth + 1)?
                    }
                    LetValue::Const { name, levels, args } => {
                        self.call(name, levels, args, locals, depth + 1)?
                    }
                    LetValue::FVar { fvar, args } => {
                        let mut values = Vec::new();
                        for arg in args {
                            match arg {
                                Arg::FVar(id) if locals.value(*id)? != IRArg::Erased => {
                                    values.push(locals.value(*id)?)
                                }
                                _ => {
                                    return Err(Error::Unsupported(
                                        "dependent dynamic closure argument",
                                    ))
                                }
                            }
                        }
                        IRExpr::ClosureApply {
                            closure: locals.value(*fvar)?,
                            args: values,
                        }
                    }
                    _ => return Err(Error::Unsupported("runtime IR let value")),
                };
                let IRArg::Var(var) = locals.fresh(decl.fvar_id, decl.ty.clone(), &layout)? else {
                    unreachable!()
                };
                let rest = self.code(rest, locals, depth + 1)?;
                Ok(IRBody::VDecl {
                    var,
                    ty: layout,
                    value,
                    rest: Box::new(rest),
                })
            }
            Code::Fun(fun, rest) => {
                let bound: HashSet<_> = fun.params.iter().map(|p| p.fvar_id).collect();
                let captures = crate::opt::lambda_lift::free_vars_in_code(&fun.body, &bound)
                    .into_iter()
                    .collect::<BTreeSet<_>>();
                let mut params = Vec::new();
                let mut captured = Vec::new();
                for id in captures {
                    let ty = locals
                        .types
                        .get(&id)
                        .cloned()
                        .ok_or(Error::UnboundVariable)?;
                    if locals.value(id)? == IRArg::Erased {
                        return Err(Error::Unsupported("dependent erased closure capture"));
                    }
                    params.push(Param::new(id, Name::anon(), ty));
                    captured.push(locals.value(id)?);
                }
                params.extend(fun.params.clone());
                let name = loop {
                    self.budget.step(depth)?;
                    let candidate = self.owner.clone().str("__runtime_lift").num(self.next_name);
                    self.next_name = self
                        .next_name
                        .checked_add(1)
                        .ok_or(Error::Resource("lifted name"))?;
                    if self.names.insert(candidate.clone()) {
                        break candidate;
                    }
                };
                let mut inner = Locals::default();
                let ir_params = self.parameters(&params, &mut inner, depth + 1)?;
                let return_type = self.layout(&fun.ty, &inner, depth + 1)?;
                let body = self.code(&fun.body, &mut inner, depth + 1)?;
                let arity =
                    u16::try_from(ir_params.len()).map_err(|_| Error::Resource("closure arity"))?;
                if captured.len() >= arity as usize {
                    return Err(Error::Unsupported("empty runtime closure telescope"));
                }
                self.generated.push(IRDecl {
                    name: name.clone(),
                    params: ir_params,
                    return_type,
                    body,
                });
                let mut ty = fun.ty.clone();
                for param in fun.params.iter().rev() {
                    ty = Expr::pi(
                        clean_kernel::BinderInfo::Default,
                        param.ty.clone(),
                        ty.abstract_fvar(param.fvar_id),
                    );
                }
                let IRArg::Var(var) = locals.fresh(fun.fvar_id, ty, &IRType::Object)? else {
                    unreachable!()
                };
                let rest = self.code(rest, locals, depth + 1)?;
                Ok(IRBody::VDecl {
                    var,
                    ty: IRType::Object,
                    value: IRExpr::PartialApply {
                        fn_id: FnId(name),
                        arity,
                        args: captured,
                    },
                    rest: Box::new(rest),
                })
            }
            _ => Err(Error::Unsupported("runtime IR control flow")),
        }
    }
}
