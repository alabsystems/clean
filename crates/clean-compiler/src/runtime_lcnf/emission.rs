// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded all-owned immutable Object IR emission. This deliberately retains
//! each local until return: no borrow inference, reset/reuse or RC optimization.
//! It may retain more memory than Lean. It is not a refinement/admission API.

use super::typing::Budget;
use super::{RuntimeIrOutput, RuntimeIrStatus, RuntimeLimits, RuntimeLowerError, RuntimeRowOrigin};
use crate::emit_trust_ir::{
    emit_trust_ir_with_runtime_imports, names::wire_name, RuntimeLowering, TrustIrConfig,
};
use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeCallKind {
    Direct,
    ClosureValue,
}
#[derive(Clone, Debug)]
pub struct RuntimeCallEdge {
    pub caller: Name,
    pub callee: Name,
    pub kind: RuntimeCallKind,
    pub supplied: usize,
}
#[derive(Clone, Debug)]
pub struct RuntimeImport {
    pub function_index: usize,
    pub function_id: trust_ir::value::FuncId,
    pub symbol: String,
    pub calling_convention: trust_ir::CallingConv,
    pub linkage: trust_ir::Linkage,
    pub parameters: Vec<trust_ir::ty::Ty>,
    pub returns: Vec<trust_ir::ty::Ty>,
    pub variadic: bool,
}
#[derive(Debug, thiserror::Error)]
pub enum RuntimeEmissionError {
    #[error(transparent)]
    Lowering(#[from] RuntimeLowerError),
    #[error("runtime emission refuses {0}")]
    Unsupported(&'static str),
    #[error("required emitted declaration is absent: {0:?}")]
    Missing(Name),
    #[error("duplicate emitted declaration identity: {0:?}")]
    Duplicate(Name),
    #[error("runtime IR validation: {0}")]
    Invalid(String),
    #[error("Trust-IR emission: {0}")]
    Backend(String),
}
type Error = RuntimeEmissionError;

#[derive(Debug)]
pub struct RuntimeEmissionOutput {
    /// Unchanged complete captured dependency outcomes, including refused rows.
    pub captured: RuntimeIrOutput,
    pub emission: Result<RuntimeEmission, Error>,
}
#[derive(Debug)]
pub struct RuntimeEmission {
    pub mode: RuntimeLowering,
    /// Selected exact named Call/PAP closure; never substitutes an extern body.
    pub before_rc: Vec<IRDecl>,
    pub owned_ir: Vec<IRDecl>,
    pub origins: Vec<(Name, RuntimeRowOrigin)>,
    /// Occurrences, not a deduplicated set of edges.
    pub named_edges: Vec<RuntimeCallEdge>,
    /// Dynamic applications stay visible; these are not statically resolved
    /// function identities or a claim about arbitrary closure-valued inputs.
    pub dynamic_applications: usize,
    pub module: trust_ir::Module,
    /// Exact fixed C runtime declarations, separate from every captured callee.
    /// Empty in Dialect mode. Includes unused ABI declarations honestly.
    pub runtime_imports: Vec<RuntimeImport>,
}

pub(super) fn emit(
    output: &RuntimeIrOutput,
    limits: RuntimeLimits,
    mode: RuntimeLowering,
) -> Result<RuntimeEmission, Error> {
    let mut candidates = BTreeMap::new();
    for row in &output.rows {
        if let RuntimeIrStatus::Lowered(decls) = &row.status {
            for decl in decls {
                if candidates
                    .insert(decl.name.clone(), (decl, &row.origin))
                    .is_some()
                {
                    return Err(Error::Duplicate(decl.name.clone()));
                }
            }
        }
    }
    let mut queue = VecDeque::from([output.root.clone()]);
    let mut seen = BTreeSet::new();
    let mut before_rc = Vec::new();
    let mut origins = Vec::new();
    let mut named_edges = Vec::new();
    let mut dynamic_applications = 0;
    let mut budget = Budget::new(limits);
    while let Some(name) = queue.pop_front() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if seen.len() > limits.declarations {
            return Err(RuntimeLowerError::Resource("emitted declarations").into());
        }
        let (decl, origin) = candidates
            .get(&name)
            .ok_or_else(|| Error::Missing(name.clone()))?;
        let start = named_edges.len();
        edges(
            &decl.body,
            &name,
            &mut named_edges,
            &mut dynamic_applications,
            &mut budget,
            0,
        )?;
        queue.extend(named_edges[start..].iter().map(|edge| edge.callee.clone()));
        before_rc.push((*decl).clone());
        origins.push((name, (*origin).clone()));
    }
    crate::ir_checker::check_decls(&before_rc).map_err(|e| Error::Invalid(e.to_string()))?;
    let owned_ir = before_rc
        .iter()
        .map(|d| own(d, &mut budget))
        .collect::<Result<Vec<_>, _>>()?;
    crate::ir_checker::check_decls(&owned_ir).map_err(|e| Error::Invalid(e.to_string()))?;
    let config = TrustIrConfig {
        module_name: "captured_runtime_diagnostic".into(),
        runtime_lowering: mode,
        use_clean_dialect: mode == RuntimeLowering::Dialect,
        certify_translation: false,
        ..TrustIrConfig::default()
    };
    let (emitted, requested) = emit_trust_ir_with_runtime_imports(&owned_ir, &config, &[])
        .map_err(|e| Error::Backend(e.to_string()))?;
    let module = emitted.module;
    let runtime_imports = postflight(&module, &owned_ir, mode, &requested)?;
    Ok(RuntimeEmission {
        mode,
        before_rc,
        owned_ir,
        origins,
        named_edges,
        dynamic_applications,
        module,
        runtime_imports,
    })
}

fn postflight(
    module: &trust_ir::Module,
    owned_ir: &[IRDecl],
    mode: RuntimeLowering,
    requested: &[crate::emit_trust_ir_runtime::RuntimeImport],
) -> Result<Vec<RuntimeImport>, Error> {
    // Reconstruct the existing ABI declaration roster, not a string-prefix
    // allowlist. Any dropped-callee fallback, primitive removal/wrapper or
    // symbol collision changes this exact population and is refused.
    let mut abi_builder = trust_ir_build::ModuleBuilder::new("runtime_abi_observation");
    if mode == RuntimeLowering::ExternCalls {
        crate::emit_trust_ir_runtime::RuntimeAbi::declare_arc(&mut abi_builder);
    } else if !requested.is_empty() {
        return Err(Error::Unsupported(
            "dialect emission requested runtime imports",
        ));
    }
    let first_user = abi_builder
        .peek_next_func_id()
        .map_err(|e| Error::Backend(e.to_string()))?
        .index() as usize;
    // Reconstruct every expected slot from the original source declarations
    // and the ordered roles actually requested by this invocation. No names or
    // signatures from the module under inspection construct this population.
    let code_pointer = abi_builder.add_func_type(vec![], vec![]);
    for decl in owned_ir {
        let ty = abi_builder.add_func_type(
            vec![trust_ir::Ty::Ptr; decl.params.len()],
            vec![trust_ir::Ty::Ptr],
        );
        abi_builder.declare_function(wire_name(&decl.name), ty);
    }
    for role in requested {
        role.declare(&mut abi_builder, code_pointer);
    }
    let users = first_user..first_user + owned_ir.len();
    let abi = abi_builder.build().map_err(|fault| {
        Error::Backend(format!("the runtime ABI roster did not build: {fault}"))
    })?;
    if module.functions.len() != abi.functions.len() {
        return Err(Error::Unsupported("emitter changed declaration population"));
    }
    let mut runtime_imports = Vec::new();
    let mut labels = BTreeSet::new();
    for (index, expected) in abi.functions.iter().enumerate() {
        if users.contains(&index) {
            continue;
        }
        let actual = &module.functions[index];
        if actual.name != expected.name
            || actual.id != expected.id
            || actual.calling_conv != expected.calling_conv
            || actual.linkage != expected.linkage
            || !actual.blocks.is_empty()
            || module.func_type(actual.ty) != abi.func_type(expected.ty)
        {
            return Err(Error::Unsupported("runtime ABI observation disagrees"));
        }
        if !labels.insert(actual.name.clone()) {
            return Err(Error::Unsupported("duplicate runtime ABI symbol"));
        }
        let ty = module
            .func_type(actual.ty)
            .ok_or(Error::Unsupported("runtime signature missing"))?;
        runtime_imports.push(RuntimeImport {
            function_index: index,
            function_id: actual.id,
            symbol: actual.name.clone(),
            calling_convention: actual.calling_conv,
            linkage: actual.linkage,
            parameters: ty.params.clone(),
            returns: ty.returns.clone(),
            variadic: ty.is_vararg,
        });
    }
    for (index, decl) in owned_ir.iter().enumerate() {
        let actual = &module.functions[first_user + index];
        let label = wire_name(&decl.name);
        let expected_ty = trust_ir::ty::FuncTy {
            params: vec![trust_ir::ty::Ty::Ptr; decl.params.len()],
            returns: vec![trust_ir::ty::Ty::Ptr],
            is_vararg: false,
            abi: None,
        };
        if actual.name != label
            || actual.blocks.is_empty()
            || !labels.insert(label)
            || actual.id.0 as usize != first_user + index
            || actual.calling_conv != trust_ir::CallingConv::C
            || actual.linkage != trust_ir::Linkage::External
            || module.func_type(actual.ty) != Some(&expected_ty)
            || actual.producer != Some(trust_ir::Producer::Clean)
        {
            return Err(Error::Unsupported("emitted source identity/body disagrees"));
        }
    }
    Ok(runtime_imports)
}

fn edges(
    body: &IRBody,
    caller: &Name,
    out: &mut Vec<RuntimeCallEdge>,
    dynamic: &mut usize,
    budget: &mut Budget,
    depth: usize,
) -> Result<(), Error> {
    budget.step(depth)?;
    match body {
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Apply { fn_id, args } | IRExpr::PartialApply { fn_id, args, .. } => {
                    out.push(RuntimeCallEdge {
                        caller: caller.clone(),
                        callee: fn_id.0.clone(),
                        kind: if matches!(value, IRExpr::Apply { .. }) {
                            RuntimeCallKind::Direct
                        } else {
                            RuntimeCallKind::ClosureValue
                        },
                        supplied: args.len(),
                    });
                }
                IRExpr::ClosureApply { .. } => {
                    *dynamic = dynamic
                        .checked_add(1)
                        .ok_or(Error::Unsupported("dynamic site overflow"))?
                }
                _ => {}
            }
            edges(rest, caller, out, dynamic, budget, depth + 1)
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                edges(&alt.body, caller, out, dynamic, budget, depth + 1)?;
            }
            if let Some(body) = default {
                edges(body, caller, out, dynamic, budget, depth + 1)?;
            }
            Ok(())
        }
        IRBody::Ret(_) => Ok(()),
        _ => Err(Error::Unsupported("pre-RC control/effect shape")),
    }
}

fn own(decl: &IRDecl, budget: &mut Budget) -> Result<IRDecl, Error> {
    if decl.return_type != IRType::Object || decl.params.iter().any(|(_, t)| *t != IRType::Object) {
        return Err(Error::Unsupported("non-Object ownership ABI"));
    }
    let locals = decl.params.iter().map(|(v, _)| *v).collect::<Vec<_>>();
    let body = own_body(&decl.body, &locals, budget, 0)?;
    Ok(IRDecl {
        body,
        ..decl.clone()
    })
}
fn variable(arg: &IRArg, locals: &[VarId]) -> Result<VarId, Error> {
    match arg {
        IRArg::Var(v) if locals.contains(v) => Ok(*v),
        _ => Err(Error::Unsupported("non-owned/erased argument")),
    }
}
fn own_body(
    body: &IRBody,
    locals: &[VarId],
    budget: &mut Budget,
    depth: usize,
) -> Result<IRBody, Error> {
    budget.step(depth)?;
    match body {
        IRBody::Ret(arg) => {
            let returned = variable(arg, locals)?;
            let mut result = body.clone();
            for v in locals.iter().rev().filter(|v| **v != returned) {
                budget.step(depth)?;
                result = IRBody::Dec {
                    var: *v,
                    rest: Box::new(result),
                };
            }
            Ok(result)
        }
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if *ty != IRType::Object || locals.contains(var) {
                return Err(Error::Unsupported("local ownership layout/identity"));
            }
            let mut consumed = Vec::new();
            let borrowed = match value {
                IRExpr::Ctor { info, args } => {
                    if info.num_scalars != 0
                        || info.field_types.iter().any(|t| *t != IRType::Object)
                    {
                        return Err(Error::Unsupported("constructor ownership layout"));
                    }
                    for arg in args {
                        consumed.push(variable(arg, locals)?);
                    }
                    false
                }
                IRExpr::Apply { args, .. } | IRExpr::PartialApply { args, .. } => {
                    for arg in args {
                        consumed.push(variable(arg, locals)?);
                    }
                    false
                }
                IRExpr::ClosureApply { closure, args } => {
                    consumed.push(variable(closure, locals)?);
                    for arg in args {
                        consumed.push(variable(arg, locals)?);
                    }
                    false
                }
                IRExpr::Proj { arg, ty, .. } if *ty == IRType::Object => {
                    variable(arg, locals)?;
                    true
                }
                _ => return Err(Error::Unsupported("expression ownership semantics")),
            };
            let mut extended = locals.to_vec();
            extended.push(*var);
            let mut tail = own_body(rest, &extended, budget, depth + 1)?;
            // Projection reads borrow from a still-owned parent. Its local gets
            // a distinct owned reference BEFORE any continuation consumes it.
            if borrowed {
                budget.step(depth)?;
                tail = IRBody::Inc {
                    var: *var,
                    n: 1,
                    rest: Box::new(tail),
                };
            }
            let mut result = IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: value.clone(),
                rest: Box::new(tail),
            };
            // Each occurrence is owned, including repeated/aliased operands.
            // Inc BEFORE a consuming call (never after potential destruction).
            for v in consumed.into_iter().rev() {
                budget.step(depth)?;
                result = IRBody::Inc {
                    var: v,
                    n: 1,
                    rest: Box::new(result),
                };
            }
            Ok(result)
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            if !locals.contains(scrutinee) {
                return Err(Error::Unsupported("case borrowed scrutinee"));
            }
            let mut alts = alts.clone();
            for alt in &mut alts {
                *alt.body = own_body(&alt.body, locals, budget, depth + 1)?;
            }
            let default = default
                .as_ref()
                .map(|b| own_body(b, locals, budget, depth + 1).map(Box::new))
                .transpose()?;
            Ok(IRBody::Case {
                scrutinee: *scrutinee,
                alts,
                default,
            })
        }
        _ => Err(Error::Unsupported("pre-RC control/effect shape")),
    }
}

#[cfg(test)]
#[path = "emission_tests.rs"]
mod tests;
