// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust Code Emitter
//!
//! Generates Rust source code from lowered L5IR. Consumes `LoweredDecl`
//! produced by the join point lowering pass, which replaces JDecl/Jmp
//! with labeled blocks and loops compatible with Rust's control flow.
//!
//! # Calling Convention (Rust backend)
//!
//! The Rust backend uses **slice references** (`&[T]`) for variable-length
//! argument lists. This diverges from the C backend (see `emit_c.rs`) which
//! uses positional arguments with explicit counts.
//!
//! ## Divergent operations vs C backend
//!
//! **PartialApply (closure allocation):**
//! - Rust: `clean_alloc_closure(fn as *const (), arity, &[arg1, arg2, ...])`
//! - C: `clean_alloc_closure((void*)fn, arity, num_fixed, arg1, arg2, ...)`
//! - Rationale: Rust `&[T]` carries `.len()`, making an explicit `num_fixed`
//!   parameter redundant. The C backend passes it because C varargs have no
//!   intrinsic length.
//!
//! **ClosureApply (closure invocation):**
//! - Rust: `clean_closure_apply(closure, &[arg1, arg2, ...])`
//! - C: `clean_apply_N(closure, a1, ..., aN)` for N in 0..=16,
//!   `clean_apply_n(closure, n, (clean_obj*[]){...})` for N > 16
//! - Rationale: Rust uses a single generic function since `&[T]` is
//!   stack-allocated and zero-cost. The C backend uses arity-specialized
//!   entry points (`clean_apply_0` through `clean_apply_16`) to avoid heap
//!   allocation, matching Lean 4's C runtime pattern.
//!
//! **Reuse (memory reuse after reset):**
//! - Rust: `clean_reuse(slot, tag, scalar_sz, &[arg1, arg2, ...])`
//! - C: `clean_reuse(slot, tag, num_objs, scalar_sz, arg1, arg2, ...)`
//! - Rationale: Same as PartialApply -- slice length replaces the explicit
//!   `num_objs` parameter. Note: in the C backend, `num_objs` is sourced from
//!   `CtorInfo::num_objects`, not `args.len()`.
//!
//! These divergences are **intentional** (language ABI constraints), not bugs.
//! Both backends emit semantically equivalent operations for the same IR input.
//! That includes the C2 carrier projections (`Proj`/`SProj`/`UProj` out of an
//! unboxed scalar carrier: identity at the same lowered width, re-box for a
//! pointer-class result) and the saturated-call + `clean_closure_apply`
//! over-application discipline — both mirrored from `emit_c`/`emit_trust_ir`.
//!
//! Part of #1889 - Rust backend emission.

mod body;
#[cfg(test)]
mod default_config_tests;
#[cfg(test)]
mod tests;

use crate::emit_base::EmitterBase;
use crate::ir::{CtorInfo, FnId, IRArg, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId};
use crate::ir_checker::{check_decls, IRError};
use crate::join_point_lower::{lower_decls, LoweredDecl};
use crate::mangle::mangle_name;
use clean_kernel::Name;
use std::collections::HashMap;

/// Map scalar IRType to the `clean_ctor_get_*` getter function name.
///
/// Only valid for SProj scalar types. Returns an error on invalid types.
pub(crate) fn scalar_getter_name(ty: &IRType) -> Result<&'static str, IRError> {
    match ty {
        IRType::Bool | IRType::UInt8 => Ok("clean_ctor_get_uint8"),
        IRType::UInt16 => Ok("clean_ctor_get_uint16"),
        IRType::UInt32 => Ok("clean_ctor_get_uint32"),
        IRType::UInt64 => Ok("clean_ctor_get_uint64"),
        IRType::Float32 => Ok("clean_ctor_get_float32"),
        IRType::Float64 => Ok("clean_ctor_get_float"),
        _ => Err(IRError::InvalidScalarType {
            ty: ty.clone(),
            op: "SProj",
        }),
    }
}

/// Map scalar IRType to the `clean_ctor_set_*` setter function name.
///
/// Only valid for SSet scalar types. Returns an error on invalid types.
pub(crate) fn scalar_setter_name(ty: &IRType) -> Result<&'static str, IRError> {
    match ty {
        IRType::Bool | IRType::UInt8 => Ok("clean_ctor_set_uint8"),
        IRType::UInt16 => Ok("clean_ctor_set_uint16"),
        IRType::UInt32 => Ok("clean_ctor_set_uint32"),
        IRType::UInt64 => Ok("clean_ctor_set_uint64"),
        IRType::Float32 => Ok("clean_ctor_set_float32"),
        IRType::Float64 => Ok("clean_ctor_set_float"),
        _ => Err(IRError::InvalidScalarType {
            ty: ty.clone(),
            op: "SSet",
        }),
    }
}

/// Format a Rust byte offset expression for scalar field access.
pub(crate) fn rust_byte_offset(n: u32, offset: u32) -> String {
    format!("core::mem::size_of::<*const ()>() * {} + {}", n, offset)
}

/// Configuration for Rust code generation.
#[derive(Debug, Clone)]
pub struct RustEmitConfig {
    /// Indent string (spaces or tabs).
    pub indent: String,
    /// Validate IR before emitting (default: enabled).
    pub check_ir: bool,
}

impl Default for RustEmitConfig {
    fn default() -> Self {
        Self {
            indent: "    ".to_string(),
            check_ir: true,
        }
    }
}

/// Rust code emitter state.
pub struct RustEmitter {
    /// Shared output buffering and indentation.
    pub(crate) base: EmitterBase,
    /// Configuration (reserved for future use beyond check_ir).
    #[allow(dead_code)]
    config: RustEmitConfig,
    /// In-slice declaration shapes (parameter count + return type), populated
    /// by `emit_decls`. Drives the saturated-call + `clean_closure_apply`
    /// over-application discipline in the `Apply` arm (parity with `emit_c` /
    /// `emit_trust_ir`). Unknown callees keep the historical direct call.
    decl_shapes: HashMap<Name, (usize, IRType)>,
    /// Known IR type of each in-scope variable (function params, `VDecl`
    /// bindings, join-point params). Used by the C2 carrier-projection arms
    /// of `emit_expr` (parity with `emit_c`).
    pub(crate) var_types: HashMap<VarId, IRType>,
}

impl RustEmitter {
    pub fn new() -> Self {
        Self::with_config(RustEmitConfig::default())
    }

    pub fn with_config(config: RustEmitConfig) -> Self {
        let base = EmitterBase::new(config.indent.clone());
        Self {
            base,
            config,
            decl_shapes: HashMap::new(),
            var_types: HashMap::new(),
        }
    }

    /// Record the IR type of an in-scope variable for the C2
    /// carrier-projection arms.
    pub(crate) fn record_var_type(&mut self, var: VarId, ty: &IRType) {
        self.var_types.insert(var, ty.clone());
    }

    /// The Rust spelling of a same-lowered-width carrier identity: exact
    /// same type is the variable itself; the `UInt64`/`USize` class needs an
    /// `as` cast (`u64` vs `usize` are distinct Rust types, unlike C's
    /// implicitly-converting `uint64_t`/`size_t`), which is lossless on the
    /// 64-bit targets the runtime supports.
    fn carrier_identity(&self, var: VarId, carrier: &IRType, result: &IRType) -> String {
        if carrier == result {
            self.emit_var(var)
        } else {
            format!("({} as {})", self.emit_var(var), self.emit_type(result))
        }
    }

    /// Re-box an unboxed scalar carrier into a managed object (the Rust
    /// mirror of `emit_c::emit_box_scalar_carrier` / `emit_trust_ir::
    /// box_scalar_tagged`): floats heap-box via `clean_box_float`;
    /// integer/Bool carriers become the tagged immediate via `clean_box`.
    fn emit_box_scalar_carrier(&self, carrier: &IRType, var: VarId) -> String {
        match carrier {
            IRType::Float64 | IRType::Float32 => {
                format!("clean_box_float({} as f64)", self.emit_var(var))
            }
            _ => format!("clean_box({} as usize)", self.emit_var(var)),
        }
    }

    /// The ordinary boxed-object field getter for a `Proj` (the non-carrier
    /// path of the `Proj` arm).
    fn emit_proj_getter(&self, idx: u32, ty: &IRType, arg: &IRArg) -> String {
        match ty {
            IRType::UInt8 => format!("clean_ctor_get_uint8({}, {})", self.emit_arg(arg), idx),
            IRType::UInt16 => format!("clean_ctor_get_uint16({}, {})", self.emit_arg(arg), idx),
            IRType::UInt32 => format!("clean_ctor_get_uint32({}, {})", self.emit_arg(arg), idx),
            IRType::UInt64 => format!("clean_ctor_get_uint64({}, {})", self.emit_arg(arg), idx),
            IRType::USize => format!("clean_ctor_get_usize({}, {})", self.emit_arg(arg), idx),
            IRType::Float64 => format!("clean_ctor_get_float({}, {})", self.emit_arg(arg), idx),
            IRType::Float32 => {
                format!("clean_ctor_get_float32({}, {})", self.emit_arg(arg), idx)
            }
            _ => format!("clean_ctor_get({}, {})", self.emit_arg(arg), idx),
        }
    }

    pub fn finish(self) -> String {
        self.base.finish()
    }

    pub(crate) fn writeln(&mut self, s: &str) {
        self.base.writeln(s);
    }

    pub(crate) fn indent(&mut self) {
        self.base.indent();
    }

    pub(crate) fn dedent(&mut self) {
        self.base.dedent();
    }

    pub fn emit_header(&mut self) {
        self.writeln("// Generated by clean compiler");
        self.writeln("// Do not edit manually");
        self.writeln("");
        self.writeln("#![allow(unused_variables, unused_assignments, unreachable_code)]");
        self.writeln("");
        self.writeln("use clean_runtime::*;");
        self.writeln("");
    }

    pub(crate) fn emit_type(&self, ty: &IRType) -> String {
        match ty {
            IRType::Bool | IRType::UInt8 => "u8".to_string(),
            IRType::UInt16 => "u16".to_string(),
            IRType::UInt32 => "u32".to_string(),
            IRType::UInt64 => "u64".to_string(),
            IRType::USize => "usize".to_string(),
            IRType::Float32 => "f32".to_string(),
            IRType::Float64 => "f64".to_string(),
            IRType::Object
            | IRType::TObject
            | IRType::Struct(_)
            | IRType::Union(_)
            | IRType::Erased => "*mut CleanObj".to_string(),
            IRType::Void => "()".to_string(),
        }
    }

    pub(crate) fn emit_default(&self, ty: &IRType) -> String {
        match ty {
            IRType::Bool | IRType::UInt8 => "0u8".to_string(),
            IRType::UInt16 => "0u16".to_string(),
            IRType::UInt32 => "0u32".to_string(),
            IRType::UInt64 => "0u64".to_string(),
            IRType::USize => "0usize".to_string(),
            IRType::Float32 => "0.0f32".to_string(),
            IRType::Float64 => "0.0f64".to_string(),
            IRType::Object
            | IRType::TObject
            | IRType::Struct(_)
            | IRType::Union(_)
            | IRType::Erased => "std::ptr::null_mut()".to_string(),
            IRType::Void => "()".to_string(),
        }
    }

    pub(crate) fn emit_var(&self, var: VarId) -> String {
        self.base.emit_var(var)
    }

    pub(crate) fn emit_jp_label(&self, jp: JoinPointId) -> String {
        format!("'_jp{}", jp.0)
    }

    pub(crate) fn emit_jp_init_label(&self, jp: JoinPointId) -> String {
        format!("'_jp{}_init", jp.0)
    }

    fn emit_fn_id(&self, fn_id: &FnId) -> String {
        self.base.emit_fn_id(fn_id)
    }

    pub(crate) fn emit_arg(&self, arg: &IRArg) -> String {
        self.base.emit_arg(arg)
    }

    pub(crate) fn emit_args_joined(&self, args: &[IRArg]) -> String {
        self.base.emit_args_joined(args)
    }

    fn emit_literal(&self, lit: &IRLiteral) -> String {
        match lit {
            IRLiteral::Bool(b) => if *b { "1u8" } else { "0u8" }.to_string(),
            IRLiteral::UInt8(n) => format!("{}u8", n),
            IRLiteral::UInt16(n) => format!("{}u16", n),
            IRLiteral::UInt32(n) => format!("{}u32", n),
            IRLiteral::UInt64(n) => format!("{}u64", n),
            IRLiteral::USize(n) => format!("{}usize", n),
            // Big Nat literal (>= 2^64): heap Nat from two u64 limbs (RUNG B).
            IRLiteral::NatBig(v) => {
                format!("clean_nat_big({}u64, {}u64)", *v as u64, (*v >> 64) as u64)
            }
            IRLiteral::Float32(f) if f.is_nan() => "f32::NAN".to_string(),
            IRLiteral::Float32(f) if f.is_infinite() => if f.is_sign_positive() {
                "f32::INFINITY"
            } else {
                "f32::NEG_INFINITY"
            }
            .to_string(),
            IRLiteral::Float32(f) => format!("{}f32", f),
            IRLiteral::Float64(f) if f.is_nan() => "f64::NAN".to_string(),
            IRLiteral::Float64(f) if f.is_infinite() => if f.is_sign_positive() {
                "f64::INFINITY"
            } else {
                "f64::NEG_INFINITY"
            }
            .to_string(),
            IRLiteral::Float64(f) => format!("{}f64", f),
        }
    }

    /// Emit a constructor expression. Part of #1974, #2005.
    fn emit_ctor(&self, info: &CtorInfo, args: &[IRArg]) -> String {
        if args.is_empty() && info.scalar_size() == 0 {
            format!("clean_box({})", info.tag)
        } else if args.is_empty() {
            format!(
                "clean_alloc_ctor({}, 0, {}, &[])",
                info.tag,
                info.scalar_size()
            )
        } else {
            format!(
                "clean_alloc_ctor({}, {}, {}, &[{}])",
                info.tag,
                info.num_objects,
                info.scalar_size(),
                self.emit_args_joined(args)
            )
        }
    }

    /// Emit an IR expression as a Rust expression string.
    pub(crate) fn emit_expr(&self, expr: &IRExpr) -> Result<String, IRError> {
        Ok(match expr {
            IRExpr::Ctor { info, args } => self.emit_ctor(info, args),
            IRExpr::Proj { idx, ty, arg } => {
                // C2 carrier projection (parity with `emit_c`): identity at
                // the same lowered width, re-box for a pointer-class result,
                // refusal otherwise.
                if let IRArg::Var(v) = arg {
                    if let Some(carrier) = self.var_types.get(v).filter(|t| t.is_scalar()) {
                        if carrier.same_lowered_scalar(ty) {
                            return Ok(self.carrier_identity(*v, carrier, ty));
                        }
                        if ty.lowers_to_ptr() {
                            return Ok(self.emit_box_scalar_carrier(carrier, *v));
                        }
                        return Err(IRError::TypeMismatch {
                            expected: "same-width scalar or object result",
                            actual: carrier.clone(),
                            context: "projection out of scalar carrier",
                        });
                    }
                }
                self.emit_proj_getter(*idx, ty, arg)
            }
            IRExpr::Tag(arg) => format!("clean_obj_tag({}) as u32", self.emit_arg(arg)),
            IRExpr::Box { ty, arg } => match ty {
                IRType::UInt64 => format!("clean_box_uint64({})", self.emit_arg(arg)),
                IRType::UInt32 => format!("clean_box_uint32({})", self.emit_arg(arg)),
                IRType::Float64 => format!("clean_box_float({})", self.emit_arg(arg)),
                IRType::Float32 => format!("clean_box_float({} as f64)", self.emit_arg(arg)),
                _ => format!("clean_box({} as usize)", self.emit_arg(arg)),
            },
            IRExpr::Unbox { ty, arg } => match ty {
                IRType::Float64 => format!("clean_unbox_float({})", self.emit_arg(arg)),
                IRType::Float32 => format!("clean_unbox_float({}) as f32", self.emit_arg(arg)),
                IRType::UInt64 => format!("clean_unbox_uint64({})", self.emit_arg(arg)),
                IRType::UInt32 => format!("clean_unbox_uint32({})", self.emit_arg(arg)),
                _ => format!("clean_unbox({})", self.emit_arg(arg)),
            },
            IRExpr::Lit(lit) => self.emit_literal(lit),
            IRExpr::Apply { fn_id, args } => {
                // Saturated-call + `clean_closure_apply` over-application
                // discipline (parity with `emit_c::emit_apply` /
                // `emit_trust_ir::emit_apply_user`): the extras are applied
                // to the saturated call's result closure. Under-application
                // and over-application of a scalar-returning callee are
                // refused (the ir_checker refuses them too; this keeps
                // `check_ir: false` callers honest). Unknown callees keep
                // the historical direct call.
                if let Some((n_params, return_type)) = self.decl_shapes.get(&fn_id.0) {
                    if args.len() < *n_params
                        || (args.len() > *n_params && !return_type.lowers_to_ptr())
                    {
                        return Err(IRError::ArityMismatch {
                            function: fn_id.0.clone(),
                            expected: *n_params,
                            actual: args.len(),
                        });
                    }
                    let (direct, extra) = args.split_at(*n_params);
                    let saturated = format!(
                        "{}({})",
                        self.emit_fn_id(fn_id),
                        self.emit_args_joined(direct)
                    );
                    if extra.is_empty() {
                        return Ok(saturated);
                    }
                    return Ok(format!(
                        "clean_closure_apply({}, &[{}])",
                        saturated,
                        self.emit_args_joined(extra)
                    ));
                }
                format!(
                    "{}({})",
                    self.emit_fn_id(fn_id),
                    self.emit_args_joined(args)
                )
            }
            IRExpr::PartialApply { fn_id, arity, args } => format!(
                "clean_alloc_closure({} as *const (), {}, &[{}])",
                self.emit_fn_id(fn_id),
                arity,
                self.emit_args_joined(args)
            ),
            IRExpr::ClosureApply { closure, args } => format!(
                "clean_closure_apply({}, &[{}])",
                self.emit_arg(closure),
                self.emit_args_joined(args)
            ),
            IRExpr::UProj { idx, var } => {
                // C2 carrier projection: `UProj` produces `usize`, so out of
                // an unboxed scalar carrier only the `u64`/`usize` class is
                // the faithful identity (parity with `emit_c`).
                if let Some(carrier) = self.var_types.get(var).filter(|t| t.is_scalar()) {
                    if carrier.same_lowered_scalar(&IRType::USize) {
                        return Ok(self.carrier_identity(*var, carrier, &IRType::USize));
                    }
                    return Err(IRError::TypeMismatch {
                        expected: "object or UInt64/USize carrier",
                        actual: carrier.clone(),
                        context: "uproj source",
                    });
                }
                format!("clean_ctor_get_usize({}, {})", self.emit_var(*var), idx)
            }
            IRExpr::SProj { n, offset, var, ty } => {
                // C2 carrier projection: same-lowered-width identity out of
                // an unboxed scalar carrier (parity with `emit_c`).
                if let Some(carrier) = self.var_types.get(var).filter(|t| t.is_scalar()) {
                    if carrier.same_lowered_scalar(ty) {
                        return Ok(self.carrier_identity(*var, carrier, ty));
                    }
                    return Err(IRError::TypeMismatch {
                        expected: "object or same-width scalar carrier",
                        actual: carrier.clone(),
                        context: "sproj source",
                    });
                }
                format!(
                    "{}({}, {})",
                    scalar_getter_name(ty)?,
                    self.emit_var(*var),
                    rust_byte_offset(*n, *offset)
                )
            }
            IRExpr::IsShared(var) => {
                format!("(!clean_is_exclusive({})) as u8", self.emit_var(*var))
            }
            IRExpr::String(s) => format!("clean_mk_string({:?})", s),
            IRExpr::Reset(var) => format!("clean_reset({})", self.emit_var(*var)),
            IRExpr::Reuse { var, ctor, args } => format!(
                "clean_reuse({}, {}, {}, &[{}])",
                self.emit_var(*var),
                ctor.tag,
                ctor.scalar_size(),
                self.emit_args_joined(args)
            ),
        })
    }

    /// Emit a complete function declaration.
    pub fn emit_decl(&mut self, decl: &LoweredDecl) -> Result<(), IRError> {
        let fn_name = mangle_name(&decl.name);
        let return_ty = self.emit_type(&decl.return_type);
        // Record parameter types for the C2 carrier-projection arms.
        for (var, ty) in &decl.params {
            self.record_var_type(*var, ty);
        }
        let params: Vec<String> = decl
            .params
            .iter()
            .map(|(var, ty)| format!("{}: {}", self.emit_var(*var), self.emit_type(ty)))
            .collect();
        self.writeln(&format!(
            "pub unsafe fn {}({}) -> {} {{",
            fn_name,
            params.join(", "),
            return_ty
        ));
        self.indent();
        self.emit_body(&decl.body)?;
        self.dedent();
        self.writeln("}");
        self.writeln("");
        Ok(())
    }

    pub fn emit_decls(&mut self, decls: &[LoweredDecl]) -> Result<(), IRError> {
        // Record in-slice callee shapes for the `Apply` over-application
        // discipline (see the `IRExpr::Apply` arm of `emit_expr`).
        for decl in decls {
            self.decl_shapes.insert(
                decl.name.clone(),
                (decl.params.len(), decl.return_type.clone()),
            );
        }
        for decl in decls {
            self.emit_decl(decl)?;
        }
        Ok(())
    }
}

impl Default for RustEmitter {
    fn default() -> Self {
        Self::new()
    }
}

/// Emit Rust code for a list of IR declarations.
pub fn emit_rust(decls: &[IRDecl]) -> Result<String, IRError> {
    emit_rust_with_config(decls, RustEmitConfig::default())
}

/// Emit Rust code with custom configuration.
pub fn emit_rust_with_config(decls: &[IRDecl], config: RustEmitConfig) -> Result<String, IRError> {
    if config.check_ir {
        check_decls(decls)?;
    }
    let lowered = lower_decls(decls);
    let mut emitter = RustEmitter::with_config(config);
    emitter.emit_header();
    emitter.emit_decls(&lowered)?;
    Ok(emitter.finish())
}
