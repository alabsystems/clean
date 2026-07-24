// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C Code Emitter
//!
//! Generates C source code from L5IR (clean Low-Level IR).
//! Part of Phase 4 of the compiler pipeline.
//!
//! # Architecture
//!
//! ```text
//! L5IR (with RC ops) → emit_c() → C source → GCC/Clang → executable
//! ```
//!
//! # Object Representation
//!
//! All heap objects share a common header layout:
//! - Reference count (atomic u32)
//! - Constructor tag (u8)
//! - Other fields (u8) for inline scalar data
//!
//! Based on Lean 4's runtime: lean4/src/runtime/object.h
//!
//! # Calling Convention (C backend)
//!
//! The C backend uses **positional arguments with explicit counts**, matching
//! standard C calling conventions where variadic/array arguments need an
//! explicit length parameter. This diverges from the Rust backend (see
//! `emit_rust.rs`) which uses slice references that carry their own length.
//!
//! ## Divergent operations vs Rust backend
//!
//! **PartialApply (closure allocation):**
//! - C: `clean_alloc_closure((void*)fn, arity, num_fixed, arg1, arg2, ...)`
//! - Rust: `clean_alloc_closure(fn as *const (), arity, &[arg1, arg2, ...])`
//! - Rationale: C lacks fat pointer slices. The `num_fixed` count is passed
//!   explicitly because C varargs have no intrinsic length. The Rust backend
//!   omits it since `&[T]` carries `.len()`.
//!
//! **ClosureApply (closure invocation):**
//! - C: `clean_apply_N(closure, a1, ..., aN)` for N in 0..=16,
//!   `clean_apply_n(closure, n, (clean_obj*[]){...})` for N > 16
//! - Rust: `clean_closure_apply(closure, &[arg1, arg2, ...])`
//! - Rationale: C uses arity-specialized entry points to avoid heap allocation
//!   for the common case (<=16 args). This matches Lean 4's C runtime which
//!   provides `lean_apply_1` through `lean_apply_16`. The Rust backend uses a
//!   single generic function since `&[T]` is stack-allocated and zero-cost.
//!
//! **Reuse (memory reuse after reset):**
//! - C: `clean_reuse(slot, tag, num_objs, scalar_sz, arg1, arg2, ...)`
//! - Rust: `clean_reuse(slot, tag, scalar_sz, &[arg1, arg2, ...])`
//! - Rationale: Same as PartialApply -- C needs explicit `num_objs` because
//!   positional args have no intrinsic count. The Rust slice provides this
//!   via `.len()`. Note: `num_objs` comes from `CtorInfo::num_objects`, not
//!   `args.len()`, which may differ when scalar-only fields are present.
//!
//! These divergences are **intentional** (language ABI constraints), not bugs.
//! Both backends emit semantically equivalent operations for the same IR input.
//! The C runtime API surface is larger (10+ apply functions vs 1) as a
//! consequence of C's lack of slice types.
//!
//! Part of #963 - Compiler IR infrastructure.

mod body;
mod helpers;
#[cfg(test)]
mod tests;

use std::collections::HashMap;

use crate::emit_base::EmitterBase;
use crate::ir::{FnId, IRArg, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId};
use crate::ir_checker::{check_decls, IRError};
use clean_kernel::Name;

// Re-export helpers at module level for body.rs and tests.
pub(crate) use helpers::{c_byte_offset, c_scalar_getter_name, c_scalar_setter_name};
use helpers::{emit_c_float32, emit_c_float64, emit_c_string_literal};

/// The native C comparison operator a target-pinned `USize` decision procedure
/// lowers to, or `None` if `decl` is not one of them.
///
/// SOUNDNESS FIX (2026-07-12). Genuine v4.30 `USize` is width-ABSTRACT: its
/// carrier is `BitVec System.Platform.numBits`, and `numBits` is an OPAQUE
/// irreducible (`clean-kernel` `data_types_uint.rs`
/// `register_platform_num_bits`). So `USize.decEq` / `USize.decLt` /
/// `USize.decLe` cannot resolve the width to a concrete literal at lowering and
/// fall onto the width-abstract `@instDecidableEqBitVec numBits` path — which
/// (a) re-boxes each operand with the tagged-immediate `clean_box` (`(v<<1)|1`,
/// TRUNCATING for `v >= 2^63`), and (b) destructures `USize.ofBitVec` as
/// `switch(clean_obj_tag(clean_box(v))){case 0:}` with NO default, reachable
/// only when the low byte is `0`. Empirically `USize.decEq(1,1)` returned stack
/// garbage and every comparison silently truncated at bit 63. (The concrete-
/// width `UInt64.decEq` avoids the tag switch but shares the `clean_box`
/// truncation; it is out of scope here and left unchanged — its operands are
/// `UInt64`, so the guard below never matches it.)
///
/// `USize` is target-pinned to a native `u64` on this target (the type map sends
/// `IRType::USize -> size_t`, and these primitives already lower to the
/// `size_t`-parameter signature `uint8_t l_USize_dec*(size_t, size_t)`). The
/// SOUND lowering is therefore a *direct native comparison* on the two `size_t`
/// operands — exactly the value the width-abstract path was meant to compute,
/// with no boxing, no `clean_obj_tag` switch, and no truncation across the full
/// 64-bit range. FAIL-CLOSED: fires only for the exact 2×`USize` → `Bool`
/// primitive shape; any other decl keeps its generic body.
fn usize_native_decision_op(decl: &IRDecl) -> Option<&'static str> {
    if decl.params.len() != 2
        || decl.params[0].1 != IRType::USize
        || decl.params[1].1 != IRType::USize
        || decl.return_type != IRType::Bool
    {
        return None;
    }
    match decl.name.to_string().as_str() {
        "USize.decEq" => Some("=="),
        "USize.decLt" => Some("<"),
        "USize.decLe" => Some("<="),
        _ => None,
    }
}

/// Configuration for C code generation.
#[derive(Debug, Clone)]
pub struct CEmitConfig {
    /// Include debug assertions.
    pub debug: bool,
    /// Use atomic ref counting (for thread safety).
    pub atomic_rc: bool,
    /// Indent string (spaces or tabs).
    pub indent: String,
    /// Validate IR before emitting C (default: enabled).
    pub check_ir: bool,
}

impl Default for CEmitConfig {
    fn default() -> Self {
        Self {
            debug: false,
            atomic_rc: true,
            indent: "  ".to_string(),
            check_ir: true,
        }
    }
}

/// C code emitter state.
pub struct CEmitter {
    /// Shared output buffering and indentation.
    pub(crate) base: EmitterBase,
    /// Configuration (debug, atomic_rc fields reserved for future use).
    #[allow(dead_code)]
    config: CEmitConfig,
    /// Join point parameter VarIds, populated by JDecl for Jmp lookup.
    pub(crate) jp_params: HashMap<JoinPointId, Vec<VarId>>,
    /// Known IR type of each in-scope variable (function params, `VDecl`
    /// bindings, join-point params). Used by `emit_case` to decide whether a
    /// `Case` scrutinee is an unboxed scalar (switch on its value directly) or a
    /// boxed object (switch on `clean_obj_tag`), and by the C2
    /// carrier-projection arms of `emit_expr`.
    pub(crate) var_types: HashMap<VarId, IRType>,
    /// In-slice declaration shapes (parameter count + return type), populated
    /// by `emit_decls`. Drives the saturated-call + `clean_apply_N`
    /// over-application discipline in the `Apply` arm — the same discipline
    /// as `emit_trust_ir::emit_apply_user`. Callees not in this map are
    /// emitted as direct calls (historical behavior for external symbols).
    decl_shapes: HashMap<Name, (usize, IRType)>,
}

impl CEmitter {
    /// Create a new C emitter with default configuration.
    pub fn new() -> Self {
        Self::with_config(CEmitConfig::default())
    }

    /// Create a new C emitter with custom configuration.
    pub fn with_config(config: CEmitConfig) -> Self {
        let base = EmitterBase::new(config.indent.clone());
        Self {
            base,
            config,
            jp_params: HashMap::new(),
            var_types: HashMap::new(),
            decl_shapes: HashMap::new(),
        }
    }

    /// Record the IR type of an in-scope variable for later scrutinee analysis.
    pub(crate) fn record_var_type(&mut self, var: VarId, ty: &IRType) {
        self.var_types.insert(var, ty.clone());
    }

    /// Whether `ty` is an unboxed scalar in the C representation (its C value
    /// *is* the runtime tag for single-byte enums like `Bool`), as opposed to a
    /// boxed `clean_obj*` whose tag must be read with `clean_obj_tag`.
    pub(crate) fn is_unboxed_scalar(ty: &IRType) -> bool {
        matches!(
            ty,
            IRType::Bool
                | IRType::UInt8
                | IRType::UInt16
                | IRType::UInt32
                | IRType::UInt64
                | IRType::USize
        )
    }

    /// Get the generated C code.
    pub fn finish(self) -> String {
        self.base.finish()
    }

    /// Write a line with current indentation.
    pub(crate) fn writeln(&mut self, s: &str) {
        self.base.writeln(s);
    }

    /// Increase indentation.
    pub(crate) fn indent(&mut self) {
        self.base.indent();
    }

    /// Decrease indentation.
    pub(crate) fn dedent(&mut self) {
        self.base.dedent();
    }

    /// Emit file header with includes.
    pub fn emit_header(&mut self) {
        self.writeln("// Generated by clean compiler");
        self.writeln("// Do not edit manually");
        self.writeln("");
        self.writeln("#include <stdint.h>");
        self.writeln("#include <stdbool.h>");
        self.writeln("#include <stdlib.h>");
        self.writeln("#include <math.h>");
        self.writeln("#include \"clean_runtime.h\"");
        self.writeln("");
    }

    /// Emit `extern` forward declarations for FFI-linked functions.
    ///
    /// For each `@[extern "c_func"]` declaration, emits a C `extern`
    /// declaration so the generated code can call the native function.
    /// These are placed after `#include` and before function definitions.
    ///
    /// # Example output
    ///
    /// ```c
    /// /* extern: IO.Handle.mk -> clean_io_handle_mk */
    /// extern clean_obj* clean_io_handle_mk(clean_obj*);
    /// ```
    pub fn emit_extern_decls(&mut self, bridge: &crate::ffi_bridge::FfiBridge) {
        let externs = bridge.extern_decls();
        if externs.is_empty() {
            return;
        }

        self.writeln("/* ── Extern (FFI) forward declarations ── */");
        self.writeln("");

        for ext in externs {
            let return_ty = self.emit_type(&ext.return_type);
            let params_str = if ext.param_types.is_empty() {
                "void".to_string()
            } else {
                ext.param_types
                    .iter()
                    .map(|ty| self.emit_type(ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            };

            self.writeln(&format!(
                "/* extern: {} -> {} */",
                ext.lean_name, ext.c_name
            ));
            self.writeln(&format!(
                "extern {} {}({});",
                return_ty, ext.c_name, params_str
            ));
        }
        self.writeln("");
    }

    /// Emit type definition for IR type.
    pub(crate) fn emit_type(&self, ty: &IRType) -> String {
        match ty {
            IRType::Bool => "uint8_t".to_string(),
            IRType::UInt8 => "uint8_t".to_string(),
            IRType::UInt16 => "uint16_t".to_string(),
            IRType::UInt32 => "uint32_t".to_string(),
            IRType::UInt64 => "uint64_t".to_string(),
            IRType::USize => "size_t".to_string(),
            IRType::Float32 => "float".to_string(),
            IRType::Float64 => "double".to_string(),
            IRType::Object | IRType::TObject => "clean_obj*".to_string(),
            IRType::Struct(_) => "clean_obj*".to_string(), // Boxed struct
            IRType::Union(_) => "clean_obj*".to_string(),  // Tagged union
            IRType::Erased => "clean_obj*".to_string(),    // Erased = unit
            IRType::Void => "void".to_string(),
        }
    }

    /// Emit C identifier for a Name.
    fn emit_name(&self, name: &Name) -> String {
        self.base.emit_name(name)
    }

    /// Emit variable reference.
    pub(crate) fn emit_var(&self, var: VarId) -> String {
        self.base.emit_var(var)
    }

    /// Emit join point label.
    pub(crate) fn emit_jp(&self, jp: JoinPointId) -> String {
        format!("_jp{}", jp.0)
    }

    /// Emit function ID.
    fn emit_fn_id(&self, fn_id: &FnId) -> String {
        self.base.emit_fn_id(fn_id)
    }

    /// Emit an IR argument.
    pub(crate) fn emit_arg(&self, arg: &IRArg) -> String {
        self.base.emit_arg(arg)
    }

    /// Emit a literal value.
    pub(crate) fn emit_literal(&self, lit: &IRLiteral) -> String {
        match lit {
            IRLiteral::Bool(b) => if *b { "1" } else { "0" }.to_string(),
            IRLiteral::UInt8(n) => format!("UINT8_C({})", n),
            IRLiteral::UInt16(n) => format!("UINT16_C({})", n),
            IRLiteral::UInt32(n) => format!("UINT32_C({})", n),
            IRLiteral::UInt64(n) => format!("UINT64_C({})", n),
            IRLiteral::USize(n) => format!("(size_t){}", n),
            // Big Nat literal (>= 2^64): a heap Nat built from two u64 limbs
            // (RUNG B). Object-typed, so it needs no further boxing.
            IRLiteral::NatBig(v) => format!(
                "clean_nat_big(UINT64_C({}), UINT64_C({}))",
                *v as u64,
                (*v >> 64) as u64
            ),
            IRLiteral::Float32(f) => emit_c_float32(*f),
            IRLiteral::Float64(f) => emit_c_float64(*f),
        }
    }

    /// Emit a closure allocation (PartialApply).
    fn emit_partial_apply(&self, fn_id: &FnId, arity: u16, args: &[IRArg]) -> String {
        let args_str: Vec<String> = args.iter().map(|a| self.emit_arg(a)).collect();
        if args.is_empty() {
            format!(
                "clean_alloc_closure((void*){}, {}, 0)",
                self.emit_fn_id(fn_id),
                arity,
            )
        } else {
            format!(
                "clean_alloc_closure((void*){}, {}, {}, {})",
                self.emit_fn_id(fn_id),
                arity,
                args.len(),
                args_str.join(", ")
            )
        }
    }

    /// Emit a dynamic closure application.
    ///
    /// Uses positional `clean_apply_N(closure, a1, ..., aN)` for arities 0..=16,
    /// matching the runtime's `closure_apply.rs` dispatch range. Falls back to
    /// variadic `clean_apply_n(closure, n, args[])` above 16.
    fn emit_closure_apply(&self, closure: &IRArg, args: &[IRArg]) -> String {
        let n = args.len();
        if n <= 16 {
            let mut call_args = vec![self.emit_arg(closure)];
            call_args.extend(args.iter().map(|a| self.emit_arg(a)));
            format!("clean_apply_{}({})", n, call_args.join(", "))
        } else {
            let args_str: Vec<String> = args.iter().map(|a| self.emit_arg(a)).collect();
            format!(
                "clean_apply_n({}, {}, (clean_obj*[]){{{}}})",
                self.emit_arg(closure),
                n,
                args_str.join(", ")
            )
        }
    }

    /// Emit a direct application with the saturated-call + `clean_apply_N`
    /// over-application discipline (parity with
    /// `emit_trust_ir::emit_apply_user`).
    ///
    /// L5IR `Apply` args are the full application spine of the call site, so
    /// for an in-slice callee (`decl_shapes`):
    ///
    /// * `args.len() == params` → plain direct call;
    /// * `args.len() > params` → the saturated prefix is the direct call and
    ///   the extras are applied to its RESULT closure via `clean_apply_N`
    ///   (`Functor.mapRev` calling the 2-param projection with a 6-arg
    ///   spine). Requires a `clean_obj*`-returning callee — a scalar result
    ///   has nothing to apply the extras to. The old direct emission produced
    ///   an arity-mismatched C call that did not compile;
    /// * `args.len() < params` → under-application outside a `PartialApply`
    ///   has no faithful lowering; refused (the ir_checker refuses it too —
    ///   this keeps `check_ir: false` callers honest).
    ///
    /// Unknown callees (external symbols) keep the historical direct call:
    /// there is no shape to discipline against.
    fn emit_apply(&self, fn_id: &FnId, args: &[IRArg]) -> Result<String, IRError> {
        let Some((n_params, return_type)) = self.decl_shapes.get(&fn_id.0) else {
            let args_str: Vec<String> = args.iter().map(|a| self.emit_arg(a)).collect();
            return Ok(format!(
                "{}({})",
                self.emit_fn_id(fn_id),
                args_str.join(", ")
            ));
        };
        if args.len() < *n_params || (args.len() > *n_params && !return_type.lowers_to_ptr()) {
            return Err(IRError::ArityMismatch {
                function: fn_id.0.clone(),
                expected: *n_params,
                actual: args.len(),
            });
        }
        let (direct, extra) = args.split_at(*n_params);
        let direct_str: Vec<String> = direct.iter().map(|a| self.emit_arg(a)).collect();
        let saturated = format!("{}({})", self.emit_fn_id(fn_id), direct_str.join(", "));
        if extra.is_empty() {
            return Ok(saturated);
        }
        let n = extra.len();
        if n <= 16 {
            let mut call_args = vec![saturated];
            call_args.extend(extra.iter().map(|a| self.emit_arg(a)));
            Ok(format!("clean_apply_{}({})", n, call_args.join(", ")))
        } else {
            let extra_str: Vec<String> = extra.iter().map(|a| self.emit_arg(a)).collect();
            Ok(format!(
                "clean_apply_n({}, {}, (clean_obj*[]){{{}}})",
                saturated,
                n,
                extra_str.join(", ")
            ))
        }
    }

    /// Re-box an unboxed scalar carrier into a managed object (the C mirror
    /// of `emit_trust_ir::box_scalar_tagged`): floats heap-box via
    /// `clean_box_float`; integer/Bool carriers become the tagged immediate
    /// via `clean_box`.
    fn emit_box_scalar_carrier(carrier: &IRType, var_str: &str) -> String {
        match carrier {
            IRType::Float64 | IRType::Float32 => {
                format!("clean_box_float((double){var_str})")
            }
            // U64-width `Nat` carriers (`UInt64`/`USize`) may reach bit 63, which
            // the tagged `clean_box` would truncate (`UInt64.toNat(2^63)` -> 0).
            // Route through the sound `clean_nat_of_u64` producer (RUNG B) — the
            // C mirror of `emit_trust_ir::box_scalar_tagged`. Narrower carriers
            // (U8/U16/U32/Bool) are always < 2^63, so tagged `clean_box` is exact.
            IRType::UInt64 | IRType::USize => {
                format!("clean_nat_of_u64((uint64_t){var_str})")
            }
            _ => format!("clean_box((size_t){var_str})"),
        }
    }

    /// Emit an IR expression.
    pub(crate) fn emit_expr(&mut self, expr: &IRExpr) -> Result<String, IRError> {
        Ok(match expr {
            IRExpr::Ctor { info, args } => {
                let args_str: Vec<String> = args.iter().map(|a| self.emit_arg(a)).collect();
                if args.is_empty() && info.scalar_size() == 0 {
                    format!("clean_box({})", info.tag)
                } else if args.is_empty() {
                    // Scalar-only ctor: no object args but needs heap allocation
                    // for scalar storage. Part of #1974.
                    format!("clean_alloc_ctor({}, 0, {})", info.tag, info.scalar_size())
                } else {
                    // clean_alloc_ctor(tag, num_objs, scalar_sz, args...)
                    // scalar_sz ensures the runtime allocates enough space for
                    // inline scalar data after the object pointer array.
                    // Part of #1953.
                    format!(
                        "clean_alloc_ctor({}, {}, {}, {})",
                        info.tag,
                        info.num_objects,
                        info.scalar_size(),
                        args_str.join(", ")
                    )
                }
            }
            IRExpr::Proj { idx, ty, arg } => {
                // C2 carrier projection (parity with `emit_trust_ir`): a
                // projection out of an UNBOXED SCALAR carrier (`Char` lowered
                // to `uint32_t`) is the identity at the same lowered width
                // (`Char.val`), or a re-boxing when the declared result is
                // pointer-class (`UInt8.toBitVec` re-boxing the carrier;
                // `Char.valid` projecting an erased proof — any managed value
                // is faithful there). A width-changing scalar projection has
                // no faithful lowering and is refused (the ir_checker refuses
                // it too; this arm keeps `check_ir: false` callers honest).
                if let IRArg::Var(v) = arg {
                    if let Some(carrier) = self.var_types.get(v).filter(|t| t.is_scalar()) {
                        if carrier.same_lowered_scalar(ty) {
                            return Ok(self.emit_var(*v));
                        }
                        if ty.lowers_to_ptr() {
                            return Ok(Self::emit_box_scalar_carrier(carrier, &self.emit_var(*v)));
                        }
                        return Err(IRError::TypeMismatch {
                            expected: "same-width scalar or object result",
                            actual: carrier.clone(),
                            context: "projection out of scalar carrier",
                        });
                    }
                }
                match ty {
                    IRType::UInt8 => {
                        format!("clean_ctor_get_uint8({}, {})", self.emit_arg(arg), idx)
                    }
                    IRType::UInt16 => {
                        format!("clean_ctor_get_uint16({}, {})", self.emit_arg(arg), idx)
                    }
                    IRType::UInt32 => {
                        format!("clean_ctor_get_uint32({}, {})", self.emit_arg(arg), idx)
                    }
                    IRType::UInt64 => {
                        format!("clean_ctor_get_uint64({}, {})", self.emit_arg(arg), idx)
                    }
                    IRType::USize => {
                        format!("clean_ctor_get_usize({}, {})", self.emit_arg(arg), idx)
                    }
                    IRType::Float64 => {
                        format!("clean_ctor_get_float({}, {})", self.emit_arg(arg), idx)
                    }
                    IRType::Float32 => {
                        format!("clean_ctor_get_float32({}, {})", self.emit_arg(arg), idx)
                    }
                    _ => format!("clean_ctor_get({}, {})", self.emit_arg(arg), idx),
                }
            }
            IRExpr::Tag(arg) => format!("clean_obj_tag({})", self.emit_arg(arg)),
            IRExpr::Box { ty, arg } => match ty {
                IRType::UInt64 => format!("clean_box_uint64({})", self.emit_arg(arg)),
                IRType::UInt32 => format!("clean_box_uint32({})", self.emit_arg(arg)),
                IRType::Float64 => format!("clean_box_float({})", self.emit_arg(arg)),
                IRType::Float32 => format!("clean_box_float((double){})", self.emit_arg(arg)),
                _ => format!("clean_box((size_t){})", self.emit_arg(arg)),
            },
            IRExpr::Unbox { ty, arg } => match ty {
                IRType::Float64 => format!("clean_unbox_float({})", self.emit_arg(arg)),
                IRType::Float32 => format!("(float)clean_unbox_float({})", self.emit_arg(arg)),
                // USize joins UInt64 on the tagged-or-heap 64-bit unbox (parity
                // with emit_trust_ir's `UInt64 | USize` arm); the `_` fallthrough
                // was tagged-only `clean_unbox`, wrong for a heap-boxed carrier.
                IRType::UInt64 | IRType::USize => {
                    format!("clean_unbox_uint64({})", self.emit_arg(arg))
                }
                IRType::UInt32 => format!("clean_unbox_uint32({})", self.emit_arg(arg)),
                _ => format!("clean_unbox({})", self.emit_arg(arg)),
            },
            IRExpr::Lit(lit) => self.emit_literal(lit),
            IRExpr::Apply { fn_id, args } => self.emit_apply(fn_id, args)?,
            IRExpr::PartialApply { fn_id, arity, args } => {
                self.emit_partial_apply(fn_id, *arity, args)
            }
            IRExpr::ClosureApply { closure, args } => self.emit_closure_apply(closure, args),
            IRExpr::UProj { idx, var } => {
                // C2 carrier projection: `UProj` produces `size_t`, so out of
                // an unboxed scalar carrier only a `uint64_t`/`size_t`-class
                // carrier is the faithful identity (parity with
                // `emit_trust_ir`'s `UProj` arm).
                if let Some(carrier) = self.var_types.get(var).filter(|t| t.is_scalar()) {
                    if carrier.same_lowered_scalar(&IRType::USize) {
                        return Ok(self.emit_var(*var));
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
                // an unboxed scalar carrier (`Char.val` as `sproj` on a
                // `uint32_t`); any other width has no faithful lowering.
                if let Some(carrier) = self.var_types.get(var).filter(|t| t.is_scalar()) {
                    if carrier.same_lowered_scalar(ty) {
                        return Ok(self.emit_var(*var));
                    }
                    return Err(IRError::TypeMismatch {
                        expected: "object or same-width scalar carrier",
                        actual: carrier.clone(),
                        context: "sproj source",
                    });
                }
                format!(
                    "{}({}, {})",
                    c_scalar_getter_name(ty)?,
                    self.emit_var(*var),
                    c_byte_offset(*n, *offset)
                )
            }
            IRExpr::IsShared(var) => {
                format!("!clean_is_exclusive({})", self.emit_var(*var))
            }
            IRExpr::String(s) => format!("clean_mk_string({})", emit_c_string_literal(s)),
            IRExpr::Reset(var) => format!("clean_reset({})", self.emit_var(*var)),
            IRExpr::Reuse { var, ctor, args } => {
                let args_str: Vec<String> = args.iter().map(|a| self.emit_arg(a)).collect();
                if args.is_empty() {
                    // clean_reuse(slot, tag, num_objs, scalar_sz)
                    format!(
                        "clean_reuse({}, {}, 0, {})",
                        self.emit_var(*var),
                        ctor.tag,
                        ctor.scalar_size()
                    )
                } else {
                    // clean_reuse(slot, tag, num_objs, scalar_sz, obj_args...)
                    // Part of #1974: use ctor.num_objects (not args.len()) and
                    // pass scalar_size for correct allocation sizing.
                    format!(
                        "clean_reuse({}, {}, {}, {}, {})",
                        self.emit_var(*var),
                        ctor.tag,
                        ctor.num_objects,
                        ctor.scalar_size(),
                        args_str.join(", ")
                    )
                }
            }
        })
    }

    /// Emit a complete function declaration.
    pub fn emit_decl(&mut self, decl: &IRDecl) -> Result<(), IRError> {
        let fn_name = self.emit_name(&decl.name);
        let return_ty = self.emit_type(&decl.return_type);

        // Record parameter types so an `if`-style `Case` whose scrutinee is an
        // unboxed `Bool` parameter switches on the value, not `clean_obj_tag`.
        for (var, ty) in &decl.params {
            self.record_var_type(*var, ty);
        }

        // Build parameter list
        let params: Vec<String> = decl
            .params
            .iter()
            .map(|(var, ty)| format!("{} {}", self.emit_type(ty), self.emit_var(*var)))
            .collect();

        let params_str = if params.is_empty() {
            "void".to_string()
        } else {
            params.join(", ")
        };

        // Function signature
        self.writeln(&format!("{} {}({}) {{", return_ty, fn_name, params_str));
        self.indent();

        // SOUNDNESS FIX (2026-07-12): the target-pinned `USize` decision
        // procedures (`USize.decEq` / `decLt` / `decLe`) lower to a DIRECT
        // native `size_t` comparison, bypassing the width-abstract
        // `clean_box` + `clean_obj_tag` switch path that boxed each operand
        // (truncating at bit 63) and destructured `USize.ofBitVec` as a
        // no-default tag switch (returning stack garbage). See
        // `usize_native_decision_op` for the full root-cause analysis; the
        // guard there fires only for the exact 2×`USize` → `Bool` shape.
        if let Some(op) = usize_native_decision_op(decl) {
            let lhs = self.emit_var(decl.params[0].0);
            let rhs = self.emit_var(decl.params[1].0);
            self.writeln(&format!("return {lhs} {op} {rhs};"));
        } else {
            // Function body
            self.emit_body(&decl.body)?;
        }

        self.dedent();
        self.writeln("}");
        self.writeln("");
        Ok(())
    }

    /// Emit multiple declarations.
    pub fn emit_decls(&mut self, decls: &[IRDecl]) -> Result<(), IRError> {
        // Record in-slice callee shapes for the `Apply` over-application
        // discipline (see `emit_apply`).
        for decl in decls {
            self.decl_shapes.insert(
                decl.name.clone(),
                (decl.params.len(), decl.return_type.clone()),
            );
        }
        // Emit forward declarations first
        for decl in decls {
            let fn_name = self.emit_name(&decl.name);
            let return_ty = self.emit_type(&decl.return_type);
            let params: Vec<String> = decl
                .params
                .iter()
                .map(|(var, ty)| format!("{} {}", self.emit_type(ty), self.emit_var(*var)))
                .collect();
            let params_str = if params.is_empty() {
                "void".to_string()
            } else {
                params.join(", ")
            };
            self.writeln(&format!("{} {}({});", return_ty, fn_name, params_str));
        }
        self.writeln("");

        // Emit function bodies
        for decl in decls {
            self.emit_decl(decl)?;
        }
        Ok(())
    }
}

impl Default for CEmitter {
    fn default() -> Self {
        Self::new()
    }
}

/// Emit C code for a list of declarations.
pub fn emit_c(decls: &[IRDecl]) -> Result<String, IRError> {
    emit_c_with_config(decls, CEmitConfig::default())
}

/// Emit C code with custom configuration.
///
/// Returns an error if IR validation is enabled and the IR is invalid.
pub fn emit_c_with_config(decls: &[IRDecl], config: CEmitConfig) -> Result<String, IRError> {
    if config.check_ir {
        check_decls(decls)?;
    }
    let mut emitter = CEmitter::with_config(config);
    emitter.emit_header();
    emitter.emit_decls(decls)?;
    Ok(emitter.finish())
}
