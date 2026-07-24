// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Rust Code Emitter
//!
//! Higher-level Rust emission: IR-to-Rust type mapping with ownership semantics,
//! function emission, body emission with match/let, closure emission, trait impl
//! emission (From, Drop for RC types), module structure, Cargo.toml snippet
//! generation, FFI bridge emission (`#[no_mangle] extern "C"`), and statistics.
//!
//! Part of #3084 - IO/FFI/Native.

use std::fmt::Write as FmtWrite;

use crate::emit_base::EmitterBase;
use crate::ir::{IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use crate::ir_checker::IRError;
use crate::mangle::mangle_name;

/// Ownership mode for a Rust binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Ownership {
    Owned,
    Borrowed,
    BorrowedMut,
}

/// Map an IR type to a Rust type string (owned form).
#[must_use]
pub(crate) fn rust_type_owned(ty: &IRType) -> String {
    match ty {
        IRType::Bool | IRType::UInt8 => "u8".into(),
        IRType::UInt16 => "u16".into(),
        IRType::UInt32 => "u32".into(),
        IRType::UInt64 => "u64".into(),
        IRType::USize => "usize".into(),
        IRType::Float32 => "f32".into(),
        IRType::Float64 => "f64".into(),
        IRType::Object
        | IRType::TObject
        | IRType::Struct(_)
        | IRType::Union(_)
        | IRType::Erased => "LeanObj".into(),
        IRType::Void => "()".into(),
    }
}

/// Map an IR type to a borrowed Rust type string.
#[must_use]
pub(crate) fn rust_type_borrowed(ty: &IRType) -> String {
    if ty.is_scalar() || ty.is_void() {
        rust_type_owned(ty)
    } else {
        format!("&{}", rust_type_owned(ty))
    }
}

/// Map an IR type to a boxed Rust type (heap-allocated RC wrapper).
#[must_use]
pub(crate) fn rust_type_boxed(ty: &IRType) -> String {
    if ty.is_scalar() || ty.is_void() {
        rust_type_owned(ty)
    } else {
        format!("Box<{}>", rust_type_owned(ty))
    }
}

/// Determine ownership for a parameter based on IR type.
#[must_use]
pub(crate) fn default_ownership(_ty: &IRType) -> Ownership {
    // All parameters are owned by default: scalars/voids are trivially owned,
    // and RC types are moved (passed by value).
    Ownership::Owned
}

/// Statistics collected during extended Rust emission.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct RustExtStats {
    pub(crate) functions_emitted: u32,
    pub(crate) closures_emitted: u32,
    pub(crate) trait_impls_emitted: u32,
    pub(crate) ffi_bridges_emitted: u32,
    pub(crate) let_bindings_emitted: u32,
    pub(crate) match_exprs_emitted: u32,
}

/// Configuration for the extended Rust emitter.
#[derive(Debug, Clone)]
pub(crate) struct RustExtConfig {
    pub(crate) module_name: String,
    pub(crate) emit_trait_impls: bool,
    pub(crate) emit_cargo_snippet: bool,
    pub(crate) indent: String,
}

impl Default for RustExtConfig {
    fn default() -> Self {
        Self {
            module_name: "clean_generated".into(),
            emit_trait_impls: true,
            emit_cargo_snippet: false,
            indent: "    ".into(),
        }
    }
}

/// FFI function descriptor for `#[no_mangle] extern "C"` wrapper generation.
#[derive(Debug, Clone)]
pub(crate) struct RustFfiFunc {
    pub(crate) lean_name: String,
    pub(crate) extern_name: String,
    pub(crate) param_types: Vec<IRType>,
    pub(crate) return_type: IRType,
}

/// Extended Rust code emitter with ownership tracking and statistics.
pub(crate) struct RustExtEmitter {
    base: EmitterBase,
    config: RustExtConfig,
    stats: RustExtStats,
}

impl RustExtEmitter {
    pub(crate) fn new() -> Self {
        Self::with_config(RustExtConfig::default())
    }

    pub(crate) fn with_config(config: RustExtConfig) -> Self {
        Self {
            base: EmitterBase::new(config.indent.clone()),
            config,
            stats: RustExtStats::default(),
        }
    }

    pub(crate) fn finish(self) -> String {
        self.base.finish()
    }
    pub(crate) fn stats(&self) -> &RustExtStats {
        &self.stats
    }

    fn writeln(&mut self, s: &str) {
        self.base.writeln(s);
    }
    fn indent(&mut self) {
        self.base.indent();
    }
    fn dedent(&mut self) {
        self.base.dedent();
    }
    fn emit_var(&self, var: VarId) -> String {
        self.base.emit_var(var)
    }
    fn emit_arg(&self, arg: &IRArg) -> String {
        self.base.emit_arg(arg)
    }
    fn emit_fn_name(&self, name: &clean_kernel::Name) -> String {
        mangle_name(name)
    }

    // ── Type mapping ──

    pub(crate) fn map_type(ty: &IRType) -> String {
        rust_type_owned(ty)
    }

    pub(crate) fn map_type_with_ownership(ty: &IRType, ownership: Ownership) -> String {
        match ownership {
            Ownership::Owned => rust_type_owned(ty),
            Ownership::Borrowed => rust_type_borrowed(ty),
            Ownership::BorrowedMut => {
                if ty.is_scalar() || ty.is_void() {
                    rust_type_owned(ty)
                } else {
                    format!("&mut {}", rust_type_owned(ty))
                }
            }
        }
    }

    fn format_params(&self, params: &[(VarId, IRType)]) -> String {
        if params.is_empty() {
            return String::new();
        }
        params
            .iter()
            .map(|(var, ty)| {
                format!(
                    "{}: {}",
                    self.emit_var(*var),
                    Self::map_type_with_ownership(ty, default_ownership(ty))
                )
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    // ── Module structure ──

    pub(crate) fn emit_module_header(&mut self) {
        self.writeln(&format!(
            "//! Generated module: {}",
            self.config.module_name
        ));
        self.writeln("//! Do not edit manually.");
        self.writeln("");
        self.writeln("#![allow(unused_variables, unused_assignments, unreachable_code)]");
        self.writeln("");
        self.writeln("use clean_runtime::*;");
        self.writeln("");
    }

    pub(crate) fn emit_mod_decl(&mut self, name: &str) {
        self.writeln(&format!("pub mod {};", name));
    }
    pub(crate) fn emit_use_stmt(&mut self, path: &str) {
        self.writeln(&format!("use {};", path));
    }

    // ── Function emission ──

    pub(crate) fn emit_function(&mut self, decl: &IRDecl) -> Result<(), IRError> {
        let (fn_name, ret_ty, params) = (
            self.emit_fn_name(&decl.name),
            Self::map_type(&decl.return_type),
            self.format_params(&decl.params),
        );
        self.writeln(&format!(
            "pub unsafe fn {}({}) -> {} {{",
            fn_name, params, ret_ty
        ));
        self.indent();
        self.emit_body(&decl.body)?;
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.stats.functions_emitted += 1;
        Ok(())
    }

    pub(crate) fn emit_functions(&mut self, decls: &[IRDecl]) -> Result<(), IRError> {
        for decl in decls {
            self.emit_function(decl)?;
        }
        Ok(())
    }

    // ── Body emission ──

    fn emit_body(&mut self, body: &IRBody) -> Result<(), IRError> {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                let val_s = self.emit_expr(value)?;
                self.writeln(&format!(
                    "let {}: {} = {};",
                    self.emit_var(*var),
                    Self::map_type(ty),
                    val_s
                ));
                self.stats.let_bindings_emitted += 1;
                self.emit_body(rest)?;
            }
            IRBody::JDecl {
                jp,
                params,
                body: jp_body,
                rest,
            } => {
                for (var, ty) in params {
                    self.writeln(&format!(
                        "let mut {}: {};",
                        self.emit_var(*var),
                        Self::map_type(ty)
                    ));
                }
                self.emit_body(rest)?;
                self.writeln(&format!("'_jp{}: loop {{", jp.0));
                self.indent();
                self.emit_body(jp_body)?;
                self.writeln("break;");
                self.dedent();
                self.writeln("}");
            }
            IRBody::Inc { var, n, rest } => {
                let v = self.emit_var(*var);
                if *n == 1 {
                    self.writeln(&format!("clean_inc_ref({});", v));
                } else {
                    self.writeln(&format!("clean_inc_ref_n({}, {});", v, n));
                }
                self.emit_body(rest)?;
            }
            IRBody::Dec { var, rest } => {
                self.writeln(&format!("clean_dec_ref({});", self.emit_var(*var)));
                self.emit_body(rest)?;
            }
            IRBody::Set {
                var,
                idx,
                value,
                rest,
            } => {
                self.writeln(&format!(
                    "clean_ctor_set({}, {}, {});",
                    self.emit_var(*var),
                    idx,
                    self.emit_var(*value)
                ));
                self.emit_body(rest)?;
            }
            IRBody::SetTag { var, tag, rest } => {
                self.writeln(&format!(
                    "clean_ctor_set_tag({}, {});",
                    self.emit_var(*var),
                    tag
                ));
                self.emit_body(rest)?;
            }
            IRBody::USet {
                var,
                idx,
                value,
                rest,
            } => {
                self.writeln(&format!(
                    "clean_ctor_set_usize({}, {}, {});",
                    self.emit_var(*var),
                    idx,
                    self.emit_var(*value)
                ));
                self.emit_body(rest)?;
            }
            IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => {
                let off = (*n as usize) * size_of::<usize>() + (*offset as usize);
                self.writeln(&format!(
                    "{}({}, {}, {});",
                    scalar_setter(ty),
                    self.emit_var(*var),
                    off,
                    self.emit_var(*value)
                ));
                self.emit_body(rest)?;
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                self.emit_match(*scrutinee, alts, default.as_deref())?;
            }
            IRBody::Jmp { jp, args } => {
                for (i, arg) in args.iter().enumerate() {
                    self.writeln(&format!("_jp{}_arg{} = {};", jp.0, i, self.emit_arg(arg)));
                }
                self.writeln(&format!("continue '_jp{};", jp.0));
            }
            IRBody::Ret(arg) => {
                self.writeln(&format!("return {};", self.emit_arg(arg)));
            }
            IRBody::Unreachable => {
                self.writeln("unreachable!(\"IR unreachable\");");
            }
        }
        Ok(())
    }

    fn emit_match(
        &mut self,
        scrutinee: VarId,
        alts: &[IRAlt],
        default: Option<&IRBody>,
    ) -> Result<(), IRError> {
        self.writeln(&format!(
            "match clean_obj_tag({}) {{",
            self.emit_var(scrutinee)
        ));
        self.indent();
        for alt in alts {
            self.writeln(&format!("{} => {{", alt.ctor.tag));
            self.indent();
            self.emit_body(&alt.body)?;
            self.dedent();
            self.writeln("}");
        }
        if let Some(def) = default {
            self.writeln("_ => {");
            self.indent();
            self.emit_body(def)?;
            self.dedent();
            self.writeln("}");
        }
        self.dedent();
        self.writeln("}");
        self.stats.match_exprs_emitted += 1;
        Ok(())
    }

    // ── Expression emission ──

    fn emit_expr(&mut self, expr: &IRExpr) -> Result<String, IRError> {
        Ok(match expr {
            IRExpr::Ctor { info, args } => {
                let a = self.base.emit_args_joined(args);
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
                        a
                    )
                }
            }
            IRExpr::Proj { idx, ty, arg } => {
                let g = match ty {
                    IRType::UInt8 => "clean_ctor_get_uint8",
                    IRType::UInt16 => "clean_ctor_get_uint16",
                    IRType::UInt32 => "clean_ctor_get_uint32",
                    IRType::UInt64 => "clean_ctor_get_uint64",
                    IRType::USize => "clean_ctor_get_usize",
                    IRType::Float64 => "clean_ctor_get_float",
                    IRType::Float32 => "clean_ctor_get_float32",
                    _ => "clean_ctor_get",
                };
                format!("{}({}, {})", g, self.emit_arg(arg), idx)
            }
            IRExpr::Tag(arg) => format!("clean_obj_tag({}) as u32", self.emit_arg(arg)),
            IRExpr::Box { ty, arg } => match ty {
                IRType::UInt64 => format!("clean_box_uint64({})", self.emit_arg(arg)),
                IRType::UInt32 => format!("clean_box_uint32({})", self.emit_arg(arg)),
                IRType::Float64 => format!("clean_box_float({})", self.emit_arg(arg)),
                _ => format!("clean_box({} as usize)", self.emit_arg(arg)),
            },
            IRExpr::Unbox { ty, arg } => match ty {
                IRType::Float64 => format!("clean_unbox_float({})", self.emit_arg(arg)),
                IRType::UInt64 => format!("clean_unbox_uint64({})", self.emit_arg(arg)),
                IRType::UInt32 => format!("clean_unbox_uint32({})", self.emit_arg(arg)),
                _ => format!("clean_unbox({})", self.emit_arg(arg)),
            },
            IRExpr::Lit(lit) => emit_rust_literal(lit),
            IRExpr::Apply { fn_id, args } => {
                format!(
                    "{}({})",
                    self.base.emit_fn_id(fn_id),
                    self.base.emit_args_joined(args)
                )
            }
            IRExpr::PartialApply { fn_id, arity, args } => {
                self.stats.closures_emitted += 1;
                format!(
                    "clean_alloc_closure({} as *const (), {}, &[{}])",
                    self.base.emit_fn_id(fn_id),
                    arity,
                    self.base.emit_args_joined(args)
                )
            }
            IRExpr::ClosureApply { closure, args } => {
                format!(
                    "clean_closure_apply({}, &[{}])",
                    self.emit_arg(closure),
                    self.base.emit_args_joined(args)
                )
            }
            IRExpr::UProj { idx, var } => {
                format!("clean_ctor_get_usize({}, {})", self.emit_var(*var), idx)
            }
            IRExpr::SProj { n, offset, var, ty } => {
                let off = (*n as usize) * size_of::<usize>() + (*offset as usize);
                format!("{}({}, {})", scalar_getter(ty), self.emit_var(*var), off)
            }
            IRExpr::IsShared(var) => {
                format!("(!clean_is_exclusive({})) as u8", self.emit_var(*var))
            }
            IRExpr::String(s) => format!("clean_mk_string({:?})", s),
            IRExpr::Reset(var) => format!("clean_reset({})", self.emit_var(*var)),
            IRExpr::Reuse { var, ctor, args } => {
                format!(
                    "clean_reuse({}, {}, {}, &[{}])",
                    self.emit_var(*var),
                    ctor.tag,
                    ctor.scalar_size(),
                    self.base.emit_args_joined(args)
                )
            }
        })
    }

    // ── Closure emission ──

    pub(crate) fn emit_closure_struct(
        &mut self,
        name: &str,
        captured: &[(VarId, IRType)],
        remaining_params: &[(VarId, IRType)],
        return_type: &IRType,
    ) {
        let sn = format!("Closure_{}", name);
        self.writeln(&format!("pub(crate) struct {} {{", sn));
        self.indent();
        for (var, ty) in captured {
            self.writeln(&format!("{}: {},", self.emit_var(*var), Self::map_type(ty)));
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");
        let ps = remaining_params
            .iter()
            .map(|(var, ty)| format!("{}: {}", self.emit_var(*var), Self::map_type(ty)))
            .collect::<Vec<_>>()
            .join(", ");
        self.writeln(&format!("impl {} {{", sn));
        self.indent();
        self.writeln(&format!(
            "pub unsafe fn call(&self, {}) -> {} {{",
            ps,
            Self::map_type(return_type)
        ));
        self.indent();
        self.writeln("unreachable!(\"closure body filled by codegen\")");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.stats.closures_emitted += 1;
    }

    // ── Trait implementation emission ──

    pub(crate) fn emit_drop_impl(&mut self, type_name: &str) {
        self.writeln(&format!("impl Drop for {} {{", type_name));
        self.indent();
        self.writeln("fn drop(&mut self) {");
        self.indent();
        self.writeln("unsafe { clean_dec_ref(self.ptr); }");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.stats.trait_impls_emitted += 1;
    }

    pub(crate) fn emit_from_impl(&mut self, type_name: &str) {
        self.writeln(&format!("impl From<*mut LeanObj> for {} {{", type_name));
        self.indent();
        self.writeln("fn from(ptr: *mut LeanObj) -> Self {");
        self.indent();
        self.writeln(&format!("{} {{ ptr }}", type_name));
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.stats.trait_impls_emitted += 1;
    }

    // ── FFI bridge emission ──

    pub(crate) fn emit_ffi_bridge(&mut self, func: &RustFfiFunc) {
        let ret_ty = Self::map_type(&func.return_type);
        let params: Vec<String> = func
            .param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| format!("_a{}: {}", i, Self::map_type(ty)))
            .collect();
        self.writeln("#[no_mangle]");
        self.writeln(&format!(
            "pub unsafe extern \"C\" fn {}({}) -> {} {{",
            func.extern_name,
            params.join(", "),
            ret_ty
        ));
        self.indent();
        let call_args: Vec<String> = (0..func.param_types.len())
            .map(|i| format!("_a{}", i))
            .collect();
        self.writeln(&format!(
            "{}({})",
            mangle_name(&clean_kernel::Name::from_string(&func.lean_name)),
            call_args.join(", ")
        ));
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.stats.ffi_bridges_emitted += 1;
    }

    // ── Cargo.toml snippet generation ──

    #[must_use]
    pub(crate) fn cargo_toml_snippet(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "[package]");
        let _ = writeln!(out, "name = \"{}\"", self.config.module_name);
        let _ = writeln!(out, "version = \"0.1.0\"");
        let _ = writeln!(out, "edition = \"2021\"");
        let _ = writeln!(out);
        let _ = writeln!(out, "[dependencies]");
        let _ = writeln!(out, "clean-runtime = {{ path = \"../clean-runtime\" }}");
        out
    }

    // ── Full module emission ──

    pub(crate) fn emit_module(
        &mut self,
        decls: &[IRDecl],
        ffi_funcs: &[RustFfiFunc],
    ) -> Result<(), IRError> {
        self.emit_module_header();
        self.emit_functions(decls)?;
        if !ffi_funcs.is_empty() {
            self.writeln("// ── FFI bridges ──");
            self.writeln("");
            for func in ffi_funcs {
                self.emit_ffi_bridge(func);
            }
        }
        Ok(())
    }
}

impl Default for RustExtEmitter {
    fn default() -> Self {
        Self::new()
    }
}

// ── Free functions ──

fn emit_rust_literal(lit: &IRLiteral) -> String {
    match lit {
        IRLiteral::Bool(b) => if *b { "1u8" } else { "0u8" }.to_string(),
        IRLiteral::UInt8(n) => format!("{}u8", n),
        IRLiteral::UInt16(n) => format!("{}u16", n),
        IRLiteral::UInt32(n) => format!("{}u32", n),
        IRLiteral::UInt64(n) => format!("{}u64", n),
        IRLiteral::USize(n) => format!("{}usize", n),
        IRLiteral::NatBig(v) => {
            format!("clean_nat_big({}u64, {}u64)", *v as u64, (*v >> 64) as u64)
        }
        IRLiteral::Float32(f) if f.is_nan() => "f32::NAN".into(),
        IRLiteral::Float32(f) if f.is_infinite() => if f.is_sign_positive() {
            "f32::INFINITY"
        } else {
            "f32::NEG_INFINITY"
        }
        .into(),
        IRLiteral::Float32(f) => format!("{}f32", f),
        IRLiteral::Float64(f) if f.is_nan() => "f64::NAN".into(),
        IRLiteral::Float64(f) if f.is_infinite() => if f.is_sign_positive() {
            "f64::INFINITY"
        } else {
            "f64::NEG_INFINITY"
        }
        .into(),
        IRLiteral::Float64(f) => format!("{}f64", f),
    }
}

fn scalar_getter(ty: &IRType) -> &'static str {
    match ty {
        IRType::UInt8 | IRType::Bool => "clean_ctor_get_uint8",
        IRType::UInt16 => "clean_ctor_get_uint16",
        IRType::UInt32 => "clean_ctor_get_uint32",
        IRType::UInt64 => "clean_ctor_get_uint64",
        IRType::Float32 => "clean_ctor_get_float32",
        IRType::Float64 => "clean_ctor_get_float",
        IRType::USize => "clean_ctor_get_usize",
        _ => "clean_ctor_get",
    }
}

fn scalar_setter(ty: &IRType) -> &'static str {
    match ty {
        IRType::UInt8 | IRType::Bool => "clean_ctor_set_uint8",
        IRType::UInt16 => "clean_ctor_set_uint16",
        IRType::UInt32 => "clean_ctor_set_uint32",
        IRType::UInt64 => "clean_ctor_set_uint64",
        IRType::Float32 => "clean_ctor_set_float32",
        IRType::Float64 => "clean_ctor_set_float",
        IRType::USize => "clean_ctor_set_usize",
        _ => "clean_ctor_set",
    }
}
