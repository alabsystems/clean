// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended native code generation infrastructure.
//!
//! Provides target-aware type mapping, runtime function declarations,
//! C/Rust header generation, name mangling, and platform-specific size/alignment
//! computation for the clean compiler's native backends.
//!
//! Part of #3084 - IO/FFI/Native code generation infrastructure.

use std::fmt;

use crate::ir::{IRDecl, IRType};

// ---------------------------------------------------------------------------
// NativeTarget
// ---------------------------------------------------------------------------

/// Code generation target backend.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum NativeTarget {
    /// C source output (gcc/clang).
    C,
    /// Rust source output.
    Rust,
    /// LLVM IR output.
    Llvm,
}

impl fmt::Display for NativeTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::C => write!(f, "C"),
            Self::Rust => write!(f, "Rust"),
            Self::Llvm => write!(f, "LLVM"),
        }
    }
}

// ---------------------------------------------------------------------------
// Platform
// ---------------------------------------------------------------------------

/// Target platform for native code generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum Platform {
    Linux,
    MacOs,
    Windows,
    Wasm,
}

impl Platform {
    /// Pointer size in bytes for this platform.
    #[must_use]
    pub(crate) fn pointer_size(self) -> usize {
        match self {
            Self::Wasm => 4,
            Self::Linux | Self::MacOs | Self::Windows => 8,
        }
    }
}

// ---------------------------------------------------------------------------
// NativeCodegenConfig
// ---------------------------------------------------------------------------

/// Configuration for native code generation.
#[derive(Debug, Clone)]
pub(crate) struct NativeCodegenConfig {
    pub(crate) target: NativeTarget,
    pub(crate) optimize: bool,
    pub(crate) debug_info: bool,
    pub(crate) runtime_checks: bool,
    pub(crate) platform: Platform,
}

impl Default for NativeCodegenConfig {
    fn default() -> Self {
        Self {
            target: NativeTarget::C,
            optimize: false,
            debug_info: false,
            runtime_checks: true,
            platform: Platform::Linux,
        }
    }
}

// ---------------------------------------------------------------------------
// NativeType (extended, target-aware)
// ---------------------------------------------------------------------------

/// Machine-level type for native code generation.
///
/// Unlike the IR-level `IRType`, these types map directly to C/Rust/LLVM
/// declarations and carry enough information for sizeof/alignof computation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum ExtNativeType {
    Void,
    Bool,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Int8,
    Int16,
    Int32,
    Int64,
    Float,
    Double,
    /// Pointer to another native type.
    Ptr(Box<ExtNativeType>),
    /// Lean runtime object (`clean_obj*`).
    LeanObj,
    /// Lean boxed scalar (`clean_box*`).
    LeanBox,
    /// Fixed-element-type array.
    Array(Box<ExtNativeType>),
    /// Named struct type.
    Struct(String),
}

impl ExtNativeType {
    /// C type name for this native type.
    #[must_use]
    pub(crate) fn c_name(&self) -> String {
        match self {
            Self::Void => "void".to_owned(),
            Self::Bool => "uint8_t".to_owned(),
            Self::UInt8 => "uint8_t".to_owned(),
            Self::UInt16 => "uint16_t".to_owned(),
            Self::UInt32 => "uint32_t".to_owned(),
            Self::UInt64 => "uint64_t".to_owned(),
            Self::Int8 => "int8_t".to_owned(),
            Self::Int16 => "int16_t".to_owned(),
            Self::Int32 => "int32_t".to_owned(),
            Self::Int64 => "int64_t".to_owned(),
            Self::Float => "float".to_owned(),
            Self::Double => "double".to_owned(),
            Self::Ptr(inner) => format!("{}*", inner.c_name()),
            Self::LeanObj => "clean_obj*".to_owned(),
            Self::LeanBox => "clean_box*".to_owned(),
            Self::Array(elem) => format!("{}*", elem.c_name()),
            Self::Struct(name) => format!("struct {name}"),
        }
    }

    /// Rust type name for this native type.
    #[must_use]
    pub(crate) fn rust_name(&self) -> String {
        match self {
            Self::Void => "()".to_owned(),
            Self::Bool => "u8".to_owned(),
            Self::UInt8 => "u8".to_owned(),
            Self::UInt16 => "u16".to_owned(),
            Self::UInt32 => "u32".to_owned(),
            Self::UInt64 => "u64".to_owned(),
            Self::Int8 => "i8".to_owned(),
            Self::Int16 => "i16".to_owned(),
            Self::Int32 => "i32".to_owned(),
            Self::Int64 => "i64".to_owned(),
            Self::Float => "f32".to_owned(),
            Self::Double => "f64".to_owned(),
            Self::Ptr(inner) => format!("*mut {}", inner.rust_name()),
            Self::LeanObj => "*mut CleanObj".to_owned(),
            Self::LeanBox => "*mut CleanBox".to_owned(),
            Self::Array(elem) => format!("*mut {}", elem.rust_name()),
            Self::Struct(name) => name.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// RuntimeDecl
// ---------------------------------------------------------------------------

/// A runtime function declaration for the clean C/Rust ABI.
#[derive(Debug, Clone)]
pub(crate) struct RuntimeDecl {
    pub(crate) name: String,
    pub(crate) params: Vec<(String, ExtNativeType)>,
    pub(crate) return_type: ExtNativeType,
    pub(crate) is_extern: bool,
}

/// Build an extern `RuntimeDecl` from name, parameter list, and return type.
fn rt(name: &str, params: Vec<(&str, ExtNativeType)>, ret: ExtNativeType) -> RuntimeDecl {
    RuntimeDecl {
        name: name.to_owned(),
        params: params.into_iter().map(|(n, t)| (n.to_owned(), t)).collect(),
        return_type: ret,
        is_extern: true,
    }
}

/// Map an IR type to an extended native type.
#[must_use]
pub(crate) fn ir_type_to_native(ir_type: &IRType, config: &NativeCodegenConfig) -> ExtNativeType {
    match ir_type {
        IRType::Bool => ExtNativeType::Bool,
        IRType::UInt8 => ExtNativeType::UInt8,
        IRType::UInt16 => ExtNativeType::UInt16,
        IRType::UInt32 => ExtNativeType::UInt32,
        IRType::UInt64 => ExtNativeType::UInt64,
        IRType::USize => {
            if config.platform == Platform::Wasm {
                ExtNativeType::UInt32
            } else {
                ExtNativeType::UInt64
            }
        }
        IRType::Float32 => ExtNativeType::Float,
        IRType::Float64 => ExtNativeType::Double,
        IRType::Object | IRType::TObject => ExtNativeType::LeanObj,
        IRType::Struct(_) => ExtNativeType::LeanObj,
        IRType::Union(_) => ExtNativeType::LeanObj,
        IRType::Erased => ExtNativeType::LeanObj,
        IRType::Void => ExtNativeType::Void,
    }
}

// ---------------------------------------------------------------------------
// generate_runtime_decls
// ---------------------------------------------------------------------------

/// Generate the set of clean runtime function declarations.
#[must_use]
pub(crate) fn generate_runtime_decls(config: &NativeCodegenConfig) -> Vec<RuntimeDecl> {
    let o = ExtNativeType::LeanObj;
    let u = ExtNativeType::UInt32;
    let sz = if config.platform == Platform::Wasm {
        ExtNativeType::UInt32
    } else {
        ExtNativeType::UInt64
    };
    let v = ExtNativeType::Void;
    let mut d = vec![
        rt(
            "clean_inc",
            vec![("o", o.clone()), ("n", u.clone())],
            v.clone(),
        ),
        rt("clean_dec", vec![("o", o.clone())], v.clone()),
        rt(
            "clean_alloc_ctor",
            vec![
                ("tag", u.clone()),
                ("num_objs", u.clone()),
                ("scalar_sz", u.clone()),
            ],
            o.clone(),
        ),
        rt(
            "clean_ctor_get",
            vec![("o", o.clone()), ("i", u.clone())],
            o.clone(),
        ),
        rt(
            "clean_ctor_set",
            vec![("o", o.clone()), ("i", u.clone()), ("v", o.clone())],
            v.clone(),
        ),
        rt("clean_box", vec![("v", sz.clone())], o.clone()),
        rt("clean_unbox", vec![("o", o.clone())], sz),
        rt(
            "clean_is_exclusive",
            vec![("o", o.clone())],
            ExtNativeType::Bool,
        ),
        rt("clean_ctor_tag", vec![("o", o.clone())], u),
    ];
    if config.runtime_checks {
        d.push(rt("clean_assert_rc", vec![("o", o)], v));
    }
    d
}

// ---------------------------------------------------------------------------
// generate_header
// ---------------------------------------------------------------------------

/// Generate a C header or Rust extern block for the given IR declarations.
#[must_use]
pub(crate) fn generate_header(decls: &[IRDecl], config: &NativeCodegenConfig) -> String {
    let mut out = String::with_capacity(1024);

    match config.target {
        NativeTarget::C => {
            out.push_str("#pragma once\n");
            out.push_str("#include <stdint.h>\n");
            out.push_str("#include \"clean_runtime.h\"\n\n");
            for decl in decls {
                let ret = ir_type_to_native(&decl.return_type, config);
                let mangled = mangle_for_target(&decl.name.to_string(), &config.target);
                let params: Vec<String> = decl
                    .params
                    .iter()
                    .map(|(_, ty)| ir_type_to_native(ty, config).c_name())
                    .collect();
                out.push_str(&format!(
                    "{} {}({});\n",
                    ret.c_name(),
                    mangled,
                    if params.is_empty() {
                        "void".to_owned()
                    } else {
                        params.join(", ")
                    }
                ));
            }
        }
        NativeTarget::Rust => {
            out.push_str("extern \"C\" {\n");
            for decl in decls {
                let ret = ir_type_to_native(&decl.return_type, config);
                let mangled = mangle_for_target(&decl.name.to_string(), &config.target);
                let params: Vec<String> = decl
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, (_, ty))| {
                        format!("arg{}: {}", i, ir_type_to_native(ty, config).rust_name())
                    })
                    .collect();
                let ret_str = if ret == ExtNativeType::Void {
                    String::new()
                } else {
                    format!(" -> {}", ret.rust_name())
                };
                out.push_str(&format!(
                    "    fn {}({}){ret_str};\n",
                    mangled,
                    params.join(", ")
                ));
            }
            out.push_str("}\n");
        }
        NativeTarget::Llvm => {
            out.push_str("; LLVM IR declarations\n");
            for decl in decls {
                let mangled = mangle_for_target(&decl.name.to_string(), &config.target);
                out.push_str(&format!("declare void @{mangled}()\n"));
            }
        }
    }

    out
}

// ---------------------------------------------------------------------------
// generate_type_decl
// ---------------------------------------------------------------------------

/// Generate a struct type declaration for the target language.
#[must_use]
pub(crate) fn generate_type_decl(
    name: &str,
    fields: &[(String, ExtNativeType)],
    config: &NativeCodegenConfig,
) -> String {
    let mut out = String::new();

    match config.target {
        NativeTarget::C => {
            out.push_str(&format!("typedef struct {name} {{\n"));
            for (fname, ftype) in fields {
                out.push_str(&format!("    {} {};\n", ftype.c_name(), fname));
            }
            out.push_str(&format!("}} {name};\n"));
        }
        NativeTarget::Rust => {
            out.push_str(&format!("#[repr(C)]\npub struct {name} {{\n"));
            for (fname, ftype) in fields {
                out.push_str(&format!("    pub {}: {},\n", fname, ftype.rust_name()));
            }
            out.push_str("}\n");
        }
        NativeTarget::Llvm => {
            let field_types: Vec<&str> = fields.iter().map(|_| "i64").collect();
            out.push_str(&format!(
                "%{name} = type {{ {} }}\n",
                field_types.join(", ")
            ));
        }
    }

    out
}

// ---------------------------------------------------------------------------
// mangle_for_target
// ---------------------------------------------------------------------------

/// Mangle a Lean name for the specified code generation target.
///
/// - C: `l5_` prefix, dots replaced with `__`.
/// - Rust: `l5_` prefix, dots replaced with `_`.
/// - LLVM: `@l5_` prefix, dots replaced with `.`.
#[must_use]
pub(crate) fn mangle_for_target(name: &str, target: &NativeTarget) -> String {
    match target {
        NativeTarget::C => format!("l5_{}", name.replace('.', "__")),
        NativeTarget::Rust => format!("l5_{}", name.replace('.', "_")),
        NativeTarget::Llvm => format!("l5_{}", name.replace('.', "$")),
    }
}

// ---------------------------------------------------------------------------
// sizeof_native / alignof_native
// ---------------------------------------------------------------------------

/// Compute the byte size of a native type on the given platform.
#[must_use]
pub(crate) fn sizeof_native(ty: &ExtNativeType, platform: &Platform) -> usize {
    match ty {
        ExtNativeType::Void => 0,
        ExtNativeType::Bool | ExtNativeType::UInt8 | ExtNativeType::Int8 => 1,
        ExtNativeType::UInt16 | ExtNativeType::Int16 => 2,
        ExtNativeType::UInt32 | ExtNativeType::Int32 | ExtNativeType::Float => 4,
        ExtNativeType::UInt64 | ExtNativeType::Int64 | ExtNativeType::Double => 8,
        ExtNativeType::Ptr(_)
        | ExtNativeType::LeanObj
        | ExtNativeType::LeanBox
        | ExtNativeType::Array(_) => platform.pointer_size(),
        ExtNativeType::Struct(_) => {
            // Opaque struct — return pointer size as conservative estimate.
            platform.pointer_size()
        }
    }
}

/// Compute the alignment of a native type on the given platform.
#[must_use]
pub(crate) fn alignof_native(ty: &ExtNativeType, platform: &Platform) -> usize {
    match ty {
        ExtNativeType::Void => 1,
        ExtNativeType::Bool | ExtNativeType::UInt8 | ExtNativeType::Int8 => 1,
        ExtNativeType::UInt16 | ExtNativeType::Int16 => 2,
        ExtNativeType::UInt32 | ExtNativeType::Int32 | ExtNativeType::Float => 4,
        ExtNativeType::UInt64 | ExtNativeType::Int64 | ExtNativeType::Double => 8,
        ExtNativeType::Ptr(_)
        | ExtNativeType::LeanObj
        | ExtNativeType::LeanBox
        | ExtNativeType::Array(_) => platform.pointer_size(),
        ExtNativeType::Struct(_) => platform.pointer_size(),
    }
}

// ---------------------------------------------------------------------------
// is_boxed_type
// ---------------------------------------------------------------------------

/// Check if an IR type requires boxing in native code.
///
/// Object types and composite types are represented as heap-allocated
/// `clean_obj*` pointers. Scalars are stored inline.
#[must_use]
pub(crate) fn is_boxed_type(ir_type: &IRType) -> bool {
    matches!(
        ir_type,
        IRType::Object | IRType::TObject | IRType::Struct(_) | IRType::Union(_)
    )
}
