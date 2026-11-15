// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FFI extern declaration elaboration.
//!
//! Handles `@[extern "c_name"]` and `@[implemented_by impl_name]` attributes
//! during elaboration. Validates extern signatures for FFI compatibility,
//! extracts C/native function names, and generates [`ExternDecl`] records
//! for the compiler backend.
//!
//! # Lean 4 Reference
//!
//! In Lean 4, `@[extern "name"]` is processed by `ExternAttr.lean` which stores
//! entries in a persistent extension keyed by backend name. The elaborator
//! validates that the declaration exists and the extern name is non-empty.
//! Multi-backend declarations use `@[extern c "c_name" llvm "llvm_name"]`.
//!
//! `@[implemented_by impl_name]` is processed by `ImplementedByAttr.lean`. It
//! resolves the target as an existing global constant, requires equal
//! universe-parameter counts, and requires the target's type, instantiated at
//! the declaration's universe parameters, to be STRUCTURALLY equal to the
//! declaration's (`Expr` `==`, which ignores binder names and annotations —
//! not definitional equality). [`validate_implemented_by`] is that rule.

use clean_kernel::expr::ExprKind;
use clean_kernel::{Environment, Expr, Level, Name};

use crate::error::ElabError;

/// FFI-compatible type classification for extern signatures.
///
/// Maps Lean types to their C ABI representation. Used during elaboration
/// to validate that extern function parameters and return types can cross
/// the FFI boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum FfiType {
    /// `UInt8` / `Bool` -> `uint8_t`
    UInt8,
    /// `UInt16` -> `uint16_t`
    UInt16,
    /// `UInt32` / `Char` -> `uint32_t`
    UInt32,
    /// `UInt64` -> `uint64_t`
    UInt64,
    /// `USize` -> `size_t`
    USize,
    /// `Float` -> `double` (Lean Float is 64-bit)
    Float,
    /// `Float32` -> `float`
    Float32,
    /// `Unit` -> `void` (for return types only)
    Unit,
    /// Any boxed Lean object (reference-counted) -> `lean_object*`
    Object,
}

impl FfiType {
    /// Human-readable C type name for diagnostics.
    #[must_use]
    pub(crate) fn c_type_name(self) -> &'static str {
        match self {
            FfiType::UInt8 => "uint8_t",
            FfiType::UInt16 => "uint16_t",
            FfiType::UInt32 => "uint32_t",
            FfiType::UInt64 => "uint64_t",
            FfiType::USize => "size_t",
            FfiType::Float => "double",
            FfiType::Float32 => "float",
            FfiType::Unit => "void",
            FfiType::Object => "lean_object*",
        }
    }
}

/// A resolved extern declaration record for the compiler backend.
///
/// Produced during elaboration when `@[extern "c_name"]` is encountered.
/// Carries the validated signature information downstream to the compiler's
/// [`FfiBridge`](clean_compiler) for C code emission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExternDecl {
    /// The Lean declaration name.
    pub(crate) lean_name: Name,
    /// The C/native symbol name from the attribute.
    pub(crate) extern_name: String,
    /// Backend identifier (`"c"`, `"llvm"`, `"all"`, etc.).
    pub(crate) backend: String,
    /// Parameter FFI types extracted from the function signature.
    pub(crate) param_types: Vec<FfiType>,
    /// Return FFI type.
    pub(crate) return_type: FfiType,
}

/// A parsed extern entry from a multi-backend extern attribute.
///
/// `@[extern c "c_name" llvm "llvm_name"]` produces two entries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExternEntry {
    /// Backend name (e.g., `"c"`, `"llvm"`, `"all"`).
    pub(crate) backend: String,
    /// Symbol name for that backend.
    pub(crate) name: String,
}

/// Classify a kernel `Expr` type as an FFI-compatible type.
///
/// Walks through the head constant name to determine the C ABI mapping.
/// Types that don't have a direct C representation are classified as
/// `FfiType::Object` (boxed Lean objects).
#[must_use]
pub(crate) fn classify_ffi_type(ty: &Expr) -> FfiType {
    // Strip applications to get the head constant
    let head = ty.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => classify_const_name(name),
        _ => FfiType::Object,
    }
}

/// Map a constant name to its FFI type classification.
fn classify_const_name(name: &Name) -> FfiType {
    let s = name.to_string();
    match s.as_str() {
        "UInt8" => FfiType::UInt8,
        "Bool" => FfiType::UInt8,
        "UInt16" => FfiType::UInt16,
        "UInt32" => FfiType::UInt32,
        "Char" => FfiType::UInt32,
        "UInt64" => FfiType::UInt64,
        "USize" => FfiType::USize,
        "Float" => FfiType::Float,
        "Float32" => FfiType::Float32,
        "Unit" | "PUnit" => FfiType::Unit,
        _ => FfiType::Object,
    }
}

/// Extract parameter types and return type from a function signature.
///
/// Walks through nested `Pi` types to collect parameters, with the
/// final non-Pi body as the return type.
pub(crate) fn extract_ffi_signature(ty: &Expr) -> (Vec<FfiType>, FfiType) {
    let mut params = Vec::new();
    let mut current = ty.clone();

    loop {
        match current.kind() {
            ExprKind::Pi(_, domain, body) => {
                params.push(classify_ffi_type(domain.as_ref()));
                current = body.as_ref().clone();
            }
            _ => {
                let ret = classify_ffi_type(&current);
                return (params, ret);
            }
        }
    }
}

/// Parse an extern attribute string into backend/name entries.
///
/// Supports two forms:
/// - Simple: `"c_name"` -> single entry with backend `"all"`
/// - Multi-backend: `c "c_name" llvm "llvm_name"` -> multiple entries
///
/// # Errors
///
/// Returns `Err` if the extern name is empty or the multi-backend
/// syntax is malformed (odd number of tokens, empty name).
pub(crate) fn parse_extern_attr(attr_value: &str) -> Result<Vec<ExternEntry>, ElabError> {
    let trimmed = attr_value.trim();
    if trimmed.is_empty() {
        return Err(ElabError::Unsupported {
            feature: "extern attribute requires a non-empty name".to_owned(),
        });
    }

    // Simple case: just a C name (no backend prefix)
    // This is the common `@[extern "lean_io_prim_handle_mk"]` form
    if !trimmed.contains(' ') {
        return Ok(vec![ExternEntry {
            backend: "all".to_owned(),
            name: trimmed.to_owned(),
        }]);
    }

    // Multi-backend: parse pairs of (backend, "name")
    let tokens: Vec<&str> = trimmed.split_whitespace().collect();
    if !tokens.len().is_multiple_of(2) {
        return Err(ElabError::Unsupported {
            feature: format!(
                "extern attribute has odd number of tokens (expected backend/name pairs): '{trimmed}'"
            ),
        });
    }

    let mut entries = Vec::with_capacity(tokens.len() / 2);
    for pair in tokens.chunks(2) {
        let backend = pair[0];
        let name = pair[1].trim_matches('"');
        if name.is_empty() {
            return Err(ElabError::Unsupported {
                feature: format!("extern name for backend '{backend}' is empty"),
            });
        }
        entries.push(ExternEntry {
            backend: backend.to_owned(),
            name: name.to_owned(),
        });
    }

    Ok(entries)
}

/// Validate an extern declaration signature for FFI compatibility.
///
/// Checks that all parameter types and the return type are FFI-compatible.
/// Returns warnings for types that will be boxed as `lean_object*` (these
/// are valid but may indicate a missing unboxing opportunity).
///
/// # Errors
///
/// Returns `Err` if the extern name is empty.
pub(crate) fn validate_extern_signature(
    decl_name: &Name,
    extern_name: &str,
    ty: &Expr,
) -> Result<ExternDecl, ElabError> {
    if extern_name.is_empty() {
        return Err(ElabError::Unsupported {
            feature: format!("extern declaration '{decl_name}' has empty extern name"),
        });
    }

    let (param_types, return_type) = extract_ffi_signature(ty);

    Ok(ExternDecl {
        lean_name: decl_name.clone(),
        extern_name: extern_name.to_owned(),
        backend: "all".to_owned(),
        param_types,
        return_type,
    })
}

/// Validate an `@[implemented_by impl_name]` binding with Lean's rule
/// (`src/Lean/Compiler/ImplementedByAttr.lean`, v4.30.0-rc2), after the
/// declaration is registered and before the binding is:
///
/// 1. `impl_name` must name a constant that ALREADY exists — a forward
///    reference is Lean's "Unknown constant" (it resolves the argument with
///    `realizeGlobalConstNoOverload` when the attribute is applied);
/// 2. the two universe-parameter counts must be equal;
/// 3. the implementation's type, instantiated at the declaration's universe
///    parameters (positionally), must be structurally equal to the
///    declaration's type — [`implemented_by_types_agree`], NOT definitional
///    equality: Lean rejects `MyNat → MyNat` for `Nat → Nat` under
///    `abbrev MyNat := Nat`;
/// 4. the implementation must not be the declaration itself.
///
/// The compiler substitutes the implementation at every call
/// (`clean_compiler::to_lcnf`), so a binding this accepts must be one Lean
/// accepts: a mismatched type would run code of another type.
///
/// # Errors
///
/// [`ElabError::InvalidImplementedBy`] with Lean's message: an empty or
/// unregistered name is an unknown constant (the resolver,
/// `crate::implemented_by::resolve_implemented_by`, has refused those before
/// this runs), the rest are 2-4.
pub(crate) fn validate_implemented_by(
    decl_name: &Name,
    impl_name: &Name,
    env: &Environment,
) -> Result<(), ElabError> {
    use crate::implemented_by::ImplementedByDefect;
    let refuse = |target: &Name, defect| ElabError::InvalidImplementedBy {
        decl: decl_name.clone(),
        target: target.to_string(),
        defect,
    };
    let (Some(decl), Some(target)) = (env.get_const(decl_name), env.get_const(impl_name)) else {
        let missing = if env.get_const(decl_name).is_none() {
            decl_name
        } else {
            impl_name
        };
        return Err(refuse(missing, ImplementedByDefect::UnknownConstant));
    };
    if decl.level_params.len() != target.level_params.len() {
        return Err(refuse(
            impl_name,
            ImplementedByDefect::LevelCount {
                target_levels: target.level_params.len(),
                decl_levels: decl.level_params.len(),
            },
        ));
    }
    let levels: Vec<Level> = decl
        .level_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    let target_type = target
        .type_
        .instantiate_level_params_direct(&target.level_params, &levels);
    if !implemented_by_types_agree(&decl.type_, &target_type) {
        return Err(refuse(
            impl_name,
            ImplementedByDefect::TypeMismatch {
                target_type: target_type.to_string(),
                decl_type: decl.type_.to_string(),
            },
        ));
    }
    if decl_name == impl_name {
        return Err(refuse(impl_name, ImplementedByDefect::SelfImplementation));
    }
    Ok(())
}

/// Lean's `Expr` `==` (`Expr.eqv`): structural equality up to binder names and
/// binder annotations. Clean's `Expr` `==` also compares binder annotations,
/// and Lean accepts `def slow {α} (x : α)` implemented by `def fast (α) (x : α)`.
/// Anything this does not recognise falls back to Clean's stricter `==`, so it
/// can only refuse more than Lean, never accept a pair Lean rejects.
pub(crate) fn implemented_by_types_agree(a: &Expr, b: &Expr) -> bool {
    if a == b {
        return true;
    }
    match (a.kind(), b.kind()) {
        (ExprKind::Pi(_, ta, ba), ExprKind::Pi(_, tb, bb))
        | (ExprKind::Lam(_, ta, ba), ExprKind::Lam(_, tb, bb))
        | (ExprKind::App(ta, ba), ExprKind::App(tb, bb)) => {
            implemented_by_types_agree(ta, tb) && implemented_by_types_agree(ba, bb)
        }
        (ExprKind::Let(_, ta, va, ba, _), ExprKind::Let(_, tb, vb, bb, _)) => {
            implemented_by_types_agree(ta, tb)
                && implemented_by_types_agree(va, vb)
                && implemented_by_types_agree(ba, bb)
        }
        (ExprKind::MData(ma, ia), ExprKind::MData(mb, ib)) => {
            ma == mb && implemented_by_types_agree(ia, ib)
        }
        (ExprKind::Proj(na, ia, ea), ExprKind::Proj(nb, ib, eb)) => {
            na == nb && ia == ib && implemented_by_types_agree(ea, eb)
        }
        _ => false,
    }
}

/// Process a complete extern attribute during elaboration.
///
/// This is the main entry point called from the attribute processing path.
/// It parses the extern attribute, validates the signature, and returns
/// the resolved extern declarations for registration.
///
/// # Errors
///
/// Returns `Err` if parsing or validation fails.
pub(crate) fn process_extern_attr(
    decl_name: &Name,
    attr_value: &str,
    ty: &Expr,
) -> Result<Vec<ExternDecl>, ElabError> {
    let entries = parse_extern_attr(attr_value)?;
    let (param_types, return_type) = extract_ffi_signature(ty);

    let decls = entries
        .into_iter()
        .map(|entry| ExternDecl {
            lean_name: decl_name.clone(),
            extern_name: entry.name,
            backend: entry.backend,
            param_types: param_types.clone(),
            return_type,
        })
        .collect();

    Ok(decls)
}

/// Check whether a Lean type is directly FFI-compatible (unboxed).
///
/// Returns `true` for scalar types that map directly to C types without
/// boxing. These are the types that can be passed by value across the
/// FFI boundary.
#[must_use]
pub(crate) fn is_ffi_scalar(ty: &Expr) -> bool {
    matches!(
        classify_ffi_type(ty),
        FfiType::UInt8
            | FfiType::UInt16
            | FfiType::UInt32
            | FfiType::UInt64
            | FfiType::USize
            | FfiType::Float
            | FfiType::Float32
            | FfiType::Unit
    )
}

/// Check whether a type requires boxing for FFI transport.
///
/// Returns `true` for types that must be boxed as `lean_object*` when
/// passed to or returned from C functions.
#[must_use]
pub(crate) fn requires_boxing(ty: &Expr) -> bool {
    classify_ffi_type(ty) == FfiType::Object
}

/// Validate that an extern C name follows naming conventions.
///
/// Lean 4 extern names typically follow `lean_` or `lean4_` prefixes for
/// runtime functions, or arbitrary C identifiers for user-provided FFI.
/// This function checks for obviously invalid names (empty, contains spaces,
/// starts with a digit).
pub(crate) fn validate_extern_name(name: &str) -> Result<(), ElabError> {
    if name.is_empty() {
        return Err(ElabError::Unsupported {
            feature: "extern name is empty".to_owned(),
        });
    }

    // C identifiers: [a-zA-Z_][a-zA-Z0-9_]*
    let first = name.as_bytes()[0];
    if !first.is_ascii_alphabetic() && first != b'_' {
        return Err(ElabError::Unsupported {
            feature: format!(
                "extern name '{name}' is not a valid C identifier (must start with letter or underscore)"
            ),
        });
    }

    if !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
        return Err(ElabError::Unsupported {
            feature: format!("extern name '{name}' contains invalid characters for a C identifier"),
        });
    }

    Ok(())
}
