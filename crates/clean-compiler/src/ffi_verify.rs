// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verify extern declarations against the known C runtime ABI.

use crate::ir::IRType;
use crate::lcnf::{ExternAttr, ExternEntry, Param};
use crate::to_ir::expr_to_ir_type;
use clean_kernel::{Expr, Name};
use thiserror::Error;

/// Current compiler-side extern binding packet.
///
/// The broader kernel `ExternBindingData` plumbing from the earlier design has
/// not landed in this tree yet, so the verifier treats the LCNF `ExternAttr`
/// payload as the current binding packet shape.
pub type ExternBindingData = ExternAttr;

/// Current compiler-side extern binding entry.
pub type ExternBindingEntry = ExternEntry;

/// ABI mismatch discovered while validating an extern declaration.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum FfiMismatch {
    /// The referenced C runtime symbol is not in the known ABI surface.
    #[error("extern declaration {decl:?} references unknown {backend} symbol {extern_name}")]
    UnknownExtern {
        decl: Name,
        backend: String,
        extern_name: String,
    },

    /// The extern declaration's parameter count does not match the runtime ABI.
    #[error(
        "extern declaration {decl:?} uses {backend} symbol {extern_name} with arity {found}, expected {expected}"
    )]
    ArityMismatch {
        decl: Name,
        backend: String,
        extern_name: String,
        expected: String,
        found: usize,
    },

    /// The extern declaration's return type is not ABI-compatible.
    #[error(
        "extern declaration {decl:?} uses {backend} symbol {extern_name} with return type {found}, expected compatible with {expected}"
    )]
    TypeMismatch {
        decl: Name,
        backend: String,
        extern_name: String,
        expected: String,
        found: String,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuntimeReturnType {
    Bool,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    USize,
    Float32,
    Float64,
    Object,
    Void,
}

impl RuntimeReturnType {
    fn as_str(self) -> &'static str {
        match self {
            RuntimeReturnType::Bool => "bool",
            RuntimeReturnType::UInt8 => "uint8_t",
            RuntimeReturnType::UInt16 => "uint16_t",
            RuntimeReturnType::UInt32 => "uint32_t",
            RuntimeReturnType::UInt64 => "uint64_t",
            RuntimeReturnType::USize => "size_t",
            RuntimeReturnType::Float32 => "float",
            RuntimeReturnType::Float64 => "double",
            RuntimeReturnType::Object => "clean_obj*",
            RuntimeReturnType::Void => "void",
        }
    }

    fn is_compatible_with(self, ir_type: Option<&IRType>) -> bool {
        match (self, ir_type) {
            (RuntimeReturnType::Bool, Some(IRType::Bool)) => true,
            (RuntimeReturnType::UInt8, Some(IRType::UInt8)) => true,
            (RuntimeReturnType::UInt16, Some(IRType::UInt16)) => true,
            (RuntimeReturnType::UInt32, Some(IRType::UInt32)) => true,
            (RuntimeReturnType::UInt64, Some(IRType::UInt64)) => true,
            (RuntimeReturnType::USize, Some(IRType::USize)) => true,
            (RuntimeReturnType::Float32, Some(IRType::Float32)) => true,
            (RuntimeReturnType::Float64, Some(IRType::Float64)) => true,
            (RuntimeReturnType::Object, Some(ir_type)) => ir_type.is_object(),
            (RuntimeReturnType::Void, Some(IRType::Erased)) => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RuntimeSignature {
    name: &'static str,
    fixed_arity: usize,
    variadic: bool,
    return_type: RuntimeReturnType,
}

impl RuntimeSignature {
    fn matches_arity(self, found: usize) -> bool {
        if self.variadic {
            found >= self.fixed_arity
        } else {
            found == self.fixed_arity
        }
    }

    fn expected_arity(self) -> String {
        if self.variadic {
            format!(">= {}", self.fixed_arity)
        } else {
            self.fixed_arity.to_string()
        }
    }
}

const RUNTIME_SIGNATURES: &[RuntimeSignature] = &[
    RuntimeSignature {
        name: "clean_box",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_unbox",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::USize,
    },
    RuntimeSignature {
        name: "clean_is_scalar",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Bool,
    },
    RuntimeSignature {
        name: "clean_box_uint32",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_box_uint64",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_box_float",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_unbox_uint32",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::UInt32,
    },
    RuntimeSignature {
        name: "clean_unbox_uint64",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::UInt64,
    },
    RuntimeSignature {
        name: "clean_unbox_float",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Float64,
    },
    RuntimeSignature {
        name: "clean_inc",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_inc_n",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_dec",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_ctor_get",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_ctor_set",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_obj_tag",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::UInt8,
    },
    RuntimeSignature {
        name: "clean_ctor_get_uint8",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::UInt8,
    },
    RuntimeSignature {
        name: "clean_ctor_get_uint16",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::UInt16,
    },
    RuntimeSignature {
        name: "clean_ctor_get_uint32",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::UInt32,
    },
    RuntimeSignature {
        name: "clean_ctor_get_uint64",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::UInt64,
    },
    RuntimeSignature {
        name: "clean_ctor_get_usize",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::USize,
    },
    RuntimeSignature {
        name: "clean_ctor_get_float",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::Float64,
    },
    RuntimeSignature {
        name: "clean_ctor_get_float32",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::Float32,
    },
    RuntimeSignature {
        name: "clean_ctor_set_uint8",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_ctor_set_uint16",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_ctor_set_uint32",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_ctor_set_uint64",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_ctor_set_usize",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_ctor_set_float",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_ctor_set_float32",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_ctor_set_tag",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_is_exclusive",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Bool,
    },
    RuntimeSignature {
        name: "clean_alloc_ctor",
        fixed_arity: 3,
        variadic: true,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_alloc_ctor_uninit",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_reset",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_reuse",
        fixed_arity: 4,
        variadic: true,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_alloc_closure",
        fixed_arity: 3,
        variadic: true,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_0",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_1",
        fixed_arity: 2,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_2",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_3",
        fixed_arity: 4,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_4",
        fixed_arity: 5,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_5",
        fixed_arity: 6,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_6",
        fixed_arity: 7,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_7",
        fixed_arity: 8,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_8",
        fixed_arity: 9,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_apply_n",
        fixed_arity: 3,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_mk_string",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Object,
    },
    RuntimeSignature {
        name: "clean_panic",
        fixed_arity: 1,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_runtime_init",
        fixed_arity: 0,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
    RuntimeSignature {
        name: "clean_runtime_finalize",
        fixed_arity: 0,
        variadic: false,
        return_type: RuntimeReturnType::Void,
    },
];

/// Verify a declaration's C-backed extern entries against the known runtime ABI.
///
/// Entries for non-C backends are ignored here because this verifier is scoped
/// specifically to the C runtime boundary.
pub fn verify_extern_signature(
    decl_name: &Name,
    params: &[Param],
    return_ty: &Expr,
    extern_data: &ExternBindingData,
) -> Result<(), FfiMismatch> {
    let return_ir_type = expr_to_ir_type(return_ty).ok();
    let found_return = format_decl_return_type(return_ty, return_ir_type.as_ref());

    for entry in extern_data
        .entries
        .iter()
        .filter(|entry| is_c_backend(&entry.backend))
    {
        let Some(signature) = lookup_runtime_signature(&entry.name) else {
            return Err(FfiMismatch::UnknownExtern {
                decl: decl_name.clone(),
                backend: entry.backend.clone(),
                extern_name: entry.name.clone(),
            });
        };

        if !signature.matches_arity(params.len()) {
            return Err(FfiMismatch::ArityMismatch {
                decl: decl_name.clone(),
                backend: entry.backend.clone(),
                extern_name: entry.name.clone(),
                expected: signature.expected_arity(),
                found: params.len(),
            });
        }

        if !signature
            .return_type
            .is_compatible_with(return_ir_type.as_ref())
        {
            return Err(FfiMismatch::TypeMismatch {
                decl: decl_name.clone(),
                backend: entry.backend.clone(),
                extern_name: entry.name.clone(),
                expected: signature.return_type.as_str().to_owned(),
                found: found_return.clone(),
            });
        }
    }

    Ok(())
}

fn is_c_backend(backend: &str) -> bool {
    backend.eq_ignore_ascii_case("c") || backend.eq_ignore_ascii_case("all")
}

fn lookup_runtime_signature(name: &str) -> Option<RuntimeSignature> {
    RUNTIME_SIGNATURES
        .iter()
        .copied()
        .find(|signature| signature.name == name)
}

fn format_decl_return_type(return_ty: &Expr, return_ir_type: Option<&IRType>) -> String {
    match return_ir_type {
        Some(ir_type) => format!("{ir_type:?}"),
        None => format!("{return_ty:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lcnf::{ExternAttr, ExternEntry};
    use clean_kernel::FVarId;

    fn name(s: &str) -> Name {
        Name::from_string(s)
    }

    fn fvar(n: u64) -> FVarId {
        FVarId::new(n)
    }

    fn param(n: u64) -> Param {
        Param::new(fvar(n), name(&format!("x{n}")), Expr::const_str("Nat"))
    }

    fn extern_data(backend: &str, extern_name: &str) -> ExternBindingData {
        ExternAttr {
            entries: vec![ExternEntry {
                backend: backend.to_owned(),
                name: extern_name.to_owned(),
            }],
        }
    }

    #[test]
    fn test_verify_extern_signature_accepts_void_to_unit() {
        let result = verify_extern_signature(
            &name("init"),
            &[],
            &Expr::const_str("Unit"),
            &extern_data("c", "clean_runtime_init"),
        );

        assert!(result.is_ok(), "void Unit extern should verify: {result:?}");
    }

    #[test]
    fn test_verify_extern_signature_accepts_known_object_return() {
        let result = verify_extern_signature(
            &name("reset"),
            &[param(0)],
            &Expr::const_str("Nat"),
            &extern_data("c", "clean_reset"),
        );

        assert!(
            result.is_ok(),
            "object-return extern should verify: {result:?}"
        );
    }

    #[test]
    fn test_verify_extern_signature_reports_unknown_extern() {
        let err = verify_extern_signature(
            &name("mystery"),
            &[],
            &Expr::const_str("Unit"),
            &extern_data("c", "clean_missing_symbol"),
        )
        .expect_err("unknown runtime symbol should fail");

        assert!(matches!(
            err,
            FfiMismatch::UnknownExtern { extern_name, .. } if extern_name == "clean_missing_symbol"
        ));
    }

    #[test]
    fn test_verify_extern_signature_reports_arity_mismatch() {
        let err = verify_extern_signature(
            &name("inc_n"),
            &[param(0)],
            &Expr::const_str("Unit"),
            &extern_data("c", "clean_inc_n"),
        )
        .expect_err("wrong arity should fail");

        assert!(matches!(
            err,
            FfiMismatch::ArityMismatch { ref expected, found, .. }
                if expected == "2" && found == 1
        ));
    }

    #[test]
    fn test_verify_extern_signature_reports_type_mismatch() {
        let err = verify_extern_signature(
            &name("inc"),
            &[param(0)],
            &Expr::const_str("USize"),
            &extern_data("c", "clean_inc"),
        )
        .expect_err("void vs USize should fail");

        assert!(matches!(
            err,
            FfiMismatch::TypeMismatch { ref expected, ref found, .. }
                if expected == "void" && found == "USize"
        ));
    }

    #[test]
    fn test_verify_extern_signature_skips_non_c_entries() {
        let result = verify_extern_signature(
            &name("llvm_only"),
            &[param(0)],
            &Expr::const_str("Bool"),
            &extern_data("llvm", "not_a_c_runtime_symbol"),
        );

        assert!(
            result.is_ok(),
            "non-C externs should be ignored: {result:?}"
        );
    }
}
