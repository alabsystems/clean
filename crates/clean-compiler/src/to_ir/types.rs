// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type conversion from kernel `Expr` types to `IRType`.

use crate::error::CompilerError;
use crate::ir::IRType;
use clean_kernel::name::NameInner;
use clean_kernel::{Expr, ExprKind, Name};

/// Convert a kernel Expr type to an IRType.
///
/// This is a simplified version that handles common cases.
/// A full implementation would require environment access for inductive info.
pub fn expr_to_ir_type(expr: &Expr) -> Result<IRType, CompilerError> {
    // Strip metadata and get the head of applications
    let head = expr.strip_mdata().get_app_fn();

    match head.kind() {
        // Synthetic "_" placeholders are not runtime types and must keep the
        // fail-closed boundary from #2826.
        ExprKind::Const(name, _) if is_placeholder_type_name(name) => {
            Err(CompilerError::UnsupportedIrType {
                expr: format!("{expr:?}"),
            })
        }
        ExprKind::Const(name, _) => Ok(name_to_ir_type(name)),
        ExprKind::BVar(_) | ExprKind::FVar(_) => Ok(IRType::Object),
        // SOUNDNESS: A field whose TYPE is a function (`Pi`, e.g. `α → β` or
        // `α → α → Prop`) is represented at runtime by a boxed closure, so it
        // lowers to `IRType::Object`. This MUST match LCNF erasure, because the
        // `field_types` vector is reconciled against the LCNF constructor args
        // by `align_ctor_field_types` (to_ir/code.rs) and the resulting
        // object/scalar counts drive the byte/object offsets computed in
        // `compute_proj_expr` (to_ir/code.rs). A misclassified field shifts
        // `num_objects`/`num_scalars` and corrupts projection layout.
        //
        // LCNF (`to_lcnf/lower.rs::classify_expr_arg`) erases an arg only when
        // its INFERRED TYPE is a Prop/SProp (a proof), a bare `Sort` (a type),
        // or a singleton. A function VALUE of type `α → … → β` or
        // `α → … → Prop` has a function (`Pi`) type, which is none of those, so
        // LCNF classifies it `Normal` and keeps it as a real runtime arg.
        // Empirically all 41 previously-rejected prelude constructors carry
        // function-typed fields of exactly this shape: 124 function-value
        // fields plus 2 type-family fields (`LT.lt`/`LE.lt : α → α → Prop`).
        // LCNF keeps every one of them, so `Object` (never `Erased`) is the
        // layout-safe classification — erasing a field LCNF retains would drop
        // it from `num_objects` while the LCNF arg list still carries it.
        // Mirrors the existing treatment of proof-typed fields (e.g. `h : a = b`,
        // type head `Const("Eq")`), which already lower to `Object` via
        // `name_to_ir_type`'s `_` arm. Part of Phase 0 #1.
        ExprKind::Pi(_, _, _) => Ok(IRType::Object),
        _ => Err(CompilerError::UnsupportedIrType {
            expr: format!("{expr:?}"),
        }),
    }
}

/// Convert a kernel Expr type to an IRType in RETURN position (a decl's
/// result type). C4: uniform boxed lowering for polymorphic/dependent shapes.
///
/// Return position is pure CALLING CONVENTION: unlike constructor-field types
/// (`ctor_env`), a decl's return type never feeds the `num_scalars` /
/// `num_objects` layout counts that drive projection offsets, so the #2826
/// layout-soundness concern does not apply here. Everything non-scalar is a
/// managed pointer downstream (`emit_trust_ir::lower_ty` maps `Object` to
/// `Ptr`), and the trust-ir validator independently re-checks every `Return`
/// against the emitted signature, so a wrong claim here is REFUSED, never
/// silently miscompiled (the fail-closed backstop C2b's return alignment
/// builds on).
///
/// Accepted shapes beyond [`expr_to_ir_type`]:
///
/// * The synthetic `_` placeholder. It is produced exactly where LCNF's
///   kernel-type inference fails on an OPEN term — `infer_type_or_placeholder`
///   on a lifted local function's body (`to_lcnf/lower.rs`), i.e. the
///   `casesOn`/`recOn` motive minor premises and field-access lambdas
///   (`Array.data`-class) whose result type mentions binders the kernel
///   checker cannot see. Those lambdas were classified `Normal` (runtime
///   values) by LCNF — proof- and type-valued args are erased before
///   `expr_to_local_fun` runs — and lifted closures use the boxed calling
///   convention, so `Object` is the faithful signature. In VALUE positions
///   (params, ctor fields) `_` stays fail-closed rejected: there a
///   misclassification can shift scalar/object layout (#2826).
/// * Dependent type-expression heads that denote a runtime type but are not
///   in head-normal form: a beta-unreduced motive application
///   (`(fun x => T) a`, head `Lam`), a type-level structure projection
///   (head `Proj`), or a type-level `let` (head `Let`). All are
///   Object-representable for the same reason as the `BVar`/`FVar`/`Pi`
///   arms of [`expr_to_ir_type`].
///
/// `Sort`-/`SProp`-valued shapes still ERROR via the strict fallthrough: a
/// decl returning a type is type-level machinery that C3 erases at LCNF; one
/// reaching this point is a lowering bug and must keep failing closed.
pub(crate) fn expr_to_ir_type_return(expr: &Expr) -> Result<IRType, CompilerError> {
    let head = expr.strip_mdata().get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) if is_placeholder_type_name(name) => Ok(IRType::Object),
        ExprKind::Lam(_, _, _) | ExprKind::Proj(_, _, _) | ExprKind::Let(_, _, _, _, _) => {
            Ok(IRType::Object)
        }
        _ => expr_to_ir_type(expr),
    }
}

fn is_placeholder_type_name(name: &Name) -> bool {
    matches!(
        name.inner(),
        NameInner::Str(prefix, component) if prefix.is_anon() && component.as_ref() == "_"
    )
}

/// Convert a type name to IRType.
pub(crate) fn name_to_ir_type(name: &Name) -> IRType {
    let s = name.to_string();
    match s.as_str() {
        "Bool" => IRType::Bool,
        "Char" => IRType::UInt32,
        "UInt8" => IRType::UInt8,
        "UInt16" => IRType::UInt16,
        "UInt32" => IRType::UInt32,
        "UInt64" => IRType::UInt64,
        "USize" => IRType::USize,
        "Float" | "Float64" => IRType::Float64,
        "Float32" => IRType::Float32,
        "Unit" | "PUnit" => IRType::Erased,
        "Nat" | "Int" | "String" => IRType::Object,
        _ => IRType::Object,
    }
}
