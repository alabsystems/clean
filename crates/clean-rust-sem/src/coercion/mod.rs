// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implicit type coercion for Rust semantics.
//!
//! Implements the coercion rules from the Rust Reference:
//! <https://doc.rust-lang.org/reference/type-coercions.html>
//!
//! Coercion sites include function arguments, let bindings with type
//! annotations, struct field initializers, and return expressions.
//! This module provides the type-level query (`try_coerce`) and the
//! value-level transform (`coerce_value`).

#[cfg(test)]
mod dyn_trait_unsize_tests;
#[cfg(test)]
mod tests;
mod trait_object_unsize;

use crate::types::{Mutability, RustType};
use crate::values::{FatPointer, Value};

/// The kind of implicit coercion applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoercionKind {
    /// `&mut T` → `&T`: mutability weakening (reborrow).
    MutToSharedRef,

    /// Deref coercion through a known `Deref` impl:
    /// `&String` → `&str`, `&Vec<T>` → `&[T]`, `&Box<T>` → `&T`.
    DerefCoercion {
        /// Name of the source type that implements `Deref`.
        source: String,
    },

    /// `&[T; N]` → `&[T]`: array-to-slice unsizing.
    UnsizeArrayToSlice,

    /// Pointer unsizing to a trait object: `&T`/`&mut T`/`Box<T>` →
    /// `&dyn Trait`/`&mut dyn Trait`/`Box<dyn Trait>`.
    /// Runtime trait-object materialization lives in `runtime_coercion.rs`.
    UnsizeToDynTrait,

    /// `&T` → `*const T`, `&mut T` → `*mut T`: reference to raw pointer.
    RefToRawPtr,

    /// `*mut T` → `*const T`: mutable raw pointer weakening.
    MutPtrToConstPtr,

    /// `!` → any type: the never type coerces to everything.
    NeverToAny,

    /// `Fn` closure → `FnMut` or `FnOnce`, etc.
    ClosureKindUpcast,

    /// Non-capturing closure → `fn()` pointer.
    ///
    /// A closure with an empty capture list can be coerced to a function pointer
    /// with matching parameter and return types.
    ClosureToFnPtr,

    /// A chain of two or more coercions applied in sequence.
    Transitive(Vec<CoercionKind>),
}

/// Determine whether `from` can be implicitly coerced to `to`.
///
/// Returns `Some(kind)` describing the coercion, or `None` if no
/// implicit coercion is available.
pub fn try_coerce(from: &RustType, to: &RustType) -> Option<CoercionKind> {
    if from == to || from.is_compatible(to) {
        return None;
    }

    if matches!(from, RustType::Never) {
        return Some(CoercionKind::NeverToAny);
    }

    if let Some(kind) = try_coerce_reference(from, to) {
        return Some(kind);
    }

    if let Some(kind) = trait_object_unsize::try_coerce_box_unsize(from, to) {
        return Some(kind);
    }

    if let Some(kind) = try_coerce_raw_ptr(from, to) {
        return Some(kind);
    }

    if let Some(kind) = try_coerce_closure(from, to) {
        return Some(kind);
    }

    try_coerce_closure_to_fn_ptr(from, to)
}

/// Reference-to-reference coercions: mutability weakening, deref, unsizing.
fn try_coerce_reference(from: &RustType, to: &RustType) -> Option<CoercionKind> {
    // &mut T → &T  (mutability weakening)
    if let (
        RustType::Reference {
            mutability: Mutability::Mutable,
            inner: from_inner,
            ..
        },
        RustType::Reference {
            mutability: Mutability::Shared,
            inner: to_inner,
            ..
        },
    ) = (from, to)
    {
        if from_inner == to_inner || from_inner.is_compatible(to_inner) {
            return Some(CoercionKind::MutToSharedRef);
        }
    }

    // Deref coercions: &String→&str, &Vec<T>→&[T], &Box<T>→&T
    if let (
        RustType::Reference {
            mutability: from_mutability,
            inner: src,
            ..
        },
        RustType::Reference {
            mutability: target_mutability,
            inner: dst,
            ..
        },
    ) = (from, to)
    {
        if let Some(kind) = try_deref_coerce(src, dst, *from_mutability, *target_mutability) {
            return Some(kind);
        }
    }

    // &[T; N] → &[T]  (array-to-slice unsizing)
    if let (
        RustType::Reference {
            mutability: from_mut,
            inner: from_inner,
            ..
        },
        RustType::Reference {
            mutability: to_mut,
            inner: to_inner,
            ..
        },
    ) = (from, to)
    {
        if let (RustType::Array { element: e1, .. }, RustType::Slice { elem: e2 }) =
            (from_inner.as_ref(), to_inner.as_ref())
        {
            // Shared target is always fine; mutable target requires mutable source.
            let mutability_ok = *to_mut == Mutability::Shared || *from_mut == Mutability::Mutable;
            if mutability_ok && (e1 == e2 || e1.is_compatible(e2)) {
                return Some(CoercionKind::UnsizeArrayToSlice);
            }
        }
    }

    if let Some(kind) = trait_object_unsize::try_coerce_ref_to_dyn_trait(from, to) {
        return Some(kind);
    }

    None
}

/// Raw-pointer coercions: &T→*const T, &mut T→*mut T, *mut T→*const T.
fn try_coerce_raw_ptr(from: &RustType, to: &RustType) -> Option<CoercionKind> {
    // &T → *const T, &mut T → *mut T
    if let (
        RustType::Reference {
            mutability: ref_mut,
            inner: ref_inner,
            ..
        },
        RustType::RawPtr {
            mutability: ptr_mut,
            inner: ptr_inner,
        },
    ) = (from, to)
    {
        if ref_inner == ptr_inner || ref_inner.is_compatible(ptr_inner) {
            let ok = matches!(
                (ref_mut, ptr_mut),
                (Mutability::Shared, Mutability::Shared)
                    | (Mutability::Mutable, Mutability::Mutable)
                    | (Mutability::Mutable, Mutability::Shared)
            );
            if ok {
                return Some(CoercionKind::RefToRawPtr);
            }
        }
    }

    // *mut T → *const T
    if let (
        RustType::RawPtr {
            mutability: Mutability::Mutable,
            inner: from_inner,
        },
        RustType::RawPtr {
            mutability: Mutability::Shared,
            inner: to_inner,
        },
    ) = (from, to)
    {
        if from_inner == to_inner || from_inner.is_compatible(to_inner) {
            return Some(CoercionKind::MutPtrToConstPtr);
        }
    }

    None
}

/// Closure kind upcast: Fn → FnMut, Fn → FnOnce, FnMut → FnOnce.
fn try_coerce_closure(from: &RustType, to: &RustType) -> Option<CoercionKind> {
    if let (
        RustType::Closure {
            kind: from_kind,
            params: from_params,
            ret: from_ret,
            ..
        },
        RustType::Closure {
            kind: to_kind,
            params: to_params,
            ret: to_ret,
            ..
        },
    ) = (from, to)
    {
        if from_kind != to_kind
            && from_kind.can_coerce_to(*to_kind)
            && from_params == to_params
            && from_ret == to_ret
        {
            return Some(CoercionKind::ClosureKindUpcast);
        }
    }
    None
}

/// Non-capturing closure → fn pointer: `|| 42` → `fn() -> i32`.
fn try_coerce_closure_to_fn_ptr(from: &RustType, to: &RustType) -> Option<CoercionKind> {
    if let (
        RustType::Closure {
            params: from_params,
            ret: from_ret,
            captures,
            ..
        },
        RustType::Function {
            params: to_params,
            ret: to_ret,
        },
    ) = (from, to)
    {
        if captures.is_empty() && from_params == to_params && from_ret.as_ref() == to_ret.as_ref() {
            return Some(CoercionKind::ClosureToFnPtr);
        }
    }
    None
}

/// Deref coercion between the *inner* types of two references.
fn try_deref_coerce(
    src: &RustType,
    dst: &RustType,
    from_ref_mutability: Mutability,
    target_ref_mutability: Mutability,
) -> Option<CoercionKind> {
    // String → str
    if is_string_type(src)
        && matches!(dst, RustType::Str)
        && deref_mutability_allows(
            DerefMutabilitySupport::Mutable,
            from_ref_mutability,
            target_ref_mutability,
        )
    {
        return Some(CoercionKind::DerefCoercion {
            source: "String".to_string(),
        });
    }

    // Vec<T> → [T]
    if let (RustType::Vec { element: ve }, RustType::Slice { elem: se }) = (src, dst) {
        if (ve == se || ve.is_compatible(se))
            && deref_mutability_allows(
                DerefMutabilitySupport::Mutable,
                from_ref_mutability,
                target_ref_mutability,
            )
        {
            return Some(CoercionKind::DerefCoercion {
                source: "Vec".to_string(),
            });
        }
    }

    // Box<T> / Rc<T> / Arc<T> → T, plus chained deref like Rc<String> → str.
    if let Some((source, inner, support)) = smart_pointer_inner(src) {
        if !deref_mutability_allows(support, from_ref_mutability, target_ref_mutability) {
            return None;
        }
        if inner == dst || inner.is_compatible(dst) {
            return Some(CoercionKind::DerefCoercion {
                source: source.to_string(),
            });
        }
        if let Some(next) = try_deref_coerce(inner, dst, from_ref_mutability, target_ref_mutability)
        {
            return Some(prepend_deref_step(source, next));
        }
        if let Some(kind) = trait_object_unsize::try_deref_unsize_to_dyn_trait(
            inner,
            dst,
            from_ref_mutability,
            target_ref_mutability,
        ) {
            return Some(prepend_deref_step(source, kind));
        }
    }

    None
}

fn is_string_type(ty: &RustType) -> bool {
    matches!(
        ty,
        RustType::Named { name, .. } if name == "String" || name == "std::string::String"
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DerefMutabilitySupport {
    SharedOnly,
    Mutable,
}

fn deref_mutability_allows(
    support: DerefMutabilitySupport,
    from_ref_mutability: Mutability,
    target_ref_mutability: Mutability,
) -> bool {
    match target_ref_mutability {
        Mutability::Shared => true,
        Mutability::Mutable => {
            from_ref_mutability == Mutability::Mutable && support == DerefMutabilitySupport::Mutable
        }
    }
}

fn smart_pointer_inner(ty: &RustType) -> Option<(&'static str, &RustType, DerefMutabilitySupport)> {
    match ty {
        RustType::Box { inner } => Some(("Box", inner.as_ref(), DerefMutabilitySupport::Mutable)),
        RustType::Named {
            name, type_args, ..
        } if matches!(name.as_str(), "Rc" | "std::rc::Rc" | "alloc::rc::Rc")
            && type_args.len() == 1 =>
        {
            Some(("Rc", &type_args[0], DerefMutabilitySupport::SharedOnly))
        }
        RustType::Named {
            name, type_args, ..
        } if matches!(name.as_str(), "Arc" | "std::sync::Arc" | "alloc::sync::Arc")
            && type_args.len() == 1 =>
        {
            Some(("Arc", &type_args[0], DerefMutabilitySupport::SharedOnly))
        }
        _ => None,
    }
}

fn prepend_deref_step(source: &str, next: CoercionKind) -> CoercionKind {
    let mut steps = vec![CoercionKind::DerefCoercion {
        source: source.to_string(),
    }];
    match next {
        CoercionKind::Transitive(rest) => steps.extend(rest),
        kind => steps.push(kind),
    }
    CoercionKind::Transitive(steps)
}

/// Apply an implicit coercion to a runtime value.
///
/// Returns `Some(coerced_value)` if the coercion succeeds, or `None`
/// if the value cannot be coerced (type mismatch at runtime).
pub fn coerce_value(value: &Value, from: &RustType, to: &RustType) -> Option<Value> {
    let kind = try_coerce(from, to)?;
    if matches!(kind, CoercionKind::UnsizeArrayToSlice) {
        return apply_array_to_slice_unsize(value, from, to);
    }
    apply_coercion(value, &kind, to)
}

fn apply_coercion(value: &Value, kind: &CoercionKind, target: &RustType) -> Option<Value> {
    match kind {
        CoercionKind::NeverToAny => Some(value.clone()),

        CoercionKind::MutToSharedRef => apply_mut_to_shared(value),

        CoercionKind::DerefCoercion { source } => apply_deref_coercion(value, source, target),

        CoercionKind::UnsizeArrayToSlice => None,

        // Trait-object materialization needs trait impl metadata, so the evaluator handles it.
        CoercionKind::UnsizeToDynTrait => None,

        CoercionKind::RefToRawPtr => apply_ref_to_raw_ptr(value, target),

        CoercionKind::MutPtrToConstPtr => apply_mut_ptr_to_const(value),

        CoercionKind::ClosureKindUpcast | CoercionKind::ClosureToFnPtr => Some(value.clone()),

        CoercionKind::Transitive(steps) => {
            let mut current = value.clone();
            for step in steps {
                current = apply_coercion(&current, step, target)?;
            }
            Some(current)
        }
    }
}

fn apply_mut_to_shared(value: &Value) -> Option<Value> {
    if let Value::Reference {
        addr,
        lifetime,
        referent,
        ..
    } = value
    {
        Some(Value::Reference {
            addr: *addr,
            mutability: Mutability::Shared,
            lifetime: lifetime.clone(),
            referent: referent.clone(),
        })
    } else {
        None
    }
}

fn apply_ref_to_raw_ptr(value: &Value, target: &RustType) -> Option<Value> {
    if let Value::Reference { addr, .. } = value {
        let ptr_mut = match target {
            RustType::RawPtr { mutability, .. } => *mutability,
            _ => Mutability::Shared,
        };
        Some(Value::RawPtr {
            addr: *addr,
            mutability: ptr_mut,
            tag: None,
        })
    } else {
        None
    }
}

fn apply_mut_ptr_to_const(value: &Value) -> Option<Value> {
    if let Value::RawPtr { addr, .. } = value {
        Some(Value::RawPtr {
            addr: *addr,
            mutability: Mutability::Shared,
            tag: None,
        })
    } else {
        None
    }
}

fn apply_deref_coercion(value: &Value, _source: &str, target: &RustType) -> Option<Value> {
    if let Value::Reference {
        addr,
        lifetime,
        referent,
        ..
    } = value
    {
        let target_mut = match target {
            RustType::Reference { mutability, .. } => *mutability,
            _ => Mutability::Shared,
        };
        Some(Value::Reference {
            addr: *addr,
            mutability: target_mut,
            lifetime: lifetime.clone(),
            referent: referent.clone(),
        })
    } else {
        None
    }
}

fn apply_array_to_slice_unsize(
    value: &Value,
    source: &RustType,
    target: &RustType,
) -> Option<Value> {
    let Value::Reference { addr, referent, .. } = value else {
        return None;
    };
    let RustType::Reference {
        lifetime,
        mutability,
        ..
    } = target
    else {
        return None;
    };
    let len = match referent.as_deref() {
        Some(Value::Array(values)) => values.len(),
        _ => match source {
            RustType::Reference {
                inner: array_ty, ..
            } => match array_ty.as_ref() {
                RustType::Array { len, .. } => len.as_usize(&std::collections::HashMap::new())?,
                _ => return None,
            },
            _ => return None,
        },
    };
    Some(Value::FatPtr(FatPointer::slice(
        Value::Reference {
            addr: *addr,
            mutability: *mutability,
            lifetime: lifetime.clone(),
            referent: referent.clone(),
        },
        len,
    )))
}

/// Check whether `from` is coercible to `to` (type-level predicate).
pub fn is_coercible(from: &RustType, to: &RustType) -> bool {
    from == to || from.is_compatible(to) || try_coerce(from, to).is_some()
}
