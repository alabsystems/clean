// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared pattern and type helper functions for VIR lowering.

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::expr::{Expr, Pattern};
use crate::ownership::Place;
use crate::types::RustType;

pub(super) fn pattern_is_irrefutable(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Wildcard | Pattern::Rest => true,
        Pattern::Binding {
            subpattern: None, ..
        } => true,
        Pattern::Binding {
            subpattern: Some(subpattern),
            ..
        }
        | Pattern::Ref {
            pattern: subpattern,
            ..
        } => pattern_is_irrefutable(subpattern),
        Pattern::Tuple(patterns) => patterns.iter().all(pattern_is_irrefutable),
        Pattern::Struct { fields, .. } => fields
            .iter()
            .all(|(_, subpat)| pattern_is_irrefutable(subpat)),
        Pattern::Slice(patterns) => patterns.iter().all(pattern_is_irrefutable),
        _ => false,
    }
}

pub(super) fn pattern_contains_binding(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Binding { .. } => true,
        Pattern::Ref { pattern, .. } => pattern_contains_binding(pattern),
        Pattern::Tuple(patterns) => patterns.iter().any(pattern_contains_binding),
        Pattern::Struct { fields, .. } => fields
            .iter()
            .any(|(_, subpat)| pattern_contains_binding(subpat)),
        Pattern::EnumVariant { payload, .. } => match payload {
            crate::expr::EnumPatternPayload::Unit => false,
            crate::expr::EnumPatternPayload::Tuple(patterns) => {
                patterns.iter().any(pattern_contains_binding)
            }
            crate::expr::EnumPatternPayload::Struct(fields) => fields
                .iter()
                .any(|(_, subpat)| pattern_contains_binding(subpat)),
        },
        Pattern::Or(alternatives) | Pattern::Slice(alternatives) => {
            alternatives.iter().any(pattern_contains_binding)
        }
        _ => false,
    }
}

pub(super) fn nominal_type_name(ty: &RustType) -> Option<String> {
    match ty {
        RustType::Named { name, .. } => Some(name.clone()),
        RustType::Option { .. } => Some("Option".to_string()),
        RustType::Result { .. } => Some("Result".to_string()),
        RustType::Vec { .. } => Some("Vec".to_string()),
        RustType::Reference { inner, .. }
        | RustType::RawPtr { inner, .. }
        | RustType::Box { inner }
        | RustType::Pin { inner } => nominal_type_name(inner),
        _ => None,
    }
}

/// Synthetic field schema for built-in nominal collection types.
///
/// Built-in collection types (`Vec<T>`, …) carry no user-supplied `struct_fields`
/// entry. To support the source-to-VIR field-projection path (`v.len`, …) the
/// lowering recognizes a small set of well-known fields and returns a type
/// parameterized on the collection's element type. This is a synthetic model,
/// not a faithful reflection of `std::vec::Vec`'s real (private) layout — it
/// exists to give NLL conflict checking a typed place-projection target on
/// the same axis that user structs use.
///
/// Returns `None` for unknown (type, field) pairs so the caller can fall back
/// to the standard MissingType error path.
pub(super) fn builtin_collection_field_type(base_ty: &RustType, field: &str) -> Option<RustType> {
    match base_ty {
        RustType::Vec { element } => match field {
            // `Vec<T>` exposes a synthetic `len` field typed as the element
            // type, matching the test-model convention used by source-to-VIR
            // NLL fixtures (`Vec { len: 3u32 }` with `v.len: T`).
            "len" => Some((**element).clone()),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn autoderef_place_to_expected_inner(
    ctx: &mut FunctionLoweringContext<'_>,
    receiver_expr: &Expr,
    expected_inner: &RustType,
) -> Result<Place, VirLoweringError> {
    let mut place = ctx.lower_place_or_temp(receiver_expr)?;
    loop {
        let place_ty = ctx.place_type(&place)?;
        if place_ty == *expected_inner || place_ty.is_compatible(expected_inner) {
            return Ok(place);
        }
        match place_ty {
            RustType::Reference { .. } | RustType::Box { .. } | RustType::Pin { .. } => {
                place = Place::Deref(Box::new(place));
            }
            other => {
                return Err(VirLoweringError::Unsupported {
                    context: "method receiver",
                    detail: format!(
                        "cannot autoderef receiver `{receiver_expr:?}` of type `{other:?}` to `{expected_inner:?}`"
                    ),
                });
            }
        }
    }
}

pub(super) fn autoderef_projection_base(
    ctx: &mut FunctionLoweringContext<'_>,
    base_expr: &Expr,
) -> Result<Place, VirLoweringError> {
    let mut place = ctx.lower_place_or_temp(base_expr)?;
    // Field and index syntax auto-deref references/Box values, but raw pointers
    // still require an explicit deref in the semantic AST.
    while matches!(
        ctx.place_type(&place)?,
        RustType::Reference { .. } | RustType::Box { .. } | RustType::Pin { .. }
    ) {
        place = Place::Deref(Box::new(place));
    }
    Ok(place)
}

pub(super) fn projected_field_type(
    ctx: &FunctionLoweringContext<'_>,
    base_ty: &RustType,
    field: &str,
    base_repr: &str,
) -> Result<RustType, VirLoweringError> {
    match base_ty {
        RustType::Tuple(field_tys) => {
            tuple_field_type(field_tys, field, ctx.function_name, base_repr)
        }
        RustType::Reference { inner, .. }
        | RustType::RawPtr { inner, .. }
        | RustType::Box { inner }
        | RustType::Pin { inner } => projected_field_type(ctx, inner, field, base_repr),
        _ => {
            let type_name =
                nominal_type_name(base_ty).ok_or_else(|| VirLoweringError::MissingType {
                    context: format!("field base `{base_repr}` in `{}`", ctx.function_name),
                })?;
            if let Some(ty) = ctx.field_type(&type_name, field).cloned() {
                return Ok(ty);
            }
            // Built-in nominal collections (`Vec<T>`, …) have no
            // user-registered field schema; consult the synthetic
            // builtin schema before reporting MissingType.
            if let Some(ty) = builtin_collection_field_type(base_ty, field) {
                return Ok(ty);
            }
            Err(VirLoweringError::MissingType {
                context: format!(
                    "field `{field}` on `{type_name}` in `{}`",
                    ctx.function_name
                ),
            })
        }
    }
}

pub(super) fn indexed_element_type(ty: RustType) -> Option<RustType> {
    match ty {
        RustType::Array { element, .. }
        | RustType::Slice { elem: element }
        | RustType::Vec { element } => Some(*element),
        RustType::Reference { inner, .. }
        | RustType::RawPtr { inner, .. }
        | RustType::Box { inner }
        | RustType::Pin { inner } => indexed_element_type(*inner),
        _ => None,
    }
}

pub(super) fn type_is_index(ty: &RustType) -> bool {
    matches!(ty, RustType::Uint(_) | RustType::Int(_))
}

/// True if `ty` is one of the standard range types used as an index to slice a
/// container (`a[1..3]`, `a[..]`, `a[2..]`, `a[..5]`, `a[1..=3]`).
///
/// Slicing by a range yields a slice `[T]` rather than a single element `T`, and
/// for borrow-checking purposes touches the *whole* container (the `Index::index`
/// call takes `&self`). Detecting the range index lets the slice path
/// over-approximate the borrowed place to the entire base.
pub(super) fn type_is_range(ty: &RustType) -> bool {
    matches!(
        ty,
        RustType::Named { name, .. }
            if matches!(
                name.as_str(),
                "Range" | "RangeFrom" | "RangeTo" | "RangeFull" | "RangeInclusive"
            )
    )
}

/// The slice element type produced by indexing into `ty`, used by the
/// range-slicing path. Mirrors [`indexed_element_type`] but is named for the
/// slice result so call sites read clearly.
pub(super) fn sliced_element_type(ty: RustType) -> Option<RustType> {
    indexed_element_type(ty)
}

fn tuple_field_type(
    field_tys: &[RustType],
    field: &str,
    function_name: &str,
    base_repr: &str,
) -> Result<RustType, VirLoweringError> {
    let index = field
        .parse::<usize>()
        .map_err(|_| VirLoweringError::Unsupported {
            context: "tuple field",
            detail: format!(
                "tuple field `{field}` on `{base_repr}` in `{function_name}` is not a numeric index"
            ),
        })?;
    field_tys
        .get(index)
        .cloned()
        .ok_or_else(|| VirLoweringError::MissingType {
            context: format!("tuple field `{field}` on `{base_repr}` in `{function_name}`"),
        })
}
