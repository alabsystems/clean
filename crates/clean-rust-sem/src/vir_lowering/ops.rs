// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pure helpers for VIR lowering operations and constants.

use super::VirLoweringError;
use crate::types::{FloatType, RustType, UintType};
use crate::values::{BinOp as ExprBinOp, EnumPayload, UnOp as ExprUnOp, Value};
use crate::vir::{
    AggregateConst, BinOp as VirBinOp, CastKind, ConstAggregateKind, Constant, ScalarValue,
    UnOp as VirUnOp,
};

pub(super) fn constant_from_value(value: &Value) -> Result<Constant, VirLoweringError> {
    match value {
        Value::Unit => Ok(Constant::ZeroSized),
        Value::Bool(value) => Ok(Constant::Scalar(ScalarValue::Bool(*value))),
        Value::Char(value) => Ok(Constant::Scalar(ScalarValue::Char(*value))),
        Value::Str(value) => Ok(Constant::Str(value.clone())),
        Value::Uint { value, .. } => Ok(Constant::Scalar(ScalarValue::Uint(*value))),
        Value::Int { value, .. } => Ok(Constant::Scalar(ScalarValue::Int(*value))),
        Value::Float {
            bits,
            ty: FloatType::F32,
        } => Ok(Constant::Scalar(ScalarValue::Float32(f32::from_bits(
            *bits as u32,
        )))),
        Value::Float {
            bits,
            ty: FloatType::F64,
        } => Ok(Constant::Scalar(ScalarValue::Float64(f64::from_bits(
            *bits,
        )))),
        // Byte-string literals (`b"..."`) are represented in semantic values as
        // a fixed `Value::Array` of `u8` scalars (see `source::literals`).  In
        // MIR they lower to a dedicated `ByteStr` constant rather than an
        // aggregate, both as a value (`let x = b"ab";`) and as a match scrutinee
        // (`match s { b"ab" => ... }`), so reconstruct that here.  This is
        // sound: it only succeeds when every element is a concrete `u8` literal,
        // preserving the exact byte sequence.  Any other array (including the
        // empty array, which is a zero-length byte string) falls through to the
        // generic composite path below only when it is *not* an all-`u8` array.
        Value::Array(elements) => {
            if let Some(byte_str) = byte_string_constant(elements) {
                return Ok(byte_str);
            }
            // A non-byte fixed array of constants is itself a constant aggregate.
            // Derive the element type from the first element (every element of a
            // well-typed array shares one type); a non-byte array always has at
            // least one element, since the empty array took the byte-string path.
            let element_ty = elements.first().map_or(RustType::Unit, value_leaf_type);
            let element_constants = lower_constant_elements(elements)?;
            Ok(Constant::Aggregate(Box::new(AggregateConst::array(
                element_ty,
                element_constants,
            ))))
        }
        // Tuple literals whose elements are all constants form a constant tuple
        // aggregate, e.g. `const X: (i32, bool) = (1, true);`.
        Value::Tuple(elements) => {
            let element_constants = lower_constant_elements(elements)?;
            Ok(Constant::Aggregate(Box::new(AggregateConst::tuple(
                element_constants,
            ))))
        }
        // Struct literals whose fields are all constants form a constant struct
        // aggregate.  Field order follows the `BTreeMap` iteration order, which
        // is deterministic, and we keep field names alongside the constants so
        // consumers can reconstruct the named structure faithfully.
        Value::Struct { name, fields } => {
            let mut field_names = Vec::with_capacity(fields.len());
            let mut element_constants = Vec::with_capacity(fields.len());
            for (field_name, field_value) in fields {
                field_names.push(field_name.clone());
                element_constants.push(constant_from_value(field_value)?);
            }
            Ok(Constant::Aggregate(Box::new(AggregateConst {
                kind: ConstAggregateKind::Struct {
                    name: name.clone(),
                    field_names,
                },
                elements: element_constants,
            })))
        }
        // Enum variant literals whose payload is all constants form a constant
        // enum aggregate, e.g. `const X: Option<i32> = Some(3);`.
        Value::Enum {
            name,
            variant,
            payload,
        } => {
            let (field_names, element_constants) = match payload.as_ref() {
                EnumPayload::Unit => (Vec::new(), Vec::new()),
                EnumPayload::Tuple(elements) => (Vec::new(), lower_constant_elements(elements)?),
                EnumPayload::Struct(fields) => {
                    let mut field_names = Vec::with_capacity(fields.len());
                    let mut element_constants = Vec::with_capacity(fields.len());
                    for (field_name, field_value) in fields {
                        field_names.push(field_name.clone());
                        element_constants.push(constant_from_value(field_value)?);
                    }
                    (field_names, element_constants)
                }
            };
            Ok(Constant::Aggregate(Box::new(AggregateConst {
                kind: ConstAggregateKind::Enum {
                    name: name.clone(),
                    variant: variant.clone(),
                    field_names,
                },
                elements: element_constants,
            })))
        }
        other => Err(VirLoweringError::Unsupported {
            context: "literal",
            detail: format!("non-scalar literal lowering is not implemented for `{other:?}`"),
        }),
    }
}

/// Lower every element of a composite to a constant, propagating the first
/// unsupported element as an error.  Keeps the all-or-nothing guarantee: a
/// composite is a constant aggregate only when *all* of its components are
/// constants.
fn lower_constant_elements(elements: &[Value]) -> Result<Vec<Constant>, VirLoweringError> {
    elements.iter().map(constant_from_value).collect()
}

/// Best-effort leaf type of a value, used only to annotate the element type of
/// an array constant aggregate.  Returns the precise scalar type for scalar
/// leaves and `RustType::Unit` as a neutral placeholder for shapes that do not
/// carry their own type tag; this is metadata only and never affects the
/// materialized constant values.
fn value_leaf_type(value: &Value) -> RustType {
    match value {
        Value::Bool(_) => RustType::Bool,
        Value::Char(_) => RustType::Char,
        Value::Uint { ty, .. } => RustType::Uint(*ty),
        Value::Int { ty, .. } => RustType::Int(*ty),
        Value::Float { ty, .. } => RustType::Float(*ty),
        _ => RustType::Unit,
    }
}

/// Reconstruct a byte-string constant from an array literal whose elements are
/// all concrete `u8` scalars in range.  Returns `None` for any non-byte array,
/// so the caller can reject genuinely unsupported composite literals.
fn byte_string_constant(elements: &[Value]) -> Option<Constant> {
    let mut bytes = Vec::with_capacity(elements.len());
    for element in elements {
        match element {
            Value::Uint {
                value,
                ty: UintType::U8,
            } if *value <= u128::from(u8::MAX) => bytes.push(*value as u8),
            _ => return None,
        }
    }
    Some(Constant::ByteStr(bytes))
}

pub(super) fn lower_bin_op(op: ExprBinOp) -> VirBinOp {
    match op {
        ExprBinOp::Add => VirBinOp::Add,
        ExprBinOp::Sub => VirBinOp::Sub,
        ExprBinOp::Mul => VirBinOp::Mul,
        ExprBinOp::Div => VirBinOp::Div,
        ExprBinOp::Rem => VirBinOp::Rem,
        ExprBinOp::BitXor => VirBinOp::BitXor,
        ExprBinOp::BitAnd => VirBinOp::BitAnd,
        ExprBinOp::BitOr => VirBinOp::BitOr,
        ExprBinOp::Shl => VirBinOp::Shl,
        ExprBinOp::Shr => VirBinOp::Shr,
        ExprBinOp::Eq => VirBinOp::Eq,
        ExprBinOp::Lt => VirBinOp::Lt,
        ExprBinOp::Le => VirBinOp::Le,
        ExprBinOp::Ne => VirBinOp::Ne,
        ExprBinOp::Ge => VirBinOp::Ge,
        ExprBinOp::Gt => VirBinOp::Gt,
    }
}

pub(super) fn lower_un_op(op: ExprUnOp) -> VirUnOp {
    match op {
        ExprUnOp::Not => VirUnOp::Not,
        ExprUnOp::Neg => VirUnOp::Neg,
    }
}

pub(super) fn lower_cast_kind(source: &RustType, target: &RustType) -> CastKind {
    if is_pointer_unsize(source, target) {
        CastKind::PointerUnsize
    } else if is_pointer_like(source) && is_pointer_like(target) {
        CastKind::PtrToPtr
    } else if is_float_like(source) && is_integer_like(target) {
        CastKind::FloatToInt
    } else if is_integer_like(source) && is_float_like(target) {
        CastKind::IntToFloat
    } else if is_float_like(source) && is_float_like(target) {
        CastKind::FloatToFloat
    } else if is_pointer_like(source) && is_integer_like(target) {
        CastKind::PointerExposeAddress
    } else if is_integer_like(source) && is_pointer_like(target) {
        CastKind::PointerFromExposedAddress
    } else if is_function_like(source) && (is_pointer_like(target) || is_function_like(target)) {
        CastKind::FnPtrToPtr
    } else if is_integer_like(source) && is_integer_like(target) {
        CastKind::IntToInt
    } else {
        CastKind::Transmute
    }
}

fn is_integer_like(ty: &RustType) -> bool {
    matches!(
        ty,
        RustType::Bool | RustType::Char | RustType::Uint(_) | RustType::Int(_)
    )
}

fn is_float_like(ty: &RustType) -> bool {
    matches!(ty, RustType::Float(_))
}

fn is_pointer_like(ty: &RustType) -> bool {
    matches!(
        ty,
        RustType::Reference { .. }
            | RustType::RawPtr { .. }
            | RustType::Box { .. }
            | RustType::Pin { .. }
    )
}

fn is_function_like(ty: &RustType) -> bool {
    matches!(ty, RustType::Function { .. })
}

fn is_pointer_unsize(source: &RustType, target: &RustType) -> bool {
    match (source, target) {
        (RustType::Reference { inner: src, .. }, RustType::Reference { inner: dst, .. })
        | (RustType::RawPtr { inner: src, .. }, RustType::RawPtr { inner: dst, .. })
        | (RustType::Box { inner: src }, RustType::Box { inner: dst }) => {
            is_unsize_inner(src.as_ref(), dst.as_ref())
        }
        _ => false,
    }
}

fn is_unsize_inner(source: &RustType, target: &RustType) -> bool {
    match target {
        RustType::DynTrait { .. } => !matches!(source, RustType::DynTrait { .. }),
        RustType::Slice {
            elem: target_element,
        } => matches!(
            source,
            RustType::Array {
                element: source_element,
                ..
            } if source_element.is_compatible(target_element)
        ),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::IntType;

    #[test]
    fn test_constant_from_value_byte_array_lowers_to_byte_str() {
        let value = Value::Array(vec![Value::u8(b'h'), Value::u8(b'i')]);
        let constant =
            constant_from_value(&value).expect("byte array should lower to a byte-string constant");
        match constant {
            Constant::ByteStr(bytes) => assert_eq!(bytes, vec![b'h', b'i']),
            other => panic!("expected Constant::ByteStr, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_empty_byte_array_lowers_to_empty_byte_str() {
        let value = Value::Array(vec![]);
        let constant =
            constant_from_value(&value).expect("empty array should lower to empty byte-string");
        match constant {
            Constant::ByteStr(bytes) => assert!(bytes.is_empty()),
            other => panic!("expected empty Constant::ByteStr, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_non_byte_array_lowers_to_array_aggregate() {
        // An array of non-`u8` scalars is not a byte string but is still a
        // constant aggregate when every element is itself a constant.
        let value = Value::Array(vec![
            Value::Uint {
                value: 1,
                ty: UintType::U32,
            },
            Value::Uint {
                value: 2,
                ty: UintType::U32,
            },
            Value::Uint {
                value: 3,
                ty: UintType::U32,
            },
        ]);
        let constant =
            constant_from_value(&value).expect("non-byte array of constants lowers to aggregate");
        match constant {
            Constant::Aggregate(aggregate) => {
                assert!(
                    matches!(
                        aggregate.kind,
                        ConstAggregateKind::Array(RustType::Uint(UintType::U32))
                    ),
                    "expected u32 array element type, got {:?}",
                    aggregate.kind
                );
                assert_eq!(aggregate.elements.len(), 3);
                assert!(matches!(
                    aggregate.elements[0],
                    Constant::Scalar(ScalarValue::Uint(1))
                ));
                assert!(matches!(
                    aggregate.elements[2],
                    Constant::Scalar(ScalarValue::Uint(3))
                ));
            }
            other => panic!("expected Constant::Aggregate, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_array_with_signed_element_lowers_to_array_aggregate() {
        // Mixing a non-`u8` element disqualifies the byte-string fast-path, but
        // both elements are still constants, so the array lowers as an aggregate.
        let value = Value::Array(vec![
            Value::u8(0),
            Value::Int {
                value: 1,
                ty: IntType::I8,
            },
        ]);
        let constant = constant_from_value(&value)
            .expect("array of scalar constants lowers to an array aggregate");
        match constant {
            Constant::Aggregate(aggregate) => {
                assert!(matches!(aggregate.kind, ConstAggregateKind::Array(_)));
                assert_eq!(aggregate.elements.len(), 2);
            }
            other => panic!("expected Constant::Aggregate, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_tuple_literal_lowers_to_tuple_aggregate() {
        // A tuple whose elements are all constants is a constant tuple aggregate.
        let value = Value::Tuple(vec![
            Value::Int {
                value: 1,
                ty: IntType::I32,
            },
            Value::Int {
                value: 2,
                ty: IntType::I32,
            },
        ]);
        let constant =
            constant_from_value(&value).expect("tuple of constants lowers to a tuple aggregate");
        match constant {
            Constant::Aggregate(aggregate) => {
                assert!(matches!(aggregate.kind, ConstAggregateKind::Tuple));
                assert_eq!(aggregate.elements.len(), 2);
                assert!(matches!(
                    aggregate.elements[0],
                    Constant::Scalar(ScalarValue::Int(1))
                ));
                assert!(matches!(
                    aggregate.elements[1],
                    Constant::Scalar(ScalarValue::Int(2))
                ));
            }
            other => panic!("expected Constant::Aggregate, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_struct_literal_lowers_to_struct_aggregate() {
        let mut fields = std::collections::BTreeMap::new();
        fields.insert(
            "x".to_string(),
            Value::Int {
                value: 1,
                ty: IntType::I32,
            },
        );
        fields.insert(
            "y".to_string(),
            Value::Int {
                value: 2,
                ty: IntType::I32,
            },
        );
        let value = Value::Struct {
            name: "Point".to_string(),
            fields,
        };
        let constant =
            constant_from_value(&value).expect("struct of constants lowers to a struct aggregate");
        match constant {
            Constant::Aggregate(aggregate) => match aggregate.kind {
                ConstAggregateKind::Struct { name, field_names } => {
                    assert_eq!(name, "Point");
                    // BTreeMap order is sorted: x then y.
                    assert_eq!(field_names, vec!["x".to_string(), "y".to_string()]);
                    assert_eq!(aggregate.elements.len(), 2);
                    assert!(matches!(
                        aggregate.elements[0],
                        Constant::Scalar(ScalarValue::Int(1))
                    ));
                }
                other => panic!("expected Struct kind, got {other:?}"),
            },
            other => panic!("expected Constant::Aggregate, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_enum_tuple_variant_lowers_to_enum_aggregate() {
        // `Some(3)`-style tuple variant.
        let value = Value::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Value::Int {
                value: 3,
                ty: IntType::I32,
            }])),
        };
        let constant = constant_from_value(&value)
            .expect("enum tuple variant of constants lowers to aggregate");
        match constant {
            Constant::Aggregate(aggregate) => match aggregate.kind {
                ConstAggregateKind::Enum {
                    name,
                    variant,
                    field_names,
                } => {
                    assert_eq!(name, "Option");
                    assert_eq!(variant, "Some");
                    assert!(
                        field_names.is_empty(),
                        "tuple variant has positional fields"
                    );
                    assert_eq!(aggregate.elements.len(), 1);
                    assert!(matches!(
                        aggregate.elements[0],
                        Constant::Scalar(ScalarValue::Int(3))
                    ));
                }
                other => panic!("expected Enum kind, got {other:?}"),
            },
            other => panic!("expected Constant::Aggregate, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_enum_unit_variant_lowers_to_empty_aggregate() {
        // `None`-style unit variant: no element constants.
        let value = Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        };
        let constant =
            constant_from_value(&value).expect("unit enum variant lowers to an empty aggregate");
        match constant {
            Constant::Aggregate(aggregate) => {
                assert!(matches!(aggregate.kind, ConstAggregateKind::Enum { .. }));
                assert!(aggregate.elements.is_empty());
            }
            other => panic!("expected Constant::Aggregate, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_nested_composite_lowers_recursively() {
        // `([1, 2], (true,))` — array nested inside a tuple, nested constants.
        let inner_array = Value::Array(vec![
            Value::Int {
                value: 1,
                ty: IntType::I32,
            },
            Value::Int {
                value: 2,
                ty: IntType::I32,
            },
        ]);
        let inner_tuple = Value::Tuple(vec![Value::Bool(true)]);
        let value = Value::Tuple(vec![inner_array, inner_tuple]);
        let constant =
            constant_from_value(&value).expect("nested composite of constants lowers recursively");
        match constant {
            Constant::Aggregate(outer) => {
                assert!(matches!(outer.kind, ConstAggregateKind::Tuple));
                assert_eq!(outer.elements.len(), 2);
                assert!(
                    matches!(&outer.elements[0], Constant::Aggregate(inner)
                        if matches!(inner.kind, ConstAggregateKind::Array(_))),
                    "first element should be a nested array aggregate"
                );
                assert!(
                    matches!(&outer.elements[1], Constant::Aggregate(inner)
                        if matches!(inner.kind, ConstAggregateKind::Tuple)),
                    "second element should be a nested tuple aggregate"
                );
            }
            other => panic!("expected nested Constant::Aggregate, got {other:?}"),
        }
    }

    #[test]
    fn test_constant_from_value_composite_with_nonconst_element_is_rejected() {
        // A tuple containing a value with no constant representation (a function
        // pointer is not a literal here) must remain unsupported, preserving the
        // all-or-nothing guarantee.
        let value = Value::Tuple(vec![
            Value::Bool(true),
            Value::FnPtr {
                name: "f".to_string(),
            },
        ]);
        assert!(
            matches!(
                constant_from_value(&value),
                Err(VirLoweringError::Unsupported { .. })
            ),
            "a composite with a non-constant element must remain unsupported"
        );
    }

    #[test]
    fn test_constant_from_value_scalar_still_lowers() {
        let constant = constant_from_value(&Value::Bool(true)).expect("bool lowers");
        assert!(matches!(
            constant,
            Constant::Scalar(ScalarValue::Bool(true))
        ));
    }
}
