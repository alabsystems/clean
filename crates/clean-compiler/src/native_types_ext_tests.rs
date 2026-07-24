// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended native type analysis.
//!
//! Part of #3084 - Native type compilation for UInt and Float.

use super::*;
use crate::ir::IRType;
use crate::native_types::NativeType;

// ---------------------------------------------------------------------------
// Layout computation
// ---------------------------------------------------------------------------

#[test]
fn test_layout_uint8_size_and_alignment() {
    let layout = compute_layout(NativeType::UInt8, &TargetConfig::lp64_le()).unwrap();
    assert_eq!(layout.size, 1);
    assert_eq!(layout.alignment, 1);
}

#[test]
fn test_layout_uint16_size_and_alignment() {
    let layout = compute_layout(NativeType::UInt16, &TargetConfig::lp64_le()).unwrap();
    assert_eq!(layout.size, 2);
    assert_eq!(layout.alignment, 2);
}

#[test]
fn test_layout_uint32_size_and_alignment() {
    let layout = compute_layout(NativeType::UInt32, &TargetConfig::lp64_le()).unwrap();
    assert_eq!(layout.size, 4);
    assert_eq!(layout.alignment, 4);
}

#[test]
fn test_layout_uint64_size_and_alignment() {
    let layout = compute_layout(NativeType::UInt64, &TargetConfig::lp64_le()).unwrap();
    assert_eq!(layout.size, 8);
    assert_eq!(layout.alignment, 8);
}

#[test]
fn test_layout_float_size_and_alignment() {
    let layout = compute_layout(NativeType::Float, &TargetConfig::lp64_le()).unwrap();
    assert_eq!(layout.size, 8);
    assert_eq!(layout.alignment, 8);
}

#[test]
fn test_layout_usize_64bit_target() {
    let layout = compute_layout(NativeType::USize, &TargetConfig::lp64_le()).unwrap();
    assert_eq!(layout.size, 8);
    assert_eq!(layout.alignment, 8);
}

#[test]
fn test_layout_usize_32bit_target() {
    let layout = compute_layout(NativeType::USize, &TargetConfig::ilp32_le()).unwrap();
    assert_eq!(layout.size, 4);
    assert_eq!(layout.alignment, 4);
}

#[test]
fn test_layout_bool_returns_error() {
    let result = compute_layout(NativeType::Bool, &TargetConfig::lp64_le());
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, NativeTypeError::NoLayout(NativeType::Bool)));
}

// ---------------------------------------------------------------------------
// Padding computation
// ---------------------------------------------------------------------------

#[test]
fn test_padding_already_aligned() {
    assert_eq!(compute_padding(0, 4), 0);
    assert_eq!(compute_padding(8, 4), 0);
    assert_eq!(compute_padding(16, 8), 0);
}

#[test]
fn test_padding_needed() {
    assert_eq!(compute_padding(1, 4), 3);
    assert_eq!(compute_padding(3, 4), 1);
    assert_eq!(compute_padding(5, 8), 3);
    assert_eq!(compute_padding(6, 4), 2);
}

#[test]
fn test_padding_alignment_one() {
    // Alignment 1 never needs padding.
    assert_eq!(compute_padding(0, 1), 0);
    assert_eq!(compute_padding(7, 1), 0);
    assert_eq!(compute_padding(100, 1), 0);
}

// ---------------------------------------------------------------------------
// Struct layout
// ---------------------------------------------------------------------------

#[test]
fn test_struct_layout_empty() {
    let layout = compute_struct_layout(&[], &TargetConfig::lp64_le()).unwrap();
    assert_eq!(layout.size, 0);
    assert_eq!(layout.alignment, 1);
}

#[test]
fn test_struct_layout_single_field() {
    let layout = compute_struct_layout(&[NativeType::UInt32], &TargetConfig::lp64_le()).unwrap();
    assert_eq!(layout.size, 4);
    assert_eq!(layout.alignment, 4);
}

#[test]
fn test_struct_layout_two_same_fields() {
    let layout = compute_struct_layout(
        &[NativeType::UInt32, NativeType::UInt32],
        &TargetConfig::lp64_le(),
    )
    .unwrap();
    assert_eq!(layout.size, 8);
    assert_eq!(layout.alignment, 4);
}

#[test]
fn test_struct_layout_with_padding() {
    // u8 (1B) + padding (1B) + u16 (2B) = 4B
    let layout = compute_struct_layout(
        &[NativeType::UInt8, NativeType::UInt16],
        &TargetConfig::lp64_le(),
    )
    .unwrap();
    assert_eq!(layout.size, 4);
    assert_eq!(layout.alignment, 2);
}

#[test]
fn test_struct_layout_trailing_padding() {
    // u64 (8B) + u8 (1B) + trailing (7B) = 16B, align 8
    let layout = compute_struct_layout(
        &[NativeType::UInt64, NativeType::UInt8],
        &TargetConfig::lp64_le(),
    )
    .unwrap();
    assert_eq!(layout.size, 16);
    assert_eq!(layout.alignment, 8);
}

#[test]
fn test_struct_layout_bool_field_returns_error() {
    let result = compute_struct_layout(
        &[NativeType::UInt32, NativeType::Bool],
        &TargetConfig::lp64_le(),
    );
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// Compatibility
// ---------------------------------------------------------------------------

#[test]
fn test_layout_compatible_same_type() {
    let result = is_layout_compatible(
        NativeType::UInt32,
        NativeType::UInt32,
        &TargetConfig::lp64_le(),
    )
    .unwrap();
    assert!(result);
}

#[test]
fn test_layout_compatible_different_size() {
    let result = is_layout_compatible(
        NativeType::UInt16,
        NativeType::UInt32,
        &TargetConfig::lp64_le(),
    )
    .unwrap();
    assert!(!result);
}

#[test]
fn test_layout_compatible_uint64_and_float() {
    // Both 8 bytes, 8 alignment on lp64.
    let result = is_layout_compatible(
        NativeType::UInt64,
        NativeType::Float,
        &TargetConfig::lp64_le(),
    )
    .unwrap();
    assert!(result);
}

#[test]
fn test_layout_compatible_usize_varies_by_target() {
    let result_64 = is_layout_compatible(
        NativeType::USize,
        NativeType::UInt64,
        &TargetConfig::lp64_le(),
    )
    .unwrap();
    assert!(result_64);

    let result_32 = is_layout_compatible(
        NativeType::USize,
        NativeType::UInt32,
        &TargetConfig::ilp32_le(),
    )
    .unwrap();
    assert!(result_32);
}

// ---------------------------------------------------------------------------
// Safe widening
// ---------------------------------------------------------------------------

#[test]
fn test_safe_widening_u8_to_u16() {
    assert!(is_safe_widening(NativeType::UInt8, NativeType::UInt16));
}

#[test]
fn test_safe_widening_u8_to_u64() {
    assert!(is_safe_widening(NativeType::UInt8, NativeType::UInt64));
}

#[test]
fn test_safe_widening_u32_to_u64() {
    assert!(is_safe_widening(NativeType::UInt32, NativeType::UInt64));
}

#[test]
fn test_narrowing_is_not_safe() {
    assert!(!is_safe_widening(NativeType::UInt32, NativeType::UInt16));
    assert!(!is_safe_widening(NativeType::UInt64, NativeType::UInt8));
}

#[test]
fn test_float_widening_is_not_safe() {
    assert!(!is_safe_widening(NativeType::UInt32, NativeType::Float));
    assert!(!is_safe_widening(NativeType::Float, NativeType::UInt64));
}

#[test]
fn test_same_type_is_not_widening() {
    assert!(!is_safe_widening(NativeType::UInt32, NativeType::UInt32));
}

// ---------------------------------------------------------------------------
// Type classification
// ---------------------------------------------------------------------------

#[test]
fn test_classify_integer_types() {
    assert_eq!(classify_type(NativeType::UInt8), TypeCategory::Integer);
    assert_eq!(classify_type(NativeType::UInt16), TypeCategory::Integer);
    assert_eq!(classify_type(NativeType::UInt32), TypeCategory::Integer);
    assert_eq!(classify_type(NativeType::UInt64), TypeCategory::Integer);
    assert_eq!(classify_type(NativeType::USize), TypeCategory::Integer);
}

#[test]
fn test_classify_float_type() {
    assert_eq!(
        classify_type(NativeType::Float),
        TypeCategory::FloatingPoint
    );
}

#[test]
fn test_classify_bool_type() {
    assert_eq!(classify_type(NativeType::Bool), TypeCategory::Boolean);
}

#[test]
fn test_classify_ir_type_scalars() {
    assert_eq!(
        classify_ir_type(&IRType::UInt8),
        Some(TypeCategory::Integer)
    );
    assert_eq!(
        classify_ir_type(&IRType::Float64),
        Some(TypeCategory::FloatingPoint)
    );
    assert_eq!(classify_ir_type(&IRType::Bool), Some(TypeCategory::Boolean));
}

#[test]
fn test_classify_ir_type_non_native_returns_none() {
    assert_eq!(classify_ir_type(&IRType::Object), None);
    assert_eq!(classify_ir_type(&IRType::Erased), None);
    assert_eq!(classify_ir_type(&IRType::Struct(vec![])), None);
}

// ---------------------------------------------------------------------------
// Type statistics
// ---------------------------------------------------------------------------

#[test]
fn test_type_stats_empty() {
    let stats = compute_type_stats(&[]);
    assert_eq!(stats.total, 0);
    assert_eq!(stats.integer_count, 0);
    assert_eq!(stats.float_count, 0);
    assert_eq!(stats.bool_count, 0);
}

#[test]
fn test_type_stats_mixed() {
    let types = [
        NativeType::UInt32,
        NativeType::Float,
        NativeType::UInt8,
        NativeType::Bool,
        NativeType::UInt64,
    ];
    let stats = compute_type_stats(&types);
    assert_eq!(stats.total, 5);
    assert_eq!(stats.integer_count, 3);
    assert_eq!(stats.float_count, 1);
    assert_eq!(stats.bool_count, 1);
}

#[test]
fn test_average_field_size_mixed() {
    let types = [NativeType::UInt8, NativeType::UInt32, NativeType::UInt64];
    let avg = average_field_size(&types, &TargetConfig::lp64_le()).unwrap();
    // (1 + 4 + 8) / 3 ≈ 4.333
    assert!((avg - 4.333).abs() < 0.01);
}

#[test]
fn test_average_field_size_skips_bool() {
    let types = [NativeType::Bool, NativeType::UInt32];
    let avg = average_field_size(&types, &TargetConfig::lp64_le()).unwrap();
    assert!((avg - 4.0).abs() < f64::EPSILON);
}

#[test]
fn test_average_field_size_all_bool_returns_none() {
    let types = [NativeType::Bool, NativeType::Bool];
    assert!(average_field_size(&types, &TargetConfig::lp64_le()).is_none());
}

// ---------------------------------------------------------------------------
// ABI analysis
// ---------------------------------------------------------------------------

#[test]
fn test_passing_convention_integers() {
    assert_eq!(
        passing_convention(NativeType::UInt32),
        PassingConvention::IntegerRegister
    );
    assert_eq!(
        passing_convention(NativeType::UInt64),
        PassingConvention::IntegerRegister
    );
}

#[test]
fn test_passing_convention_float() {
    assert_eq!(
        passing_convention(NativeType::Float),
        PassingConvention::FloatRegister
    );
}

#[test]
fn test_passing_convention_bool() {
    assert_eq!(
        passing_convention(NativeType::Bool),
        PassingConvention::Stack
    );
}

#[test]
fn test_register_usage_few_params() {
    let params = [NativeType::UInt32, NativeType::Float, NativeType::UInt64];
    let usage = count_register_usage(&params);
    assert_eq!(usage.integer_regs, 2);
    assert_eq!(usage.float_regs, 1);
    assert_eq!(usage.stack_params, 0);
    assert!(usage.all_in_registers());
}

#[test]
fn test_register_usage_overflow_integer_regs() {
    // 7 integer params: 6 in regs, 1 on stack
    let params = [NativeType::UInt64; 7];
    let usage = count_register_usage(&params);
    assert_eq!(usage.integer_regs, 6);
    assert_eq!(usage.stack_params, 1);
    assert!(!usage.all_in_registers());
}

#[test]
fn test_register_usage_overflow_float_regs() {
    // 9 float params: 8 in regs, 1 on stack
    let params = [NativeType::Float; 9];
    let usage = count_register_usage(&params);
    assert_eq!(usage.float_regs, 8);
    assert_eq!(usage.stack_params, 1);
    assert!(!usage.all_in_registers());
}

#[test]
fn test_register_usage_empty_params() {
    let usage = count_register_usage(&[]);
    assert_eq!(usage.integer_regs, 0);
    assert_eq!(usage.float_regs, 0);
    assert_eq!(usage.stack_params, 0);
    assert!(usage.all_in_registers());
}

// ---------------------------------------------------------------------------
// Pretty printing
// ---------------------------------------------------------------------------

#[test]
fn test_c_name_uint8() {
    assert_eq!(native_type_to_c_name(NativeType::UInt8), "uint8_t");
}

#[test]
fn test_c_name_uint64() {
    assert_eq!(native_type_to_c_name(NativeType::UInt64), "uint64_t");
}

#[test]
fn test_c_name_float() {
    assert_eq!(native_type_to_c_name(NativeType::Float), "double");
}

#[test]
fn test_c_name_bool() {
    assert_eq!(native_type_to_c_name(NativeType::Bool), "_Bool");
}

#[test]
fn test_c_struct_display() {
    let fields = vec![
        ("x".to_owned(), NativeType::UInt32),
        ("y".to_owned(), NativeType::Float),
    ];
    let display = CStructDisplay {
        name: "Point",
        fields: &fields,
    };
    let output = format!("{}", display);
    assert!(output.contains("struct Point {"));
    assert!(output.contains("uint32_t x;"));
    assert!(output.contains("double y;"));
}

// ---------------------------------------------------------------------------
// Endianness handling
// ---------------------------------------------------------------------------

#[test]
fn test_endian_sensitive_multibyte() {
    assert!(is_endian_sensitive(NativeType::UInt16));
    assert!(is_endian_sensitive(NativeType::UInt32));
    assert!(is_endian_sensitive(NativeType::UInt64));
    assert!(is_endian_sensitive(NativeType::Float));
    assert!(is_endian_sensitive(NativeType::USize));
}

#[test]
fn test_endian_insensitive_single_byte() {
    assert!(!is_endian_sensitive(NativeType::UInt8));
    assert!(!is_endian_sensitive(NativeType::Bool));
}

#[test]
fn test_byte_swap_uint16() {
    let swapped = byte_swap(NativeType::UInt16, 0x0102).unwrap();
    assert_eq!(swapped, 0x0201);
}

#[test]
fn test_byte_swap_uint32() {
    let swapped = byte_swap(NativeType::UInt32, 0x01020304).unwrap();
    assert_eq!(swapped, 0x04030201);
}

#[test]
fn test_byte_swap_uint8_noop() {
    let swapped = byte_swap(NativeType::UInt8, 0xAB).unwrap();
    assert_eq!(swapped, 0xAB);
}

#[test]
fn test_byte_swap_bool_returns_error() {
    let result = byte_swap(NativeType::Bool, 1);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// IR type conversions
// ---------------------------------------------------------------------------

#[test]
fn test_native_to_ir_type_round_trip_integers() {
    for ty in [
        NativeType::UInt8,
        NativeType::UInt16,
        NativeType::UInt32,
        NativeType::UInt64,
        NativeType::USize,
    ] {
        let ir = native_to_ir_type(ty);
        let back = ir_to_native_type(&ir);
        assert_eq!(back, Some(ty));
    }
}

#[test]
fn test_native_to_ir_float() {
    let ir = native_to_ir_type(NativeType::Float);
    assert_eq!(ir, IRType::Float64);
}

#[test]
fn test_native_to_ir_bool() {
    let ir = native_to_ir_type(NativeType::Bool);
    assert_eq!(ir, IRType::Bool);
}

#[test]
fn test_ir_to_native_object_returns_none() {
    assert_eq!(ir_to_native_type(&IRType::Object), None);
}

#[test]
fn test_ir_to_native_erased_returns_none() {
    assert_eq!(ir_to_native_type(&IRType::Erased), None);
}

#[test]
fn test_ir_to_native_float32_returns_none() {
    // Float32 has no NativeType equivalent (NativeType::Float is 64-bit).
    assert_eq!(ir_to_native_type(&IRType::Float32), None);
}

// ---------------------------------------------------------------------------
// Target config constructors
// ---------------------------------------------------------------------------

#[test]
fn test_target_lp64_le() {
    let t = TargetConfig::lp64_le();
    assert_eq!(t.pointer_width, 64);
    assert!(!t.big_endian);
}

#[test]
fn test_target_ilp32_le() {
    let t = TargetConfig::ilp32_le();
    assert_eq!(t.pointer_width, 32);
    assert!(!t.big_endian);
}

#[test]
fn test_target_lp64_be() {
    let t = TargetConfig::lp64_be();
    assert_eq!(t.pointer_width, 64);
    assert!(t.big_endian);
}

#[test]
fn test_target_default_is_lp64_le() {
    assert_eq!(TargetConfig::default(), TargetConfig::lp64_le());
}
