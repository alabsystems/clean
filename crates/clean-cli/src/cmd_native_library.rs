// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-owned native-library replacement evidence surfaces.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use clap::{Args, Subcommand, ValueEnum};
use serde::Serialize;

const MATRIX_GENERATOR: &str = "clean replacement native-library coverage-matrix --json";
const MATRIX_SCHEMA_VERSION: &str = "clean-native-library-coverage-matrix-v1";
const MATRIX_CHECK_SCHEMA_VERSION: &str = "clean-native-library-coverage-matrix-check-v1";
const MATHLIB_API_SCHEMA_VERSION: &str = "clean-native-library-mathlib-api-v1";
const API_SLICE_SCHEMA_VERSION: &str = "clean-native-library-api-slice-v1";
const NATIVE_REDUCER_SOURCE_GLOB: &str = "crates/clean-kernel/src/env/native_reducers*.rs";
#[cfg(test)]
const DEFAULT_REPORT_PATH: &str = "reports/native-library-replacement.json";
const OLD_MATRIX_BLOCKER: &str =
    "No complete generated Init, Std, or core-Mathlib API coverage matrix exists yet.";
const SCOPED_MATRIX_BLOCKER: &str = "Generated API coverage matrix is scoped to registered native reducer names and compatibility-only Mathlib evidence; it is not a complete Init, Std, or core-Mathlib API enumeration.";

const INIT_REDUCER_SOURCES: &[&str] = &[
    "crates/clean-kernel/src/env/native_reducers.rs",
    "crates/clean-kernel/src/env/native_reducers_init.rs",
];
const MATHLIB_COMPATIBILITY_EVIDENCE: &[&str] = &[
    "reports/2026-04-13-mathlib-smoke-test.md",
    "reports/2026-04-14-mathlib-verify-progress.md",
    "reports/2026-04-14-mathlib-verify-200.json",
    "crates/clean-olean/tests/verify_mathlib_tests.rs",
    "crates/clean-cli/src/cmd_olean.rs",
    "crates/clean-olean/src/cli/mod.rs",
];
const NAT_ARITHMETIC_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_arith.rs";
const NAT_ARITHMETIC_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_arith_tests.rs";
const NAT_ARITHMETIC_APIS: &[&str] = &[
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.pow", "Nat.beq", "Nat.ble",
    "Nat.blt",
];
const NAT_ARITHMETIC_TEST_MARKERS: &[&str] = &[
    "fn test_nat_add_basic",
    "fn test_nat_sub_basic",
    "fn test_nat_mul_basic",
    "fn test_nat_div_basic",
    "fn test_nat_mod_basic",
    "fn test_nat_pow_basic",
    "fn test_nat_beq_equal",
    "fn test_nat_ble_true",
    "fn test_nat_blt_true",
];
const NAT_BITWISE_APIS: &[&str] = &[
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
];
const NAT_BITWISE_TEST_MARKERS: &[&str] = &[
    "fn test_nat_land",
    "fn test_nat_lor",
    "fn test_nat_lxor",
    "fn test_nat_shift_left",
    "fn test_nat_shift_right",
    "fn test_nat_shift_left_bignat_result",
];
const BOOL_NAT_EXT_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_bool_ext.rs";
const BOOL_NAT_EXT_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_bool_ext_tests.rs";
const BOOL_NAT_EXT_APIS: &[&str] = &["Bool.beq", "Nat.gcd"];
const BOOL_NAT_EXT_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_bool_beq_true_true",
    "fn test_reduce_bool_beq_true_false",
    "fn test_reduce_nat_gcd_basic",
    "fn test_reduce_nat_gcd_with_zero",
    "fn test_bool_ext_reducers_registered",
];
const STRING_EXT_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_string_ext.rs";
const STRING_EXT_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_string_ext_tests.rs";
const STRING_EXT_APIS: &[&str] = &[
    "String.startsWith",
    "String.endsWith",
    "String.containsSubstr",
    "String.replace",
    "String.trimLeft",
    "String.trimRight",
    "String.substrEq",
];
const STRING_EXT_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_string_starts_with_true",
    "fn test_reduce_string_starts_with_false",
    "fn test_reduce_string_ends_with_true",
    "fn test_reduce_string_ends_with_false",
    "fn test_reduce_string_contains_true",
    "fn test_reduce_string_contains_false",
    "fn test_reduce_string_replace",
    "fn test_reduce_string_trim_left",
    "fn test_reduce_string_trim_right",
    "fn test_reduce_string_substr_eq_true",
    "fn test_reduce_string_substr_eq_false",
    "fn test_reduce_string_substr_eq_out_of_bounds",
    "fn test_string_ext_native_reducers_registered",
];
const STRING_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_string.rs";
const STRING_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_string_tests.rs";
const STRING_CORE_APIS: &[&str] = &[
    "String.get",
    "String.next",
    "String.prev",
    "String.atEnd",
    "String.front",
    "String.singleton",
];
const STRING_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_string_get_ascii",
    "fn test_reduce_string_get_unicode",
    "fn test_reduce_string_next_ascii",
    "fn test_reduce_string_prev_ascii",
    "fn test_reduce_string_at_end_true",
    "fn test_reduce_string_front",
    "fn test_reduce_string_singleton",
];
const STRING_TRANSFORM_APIS: &[&str] = &[
    "String.extract",
    "String.intercalate",
    "String.take",
    "String.drop",
    "String.toLower",
    "String.toUpper",
];
const STRING_TRANSFORM_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_string_extract_basic",
    "fn test_reduce_string_extract_empty",
    "fn test_reduce_string_intercalate_empty_list",
    "fn test_reduce_string_take",
    "fn test_reduce_string_drop",
    "fn test_reduce_string_to_lower",
    "fn test_reduce_string_to_upper",
];
const STRING_HASH_APIS: &[&str] = &["String.hash"];
const STRING_HASH_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_string_hash_deterministic",
    "fn test_string_hash_uses_seed_11",
    "fn test_string_hash_lean4_reference_hello",
    "fn test_string_hash_lean4_reference_world",
    "fn test_string_hash_lean4_reference_empty",
    "fn test_string_hash_lean4_reference_nat",
];
const NAME_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_name.rs";
const NAME_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_name_tests.rs";
const NAME_CORE_APIS: &[&str] = &[
    "Lean.Name.mkStr",
    "Lean.Name.mkNum",
    "Lean.Name.beq",
    "Lean.Name.hash",
    "Lean.Name.toString",
    "Lean.Name.append",
];
const NAME_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_name_mk_str_basic",
    "fn test_reduce_name_mk_num_basic",
    "fn test_reduce_name_beq_equal",
    "fn test_reduce_name_hash_produces_nat",
    "fn test_reduce_name_to_string_simple",
    "fn test_reduce_name_append_basic",
    "fn test_name_native_reducers_registered",
];
const DECIDABLE_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_decidable.rs";
const DECIDABLE_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_decidable_tests.rs";
const DECIDABLE_CORE_APIS: &[&str] = &[
    "instDecidableNatLt",
    "instDecidableNatLe",
    "instDecidableEqNat",
    "instDecidableEqBool",
    "instDecidableEqString",
    "instDecidableEqFin",
    "Fin.decEq",
];
const DECIDABLE_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_inst_decidable_nat_lt_true",
    "fn test_inst_decidable_nat_le_true_less",
    "fn test_inst_decidable_eq_nat_equal",
    "fn test_inst_decidable_eq_bool_equal",
    "fn test_inst_decidable_eq_string_equal",
    "fn test_fin_dec_eq_equal",
    "fn test_decidable_reducers_registered",
];
const DECIDABLE_EQ_ALIASES_SOURCE: &str =
    "crates/clean-kernel/src/env/native_reducers_decidable_aliases.rs";
const DECIDABLE_EQ_ALIASES_APIS: &[&str] = &[
    "instDecidableEqChar",
    "instDecidableEqUInt8",
    "instDecidableEqFloat",
];
const DECIDABLE_EQ_ALIASES_TEST_MARKERS: &[&str] = &[
    "fn test_inst_decidable_eq_char_reduces",
    "fn test_inst_decidable_eq_uint8_reduces",
    "fn test_inst_decidable_eq_float_reduces",
    "fn test_decidable_aliases_registered",
];
const INT_ORDER_DECIDABLE_SOURCE: &str =
    "crates/clean-kernel/src/env/native_reducers_decidable_ext.rs";
const INT_ORDER_DECIDABLE_TESTS: &str =
    "crates/clean-kernel/src/env/native_reducers_decidable_ext_tests.rs";
const INT_ORDER_DECIDABLE_APIS: &[&str] = &["Int.decLe", "Int.decLt"];
const INT_ORDER_DECIDABLE_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_int_dec_le_true",
    "fn test_reduce_int_dec_le_false",
    "fn test_reduce_int_dec_lt_true",
    "fn test_reduce_int_dec_lt_false",
    "fn test_registration",
];
const SIGNED_DECIDABLE_EQ_ALIAS_SOURCES: &[&str] = &[
    "crates/clean-kernel/src/env/native_reducers_decidable_ext.rs",
    "crates/clean-kernel/src/env/native_reducers_sint.rs",
];
const SIGNED_DECIDABLE_EQ_ALIAS_TESTS: &[&str] = &[
    "crates/clean-kernel/src/env/native_reducers_decidable_ext_tests.rs",
    "crates/clean-kernel/src/env/native_reducers_sint_tests.rs",
];
const SIGNED_DECIDABLE_EQ_ALIAS_APIS: &[&str] = &[
    "instDecidableEqInt",
    "instDecidableEqInt8",
    "instDecidableEqInt16",
    "instDecidableEqInt32",
    "instDecidableEqInt64",
    "instDecidableEqISize",
];
const SIGNED_DECIDABLE_EQ_ALIAS_TEST_MARKERS: &[&str] = &[
    "fn test_inst_decidable_eq_int_alias_reduces",
    "fn test_signed_int_decidable_eq_aliases_reduce",
    "fn test_registration",
    "fn test_sint_reducers_registered",
];
const HETERO_OPS_SOURCE: &str =
    "crates/clean-kernel/src/env/native_reducers_hetero_shortcircuit.rs";
const HETERO_OPS_APIS: &[&str] = &[
    "HAdd.hAdd",
    "HSub.hSub",
    "HMul.hMul",
    "HDiv.hDiv",
    "HMod.hMod",
    "HPow.hPow",
    "HAppend.hAppend",
];
const HETERO_OPS_TEST_MARKERS: &[&str] = &[
    "fn test_hadd_nat_reduces",
    "fn test_hsub_nat_reduces",
    "fn test_hmul_nat_reduces",
    "fn test_hdiv_nat_reduces",
    "fn test_hmod_nat_reduces",
    "fn test_hpow_nat_reduces",
    "fn test_happend_string_reduces",
    "fn test_hetero_shortcircuit_registered",
];
const BEQ_SHORTCIRCUIT_SOURCE: &str =
    "crates/clean-kernel/src/env/native_reducers_beq_shortcircuit.rs";
const BEQ_SHORTCIRCUIT_APIS: &[&str] = &["BEq.beq"];
const BEQ_SHORTCIRCUIT_TEST_MARKERS: &[&str] = &[
    "fn test_beq_beq_nat_equal",
    "fn test_beq_beq_bool_equal",
    "fn test_beq_beq_string_equal",
    "fn test_beq_beq_uint32_equal",
    "fn test_beq_beq_char_equal",
    "fn test_beq_beq_int_equal",
    "fn test_beq_beq_fin_equal",
    "fn test_beq_shortcircuit_registered",
];
const DECIDABLE_COMBINATORS_SOURCE: &str =
    "crates/clean-kernel/src/env/native_reducers_decidable_ext.rs";
const DECIDABLE_COMBINATORS_TESTS: &str =
    "crates/clean-kernel/src/env/native_reducers_decidable_ext_tests.rs";
const DECIDABLE_COMBINATORS_APIS: &[&str] = &[
    "decide",
    "Decidable.decide",
    "instDecidableAnd",
    "instDecidableOr",
    "instDecidableNot",
];
const DECIDABLE_COMBINATORS_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_decide_true",
    "fn test_reduce_decide_false",
    "fn test_reduce_inst_decidable_and_both_true",
    "fn test_reduce_inst_decidable_and_one_false",
    "fn test_reduce_inst_decidable_or_one_true",
    "fn test_reduce_inst_decidable_or_both_false",
    "fn test_reduce_inst_decidable_not_true_gives_false",
    "fn test_reduce_inst_decidable_not_false_gives_true",
    "fn test_registration",
];
const NAT_ORDER_DECIDABLE_SOURCE: &str =
    "crates/clean-kernel/src/env/native_reducers_decidable_ext.rs";
const NAT_ORDER_DECIDABLE_TESTS: &str =
    "crates/clean-kernel/src/env/native_reducers_decidable_ext_tests.rs";
const NAT_ORDER_DECIDABLE_APIS: &[&str] = &["Nat.decLe", "Nat.decLt"];
const NAT_ORDER_DECIDABLE_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_nat_dec_le_true",
    "fn test_reduce_nat_dec_le_false",
    "fn test_reduce_nat_dec_le_equal",
    "fn test_reduce_nat_dec_lt_true",
    "fn test_reduce_nat_dec_lt_false_equal",
    "fn test_registration",
];
const CHAR_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_char.rs";
const CHAR_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_char_tests.rs";
const CHAR_CORE_APIS: &[&str] = &[
    "Char.toNat",
    "Char.decEq",
    "Char.decLe",
    "Char.isAlpha",
    "Char.isDigit",
    "Char.isWhitespace",
    "Char.isLower",
    "Char.isUpper",
    "Char.toLower",
    "Char.toUpper",
];
const CHAR_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_reduce_char_to_nat",
    "fn test_reduce_char_dec_eq_equal",
    "fn test_reduce_char_dec_le_declines",
    "fn test_reduce_char_is_alpha_true",
    "fn test_reduce_char_is_digit_true",
    "fn test_reduce_char_is_whitespace_true",
    "fn test_reduce_char_is_lower_true",
    "fn test_reduce_char_is_upper_true",
    "fn test_reduce_char_to_lower",
    "fn test_reduce_char_to_upper",
    "fn test_char_native_reducers_registered",
];
const UINT_OF_NAT_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint_conv.rs";
const UINT_OF_NAT_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_conv_tests.rs";
const UINT_OF_NAT_APIS: &[&str] = &[
    "UInt8.ofNat",
    "UInt16.ofNat",
    "UInt32.ofNat",
    "UInt64.ofNat",
    "USize.ofNat",
];
const UINT_OF_NAT_TEST_MARKERS: &[&str] = &[
    "fn test_uint_of_nat_native_reducers_are_intentionally_unregistered",
    "fn test_uint8_of_nat_delta_unfolds_to_genuine_ctor",
    "fn test_all_conv_reducers_registered",
];
const FIN_VAL_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint_conv.rs";
const FIN_VAL_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_conv_tests.rs";
const FIN_VAL_APIS: &[&str] = &["Fin.val"];
const FIN_VAL_TEST_MARKERS: &[&str] = &[
    "fn test_fin_val_identity",
    "fn test_fin_val_no_args_returns_none",
    "fn test_fin_val_non_literal_returns_none",
    "fn test_all_conv_reducers_registered",
];
const UINT_NARROWING_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint_conv.rs";
const UINT_NARROWING_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_conv_tests.rs";
const UINT_NARROWING_APIS: &[&str] = &[
    "UInt16.toUInt8",
    "UInt32.toUInt8",
    "UInt32.toUInt16",
    "UInt64.toUInt8",
    "UInt64.toUInt16",
    "UInt64.toUInt32",
    "USize.toUInt8",
    "USize.toUInt16",
    "USize.toUInt32",
];
const UINT_NARROWING_TEST_MARKERS: &[&str] = &[
    "fn test_uint16_to_uint8_narrowing",
    "fn test_uint32_to_uint8_narrowing",
    "fn test_uint32_to_uint16_narrowing",
    "fn test_uint64_to_uint8_narrowing",
    "fn test_uint64_to_uint16_narrowing",
    "fn test_uint64_to_uint32_narrowing",
    "fn test_usize_to_uint8_narrowing",
    "fn test_usize_to_uint16_narrowing",
    "fn test_usize_to_uint32_narrowing",
    "fn test_all_conv_reducers_registered",
];
const UINT_WIDENING_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint_conv.rs";
const UINT_WIDENING_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_conv_tests.rs";
const UINT_WIDENING_APIS: &[&str] = &[
    "UInt8.toUInt16",
    "UInt8.toUInt32",
    "UInt8.toUInt64",
    "UInt16.toUInt32",
    "UInt16.toUInt64",
    "UInt32.toUInt64",
    "UInt8.toUSize",
    "UInt16.toUSize",
    "UInt32.toUSize",
    "UInt64.toUSize",
    "USize.toUInt64",
];
const UINT_WIDENING_TEST_MARKERS: &[&str] = &[
    "fn test_uint8_to_uint16_widening",
    "fn test_uint8_to_uint32_widening",
    "fn test_uint8_to_uint64_widening",
    "fn test_uint16_to_uint32_widening",
    "fn test_uint16_to_uint64_widening",
    "fn test_uint32_to_uint64_widening",
    "fn test_uint8_to_usize_widening",
    "fn test_uint16_to_usize_widening",
    "fn test_uint32_to_usize_widening",
    "fn test_uint64_to_usize_identity",
    "fn test_usize_to_uint64_identity",
    "fn test_all_conv_reducers_registered",
];
const BITVEC_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_bitvec.rs";
const BITVEC_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_bitvec_tests.rs";
const BITVEC_CORE_APIS: &[&str] = &[
    "BitVec.ofNat",
    "BitVec.toNat",
    "BitVec.toFin",
    "BitVec.ofFin",
];
const BITVEC_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_bitvec_of_nat_8bit_in_range",
    "fn test_bitvec_of_nat_8bit_wraps",
    "fn test_bitvec_to_nat_identity",
    "fn test_bitvec_to_fin_identity",
    "fn test_bitvec_of_fin_identity",
    "fn test_all_bitvec_reducers_registered",
];
const UINT_BITVEC_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_bitvec.rs";
const UINT_BITVEC_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_bitvec_tests.rs";
const UINT_BITVEC_APIS: &[&str] = &[
    "UInt8.toBitVec",
    "UInt16.toBitVec",
    "UInt32.toBitVec",
    "UInt64.toBitVec",
    "USize.toBitVec",
    "UInt8.ofBitVec",
    "UInt16.ofBitVec",
    "UInt32.ofBitVec",
    "UInt64.ofBitVec",
    "USize.ofBitVec",
];
const UINT_BITVEC_TEST_MARKERS: &[&str] = &[
    "fn test_uint8_to_bitvec_identity",
    "fn test_uint16_to_bitvec_identity",
    "fn test_uint32_to_bitvec_identity",
    "fn test_uint64_to_bitvec_identity",
    "fn test_usize_to_bitvec_identity",
    "fn test_uint8_of_bitvec_identity",
    "fn test_uint16_of_bitvec_identity",
    "fn test_uint32_of_bitvec_identity",
    "fn test_uint64_of_bitvec_identity",
    "fn test_usize_of_bitvec_identity",
    "fn test_all_bitvec_reducers_registered",
];
const SIGNED_BITVEC_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_bitvec.rs";
const SIGNED_BITVEC_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_bitvec_tests.rs";
const SIGNED_BITVEC_APIS: &[&str] = &[
    "Int8.toUInt8",
    "Int16.toUInt16",
    "Int32.toUInt32",
    "Int64.toUInt64",
    "ISize.toUSize",
    "Int8.ofUInt8",
    "Int16.ofUInt16",
    "Int32.ofUInt32",
    "Int64.ofUInt64",
    "ISize.ofUSize",
    "Int8.toBitVec",
    "Int16.toBitVec",
    "Int32.toBitVec",
    "Int64.toBitVec",
    "ISize.toBitVec",
];
const SIGNED_BITVEC_TEST_MARKERS: &[&str] = &[
    "fn test_int8_to_uint8_identity",
    "fn test_int16_to_uint16_identity",
    "fn test_int32_to_uint32_identity",
    "fn test_int64_to_uint64_identity",
    "fn test_isize_to_usize_identity",
    "fn test_int8_of_uint8_identity",
    "fn test_int16_of_uint16_identity",
    "fn test_int32_of_uint32_identity",
    "fn test_int64_of_uint64_identity",
    "fn test_isize_of_usize_identity",
    "fn test_int8_to_bitvec_identity",
    "fn test_int16_to_bitvec_identity",
    "fn test_int32_to_bitvec_identity",
    "fn test_int64_to_bitvec_identity",
    "fn test_isize_to_bitvec_identity",
    "fn test_all_bitvec_reducers_registered",
];
const UINT8_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const UINT8_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_tests.rs";
const UINT8_CORE_APIS: &[&str] = &[
    "UInt8.add",
    "UInt8.sub",
    "UInt8.mul",
    "UInt8.div",
    "UInt8.mod",
    "UInt8.beq",
    "UInt8.blt",
    "UInt8.ble",
    "UInt8.decEq",
];
const UINT8_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_uint8_reducers",
    "fn test_uint_native_reducer_registration",
    "fn test_reduce_native_fires_for_uint8_add",
];
const UINT16_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const UINT16_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_tests.rs";
const UINT16_CORE_APIS: &[&str] = &[
    "UInt16.add",
    "UInt16.sub",
    "UInt16.mul",
    "UInt16.div",
    "UInt16.mod",
    "UInt16.beq",
    "UInt16.blt",
    "UInt16.ble",
    "UInt16.decEq",
];
const UINT16_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_uint16_reducers",
    "fn test_uint_native_reducer_registration",
];
const UINT32_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const UINT32_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_tests.rs";
const UINT32_CORE_APIS: &[&str] = &[
    "UInt32.add",
    "UInt32.sub",
    "UInt32.mul",
    "UInt32.div",
    "UInt32.mod",
    "UInt32.beq",
    "UInt32.blt",
    "UInt32.ble",
    "UInt32.decEq",
];
const UINT32_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_uint32_reducers",
    "fn test_uint_native_reducer_registration",
];
const UINT64_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const UINT64_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_tests.rs";
const UINT64_CORE_APIS: &[&str] = &[
    "UInt64.add",
    "UInt64.sub",
    "UInt64.mul",
    "UInt64.div",
    "UInt64.mod",
    "UInt64.beq",
    "UInt64.blt",
    "UInt64.ble",
    "UInt64.decEq",
];
const UINT64_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_uint64_reducers",
    "fn test_uint_native_reducer_registration",
];
const USIZE_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const USIZE_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_uint_tests.rs";
const USIZE_CORE_APIS: &[&str] = &[
    "USize.add",
    "USize.sub",
    "USize.mul",
    "USize.div",
    "USize.mod",
    "USize.beq",
    "USize.blt",
    "USize.ble",
    "USize.decEq",
];
const USIZE_CORE_TEST_MARKERS: &[&str] =
    &["fn test_usize_core_native_reducers_are_intentionally_unregistered"];
const UINT8_BITWISE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const UINT8_BITWISE_TESTS: &str =
    "crates/clean-kernel/src/env/native_reducers_uint_bitwise_tests.rs";
const UINT8_BITWISE_APIS: &[&str] = &[
    "UInt8.land",
    "UInt8.lor",
    "UInt8.xor",
    "UInt8.shiftLeft",
    "UInt8.shiftRight",
    "UInt8.complement",
    "UInt8.toNat",
];
const UINT8_BITWISE_TEST_MARKERS: &[&str] = &[
    "land_cases = test_uint8_land_cases",
    "lor_cases = test_uint8_lor_cases",
    "xor_cases = test_uint8_xor_cases",
    "shl_cases = test_uint8_shl_cases",
    "shr_cases = test_uint8_shr_cases",
    "complement_cases = test_uint8_complement_cases",
    "to_nat_cases = test_uint8_to_nat_cases",
    "fn test_uint8_shl_by_10_shifts_by_2",
    "fn test_uint8_shr_128_by_10_shifts_by_2",
];
const UINT16_BITWISE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const UINT16_BITWISE_TESTS: &str =
    "crates/clean-kernel/src/env/native_reducers_uint_bitwise_tests.rs";
const UINT16_BITWISE_APIS: &[&str] = &[
    "UInt16.land",
    "UInt16.lor",
    "UInt16.xor",
    "UInt16.shiftLeft",
    "UInt16.shiftRight",
    "UInt16.complement",
    "UInt16.toNat",
];
const UINT16_BITWISE_TEST_MARKERS: &[&str] = &[
    "land_cases = test_uint16_land_cases",
    "lor_cases = test_uint16_lor_cases",
    "xor_cases = test_uint16_xor_cases",
    "shl_cases = test_uint16_shl_cases",
    "shr_cases = test_uint16_shr_cases",
    "complement_cases = test_uint16_complement_cases",
    "to_nat_cases = test_uint16_to_nat_cases",
    "fn test_uint16_shl_max_by_bitwidth_wraps_to_identity",
];
const UINT32_BITWISE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const UINT32_BITWISE_TESTS: &str =
    "crates/clean-kernel/src/env/native_reducers_uint_bitwise_tests.rs";
const UINT32_BITWISE_APIS: &[&str] = &[
    "UInt32.land",
    "UInt32.lor",
    "UInt32.xor",
    "UInt32.shiftLeft",
    "UInt32.shiftRight",
    "UInt32.complement",
    "UInt32.toNat",
];
const UINT32_BITWISE_TEST_MARKERS: &[&str] = &[
    "land_cases = test_uint32_land_cases",
    "lor_cases = test_uint32_lor_cases",
    "xor_cases = test_uint32_xor_cases",
    "shl_cases = test_uint32_shl_cases",
    "shr_cases = test_uint32_shr_cases",
    "complement_cases = test_uint32_complement_cases",
    "to_nat_cases = test_uint32_to_nat_cases",
    "fn test_uint32_shl_by_32_wraps_to_identity",
];
const UINT64_BITWISE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const UINT64_BITWISE_TESTS: &str =
    "crates/clean-kernel/src/env/native_reducers_uint_bitwise_tests.rs";
const UINT64_BITWISE_APIS: &[&str] = &[
    "UInt64.land",
    "UInt64.lor",
    "UInt64.xor",
    "UInt64.shiftLeft",
    "UInt64.shiftRight",
    "UInt64.complement",
    "UInt64.toNat",
];
const UINT64_BITWISE_TEST_MARKERS: &[&str] = &[
    "land_cases = test_uint64_land_cases",
    "lor_cases = test_uint64_lor_cases",
    "xor_cases = test_uint64_xor_cases",
    "shl_cases = test_uint64_shl_cases",
    "shr_cases = test_uint64_shr_cases",
    "complement_cases = test_uint64_complement_cases",
    "to_nat_cases = test_uint64_to_nat_cases",
    "fn test_uint64_shl_by_64_wraps_to_identity",
    "fn test_uint64_shr_by_64_wraps_to_identity",
];
const USIZE_BITWISE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_uint.rs";
const USIZE_BITWISE_TESTS: &str =
    "crates/clean-kernel/src/env/native_reducers_uint_bitwise_tests.rs";
const USIZE_BITWISE_APIS: &[&str] = &[
    "USize.land",
    "USize.lor",
    "USize.xor",
    "USize.shiftLeft",
    "USize.shiftRight",
    "USize.complement",
    "USize.toNat",
];
const USIZE_BITWISE_TEST_MARKERS: &[&str] =
    &["fn test_usize_bitwise_native_reducers_are_intentionally_unregistered"];
const PLATFORM_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_platform.rs";
const PLATFORM_CORE_APIS: &[&str] = &[
    "System.Platform.getIsWindows",
    "System.Platform.getIsOSX",
    "System.Platform.getIsEmscripten",
];
const PLATFORM_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_get_num_bits_no_longer_registered",
    "fn test_reduce_get_is_windows_returns_false",
    "fn test_reduce_get_is_osx_returns_bool",
    "fn test_reduce_get_is_emscripten_returns_false",
    "fn test_platform_reducers_registered",
];
const FLOAT_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_float.rs";
const FLOAT_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_float_tests.rs";
const FLOAT_CORE_APIS: &[&str] = &[
    "Float.add",
    "Float.sub",
    "Float.mul",
    "Float.div",
    "Float.neg",
    "Float.beq",
    "Float.blt",
    "Float.ble",
];
const FLOAT_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_float_add_basic",
    "fn test_float_sub_basic",
    "fn test_float_mul_basic",
    "fn test_float_div_basic",
    "fn test_float_div_by_zero",
    "fn test_float_neg",
    "fn test_float_beq_equal",
    "fn test_float_beq_not_equal",
    "fn test_float_beq_nan",
    "fn test_float_blt_true",
    "fn test_float_blt_false",
    "fn test_float_ble_equal",
    "fn test_float_reducers_registered",
];
const FLOAT_CLASSIFICATION_APIS: &[&str] = &["Float.isNaN", "Float.isInf", "Float.isFinite"];
const FLOAT_CLASSIFICATION_TEST_MARKERS: &[&str] = &[
    "fn test_float_is_nan_true",
    "fn test_float_is_nan_false",
    "fn test_float_is_inf_true",
    "fn test_float_is_inf_false",
    "fn test_float_is_finite_true",
    "fn test_float_is_finite_nan",
    "fn test_float_reducers_registered",
];
const FLOAT_FUNCTIONS_APIS: &[&str] = &[
    "Float.sqrt",
    "Float.abs",
    "Float.ceil",
    "Float.floor",
    "Float.round",
];
const FLOAT_FUNCTIONS_TEST_MARKERS: &[&str] = &[
    "fn test_float_sqrt",
    "fn test_float_abs_positive",
    "fn test_float_abs_negative",
    "fn test_float_ceil",
    "fn test_float_floor",
    "fn test_float_round",
    "fn test_float_reducers_registered",
];
const FLOAT_INPUT_CONVERSIONS_APIS: &[&str] = &["Float.ofNat", "Float.ofInt", "Float.ofScientific"];
const FLOAT_INPUT_CONVERSIONS_TEST_MARKERS: &[&str] = &[
    "fn test_float_of_nat",
    "fn test_float_of_int_positive",
    "fn test_float_of_int_negative",
    "fn test_float_of_int_neg_succ_large",
    "fn test_float_of_int_zero",
    "fn test_float_of_int_bare_nat",
    "fn test_float_of_scientific_positive_exponent",
    "fn test_float_of_scientific_negative_exponent",
    "fn test_float_reducers_registered",
];
const FLOAT_FORMATTING_APIS: &[&str] = &["Float.toString"];
const FLOAT_FORMATTING_TEST_MARKERS: &[&str] = &[
    "fn test_float_to_string",
    "fn test_float_to_string_nan",
    "fn test_float_reducers_registered",
];
const FLOAT_OUTPUT_CONVERSIONS_APIS: &[&str] = &[
    "Float.toUInt8",
    "Float.toUInt16",
    "Float.toUInt32",
    "Float.toUInt64",
];
const FLOAT_OUTPUT_CONVERSIONS_TEST_MARKERS: &[&str] = &[
    "fn test_float_to_uint8",
    "fn test_float_to_uint8_overflow",
    "fn test_float_to_uint16",
    "fn test_float_to_uint16_overflow",
    "fn test_float_to_uint32",
    "fn test_float_to_uint32_nan",
    "fn test_float_to_uint32_overflow",
    "fn test_float_to_uint64",
    "fn test_float_to_uint64_negative",
    "fn test_float_reducers_registered",
];
const INT_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_int.rs";
const INT_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_int_tests.rs";
const INT_CORE_APIS: &[&str] = &[
    "Int.add",
    "Int.sub",
    "Int.mul",
    "Int.div",
    "Int.mod",
    "Int.neg",
    "Int.natAbs",
    "Int.toNat",
    "Int.beq",
    "Int.blt",
    "Int.ble",
    "Int.decEq",
];
const INT_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_int_add_zero_identity",
    "fn test_int_sub_self_and_zero_are_zero",
    "fn test_int_mul_one_identity",
    "fn test_int_div_truncates_toward_zero_negative_positive",
    "fn test_int_mod_t_remainder_negative_positive",
    "fn test_int_neg_edge_cases",
    "fn test_int_nat_abs_edge_cases",
    "fn test_int_to_nat_edge_cases",
    "fn test_int_beq_edge_cases",
    "fn test_int_blt_edge_cases",
    "fn test_int_ble_edge_cases",
    "fn test_int_dec_eq_edge_cases",
];
const INT8_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_sint.rs";
const INT8_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_sint_tests.rs";
const INT8_CORE_APIS: &[&str] = &[
    "Int8.add",
    "Int8.sub",
    "Int8.mul",
    "Int8.div",
    "Int8.mod",
    "Int8.beq",
    "Int8.blt",
    "Int8.ble",
    "Int8.decEq",
    "Int8.decLt",
    "Int8.decLe",
];
const INT8_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_int8_add_simple",
    "fn test_int8_sub_wrapping",
    "fn test_int8_mul_simple",
    "fn test_int8_div_signed",
    "fn test_int8_mod_signed",
    "fn test_int8_beq_equal",
    "fn test_int8_blt_signed",
    "fn test_int8_ble_signed",
    "fn test_int8_dec_eq_equal",
    "fn test_int8_dec_lt_true",
    "fn test_int8_dec_le_equal",
    "fn test_sint_reducers_registered",
];
const INT16_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_sint.rs";
const INT16_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_sint_tests.rs";
const INT16_CORE_APIS: &[&str] = &[
    "Int16.add",
    "Int16.sub",
    "Int16.mul",
    "Int16.div",
    "Int16.mod",
    "Int16.beq",
    "Int16.blt",
    "Int16.ble",
    "Int16.decEq",
    "Int16.decLt",
    "Int16.decLe",
];
const INT16_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_int16_add_wrapping",
    "fn test_int16_sub_wrapping",
    "fn test_int16_mul_simple",
    "fn test_int16_div_signed",
    "fn test_int16_mod_signed",
    "fn test_int16_beq_equal",
    "fn test_int16_blt_signed",
    "fn test_int16_ble_signed",
    "fn test_int16_dec_eq_equal",
    "fn test_int16_dec_lt_true",
    "fn test_int16_dec_le_equal",
    "fn test_sint_reducers_registered",
];
const INT32_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_sint.rs";
const INT32_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_sint_tests.rs";
const INT32_CORE_APIS: &[&str] = &[
    "Int32.add",
    "Int32.sub",
    "Int32.mul",
    "Int32.div",
    "Int32.mod",
    "Int32.beq",
    "Int32.blt",
    "Int32.ble",
    "Int32.decEq",
    "Int32.decLt",
    "Int32.decLe",
];
const INT32_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_int32_add_simple",
    "fn test_int32_sub_wrapping",
    "fn test_int32_mul_simple",
    "fn test_int32_div_signed",
    "fn test_int32_mod_signed",
    "fn test_int32_beq_equal",
    "fn test_int32_blt_signed",
    "fn test_int32_ble_signed",
    "fn test_int32_dec_eq_equal",
    "fn test_int32_dec_lt_true",
    "fn test_int32_dec_le_equal",
    "fn test_sint_reducers_registered",
];
const INT64_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_sint.rs";
const INT64_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_sint_tests.rs";
const INT64_CORE_APIS: &[&str] = &[
    "Int64.add",
    "Int64.sub",
    "Int64.mul",
    "Int64.div",
    "Int64.mod",
    "Int64.beq",
    "Int64.blt",
    "Int64.ble",
    "Int64.decEq",
    "Int64.decLt",
    "Int64.decLe",
];
const INT64_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_int64_add_wrapping",
    "fn test_int64_sub_wrapping",
    "fn test_int64_mul_simple",
    "fn test_int64_div_signed",
    "fn test_int64_mod_signed",
    "fn test_int64_beq_equal",
    "fn test_int64_blt_signed",
    "fn test_int64_ble_signed",
    "fn test_int64_dec_eq_equal",
    "fn test_int64_dec_lt_true",
    "fn test_int64_dec_le_equal",
    "fn test_sint_reducers_registered",
];
const ISIZE_CORE_SOURCE: &str = "crates/clean-kernel/src/env/native_reducers_sint.rs";
const ISIZE_CORE_TESTS: &str = "crates/clean-kernel/src/env/native_reducers_sint_tests.rs";
const ISIZE_CORE_APIS: &[&str] = &[
    "ISize.add",
    "ISize.sub",
    "ISize.mul",
    "ISize.div",
    "ISize.mod",
    "ISize.beq",
    "ISize.blt",
    "ISize.ble",
    "ISize.decEq",
    "ISize.decLt",
    "ISize.decLe",
];
const ISIZE_CORE_TEST_MARKERS: &[&str] = &[
    "fn test_isize_add_wrapping",
    "fn test_isize_sub_wrapping",
    "fn test_isize_mul_simple",
    "fn test_isize_div_signed",
    "fn test_isize_mod_signed",
    "fn test_isize_beq_equal",
    "fn test_isize_blt_signed",
    "fn test_isize_ble_signed",
    "fn test_isize_dec_eq_equal",
    "fn test_isize_dec_lt_true",
    "fn test_isize_dec_le_equal",
    "fn test_sint_reducers_registered",
];

/// Verbs under `clean replacement native-library`.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum NativeLibraryCommands {
    /// Generate, check, or update the native reducer coverage matrix.
    CoverageMatrix(NativeLibraryCoverageMatrixArgs),
    /// Prove a concrete native API slice from Rust reducer source and tests.
    ApiSlice(NativeLibraryApiSliceArgs),
    /// Report fail-closed native Mathlib API replacement status.
    MathlibApi(NativeLibraryMathlibApiArgs),
}

/// Arguments accepted by `clean replacement native-library coverage-matrix`.
#[derive(Debug, Clone, Args)]
pub(crate) struct NativeLibraryCoverageMatrixArgs {
    /// Emit JSON instead of a compact human-readable summary.
    #[arg(long)]
    pub json: bool,
    /// Compare the checked-in report matrix against the Rust generator.
    #[arg(long, value_name = "REPORT", conflicts_with = "update_report")]
    pub check_report: Option<PathBuf>,
    /// Update a native-library replacement report in place.
    #[arg(long, value_name = "REPORT", conflicts_with = "check_report")]
    pub update_report: Option<PathBuf>,
}

/// Arguments accepted by `clean replacement native-library api-slice`.
#[derive(Debug, Clone, Args)]
pub(crate) struct NativeLibraryApiSliceArgs {
    /// Concrete native API slice to prove.
    #[arg(long, value_enum)]
    pub slice: NativeLibraryApiSliceKind,
    /// Emit JSON instead of a compact human-readable summary.
    #[arg(long)]
    pub json: bool,
}

/// Native API slices with explicit fail-closed evidence contracts.
#[derive(Debug, Clone, Copy, ValueEnum, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum NativeLibraryApiSliceKind {
    /// Nat arithmetic/comparison reducers backed by native_reducers_arith.rs tests.
    NatArithmetic,
    /// Nat bitwise/shift reducers backed by native_reducers_arith.rs tests.
    NatBitwise,
    /// Extended Bool/Nat reducers backed by native_reducers_bool_ext.rs tests.
    BoolNatExt,
    /// Extended String reducers backed by native_reducers_string_ext.rs tests.
    StringExt,
    /// Core String position/character reducers backed by native_reducers_string.rs tests.
    StringCore,
    /// String extraction/casing/intercalation reducers backed by native_reducers_string.rs tests.
    StringTransform,
    /// String hash reducer backed by Lean 4 reference-value tests.
    StringHash,
    /// Core Lean.Name reducers backed by native_reducers_name.rs tests.
    NameCore,
    /// Core Decidable reducers backed by native_reducers_decidable.rs tests.
    DecidableCore,
    /// Focused Decidable equality aliases backed by native_reducers_decidable_aliases.rs tests.
    DecidableEqAliases,
    /// Int order Decidable reducers backed by native_reducers_decidable_ext.rs tests.
    IntOrderDecidable,
    /// Signed Int decidable equality aliases backed by focused reducer tests.
    SignedDecidableEqAliases,
    /// Heterogeneous operation short-circuit reducers backed by focused reducer tests.
    HeteroOps,
    /// BEq.beq short-circuit reducer backed by focused reducer tests.
    BeqShortcircuit,
    /// Decidable decide/combinator reducers backed by focused reducer tests.
    DecidableCombinators,
    /// Nat order Decidable reducers backed by focused reducer tests.
    NatOrderDecidable,
    /// Active core Char reducers backed by native_reducers_char.rs tests.
    CharCore,
    /// Proof that UInt/USize ofNat uses genuine definition reduction, not native reducers.
    UintOfNat,
    /// Fin.val conversion reducer backed by native_reducers_uint_conv.rs tests.
    FinVal,
    /// UInt/USize narrowing conversion reducers backed by native_reducers_uint_conv.rs tests.
    UintNarrowing,
    /// Tested UInt/USize widening conversion reducers backed by native_reducers_uint_conv.rs tests.
    UintWidening,
    /// Core BitVec conversion reducers backed by native_reducers_bitvec.rs tests.
    BitvecCore,
    /// UInt/USize BitVec conversion reducers backed by native_reducers_bitvec.rs tests.
    UintBitvec,
    /// Signed Int/ISize BitVec conversion reducers backed by native_reducers_bitvec.rs tests.
    SignedBitvec,
    /// UInt8 arithmetic/comparison reducers backed by native_reducers_uint.rs tests.
    Uint8Core,
    /// UInt16 arithmetic/comparison reducers backed by native_reducers_uint.rs tests.
    Uint16Core,
    /// UInt32 arithmetic/comparison reducers backed by native_reducers_uint.rs tests.
    Uint32Core,
    /// UInt64 arithmetic/comparison reducers backed by native_reducers_uint.rs tests.
    Uint64Core,
    /// Proof that width-dependent USize arithmetic/comparison stays unregistered.
    UsizeCore,
    /// UInt8 bitwise/shift/toNat reducers backed by native_reducers_uint.rs tests.
    Uint8Bitwise,
    /// UInt16 bitwise/shift/toNat reducers backed by native_reducers_uint.rs tests.
    Uint16Bitwise,
    /// UInt32 bitwise/shift/toNat reducers backed by native_reducers_uint.rs tests.
    Uint32Bitwise,
    /// UInt64 bitwise/shift/toNat reducers backed by native_reducers_uint.rs tests.
    Uint64Bitwise,
    /// Proof that width-dependent USize bitwise/shift/toNat stays unregistered.
    UsizeBitwise,
    /// Platform extern constant reducers backed by native_reducers_platform.rs tests.
    PlatformCore,
    /// Float arithmetic/comparison reducers backed by native_reducers_float.rs tests.
    FloatCore,
    /// Float classification reducers backed by native_reducers_float.rs tests.
    FloatClassification,
    /// Float numeric function reducers backed by native_reducers_float.rs tests.
    FloatFunctions,
    /// Float input conversion reducers backed by native_reducers_float.rs tests.
    FloatInputConversions,
    /// Float formatting reducer backed by native_reducers_float.rs tests.
    FloatFormatting,
    /// Float output conversion reducers backed by native_reducers_float.rs tests.
    FloatOutputConversions,
    /// Core Int reducers backed by native_reducers_int.rs tests.
    IntCore,
    /// Core Int8 reducers backed by native_reducers_sint.rs tests.
    Int8Core,
    /// Core Int16 reducers backed by native_reducers_sint.rs tests.
    Int16Core,
    /// Core Int32 reducers backed by native_reducers_sint.rs tests.
    Int32Core,
    /// Core Int64 reducers backed by native_reducers_sint.rs tests.
    Int64Core,
    /// Core ISize reducers backed by native_reducers_sint.rs tests.
    IsizeCore,
}

/// Arguments accepted by `clean replacement native-library mathlib-api`.
#[derive(Debug, Clone, Args)]
pub(crate) struct NativeLibraryMathlibApiArgs {
    /// Emit JSON instead of a compact human-readable NOT READY report.
    #[arg(long)]
    pub json: bool,
    /// Treat the current compatibility-only NOT READY state as the expected validation result.
    #[arg(long)]
    pub expect_blocked: bool,
}

/// Errors surfaced by native-library replacement evidence commands.
#[derive(Debug, thiserror::Error)]
pub(crate) enum NativeLibraryError {
    /// Reading a native-library input failed.
    #[error("failed to read {path}: {source}")]
    Read {
        path: String,
        #[source]
        source: io::Error,
    },
    /// Writing a native-library output failed.
    #[error("failed to write {path}: {source}")]
    Write {
        path: String,
        #[source]
        source: io::Error,
    },
    /// Parsing a native-library JSON report failed.
    #[error("failed to parse {path}: {source}")]
    ParseJson {
        path: String,
        #[source]
        source: serde_json::Error,
    },
    /// Serializing a native-library JSON report failed.
    #[error("failed to serialize native-library JSON: {0}")]
    Serialize(serde_json::Error),
    /// Writing native-library command output failed.
    #[error("failed to write native-library output: {0}")]
    Io(#[from] io::Error),
    /// Native reducer source parsing failed closed.
    #[error("native-library coverage matrix generation failed: {message}")]
    MatrixGeneration { message: String },
    /// A checked-in native-library report is stale.
    #[error("native-library coverage matrix check failed: {message}")]
    MatrixCheck { message: String },
    /// A concrete native API slice is missing source, registration, or test evidence.
    #[error("native-library API slice check failed: {message}")]
    ApiSlice { message: String },
    /// Native Mathlib API replacement remains unavailable.
    #[error("native Mathlib API replacement is not ready: {message}")]
    MathlibApiNotReady { message: String },
    /// Working directory discovery failed.
    #[error("failed to discover repository root: {0}")]
    RepoRoot(io::Error),
}

/// Dispatch entry point for `clean replacement native-library`.
pub(crate) fn handle_native_library_command(
    command: NativeLibraryCommands,
) -> Result<(), NativeLibraryError> {
    match command {
        NativeLibraryCommands::CoverageMatrix(args) => run_coverage_matrix(args),
        NativeLibraryCommands::ApiSlice(args) => run_api_slice(args),
        NativeLibraryCommands::MathlibApi(args) => run_mathlib_api(args),
    }
}

fn run_coverage_matrix(args: NativeLibraryCoverageMatrixArgs) -> Result<(), NativeLibraryError> {
    let repo_root = discover_repo_root()?;
    let matrix = NativeLibraryCoverageMatrix::build(&repo_root)?;

    if let Some(report_path) = args.update_report {
        let report_path = repo_path(&repo_root, &report_path);
        update_report_matrix(&report_path, &matrix)?;
        let mut out = io::stdout().lock();
        if args.json {
            let check = NativeLibraryMatrixCheck::passed(&report_path, &matrix);
            writeln!(
                out,
                "{}",
                serde_json::to_string_pretty(&check).map_err(NativeLibraryError::Serialize)?
            )?;
        } else {
            writeln!(out, "updated {}", display_path(&repo_root, &report_path))?;
        }
        return Ok(());
    }

    if let Some(report_path) = args.check_report {
        let report_path = repo_path(&repo_root, &report_path);
        let check = NativeLibraryMatrixCheck::from_report(&report_path, &matrix)?;
        let mut out = io::stdout().lock();
        if args.json {
            writeln!(
                out,
                "{}",
                serde_json::to_string_pretty(&check).map_err(NativeLibraryError::Serialize)?
            )?;
        } else {
            render_matrix_check_human(&mut out, &repo_root, &check)?;
        }
        if check.validation_passed {
            return Ok(());
        }
        return Err(NativeLibraryError::MatrixCheck {
            message: check.failures.join("; "),
        });
    }

    let mut out = io::stdout().lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&matrix).map_err(NativeLibraryError::Serialize)?
        )?;
    } else {
        render_matrix_human(&mut out, &matrix)?;
    }
    Ok(())
}

fn run_api_slice(args: NativeLibraryApiSliceArgs) -> Result<(), NativeLibraryError> {
    let repo_root = discover_repo_root()?;
    let report = NativeLibraryApiSliceReport::from_kind(&repo_root, args.slice)?;
    let mut out = io::stdout().lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&report).map_err(NativeLibraryError::Serialize)?
        )?;
    } else {
        render_api_slice_human(&mut out, &report)?;
    }
    if report.validation_passed {
        Ok(())
    } else {
        Err(NativeLibraryError::ApiSlice {
            message: report.failures.join("; "),
        })
    }
}

fn run_mathlib_api(args: NativeLibraryMathlibApiArgs) -> Result<(), NativeLibraryError> {
    let report = NativeLibraryMathlibApiReport::current(args.expect_blocked);
    let mut out = io::stdout().lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&report).map_err(NativeLibraryError::Serialize)?
        )?;
    } else {
        writeln!(out, "Native Mathlib API replacement: NOT READY")?;
        writeln!(out, "status: {}", report.status)?;
        writeln!(out, "validation_passed: {}", report.validation_passed)?;
        writeln!(out, "blocker: {}", report.blocker)?;
    }
    if args.expect_blocked && report.validation_passed {
        return Ok(());
    }
    Err(NativeLibraryError::MathlibApiNotReady {
        message: report.blocker,
    })
}

#[derive(Debug, Clone, Serialize)]
struct NativeLibraryApiSliceReport {
    schema_version: &'static str,
    generated_by: &'static str,
    slice: NativeLibraryApiSliceKind,
    status: &'static str,
    validation_passed: bool,
    api_scope: &'static str,
    coverage_basis: &'static str,
    source_files: Vec<&'static str>,
    test_files: Vec<&'static str>,
    required_apis: Vec<&'static str>,
    registered_apis: Vec<String>,
    required_test_markers: Vec<&'static str>,
    failures: Vec<String>,
    non_claims: Vec<&'static str>,
}

impl NativeLibraryApiSliceReport {
    fn from_kind(
        repo_root: &Path,
        kind: NativeLibraryApiSliceKind,
    ) -> Result<Self, NativeLibraryError> {
        match kind {
            NativeLibraryApiSliceKind::NatArithmetic => Self::nat_arithmetic(repo_root),
            NativeLibraryApiSliceKind::NatBitwise => Self::nat_bitwise(repo_root),
            NativeLibraryApiSliceKind::BoolNatExt => Self::bool_nat_ext(repo_root),
            NativeLibraryApiSliceKind::StringExt => Self::string_ext(repo_root),
            NativeLibraryApiSliceKind::StringCore => Self::string_core(repo_root),
            NativeLibraryApiSliceKind::StringTransform => Self::string_transform(repo_root),
            NativeLibraryApiSliceKind::StringHash => Self::string_hash(repo_root),
            NativeLibraryApiSliceKind::NameCore => Self::name_core(repo_root),
            NativeLibraryApiSliceKind::DecidableCore => Self::decidable_core(repo_root),
            NativeLibraryApiSliceKind::DecidableEqAliases => Self::decidable_eq_aliases(repo_root),
            NativeLibraryApiSliceKind::IntOrderDecidable => Self::int_order_decidable(repo_root),
            NativeLibraryApiSliceKind::SignedDecidableEqAliases => {
                Self::signed_decidable_eq_aliases(repo_root)
            }
            NativeLibraryApiSliceKind::HeteroOps => Self::hetero_ops(repo_root),
            NativeLibraryApiSliceKind::BeqShortcircuit => Self::beq_shortcircuit(repo_root),
            NativeLibraryApiSliceKind::DecidableCombinators => {
                Self::decidable_combinators(repo_root)
            }
            NativeLibraryApiSliceKind::NatOrderDecidable => Self::nat_order_decidable(repo_root),
            NativeLibraryApiSliceKind::CharCore => Self::char_core(repo_root),
            NativeLibraryApiSliceKind::UintOfNat => Self::uint_of_nat(repo_root),
            NativeLibraryApiSliceKind::FinVal => Self::fin_val(repo_root),
            NativeLibraryApiSliceKind::UintNarrowing => Self::uint_narrowing(repo_root),
            NativeLibraryApiSliceKind::UintWidening => Self::uint_widening(repo_root),
            NativeLibraryApiSliceKind::BitvecCore => Self::bitvec_core(repo_root),
            NativeLibraryApiSliceKind::UintBitvec => Self::uint_bitvec(repo_root),
            NativeLibraryApiSliceKind::SignedBitvec => Self::signed_bitvec(repo_root),
            NativeLibraryApiSliceKind::Uint8Core => Self::uint8_core(repo_root),
            NativeLibraryApiSliceKind::Uint16Core => Self::uint16_core(repo_root),
            NativeLibraryApiSliceKind::Uint32Core => Self::uint32_core(repo_root),
            NativeLibraryApiSliceKind::Uint64Core => Self::uint64_core(repo_root),
            NativeLibraryApiSliceKind::UsizeCore => Self::usize_core(repo_root),
            NativeLibraryApiSliceKind::Uint8Bitwise => Self::uint8_bitwise(repo_root),
            NativeLibraryApiSliceKind::Uint16Bitwise => Self::uint16_bitwise(repo_root),
            NativeLibraryApiSliceKind::Uint32Bitwise => Self::uint32_bitwise(repo_root),
            NativeLibraryApiSliceKind::Uint64Bitwise => Self::uint64_bitwise(repo_root),
            NativeLibraryApiSliceKind::UsizeBitwise => Self::usize_bitwise(repo_root),
            NativeLibraryApiSliceKind::PlatformCore => Self::platform_core(repo_root),
            NativeLibraryApiSliceKind::FloatCore => Self::float_core(repo_root),
            NativeLibraryApiSliceKind::FloatClassification => Self::float_classification(repo_root),
            NativeLibraryApiSliceKind::FloatFunctions => Self::float_functions(repo_root),
            NativeLibraryApiSliceKind::FloatInputConversions => {
                Self::float_input_conversions(repo_root)
            }
            NativeLibraryApiSliceKind::FloatFormatting => Self::float_formatting(repo_root),
            NativeLibraryApiSliceKind::FloatOutputConversions => {
                Self::float_output_conversions(repo_root)
            }
            NativeLibraryApiSliceKind::IntCore => Self::int_core(repo_root),
            NativeLibraryApiSliceKind::Int8Core => Self::int8_core(repo_root),
            NativeLibraryApiSliceKind::Int16Core => Self::int16_core(repo_root),
            NativeLibraryApiSliceKind::Int32Core => Self::int32_core(repo_root),
            NativeLibraryApiSliceKind::Int64Core => Self::int64_core(repo_root),
            NativeLibraryApiSliceKind::IsizeCore => Self::isize_core(repo_root),
        }
    }

    fn nat_arithmetic(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::NatArithmetic,
            "Nat arithmetic/comparison native reducers",
            &[NAT_ARITHMETIC_SOURCE],
            &[NAT_ARITHMETIC_TESTS],
            NAT_ARITHMETIC_APIS,
            NAT_ARITHMETIC_TEST_MARKERS,
            "focused Nat arithmetic",
            &[
                "This slice proves only the listed Nat arithmetic/comparison native reducers.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn nat_bitwise(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::NatBitwise,
            "Nat bitwise/shift native reducers",
            &[NAT_ARITHMETIC_SOURCE],
            &[NAT_ARITHMETIC_TESTS],
            NAT_BITWISE_APIS,
            NAT_BITWISE_TEST_MARKERS,
            "focused Nat bitwise/shift",
            &[
                "This slice proves only the listed Nat bitwise and shift native reducers.",
                "This slice does not claim complete Nat, Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn bool_nat_ext(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::BoolNatExt,
            "Bool equality and Nat gcd native reducers",
            &[BOOL_NAT_EXT_SOURCE],
            &[BOOL_NAT_EXT_TESTS],
            BOOL_NAT_EXT_APIS,
            BOOL_NAT_EXT_TEST_MARKERS,
            "focused Bool/Nat extension",
            &[
                "This slice proves only Bool.beq and Nat.gcd native reducers.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn string_ext(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::StringExt,
            "Extended String native reducers",
            &[STRING_EXT_SOURCE],
            &[STRING_EXT_TESTS],
            STRING_EXT_APIS,
            STRING_EXT_TEST_MARKERS,
            "focused String extension",
            &[
                "This slice proves only the listed extended String native reducers.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn string_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::StringCore,
            "Core String position/character native reducers",
            &[STRING_CORE_SOURCE],
            &[STRING_CORE_TESTS],
            STRING_CORE_APIS,
            STRING_CORE_TEST_MARKERS,
            "focused String core position/character",
            &[
                "This slice proves only the listed String position and character native reducers.",
                "String extraction, hashing, casing, and extended search/replace APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn string_transform(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::StringTransform,
            "String extraction/casing/intercalation native reducers",
            &[STRING_CORE_SOURCE],
            &[STRING_CORE_TESTS],
            STRING_TRANSFORM_APIS,
            STRING_TRANSFORM_TEST_MARKERS,
            "focused String extraction/casing/intercalation",
            &[
                "This slice proves only String.extract, String.intercalate, String.take, String.drop, String.toLower, and String.toUpper native reducers.",
                "String hashing, comparison, constructor, position, and extended search/replace APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn string_hash(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::StringHash,
            "String hash native reducer",
            &[STRING_CORE_SOURCE],
            &[STRING_CORE_TESTS],
            STRING_HASH_APIS,
            STRING_HASH_TEST_MARKERS,
            "focused String hash with Lean 4 reference values",
            &[
                "This slice proves only the String.hash native reducer.",
                "String extraction, casing, comparison, and constructor APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn name_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::NameCore,
            "Core Lean.Name native reducers",
            &[NAME_CORE_SOURCE],
            &[NAME_CORE_TESTS],
            NAME_CORE_APIS,
            NAME_CORE_TEST_MARKERS,
            "focused Lean.Name core",
            &[
                "This slice proves only the listed Lean.Name native reducers.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn decidable_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::DecidableCore,
            "Core Decidable native reducers",
            &[DECIDABLE_CORE_SOURCE],
            &[DECIDABLE_CORE_TESTS],
            DECIDABLE_CORE_APIS,
            DECIDABLE_CORE_TEST_MARKERS,
            "focused Decidable core",
            &[
                "This slice proves only the listed core Decidable native reducers.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
                "Computationally irrelevant negative Decidable proof payload limitations remain tracked by the native-library report blocker.",
            ],
        )
    }

    fn decidable_eq_aliases(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::DecidableEqAliases,
            "Focused Decidable equality alias native reducers",
            &[DECIDABLE_EQ_ALIASES_SOURCE],
            &[DECIDABLE_EQ_ALIASES_SOURCE],
            DECIDABLE_EQ_ALIASES_APIS,
            DECIDABLE_EQ_ALIASES_TEST_MARKERS,
            "focused Decidable equality alias",
            &[
                "This slice proves only the listed Decidable equality alias native reducers.",
                "Other Decidable equality aliases in the same source remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn int_order_decidable(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::IntOrderDecidable,
            "Int order Decidable native reducers",
            &[INT_ORDER_DECIDABLE_SOURCE],
            &[INT_ORDER_DECIDABLE_TESTS],
            INT_ORDER_DECIDABLE_APIS,
            INT_ORDER_DECIDABLE_TEST_MARKERS,
            "focused Int order Decidable",
            &[
                "This slice proves only Int.decLe and Int.decLt native reducers.",
                "Int.decEq, instDecidableEqInt, fixed-width signed Int reducers, Decidable aliases, and theorem APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn signed_decidable_eq_aliases(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::SignedDecidableEqAliases,
            "Signed Int Decidable equality alias native reducers",
            SIGNED_DECIDABLE_EQ_ALIAS_SOURCES,
            SIGNED_DECIDABLE_EQ_ALIAS_TESTS,
            SIGNED_DECIDABLE_EQ_ALIAS_APIS,
            SIGNED_DECIDABLE_EQ_ALIAS_TEST_MARKERS,
            "focused signed Int Decidable equality alias",
            &[
                "This slice proves only instDecidableEqInt, instDecidableEqInt8, instDecidableEqInt16, instDecidableEqInt32, instDecidableEqInt64, and instDecidableEqISize native reducer aliases.",
                "Function-form Int.decEq and fixed-width signed Int.decEq reducers are covered by separate scoped evidence; theorem APIs remain separate.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn hetero_ops(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::HeteroOps,
            "Heterogeneous operation short-circuit native reducers",
            &[HETERO_OPS_SOURCE],
            &[HETERO_OPS_SOURCE],
            HETERO_OPS_APIS,
            HETERO_OPS_TEST_MARKERS,
            "focused heterogeneous operation short-circuit",
            &[
                "This slice proves only HAdd.hAdd, HSub.hSub, HMul.hMul, HDiv.hDiv, HMod.hMod, HPow.hPow, and HAppend.hAppend native reducers.",
                "Instance coverage is limited to the reducer-supported Nat arithmetic and String append short-circuit paths; other H* instances remain outside this slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn beq_shortcircuit(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::BeqShortcircuit,
            "BEq.beq short-circuit native reducer",
            &[BEQ_SHORTCIRCUIT_SOURCE],
            &[BEQ_SHORTCIRCUIT_SOURCE],
            BEQ_SHORTCIRCUIT_APIS,
            BEQ_SHORTCIRCUIT_TEST_MARKERS,
            "focused BEq.beq short-circuit",
            &[
                "This slice proves only the BEq.beq native reducer projection shortcut.",
                "Instance coverage is limited to focused reducer tests for Nat, Bool, String, UInt32, Char, Int, and Fin paths; complete BEq instance replacement remains outside this slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn decidable_combinators(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::DecidableCombinators,
            "Decidable decide/combinator native reducers",
            &[DECIDABLE_COMBINATORS_SOURCE],
            &[DECIDABLE_COMBINATORS_TESTS],
            DECIDABLE_COMBINATORS_APIS,
            DECIDABLE_COMBINATORS_TEST_MARKERS,
            "focused Decidable decide/combinator",
            &[
                "This slice proves only decide, Decidable.decide, instDecidableAnd, instDecidableOr, and instDecidableNot native reducers.",
                "The slice requires concrete Decidable.isTrue/isFalse inputs and does not claim complete Decidable proposition or theorem API replacement.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn nat_order_decidable(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::NatOrderDecidable,
            "Nat order Decidable native reducers",
            &[NAT_ORDER_DECIDABLE_SOURCE],
            &[NAT_ORDER_DECIDABLE_TESTS],
            NAT_ORDER_DECIDABLE_APIS,
            NAT_ORDER_DECIDABLE_TEST_MARKERS,
            "focused Nat order Decidable",
            &[
                "This slice proves only Nat.decLe and Nat.decLt native reducers.",
                "instDecidableNatLe and instDecidableNatLt aliases are covered by separate Decidable core evidence; theorem APIs remain separate.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn char_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::CharCore,
            "Core Char native reducers",
            &[CHAR_CORE_SOURCE],
            &[CHAR_CORE_TESTS],
            CHAR_CORE_APIS,
            CHAR_CORE_TEST_MARKERS,
            "focused Char core",
            &[
                "This slice proves only the listed Char native reducers.",
                "Char.ofNat and Char.val are deliberately not registered; genuine definition/projection reduction remains authoritative.",
                "Char.decLe is registered only as a fail-closed reducer that declines until order-proof reconstruction exists.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint_of_nat(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build_absence(
            repo_root,
            NativeLibraryApiSliceKind::UintOfNat,
            "UInt/USize ofNat genuine-definition reduction (native reducers absent)",
            &[UINT_OF_NAT_SOURCE],
            &[UINT_OF_NAT_TESTS],
            UINT_OF_NAT_APIS,
            UINT_OF_NAT_TEST_MARKERS,
            "focused UInt ofNat conversion",
            &[
                "This slice proves the listed UInt/USize ofNat names are intentionally not native reducers.",
                "Each ofNat operation delta-unfolds the environment's genuine definition, avoiding a width-blind or fictional constructor shortcut.",
                "Other UInt/USize conversion reducers in the same source remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn fin_val(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::FinVal,
            "Fin.val native reducer",
            &[FIN_VAL_SOURCE],
            &[FIN_VAL_TESTS],
            FIN_VAL_APIS,
            FIN_VAL_TEST_MARKERS,
            "focused Fin.val conversion",
            &[
                "This slice proves only the Fin.val native reducer.",
                "Other UInt/USize conversion reducers in the same source remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint_narrowing(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::UintNarrowing,
            "UInt/USize narrowing conversion native reducers",
            &[UINT_NARROWING_SOURCE],
            &[UINT_NARROWING_TESTS],
            UINT_NARROWING_APIS,
            UINT_NARROWING_TEST_MARKERS,
            "focused UInt narrowing conversion",
            &[
                "This slice proves only the listed UInt/USize narrowing conversion native reducers.",
                "UInt/USize widening conversion reducers in the same source remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint_widening(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::UintWidening,
            "Tested UInt/USize widening conversion native reducers",
            &[UINT_WIDENING_SOURCE],
            &[UINT_WIDENING_TESTS],
            UINT_WIDENING_APIS,
            UINT_WIDENING_TEST_MARKERS,
            "focused UInt widening conversion",
            &[
                "This slice proves only the listed tested UInt/USize widening conversion native reducers.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn bitvec_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::BitvecCore,
            "Core BitVec conversion native reducers",
            &[BITVEC_CORE_SOURCE],
            &[BITVEC_CORE_TESTS],
            BITVEC_CORE_APIS,
            BITVEC_CORE_TEST_MARKERS,
            "focused BitVec core conversion",
            &[
                "This slice proves only BitVec.ofNat, BitVec.toNat, BitVec.toFin, and BitVec.ofFin native reducers.",
                "UInt/Int BitVec conversion reducers in the same source remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint_bitvec(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::UintBitvec,
            "UInt/USize BitVec conversion native reducers",
            &[UINT_BITVEC_SOURCE],
            &[UINT_BITVEC_TESTS],
            UINT_BITVEC_APIS,
            UINT_BITVEC_TEST_MARKERS,
            "focused UInt BitVec conversion",
            &[
                "This slice proves only the listed UInt/USize toBitVec and ofBitVec native reducers.",
                "Signed Int/ISize BitVec conversion reducers in the same source remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn signed_bitvec(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::SignedBitvec,
            "Signed Int/ISize BitVec conversion native reducers",
            &[SIGNED_BITVEC_SOURCE],
            &[SIGNED_BITVEC_TESTS],
            SIGNED_BITVEC_APIS,
            SIGNED_BITVEC_TEST_MARKERS,
            "focused signed BitVec conversion",
            &[
                "This slice proves only the listed signed Int/ISize toUInt, ofUInt, and toBitVec native reducers.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint8_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Uint8Core,
            "UInt8 arithmetic/comparison native reducers",
            &[UINT8_CORE_SOURCE],
            &[UINT8_CORE_TESTS],
            UINT8_CORE_APIS,
            UINT8_CORE_TEST_MARKERS,
            "focused UInt8 core arithmetic/comparison",
            &[
                "This slice proves only the listed UInt8 arithmetic, comparison, and decEq native reducers.",
                "UInt8 bitwise, shift, complement, and toNat reducers remain outside this narrow slice.",
                "Other UInt widths remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint16_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Uint16Core,
            "UInt16 arithmetic/comparison native reducers",
            &[UINT16_CORE_SOURCE],
            &[UINT16_CORE_TESTS],
            UINT16_CORE_APIS,
            UINT16_CORE_TEST_MARKERS,
            "focused UInt16 core arithmetic/comparison",
            &[
                "This slice proves only the listed UInt16 arithmetic, comparison, and decEq native reducers.",
                "UInt16 bitwise, shift, complement, and toNat reducers remain outside this narrow slice.",
                "Other UInt widths remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint32_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Uint32Core,
            "UInt32 arithmetic/comparison native reducers",
            &[UINT32_CORE_SOURCE],
            &[UINT32_CORE_TESTS],
            UINT32_CORE_APIS,
            UINT32_CORE_TEST_MARKERS,
            "focused UInt32 core arithmetic/comparison",
            &[
                "This slice proves only the listed UInt32 arithmetic, comparison, and decEq native reducers.",
                "UInt32 bitwise, shift, complement, and toNat reducers remain outside this narrow slice.",
                "Other UInt widths remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint64_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Uint64Core,
            "UInt64 arithmetic/comparison native reducers",
            &[UINT64_CORE_SOURCE],
            &[UINT64_CORE_TESTS],
            UINT64_CORE_APIS,
            UINT64_CORE_TEST_MARKERS,
            "focused UInt64 core arithmetic/comparison",
            &[
                "This slice proves only the listed UInt64 arithmetic, comparison, and decEq native reducers.",
                "UInt64 bitwise, shift, complement, and toNat reducers remain outside this narrow slice.",
                "Other UInt widths remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn usize_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build_absence(
            repo_root,
            NativeLibraryApiSliceKind::UsizeCore,
            "Width-dependent USize arithmetic/comparison (native reducers absent)",
            &[USIZE_CORE_SOURCE],
            &[USIZE_CORE_TESTS],
            USIZE_CORE_APIS,
            USIZE_CORE_TEST_MARKERS,
            "focused USize core arithmetic/comparison",
            &[
                "This slice proves the listed width-dependent USize operations are intentionally not native reducers.",
                "System.Platform.numBits remains abstract, so concrete USize computation must stay kernel-stuck rather than assume a host width.",
                "Other UInt widths remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint8_bitwise(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Uint8Bitwise,
            "UInt8 bitwise/shift/toNat native reducers",
            &[UINT8_BITWISE_SOURCE],
            &[UINT8_BITWISE_TESTS],
            UINT8_BITWISE_APIS,
            UINT8_BITWISE_TEST_MARKERS,
            "focused UInt8 bitwise/shift/toNat",
            &[
                "This slice proves only the listed UInt8 bitwise, shift, complement, and toNat native reducers.",
                "UInt16, UInt32, UInt64, and USize bitwise reducers remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint16_bitwise(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Uint16Bitwise,
            "UInt16 bitwise/shift/toNat native reducers",
            &[UINT16_BITWISE_SOURCE],
            &[UINT16_BITWISE_TESTS],
            UINT16_BITWISE_APIS,
            UINT16_BITWISE_TEST_MARKERS,
            "focused UInt16 bitwise/shift/toNat",
            &[
                "This slice proves only the listed UInt16 bitwise, shift, complement, and toNat native reducers.",
                "UInt32, UInt64, and USize bitwise reducers remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint32_bitwise(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Uint32Bitwise,
            "UInt32 bitwise/shift/toNat native reducers",
            &[UINT32_BITWISE_SOURCE],
            &[UINT32_BITWISE_TESTS],
            UINT32_BITWISE_APIS,
            UINT32_BITWISE_TEST_MARKERS,
            "focused UInt32 bitwise/shift/toNat",
            &[
                "This slice proves only the listed UInt32 bitwise, shift, complement, and toNat native reducers.",
                "UInt64 and USize bitwise reducers remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn uint64_bitwise(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Uint64Bitwise,
            "UInt64 bitwise/shift/toNat native reducers",
            &[UINT64_BITWISE_SOURCE],
            &[UINT64_BITWISE_TESTS],
            UINT64_BITWISE_APIS,
            UINT64_BITWISE_TEST_MARKERS,
            "focused UInt64 bitwise/shift/toNat",
            &[
                "This slice proves only the listed UInt64 bitwise, shift, complement, and toNat native reducers.",
                "USize bitwise reducers remain outside this narrow slice.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn usize_bitwise(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build_absence(
            repo_root,
            NativeLibraryApiSliceKind::UsizeBitwise,
            "Width-dependent USize bitwise/shift/toNat (native reducers absent)",
            &[USIZE_BITWISE_SOURCE],
            &[USIZE_BITWISE_TESTS],
            USIZE_BITWISE_APIS,
            USIZE_BITWISE_TEST_MARKERS,
            "focused USize bitwise/shift/toNat",
            &[
                "This slice proves the listed width-dependent USize operations are intentionally not native reducers.",
                "System.Platform.numBits remains abstract, so USize bitwise and shift computation must stay kernel-stuck rather than assume a host width.",
                "This slice does not claim complete UInt/USize native API replacement.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn platform_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::PlatformCore,
            "System.Platform native extern constants",
            &[PLATFORM_CORE_SOURCE],
            &[PLATFORM_CORE_SOURCE],
            PLATFORM_CORE_APIS,
            PLATFORM_CORE_TEST_MARKERS,
            "focused System.Platform extern constant",
            &[
                "This slice proves only the listed System.Platform extern constant native reducers.",
                "System.Platform.getNumBits is deliberately unregistered so target width remains abstract in the kernel.",
                "This slice does not claim complete platform, runtime, or FFI replacement.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn float_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::FloatCore,
            "Float arithmetic/comparison native reducers",
            &[FLOAT_CORE_SOURCE],
            &[FLOAT_CORE_TESTS],
            FLOAT_CORE_APIS,
            FLOAT_CORE_TEST_MARKERS,
            "focused Float arithmetic/comparison",
            &[
                "This slice proves only the listed Float arithmetic/comparison native reducers.",
                "Float Decidable, conversion, formatting, and classification APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn float_classification(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::FloatClassification,
            "Float classification native reducers",
            &[FLOAT_CORE_SOURCE],
            &[FLOAT_CORE_TESTS],
            FLOAT_CLASSIFICATION_APIS,
            FLOAT_CLASSIFICATION_TEST_MARKERS,
            "focused Float classification",
            &[
                "This slice proves only Float.isNaN, Float.isInf, and Float.isFinite native reducers.",
                "Float arithmetic, Decidable, conversion, formatting, and rounding APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn float_functions(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::FloatFunctions,
            "Float numeric function native reducers",
            &[FLOAT_CORE_SOURCE],
            &[FLOAT_CORE_TESTS],
            FLOAT_FUNCTIONS_APIS,
            FLOAT_FUNCTIONS_TEST_MARKERS,
            "focused Float numeric functions",
            &[
                "This slice proves only Float.sqrt, Float.abs, Float.ceil, Float.floor, and Float.round native reducers.",
                "Float arithmetic, classification, Decidable, conversion, and formatting APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn float_input_conversions(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::FloatInputConversions,
            "Float input conversion native reducers",
            &[FLOAT_CORE_SOURCE],
            &[FLOAT_CORE_TESTS],
            FLOAT_INPUT_CONVERSIONS_APIS,
            FLOAT_INPUT_CONVERSIONS_TEST_MARKERS,
            "focused Float input conversions",
            &[
                "This slice proves only Float.ofNat, Float.ofInt, and Float.ofScientific native reducers.",
                "Float output conversion, formatting, Decidable, arithmetic, classification, and rounding APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn float_formatting(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::FloatFormatting,
            "Float formatting native reducer",
            &[FLOAT_CORE_SOURCE],
            &[FLOAT_CORE_TESTS],
            FLOAT_FORMATTING_APIS,
            FLOAT_FORMATTING_TEST_MARKERS,
            "focused Float formatting",
            &[
                "This slice proves only the Float.toString native reducer.",
                "Float output conversion, Decidable, arithmetic, classification, rounding, and input conversion APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn float_output_conversions(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::FloatOutputConversions,
            "Float output conversion native reducers",
            &[FLOAT_CORE_SOURCE],
            &[FLOAT_CORE_TESTS],
            FLOAT_OUTPUT_CONVERSIONS_APIS,
            FLOAT_OUTPUT_CONVERSIONS_TEST_MARKERS,
            "focused Float output conversions",
            &[
                "This slice proves only Float.toUInt8, Float.toUInt16, Float.toUInt32, and Float.toUInt64 native reducers.",
                "Float formatting, Decidable, arithmetic, classification, rounding, and input conversion APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn int_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::IntCore,
            "Int core native reducers",
            &[INT_CORE_SOURCE],
            &[INT_CORE_TESTS],
            INT_CORE_APIS,
            INT_CORE_TEST_MARKERS,
            "focused Int core",
            &[
                "This slice proves only Int.add, Int.sub, Int.mul, Int.div, Int.mod, Int.neg, Int.natAbs, Int.toNat, Int.beq, Int.blt, Int.ble, and Int.decEq native reducers.",
                "UInt, Float, signed fixed-width Int, Decidable alias, and theorem APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn int8_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Int8Core,
            "Int8 core native reducers",
            &[INT8_CORE_SOURCE],
            &[INT8_CORE_TESTS],
            INT8_CORE_APIS,
            INT8_CORE_TEST_MARKERS,
            "focused Int8 core",
            &[
                "This slice proves only Int8.add, Int8.sub, Int8.mul, Int8.div, Int8.mod, Int8.beq, Int8.blt, Int8.ble, Int8.decEq, Int8.decLt, and Int8.decLe native reducers.",
                "Int16, Int32, Int64, ISize, arbitrary-precision Int, UInt, Float, Decidable alias, and theorem APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn int16_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Int16Core,
            "Int16 core native reducers",
            &[INT16_CORE_SOURCE],
            &[INT16_CORE_TESTS],
            INT16_CORE_APIS,
            INT16_CORE_TEST_MARKERS,
            "focused Int16 core",
            &[
                "This slice proves only Int16.add, Int16.sub, Int16.mul, Int16.div, Int16.mod, Int16.beq, Int16.blt, Int16.ble, Int16.decEq, Int16.decLt, and Int16.decLe native reducers.",
                "Int32, Int64, ISize, arbitrary-precision Int, UInt, Float, Decidable alias, and theorem APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn int32_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Int32Core,
            "Int32 core native reducers",
            &[INT32_CORE_SOURCE],
            &[INT32_CORE_TESTS],
            INT32_CORE_APIS,
            INT32_CORE_TEST_MARKERS,
            "focused Int32 core",
            &[
                "This slice proves only Int32.add, Int32.sub, Int32.mul, Int32.div, Int32.mod, Int32.beq, Int32.blt, Int32.ble, Int32.decEq, Int32.decLt, and Int32.decLe native reducers.",
                "Int64, ISize, arbitrary-precision Int, UInt, Float, Decidable alias, and theorem APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn int64_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::Int64Core,
            "Int64 core native reducers",
            &[INT64_CORE_SOURCE],
            &[INT64_CORE_TESTS],
            INT64_CORE_APIS,
            INT64_CORE_TEST_MARKERS,
            "focused Int64 core",
            &[
                "This slice proves only Int64.add, Int64.sub, Int64.mul, Int64.div, Int64.mod, Int64.beq, Int64.blt, Int64.ble, Int64.decEq, Int64.decLt, and Int64.decLe native reducers.",
                "ISize, arbitrary-precision Int, UInt, Float, Decidable alias, and theorem APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn isize_core(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        Self::build(
            repo_root,
            NativeLibraryApiSliceKind::IsizeCore,
            "ISize core native reducers",
            &[ISIZE_CORE_SOURCE],
            &[ISIZE_CORE_TESTS],
            ISIZE_CORE_APIS,
            ISIZE_CORE_TEST_MARKERS,
            "focused ISize core",
            &[
                "This slice proves only ISize.add, ISize.sub, ISize.mul, ISize.div, ISize.mod, ISize.beq, ISize.blt, ISize.ble, ISize.decEq, ISize.decLt, and ISize.decLe native reducers.",
                "Arbitrary-precision Int, UInt, Float, Decidable alias, and theorem APIs remain separate scoped evidence.",
                "This slice does not claim complete Init, Std, or Mathlib API replacement.",
            ],
        )
    }

    fn build(
        repo_root: &Path,
        kind: NativeLibraryApiSliceKind,
        api_scope: &'static str,
        source_files: &[&'static str],
        test_files: &[&'static str],
        required_api_set: &[&'static str],
        required_test_markers: &[&'static str],
        marker_label: &str,
        non_claims: &[&'static str],
    ) -> Result<Self, NativeLibraryError> {
        Self::build_with_registration_expectation(
            repo_root,
            kind,
            api_scope,
            source_files,
            test_files,
            required_api_set,
            required_test_markers,
            marker_label,
            non_claims,
            true,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn build_absence(
        repo_root: &Path,
        kind: NativeLibraryApiSliceKind,
        api_scope: &'static str,
        source_files: &[&'static str],
        test_files: &[&'static str],
        required_api_set: &[&'static str],
        required_test_markers: &[&'static str],
        marker_label: &str,
        non_claims: &[&'static str],
    ) -> Result<Self, NativeLibraryError> {
        Self::build_with_registration_expectation(
            repo_root,
            kind,
            api_scope,
            source_files,
            test_files,
            required_api_set,
            required_test_markers,
            marker_label,
            non_claims,
            false,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn build_with_registration_expectation(
        repo_root: &Path,
        kind: NativeLibraryApiSliceKind,
        api_scope: &'static str,
        source_files: &[&'static str],
        test_files: &[&'static str],
        required_api_set: &[&'static str],
        required_test_markers: &[&'static str],
        marker_label: &str,
        non_claims: &[&'static str],
        expect_registered: bool,
    ) -> Result<Self, NativeLibraryError> {
        let matrix = NativeLibraryCoverageMatrix::build(repo_root)?;
        let registered = matrix
            .matrix_rows
            .iter()
            .flat_map(|row| row.registered_apis.iter().cloned())
            .collect::<BTreeSet<_>>();
        let mut failures = Vec::new();
        let required_apis = required_api_set.to_vec();
        for api in &required_apis {
            if expect_registered && !registered.contains(*api) {
                failures.push(format!("{api} is not registered as a native reducer"));
            } else if !expect_registered && registered.contains(*api) {
                failures.push(format!(
                    "{api} is unexpectedly registered as a native reducer"
                ));
            }
        }

        for source in source_files.iter().chain(test_files.iter()) {
            if !repo_root.join(source).is_file() {
                failures.push(format!("missing required evidence file: {source}"));
            }
        }
        let mut combined_test_text = String::new();
        for test_file in test_files {
            combined_test_text.push_str(&read_to_string(&repo_root.join(test_file))?);
            combined_test_text.push('\n');
        }
        for marker in required_test_markers {
            if !combined_test_text.contains(marker) {
                failures.push(format!("missing {marker_label} test marker: {marker}"));
            }
        }

        let registered_apis = required_apis
            .iter()
            .filter(|api| registered.contains(**api))
            .map(|api| (*api).to_owned())
            .collect::<Vec<_>>();
        Ok(Self {
            schema_version: API_SLICE_SCHEMA_VERSION,
            generated_by: "clean replacement native-library api-slice",
            slice: kind,
            status: if failures.is_empty() {
                "in_progress"
            } else {
                "blocked"
            },
            validation_passed: failures.is_empty(),
            api_scope,
            coverage_basis: if expect_registered {
                "registered native reducer names plus focused Rust reducer tests"
            } else {
                "absence from the native reducer registry plus focused Rust fail-closed tests"
            },
            source_files: source_files.to_vec(),
            test_files: test_files.to_vec(),
            required_apis,
            registered_apis,
            required_test_markers: required_test_markers.to_vec(),
            failures,
            non_claims: non_claims.to_vec(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct NativeLibraryCoverageMatrix {
    schema_version: &'static str,
    generator: &'static str,
    coverage_kind: &'static str,
    complete_api_enumeration: bool,
    scope_note: &'static str,
    source_globs: Vec<&'static str>,
    source_files: Vec<String>,
    totals: NativeLibraryMatrixTotals,
    source_name_census: SourceNameCensus,
    matrix_rows: Vec<NativeLibraryMatrixRow>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct NativeLibraryMatrixTotals {
    matrix_row_count: usize,
    unique_registered_native_api_count: usize,
    init_native_api_count: usize,
    std_native_api_count: usize,
    core_mathlib_native_api_count: usize,
    source_visible_name_count: usize,
    support_only_source_name_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct SourceNameCensus {
    basis: &'static str,
    complete_lean_api_census: bool,
    source_visible_name_count: usize,
    registered_native_api_count: usize,
    support_only_name_count: usize,
    support_only_names: Vec<String>,
    blockers: Vec<&'static str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct NativeLibraryMatrixRow {
    id: &'static str,
    api_scope: &'static str,
    status: &'static str,
    coverage_basis: &'static str,
    source_files: Vec<String>,
    native_api_count: usize,
    registered_apis: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    compatibility_evidence: Vec<&'static str>,
    blockers: Vec<&'static str>,
}

impl NativeLibraryCoverageMatrix {
    fn build(repo_root: &Path) -> Result<Self, NativeLibraryError> {
        let sources = native_reducer_sources(repo_root)?;
        let constants = name_constants(&sources)?;
        let by_source = registered_apis_by_source(repo_root, &sources, &constants)?;
        let source_files = by_source.keys().cloned().collect::<Vec<_>>();
        let init_source_set = INIT_REDUCER_SOURCES
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let init_sources = source_files
            .iter()
            .filter(|source| init_source_set.contains(source.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        let std_sources = source_files
            .iter()
            .filter(|source| !init_source_set.contains(source.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        let init_apis = apis_for_sources(&by_source, &init_sources);
        let std_apis = apis_for_sources(&by_source, &std_sources);
        let unique_apis = init_apis
            .iter()
            .chain(std_apis.iter())
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let source_name_census = source_visible_name_census(&constants, &unique_apis);

        Ok(Self {
            schema_version: MATRIX_SCHEMA_VERSION,
            generator: MATRIX_GENERATOR,
            coverage_kind: "scoped_registered_native_reducer_matrix",
            complete_api_enumeration: false,
            scope_note: "This generated matrix covers clean native reducer registration names only. It is evidence for scoped Init/Std replacement work, not a complete Lean 4 Init, Std, or core-Mathlib API census.",
            source_globs: vec![NATIVE_REDUCER_SOURCE_GLOB],
            source_files,
            totals: NativeLibraryMatrixTotals {
                matrix_row_count: 3,
                unique_registered_native_api_count: unique_apis.len(),
                init_native_api_count: init_apis.len(),
                std_native_api_count: std_apis.len(),
                core_mathlib_native_api_count: 0,
                source_visible_name_count: source_name_census.source_visible_name_count,
                support_only_source_name_count: source_name_census.support_only_name_count,
            },
            source_name_census,
            matrix_rows: vec![
                NativeLibraryMatrixRow {
                    id: "init-native-reducers",
                    api_scope: "Init",
                    status: "in_progress",
                    coverage_basis: "registered native reducer names",
                    source_files: init_sources,
                    native_api_count: init_apis.len(),
                    registered_apis: init_apis,
                    compatibility_evidence: Vec::new(),
                    blockers: vec![
                        "Reducer registrations are scoped native evidence, not complete Init API replacement.",
                        "Some negative Decidable proof payloads still use sorryAx.",
                    ],
                },
                NativeLibraryMatrixRow {
                    id: "std-native-reducers",
                    api_scope: "Std/high-use primitives",
                    status: "in_progress",
                    coverage_basis: "registered native reducer names",
                    source_files: std_sources,
                    native_api_count: std_apis.len(),
                    registered_apis: std_apis,
                    compatibility_evidence: Vec::new(),
                    blockers: vec![
                        "Primitive reducer registrations are not complete Std API replacement.",
                        "Reducer evidence does not cover all Std declarations or theorem APIs.",
                    ],
                },
                NativeLibraryMatrixRow {
                    id: "mathlib-olean-compatibility",
                    api_scope: "core-Mathlib",
                    status: "compatibility_only",
                    coverage_basis: ".olean load/type-check compatibility evidence only",
                    source_files: Vec::new(),
                    native_api_count: 0,
                    registered_apis: Vec::new(),
                    compatibility_evidence: MATHLIB_COMPATIBILITY_EVIDENCE.to_vec(),
                    blockers: vec![
                        "No native core-Mathlib API replacement source is represented in this matrix.",
                        "Mathlib evidence remains .olean compatibility-only.",
                    ],
                },
            ],
        })
    }
}

fn source_visible_name_census(
    constants: &BTreeMap<String, BTreeSet<String>>,
    registered_apis: &[String],
) -> SourceNameCensus {
    let all_source_names = constants
        .values()
        .flat_map(|names| names.iter().cloned())
        .collect::<BTreeSet<_>>();
    let registered = registered_apis.iter().cloned().collect::<BTreeSet<_>>();
    let support_only_names = all_source_names
        .difference(&registered)
        .cloned()
        .collect::<Vec<_>>();
    SourceNameCensus {
        basis: "Lean Name constants in native reducer implementation sources",
        complete_lean_api_census: false,
        source_visible_name_count: all_source_names.len(),
        registered_native_api_count: registered_apis.len(),
        support_only_name_count: support_only_names.len(),
        support_only_names,
        blockers: vec![
            "This census only accounts for Lean names mentioned by native reducer implementation sources.",
            "Support-only names are constructors, instances, proof constructors, or type names used by reducers; they are not counted as native API replacements.",
            "Lean 4 Init, Std, and core-Mathlib declarations not mentioned in native reducer sources remain outside this census.",
        ],
    }
}

fn native_reducer_sources(repo_root: &Path) -> Result<Vec<PathBuf>, NativeLibraryError> {
    let env_dir = repo_root.join("crates/clean-kernel/src/env");
    let mut sources = Vec::new();
    let entries = fs::read_dir(&env_dir).map_err(|source| NativeLibraryError::Read {
        path: env_dir.display().to_string(),
        source,
    })?;
    for entry in entries {
        let entry = entry.map_err(|source| NativeLibraryError::Read {
            path: env_dir.display().to_string(),
            source,
        })?;
        let path = entry.path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if name.starts_with("native_reducers")
            && name.ends_with(".rs")
            && !name.ends_with("_tests.rs")
        {
            sources.push(path);
        }
    }
    sources.sort();
    Ok(sources)
}

fn name_constants(
    sources: &[PathBuf],
) -> Result<BTreeMap<String, BTreeSet<String>>, NativeLibraryError> {
    let mut constants: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for source in sources {
        let text = read_to_string(source)?;
        collect_static_name_constants(&text, &mut constants);
        collect_macro_name_constants(&text, &mut constants);
    }
    Ok(constants)
}

fn collect_static_name_constants(text: &str, constants: &mut BTreeMap<String, BTreeSet<String>>) {
    let mut search_from = 0;
    while let Some(relative_start) = text[search_from..].find("static ") {
        let start = search_from + relative_start + "static ".len();
        let Some(colon_relative) = text[start..].find(':') else {
            break;
        };
        let ident = text[start..start + colon_relative].trim();
        let after_colon = start + colon_relative;
        let Some(name_relative) = text[after_colon..].find("Name::from_string(\"") else {
            search_from = after_colon;
            continue;
        };
        let value_start = after_colon + name_relative + "Name::from_string(\"".len();
        let Some(value_end_relative) = text[value_start..].find('"') else {
            break;
        };
        if is_name_ident(ident) {
            constants
                .entry(ident.to_owned())
                .or_default()
                .insert(text[value_start..value_start + value_end_relative].to_owned());
        }
        search_from = value_start + value_end_relative;
    }
}

fn collect_macro_name_constants(text: &str, constants: &mut BTreeMap<String, BTreeSet<String>>) {
    let mut search_from = 0;
    while let Some(relative_start) = text[search_from..].find("name!(") {
        let body_start = search_from + relative_start + "name!(".len();
        let Some(body_end_relative) = text[body_start..].find(");") else {
            break;
        };
        let body = text[body_start..body_start + body_end_relative].trim();
        let Some(eq_index) = body.find('=') else {
            search_from = body_start + body_end_relative;
            continue;
        };
        let ident = body[..eq_index]
            .trim()
            .strip_prefix("pub(crate)")
            .unwrap_or(body[..eq_index].trim())
            .trim();
        let value_part = body[eq_index + 1..].trim();
        if let Some(lean_name) = quoted_prefix(value_part).filter(|_| is_name_ident(ident)) {
            constants
                .entry(ident.to_owned())
                .or_default()
                .insert(lean_name.to_owned());
        }
        search_from = body_start + body_end_relative;
    }
}

fn registered_apis_by_source(
    repo_root: &Path,
    sources: &[PathBuf],
    constants: &BTreeMap<String, BTreeSet<String>>,
) -> Result<BTreeMap<String, BTreeSet<String>>, NativeLibraryError> {
    let mut by_source = BTreeMap::new();
    for source in sources {
        let rel_source = display_path(repo_root, source);
        let text = read_to_string(source)?;
        let registered_ids = registered_name_ids(&text);
        let unresolved = registered_ids
            .iter()
            .filter(|ident| !constants.contains_key(*ident))
            .cloned()
            .collect::<Vec<_>>();
        if !unresolved.is_empty() {
            return Err(NativeLibraryError::MatrixGeneration {
                message: format!(
                    "{rel_source} has registered native reducer names without Name::from_string constants: {unresolved:?}"
                ),
            });
        }
        let ambiguous = registered_ids
            .iter()
            .filter_map(|ident| {
                let names = constants.get(ident)?;
                (names.len() != 1).then(|| (ident.clone(), names.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        if !ambiguous.is_empty() {
            return Err(NativeLibraryError::MatrixGeneration {
                message: format!(
                    "{rel_source} has ambiguous registered native reducer names: {ambiguous:?}"
                ),
            });
        }
        let apis = registered_ids
            .iter()
            .filter_map(|ident| constants.get(ident).and_then(|names| names.iter().next()))
            .cloned()
            .collect::<BTreeSet<_>>();
        by_source.insert(rel_source, apis);
    }
    Ok(by_source)
}

fn registered_name_ids(text: &str) -> BTreeSet<String> {
    let mut ids = BTreeSet::new();
    let mut search_from = 0;
    while let Some(relative_start) = text[search_from..].find("register_native_reducer(") {
        let start = search_from + relative_start + "register_native_reducer(".len();
        if let Some(ident) = direct_registration_name_id(&text[start..]) {
            ids.insert(ident.to_owned());
        }
        search_from = start;
    }
    for body in macro_invocation_bodies(text, "register_all") {
        let mut body_from = 0;
        while let Some(relative_start) = body[body_from..].find("names::") {
            let start = body_from + relative_start + "names::".len();
            if let Some((ident, end)) = parse_ident(&body[start..]) {
                if body[start + end..].trim_start().starts_with("=>") {
                    ids.insert(ident.to_owned());
                }
                body_from = start + end;
            } else {
                break;
            }
        }
    }
    for macro_name in ["register_uint_width", "register_sint_width"] {
        for body in macro_invocation_bodies(text, macro_name) {
            let mut body_from = 0;
            while let Some(relative_start) = body[body_from..].find("names::") {
                let start = body_from + relative_start + "names::".len();
                if let Some((ident, end)) = parse_ident(&body[start..]) {
                    ids.insert(ident.to_owned());
                    body_from = start + end;
                } else {
                    break;
                }
            }
        }
    }
    ids
}

fn macro_invocation_bodies<'a>(text: &'a str, macro_name: &str) -> Vec<&'a str> {
    let marker = format!("{macro_name}!(");
    let mut bodies = Vec::new();
    let mut search_from = 0;
    while let Some(relative_start) = text[search_from..].find(&marker) {
        let body_start = search_from + relative_start + marker.len();
        let mut depth = 1usize;
        let mut index = body_start;
        for (offset, ch) in text[body_start..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        index = body_start + offset;
                        break;
                    }
                }
                _ => {}
            }
        }
        if depth == 0 {
            bodies.push(&text[body_start..index]);
            search_from = index + 1;
        } else {
            break;
        }
    }
    bodies
}

fn direct_registration_name_id(text: &str) -> Option<&str> {
    let text = text.trim_start();
    let rest = text.strip_prefix("names::")?;
    let (ident, end) = parse_ident(rest)?;
    rest[end..]
        .trim_start()
        .starts_with(".clone()")
        .then_some(ident)
}

fn parse_ident(text: &str) -> Option<(&str, usize)> {
    let end = text
        .char_indices()
        .take_while(|(_, ch)| ch.is_ascii_uppercase() || ch.is_ascii_digit() || *ch == '_')
        .map(|(idx, ch)| idx + ch.len_utf8())
        .last()?;
    Some((&text[..end], end))
}

fn is_name_ident(ident: &str) -> bool {
    let mut chars = ident.chars();
    matches!(chars.next(), Some(ch) if ch.is_ascii_uppercase())
        && chars.all(|ch| ch.is_ascii_uppercase() || ch.is_ascii_digit() || ch == '_')
}

fn quoted_prefix(text: &str) -> Option<&str> {
    let rest = text.strip_prefix('"')?;
    let end = rest.find('"')?;
    Some(&rest[..end])
}

fn apis_for_sources(
    by_source: &BTreeMap<String, BTreeSet<String>>,
    selected_sources: &[String],
) -> Vec<String> {
    selected_sources
        .iter()
        .filter_map(|source| by_source.get(source))
        .flat_map(|apis| apis.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[derive(Debug, Clone, Serialize)]
struct NativeLibraryMatrixCheck {
    schema_version: &'static str,
    generated_by: &'static str,
    report_path: String,
    validation_passed: bool,
    failures: Vec<String>,
    matrix: NativeLibraryCoverageMatrix,
}

impl NativeLibraryMatrixCheck {
    fn passed(report_path: &Path, matrix: &NativeLibraryCoverageMatrix) -> Self {
        Self {
            schema_version: MATRIX_CHECK_SCHEMA_VERSION,
            generated_by: MATRIX_GENERATOR,
            report_path: report_path.display().to_string(),
            validation_passed: true,
            failures: Vec::new(),
            matrix: matrix.clone(),
        }
    }

    fn from_report(
        report_path: &Path,
        matrix: &NativeLibraryCoverageMatrix,
    ) -> Result<Self, NativeLibraryError> {
        let report = read_report_json(report_path)?;
        let actual_matrix = report
            .get("api_coverage_matrix")
            .cloned()
            .unwrap_or(serde_json::Value::Null);
        let expected_matrix =
            serde_json::to_value(matrix).map_err(NativeLibraryError::Serialize)?;
        let failures = if actual_matrix == expected_matrix {
            Vec::new()
        } else {
            vec![
                "api_coverage_matrix does not match Rust-generated native reducer coverage matrix"
                    .to_owned(),
            ]
        };
        Ok(Self {
            schema_version: MATRIX_CHECK_SCHEMA_VERSION,
            generated_by: MATRIX_GENERATOR,
            report_path: report_path.display().to_string(),
            validation_passed: failures.is_empty(),
            failures,
            matrix: matrix.clone(),
        })
    }
}

fn update_report_matrix(
    report_path: &Path,
    matrix: &NativeLibraryCoverageMatrix,
) -> Result<(), NativeLibraryError> {
    let mut report = read_report_json(report_path)?;
    let matrix_value = serde_json::to_value(matrix).map_err(NativeLibraryError::Serialize)?;
    let report_object =
        report
            .as_object_mut()
            .ok_or_else(|| NativeLibraryError::MatrixGeneration {
                message: format!("{} is not a JSON object", report_path.display()),
            })?;
    report_object.insert("api_coverage_matrix".to_owned(), matrix_value);
    if let Some(blockers) = report_object
        .get_mut("overall_blockers")
        .and_then(|value| value.as_array_mut())
    {
        for blocker in blockers {
            if blocker == OLD_MATRIX_BLOCKER {
                *blocker = serde_json::Value::String(SCOPED_MATRIX_BLOCKER.to_owned());
            }
        }
    }
    let text = serde_json::to_string_pretty(&report).map_err(NativeLibraryError::Serialize)?;
    fs::write(report_path, format!("{text}\n")).map_err(|source| NativeLibraryError::Write {
        path: report_path.display().to_string(),
        source,
    })
}

fn read_report_json(report_path: &Path) -> Result<serde_json::Value, NativeLibraryError> {
    let text = read_to_string(report_path)?;
    serde_json::from_str(&text).map_err(|source| NativeLibraryError::ParseJson {
        path: report_path.display().to_string(),
        source,
    })
}

#[derive(Debug, Clone, Serialize)]
struct NativeLibraryMathlibApiReport {
    schema_version: &'static str,
    generated_by: &'static str,
    status: &'static str,
    validation_passed: bool,
    expect_blocked: bool,
    native_mathlib_api_ready: bool,
    compatibility_only: bool,
    native_mathlib_source_present: bool,
    compatibility_evidence: Vec<&'static str>,
    replacement_cli: &'static str,
    blocker: String,
    non_claims: Vec<&'static str>,
}

impl NativeLibraryMathlibApiReport {
    fn current(expect_blocked: bool) -> Self {
        Self {
            schema_version: MATHLIB_API_SCHEMA_VERSION,
            generated_by: "clean replacement native-library mathlib-api",
            status: "blocked",
            validation_passed: expect_blocked,
            expect_blocked,
            native_mathlib_api_ready: false,
            compatibility_only: true,
            native_mathlib_source_present: false,
            compatibility_evidence: MATHLIB_COMPATIBILITY_EVIDENCE.to_vec(),
            replacement_cli: "clean olean verify-batch",
            blocker: "Mathlib evidence remains .olean compatibility-only; no native core-Mathlib API replacement source is represented yet.".to_owned(),
            non_claims: vec![
                "This command does not claim native Mathlib API replacement.",
                "Compatibility-only .olean loading does not certify launch readiness.",
            ],
        }
    }
}

fn render_matrix_human(
    out: &mut dyn Write,
    matrix: &NativeLibraryCoverageMatrix,
) -> io::Result<()> {
    writeln!(out, "native-library coverage matrix")?;
    writeln!(out, "generator: {}", matrix.generator)?;
    writeln!(
        out,
        "registered_native_apis: {}",
        matrix.totals.unique_registered_native_api_count
    )?;
    for row in &matrix.matrix_rows {
        writeln!(
            out,
            "- {}: {} APIs ({})",
            row.id, row.native_api_count, row.status
        )?;
    }
    Ok(())
}

fn render_matrix_check_human(
    out: &mut dyn Write,
    repo_root: &Path,
    check: &NativeLibraryMatrixCheck,
) -> io::Result<()> {
    writeln!(
        out,
        "native-library matrix check: {}",
        if check.validation_passed {
            "PASS"
        } else {
            "FAIL"
        }
    )?;
    writeln!(
        out,
        "report: {}",
        display_path(repo_root, Path::new(&check.report_path))
    )?;
    for failure in &check.failures {
        writeln!(out, "- {failure}")?;
    }
    Ok(())
}

fn render_api_slice_human(
    out: &mut dyn Write,
    report: &NativeLibraryApiSliceReport,
) -> io::Result<()> {
    writeln!(
        out,
        "native-library API slice: {}",
        if report.validation_passed {
            "PASS"
        } else {
            "FAIL"
        }
    )?;
    writeln!(out, "slice: {:?}", report.slice)?;
    writeln!(out, "registered_apis: {}", report.registered_apis.len())?;
    for failure in &report.failures {
        writeln!(out, "- {failure}")?;
    }
    Ok(())
}

fn discover_repo_root() -> Result<PathBuf, NativeLibraryError> {
    let mut dir = std::env::current_dir().map_err(NativeLibraryError::RepoRoot)?;
    loop {
        if dir.join("Cargo.toml").is_file() && dir.join("crates/clean-cli").is_dir() {
            return Ok(dir);
        }
        if !dir.pop() {
            return std::env::current_dir().map_err(NativeLibraryError::RepoRoot);
        }
    }
}

fn repo_path(repo_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo_root.join(path)
    }
}

fn display_path(repo_root: &Path, path: &Path) -> String {
    path.strip_prefix(repo_root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn read_to_string(path: &Path) -> Result<String, NativeLibraryError> {
    fs::read_to_string(path).map_err(|source| NativeLibraryError::Read {
        path: path.display().to_string(),
        source,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coverage_matrix_tracks_current_native_reducer_registrations() {
        let repo_root = discover_repo_root().expect("repo root");
        let matrix = NativeLibraryCoverageMatrix::build(&repo_root).expect("coverage matrix");
        let rows = matrix
            .matrix_rows
            .iter()
            .map(|row| (row.id, row))
            .collect::<BTreeMap<_, _>>();

        assert_eq!(matrix.schema_version, MATRIX_SCHEMA_VERSION);
        assert_eq!(matrix.generator, MATRIX_GENERATOR);
        assert_eq!(matrix.totals.matrix_row_count, matrix.matrix_rows.len());
        assert!(!matrix.complete_api_enumeration);
        assert_eq!(
            rows.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([
                "init-native-reducers",
                "mathlib-olean-compatibility",
                "std-native-reducers"
            ])
        );
        assert!(rows["init-native-reducers"]
            .registered_apis
            .contains(&"ite".to_owned()));
        assert!(rows["init-native-reducers"]
            .registered_apis
            .contains(&"Array.size".to_owned()));
        assert!(rows["std-native-reducers"]
            .registered_apis
            .contains(&"Nat.add".to_owned()));
        assert!(rows["std-native-reducers"]
            .registered_apis
            .contains(&"String.replace".to_owned()));
        assert_eq!(rows["mathlib-olean-compatibility"].native_api_count, 0);
        assert!(rows["mathlib-olean-compatibility"]
            .compatibility_evidence
            .contains(&"crates/clean-cli/src/cmd_olean.rs"));
        assert!(matrix
            .source_name_census
            .support_only_names
            .contains(&"Decidable.isTrue".to_owned()));
    }

    #[test]
    fn checked_in_native_library_report_matrix_matches_rust_generator() {
        let repo_root = discover_repo_root().expect("repo root");
        let report_path = repo_root.join(DEFAULT_REPORT_PATH);
        // The checked-in report needs to exist in its real form for this
        // matrix check; a stub artifact has no `api_coverage_matrix`
        // section. Skip cleanly on machines that don't carry the full
        // generated report.
        if let Ok(text) = std::fs::read_to_string(&report_path) {
            if text.contains("\"stub\": true") {
                eprintln!("SKIP: {} is a stub artifact", report_path.display());
                return;
            }
        }
        let matrix = NativeLibraryCoverageMatrix::build(&repo_root).expect("coverage matrix");
        let check =
            NativeLibraryMatrixCheck::from_report(&report_path, &matrix).expect("matrix check");

        assert!(check.validation_passed, "{:?}", check.failures);
    }

    #[test]
    fn nat_arithmetic_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::NatArithmetic,
        )
        .expect("Nat arithmetic API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), NAT_ARITHMETIC_APIS.len());
        assert!(report.registered_apis.contains(&"Nat.add".to_owned()));
        assert!(report.registered_apis.contains(&"Nat.pow".to_owned()));
        assert_eq!(report.source_files, vec![NAT_ARITHMETIC_SOURCE]);
        assert_eq!(report.test_files, vec![NAT_ARITHMETIC_TESTS]);
    }

    #[test]
    fn nat_bitwise_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::NatBitwise,
        )
        .expect("Nat bitwise API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), NAT_BITWISE_APIS.len());
        assert!(report.registered_apis.contains(&"Nat.land".to_owned()));
        assert!(report.registered_apis.contains(&"Nat.shiftLeft".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Nat.shiftRight".to_owned()));
        assert_eq!(report.source_files, vec![NAT_ARITHMETIC_SOURCE]);
        assert_eq!(report.test_files, vec![NAT_ARITHMETIC_TESTS]);
    }

    #[test]
    fn bool_nat_ext_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::BoolNatExt,
        )
        .expect("Bool/Nat extension API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), BOOL_NAT_EXT_APIS.len());
        assert!(report.registered_apis.contains(&"Bool.beq".to_owned()));
        assert!(report.registered_apis.contains(&"Nat.gcd".to_owned()));
        assert_eq!(report.source_files, vec![BOOL_NAT_EXT_SOURCE]);
        assert_eq!(report.test_files, vec![BOOL_NAT_EXT_TESTS]);
    }

    #[test]
    fn string_ext_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::StringExt,
        )
        .expect("String extension API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), STRING_EXT_APIS.len());
        assert!(report
            .registered_apis
            .contains(&"String.startsWith".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"String.replace".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"String.substrEq".to_owned()));
        assert_eq!(report.source_files, vec![STRING_EXT_SOURCE]);
        assert_eq!(report.test_files, vec![STRING_EXT_TESTS]);
    }

    #[test]
    fn string_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::StringCore,
        )
        .expect("String core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), STRING_CORE_APIS.len());
        assert!(report.registered_apis.contains(&"String.get".to_owned()));
        assert!(report.registered_apis.contains(&"String.next".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"String.singleton".to_owned()));
        assert_eq!(report.source_files, vec![STRING_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![STRING_CORE_TESTS]);
    }

    #[test]
    fn string_hash_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::StringHash,
        )
        .expect("String hash API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), STRING_HASH_APIS.len());
        assert!(report.registered_apis.contains(&"String.hash".to_owned()));
        assert_eq!(report.source_files, vec![STRING_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![STRING_CORE_TESTS]);
    }

    #[test]
    fn string_transform_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::StringTransform,
        )
        .expect("String transform API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), STRING_TRANSFORM_APIS.len());
        for api in STRING_TRANSFORM_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![STRING_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![STRING_CORE_TESTS]);
    }

    #[test]
    fn name_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report =
            NativeLibraryApiSliceReport::from_kind(&repo_root, NativeLibraryApiSliceKind::NameCore)
                .expect("Lean.Name core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), NAME_CORE_APIS.len());
        assert!(report
            .registered_apis
            .contains(&"Lean.Name.mkStr".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Lean.Name.hash".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Lean.Name.append".to_owned()));
        assert_eq!(report.source_files, vec![NAME_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![NAME_CORE_TESTS]);
    }

    #[test]
    fn decidable_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::DecidableCore,
        )
        .expect("Decidable core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), DECIDABLE_CORE_APIS.len());
        assert!(report
            .registered_apis
            .contains(&"instDecidableNatLt".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"instDecidableEqString".to_owned()));
        assert!(report.registered_apis.contains(&"Fin.decEq".to_owned()));
        assert_eq!(report.source_files, vec![DECIDABLE_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![DECIDABLE_CORE_TESTS]);
    }

    #[test]
    fn decidable_eq_aliases_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::DecidableEqAliases,
        )
        .expect("Decidable equality aliases API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(
            report.registered_apis.len(),
            DECIDABLE_EQ_ALIASES_APIS.len()
        );
        assert!(report
            .registered_apis
            .contains(&"instDecidableEqChar".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"instDecidableEqUInt8".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"instDecidableEqFloat".to_owned()));
        assert_eq!(report.source_files, vec![DECIDABLE_EQ_ALIASES_SOURCE]);
        assert_eq!(report.test_files, vec![DECIDABLE_EQ_ALIASES_SOURCE]);
    }

    #[test]
    fn int_order_decidable_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::IntOrderDecidable,
        )
        .expect("Int order Decidable API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), INT_ORDER_DECIDABLE_APIS.len());
        assert!(report.registered_apis.contains(&"Int.decLe".to_owned()));
        assert!(report.registered_apis.contains(&"Int.decLt".to_owned()));
        assert_eq!(report.source_files, vec![INT_ORDER_DECIDABLE_SOURCE]);
        assert_eq!(report.test_files, vec![INT_ORDER_DECIDABLE_TESTS]);
    }

    #[test]
    fn signed_decidable_eq_aliases_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::SignedDecidableEqAliases,
        )
        .expect("Signed Int Decidable equality aliases API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(
            report.registered_apis.len(),
            SIGNED_DECIDABLE_EQ_ALIAS_APIS.len()
        );
        for api in SIGNED_DECIDABLE_EQ_ALIAS_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(
            report.source_files,
            SIGNED_DECIDABLE_EQ_ALIAS_SOURCES
                .iter()
                .map(|path| (*path).to_owned())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            report.test_files,
            SIGNED_DECIDABLE_EQ_ALIAS_TESTS
                .iter()
                .map(|path| (*path).to_owned())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn hetero_ops_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::HeteroOps,
        )
        .expect("heterogeneous operation short-circuit API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), HETERO_OPS_APIS.len());
        for api in HETERO_OPS_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![HETERO_OPS_SOURCE]);
        assert_eq!(report.test_files, vec![HETERO_OPS_SOURCE]);
    }

    #[test]
    fn beq_shortcircuit_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::BeqShortcircuit,
        )
        .expect("BEq.beq short-circuit API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis, vec!["BEq.beq"]);
        assert_eq!(report.source_files, vec![BEQ_SHORTCIRCUIT_SOURCE]);
        assert_eq!(report.test_files, vec![BEQ_SHORTCIRCUIT_SOURCE]);
    }

    #[test]
    fn decidable_combinators_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::DecidableCombinators,
        )
        .expect("Decidable decide/combinator API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(
            report.registered_apis.len(),
            DECIDABLE_COMBINATORS_APIS.len()
        );
        for api in DECIDABLE_COMBINATORS_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![DECIDABLE_COMBINATORS_SOURCE]);
        assert_eq!(report.test_files, vec![DECIDABLE_COMBINATORS_TESTS]);
    }

    #[test]
    fn nat_order_decidable_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::NatOrderDecidable,
        )
        .expect("Nat order Decidable API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), NAT_ORDER_DECIDABLE_APIS.len());
        assert!(report.registered_apis.contains(&"Nat.decLe".to_owned()));
        assert!(report.registered_apis.contains(&"Nat.decLt".to_owned()));
        assert_eq!(report.source_files, vec![NAT_ORDER_DECIDABLE_SOURCE]);
        assert_eq!(report.test_files, vec![NAT_ORDER_DECIDABLE_TESTS]);
    }

    #[test]
    fn char_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report =
            NativeLibraryApiSliceReport::from_kind(&repo_root, NativeLibraryApiSliceKind::CharCore)
                .expect("Char core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), CHAR_CORE_APIS.len());
        assert!(report.registered_apis.contains(&"Char.toNat".to_owned()));
        assert!(report.registered_apis.contains(&"Char.decEq".to_owned()));
        assert!(report.registered_apis.contains(&"Char.toUpper".to_owned()));
        assert_eq!(report.source_files, vec![CHAR_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![CHAR_CORE_TESTS]);
    }

    #[test]
    fn uint_of_nat_native_absence_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::UintOfNat,
        )
        .expect("UInt ofNat API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert!(report.registered_apis.is_empty());
        assert_eq!(report.required_apis, UINT_OF_NAT_APIS);
        assert_eq!(report.source_files, vec![UINT_OF_NAT_SOURCE]);
        assert_eq!(report.test_files, vec![UINT_OF_NAT_TESTS]);
    }

    #[test]
    fn fin_val_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report =
            NativeLibraryApiSliceReport::from_kind(&repo_root, NativeLibraryApiSliceKind::FinVal)
                .expect("Fin.val API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis, vec!["Fin.val".to_owned()]);
        assert_eq!(report.source_files, vec![FIN_VAL_SOURCE]);
        assert_eq!(report.test_files, vec![FIN_VAL_TESTS]);
    }

    #[test]
    fn uint_narrowing_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::UintNarrowing,
        )
        .expect("UInt narrowing API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT_NARROWING_APIS.len());
        assert!(report
            .registered_apis
            .contains(&"UInt16.toUInt8".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt64.toUInt32".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"USize.toUInt32".to_owned()));
        assert_eq!(report.source_files, vec![UINT_NARROWING_SOURCE]);
        assert_eq!(report.test_files, vec![UINT_NARROWING_TESTS]);
    }

    #[test]
    fn uint_widening_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::UintWidening,
        )
        .expect("UInt widening API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT_WIDENING_APIS.len());
        assert!(report
            .registered_apis
            .contains(&"UInt8.toUInt16".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt32.toUInt64".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt16.toUSize".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt32.toUSize".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"USize.toUInt64".to_owned()));
        assert_eq!(report.source_files, vec![UINT_WIDENING_SOURCE]);
        assert_eq!(report.test_files, vec![UINT_WIDENING_TESTS]);
    }

    #[test]
    fn bitvec_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::BitvecCore,
        )
        .expect("BitVec core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), BITVEC_CORE_APIS.len());
        assert!(report.registered_apis.contains(&"BitVec.ofNat".to_owned()));
        assert!(report.registered_apis.contains(&"BitVec.toNat".to_owned()));
        assert!(report.registered_apis.contains(&"BitVec.toFin".to_owned()));
        assert!(report.registered_apis.contains(&"BitVec.ofFin".to_owned()));
        assert_eq!(report.source_files, vec![BITVEC_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![BITVEC_CORE_TESTS]);
    }

    #[test]
    fn uint_bitvec_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::UintBitvec,
        )
        .expect("UInt BitVec API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT_BITVEC_APIS.len());
        assert!(report
            .registered_apis
            .contains(&"UInt8.toBitVec".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"USize.toBitVec".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt32.ofBitVec".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"USize.ofBitVec".to_owned()));
        assert_eq!(report.source_files, vec![UINT_BITVEC_SOURCE]);
        assert_eq!(report.test_files, vec![UINT_BITVEC_TESTS]);
    }

    #[test]
    fn signed_bitvec_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::SignedBitvec,
        )
        .expect("signed BitVec API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), SIGNED_BITVEC_APIS.len());
        assert!(report.registered_apis.contains(&"Int8.toUInt8".to_owned()));
        assert!(report.registered_apis.contains(&"ISize.toUSize".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Int32.ofUInt32".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"ISize.toBitVec".to_owned()));
        assert_eq!(report.source_files, vec![SIGNED_BITVEC_SOURCE]);
        assert_eq!(report.test_files, vec![SIGNED_BITVEC_TESTS]);
    }

    #[test]
    fn uint8_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Uint8Core,
        )
        .expect("UInt8 core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT8_CORE_APIS.len());
        assert!(report.registered_apis.contains(&"UInt8.add".to_owned()));
        assert!(report.registered_apis.contains(&"UInt8.mod".to_owned()));
        assert!(report.registered_apis.contains(&"UInt8.decEq".to_owned()));
        assert_eq!(report.source_files, vec![UINT8_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![UINT8_CORE_TESTS]);
    }

    #[test]
    fn uint16_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Uint16Core,
        )
        .expect("UInt16 core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT16_CORE_APIS.len());
        assert!(report.registered_apis.contains(&"UInt16.add".to_owned()));
        assert!(report.registered_apis.contains(&"UInt16.mod".to_owned()));
        assert!(report.registered_apis.contains(&"UInt16.decEq".to_owned()));
        assert_eq!(report.source_files, vec![UINT16_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![UINT16_CORE_TESTS]);
    }

    #[test]
    fn uint32_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Uint32Core,
        )
        .expect("UInt32 core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT32_CORE_APIS.len());
        assert!(report.registered_apis.contains(&"UInt32.add".to_owned()));
        assert!(report.registered_apis.contains(&"UInt32.mod".to_owned()));
        assert!(report.registered_apis.contains(&"UInt32.decEq".to_owned()));
        assert_eq!(report.source_files, vec![UINT32_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![UINT32_CORE_TESTS]);
    }

    #[test]
    fn uint64_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Uint64Core,
        )
        .expect("UInt64 core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT64_CORE_APIS.len());
        assert!(report.registered_apis.contains(&"UInt64.add".to_owned()));
        assert!(report.registered_apis.contains(&"UInt64.mod".to_owned()));
        assert!(report.registered_apis.contains(&"UInt64.decEq".to_owned()));
        assert_eq!(report.source_files, vec![UINT64_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![UINT64_CORE_TESTS]);
    }

    #[test]
    fn usize_core_native_absence_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::UsizeCore,
        )
        .expect("USize core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert!(report.registered_apis.is_empty());
        assert_eq!(report.required_apis, USIZE_CORE_APIS);
        assert_eq!(report.source_files, vec![USIZE_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![USIZE_CORE_TESTS]);
    }

    #[test]
    fn uint8_bitwise_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Uint8Bitwise,
        )
        .expect("UInt8 bitwise API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT8_BITWISE_APIS.len());
        assert!(report.registered_apis.contains(&"UInt8.land".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt8.shiftLeft".to_owned()));
        assert!(report.registered_apis.contains(&"UInt8.toNat".to_owned()));
        assert_eq!(report.source_files, vec![UINT8_BITWISE_SOURCE]);
        assert_eq!(report.test_files, vec![UINT8_BITWISE_TESTS]);
    }

    #[test]
    fn uint16_bitwise_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Uint16Bitwise,
        )
        .expect("UInt16 bitwise API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT16_BITWISE_APIS.len());
        assert!(report.registered_apis.contains(&"UInt16.land".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt16.shiftLeft".to_owned()));
        assert!(report.registered_apis.contains(&"UInt16.toNat".to_owned()));
        assert_eq!(report.source_files, vec![UINT16_BITWISE_SOURCE]);
        assert_eq!(report.test_files, vec![UINT16_BITWISE_TESTS]);
    }

    #[test]
    fn uint32_bitwise_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Uint32Bitwise,
        )
        .expect("UInt32 bitwise API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT32_BITWISE_APIS.len());
        assert!(report.registered_apis.contains(&"UInt32.land".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt32.shiftLeft".to_owned()));
        assert!(report.registered_apis.contains(&"UInt32.toNat".to_owned()));
        assert_eq!(report.source_files, vec![UINT32_BITWISE_SOURCE]);
        assert_eq!(report.test_files, vec![UINT32_BITWISE_TESTS]);
    }

    #[test]
    fn uint64_bitwise_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Uint64Bitwise,
        )
        .expect("UInt64 bitwise API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), UINT64_BITWISE_APIS.len());
        assert!(report.registered_apis.contains(&"UInt64.land".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"UInt64.shiftLeft".to_owned()));
        assert!(report.registered_apis.contains(&"UInt64.toNat".to_owned()));
        assert_eq!(report.source_files, vec![UINT64_BITWISE_SOURCE]);
        assert_eq!(report.test_files, vec![UINT64_BITWISE_TESTS]);
    }

    #[test]
    fn usize_bitwise_native_absence_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::UsizeBitwise,
        )
        .expect("USize bitwise API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert!(report.registered_apis.is_empty());
        assert_eq!(report.required_apis, USIZE_BITWISE_APIS);
        assert_eq!(report.source_files, vec![USIZE_BITWISE_SOURCE]);
        assert_eq!(report.test_files, vec![USIZE_BITWISE_TESTS]);
    }

    #[test]
    fn platform_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::PlatformCore,
        )
        .expect("System.Platform core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), PLATFORM_CORE_APIS.len());
        assert!(report
            .registered_apis
            .contains(&"System.Platform.getIsWindows".to_owned()));
        assert!(report.source_files.contains(&PLATFORM_CORE_SOURCE));
        assert!(report.test_files.contains(&PLATFORM_CORE_SOURCE));
    }

    #[test]
    fn float_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::FloatCore,
        )
        .expect("Float core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), FLOAT_CORE_APIS.len());
        assert!(report.registered_apis.contains(&"Float.add".to_owned()));
        assert!(report.registered_apis.contains(&"Float.neg".to_owned()));
        assert!(report.registered_apis.contains(&"Float.beq".to_owned()));
        assert!(report.registered_apis.contains(&"Float.ble".to_owned()));
        assert_eq!(report.source_files, vec![FLOAT_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![FLOAT_CORE_TESTS]);
    }

    #[test]
    fn float_classification_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::FloatClassification,
        )
        .expect("Float classification API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(
            report.registered_apis.len(),
            FLOAT_CLASSIFICATION_APIS.len()
        );
        assert!(report.registered_apis.contains(&"Float.isNaN".to_owned()));
        assert!(report.registered_apis.contains(&"Float.isInf".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Float.isFinite".to_owned()));
        assert_eq!(report.source_files, vec![FLOAT_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![FLOAT_CORE_TESTS]);
    }

    #[test]
    fn float_functions_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::FloatFunctions,
        )
        .expect("Float functions API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), FLOAT_FUNCTIONS_APIS.len());
        assert!(report.registered_apis.contains(&"Float.sqrt".to_owned()));
        assert!(report.registered_apis.contains(&"Float.abs".to_owned()));
        assert!(report.registered_apis.contains(&"Float.ceil".to_owned()));
        assert!(report.registered_apis.contains(&"Float.floor".to_owned()));
        assert!(report.registered_apis.contains(&"Float.round".to_owned()));
        assert_eq!(report.source_files, vec![FLOAT_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![FLOAT_CORE_TESTS]);
    }

    #[test]
    fn float_input_conversions_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::FloatInputConversions,
        )
        .expect("Float input conversions API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(
            report.registered_apis.len(),
            FLOAT_INPUT_CONVERSIONS_APIS.len()
        );
        assert!(report.registered_apis.contains(&"Float.ofNat".to_owned()));
        assert!(report.registered_apis.contains(&"Float.ofInt".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Float.ofScientific".to_owned()));
        assert_eq!(report.source_files, vec![FLOAT_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![FLOAT_CORE_TESTS]);
    }

    #[test]
    fn float_formatting_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::FloatFormatting,
        )
        .expect("Float formatting API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), FLOAT_FORMATTING_APIS.len());
        assert!(report
            .registered_apis
            .contains(&"Float.toString".to_owned()));
        assert_eq!(report.source_files, vec![FLOAT_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![FLOAT_CORE_TESTS]);
    }

    #[test]
    fn float_output_conversions_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::FloatOutputConversions,
        )
        .expect("Float output conversions API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(
            report.registered_apis.len(),
            FLOAT_OUTPUT_CONVERSIONS_APIS.len()
        );
        assert!(report.registered_apis.contains(&"Float.toUInt8".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Float.toUInt16".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Float.toUInt32".to_owned()));
        assert!(report
            .registered_apis
            .contains(&"Float.toUInt64".to_owned()));
        assert_eq!(report.source_files, vec![FLOAT_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![FLOAT_CORE_TESTS]);
    }

    #[test]
    fn int_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report =
            NativeLibraryApiSliceReport::from_kind(&repo_root, NativeLibraryApiSliceKind::IntCore)
                .expect("Int core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), INT_CORE_APIS.len());
        for api in INT_CORE_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![INT_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![INT_CORE_TESTS]);
    }

    #[test]
    fn int8_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report =
            NativeLibraryApiSliceReport::from_kind(&repo_root, NativeLibraryApiSliceKind::Int8Core)
                .expect("Int8 core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), INT8_CORE_APIS.len());
        for api in INT8_CORE_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![INT8_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![INT8_CORE_TESTS]);
    }

    #[test]
    fn int16_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Int16Core,
        )
        .expect("Int16 core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), INT16_CORE_APIS.len());
        for api in INT16_CORE_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![INT16_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![INT16_CORE_TESTS]);
    }

    #[test]
    fn int32_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Int32Core,
        )
        .expect("Int32 core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), INT32_CORE_APIS.len());
        for api in INT32_CORE_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![INT32_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![INT32_CORE_TESTS]);
    }

    #[test]
    fn int64_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::Int64Core,
        )
        .expect("Int64 core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), INT64_CORE_APIS.len());
        for api in INT64_CORE_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![INT64_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![INT64_CORE_TESTS]);
    }

    #[test]
    fn isize_core_api_slice_is_rust_proven() {
        let repo_root = discover_repo_root().expect("repo root");
        let report = NativeLibraryApiSliceReport::from_kind(
            &repo_root,
            NativeLibraryApiSliceKind::IsizeCore,
        )
        .expect("ISize core API slice");

        assert!(report.validation_passed, "{:?}", report.failures);
        assert_eq!(report.status, "in_progress");
        assert_eq!(report.registered_apis.len(), ISIZE_CORE_APIS.len());
        for api in ISIZE_CORE_APIS {
            assert!(
                report.registered_apis.contains(&(*api).to_owned()),
                "missing registered API {api}"
            );
        }
        assert_eq!(report.source_files, vec![ISIZE_CORE_SOURCE]);
        assert_eq!(report.test_files, vec![ISIZE_CORE_TESTS]);
    }

    #[test]
    fn mathlib_api_report_is_fail_closed_compatibility_only() {
        let report = NativeLibraryMathlibApiReport::current(false);

        assert_eq!(report.status, "blocked");
        assert!(!report.validation_passed);
        assert!(!report.native_mathlib_api_ready);
        assert!(report.compatibility_only);
        assert!(!report.native_mathlib_source_present);
        assert_eq!(report.replacement_cli, "clean olean verify-batch");
        assert!(report
            .blocker
            .contains("no native core-Mathlib API replacement source"));
    }

    #[test]
    fn mathlib_api_report_can_validate_expected_blocked_state() {
        let report = NativeLibraryMathlibApiReport::current(true);

        assert_eq!(report.status, "blocked");
        assert!(report.validation_passed);
        assert!(report.expect_blocked);
        assert!(report.compatibility_only);
        assert!(!report.native_mathlib_api_ready);
    }
}
