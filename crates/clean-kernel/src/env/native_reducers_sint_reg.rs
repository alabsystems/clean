// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Registration of signed fixed-width int native reducers on the Environment.
//! Split from native_reducers_sint.rs for file size.

use super::*;

macro_rules! register_sint_width {
    ($env:expr,
     $ADD_N:expr, $SUB_N:expr, $MUL_N:expr, $DIV_N:expr, $MOD_N:expr,
     $BEQ_N:expr, $BLT_N:expr, $BLE_N:expr,
     $DEC_EQ_N:expr, $DEC_LT_N:expr, $DEC_LE_N:expr,
     $add:expr, $sub:expr, $mul:expr, $div:expr, $mod_:expr,
     $beq:expr, $blt:expr, $ble:expr,
     $dec_eq:expr, $dec_lt:expr, $dec_le:expr
    ) => {{
        $env.register_native_reducer($ADD_N.clone(), $add as NativeReducerFn);
        $env.register_native_reducer($SUB_N.clone(), $sub as NativeReducerFn);
        $env.register_native_reducer($MUL_N.clone(), $mul as NativeReducerFn);
        $env.register_native_reducer($DIV_N.clone(), $div as NativeReducerFn);
        $env.register_native_reducer($MOD_N.clone(), $mod_ as NativeReducerFn);
        $env.register_native_reducer($BEQ_N.clone(), $beq as NativeReducerFn);
        $env.register_native_reducer($BLT_N.clone(), $blt as NativeReducerFn);
        $env.register_native_reducer($BLE_N.clone(), $ble as NativeReducerFn);
        $env.register_native_reducer($DEC_EQ_N.clone(), $dec_eq as NativeReducerFn);
        $env.register_native_reducer($DEC_LT_N.clone(), $dec_lt as NativeReducerFn);
        $env.register_native_reducer($DEC_LE_N.clone(), $dec_le as NativeReducerFn);
    }};
}

impl Environment {
    /// Register all signed fixed-width int native reducers.
    /// 5 widths x 11 ops = 55 reducers + 5 decidable instance aliases = 60 total.
    pub(crate) fn init_sint_native_reducers(&mut self) {
        // Int8: 11 operations
        register_sint_width!(
            self,
            names::INT8_ADD,
            names::INT8_SUB,
            names::INT8_MUL,
            names::INT8_DIV,
            names::INT8_MOD,
            names::INT8_BEQ,
            names::INT8_BLT,
            names::INT8_BLE,
            names::INT8_DEC_EQ,
            names::INT8_DEC_LT,
            names::INT8_DEC_LE,
            reduce_int8_add,
            reduce_int8_sub,
            reduce_int8_mul,
            reduce_int8_div,
            reduce_int8_mod,
            reduce_int8_beq,
            reduce_int8_blt,
            reduce_int8_ble,
            reduce_int8_dec_eq,
            reduce_int8_dec_lt,
            reduce_int8_dec_le
        );
        // Int16: 11 operations
        register_sint_width!(
            self,
            names::INT16_ADD,
            names::INT16_SUB,
            names::INT16_MUL,
            names::INT16_DIV,
            names::INT16_MOD,
            names::INT16_BEQ,
            names::INT16_BLT,
            names::INT16_BLE,
            names::INT16_DEC_EQ,
            names::INT16_DEC_LT,
            names::INT16_DEC_LE,
            reduce_int16_add,
            reduce_int16_sub,
            reduce_int16_mul,
            reduce_int16_div,
            reduce_int16_mod,
            reduce_int16_beq,
            reduce_int16_blt,
            reduce_int16_ble,
            reduce_int16_dec_eq,
            reduce_int16_dec_lt,
            reduce_int16_dec_le
        );
        // Int32: 11 operations
        register_sint_width!(
            self,
            names::INT32_ADD,
            names::INT32_SUB,
            names::INT32_MUL,
            names::INT32_DIV,
            names::INT32_MOD,
            names::INT32_BEQ,
            names::INT32_BLT,
            names::INT32_BLE,
            names::INT32_DEC_EQ,
            names::INT32_DEC_LT,
            names::INT32_DEC_LE,
            reduce_int32_add,
            reduce_int32_sub,
            reduce_int32_mul,
            reduce_int32_div,
            reduce_int32_mod,
            reduce_int32_beq,
            reduce_int32_blt,
            reduce_int32_ble,
            reduce_int32_dec_eq,
            reduce_int32_dec_lt,
            reduce_int32_dec_le
        );
        // Int64: 11 operations
        register_sint_width!(
            self,
            names::INT64_ADD,
            names::INT64_SUB,
            names::INT64_MUL,
            names::INT64_DIV,
            names::INT64_MOD,
            names::INT64_BEQ,
            names::INT64_BLT,
            names::INT64_BLE,
            names::INT64_DEC_EQ,
            names::INT64_DEC_LT,
            names::INT64_DEC_LE,
            reduce_int64_add,
            reduce_int64_sub,
            reduce_int64_mul,
            reduce_int64_div,
            reduce_int64_mod,
            reduce_int64_beq,
            reduce_int64_blt,
            reduce_int64_ble,
            reduce_int64_dec_eq,
            reduce_int64_dec_lt,
            reduce_int64_dec_le
        );
        // ISize: 11 operations
        register_sint_width!(
            self,
            names::ISIZE_ADD,
            names::ISIZE_SUB,
            names::ISIZE_MUL,
            names::ISIZE_DIV,
            names::ISIZE_MOD,
            names::ISIZE_BEQ,
            names::ISIZE_BLT,
            names::ISIZE_BLE,
            names::ISIZE_DEC_EQ,
            names::ISIZE_DEC_LT,
            names::ISIZE_DEC_LE,
            reduce_isize_add,
            reduce_isize_sub,
            reduce_isize_mul,
            reduce_isize_div,
            reduce_isize_mod,
            reduce_isize_beq,
            reduce_isize_blt,
            reduce_isize_ble,
            reduce_isize_dec_eq,
            reduce_isize_dec_lt,
            reduce_isize_dec_le
        );

        // Instance name aliases for decidable equality
        self.register_native_reducer(
            names::INST_DEC_EQ_INT8.clone(),
            reduce_int8_dec_eq as NativeReducerFn,
        );
        self.register_native_reducer(
            names::INST_DEC_EQ_INT16.clone(),
            reduce_int16_dec_eq as NativeReducerFn,
        );
        self.register_native_reducer(
            names::INST_DEC_EQ_INT32.clone(),
            reduce_int32_dec_eq as NativeReducerFn,
        );
        self.register_native_reducer(
            names::INST_DEC_EQ_INT64.clone(),
            reduce_int64_dec_eq as NativeReducerFn,
        );
        self.register_native_reducer(
            names::INST_DEC_EQ_ISIZE.clone(),
            reduce_isize_dec_eq as NativeReducerFn,
        );
    }
}
