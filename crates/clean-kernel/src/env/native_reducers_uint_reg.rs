// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Registration of UInt native reducers on the Environment.
//! Split from native_reducers_uint.rs for file size.

use super::*;

macro_rules! register_uint_width {
    ($env:expr,
     $ADD_N:expr, $SUB_N:expr, $MUL_N:expr, $DIV_N:expr, $MOD_N:expr,
     $BEQ_N:expr, $BLT_N:expr, $BLE_N:expr, $DEC_EQ_N:expr, $DEC_LT_N:expr,
     $LAND_N:expr, $LOR_N:expr, $XOR_N:expr,
     $SHL_N:expr, $SHR_N:expr, $COMPL_N:expr, $TONAT_N:expr,
     $add:expr, $sub:expr, $mul:expr, $div:expr, $mod_:expr,
     $beq:expr, $blt:expr, $ble:expr, $dec_eq:expr, $dec_lt:expr,
     $land:expr, $lor:expr, $xor:expr,
     $shl:expr, $shr:expr, $compl:expr, $to_nat:expr
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
        $env.register_native_reducer($LAND_N.clone(), $land as NativeReducerFn);
        $env.register_native_reducer($LOR_N.clone(), $lor as NativeReducerFn);
        $env.register_native_reducer($XOR_N.clone(), $xor as NativeReducerFn);
        $env.register_native_reducer($SHL_N.clone(), $shl as NativeReducerFn);
        $env.register_native_reducer($SHR_N.clone(), $shr as NativeReducerFn);
        $env.register_native_reducer($COMPL_N.clone(), $compl as NativeReducerFn);
        $env.register_native_reducer($TONAT_N.clone(), $to_nat as NativeReducerFn);
    }};
}

impl Environment {
    /// Register all UInt native reducers (5 widths x 17 ops = 85 reducers).
    pub(crate) fn init_uint_native_reducers(&mut self) {
        register_uint_width!(
            self,
            names::UINT8_ADD,
            names::UINT8_SUB,
            names::UINT8_MUL,
            names::UINT8_DIV,
            names::UINT8_MOD,
            names::UINT8_BEQ,
            names::UINT8_BLT,
            names::UINT8_BLE,
            names::UINT8_DEC_EQ,
            names::UINT8_DEC_LT,
            names::UINT8_LAND,
            names::UINT8_LOR,
            names::UINT8_XOR,
            names::UINT8_SHIFT_LEFT,
            names::UINT8_SHIFT_RIGHT,
            names::UINT8_COMPLEMENT,
            names::UINT8_TO_NAT,
            reduce_uint8_add,
            reduce_uint8_sub,
            reduce_uint8_mul,
            reduce_uint8_div,
            reduce_uint8_mod,
            reduce_uint8_beq,
            reduce_uint8_blt,
            reduce_uint8_ble,
            reduce_uint8_dec_eq,
            reduce_uint8_dec_lt,
            reduce_uint8_land,
            reduce_uint8_lor,
            reduce_uint8_xor,
            reduce_uint8_shl,
            reduce_uint8_shr,
            reduce_uint8_compl,
            reduce_uint8_to_nat
        );
        register_uint_width!(
            self,
            names::UINT16_ADD,
            names::UINT16_SUB,
            names::UINT16_MUL,
            names::UINT16_DIV,
            names::UINT16_MOD,
            names::UINT16_BEQ,
            names::UINT16_BLT,
            names::UINT16_BLE,
            names::UINT16_DEC_EQ,
            names::UINT16_DEC_LT,
            names::UINT16_LAND,
            names::UINT16_LOR,
            names::UINT16_XOR,
            names::UINT16_SHIFT_LEFT,
            names::UINT16_SHIFT_RIGHT,
            names::UINT16_COMPLEMENT,
            names::UINT16_TO_NAT,
            reduce_uint16_add,
            reduce_uint16_sub,
            reduce_uint16_mul,
            reduce_uint16_div,
            reduce_uint16_mod,
            reduce_uint16_beq,
            reduce_uint16_blt,
            reduce_uint16_ble,
            reduce_uint16_dec_eq,
            reduce_uint16_dec_lt,
            reduce_uint16_land,
            reduce_uint16_lor,
            reduce_uint16_xor,
            reduce_uint16_shl,
            reduce_uint16_shr,
            reduce_uint16_compl,
            reduce_uint16_to_nat
        );
        register_uint_width!(
            self,
            names::UINT32_ADD,
            names::UINT32_SUB,
            names::UINT32_MUL,
            names::UINT32_DIV,
            names::UINT32_MOD,
            names::UINT32_BEQ,
            names::UINT32_BLT,
            names::UINT32_BLE,
            names::UINT32_DEC_EQ,
            names::UINT32_DEC_LT,
            names::UINT32_LAND,
            names::UINT32_LOR,
            names::UINT32_XOR,
            names::UINT32_SHIFT_LEFT,
            names::UINT32_SHIFT_RIGHT,
            names::UINT32_COMPLEMENT,
            names::UINT32_TO_NAT,
            reduce_uint32_add,
            reduce_uint32_sub,
            reduce_uint32_mul,
            reduce_uint32_div,
            reduce_uint32_mod,
            reduce_uint32_beq,
            reduce_uint32_blt,
            reduce_uint32_ble,
            reduce_uint32_dec_eq,
            reduce_uint32_dec_lt,
            reduce_uint32_land,
            reduce_uint32_lor,
            reduce_uint32_xor,
            reduce_uint32_shl,
            reduce_uint32_shr,
            reduce_uint32_compl,
            reduce_uint32_to_nat
        );
        register_uint_width!(
            self,
            names::UINT64_ADD,
            names::UINT64_SUB,
            names::UINT64_MUL,
            names::UINT64_DIV,
            names::UINT64_MOD,
            names::UINT64_BEQ,
            names::UINT64_BLT,
            names::UINT64_BLE,
            names::UINT64_DEC_EQ,
            names::UINT64_DEC_LT,
            names::UINT64_LAND,
            names::UINT64_LOR,
            names::UINT64_XOR,
            names::UINT64_SHIFT_LEFT,
            names::UINT64_SHIFT_RIGHT,
            names::UINT64_COMPLEMENT,
            names::UINT64_TO_NAT,
            reduce_uint64_add,
            reduce_uint64_sub,
            reduce_uint64_mul,
            reduce_uint64_div,
            reduce_uint64_mod,
            reduce_uint64_beq,
            reduce_uint64_blt,
            reduce_uint64_ble,
            reduce_uint64_dec_eq,
            reduce_uint64_dec_lt,
            reduce_uint64_land,
            reduce_uint64_lor,
            reduce_uint64_xor,
            reduce_uint64_shl,
            reduce_uint64_shr,
            reduce_uint64_compl,
            reduce_uint64_to_nat
        );
        // USize native reducers are DELETED (carrier-parity Phase 1, §7.4):
        // genuine v4.30 USize is width-abstract (opaque
        // `System.Platform.getNumBits`), so width-dependent USize ops are STUCK
        // in Lean's kernel. Computing them was a def-eq excess (silently
        // axiomatizing `numBits = 64`). Clean now matches Lean's stuckness.
    }
}
