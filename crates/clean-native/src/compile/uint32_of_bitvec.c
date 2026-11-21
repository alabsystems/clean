// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#include "clean_runtime.h"

clean_obj* l_UInt32_ofBitVec(clean_obj* bits) {
    unsigned __int128 value = clean_nat_to_u128(bits);
    if (value > UINT32_MAX) clean_panic("invalid BitVec 32 carrier");
    clean_dec(bits);
    return clean_box_uint32((uint32_t)value);
}
