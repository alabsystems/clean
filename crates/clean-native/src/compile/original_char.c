// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#include "clean_runtime.h"

// The selected Init.Prelude IR borrows n. Our boxed boundary consumes it.
// Each comparison takes an owned reference and returns an immediate Bool.
clean_obj* l_Char_ofNat(clean_obj* n) {
    clean_inc(n);
    if (clean_unbox(l_Nat_decLt(n, clean_box(55296)))) {
        return l_Char_ofNatAux(n, clean_box(0));
    }
    clean_inc(n);
    if (clean_unbox(l_Nat_decLt(clean_box(57343), n))) {
        clean_inc(n);
        if (clean_unbox(l_Nat_decLt(n, clean_box(1114112)))) {
            return l_Char_ofNatAux(n, clean_box(0));
        }
    }
    clean_dec(n);
    return l_UInt32_ofBitVec(clean_box(0));
}
