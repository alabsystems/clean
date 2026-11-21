// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#include "clean_runtime.h"

// The checked Lean type is {σ : Type} → σ → Void σ. Clean's generic calls
// pass the erased type argument as well as the owned, boxed value.
clean_obj* l_Void_mk(clean_obj* type, clean_obj* value) {
    clean_dec(type);
    clean_dec(value);
    return clean_box(0);
}
