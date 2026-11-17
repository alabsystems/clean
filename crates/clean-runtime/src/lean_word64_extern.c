/* Copyright 2026 Andrew Yates | Apache-2.0
 *
 * Optional source DATA for materializing the scalar externs named by the
 * pinned Lean UInt64 declarations. Compile this separate translation unit
 * with the corresponding, retained Lean include directory. It forwards the
 * actual header definitions; it does not duplicate their arithmetic.
 *
 * This source is not selected by the normal runtime build. In particular it
 * supplies neither a boxed closure adapter nor source/ABI/NoUB evidence, and
 * it does not authorize a compiler to accept a previously refused call.
 */
#define lean_uint64_add lean_uint64_add__clean_header_owner
#define lean_uint64_mul lean_uint64_mul__clean_header_owner
#include <lean/lean.h>
#undef lean_uint64_add
#undef lean_uint64_mul

_Static_assert(_Generic(&lean_uint64_add__clean_header_owner,
    uint64_t (*)(uint64_t, uint64_t): 1, default: 0), "header add ABI");
_Static_assert(_Generic(&lean_uint64_mul__clean_header_owner,
    uint64_t (*)(uint64_t, uint64_t): 1, default: 0), "header mul ABI");

uint64_t lean_uint64_add(uint64_t left, uint64_t right) {
    return lean_uint64_add__clean_header_owner(left, right);
}

uint64_t lean_uint64_mul(uint64_t left, uint64_t right) {
    return lean_uint64_mul__clean_header_owner(left, right);
}
