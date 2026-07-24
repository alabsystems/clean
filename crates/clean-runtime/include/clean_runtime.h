/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * SPDX-License-Identifier: Apache-2.0
 *
 * clean Runtime Library - C Header
 *
 * Provides memory management primitives for compiled clean programs.
 * Based on Lean 4's runtime (lean4/src/runtime/object.h).
 *
 * Part of #963 - Compiler IR infrastructure (Phase 4).
 */

#ifndef CLEAN_RUNTIME_H
#define CLEAN_RUNTIME_H

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>
#include <assert.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ============================================================================
 * Object Representation
 * ============================================================================
 *
 * All clean heap objects share a common header:
 *
 *   ┌─────────────┬──────┬──────┬──────────┬───────────┐
 *   │  ref_count  │ tag  │ kind │ num_objs │ scalar_sz │
 *   │   32 bits   │ 8b   │ 8b   │   8 bits │   8 bits  │
 *   └─────────────┴──────┴──────┴──────────┴───────────┘
 *
 * - ref_count: Atomic reference count (0 = unique, use for mutation)
 * - tag: Constructor tag (0-255)
 * - kind: Object kind (ctor, closure, array, string, etc.)
 * - num_objs: Number of object (pointer) fields (0-255)
 * - scalar_sz: Bytes of inline scalar payload after object pointers (0-255)
 */

/* Object kinds */
#define CLEAN_OBJ_KIND_CTOR     0  /* Constructor */
#define CLEAN_OBJ_KIND_CLOSURE  1  /* Closure (partial application) */
#define CLEAN_OBJ_KIND_ARRAY    2  /* Array */
#define CLEAN_OBJ_KIND_STRING   3  /* String (UTF-8) */
#define CLEAN_OBJ_KIND_THUNK    4  /* Lazy thunk */
#define CLEAN_OBJ_KIND_TASK     5  /* Task (for concurrency) */
#define CLEAN_OBJ_KIND_EXTERNAL 6  /* External (FFI) */

/* Object header — must match Rust ObjHeader layout exactly (8 bytes, #[repr(C)]). */
typedef struct clean_obj_header {
    _Atomic uint32_t ref_count;
    uint8_t tag;
    uint8_t kind;
    uint8_t num_objs;   /* was uint16_t — now u8 matching Lean 4 m_other (Part of #1990) */
    uint8_t scalar_sz;  /* bytes of scalar payload after object pointers (Part of #1990) */
} clean_obj_header;

_Static_assert(sizeof(clean_obj_header) == 8, "ObjHeader must be exactly 8 bytes");

/* Generic object - header followed by fields */
typedef struct clean_obj {
    clean_obj_header header;
    /* Object fields follow:
     * - Object pointers first (num_objs count)
     * - Scalar fields after (size varies by constructor)
     */
    struct clean_obj* fields[];
} clean_obj;

/* Closure object */
typedef struct clean_closure {
    clean_obj_header header;
    void* fn;           /* Function pointer */
    uint16_t arity;     /* Total arity */
    uint16_t num_fixed; /* Number of captured args */
    clean_obj* args[];  /* Captured arguments */
} clean_closure;

/* Get the number of child (object-pointer) fields for an object.
 * For closures, reads num_fixed (u16) instead of header.num_objs (u8)
 * to avoid truncation for closures with >255 captured args.
 * Matches Rust runtime dispatch pattern. Part of #1996. */
static inline uint16_t clean_num_child_fields(clean_obj* o) {
    if (o->header.kind == CLEAN_OBJ_KIND_CLOSURE) {
        return ((clean_closure*)o)->num_fixed;
    }
    return o->header.num_objs;
}

/* ============================================================================
 * Tagged Pointers
 * ============================================================================
 *
 * Small values (0 to SIZE_MAX/2) are represented as tagged pointers to avoid allocation:
 *   - Pointer with lowest bit set = tagged value
 *   - Value stored in upper bits
 *
 * This handles common cases like Nat small integers and Unit.
 */

#define CLEAN_TAG_BIT 1
#define CLEAN_MAX_SMALL (SIZE_MAX >> 1)

/* Check if pointer is a tagged (boxed small) value */
static inline bool clean_is_scalar(clean_obj* o) {
    return ((uintptr_t)o & CLEAN_TAG_BIT) != 0;
}

/* Box a small integer into a tagged pointer */
static inline clean_obj* clean_box(size_t n) {
    return (clean_obj*)((n << 1) | CLEAN_TAG_BIT);
}

/* Unbox a tagged pointer to get the value */
static inline size_t clean_unbox(clean_obj* o) {
    return ((uintptr_t)o) >> 1;
}

/* Box larger integers (allocates) */
clean_obj* clean_box_uint64(uint64_t n);
clean_obj* clean_box_uint32(uint32_t n);
clean_obj* clean_box_float(double f);

/* Unbox uint64 (handles both tagged and heap-allocated).
 * Mirrors clean_unbox_uint32's tagged-or-heap dispatch: a small value is the
 * tagged immediate (v<<1)|1 (Nat's universal representation on this runtime,
 * capped below 2^63), a larger value is a clean_box_uint64 heap cell whose
 * scalar payload holds the raw u64. Was heap-only, which read garbage off a
 * tagged pointer — that is why UInt64.ofNat / UInt64.ofNatLT / USize.ofNatLT
 * (which decode a tagged Nat carrier) were refused fail-closed. */
static inline uint64_t clean_unbox_uint64(clean_obj* o) {
    if (clean_is_scalar(o)) {
        return (uint64_t)clean_unbox(o);
    }
    return *(uint64_t*)(o->fields);
}

/* Unbox uint32 (handles both tagged and heap-allocated) */
static inline uint32_t clean_unbox_uint32(clean_obj* o) {
    if (clean_is_scalar(o)) {
        return (uint32_t)clean_unbox(o);
    }
    return *(uint32_t*)(o->fields);
}

/* Unbox heap-allocated float64 */
static inline double clean_unbox_float(clean_obj* o) {
    return *(double*)(o->fields);
}

/* ============================================================================
 * Heap Nat (values >= 2^63) — RUNG B
 * ============================================================================
 *
 * This runtime's `Nat` is the tagged immediate `(v << 1) | 1` for `v < 2^63`
 * (`clean_box` / `clean_unbox`). A value the tag bit cannot hold — `[2^63,
 * 2^128)` — is boxed as a HEAP Nat: a Ctor cell (`kind == CTOR`, `num_objs 0`)
 * whose inline scalar payload holds the value as two little-endian `uint64_t`
 * limbs `[lo, hi]` (`scalar_sz == 16`). Because both limbs are 8-byte aligned
 * (`o->fields` sits at header offset 8), the read never needs 16-byte
 * `__int128` alignment.
 *
 * Consumers dispatch on representation, never on a producer assumption:
 *   - tagged (LSB=1)         -> value is `clean_unbox(o)`            (< 2^63)
 *   - heap, scalar_sz >= 16  -> two-limb `[lo, hi]` u128             (>= 2^63)
 *   - heap, scalar_sz == 8   -> single `uint64_t` limb              (a UInt64-
 *     carried Nat boxed by `clean_box_uint64`, i.e. `[2^32, 2^64)`)
 *
 * FAIL-CLOSED: a value that does not fit `u128` (`>= 2^128`) aborts via
 * `clean_panic` rather than truncating — never a wrong value. Every
 * `UInt64`/`USize`-derived Nat is `<= 2^64`, well inside `u128`.
 */
#define CLEAN_NAT_HEAP_SCALAR_SZ 16

/* Build a Nat from a 128-bit value: tagged immediate if `< 2^63`, else a heap
 * two-limb cell. */
clean_obj* clean_nat_of_u128(unsigned __int128 v);

/* Build a Nat from a 64-bit value (the `UInt64.toNat` / `USize.toNat` /
 * scalar-carrier re-box producer). External symbol (NOT `static inline`) so the
 * trust-ir `ExternCalls` backend can name it as a link-time import. */
clean_obj* clean_nat_of_u64(uint64_t v);

/* Build a Nat from a big literal given as two little-endian u64 limbs
 * `lo + hi*2^64` (a `Nat` literal `>= 2^64` — e.g. `UInt64.size = 2^64`). The
 * value is `< 2^128` by construction (the emitter fails closed above two
 * limbs), so it is always representable. Tagged if it somehow fits below 2^63
 * (`hi == 0 && lo < 2^63`), else a heap two-limb cell. */
clean_obj* clean_nat_big(uint64_t lo, uint64_t hi);

/* Read a Nat value as `u128`, dispatching tagged / heap-two-limb / legacy-u64.
 * Does NOT consume `o`. */
unsigned __int128 clean_nat_to_u128(clean_obj* o);

/* Heap-aware `Nat` shims. Each CONSUMES (dec's) both arguments per the Perceus
 * all-owned ABI (reading their values first), so a heap Nat operand is freed
 * exactly once. Arithmetic follows Lean 4 `Nat` semantics: truncated
 * subtraction (floored at 0), `n / 0 = 0`, `n % 0 = n`. `dec_eq` / `ble` / `blt`
 * / `beq` return a tagged `0`/`1` (a `Decidable` / `Bool` scrutinee, never a
 * Nat). A result exceeding `u128` fails closed (`clean_panic`). These back the
 * `l_Nat_*` prelude shims. */
clean_obj* clean_nat_add(clean_obj* a, clean_obj* b);
clean_obj* clean_nat_sub(clean_obj* a, clean_obj* b);
clean_obj* clean_nat_mul(clean_obj* a, clean_obj* b);
clean_obj* clean_nat_div(clean_obj* a, clean_obj* b);
clean_obj* clean_nat_mod(clean_obj* a, clean_obj* b);
clean_obj* clean_nat_dec_eq(clean_obj* a, clean_obj* b);
clean_obj* clean_nat_ble(clean_obj* a, clean_obj* b);
clean_obj* clean_nat_blt(clean_obj* a, clean_obj* b);
clean_obj* clean_nat_beq(clean_obj* a, clean_obj* b);

/* Heap-aware `Int` decision shims. `Int` is a two-ctor cell (tag 0 `ofNat n` =
 * `+n`, tag 1 `negSucc n` = `-(n+1)`) with the `Nat` payload in field 0; the
 * magnitude is decoded via the heap-aware `clean_nat_to_u128`, and the compare
 * splits on sign so no signed overflow is possible. Each CONSUMES both `Int`
 * arguments and returns a tagged `0`/`1` `Decidable` scrutinee (isFalse/isTrue).
 * These back the `l_Int_decLt` / `l_Int_decLe` / `l_Int_decEq` prelude shims. */
clean_obj* clean_int_dec_lt(clean_obj* a, clean_obj* b);
clean_obj* clean_int_dec_le(clean_obj* a, clean_obj* b);
clean_obj* clean_int_dec_eq(clean_obj* a, clean_obj* b);

/* `Nat.shiftRight n k = n >>> k` (Lean 4 arbitrary-precision Nat). Heap-aware +
 * arg-consuming like the ops above; a shift count >= 128 yields 0. Backs the
 * `l_Nat_shiftRight` prelude shim (instHShiftRightNat). */
clean_obj* clean_nat_shift_right(clean_obj* a, clean_obj* b);

/* ============================================================================
 * Quotient eliminators (Quot.lift / Quot.ind)
 * ============================================================================
 *
 * `Quot.mk` is runtime-identity, so `Quot r` IS its representative:
 *   clean_quot_lift(f, q) ≡ f q   — genuine computation, consumes f and q.
 *   clean_quot_ind(f, q)          — PROOF eliminator (motive : … → Prop):
 *                                   dec f/q, return the erased proof clean_box(0).
 * Back the `l_Quot_lift` / `l_Quot_ind` prelude shims (Finset.cons/Multiset.cons). */
clean_obj* clean_quot_lift(clean_obj* f, clean_obj* q);
clean_obj* clean_quot_ind(clean_obj* f, clean_obj* q);

/* ============================================================================
 * Reference Counting
 * ============================================================================
 */

/* Increment reference count */
static inline void clean_inc(clean_obj* o) {
    if (!clean_is_scalar(o)) {
        atomic_fetch_add_explicit(&o->header.ref_count, 1, memory_order_relaxed);
    }
}

/* Increment by n */
static inline void clean_inc_n(clean_obj* o, uint32_t n) {
    if (!clean_is_scalar(o)) {
        atomic_fetch_add_explicit(&o->header.ref_count, n, memory_order_relaxed);
    }
}

/* Decrement reference count, free if zero */
void clean_dec(clean_obj* o);

/* Check if object is exclusively owned (ref_count == 0 means 1 reference).
 * Relaxed suffices: is_unique is a hint for reuse optimization.
 * False positive (shared when exclusive) -> unnecessary alloc (safe).
 * False negative cannot happen: the caller holds a reference.
 * Matches Lean 4 lean_is_exclusive (lean.h:550). Part of #2005. */
static inline bool clean_is_exclusive(clean_obj* o) {
    if (clean_is_scalar(o)) return true;
    return atomic_load_explicit(&o->header.ref_count, memory_order_relaxed) == 0;
}

/* ============================================================================
 * Object Allocation
 * ============================================================================
 */

/* Allocate constructor with given tag, field layout, and object fields.
 * scalar_sz is the total byte count for inline scalar storage (after object ptrs).
 * Scalar values are written separately via SSet; only object fields are varargs.
 * Note: tag/num_objs/scalar_sz use unsigned int to avoid varargs promotion issues. */
clean_obj* clean_alloc_ctor(unsigned int tag, unsigned int num_objs, unsigned int scalar_sz, ...);

/* Allocate constructor without initializing fields */
clean_obj* clean_alloc_ctor_uninit(uint8_t tag, uint8_t num_objs, uint8_t scalar_size);

/* Allocate closure.
 * fn: function pointer, arity: total parameter count, num_fixed: captured arg count.
 * Note: arity/num_fixed use unsigned int to avoid varargs promotion issues.
 * Varargs are the num_fixed captured arguments. */
clean_obj* clean_alloc_closure(void* fn, unsigned int arity, unsigned int num_fixed, ...);

/* ============================================================================
 * Closure Application (Dynamic Dispatch)
 * ============================================================================
 *
 * clean_apply_N: Apply N arguments to a closure object.
 * Three-way dispatch matching Lean 4 runtime (src/runtime/apply.cpp):
 *   - Under-application: create bigger closure with more captured args
 *   - Exact application: invoke the function pointer directly
 *   - Over-application: saturate, invoke, recursively apply remainder
 */

/* Specialized apply for small argument counts (fast path) */
clean_obj* clean_apply_0(clean_obj* closure);
clean_obj* clean_apply_1(clean_obj* closure, clean_obj* a1);
clean_obj* clean_apply_2(clean_obj* closure, clean_obj* a1, clean_obj* a2);
clean_obj* clean_apply_3(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3);
clean_obj* clean_apply_4(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4);
clean_obj* clean_apply_5(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5);
clean_obj* clean_apply_6(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6);
clean_obj* clean_apply_7(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7);
clean_obj* clean_apply_8(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8);
clean_obj* clean_apply_9(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9);
clean_obj* clean_apply_10(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10);
clean_obj* clean_apply_11(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11);
clean_obj* clean_apply_12(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12);
clean_obj* clean_apply_13(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13);
clean_obj* clean_apply_14(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14);
clean_obj* clean_apply_15(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15);
clean_obj* clean_apply_16(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16);
clean_obj* clean_apply_17(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17);
clean_obj* clean_apply_18(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18);
/* Wide algebraic-hierarchy eliminators (DivisionRing arity 20, Field arity 21;
 * generous ceiling 32 kept in lockstep with clean_invoke and the emitter). */
clean_obj* clean_apply_19(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19);
clean_obj* clean_apply_20(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20);
clean_obj* clean_apply_21(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21);
clean_obj* clean_apply_22(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22);
clean_obj* clean_apply_23(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23);
clean_obj* clean_apply_24(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24);
clean_obj* clean_apply_25(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25);
clean_obj* clean_apply_26(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26);
clean_obj* clean_apply_27(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27);
clean_obj* clean_apply_28(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28);
clean_obj* clean_apply_29(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28, clean_obj* a29);
clean_obj* clean_apply_30(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28, clean_obj* a29, clean_obj* a30);
clean_obj* clean_apply_31(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28, clean_obj* a29, clean_obj* a30, clean_obj* a31);
clean_obj* clean_apply_32(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28, clean_obj* a29, clean_obj* a30, clean_obj* a31, clean_obj* a32);

/* Generic apply for arbitrary argument counts */
clean_obj* clean_apply_n(clean_obj* closure, unsigned int n, clean_obj** args);

/* ============================================================================
 * Field Access
 * ============================================================================
 */

/* Get object field */
static inline clean_obj* clean_ctor_get(clean_obj* o, size_t idx) {
    return o->fields[idx];
}

/* Set object field (requires unique ownership) */
static inline void clean_ctor_set(clean_obj* o, size_t idx, clean_obj* v) {
    o->fields[idx] = v;
}

/* Get object tag */
static inline uint8_t clean_obj_tag(clean_obj* o) {
    if (clean_is_scalar(o)) {
        return (uint8_t)clean_unbox(o);
    }
    return o->header.tag;
}

/* Set constructor tag (requires exclusive ownership).
 * Used by IRBody::SetTag for in-place tag update during reuse optimization.
 * Matches Lean 4: lean_ctor_set_tag (lean.h:634). Part of #2005. */
static inline void clean_ctor_set_tag(clean_obj* o, uint8_t new_tag) {
    o->header.tag = new_tag;
}

/* ============================================================================
 * Typed Scalar Access
 * ============================================================================
 *
 * Access the scalar region after num_objs object pointer fields.
 * Byte-offset accessors: `offset` is measured from the start of o->fields.
 * The scalar region begins at byte num_objs * sizeof(void*) from fields[0].
 *
 * Slot-index accessors (usize): `i` is a slot index into o->fields, where
 * i >= num_objs indicates a scalar slot that holds a pointer-sized value.
 *
 * Matches Lean 4 lean.h:650-718. Part of #2005.
 */

/* Typed scalar getters */
static inline uint8_t clean_ctor_get_uint8(clean_obj* o, unsigned offset) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    return *(uint8_t*)((uint8_t*)(o->fields) + offset);
}

static inline uint16_t clean_ctor_get_uint16(clean_obj* o, unsigned offset) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    return *(uint16_t*)((uint8_t*)(o->fields) + offset);
}

static inline uint32_t clean_ctor_get_uint32(clean_obj* o, unsigned offset) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    return *(uint32_t*)((uint8_t*)(o->fields) + offset);
}

static inline uint64_t clean_ctor_get_uint64(clean_obj* o, unsigned offset) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    return *(uint64_t*)((uint8_t*)(o->fields) + offset);
}

static inline size_t clean_ctor_get_usize(clean_obj* o, unsigned i) {
    assert(i >= o->header.num_objs);
    return ((size_t*)(o->fields))[i];
}

static inline double clean_ctor_get_float(clean_obj* o, unsigned offset) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    return *(double*)((uint8_t*)(o->fields) + offset);
}

static inline float clean_ctor_get_float32(clean_obj* o, unsigned offset) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    return *(float*)((uint8_t*)(o->fields) + offset);
}

/* Typed scalar setters */
static inline void clean_ctor_set_uint8(clean_obj* o, unsigned offset, uint8_t v) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    *(uint8_t*)((uint8_t*)(o->fields) + offset) = v;
}

static inline void clean_ctor_set_uint16(clean_obj* o, unsigned offset, uint16_t v) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    *(uint16_t*)((uint8_t*)(o->fields) + offset) = v;
}

static inline void clean_ctor_set_uint32(clean_obj* o, unsigned offset, uint32_t v) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    *(uint32_t*)((uint8_t*)(o->fields) + offset) = v;
}

static inline void clean_ctor_set_uint64(clean_obj* o, unsigned offset, uint64_t v) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    *(uint64_t*)((uint8_t*)(o->fields) + offset) = v;
}

static inline void clean_ctor_set_usize(clean_obj* o, unsigned i, size_t v) {
    assert(i >= o->header.num_objs);
    ((size_t*)(o->fields))[i] = v;
}

static inline void clean_ctor_set_float(clean_obj* o, unsigned offset, double v) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    *(double*)((uint8_t*)(o->fields) + offset) = v;
}

static inline void clean_ctor_set_float32(clean_obj* o, unsigned offset, float v) {
    assert(offset >= o->header.num_objs * sizeof(clean_obj*));
    *(float*)((uint8_t*)(o->fields) + offset) = v;
}

/* ============================================================================
 * Reset/Reuse (Memory Optimization)
 * ============================================================================
 *
 * If an object is uniquely owned, we can reuse its memory for a new object
 * of the same size, avoiding allocation/deallocation overhead.
 */

/* Reset object for potential reuse.
 * Only Ctor, Closure, and Str kinds are reusable — their children live in
 * header.fields[] or closure.args[] and can be dec'd generically.
 * Array/Thunk/Task/External have per-kind internal structure that requires
 * specialized teardown — decline reuse and dec the whole object.
 * Matches Rust lean_reset (string_reset.rs). Part of #2019, #1944. */
static inline clean_obj* clean_reset(clean_obj* o) {
    if (clean_is_scalar(o)) return o;
    if (clean_is_exclusive(o)) {
        uint8_t kind = o->header.kind;
        /* Thunk/Task/External/Array: not reusable — specialized teardown needed.
         * num_child_fields returns 0 for Thunk/Task/External (Part of #2019),
         * and Array has a separate buffer. Dec whole object instead. */
        if (kind == CLEAN_OBJ_KIND_ARRAY || kind == CLEAN_OBJ_KIND_THUNK ||
            kind == CLEAN_OBJ_KIND_TASK || kind == CLEAN_OBJ_KIND_EXTERNAL) {
            clean_dec(o);
            return NULL;
        }
        uint16_t num_children = clean_num_child_fields(o);
        if (kind == CLEAN_OBJ_KIND_CLOSURE) {
            clean_closure* c = (clean_closure*)o;
            for (uint16_t i = 0; i < num_children; i++) {
                clean_dec(c->args[i]);
            }
        } else {
            for (uint16_t i = 0; i < num_children; i++) {
                clean_dec(o->fields[i]);
            }
        }
        return o;  /* Can be reused */
    }
    clean_dec(o);
    return NULL;  /* Must allocate fresh */
}

/* Reuse reset object or allocate new.
 * num_objs is the number of object pointer fields that follow in varargs.
 * scalar_sz is the total byte count for inline scalar storage.
 * Note: tag/num_objs/scalar_sz use unsigned int to avoid varargs promotion issues. */
clean_obj* clean_reuse(clean_obj* reset_slot, unsigned int tag, unsigned int num_objs, unsigned int scalar_sz, ...);

/* ============================================================================
 * String Operations
 * ============================================================================
 */

/* Create string from C string literal */
clean_obj* clean_mk_string(const char* s);

/* Get string data (UTF-8) */
const char* clean_string_data(clean_obj* s);

/* Get string length in bytes */
size_t clean_string_len(clean_obj* s);

/* ============================================================================
 * Panic / Error Handling
 * ============================================================================
 */

/* Abort with error message */
_Noreturn void clean_panic(const char* msg);

/* ============================================================================
 * Initialization
 * ============================================================================
 */

/* Initialize runtime (call once at program start) */
void clean_runtime_init(void);

/* Finalize runtime (call before exit) */
void clean_runtime_finalize(void);

#ifdef __cplusplus
}
#endif

#endif /* CLEAN_RUNTIME_H */
