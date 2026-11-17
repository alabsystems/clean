/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * SPDX-License-Identifier: Apache-2.0
 *
 * clean Runtime Library - C Implementation
 *
 * Part of #963 - Compiler IR infrastructure (Phase 4).
 */

#include "../include/clean_runtime.h"
#include <stdio.h>
#include <stdarg.h>
#include <assert.h>

/* ============================================================================
 * Memory Allocation
 * ============================================================================
 */

/* Allocate memory with alignment */
static inline void* clean_malloc(size_t size) {
    void* ptr = malloc(size);
    if (!ptr) {
        clean_panic("out of memory");
    }
    return ptr;
}

/* Free memory */
static inline void clean_free(void* ptr) {
    free(ptr);
}

/* ============================================================================
 * Object Allocation
 * ============================================================================
 */

clean_obj* clean_alloc_ctor_uninit(uint8_t tag, uint8_t num_objs, uint8_t scalar_size) {
    size_t size = sizeof(clean_obj_header) +
                  num_objs * sizeof(clean_obj*) +
                  scalar_size;
    clean_obj* o = (clean_obj*)clean_malloc(size);

    atomic_init(&o->header.ref_count, 0);  /* Start with ref_count = 0 (unique) */
    o->header.tag = tag;
    o->header.kind = CLEAN_OBJ_KIND_CTOR;
    o->header.num_objs = num_objs;
    o->header.scalar_sz = scalar_size;  /* Part of #1990: track scalar layout for dealloc */

    return o;
}

/* The header keeps tag, num_objs and scalar_sz in one byte each. A larger
 * value used to be cast to uint8_t for the allocation while the vararg loop
 * wrote the untruncated num_objs: 256 object fields allocated 0 slots and
 * took 256 pointer writes, 320 scalar bytes allocated 64. Stop by name
 * instead. The IR checker refuses these shapes before any lane emits them
 * (ir_checker rule C1); this is the defence in depth. */
static void clean_check_ctor_layout(const char* who, unsigned int tag, unsigned int num_objs,
                                    unsigned int scalar_sz) {
    char msg[160];
    if (tag > UINT8_MAX) {
        snprintf(msg, sizeof msg, "%s: constructor tag %u exceeds the 8-bit object header (max %u)",
                 who, tag, (unsigned)UINT8_MAX);
        clean_panic(msg);
    }
    if (num_objs > UINT8_MAX) {
        snprintf(msg, sizeof msg, "%s: %u object fields exceed the 8-bit object header (max %u)",
                 who, num_objs, (unsigned)UINT8_MAX);
        clean_panic(msg);
    }
    if (scalar_sz > UINT8_MAX) {
        snprintf(msg, sizeof msg, "%s: %u scalar bytes exceed the 8-bit object header (max %u)",
                 who, scalar_sz, (unsigned)UINT8_MAX);
        clean_panic(msg);
    }
}

clean_obj* clean_alloc_ctor(unsigned int tag, unsigned int num_objs, unsigned int scalar_sz, ...) {
    clean_check_ctor_layout("clean_alloc_ctor", tag, num_objs, scalar_sz);
    clean_obj* o = clean_alloc_ctor_uninit((uint8_t)tag, (uint8_t)num_objs, (uint8_t)scalar_sz);

    if (num_objs > 0) {
        va_list args;
        va_start(args, scalar_sz);
        for (unsigned int i = 0; i < num_objs; i++) {
            o->fields[i] = va_arg(args, clean_obj*);
        }
        va_end(args);
    }

    return o;
}

clean_obj* clean_alloc_closure(void* fn, unsigned int arity, unsigned int num_fixed, ...) {
    size_t size = sizeof(clean_closure) + num_fixed * sizeof(clean_obj*);
    clean_closure* c = (clean_closure*)clean_malloc(size);

    atomic_init(&c->header.ref_count, 0);
    c->header.tag = 0;
    c->header.kind = CLEAN_OBJ_KIND_CLOSURE;
    c->header.num_objs = (uint8_t)num_fixed;
    c->header.scalar_sz = 0;  /* Closures have no scalar payload */
    c->fn = fn;
    c->arity = (uint16_t)arity;
    c->num_fixed = (uint16_t)num_fixed;

    if (num_fixed > 0) {
        va_list args;
        va_start(args, num_fixed);
        for (unsigned int i = 0; i < num_fixed; i++) {
            c->args[i] = va_arg(args, clean_obj*);
        }
        va_end(args);
    }

    return (clean_obj*)c;
}

/* ============================================================================
 * Reference Counting
 * ============================================================================
 */

/* Cold path of clean_inc_n (Lean v4.35.0 object.cpp:433 lean_inc_ref_huge_n):
 * each step is one ordinary increment of at most CLEAN_RC_INC_MAX, and
 * re-reading the count stops the loop once the count is frozen. The whole n is
 * applied or the count is left frozen; it never wraps. */
void clean_inc_ref_huge_n(clean_obj* o, size_t n) {
    if (clean_is_scalar(o)) return;
    while (n > 0 &&
           atomic_load_explicit(&o->header.ref_count, memory_order_relaxed) < CLEAN_RC_STICKY) {
        size_t chunk = n < CLEAN_RC_INC_MAX ? n : CLEAN_RC_INC_MAX;
        atomic_fetch_add_explicit(&o->header.ref_count, (uint32_t)chunk, memory_order_relaxed);
        n -= chunk;
    }
}

/* Drop one reference. True when it was the last one (the caller frees).
 * A frozen count (>= CLEAN_RC_STICKY_DROP) is left untouched (Lean
 * lean_is_never_freed, lean4#15241). Release on the decrement and an acquire
 * fence before freeing, so every write of a former holder is visible. */
static inline bool clean_rc_drop(clean_obj* o) {
    if (atomic_load_explicit(&o->header.ref_count, memory_order_relaxed) >= CLEAN_RC_STICKY_DROP)
        return false;
    if (atomic_fetch_sub_explicit(&o->header.ref_count, 1, memory_order_release) != 0)
        return false;
    atomic_thread_fence(memory_order_acquire);
    return true;
}

#define CLEAN_DEC_LOCAL 64

static clean_obj** clean_dec_grow(clean_obj** todo, clean_obj** local, size_t* cap) {
    if (*cap > SIZE_MAX / 2 / sizeof(clean_obj*))
        clean_panic("clean_dec: deletion worklist size overflow");
    size_t new_cap = *cap * 2;
    clean_obj** grown = (todo == local)
        ? (clean_obj**)malloc(new_cap * sizeof(clean_obj*))
        : (clean_obj**)realloc(todo, new_cap * sizeof(clean_obj*));
    if (grown == NULL)
        clean_panic("clean_dec: out of memory growing the deletion worklist");
    if (todo == local) memcpy(grown, local, *cap * sizeof(clean_obj*));
    *cap = new_cap;
    return grown;
}

/* Free `o`, whose last reference was just dropped, and every child whose last
 * reference that frees, through an explicit worklist: no recursion, so a graph
 * of any shape and depth frees in constant C stack. A frozen child is never
 * adjusted or freed; a dying child with no children is freed at once. Closures
 * keep their children in args[] (count num_fixed, u16, Part of #1944/#1996).
 * Out of line, so clean_dec's frame carries no worklist. */
#if defined(__GNUC__) || defined(__clang__)
__attribute__((noinline))
#endif
static void clean_dec_release(clean_obj* o) {
    clean_obj* local[CLEAN_DEC_LOCAL];
    clean_obj** todo = local;
    size_t len = 0, cap = CLEAN_DEC_LOCAL;
    for (;;) {
        uint16_t n = clean_num_child_fields(o);
        clean_obj** kids = (o->header.kind == CLEAN_OBJ_KIND_CLOSURE)
                               ? ((clean_closure*)o)->args : o->fields;
        for (uint16_t i = 0; i < n; i++) {
            clean_obj* c = kids[i];
            if (clean_is_scalar(c) || !clean_rc_drop(c)) continue;
            if (clean_num_child_fields(c) == 0) {
                clean_free(c);
                continue;
            }
            if (len == cap) todo = clean_dec_grow(todo, local, &cap);
            todo[len++] = c;
        }
        clean_free(o);
        if (len == 0) break;
        o = todo[--len];
    }
    if (todo != local) free(todo);
}

/* Decrement ref count; on the last reference free the object and every child
 * that reference kept alive. A no-op on a scalar or a frozen count. */
void clean_dec(clean_obj* o) {
    if (!clean_is_scalar(o) && clean_rc_drop(o)) clean_dec_release(o);
}

/* ============================================================================
 * Boxing
 * ============================================================================
 */

/* Box uint64 (always allocates - larger than tagged pointer) */
clean_obj* clean_box_uint64(uint64_t n) {
    clean_obj* o = clean_alloc_ctor_uninit(0, 0, sizeof(uint64_t));
    *(uint64_t*)(o->fields) = n;
    return o;
}

clean_obj* clean_box_uint32(uint32_t n) {
#if SIZE_MAX > UINT32_MAX
    /* Every uint32 fits the tagged payload when size_t is wider. */
    return clean_box(n);
#else
    if (n <= CLEAN_MAX_SMALL) {
        return clean_box(n);
    }
    clean_obj* o = clean_alloc_ctor_uninit(0, 0, sizeof(uint32_t));
    *(uint32_t*)(o->fields) = n;
    return o;
#endif
}

clean_obj* clean_box_float(double f) {
    clean_obj* o = clean_alloc_ctor_uninit(0, 0, sizeof(double));
    *(double*)(o->fields) = f;
    return o;
}

/* ============================================================================
 * Heap Nat (values >= 2^63) — RUNG B
 * ============================================================================
 *
 * See clean_runtime.h for the representation contract. The tagged-vs-heap
 * dispatch here is the SINGLE source of truth every Nat producer/consumer
 * routes through, so heap-boxing a producer can never desync from a consumer
 * that assumed tagged (the failure mode this rung closes).
 */

clean_obj* clean_nat_of_u128(unsigned __int128 v) {
    if (v <= (unsigned __int128)CLEAN_MAX_SMALL) {
        /* Fits the tagged immediate (< 2^63): the universal small-Nat form. */
        return clean_box((size_t)(uint64_t)v);
    }
    /* Heap two-limb cell: [lo, hi], little-endian, scalar_sz == 16. */
    clean_obj* o = clean_alloc_ctor_uninit(0, 0, CLEAN_NAT_HEAP_SCALAR_SZ);
    uint64_t* limbs = (uint64_t*)(o->fields);
    limbs[0] = (uint64_t)v;
    limbs[1] = (uint64_t)(v >> 64);
    return o;
}

clean_obj* clean_nat_of_u64(uint64_t v) {
    return clean_nat_of_u128((unsigned __int128)v);
}

clean_obj* clean_nat_big(uint64_t lo, uint64_t hi) {
    return clean_nat_of_u128(((unsigned __int128)hi << 64) | (unsigned __int128)lo);
}

unsigned __int128 clean_nat_to_u128(clean_obj* o) {
    if (clean_is_scalar(o)) {
        return (unsigned __int128)clean_unbox(o);
    }
    /* Heap Nat: dispatch on the inline scalar payload width. */
    if (o->header.scalar_sz >= CLEAN_NAT_HEAP_SCALAR_SZ) {
        const uint64_t* limbs = (const uint64_t*)(o->fields);
        return ((unsigned __int128)limbs[1] << 64) | (unsigned __int128)limbs[0];
    }
    /* Legacy single-limb clean_box_uint64 cell (scalar_sz == 8): a UInt64-
     * carried Nat in [2^32, 2^64). */
    return (unsigned __int128)(*(const uint64_t*)(o->fields));
}

clean_obj* clean_nat_add(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    unsigned __int128 r = x + y;
    if (r < x) {
        clean_panic("clean_nat_add: Nat result >= 2^128 (fail-closed)");
    }
    return clean_nat_of_u128(r);
}

clean_obj* clean_nat_sub(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    /* Lean truncated subtraction: floors at 0, never wraps. */
    return clean_nat_of_u128(x >= y ? x - y : (unsigned __int128)0);
}

clean_obj* clean_nat_mul(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    unsigned __int128 r = x * y;
    if (x != 0 && r / x != y) {
        clean_panic("clean_nat_mul: Nat result >= 2^128 (fail-closed)");
    }
    return clean_nat_of_u128(r);
}

clean_obj* clean_nat_div(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    /* Lean convention: n / 0 = 0. */
    return clean_nat_of_u128(y == 0 ? (unsigned __int128)0 : x / y);
}

clean_obj* clean_nat_mod(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    /* Lean convention: n % 0 = n. */
    return clean_nat_of_u128(y == 0 ? x : x % y);
}

clean_obj* clean_nat_dec_eq(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    /* Decidable (a = b) scrutinee: tagged 0/1, never a Nat. */
    return clean_box(x == y ? 1 : 0);
}

clean_obj* clean_nat_ble(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    /* Bool scrutinee: tagged 0/1, never a Nat. */
    return clean_box(x <= y ? 1 : 0);
}

clean_obj* clean_nat_shift_right(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 k = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    /* Lean 4 `Nat.shiftRight n k = n >>> k` (arbitrary precision). Every Nat this
     * runtime represents is < 2^128, so a shift count >= 128 yields 0 — and a C
     * `>>` on __int128 by >= its width is undefined, so the wide count is guarded
     * explicitly rather than executed. Heap-aware + arg-consuming (RUNG B): a
     * result >= 2^63 heap-boxes, below it tags. */
    unsigned __int128 r = (k >= 128) ? (unsigned __int128)0 : (x >> (unsigned)k);
    return clean_nat_of_u128(r);
}

/* Lean 4 `Nat.land` / `Nat.lor` / `Nat.xor` (arbitrary precision). Both
 * operands are < 2^128 (the runtime's Nat bound), so each result is too and
 * `clean_nat_of_u128` represents it exactly: tagged below 2^63, heap above.
 * Heap-aware + arg-consuming (RUNG B). These replace the prelude's
 * `Nat.bitwise` body for execution — a unary-fuel definition (`fuel = m + n`,
 * one recursion level per unit) that overflows the stack at any heap input
 * (WS6.3, F-105; postmortems/2026-09-18-ws6-3-mask-crash.md). */
clean_obj* clean_nat_land(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    return clean_nat_of_u128(x & y);
}

clean_obj* clean_nat_lor(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    return clean_nat_of_u128(x | y);
}

clean_obj* clean_nat_xor(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    return clean_nat_of_u128(x ^ y);
}

/* ============================================================================
 * Quotient eliminators (Quot.lift / Quot.ind)
 * ============================================================================
 *
 * Lean's `Quot r` has the SAME runtime representation as its representative:
 * `Quot.mk r a` is runtime-identity on `a` (the compiler's to_mono
 * `Quot.mk → arg[2]` rule). The eliminators therefore reduce to applying the
 * given function to the underlying representative:
 *
 *   Quot.lift f h (Quot.mk r a)  ≡  f a
 *   Quot.ind  f   (Quot.mk r a)  ≡  f a
 *
 * `clean_quot_lift` is the GENUINE computation: the emitted `f` is a closure
 * that needs exactly one more argument (the representative), so applying `q`
 * saturates and runs it (e.g. Multiset.cons's `fun l => Quot.mk _ (a :: l)`).
 * Both `f` and `q` are consumed by clean_apply_1 per the all-owned ABI.
 *
 * `clean_quot_ind` is a PROOF eliminator: its motive lands in `Prop`
 * (`motive : Quot r → Prop`), so its result is proof-irrelevant — the canonical
 * erased proof `clean_box(0)`, value-identical to the erased-proof body the
 * emitter itself lowers the minor premise to. The owned `f`/`q` are dec'd so the
 * erasure is reference-count-clean (no leak of the captured environment). These
 * back the l_Quot_lift / l_Quot_ind prelude shims (Finset.cons, Multiset.cons).
 */
clean_obj* clean_quot_lift(clean_obj* f, clean_obj* q) {
    return clean_apply_1(f, q);
}

clean_obj* clean_quot_ind(clean_obj* f, clean_obj* q) {
    clean_dec(f);
    clean_dec(q);
    return clean_box(0);
}

clean_obj* clean_nat_blt(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    /* Bool scrutinee: tagged 0/1, never a Nat. */
    return clean_box(x < y ? 1 : 0);
}

clean_obj* clean_nat_beq(clean_obj* a, clean_obj* b) {
    unsigned __int128 x = clean_nat_to_u128(a);
    unsigned __int128 y = clean_nat_to_u128(b);
    clean_dec(a);
    clean_dec(b);
    /* Bool scrutinee: tagged 0/1, never a Nat. */
    return clean_box(x == y ? 1 : 0);
}

/* ============================================================================
 * Heap-aware Int comparison — RUNG B
 * ============================================================================
 *
 * `Int` lowers to a two-constructor Ctor cell (never a tagged scalar):
 *   - tag 0  `Int.ofNat n`     -> the value  +n
 *   - tag 1  `Int.negSucc n`   -> the value  -(n+1)
 * with the `Nat` payload `n` in object field 0. The magnitude is decoded via
 * the heap-aware `clean_nat_to_u128`, so an `Int` whose magnitude reaches into
 * `[2^63, 2^128)` compares exactly instead of decoding a heap pointer as
 * garbage. The comparison splits on the two signs rather than converting to one
 * signed integer, so no `__int128` sign overflow is ever possible.
 */

/* Three-way compare of two `Int` ctors: -1 if a<b, 0 if a==b, +1 if a>b.
 * Does NOT consume a/b (reads their Nat payloads by borrow). */
static int clean_int_cmp(clean_obj* a, clean_obj* b) {
    unsigned ta = clean_obj_tag(a);
    unsigned tb = clean_obj_tag(b);
    unsigned __int128 na = clean_nat_to_u128(clean_ctor_get(a, 0));
    unsigned __int128 nb = clean_nat_to_u128(clean_ctor_get(b, 0));
    if (ta == 0 && tb == 0) {
        /* +na  vs  +nb */
        return na < nb ? -1 : (na > nb ? 1 : 0);
    }
    if (ta == 0) {
        /* a = +na (>= 0), b = negSucc (< 0)  =>  a > b */
        return 1;
    }
    if (tb == 0) {
        /* a = negSucc (< 0), b = +nb (>= 0)  =>  a < b */
        return -1;
    }
    /* both negSucc: a = -(na+1), b = -(nb+1)  =>  a < b iff na > nb */
    return na > nb ? -1 : (na < nb ? 1 : 0);
}

clean_obj* clean_int_dec_lt(clean_obj* a, clean_obj* b) {
    int c = clean_int_cmp(a, b);
    clean_dec(a);
    clean_dec(b);
    /* Decidable (a < b): isTrue(1) iff a<b, else isFalse(0). */
    return clean_box(c < 0 ? 1 : 0);
}

clean_obj* clean_int_dec_le(clean_obj* a, clean_obj* b) {
    int c = clean_int_cmp(a, b);
    clean_dec(a);
    clean_dec(b);
    /* Decidable (a <= b): isTrue(1) iff a<=b, else isFalse(0). */
    return clean_box(c <= 0 ? 1 : 0);
}

clean_obj* clean_int_dec_eq(clean_obj* a, clean_obj* b) {
    int c = clean_int_cmp(a, b);
    clean_dec(a);
    clean_dec(b);
    /* Decidable (a = b): isTrue(1) iff a==b, else isFalse(0). */
    return clean_box(c == 0 ? 1 : 0);
}

/* ============================================================================
 * Reset/Reuse
 * ============================================================================
 */

clean_obj* clean_reuse(clean_obj* reset_slot, unsigned int tag, unsigned int num_objs, unsigned int scalar_sz, ...) {
    clean_obj* o;

    /* Before either path: the same-layout assertions below compare header
     * bytes, which a truncated 256 would have matched against a 0-field slot. */
    clean_check_ctor_layout("clean_reuse", tag, num_objs, scalar_sz);

    if (reset_slot != NULL && reset_slot->header.kind == CLEAN_OBJ_KIND_CTOR) {
        /* Reuse the Ctor reset slot — update header to match new constructor.
         * Part of #1990: must set num_objs and scalar_sz, not just tag.
         * Without this, clean_dec iterates wrong child count on dealloc. */
        assert(reset_slot->header.num_objs == (uint8_t)num_objs &&
               "clean_reuse: num_objs mismatch — compiler must generate same-layout reuse");
        assert(reset_slot->header.scalar_sz == (uint8_t)scalar_sz &&
               "clean_reuse: scalar_sz mismatch — compiler must generate same-layout reuse");
        o = reset_slot;
        o->header.tag = (uint8_t)tag;
        o->header.num_objs = (uint8_t)num_objs;
        o->header.scalar_sz = (uint8_t)scalar_sz;
    } else {
        if (reset_slot != NULL) {
            /* Non-Ctor slot (Closure, String, etc.) — layout mismatch
             * prevents safe in-place reuse. Free the old allocation. */
            clean_free(reset_slot);
        }
        /* Allocate fresh Ctor with correct field count and scalar space. */
        o = clean_alloc_ctor_uninit((uint8_t)tag, (uint8_t)num_objs, (uint8_t)scalar_sz);
    }

    /* Set object fields from varargs (count-bounded).
     * Scalar fields are written separately via SSet instructions. */
    va_list args;
    va_start(args, scalar_sz);
    for (unsigned int i = 0; i < num_objs; i++) {
        o->fields[i] = va_arg(args, clean_obj*);
    }
    va_end(args);

    return o;
}

/* ============================================================================
 * Strings
 * ============================================================================
 */

/* String object layout: header + length + data */
typedef struct clean_string {
    clean_obj_header header;
    size_t len;
    char data[];
} clean_string;

clean_obj* clean_mk_string_from_bytes(const char* s, size_t len) {
    if (len > SIZE_MAX - sizeof(clean_string) - 1) {
        clean_panic("clean_mk_string_from_bytes: string size overflow");
    }
    size_t size = sizeof(clean_string) + len + 1;

    clean_string* str = (clean_string*)clean_malloc(size);
    atomic_init(&str->header.ref_count, 0);
    str->header.tag = 0;
    str->header.kind = CLEAN_OBJ_KIND_STRING;
    str->header.num_objs = 0;
    str->header.scalar_sz = 0;  /* Strings use their own layout, not scalar_sz */
    str->len = len;
    if (len != 0) {
        memcpy(str->data, s, len);
    }
    str->data[len] = 0;

    return (clean_obj*)str;
}

clean_obj* clean_mk_string(const char* s) {
    return clean_mk_string_from_bytes(s, strlen(s));
}

const char* clean_string_data(clean_obj* s) {
    return ((clean_string*)s)->data;
}

size_t clean_string_len(clean_obj* s) {
    return ((clean_string*)s)->len;
}

/* ============================================================================
 * Panic
 * ============================================================================
 */

/* Lean 4's runtime fatal path, matched (pinned v4.30.0-rc2 `libleanrt.a`,
 * `object.cpp`: `lean_internal_panic` prints `INTERNAL PANIC: <msg>` to stderr
 * and calls `exit(1)`; it calls `abort()` only when `LEAN_ABORT_ON_PANIC` is
 * set). The program ENDS WITH STATUS 1 and no crash signal is raised; `exit`
 * flushes the program's buffered stdout, as Lean's does. `abort()` here made
 * every fail-closed refusal a SIGABRT death: a macOS crash report per run and
 * `clean run` reporting signal 6 (macOS's `abort()` flushes stdio too, so the
 * output there was kept; glibc's does not) (docs/DECISIONS.md R86). */
_Noreturn void clean_panic(const char* msg) {
    fprintf(stderr, "clean panic: %s\n", msg);
    exit(1);
}

/* ============================================================================
 * Closure Application (Dynamic Dispatch)
 * ============================================================================
 *
 * Implements the three-way dispatch for closure application:
 *   - Under-application: create bigger closure with more captured args
 *   - Exact application: invoke the function pointer directly
 *   - Over-application: saturate, invoke, recursively apply remainder
 *
 * Matches Lean 4 runtime semantics (src/runtime/apply.cpp).
 */

/* Invoke a function pointer with the given arguments (dispatch by arity). */
static clean_obj* clean_invoke(void* fn, unsigned int n, clean_obj** args) {
    switch (n) {
    case 0: return ((clean_obj* (*)(void))fn)();
    case 1: return ((clean_obj* (*)(clean_obj*))fn)(args[0]);
    case 2: return ((clean_obj* (*)(clean_obj*, clean_obj*))fn)(args[0], args[1]);
    case 3: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2]);
    case 4: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3]);
    case 5: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4]);
    case 6: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5]);
    case 7: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
    case 8: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
    case 9: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8]);
    case 10: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9]);
    case 11: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10]);
    case 12: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11]);
    case 13: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12]);
    case 14: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13]);
    case 15: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14]);
    case 16: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15]);
    case 17: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16]);
    case 18: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17]);
    /* Wide algebraic-hierarchy eliminators: DivisionRing.casesOn/recOn apply a
     * bare arity-20 minor-premise closure, Field.casesOn/recOn arity 21. Every
     * Clean value is pointer-sized (clean_obj*), but the AArch64 & SysV ABIs
     * pass a fixed-arity call differently from a variadic one, so a single
     * variadic cast would mis-pass arguments — each arity needs a concrete
     * positional cast. The ceiling (32) is generous headroom over Field(21);
     * kept in lockstep with the emitter's MAX_RUNTIME_APPLY_ARGS. */
    case 19: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18]);
    case 20: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19]);
    case 21: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20]);
    case 22: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21]);
    case 23: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22]);
    case 24: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23]);
    case 25: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23], args[24]);
    case 26: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23], args[24], args[25]);
    case 27: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23], args[24], args[25], args[26]);
    case 28: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23], args[24], args[25], args[26], args[27]);
    case 29: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23], args[24], args[25], args[26], args[27], args[28]);
    case 30: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23], args[24], args[25], args[26], args[27], args[28], args[29]);
    case 31: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23], args[24], args[25], args[26], args[27], args[28], args[29], args[30]);
    case 32: return ((clean_obj* (*)(clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*, clean_obj*))fn)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15], args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23], args[24], args[25], args[26], args[27], args[28], args[29], args[30], args[31]);
    default:
        clean_panic("clean_invoke: arity exceeds maximum supported (32)");
    }
}

/* Allocate closure from two argument arrays (old captured + new captured). */
static clean_obj* clean_alloc_closure_from_arrays(
    void* fn, unsigned int arity,
    unsigned int old_n, clean_obj** old_args,
    unsigned int new_n, clean_obj** new_args
) {
    unsigned int total_fixed = old_n + new_n;
    size_t size = sizeof(clean_closure) + total_fixed * sizeof(clean_obj*);
    clean_closure* c = (clean_closure*)clean_malloc(size);

    atomic_init(&c->header.ref_count, 0);
    c->header.tag = 0;
    c->header.kind = CLEAN_OBJ_KIND_CLOSURE;
    c->header.num_objs = (uint8_t)total_fixed;
    c->header.scalar_sz = 0;
    c->fn = fn;
    c->arity = (uint16_t)arity;
    c->num_fixed = (uint16_t)total_fixed;

    for (unsigned int i = 0; i < old_n; i++) c->args[i] = old_args[i];
    for (unsigned int i = 0; i < new_n; i++) c->args[old_n + i] = new_args[i];

    return (clean_obj*)c;
}

/* Forward a closure's captured args into a call under the all-owned ABI,
 * transferring ownership per the Perceus steal-when-exclusive protocol.
 *
 * The invoked function consumes every argument it receives, captured args
 * included (rc/mod.rs `abi_owned_map`: the callee dec's each param). So the
 * captures handed to the call must each carry one owned reference:
 *   - EXCLUSIVE closure (rc == 0, this apply is the sole owner): MOVE the
 *     captures into the call and free the closure cell WITHOUT dec'ing the
 *     captures — their single reference is transferred to the callee.
 *   - SHARED closure (rc > 0): the closure retains ownership of its captures,
 *     so INC each forwarded capture (to balance the callee's dec) and dec the
 *     closure (dropping only this apply's reference to the cell).
 * `exclusive` is sampled once, before the closure is freed/dec'd. With
 * num_fixed == 0 both loops are empty, so bare closures are just freed/dec'd.
 * Matches Lean 4 src/runtime/apply.cpp. R3 closure-apply UAF fix. */
static inline void clean_apply_consume_closure(clean_obj* closure, bool exclusive) {
    clean_closure* c = (clean_closure*)closure;
    if (exclusive) {
        clean_free(closure);  /* captures already moved into the call */
    } else {
        for (uint16_t i = 0; i < c->num_fixed; i++) {
            clean_inc(c->args[i]);
        }
        clean_dec(closure);
    }
}

/* Generic closure application: apply n arguments to a closure.
 *
 * Ownership (Perceus, matching Lean 4 src/runtime/apply.cpp): consumes one
 * owned reference to `closure` and to each `new_args[i]`, and returns one
 * owned reference. See clean_apply_consume_closure for how the closure's own
 * captured args are transferred into the invoked call. R3 closure-apply UAF fix. */
clean_obj* clean_apply_n(clean_obj* closure, unsigned int n, clean_obj** new_args) {
    clean_closure* c = (clean_closure*)closure;
    unsigned int arity = c->arity;
    unsigned int nf = c->num_fixed;
    unsigned int total = nf + n;
    /* Cache the function pointer: the exclusive path frees the closure cell in
     * clean_apply_consume_closure, so c->fn must be read BEFORE consuming. */
    void* fn = c->fn;
    /* Sample ownership BEFORE we free/dec the closure below. */
    bool exclusive = clean_is_exclusive(closure);

    if (total < arity) {
        /* Under-application: extend closure with more captured args. The old
         * captures are copied into `bigger` first, then their ownership is
         * transferred out of the consumed closure. */
        clean_obj* bigger =
            clean_alloc_closure_from_arrays(fn, arity, nf, c->args, n, new_args);
        clean_apply_consume_closure(closure, exclusive);
        return bigger;
    }

    /* total >= arity: build the saturating argument vector (all nf captures
     * plus the first `needed` new args), transfer capture ownership into it,
     * then invoke the underlying function. */
    unsigned int needed = arity - nf;
    clean_obj** all = (clean_obj**)clean_malloc(arity * sizeof(clean_obj*));
    for (unsigned int i = 0; i < nf; i++) all[i] = c->args[i];
    for (unsigned int i = 0; i < needed; i++) all[nf + i] = new_args[i];
    clean_apply_consume_closure(closure, exclusive);
    clean_obj* result = clean_invoke(fn, arity, all);
    free(all);

    if (total == arity) {
        /* Exact application. */
        return result;
    }
    /* Over-application: apply the remaining args to the result closure. The
     * saturating call above consumed `closure`; this tail consumes `result`. */
    return clean_apply_n(result, n - needed, new_args + needed);
}

/* Specialized apply_0 through apply_32 (fast paths avoiding array allocation).
 * The 0..=32 range matches clean_invoke's dispatch and the emitter's positional
 * clean_apply_N emission; >32 args route through clean_apply_n directly. The
 * 17/18 rung carries Ring.casesOn (arity 17) / CommRing.casesOn (arity 18); the
 * 20/21 rung carries DivisionRing.casesOn/recOn (arity 20) and Field.casesOn/
 * recOn (arity 21), which apply a bare minor-premise closure at that arity. */
clean_obj* clean_apply_0(clean_obj* closure) {
    /* Zero-argument application is the identity on any NON-closure object: a
     * tagged scalar or a fully-evaluated constructor is already a value, and
     * applying no arguments yields it unchanged. The emitter reaches here for
     * `Quot.mk`'s runtime-identity result (`clean_apply_0(<cons cell>)` inside
     * Multiset.cons's lift lambda, `clean_apply_0(clean_box(n))` for a scalar
     * quotient representative) — both are non-closures. Reading such an object
     * as a `clean_closure` (its payload as an arity/fn header) would dereference
     * garbage and crash, so short-circuit. Genuine closures keep the general
     * `clean_apply_n` path unchanged: an arity-0 closure is still invoked, an
     * under-saturated one still returns itself. */
    if (clean_is_scalar(closure) ||
        closure->header.kind != CLEAN_OBJ_KIND_CLOSURE) {
        return closure;
    }
    return clean_apply_n(closure, 0, NULL);
}

clean_obj* clean_apply_1(clean_obj* closure, clean_obj* a1) {
    clean_obj* args[1] = { a1 };
    return clean_apply_n(closure, 1, args);
}

clean_obj* clean_apply_2(clean_obj* closure, clean_obj* a1, clean_obj* a2) {
    clean_obj* args[2] = { a1, a2 };
    return clean_apply_n(closure, 2, args);
}

clean_obj* clean_apply_3(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3) {
    clean_obj* args[3] = { a1, a2, a3 };
    return clean_apply_n(closure, 3, args);
}

clean_obj* clean_apply_4(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4) {
    clean_obj* args[4] = { a1, a2, a3, a4 };
    return clean_apply_n(closure, 4, args);
}

clean_obj* clean_apply_5(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5) {
    clean_obj* args[5] = { a1, a2, a3, a4, a5 };
    return clean_apply_n(closure, 5, args);
}

clean_obj* clean_apply_6(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6) {
    clean_obj* args[6] = { a1, a2, a3, a4, a5, a6 };
    return clean_apply_n(closure, 6, args);
}

clean_obj* clean_apply_7(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7) {
    clean_obj* args[7] = { a1, a2, a3, a4, a5, a6, a7 };
    return clean_apply_n(closure, 7, args);
}

clean_obj* clean_apply_8(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8) {
    clean_obj* args[8] = { a1, a2, a3, a4, a5, a6, a7, a8 };
    return clean_apply_n(closure, 8, args);
}

clean_obj* clean_apply_9(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9) {
    clean_obj* args[9] = { a1, a2, a3, a4, a5, a6, a7, a8, a9 };
    return clean_apply_n(closure, 9, args);
}

clean_obj* clean_apply_10(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10) {
    clean_obj* args[10] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 };
    return clean_apply_n(closure, 10, args);
}

clean_obj* clean_apply_11(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11) {
    clean_obj* args[11] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 };
    return clean_apply_n(closure, 11, args);
}

clean_obj* clean_apply_12(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12) {
    clean_obj* args[12] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 };
    return clean_apply_n(closure, 12, args);
}

clean_obj* clean_apply_13(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13) {
    clean_obj* args[13] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 };
    return clean_apply_n(closure, 13, args);
}

clean_obj* clean_apply_14(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14) {
    clean_obj* args[14] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14 };
    return clean_apply_n(closure, 14, args);
}

clean_obj* clean_apply_15(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15) {
    clean_obj* args[15] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 };
    return clean_apply_n(closure, 15, args);
}

clean_obj* clean_apply_16(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16) {
    clean_obj* args[16] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 };
    return clean_apply_n(closure, 16, args);
}

clean_obj* clean_apply_17(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17) {
    clean_obj* args[17] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17 };
    return clean_apply_n(closure, 17, args);
}

clean_obj* clean_apply_18(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18) {
    clean_obj* args[18] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18 };
    return clean_apply_n(closure, 18, args);
}

clean_obj* clean_apply_19(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19) {
    clean_obj* args[19] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19 };
    return clean_apply_n(closure, 19, args);
}

clean_obj* clean_apply_20(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20) {
    clean_obj* args[20] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20 };
    return clean_apply_n(closure, 20, args);
}

clean_obj* clean_apply_21(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21) {
    clean_obj* args[21] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21 };
    return clean_apply_n(closure, 21, args);
}

clean_obj* clean_apply_22(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22) {
    clean_obj* args[22] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22 };
    return clean_apply_n(closure, 22, args);
}

clean_obj* clean_apply_23(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23) {
    clean_obj* args[23] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23 };
    return clean_apply_n(closure, 23, args);
}

clean_obj* clean_apply_24(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24) {
    clean_obj* args[24] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24 };
    return clean_apply_n(closure, 24, args);
}

clean_obj* clean_apply_25(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25) {
    clean_obj* args[25] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25 };
    return clean_apply_n(closure, 25, args);
}

clean_obj* clean_apply_26(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26) {
    clean_obj* args[26] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26 };
    return clean_apply_n(closure, 26, args);
}

clean_obj* clean_apply_27(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27) {
    clean_obj* args[27] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27 };
    return clean_apply_n(closure, 27, args);
}

clean_obj* clean_apply_28(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28) {
    clean_obj* args[28] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28 };
    return clean_apply_n(closure, 28, args);
}

clean_obj* clean_apply_29(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28, clean_obj* a29) {
    clean_obj* args[29] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29 };
    return clean_apply_n(closure, 29, args);
}

clean_obj* clean_apply_30(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28, clean_obj* a29, clean_obj* a30) {
    clean_obj* args[30] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30 };
    return clean_apply_n(closure, 30, args);
}

clean_obj* clean_apply_31(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28, clean_obj* a29, clean_obj* a30, clean_obj* a31) {
    clean_obj* args[31] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 };
    return clean_apply_n(closure, 31, args);
}

clean_obj* clean_apply_32(clean_obj* closure, clean_obj* a1, clean_obj* a2, clean_obj* a3, clean_obj* a4, clean_obj* a5, clean_obj* a6, clean_obj* a7, clean_obj* a8, clean_obj* a9, clean_obj* a10, clean_obj* a11, clean_obj* a12, clean_obj* a13, clean_obj* a14, clean_obj* a15, clean_obj* a16, clean_obj* a17, clean_obj* a18, clean_obj* a19, clean_obj* a20, clean_obj* a21, clean_obj* a22, clean_obj* a23, clean_obj* a24, clean_obj* a25, clean_obj* a26, clean_obj* a27, clean_obj* a28, clean_obj* a29, clean_obj* a30, clean_obj* a31, clean_obj* a32) {
    clean_obj* args[32] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32 };
    return clean_apply_n(closure, 32, args);
}

/* ============================================================================
 * Initialization
 * ============================================================================
 */

void clean_runtime_init(void) {
    /* Currently no-op, placeholder for future initialization */
}

void clean_runtime_finalize(void) {
    /* Currently no-op, placeholder for cleanup */
}
