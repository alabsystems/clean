/*
 * Copyright 2026 Andrew Yates
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * SPDX-License-Identifier: Apache-2.0
 *
 * clean Runtime Library - external-symbol materialization TU
 * ==========================================================
 *
 * The RC / box / field-access primitives in `clean_runtime.h` are declared
 * `static inline`: they have INTERNAL linkage and therefore emit NO linkable
 * symbol. The `emit_c` backend is happy with that — it `#include`s the header
 * and the C compiler inlines each primitive directly into the emitted program.
 *
 * The `trust-cg` backend (clean -> trust-ir -> trust-cg -> object) is NOT: it
 * lowers `clean_inc` / `clean_box` / `clean_unbox` / `clean_ctor_get` /
 * `clean_obj_tag` / `clean_unbox_uint64` / ... to *external calls* (the
 * `ExternCalls` runtime-lowering). With only `static inline` definitions in the
 * header there is no symbol to bind, so the native link fails with undefined
 * `_clean_*` references and every non-trivial root drops out.
 *
 * This translation unit MATERIALIZES a real, external (link-visible) definition
 * of every `static inline` header primitive, so the trust-cg object can bind
 * them at link time. It does so WITHOUT touching the header (so `emit_c` still
 * inlines exactly as before) and WITHOUT touching `clean_runtime.c` (so the
 * runtime still compiles standalone): each header primitive is textually
 * renamed to a private `<name>__hdr` alias *before* the header is included, and
 * a fresh external `<name>` forwarder is defined that calls the (renamed)
 * inline body. At -O1/-O2 the forwarder inlines the body, so the exported
 * symbol carries the identical logic — one authoritative definition, the
 * header's.
 *
 * Compiled and linked as part of the clean-runtime build (see
 * `clean_runtime::runtime_extern_source`). Linking it alongside
 * `clean_runtime.o` is a no-op for `emit_c` (whose program inlines its own
 * copies and never references these external symbols) and is the bridge the
 * trust-cg path needs.
 */

/* Rename each header `static inline` primitive to a private `__hdr` alias so we
 * can export a real external symbol of the ORIGINAL name below without a
 * `static`/non-`static` redefinition clash. Token-based macro replacement:
 * e.g. `clean_box` is NOT `clean_box_uint64` (distinct tokens), and inter-inline
 * calls (`clean_unbox_uint64` -> `clean_unbox`, `clean_reset` -> `clean_dec`)
 * stay consistent — every callee that is itself a renamed inline resolves to its
 * `__hdr` alias, while genuinely external callees (`clean_dec`, `clean_panic`,
 * `clean_alloc_ctor`) are untouched and resolve at link against clean_runtime.o. */
#define clean_num_child_fields   clean_num_child_fields__hdr
#define clean_is_scalar          clean_is_scalar__hdr
#define clean_box                clean_box__hdr
#define clean_unbox              clean_unbox__hdr
#define clean_unbox_uint64       clean_unbox_uint64__hdr
#define clean_unbox_uint32       clean_unbox_uint32__hdr
#define clean_unbox_float        clean_unbox_float__hdr
#define clean_inc                clean_inc__hdr
#define clean_inc_n              clean_inc_n__hdr
#define clean_is_exclusive       clean_is_exclusive__hdr
#define clean_ctor_get           clean_ctor_get__hdr
#define clean_ctor_set           clean_ctor_set__hdr
#define clean_obj_tag            clean_obj_tag__hdr
#define clean_ctor_set_tag       clean_ctor_set_tag__hdr
#define clean_ctor_get_uint8     clean_ctor_get_uint8__hdr
#define clean_ctor_get_uint16    clean_ctor_get_uint16__hdr
#define clean_ctor_get_uint32    clean_ctor_get_uint32__hdr
#define clean_ctor_get_uint64    clean_ctor_get_uint64__hdr
#define clean_ctor_get_usize     clean_ctor_get_usize__hdr
#define clean_ctor_get_float     clean_ctor_get_float__hdr
#define clean_ctor_get_float32   clean_ctor_get_float32__hdr
#define clean_ctor_set_uint8     clean_ctor_set_uint8__hdr
#define clean_ctor_set_uint16    clean_ctor_set_uint16__hdr
#define clean_ctor_set_uint32    clean_ctor_set_uint32__hdr
#define clean_ctor_set_uint64    clean_ctor_set_uint64__hdr
#define clean_ctor_set_usize     clean_ctor_set_usize__hdr
#define clean_ctor_set_float     clean_ctor_set_float__hdr
#define clean_ctor_set_float32   clean_ctor_set_float32__hdr
#define clean_reset              clean_reset__hdr

#include "../include/clean_runtime.h"

#undef clean_num_child_fields
#undef clean_is_scalar
#undef clean_box
#undef clean_unbox
#undef clean_unbox_uint64
#undef clean_unbox_uint32
#undef clean_unbox_float
#undef clean_inc
#undef clean_inc_n
#undef clean_is_exclusive
#undef clean_ctor_get
#undef clean_ctor_set
#undef clean_obj_tag
#undef clean_ctor_set_tag
#undef clean_ctor_get_uint8
#undef clean_ctor_get_uint16
#undef clean_ctor_get_uint32
#undef clean_ctor_get_uint64
#undef clean_ctor_get_usize
#undef clean_ctor_get_float
#undef clean_ctor_get_float32
#undef clean_ctor_set_uint8
#undef clean_ctor_set_uint16
#undef clean_ctor_set_uint32
#undef clean_ctor_set_uint64
#undef clean_ctor_set_usize
#undef clean_ctor_set_float
#undef clean_ctor_set_float32
#undef clean_reset

/* ---- Real external symbols: one authoritative forwarder per primitive. ---- */

uint16_t clean_num_child_fields(clean_obj* o) { return clean_num_child_fields__hdr(o); }
bool clean_is_scalar(clean_obj* o) { return clean_is_scalar__hdr(o); }
clean_obj* clean_box(size_t n) { return clean_box__hdr(n); }
size_t clean_unbox(clean_obj* o) { return clean_unbox__hdr(o); }
uint64_t clean_unbox_uint64(clean_obj* o) { return clean_unbox_uint64__hdr(o); }
uint32_t clean_unbox_uint32(clean_obj* o) { return clean_unbox_uint32__hdr(o); }
double clean_unbox_float(clean_obj* o) { return clean_unbox_float__hdr(o); }
void clean_inc(clean_obj* o) { clean_inc__hdr(o); }
void clean_inc_n(clean_obj* o, uint32_t n) { clean_inc_n__hdr(o, n); }
bool clean_is_exclusive(clean_obj* o) { return clean_is_exclusive__hdr(o); }
clean_obj* clean_ctor_get(clean_obj* o, size_t idx) { return clean_ctor_get__hdr(o, idx); }
void clean_ctor_set(clean_obj* o, size_t idx, clean_obj* v) { clean_ctor_set__hdr(o, idx, v); }
uint8_t clean_obj_tag(clean_obj* o) { return clean_obj_tag__hdr(o); }
void clean_ctor_set_tag(clean_obj* o, uint8_t new_tag) { clean_ctor_set_tag__hdr(o, new_tag); }

uint8_t clean_ctor_get_uint8(clean_obj* o, unsigned offset) { return clean_ctor_get_uint8__hdr(o, offset); }
uint16_t clean_ctor_get_uint16(clean_obj* o, unsigned offset) { return clean_ctor_get_uint16__hdr(o, offset); }
uint32_t clean_ctor_get_uint32(clean_obj* o, unsigned offset) { return clean_ctor_get_uint32__hdr(o, offset); }
uint64_t clean_ctor_get_uint64(clean_obj* o, unsigned offset) { return clean_ctor_get_uint64__hdr(o, offset); }
size_t clean_ctor_get_usize(clean_obj* o, unsigned i) { return clean_ctor_get_usize__hdr(o, i); }
double clean_ctor_get_float(clean_obj* o, unsigned offset) { return clean_ctor_get_float__hdr(o, offset); }
float clean_ctor_get_float32(clean_obj* o, unsigned offset) { return clean_ctor_get_float32__hdr(o, offset); }

void clean_ctor_set_uint8(clean_obj* o, unsigned offset, uint8_t v) { clean_ctor_set_uint8__hdr(o, offset, v); }
void clean_ctor_set_uint16(clean_obj* o, unsigned offset, uint16_t v) { clean_ctor_set_uint16__hdr(o, offset, v); }
void clean_ctor_set_uint32(clean_obj* o, unsigned offset, uint32_t v) { clean_ctor_set_uint32__hdr(o, offset, v); }
void clean_ctor_set_uint64(clean_obj* o, unsigned offset, uint64_t v) { clean_ctor_set_uint64__hdr(o, offset, v); }
void clean_ctor_set_usize(clean_obj* o, unsigned i, size_t v) { clean_ctor_set_usize__hdr(o, i, v); }
void clean_ctor_set_float(clean_obj* o, unsigned offset, double v) { clean_ctor_set_float__hdr(o, offset, v); }
void clean_ctor_set_float32(clean_obj* o, unsigned offset, float v) { clean_ctor_set_float32__hdr(o, offset, v); }

clean_obj* clean_reset(clean_obj* o) { return clean_reset__hdr(o); }
