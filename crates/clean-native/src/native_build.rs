// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared native build engine: emit → render → cc-link.
//!
//! This is the single source of truth for the file → emit → **link** pipeline
//! shared by `clean run` (which builds then runs the binary in place) and
//! `clean lake run` (which builds the binary to a stable `build_dir/bin/<name>`
//! path then executes it). Previously each surface re-implemented its own
//! emit + shim + cc-link logic, which diverged: `clean run` carried the full
//! `NAT`/`BOOL`/`TYPECLASS`/`IO` shim tables (so arithmetic, recursion, match,
//! and `toString` linked), while the Lake path carried only a narrow inline IO
//! prelude, so a single-module `Main` that did typeclass arithmetic / recursion
//! / `toString` could fail at link under `clean lake run` even though `clean run`
//! on the same file succeeded.
//!
//! Both surfaces now route through [`build_native_executable`], inheriting the
//! same shim coverage and the same [`clean_runtime`]-materialized runtime.
//!
//! ## Pipeline
//!
//! 1. **emit** the C closure for `decl` (root + transitive compilable deps) via
//!    the exact `clean compile --emit c` pipeline ([`emit_entry_c_with_type`]).
//! 2. **derive the entry contract** ([`entry_contract`]) — `IO` vs nullary
//!    `Nat` (which selects the driver and shim set), the call shape (does the
//!    emitted prototype take `argv`?), and the exit shape (`IO Unit` -> 0 vs
//!    `IO UInt32` -> the returned status).
//! 3. **select shims** the emitted C references ([`select_shims_from_tables`]),
//!    failing closed if it references a mangled extern no shim covers.
//! 4. **render** the combined translation unit (includes + shims + emitted
//!    closure + synthesized `main`).
//! 5. **materialize** the program + the embedded Clean C runtime into a scratch
//!    dir and **cc-link** them into a native executable.
//!
//! ## IO lowering
//!
//! For `def main : IO Unit := IO.println "hi"` the emitter produces:
//!
//! ```text
//! clean_obj* l_main(void) {
//!   clean_obj* _x0 = clean_mk_string("hi");
//!   clean_obj* _x1 = l_IO_println(_x0);   // effect happens HERE (eager)
//!   clean_inc(_x0);
//!   return _x1;                            // returns the Unit result
//! }
//! ```
//!
//! There is **no** world-token / `EStateM` state threaded into these calls — the
//! lowering passes the `IO` monad dictionary (`l_IO()`) and type erasures
//! (`clean_box(0)`) but the action functions take only their real arguments.
//! Effects fire in source order: `l_main()` *is* the driver — calling it runs
//! every effect and returns the action's final value.
//!
//! ## The entry contract
//!
//! Lean 4's entry point is `def main : IO Unit`, `def main : IO UInt32`, or
//! either of those taking `(args : List String)`. Both halves of that are
//! decided here, from two different sources, because neither source has both:
//!
//! * **Call shape** comes from the emitted C prototype ([`entry_arity_in_c`]).
//!   That is the ground truth for the call the driver has to make — the
//!   emitter, not the Lean type, decides whether the symbol is
//!   `l_main(void)` or `l_main(clean_obj*)`.
//! * **Exit shape** comes from the entry's elaborated Lean type. It CANNOT come
//!   from the C: `IO Unit` and `IO UInt32` lower to the same
//!   `clean_obj* l_main(...)` signature, so a driver working from the artifact
//!   alone would have to guess, and guessing "always 0" is exactly the bug this
//!   contract closes.
//!
//! The two are cross-checked rather than trusted independently: a unary entry
//! is only handed a marshalled `List String` when the Lean type agrees that is
//! what it takes, and anything wider is refused with a message naming the
//! contract.
//!
//! If the emitted C references a mangled `l_*` symbol outside the shim tables we
//! refuse with an explicit message rather than emit a binary that fails to link.
//! That keeps the surface honest: a `decl` either builds-and-runs, or reports
//! precisely which prelude extern it would need.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context};

use crate::compile::compile_to_string_with_decl_type;
use crate::native_string_layout_policy::StringLayoutPolicy;

#[path = "native_build_artifact.rs"]
mod artifact;
pub use artifact::{emit_native_c_artifact, NativeCArtifact};
use clean_compiler::cli::{CompileArgs, EmitFormat};
use clean_kernel::{Expr, ExprKind};

#[cfg(test)]
#[path = "native_string_bytearray_runtime_tests.rs"]
mod string_bytearray_runtime_tests;
#[cfg(test)]
#[path = "native_string_bytes_tests.rs"]
mod string_bytes_tests;

/// A prelude extern shim: the mangled symbol the emitted C may call, paired with
/// a faithful small-`Nat` C definition. Injected into the build only when the
/// emitted C references `<symbol>(`.
#[derive(Debug)]
pub(crate) struct PreludeShim {
    /// Mangled symbol as it appears in emitted C (without the trailing `(`).
    symbol: &'static str,
    /// Full C definition of the symbol (forward-declared by being defined ahead
    /// of the emitted closure in the same translation unit).
    definition: &'static str,
}

/// `Nat` shims for the prelude arithmetic externs the L5 emitter lowers to.
/// Each delegates to the heap-aware `clean_nat_*` runtime helper (RUNG B), which
/// dispatches tagged (`< 2^63`) vs heap Nat (`>= 2^63`) on BOTH operands and
/// consumes them per the Perceus all-owned ABI. The pre-RUNG-B bodies read via
/// tagged-only `clean_unbox`, so a heap-boxed operand (a `UInt64.toNat` result,
/// a large literal) decoded to garbage — the exact consumer-side failure this
/// closes. Semantics are unchanged for the tagged range and now correct above it.
const NAT_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_Nat_add",
        definition: "clean_obj* l_Nat_add(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_add(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Nat_mul",
        definition: "clean_obj* l_Nat_mul(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_mul(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Nat_sub",
        definition: "clean_obj* l_Nat_sub(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_sub(a, b);\n}\n",
    },
    // `Nat.div`/`Nat.mod` follow Lean 4 conventions: `n / 0 = 0`, `n % 0 = n`
    // (implemented in the runtime helpers).
    PreludeShim {
        symbol: "l_Nat_div",
        definition: "clean_obj* l_Nat_div(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_div(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Nat_mod",
        definition: "clean_obj* l_Nat_mod(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_mod(a, b);\n}\n",
    },
    // `toString {a} [ToString a] (x : a) : String` is the PROJECTION of the
    // single-method class `ToString`, so under the R3 representation documented
    // on [`TYPECLASS_PRELUDE_SHIMS`] it applies its instance: the instance IS
    // its bare method closure, and `ToString.toString inst x` is
    // `clean_apply_1(inst, x)` — the same shape `l_HAdd_hAdd` / `l_HMod_hMod`
    // already use. `clean_apply_1` consumes both per the all-owned ABI.
    //
    // It did not always. This shim was the one projection never converted to
    // R3: it discarded `inst` and decimal-rendered `x` as a `Nat`, which made
    // every non-`Nat` instance print a NUMBER instead of its own rendering,
    // silently and with exit status 0 — `toString "world"` printed `5` (the
    // string carrier's `len` field, read as a tagged Nat) and `toString true`
    // printed `1`. Nothing was missing from the compiler: for both of those the
    // emitter already lowers the genuine instance (`l_instToStringString`'s
    // method is the identity; `l_instToStringBool`'s is a boxed switch onto
    // `"true"`/`"false"`) and passes it in as `inst`. Only the shim threw it
    // away. The `Nat` rendering the old body open-coded is not lost — it is
    // exactly `l_instToStringNat`'s `clean_shim_nat_repr` below, which is the
    // instance this now applies for `Nat`, heap-aware `u128` buffer and all.
    //
    // A non-closure `inst` means the caller erased an instance this projection
    // needs, so fail loudly: `clean_apply_n` would read a tagged scalar's
    // payload as an arity/fn header and jump through garbage, and the old body
    // would have "succeeded" with a wrong number.
    PreludeShim {
        symbol: "l_toString",
        definition: "clean_obj* l_toString(clean_obj* ty, clean_obj* inst, clean_obj* x) {\n  \
            (void)ty;\n  \
            if (clean_is_scalar(inst) || inst->header.kind != CLEAN_OBJ_KIND_CLOSURE) {\n    \
            clean_panic(\"toString: ToString instance is not a method closure\");\n  \
            }\n  \
            return clean_apply_1(inst, x);\n}\n",
    },
    // `Nat.decEq a b : Decidable (a = b)`. The control-flow lowering uses its
    // result purely as a tag scrutinee; box `1` when equal, `0` otherwise.
    // Heap-aware + arg-consuming via the runtime helper (RUNG B).
    PreludeShim {
        symbol: "l_Nat_decEq",
        definition: "clean_obj* l_Nat_decEq(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_dec_eq(a, b);\n}\n",
    },
    // `Nat.shiftRight n k : Nat`. `instHShiftRightNat` lowers `n >>> k` to a
    // bare `(void*)l_Nat_shiftRight` fn-pointer (a 2-arity closure, no explicit
    // shim previously — so the emitted C referenced an undeclared identifier and
    // failed to compile). Delegates to the heap-aware runtime helper: arbitrary-
    // precision right shift, arg-consuming, tagged for small results / heap above
    // 2^63 (RUNG B). A shift count >= 128 yields 0 (guarded — every runtime Nat
    // is < 2^128).
    PreludeShim {
        symbol: "l_Nat_shiftRight",
        definition: "clean_obj* l_Nat_shiftRight(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_shift_right(a, b);\n}\n",
    },
    // `Nat.ble` / `Nat.blt` / `Nat.beq : Nat -> Nat -> Bool`. Although the Lean
    // result is `Bool`, denylisting keeps these as EXTERNs, and the emitter
    // lowers an extern call under the universal BOXED ABI (`clean_obj* _x =
    // l_Nat_ble(a, b);`, then reads it with `clean_unbox_uint64` /
    // `clean_obj_tag` — verified in the emitted `Nat.decLe`/`decLt` Bool-switch),
    // exactly like the already-wired `l_Nat_decEq`. So these shims RETURN the
    // tagged `0`/`1` `clean_obj*` the runtime helper produces. The helper is
    // heap-aware and O(1) (RUNG B); the source-compiled bodies they replace did
    // O(n) structural recursion — a heap Nat >= 2^63 would allocate ~2^63
    // closures (a hang/OOM). Denylisting keeps the shim, not the recursive body.
    PreludeShim {
        symbol: "l_Nat_ble",
        definition: "clean_obj* l_Nat_ble(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_ble(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Nat_blt",
        definition: "clean_obj* l_Nat_blt(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_blt(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Nat_beq",
        definition: "clean_obj* l_Nat_beq(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_beq(a, b);\n}\n",
    },
    // `Nat.land` / `Nat.lor` / `Nat.xor : Nat -> Nat -> Nat` (`&&&` / `|||` /
    // `^^^`, and the bodies of `UInt{N}.land/lor`). Same reason as `ble`/`blt`/
    // `beq` above, measured worse (WS6.3, F-105; postmortems/2026-09-18-ws6-3-
    // mask-crash.md): the prelude defines them as `Nat.bitwise f m n ≡
    // Nat.bitwiseAux f (m + n) m n`, a proof-oriented body whose UNARY fuel
    // `m + n` costs one recursion level per unit and never stops early. Compiled
    // from source, `mask (2^64-1) (2^64-2)` recursed ~2^65 deep and died on the
    // stack (SIGSEGV through both backends); at a doubled stack the crash
    // threshold doubled, and at 2^65 no stack helps. The runtime helpers are
    // O(1), heap-aware and arg-consuming, and denylisting keeps the source body
    // out of every build. They are TCB for the native path, so a test holds
    // them against the kernel's own `Nat.land/lor/xor` on random u128 pairs.
    PreludeShim {
        symbol: "l_Nat_land",
        definition: "clean_obj* l_Nat_land(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_land(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Nat_lor",
        definition: "clean_obj* l_Nat_lor(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_lor(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Nat_xor",
        definition: "clean_obj* l_Nat_xor(clean_obj* a, clean_obj* b) {\n  \
            return clean_nat_xor(a, b);\n}\n",
    },
];

/// `Int` decision-procedure shims. `Int.decLt`/`decLe`/`decEq` return
/// `Decidable`, which the emitter keeps in the BOXED `clean_obj*` representation
/// for an extern (only a source-compiled body with fully-visible callers gets
/// its return specialized to `uint8_t`), so these shims RETURN `clean_obj*` — a
/// tagged `0`/`1` (`isFalse`/`isTrue`) the caller reads via `clean_obj_tag` /
/// `clean_unbox_uint64`, mirroring the already-wired `l_Nat_decEq`. `Int.decLt`
/// is otherwise an UNRESOLVED extern (its body does not lower), so `x < y` /
/// `x <= y` on `Int` (which route through `Int.decNonNeg -> Int.decLt`) fail to
/// link without it; the helpers are heap-aware and O(1) across `[−2^128, 2^128)`.
const INT_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_Int_decLt",
        definition: "clean_obj* l_Int_decLt(clean_obj* a, clean_obj* b) {\n  \
            return clean_int_dec_lt(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Int_decLe",
        definition: "clean_obj* l_Int_decLe(clean_obj* a, clean_obj* b) {\n  \
            return clean_int_dec_le(a, b);\n}\n",
    },
    PreludeShim {
        symbol: "l_Int_decEq",
        definition: "clean_obj* l_Int_decEq(clean_obj* a, clean_obj* b) {\n  \
            return clean_int_dec_eq(a, b);\n}\n",
    },
];

/// `UInt32` shims for the fixed-width externs the L5 emitter lowers to.
///
/// CALLING CONVENTION, measured rather than assumed. `emit_type` maps
/// `IRType::UInt32` to an unboxed `uint32_t`, but the extraction path reaches
/// these symbols through the BOXED object path — the emitted C is
/// `clean_obj* _x5 = l_UInt32_ofNat(_x4);`. An unboxed signature compiles to
/// `-Wint-conversion` errors on every call site, so both shims take and return
/// `clean_obj*`. The differential battery (kernel whnf vs executed binary) is
/// what confirms the representation actually agrees, rather than this comment.
///
/// Why they are needed at all: the prelude's `UInt32.add`/`mul` are compiled
/// FROM SOURCE, and their bodies route through `UInt32.ofNat`. So every UIntW
/// extraction — including the design's own V1 pick
/// `def affineU (a b : UInt32) : UInt32 := UInt32.add (UInt32.mul a b) b`, and
/// even the minimal `def duo (a b : UInt32) : UInt32 := UInt32.add a b` —
/// bailed with "uncovered extern in emitted C: `l_UInt32_ofNat`". That one
/// missing symbol blocked the whole UIntW lane
/// (`designs/2026-08-06-clean-extract-width1.md`, rank 5).
///
/// `UInt32.ofNat n` is `n % 2^32`: read the Nat at full width through the
/// heap-aware helper, then truncate. Truncation IS the semantics, not a
/// lossy shortcut — `ofNat` is total and wraps, so a Nat above `2^32` must
/// reduce mod `2^32` rather than saturate or trap. Reading via
/// `clean_nat_to_u128` (not tagged-only `clean_unbox`) keeps that exact for a
/// heap-boxed argument. Consumes its argument per the all-owned ABI.
const UINT32_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_UInt32_ofNat",
        definition: "clean_obj* l_UInt32_ofNat(clean_obj* n) {\n  \
            unsigned __int128 v = clean_nat_to_u128(n);\n  \
            clean_dec(n);\n  \
            return clean_nat_of_u64((uint64_t)(v & 0xFFFFFFFFu));\n}\n",
    },
    PreludeShim {
        symbol: "l_UInt32_toNat",
        definition: "clean_obj* l_UInt32_toNat(clean_obj* v) {\n  \
            unsigned __int128 x = clean_nat_to_u128(v);\n  \
            clean_dec(v);\n  \
            return clean_nat_of_u64((uint64_t)(x & 0xFFFFFFFFu));\n}\n",
    },
];

/// The `UInt64` counterparts of [`UINT32_PRELUDE_SHIMS`], same rationale and
/// same boxed signatures — truncation IS `ofNat`'s semantics, `toNat` is the
/// identity on the 64-bit window, and both read heap-aware through
/// `clean_nat_to_u128` rather than tagged-only `clean_unbox` (a `UInt64` above
/// `2^63` is a heap Nat).
///
/// Measured 2026-08-27, before this table existed: `def main : IO Unit :=
/// IO.println (toString (9 : UInt64))` was refused with "native build cannot
/// satisfy prelude extern `l_UInt64_ofNat`" — fail-closed, but it put every
/// `UInt64`-touching entry outside the pillar, so `instToStringUInt64` could
/// not have been measured through `clean run` without them.
const UINT64_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_UInt64_ofNat",
        definition: "clean_obj* l_UInt64_ofNat(clean_obj* n) {\n  \
            unsigned __int128 v = clean_nat_to_u128(n);\n  \
            clean_dec(n);\n  \
            return clean_nat_of_u64((uint64_t)(v & 0xFFFFFFFFFFFFFFFFull));\n}\n",
    },
    PreludeShim {
        symbol: "l_UInt64_toNat",
        definition: "clean_obj* l_UInt64_toNat(clean_obj* v) {\n  \
            unsigned __int128 x = clean_nat_to_u128(v);\n  \
            clean_dec(v);\n  \
            return clean_nat_of_u64((uint64_t)(x & 0xFFFFFFFFFFFFFFFFull));\n}\n",
    },
];

/// Actual-source bridge primitives, separate from the kernel native reducers.
/// These consume the owned reference passed by an ordinary Const call; reuse
/// compensation is inserted before that call. Their results are fresh owned
/// objects, and carrier ownership is exercised by the runtime tests.
const SOURCE_STRING_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_String_ofList",
        definition: include_str!("string_of_list.c"),
    },
    PreludeShim {
        symbol: "l_String_ofByteArray",
        definition: include_str!("string_from_byte_array.c"),
    },
    PreludeShim {
        symbol: "l_String_toByteArray",
        definition: include_str!("string_to_byte_array.c"),
    },
];

/// `String` shims for the byte-string runtime carrier.
///
/// REPRESENTATION MISMATCH, verified in source rather than assumed. The
/// runtime carrier is the flat byte string `clean_mk_string` builds
/// (`clean_string`: header + `len` word + NUL-terminated UTF-8 bytes), but the
/// prelude registers `String.length`/`String.append` as genuine Definitions
/// over the `List Char` model (`data_types_collections.rs`: `String.length s
/// := List.length Char (String.data s)`). A `String.*` body lowered FROM
/// SOURCE therefore projects `String.data` out of the byte-string object —
/// `clean_ctor_get(s, 0)` reads the `len` word as a `clean_obj*` — and then
/// walks garbage. That compiles and links cleanly: a SILENT miscompile. Closed
/// from both sides: these ops are denylisted (via [`ALL_PRELUDE_SHIM_TABLES`])
/// so the #14 boundary keeps them extern and the shim implements them against
/// the real carrier. Other legacy source-lowered `String.*` bodies refuse in
/// [`select_shims_from_tables_with_policy`]; checked byte-backed source bodies
/// require the separate environment-derived carrier policy.
///
/// The table covers exactly the kernel's `String` native-reducer surface
/// (`clean-kernel/src/env/native_reducers.rs`), whose semantics these bodies
/// mirror — the kernel is the differential authority: `length` counts CODE
/// POINTS, not bytes (Lean: `s.data.length`); `utf8ByteSize` is the byte
/// length; `append` is byte concatenation; `push` appends the UTF-8 encoding
/// of the Char's code point (the Char arrives boxed, read via tagged-or-heap
/// `clean_unbox_uint32`, and is a valid Unicode scalar by the `Char.valid`
/// invariant); `decEq`/`beq`/`isEmpty` return the tagged `0`/`1` the switch
/// lowering reads via `clean_obj_tag`/`clean_unbox_uint64`, exactly like the
/// wired `l_Nat_decEq`.
///
/// The kernel native-reducer String operations borrow their string inputs.
const STRING_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_String_append",
        definition: "clean_obj* l_String_append(clean_obj* a, clean_obj* b) {\n  \
            size_t la = clean_string_len(a);\n  \
            size_t lb = clean_string_len(b);\n  \
            if (lb == SIZE_MAX || la > SIZE_MAX - lb - 1) { clean_panic(\"l_String_append: string size overflow\"); }\n  \
            char* buf = (char*)malloc(la + lb + 1);\n  \
            if (!buf) { clean_panic(\"l_String_append: allocation failed\"); }\n  \
            memcpy(buf, clean_string_data(a), la);\n  \
            memcpy(buf + la, clean_string_data(b), lb);\n  \
            buf[la + lb] = 0;\n  \
            clean_obj* r = clean_mk_string_from_bytes(buf, la + lb);\n  \
            free(buf);\n  \
            return r;\n}\n",
    },
    // Code points, not bytes: count non-continuation bytes ((b & 0xC0) != 0x80),
    // which equals `chars().count()` on the valid UTF-8 the carrier holds.
    PreludeShim {
        symbol: "l_String_length",
        definition: "clean_obj* l_String_length(clean_obj* s) {\n  \
            const unsigned char* p = (const unsigned char*)clean_string_data(s);\n  \
            size_t bytes = clean_string_len(s);\n  \
            uint64_t chars = 0;\n  \
            for (size_t i = 0; i < bytes; i++) {\n    \
            if ((p[i] & 0xC0) != 0x80) { chars++; }\n  \
            }\n  \
            return clean_nat_of_u64(chars);\n}\n",
    },
    // The carrier's explicit byte length includes an appended U+0000.
    PreludeShim {
        symbol: "l_String_push",
        definition: "clean_obj* l_String_push(clean_obj* s, clean_obj* c) {\n  \
            uint32_t cp = clean_unbox_uint32(c);\n  \
            size_t len = clean_string_len(s);\n  \
            if (len > SIZE_MAX - 5) { clean_panic(\"l_String_push: string size overflow\"); }\n  \
            char* buf = (char*)malloc(len + 4 + 1);\n  \
            if (!buf) { clean_panic(\"l_String_push: allocation failed\"); }\n  \
            memcpy(buf, clean_string_data(s), len);\n  \
            size_t k = len;\n  \
            if (cp < 0x80) { buf[k++] = (char)cp; }\n  \
            else if (cp < 0x800) {\n    \
            buf[k++] = (char)(0xC0 | (cp >> 6));\n    \
            buf[k++] = (char)(0x80 | (cp & 0x3F));\n  \
            } else if (cp < 0x10000) {\n    \
            buf[k++] = (char)(0xE0 | (cp >> 12));\n    \
            buf[k++] = (char)(0x80 | ((cp >> 6) & 0x3F));\n    \
            buf[k++] = (char)(0x80 | (cp & 0x3F));\n  \
            } else {\n    \
            buf[k++] = (char)(0xF0 | (cp >> 18));\n    \
            buf[k++] = (char)(0x80 | ((cp >> 12) & 0x3F));\n    \
            buf[k++] = (char)(0x80 | ((cp >> 6) & 0x3F));\n    \
            buf[k++] = (char)(0x80 | (cp & 0x3F));\n  \
            }\n  \
            buf[k] = 0;\n  \
            clean_obj* r = clean_mk_string_from_bytes(buf, k);\n  \
            free(buf);\n  \
            return r;\n}\n",
    },
    // Byte equality IS code-point equality on UTF-8, so `memcmp` decides both
    // `decEq` and `beq` exactly.
    PreludeShim {
        symbol: "l_String_decEq",
        definition: "clean_obj* l_String_decEq(clean_obj* a, clean_obj* b) {\n  \
            size_t la = clean_string_len(a);\n  \
            int eq = la == clean_string_len(b) &&\n      \
            memcmp(clean_string_data(a), clean_string_data(b), la) == 0;\n  \
            return clean_box(eq ? 1 : 0);\n}\n",
    },
    PreludeShim {
        symbol: "l_String_beq",
        definition: "clean_obj* l_String_beq(clean_obj* a, clean_obj* b) {\n  \
            size_t la = clean_string_len(a);\n  \
            int eq = la == clean_string_len(b) &&\n      \
            memcmp(clean_string_data(a), clean_string_data(b), la) == 0;\n  \
            return clean_box(eq ? 1 : 0);\n}\n",
    },
    PreludeShim {
        symbol: "l_String_isEmpty",
        definition: "clean_obj* l_String_isEmpty(clean_obj* s) {\n  \
            return clean_box(clean_string_len(s) == 0 ? 1 : 0);\n}\n",
    },
    PreludeShim {
        symbol: "l_String_utf8ByteSize",
        definition: "clean_obj* l_String_utf8ByteSize(clean_obj* s) {\n  \
            return clean_nat_of_u64((uint64_t)clean_string_len(s));\n}\n",
    },
];

/// All prelude shim tables, in one place. The union of these symbols is the
/// `PRIMITIVE_DENYLIST` the #14 dependency-closure boundary treats as never
/// compiled-from-source even if their bodies lower, so the shim always wins and
/// the two cannot conflict or double-define.
const ALL_PRELUDE_SHIM_TABLES: &[&[PreludeShim]] = &[
    NAT_PRELUDE_SHIMS,
    INT_PRELUDE_SHIMS,
    UINT32_PRELUDE_SHIMS,
    UINT64_PRELUDE_SHIMS,
    SOURCE_STRING_PRELUDE_SHIMS,
    STRING_PRELUDE_SHIMS,
    BOOL_PRELUDE_SHIMS,
    TYPECLASS_PRELUDE_SHIMS,
    IO_PRELUDE_SHIMS,
    QUOT_PRELUDE_SHIMS,
];

/// Whether `mangled` names a prelude symbol backed by a runtime shim, i.e. one
/// that must stay an extern (shimmed) rather than be compiled from source by the
/// #14 dependency-closure boundary in `compile`.
pub fn is_primitive_denylisted(mangled: &str) -> bool {
    ALL_PRELUDE_SHIM_TABLES
        .iter()
        .flat_map(|table| table.iter())
        .any(|shim| shim.symbol == mangled)
}

/// Every mangled symbol the prelude shim tables define, in table order — the
/// `l_*` half of what an emitted object may leave for the link to resolve
/// (the runtime defines only `clean_*`). Read by the WS6.14 census LINK oracle
/// in `compile`'s battery tests and, feature-free, by the WS6.13
/// runtime-archive test that links a driver demanding EVERY shim against
/// `libclean_runtime.a`.
#[cfg(test)]
pub(crate) fn prelude_shim_symbols() -> Vec<&'static str> {
    ALL_PRELUDE_SHIM_TABLES
        .iter()
        .flat_map(|table| table.iter())
        .map(|shim| shim.symbol)
        .collect()
}

/// Every prelude shim as `(symbol, C definition)`, in table order. Read by
/// the WS6.14 census's shim-ABI check, which compares each definition's C
/// signature with the declaration an emitted module links against, and by the
/// same check in the experimental trust-cg lane (`native_trustcg`).
#[cfg(feature = "trust-ir-backend")]
pub(crate) fn prelude_shim_definitions() -> Vec<(&'static str, &'static str)> {
    ALL_PRELUDE_SHIM_TABLES
        .iter()
        .flat_map(|table| table.iter())
        .map(|shim| (shim.symbol, shim.definition))
        .collect()
}

/// The whole prelude shim union as ONE C translation unit (what a consumer
/// links an emitted object against), minus the definitions named in `omit`.
/// `omit` exists for the census LINK oracle's mutation control: it drops a
/// definition from the LINK input while the lowering's denylist stays
/// untouched, so the link must name the missing symbol. The experimental
/// trust-cg lane (`native_trustcg`) compiles it, with nothing omitted, into the
/// shim object it links a trust-cg object against.
///
/// Not test-only and not feature-gated since WS6.13: this TU is the
/// `clean_prelude_shims.o` member of the linkable runtime archive
/// `clean native-runtime` materializes (`native_runtime`), the only way the
/// shims — Rust string tables, not a C file in the tree — reach a consumer
/// linking an emitted object outside this process.
pub(crate) fn prelude_shims_translation_unit(omit: &[&str]) -> String {
    let mut tu = String::from("#include <stdio.h>\n#include \"clean_runtime.h\"\n");
    for shim in ALL_PRELUDE_SHIM_TABLES
        .iter()
        .flat_map(|table| table.iter())
        .filter(|shim| !omit.contains(&shim.symbol))
    {
        tu.push_str(shim.definition);
        tu.push('\n');
    }
    tu
}

/// Faithful C shims for the nullary `Bool` constructors the L5 emitter lowers
/// `true` / `false` to (mangled `l_true` / `l_false`).
const BOOL_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_true",
        definition: "clean_obj* l_true(void) {\n  return clean_box(1);\n}\n",
    },
    PreludeShim {
        symbol: "l_false",
        definition: "clean_obj* l_false(void) {\n  return clean_box(0);\n}\n",
    },
];

/// Faithful C shims for the heterogeneous-arithmetic typeclass externs the L5
/// emitter lowers `a + b` / `a * b` / `a - b` to.
///
/// R3 representation: a single-method-class instance IS its bare method
/// closure (the compiler's trivial-structure elimination — `HAdd.mk f = f`,
/// `HAdd.hAdd inst = inst`). The `mk` shims are identity on the method and
/// the projection shims apply the instance directly; the pre-R3 cell
/// spelling (`alloc_ctor` + `ctor_get`) crashed against compiled instances
/// once construction stopped allocating (`clean_ctor_get` on a closure).
const TYPECLASS_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_HAdd_mk",
        definition: "clean_obj* l_HAdd_mk(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* addFn) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return addFn;\n}\n",
    },
    PreludeShim {
        symbol: "l_HAdd_hAdd",
        definition: "clean_obj* l_HAdd_hAdd(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* inst, clean_obj* x, clean_obj* y) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return clean_apply_2(inst, x, y);\n}\n",
    },
    PreludeShim {
        symbol: "l_HMul_mk",
        definition: "clean_obj* l_HMul_mk(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* mulFn) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return mulFn;\n}\n",
    },
    PreludeShim {
        symbol: "l_HMul_hMul",
        definition: "clean_obj* l_HMul_hMul(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* inst, clean_obj* x, clean_obj* y) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return clean_apply_2(inst, x, y);\n}\n",
    },
    PreludeShim {
        symbol: "l_HSub_mk",
        definition: "clean_obj* l_HSub_mk(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* subFn) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return subFn;\n}\n",
    },
    PreludeShim {
        symbol: "l_HSub_hSub",
        definition: "clean_obj* l_HSub_hSub(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* inst, clean_obj* x, clean_obj* y) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return clean_apply_2(inst, x, y);\n}\n",
    },
    PreludeShim {
        symbol: "l_HDiv_mk",
        definition: "clean_obj* l_HDiv_mk(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* divFn) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return divFn;\n}\n",
    },
    PreludeShim {
        symbol: "l_HDiv_hDiv",
        definition: "clean_obj* l_HDiv_hDiv(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* inst, clean_obj* x, clean_obj* y) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return clean_apply_2(inst, x, y);\n}\n",
    },
    PreludeShim {
        symbol: "l_HMod_mk",
        definition: "clean_obj* l_HMod_mk(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* modFn) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return modFn;\n}\n",
    },
    PreludeShim {
        symbol: "l_HMod_hMod",
        definition: "clean_obj* l_HMod_hMod(clean_obj* a, clean_obj* b, clean_obj* g, \
            clean_obj* inst, clean_obj* x, clean_obj* y) {\n  \
            (void)a; (void)b; (void)g;\n  \
            return clean_apply_2(inst, x, y);\n}\n",
    },
    // `instToStringNat : ToString Nat` (B04, GAP_SWEEP_2026-07-09). The kernel
    // instance now carries the GENUINE `⟨fun n => Nat.repr n⟩` body (a
    // `Nat.rec`-based digit recursion the L5 emitter cannot lower), so the
    // emitted C references it as an extern instead of compiling it from
    // source. The shim builds the instance ctor around a decimal renderer.
    // When the instance closure is actually applied — `ToString.toString inst x`
    // lowers to `clean_apply_1(inst, x)`, invoking `clean_shim_nat_repr` — a
    // heap `Nat` (>= 2^63) must be read heap-aware: the renderer decodes via
    // `clean_nat_to_u128` (RUNG B, the same faithful rendering as `l_toString`)
    // rather than the tagged-only `clean_unbox`, which silently truncated a heap
    // pointer to garbage. Consumes `x` per the all-owned closure ABI. `u128`
    // needs up to 39 digits, so the buffer is 48.
    PreludeShim {
        symbol: "l_instToStringNat",
        definition: "static clean_obj* clean_shim_nat_repr(clean_obj* n) {\n  \
            unsigned __int128 v = clean_nat_to_u128(n);\n  \
            clean_dec(n);\n  \
            char buf[48];\n  \
            int i = (int)sizeof(buf);\n  \
            buf[--i] = 0;\n  \
            if (v == 0) { buf[--i] = '0'; }\n  \
            else { while (v > 0) { buf[--i] = (char)('0' + (unsigned)(v % 10)); v /= 10; } }\n  \
            return clean_mk_string(buf + i);\n}\n\
            clean_obj* l_instToStringNat(void) {\n  \
            return clean_alloc_closure((void*)clean_shim_nat_repr, 1, 0);\n}\n",
    },
    // `instToStringChar : ToString Char`. The kernel instance carries Lean's
    // `⟨fun c => String.singleton c⟩`, which this prelude spells `String.mk [c]`
    // because it declares no `String.singleton`. That body MUST NOT be lowered
    // from source: `String.mk` compiles to `clean_alloc_ctor(0, 1, 0, list)` — a
    // ctor cell over the `List Char` model — while the runtime carrier is the
    // flat byte string `clean_mk_string` builds. Measured on the emitted C
    // (2026-08-27): a source-lowered `⟨fun c => String.mk [c]⟩` produces exactly
    // that ctor cell, and it links, so `IO.println` would then read a `len` word
    // out of a constructor field. That is the same silent miscompile
    // [`STRING_PRELUDE_SHIMS`] exists to close, and it is why this instance is
    // denylisted and rendered here instead.
    //
    // The encoder is `l_String_push`'s, minus the prefix: a Char arrives boxed
    // and is read with tagged-or-heap `clean_unbox_uint32`, and is a valid
    // Unicode scalar by the `Char.valid` invariant. U+0000 occupies one byte,
    // retained by the sized constructor just like every other scalar.
    // Consumes its argument per the all-owned closure ABI, like the `Nat` shim
    // above (`clean_dec` on a tagged scalar is a no-op).
    PreludeShim {
        symbol: "l_instToStringChar",
        definition: "static clean_obj* clean_shim_char_to_string(clean_obj* c) {\n  \
            uint32_t cp = clean_unbox_uint32(c);\n  \
            clean_dec(c);\n  \
            char buf[5];\n  \
            size_t k = 0;\n  \
            if (cp < 0x80) { buf[k++] = (char)cp; }\n  \
            else if (cp < 0x800) {\n    \
            buf[k++] = (char)(0xC0 | (cp >> 6));\n    \
            buf[k++] = (char)(0x80 | (cp & 0x3F));\n  \
            } else if (cp < 0x10000) {\n    \
            buf[k++] = (char)(0xE0 | (cp >> 12));\n    \
            buf[k++] = (char)(0x80 | ((cp >> 6) & 0x3F));\n    \
            buf[k++] = (char)(0x80 | (cp & 0x3F));\n  \
            } else {\n    \
            buf[k++] = (char)(0xF0 | (cp >> 18));\n    \
            buf[k++] = (char)(0x80 | ((cp >> 12) & 0x3F));\n    \
            buf[k++] = (char)(0x80 | ((cp >> 6) & 0x3F));\n    \
            buf[k++] = (char)(0x80 | (cp & 0x3F));\n  \
            }\n  \
            buf[k] = 0;\n  \
            return clean_mk_string_from_bytes(buf, k);\n}\n\
            clean_obj* l_instToStringChar(void) {\n  \
            return clean_alloc_closure((void*)clean_shim_char_to_string, 1, 0);\n}\n",
    },
];

/// Faithful C shims for the `IO`-monad prelude externs the L5 emitter lowers to,
/// under the eager-effect model documented in the module header.
const IO_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_IO",
        definition: "clean_obj* l_IO(void) {\n  return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_Unit_unit",
        definition: "clean_obj* l_Unit_unit(void) {\n  return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_IO_println",
        definition: "clean_obj* l_IO_println(clean_obj* s) {\n  \
            fwrite(clean_string_data(s), 1, clean_string_len(s), stdout);\n  \
            fputc('\\n', stdout);\n  \
            return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_IO_print",
        definition: "clean_obj* l_IO_print(clean_obj* s) {\n  \
            fwrite(clean_string_data(s), 1, clean_string_len(s), stdout);\n  \
            return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_IO_eprintln",
        definition: "clean_obj* l_IO_eprintln(clean_obj* s) {\n  \
            fwrite(clean_string_data(s), 1, clean_string_len(s), stderr);\n  \
            fputc('\\n', stderr);\n  \
            return clean_box(0);\n}\n",
    },
    // `Pure.pure` / `Bind.bind` are Lean's class projections (2026-09-28;
    // until then instance-less axioms that proved `False`), so each call
    // carries its instance argument after the monad: `@Pure.pure m inst α v`,
    // `@Bind.bind m inst α β a k`. The shims implement the eager-IO semantics
    // only, which is why `native_eager_io_check` admits them at `IO`/`Id`
    // alone; the instance is erased like the other type-level arguments.
    PreludeShim {
        symbol: "l_Pure_pure",
        definition: "clean_obj* l_Pure_pure(clean_obj* m, clean_obj* inst, clean_obj* ty, \
            clean_obj* v) {\n  \
            (void)m; clean_dec(inst); (void)ty;\n  \
            return v;\n}\n",
    },
    PreludeShim {
        symbol: "l_Bind_bind",
        definition: "clean_obj* l_Bind_bind(clean_obj* m, clean_obj* inst, clean_obj* ta, \
            clean_obj* tb, clean_obj* a, clean_obj* k) {\n  \
            (void)m; clean_dec(inst); (void)ta; (void)tb;\n  \
            return clean_apply_1(k, a);\n}\n",
    },
    // `IO.pure` under the eager model: an `IO α` value IS its result.
    PreludeShim {
        symbol: "l_IO_pure",
        definition: "clean_obj* l_IO_pure(clean_obj* ty, clean_obj* v) {\n  \
            (void)ty;\n  \
            return v;\n}\n",
    },
    // `IO.bind` lowers to `l_IO_bind(io_type, unit_type, action, cont)` for the
    // explicit-bind shape. Under the eager-effect model the action has already
    // executed, so apply the continuation to its result.
    PreludeShim {
        symbol: "l_IO_bind",
        definition: "clean_obj* l_IO_bind(clean_obj* io_type, clean_obj* unit_type, \
            clean_obj* action, clean_obj* cont) {\n  \
            (void)io_type; (void)unit_type;\n  \
            return clean_apply_1(cont, action);\n}\n",
    },
];

/// The genuine-`Init` arity of the console-output shims. Clean's bootstrap
/// program environment declares `IO.println : String → IO Unit` (one C
/// argument, [`IO_PRELUDE_SHIMS`]); Lean's genuine `Init`, which a program
/// reaching an artifact import elaborates against, declares
/// `IO.println {α} [ToString α] (s : α) : IO Unit` (and `IO.print`,
/// `IO.eprintln` alike), so the emitter calls
/// `l_IO_println(clean_box(0), inst, s)`. Lean's body prints
/// `toString s` (plus the newline); the instance is the single-field `ToString`
/// structure, which the emitter represents as its `toString` closure (see
/// `l_instToStringNat`), so `toString s` is `clean_apply_1(inst, s)`, which
/// consumes both. As in `l_toString`, a scalar or non-closure `inst` means the
/// caller erased the instance, so each shim panics rather than let
/// `clean_apply_1` jump through a tagged scalar's payload. These are never in [`ALL_PRELUDE_SHIM_TABLES`]: they define
/// the same symbols, and [`genuine_init_arity_variant`] picks one per build
/// from the arity the emitted C actually calls.
const GENUINE_INIT_IO_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_IO_println",
        definition: "clean_obj* l_IO_println(clean_obj* ty, clean_obj* inst, clean_obj* x) {\n  \
            (void)ty;\n  \
            if (clean_is_scalar(inst) || inst->header.kind != CLEAN_OBJ_KIND_CLOSURE) {\n    \
            clean_panic(\"IO.println: ToString instance is not a method closure\");\n  \
            }\n  \
            clean_obj* s = clean_apply_1(inst, x);\n  \
            fwrite(clean_string_data(s), 1, clean_string_len(s), stdout);\n  \
            fputc('\\n', stdout);\n  \
            clean_dec(s);\n  \
            return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_IO_print",
        definition: "clean_obj* l_IO_print(clean_obj* ty, clean_obj* inst, clean_obj* x) {\n  \
            (void)ty;\n  \
            if (clean_is_scalar(inst) || inst->header.kind != CLEAN_OBJ_KIND_CLOSURE) {\n    \
            clean_panic(\"IO.print: ToString instance is not a method closure\");\n  \
            }\n  \
            clean_obj* s = clean_apply_1(inst, x);\n  \
            fwrite(clean_string_data(s), 1, clean_string_len(s), stdout);\n  \
            clean_dec(s);\n  \
            return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_IO_eprintln",
        definition: "clean_obj* l_IO_eprintln(clean_obj* ty, clean_obj* inst, clean_obj* x) {\n  \
            (void)ty;\n  \
            if (clean_is_scalar(inst) || inst->header.kind != CLEAN_OBJ_KIND_CLOSURE) {\n    \
            clean_panic(\"IO.eprintln: ToString instance is not a method closure\");\n  \
            }\n  \
            clean_obj* s = clean_apply_1(inst, x);\n  \
            fwrite(clean_string_data(s), 1, clean_string_len(s), stderr);\n  \
            fputc('\\n', stderr);\n  \
            clean_dec(s);\n  \
            return clean_box(0);\n}\n",
    },
];

/// The C argument count of [`GENUINE_INIT_IO_PRELUDE_SHIMS`]' definitions.
const GENUINE_INIT_IO_ARITY: usize = 3;

/// Mask C literal/comment contents only for the arity scanner. Keep byte
/// offsets and newlines stable, and retain each literal as an opaque operand.
/// This does not change the emitted-C coverage checks or parse preprocessing.
fn c_arity_scan_code(source: &str) -> String {
    fn blank(out: &mut String, ch: char) {
        if ch == '\n' || ch == '\r' {
            out.push(ch);
        } else {
            for _ in 0..ch.len_utf8() {
                out.push(' ');
            }
        }
    }

    let mut out = String::with_capacity(source.len());
    let mut chars = source.chars().peekable();
    let mut quoted = None;
    let mut escaped = false;
    let mut line_comment = false;
    let mut block_comment = false;
    while let Some(ch) = chars.next() {
        if let Some(delimiter) = quoted {
            blank(&mut out, ch);
            if ch == '\\' && matches!(chars.peek().copied(), Some('\n' | '\r')) {
                // Line splicing precedes quote escape interpretation. Keep
                // the parity of any earlier logical backslash unchanged.
                if let Some(newline) = chars.next() {
                    out.push(newline);
                    if newline == '\r' && chars.peek() == Some(&'\n') {
                        let _ = chars.next();
                        out.push('\n');
                    }
                }
            } else if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == delimiter {
                quoted = None;
            }
        } else if line_comment {
            blank(&mut out, ch);
            // C's backslash-newline keeps a // comment on its logical line.
            if ch == '\\' && matches!(chars.peek().copied(), Some('\n' | '\r')) {
                if let Some(newline) = chars.next() {
                    out.push(newline);
                    if newline == '\r' && chars.peek() == Some(&'\n') {
                        let _ = chars.next();
                        out.push('\n');
                    }
                }
            } else if ch == '\n' || ch == '\r' {
                line_comment = false;
            }
        } else if block_comment {
            blank(&mut out, ch);
            if ch == '*' && chars.peek() == Some(&'/') {
                let _ = chars.next();
                out.push(' ');
                block_comment = false;
            }
        } else if ch == '"' || ch == '\'' {
            // Blanking a literal entirely would turn f("text") into f().
            out.push('0');
            quoted = Some(ch);
        } else if ch == '/' && chars.peek() == Some(&'/') {
            let _ = chars.next();
            out.push_str("  ");
            line_comment = true;
        } else if ch == '/' && chars.peek() == Some(&'*') {
            let _ = chars.next();
            out.push_str("  ");
            block_comment = true;
        } else {
            out.push(ch);
        }
    }
    out
}

/// Every arity at which `emitted_c` uses `symbol`: each call `symbol(a, …)`
/// (top-level arguments counted with parentheses balanced) and each closure
/// `clean_alloc_closure((void*)symbol, N, …)`. A line that opens with
/// `clean_obj* symbol(` declares or defines it and is not a use.
fn symbol_use_arities(emitted_c: &str, symbol: &str) -> BTreeSet<usize> {
    let mut arities = BTreeSet::new();
    let declaration = format!("clean_obj* {symbol}(");
    let code = c_arity_scan_code(emitted_c);
    for line in code.lines() {
        if line.trim_start().starts_with(&declaration) {
            continue;
        }
        let bytes = line.as_bytes();
        let mut from = 0usize;
        while let Some(rel) = line[from..].find(symbol) {
            let start = from + rel;
            let end = start + symbol.len();
            from = end;
            if start > 0 && is_ident_byte(bytes[start - 1]) {
                continue;
            }
            match bytes.get(end) {
                Some(b'(') => {
                    if let Some(count) = call_argument_count(&line[end + 1..]) {
                        arities.insert(count);
                    }
                }
                Some(b',') if line[..start].ends_with("(void*)") => {
                    let digits: String = line[end + 1..]
                        .trim_start()
                        .chars()
                        .take_while(char::is_ascii_digit)
                        .collect();
                    if let Ok(count) = digits.parse() {
                        arities.insert(count);
                    }
                }
                _ => {}
            }
        }
    }
    arities
}

/// Count the top-level arguments of a call whose text after the opening
/// parenthesis is `rest`; `None` when the call does not close on this line.
fn call_argument_count(rest: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut commas = 0usize;
    let mut nonblank = false;
    for ch in rest.chars() {
        match ch {
            '(' => depth += 1,
            ')' if depth == 0 => return Some(if nonblank { commas + 1 } else { 0 }),
            ')' => depth -= 1,
            ',' if depth == 0 => commas += 1,
            _ => {}
        }
        if !ch.is_whitespace() {
            nonblank = true;
        }
    }
    None
}

/// The shim to inject for `shim`'s symbol given how `emitted_c` uses it: the
/// genuine-`Init` variant when every use has its arity, `shim` itself
/// otherwise. A build using one symbol at both arities is refused: no single C
/// definition satisfies it, and mixing the two Inits in one program is the
/// world mixing the source setup exists to prevent.
fn genuine_init_arity_variant(
    emitted_c: &str,
    shim: &'static PreludeShim,
) -> anyhow::Result<&'static PreludeShim> {
    let Some(genuine) = GENUINE_INIT_IO_PRELUDE_SHIMS
        .iter()
        .find(|candidate| candidate.symbol == shim.symbol)
    else {
        return Ok(shim);
    };
    let arities = symbol_use_arities(emitted_c, shim.symbol);
    if arities.contains(&GENUINE_INIT_IO_ARITY) {
        if arities.len() > 1 {
            bail!(
                "native build refuses `{}` used at arities {arities:?}: the bootstrap \
                 `String → IO Unit` shim and the genuine-Init `[ToString α] (s : α)` shim \
                 define the same symbol, so one program cannot call both",
                shim.symbol
            );
        }
        return Ok(genuine);
    }
    Ok(shim)
}

/// Faithful C shims for Lean's quotient eliminators. `Quot.mk` is runtime-
/// identity (the compiler's `Quot.mk → arg[2]` rule), so `Quot r` IS its
/// representative and the eliminators reduce to applying the given function to
/// the underlying value.
///
/// The emitter lowers both with ALL kernel arguments materialized positionally
/// (erased type/relation/motive args become `clean_box(0)`), so the shim
/// signatures match the full kernel arity:
///
/// - `Quot.lift {α} {r} {β} (f) (h) (q) : β` → `l_Quot_lift(a, r, b, f, h, q)`.
///   The genuine computation: apply `f` to representative `q`. `h` is the erased
///   respects-`r` proof, materialized as an owned closure — dec'd per the
///   all-owned ABI so it is not leaked (the erased type args are `clean_box(0)`
///   immediates, void'd). Backs Multiset.cons `= fun a s => Quot.lift … s`.
/// - `Quot.ind {α} {r} {motive} (f) (q) : motive q` → `l_Quot_ind(a, r, m, f, q)`.
///   A PROOF eliminator (`motive : Quot r → Prop`): the result is proof-
///   irrelevant, so it is the erased proof `clean_box(0)` (value-identical to the
///   erased-proof body the emitter lowers the minor premise to); `f`/`q` are
///   consumed. Backs Finset.cons's `Multiset.nodup_cons` obligation.
const QUOT_PRELUDE_SHIMS: &[PreludeShim] = &[
    PreludeShim {
        symbol: "l_Quot_lift",
        definition: "clean_obj* l_Quot_lift(clean_obj* a, clean_obj* r, clean_obj* b, \
            clean_obj* f, clean_obj* h, clean_obj* q) {\n  \
            (void)a; (void)r; (void)b;\n  \
            clean_dec(h);\n  \
            return clean_quot_lift(f, q);\n}\n",
    },
    PreludeShim {
        symbol: "l_Quot_ind",
        definition: "clean_obj* l_Quot_ind(clean_obj* a, clean_obj* r, clean_obj* m, \
            clean_obj* f, clean_obj* q) {\n  \
            (void)a; (void)r; (void)m;\n  \
            return clean_quot_ind(f, q);\n}\n",
    },
];

/// The shape of the entry declaration, which selects the synthesized driver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntryKind {
    /// A nullary `Nat`-returning entry: unbox and print the result.
    Nat,
    /// An `IO` entry: drive the (eager) IO action, then exit per [`EntryExit`].
    Io,
}

/// What the synthesized driver hands the entry — Lean 4's two `main` shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum EntryArgs {
    /// `def main : IO α` — call the entry with no arguments.
    #[default]
    None,
    /// `def main (args : List String) : IO α` — marshal `argv[1..]` into a
    /// `List String` and pass it.
    Argv,
}

/// How the synthesized driver turns the entry's returned object into the
/// process exit status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum EntryExit {
    /// `IO Unit` (and the nullary `Nat` driver): always exit `0`.
    #[default]
    AlwaysZero,
    /// `IO UInt32` — Lean 4's entry contract: the returned `UInt32` **is** the
    /// process status.
    FromUInt32,
}

/// The full entry contract: which driver to synthesize, what to call the entry
/// with, and what to return from `main`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct EntryContract {
    /// Nat-print driver vs IO driver.
    pub(crate) kind: EntryKind,
    /// Call shape, from the emitted C prototype (checked against the Lean type).
    pub(crate) args: EntryArgs,
    /// Exit shape, from the Lean type — the emitted C cannot carry it.
    pub(crate) exit: EntryExit,
}

/// The `IO`-monad prelude externs the L5 emitter only lowers to for `IO`
/// entries: a build that calls any of them drives an `IO` entry. Read off the
/// emitted C by [`classify_entry`], and off an emitted trust-ir module's
/// declarations by the experimental trust-cg lane (`native_trustcg`).
pub(crate) const IO_ENTRY_MARKERS: [&str; 8] = [
    "l_IO_println",
    "l_IO_print",
    "l_IO_eprintln",
    "l_IO_bind",
    "l_Bind_bind",
    "l_Pure_pure",
    "l_IO",
    "l_Unit_unit",
];

/// Decide whether the emitted entry is an `IO` program or a nullary `Nat`
/// computation, by detecting the `IO`-monad prelude externs the L5 emitter only
/// lowers to for `IO` entries.
pub fn classify_entry(emitted_c: &str) -> EntryKind {
    if IO_ENTRY_MARKERS
        .iter()
        .any(|m| emitted_c.contains(&format!("{m}(")))
    {
        EntryKind::Io
    } else {
        EntryKind::Nat
    }
}

/// Count the `clean_obj*` parameters the emitted C declares for `mangled_entry`.
///
/// This PARSES the emitted artifact's own prototype rather than scanning source
/// text for a signature: the C prototype is the ground truth for the call the
/// driver has to make (lambda lifting, closure conversion and eta can move
/// binders between the Lean type and the emitted symbol). `Some(0)` is a
/// declared `(void)`; `None` means the emitted C declares no such entry.
pub fn entry_arity_in_c(emitted_c: &str, mangled_entry: &str) -> Option<usize> {
    let needle = format!("{mangled_entry}(");
    let bytes = emitted_c.as_bytes();
    let mut from = 0usize;
    while let Some(rel) = emitted_c[from..].find(&needle) {
        let start = from + rel;
        from = start + needle.len();
        // Whole-identifier match only: `l_mainly(` must not answer for `l_main`.
        if start > 0 && is_ident_byte(bytes[start - 1]) {
            continue;
        }
        let open = start + needle.len();
        let close = match emitted_c[open..].find(')') {
            Some(rel_close) => open + rel_close,
            None => continue,
        };
        let params = emitted_c[open..close].trim();
        return Some(if params.is_empty() || params == "void" {
            0
        } else {
            params.split(',').count()
        });
    }
    None
}

/// Peel the type-checking-transparent `MData` wrapper off an expression.
fn strip_mdata(expr: &Expr) -> &Expr {
    let mut cur = expr;
    while let ExprKind::MData(_, inner) = cur.kind() {
        cur = inner;
    }
    cur
}

/// Is `expr` the constant `name` (modulo `MData`)?
fn is_const_named(expr: &Expr, name: &str) -> bool {
    matches!(strip_mdata(expr).kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

/// Is `expr` syntactically `List String` — the type of Lean's `main` argument?
fn is_list_string(expr: &Expr) -> bool {
    match strip_mdata(expr).kind() {
        ExprKind::App(f, a) => is_const_named(f, "List") && is_const_named(a, "String"),
        _ => false,
    }
}

/// Split an entry's elaborated type into its explicit binder domains and the
/// result type.
fn peel_entry_binders(ty: &Expr) -> (Vec<&Expr>, &Expr) {
    let mut domains = Vec::new();
    let mut cur = strip_mdata(ty);
    while let ExprKind::Pi(_, domain, body) = cur.kind() {
        domains.push(domain.as_ref());
        cur = strip_mdata(body);
    }
    (domains, cur)
}

/// Derive the full entry contract: the driver shape from the emitted C, the
/// call shape from the emitted C prototype, and the exit shape from the Lean
/// type.
///
/// Fails closed rather than mis-marshalling: an entry the emitted C declares
/// with an argument is only driven when the Lean type agrees that the argument
/// is `List String`, and an entry with more than one argument is refused with a
/// message naming what Lean's entry contract allows.
pub(crate) fn entry_contract(
    decl: &str,
    emitted_c: &str,
    decl_type: Option<&Expr>,
) -> anyhow::Result<EntryContract> {
    let mangled_entry = mangle_decl(decl);
    entry_contract_from_parts(
        decl,
        classify_entry(emitted_c),
        entry_arity_in_c(emitted_c, &mangled_entry),
        decl_type,
    )
}

/// [`entry_contract`] from its parts: the driver shape and the emitted entry's
/// arity, however the caller read them. The C lane reads both off the emitted
/// C ([`classify_entry`], [`entry_arity_in_c`]); the experimental trust-cg lane
/// (`native_trustcg`) reads them off the emitted trust-ir module. The exit
/// shape and the argv cross-check are this one function either way.
pub(crate) fn entry_contract_from_parts(
    decl: &str,
    kind: EntryKind,
    c_arity: Option<usize>,
    decl_type: Option<&Expr>,
) -> anyhow::Result<EntryContract> {
    // The Nat driver prints the unboxed result and exits 0; it has exactly one
    // supported shape (nullary), guarded in `build_native_binary_in_scratch`.
    if kind == EntryKind::Nat {
        return Ok(EntryContract {
            kind,
            args: EntryArgs::None,
            exit: EntryExit::AlwaysZero,
        });
    }

    let binders = decl_type.map(peel_entry_binders);

    // EXIT SHAPE — only the Lean type carries it. `IO Unit` and `IO UInt32`
    // both lower to `clean_obj* l_main(...)`, so the emitted C cannot tell
    // them apart; an `IO UInt32` entry driven as `IO Unit` silently exits 0
    // where Lean exits with the returned status.
    let exit = match binders.as_ref().map(|(_, result)| *result) {
        Some(result) => match strip_mdata(result).kind() {
            ExprKind::App(f, a) if is_const_named(f, "IO") && is_const_named(a, "UInt32") => {
                EntryExit::FromUInt32
            }
            _ => EntryExit::AlwaysZero,
        },
        None => EntryExit::AlwaysZero,
    };

    // CALL SHAPE — the emitted prototype decides how many arguments to pass.
    let args = match c_arity {
        None | Some(0) => EntryArgs::None,
        Some(1) => {
            if let Some((domains, _)) = binders.as_ref() {
                let ok = domains.len() == 1 && is_list_string(domains[0]);
                if !ok {
                    bail!(
                        "native build entry `{decl}` takes one argument the driver cannot \
                         marshal: Lean's entry contract is `def main : IO Unit`, \
                         `def main : IO UInt32`, or `def main (args : List String) : IO ...`."
                    );
                }
            }
            EntryArgs::Argv
        }
        Some(n) => bail!(
            "native build entry `{decl}` is emitted with {n} arguments; Lean's entry \
             contract allows at most one (`def main (args : List String) : IO ...`)."
        ),
    };

    Ok(EntryContract { kind, args, exit })
}

/// Emit the C closure for `decl` (root + transitive compilable deps) through
/// the exact `clean compile --emit c` pipeline, together with the entry's
/// elaborated type.
///
/// The type is not optional garnish: it is the only place the
/// `IO Unit` / `IO UInt32` distinction survives lowering, and therefore the
/// only input that can decide the process exit status. It shares one
/// elaboration with the emit, so there is no cheaper type-less variant to
/// reach for.
pub fn emit_entry_c_with_type(
    file: &Path,
    decl: &str,
    opt_level: u8,
) -> anyhow::Result<(String, Option<Expr>)> {
    compile_to_string_with_decl_type(CompileArgs {
        file: Some(file.to_path_buf()),
        decl: Some(decl.to_owned()),
        emit: EmitFormat::C,
        opt_level,
        output: None,
        link_artifact: Vec::new(),
    })
    .with_context(|| format!("failed to emit C for `{decl}` in {}", file.display()))
}

/// Build a native executable for `decl` in `file` and write it to `out_path`.
///
/// This is the shared link/write step: it emits the closure C, classifies the
/// entry shape, selects the needed shims (failing closed if any extern is
/// uncovered), renders the combined translation unit, materializes the program
/// + the embedded Clean runtime into a scratch dir, cc-links a native binary,
/// and copies it to `out_path` (creating parent dirs). The scratch dir is
/// cleaned up on drop. `clean run` runs the binary in place via the lower-level
/// helpers; `clean lake run` calls this to land a stable binary it then execs.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) fn build_native_executable(
    file: &Path,
    decl: &str,
    opt_level: u8,
    out_path: &Path,
) -> anyhow::Result<()> {
    build_native_executable_with_source_sink(file, decl, opt_level, out_path, None)
}

/// Like [`build_native_executable`], but if `source_sink` is `Some`, also writes
/// the rendered combined translation unit (shims + emitted closure + `main`) to
/// that path before linking. `clean lake run` uses this to persist the C source
/// under `build_dir/native/c/<name>.c` for inspection/debugging.
pub fn build_native_executable_with_source_sink(
    file: &Path,
    decl: &str,
    opt_level: u8,
    out_path: &Path,
    source_sink: Option<&Path>,
) -> anyhow::Result<()> {
    let artifact = emit_native_c_artifact(file, decl, opt_level)?;
    let program = artifact.render()?;

    if let Some(sink) = source_sink {
        if let Some(parent) = sink.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("failed to create source dir {}", parent.display()))?;
        }
        std::fs::write(sink, &program)
            .with_context(|| format!("failed to write C source artifact {}", sink.display()))?;
    }

    let built = link_program_in_scratch(&program)?;

    if let Some(parent) = out_path.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("failed to create output dir {}", parent.display()))?;
    }
    std::fs::copy(&built.binary, out_path).with_context(|| {
        format!(
            "failed to copy native binary {} to {}",
            built.binary.display(),
            out_path.display()
        )
    })?;
    Ok(())
}

/// The result of compiling + linking the native entry binary into a scratch dir.
pub struct BuiltBinary {
    /// Path to the linked native executable inside the scratch dir.
    pub(crate) binary: PathBuf,
    /// Owns the scratch dir; dropped (and removed) when this struct is dropped,
    /// unless `--keep-temp` leaked it via [`keep_scratch`].
    _scratch: tempfile::TempDir,
}

impl BuiltBinary {
    /// The linked native executable inside the scratch dir.
    #[must_use]
    pub fn binary(&self) -> &Path {
        &self.binary
    }
}

/// Synthesize `main` + the prelude shims the emitted C references, materialize
/// against the embedded Clean runtime, and cc-link a native binary in a scratch
/// dir. Does NOT run it — the caller chooses to run-in-place (`clean run`) or
/// copy to a stable path (`clean lake run`).
pub fn build_native_binary_in_scratch(
    decl: &str,
    emitted_c: &str,
    decl_type: Option<&Expr>,
    nat_strict_guard: bool,
) -> anyhow::Result<BuiltBinary> {
    build_native_binary_with_policy(
        decl,
        emitted_c,
        decl_type,
        nat_strict_guard,
        StringLayoutPolicy::default(),
    )
}

fn build_native_binary_with_policy(
    decl: &str,
    emitted_c: &str,
    decl_type: Option<&Expr>,
    nat_strict_guard: bool,
    policy: StringLayoutPolicy,
) -> anyhow::Result<BuiltBinary> {
    let mangled_entry = mangle_decl(decl);
    let kind = classify_entry(emitted_c);

    if nat_strict_guard
        && kind == EntryKind::Nat
        && entry_arity_in_c(emitted_c, &mangled_entry) != Some(0)
    {
        bail!(
            "native build entry must be a nullary declaration: the emitted C does not \
             declare `{mangled_entry}(void)`. Use e.g. `def {decl} : Nat := Nat.succ 0` \
             or `def {decl} : IO Unit := IO.println \"hi\"`."
        );
    }

    let program = if policy.permits_byte_backed_bodies() {
        render_native_translation_unit_with_policy(decl, emitted_c, decl_type, policy)?
    } else {
        render_native_translation_unit(decl, emitted_c, decl_type)?
    };
    link_program_in_scratch(&program)
}

/// Render the combined translation unit (includes + the prelude shims the
/// emitted C references + the emitted closure + the synthesized driver `main`)
/// for `decl`. Selects the shim set from the entry shape; fails closed if the
/// emitted C references an uncovered mangled extern.
///
/// `decl_type` is the entry's elaborated type. It is optional because the two
/// non-`IO` render paths do not need it, but WITHOUT it an `IO UInt32` entry is
/// driven as if it were `IO Unit` (exit `0`) — the exit shape lives only in the
/// type. Production callers thread it through; pass `None` only where the
/// emitted artifact is genuinely all that exists.
pub(crate) fn render_native_translation_unit(
    decl: &str,
    emitted_c: &str,
    decl_type: Option<&Expr>,
) -> anyhow::Result<String> {
    render_native_translation_unit_with_policy(
        decl,
        emitted_c,
        decl_type,
        StringLayoutPolicy::default(),
    )
}

fn render_native_translation_unit_with_policy(
    decl: &str,
    emitted_c: &str,
    decl_type: Option<&Expr>,
    policy: StringLayoutPolicy,
) -> anyhow::Result<String> {
    let mangled_entry = mangle_decl(decl);
    let contract = entry_contract(decl, emitted_c, decl_type)?;
    let program = match contract.kind {
        EntryKind::Nat => {
            let shims = select_shims_from_tables_with_policy(
                emitted_c,
                &[
                    NAT_PRELUDE_SHIMS,
                    INT_PRELUDE_SHIMS,
                    UINT32_PRELUDE_SHIMS,
                    UINT64_PRELUDE_SHIMS,
                    SOURCE_STRING_PRELUDE_SHIMS,
                    STRING_PRELUDE_SHIMS,
                    BOOL_PRELUDE_SHIMS,
                    TYPECLASS_PRELUDE_SHIMS,
                    QUOT_PRELUDE_SHIMS,
                ],
                policy,
            )?;
            render_program(emitted_c, &shims, &mangled_entry)
        }
        EntryKind::Io => {
            // An IO program can also compute — arithmetic, recursion, matchers,
            // `toString`, quotient eliminators — so draw from all shim tables,
            // not just the IO ones.
            let shims = select_shims_from_tables_with_policy(
                emitted_c,
                &[
                    IO_PRELUDE_SHIMS,
                    NAT_PRELUDE_SHIMS,
                    INT_PRELUDE_SHIMS,
                    UINT32_PRELUDE_SHIMS,
                    UINT64_PRELUDE_SHIMS,
                    SOURCE_STRING_PRELUDE_SHIMS,
                    STRING_PRELUDE_SHIMS,
                    BOOL_PRELUDE_SHIMS,
                    TYPECLASS_PRELUDE_SHIMS,
                    QUOT_PRELUDE_SHIMS,
                ],
                policy,
            )?;
            render_io_program(emitted_c, &shims, &mangled_entry, contract)
        }
    };
    Ok(program)
}

/// Materialize the rendered program + the embedded Clean runtime into a scratch
/// dir and cc-link a native binary. Does NOT run it.
fn link_program_in_scratch(program: &str) -> anyhow::Result<BuiltBinary> {
    let dir = tempfile::Builder::new()
        .prefix("clean-native-")
        .tempdir()
        .context("failed to create scratch build directory")?;
    let build = materialize_build(dir.path(), program)?;
    let binary = compile_and_link(dir.path(), &build)?;

    Ok(BuiltBinary {
        binary,
        _scratch: dir,
    })
}

/// Leak the scratch dir so the caller can inspect it (`--keep-temp`). Returns
/// the retained path.
pub fn keep_scratch(built: BuiltBinary) -> PathBuf {
    built._scratch.keep()
}

/// Mangle a surface decl name to its emitted C symbol (`Foo.bar` -> `l_Foo_bar`).
pub(crate) fn mangle_decl(decl: &str) -> String {
    let mut out = String::from("l_");
    for ch in decl.chars() {
        match ch {
            '.' => out.push('_'),
            c if c.is_ascii_alphanumeric() || c == '_' => out.push(c),
            other => out.push(other),
        }
    }
    out
}

/// Like [`select_shims_from`] but over several tables, concatenated in order.
/// Extract-lane helper: shim coverage over emitted C TEXT — returns the
/// concatenated C definitions of every referenced shim, or an error naming
/// the first uncovered extern (fail-closed; `clean extract`).
pub fn select_shims_for_c_text(emitted_c: &str) -> anyhow::Result<String> {
    select_shims_for_c_text_with_policy(emitted_c, StringLayoutPolicy::default())
}

pub(crate) fn select_shims_for_c_text_with_policy(
    emitted_c: &str,
    policy: StringLayoutPolicy,
) -> anyhow::Result<String> {
    let shims = select_shims_from_tables_with_policy(emitted_c, ALL_PRELUDE_SHIM_TABLES, policy)?;
    Ok(shims
        .iter()
        .map(|s| s.definition)
        .collect::<Vec<_>>()
        .join("\n"))
}

/// Extract-lane helper: the mangled `l_*` symbol for a declaration.
pub fn mangle_decl_symbol(decl: &str) -> String {
    mangle_decl(decl)
}

/// Extract-lane helper: materialize the runtime + emitted C + a caller-
/// provided driver `main()` into `dir`, then cc-compile and link. Returns
/// the executable path.
pub fn build_extract_executable(
    dir: &Path,
    shims_c: &str,
    emitted_c: &str,
    driver_c: &str,
) -> anyhow::Result<PathBuf> {
    // Shims must precede the emitted closure (same-translation-unit forward
    // definition, matching the `clean run` layout).
    let program = format!("#include \"clean_runtime.h\"\n{shims_c}\n{emitted_c}\n{driver_c}");
    let build = materialize_build(dir, &program)?;
    compile_and_link(dir, &build)
}

#[cfg(test)]
fn select_shims_from_tables(
    emitted_c: &str,
    tables: &[&'static [PreludeShim]],
) -> anyhow::Result<Vec<&'static PreludeShim>> {
    select_shims_from_tables_with_policy(emitted_c, tables, StringLayoutPolicy::default())
}

fn select_shims_from_tables_with_policy(
    emitted_c: &str,
    tables: &[&'static [PreludeShim]],
    policy: StringLayoutPolicy,
) -> anyhow::Result<Vec<&'static PreludeShim>> {
    // String bodies refuse BEFORE selection: a source-lowered `String.*` body
    // would link cleanly and compute garbage against the byte-string carrier
    // (see STRING_PRELUDE_SHIMS), so it can never ride the double-emit guard
    // into the binary — shimmed symbol or not.
    if let Some(op) =
        first_source_lowered_string_body(emitted_c).filter(|_| !policy.permits_byte_backed_bodies())
    {
        bail!(
            "native build refuses source-lowered String body `{op}`: the runtime \
             `String` carrier is a flat byte string, but a body lowered from the \
             prelude's `List Char` model reads it as a constructor cell — it \
             links and silently computes garbage. Shimmed String ops: {:?}; add \
             a shim to STRING_PRELUDE_SHIMS in native_build (or keep `{op}` out \
             of the entry's dependency closure).",
            STRING_PRELUDE_SHIMS
                .iter()
                .map(|s| s.symbol)
                .collect::<Vec<_>>()
        );
    }
    let needed: Vec<&PreludeShim> = tables
        .iter()
        .flat_map(|table| table.iter())
        .filter(|shim| c_references_symbol(emitted_c, shim.symbol))
        // Double-emit guard: if a prelude fn is now compiled from source into the
        // emitted C, do NOT also inject the shim, or the linker sees two
        // definitions of `l_X`.
        .filter(|shim| !file_defines_symbol(emitted_c, shim.symbol))
        .map(|shim| genuine_init_arity_variant(emitted_c, shim))
        .collect::<anyhow::Result<_>>()?;

    if let Some(unknown) = first_uncovered_prelude_call(emitted_c, &needed) {
        bail!(
            "native build cannot satisfy prelude extern `{unknown}`: only the \
             shims {:?} are wired for this entry shape. Add a shim in native_build \
             (or restrict the entry).",
            tables
                .iter()
                .flat_map(|t| t.iter())
                .map(|s| s.symbol)
                .collect::<Vec<_>>()
        );
    }
    Ok(needed)
}

/// Scan the emitted C for mangled `l_*` calls and return the subset of `table`
/// needed to satisfy them.
#[cfg(test)]
fn select_shims_from(
    emitted_c: &str,
    table: &'static [PreludeShim],
) -> anyhow::Result<Vec<&'static PreludeShim>> {
    select_shims_from_tables(emitted_c, &[table])
}

/// Convenience for the `Nat` entry shapes used by `clean run` tests.
#[cfg(test)]
fn select_prelude_shims(emitted_c: &str) -> anyhow::Result<Vec<&'static PreludeShim>> {
    select_shims_from_tables(
        emitted_c,
        &[
            NAT_PRELUDE_SHIMS,
            INT_PRELUDE_SHIMS,
            BOOL_PRELUDE_SHIMS,
            TYPECLASS_PRELUDE_SHIMS,
        ],
    )
}

/// Find the first mangled prelude call (`l_Foo_bar(`) in `emitted_c` that is
/// neither a user-emitted body nor a covered shim. Returns the symbol name.
fn first_uncovered_prelude_call(
    emitted_c: &str,
    covered: &[&'static PreludeShim],
) -> Option<String> {
    for line in emitted_c.lines() {
        let trimmed = line.trim_start();
        for token in extract_mangled_calls(trimmed) {
            if trimmed.contains(&format!("{token}(")) && trimmed.ends_with('{') {
                continue;
            }
            if covered.iter().any(|s| s.symbol == token) {
                continue;
            }
            if file_defines_symbol(emitted_c, &token) {
                continue;
            }
            return Some(token);
        }
    }
    None
}

/// Whether `emitted_c` contains a *definition* (body) for mangled `symbol`.
fn file_defines_symbol(emitted_c: &str, symbol: &str) -> bool {
    emitted_c.lines().any(|line| {
        let l = line.trim_start();
        l.contains(&format!("{symbol}(")) && l.trim_end().ends_with('{')
    })
}

/// Find the first `l_String_*` symbol the emitted C DEFINES (same brace-line
/// heuristic as [`file_defines_symbol`]). The `l_String_` prefix cannot false-
/// positive on compound names (`Stringify.foo` mangles to `l_Stringify_foo`,
/// which the trailing underscore excludes); it does catch a String op's mangled
/// helpers (`l_String_take_go`, `l_String_take___boxed`), which lower from the
/// same `List Char` model and are equally wrong on the byte-string carrier.
/// L5CNF is let-normalized — calls are bound to temps, never opened on a
/// brace-line — so a brace-line match is a definition, not a call.
fn first_source_lowered_string_body(emitted_c: &str) -> Option<String> {
    for line in emitted_c.lines() {
        let trimmed = line.trim_start();
        if !trimmed.trim_end().ends_with('{') {
            continue;
        }
        if let Some(sym) = extract_mangled_calls(trimmed)
            .into_iter()
            .find(|token| token.starts_with("l_String_"))
        {
            return Some(sym);
        }
    }
    None
}

/// Extract mangled `l_*` identifiers immediately followed by `(` on a line.
fn extract_mangled_calls(line: &str) -> Vec<String> {
    let bytes = line.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i + 2 < bytes.len() {
        let at_boundary = i == 0 || !is_ident_byte(bytes[i - 1]);
        if at_boundary && bytes[i] == b'l' && bytes[i + 1] == b'_' {
            let start = i;
            let mut j = i;
            while j < bytes.len() && is_ident_byte(bytes[j]) {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'(' {
                out.push(line[start..j].to_string());
            }
            i = j.max(i + 1);
        } else {
            i += 1;
        }
    }
    out
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Whether `emitted_c` references mangled `symbol` either as a call (`symbol(`)
/// or as a first-class value (`(void*)symbol`). Matches on whole-token
/// boundaries to avoid prefix false positives.
fn c_references_symbol(emitted_c: &str, symbol: &str) -> bool {
    let bytes = emitted_c.as_bytes();
    let sym = symbol.as_bytes();
    let mut i = 0;
    while let Some(off) = emitted_c[i..].find(symbol) {
        let start = i + off;
        let end = start + sym.len();
        let left_boundary = start == 0 || !is_ident_byte(bytes[start - 1]);
        let after = bytes.get(end).copied();
        let right_token_end = !matches!(after, Some(b) if is_ident_byte(b));
        if left_boundary && right_token_end {
            return true;
        }
        i = end;
    }
    false
}

/// The materialized C source for one self-contained native build.
struct BuildSources {
    /// Combined translation unit: prelude shims + emitted closure + `main`.
    program: PathBuf,
    /// Clean C runtime implementation.
    runtime: PathBuf,
}

/// Render the combined translation unit for a nullary `Nat` entry.
fn render_program(emitted_c: &str, shims: &[&PreludeShim], mangled_entry: &str) -> String {
    let mut s = String::new();
    s.push_str(
        "/* Synthesized by clean native_build — prelude shims + emitted closure + main. */\n",
    );
    s.push_str("#include <stdio.h>\n");
    s.push_str("#include \"clean_runtime.h\"\n\n");
    for shim in shims {
        s.push_str(shim.definition);
        s.push('\n');
    }
    s.push_str("/* ---- emitted closure (clean compile --emit c) ---- */\n");
    s.push_str(emitted_c);
    if !emitted_c.ends_with('\n') {
        s.push('\n');
    }
    let nat = EntryContract {
        kind: EntryKind::Nat,
        args: EntryArgs::None,
        exit: EntryExit::AlwaysZero,
    };
    s.push_str(&render_entry_driver(nat, mangled_entry, "main"));
    s
}

/// Marshal the process `argv` into Lean's `List String`.
///
/// The layout is the emitter's own, read off its output for `[1, 2, 3]` rather
/// than assumed: `nil` is the tagged scalar `clean_box(0)` (NOT a heap ctor
/// cell), and `cons` is `clean_alloc_ctor(1, 2, 0, head, tail)` with field 0 the
/// head and field 1 the tail — which is exactly what the emitted
/// `List.length` reads back (`clean_ctor_get(xs, 1)` for the tail under
/// `case 1:`). Built back-to-front so the list comes out in argv order, and
/// every cell is freshly allocated with refcount 1, matching the all-owned ABI
/// the emitted entry consumes (`clean_inc(_x0)` … `clean_dec(_x0)`).
///
/// `argv[0]` — the program path — is excluded: Lean's `main (args : List
/// String)` receives the arguments only, which is why `#args` is `argc - 1`.
const ARGV_MARSHAL_HELPER: &str = "static clean_obj* clean_driver_argv_list(int argc, \
     char** argv) {\n  \
     clean_obj* xs = clean_box(0); /* List.nil */\n  \
     for (int i = argc - 1; i >= 1; i--) {\n    \
     clean_obj* head = clean_mk_string(argv[i]);\n    \
     xs = clean_alloc_ctor(1, 2, 0, head, xs); /* List.cons head tail */\n  \
     }\n  \
     return xs;\n}\n";

/// Render the combined translation unit for an `IO` entry, honouring Lean's
/// entry contract: `argv` marshalling when the entry takes `List String`, and
/// the returned `UInt32` propagated to the process exit status.
fn render_io_program(
    emitted_c: &str,
    shims: &[&PreludeShim],
    mangled_entry: &str,
    contract: EntryContract,
) -> String {
    let mut s = String::new();
    s.push_str(
        "/* Synthesized by clean native_build — IO prelude shims + emitted closure + IO main. */\n",
    );
    s.push_str("#include <stdio.h>\n");
    s.push_str("#include \"clean_runtime.h\"\n\n");
    for shim in shims {
        s.push_str(shim.definition);
        s.push('\n');
    }
    s.push_str("/* ---- emitted closure (clean compile --emit c) ---- */\n");
    s.push_str(emitted_c);
    if !emitted_c.ends_with('\n') {
        s.push('\n');
    }
    s.push_str(&render_entry_driver(contract, mangled_entry, "main"));
    s
}

/// The synthesized entry driver: the C function that initializes the runtime,
/// calls the entry `entry_callee` per `contract`, and turns its result into
/// the process exit status. The C lane appends it to the emitted closure as
/// `main`; the experimental trust-cg lane (`native_trustcg`) compiles it on its
/// own and calls the trust-cg object's entry through an asm label, under
/// `driver_fn` when the entry's own link symbol is already `main`.
///
/// One renderer for both lanes, so the argv marshalling and the `IO UInt32`
/// exit contract cannot drift apart between them.
pub(crate) fn render_entry_driver(
    contract: EntryContract,
    entry_callee: &str,
    driver_fn: &str,
) -> String {
    let mut s = String::new();
    if contract.kind == EntryKind::Nat {
        s.push_str("\n/* ---- synthesized entry ---- */\n");
        s.push_str(&format!("int {driver_fn}(void) {{\n"));
        s.push_str("  clean_runtime_init();\n");
        s.push_str(&format!("  clean_obj* _r = {entry_callee}();\n"));
        s.push_str("  printf(\"%zu\\n\", clean_unbox(_r));\n");
        s.push_str("  clean_runtime_finalize();\n");
        s.push_str("  return 0;\n");
        s.push_str("}\n");
        return s;
    }
    s.push_str("\n/* ---- synthesized IO entry ---- */\n");
    match contract.args {
        EntryArgs::None => {
            s.push_str(&format!("int {driver_fn}(void) {{\n"));
            s.push_str("  clean_runtime_init();\n");
            s.push_str(&format!(
                "  clean_obj* _r = {entry_callee}(); /* drives every IO effect */\n"
            ));
        }
        EntryArgs::Argv => {
            s.push_str(ARGV_MARSHAL_HELPER);
            s.push('\n');
            s.push_str(&format!("int {driver_fn}(int argc, char** argv) {{\n"));
            s.push_str("  clean_runtime_init();\n");
            s.push_str("  clean_obj* _args = clean_driver_argv_list(argc, argv);\n");
            s.push_str(&format!(
                "  clean_obj* _r = {entry_callee}(_args); /* drives every IO effect */\n"
            ));
        }
    }
    s.push_str("  fflush(stdout);\n");
    s.push_str("  fflush(stderr);\n");
    match contract.exit {
        EntryExit::AlwaysZero => {
            s.push_str("  (void)_r; /* IO Unit: the final Unit is discarded */\n");
            s.push_str("  int _status = 0;\n");
        }
        EntryExit::FromUInt32 => {
            // Lean's entry contract for `def main : IO UInt32`. Under the eager
            // IO model `l_main()` returns the final value of the action, so the
            // returned object IS the status; read it through the tagged-or-heap
            // dispatch rather than assuming the tagged representation.
            s.push_str("  /* Lean entry contract: the returned UInt32 IS the exit status. */\n");
            s.push_str("  int _status = (int)clean_unbox_uint32(_r);\n");
        }
    }
    s.push_str("  clean_runtime_finalize();\n");
    s.push_str("  return _status;\n");
    s.push_str("}\n");
    s
}

/// Write the combined program, the runtime header, and the runtime source into
/// `dir`. The runtime ships with a crate-relative include; rewrite it to flat.
fn materialize_build(dir: &Path, program: &str) -> anyhow::Result<BuildSources> {
    let header = dir.join("clean_runtime.h");
    std::fs::write(&header, clean_runtime::runtime_header())
        .with_context(|| format!("failed to write {}", header.display()))?;

    let runtime_src = clean_runtime::runtime_source().replacen(
        "../include/clean_runtime.h",
        "clean_runtime.h",
        1,
    );
    let runtime = dir.join("clean_runtime.c");
    std::fs::write(&runtime, runtime_src)
        .with_context(|| format!("failed to write {}", runtime.display()))?;

    let program_path = dir.join("program.c");
    std::fs::write(&program_path, program)
        .with_context(|| format!("failed to write {}", program_path.display()))?;

    Ok(BuildSources {
        program: program_path,
        runtime,
    })
}

/// Compile + link the program and runtime into a native executable in `dir`.
fn compile_and_link(dir: &Path, build: &BuildSources) -> anyhow::Result<PathBuf> {
    let cc = find_c_compiler().ok_or_else(|| {
        anyhow!(
            "no C compiler found for native link. Set CLEAN_CC or CC, or install one of: \
             cc, gcc, clang."
        )
    })?;
    let binary = dir.join("program");
    let mut cmd = crate::native_c_toolchain::command(&cc)?;
    cmd.arg("-O2")
        .arg("-std=c11")
        .arg("-I")
        .arg(dir)
        .arg(&build.program)
        .arg(&build.runtime)
        .arg("-lm")
        .arg("-o")
        .arg(&binary);

    let pretty = format!(
        "{cc} -O2 -std=c11 -I {} {} {} -lm -o {}",
        dir.display(),
        build.program.display(),
        build.runtime.display(),
        binary.display()
    );

    let output = cmd
        .output()
        .with_context(|| format!("failed to launch C compiler: {pretty}"))?;
    if !output.status.success() {
        bail!(
            "C compile/link failed.\n  command: {pretty}\n  stderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    if !binary.exists() {
        return Err(anyhow!(
            "C compiler reported success but produced no binary at {}",
            binary.display()
        ));
    }
    Ok(binary)
}

/// Locate a C compiler: `$CLEAN_CC`, `$CC`, then `cc`/`gcc`/`clang` on PATH.
pub(crate) fn find_c_compiler() -> Option<String> {
    for var in ["CLEAN_CC", "CC"] {
        if let Ok(value) = std::env::var(var) {
            if !value.trim().is_empty() {
                return Some(value);
            }
        }
    }
    for compiler in ["cc", "gcc", "clang"] {
        if Command::new(compiler)
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
        {
            return Some(compiler.to_string());
        }
    }
    None
}

#[cfg(test)]
fn cc_available() -> bool {
    find_c_compiler().is_some()
}

/// Test-only link plumbing shared by the WS6.14 census LINK oracle
/// (`compile_battery_census_tests`) and the WS6.13 runtime-archive
/// tests (`native_runtime`): a driver that retains a symbol set by
/// address, and the parser for what the linker reports undefined.
#[cfg(test)]
pub(crate) mod link_probe {
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};

    /// Symbols the linker reports undefined (Mach-O leading `_` stripped).
    /// Same grammar as `trustcg_census.rs`'s step-3 parser: ld64's
    /// `"_sym", referenced from:` and GNU ld's ``undefined reference to `sym'``.
    pub(crate) fn linker_undefined(stderr: &str) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        for line in stderr.lines() {
            if let Some(q0) = line.find('"') {
                if let Some(q1) = line[q0 + 1..].find('"') {
                    let inner = &line[q0 + 1..q0 + 1 + q1];
                    if line.contains("referenced from") {
                        out.insert(inner.strip_prefix('_').unwrap_or(inner).to_owned());
                        continue;
                    }
                }
            }
            if let Some(idx) = line.find("undefined reference to") {
                let rest = &line[idx..];
                if let (Some(b0), Some(b1)) = (rest.find('`'), rest.find('\'')) {
                    if b0 < b1 {
                        out.insert(rest[b0 + 1..b1].to_owned());
                    }
                }
            }
        }
        out
    }

    /// A driver that retains `symbols` by address, so each must resolve at
    /// link time. Symbols are referenced through asm labels, so a
    /// Lean-shaped name (`isLt`) and a mangled one (`l_Nat_add`) are spelled
    /// the same way.
    pub(crate) fn retaining_driver(dir: &Path, symbols: &BTreeSet<String>) -> PathBuf {
        let prefix = if cfg!(target_vendor = "apple") {
            "_"
        } else {
            ""
        };
        let mut c = String::new();
        for (i, sym) in symbols.iter().enumerate() {
            c.push_str(&format!(
                "extern void ref_{i}(void) __asm__(\"{prefix}{sym}\");\n"
            ));
        }
        c.push_str("int main(void) {\n");
        for i in 0..symbols.len() {
            c.push_str(&format!(
                "  {{ void* volatile p = (void*)&ref_{i}; (void)p; }}\n"
            ));
        }
        c.push_str("  return 0;\n}\n");
        let path = dir.join("driver.c");
        std::fs::write(&path, c).expect("write driver");
        path
    }

    #[test]
    fn linker_undefined_reads_both_linker_grammars() {
        let ld64 = "Undefined symbols for architecture arm64:\n  \"_clean_inc\", referenced from:\n      _main in driver.o\nld: symbol(s) not found";
        assert_eq!(
            linker_undefined(ld64),
            ["clean_inc".to_owned()]
                .into_iter()
                .collect::<BTreeSet<_>>()
        );
        let gnu = "driver.o: in function `main':\ndriver.c:(.text+0x4): undefined reference to `clean_inc'\ncollect2: error: ld returned 1 exit status";
        assert_eq!(
            linker_undefined(gnu),
            ["clean_inc".to_owned()]
                .into_iter()
                .collect::<BTreeSet<_>>()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Name};

    fn write_temp_lean(source: &str) -> (tempfile::TempDir, PathBuf) {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("run_fixture.lean");
        std::fs::write(&file, source).expect("write fixture");
        (dir, file)
    }

    #[test]
    fn test_mangle_decl_dots_become_underscores() {
        assert_eq!(mangle_decl("answer"), "l_answer");
        assert_eq!(mangle_decl("Nat.add"), "l_Nat_add");
    }

    #[test]
    fn test_extract_mangled_calls_finds_call_site() {
        let calls = extract_mangled_calls("  clean_obj* _x2 = l_Nat_add(_x6, _x7);");
        assert!(calls.contains(&"l_Nat_add".to_string()), "{calls:?}");
    }

    #[test]
    fn test_select_prelude_shims_includes_only_referenced() {
        let c = "clean_obj* _x = l_Nat_add(a, b);";
        let shims = select_prelude_shims(c).expect("nat add is covered");
        assert_eq!(shims.len(), 1);
        assert_eq!(shims[0].symbol, "l_Nat_add");
    }

    #[test]
    fn test_select_prelude_shims_rejects_uncovered_extern() {
        // `l_HShiftLeft_hShiftLeft` is genuinely unwired (HDiv/HMod are now covered).
        let c = "clean_obj* _x = l_HShiftLeft_hShiftLeft(a, b, c);";
        let err = select_prelude_shims(c).expect_err("uncovered extern must be rejected");
        assert!(
            err.to_string().contains("l_HShiftLeft_hShiftLeft"),
            "error should name the uncovered extern: {err:#}"
        );
    }

    #[test]
    fn test_select_prelude_shims_covers_hadd_dispatch() {
        let c = "clean_obj* _x0 = clean_alloc_closure((void*)l_Nat_add, 2, 0);\n\
                 clean_obj* _x1 = l_HAdd_mk(clean_box(0), clean_box(0), clean_box(0), _x0);\n\
                 clean_obj* _x4 = l_HAdd_hAdd(clean_box(0), clean_box(0), clean_box(0), _x1, _x5, _x6);";
        let shims = select_prelude_shims(c).expect("hadd dispatch must be covered");
        let names: Vec<&str> = shims.iter().map(|s| s.symbol).collect();
        assert!(names.contains(&"l_Nat_add"), "{names:?}");
        assert!(names.contains(&"l_HAdd_mk"), "{names:?}");
        assert!(names.contains(&"l_HAdd_hAdd"), "{names:?}");
    }

    #[test]
    fn test_render_program_has_main_and_entry_call() {
        let emitted = "clean_obj* l_answer(void) { return clean_box(2); }\n";
        let program = render_program(emitted, &[], "l_answer");
        assert!(program.contains("int main(void)"), "{program}");
        assert!(program.contains("l_answer();"), "{program}");
        assert!(program.contains("clean_runtime_init();"), "{program}");
    }

    #[test]
    fn test_select_prelude_shims_covers_control_flow_externs() {
        let c = "clean_obj* _x0 = l_true();\n\
                 clean_obj* _x1 = l_false();\n\
                 clean_obj* _x2 = l_Nat_decEq(_x0, _x1);";
        let shims = select_prelude_shims(c).expect("control-flow externs must be covered");
        let names: Vec<&str> = shims.iter().map(|s| s.symbol).collect();
        assert!(names.contains(&"l_true"), "{names:?}");
        assert!(names.contains(&"l_false"), "{names:?}");
        assert!(names.contains(&"l_Nat_decEq"), "{names:?}");
    }

    #[test]
    fn test_uncovered_guard_accepts_local_bool_param_helper() {
        let c = "clean_obj* l_g(uint8_t _x0) {\n  return _x0;\n}\n\
                 clean_obj* l_rTrue(void) {\n  return l_g(1);\n}";
        let shims = select_prelude_shims(c).expect("local bool-param helper must be accepted");
        assert!(shims.is_empty(), "no prelude shims expected, got {shims:?}");
    }

    #[test]
    fn test_classify_entry_io_vs_nat() {
        let nat = "clean_obj* l_answer(void) { return clean_box(2); }\n";
        assert_eq!(classify_entry(nat), EntryKind::Nat);

        let io =
            "clean_obj* l_main(void) {\n  clean_obj* _x1 = l_IO_println(_x0);\n  return _x1;\n}";
        assert_eq!(classify_entry(io), EntryKind::Io);

        let io_bind = "clean_obj* _x4 = l_Bind_bind(_x0, _x1, x, y, _x2, _x3);";
        assert_eq!(classify_entry(io_bind), EntryKind::Io);
    }

    #[test]
    fn test_select_io_shims_includes_only_referenced() {
        let c = "clean_obj* _x1 = l_IO_println(_x0);";
        let shims = select_shims_from(c, IO_PRELUDE_SHIMS).expect("io println is covered");
        assert!(
            shims.iter().any(|s| s.symbol == "l_IO_println"),
            "{shims:?}"
        );
    }

    /// Genuine `Init`'s `IO.println {α} [ToString α] (s : α)` is called with
    /// three C arguments; the bootstrap `String → IO Unit` shim has one, and
    /// injecting it made the program fail to compile (lake_path_stripped).
    #[test]
    fn test_genuine_init_println_selects_instance_shim() {
        let c = "clean_obj* l_main(void) {\n  \
                 clean_obj* _x0 = l_instToStringString();\n  \
                 clean_obj* _x2 = l_IO_println(clean_box(0), _x0, _x1);\n  \
                 return _x2;\n}\n\
                 clean_obj* l_instToStringString(void) {\n  \
                 return clean_alloc_closure((void*)l_id_lambda, 1, 0);\n}";
        let shims = select_shims_from(c, IO_PRELUDE_SHIMS).expect("genuine println is covered");
        let println = shims
            .iter()
            .find(|s| s.symbol == "l_IO_println")
            .expect("println shim selected");
        assert!(
            println
                .definition
                .contains("l_IO_println(clean_obj* ty, clean_obj* inst, clean_obj* x)")
                && println.definition.contains("clean_apply_1(inst, x)"),
            "{}",
            println.definition
        );
        for genuine in GENUINE_INIT_IO_PRELUDE_SHIMS {
            let guard = genuine
                .definition
                .find("if (clean_is_scalar(inst) || inst->header.kind != CLEAN_OBJ_KIND_CLOSURE)")
                .unwrap_or_else(|| panic!("{} lacks the closure check", genuine.symbol));
            let apply = genuine
                .definition
                .find("clean_apply_1(inst, x)")
                .expect("genuine shim applies the instance");
            assert!(
                guard < apply && genuine.definition[guard..apply].contains("clean_panic("),
                "{} must panic on a non-closure instance before applying it",
                genuine.symbol
            );
        }

        let bootstrap = "clean_obj* _x1 = l_IO_println(_x0);";
        let shims = select_shims_from(bootstrap, IO_PRELUDE_SHIMS).expect("bootstrap println");
        assert!(
            shims
                .iter()
                .any(|s| s.definition.contains("l_IO_println(clean_obj* s)")),
            "{shims:?}"
        );
    }

    #[test]
    fn test_println_at_both_arities_is_refused() {
        let c = "clean_obj* _x1 = l_IO_println(_x0);\n\
                 clean_obj* _x2 = l_IO_println(clean_box(0), _x3, _x4);";
        let err = select_shims_from(c, IO_PRELUDE_SHIMS).expect_err("mixed arities refuse");
        assert!(err.to_string().contains("arities"), "{err}");
    }

    #[test]
    fn test_symbol_use_arities_reads_calls_and_closures_not_definitions() {
        let c = "clean_obj* l_IO_print(clean_obj* s) {\n\
                 clean_obj* _x = l_IO_print(f(a, b), c);\n\
                 clean_obj* _y = clean_alloc_closure((void*)l_IO_print, 3, 0);\n\
                 clean_obj* _z = l_IO_println(_q);";
        assert_eq!(symbol_use_arities(c, "l_IO_print"), BTreeSet::from([2, 3]));
    }

    #[test]
    fn test_symbol_use_arities_ignores_c_literals_and_comments() {
        let c = r#"clean_obj* _text = clean_mk_string("l_IO_println(a,b,c)");
const char* _escaped = "quote: \" l_IO_println(a,b,c)";
const char* _continued = "continued \
l_IO_println(a,b,c)";
const char* _escaped_continued = "escaped backslash \\
" l_IO_println(a,b,c)";
// l_IO_println(a,b,c); clean_alloc_closure((void*)l_IO_println, 3, 0);
// continued comment \
l_IO_println(a,b,c);
/* multiline comment
l_IO_println(a,b,c);
clean_alloc_closure((void*)l_IO_println, 3, 0);
*/
clean_obj* _actual = l_IO_println(_text);
"#;
        assert_eq!(symbol_use_arities(c, "l_IO_println"), BTreeSet::from([1]));
        let shims = select_shims_from(c, IO_PRELUDE_SHIMS)
            .expect("literal/comment lookalikes do not manufacture mixed arities");
        assert!(
            shims
                .iter()
                .any(|shim| shim.definition.contains("l_IO_println(clean_obj* s)")),
            "{shims:?}"
        );
    }

    #[test]
    fn test_symbol_use_arities_retains_literal_arguments_as_opaque_operands() {
        let c = r#"clean_obj* _a = l_IO_println("é,a(b)");
clean_obj* _b = l_IO_println(',');
clean_obj* _c = l_IO_println('(');
clean_obj* _d = l_IO_println('\'');
"#;
        let masked = c_arity_scan_code(c);
        assert_eq!(masked.len(), c.len());
        assert_eq!(
            masked
                .match_indices('\n')
                .map(|(offset, _)| offset)
                .collect::<Vec<_>>(),
            c.match_indices('\n')
                .map(|(offset, _)| offset)
                .collect::<Vec<_>>()
        );
        assert_eq!(symbol_use_arities(c, "l_IO_println"), BTreeSet::from([1]));
        assert_eq!(
            symbol_use_arities(
                "clean_obj* _x = l_IO_println(clean_box(0), _inst, \"a,b(c)\");",
                "l_IO_println"
            ),
            BTreeSet::from([3])
        );
    }

    #[test]
    fn test_render_io_program_drives_entry_and_exits_zero() {
        let emitted = "clean_obj* l_main(void) { return clean_box(0); }\n";
        let program = render_io_program(
            emitted,
            &[],
            "l_main",
            EntryContract {
                kind: EntryKind::Io,
                args: EntryArgs::None,
                exit: EntryExit::AlwaysZero,
            },
        );
        assert!(program.contains("int main(void)"), "{program}");
        assert!(program.contains("l_main();"), "{program}");
        assert!(!program.contains("printf(\"%zu"), "{program}");
        assert!(program.contains("int _status = 0;"), "{program}");
        assert!(program.contains("return _status;"), "{program}");
    }

    /// The emitted C prototype — not a source-text scan — decides the arity the
    /// driver calls with.
    #[test]
    fn test_entry_arity_in_c_reads_the_emitted_prototype() {
        assert_eq!(
            entry_arity_in_c("clean_obj* l_main(void);\n", "l_main"),
            Some(0)
        );
        assert_eq!(
            entry_arity_in_c("clean_obj* l_main(clean_obj* _x0);\n", "l_main"),
            Some(1)
        );
        assert_eq!(
            entry_arity_in_c("clean_obj* l_f(clean_obj* _x0, clean_obj* _x1);\n", "l_f"),
            Some(2)
        );
        assert_eq!(
            entry_arity_in_c("clean_obj* l_other(void);\n", "l_main"),
            None
        );
        // Whole-identifier match only: a longer symbol must not answer.
        assert_eq!(
            entry_arity_in_c("clean_obj* l_x_l_main(void);\n", "l_main"),
            None
        );
    }

    /// Without the entry's Lean type the driver CANNOT know the exit shape, so
    /// it must stay on the safe `IO Unit` reading rather than guess. This pins
    /// why the type is threaded through the production callers at all.
    #[test]
    fn test_entry_contract_without_type_defaults_to_exit_zero() {
        let emitted = "clean_obj* l_main(void);\nclean_obj* _x = l_IO_println(_s);\n";
        let contract = entry_contract("main", emitted, None).expect("contract");
        assert_eq!(contract.kind, EntryKind::Io);
        assert_eq!(contract.args, EntryArgs::None);
        assert_eq!(contract.exit, EntryExit::AlwaysZero);
    }

    /// A unary entry the Lean type says is NOT `List String` must be refused,
    /// not marshalled: passing a `List String` where the body expects something
    /// else links cleanly and then reads the wrong representation.
    #[test]
    fn test_entry_contract_refuses_unary_entry_that_is_not_argv() {
        let emitted = "clean_obj* l_main(clean_obj* _x0);\nclean_obj* _x = l_IO_println(_s);\n";
        let nat_arg = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("IO"), vec![]),
                Expr::const_(Name::from_string("Unit"), vec![]),
            ),
        );
        let err = entry_contract("main", emitted, Some(&nat_arg))
            .expect_err("a non-`List String` argument must be refused");
        assert!(
            err.to_string().contains("List String"),
            "the refusal should name Lean's entry contract: {err:#}"
        );

        // Control: the same emitted C with the real `List String` domain is
        // accepted and marshals argv.
        let argv_arg = Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(Name::from_string("List"), vec![]),
                Expr::const_(Name::from_string("String"), vec![]),
            ),
            Expr::app(
                Expr::const_(Name::from_string("IO"), vec![]),
                Expr::const_(Name::from_string("UInt32"), vec![]),
            ),
        );
        let contract = entry_contract("main", emitted, Some(&argv_arg)).expect("argv contract");
        assert_eq!(contract.args, EntryArgs::Argv);
        assert_eq!(contract.exit, EntryExit::FromUInt32);
    }

    /// The argv driver's list layout must be the EMITTER's layout, read off its
    /// own output for `[1, 2, 3]`: `nil` is the tagged scalar `clean_box(0)`,
    /// `cons` is `clean_alloc_ctor(1, 2, 0, head, tail)`. A heap-cell nil (what
    /// the brick's original note assumed) would still switch correctly but is
    /// not what the emitter produces, and `argv[0]` must be excluded.
    #[test]
    fn test_render_io_program_argv_driver_uses_the_emitter_list_layout() {
        let emitted = "clean_obj* l_main(clean_obj* _x0) { return clean_box(0); }\n";
        let program = render_io_program(
            emitted,
            &[],
            "l_main",
            EntryContract {
                kind: EntryKind::Io,
                args: EntryArgs::Argv,
                exit: EntryExit::FromUInt32,
            },
        );
        assert!(
            program.contains("int main(int argc, char** argv)"),
            "{program}"
        );
        assert!(
            program.contains("clean_obj* xs = clean_box(0);"),
            "{program}"
        );
        assert!(
            program.contains("clean_alloc_ctor(1, 2, 0, head, xs)"),
            "{program}"
        );
        assert!(
            program.contains("i >= 1; i--"),
            "argv[0] must be skipped: {program}"
        );
        assert!(program.contains("l_main(_args);"), "{program}");
        assert!(
            program.contains("int _status = (int)clean_unbox_uint32(_r);"),
            "{program}"
        );
    }

    #[test]
    fn test_primitive_denylist_covers_all_shim_symbols() {
        for table in ALL_PRELUDE_SHIM_TABLES {
            for shim in table.iter() {
                assert!(
                    is_primitive_denylisted(shim.symbol),
                    "shimmed symbol {} must be denylisted (else it could double-define)",
                    shim.symbol
                );
            }
        }
        assert!(
            !is_primitive_denylisted("l_Nat_pred"),
            "Nat.pred has no shim and must be compilable from source"
        );
        assert!(
            is_primitive_denylisted("l_String_length"),
            "String.length is shimmed: its source body computes over the \
             List Char model, which miscompiles against the byte-string carrier"
        );
    }

    /// The String shim table mirrors the kernel's `String` native-reducer
    /// surface (`native_reducers.rs`) — the differential authority for these
    /// semantics. A symbol drifting out of this set silently re-opens the
    /// source-lowered path for that op.
    #[test]
    fn test_string_shim_table_matches_kernel_reducer_surface() {
        let symbols: Vec<&str> = STRING_PRELUDE_SHIMS.iter().map(|s| s.symbol).collect();
        assert_eq!(
            symbols,
            [
                "l_String_append",
                "l_String_length",
                "l_String_push",
                "l_String_decEq",
                "l_String_beq",
                "l_String_isEmpty",
                "l_String_utf8ByteSize",
            ],
            "STRING_PRELUDE_SHIMS must cover exactly the kernel String \
             native-reducer surface"
        );
    }

    #[test]
    fn test_select_string_shims_includes_only_referenced() {
        let c = "clean_obj* _x2 = l_String_append(_x0, _x1);";
        let shims = select_shims_from(c, STRING_PRELUDE_SHIMS).expect("string append is covered");
        assert_eq!(shims.len(), 1);
        assert_eq!(shims[0].symbol, "l_String_append");
    }

    /// A `String.*` body compiled from source (here: an unshimmed op) must be
    /// refused with an error naming the op — this is the silent-miscompile
    /// path (the body links, then reads the byte string as a ctor cell).
    #[test]
    fn test_source_lowered_string_body_is_refused() {
        let c = "clean_obj* l_String_take(clean_obj* _x0, clean_obj* _x1) {\n  \
                 return _x0;\n}\n\
                 clean_obj* l_entry(void) {\n  return clean_box(0);\n}";
        let err = select_prelude_shims(c).expect_err("source-lowered String body must be refused");
        assert!(
            err.to_string().contains("l_String_take"),
            "error should name the source-lowered String op: {err:#}"
        );
    }

    /// Even a SHIMMED symbol defined from source (root-decl edge: the #14
    /// denylist only guards the dependency closure, not the selected root) must
    /// refuse — the double-emit guard would otherwise drop the shim and let the
    /// List-Char-model body run against the byte-string carrier.
    #[test]
    fn test_shimmed_string_symbol_defined_from_source_is_refused() {
        let c = "clean_obj* l_String_length(clean_obj* _x0) {\n  return _x0;\n}";
        let err = select_prelude_shims(c).expect_err("source-defined String.length must refuse");
        assert!(
            err.to_string().contains("l_String_length"),
            "error should name the source-lowered String op: {err:#}"
        );
    }

    #[test]
    fn test_render_nat_program_covers_string_externs() {
        let emitted = "clean_obj* l_answer(void) {\n  \
                       clean_obj* _x0 = clean_mk_string(\"ab\");\n  \
                       clean_obj* _x1 = l_String_length(_x0);\n  \
                       return _x1;\n}\n";
        let program = render_native_translation_unit("answer", emitted, None)
            .expect("string extern is covered");
        assert!(
            program.contains("clean_obj* l_String_length(clean_obj* s)"),
            "rendered program should inject the String length shim: {program}"
        );
    }

    /// Full end-to-end: build a native binary to an explicit out_path and run it.
    /// Proves `build_native_executable` writes the binary to the requested path.
    #[test]
    fn test_build_native_executable_writes_to_out_path_and_runs() {
        if !cc_available() {
            eprintln!("skipping test_build_native_executable_writes_to_out_path_and_runs: no cc");
            return;
        }
        let (dir, file) = write_temp_lean("def main : IO Unit := IO.println \"hello out\"\n");
        let out_path = dir.path().join("bin").join("hello");
        build_native_executable(&file, "main", 0, &out_path).expect("build to out_path");
        assert!(
            out_path.exists(),
            "binary should exist at {}",
            out_path.display()
        );

        let output = Command::new(&out_path).output().expect("run binary");
        assert!(output.status.success(), "binary should exit 0: {output:?}");
        assert_eq!(String::from_utf8_lossy(&output.stdout), "hello out\n");
    }

    /// The Lake production path, end to end: `clean lake run` builds the target
    /// through THIS function and then execs the produced binary with the
    /// caller's arguments (`cmd_lake/run.rs`, `run_native_executable` ->
    /// `Command::new(path).args(args)`). So the argv marshalling and the
    /// `UInt32` exit status have to hold in the artifact this writes, not only
    /// in `clean run`'s scratch build.
    #[test]
    fn test_build_native_executable_argv_and_exit_status_end_to_end() {
        if !cc_available() {
            eprintln!(
                "skipping test_build_native_executable_argv_and_exit_status_end_to_end: no cc"
            );
            return;
        }
        let (dir, file) = write_temp_lean(
            "def main (args : List String) : IO UInt32 := do\n  \
             IO.println (toString args.length)\n  \
             pure (UInt32.ofNat args.length)\n",
        );
        let out_path = dir.path().join("bin").join("argv_exit");
        build_native_executable(&file, "main", 0, &out_path).expect("build argv/UInt32 entry");

        let three = Command::new(&out_path)
            .args(["a", "b", "c"])
            .output()
            .expect("run with 3 args");
        assert_eq!(
            String::from_utf8_lossy(&three.stdout),
            "3\n",
            "argv[1..] must marshal into the List String the entry counts"
        );
        assert_eq!(
            three.status.code(),
            Some(3),
            "the returned UInt32 must be the process exit status"
        );

        let none = Command::new(&out_path).output().expect("run with no args");
        assert_eq!(String::from_utf8_lossy(&none.stdout), "0\n");
        assert_eq!(
            none.status.code(),
            Some(0),
            "no arguments: nil marshals to length 0 and the status follows it"
        );
    }

    /// `build_native_executable` must handle compute-and-print (toString of a
    /// computed Nat) — the coverage the Lake path previously lacked.
    #[test]
    fn test_build_native_executable_compute_and_print() {
        if !cc_available() {
            eprintln!("skipping test_build_native_executable_compute_and_print: no cc");
            return;
        }
        let (dir, file) = write_temp_lean("def main : IO Unit := IO.println (toString (1 + 1))\n");
        let out_path = dir.path().join("bin").join("compute");
        build_native_executable(&file, "main", 0, &out_path).expect("build compute to out_path");
        let output = Command::new(&out_path)
            .output()
            .expect("run compute binary");
        assert!(output.status.success(), "{output:?}");
        assert_eq!(String::from_utf8_lossy(&output.stdout), "2\n");
    }

    /// String ops must route through the byte-string shims end-to-end: append
    /// two literals at runtime (opt 0 — no const-fold) and print the result.
    /// Before the shim table, `String.append`'s List-Char-model body was the
    /// silent-miscompile path.
    #[test]
    fn test_build_native_executable_string_append_prints() {
        if !cc_available() {
            eprintln!("skipping test_build_native_executable_string_append_prints: no cc");
            return;
        }
        let (dir, file) =
            write_temp_lean("def main : IO Unit := IO.println (String.append \"ab\" \"cd\")\n");
        let out_path = dir.path().join("bin").join("append");
        build_native_executable(&file, "main", 0, &out_path).expect("build string append");
        let output = Command::new(&out_path).output().expect("run append binary");
        assert!(output.status.success(), "{output:?}");
        assert_eq!(String::from_utf8_lossy(&output.stdout), "abcd\n");
    }

    /// `String.length` must be the shim's code-point count — a garbage value
    /// here is the exact signature of the source List-Char body reading the
    /// byte string as a ctor cell. ASCII input keeps the byte/code-point
    /// distinction out of scope for this fixture (the shim comment carries it).
    #[test]
    fn test_build_native_executable_string_length_prints() {
        if !cc_available() {
            eprintln!("skipping test_build_native_executable_string_length_prints: no cc");
            return;
        }
        let (dir, file) = write_temp_lean(
            "def main : IO Unit := IO.println (toString (String.length \"hello\"))\n",
        );
        let out_path = dir.path().join("bin").join("strlen");
        build_native_executable(&file, "main", 0, &out_path).expect("build string length");
        let output = Command::new(&out_path).output().expect("run length binary");
        assert!(output.status.success(), "{output:?}");
        assert_eq!(String::from_utf8_lossy(&output.stdout), "5\n");
    }

    /// `toString` is the PROJECTION of the single-method class `ToString`, so it
    /// must render through the instance the emitter hands it — not through a
    /// hardcoded `Nat` renderer.
    ///
    /// The pre-R3 shim discarded `inst` and decimal-rendered its argument, so
    /// every non-`Nat` instance printed a NUMBER: `toString "world"` printed `5`
    /// (the string carrier's `len` field, read as a tagged Nat) and
    /// `toString true` printed `1` — silently, with exit status 0. Neither was a
    /// missing capability: the emitter already lowers both instances correctly
    /// (`instToStringString`'s method is the identity, `instToStringBool`'s is a
    /// boxed switch onto `"true"`/`"false"`) and already passes them in. Only
    /// the shim ignored them.
    ///
    /// One program covers every case so a single link proves the dispatch, and
    /// the `Nat` line is the CONTROL: it must still render decimally, now via
    /// `l_instToStringNat`'s closure rather than the shim's open-coded copy.
    #[test]
    fn test_build_native_executable_tostring_dispatches_on_instance() {
        if !cc_available() {
            eprintln!(
                "skipping test_build_native_executable_tostring_dispatches_on_instance: no cc"
            );
            return;
        }
        let (dir, file) = write_temp_lean(
            "def main : IO Unit := do\n  \
             IO.println (toString \"world\")\n  \
             IO.println (toString true)\n  \
             IO.println (toString false)\n  \
             IO.println (toString (40 + 2))\n",
        );
        let out_path = dir.path().join("bin").join("tostring_dispatch");
        build_native_executable(&file, "main", 0, &out_path).expect("build toString dispatch");
        let output = Command::new(&out_path)
            .output()
            .expect("run toString binary");
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "world\ntrue\nfalse\n42\n",
            "each line must come from its OWN ToString instance; `5` and `1` for \
             the first two are the pre-R3 signature of the shim discarding \
             `inst` and rendering its argument as a Nat"
        );
    }

    /// A USER-DEFINED `ToString` instance must render through its own method —
    /// the proof that the projection dispatches on the instance rather than on
    /// a hardcoded set of prelude types.
    ///
    /// This is the case that shows the old shim reached user code, not just
    /// prelude types: `toString { n := 7 : Tag }` printed `7`, the structure's
    /// first field read as a tagged Nat, for an instance whose method ignores
    /// its argument and returns a constant string. A renderer that happened to
    /// special-case `String` and `Bool` would still fail this.
    #[test]
    fn test_build_native_executable_tostring_uses_user_defined_instance() {
        if !cc_available() {
            eprintln!(
                "skipping test_build_native_executable_tostring_uses_user_defined_instance: no cc"
            );
            return;
        }
        let (dir, file) = write_temp_lean(
            "structure Tag where\n  \
             n : Nat\n\n\
             instance : ToString Tag where\n  \
             toString _ := \"TAG\"\n\n\
             def main : IO Unit := IO.println (toString { n := 7 : Tag })\n",
        );
        let out_path = dir.path().join("bin").join("tostring_user");
        build_native_executable(&file, "main", 0, &out_path).expect("build user ToString instance");
        let output = Command::new(&out_path)
            .output()
            .expect("run user-instance binary");
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "TAG\n",
            "the user instance's method must run; `7` is the structure's `n` \
             field rendered as a Nat by a shim ignoring `inst`"
        );
    }

    /// `for x in xs do` with a `let mut` accumulator compiles, links and RUNS.
    ///
    /// Lean lowers `for` through `ForIn` and `let mut` through state-threading,
    /// and Clean's elaborator already produced exactly that term — `List.rec`
    /// over `ForInStep.rec` with the accumulator threaded as `ForIn`'s `β`.
    /// Every piece of it was already lowerable. The single blocker was that
    /// `to_lcnf::lower::expr_to_let_value` had no `Let` arm, so a `let` reached
    /// in VALUE position (the reassignment inside the step function; the whole
    /// `do` block once `Id.run` inlines into an argument) failed the whole
    /// declaration with `unsupported expression: Expression form: Let(..)`.
    ///
    /// Asserting the exact digits is the load-bearing half. Merely compiling
    /// and linking would not catch a mis-scoped accumulator, which is the way
    /// a let-flattening bug actually presents: the binding lands in the
    /// statement stream but names the wrong `FVarId`, and the program prints a
    /// wrong number with exit status 0. Each expected value is fixed by
    /// arithmetic, not by what the implementation happens to emit:
    ///
    /// - `sum3`    `1+2+3`                        = 6
    /// - `upto`    `1+2+3`, `break` at `x > 3`    = 6   (`ForInStep.done`)
    /// - `grid`    `(1+2+3)*(10+20)`              = 180 (nested loops)
    /// - `mutonly` `7+5`                          = 12  (`let mut`, no loop)
    ///
    /// `mutonly` is the control that separates the two constructs: it has no
    /// `for` at all and was refused by the same missing arm, so it fails
    /// independently of anything `ForIn`-shaped.
    #[test]
    fn test_build_native_executable_for_in_with_let_mut_runs() {
        if !cc_available() {
            eprintln!("skipping test_build_native_executable_for_in_with_let_mut_runs: no cc");
            return;
        }
        let (dir, file) = write_temp_lean(
            "def sum3 : Nat := Id.run do\n  \
               let mut acc := 0\n  \
               for x in [1, 2, 3] do\n    \
                 acc := acc + x\n  \
               return acc\n\n\
             def upto : Nat := Id.run do\n  \
               let mut acc := 0\n  \
               for x in [1, 2, 3, 4, 5] do\n    \
                 if x > 3 then\n      \
                   break\n    \
                 acc := acc + x\n  \
               return acc\n\n\
             def grid : Nat := Id.run do\n  \
               let mut acc := 0\n  \
               for x in [1, 2, 3] do\n    \
                 for y in [10, 20] do\n      \
                   acc := acc + x * y\n  \
               return acc\n\n\
             def mutonly : Nat := Id.run do\n  \
               let mut acc := 7\n  \
               acc := acc + 5\n  \
               return acc\n\n\
             def main : IO Unit := do\n  \
               IO.println (toString sum3)\n  \
               IO.println (toString upto)\n  \
               IO.println (toString grid)\n  \
               IO.println (toString mutonly)\n",
        );
        let out_path = dir.path().join("bin").join("for_in_let_mut");
        build_native_executable(&file, "main", 0, &out_path).expect("build for-in + let-mut");
        let output = Command::new(&out_path).output().expect("run for-in binary");
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "6\n6\n180\n12\n",
            "the loop must actually iterate and the mutable accumulator must \
             thread through it; a wrong number here is a mis-scoped flattened \
             `let`, not a missing capability"
        );
    }
}
