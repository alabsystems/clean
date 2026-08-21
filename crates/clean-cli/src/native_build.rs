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
//!    the exact `clean compile --emit c` pipeline ([`emit_entry_c`]).
//! 2. **classify** the entry shape ([`classify_entry`]) — `IO Unit` vs nullary
//!    `Nat` — which selects the synthesized driver and shim set.
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
//! every effect and returns the final `Unit`, which the synthesized `main`
//! discards before returning `0`.
//!
//! If the emitted C references a mangled `l_*` symbol outside the shim tables we
//! refuse with an explicit message rather than emit a binary that fails to link.
//! That keeps the surface honest: a `decl` either builds-and-runs, or reports
//! precisely which prelude extern it would need.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context};

use crate::cmd_compile::compile_to_string;
use clean_compiler::cli::{CompileArgs, EmitFormat};

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
    // `toString {a} [ToString a] (x : a) : String`. Supports printing a computed
    // `Nat`: the instance + type args are erased and the value (last arg, a
    // boxed Nat) is rendered as a decimal string. Heap-aware (RUNG B): reads the
    // value via `clean_nat_to_u128` so a Nat >= 2^63 renders exactly rather than
    // decoding the heap pointer as garbage, and consumes `x` per the all-owned
    // ABI. `u128` needs up to 39 digits, so the buffer is 48.
    PreludeShim {
        symbol: "l_toString",
        definition: "clean_obj* l_toString(clean_obj* ty, clean_obj* inst, clean_obj* x) {\n  \
            (void)ty; (void)inst;\n  \
            unsigned __int128 v = clean_nat_to_u128(x);\n  \
            clean_dec(x);\n  \
            char buf[48];\n  \
            int i = (int)sizeof(buf);\n  \
            buf[--i] = 0;\n  \
            if (v == 0) { buf[--i] = '0'; }\n  \
            else { while (v > 0) { buf[--i] = (char)('0' + (unsigned)(v % 10)); v /= 10; } }\n  \
            return clean_mk_string(buf + i);\n}\n",
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

/// All prelude shim tables, in one place. The union of these symbols is the
/// `PRIMITIVE_DENYLIST` the #14 dependency-closure boundary treats as never
/// compiled-from-source even if their bodies lower, so the shim always wins and
/// the two cannot conflict or double-define.
const ALL_PRELUDE_SHIM_TABLES: &[&[PreludeShim]] = &[
    NAT_PRELUDE_SHIMS,
    INT_PRELUDE_SHIMS,
    UINT32_PRELUDE_SHIMS,
    BOOL_PRELUDE_SHIMS,
    TYPECLASS_PRELUDE_SHIMS,
    IO_PRELUDE_SHIMS,
    QUOT_PRELUDE_SHIMS,
];

/// Whether `mangled` names a prelude symbol backed by a runtime shim, i.e. one
/// that must stay an extern (shimmed) rather than be compiled from source by the
/// #14 dependency-closure boundary in `cmd_compile`.
pub(crate) fn is_primitive_denylisted(mangled: &str) -> bool {
    ALL_PRELUDE_SHIM_TABLES
        .iter()
        .flat_map(|table| table.iter())
        .any(|shim| shim.symbol == mangled)
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
            fputs(clean_string_data(s), stdout);\n  \
            fputc('\\n', stdout);\n  \
            return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_IO_print",
        definition: "clean_obj* l_IO_print(clean_obj* s) {\n  \
            fputs(clean_string_data(s), stdout);\n  \
            return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_IO_eprintln",
        definition: "clean_obj* l_IO_eprintln(clean_obj* s) {\n  \
            fputs(clean_string_data(s), stderr);\n  \
            fputc('\\n', stderr);\n  \
            return clean_box(0);\n}\n",
    },
    PreludeShim {
        symbol: "l_Pure_pure",
        definition: "clean_obj* l_Pure_pure(clean_obj* m, clean_obj* ty, clean_obj* v) {\n  \
            (void)m; (void)ty;\n  \
            return v;\n}\n",
    },
    PreludeShim {
        symbol: "l_Bind_bind",
        definition: "clean_obj* l_Bind_bind(clean_obj* m, clean_obj* ta, clean_obj* tb, \
            clean_obj* a, clean_obj* k) {\n  \
            (void)m; (void)ta; (void)tb;\n  \
            return clean_apply_1(k, a);\n}\n",
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
pub(crate) enum EntryKind {
    /// A nullary `Nat`-returning entry: unbox and print the result.
    Nat,
    /// An `IO Unit` entry: drive the (eager) IO action and exit `0`.
    Io,
}

/// Decide whether the emitted entry is an `IO Unit` program or a nullary `Nat`
/// computation, by detecting the `IO`-monad prelude externs the L5 emitter only
/// lowers to for `IO` entries.
pub(crate) fn classify_entry(emitted_c: &str) -> EntryKind {
    let io_markers = [
        "l_IO_println(",
        "l_IO_print(",
        "l_IO_eprintln(",
        "l_IO_bind(",
        "l_Bind_bind(",
        "l_Pure_pure(",
        "l_IO(",
        "l_Unit_unit(",
    ];
    if io_markers.iter().any(|m| emitted_c.contains(m)) {
        EntryKind::Io
    } else {
        EntryKind::Nat
    }
}

/// Emit the C closure for `decl` (root + transitive compilable deps), reusing
/// the exact `clean compile --emit c` pipeline.
pub(crate) fn emit_entry_c(file: &Path, decl: &str, opt_level: u8) -> anyhow::Result<String> {
    compile_to_string(CompileArgs {
        file: Some(file.to_path_buf()),
        decl: Some(decl.to_owned()),
        emit: EmitFormat::C,
        opt_level,
        output: None,
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
pub(crate) fn build_native_executable_with_source_sink(
    file: &Path,
    decl: &str,
    opt_level: u8,
    out_path: &Path,
    source_sink: Option<&Path>,
) -> anyhow::Result<()> {
    let emitted_c = emit_entry_c(file, decl, opt_level)?;
    let program = render_native_translation_unit(decl, &emitted_c)?;

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
pub(crate) struct BuiltBinary {
    /// Path to the linked native executable inside the scratch dir.
    pub(crate) binary: PathBuf,
    /// Owns the scratch dir; dropped (and removed) when this struct is dropped,
    /// unless `--keep-temp` leaked it via [`keep_scratch`].
    _scratch: tempfile::TempDir,
}

/// Synthesize `main` + the prelude shims the emitted C references, materialize
/// against the embedded Clean runtime, and cc-link a native binary in a scratch
/// dir. Does NOT run it — the caller chooses to run-in-place (`clean run`) or
/// copy to a stable path (`clean lake run`).
pub(crate) fn build_native_binary_in_scratch(
    decl: &str,
    emitted_c: &str,
    nat_strict_guard: bool,
) -> anyhow::Result<BuiltBinary> {
    let mangled_entry = mangle_decl(decl);
    let kind = classify_entry(emitted_c);

    if nat_strict_guard
        && kind == EntryKind::Nat
        && !emitted_c.contains(&format!("{mangled_entry}(void)"))
    {
        bail!(
            "native build entry must be a nullary declaration: the emitted C does not \
             declare `{mangled_entry}(void)`. Use e.g. `def {decl} : Nat := Nat.succ 0` \
             or `def {decl} : IO Unit := IO.println \"hi\"`."
        );
    }

    let program = render_native_translation_unit(decl, emitted_c)?;
    link_program_in_scratch(&program)
}

/// Render the combined translation unit (includes + the prelude shims the
/// emitted C references + the emitted closure + the synthesized driver `main`)
/// for `decl`. Selects the shim set from the entry shape; fails closed if the
/// emitted C references an uncovered mangled extern.
pub(crate) fn render_native_translation_unit(
    decl: &str,
    emitted_c: &str,
) -> anyhow::Result<String> {
    let mangled_entry = mangle_decl(decl);
    let program = match classify_entry(emitted_c) {
        EntryKind::Nat => {
            let shims = select_shims_from_tables(
                emitted_c,
                &[
                    NAT_PRELUDE_SHIMS,
                    INT_PRELUDE_SHIMS,
                    BOOL_PRELUDE_SHIMS,
                    TYPECLASS_PRELUDE_SHIMS,
                    QUOT_PRELUDE_SHIMS,
                ],
            )?;
            render_program(emitted_c, &shims, &mangled_entry)
        }
        EntryKind::Io => {
            // An IO program can also compute — arithmetic, recursion, matchers,
            // `toString`, quotient eliminators — so draw from all shim tables,
            // not just the IO ones.
            let shims = select_shims_from_tables(
                emitted_c,
                &[
                    IO_PRELUDE_SHIMS,
                    NAT_PRELUDE_SHIMS,
                    INT_PRELUDE_SHIMS,
                    BOOL_PRELUDE_SHIMS,
                    TYPECLASS_PRELUDE_SHIMS,
                    QUOT_PRELUDE_SHIMS,
                ],
            )?;
            render_io_program(emitted_c, &shims, &mangled_entry)
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
pub(crate) fn keep_scratch(built: BuiltBinary) -> PathBuf {
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
pub(crate) fn select_shims_for_c_text(emitted_c: &str) -> anyhow::Result<String> {
    let shims = select_shims_from_tables(emitted_c, ALL_PRELUDE_SHIM_TABLES)?;
    Ok(shims
        .iter()
        .map(|s| s.definition)
        .collect::<Vec<_>>()
        .join("\n"))
}

/// Extract-lane helper: the mangled `l_*` symbol for a declaration.
pub(crate) fn mangle_decl_symbol(decl: &str) -> String {
    mangle_decl(decl)
}

/// Extract-lane helper: materialize the runtime + emitted C + a caller-
/// provided driver `main()` into `dir`, then cc-compile and link. Returns
/// the executable path.
pub(crate) fn build_extract_executable(
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

fn select_shims_from_tables(
    emitted_c: &str,
    tables: &[&'static [PreludeShim]],
) -> anyhow::Result<Vec<&'static PreludeShim>> {
    let needed: Vec<&PreludeShim> = tables
        .iter()
        .flat_map(|table| table.iter())
        .filter(|shim| c_references_symbol(emitted_c, shim.symbol))
        // Double-emit guard: if a prelude fn is now compiled from source into the
        // emitted C, do NOT also inject the shim, or the linker sees two
        // definitions of `l_X`.
        .filter(|shim| !file_defines_symbol(emitted_c, shim.symbol))
        .collect();

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
    s.push_str("\n/* ---- synthesized entry ---- */\n");
    s.push_str("int main(void) {\n");
    s.push_str("  clean_runtime_init();\n");
    s.push_str(&format!("  clean_obj* _r = {mangled_entry}();\n"));
    s.push_str("  printf(\"%zu\\n\", clean_unbox(_r));\n");
    s.push_str("  clean_runtime_finalize();\n");
    s.push_str("  return 0;\n");
    s.push_str("}\n");
    s
}

/// Render the combined translation unit for an `IO Unit` entry.
fn render_io_program(emitted_c: &str, shims: &[&PreludeShim], mangled_entry: &str) -> String {
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
    s.push_str("\n/* ---- synthesized IO entry ---- */\n");
    s.push_str("int main(void) {\n");
    s.push_str("  clean_runtime_init();\n");
    s.push_str(&format!(
        "  clean_obj* _r = {mangled_entry}(); /* drives every IO effect */\n"
    ));
    s.push_str("  (void)_r; /* the final Unit is discarded */\n");
    s.push_str("  fflush(stdout);\n");
    s.push_str("  fflush(stderr);\n");
    s.push_str("  clean_runtime_finalize();\n");
    s.push_str("  return 0;\n");
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
    let mut cmd = Command::new(&cc);
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
fn find_c_compiler() -> Option<String> {
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

#[cfg(test)]
mod tests {
    use super::*;

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

        let io_bind = "clean_obj* _x4 = l_Bind_bind(_x0, x, y, _x2, _x3);";
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

    #[test]
    fn test_render_io_program_drives_entry_and_exits_zero() {
        let emitted = "clean_obj* l_main(void) { return clean_box(0); }\n";
        let program = render_io_program(emitted, &[], "l_main");
        assert!(program.contains("int main(void)"), "{program}");
        assert!(program.contains("l_main();"), "{program}");
        assert!(!program.contains("printf(\"%zu"), "{program}");
        assert!(program.contains("return 0;"), "{program}");
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
            !is_primitive_denylisted("l_String_length"),
            "String.length has no shim and must be compilable from source"
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
}
