// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end LINK+RUN census of the Clean producer. With neither iteration
//! knob set, it selects the full computable prelude
//! (`Environment::with_prelude` + `init_io_ops`).
//!
//! For every computable root (a prelude constant whose `constant_to_decl`
//! yields a `Decl`) this harness runs the SAME pipeline `clean run` uses:
//!
//!   1. LOWER  — `constant_to_decl` + `compile_lcnf_decls` over the root's
//!      `#14` dependency closure (the clean-cli PRIMITIVE_DENYLIST discipline:
//!      per-dep probe, extern-drop on failure, runtime-primitive shims kept
//!      extern), then `emit_c`.
//!   2. LINK   — render `<28 native_build shims (only those referenced)>` +
//!      `<emitted closure>` + a `main`, then host `cc` against a
//!      once-precompiled `clean_runtime.o`. The LINKER is the authoritative
//!      oracle: any dangling extern (a dropped proof-machinery residue symbol,
//!      a missing comparison shim, an undefined `_boxed` trampoline) fails the
//!      link and is reported by exact symbol.
//!   3. RUN    — execute the produced binary. For the checkable oracle subset
//!      (arithmetic / comparison decidables) the root is CALLED with sample
//!      arguments and the result is asserted against a hand-computed value; a
//!      wrong value is `RUN_FAIL`, never `OK`. For roots outside that subset,
//!      the driver retains the root at link time but does not call it, so `OK`
//!      establishes emit/link/load viability, not functional correctness.
//!
//! FAIL-CLOSED within that scope: a root is `OK` only if it emits, links, and
//! its retained-root binary executes (exit 0) — and, where checkable, computes
//! the expected sample value. The 37 embedded shims mirror
//! `clean-cli/native_build.rs`; a static source audit must keep this copied table
//! synchronized.
//!
//! This is an explicit qualification utility (it forks `cc` ~800×), not a
//! default test. Missing compiler prerequisites fail, and any non-OK root makes
//! the process fail. Run:
//!   LINKRUN_OUT=/path/out.tsv cargo run -p clean-compiler --release \
//!     --features round-trip-compile --example linkrun_census
//!
//! Optional env: `LINKRUN_LIMIT=N` (first N computable roots, for iteration;
//! output is labeled `LIMITED — NOT FULL QUALIFICATION`);
//! `LINKRUN_NO_IO=1` (skip `init_io_ops`; also labeled non-full).

#![cfg(feature = "round-trip-compile")]

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::Write as _;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_compiler::emit_c::{emit_c_with_config, CEmitConfig};
use clean_compiler::mangle::mangle_name;
use clean_compiler::pass_manager::{compile_lcnf_decls, PipelineConfig};
use clean_compiler::to_lcnf::constant_to_decl;
use clean_compiler::Decl;
use clean_kernel::{ConstantKind, Environment, Expr, ExprVisitor, LevelVec, Name};

// ---------------------------------------------------------------------------
// Runtime primitives: the clean-cli PRIMITIVE_DENYLIST + verbatim shim mirror.
// ---------------------------------------------------------------------------

/// The 37 mangled symbols `native_build.rs` provides as runtime shims (the
/// `#14` dependency-closure boundary: never compiled from source even if their
/// bodies lower, so the shim always wins). This is the UNION of every
/// `*_PRELUDE_SHIMS` table's `symbol:` fields in `native_build.rs` at the
/// linkrun-integ integration (origin/main c46dd8734 + quot-shiftright,
/// cause23-cmp-tostring-shims, cause1, cause4, cause5): the base 28 plus the
/// quot eliminators (`l_Quot_lift`/`l_Quot_ind`), `l_Nat_shiftRight`, the
/// heap-aware Nat Bool comparators (`l_Nat_ble`/`l_Nat_blt`/`l_Nat_beq`) and
/// the Int decision procedures (`l_Int_decLt`/`l_Int_decLe`/`l_Int_decEq`).
const PRIMITIVE_DENYLIST: &[&str] = &[
    // NAT_PRELUDE_SHIMS
    "l_Nat_add",
    "l_Nat_mul",
    "l_Nat_sub",
    "l_Nat_div",
    "l_Nat_mod",
    "l_toString",
    "l_Nat_decEq",
    "l_Nat_shiftRight",
    "l_Nat_ble",
    "l_Nat_blt",
    "l_Nat_beq",
    // INT_PRELUDE_SHIMS
    "l_Int_decLt",
    "l_Int_decLe",
    "l_Int_decEq",
    // BOOL_PRELUDE_SHIMS
    "l_true",
    "l_false",
    // TYPECLASS_PRELUDE_SHIMS
    "l_HAdd_mk",
    "l_HAdd_hAdd",
    "l_HMul_mk",
    "l_HMul_hMul",
    "l_HSub_mk",
    "l_HSub_hSub",
    "l_HDiv_mk",
    "l_HDiv_hDiv",
    "l_HMod_mk",
    "l_HMod_hMod",
    "l_instToStringNat",
    // IO_PRELUDE_SHIMS
    "l_IO",
    "l_Unit_unit",
    "l_IO_println",
    "l_IO_print",
    "l_IO_eprintln",
    "l_Pure_pure",
    "l_Bind_bind",
    "l_IO_bind",
    // QUOT_PRELUDE_SHIMS
    "l_Quot_lift",
    "l_Quot_ind",
];

/// A prelude shim: mangled symbol + faithful C body. Verbatim mirror of the
/// `PreludeShim` table in `clean-cli/native_build.rs` (RUNG-B heap-aware `Nat`
/// helpers; R3 trivial-structure typeclass identities; eager-effect `IO`).
struct Shim {
    symbol: &'static str,
    def: &'static str,
}

const SHIMS: &[Shim] = &[
    // ---- NAT_PRELUDE_SHIMS ----
    Shim { symbol: "l_Nat_add", def: "clean_obj* l_Nat_add(clean_obj* a, clean_obj* b) { return clean_nat_add(a, b); }\n" },
    Shim { symbol: "l_Nat_mul", def: "clean_obj* l_Nat_mul(clean_obj* a, clean_obj* b) { return clean_nat_mul(a, b); }\n" },
    Shim { symbol: "l_Nat_sub", def: "clean_obj* l_Nat_sub(clean_obj* a, clean_obj* b) { return clean_nat_sub(a, b); }\n" },
    Shim { symbol: "l_Nat_div", def: "clean_obj* l_Nat_div(clean_obj* a, clean_obj* b) { return clean_nat_div(a, b); }\n" },
    Shim { symbol: "l_Nat_mod", def: "clean_obj* l_Nat_mod(clean_obj* a, clean_obj* b) { return clean_nat_mod(a, b); }\n" },
    Shim { symbol: "l_toString", def:
        "clean_obj* l_toString(clean_obj* ty, clean_obj* inst, clean_obj* x) {\n  \
         (void)ty; (void)inst;\n  \
         unsigned __int128 v = clean_nat_to_u128(x);\n  \
         clean_dec(x);\n  \
         char buf[48];\n  int i = (int)sizeof(buf);\n  buf[--i] = 0;\n  \
         if (v == 0) { buf[--i] = '0'; }\n  \
         else { while (v > 0) { buf[--i] = (char)('0' + (unsigned)(v % 10)); v /= 10; } }\n  \
         return clean_mk_string(buf + i);\n}\n" },
    Shim { symbol: "l_Nat_decEq", def: "clean_obj* l_Nat_decEq(clean_obj* a, clean_obj* b) { return clean_nat_dec_eq(a, b); }\n" },
    Shim { symbol: "l_Nat_shiftRight", def: "clean_obj* l_Nat_shiftRight(clean_obj* a, clean_obj* b) { return clean_nat_shift_right(a, b); }\n" },
    Shim { symbol: "l_Nat_ble", def: "clean_obj* l_Nat_ble(clean_obj* a, clean_obj* b) { return clean_nat_ble(a, b); }\n" },
    Shim { symbol: "l_Nat_blt", def: "clean_obj* l_Nat_blt(clean_obj* a, clean_obj* b) { return clean_nat_blt(a, b); }\n" },
    Shim { symbol: "l_Nat_beq", def: "clean_obj* l_Nat_beq(clean_obj* a, clean_obj* b) { return clean_nat_beq(a, b); }\n" },
    // ---- INT_PRELUDE_SHIMS ----
    Shim { symbol: "l_Int_decLt", def: "clean_obj* l_Int_decLt(clean_obj* a, clean_obj* b) { return clean_int_dec_lt(a, b); }\n" },
    Shim { symbol: "l_Int_decLe", def: "clean_obj* l_Int_decLe(clean_obj* a, clean_obj* b) { return clean_int_dec_le(a, b); }\n" },
    Shim { symbol: "l_Int_decEq", def: "clean_obj* l_Int_decEq(clean_obj* a, clean_obj* b) { return clean_int_dec_eq(a, b); }\n" },
    // ---- BOOL_PRELUDE_SHIMS ----
    Shim { symbol: "l_true", def: "clean_obj* l_true(void) { return clean_box(1); }\n" },
    Shim { symbol: "l_false", def: "clean_obj* l_false(void) { return clean_box(0); }\n" },
    // ---- TYPECLASS_PRELUDE_SHIMS ----
    Shim { symbol: "l_HAdd_mk", def: "clean_obj* l_HAdd_mk(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* addFn) { (void)a;(void)b;(void)g; return addFn; }\n" },
    Shim { symbol: "l_HAdd_hAdd", def: "clean_obj* l_HAdd_hAdd(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* inst, clean_obj* x, clean_obj* y) { (void)a;(void)b;(void)g; return clean_apply_2(inst, x, y); }\n" },
    Shim { symbol: "l_HMul_mk", def: "clean_obj* l_HMul_mk(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* mulFn) { (void)a;(void)b;(void)g; return mulFn; }\n" },
    Shim { symbol: "l_HMul_hMul", def: "clean_obj* l_HMul_hMul(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* inst, clean_obj* x, clean_obj* y) { (void)a;(void)b;(void)g; return clean_apply_2(inst, x, y); }\n" },
    Shim { symbol: "l_HSub_mk", def: "clean_obj* l_HSub_mk(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* subFn) { (void)a;(void)b;(void)g; return subFn; }\n" },
    Shim { symbol: "l_HSub_hSub", def: "clean_obj* l_HSub_hSub(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* inst, clean_obj* x, clean_obj* y) { (void)a;(void)b;(void)g; return clean_apply_2(inst, x, y); }\n" },
    Shim { symbol: "l_HDiv_mk", def: "clean_obj* l_HDiv_mk(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* divFn) { (void)a;(void)b;(void)g; return divFn; }\n" },
    Shim { symbol: "l_HDiv_hDiv", def: "clean_obj* l_HDiv_hDiv(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* inst, clean_obj* x, clean_obj* y) { (void)a;(void)b;(void)g; return clean_apply_2(inst, x, y); }\n" },
    Shim { symbol: "l_HMod_mk", def: "clean_obj* l_HMod_mk(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* modFn) { (void)a;(void)b;(void)g; return modFn; }\n" },
    Shim { symbol: "l_HMod_hMod", def: "clean_obj* l_HMod_hMod(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* inst, clean_obj* x, clean_obj* y) { (void)a;(void)b;(void)g; return clean_apply_2(inst, x, y); }\n" },
    Shim { symbol: "l_instToStringNat", def:
        "static clean_obj* clean_shim_nat_repr(clean_obj* n) {\n  \
         unsigned __int128 v = clean_nat_to_u128(n);\n  clean_dec(n);\n  \
         char buf[48];\n  int i = (int)sizeof(buf);\n  buf[--i] = 0;\n  \
         if (v == 0) { buf[--i] = '0'; }\n  \
         else { while (v > 0) { buf[--i] = (char)('0' + (unsigned)(v % 10)); v /= 10; } }\n  \
         return clean_mk_string(buf + i);\n}\n\
         clean_obj* l_instToStringNat(void) {\n  \
         return clean_alloc_closure((void*)clean_shim_nat_repr, 1, 0);\n}\n" },
    // ---- IO_PRELUDE_SHIMS ----
    Shim { symbol: "l_IO", def: "clean_obj* l_IO(void) { return clean_box(0); }\n" },
    Shim { symbol: "l_Unit_unit", def: "clean_obj* l_Unit_unit(void) { return clean_box(0); }\n" },
    Shim { symbol: "l_IO_println", def: "clean_obj* l_IO_println(clean_obj* s) { fputs(clean_string_data(s), stdout); fputc('\\n', stdout); return clean_box(0); }\n" },
    Shim { symbol: "l_IO_print", def: "clean_obj* l_IO_print(clean_obj* s) { fputs(clean_string_data(s), stdout); return clean_box(0); }\n" },
    Shim { symbol: "l_IO_eprintln", def: "clean_obj* l_IO_eprintln(clean_obj* s) { fputs(clean_string_data(s), stderr); fputc('\\n', stderr); return clean_box(0); }\n" },
    Shim { symbol: "l_Pure_pure", def: "clean_obj* l_Pure_pure(clean_obj* m, clean_obj* ty, clean_obj* v) { (void)m;(void)ty; return v; }\n" },
    Shim { symbol: "l_Bind_bind", def: "clean_obj* l_Bind_bind(clean_obj* m, clean_obj* ta, clean_obj* tb, clean_obj* a, clean_obj* k) { (void)m;(void)ta;(void)tb; return clean_apply_1(k, a); }\n" },
    Shim { symbol: "l_IO_bind", def: "clean_obj* l_IO_bind(clean_obj* io_type, clean_obj* unit_type, clean_obj* action, clean_obj* cont) { (void)io_type;(void)unit_type; return clean_apply_1(cont, action); }\n" },
    // ---- QUOT_PRELUDE_SHIMS ----
    Shim { symbol: "l_Quot_lift", def: "clean_obj* l_Quot_lift(clean_obj* a, clean_obj* r, clean_obj* b, clean_obj* f, clean_obj* h, clean_obj* q) { (void)a;(void)r;(void)b; clean_dec(h); return clean_quot_lift(f, q); }\n" },
    Shim { symbol: "l_Quot_ind", def: "clean_obj* l_Quot_ind(clean_obj* a, clean_obj* r, clean_obj* m, clean_obj* f, clean_obj* q) { (void)a;(void)r;(void)m; return clean_quot_ind(f, q); }\n" },
];

// ---------------------------------------------------------------------------
// cc plumbing (mirrors bounded_rungs_e2e.rs).
// ---------------------------------------------------------------------------

fn runtime_include_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/include")
}
fn runtime_c_source() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/src/clean_runtime.c")
}
fn find_c_compiler() -> Option<String> {
    for compiler in ["cc", "gcc", "clang"] {
        if Command::new(compiler)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return Some(compiler.to_string());
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Dependency-closure BFS (the clean-cli #14 discipline).
// ---------------------------------------------------------------------------

struct DepCollector {
    deps: Vec<Name>,
}
impl ExprVisitor for DepCollector {
    type Result = ();
    fn combine(&self, _a: (), _b: ()) {}
    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        self.deps.push(name.clone());
    }
}
fn collect_deps(value: &Expr) -> Vec<Name> {
    let mut c = DepCollector { deps: Vec::new() };
    c.visit_expr(value);
    c.deps
}

/// Per-dep probe with a persistent cache (each dep is lowered once across all
/// roots). Denylisted primitives return `None` (kept extern → shim wins).
fn probe(env: &Environment, name: &Name, cache: &mut HashMap<Name, Option<Decl>>) -> Option<Decl> {
    if let Some(v) = cache.get(name) {
        return v.clone();
    }
    let v = (|| {
        if PRIMITIVE_DENYLIST.contains(&mangle_name(name).as_str()) {
            return None;
        }
        let info = env.get_const(name)?;
        let decl = catch_unwind(AssertUnwindSafe(|| constant_to_decl(env, info)))
            .ok()?
            .ok()??;
        let ok = catch_unwind(AssertUnwindSafe(|| {
            compile_lcnf_decls(std::slice::from_ref(&decl), env, &PipelineConfig::default()).is_ok()
        }));
        matches!(ok, Ok(true)).then_some(decl)
    })();
    cache.insert(name.clone(), v.clone());
    v
}

/// The compilable dependency closure of `root` (root already probed OK).
fn build_closure(
    env: &Environment,
    root: &Name,
    root_decl: Decl,
    cache: &mut HashMap<Name, Option<Decl>>,
) -> Vec<Decl> {
    let mut seen: HashSet<Name> = HashSet::new();
    seen.insert(root.clone());
    let mut decls: Vec<Decl> = vec![root_decl];
    let mut worklist: Vec<Name> = env
        .get_const(root)
        .and_then(|i| i.value.as_ref())
        .map(collect_deps)
        .unwrap_or_default();
    while let Some(dep) = worklist.pop() {
        if !seen.insert(dep.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&dep) else {
            continue;
        };
        let Some(decl) = probe(env, &dep, cache) else {
            continue;
        };
        if let Some(value) = &info.value {
            worklist.extend(collect_deps(value));
        }
        decls.push(decl);
    }
    decls
}

// ---------------------------------------------------------------------------
// Extern scanning (mirrors native_build's select/first_uncovered logic).
// ---------------------------------------------------------------------------

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// All mangled `l_*` identifiers immediately followed by `(` on a line.
fn mangled_calls(line: &str) -> Vec<String> {
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

/// Whether emitted C DEFINES `symbol` (a body line: `... symbol(...) ... {`).
fn defines_symbol(emitted: &str, symbol: &str) -> bool {
    emitted.lines().any(|line| {
        let l = line.trim_start();
        l.contains(&format!("{symbol}(")) && l.trim_end().ends_with('{')
    })
}

/// `l_*` symbols the emitted C CALLS but neither defines nor is covered by a
/// shim — the dangling externs that will fail the link. Deterministic mirror of
/// the linker verdict (the linker is still the authoritative oracle below).
fn dangling_externs(emitted: &str) -> Vec<String> {
    let defined: HashSet<String> = emitted
        .lines()
        .filter(|l| l.trim_end().ends_with('{'))
        .flat_map(|l| mangled_calls(l.trim_start()))
        .collect();
    let mut out: Vec<String> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    for line in emitted.lines() {
        let t = line.trim_start();
        // A definition header line (`sym(...) {`) is not a call site.
        let is_def_header = t.trim_end().ends_with('{');
        for tok in mangled_calls(t) {
            if is_def_header && defined.contains(&tok) {
                continue;
            }
            if defined.contains(&tok) || PRIMITIVE_DENYLIST.contains(&tok.as_str()) {
                continue;
            }
            if seen.insert(tok.clone()) {
                out.push(tok);
            }
        }
    }
    out.sort();
    out
}

/// Whether `emitted` references mangled `symbol` either as a call (`symbol(`)
/// or as a first-class value (`(void*)symbol`), matched on whole-token
/// boundaries. Verbatim port of `native_build::c_references_symbol` — so the
/// shim-injection set is byte-identical to what `clean run` would select.
fn c_references_symbol(emitted: &str, symbol: &str) -> bool {
    let bytes = emitted.as_bytes();
    let mut i = 0;
    while let Some(off) = emitted[i..].find(symbol) {
        let start = i + off;
        let end = start + symbol.len();
        let left_boundary = start == 0 || !is_ident_byte(bytes[start - 1]);
        let right_token_end = !matches!(bytes.get(end).copied(), Some(b) if is_ident_byte(b));
        if left_boundary && right_token_end {
            return true;
        }
        i = end;
    }
    false
}

/// The shim definitions referenced by `emitted` and not already defined there
/// (the native_build select-and-not-double-emit rule).
fn selected_shims(emitted: &str) -> String {
    let mut s = String::new();
    for shim in SHIMS {
        if c_references_symbol(emitted, shim.symbol) && !defines_symbol(emitted, shim.symbol) {
            s.push_str(shim.def);
        }
    }
    s
}

// ---------------------------------------------------------------------------
// Value oracles: checkable roots called with sample args + hand-computed result.
// Each entry: root -> (C main body printing "R", expected stdout).
// The bodies only touch roots proven to compile from source elsewhere
// (r2_behavior_e2e / bounded_rungs_e2e), so a wrong value is a real defect.
// ---------------------------------------------------------------------------

fn oracle(root: &str) -> Option<(&'static str, &'static str)> {
    match root {
        "Nat.pow" => Some((
            "int main(void){ printf(\"%zu %zu %zu\\n\", clean_unbox(l_Nat_pow(clean_box(2),clean_box(10))), clean_unbox(l_Nat_pow(clean_box(5),clean_box(3))), clean_unbox(l_Nat_pow(clean_box(7),clean_box(0)))); return 0; }",
            "1024 125 1",
        )),
        "Nat.decLe" => Some((
            "int main(void){ printf(\"%u %u %u\\n\", l_Nat_decLe(clean_box(2),clean_box(5)), l_Nat_decLe(clean_box(5),clean_box(2)), l_Nat_decLe(clean_box(3),clean_box(3))); return 0; }",
            "1 0 1",
        )),
        "Nat.decLt" => Some((
            "int main(void){ printf(\"%u %u %u\\n\", l_Nat_decLt(clean_box(2),clean_box(5)), l_Nat_decLt(clean_box(5),clean_box(2)), l_Nat_decLt(clean_box(3),clean_box(3))); return 0; }",
            "1 0 0",
        )),
        _ => None,
    }
}

/// Shim symbol -> its C definition (from the `SHIMS` table).
fn shim_def_for(symbol: &str) -> Option<&'static str> {
    SHIMS.iter().find(|s| s.symbol == symbol).map(|s| s.def)
}

/// Value-oracles for DENYLISTED (shim-backed) roots. A denylisted root is
/// runnable-by-construction (its symbol comes from a runtime shim), which only
/// establishes LINKABILITY. These oracles additionally CALL the shim with
/// sample cells and assert the COMPUTED value, so a wrong shim result is a
/// `RUN_FAIL`, not a silent `OK_SHIM`. Returns the shim symbol whose C body to
/// embed, the driver (helpers + `main`), and expected stdout.
///
/// `Int` is a two-ctor cell — tag 0 `ofNat n` (= +n), tag 1 `negSucc n`
/// (= -(n+1)), Nat magnitude in field 0 (`clean_int_cmp` in `clean_runtime.c`).
/// `Int.decLt/decLe/decEq` consume both args and return a tagged 0/1
/// `Decidable` scrutinee (`clean_unbox` -> 0/1). `Nat.shiftRight` returns a
/// (heap-aware) `Nat` read via `clean_nat_to_u128`; `toString` on a heap `Nat`
/// (>= 2^63, built via `clean_nat_of_u64`) formats its decimal string.
fn shim_oracle(root: &str) -> Option<(&'static str, &'static str, &'static str)> {
    match root {
        // decLt 3 5 = true, decLt (-2) 1 = true, decLt 5 (-2) = false.
        "Int.decLt" => Some((
            "l_Int_decLt",
            "static clean_obj* int_ofNat(size_t n){ return clean_alloc_ctor(0,1,0,clean_box(n)); }\n\
             static clean_obj* int_negSucc(size_t n){ return clean_alloc_ctor(1,1,0,clean_box(n)); }\n\
             int main(void){ printf(\"%zu %zu %zu\\n\", \
               clean_unbox(l_Int_decLt(int_ofNat(3), int_ofNat(5))), \
               clean_unbox(l_Int_decLt(int_negSucc(1), int_ofNat(1))), \
               clean_unbox(l_Int_decLt(int_ofNat(5), int_negSucc(1)))); return 0; }",
            "1 1 0",
        )),
        // decLe 3 3 = true, decLe (-2) 1 = true, decLe 5 (-2) = false.
        "Int.decLe" => Some((
            "l_Int_decLe",
            "static clean_obj* int_ofNat(size_t n){ return clean_alloc_ctor(0,1,0,clean_box(n)); }\n\
             static clean_obj* int_negSucc(size_t n){ return clean_alloc_ctor(1,1,0,clean_box(n)); }\n\
             int main(void){ printf(\"%zu %zu %zu\\n\", \
               clean_unbox(l_Int_decLe(int_ofNat(3), int_ofNat(3))), \
               clean_unbox(l_Int_decLe(int_negSucc(1), int_ofNat(1))), \
               clean_unbox(l_Int_decLe(int_ofNat(5), int_negSucc(1)))); return 0; }",
            "1 1 0",
        )),
        // decEq (-2) (-2) = true, decEq 3 5 = false, decEq (-2) 3 = false.
        "Int.decEq" => Some((
            "l_Int_decEq",
            "static clean_obj* int_ofNat(size_t n){ return clean_alloc_ctor(0,1,0,clean_box(n)); }\n\
             static clean_obj* int_negSucc(size_t n){ return clean_alloc_ctor(1,1,0,clean_box(n)); }\n\
             int main(void){ printf(\"%zu %zu %zu\\n\", \
               clean_unbox(l_Int_decEq(int_negSucc(1), int_negSucc(1))), \
               clean_unbox(l_Int_decEq(int_ofNat(3), int_ofNat(5))), \
               clean_unbox(l_Int_decEq(int_negSucc(1), int_ofNat(3)))); return 0; }",
            "1 0 0",
        )),
        // 13 >>> 2 = 3, 1024 >>> 3 = 128, 5 >>> 10 = 0.
        "Nat.shiftRight" => Some((
            "l_Nat_shiftRight",
            "int main(void){ printf(\"%llu %llu %llu\\n\", \
               (unsigned long long)clean_nat_to_u128(l_Nat_shiftRight(clean_box(13), clean_box(2))), \
               (unsigned long long)clean_nat_to_u128(l_Nat_shiftRight(clean_box(1024), clean_box(3))), \
               (unsigned long long)clean_nat_to_u128(l_Nat_shiftRight(clean_box(5), clean_box(10)))); return 0; }",
            "3 128 0",
        )),
        // toString of a HEAP Nat (2^63 = 9223372036854775808, boxed by
        // clean_nat_of_u64 since it does not fit the tagged immediate < 2^63).
        "toString" => Some((
            "l_toString",
            "int main(void){ clean_obj* s = l_toString(clean_box(0), clean_box(0), clean_nat_of_u64(9223372036854775808ULL)); \
               fputs(clean_string_data(s), stdout); fputc('\\n', stdout); return 0; }",
            "9223372036854775808",
        )),
        _ => None,
    }
}

/// Build a driver embedding one shim definition + a value-checking `main`, link
/// it against the precompiled runtime, run it, and assert the printed value.
/// Upgrades a shim-backed root from `OK_SHIM` to `OK_CHECKED` (wrong value ->
/// `RUN_FAIL`).
fn check_shim_value(
    cc: &str,
    runtime_o: &Path,
    shim_symbol: &str,
    main_body: &str,
    expected: &str,
) -> Verdict {
    let Some(shim_def) = shim_def_for(shim_symbol) else {
        return fail("LINK_FAIL", format!("no shim def for `{shim_symbol}`"));
    };
    let program = format!(
        "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n\
         #include \"clean_runtime.h\"\n{shim_def}\n{main_body}\n"
    );
    let dir = tempfile::tempdir().expect("shim tempdir");
    let src = dir.path().join("driver.c");
    let bin = dir.path().join("driver");
    if std::fs::write(&src, &program).is_err() {
        return fail("LINK_FAIL", "could not write shim driver.c".into());
    }
    let compile = Command::new(cc)
        .arg("-O1")
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .arg(runtime_o)
        .arg("-I")
        .arg(runtime_include_dir())
        .output()
        .expect("spawn cc");
    if !compile.status.success() {
        let stderr = String::from_utf8_lossy(&compile.stderr);
        return fail(
            "LINK_FAIL",
            format!(
                "shim `{shim_symbol}` driver failed: {}",
                stderr.lines().last().unwrap_or("see stderr")
            ),
        );
    }
    let run = Command::new(&bin).output().expect("run shim driver");
    if !run.status.success() {
        return fail(
            "RUN_FAIL",
            format!(
                "shim `{shim_symbol}` exit={:?} (crash/nonzero)",
                run.status.code()
            ),
        );
    }
    let got = String::from_utf8_lossy(&run.stdout);
    let got = got.trim();
    if got != expected {
        return fail(
            "RUN_FAIL",
            format!("shim `{shim_symbol}` wrong value: got `{got}` want `{expected}`"),
        );
    }
    ok("OK_CHECKED")
}

// ---------------------------------------------------------------------------
// Verdicts.
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct Verdict {
    /// OK | OK_SHIM | OK_CHECKED | LOWER_FAIL | LINK_FAIL | RUN_FAIL | NO_ENTRY
    tag: &'static str,
    detail: String,
}

fn ok(t: &'static str) -> Verdict {
    Verdict {
        tag: t,
        detail: String::new(),
    }
}
fn fail(t: &'static str, d: String) -> Verdict {
    Verdict { tag: t, detail: d }
}

fn is_ok(tag: &str) -> bool {
    matches!(tag, "OK" | "OK_SHIM" | "OK_CHECKED")
}

fn optional_usize_env(name: &str) -> Option<usize> {
    match std::env::var(name) {
        Ok(value) => Some(
            value
                .parse()
                .unwrap_or_else(|_| panic!("{name} must be a non-negative integer")),
        ),
        Err(std::env::VarError::NotPresent) => None,
        Err(error) => panic!("{name} is not valid Unicode: {error}"),
    }
}

fn main() {
    let Some(cc) = find_c_compiler() else {
        panic!("linkrun_census requires a C compiler (cc/gcc/clang)");
    };
    let limit = optional_usize_env("LINKRUN_LIMIT");
    let no_io = match std::env::var("LINKRUN_NO_IO") {
        Ok(value) => {
            assert_eq!(value, "1", "LINKRUN_NO_IO, when set, must equal 1");
            true
        }
        Err(std::env::VarError::NotPresent) => false,
        Err(error) => panic!("LINKRUN_NO_IO is not valid Unicode: {error}"),
    };
    let out_path = std::env::var("LINKRUN_OUT").ok();

    let mut env = Environment::with_prelude();
    if !no_io {
        env.init_io_ops()
            .expect("initialize IO prelude for full census");
    }
    let pipeline = PipelineConfig::default();

    // Silence probe-style panic backtraces.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    // Shared scratch dir: precompile clean_runtime.c -> runtime.o ONCE.
    let scratch = tempfile::tempdir().expect("scratch tempdir");
    let runtime_o = scratch.path().join("clean_runtime.o");
    let rc = Command::new(&cc)
        .args(["-O1", "-c"])
        .arg(runtime_c_source())
        .arg("-I")
        .arg(runtime_include_dir())
        .arg("-o")
        .arg(&runtime_o)
        .output()
        .expect("spawn cc for runtime");
    assert!(
        rc.status.success(),
        "precompiling clean_runtime.o failed:\n{}",
        String::from_utf8_lossy(&rc.stderr)
    );

    // Enumerate + stably order the prelude.
    let mut names: Vec<Name> = env.constants().map(|c| c.name.clone()).collect();
    names.sort_by_key(|n| n.to_string());

    // Stage 0: per-decl lower verdict -> the computable population.
    // Population = `constant_to_decl` yields a Decl AND kind == Definition
    // (Lean's own "computable value" class). Theorems (proof-irrelevant),
    // opaque and axiom constants are proofs/abstract, not runnable data, and
    // are EXCLUDED from the denominator (counted separately).
    let mut computable: Vec<Name> = Vec::new();
    let mut n_none = 0usize; // constant_to_decl None (noncomputable / no value)
    let mut n_lowfail = 0usize; // err/panic in constant_to_decl
    let mut n_theorem = 0usize; // kind Theorem (proof), value lowered
    let mut n_opaque = 0usize; // kind Opaque
    let mut n_axiomkind = 0usize; // kind Axiom but carrying a value (rare)
    for name in &names {
        let info = env.get_const(name).expect("const exists");
        let v = catch_unwind(AssertUnwindSafe(|| constant_to_decl(&env, info)));
        match v {
            Ok(Ok(Some(_))) => match info.kind {
                ConstantKind::Definition => computable.push(name.clone()),
                ConstantKind::Theorem => n_theorem += 1,
                ConstantKind::Opaque => n_opaque += 1,
                ConstantKind::Axiom => n_axiomkind += 1,
            },
            Ok(Ok(None)) => n_none += 1,
            _ => n_lowfail += 1,
        }
    }
    let full_population = computable.len();
    if let Some(n) = limit {
        computable.truncate(n);
    }

    // Stage 1: per-root LINK+RUN.
    let mut cache: HashMap<Name, Option<Decl>> = HashMap::new();
    let mut verdicts: BTreeMap<String, Verdict> = BTreeMap::new();
    let total = computable.len();
    for (idx, root) in computable.iter().enumerate() {
        let root_s = root.to_string();
        let mangled = mangle_name(root);
        let v = classify_root(&cc, &runtime_o, &env, &pipeline, root, &mangled, &mut cache);
        if (idx + 1) % 50 == 0 || idx + 1 == total {
            eprintln!("  ... {}/{} ({})", idx + 1, total, root_s);
        }
        verdicts.insert(root_s, v);
    }

    std::panic::set_hook(prev_hook);

    // ---- Report ----
    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for v in verdicts.values() {
        *counts.entry(v.tag).or_default() += 1;
    }
    let n_ok = verdicts.values().filter(|v| is_ok(v.tag)).count();
    let scope = if limit.is_some() || no_io {
        "LIMITED — NOT FULL QUALIFICATION"
    } else {
        "FULL"
    };

    println!("\n==================== LINKRUN CENSUS ====================");
    println!("scope                       = {scope}");
    println!("requested limit             = {limit:?}");
    println!("IO prelude included         = {}", !no_io);
    println!("total_constants             = {}", names.len());
    println!("non_computable (lower none) = {n_none}");
    println!("lower_err_or_panic          = {n_lowfail}");
    println!("excluded proofs (Theorem)   = {n_theorem}");
    println!("excluded Opaque             = {n_opaque}");
    println!("excluded Axiom-with-value   = {n_axiomkind}");
    println!("COMPUTABLE defs (full population) = {full_population}");
    println!("COMPUTABLE defs (selected)   = {total}");
    println!("-------------------------------------------------------");
    println!("CENSUS OK                   = {n_ok} / {total}");
    for (tag, c) in &counts {
        println!("  {tag:<12} = {c}");
    }
    println!("=======================================================");
    println!("\n---- NON-OK ROOTS (bucketed) ----");
    for tag in ["LOWER_FAIL", "LINK_FAIL", "RUN_FAIL", "NO_ENTRY"] {
        let rows: Vec<(&String, &Verdict)> =
            verdicts.iter().filter(|(_, v)| v.tag == tag).collect();
        if rows.is_empty() {
            continue;
        }
        println!("\n### {tag} ({})", rows.len());
        for (name, v) in rows {
            println!("{name}\t{}", v.detail);
        }
    }

    if let Some(path) = out_path {
        let mut f = std::fs::File::create(&path).expect("open LINKRUN_OUT");
        writeln!(
            f,
            "# scope={scope:?} requested_limit={limit:?} io_prelude={} total_constants={} non_computable={} lower_err={} theorems={} opaque={} axiomkind={} full_population={} selected_defs={} ok={}",
            !no_io,
            names.len(),
            n_none,
            n_lowfail,
            n_theorem,
            n_opaque,
            n_axiomkind,
            full_population,
            total,
            n_ok
        ).unwrap();
        for (name, v) in &verdicts {
            writeln!(f, "{name}\t{}\t{}", v.tag, v.detail).unwrap();
        }
        eprintln!("wrote {path}");
    }

    // Every selected census must be non-vacuous and fail on any selected root.
    // The scope label above is FULL only when neither iteration knob is active.
    assert!(total > 0, "no computable roots enumerated");
    assert_eq!(
        n_ok,
        total,
        "selected link+run census failed for {} of {total} computable roots",
        total - n_ok
    );
}

/// Classify one computable root end-to-end.
fn classify_root(
    cc: &str,
    runtime_o: &Path,
    env: &Environment,
    pipeline: &PipelineConfig,
    root: &Name,
    mangled: &str,
    cache: &mut HashMap<Name, Option<Decl>>,
) -> Verdict {
    // Denylisted primitives are runtime-shim-backed: runnable by construction.
    // Where a value-oracle exists, CALL the shim with sample cells and assert
    // the computed value (OK_SHIM -> OK_CHECKED; a wrong value is RUN_FAIL) so
    // the shim's correctness is exercised in the instrument, not just its link.
    if PRIMITIVE_DENYLIST.contains(&mangled) {
        if let Some((sym, body, expected)) = shim_oracle(&root.to_string()) {
            return check_shim_value(cc, runtime_o, sym, body, expected);
        }
        return ok("OK_SHIM");
    }
    // Root must itself compile from source.
    let Some(root_decl) = probe(env, root, cache) else {
        return fail("LOWER_FAIL", "root does not compile from source".into());
    };
    let decls = build_closure(env, root, root_decl, cache);

    // emit_c the closure (through the full pipeline).
    let emitted = catch_unwind(AssertUnwindSafe(|| {
        let compiled = compile_lcnf_decls(&decls, env, pipeline).ok()?;
        emit_c_with_config(
            &compiled.boxed_ir_decls,
            CEmitConfig {
                check_ir: false,
                ..CEmitConfig::default()
            },
        )
        .ok()
    }));
    let emitted = match emitted {
        Ok(Some(s)) => s,
        Ok(None) => {
            return fail(
                "LOWER_FAIL",
                "compile_lcnf_decls/emit_c returned Err".into(),
            )
        }
        Err(_) => return fail("LOWER_FAIL", "panic in pipeline/emit_c".into()),
    };

    if !defines_symbol(&emitted, mangled) {
        return fail("NO_ENTRY", format!("emitted C defines no `{mangled}` body"));
    }

    // Predicted dangling externs (linker confirms below).
    let dangling = dangling_externs(&emitted);

    // Render translation unit: includes + selected shims + closure + main.
    let (main_body, expected): (String, Option<&'static str>) = match oracle(&root.to_string()) {
        Some((body, exp)) => (body.to_string(), Some(exp)),
        // Reference-only driver: the closure's `.o` retains every undefined
        // extern, so the LINK still exercises the full symbol graph; the binary
        // executes trivially.
        None => ("int main(void){ return 0; }".to_string(), None),
    };
    let program = format!(
        "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n\
         #include \"clean_runtime.h\"\n{shims}\n{emitted}\n{main_body}\n",
        shims = selected_shims(&emitted),
    );

    // Materialize + link against the precompiled runtime.o.
    let dir = tempfile::tempdir().expect("root tempdir");
    let src = dir.path().join("driver.c");
    let bin = dir.path().join("driver");
    if std::fs::write(&src, &program).is_err() {
        return fail("LINK_FAIL", "could not write driver.c".into());
    }
    let compile = Command::new(cc)
        .arg("-O1")
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .arg(runtime_o)
        .arg("-I")
        .arg(runtime_include_dir())
        .output()
        .expect("spawn cc");
    if !compile.status.success() {
        let stderr = String::from_utf8_lossy(&compile.stderr);
        let detail = if !dangling.is_empty() {
            format!("undefined: {}", dangling.join(","))
        } else {
            // Not a dangling-extern link error: surface a compact stderr tail.
            let tail: String = stderr
                .lines()
                .filter(|l| {
                    l.contains("error") || l.contains("Undefined") || l.contains("undefined")
                })
                .take(3)
                .collect::<Vec<_>>()
                .join(" | ");
            format!(
                "cc failed: {}",
                if tail.is_empty() {
                    "see stderr".into()
                } else {
                    tail
                }
            )
        };
        return fail("LINK_FAIL", detail);
    }

    // Run.
    let run = Command::new(&bin).output().expect("run driver");
    if !run.status.success() {
        return fail(
            "RUN_FAIL",
            format!("exit={:?} (crash/nonzero)", run.status.code()),
        );
    }
    if let Some(exp) = expected {
        let got = String::from_utf8_lossy(&run.stdout);
        let got = got.trim();
        if got != exp {
            return fail("RUN_FAIL", format!("wrong value: got `{got}` want `{exp}`"));
        }
        return ok("OK_CHECKED");
    }
    ok("OK")
}
