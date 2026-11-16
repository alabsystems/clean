// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TrustCG-path LINK+RUN census of the Clean producer. Without
//! `TRUSTCG_LIMIT`, it selects the full computable prelude. Unlike
//! `linkrun_census.rs` (which uses `emit_c`, a C-backend proxy), this harness
//! routes every root through the trust-ir -> trust-cg -> object path used by
//! `clean compile --emit obj`:
//!
//!   1. LOWER   — `constant_to_decl` + `compile_lcnf_decls` over the root's
//!      `#14` dependency closure (same probe/extern-drop discipline as
//!      linkrun_census.rs), then `compile_lcnf_to_trust_ir` (ExternCalls,
//!      host target — the `cmd_compile::compile_to_object` config)
//!      + `serialize_tmbc`. A refusal here (clean cannot emit the tMBC) is
//!      EMITIR_FAIL.
//!   2. CODEGEN — invoke the explicitly selected `trust-cg` CLI:
//!        trust-cg -c --target <host> -o root.o root.tmbc
//!      A nonzero exit is TRUSTCG_FAIL (the adapter fail-closed: its exact
//!      stderr — "unsupported trust_ir type ...", "not yet lowered", etc. — is
//!      recorded). A tMBC the CG cannot even READ is VERSION_FAIL.
//!   3. LINK    — cc-link root.o + <shims.o> + clean_runtime.o + a driver. The
//!      LINKER is the authoritative oracle for the shared runtime-symbol gap:
//!      an undefined `l_Int_decLt` / `l_Quot_*` / `l_Nat_shiftRight` fails the
//!      link and is reported by exact symbol.
//!   4. RUN     — execute. For the checkable oracle subset the root is CALLED
//!      with sample args and the trust-cg-produced binary's value is asserted
//!      against the same hand-computed constants linkrun_census.rs checks. For
//!      other roots, the driver retains the entry at link time but does not call
//!      it, so `OK` establishes emit/link/load viability, not root semantics.
//!
//! FAIL-CLOSED within that scope: a root is OK only if the trust-cg-produced
//! retained-root binary links, runs (exit 0), and — where checkable — computes
//! the expected sample value.
//!
//! This census counts producer-labeled `Certified` translation-validation
//! obligations before stripping proof sections for codegen compatibility. It
//! does not re-check those certificates and does not qualify TrustCG's
//! production consumption of proof-bearing tMBC.
//!
//! This is an explicit qualification utility, not a default test. `TRUSTCG_BIN`
//! is mandatory; the report records its canonical path and reported version.
//! Missing compiler prerequisites and every non-OK root fail the process.
//!
//! Gated opt-in by the `trustcg-census` leg of `scripts/local_gate.sh`
//! (`CLEAN_TRUSTCG_CENSUS=1` + `TRUSTCG_BIN`): the leg compares `TRUSTCG_OUT`
//! row by row against the verdicts pinned in `trustcg_census.expected.json`
//! beside this file (`scripts/check_trustcg_census.py`), so a changed root is
//! refused by name rather than folded into the all-OK count checked below.
//!
//! Run:
//!   TRUSTCG_BIN=/path/to/trust-cg/target/release/trust-cg \
//!   TRUSTCG_OUT=/path/out.tsv cargo run -p clean-compiler --release \
//!     --features trust-ir-backend --example trustcg_census
//!
//! Optional: `TRUSTCG_LIMIT=N` (first N computable roots; output is labeled
//! `LIMITED — NOT FULL QUALIFICATION`).

#![cfg(feature = "trust-ir-backend")]

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::Write as _;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_compiler::emit_trust_ir::{serialize_tmbc, RuntimeLowering, TrustIrConfig};
use clean_compiler::mangle::mangle_name;
use clean_compiler::pass_manager::{compile_lcnf_decls, compile_lcnf_to_trust_ir, PipelineConfig};
use clean_compiler::to_lcnf::constant_to_decl;
use clean_compiler::Decl;
use clean_kernel::{ConstantKind, Environment, Expr, ExprVisitor, LevelVec, Name};

#[path = "trustcg_census/diagnostics.rs"]
mod diagnostics;
use diagnostics::undefined_symbols;

// ---------------------------------------------------------------------------
// Runtime primitives: the clean-cli PRIMITIVE_DENYLIST + verbatim shim mirror.
// (Byte-identical to linkrun_census.rs.)
// ---------------------------------------------------------------------------

// The 37 mangled symbols the runtime provides as prelude shims — the UNION of
// every `*_PRELUDE_SHIMS` table at the linkrun-integ integration. Byte-identical
// to `linkrun_census.rs`: the base 28 plus the quot eliminators
// (`l_Quot_lift`/`l_Quot_ind`), `l_Nat_shiftRight`, the heap-aware Nat Bool
// comparators (`l_Nat_ble`/`l_Nat_blt`/`l_Nat_beq`) and the Int decision
// procedures (`l_Int_decLt`/`l_Int_decLe`/`l_Int_decEq`). These are the extra
// `l_*` that closed the trust-cg census 846 -> 881.
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

struct Shim {
    // Not read by the harness (defs are concatenated wholesale); kept because
    // the table is a hand-maintained mirror of clean-cli's shim tables and the
    // symbol column is what makes each row auditable against that source.
    #[allow(dead_code)]
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

/// All shim definitions, as one C translation unit (compiled to shims.o once).
fn all_shims_c() -> String {
    let mut s = String::from("#include <stdio.h>\n#include \"clean_runtime.h\"\n");
    for shim in SHIMS {
        s.push_str(shim.def);
    }
    s
}

// ---------------------------------------------------------------------------
// cc + trust-cg plumbing.
// ---------------------------------------------------------------------------

fn runtime_include_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/include")
}
fn runtime_c_source() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/src/clean_runtime.c")
}
/// The inline-primitive materialization TU: real external symbols for the
/// header's `static inline` RC/box/field primitives that trust-cg lowers to
/// external calls. Linked into every root so the trust-cg object binds them.
fn runtime_extern_c_source() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/src/runtime_extern.c")
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
fn trust_cg_bin() -> PathBuf {
    std::env::var_os("TRUSTCG_BIN")
        .map(PathBuf::from)
        .expect("qualification requires an explicit TRUSTCG_BIN path")
}
fn host_target() -> &'static str {
    match std::env::consts::ARCH {
        "aarch64" => "aarch64",
        "x86_64" => "x86_64",
        other => panic!("unsupported host arch for trust-cg: {other}"),
    }
}

// ---------------------------------------------------------------------------
// Dependency-closure BFS (the clean-cli #14 discipline). Byte-identical logic
// to linkrun_census.rs.
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

/// Root lowering WITHOUT the denylist: `select_lcnf_decl` compiles the root
/// unconditionally (the denylist only drops DEPS to extern). So a denylisted
/// primitive AS A ROOT is real trust-cg codegen, not a shim.
fn probe_root(env: &Environment, name: &Name) -> Option<Decl> {
    let info = env.get_const(name)?;
    let decl = catch_unwind(AssertUnwindSafe(|| constant_to_decl(env, info)))
        .ok()?
        .ok()??;
    let ok = catch_unwind(AssertUnwindSafe(|| {
        compile_lcnf_decls(std::slice::from_ref(&decl), env, &PipelineConfig::default()).is_ok()
    }));
    matches!(ok, Ok(true)).then_some(decl)
}

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
// Value oracles (verbatim from linkrun_census.rs, plus ABI-correct prototypes
// so the calls are well-typed against the trust-cg object). Expected values are
// the SAME hand-computed constants linkrun_census.rs's OK_CHECKED verified.
// ---------------------------------------------------------------------------

/// (prototype decls binding the raw dotted entry symbol via an __asm__ label,
/// main body, expected stdout). clean names the entry by its RAW Lean name
/// (`Nat.pow`), emitted as Mach-O `_Nat.pow`; C reaches it via an asm label.
fn oracle(root: &str) -> Option<(&'static str, &'static str, &'static str)> {
    match root {
        "Nat.pow" => Some((
            // clean_nat_to_u128: heap-aware extractor (trust-cg returns the
            // zero-exponent literal 1 as a HEAP nat, which tagged-only
            // clean_unbox would misread). Value verified: 1024 125 1.
            "extern clean_obj* oracle_fn(clean_obj*, clean_obj*) __asm__(\"_Nat.pow\");",
            "int main(void){ printf(\"%llu %llu %llu\\n\", (unsigned long long)clean_nat_to_u128(oracle_fn(clean_box(2),clean_box(10))), (unsigned long long)clean_nat_to_u128(oracle_fn(clean_box(5),clean_box(3))), (unsigned long long)clean_nat_to_u128(oracle_fn(clean_box(7),clean_box(0)))); return 0; }",
            "1024 125 1",
        )),
        "Nat.decLe" => Some((
            "extern unsigned oracle_fn(clean_obj*, clean_obj*) __asm__(\"_Nat.decLe\");",
            "int main(void){ printf(\"%u %u %u\\n\", oracle_fn(clean_box(2),clean_box(5)), oracle_fn(clean_box(5),clean_box(2)), oracle_fn(clean_box(3),clean_box(3))); return 0; }",
            "1 0 1",
        )),
        "Nat.decLt" => Some((
            "extern unsigned oracle_fn(clean_obj*, clean_obj*) __asm__(\"_Nat.decLt\");",
            "int main(void){ printf(\"%u %u %u\\n\", oracle_fn(clean_box(2),clean_box(5)), oracle_fn(clean_box(5),clean_box(2)), oracle_fn(clean_box(3),clean_box(3))); return 0; }",
            "1 0 0",
        )),
        // ---- Int / UInt64 VALUE oracles (make the census honest, not link-only) ----
        // `Int` is a two-ctor cell — tag 0 `ofNat n` (= +n), tag 1 `negSucc n`
        // (= -(n+1)), Nat magnitude in object field 0. These roots are compiled by
        // trust-cg and BUILD Int cells at run time (via `clean_alloc_ctor`), then
        // pass them to the `clean_int_cmp`/heap-Nat runtime shims. Before the
        // trust-cg call-argument-fixup fix, the ctor's `num_objs` was clobbered to
        // garbage and `clean_ctor_get` read out of bounds (SIGSEGV/heap-overflow);
        // after it, the values are correct. The `iof`/`ins` helpers construct the
        // C-side operands with the SAME canonical layout.
        "Int.sub" => Some((
            "extern clean_obj* oracle_fn(clean_obj*, clean_obj*) __asm__(\"_Int.sub\");",
            "static clean_obj* iof(size_t n){ return clean_alloc_ctor(0,1,0,clean_box(n)); }\n\
             static clean_obj* ins(size_t n){ return clean_alloc_ctor(1,1,0,clean_box(n)); }\n\
             static long long idec(clean_obj* x){ unsigned t=clean_obj_tag(x); \
               unsigned long long n=(unsigned long long)clean_nat_to_u128(clean_ctor_get(x,0)); \
               return t==0?(long long)n:-(long long)(n+1); }\n\
             int main(void){ printf(\"%lld %lld %lld\\n\", \
               idec(oracle_fn(iof(5),iof(3))), \
               idec(oracle_fn(iof(3),iof(5))), \
               idec(oracle_fn(iof(10),iof(2)))); return 0; }",
            "2 -2 8",
        )),
        // Int.decLe compiled: its internal sign-check resolves to the l_Int_decLe
        // SHIM (Int.decLe is the root, so Int.decLt/Int.add sign-checks are deps ->
        // denylisted -> shim), so it terminates. Result is a Decidable scrutinee
        // read as an unboxed 0/1 tag. decLe 3 3=1, 5 3=0, -2 1=1.
        "Int.decLe" => Some((
            "extern unsigned oracle_fn(clean_obj*, clean_obj*) __asm__(\"_Int.decLe\");",
            "static clean_obj* iof(size_t n){ return clean_alloc_ctor(0,1,0,clean_box(n)); }\n\
             static clean_obj* ins(size_t n){ return clean_alloc_ctor(1,1,0,clean_box(n)); }\n\
             int main(void){ printf(\"%u %u %u\\n\", \
               oracle_fn(iof(3),iof(3)), \
               oracle_fn(iof(5),iof(3)), \
               oracle_fn(ins(1),iof(1))); return 0; }",
            "1 0 1",
        )),
        // Int.decLt as a COMPILED root does not terminate: clean lowers Int.add's
        // constructor-match sign-check to `Int.decLt`, and Int.decLt calls Int.add
        // (a+1), so the compiled root mutually recurses (Int.decLt<->Int.add) with
        // no base case. This is a clean-lowering cycle (present in the trust-ir
        // itself, independent of the ctor codegen fix) that also affects emit_c's
        // compiled Int.decLt. Both censuses therefore VALUE-CHECK Int.decLt via the
        // runtime SHIM `l_Int_decLt` (the runtime-provided primitive real code
        // links against) over C-constructed cells, exactly like linkrun_census's
        // `shim_oracle`. decLt 3 5=1, -2 1=1, 5 -2=0.
        "Int.decLt" => Some((
            "extern clean_obj* l_Int_decLt(clean_obj*, clean_obj*);",
            "static clean_obj* iof(size_t n){ return clean_alloc_ctor(0,1,0,clean_box(n)); }\n\
             static clean_obj* ins(size_t n){ return clean_alloc_ctor(1,1,0,clean_box(n)); }\n\
             int main(void){ printf(\"%zu %zu %zu\\n\", \
               clean_unbox(l_Int_decLt(iof(3),iof(5))), \
               clean_unbox(l_Int_decLt(ins(1),iof(1))), \
               clean_unbox(l_Int_decLt(iof(5),ins(1)))); return 0; }",
            "1 1 0",
        )),
        // UInt64.ofNat n = clean_unbox_uint64(n): the Nat lowered to a native U64
        // scalar, returned raw (not boxed). ofNat 100=100, 0=0, 255=255.
        "UInt64.ofNat" => Some((
            "extern unsigned long long oracle_fn(clean_obj*) __asm__(\"_UInt64.ofNat\");",
            "int main(void){ printf(\"%llu %llu %llu\\n\", \
               oracle_fn(clean_box(100)), oracle_fn(clean_box(0)), oracle_fn(clean_box(255))); return 0; }",
            "100 0 255",
        )),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Verdicts.
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct Verdict {
    /// OK | OK_CHECKED | OK_SHIM | LOWER_FAIL | EMITIR_FAIL | TRUSTCG_FAIL
    /// | VERSION_FAIL | LINK_FAIL | RUN_FAIL | NO_ENTRY
    tag: &'static str,
    detail: String,
}
fn ok(t: &'static str) -> Verdict {
    Verdict {
        tag: t,
        detail: String::new(),
    }
}
/// A failing verdict. The detail is made ONE TSV FIELD here, at the only
/// constructor: a tab, CR or newline inside it (an `EMITIR_FAIL` error's
/// Display, or the stdout of a miscompiled driver quoted by `RUN_FAIL`) would
/// otherwise split the `TRUSTCG_OUT` row, and `check_trustcg_census.py`
/// refuses a split row (its selftest arm "a detail split across lines"), so
/// one root's multi-line detail would make the WHOLE census uncomparable
/// instead of naming that root (found in the WS6.0 review).
fn fail(t: &'static str, d: String) -> Verdict {
    Verdict {
        tag: t,
        detail: d
            .replace('\t', "\\t")
            .replace('\r', "\\r")
            .replace('\n', "\\n"),
    }
}
fn is_ok(tag: &str) -> bool {
    matches!(tag, "OK" | "OK_CHECKED" | "OK_SHIM")
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

/// Aggregate backend-TV status coverage over the census population (minted by
/// `compile_lcnf_to_trust_ir`; not re-checked by this utility).
#[derive(Default)]
struct CertStats {
    /// Roots whose emitted module carries >= 1 producer-labeled `Certified`
    /// `TranslationValidation` obligation. This census does not re-check it.
    roots_with_certs: usize,
    /// Total producer-labeled Certified obligations across all root modules.
    decls_certified: usize,
}

fn main() {
    let Some(cc) = find_c_compiler() else {
        panic!("trustcg_census requires a C compiler (cc/gcc/clang)");
    };
    let tcg = trust_cg_bin();
    assert!(
        tcg.is_file(),
        "trust-cg binary not found at {}",
        tcg.display()
    );
    let tcg = std::fs::canonicalize(&tcg).expect("canonicalize TRUSTCG_BIN");
    let tcg_version_output = Command::new(&tcg)
        .arg("--version")
        .output()
        .expect("invoke TRUSTCG_BIN --version");
    assert!(
        tcg_version_output.status.success(),
        "TRUSTCG_BIN --version failed:\n{}",
        String::from_utf8_lossy(&tcg_version_output.stderr)
    );
    let tcg_version = String::from_utf8(tcg_version_output.stdout)
        .expect("TRUSTCG_BIN --version emitted non-UTF-8 output")
        .trim()
        .to_owned();
    assert!(
        !tcg_version.is_empty(),
        "TRUSTCG_BIN --version emitted empty output"
    );
    let target = host_target();
    let limit = optional_usize_env("TRUSTCG_LIMIT");
    let out_path = std::env::var("TRUSTCG_OUT").ok();

    let mut env = Environment::with_prelude();
    env.init_io_ops()
        .expect("initialize IO prelude for TrustCG census");
    let pipeline = PipelineConfig::default();

    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    // Shared scratch: precompile clean_runtime.o + runtime_extern.o + shims.o ONCE.
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

    // The inline-primitive bridge: real external symbols for the header's
    // `static inline` primitives that trust-cg lowers to external calls. Compiled
    // from the crate source by default; `TRUSTCG_RTEXTERN_O` overrides the path
    // (e.g. an independently built .o). Linked into EVERY root below.
    let rtextern_o: PathBuf = match std::env::var_os("TRUSTCG_RTEXTERN_O") {
        Some(p) => PathBuf::from(p),
        None => {
            let o = scratch.path().join("runtime_extern.o");
            let re = Command::new(&cc)
                .args(["-O1", "-c"])
                .arg(runtime_extern_c_source())
                .arg("-I")
                .arg(runtime_include_dir())
                .arg("-o")
                .arg(&o)
                .output()
                .expect("spawn cc for runtime_extern");
            assert!(
                re.status.success(),
                "precompiling runtime_extern.o failed:\n{}",
                String::from_utf8_lossy(&re.stderr)
            );
            o
        }
    };

    let shims_c = scratch.path().join("shims.c");
    std::fs::write(&shims_c, all_shims_c()).expect("write shims.c");
    let shims_o = scratch.path().join("shims.o");
    let sc = Command::new(&cc)
        .args(["-O1", "-c"])
        .arg(&shims_c)
        .arg("-I")
        .arg(runtime_include_dir())
        .arg("-o")
        .arg(&shims_o)
        .output()
        .expect("spawn cc for shims");
    assert!(
        sc.status.success(),
        "precompiling shims.o failed:\n{}",
        String::from_utf8_lossy(&sc.stderr)
    );

    // Enumerate + stably order the prelude.
    let mut names: Vec<Name> = env.constants().map(|c| c.name.clone()).collect();
    names.sort_by_key(|n| n.to_string());

    // Stage 0: computable population = constant_to_decl yields Some AND
    // kind == Definition (identical classification to linkrun_census.rs).
    let mut computable: Vec<Name> = Vec::new();
    let mut n_none = 0usize;
    let mut n_lowfail = 0usize;
    let mut n_theorem = 0usize;
    let mut n_opaque = 0usize;
    let mut n_axiomkind = 0usize;
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

    // Stage 1: per-root LOWER -> CODEGEN -> LINK -> RUN.
    let mut cache: HashMap<Name, Option<Decl>> = HashMap::new();
    let mut verdicts: BTreeMap<String, Verdict> = BTreeMap::new();
    let mut cert_stats = CertStats::default();
    let total = computable.len();
    for (idx, root) in computable.iter().enumerate() {
        let root_s = root.to_string();
        let mangled = mangle_name(root);
        let v = classify_root(
            &cc,
            &tcg,
            target,
            &runtime_o,
            &rtextern_o,
            &shims_o,
            &env,
            &pipeline,
            root,
            &mangled,
            &mut cache,
            &mut cert_stats,
        );
        if (idx + 1) % 50 == 0 || idx + 1 == total {
            eprintln!("  ... {}/{} ({}) [{}]", idx + 1, total, root_s, v.tag);
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
    let scope = if limit.is_some() {
        "LIMITED — NOT FULL QUALIFICATION"
    } else {
        "FULL"
    };

    println!("\n================ TRUST-CG LINK+RUN CENSUS ================");
    println!("scope                       = {scope}");
    println!("requested limit             = {limit:?}");
    println!("trust-cg binary             = {}", tcg.display());
    println!("trust-cg version            = {tcg_version}");
    println!("total_constants             = {}", names.len());
    println!("non_computable (lower none) = {n_none}");
    println!("lower_err_or_panic          = {n_lowfail}");
    println!("excluded proofs (Theorem)   = {n_theorem}");
    println!("excluded Opaque             = {n_opaque}");
    println!("excluded Axiom-with-value   = {n_axiomkind}");
    println!("COMPUTABLE defs (full population) = {full_population}");
    println!("COMPUTABLE defs (selected)   = {total}");
    println!("---------------------------------------------------------");
    println!("CENSUS OK (via trust-cg)    = {n_ok} / {total}");
    for (tag, c) in &counts {
        println!("  {tag:<13} = {c}");
    }
    println!("---------------------------------------------------------");
    println!(
        "TV status=Certified (unrechecked) = {} / {total} ({} decl(s) total)",
        cert_stats.roots_with_certs, cert_stats.decls_certified
    );
    println!("=========================================================");
    for tag in [
        "EMITIR_FAIL",
        "TRUSTCG_FAIL",
        "VERSION_FAIL",
        "NO_ENTRY",
        "LINK_FAIL",
        "RUN_FAIL",
        "LOWER_FAIL",
    ] {
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
        let mut f = std::fs::File::create(&path).expect("open TRUSTCG_OUT");
        writeln!(
            f,
            "# scope={scope:?} requested_limit={limit:?} trustcg_bin={:?} trustcg_version={tcg_version:?} total_constants={} non_computable={} lower_err={} theorems={} opaque={} axiomkind={} full_population={} selected_defs={} ok={} tv_status_certified_roots={} tv_status_certified_decls={} tv_status_rechecked=false",
            tcg.display().to_string(),
            names.len(),
            n_none,
            n_lowfail,
            n_theorem,
            n_opaque,
            n_axiomkind,
            full_population,
            total,
            n_ok,
            cert_stats.roots_with_certs,
            cert_stats.decls_certified
        ).unwrap();
        for (name, v) in &verdicts {
            writeln!(f, "{name}\t{}\t{}", v.tag, v.detail).unwrap();
        }
        eprintln!("wrote {path}");
    }

    // A failed census is a verdict, not a crash. The release profile builds
    // with `panic = "abort"`, so the `assert_eq!` that stood here ended every
    // red run with SIGABRT (exit 134), which also makes macOS write a crash
    // report. `check_trustcg_census.py --census-exit` needs only a non-zero
    // status exactly when some row is not OK.
    if total == 0 {
        eprintln!("no computable roots enumerated");
        std::process::exit(2);
    }
    if n_ok != total {
        eprintln!(
            "selected TrustCG census failed for {} of {total} computable roots",
            total - n_ok
        );
        std::process::exit(1);
    }
}

/// Classify one computable root end-to-end through the trust-cg path.
#[allow(clippy::too_many_arguments)]
fn classify_root(
    cc: &str,
    tcg: &Path,
    target: &str,
    runtime_o: &Path,
    rtextern_o: &Path,
    shims_o: &Path,
    env: &Environment,
    pipeline: &PipelineConfig,
    root: &Name,
    mangled: &str,
    cache: &mut HashMap<Name, Option<Decl>>,
    cert_stats: &mut CertStats,
) -> Verdict {
    // Root must itself compile from source (WITHOUT the denylist — the real
    // `select_lcnf_decl` compiles the root unconditionally; the denylist only
    // drops DEPS to extern shims).
    let Some(root_decl) = probe_root(env, root) else {
        return fail("LOWER_FAIL", "root does not compile from source".into());
    };
    let decls = build_closure(env, root, root_decl, cache);
    let raw = root.to_string();

    // (1) LOWER to trust-ir with cmd_compile::compile_to_object's config.
    let config = TrustIrConfig {
        module_name: "clean_module".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        source_file: None,
        ..TrustIrConfig::default()
    };
    let tmbc = catch_unwind(AssertUnwindSafe(|| {
        compile_lcnf_to_trust_ir(&decls, env, pipeline, &config).map(|mut m| {
            // Status coverage: producer-labeled `Certified`
            // TranslationValidation obligations minted by the default-on
            // backend TV pass. This census counts but does not re-check them.
            let certs = m
                .proof_obligations
                .iter()
                .filter(|o| {
                    o.kind == trust_ir::proof::ObligationKind::TranslationValidation
                        && o.status == trust_ir::proof::ProofStatus::Certified
                })
                .count();
            // CODEGEN is cert-agnostic: trust-cg lowers the IR, it does not
            // consume proofs. Certificate re-checking belongs to
            // `trust_ir_build::validate` and is outside this census. Strip the
            // proof sections before serializing FOR CODEGEN so this census
            // measures the trust-ir->object->link->run path only — and stays
            // decoupled from the proof-lineage wire subversion a stale trust-cg
            // binary may predate. (The count above is taken from the FULL
            // minted module.) NB: the real `clean compile --emit obj` path
            // ships the certs; a shipping trust-cg must be built against a
            // trust-ir new enough to read the CleanCic proof lineage.
            m.proof_obligations.clear();
            m.proof_certificates.clear();
            (serialize_tmbc(&m), certs)
        })
    }));
    let (tmbc_bytes, certs) = match tmbc {
        Ok(Ok((Ok(bytes), certs))) => (bytes, certs),
        Ok(Ok((Err(error), _))) => return fail("EMITIR_FAIL", error.to_string()),
        Ok(Err(e)) => return fail("EMITIR_FAIL", format!("{e}")),
        Err(_) => return fail("EMITIR_FAIL", "panic in compile_lcnf_to_trust_ir".into()),
    };
    cert_stats.decls_certified += certs;
    if certs > 0 {
        cert_stats.roots_with_certs += 1;
    }

    let dir = tempfile::tempdir().expect("root tempdir");
    let tmbc_path = dir.path().join("root.tmbc");
    let obj_path = dir.path().join("root.o");
    if std::fs::write(&tmbc_path, &tmbc_bytes).is_err() {
        return fail("EMITIR_FAIL", "could not write root.tmbc".into());
    }

    // (2) CODEGEN via the selected trust-cg CLI, using cmd_compile's invocation:
    // `trust-cg -c --target <t> -o out.o in.tmbc`.
    let cg = Command::new(tcg)
        .args(["-c", "--target", target, "-o"])
        .arg(&obj_path)
        .arg(&tmbc_path)
        .output()
        .expect("spawn trust-cg");
    if !cg.status.success() {
        let stderr = String::from_utf8_lossy(&cg.stderr);
        // Extract the trust-cg diagnostic line (adapter message).
        let msg = stderr
            .lines()
            .find(|l| l.contains("trust-cg: error"))
            .unwrap_or_else(|| stderr.lines().last().unwrap_or(""))
            .trim()
            .to_string();
        if msg.contains("failed to read trust_ir module") {
            return fail("VERSION_FAIL", msg);
        }
        return fail(
            "TRUSTCG_FAIL",
            if msg.is_empty() {
                "trust-cg nonzero, empty stderr".into()
            } else {
                msg
            },
        );
    }
    if !obj_path.exists() {
        return fail(
            "TRUSTCG_FAIL",
            "trust-cg exit 0 but no object produced".into(),
        );
    }
    // Optional dump for symbol-name forensics.
    if let Some(keep) = std::env::var_os("TRUSTCG_KEEPDIR") {
        let d = PathBuf::from(keep);
        let _ = std::fs::create_dir_all(&d);
        let _ = std::fs::copy(&obj_path, d.join(format!("{mangled}.o")));
        let _ = std::fs::copy(&tmbc_path, d.join(format!("{mangled}.tmbc")));
    }

    // (3) LINK: driver + root.o + shims.o + clean_runtime.o.
    let (proto, main_body, expected): (&str, String, Option<&'static str>) =
        match oracle(&root.to_string()) {
            Some((p, body, exp)) => (p, body.to_string(), Some(exp)),
            None => (
                "",
                // Reference the root's raw dotted entry symbol (via asm label)
                // so its object — and every transitive undefined runtime extern
                // it carries — is retained and must resolve at link time.
                format!("extern void oracle_fn(void) __asm__(\"_{raw}\"); int main(void){{ void* volatile p = (void*)&oracle_fn; (void)p; return 0; }}"),
                None,
            ),
        };
    let program = format!(
        "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n\
         #include \"clean_runtime.h\"\n{proto}\n{main_body}\n"
    );
    let src = dir.path().join("driver.c");
    let bin = dir.path().join("driver");
    if std::fs::write(&src, &program).is_err() {
        return fail("LINK_FAIL", "could not write driver.c".into());
    }
    let mut link_cmd = Command::new(cc);
    link_cmd
        .arg("-O0")
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .arg(&obj_path)
        .arg(shims_o)
        .arg(runtime_o)
        // The inline-primitive bridge: real symbols for the clean runtime's
        // header-only `static inline` primitives (`clean_inc` / `clean_box` /
        // `clean_unbox*` / `clean_ctor_get` / `clean_obj_tag` / ...) that
        // trust-cg lowers to external calls. Part of the clean-runtime build
        // (see `runtime_extern_c_source`); precompiled once above.
        .arg(rtextern_o);
    let link = link_cmd
        .arg("-I")
        .arg(runtime_include_dir())
        .output()
        .expect("spawn cc link");
    if !link.status.success() {
        let stderr = String::from_utf8_lossy(&link.stderr);
        let undef = undefined_symbols(&stderr);
        // If the ONLY missing symbol is the root's own entry, trust-cg produced
        // an object without the expected body -> NO_ENTRY.
        if undef.len() == 1 && undef[0] == raw {
            return fail("NO_ENTRY", format!("trust-cg emitted no `{raw}` body"));
        }
        let detail = if !undef.is_empty() {
            format!("undefined: {}", undef.join(","))
        } else {
            let tail: String = stderr
                .lines()
                .filter(|l| {
                    l.contains("error") || l.contains("Undefined") || l.contains("undefined")
                })
                .take(3)
                .collect::<Vec<_>>()
                .join(" | ");
            format!(
                "cc/link failed: {}",
                if tail.is_empty() {
                    "see stderr".into()
                } else {
                    tail
                }
            )
        };
        return fail("LINK_FAIL", detail);
    }

    // (4) RUN.
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
