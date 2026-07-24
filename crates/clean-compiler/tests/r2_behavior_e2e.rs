// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R2 BEHAVIORAL pins, end-to-end (kernel prelude value → LCNF → full
//! pipeline → emitted C → host `cc` (+ AddressSanitizer when available) →
//! executed against the real clean runtime), with hand-computed expectations:
//!
//! 1. **Multi-parameter `Nat.rec` declarations** (`List.replicate`,
//!    `Nat.pow`) — the retired `lower_nat_rec` special case materialized the
//!    induction hypothesis as `self_name(pred)`, the enclosing declaration
//!    applied to the predecessor ONLY: census-green, but every
//!    multi-parameter declaration received an under-applied PAP closure as
//!    its IH (`List.replicate n x`'s minor consumed a closure awaiting `x`
//!    where the recursive LIST belonged). The R1 synthesized-recursion path
//!    threads the captures; these drive the real values.
//! 2. **RC last-use transfer** (`rc::insert`) — a non-param local whose last
//!    use is a consuming call used to receive a compensating `inc` with no
//!    death `dec` (one leaked reference per cons step in recursive `go`s).
//!    A recursion-heavy workload is driven in a loop and (on macOS) the
//!    malloc-zone block count must stay flat.
//! 3. **UIntN scalar-carrier decodes** (`UIntN.ofNat` / `ofNatLT`, widths
//!    8/16/32): `UInt32.ofNat 300 = 300`, the `2^32 - 1` boundary, the
//!    modular wrap `2^32 + 7 -> 7`, and `UInt8.ofNat 300 = 44`.
//!    (`UInt64`/`USize` decodes are REFUSED by
//!    design — both emitters' `Unbox` route for width 64 is the heap-only
//!    `clean_unbox_uint64`, and a `>= 2^63` payload cannot round-trip the
//!    tagged box — so there is no runtime pin for them; the refusal is
//!    pinned in `to_ir` unit tests.)
//!
//! Skips (like the other native e2e tests) when no C compiler is found.

#![cfg(feature = "round-trip-compile")]

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_compiler::emit_c::{emit_c_with_config, CEmitConfig};
use clean_compiler::pass_manager::{compile_lcnf_decls, PipelineConfig};
use clean_compiler::to_lcnf::constant_to_decl;
use clean_compiler::Decl;
use clean_kernel::{Environment, Expr, ExprVisitor, LevelVec, Name};

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
            .map(|output| output.status.success())
            .unwrap_or(false)
        {
            return Some(compiler.to_string());
        }
    }
    None
}

/// Whether `cc` can link a trivial AddressSanitizer binary in `dir`.
fn asan_supported(cc: &str, dir: &Path) -> bool {
    let probe_src = dir.join("asan_probe.c");
    let probe_bin = dir.join("asan_probe");
    if std::fs::write(&probe_src, "int main(void){return 0;}\n").is_err() {
        return false;
    }
    Command::new(cc)
        .arg("-fsanitize=address")
        .arg("-o")
        .arg(&probe_bin)
        .arg(&probe_src)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

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
    let mut collector = DepCollector { deps: Vec::new() };
    collector.visit_expr(value);
    collector.deps
}

/// The primitive shims the driver preamble provides; the closure BFS treats
/// them as extern boundaries so the shim ALWAYS wins over a from-source
/// compile — the same `#14` denylist discipline as `clean-cli`'s native
/// build. (Since R2 routes every `Nat.rec` through the synthesized-recursion
/// path, `Nat.add`/`Nat.mul` genuinely compile from source; without the
/// denylist they would collide with the preamble shims at link time.)
const DRIVER_DENYLIST: &[&str] = &[
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.decEq",
];

/// The compilable dependency closure of `roots` (the `clean compile` BFS:
/// per-declaration probe, extern-drop on failure and on the driver
/// denylist), compiled through the full default pipeline. Mirrors
/// `rec_eliminator_e2e.rs` + the census denylist discipline.
fn compile_closure(
    env: &Environment,
    roots: &[&str],
    extra_denylist: &[&str],
) -> Vec<clean_compiler::ir::IRDecl> {
    let pipeline = PipelineConfig::default();
    let mut verdict: HashMap<Name, Option<Decl>> = HashMap::new();
    let mut probe = |env: &Environment, name: &Name| -> Option<Decl> {
        if let Some(v) = verdict.get(name) {
            return v.clone();
        }
        let v = (|| {
            let key = name.to_string();
            if DRIVER_DENYLIST.contains(&key.as_str()) || extra_denylist.contains(&key.as_str()) {
                return None;
            }
            let info = env.get_const(name)?;
            let decl = constant_to_decl(env, info).ok()??;
            compile_lcnf_decls(std::slice::from_ref(&decl), env, &pipeline)
                .is_ok()
                .then_some(decl)
        })();
        verdict.insert(name.clone(), v.clone());
        v
    };

    let mut seen: HashSet<Name> = HashSet::new();
    let mut decls: Vec<Decl> = Vec::new();
    let mut worklist: Vec<Name> = roots.iter().map(|r| Name::from_string(r)).collect();
    while let Some(dep) = worklist.pop() {
        if !seen.insert(dep.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&dep) else {
            continue;
        };
        let Some(decl) = probe(env, &dep) else {
            continue;
        };
        if let Some(value) = &info.value {
            worklist.extend(collect_deps(value));
        }
        decls.push(decl);
    }
    for root in roots {
        assert!(
            seen.contains(&Name::from_string(root)) && verdict[&Name::from_string(root)].is_some(),
            "root {root} must compile from source"
        );
    }
    compile_lcnf_decls(&decls, env, &pipeline)
        .expect("closure compiles through the full pipeline")
        .boxed_ir_decls
}

/// Primitive denylist shims + tiny driver helpers, prepended to the emitted C
/// (the real `clean` native build prepends its shim tables the same way).
const SHIM_PREAMBLE: &str = r#"
#include "clean_runtime.h"
clean_obj* l_Nat_add(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) + clean_unbox(b)); }
clean_obj* l_Nat_sub(clean_obj* a, clean_obj* b) { size_t x = clean_unbox(a), y = clean_unbox(b); return clean_box(x < y ? 0 : x - y); }
clean_obj* l_Nat_mul(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) * clean_unbox(b)); }
clean_obj* l_Nat_div(clean_obj* a, clean_obj* b) { size_t x = clean_unbox(a), y = clean_unbox(b); return clean_box(y == 0 ? 0 : x / y); }
clean_obj* l_Nat_mod(clean_obj* a, clean_obj* b) { size_t x = clean_unbox(a), y = clean_unbox(b); return clean_box(y == 0 ? x : x % y); }
clean_obj* l_Nat_decEq(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) == clean_unbox(b) ? 1 : 0); }
static clean_obj* nil(void) { return clean_box(0); }
/* Extern-boundary stubs for PROOF-machinery residue some closures carry
 * (Nat.divmodAux lemma lambdas, Eq.subst, the Prop head Nat.le): verified
 * UNREACHABLE from every driven entry point — the stubs abort so any future
 * change that routes execution through them fails the driver loudly instead
 * of silently computing with dummies. */
#include <stdlib.h>
static clean_obj* unreachable_proof_stub(const char* who) {
    fprintf(stderr, "driver reached proof-machinery extern %s\n", who);
    abort();
}
clean_obj* l_Eq_ndrec(clean_obj* a, clean_obj* b, clean_obj* c, clean_obj* d, clean_obj* e, clean_obj* f) { (void)a;(void)b;(void)c;(void)d;(void)e;(void)f; return unreachable_proof_stub("Eq.ndrec"); }
clean_obj* l_Nat_le__of__succ__le__succ(clean_obj* a, clean_obj* b, clean_obj* c) { (void)a;(void)b;(void)c; return unreachable_proof_stub("Nat.le_of_succ_le_succ"); }
clean_obj* l_Nat_le__trans(clean_obj* a, clean_obj* b, clean_obj* c, clean_obj* d, clean_obj* e) { (void)a;(void)b;(void)c;(void)d;(void)e; return unreachable_proof_stub("Nat.le_trans"); }
clean_obj* l_Nat_not__succ__le__zero(clean_obj* a, clean_obj* b) { (void)a;(void)b; return unreachable_proof_stub("Nat.not_succ_le_zero"); }
clean_obj* l_Nat_succ__le__succ(clean_obj* a, clean_obj* b, clean_obj* c) { (void)a;(void)b;(void)c; return unreachable_proof_stub("Nat.succ_le_succ"); }
clean_obj* l_Nat_le(clean_obj* a, clean_obj* b) { (void)a;(void)b; return unreachable_proof_stub("Nat.le"); }
"#;

/// Compile `emitted` + driver `main_body`, run it, and return stdout lines.
///
/// `want_asan`: AddressSanitizer instruments the behavior drivers so
/// UAF/overflow in the lowering surfaces as hard failures. The LEAK gate
/// must pass `false`: ASan's allocator quarantines freed blocks, so
/// `malloc_zone_statistics` never sees them return and every measurement
/// reads as a leak.
fn build_and_run(
    cc: &str,
    name: &str,
    emitted: &str,
    main_body: &str,
    want_asan: bool,
) -> Vec<String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join(format!("{name}.c"));
    let binary = dir.path().join(name);
    std::fs::write(
        &source,
        format!("#include <stdio.h>\n{SHIM_PREAMBLE}\n{emitted}\n{main_body}"),
    )
    .expect("write source");

    let mut cmd = Command::new(cc);
    let use_asan = want_asan && asan_supported(cc, dir.path());
    if use_asan {
        cmd.arg("-fsanitize=address");
    }
    let compile = cmd
        .arg("-o")
        .arg(&binary)
        .arg(&source)
        .arg(runtime_c_source())
        .arg("-I")
        .arg(runtime_include_dir())
        .output()
        .expect("spawn cc");
    assert!(
        compile.status.success(),
        "cc failed:\n{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let run = Command::new(&binary).output().expect("run driver");
    assert!(
        run.status.success(),
        "driver exited nonzero (asan={use_asan}):\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8_lossy(&run.stdout)
        .lines()
        .map(str::to_string)
        .collect()
}

/// Multi-parameter `Nat.rec` declarations compute the right VALUES: the
/// `List.replicate` class of the retired `lower_nat_rec` miscompile.
///
/// Hand-computed expectations:
///   replicate 3 7          = [7, 7, 7]        (IH is the recursive LIST)
///   replicate 0 9          = []               (zero arm)
///   pow 2 10               = 1024             (IH threaded with base 2)
///   pow 5 3                = 125
///   pow 7 0                = 1                (zero arm)
///
/// Pre-fix, the IH was the PAP closure `List.replicate(pred)` /
/// `Nat.pow(pred)` — `replicate 3 7` consed closure objects instead of
/// lists (tag/field garbage), and `pow 2 10` multiplied a closure pointer.
#[test]
fn test_multi_param_nat_rec_decls_compute_correct_values() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("e2e skipped: no C compiler found (cc/gcc/clang)");
        return;
    };

    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    let decls = compile_closure(&env, &["List.replicate", "Nat.pow"], &[]);
    let emitted = emit_c_with_config(
        &decls,
        CEmitConfig {
            check_ir: false,
            ..CEmitConfig::default()
        },
    )
    .expect("emit C for the closure");

    let main_body = r#"
static void print_list(const char* label, clean_obj* l) {
    printf("%s=[", label);
    int first = 1;
    while (clean_obj_tag(l) == 1) {
        printf(first ? "%zu" : ",%zu", clean_unbox(clean_ctor_get(l, 0)));
        first = 0;
        l = clean_ctor_get(l, 1);
    }
    printf("] end_tag=%u\n", clean_obj_tag(l));
}
int main(void) {
    clean_obj* er = clean_box(0);
    print_list("replicate_3_7", l_List_replicate(er, clean_box(3), clean_box(7)));
    print_list("replicate_0_9", l_List_replicate(er, clean_box(0), clean_box(9)));
    printf("pow_2_10=%zu\n", clean_unbox(l_Nat_pow(clean_box(2), clean_box(10))));
    printf("pow_5_3=%zu\n", clean_unbox(l_Nat_pow(clean_box(5), clean_box(3))));
    printf("pow_7_0=%zu\n", clean_unbox(l_Nat_pow(clean_box(7), clean_box(0))));
    return 0;
}
"#;

    let lines = build_and_run(&cc, "r2_multiparam", &emitted, main_body, true);
    assert_eq!(
        lines,
        vec![
            "replicate_3_7=[7,7,7] end_tag=0",
            "replicate_0_9=[] end_tag=0",
            "pow_2_10=1024",
            "pow_5_3=125",
            "pow_7_0=1",
        ],
        "multi-param Nat.rec behavioral mismatch"
    );
}

/// UIntN scalar-carrier decode behavior (widths 8/16/32), hand-computed:
///
///   UInt32.ofNat 300         = 300
///   UInt32.ofNat (2^32 - 1)  = 4294967295     (boundary)
///   UInt32.ofNat (2^32 + 7)  = 7              (the `% 2^32` semantics)
///   UInt32.ofNatLT 123 h     = 123            (kernel-bounded, no mod)
///   UInt8.ofNat 300          = 44             (300 % 256)
///   UInt16.ofNat 70000       = 4464           (70000 % 65536)
///   Char.ofNat 65            = 65 ('A')       (valid scalar range)
#[test]
fn test_uintn_scalar_carrier_decodes_compute_correct_values() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("e2e skipped: no C compiler found (cc/gcc/clang)");
        return;
    };

    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    // `Char.ofNat` is deliberately NOT driven: its census win is real (the
    // same width-32 decode `UInt32.ofNatLT` drives below), but its range
    // check pulls Decidable/Eq proof machinery whose extern residue has no
    // link surface in this harness. `Fin.ofNat` is dead code after the
    // decode rewrite (nothing in the emitted closure calls it) but its own
    // decl drags the same proof externs — keep it out of the link.
    let decls = compile_closure(
        &env,
        &[
            "UInt32.ofNat",
            "UInt32.ofNatLT",
            "UInt8.ofNat",
            "UInt16.ofNat",
        ],
        &["Fin.ofNat", "BitVec.ofNatLT"],
    );
    let emitted = emit_c_with_config(
        &decls,
        CEmitConfig {
            check_ir: false,
            ..CEmitConfig::default()
        },
    )
    .expect("emit C for the closure");

    // Extern-boundary stubs for the closure's PROOF-machinery residue
    // (Nat.divmodAux lemma lambdas, Eq.subst): verified UNREACHABLE from the
    // four driven entry points — the stubs abort so any future change that
    // routes execution through them fails this test loudly instead of
    // silently computing with dummies.
    let main_body = r#"
int main(void) {
    printf("u32_300=%u\n", l_UInt32_ofNat(clean_box(300)));
    printf("u32_max=%u\n", l_UInt32_ofNat(clean_box(4294967295u)));
    printf("u32_wrap=%u\n", l_UInt32_ofNat(clean_box(4294967296ull + 7)));
    printf("u32_lt_123=%u\n", l_UInt32_ofNatLT(clean_box(123), clean_box(0)));
    printf("u8_300=%u\n", (unsigned)l_UInt8_ofNat(clean_box(300)));
    printf("u16_70000=%u\n", (unsigned)l_UInt16_ofNat(clean_box(70000)));
    return 0;
}
"#;

    let lines = build_and_run(&cc, "r2_uintn", &emitted, main_body, true);
    assert_eq!(
        lines,
        vec![
            "u32_300=300",
            "u32_max=4294967295",
            "u32_wrap=7",
            "u32_lt_123=123",
            "u8_300=44",
            "u16_70000=4464",
        ],
        "UIntN scalar-carrier decode behavioral mismatch"
    );
}

/// RC leak gate: a recursion-heavy workload (`List.replicate` — one cons
/// cell per step — built and released in a loop) must not strand
/// references. Pre-R2, every consuming LAST USE of a local carried a
/// compensating `inc` with no death `dec`, so each loop iteration leaked
/// its cons cells; on macOS the malloc-zone in-use block count made that a
/// linear ramp. Post-R2 the count stays flat (bounded by allocator noise).
///
/// The behavioral half (list contents correct after the loop) runs on every
/// platform; the block-count differential is Darwin-only
/// (`malloc_zone_statistics`).
#[test]
fn test_recursive_workload_does_not_leak_references() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("e2e skipped: no C compiler found (cc/gcc/clang)");
        return;
    };

    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    let decls = compile_closure(&env, &["List.replicate", "List.length"], &[]);
    let emitted = emit_c_with_config(
        &decls,
        CEmitConfig {
            check_ir: false,
            ..CEmitConfig::default()
        },
    )
    .expect("emit C for the closure");

    let main_body = r#"
#ifdef __APPLE__
#include <malloc/malloc.h>
static size_t blocks_in_use(void) {
    malloc_statistics_t stats;
    malloc_zone_statistics(NULL, &stats);
    return stats.blocks_in_use;
}
#else
static size_t blocks_in_use(void) { return 0; }
#endif
int main(void) {
    clean_obj* er = clean_box(0);
    /* Warm up allocator freelists + one correctness probe. R3: the emitted
       ABI is all-params-OWNED (the callee consumes one reference per
       argument), so the driver LENDS `probe` to `l_List_length` with a
       compensating `clean_inc` and releases its own stake afterwards. The
       pre-R3 spelling (`length(er, probe)` then `dec(probe)`) leaned on the
       callee's self-inferred borrowed params — the caller-invisible private
       convention that stranded `List.append`'s suffix per call. */
    clean_obj* probe = l_List_replicate(er, clean_box(64), clean_box(5));
    clean_inc(probe);
    printf("len_64=%zu\n", clean_unbox(l_List_length(er, probe)));
    clean_dec(probe);
    for (int i = 0; i < 50; i++) {
        clean_obj* warm = l_List_replicate(er, clean_box(64), clean_box(5));
        clean_dec(warm);
    }

    size_t before = blocks_in_use();
    /* 1000 iterations x 64 cons cells: the pre-R2 leak (>= 1 stranded
       reference per cons step) would strand >= 64000 blocks here. */
    for (int i = 0; i < 1000; i++) {
        clean_obj* l = l_List_replicate(er, clean_box(64), clean_box(5));
        clean_dec(l);
    }
    size_t after = blocks_in_use();

    /* Flat modulo allocator noise: orders of magnitude below the leak. */
    long delta = (long)after - (long)before;
    printf("delta_ok=%d delta=%ld\n", delta < 4000 ? 1 : 0, delta < 4000 ? 0L : delta);
    return 0;
}
"#;

    // NO ASan here: its quarantine falsifies the malloc-zone block count.
    let lines = build_and_run(&cc, "r2_leakgate", &emitted, main_body, false);
    assert_eq!(
        lines,
        vec!["len_64=64", "delta_ok=1 delta=0"],
        "recursive workload leaked references (or computed the wrong value)"
    );
}
