// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BEHAVIORAL pins for the three bounded lowering rungs, verified end-to-end
//! (kernel prelude value -> LCNF -> full pipeline -> emitted C -> host `cc` ->
//! executed against the real clean runtime), with a malloc/free NET-BLOCK
//! COUNTER (no ASan required) so a leak or a refcount double-free shows up as a
//! non-flat block count / abort:
//!
//!   * Rung 1 — `MAX_RUNTIME_APPLY_ARGS` raised 8 -> 32: the wide
//!     algebraic-hierarchy recursors now lower. `Semiring.recOn` (15-field arm,
//!     positional `clean_apply_15`), `Ring.recOn` (17) and `CommRing.recOn`
//!     (18), `DivisionRing.recOn` (20), and `Field.recOn` (21) — the latter four
//!     via the variadic `clean_apply_n` -> `clean_invoke` path — are driven over
//!     a HEAP-capturing scrutinee both EXCLUSIVE (rc 1) and SHARED-twice (rc 2).
//!     The shared case is the UAF-history guard: it only stays net-block-flat if
//!     every projected field is `inc`'d before the wide apply consumes it (so
//!     the surviving shared ctor still owns its fields).
//!   * Rung 2 — over-applied dependent `Bool.rec` (`Nat.decLe`/`Nat.decLt`)
//!     lowers to a two-alt `Bool` switch: the VALUES are checked.
//!   * Rung 3a — `instInsertList`'s partially-applied `List.cons` ctor
//!     eta-expands to a closure: it builds `List.cons 7 []`.
//!
//! Skips when no C compiler is found.

#![cfg(feature = "round-trip-compile")]

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_compiler::emit_c::{emit_c_with_config, CEmitConfig};
use clean_compiler::mangle::mangle_name;
use clean_compiler::pass_manager::{compile_lcnf_decls, PipelineConfig};
use clean_compiler::to_lcnf::constant_to_decl;
use clean_compiler::Decl;
use clean_kernel::{Environment, Expr, ExprVisitor, LevelVec, Name};

/// Primitive symbols the real `clean` native build provides as runtime shims
/// rather than compiling from source (so their proof-carrying source closures —
/// e.g. `Nat.decEq`'s validity chain, which references the `Nat.le` PROP — are
/// never emitted, and no erased-Prop symbol dangles at link). Mirrors the
/// closure driver in `census`/`emit`-side tooling; the four arithmetic ones are
/// backed by shims in [`prologue`].
const DENYLIST: &[&str] = &[
    "l_Nat_add",
    "l_Nat_mul",
    "l_Nat_sub",
    "l_Nat_div",
    "l_Nat_mod",
    "l_toString",
    "l_Nat_decEq",
    "l_true",
    "l_false",
    "l_Not",
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
    "l_IO",
    "l_Unit_unit",
    "l_IO_println",
    "l_IO_print",
    "l_IO_eprintln",
    "l_Pure_pure",
    "l_Bind_bind",
    "l_IO_bind",
];

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

/// The compilable dependency closure of `roots` (the `clean compile` BFS:
/// per-declaration probe, extern-drop on failure), through the full pipeline.
fn compile_closure(env: &Environment, roots: &[&str]) -> Vec<clean_compiler::ir::IRDecl> {
    let pipeline = PipelineConfig::default();
    let mut verdict: HashMap<Name, Option<Decl>> = HashMap::new();
    let mut probe = |env: &Environment, name: &Name| -> Option<Decl> {
        if let Some(v) = verdict.get(name) {
            return v.clone();
        }
        let v = (|| {
            let info = env.get_const(name)?;
            if DENYLIST.contains(&mangle_name(name).as_str()) {
                return None;
            }
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

fn emit(decls: &[clean_compiler::ir::IRDecl]) -> String {
    emit_c_with_config(
        decls,
        CEmitConfig {
            check_ir: false,
            ..CEmitConfig::default()
        },
    )
    .expect("emit C")
}

/// A driver prologue that intercepts the runtime's `malloc`/`free` with a
/// net-block counter, then pulls the whole runtime in as one TU (so the
/// `static inline` allocators are counted too) and defines the denylist shims
/// + heap/ctor/minor helpers the drivers need.
fn prologue() -> String {
    let runtime = runtime_c_source();
    let mut s = format!(
        r#"#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <math.h>
static long g_live = 0;
static void* cmalloc(size_t n){{ g_live++; return malloc(n); }}
static void  cfree(void* p){{ if(p){{ g_live--; }} free(p); }}
#define malloc(n) cmalloc(n)
#define free(p) cfree(p)
#include "{}"
#undef malloc
#undef free
clean_obj* l_Nat_add(clean_obj* a, clean_obj* b){{ return clean_box(clean_unbox(a)+clean_unbox(b)); }}
clean_obj* l_Nat_sub(clean_obj* a, clean_obj* b){{ size_t x=clean_unbox(a),y=clean_unbox(b); return clean_box(x<y?0:x-y); }}
clean_obj* l_Nat_mul(clean_obj* a, clean_obj* b){{ return clean_box(clean_unbox(a)*clean_unbox(b)); }}
clean_obj* l_Nat_decEq(clean_obj* a, clean_obj* b){{ return clean_box(clean_unbox(a)==clean_unbox(b)?1:0); }}
/* Legacy extern-boundary stubs for the erased Prop-head INDUCTIVES `Nat.le` /
 * `Eq` — valueless heads a debug build (lighter DCE than release) can leave
 * referenced in dead proof-helper code the decidability functions never reach
 * at runtime (their runtime path is `ble` + tag switch). Kept defensively;
 * stubbed to a harmless erased immediate; never invoked. `Bool.noConfusionType`
 * is deliberately NOT stubbed here anymore: the type-level-machinery erasure now
 * emits a faithful self-contained stub for it INSIDE the closure, so a harness
 * definition would double-define the symbol (conflicting-types link error). */
clean_obj* l_Nat_le(clean_obj* a, clean_obj* b){{ (void)a;(void)b; return clean_box(0); }}
clean_obj* l_Eq(clean_obj* a, clean_obj* b, clean_obj* c){{ (void)a;(void)b;(void)c; return clean_box(0); }}
clean_obj* l_Not(clean_obj* a){{ (void)a; return clean_box(0); }}
static clean_obj* box_heap(size_t v){{ return clean_alloc_ctor(0, 1, 0, clean_box(v)); }}
"#,
        runtime.display()
    );
    // Arity-N minors (consume their N owned args, return a marker) and N-field
    // heap ctor builders, for the supported algebraic-hierarchy frontier.
    for n in [15usize, 17, 18, 20, 21] {
        let params = (0..n)
            .map(|i| format!("clean_obj* a{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let decs = (0..n)
            .map(|i| format!("clean_dec(a{i});"))
            .collect::<Vec<_>>()
            .join(" ");
        s.push_str(&format!(
            "static clean_obj* min{n}({params}) {{ {decs} return clean_box({n}); }}\n"
        ));
        let fields = (0..n)
            .map(|i| format!("box_heap({i})"))
            .collect::<Vec<_>>()
            .join(", ");
        s.push_str(&format!(
            "static clean_obj* mkctor{n}(void) {{ return clean_alloc_ctor(0, {n}, 0, {fields}); }}\n"
        ));
    }
    s
}

/// Compile `<prologue><emitted><main_body>` as ONE translation unit (the
/// runtime is `#include`d by the prologue) and run it; returns stdout lines.
fn compile_and_run(cc: &str, emitted: &str, main_body: &str) -> Vec<String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("driver.c");
    let binary = dir.path().join("driver");
    std::fs::write(
        &source,
        format!("{}\n{}\n{}", prologue(), emitted, main_body),
    )
    .expect("write source");
    let compile = Command::new(cc)
        .arg("-O1")
        .arg("-o")
        .arg(&binary)
        .arg(&source)
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
        "driver exited nonzero (double-free / abort?):\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8_lossy(&run.stdout)
        .lines()
        .map(str::to_string)
        .collect()
}

/// Rung 1: the wide algebraic-hierarchy recursors lower and are memory-safe
/// (net-block-flat) over a heap scrutinee, EXCLUSIVE and SHARED-twice.
#[test]
fn test_rung1_wide_recursors_leak_free() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("e2e skipped: no C compiler found");
        return;
    };
    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    let decls = compile_closure(
        &env,
        &[
            "Semiring.recOn",
            "Ring.recOn",
            "CommRing.recOn",
            "DivisionRing.recOn",
            "Field.recOn",
        ],
    );
    let emitted = emit(&decls);

    // For each width: build a heap ctor scrutinee + an arity-width minor, run
    // the recursor EXCLUSIVE (rc 1) and SHARED-twice (rc 2), and report whether
    // the net heap-block count returned to its entry value.
    let main_body = r#"
static int excl(const char* tag, clean_obj* (*rec)(clean_obj*,clean_obj*,clean_obj*,clean_obj*),
                clean_obj* (*mk)(void), void* minfn, int arity) {
    long before = g_live;
    clean_obj* minor = clean_alloc_closure(minfn, arity, 0);
    clean_obj* scrut = mk();                 /* rc = 1 */
    clean_dec(rec(clean_box(0), clean_box(0), scrut, minor));
    return g_live == before;
}
static int shared(const char* tag, clean_obj* (*rec)(clean_obj*,clean_obj*,clean_obj*,clean_obj*),
                  clean_obj* (*mk)(void), void* minfn, int arity) {
    long before = g_live;
    clean_obj* minor = clean_alloc_closure(minfn, arity, 0);
    clean_inc(minor);
    clean_obj* scrut = mk();
    clean_inc(scrut);                        /* rc = 2 (SHARED) */
    clean_dec(rec(clean_box(0), clean_box(0), scrut, minor));
    clean_dec(rec(clean_box(0), clean_box(0), scrut, minor));
    return g_live == before;
}
int main(void){
    printf("s15 %d %d\n", excl("s",l_Semiring_recOn,mkctor15,(void*)min15,15), shared("s",l_Semiring_recOn,mkctor15,(void*)min15,15));
    printf("r17 %d %d\n", excl("r",l_Ring_recOn,mkctor17,(void*)min17,17),     shared("r",l_Ring_recOn,mkctor17,(void*)min17,17));
    printf("c18 %d %d\n", excl("c",l_CommRing_recOn,mkctor18,(void*)min18,18), shared("c",l_CommRing_recOn,mkctor18,(void*)min18,18));
    printf("d20 %d %d\n", excl("d",l_DivisionRing_recOn,mkctor20,(void*)min20,20), shared("d",l_DivisionRing_recOn,mkctor20,(void*)min20,20));
    printf("f21 %d %d\n", excl("f",l_Field_recOn,mkctor21,(void*)min21,21), shared("f",l_Field_recOn,mkctor21,(void*)min21,21));
    return 0;
}
"#;
    let lines = compile_and_run(&cc, &emitted, main_body);
    assert_eq!(
        lines,
        vec!["s15 1 1", "r17 1 1", "c18 1 1", "d20 1 1", "f21 1 1",],
        "wide recursor must be net-block-flat exclusive AND shared-twice"
    );
}

/// Rung 2: the over-applied dependent `Bool.rec` lowers to a `Bool` switch that
/// computes the right decidability values.
#[test]
fn test_rung2_nat_dec_le_lt_values() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("e2e skipped: no C compiler found");
        return;
    };
    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    let decls = compile_closure(&env, &["Nat.decLe", "Nat.decLt"]);
    let emitted = emit(&decls);
    let main_body = r#"
int main(void){
    printf("le %u %u %u\n", l_Nat_decLe(clean_box(2),clean_box(5)), l_Nat_decLe(clean_box(5),clean_box(2)), l_Nat_decLe(clean_box(3),clean_box(3)));
    printf("lt %u %u %u\n", l_Nat_decLt(clean_box(2),clean_box(5)), l_Nat_decLt(clean_box(5),clean_box(2)), l_Nat_decLt(clean_box(3),clean_box(3)));
    return 0;
}
"#;
    let lines = compile_and_run(&cc, &emitted, main_body);
    assert_eq!(
        lines,
        vec!["le 1 0 1", "lt 1 0 0"],
        "decLe(n,m)=n<=m, decLt(n,m)=n<m"
    );
}

/// Rung 3a: the partially-applied `List.cons` ctor in `instInsertList`
/// eta-expands to a closure that builds `List.cons head tail`.
#[test]
fn test_rung3a_inst_insert_list_builds_cons() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("e2e skipped: no C compiler found");
        return;
    };
    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    let decls = compile_closure(&env, &["instInsertList"]);
    let emitted = emit(&decls);
    // `instInsertList _`  is the `List.cons` closure (arity 3, 1 captured type
    // param); saturating it with (7, nil) builds `List.cons 7 []` (tag 1).
    let main_body = r#"
int main(void){
    long before = g_live;
    clean_obj* ins = l_instInsertList(clean_box(0));
    clean_obj* lst = clean_apply_2(ins, clean_box(7), clean_box(0));
    printf("cons tag=%u head=%zu\n", clean_obj_tag(lst), clean_unbox(clean_ctor_get(lst, 0)));
    clean_dec(lst);
    printf("flat=%d\n", g_live == before);
    return 0;
}
"#;
    let lines = compile_and_run(&cc, &emitted, main_body);
    assert_eq!(
        lines,
        vec!["cons tag=1 head=7", "flat=1"],
        "instInsertList must build List.cons 7 [] leak-free"
    );
}
