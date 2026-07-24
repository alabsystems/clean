// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R1 BEHAVIORAL pins: recursive eliminators compiled from source
//! (`List.rec` / `Nat.rec` through the synthesized recursive function)
//! compute the right VALUES, verified end-to-end — kernel prelude value →
//! LCNF → full pipeline → emitted C → host `cc` → executed against the real
//! clean runtime — not just emit/validate success.
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

/// The compilable dependency closure of `roots` (the `clean compile` BFS:
/// per-declaration probe, extern-drop on failure), compiled through the full
/// default pipeline.
fn compile_closure(env: &Environment, roots: &[&str]) -> Vec<clean_compiler::ir::IRDecl> {
    let pipeline = PipelineConfig::default();
    let mut verdict: HashMap<Name, Option<Decl>> = HashMap::new();
    let mut probe = |env: &Environment, name: &Name| -> Option<Decl> {
        if let Some(v) = verdict.get(name) {
            return v.clone();
        }
        let v = (|| {
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
            "root {root} must compile from source (R1)"
        );
    }
    compile_lcnf_decls(&decls, env, &pipeline)
        .expect("closure compiles through the full pipeline")
        .boxed_ir_decls
}

/// Primitive denylist shims + tiny helpers the driver needs, prepended to
/// the emitted C (the real `clean` native build prepends its shim tables the
/// same way).
const SHIM_PREAMBLE: &str = r#"
#include "clean_runtime.h"
clean_obj* l_Nat_add(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) + clean_unbox(b)); }
clean_obj* l_Nat_sub(clean_obj* a, clean_obj* b) { size_t x = clean_unbox(a), y = clean_unbox(b); return clean_box(x < y ? 0 : x - y); }
clean_obj* l_Nat_mul(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) * clean_unbox(b)); }
clean_obj* l_Nat_decEq(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) == clean_unbox(b) ? 1 : 0); }
static clean_obj* test_succ(clean_obj* x) { return clean_box(clean_unbox(x) + 1); }
static clean_obj* nil(void) { return clean_box(0); }
static clean_obj* cons(size_t h, clean_obj* t) { return clean_alloc_ctor(1, 2, 0, clean_box(h), t); }
"#;

/// Behavioral differential: `List.rec` folds (length / foldl / map) and the
/// eta-shaped `Nat.rec` (`Nat.beq`) compute the same values Lean's own
/// reduction gives. `List.foldl` additionally covers the OVER-applied
/// function-building-motive spine, and `List.map` the list-building arms.
#[test]
fn test_r1_recursive_eliminators_compute_correct_values() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("e2e skipped: no C compiler found (cc/gcc/clang)");
        return;
    };

    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    let decls = compile_closure(&env, &["List.length", "List.foldl", "List.map", "Nat.beq"]);
    let emitted = emit_c_with_config(
        &decls,
        CEmitConfig {
            check_ir: false,
            ..CEmitConfig::default()
        },
    )
    .expect("emit C for the closure");

    let main_body = r#"
int main(void) {
    clean_obj* erased = clean_box(0);
    clean_obj* l = cons(10, cons(20, cons(30, nil())));
    printf("length=%zu\n", clean_unbox(l_List_length(erased, l)));
    printf("length_nil=%zu\n", clean_unbox(l_List_length(erased, nil())));
    clean_obj* addc = clean_alloc_closure((void*)l_Nat_add, 2, 0);
    clean_obj* l2 = cons(1, cons(2, cons(3, nil())));
    printf("foldl=%zu\n", clean_unbox(l_List_foldl(erased, erased, addc, clean_box(100), l2)));
    clean_obj* succc = clean_alloc_closure((void*)test_succ, 1, 0);
    clean_obj* l3 = cons(1, cons(2, cons(3, nil())));
    clean_obj* mapped = l_List_map(erased, erased, succc, l3);
    printf("map=%zu,%zu,%zu tag_end=%u\n",
        clean_unbox(clean_ctor_get(mapped, 0)),
        clean_unbox(clean_ctor_get(clean_ctor_get(mapped, 1), 0)),
        clean_unbox(clean_ctor_get(clean_ctor_get(clean_ctor_get(mapped, 1), 1), 0)),
        clean_obj_tag(clean_ctor_get(clean_ctor_get(clean_ctor_get(mapped, 1), 1), 1)));
    printf("beq_5_5=%u beq_5_6=%u beq_0_0=%u\n",
        l_Nat_beq(clean_box(5), clean_box(5)),
        l_Nat_beq(clean_box(5), clean_box(6)),
        l_Nat_beq(clean_box(0), clean_box(0)));
    return 0;
}
"#;

    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("r1_e2e.c");
    let binary = dir.path().join("r1_e2e");
    std::fs::write(
        &source,
        format!("#include <stdio.h>\n{SHIM_PREAMBLE}\n{emitted}\n{main_body}"),
    )
    .expect("write source");

    let compile = Command::new(&cc)
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

    let run = Command::new(&binary).output().expect("run r1_e2e");
    assert!(run.status.success(), "binary exited nonzero");
    let stdout = String::from_utf8_lossy(&run.stdout);
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(
        lines,
        vec![
            "length=3",
            "length_nil=0",
            "foldl=106",
            "map=2,3,4 tag_end=0",
            "beq_5_5=1 beq_5_6=0 beq_0_0=1",
        ],
        "R1 behavioral differential mismatch; full output:\n{stdout}"
    );
}
