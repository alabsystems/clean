// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end integration tests for the compiler pipeline.
//!
//! Tests the full pipeline: LCNF → mono → optimize → IR → boxing → emit_c.
//! Optionally compiles emitted C with a system C compiler against clean_runtime.
//!
//! Part of #1340 — compiler pipeline end-to-end integration test.

mod runtime_fixture;

use clean_compiler::boxing::explicit_boxing_with_config;
use clean_compiler::emit_c::{emit_c_with_config, CEmitConfig};
use clean_compiler::lcnf::{Arg, Code, Decl, LetDecl, LetValue, Param};
use clean_compiler::pass_manager::{compile_lcnf_decls, PipelineConfig};
use clean_compiler::rc;
use clean_compiler::to_ir::to_ir;
use clean_compiler::to_lcnf::constant_to_decl;
use clean_compiler::to_mono::to_mono;
use clean_compiler::{BoxingConfig, OptConfig, RCConfig};
use clean_kernel::env::Declaration;
use clean_kernel::{Environment, Expr, FVarId, Name};
use runtime_fixture::MaterializedRuntime;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Full pipeline: LCNF → mono → optimize → RC → IR → boxing → emit_c.
///
/// Returns the emitted C code string.
fn run_pipeline(decls: &[Decl]) -> String {
    let env = Environment::default();

    // Stage 1: Monomorphize
    let mono_decls: Vec<Decl> = decls.iter().map(|d| to_mono(d, &env)).collect();

    // Stage 2: Optimize (default config)
    let opt_config = OptConfig::default();
    let opt_decls: Vec<Decl> = mono_decls
        .iter()
        .map(|d| clean_compiler::optimize(d, &opt_config))
        .collect();

    // Stage 3: RC transform (borrow inference + reset/reuse + RC insertion + expand)
    let rc_config = RCConfig::default();
    let rc_decls = rc::transform(&opt_decls, &rc_config);

    // Stage 4: Lower to IR
    let ir_decls = to_ir(&rc_decls).expect("RC declarations should lower to IR");

    // Stage 5: Explicit boxing
    let boxed = explicit_boxing_with_config(&ir_decls, &BoxingConfig::default());

    // Stage 6: Emit C
    let config = CEmitConfig {
        check_ir: true,
        ..Default::default()
    };
    emit_c_with_config(&boxed, config).expect("emit_c should succeed for valid pipeline output")
}

// Part of #1340: identity function through full pipeline
#[test]
fn test_pipeline_identity_function() {
    // def id (x : Nat) : Nat := return x
    let decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );

    let c_code = run_pipeline(&[decl]);

    // Verify function definition exists
    assert!(
        c_code.contains("l_id("),
        "id function should be emitted: {c_code}"
    );
    // Verify it takes an argument (clean_obj* parameter)
    assert!(
        c_code.contains("clean_obj*"),
        "id should have clean_obj* params: {c_code}"
    );
}

// Part of #1340: constant literal through full pipeline
#[test]
fn test_pipeline_constant_literal() {
    // def const42 : Nat :=
    //   let _1 := 42
    //   return _1
    let decl = Decl::new(
        name("const42"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(0), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let c_code = run_pipeline(&[decl]);

    assert!(
        c_code.contains("l_const42("),
        "const42 function should be emitted: {c_code}"
    );
    // The literal 42 should appear somewhere (as clean_box(42) or similar)
    assert!(
        c_code.contains("42"),
        "literal 42 should appear in output: {c_code}"
    );
}

// Part of #1340: function application through full pipeline
#[test]
fn test_pipeline_closure_application() {
    // def apply_f (f : Nat → Nat) (x : Nat) : Nat :=
    //   let _1 := f x
    //   return _1
    let decl = Decl::new(
        name("apply_f"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("f"), nat_type()),
            Param::new(fvar(1), name("x"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let c_code = run_pipeline(&[decl]);

    assert!(
        c_code.contains("clean_apply_1("),
        "single-arg closure should use clean_apply_1: {c_code}"
    );
}

// Part of #1340: multiple declarations through pipeline
#[test]
fn test_pipeline_multiple_decls() {
    let id_decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );

    let const42_decl = Decl::new(
        name("const42"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(0), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let c_code = run_pipeline(&[id_decl, const42_decl]);

    assert!(
        c_code.contains("l_id("),
        "id should be in multi-decl output: {c_code}"
    );
    assert!(
        c_code.contains("l_const42("),
        "const42 should be in multi-decl output: {c_code}"
    );
}

// Part of #1340: emitted C compiles with system C compiler.
//
// This test is skipped if no C compiler is available. It verifies that the
// emitted code compiles (`cc -c`, no link) against `clean_runtime.h`.
//
// The header comes from `clean_runtime::include_dir()`, which serves the
// crate's compile-time `include/` only when that directory really holds the
// embedded header and otherwise materializes the embedded copy into a cache
// directory — so this test does not depend on where `clean-runtime` was
// compiled. Measured 2026-09-15 before that change: the shared
// `target/debug` rlib had been built from a since-deleted gate-demonstration
// sandbox and this test failed with
// `fatal error: 'clean_runtime.h' file not found`.
#[test]
fn test_pipeline_c_compilation() {
    // Check if cc is available
    let cc_check = std::process::Command::new("cc").arg("--version").output();
    if cc_check.is_err() {
        eprintln!("SKIP: no C compiler found, skipping compilation test");
        return;
    }

    // Build a simple function
    let decl = Decl::new(
        name("my_id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );

    let c_code = run_pipeline(&[decl]);

    // Write emitted C to a temp file
    let tmp_dir = std::env::temp_dir().join("clean_e2e_test");
    std::fs::create_dir_all(&tmp_dir).expect("create temp dir");

    let c_file = tmp_dir.join("test_pipeline.c");
    let obj_file = tmp_dir.join("test_pipeline.o");

    // Wrap emitted code with the runtime include
    let full_c = format!("#include \"clean_runtime.h\"\n\n{c_code}\n");
    std::fs::write(&c_file, &full_c).expect("write C file");

    // A directory holding the header this binary's clean-runtime embeds,
    // wherever that crate was compiled from (see the test comment above).
    let include_dir = clean_runtime::include_dir();

    // Compile to object file (no linking — we just verify it compiles)
    let output = std::process::Command::new("cc")
        .arg("-c")
        .arg("-Wall")
        .arg("-Werror")
        .arg("-o")
        .arg(&obj_file)
        .arg(&c_file)
        .arg(format!("-I{}", include_dir.display()))
        .output()
        .expect("run cc");

    // cleanup
    let _ = std::fs::remove_file(&c_file);
    let _ = std::fs::remove_file(&obj_file);
    let _ = std::fs::remove_dir(&tmp_dir);

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("C compilation failed!\n\nEmitted C:\n{full_c}\n\ncc stderr:\n{stderr}");
    }
}

// Part of #1340: closure application includes RC operations after RC pass
#[test]
fn test_pipeline_rc_operations_emitted() {
    // A function that uses its argument twice needs inc/dec.
    // def use_twice (f : Nat → Nat) (x : Nat) : Nat :=
    //   let _1 := f x
    //   let _2 := f x   -- second use of f and x
    //   return _2
    let decl = Decl::new(
        name("use_twice"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("f"), nat_type()),
            Param::new(fvar(1), name("x"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_2"),
                    nat_type(),
                    LetValue::FVar {
                        fvar: fvar(0),
                        args: vec![Arg::FVar(fvar(1))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
        false,
    );

    let c_code = run_pipeline(&[decl]);

    // With RC, multi-use variables should have clean_inc calls
    // (The RC pass inserts inc before second use of owned params)
    assert!(
        c_code.contains("clean_inc(") || c_code.contains("clean_dec("),
        "RC pass should insert inc/dec for multi-use args: {c_code}"
    );
}

// The `let`-in-VALUE-position family CLAUDE.md's compiler paragraph records
// as the third refusal, run END TO END at `-O0` — `OptConfig::minimal()`, the
// production default of `clean run` — where `simp_value`'s copy propagation
// does not run. So the zero-argument alias `to_lcnf` mints for `outer :=
// inner` reaches `to_ir` and must survive as the pure rename it gives it, not
// as a `clean_apply_0(inner)` whose correctness rested on the runtime's
// non-closure identity. The unit pins beside `expr_to_let_value` assert the
// LCNF and IR shapes; this is the execution they lacked (CLAUDE.md: "it
// landed unverified and the risk it named paid off").
#[test]
fn test_let_in_value_position_runs_at_opt_level_0() {
    if std::process::Command::new("cc")
        .arg("--version")
        .output()
        .is_err()
    {
        eprintln!("SKIP: no C compiler found, skipping execution test");
        return;
    }

    // def aliasChain : Nat := let outer : Nat := (let inner : Nat := 7; inner); outer
    let mut env = Environment::with_prelude();
    let inner = Expr::let_named(
        name("inner"),
        nat_type(),
        Expr::nat_lit(7),
        Expr::bvar(0),
        false,
    );
    let outer = Expr::let_named(name("outer"), nat_type(), inner, Expr::bvar(0), false);
    env.add_decl(Declaration::Definition {
        name: name("aliasChain"),
        level_params: vec![],
        type_: nat_type(),
        value: outer,
        is_reducible: true,
    })
    .expect("the kernel accepts the definition");
    let info = env
        .get_const(&name("aliasChain"))
        .expect("the definition is registered");
    let decl = constant_to_decl(&env, info)
        .expect("the definition lowers to L5CNF")
        .expect("the definition is compilable");

    let pipeline = PipelineConfig {
        opt: OptConfig::minimal(),
        ..PipelineConfig::default()
    };
    let artifacts =
        compile_lcnf_decls(&[decl], &env, &pipeline).expect("the pipeline compiles it at -O0");
    let c_code = emit_c_with_config(
        &artifacts.boxed_ir_decls,
        CEmitConfig {
            check_ir: true,
            ..Default::default()
        },
    )
    .expect("emit_c succeeds");
    assert!(
        !c_code.contains("clean_apply_0("),
        "the alias must lower as a rename, never a zero-argument closure call: {c_code}"
    );

    // Embedded runtime, not a compile-time path (see runtime_fixture.rs).
    let runtime = MaterializedRuntime::materialize();
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("alias_chain.c");
    let binary = dir.path().join("alias_chain");
    std::fs::write(
        &source,
        format!(
            "#include \"clean_runtime.h\"\n#include <stdio.h>\n{c_code}\n\
             int main(void) {{\n    clean_runtime_init();\n    clean_obj* r = l_aliasChain();\n    \
             printf(\"%zu\\n\", (size_t)clean_unbox(r));\n    clean_runtime_finalize();\n    return 0;\n}}\n"
        ),
    )
    .expect("write source");
    let compile = std::process::Command::new("cc")
        .arg("-o")
        .arg(&binary)
        .arg(&source)
        .arg(runtime.c_source())
        .arg(format!("-I{}", runtime.include_dir().display()))
        .arg("-lm")
        .arg("-std=c11")
        .output()
        .expect("spawn cc");
    assert!(
        compile.status.success(),
        "cc failed:\n{}\n\nEmitted C:\n{c_code}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let run = std::process::Command::new(&binary)
        .output()
        .expect("run alias_chain");
    assert!(
        run.status.success(),
        "alias_chain exited nonzero:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        "7",
        "`let outer := (let inner := 7; inner); outer` must compute 7 at -O0"
    );
}
