// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end integration tests for the compiler pipeline.
//!
//! Tests the full pipeline: LCNF → mono → optimize → IR → boxing → emit_c.
//! Optionally compiles emitted C with a system C compiler against clean_runtime.
//!
//! Part of #1340 — compiler pipeline end-to-end integration test.

use clean_compiler::boxing::explicit_boxing_with_config;
use clean_compiler::emit_c::{emit_c_with_config, CEmitConfig};
use clean_compiler::lcnf::{Arg, Code, Decl, LetDecl, LetValue, Param};
use clean_compiler::rc;
use clean_compiler::to_ir::to_ir;
use clean_compiler::to_mono::to_mono;
use clean_compiler::{BoxingConfig, OptConfig, RCConfig};
use clean_kernel::{Environment, Expr, FVarId, Name};

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
// emitted code, when combined with clean_runtime.h and clean_runtime.c,
// compiles without errors.
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

    // Get the include directory from clean-runtime
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
