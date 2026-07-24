// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_compiler::emit_c::CEmitConfig;
use clean_compiler::emit_rust::RustEmitConfig;
use clean_compiler::lcnf::{Code, Decl, LetDecl, LetValue, Param};
use clean_compiler::pass_manager::{
    compile_lcnf_decls, compile_lcnf_to_c, compile_lcnf_to_rust, PipelineConfig,
};
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

#[test]
fn test_compile_lcnf_decls_exposes_all_pipeline_stages() {
    let decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );
    let env = Environment::default();

    let artifacts = compile_lcnf_decls(&[decl], &env, &PipelineConfig::default())
        .expect("pipeline should succeed for a simple identity function");

    assert_eq!(
        artifacts.mono_decls.len(),
        1,
        "monomorphization should preserve the declaration count here"
    );
    assert_eq!(
        artifacts.optimized_decls.len(),
        1,
        "batch optimization should preserve the declaration count here"
    );
    assert_eq!(
        artifacts.rc_decls.len(),
        1,
        "RC transformation should preserve the declaration count here"
    );
    assert_eq!(
        artifacts.ir_decls.len(),
        1,
        "IR lowering should emit one declaration for this identity function"
    );
    assert!(
        artifacts.boxed_ir_decls.len() >= artifacts.ir_decls.len(),
        "boxing should preserve or extend the IR declaration set"
    );
    assert!(
        artifacts.warnings.is_empty(),
        "simple identity function should not produce IR warnings: {:?}",
        artifacts.warnings
    );
}

#[test]
fn test_compile_lcnf_emitters_generate_named_functions() {
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
    let env = Environment::default();
    let pipeline = PipelineConfig::default();

    let c_code = compile_lcnf_to_c(
        std::slice::from_ref(&decl),
        &env,
        &pipeline,
        CEmitConfig {
            check_ir: true,
            ..Default::default()
        },
    )
    .expect("pipeline should emit C for a constant declaration");
    assert!(
        c_code.contains("l_const42("),
        "C emitter should generate a named function: {c_code}"
    );

    let rust_code = compile_lcnf_to_rust(
        &[decl],
        &env,
        &pipeline,
        RustEmitConfig {
            check_ir: true,
            ..Default::default()
        },
    )
    .expect("pipeline should emit Rust for a constant declaration");
    assert!(
        rust_code.contains("pub unsafe fn l_const42("),
        "Rust emitter should generate a named function: {rust_code}"
    );
}
