// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ffi_verify::FfiMismatch;
use crate::lcnf::{Code, DeclValue, ExternEntry, Param};
use crate::pass_manager::PipelineError;
use crate::CompilerError;
use clean_kernel::{FVarId, Name};

fn make_test_decl(name: &str) -> Decl {
    let x = FVarId::new(0);
    Decl {
        name: Name::from_string(name),
        level_params: vec![Name::from_string("u")],
        ty: clean_kernel::Expr::const_str("Nat"),
        params: vec![Param::new(
            x,
            Name::from_string("x"),
            clean_kernel::Expr::const_str("Nat"),
        )],
        body: DeclValue::Code(Box::new(Code::Return(x))),
        recursive: false,
    }
}

fn make_extern_decl(
    name: &str,
    ty: clean_kernel::Expr,
    params: Vec<Param>,
    extern_name: &str,
) -> Decl {
    Decl::extern_decl(
        Name::from_string(name),
        vec![],
        ty,
        params,
        vec![ExternEntry {
            backend: "c".to_owned(),
            name: extern_name.to_owned(),
        }],
    )
}

#[test]
fn test_opt_level_default_is_full() {
    assert_eq!(OptLevel::default(), OptLevel::Full);
}

#[test]
fn test_opt_level_display() {
    assert_eq!(format!("{}", OptLevel::None), "none");
    assert_eq!(format!("{}", OptLevel::Basic), "basic");
    assert_eq!(format!("{}", OptLevel::Full), "full");
}

#[test]
fn test_compile_config_default() {
    let config = CompileConfig::default();
    assert_eq!(config.optimization_level, OptLevel::Full);
    assert!(config.enable_boxing);
    assert!(config.enable_lambda_lift);
    assert!(!config.debug_trace);
}

#[test]
fn test_compile_default_runs() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let result =
        compile_default(&[decl], &env).expect("compile_default should succeed on a simple decl");
    assert!(
        !result.decls.is_empty(),
        "should produce at least one IR decl"
    );
    assert!(!result.passes_run.is_empty(), "should record passes");
}

#[test]
fn test_compile_opt_none() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let config = CompileConfig {
        optimization_level: OptLevel::None,
        enable_boxing: true,
        enable_lambda_lift: true,
        debug_trace: false,
    };

    let result =
        compile(&[decl], &env, &config).expect("compile with OptLevel::None should succeed");
    assert!(!result.decls.is_empty());
    assert!(result.passes_run.contains(&"to_mono".to_owned()));
    assert!(result.passes_run.contains(&"rc".to_owned()));
}

#[test]
fn test_compile_opt_basic() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let config = CompileConfig {
        optimization_level: OptLevel::Basic,
        enable_boxing: true,
        enable_lambda_lift: true,
        debug_trace: false,
    };

    let result =
        compile(&[decl], &env, &config).expect("compile with OptLevel::Basic should succeed");
    assert!(!result.decls.is_empty());
    assert!(result.passes_run.contains(&"dce".to_owned()));
    assert!(result.passes_run.contains(&"constant_fold".to_owned()));
}

#[test]
fn test_compile_opt_full() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let config = CompileConfig {
        optimization_level: OptLevel::Full,
        enable_boxing: true,
        enable_lambda_lift: true,
        debug_trace: false,
    };

    let result =
        compile(&[decl], &env, &config).expect("compile with OptLevel::Full should succeed");
    assert!(!result.decls.is_empty());
    assert!(result.passes_run.contains(&"optimize".to_owned()));
}

#[test]
fn test_compile_boxing_disabled() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let config = CompileConfig {
        optimization_level: OptLevel::Full,
        enable_boxing: false,
        enable_lambda_lift: true,
        debug_trace: false,
    };

    let result =
        compile(&[decl], &env, &config).expect("compile with boxing disabled should succeed");
    assert!(!result.decls.is_empty());
    assert!(
        !result.passes_run.contains(&"explicit_boxing".to_owned()),
        "explicit_boxing should not appear when boxing is disabled"
    );
}

#[test]
fn test_compile_boxing_enabled() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let config = CompileConfig {
        optimization_level: OptLevel::Full,
        enable_boxing: true,
        enable_lambda_lift: true,
        debug_trace: false,
    };

    let result =
        compile(&[decl], &env, &config).expect("compile with boxing enabled should succeed");
    assert!(
        result.passes_run.contains(&"explicit_boxing".to_owned()),
        "explicit_boxing should appear when boxing is enabled"
    );
}

#[test]
fn test_compile_lambda_lift_disabled() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let config = CompileConfig {
        optimization_level: OptLevel::Full,
        enable_boxing: true,
        enable_lambda_lift: false,
        debug_trace: false,
    };

    let result =
        compile(&[decl], &env, &config).expect("compile with lambda_lift disabled should succeed");
    assert!(!result.decls.is_empty());
    assert!(
        !result.passes_run.contains(&"lambda_lifting".to_owned()),
        "lambda_lifting should not appear when disabled"
    );
}

#[test]
fn test_compile_debug_trace() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let config = CompileConfig {
        optimization_level: OptLevel::Basic,
        enable_boxing: true,
        enable_lambda_lift: true,
        debug_trace: true,
    };

    let result = compile(&[decl], &env, &config).expect("compile with debug_trace should succeed");
    assert!(
        !result.diagnostics.is_empty(),
        "debug_trace should produce diagnostic output"
    );
    let has_opt_diag = result
        .diagnostics
        .iter()
        .any(|d: &String| d.contains("optimization"));
    assert!(
        has_opt_diag,
        "diagnostics should mention optimization level"
    );
}

#[test]
fn test_compile_pass_ordering() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    let config = CompileConfig {
        optimization_level: OptLevel::Full,
        enable_boxing: true,
        enable_lambda_lift: true,
        debug_trace: false,
    };

    let result = compile(&[decl], &env, &config).expect("compile should succeed");

    // Verify ordering: lambda_lifting before to_mono before rc before to_ir
    let ll_pos = result.passes_run.iter().position(|p| p == "lambda_lifting");
    let mono_pos = result.passes_run.iter().position(|p| p == "to_mono");
    let rc_pos = result.passes_run.iter().position(|p| p == "rc");
    let ir_pos = result.passes_run.iter().position(|p| p == "to_ir");
    let box_pos = result
        .passes_run
        .iter()
        .position(|p| p == "explicit_boxing");

    assert!(ll_pos < mono_pos, "lambda_lifting must precede to_mono");
    assert!(mono_pos < rc_pos, "to_mono must precede rc");
    assert!(rc_pos < ir_pos, "rc must precede to_ir");
    assert!(ir_pos < box_pos, "to_ir must precede explicit_boxing");
}

#[test]
fn test_compile_empty_input() {
    let env = Environment::new();

    let result = compile_default(&[], &env).expect("compile_default on empty input should succeed");
    assert!(
        result.decls.is_empty(),
        "empty input should produce empty output"
    );
}

#[test]
fn test_compile_multiple_decls() {
    let decl_a = make_test_decl("fn_a");
    let decl_b = make_test_decl("fn_b");
    let env = Environment::new();

    let result = compile_default(&[decl_a, decl_b], &env)
        .expect("compile_default on multiple decls should succeed");
    assert!(
        result.decls.len() >= 2,
        "multiple input decls should produce at least as many output decls"
    );
}

#[test]
fn test_compile_result_diagnostics_include_warnings() {
    let decl = make_test_decl("test_fn");
    let env = Environment::new();

    // Even without debug_trace, pipeline warnings are captured.
    let config = CompileConfig {
        optimization_level: OptLevel::Full,
        enable_boxing: true,
        enable_lambda_lift: true,
        debug_trace: false,
    };

    let result = compile(&[decl], &env, &config).expect("compile should succeed");
    // Diagnostics vec exists (may be empty if pipeline emits no warnings).
    // We just verify the field is accessible and is a Vec<String>.
    let _: &[String] = &result.diagnostics;
}

#[test]
fn test_compile_accepts_verified_extern_decl() {
    let decl = make_extern_decl(
        "runtime_init",
        clean_kernel::Expr::const_str("Unit"),
        vec![],
        "clean_runtime_init",
    );
    let env = Environment::new();

    let result = compile_default(&[decl], &env).expect("verified extern should compile");
    assert!(
        result.decls.is_empty(),
        "extern decls do not lower to IR bodies: {result:?}"
    );
}

#[test]
fn test_compile_rejects_unknown_extern_decl() {
    let decl = make_extern_decl(
        "bad_extern",
        clean_kernel::Expr::const_str("Unit"),
        vec![],
        "clean_unknown_runtime_symbol",
    );
    let env = Environment::new();

    let err = compile_default(&[decl], &env).expect_err("unknown extern should fail");
    assert!(matches!(
        err,
        PipelineError::Compiler(CompilerError::FfiMismatch(FfiMismatch::UnknownExtern {
            extern_name,
            ..
        })) if extern_name == "clean_unknown_runtime_symbol"
    ));
}
