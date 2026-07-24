// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the IO bridge (Expr -> IoAction translation and execution).

use super::*;
use clean_kernel::level::Level;
use clean_kernel::name::Name;

// -- Helpers: build IO expressions as the kernel would after WHNF --

fn io_println_expr(msg: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("IO.println"), vec![]),
        Expr::str_lit(msg),
    )
}

fn io_pure_expr(val: Expr) -> Expr {
    let type_arg = Expr::sort(Level::succ(Level::zero()));
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("IO.pure"), vec![]), type_arg),
        val,
    )
}

fn io_getline_expr() -> Expr {
    Expr::const_(Name::from_string("IO.getLine"), vec![])
}

fn io_getenv_expr(name: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("IO.getEnv"), vec![]),
        Expr::str_lit(name),
    )
}

fn io_mono_ms_now_expr() -> Expr {
    Expr::const_(Name::from_string("IO.monoMsNow"), vec![])
}

fn io_current_dir_expr() -> Expr {
    Expr::const_(Name::from_string("IO.currentDir"), vec![])
}

fn io_mono_nanos_now_expr() -> Expr {
    Expr::const_(Name::from_string("IO.monoNanosNow"), vec![])
}

fn io_path_exists_expr(path: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("IO.FS.pathExists"), vec![]),
        Expr::str_lit(path),
    )
}

fn io_read_dir_expr(path: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("IO.FS.readDir"), vec![]),
        Expr::str_lit(path),
    )
}

fn io_remove_file_expr(path: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("IO.FS.removeFile"), vec![]),
        Expr::str_lit(path),
    )
}

fn io_append_file_expr(path: &str, content: &str) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("IO.FS.appendFile"), vec![]),
            Expr::str_lit(path),
        ),
        Expr::str_lit(content),
    )
}

// -- Translation tests --

#[test]
fn test_translate_io_println() {
    let expr = io_println_expr("hello world");
    let action = expr_to_io_action(&expr).expect("should translate IO.println");
    match action {
        IoAction::PrintLn(msg) => assert_eq!(msg, "hello world"),
        _ => panic!("expected PrintLn action"),
    }
}

#[test]
fn test_translate_io_pure_nat() {
    let expr = io_pure_expr(Expr::nat_lit(42));
    let action = expr_to_io_action(&expr).expect("should translate IO.pure");
    let rt = IoRuntime::new();
    let val = rt.execute(action).expect("should execute Pure(Nat)");
    assert_eq!(val, IoValue::Nat(42));
}

#[test]
fn test_translate_io_pure_string() {
    let expr = io_pure_expr(Expr::str_lit("test"));
    let action = expr_to_io_action(&expr).expect("should translate IO.pure string");
    let rt = IoRuntime::new();
    let val = rt.execute(action).expect("should execute Pure(String)");
    assert_eq!(val, IoValue::String("test".into()));
}

#[test]
fn test_translate_io_getline() {
    let expr = io_getline_expr();
    let action = expr_to_io_action(&expr).expect("should translate IO.getLine");
    assert!(matches!(action, IoAction::GetLine));
}

#[test]
fn test_translate_io_mono_ms_now() {
    let expr = io_mono_ms_now_expr();
    let action = expr_to_io_action(&expr).expect("should translate IO.monoMsNow");
    assert!(matches!(action, IoAction::MonoMsNow));
}

#[test]
fn test_translate_io_current_dir() {
    let expr = io_current_dir_expr();
    let action = expr_to_io_action(&expr).expect("should translate IO.currentDir");
    assert!(matches!(action, IoAction::CurrentDir));
}

#[test]
fn test_translate_io_mono_nanos_now() {
    let expr = io_mono_nanos_now_expr();
    let action = expr_to_io_action(&expr).expect("should translate IO.monoNanosNow");
    assert!(matches!(action, IoAction::MonoNanosNow));
}

#[test]
fn test_translate_io_path_exists() {
    let expr = io_path_exists_expr("/tmp/some_path");
    let action = expr_to_io_action(&expr).expect("should translate IO.FS.pathExists");
    match action {
        IoAction::PathExists(p) => assert_eq!(p, "/tmp/some_path"),
        _ => panic!("expected PathExists action"),
    }
}

#[test]
fn test_translate_filepath_path_exists_alias() {
    let expr = Expr::app(
        Expr::const_(Name::from_string("System.FilePath.pathExists"), vec![]),
        Expr::str_lit("/tmp/x"),
    );
    let action = expr_to_io_action(&expr).expect("should translate System.FilePath.pathExists");
    match action {
        IoAction::PathExists(p) => assert_eq!(p, "/tmp/x"),
        _ => panic!("expected PathExists action for canonical alias"),
    }
}

#[test]
fn test_translate_io_read_dir() {
    let expr = io_read_dir_expr("/tmp");
    let action = expr_to_io_action(&expr).expect("should translate IO.FS.readDir");
    match action {
        IoAction::ReadDir(p) => assert_eq!(p, "/tmp"),
        _ => panic!("expected ReadDir action"),
    }
}

#[test]
fn test_translate_io_remove_file() {
    let expr = io_remove_file_expr("/tmp/gone");
    let action = expr_to_io_action(&expr).expect("should translate IO.FS.removeFile");
    match action {
        IoAction::RemoveFile(p) => assert_eq!(p, "/tmp/gone"),
        _ => panic!("expected RemoveFile action"),
    }
}

#[test]
fn test_translate_io_append_file() {
    let expr = io_append_file_expr("/tmp/log", "line\n");
    let action = expr_to_io_action(&expr).expect("should translate IO.FS.appendFile");
    match action {
        IoAction::AppendFile(p, c) => {
            assert_eq!(p, "/tmp/log");
            assert_eq!(c, "line\n");
        }
        _ => panic!("expected AppendFile action"),
    }
}

#[test]
fn test_translate_unrecognized_op_returns_error() {
    let expr = Expr::const_(Name::from_string("IO.nonexistent"), vec![]);
    let result = expr_to_io_action(&expr);
    assert!(result.is_err(), "unrecognized op should return error");
    match result {
        Err(IoBridgeError::UnrecognizedOp(name)) => {
            assert_eq!(name, "IO.nonexistent");
        }
        Err(other) => panic!("expected UnrecognizedOp, got: {other}"),
        Ok(_) => panic!("expected error, got Ok"),
    }
}

// -- Execution tests --

#[test]
fn test_eval_io_println_captures_output() {
    let expr = io_println_expr("hello from eval");
    let result = eval_io_expr(&expr).expect("should execute IO.println");
    assert_eq!(result.stdout, vec!["hello from eval"]);
    assert_eq!(result.value, "()");
}

#[test]
fn test_eval_io_pure_nat_returns_value() {
    let expr = io_pure_expr(Expr::nat_lit(42));
    let result = eval_io_expr(&expr).expect("should execute IO.pure");
    assert_eq!(result.value, "42");
    assert!(result.stdout.is_empty());
}

#[test]
fn test_eval_io_pure_string_returns_value() {
    let expr = io_pure_expr(Expr::str_lit("hello"));
    let result = eval_io_expr(&expr).expect("should execute IO.pure string");
    assert_eq!(result.value, "\"hello\"");
}

#[test]
fn test_eval_io_getenv_returns_string() {
    let _env = crate::test_env::lock_env();
    let _guard = crate::test_env::ScopedEnvVar::set("CLEAN_IO_TEST_VAR", "test_value_123");
    let expr = io_getenv_expr("CLEAN_IO_TEST_VAR");
    let result = eval_io_expr(&expr).expect("should execute IO.getEnv");
    assert_eq!(result.value, "\"test_value_123\"");
}

#[test]
fn test_eval_io_current_dir_returns_path() {
    let expr = io_current_dir_expr();
    let result = eval_io_expr(&expr).expect("should execute IO.currentDir");
    assert!(result.value.starts_with('"'));
    assert!(result.value.len() > 2);
}

#[test]
fn test_eval_io_mono_ms_now_returns_nat() {
    let expr = io_mono_ms_now_expr();
    let result = eval_io_expr(&expr).expect("should execute IO.monoMsNow");
    let _val: u64 = result.value.parse().expect("should be a number");
}

#[test]
fn test_eval_io_path_exists_routes_to_runtime() {
    // The current working directory always exists; pathExists must report true.
    let cwd = std::env::current_dir().expect("cwd should be available");
    let expr = io_path_exists_expr(&cwd.to_string_lossy());
    let result = eval_io_expr(&expr).expect("should execute IO.FS.pathExists");
    assert_eq!(result.value, "true");
    assert!(result.stdout.is_empty());

    // A path that should not exist reports false.
    let missing = io_path_exists_expr("/nonexistent/clean-io-bridge/definitely/missing");
    let missing_result = eval_io_expr(&missing).expect("should execute IO.FS.pathExists");
    assert_eq!(missing_result.value, "false");
}

#[test]
fn test_eval_io_mono_nanos_now_returns_nat() {
    let expr = io_mono_nanos_now_expr();
    let result = eval_io_expr(&expr).expect("should execute IO.monoNanosNow");
    let _val: u64 = result.value.parse().expect("should be a number");
}

#[test]
fn test_eval_io_append_read_remove_round_trip() {
    // Sandbox-safe filesystem round-trip in the OS temp dir.
    let mut dir = std::env::temp_dir();
    dir.push(format!("clean_io_bridge_test_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("should create temp subdir");
    let mut file = dir.clone();
    file.push("appended.txt");
    let file_str = file.to_string_lossy().into_owned();

    // appendFile creates + writes; result is Unit "()".
    let append = io_append_file_expr(&file_str, "hello");
    let append_res = eval_io_expr(&append).expect("should execute IO.FS.appendFile");
    assert_eq!(append_res.value, "()");

    // pathExists now reports true for the created file.
    let exists = io_path_exists_expr(&file_str);
    assert_eq!(
        eval_io_expr(&exists)
            .expect("should execute IO.FS.pathExists")
            .value,
        "true"
    );

    // readDir lists the directory; the appended file name appears.
    let read_dir = io_read_dir_expr(&dir.to_string_lossy());
    let dir_res = eval_io_expr(&read_dir).expect("should execute IO.FS.readDir");
    assert!(
        dir_res.value.contains("appended.txt"),
        "readDir output should list the file, got: {}",
        dir_res.value
    );

    // removeFile deletes it; result is Unit "()".
    let remove = io_remove_file_expr(&file_str);
    let remove_res = eval_io_expr(&remove).expect("should execute IO.FS.removeFile");
    assert_eq!(remove_res.value, "()");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_unsupported_process_output_not_falsely_claimed() {
    // IO.Process.output is supported by IoRuntime but is intentionally NOT
    // wired in the bridge (it takes a structured SpawnArgs record, not flat
    // string literals). Routing it must fail honestly rather than silently
    // execute a subprocess with garbage arguments.
    assert!(
        !IO_OP_NAMES.contains(&"IO.Process.output"),
        "IO.Process.output must not be claimed as a wired IO op"
    );
    let expr = Expr::const_(Name::from_string("IO.Process.output"), vec![]);
    match expr_to_io_action(&expr) {
        Err(IoBridgeError::UnrecognizedOp(name)) => assert_eq!(name, "IO.Process.output"),
        Err(other) => panic!("expected UnrecognizedOp for IO.Process.output, got: {other}"),
        Ok(_) => panic!("IO.Process.output must not translate to an IoAction"),
    }
}

#[test]
fn test_unsupported_io_throw_not_falsely_claimed() {
    // IO.throw/catch are not wired (the continuation translator discards the
    // bound error value, so an error-inspecting handler cannot be rebuilt).
    assert!(
        !IO_OP_NAMES.contains(&"IO.throw"),
        "IO.throw must not be claimed as a wired IO op"
    );
}

// -- is_io_typed structural tests --
// Note: Environment::new() stack-overflows in the clean-elab debug test
// binary. Since is_io_typed only does name matching, test the matching
// logic directly against IO_OP_NAMES.

#[test]
fn test_is_io_typed_for_io_prefixed_const() {
    let head = Name::from_string("IO.println");
    let name_str = head.to_string();
    assert!(
        IO_OP_NAMES.iter().any(|&op| name_str == op),
        "IO.println should be in IO_OP_NAMES"
    );
}

#[test]
fn test_is_io_typed_returns_false_for_non_io_const() {
    let head = Name::from_string("Nat.add");
    let name_str = head.to_string();
    assert!(
        !IO_OP_NAMES.iter().any(|&op| name_str == op),
        "Nat.add should not be in IO_OP_NAMES"
    );
}

// -- IoEvalResult display --

#[test]
fn test_io_eval_result_display_no_stdout() {
    let result = IoEvalResult {
        value: "42".into(),
        stdout: vec![],
        stderr: vec![],
    };
    assert_eq!(format!("{result}"), "42");
}

#[test]
fn test_io_eval_result_display_with_stdout() {
    let result = IoEvalResult {
        value: "()".into(),
        stdout: vec!["hello".into(), "world".into()],
        stderr: vec![],
    };
    assert_eq!(format!("{result}"), "hello\nworld\n()");
}
