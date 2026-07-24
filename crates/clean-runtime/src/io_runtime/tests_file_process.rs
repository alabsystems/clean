// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IO runtime: file I/O, process, environment, timers, composition.

use super::*;

// =============================================================================
// GetEnv
// =============================================================================

#[test]
fn test_getenv_existing_variable() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::GetEnv("PATH".into()));
    let val = result.expect("reading PATH should succeed");
    match val {
        IoValue::String(s) => assert!(!s.is_empty(), "PATH should not be empty"),
        other => panic!("expected String, got: {other:?}"),
    }
}

#[test]
fn test_getenv_missing_variable_returns_empty() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::GetEnv("CLEAN_DEFINITELY_NOT_SET_12345".into()));
    assert_eq!(
        result.expect("missing env var should return empty string"),
        IoValue::String(String::new())
    );
}

// =============================================================================
// CurrentDir
// =============================================================================

#[test]
fn test_current_dir_returns_nonempty_string() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::CurrentDir);
    match result.expect("currentDir should succeed") {
        IoValue::String(s) => assert!(!s.is_empty(), "cwd should not be empty"),
        other => panic!("expected String, got: {other:?}"),
    }
}

// =============================================================================
// File I/O
// =============================================================================

#[test]
fn test_write_then_read_file() {
    let dir = tempfile::tempdir().expect("should create temp dir");
    let path = dir
        .path()
        .join("test_io.txt")
        .to_str()
        .expect("path should be valid UTF-8")
        .to_owned();

    let rt = IoRuntime::new();
    let write_result = rt.execute(IoAction::WriteFile(path.clone(), "hello from clean".into()));
    assert_eq!(write_result.expect("write should succeed"), IoValue::Unit);

    let read_result = rt.execute(IoAction::ReadFile(path));
    assert_eq!(
        read_result.expect("read should succeed"),
        IoValue::String("hello from clean".into())
    );
}

#[test]
fn test_read_nonexistent_file_returns_error() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::ReadFile("/tmp/clean_no_such_file_xyz".into()));
    let err = result.expect_err("reading nonexistent file should fail");
    assert!(
        matches!(&err, IoError::FileError { path, .. } if path == "/tmp/clean_no_such_file_xyz"),
        "expected FileError, got: {err}"
    );
}

#[test]
fn test_append_file_creates_and_appends() {
    let dir = tempfile::tempdir().expect("should create temp dir");
    let path = dir
        .path()
        .join("test_append.txt")
        .to_str()
        .expect("valid UTF-8")
        .to_owned();

    let rt = IoRuntime::new();
    let r1 = rt.execute(IoAction::AppendFile(path.clone(), "hello".into()));
    assert_eq!(r1.expect("first append should succeed"), IoValue::Unit);

    let r2 = rt.execute(IoAction::AppendFile(path.clone(), " world".into()));
    assert_eq!(r2.expect("second append should succeed"), IoValue::Unit);

    let read = rt.execute(IoAction::ReadFile(path));
    assert_eq!(
        read.expect("read should succeed"),
        IoValue::String("hello world".into())
    );
}

#[test]
fn test_path_exists_true_for_existing() {
    let dir = tempfile::tempdir().expect("should create temp dir");
    let path = dir
        .path()
        .join("exists.txt")
        .to_str()
        .expect("valid UTF-8")
        .to_owned();

    let rt = IoRuntime::new();
    rt.execute(IoAction::WriteFile(path.clone(), "data".into()))
        .expect("write should succeed");

    let result = rt.execute(IoAction::PathExists(path));
    assert_eq!(
        result.expect("pathExists should succeed"),
        IoValue::Bool(true)
    );
}

#[test]
fn test_path_exists_false_for_missing() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::PathExists("/tmp/clean_no_such_path_xyz".into()));
    assert_eq!(
        result.expect("pathExists should succeed"),
        IoValue::Bool(false)
    );
}

#[test]
fn test_read_dir_lists_files_sorted() {
    let dir = tempfile::tempdir().expect("should create temp dir");
    let base = dir.path().to_str().expect("valid UTF-8").to_owned();

    let rt = IoRuntime::new();
    for name in &["cherry.txt", "apple.txt", "banana.txt"] {
        let p = dir
            .path()
            .join(name)
            .to_str()
            .expect("valid UTF-8")
            .to_owned();
        rt.execute(IoAction::WriteFile(p, "content".into()))
            .expect("write should succeed");
    }

    let result = rt.execute(IoAction::ReadDir(base));
    let list = result.expect("readDir should succeed");
    match list {
        IoValue::List(entries) => {
            let names: Vec<&str> = entries
                .iter()
                .map(|e| match e {
                    IoValue::String(s) => s.as_str(),
                    _ => panic!("expected String entries"),
                })
                .collect();
            assert_eq!(names, vec!["apple.txt", "banana.txt", "cherry.txt"]);
        }
        other => panic!("expected List, got: {other:?}"),
    }
}

#[test]
fn test_remove_file_deletes() {
    let dir = tempfile::tempdir().expect("should create temp dir");
    let path = dir
        .path()
        .join("to_remove.txt")
        .to_str()
        .expect("valid UTF-8")
        .to_owned();

    let rt = IoRuntime::new();
    rt.execute(IoAction::WriteFile(path.clone(), "data".into()))
        .expect("write should succeed");

    let exists = rt.execute(IoAction::PathExists(path.clone()));
    assert_eq!(exists.expect("should exist"), IoValue::Bool(true));

    let rm = rt.execute(IoAction::RemoveFile(path.clone()));
    assert_eq!(rm.expect("remove should succeed"), IoValue::Unit);

    let gone = rt.execute(IoAction::PathExists(path));
    assert_eq!(gone.expect("should not exist"), IoValue::Bool(false));
}

#[test]
fn test_remove_nonexistent_file_returns_error() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::RemoveFile("/tmp/clean_no_such_remove_xyz".into()));
    assert!(result.is_err(), "removing nonexistent file should fail");
}

// =============================================================================
// Process
// =============================================================================

#[test]
fn test_process_output_captures_stdout() {
    let rt = IoRuntime::new();
    let action = IoAction::ProcessOutput {
        cmd: "echo".into(),
        args: vec!["hello from process".into()],
    };
    let result = rt.execute(action).expect("echo should succeed");

    match result {
        IoValue::Pair(exit_code, inner) => {
            assert_eq!(*exit_code, IoValue::Int(0), "exit code should be 0");
            match *inner {
                IoValue::Pair(stdout, _stderr) => {
                    let s = match *stdout {
                        IoValue::String(s) => s,
                        other => panic!("expected String stdout, got: {other:?}"),
                    };
                    assert!(
                        s.contains("hello from process"),
                        "stdout should contain the echo output: {s}"
                    );
                }
                other => panic!("expected Pair(stdout, stderr), got: {other:?}"),
            }
        }
        other => panic!("expected Pair(exitCode, ...), got: {other:?}"),
    }
}

#[test]
fn test_process_output_nonexistent_command() {
    let rt = IoRuntime::new();
    let action = IoAction::ProcessOutput {
        cmd: "clean_no_such_command_xyz".into(),
        args: vec![],
    };
    let result = rt.execute(action);
    let err = result.expect_err("nonexistent command should fail");
    assert!(
        matches!(&err, IoError::ProcessError { cmd, .. } if cmd == "clean_no_such_command_xyz"),
        "expected ProcessError, got: {err}"
    );
}

#[test]
fn test_process_exit_returns_error() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::ProcessExit(0));
    let err = result.expect_err("process exit should produce error");
    assert!(
        matches!(&err, IoError::ProcessExit(0)),
        "expected ProcessExit(0), got: {err}"
    );
}

#[test]
fn test_process_exit_nonzero() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::ProcessExit(1));
    let err = result.expect_err("process exit should produce error");
    assert!(
        matches!(&err, IoError::ProcessExit(1)),
        "expected ProcessExit(1), got: {err}"
    );
}

// =============================================================================
// Timers
// =============================================================================

#[test]
fn test_mono_ms_now_returns_nat() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::MonoMsNow);
    match result.expect("monoMsNow should succeed") {
        IoValue::Nat(_) => {}
        other => panic!("expected Nat, got: {other:?}"),
    }
}

#[test]
fn test_mono_nanos_now_returns_nat() {
    let rt = IoRuntime::new();
    let result = rt.execute(IoAction::MonoNanosNow);
    match result.expect("monoNanosNow should succeed") {
        IoValue::Nat(_) => {}
        other => panic!("expected Nat, got: {other:?}"),
    }
}

#[test]
fn test_mono_nanos_gte_mono_ms() {
    let rt = IoRuntime::new();
    let ms = match rt.execute(IoAction::MonoMsNow).expect("ms should succeed") {
        IoValue::Nat(n) => n,
        _ => panic!("expected Nat"),
    };
    let ns = match rt
        .execute(IoAction::MonoNanosNow)
        .expect("ns should succeed")
    {
        IoValue::Nat(n) => n,
        _ => panic!("expected Nat"),
    };
    assert!(ns >= ms, "nanos ({ns}) should be >= millis ({ms})");
}

// =============================================================================
// Complex composition
// =============================================================================

#[test]
fn test_complex_io_chain() {
    let rt = IoRuntime::new();
    let action = io_seq(
        IoAction::PrintLn("start".into()),
        io_bind(IoAction::GetEnv("PATH".into()), |path_val| {
            io_seq(
                IoAction::PrintLn("got PATH".into()),
                IoAction::Pure(path_val),
            )
        }),
    );
    let result = rt.execute(action);
    match result.expect("complex chain should succeed") {
        IoValue::String(s) => assert!(!s.is_empty(), "PATH should be non-empty"),
        other => panic!("expected String, got: {other:?}"),
    }
    assert_eq!(rt.stdout_output(), vec!["start", "got PATH"]);
}

#[test]
fn test_write_read_in_monadic_chain() {
    let dir = tempfile::tempdir().expect("should create temp dir");
    let path = dir
        .path()
        .join("chain_test.txt")
        .to_str()
        .expect("valid UTF-8")
        .to_owned();

    let rt = IoRuntime::new();
    let p1 = path.clone();
    let p2 = path;
    let action = io_bind(IoAction::WriteFile(p1, "chain data".into()), move |_| {
        io_bind(IoAction::ReadFile(p2), |content| {
            IoAction::PrintLn(format!(
                "read: {}",
                if let IoValue::String(s) = &content {
                    s.as_str()
                } else {
                    "?"
                }
            ))
        })
    });
    let result = rt.execute(action);
    assert_eq!(result.expect("chain should succeed"), IoValue::Unit);
    assert_eq!(rt.stdout_output(), vec!["read: chain data"]);
}
