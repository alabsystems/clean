// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[path = "support/rustc.rs"]
mod rustc_support;

#[path = "support/artifacts.rs"]
mod artifacts;

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_compile_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "clean_kernel_expr_must_use_{test_name}_{}_{}",
        std::process::id(),
        nanos
    ))
}

fn compile_external_snippet(test_name: &str, source: &str) -> Output {
    let executable = std::env::current_exe().expect("test executable path");
    let library = artifacts::clean_kernel(&executable, "expr_must_use_api_surface")
        .expect("resolve this test's clean_kernel dependency");
    let compile_dir = temp_compile_dir(test_name);
    fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

    let source_path = compile_dir.join("snippet.rs");
    fs::write(&source_path, source).expect("snippet source should be writable");

    // TRUST OPT-OUT -- use Cargo's selected `RUSTC` so this snippet and the
    // linked crate metadata always share a compiler ABI. When that compiler is
    // Trust, disable obligation checking: the snippet proves only that the
    // `must_use` lint fires.
    // The compiler is Trust (owner directive 2026-09-28); there is no retry
    // without the opt-out.
    let run_rustc = || {
        let mut cmd = Command::new(rustc_support::cargo_rustc());
        cmd.arg("-Ztrust-verify=off");
        cmd.arg("--crate-type")
            .arg("lib")
            .arg("--edition")
            .arg("2021")
            .arg("--emit")
            .arg("metadata")
            .arg("--out-dir")
            .arg(&compile_dir)
            .arg(&source_path)
            .arg("--extern")
            .arg(format!("clean_kernel={}", library.artifact.display()));
        for directory in &library.search_dirs {
            cmd.arg("-L")
                .arg(format!("dependency={}", directory.display()));
        }
        cmd.output()
    };
    let output = run_rustc().expect("trustc should be runnable from integration tests");

    let _ = fs::remove_dir_all(&compile_dir);
    output
}

fn assert_external_compile_fails(test_name: &str, source: &str, expected_fragments: &[&str]) {
    let output = compile_external_snippet(test_name, source);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "snippet unexpectedly compiled successfully\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    for fragment in expected_fragments {
        assert!(
            stderr.contains(fragment),
            "expected rustc stderr to contain `{fragment}`\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

#[test]
fn test_expr_is_must_use_from_external_crate() {
    assert_external_compile_fails(
        "expr_must_use",
        r#"
#![deny(unused_must_use)]
use clean_kernel::Expr;

fn dropped_expr() {
    Expr::bvar(0);
}
"#,
        &[
            "unused `Expr` that must be used",
            "expressions should be inspected or passed onward",
        ],
    );
}

#[test]
fn test_level_is_must_use_from_external_crate() {
    assert_external_compile_fails(
        "level_must_use",
        r#"
#![deny(unused_must_use)]
use clean_kernel::Level;

fn dropped_level() {
    Level::zero();
}
"#,
        &[
            "unused `Level` that must be used",
            "levels should be inspected or passed onward",
        ],
    );
}

#[test]
fn test_name_constructors_are_must_use_from_external_crate() {
    assert_external_compile_fails(
        "name_must_use",
        r#"
#![deny(unused_must_use)]
use clean_kernel::Name;

fn dropped_name() {
    Name::anon();
    Name::from_string("Nat.add");
    Name::interned("Nat.succ");
}
"#,
        &[
            "unused return value of `clean_kernel::Name::anon`",
            "unused return value of `clean_kernel::Name::from_string`",
            "unused return value of `clean_kernel::Name::interned`",
        ],
    );
}

#[test]
fn test_constant_info_constructors_are_must_use_from_external_crate() {
    assert_external_compile_fails(
        "constant_info_must_use",
        r#"
#![deny(unused_must_use)]
use clean_kernel::{ConstantInfo, ConstantKind, Expr, Name, Reducibility};

fn dropped_constant_info() {
    ConstantInfo::new(Name::anon(), vec![], Expr::prop(), None, true);
    ConstantInfo::new_with_reducibility(
        Name::from_string("Nat.zero"),
        vec![],
        Expr::prop(),
        None,
        Reducibility::Reducible,
        ConstantKind::Definition,
    );
}
"#,
        &[
            "unused return value of `ConstantInfo::new`",
            "unused return value of `ConstantInfo::new_with_reducibility`",
        ],
    );
}

#[test]
fn test_inductive_result_apis_are_must_use_from_external_crate() {
    assert_external_compile_fails(
        "inductive_result_must_use",
        r#"
#![deny(unused_must_use)]
use clean_kernel::{
    BinderInfo, Constructor, Expr, InductiveDecl, InductiveType, Name, RecursorArgOrder,
    RecursorRule, RecursorVal,
};
use clean_kernel::inductive::{check_positivity, validate_inductive};

fn dropped_inductive_results() {
    let nat = Name::from_string("Nat");
    let ctor = Constructor {
        name: Name::from_string("Nat.zero"),
        type_: Expr::const_(nat.clone(), vec![]),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![ctor],
        }],
    };
    let recursor = RecursorVal {
        name: Name::from_string("Nat.rec"),
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
        inductive_name: nat.clone(),
        num_params: 0,
        num_indices: 0,
        num_motives: 0,
        num_minors: 0,
        rules: vec![RecursorRule {
            constructor_name: Name::from_string("Nat.zero"),
            num_fields: 1,
            recursive_fields: vec![],
            rhs: Expr::bvar(0),
        }],
        is_k: false,
    };

    recursor.validate_metadata();
    check_positivity(&nat, &Expr::type_(), 0, &[&nat]);
    validate_inductive(&decl);
}
"#,
        &[
            "unused `Result` that must be used",
            "the Result indicates whether recursor metadata is consistent",
            "the Result indicates whether the constructor satisfies strict positivity",
            "the Result indicates whether the inductive declaration is well-formed",
        ],
    );
}

#[test]
fn used_api_results_compile_from_external_crate() {
    let output = compile_external_snippet(
        "used_results",
        r#"
#![deny(unused_must_use)]
use clean_kernel::{Expr, Level, Name};
pub fn kept() {
    let _ = Expr::bvar(0);
    let _ = Level::zero();
    let _ = Name::anon();
}
"#,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
