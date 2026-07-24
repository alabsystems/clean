// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn clean_kernel_metadata_artifact() -> PathBuf {
    let deps_dir = std::env::current_exe()
        .expect("integration test should know its executable path")
        .parent()
        .expect("integration test executable should live under target deps")
        .to_path_buf();
    let mut rlibs = Vec::new();
    let mut rmetas = Vec::new();

    for path in fs::read_dir(&deps_dir)
        .expect("deps directory should be readable")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
    {
        let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !file_name.starts_with("libclean_kernel-") {
            continue;
        }

        match path.extension().and_then(|ext| ext.to_str()) {
            Some("rlib") => rlibs.push(path),
            Some("rmeta") => rmetas.push(path),
            _ => {}
        }
    }

    let sort_by_mtime = |artifacts: &mut Vec<PathBuf>| {
        artifacts.sort_by_key(|path| {
            fs::metadata(path)
                .and_then(|metadata| metadata.modified())
                .unwrap_or(UNIX_EPOCH)
        });
    };
    sort_by_mtime(&mut rlibs);
    sort_by_mtime(&mut rmetas);

    rlibs
        .pop()
        .or_else(|| rmetas.pop())
        .expect("clean_kernel metadata artifact should exist in deps dir")
}

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
    let artifact = clean_kernel_metadata_artifact();
    let deps_dir = artifact
        .parent()
        .expect("clean_kernel artifact should live in deps directory");
    let compile_dir = temp_compile_dir(test_name);
    fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

    let source_path = compile_dir.join("snippet.rs");
    fs::write(&source_path, source).expect("snippet source should be writable");

    let output = Command::new("rustc")
        .arg("--crate-type")
        .arg("lib")
        .arg("--edition")
        .arg("2021")
        .arg("--emit")
        .arg("metadata")
        .arg("--out-dir")
        .arg(&compile_dir)
        .arg(&source_path)
        .arg("--extern")
        .arg(format!("clean_kernel={}", artifact.display()))
        .arg("-L")
        .arg(format!("dependency={}", deps_dir.display()))
        .output()
        .expect("rustc should be runnable from integration tests");

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
