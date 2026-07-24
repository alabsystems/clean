// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end emitter/runtime execution tests.
//!
//! These tests close the gap between compile-only emitter checks and
//! runtime-only behavioral tests by emitting real C/Rust artifacts,
//! compiling them, executing them, and checking the observed output.

#![cfg(feature = "round-trip-compile")]

mod test_helpers;

use std::path::{Path, PathBuf};
use std::process::Command;

use clean_compiler::emit_c::emit_c;
use clean_compiler::emit_rust::emit_rust;
use clean_compiler::ir::{IRBody, IRDecl, IRExpr, IRType};
use clean_compiler::mangle::mangle_name;
use tempfile::tempdir;
use test_helpers::{arg, mixed_ctor, name, obj_ctor, var};

fn runtime_include_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/include")
}

fn runtime_c_source() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/src/clean_runtime.c")
}

fn runtime_crate_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime")
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

fn output_lines(bytes: &[u8]) -> Vec<String> {
    String::from_utf8_lossy(bytes)
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(ToOwned::to_owned)
        .collect()
}

fn compile_and_run_emitted_c(decls: &[IRDecl], main_body: &str) -> Option<Vec<String>> {
    let cc = match find_c_compiler() {
        Some(cc) => cc,
        None => {
            eprintln!("No C compiler found (cc/gcc/clang) — skipping emitted C e2e test");
            return None;
        }
    };

    let dir = tempdir().expect("failed to create temp dir");
    let source_path = dir.path().join("emit_e2e.c");
    let binary_path = dir.path().join("emit_e2e");

    let emitted = emit_c(decls).unwrap();
    let full_source = format!(
        "#include <stdio.h>\n\n{emitted}\nint main(void) {{\n  clean_runtime_init();\n{main_body}\n  clean_runtime_finalize();\n  return 0;\n}}\n"
    );
    std::fs::write(&source_path, full_source).expect("failed to write emitted C source");

    let compile = Command::new(&cc)
        .arg("-o")
        .arg(&binary_path)
        .arg(&source_path)
        .arg(runtime_c_source())
        .arg(format!("-I{}", runtime_include_dir().display()))
        .arg("-lm")
        .arg("-std=c11")
        .output()
        .expect("failed to invoke C compiler");

    assert!(
        compile.status.success(),
        "emitted C compilation failed:\nstderr: {}",
        String::from_utf8_lossy(&compile.stderr),
    );

    let run = Command::new(&binary_path)
        .output()
        .expect("failed to execute emitted C binary");

    assert!(
        run.status.success(),
        "emitted C binary exited with {}:\nstderr: {}",
        run.status,
        String::from_utf8_lossy(&run.stderr),
    );

    Some(output_lines(&run.stdout))
}

fn compile_and_run_emitted_rust(decls: &[IRDecl], main_body: &str) -> Vec<String> {
    let dir = tempdir().expect("failed to create temp dir");
    std::fs::create_dir_all(dir.path().join("src")).expect("failed to create src dir");

    let manifest = format!(
        "[package]\nname = \"clean-emitted-runtime-e2e\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\nclean-runtime = {{ path = \"{}\" }}\n",
        runtime_crate_dir().display()
    );
    std::fs::write(dir.path().join("Cargo.toml"), manifest).expect("failed to write Cargo.toml");

    let emitted = emit_rust(decls).unwrap();
    let full_source = format!(
        "{emitted}\nfn main() {{\n    unsafe {{\n        clean_runtime_init();\n{main_body}\n        clean_runtime_finalize();\n    }}\n}}\n"
    );
    std::fs::write(dir.path().join("src/main.rs"), full_source)
        .expect("failed to write emitted Rust source");

    let run = Command::new("cargo")
        .arg("run")
        .arg("--quiet")
        .arg("--offline")
        .arg("--manifest-path")
        .arg(dir.path().join("Cargo.toml"))
        .env("CARGO_TARGET_DIR", dir.path().join("target"))
        .current_dir(dir.path())
        .output()
        .expect("failed to invoke cargo run");

    assert!(
        run.status.success(),
        "emitted Rust execution failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr),
    );

    output_lines(&run.stdout)
}

fn make_pair_first_decl() -> IRDecl {
    IRDecl {
        name: name("pair.first"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: obj_ctor(0, 2),
                args: vec![arg(0), arg(1)],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(3),
                ty: IRType::Object,
                value: IRExpr::Proj {
                    idx: 0,
                    ty: IRType::Object,
                    arg: arg(2),
                },
                rest: Box::new(IRBody::Inc {
                    var: var(3),
                    n: 1,
                    rest: Box::new(IRBody::Dec {
                        var: var(2),
                        rest: Box::new(IRBody::Ret(arg(3))),
                    }),
                }),
            }),
        },
    }
}

fn make_scalar_slot_roundtrip_decl() -> IRDecl {
    IRDecl {
        name: name("scalar.slot.roundtrip"),
        params: vec![(var(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mixed_ctor(0, 0, &[IRType::UInt32]),
                args: vec![],
            },
            rest: Box::new(IRBody::SSet {
                var: var(1),
                n: 0,
                offset: 0,
                value: var(0),
                ty: IRType::UInt32,
                rest: Box::new(IRBody::VDecl {
                    var: var(2),
                    ty: IRType::UInt32,
                    value: IRExpr::SProj {
                        n: 0,
                        offset: 0,
                        var: var(1),
                        ty: IRType::UInt32,
                    },
                    rest: Box::new(IRBody::Dec {
                        var: var(1),
                        rest: Box::new(IRBody::Ret(arg(2))),
                    }),
                }),
            }),
        },
    }
}

fn expected_roundtrip_lines() -> Vec<String> {
    vec!["41".to_string(), "1234".to_string()]
}

#[test]
fn test_emitted_c_executes_against_runtime() {
    let pair_decl = make_pair_first_decl();
    let scalar_decl = make_scalar_slot_roundtrip_decl();
    let pair_fn = mangle_name(&pair_decl.name);
    let scalar_fn = mangle_name(&scalar_decl.name);
    let main_body = format!(
        "  clean_obj* pair = {pair_fn}(clean_box_uint64(41), clean_box_uint64(7));\n  printf(\"%llu\\n\", (unsigned long long)clean_unbox_uint64(pair));\n  clean_dec(pair);\n  uint32_t scalar = {scalar_fn}(UINT32_C(1234));\n  printf(\"%u\\n\", (unsigned int)scalar);"
    );

    if let Some(lines) = compile_and_run_emitted_c(&[pair_decl, scalar_decl], &main_body) {
        assert_eq!(lines, expected_roundtrip_lines());
    }
}

#[test]
fn test_emitted_rust_executes_against_runtime() {
    let pair_decl = make_pair_first_decl();
    let scalar_decl = make_scalar_slot_roundtrip_decl();
    let pair_fn = mangle_name(&pair_decl.name);
    let scalar_fn = mangle_name(&scalar_decl.name);
    let main_body = format!(
        "        let pair = {pair_fn}(clean_box_uint64(41), clean_box_uint64(7));\n        println!(\"{{}}\", clean_unbox_uint64(pair));\n        clean_dec(pair);\n        let scalar = {scalar_fn}(1234u32);\n        println!(\"{{}}\", scalar);"
    );

    let lines = compile_and_run_emitted_rust(&[pair_decl, scalar_decl], &main_body);
    assert_eq!(lines, expected_roundtrip_lines());
}
