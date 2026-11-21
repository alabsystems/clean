// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execute source casesOn minors that are enclosing functions, partially
//! lambda-bound functions, and functions returning another function. The
//! inputs include a heap Nat so RC and closure application remain observable.

use crate::emit_c::{emit_c_with_config, CEmitConfig};
use crate::pass_manager::PipelineConfig;
use crate::rc_repair::e2e_support::{compile_closure_of, elaborated_env_with, o0, SHIMS_C};
use crate::rc_repair::RcRepairMode;
use std::process::Command;

const SOURCE: &str = include_str!("../../tests/fixtures/generic_cases_minors/Source.lean");
const DRIVER: &str = include_str!("../../tests/fixtures/generic_cases_minors/driver.c");
const ROOTS: &[&str] = &[
    "runLeft",
    "runRight",
    "runPair",
    "runFunctionLeft",
    "runFunctionRight",
    "runLambdaLong",
    "runNone",
];

fn execute(pipeline: &PipelineConfig) {
    let env = elaborated_env_with(SOURCE);
    let decls = compile_closure_of(&env, pipeline, RcRepairMode::Enabled, ROOTS)
        .expect("source closure compiles with RC linearity checking");
    let emitted = emit_c_with_config(
        &decls,
        CEmitConfig {
            check_ir: true,
            ..CEmitConfig::default()
        },
    )
    .expect("emit checked C");
    let directory = tempfile::tempdir().expect("native fixture directory");
    let directory = directory.path();
    std::fs::write(
        directory.join("clean_runtime.h"),
        clean_runtime::runtime_header(),
    )
    .expect("runtime header");
    std::fs::write(
        directory.join("clean_runtime.c"),
        clean_runtime::runtime_source().replacen(
            "../include/clean_runtime.h",
            "clean_runtime.h",
            1,
        ),
    )
    .expect("runtime source");
    let program = directory.join("cases.c");
    std::fs::write(
        &program,
        format!("#include \"clean_runtime.h\"\n{SHIMS_C}\n{emitted}\n{DRIVER}"),
    )
    .expect("emitted source");
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    for (label, flags) in [
        ("c0", vec!["-O0"]),
        ("c2", vec!["-O2"]),
        (
            "asan",
            vec!["-O1", "-fsanitize=address", "-fno-omit-frame-pointer"],
        ),
    ] {
        let binary = directory.join(label);
        let output = Command::new(&cc)
            .args(flags)
            .args(["-std=c11", "-g", "-I"])
            .arg(directory)
            .arg(&program)
            .arg(directory.join("clean_runtime.c"))
            .args(["-lm", "-o"])
            .arg(&binary)
            .output()
            .expect("required C compiler");
        assert!(
            output.status.success(),
            "{label} compilation: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        for input in [0u64, 7, 1u64 << 63] {
            let output = Command::new(&binary)
                .arg(input.to_string())
                .output()
                .expect("execute actual compiled source");
            assert!(
                output.status.success(),
                "{label}/{input}: {:?}, stderr={}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(
                output.stderr.is_empty(),
                "{label}/{input}: {:?}",
                output.stderr
            );
            assert_eq!(
                output.stdout,
                format!("{input}\n99\n{input}\n{input}\n17\n{input}\n{input}\n").as_bytes(),
                "{label}/{input} constructor fields must be applied to the original minor"
            );
        }
    }
}

#[test]
fn generic_cases_minors_execute_at_o0() {
    execute(&o0());
}

#[test]
fn generic_cases_minors_execute_at_default_opt() {
    execute(&PipelineConfig::default());
}
