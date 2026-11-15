// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual checked-source bodies in a fresh replay world, before default migration.
//! The production compiler, module checks, license and link inputs stay intact.

use super::*;
use clean_compiler::emit_c::CEmitConfig;
use clean_compiler::pass_manager::{
    compile_lcnf_decls_for, compile_lcnf_to_trust_ir_with_report_for, PipelineConfig,
};
use clean_compiler::{constant_to_decl_with_meaning, CodeMeaning, Decl};
use clean_kernel::expr::UsedConstants;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::path::Path;
#[cfg(target_os = "macos")]
use std::path::PathBuf;
use std::process::Command;

const ROOTS: &[&str] = &[
    "bridgeFromChars",
    "bridgePayload",
    "bridgePayloadCases",
    "bridgeRoundTrip",
    "bridgeCtorPartial",
    "bridgeDynamic",
    "bridgeDynamicPartial",
    "bridgeDynamicSelected",
    "bridgeShared",
    "bridgeEntry",
    "bridgeRewrap",
];
const DRIVER: &str = include_str!("../tests/fixtures/string_bytearray/source_bridge_driver.c");

fn digest(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes).as_ref())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn world(bytes: &[u8]) -> Environment {
    let env = crate::native_string_source_bridge_tests::source_world_for_roots(bytes, ROOTS);
    for root in ROOTS {
        assert!(
            env.axiom_deps(&Name::from_string(root))
                .expect("checked source dependency closure")
                .iter()
                .all(|name| env.is_canonical_foundational_axiom(name)),
            "actual source {root} has no domain-specific axioms"
        );
    }
    env
}

fn closure(env: &Environment) -> Vec<Decl> {
    let inline_env = crate::native_monad_inline::inlining_env(env);
    let mut pending: Vec<Name> = ROOTS.iter().map(|name| Name::from_string(name)).collect();
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone())
            || crate::native_build::is_primitive_denylisted(&clean_compiler::mangle::mangle_name(
                &name,
            ))
        {
            continue;
        }
        let info = env.get_const(&name).expect("checked source dependency");
        let info = crate::native_eager_io::prepare_native_constant(
            env,
            &inline_env,
            info,
            CodeMeaning::KernelValue,
        )
        .expect("production source fidelity audits under the checked model");
        let Some(decl) = constant_to_decl_with_meaning(env, &info, CodeMeaning::KernelValue)
            .unwrap_or_else(|error| panic!("lower actual source {name}: {error}"))
        else {
            continue;
        };
        if let Some(value) = &info.value {
            let mut dependencies = HashSet::new();
            value.used_constants_dag(UsedConstants::WithProjectionStructures, &mut dependencies);
            let mut dependencies: Vec<_> = dependencies.into_iter().collect();
            dependencies.sort();
            pending.extend(dependencies);
        }
        result.push(decl);
    }
    result
}

fn pipeline() -> PipelineConfig {
    PipelineConfig {
        opt: clean_compiler::OptConfig::minimal(),
        rc: clean_compiler::RCConfig::minimal(),
        boxing: clean_compiler::BoxingConfig::minimal(),
    }
}

fn execute(binary: &Path, packet_sha256: &str, backend: &str, address_sanitized: bool) {
    for args in [&[][..], &["x", "y", "z"][..]] {
        let output = Command::new(binary)
            .args(args)
            .output()
            .expect("execute source bridge");
        let n = args.len() as u32;
        let value = format!("{}\0λ😀", char::from_u32(97 + n).expect("small scalar"));
        let from_chars = format!("\0é€{}", char::from_u32(128512 + n).expect("small scalar"));
        let expected = format!(
            "{value}\n{value}\n{value}\n{value}\n{value}\n{from_chars}\n{value}\n{value}\n\n"
        );
        assert_eq!(output.status.code(), Some(0), "{:?}", output.stderr);
        assert_eq!(output.stdout, expected.as_bytes());
        assert!(output.stderr.is_empty(), "{:?}", output.stderr);
        eprintln!(
            "{}",
            serde_json::json!({
                "schema":"clean-checked-string-execution/v1",
                "source_packet_sha256":packet_sha256,
                "backend":backend,
                "address_sanitized_c_runtime_and_consumer":address_sanitized,
                "binary_sha256":digest(&std::fs::read(binary).expect("executed binary")),
                "args":args,
                "exit_code":output.status.code(),
                "stdout_hex":hex(&output.stdout),
                "expected_stdout_hex":hex(expected.as_bytes()),
                "stderr_hex":hex(&output.stderr),
            })
        );
    }
}

#[cfg(target_os = "macos")]
fn execute_address_sanitized(
    dir: &Path,
    sources: &[PathBuf],
    object: Option<&Path>,
    packet_sha256: &str,
    backend: &str,
) {
    let compiler = crate::native_build::find_c_compiler().expect("selected host C compiler");
    let binary = dir.join("program-address-sanitized");
    let mut command = crate::native_c_toolchain::command(&compiler).expect("host C SDK");
    command
        .args([
            "-fsanitize=address",
            "-fno-omit-frame-pointer",
            "-g",
            "-O1",
            "-std=c11",
            "-I",
        ])
        .arg(dir)
        .args(sources);
    if let Some(object) = object {
        command.arg(object);
    }
    let output = command
        .args(["-lm", "-o"])
        .arg(&binary)
        .output()
        .expect("compile address-sanitized carrier and source consumer");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    eprintln!(
        "AddressSanitizer executable SHA256 {}",
        digest(&std::fs::read(&binary).expect("sanitized binary"))
    );
    execute(&binary, packet_sha256, backend, true);
}

fn compile_c(bytes: &[u8]) {
    let env = world(bytes);
    let decls = closure(&env);
    let artifacts = compile_lcnf_decls_for(&decls, &env, &pipeline(), CodeMeaning::KernelValue)
        .expect("production compiler pipeline for checked source");
    let c = artifacts
        .emit_c(CEmitConfig {
            check_ir: true,
            ..CEmitConfig::default()
        })
        .expect("emit actual source C");
    eprintln!(
        "source packet SHA256 {}; emitted C SHA256 {}",
        digest(bytes),
        digest(c.as_bytes())
    );
    let policy = crate::native_string_layout_policy::StringLayoutPolicy::from_env(&env);
    assert!(
        policy.permits_byte_backed_bodies(),
        "actual checked source policy"
    );
    let shims =
        crate::native_build::select_shims_for_c_text_with_policy(&format!("{c}\n{DRIVER}"), policy)
            .expect("production carrier/link-demand audits");
    let dir = tempfile::tempdir().expect("tempdir");
    let binary = crate::native_build::build_extract_executable(
        dir.path(),
        &format!("#include <stdio.h>\n{shims}"),
        &c,
        DRIVER,
    )
    .expect("link actual checked-source C consumer");
    eprintln!(
        "C executable SHA256 {}",
        digest(&std::fs::read(&binary).expect("binary"))
    );
    execute(&binary, &digest(bytes), "C", false);
    #[cfg(target_os = "macos")]
    execute_address_sanitized(
        dir.path(),
        &[
            dir.path().join("program.c"),
            dir.path().join("clean_runtime.c"),
        ],
        None,
        &digest(bytes),
        "C",
    );
}

fn compile_cg(bytes: &[u8]) {
    let env = world(bytes);
    let decls = closure(&env);
    let args = CompileArgs {
        file: None,
        decl: Some("bridgeEntry".to_string()),
        emit: EmitFormat::Obj,
        opt_level: 0,
        output: None,
        link_artifact: vec![],
    };
    let artifacts = compile_lcnf_decls_for(&decls, &env, &pipeline(), CodeMeaning::KernelValue)
        .expect("production compiler pipeline before CG");
    check_decls(&artifacts.boxed_ir_decls).expect("unchanged production IR checker");
    let (mut module, _) = compile_lcnf_to_trust_ir_with_report_for(
        &decls,
        &env,
        &pipeline(),
        &object_emit_config(&args),
        CodeMeaning::KernelValue,
    )
    .expect("emit actual checked source through typed TrustIR");
    let checked = checks::module_self_checks_for_env(
        &env,
        &module,
        "bridgeEntry",
        &Name::from_string("bridgeEntry"),
        Some(&Expr::const_str("Nat")),
    )
    .expect("unchanged production module self-checks");
    let census = checked
        .license(&mut module)
        .expect("unchanged scoped native license");
    let dir = tempfile::tempdir().expect("tempdir");
    let backend = resolve_trust_cg().expect("selected actual CG");
    eprintln!(
        "source packet SHA256 {}; licensed module {}; CG {}; bodies unvalidated {}, kept {:?}",
        digest(bytes),
        module_stable_digest_string(&module).expect("module identity"),
        backend.identity(),
        census.unvalidated,
        census.kept,
    );
    let object = backend
        .compile_object(&module, host_trust_cg_target().expect("host"), dir.path())
        .expect("actual CG object with normal refusal policy");
    let driver = format!("#define CLEAN_BRIDGE_CG\n{DRIVER}");
    let sources =
        link::materialize(dir.path(), &driver).expect("production runtime and shim inputs");
    let binary = dir.path().join("program");
    let output = crate::native_c_toolchain::command("cc")
        .expect("host C compiler")
        .args(["-O2", "-std=c11", "-I"])
        .arg(dir.path())
        .args(&sources)
        .arg(&object)
        .args(["-lm", "-o"])
        .arg(&binary)
        .output()
        .expect("link CG and actual runtime");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    eprintln!(
        "CG executable SHA256 {}",
        digest(&std::fs::read(&binary).expect("binary"))
    );
    execute(&binary, &digest(bytes), "CG", false);
    // The CG object is unchanged; instrument the shipped C runtime, shims and
    // host consumer so their accesses catch released or invalid carriers.
    #[cfg(target_os = "macos")]
    execute_address_sanitized(dir.path(), &sources, Some(&object), &digest(bytes), "CG");
}

fn singleton(element_type: &str, value: Expr) -> Expr {
    let ty = Expr::const_str(element_type);
    let nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        ty.clone(),
    );
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [ty, value, nil],
    )
}

fn source_negatives(bytes: &[u8]) {
    let mut env = world(bytes);
    let byte = Expr::app(Expr::const_str("UInt8.ofNat"), Expr::nat_lit(255));
    let array = Expr::apps(
        Expr::const_(Name::from_string("Array.mk"), vec![Level::zero()]),
        [Expr::const_str("UInt8"), singleton("UInt8", byte)],
    );
    let bad_bytes = Expr::app(Expr::const_str("ByteArray.mk"), array);
    let chars = singleton(
        "Char",
        Expr::app(Expr::const_str("Char.ofNat"), Expr::nat_lit(97)),
    );
    let wrong_equality = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("ByteArray"), bad_bytes.clone()],
    );
    let false_validity = Expr::apps(
        Expr::const_str("ByteArray.IsValidUTF8.intro"),
        [bad_bytes.clone(), chars, wrong_equality],
    );
    let invalid_utf8 = Expr::apps(
        Expr::const_str("String.ofByteArray"),
        [bad_bytes.clone(), false_validity],
    );
    let missing_proof = Expr::app(Expr::const_str("String.ofByteArray"), bad_bytes);
    let wrong_result = Expr::app(Expr::const_str("bridgeRoundTrip"), Expr::str_lit("a"));
    for (name, type_, value) in [
        ("invalidUTF8", Expr::const_str("String"), invalid_utf8),
        ("missingProof", Expr::const_str("String"), missing_proof),
        ("wrongResult", Expr::const_str("Nat"), wrong_result),
    ] {
        let name = Name::from_string(name);
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_,
            value,
            is_reducible: false,
        })
        .expect_err("actual checked source refuses before proof erasure/codegen");
        assert!(
            env.get_const(&name).is_none(),
            "no refused declaration is published"
        );
    }
    let encoder = env
        .get_const(&Name::from_string("List.utf8Encode"))
        .expect("actual source encoder");
    assert!(env.is_noncomputable(&encoder.name));
    assert!(
        constant_to_decl_with_meaning(&env, encoder, CodeMeaning::LeanCompiled)
            .expect("ordinary noncomputable policy")
            .is_none(),
        "raw noncomputable model is not a runtime caller"
    );
}

const PINNED: &[u8] =
    include_bytes!("../tests/fixtures/string_bytearray/fixture-lean-4.30.0-rc2.json");
const LATEST: &[u8] = include_bytes!("../tests/fixtures/string_bytearray/fixture-lean-4.35.0.json");

#[test]
fn actual_pinned_string_constructor_cases_and_partial_execute_c() {
    compile_c(PINNED);
}
#[test]
fn actual_latest_string_constructor_cases_and_partial_execute_c() {
    compile_c(LATEST);
}
#[test]
fn actual_pinned_string_constructor_cases_and_partial_execute_cg() {
    compile_cg(PINNED);
}
#[test]
fn actual_latest_string_constructor_cases_and_partial_execute_cg() {
    compile_cg(LATEST);
}
#[test]
fn actual_pinned_source_refuses_invalid_missing_and_mistyped_proofs() {
    source_negatives(PINNED);
}
#[test]
fn actual_latest_source_refuses_invalid_missing_and_mistyped_proofs() {
    source_negatives(LATEST);
}
