// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests of the trust-cg lane's pieces that need no trust-cg: the
//! receipt's lane labels, the driver it links, the shim-ABI check and the
//! linker diagnostics it reports. The lane end to end is measured by
//! `crates/clean/tests/native_exec_battery_trustcg.rs`.

use super::checks::{shim_abi_mismatch, shim_c_signature};
use super::link::{linker_undefined, render_driver, DRIVER_ENTRY};
use super::*;
use crate::native_build::{
    prelude_shim_definitions, EntryArgs, EntryContract, EntryExit, EntryKind,
};
use clean_compiler::emit_trust_ir_lane::{AbiSlot, LinkSignature};

fn io_contract(args: EntryArgs, exit: EntryExit) -> EntryContract {
    EntryContract {
        kind: EntryKind::Io,
        args,
        exit,
    }
}

#[test]
fn test_receipt_line_names_the_lane_and_its_runtime() {
    let receipt = Receipt::new("main");
    let line = receipt.line();
    assert!(
        line.contains("lowered: clean-compiler-unvalidated"),
        "{line}"
    );
    assert!(line.contains("runtime: C via cc"), "{line}");
    assert!(line.contains(CLAIM), "{line}");
    let json = serde_json::to_value(&receipt).expect("the receipt serializes");
    assert_eq!(json["lowered"], "clean-compiler-unvalidated");
    assert_eq!(json["runtime"], "C via cc");
    assert_eq!(json["schema"], RECEIPT_SCHEMA);
}

#[test]
fn test_driver_for_a_main_entry_is_renamed_and_calls_main_by_label() {
    let driver = render_driver(
        io_contract(EntryArgs::Argv, EntryExit::FromUInt32),
        "main",
        DRIVER_ENTRY,
    );
    let label = if cfg!(target_vendor = "apple") {
        "__asm__(\"_main\")"
    } else {
        "__asm__(\"main\")"
    };
    assert!(
        driver.contains(&format!(
            "extern clean_obj* clean_lx0_entry(clean_obj*) {label};"
        )),
        "{driver}"
    );
    assert!(
        driver.contains(&format!("int {DRIVER_ENTRY}(int argc, char** argv) {{")),
        "{driver}"
    );
    assert!(
        !driver.contains("int main("),
        "the driver must not define `main`"
    );
    assert!(driver.contains("clean_lx0_entry(_args)"), "{driver}");
    assert!(driver.contains("clean_unbox_uint32(_r)"), "IO UInt32 exit");
    assert!(
        driver.contains("lowered: clean-compiler-unvalidated; runtime: C via cc"),
        "{driver}"
    );
}

#[test]
fn test_driver_for_a_nullary_nat_entry_prints_the_result() {
    let nat = EntryContract {
        kind: EntryKind::Nat,
        args: EntryArgs::None,
        exit: EntryExit::AlwaysZero,
    };
    let driver = render_driver(nat, "answer", "main");
    assert!(
        driver.contains("extern clean_obj* clean_lx0_entry(void)"),
        "{driver}"
    );
    assert!(driver.contains("int main(void) {"), "{driver}");
    assert!(driver.contains("clean_unbox(_r)"), "{driver}");
}

fn ptr_decl(symbol: &str, arity: usize) -> LinkSignature {
    LinkSignature {
        symbol: symbol.to_owned(),
        params: vec![AbiSlot::Ptr; arity],
        returns: vec![AbiSlot::Ptr],
        vararg: false,
    }
}

/// POSITIVE + MUTATION CONTROL: `l_Nat_add`'s real shim matches a two-pointer
/// declaration, and the same shim is refused against a one-pointer one.
#[test]
fn test_shim_abi_check_accepts_the_real_arity_and_refuses_another() {
    let shims = prelude_shim_definitions();
    let (_, definition) = shims
        .iter()
        .find(|(symbol, _)| *symbol == "l_Nat_add")
        .expect("l_Nat_add is a shim");
    let (params, ret) = shim_c_signature("l_Nat_add", definition).expect("a declarator");
    assert_eq!(params.len(), 2, "{definition}");
    assert!(ret.contains('*'), "{ret}");
    assert_eq!(
        shim_abi_mismatch(definition, &ptr_decl("l_Nat_add", 2)),
        None
    );
    let why = shim_abi_mismatch(definition, &ptr_decl("l_Nat_add", 1))
        .expect("a one-parameter declaration must be refused");
    assert!(why.contains("1 parameter(s), the shim defines 2"), "{why}");
    let mut scalar = ptr_decl("l_Nat_add", 2);
    scalar.params[0] = AbiSlot::Other("U64".to_owned());
    assert!(shim_abi_mismatch(definition, &scalar).is_some());
}

#[test]
fn test_byte_array_string_shims_keep_actual_boxed_arity_and_refuse_scalar_slots() {
    let shims = prelude_shim_definitions();
    for (symbol, arity) in [
        ("l_String_ofList", 1),
        ("l_String_ofByteArray", 2),
        ("l_String_toByteArray", 1),
    ] {
        let (_, definition) = shims
            .iter()
            .find(|(name, _)| *name == symbol)
            .expect("production String bridge shim");
        let declaration = ptr_decl(symbol, arity);
        assert_eq!(shim_abi_mismatch(definition, &declaration), None);
        assert!(shim_abi_mismatch(definition, &ptr_decl(symbol, arity + 1)).is_some());
        let mut scalar = declaration.clone();
        scalar.params[0] = AbiSlot::Other("U64".to_string());
        assert!(shim_abi_mismatch(definition, &scalar).is_some());
    }
}

#[test]
fn test_linker_undefined_reads_ld64_and_gnu_ld() {
    let ld64 = "Undefined symbols for architecture arm64:\n  \
                \"_l_IO_Process_exit\", referenced from:\n      _main in module.o\n  \
                \"_l_IO_Process_exit\", referenced from:\n      _f in module.o\n  \
                \"_clean_foo\", referenced from:\n      _g in module.o\n\
                ld: symbol(s) not found for architecture arm64";
    assert_eq!(
        linker_undefined(ld64),
        vec!["l_IO_Process_exit".to_owned(), "clean_foo".to_owned()]
    );
    let gnu = "/usr/bin/ld: module.o: in function `main':\n\
               (.text+0x1c): undefined reference to `l_IO_Process_exit'";
    assert_eq!(linker_undefined(gnu), vec!["l_IO_Process_exit".to_owned()]);
    assert!(linker_undefined("clang: error: no such file").is_empty());
}

#[test]
fn test_stderr_head_prefers_error_lines_and_keeps_the_status() {
    let stderr = "note: reading module.tmbc\ntrust-cg: error: function `main` is affirmatively \
                  ungated\n";
    assert_eq!(
        stderr_head(stderr, Some(1)),
        "trust-cg: error: function `main` is affirmatively ungated (exit 1)"
    );
    assert_eq!(stderr_head("", Some(2)), "<empty stderr> (exit 2)");
    assert_eq!(
        stderr_head("last words\n\n", None),
        "last words (killed by a signal)"
    );
}

/// A backend that records what it is handed and then refuses, so the lane's
/// pluggable step ([`ObjectBackend`]) is measured without any trust-cg.
struct RecordingBackend {
    seen: std::cell::RefCell<Vec<String>>,
}

impl ObjectBackend for RecordingBackend {
    fn identity(&self) -> String {
        "recording-backend (test)".to_owned()
    }

    fn compile_object(
        &self,
        module: &Module,
        target: &str,
        _dir: &Path,
    ) -> Result<PathBuf, LaneError> {
        let mut seen = self.seen.borrow_mut();
        seen.push(format!("target={target}"));
        for function in module.functions.iter().filter(|f| !f.blocks.is_empty()) {
            seen.push(format!("{} {:?}", function.name, function.body_gate));
        }
        Err(LaneError::TrustCg(
            "recording backend refuses by design".to_owned(),
        ))
    }
}

/// The seam's contract, from the lane's side: every body a backend receives
/// carries this lane's license (or a kept kernel-TV claim) — none is `Ungated`
/// or claim-less — and a backend's refusal lands in the receipt at the
/// trust-cg stage with its own message and identity.
#[test]
fn test_build_with_backend_hands_the_backend_only_licensed_bodies() {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("hello.lean");
    std::fs::write(&file, "def main : IO Unit := IO.println \"hi\"\n").expect("write the program");
    let backend = RecordingBackend {
        seen: std::cell::RefCell::new(Vec::new()),
    };
    let (receipt, built) = build_with_backend(&file, "main", 0, &backend);
    let err = built
        .err()
        .expect("the recording backend refuses, so nothing is built");
    assert_eq!(err.step(), "trust-cg", "refused at the object step: {err}");
    assert!(matches!(receipt.stage, Stage::TrustCg), "{receipt:?}");
    assert_eq!(
        receipt.trust_cg.as_deref(),
        Some("recording-backend (test)")
    );
    assert_eq!(
        receipt.cause.as_deref(),
        Some("recording backend refuses by design")
    );
    let seen = backend.seen.into_inner();
    assert!(
        seen.len() >= 2,
        "the backend must see the target and at least one body: {seen:?}"
    );
    for row in &seen[1..] {
        assert!(
            row.contains(LOWERED) || row.contains("clean-kernel-tv"),
            "a body reached the backend without this lane's license: {row}"
        );
    }
}

#[test]
fn test_failed_build_retention_keeps_exact_licensed_input_and_original_refusal() {
    struct Refusing {
        dir: std::cell::RefCell<Option<PathBuf>>,
        input: std::cell::RefCell<Vec<u8>>,
    }
    impl ObjectBackend for Refusing {
        fn identity(&self) -> String {
            "refusing retention control".into()
        }
        fn compile_object(
            &self,
            module: &Module,
            _: &str,
            dir: &Path,
        ) -> Result<PathBuf, LaneError> {
            *self.dir.borrow_mut() = Some(dir.to_path_buf());
            *self.input.borrow_mut() = serialize_tmbc(module).expect("actual licensed input");
            Err(LaneError::TrustCg("original retention refusal".into()))
        }
    }
    let fixture = tempfile::tempdir().unwrap();
    let source = fixture.path().join("hello.lean");
    std::fs::write(&source, "def main : IO Unit := IO.println \"hi\"\n").unwrap();
    for retention in [ScratchRetention::Remove, ScratchRetention::Keep] {
        let backend = Refusing {
            dir: std::cell::RefCell::new(None),
            input: std::cell::RefCell::new(Vec::new()),
        };
        let (receipt, result) =
            build_with_backend_retaining(&source, "main", 0, &backend, retention);
        assert!(
            matches!(result, Err(LaneError::TrustCg(ref cause)) if cause == "original retention refusal")
        );
        assert_eq!(receipt.stage, Stage::TrustCg);
        assert_eq!(receipt.cause.as_deref(), Some("original retention refusal"));
        let path = backend.dir.into_inner().expect("backend actually ran");
        if retention == ScratchRetention::Remove {
            assert!(
                !path.exists(),
                "default failure must clean its owned scratch"
            );
            assert!(receipt.retained_directory().is_none());
            continue;
        }
        assert_eq!(receipt.retained_directory(), Some(path.as_path()));
        let bytes = std::fs::read(path.join("module.tmbc")).unwrap();
        assert_eq!(bytes, backend.input.into_inner());
        use sha2::{Digest, Sha256};
        let digest: String = Sha256::digest(&bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        assert_eq!(
            receipt.retained_input_sha256.as_deref(),
            Some(digest.as_str())
        );
        assert_eq!(
            std::fs::read_to_string(path.join("module.tmbc.sha256")).unwrap(),
            format!("{digest}  module.tmbc\n")
        );
        let saved: serde_json::Value =
            serde_json::from_slice(&std::fs::read(path.join("build-receipt.json")).unwrap())
                .unwrap();
        assert_eq!(saved["stage"], "trust-cg");
        assert_eq!(saved["cause"], "original retention refusal");
        assert_eq!(saved["claim"], CLAIM);
        assert_eq!(saved["retained_input_sha256"], digest);
        std::fs::remove_dir_all(path).unwrap();
    }
}

#[cfg(unix)]
#[test]
fn test_failed_cli_retention_preserves_full_streams_status_and_strict_arguments() {
    use std::os::unix::fs::PermissionsExt;
    let fixture = tempfile::tempdir().unwrap();
    let source = fixture.path().join("hello.lean");
    std::fs::write(&source, "def main : IO Unit := IO.println \"hi\"\n").unwrap();
    let program = fixture.path().join("refusing-backend");
    std::fs::write(&program, "#!/bin/sh\nprintf 'diagnostic stdout\\n'\nprintf 'note: first\\nerror: original CLI refusal\\nnote: last\\n' >&2\nexit 7\n").unwrap();
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o700)).unwrap();
    let backend = TrustCg {
        path: program,
        version: "diagnostic test fixture".into(),
        retention: ScratchRetention::Keep,
    };
    let (receipt, result) =
        build_with_backend_retaining(&source, "main", 0, &backend, ScratchRetention::Keep);
    assert!(
        matches!(result, Err(LaneError::TrustCg(ref cause)) if cause == "error: original CLI refusal (exit 7)")
    );
    let dir = receipt
        .retained_directory()
        .expect("failed artifacts retained");
    assert_eq!(
        std::fs::read(dir.join("trust-cg.stdout")).unwrap(),
        b"diagnostic stdout\n"
    );
    assert_eq!(
        std::fs::read(dir.join("trust-cg.stderr")).unwrap(),
        b"note: first\nerror: original CLI refusal\nnote: last\n"
    );
    let status: serde_json::Value =
        serde_json::from_slice(&std::fs::read(dir.join("trust-cg-status.json")).unwrap()).unwrap();
    assert_eq!(status["success"], false);
    assert_eq!(status["exit_code"], 7);
    let command: serde_json::Value =
        serde_json::from_slice(&std::fs::read(dir.join("trust-cg-command.json")).unwrap()).unwrap();
    assert_eq!(
        command["arguments"],
        serde_json::json!([
            "-c",
            "--target",
            host_trust_cg_target().unwrap(),
            "--recognize-authority",
            LOWERED,
            "--refuse-unlicensed",
            "-o"
        ])
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn trust_cg_selection_refuses_missing_explicit_file_despite_path_decoy() {
    let dir = tempfile::tempdir().expect("tempdir");
    let decoy = dir.path().join("trust-cg");
    std::fs::write(&decoy, b"inert compiler, never executed").expect("decoy");
    let error = select_trust_cg_path(
        Some(dir.path().join("missing").into_os_string()),
        Some(dir.path().as_os_str().to_owned()),
    )
    .expect_err("an invalid explicit compiler cannot select the PATH decoy");
    assert!(matches!(&error, LaneError::TrustCg(_)));
    assert!(error.to_string().contains("CLEAN_TRUST_CG_BIN="));
    assert!(error.to_string().contains("never replaced"));
}

#[test]
fn trust_cg_selection_refuses_explicit_directory_and_empty_path() {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join("trust-cg"), b"inert compiler").expect("decoy");
    for selected in [dir.path().as_os_str().to_owned(), std::ffi::OsString::new()] {
        select_trust_cg_path(Some(selected), Some(dir.path().as_os_str().to_owned()))
            .expect_err("a non-file explicit selection cannot fall through");
    }
}

#[test]
fn trust_cg_selection_preserves_explicit_file_over_path_decoy() {
    let dir = tempfile::tempdir().expect("tempdir");
    let selected = dir.path().join("selected");
    std::fs::write(&selected, b"inert selected compiler").expect("selected");
    std::fs::write(dir.path().join("trust-cg"), b"inert decoy").expect("decoy");
    let actual = select_trust_cg_path(
        Some(selected.clone().into_os_string()),
        Some(dir.path().as_os_str().to_owned()),
    )
    .expect("selected file");
    assert_eq!(actual, Some(selected));
}

#[test]
fn trust_cg_selection_searches_path_only_when_unselected() {
    let dir = tempfile::tempdir().expect("tempdir");
    let skipped = dir.path().join("directory");
    let first = dir.path().join("first");
    let second = dir.path().join("second");
    for root in [&skipped, &first, &second] {
        std::fs::create_dir(root).expect("PATH directory");
    }
    std::fs::create_dir(skipped.join("trust-cg")).expect("non-file candidate");
    for root in [&first, &second] {
        std::fs::write(root.join("trust-cg"), b"inert compiler").expect("candidate");
    }
    let path = std::env::join_paths([&skipped, &first, &second]).expect("PATH");
    assert_eq!(
        select_trust_cg_path(None, Some(path)).expect("PATH selection"),
        Some(first.join("trust-cg"))
    );
    assert_eq!(
        select_trust_cg_path(None, None).expect("no selection"),
        None
    );
}

#[test]
fn trust_cg_selection_object_emission_refuses_missing_explicit_compiler() {
    const CHILD: &str = "CLEAN_NATIVE_SELECTION_CHILD";
    if std::env::var_os(CHILD).is_some() {
        let output = PathBuf::from("must-not-exist.o");
        let args = CompileArgs {
            file: Some(PathBuf::from("missing-source.lean")),
            decl: Some("main".to_owned()),
            emit: EmitFormat::Obj,
            opt_level: 0,
            output: Some(output.clone()),
            link_artifact: Vec::new(),
        };
        let error = crate::compile::compile_to_object(&args)
            .expect_err("the selected compiler must be refused before reading the source");
        let message = format!("{error:#}");
        assert!(message.contains("CLEAN_TRUST_CG_BIN="), "{message}");
        assert!(message.contains("never replaced"), "{message}");
        assert!(!output.exists());
        return;
    }

    // Exercise the public object door in a separate process without changing
    // the environment of other tests. The PATH decoy is never executable.
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join("trust-cg"), b"inert PATH decoy").expect("decoy");
    let result = Command::new(std::env::current_exe().expect("test executable"))
        .args([
            "--exact",
            "native_trustcg::tests::trust_cg_selection_object_emission_refuses_missing_explicit_compiler",
        ])
        .env(CHILD, "1")
        .env("CLEAN_TRUST_CG_BIN", dir.path().join("missing-compiler"))
        .env("PATH", dir.path())
        .current_dir(dir.path())
        .output()
        .expect("run the object-door regression");
    assert!(
        result.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(String::from_utf8_lossy(&result.stdout).contains("1 passed; 0 failed"));
    assert!(!dir.path().join("must-not-exist.o").exists());
}
