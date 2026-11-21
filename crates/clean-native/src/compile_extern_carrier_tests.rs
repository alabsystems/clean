// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Metadata completeness does not enable a native extern. All controls enter
//! through actual source elaboration and production declaration selection.
use super::*;
use crate::native_ffi_audit::UncompilableFfi;
use clean_kernel::env::CompilerExternMetadata;

fn refusal(source: &str, target: &str, external: &str) -> anyhow::Error {
    let dir = tempfile::tempdir().expect("own fixture");
    let file = dir.path().join("Carrier.lean");
    std::fs::write(&file, source).expect("write exact source");
    let env = elaborate_file_to_env(&file).expect("all source setup must elaborate first");
    assert!(
        env.get_const(&Name::from_string(target)).is_some(),
        "actual target exists"
    );
    assert!(matches!(
        env.extern_metadata(&Name::from_string(external))
            .expect("carrier"),
        Some(CompilerExternMetadata::Complete(_))
    ));
    let args = CompileArgs {
        file: Some(file),
        decl: Some(target.into()),
        emit: EmitFormat::C,
        opt_level: 0,
        output: None,
        link_artifact: Vec::new(),
    };
    select_lcnf_decl(&args).expect_err("complete metadata alone must not enable an extern")
}
#[test]
fn bodyless_borrowed_and_owned_dependencies_still_refuse() {
    for (symbol, domain) in [
        ("lean_string_utf8_byte_size", "@& String"),
        ("clean_string_utf8_byte_size_owned", "String"),
    ] {
        let source = format!("@[extern \"{symbol}\"] axiom arbitraryAlias (s : {domain}) : Nat\ndef caller : Nat := arbitraryAlias \"é🙂\"\n");
        let error = refusal(&source, "caller", "arbitraryAlias");
        assert!(
            matches!(error.downcast_ref::<UncompilableFfi>(), Some(UncompilableFfi::ExternWithoutBody { name, .. }) if name == "arbitraryAlias"),
            "{error:#}"
        );
    }
}
#[test]
fn body_bearing_extern_keeps_its_typed_refusal() {
    let source = "@[extern \"clean_string_utf8_byte_size_owned\"] def arbitraryAlias (s : String) : Nat := 37\ndef caller : Nat := arbitraryAlias \"é🙂\"\n";
    let error = refusal(source, "caller", "arbitraryAlias");
    assert!(
        matches!(error.downcast_ref::<UncompilableFfi>(), Some(UncompilableFfi::ExternWithBody { name, .. }) if name == "arbitraryAlias"),
        "{error:#}"
    );
}
#[test]
fn chosen_extern_root_keeps_its_default_refusal() {
    let source =
        "@[extern \"clean_string_utf8_byte_size_owned\"] axiom arbitraryAlias (s : String) : Nat\n";
    let error = refusal(source, "arbitraryAlias", "arbitraryAlias");
    assert!(
        matches!(error.downcast_ref::<UncompilableFfi>(), Some(UncompilableFfi::ExternWithoutBody { name, .. }) if name == "arbitraryAlias"),
        "{error:#}"
    );
}
#[test]
fn unknown_symbol_is_not_enabled_by_a_complete_descriptor() {
    let source = "@[extern \"not_a_supported_runtime_symbol\"] axiom arbitraryAlias (s : String) : Nat\ndef caller : Nat := arbitraryAlias \"é🙂\"\n";
    let error = refusal(source, "caller", "arbitraryAlias");
    assert!(
        matches!(error.downcast_ref::<UncompilableFfi>(), Some(UncompilableFfi::ExternWithoutBody { symbol, .. }) if symbol == "not_a_supported_runtime_symbol"),
        "{error:#}"
    );
}

#[test]
fn kernel_value_selection_keeps_the_existing_extern_refusal() {
    let source = "@[extern \"clean_string_utf8_byte_size_owned\"] def arbitraryAlias (s : String) : Nat := 37\ndef caller : Nat := arbitraryAlias \"é🙂\"\n";
    let dir = tempfile::tempdir().expect("own source");
    let file = dir.path().join("KernelValue.lean");
    std::fs::write(&file, source).expect("write");
    let env = elaborate_file_to_env(&file).expect("source setup succeeds");
    assert!(env.get_const(&Name::from_string("caller")).is_some());
    assert!(matches!(
        env.extern_metadata(&Name::from_string("arbitraryAlias"))
            .expect("metadata"),
        Some(CompilerExternMetadata::Complete(_))
    ));
    let args = CompileArgs {
        file: Some(file),
        decl: Some("caller".into()),
        emit: EmitFormat::C,
        opt_level: 0,
        output: None,
        link_artifact: Vec::new(),
    };
    let error =
        select_lcnf_decl_with_meaning(&args, &is_primitive_denylisted, CodeMeaning::KernelValue)
            .expect_err("KernelValue policy must not be widened by metadata completeness");
    assert!(
        matches!(error.downcast_ref::<UncompilableFfi>(), Some(UncompilableFfi::ExternWithBody { name, .. }) if name == "arbitraryAlias"),
        "{error:#}"
    );
}
