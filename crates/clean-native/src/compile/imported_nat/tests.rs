// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::path::Path;

use clean_compiler::lcnf::DeclValue;
use clean_kernel::BigNat;
use clean_olean::{prepare_imported_nat_function, CapturedModuleBytes};

use super::*;

macro_rules! fixture {
    ($fixture:literal, $suffix:literal) => {
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/fixtures/olean/v4.36.0/",
            $fixture,
            "/StableFixture/Defs.",
            $suffix
        ))
    };
}

fn original() -> CapturedModuleBytes<'static> {
    CapturedModuleBytes {
        canonical_path: Path::new("absent/StableFixture/Defs.olean"),
        base: fixture!("module-ir", "olean"),
        server: Some(fixture!("module-ir", "olean.server")),
        private: Some(fixture!("module-ir", "olean.private")),
        ir: Some(fixture!("module-ir", "ir")),
        ir_signature: Some(fixture!("module-ir", "ir.sig")),
    }
}

fn lower(captured: CapturedModuleBytes<'_>, declaration: &str) -> LoweredImportedNat {
    let declaration = Name::anon().str("StableFixture").str(declaration);
    let function = prepare_imported_nat_function(captured, &declaration)
        .expect("validate the genuine exported signature")
        .expect("first-order Nat function");
    let program = function.native_program().expect("admit captured stable IR");
    lower_imported_nat_program(&program).expect("lower admitted Nat IR")
}

#[test]
fn captured_twice_uses_the_owned_native_carrier_and_supplied_parameter() {
    let lowered = lower(original(), "twice");
    let decl = lowered.declaration;
    assert!(lowered.uses_nat_add);
    assert_eq!(decl.name, Name::anon().str("StableFixture").str("twice"));
    let [parameter] = decl.params.as_slice() else {
        panic!("expected a single parameter");
    };
    assert!(!parameter.borrow);
    assert_eq!(parameter.ty, Expr::const_str("Nat"));
    assert_eq!(decl.ty, Expr::const_str("Nat"));
    let DeclValue::Code(body) = decl.body else {
        panic!("expected an emitted body");
    };
    let Code::Let(binding, result) = *body else {
        panic!("expected the addition binding with no private helper calls");
    };
    let arg = Arg::FVar(parameter.fvar_id);
    assert_eq!(
        binding.value,
        LetValue::Const {
            name: Name::anon().str("Nat").str("add"),
            levels: Vec::new(),
            args: vec![arg.clone(), arg],
        }
    );
    assert_eq!(*result, Code::Return(binding.fvar_id));
}

fn literal_offset(captured: CapturedModuleBytes<'_>) -> BigNat {
    let lowered = lower(captured, "addOffset");
    assert!(lowered.uses_nat_add);
    let DeclValue::Code(body) = lowered.declaration.body else {
        panic!("expected an emitted body");
    };
    let Code::Let(binding, _) = *body else {
        panic!("expected the captured Nat literal binding");
    };
    let LetValue::Lit(Literal::Nat(value)) = binding.value else {
        panic!("expected a Nat literal from the compiled body");
    };
    value
}

#[test]
fn replacement_ir_changes_the_lowered_body_without_changing_kernel_parts() {
    let replacement = CapturedModuleBytes {
        ir: Some(fixture!("compiled-nat/replacement", "ir")),
        ir_signature: Some(fixture!("compiled-nat/replacement", "ir.sig")),
        ..original()
    };
    assert_eq!(literal_offset(original()), BigNat::from_u64(1));
    assert_eq!(literal_offset(replacement), BigNat::from_u64(2));
}
