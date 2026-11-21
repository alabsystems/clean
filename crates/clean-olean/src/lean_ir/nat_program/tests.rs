// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::path::Path;

use super::*;
use crate::{prepare_imported_nat_function, CapturedModuleBytes};

macro_rules! part {
    ($directory:literal, $suffix:literal) => {
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/fixtures/olean/v4.36.0/",
            $directory,
            "/StableFixture/Defs.",
            $suffix
        ))
    };
}

fn captured() -> CapturedModuleBytes<'static> {
    CapturedModuleBytes {
        canonical_path: Path::new("not-on-disk/StableFixture/Defs.olean"),
        base: part!("module-ir", "olean"),
        server: Some(part!("module-ir", "olean.server")),
        private: Some(part!("module-ir", "olean.private")),
        ir: Some(part!("module-ir", "ir")),
        ir_signature: Some(part!("module-ir", "ir.sig")),
    }
}

#[test]
fn captured_nat_program_keeps_slots_and_the_selected_ir_body() {
    let root = Name::anon().str("StableFixture").str("addOffset");
    let replacement = CapturedModuleBytes {
        ir: Some(part!("compiled-nat/replacement", "ir")),
        ir_signature: Some(part!("compiled-nat/replacement", "ir.sig")),
        ..captured()
    };
    for (capture, literal) in [(captured(), 1), (replacement, 2)] {
        let program = prepare_imported_nat_function(capture, &root)
            .unwrap()
            .expect("eligible Nat signature")
            .native_program()
            .expect("pure Nat program");
        assert_eq!(program.root(), &root);
        let [function] = program.functions() else {
            panic!("Lean inlined this provider's helper");
        };
        assert_eq!(function.name(), &root);
        assert_eq!(function.arity(), 1);
        let [CapturedNatOperation::Literal(value), CapturedNatOperation::Add { left, right }] =
            function.operations()
        else {
            panic!("expected the literal and Nat.add");
        };
        assert_eq!(*value, BigNat::from_u64(literal));
        assert_eq!((left.index(), right.index()), (0, 1));
        assert_eq!(function.result().index(), 2);
    }
}

#[test]
fn captured_nat_program_keeps_typed_private_calls_dependency_first() {
    let mut body = part!("module-ir", "ir").to_vec();
    // Substitute a call to the genuine private offset body for the inlined
    // literal. The operands point into the original compiled artifact.
    let old_expression = 0x27f0_1114_1f98_u64;
    let private_name = 0x27f0_1115_0150_u64;
    let empty_args = 0x27f0_1114_0168_u64;
    let call = 0x27f0_1115_6bc0_u64;
    assert_eq!(0x27f0_1115_0000 + body.len() as u64, call);
    assert_eq!(&body[0x878..0x880], old_expression.to_le_bytes().as_slice());
    body[0x878..0x880].copy_from_slice(&call.to_le_bytes());
    body.extend([0, 0, 0, 0, 24, 0, 2, 6]);
    body.extend(private_name.to_le_bytes());
    body.extend(empty_args.to_le_bytes());

    let capture = CapturedModuleBytes {
        ir: Some(&body),
        ..captured()
    };
    let name = Name::from_string("StableFixture.addOffset");
    let program = prepare_imported_nat_function(capture, &name)
        .unwrap()
        .unwrap()
        .native_program()
        .unwrap();
    let [private, root] = program.functions() else {
        panic!("expected the private helper before the root");
    };
    assert_eq!(private.arity(), 0);
    assert_eq!(
        private.name(),
        &Name::anon()
            .str("_private")
            .str("StableFixture")
            .str("Defs")
            .num(0)
            .str("StableFixture")
            .str("offset")
    );
    let [CapturedNatOperation::Call { target, arguments }, CapturedNatOperation::Add { .. }] =
        root.operations()
    else {
        panic!("expected the private call before the addition");
    };
    assert_eq!(target, private.name());
    assert!(arguments.is_empty());
}
