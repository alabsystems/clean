// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::path::Path;

use super::*;

macro_rules! part {
    ($suffix:literal) => {
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/fixtures/olean/v4.36.0/module-ir/StableFixture/Defs.",
            $suffix
        ))
    };
}

fn captured() -> CapturedModuleBytes<'static> {
    CapturedModuleBytes {
        canonical_path: Path::new("absent-on-disk/StableFixture/Defs.olean"),
        base: part!("olean"),
        server: Some(part!("olean.server")),
        private: Some(part!("olean.private")),
        ir: Some(part!("ir")),
        ir_signature: Some(part!("ir.sig")),
    }
}

#[test]
fn captured_nat_executes_the_real_split_lean436_ir() {
    let input = BigNat::from_u64(20);
    let twice = Name::from_string("StableFixture.twice");
    let prepared = prepare_imported_nat_function(captured(), &twice)
        .expect("read exported signature")
        .expect("public Nat function");
    assert_eq!(prepared.arity(), 1);
    let doubled = prepared.evaluate(&[input]).expect("execute split IR");
    assert_eq!(doubled, BigNat::from_u64(40));
    let offset = Name::from_string("StableFixture.addOffset");
    assert_eq!(
        evaluate_imported_nat_function(captured(), &offset, &[doubled]).unwrap(),
        BigNat::from_u64(41)
    );
    let big = BigNat::from_limbs(vec![0, 1]);
    assert_eq!(
        prepared.evaluate(&[big]).unwrap(),
        BigNat::from_limbs(vec![0, 2])
    );
}

#[test]
fn captured_nat_uses_the_replacement_ir_with_identical_declaration_parts() {
    const REPLACEMENT_SIGNATURE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/fixtures/olean/v4.36.0/compiled-nat/replacement/StableFixture/Defs.ir.sig"
    ));
    const REPLACEMENT_BODY: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/fixtures/olean/v4.36.0/compiled-nat/replacement/StableFixture/Defs.ir"
    ));
    let replacement = CapturedModuleBytes {
        ir_signature: Some(REPLACEMENT_SIGNATURE),
        ir: Some(REPLACEMENT_BODY),
        ..captured()
    };
    let twice = Name::from_string("StableFixture.twice");
    let offset = Name::from_string("StableFixture.addOffset");
    let doubled =
        evaluate_imported_nat_function(replacement, &twice, &[BigNat::from_u64(20)]).unwrap();
    assert_eq!(doubled, BigNat::from_u64(40));
    assert_eq!(
        evaluate_imported_nat_function(replacement, &offset, &[doubled]).unwrap(),
        BigNat::from_u64(42)
    );
}

#[test]
fn captured_nat_distinguishes_exported_meta_code_from_ordinary_stubs() {
    const META_BASE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/fixtures/olean/v4.36.0/meta-nat/MetaMark.olean"
    ));
    let capture = CapturedModuleBytes {
        canonical_path: Path::new("MetaMark.olean"),
        base: META_BASE,
        server: None,
        private: None,
        ir: None,
        ir_signature: None,
    };
    let marked = prepare_imported_nat_function(capture, &Name::anon().str("markedNat"))
        .unwrap()
        .unwrap();
    assert!(marked.is_marked_meta());
    assert_eq!(
        marked.evaluate(&[BigNat::from_u64(7)]).unwrap(),
        BigNat::from_u64(20)
    );
    let ordinary = prepare_imported_nat_function(capture, &Name::anon().str("ordinaryNat"))
        .unwrap()
        .unwrap();
    assert!(!ordinary.is_marked_meta());
    assert!(ordinary
        .evaluate(&[BigNat::from_u64(7)])
        .unwrap_err()
        .to_string()
        .contains("missing captured .ir.sig"));
}

#[test]
fn captured_nat_refuses_missing_and_foreign_ir_after_eligibility() {
    let function = Name::from_string("StableFixture.twice");
    let missing_signature = CapturedModuleBytes {
        ir_signature: None,
        ..captured()
    };
    let missing_body = CapturedModuleBytes {
        ir: None,
        ..captured()
    };
    for (capture, missing) in [(missing_signature, ".ir.sig"), (missing_body, ".ir")] {
        let prepared = prepare_imported_nat_function(capture, &function)
            .unwrap()
            .unwrap();
        let result = prepared
            .evaluate(&[BigNat::from_u64(20)])
            .unwrap_err()
            .to_string();
        assert!(
            result.contains(&format!("missing captured {missing}")),
            "{result}"
        );
    }

    let mut foreign_body = part!("ir").to_vec();
    foreign_body[40] = b'0';
    let foreign = CapturedModuleBytes {
        ir: Some(&foreign_body),
        ..captured()
    };
    let result = evaluate_imported_nat_function(foreign, &function, &[BigNat::from_u64(20)])
        .unwrap_err()
        .to_string();
    assert!(result.contains("StableFixture.twice"), "{result}");
    assert!(
        result.contains("registered Lean 4.36.0 artifacts"),
        "{result}"
    );
}

#[test]
fn captured_nat_checks_structural_exported_name_and_type() {
    for name in [
        Name::anon().str("StableFixture.twice"),
        Name::from_string("StableFixture.zeroRefl"),
        Name::anon()
            .str("_private")
            .str("StableFixture")
            .str("Defs")
            .num(0)
            .str("StableFixture")
            .str("offset"),
    ] {
        assert!(
            prepare_imported_nat_function(captured(), &name)
                .unwrap()
                .is_none(),
            "{name}"
        );
    }
}

#[test]
fn captured_nat_can_call_a_private_lean_ir_body() {
    // Lean inlines the private offset in addOffset. Replace that literal
    // instruction's expression with a zero-argument call to the genuine
    // private FDecl already stored in the same body part.
    let mut body = part!("ir").to_vec();
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
    let snapshot = CapturedModuleBytes {
        ir: Some(&body),
        ..captured()
    };
    let function = Name::from_string("StableFixture.addOffset");
    assert_eq!(
        evaluate_imported_nat_function(snapshot, &function, &[BigNat::from_u64(40)]).unwrap(),
        BigNat::from_u64(41)
    );
}
