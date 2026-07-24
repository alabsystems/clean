// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn sample_context() -> VcContext {
    VcContext {
        source: SourceLocation {
            file: "src/integration/demo.rs".to_string(),
            line: 12,
            column: 4,
            span: 4,
        },
        function_name: "demo_fn".to_string(),
        description: "demo VC".to_string(),
    }
}

fn smt_input() -> ExternalVcInput {
    ExternalVcInput::new(
        "smtlib2",
        "demo_fn",
        vec!["(> x 0)".to_string()],
        vec!["(> result x)".to_string()],
        vec!["(>= x 1)".to_string()],
    )
}

#[test]
fn vc_result_variants_construct_as_expected() {
    let valid = VcResult::Valid;
    let invalid = VcResult::Invalid {
        counterexample: "x = 0".to_string(),
    };
    let unknown = VcResult::Unknown {
        reason: "backend unsupported".to_string(),
    };
    let timeout = VcResult::Timeout;

    assert_eq!(valid, VcResult::Valid);
    assert_eq!(
        invalid,
        VcResult::Invalid {
            counterexample: "x = 0".to_string(),
        }
    );
    assert_eq!(
        unknown,
        VcResult::Unknown {
            reason: "backend unsupported".to_string(),
        }
    );
    assert_eq!(timeout, VcResult::Timeout);
}

#[test]
fn conversion_pipeline_elaborates_lean_inputs_and_expands_obligations() {
    let mut env = Environment::new();
    env.init_true_false().expect("initialize True/False");

    let pipeline = VcConversionPipeline::new(&env).with_source(SourceLocation {
        file: "src/demo.lean".to_string(),
        line: 8,
        column: 2,
        span: 6,
    });
    let vcs = pipeline
        .convert(&ExternalVcInput::new(
            "lean",
            "demo_fn",
            vec!["True".to_string()],
            vec!["False".to_string(), "True".to_string()],
            vec!["True".to_string()],
        ))
        .expect("Lean VC conversion should succeed");

    assert_eq!(vcs.len(), 3);
    assert_eq!(vcs[0].preconditions, vec![Expr::const_str("True")]);
    assert_eq!(vcs[0].postcondition, Expr::const_str("True"));
    assert_eq!(vcs[0].context.description, "invariant 1");
    assert_eq!(vcs[1].preconditions.len(), 2);
    assert_eq!(vcs[1].postcondition, Expr::const_str("False"));
    assert_eq!(vcs[2].postcondition, Expr::const_str("True"));
    assert_eq!(vcs[2].context.source.file, "src/demo.lean");
}

#[test]
fn conversion_pipeline_uses_opaque_constants_for_non_lean_inputs() {
    let env = Environment::new();
    let pipeline = VcConversionPipeline::new(&env);
    let vcs = pipeline
        .convert(&ExternalVcInput::new(
            "rust",
            "demo_fn",
            vec!["x > 0".to_string()],
            vec!["result > x".to_string()],
            vec!["x >= 1".to_string()],
        ))
        .expect("opaque conversion should succeed");

    assert_eq!(vcs.len(), 2);
    assert_eq!(
        vcs[0].preconditions,
        vec![Expr::const_str("ExternalVc.rust.demo_fn.precondition.1")]
    );
    assert_eq!(
        vcs[0].postcondition,
        Expr::const_str("ExternalVc.rust.demo_fn.invariant.1")
    );
    assert_eq!(
        vcs[1].preconditions,
        vec![
            Expr::const_str("ExternalVc.rust.demo_fn.precondition.1"),
            Expr::const_str("ExternalVc.rust.demo_fn.invariant.1"),
        ]
    );
    assert_eq!(
        vcs[1].postcondition,
        Expr::const_str("ExternalVc.rust.demo_fn.postcondition.1")
    );
}

#[test]
fn export_formats_serialize_external_vcs() {
    let input = smt_input();

    let json = String::from_utf8(VcExportFormat::Json.serialize(&input).expect("json export"))
        .expect("JSON stays UTF-8");
    let decoded: ExternalVcInput = serde_json::from_str(&json).expect("json should decode");
    assert_eq!(decoded, input);

    let protobuf = VcExportFormat::Protobuf
        .serialize(&input)
        .expect("protobuf export");
    let fields = decode_len_delimited_fields(&protobuf);
    assert_eq!(
        fields.iter().map(|(field, _)| *field).collect::<Vec<_>>(),
        vec![1, 2, 3, 4, 5]
    );
    assert_eq!(String::from_utf8(fields[0].1.clone()).unwrap(), "smtlib2");
    assert_eq!(String::from_utf8(fields[1].1.clone()).unwrap(), "demo_fn");
    assert_eq!(String::from_utf8(fields[2].1.clone()).unwrap(), "(> x 0)");
    assert_eq!(
        String::from_utf8(fields[3].1.clone()).unwrap(),
        "(> result x)"
    );
    assert_eq!(String::from_utf8(fields[4].1.clone()).unwrap(), "(>= x 1)");

    let smt = String::from_utf8(
        VcExportFormat::SmtLib2
            .serialize(&input)
            .expect("smtlib2 export"),
    )
    .expect("SMT-LIB2 stays UTF-8");
    assert!(smt.contains("(assert (> x 0))"));
    assert!(smt.contains("(assert (>= x 1))"));
    assert!(smt.contains("(assert (not (> result x)))"));
}

#[test]
fn kernel_vc_backend_returns_unknown_for_unproven_wellformed_vc() {
    let mut env = Environment::new();
    env.init_true_false().expect("initialize True/False");

    let backend = KernelVcBackend::new(&env);
    // `True → False` is a perfectly well-formed proposition that type-checks as
    // a Prop, but it is FALSE. The stub backend only checks well-formedness; it
    // never discharges a proof, so it must report Unknown rather than dishonestly
    // claiming the false VC is Valid.
    let vc = VerificationCondition {
        preconditions: vec![Expr::const_str("True")],
        postcondition: Expr::const_str("False"),
        context: sample_context(),
    };

    let result = backend.check_vc(&vc);
    let VcResult::Unknown { reason } = result else {
        panic!("expected Unknown for a well-formed but unproven VC, got: {result:?}");
    };
    assert!(
        reason.contains("no proof attempted"),
        "unexpected reason: {reason}"
    );
}

#[test]
fn kernel_vc_backend_reports_unknown_for_non_prop_vcs() {
    let mut env = Environment::new();
    env.init_true_false().expect("initialize True/False");

    let backend = KernelVcBackend::new(&env);
    // Use Type as the postcondition — `True → Type : Sort (imax 0 1) = Sort 1 = Type`,
    // which is NOT Prop. (Note: `Type → True : Sort (imax 1 0) = Sort 0 = Prop`
    // due to impredicativity, so that would actually be valid.)
    let vc = VerificationCondition {
        preconditions: vec![Expr::const_str("True")],
        postcondition: Expr::type_(),
        context: sample_context(),
    };

    let result = backend.check_vc(&vc);
    let VcResult::Unknown { reason } = result else {
        panic!("expected Unknown result for non-Prop VC, got: {result:?}");
    };
    assert!(
        reason.contains("Prop") || reason.contains("type"),
        "unexpected reason: {reason}"
    );
}

fn decode_len_delimited_fields(mut bytes: &[u8]) -> Vec<(u32, Vec<u8>)> {
    let mut fields = Vec::new();
    while !bytes.is_empty() {
        let tag = bytes[0];
        bytes = &bytes[1..];
        assert_eq!(tag & 0x07, 2, "only length-delimited fields are expected");
        let (len, used) = decode_varint(bytes);
        bytes = &bytes[used..];
        let len = len as usize;
        fields.push(((tag >> 3) as u32, bytes[..len].to_vec()));
        bytes = &bytes[len..];
    }
    fields
}

fn decode_varint(mut bytes: &[u8]) -> (u64, usize) {
    let mut value = 0_u64;
    let mut shift = 0_u32;
    let mut used = 0;
    loop {
        let byte = bytes[0];
        bytes = &bytes[1..];
        used += 1;
        value |= u64::from(byte & 0x7F) << shift;
        if byte & 0x80 == 0 {
            return (value, used);
        }
        shift += 7;
    }
}
