// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Ordinary wide IR inputs must not exceed their recording allowance.
use super::*;
use crate::emit_trust_ir::{serialize_module_bytes, RuntimeLowering, TrustIrConfig};
use crate::ir::{IRArg, IRBody, JoinPointId, VarId};
use clean_kernel::Name;

const WIDTH: usize = 1024;
fn parameters(start: u32) -> Vec<(VarId, IRType)> {
    (start..start + WIDTH as u32)
        .map(|id| (VarId(id), IRType::UInt64))
        .collect()
}
fn control(decl: IRDecl) {
    let payload = WIDTH * size_of::<(VarId, IRType)>();
    let limits = ObservationLimits::new(10000, 10000, 10, payload - 1, 1000000).unwrap();
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let legacy =
        crate::emit_trust_ir::emit_trust_ir_with_config(std::slice::from_ref(&decl), &config);
    let recorder = ObservationRecorder::new(limits);
    let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
    let recorded = crate::emit_trust_ir::emit_trust_ir_recording(
        std::slice::from_ref(&decl),
        &config,
        Some(&frame),
    );
    let trace = recorder.finish();
    match (legacy, recorded) {
        (Ok(a), Ok(b)) => assert_eq!(
            serialize_module_bytes(&a).unwrap(),
            serialize_module_bytes(&b).unwrap()
        ),
        (Err(a), Err(b)) => assert_eq!(a.to_string(), b.to_string()),
        _ => panic!("recording changed ordinary compiler output/refusal"),
    }
    assert!(trace.gaps().iter().any(|gap|matches!(gap,ObservationGap::Truncated(ObservationLimit::Bytes))),"complete cloned parameter payload alone exceeds byte allowance: tuple={},type={},var={}, limit={}, trace={trace:?}",size_of::<(VarId,IRType)>(),size_of::<IRType>(),size_of::<VarId>(),limits.byte_limit());
    assert!(
        trace
            .artifacts()
            .iter()
            .all(|artifact| !matches!(artifact.payload(), ArtifactPayload::IrDeclarations(_))),
        "wide input clone must be refused before retention"
    );
    assert!(trace.retained_bytes() <= limits.byte_limit());
}
#[test]
fn wide_declaration_parameter_tuples_refuse_before_clone_and_preserve_compiler_result() {
    control(IRDecl {
        name: Name::from_string("ordinaryWideDecl"),
        params: parameters(0),
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    });
}
#[test]
fn wide_join_parameter_tuples_refuse_before_clone_and_preserve_compiler_result() {
    control(IRDecl {
        name: Name::from_string("ordinaryWideJoin"),
        params: vec![(VarId(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: parameters(1),
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    });
}
