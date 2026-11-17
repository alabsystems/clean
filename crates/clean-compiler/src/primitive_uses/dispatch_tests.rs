// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::emit_trust_ir::{serialize_module_bytes, RuntimeLowering, TrustIrConfig};
use crate::ir::{CtorInfo, IRArg, IRBody, VarId};
use clean_kernel::Name;

fn run(
    decl: &IRDecl,
) -> (
    PrimitiveUseObservations,
    Result<trust_ir::Module, crate::emit_trust_ir::TrustIrError>,
) {
    let recorder = ObservationRecorder::new(ObservationLimits::default());
    let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let result = crate::emit_trust_ir::emit_trust_ir_recording(
        std::slice::from_ref(decl),
        &config,
        Some(&frame),
    );
    (recorder.finish(), result)
}

#[test]
fn actual_ctor_and_object_scalar_projection_retain_consumed_layout_and_runtime_call() {
    let info = CtorInfo {
        name: Name::from_string("ordinaryObservedBox.mk"),
        tag: 0,
        num_scalars: 1,
        num_objects: 0,
        field_types: vec![IRType::UInt64],
    };
    let decl = IRDecl {
        name: Name::from_string("ordinaryObservedBoxRoundtrip"),
        params: vec![(VarId(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: info.clone(),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::UInt64,
                value: IRExpr::SProj {
                    n: 0,
                    offset: 0,
                    var: VarId(1),
                    ty: IRType::UInt64,
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    };
    let (trace, module) = run(&decl);
    let module = module.unwrap();
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let legacy =
        crate::emit_trust_ir::emit_trust_ir_with_config(std::slice::from_ref(&decl), &config)
            .unwrap();
    assert_eq!(
        serialize_module_bytes(&module).unwrap(),
        serialize_module_bytes(&legacy).unwrap()
    );
    let ctor=trace.artifacts().iter().find(|artifact|matches!(artifact.payload(),ArtifactPayload::EmitterInput{value,..} if matches!(value.as_ref(),IRExpr::Ctor{info:actual,..} if *actual==info))).unwrap();
    assert!(
        matches!(trace.artifact(ctor.parent().unwrap()).unwrap().payload(),ArtifactPayload::IrDeclarations(decls) if decls.as_ref()==[decl.clone()])
    );
    let projection=trace.artifacts().iter().find(|artifact|matches!(artifact.payload(),ArtifactPayload::EmitterInput{value,..} if matches!(value.as_ref(),IRExpr::SProj{..}))).unwrap();
    let call=trace.decisions().iter().find(|decision|decision.before()==projection.id() && decision.after().is_some_and(|id| matches!(trace.artifact(id).unwrap().payload(),ArtifactPayload::EmissionOperation(EmissionOperation::Call{arguments,..}) if arguments.len()==2))).unwrap();
    let ArtifactPayload::EmissionOperation(EmissionOperation::Call { callee, .. }) =
        trace.artifact(call.after().unwrap()).unwrap().payload()
    else {
        panic!("actual runtime call record")
    };
    assert_eq!(
        module.functions[callee.index() as usize].name,
        "clean_ctor_get_uint64"
    );
}

#[test]
fn actual_scalar_projection_identity_and_hostile_width_refusal_are_separate() {
    let mut decl = IRDecl {
        name: Name::from_string("ordinaryObservedScalarProjection"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt32,
            value: IRExpr::SProj {
                n: 7,
                offset: 123,
                var: VarId(0),
                ty: IRType::UInt32,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let (trace, result) = run(&decl);
    result.unwrap();
    assert!(trace.artifacts().iter().any(|artifact| matches!(
        artifact.payload(),
        ArtifactPayload::EmissionOperation(EmissionOperation::Route(
            "scalar SProj identity or mismatch refusal"
        ))
    )));
    decl.return_type = IRType::UInt64;
    let IRBody::VDecl {
        ty,
        value: IRExpr::SProj { ty: projected, .. },
        ..
    } = &mut decl.body
    else {
        panic!("fixture")
    };
    *ty = IRType::UInt64;
    *projected = IRType::UInt64;
    let (trace, result) = run(&decl);
    let error = result.unwrap_err();
    assert!(error.to_string().contains("scalar"), "{error}");
    assert!(trace.gaps().iter().any(|gap| matches!(
        gap,
        ObservationGap::Failed {
            owner: "TrustIR emitter",
            ..
        }
    )));
    assert!(trace.artifacts().iter().any(|artifact|matches!(artifact.payload(),ArtifactPayload::EmitterInput{operands,..} if operands.iter().any(|(_,ty,_)|*ty==Some(IRType::UInt32)))));
}
