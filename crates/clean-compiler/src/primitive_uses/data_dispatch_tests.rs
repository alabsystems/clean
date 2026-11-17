// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Same actual emitter invocation for bounded observations and ordinary DATA.
use super::*;
use crate::emit_trust_ir::{serialize_module_bytes, RuntimeLowering, TrustIrConfig};
use crate::ir::{FnId, IRArg, IRBody, VarId};
use clean_kernel::Name;

fn caller(trace: &PrimitiveUseObservations, artifact: &RecordedArtifact) -> Option<Name> {
    let input = trace.artifact(artifact.parent()?)?;
    let declaration = trace.artifact(input.parent()?)?;
    match declaration.payload() {
        ArtifactPayload::IrDeclarations(decls) if decls.len() == 1 => Some(decls[0].name.clone()),
        _ => None,
    }
}

fn declarations() -> Vec<IRDecl> {
    let primitive = || FnId(Name::from_string("UInt64.add"));
    [
        (
            "value",
            vec![],
            IRType::Object,
            IRExpr::Apply {
                fn_id: primitive(),
                args: vec![],
            },
        ),
        (
            "partial",
            vec![],
            IRType::Object,
            IRExpr::PartialApply {
                fn_id: primitive(),
                arity: 2,
                args: vec![],
            },
        ),
        (
            "boxed",
            vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
            IRType::UInt64,
            IRExpr::Apply {
                fn_id: primitive(),
                args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
            },
        ),
    ]
    .into_iter()
    .map(|(label, params, ty, value)| IRDecl {
        name: Name::from_string(&format!("observedNativeSupply_{label}")),
        params,
        return_type: ty.clone(),
        body: IRBody::VDecl {
            var: VarId(2),
            ty,
            value,
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    })
    .collect()
}

#[test]
fn actual_native_arithmetic_data_and_bounded_decisions_share_one_emitted_module() {
    for decl in declarations() {
        let config = TrustIrConfig {
            runtime_lowering: RuntimeLowering::ExternCalls,
            ..TrustIrConfig::default()
        };
        let legacy = crate::emit_trust_ir::emit_trust_ir_with_supply_data(
            std::slice::from_ref(&decl),
            &config,
        )
        .unwrap();
        let recorder = ObservationRecorder::new(ObservationLimits::default());
        let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
        let observed = crate::emit_trust_ir::emit_trust_ir_recording_data(
            std::slice::from_ref(&decl),
            &config,
            Some(&frame),
        )
        .unwrap();
        let trace = recorder.finish();
        assert_eq!(
            serialize_module_bytes(&legacy.module).unwrap(),
            serialize_module_bytes(&observed.module).unwrap()
        );
        assert_eq!(
            serde_json::to_value(&legacy.native_arithmetic_supplies).unwrap(),
            serde_json::to_value(&observed.native_arithmetic_supplies).unwrap()
        );
        assert_eq!(
            serde_json::to_value(&legacy.native_arithmetic_uses).unwrap(),
            serde_json::to_value(&observed.native_arithmetic_uses).unwrap()
        );
        assert_eq!(observed.native_arithmetic_supplies.len(), 1);
        assert_eq!(observed.native_arithmetic_uses.len(), 1);
        let usage = &observed.native_arithmetic_uses[0];
        assert_eq!(usage.source_result, Some(VarId(2)));
        use crate::emit_trust_ir::NativeArithmeticUseKind;
        match (&decl.body, &usage.kind) {
            (
                IRBody::VDecl {
                    value: IRExpr::PartialApply { .. },
                    ..
                },
                NativeArithmeticUseKind::PartialApply { .. },
            ) => {}
            (
                IRBody::VDecl {
                    value: IRExpr::Apply { args, .. },
                    ..
                },
                NativeArithmeticUseKind::FunctionValue,
            ) if args.is_empty() => {}
            (
                IRBody::VDecl {
                    value: IRExpr::Apply { args, .. },
                    ..
                },
                NativeArithmeticUseKind::BoxedApply { .. },
            ) if args.len() == 2 => {
                let read = usage
                    .scalar_read
                    .as_ref()
                    .expect("actual boxed scalar read");
                assert!(trace.artifacts().iter().any(|artifact| matches!(artifact.payload(),ArtifactPayload::EmissionOperation(EmissionOperation::Call {callee,arguments}) if *callee==read.reader && arguments.as_ref()==[read.object]) && caller(&trace,artifact).as_ref()==Some(&usage.caller_name)));
            }
            _ => panic!("actual emitted use kind differs from ordinary input"),
        }
        let actual_callee = usage.runtime_entry.unwrap_or(usage.target);
        assert!(trace.artifacts().iter().any(|artifact|matches!(artifact.payload(),ArtifactPayload::EmissionOperation(EmissionOperation::Call { callee, arguments }) if *callee==actual_callee && arguments.as_ref()==usage.call_args.as_slice()) && caller(&trace,artifact).as_ref()==Some(&usage.caller_name)),"actual invocation must retain its actual call, not an inferred permission");
        assert!(trace.artifacts().iter().any(|artifact|matches!(artifact.payload(),ArtifactPayload::EmissionOperation(EmissionOperation::Value(result)) if *result==usage.result) && caller(&trace,artifact).as_ref()==Some(&usage.caller_name)));
        let tiny = ObservationRecorder::new(ObservationLimits::new(1, 1, 1, 1, 1).unwrap());
        let frame = tiny.frame(InvocationRole::Consumed, 0, 0);
        let limited = crate::emit_trust_ir::emit_trust_ir_recording_data(
            std::slice::from_ref(&decl),
            &config,
            Some(&frame),
        )
        .unwrap();
        let limited_trace = tiny.finish();
        assert_eq!(
            serialize_module_bytes(&legacy.module).unwrap(),
            serialize_module_bytes(&limited.module).unwrap()
        );
        assert_eq!(
            limited.native_arithmetic_uses.len(),
            1,
            "normal producer DATA is not an optional covered/empty record"
        );
        assert!(limited_trace
            .gaps()
            .iter()
            .any(|gap| matches!(gap, ObservationGap::Truncated(_))));
    }
}
