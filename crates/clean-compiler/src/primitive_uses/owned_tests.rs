// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::emit_trust_ir::{serialize_module_bytes, RuntimeLowering, TrustIrConfig};
use crate::implemented_by::CodeMeaning;
use crate::lcnf::{DeclValue, LetDecl};
use crate::pass_manager::PipelineConfig;
use clean_kernel::{Environment, Expr, FVarId, Name};

fn inputs() -> (
    Arc<[Decl]>,
    Arc<Environment>,
    Arc<PipelineConfig>,
    TrustIrConfig,
) {
    let value = FVarId::new(1);
    let declaration = Decl {
        name: Name::from_string("ordinaryOwnedObserved"),
        level_params: vec![],
        ty: Expr::const_str("Nat"),
        params: vec![],
        recursive: false,
        body: DeclValue::Code(Box::new(Code::let_bind(
            LetDecl::new(
                value,
                Name::anon(),
                Expr::const_str("Nat"),
                LetValue::nat(7),
            ),
            Code::Return(value),
        ))),
    };
    (
        vec![declaration].into(),
        Arc::new(Environment::new()),
        Arc::new(PipelineConfig::default()),
        TrustIrConfig {
            runtime_lowering: RuntimeLowering::ExternCalls,
            certify_translation: false,
            ..TrustIrConfig::default()
        },
    )
}
#[test]
fn owned_frame_retains_actual_inputs_after_original_references_drop() {
    let (decls, env, config, emit) = inputs();
    let actual_env = Arc::as_ptr(&env);
    let actual_decls = decls.as_ptr();
    let legacy = crate::pass_manager::compile_lcnf_to_trust_ir_with_report_for(
        &decls,
        &env,
        &config,
        &emit,
        CodeMeaning::KernelValue,
    )
    .unwrap();
    let output = compile_lcnf_to_trust_ir_owned_observed(
        decls,
        env,
        config,
        emit,
        CodeMeaning::KernelValue,
        None,
        ObservationLimits::default(),
        |_| Ok::<_, ()>(()),
    )
    .unwrap();
    assert!(std::ptr::eq(
        output.input().unwrap().environment(),
        actual_env
    ));
    assert_eq!(
        output.input().unwrap().declarations().as_ptr(),
        actual_decls
    );
    assert_eq!(
        serialize_module_bytes(&output.artifact().module).unwrap(),
        serialize_module_bytes(&legacy.0).unwrap()
    );
    assert!(output.observations().gaps().iter().any(|gap| matches!(
        gap,
        ObservationGap::Unobserved {
            owner: "external consumer continuation",
            ..
        }
    )));
}
#[test]
fn arbitrary_mutating_consumer_is_opaque_and_never_rebound_to_pre_consumer_module() {
    let (decls, env, config, emit) = inputs();
    let output = compile_lcnf_to_trust_ir_owned_observed(
        decls,
        env,
        config,
        emit,
        CodeMeaning::KernelValue,
        None,
        ObservationLimits::default(),
        |module| {
            module.name.push_str("_after_arbitrary_callback");
            Ok::<_, ()>(())
        },
    )
    .unwrap();
    let event = output
        .observations()
        .decisions()
        .iter()
        .find(|decision| decision.owner() == "external consumer continuation")
        .unwrap();
    let before = output.observations().artifact(event.before()).unwrap();
    let after = output
        .observations()
        .artifact(event.after().unwrap())
        .unwrap();
    let (ArtifactPayload::TrustIrModule(before), ArtifactPayload::TrustIrModule(after)) =
        (before.payload(), after.payload())
    else {
        panic!("actual snapshots")
    };
    assert_ne!(
        serialize_module_bytes(before).unwrap(),
        serialize_module_bytes(after).unwrap()
    );
    assert_eq!(
        serialize_module_bytes(after).unwrap(),
        serialize_module_bytes(&output.artifact().module).unwrap()
    );
}
#[test]
fn typed_consumer_refusal_and_tiny_recording_do_not_skip_actual_continuation() {
    let (decls, env, config, emit) = inputs();
    let mut called = 0;
    let error = compile_lcnf_to_trust_ir_owned_observed(
        decls,
        env,
        config,
        emit,
        CodeMeaning::KernelValue,
        None,
        ObservationLimits::new(1, 1, 1, 1, 1).unwrap(),
        |_| {
            called += 1;
            Err::<(), _>(47u32)
        },
    )
    .unwrap_err();
    assert_eq!(called, 1);
    assert!(matches!(error.error(), OwnedPipelineError::Consumer(47)));
    assert!(error.input().is_none());
    assert!(error
        .observations()
        .gaps()
        .iter()
        .any(|gap| matches!(gap, ObservationGap::Truncated(_))));
}
