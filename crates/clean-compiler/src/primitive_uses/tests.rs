// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use clean_kernel::FVarId;

#[test]
fn zero_observation_budgets_are_not_an_empty_success() {
    for zero in 0..5 {
        let mut budgets = [10; 5];
        budgets[zero] = 0;
        assert!(
            ObservationLimits::new(budgets[0], budgets[1], budgets[2], budgets[3], budgets[4])
                .is_err()
        );
    }
}

#[test]
fn actual_retained_artifacts_cannot_be_rebound_to_an_equal_foreign_run() {
    let code = Code::Return(FVarId::new(1));
    let first = ObservationRecorder::new(ObservationLimits::default());
    let frame = first.frame(InvocationRole::Consumed, 0, 0);
    let id = frame.code("test actual input", &code).unwrap();
    let first = first.finish();
    assert!(first.artifact(&id).is_some());
    let second = ObservationRecorder::new(ObservationLimits::default());
    let frame = second.frame(InvocationRole::Consumed, 0, 0);
    let equal = frame.code("test actual input", &code).unwrap();
    let second = second.finish();
    assert_eq!(id.ordinal(), equal.ordinal());
    assert!(!id.same_run(&equal));
    assert!(second.artifact(&id).is_none());
}

#[test]
fn exhausted_observation_bytes_stay_truncated_without_repeated_work() {
    let recorder = ObservationRecorder::new(ObservationLimits::new(10, 10, 10, 1, 100).unwrap());
    let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
    let code = Code::Return(FVarId::new(1));
    assert!(frame.code("actual code", &code).is_none());
    for _ in 0..10 {
        assert!(frame.code("actual code", &code).is_none());
    }
    let result = recorder.finish();
    assert!(result.decisions().is_empty());
    assert!(matches!(
        result.gaps(),
        [ObservationGap::Truncated(ObservationLimit::Bytes)]
    ));
    assert_eq!(result.recording_work(), 0);
}

#[test]
fn diagnostic_invocation_decisions_never_enter_consumed_population() {
    let recorder = ObservationRecorder::new(ObservationLimits::default());
    for role in [
        InvocationRole::PrefixReplay(Phase::Mono),
        InvocationRole::DependencyProbe,
        InvocationRole::Consumed,
    ] {
        let frame = recorder.frame(role, 0, 0);
        let code = Code::Return(FVarId::new(1));
        let before = frame.code("real invocation input", &code);
        let after = frame.code("real invocation output", &code);
        frame.decision("real invocation", before, after, "preserved");
    }
    let result = recorder.finish();
    assert_eq!(result.decisions().len(), 1);
    assert_eq!(result.diagnostic_runs().len(), 2);
    assert!(result
        .diagnostic_runs()
        .iter()
        .all(|run| run.decisions().len() == 1));
}

fn arithmetic_decl() -> Decl {
    use crate::lcnf::{Arg, DeclValue, LetDecl};
    use clean_kernel::{Expr, Name};
    let a = FVarId::new(1);
    let b = FVarId::new(2);
    Decl {
        name: Name::from_string("observedSucc"),
        level_params: vec![],
        ty: Expr::const_str("Nat"),
        params: vec![],
        recursive: false,
        body: DeclValue::Code(Box::new(Code::let_bind(
            LetDecl::new(a, Name::anon(), Expr::const_str("Nat"), LetValue::nat(6)),
            Code::let_bind(
                LetDecl::new(
                    b,
                    Name::anon(),
                    Expr::const_str("Nat"),
                    LetValue::Const {
                        name: Name::from_string("Nat.succ"),
                        levels: vec![],
                        args: vec![Arg::FVar(a)],
                    },
                ),
                Code::Return(b),
            ),
        ))),
    }
}
fn same_pipeline(
    a: &crate::pass_manager::PipelineArtifacts,
    b: &crate::pass_manager::PipelineArtifacts,
) {
    assert_eq!(a.mono_decls, b.mono_decls);
    assert_eq!(a.optimized_decls, b.optimized_decls);
    assert_eq!(a.rc_decls, b.rc_decls);
    assert_eq!(a.ir_decls, b.ir_decls);
    assert_eq!(a.boxed_ir_decls, b.boxed_ir_decls);
    assert_eq!(a.warnings, b.warnings);
}

#[test]
fn real_mono_introduction_fold_and_later_dce_remain_in_consumed_history() {
    use crate::implemented_by::CodeMeaning;
    use crate::pass_manager::PipelineConfig;
    let declarations = [arithmetic_decl()];
    let env = clean_kernel::Environment::new();
    let config = PipelineConfig::default();
    let observed = compile_lcnf_decls_observed_for(
        &declarations,
        &env,
        &config,
        CodeMeaning::KernelValue,
        ObservationLimits::default(),
    )
    .unwrap();
    let legacy = crate::pass_manager::compile_lcnf_decls_for(
        &declarations,
        &env,
        &config,
        CodeMeaning::KernelValue,
    )
    .unwrap();
    same_pipeline(observed.artifact(), &legacy);
    let trace = observed.observations();
    assert!(trace
        .decisions()
        .iter()
        .any(|event| event.owner() == "to_mono introduced call"));
    let fold = trace.decisions().iter().find(|event| {
        event.owner() == "constant_fold decision" && matches!(trace.artifact(event.before()).unwrap().payload(), ArtifactPayload::LcnfValue(value) if matches!(value.as_ref(), LetValue::Const { name, .. } if *name == clean_kernel::Name::from_string("Nat.add")))
    }).expect("actual introduced Nat.add was attempted by maintained folding");
    let enclosing = trace
        .artifact(fold.before())
        .unwrap()
        .parent()
        .expect("actual enclosing optimizer declaration");
    assert!(
        matches!(trace.artifact(enclosing).unwrap().payload(), ArtifactPayload::LcnfDeclarations(decls) if decls.len()==1 && decls[0].name==declarations[0].name)
    );
    assert!(
        matches!(trace.artifact(fold.after().unwrap()).unwrap().payload(), ArtifactPayload::LcnfValue(value) if **value == LetValue::nat(7))
    );
    assert!(trace
        .decisions()
        .iter()
        .any(|event| event.owner() == "dce" && event.iteration() > fold.iteration()));
    assert_eq!(trace.diagnostic_runs().len(), 2);
    assert!(std::ptr::eq(
        observed.input().unwrap().declarations(),
        declarations.as_slice()
    ));
    assert!(std::ptr::eq(observed.input().unwrap().environment(), &env));
    assert!(std::ptr::eq(observed.input().unwrap().config(), &config));
}

#[test]
fn tiny_recording_limits_do_not_change_legacy_artifacts_or_forge_empty_coverage() {
    use crate::implemented_by::CodeMeaning;
    let declarations = [arithmetic_decl()];
    let env = clean_kernel::Environment::new();
    let config = crate::pass_manager::PipelineConfig::default();
    let observed = compile_lcnf_decls_observed_for(
        &declarations,
        &env,
        &config,
        CodeMeaning::KernelValue,
        ObservationLimits::new(1, 1, 1, 1, 1).unwrap(),
    )
    .unwrap();
    let legacy = crate::pass_manager::compile_lcnf_decls_for(
        &declarations,
        &env,
        &config,
        CodeMeaning::KernelValue,
    )
    .unwrap();
    same_pipeline(observed.artifact(), &legacy);
    assert!(observed
        .observations()
        .gaps()
        .iter()
        .any(|gap| matches!(gap, ObservationGap::Truncated(_))));
    assert!(observed.observations().decisions().is_empty());
    assert!(observed.input().is_none());
    assert_eq!(observed.observations().retained_contexts(), 0);
}

#[test]
fn actual_foreign_body_and_attributes_are_not_replaced_by_equal_name_identity() {
    use crate::implemented_by::CodeMeaning;
    use clean_kernel::{Declaration, Environment, Expr, Name};
    let mut env = Environment::with_prelude();
    let root = Name::from_string("observedBody");
    env.add_decl(Declaration::Definition {
        name: root.clone(),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
        value: Expr::nat_lit(1),
        is_reducible: false,
    })
    .unwrap();
    let mut foreign = env.clone();
    foreign.forget_decl(&root);
    foreign
        .add_decl(Declaration::Definition {
            name: root.clone(),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: Expr::nat_lit(2),
            is_reducible: false,
        })
        .unwrap();
    foreign.register_extern(root.clone(), "hostile_observed_body".to_owned());
    let decls = [arithmetic_decl()];
    let config = crate::pass_manager::PipelineConfig::default();
    let first = compile_lcnf_decls_observed_for(
        &decls,
        &env,
        &config,
        CodeMeaning::KernelValue,
        ObservationLimits::default(),
    )
    .unwrap();
    let second = compile_lcnf_decls_observed_for(
        &decls,
        &foreign,
        &config,
        CodeMeaning::KernelValue,
        ObservationLimits::default(),
    )
    .unwrap();
    assert_ne!(
        first
            .input()
            .unwrap()
            .environment()
            .get_const(&root)
            .unwrap()
            .value,
        second
            .input()
            .unwrap()
            .environment()
            .get_const(&root)
            .unwrap()
            .value
    );
    assert_ne!(
        first.input().unwrap().environment().get_extern(&root),
        second.input().unwrap().environment().get_extern(&root)
    );
    let id = first.observations().artifacts()[0].id();
    assert!(second.observations().artifact(id).is_none());
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn actual_module_and_dispatch_match_legacy_and_refusals_stay_typed() {
    use crate::emit_trust_ir::{serialize_module_bytes, RuntimeLowering, TrustIrConfig};
    use crate::implemented_by::CodeMeaning;
    let declarations = [arithmetic_decl()];
    let env = clean_kernel::Environment::new();
    let config = crate::pass_manager::PipelineConfig::default();
    let emit = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        certify_translation: false,
        ..TrustIrConfig::default()
    };
    let observed = compile_lcnf_to_trust_ir_observed_for(
        &declarations,
        &env,
        &config,
        &emit,
        CodeMeaning::KernelValue,
        ObservationLimits::default(),
    )
    .unwrap();
    let legacy = crate::pass_manager::compile_lcnf_to_trust_ir_with_report_for(
        &declarations,
        &env,
        &config,
        &emit,
        CodeMeaning::KernelValue,
    )
    .unwrap();
    assert_eq!(
        serialize_module_bytes(&observed.artifact().module).unwrap(),
        serialize_module_bytes(&legacy.0).unwrap()
    );
    assert!(
        observed
            .observations()
            .artifacts()
            .iter()
            .filter(|artifact| matches!(artifact.payload(), ArtifactPayload::TrustIrModule(_)))
            .count()
            >= 2
    );
    assert!(observed
        .observations()
        .decisions()
        .iter()
        .any(|event| event.owner() == "TrustIR emitter dispatch"));
    let bad = TrustIrConfig {
        target_info: None,
        ..emit
    };
    let refused = compile_lcnf_to_trust_ir_observed_for(
        &declarations,
        &env,
        &config,
        &bad,
        CodeMeaning::KernelValue,
        ObservationLimits::default(),
    )
    .unwrap_err();
    let legacy = crate::pass_manager::compile_lcnf_to_trust_ir_with_report_for(
        &declarations,
        &env,
        &config,
        &bad,
        CodeMeaning::KernelValue,
    )
    .unwrap_err();
    assert_eq!(refused.error().to_string(), legacy.to_string());
    assert!(refused
        .observations()
        .gaps()
        .iter()
        .any(|gap| matches!(gap, ObservationGap::Failed { .. })));
}

#[test]
fn each_exhausted_dynamic_budget_is_sticky_and_never_covered_empty() {
    let code = Code::Return(FVarId::new(1));
    for (limits, expected) in [
        (
            ObservationLimits::new(1, 100, 1, 100000, 1000).unwrap(),
            ObservationLimit::Events,
        ),
        (
            ObservationLimits::new(100, 1, 1, 100000, 1000).unwrap(),
            ObservationLimit::Artifacts,
        ),
        (
            ObservationLimits::new(100, 100, 1, 100000, 1).unwrap(),
            ObservationLimit::Work,
        ),
    ] {
        let recorder = ObservationRecorder::new(limits);
        let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
        for _ in 0..3 {
            let before = frame.code("actual budgeted input", &code);
            let after = frame.code("actual budgeted output", &code);
            frame.decision("actual budgeted owner", before, after, "actual attempt");
        }
        let trace = recorder.finish();
        assert!(
            trace
                .gaps()
                .iter()
                .any(|gap| matches!(gap,ObservationGap::Truncated(limit) if *limit==expected)),
            "{trace:?}"
        );
        assert!(trace.retained_bytes() <= limits.byte_limit());
        assert!(trace.recording_work() <= limits.work_limit());
    }
}

#[test]
fn unavailable_expression_payload_and_recursive_depth_remain_explicit() {
    use crate::lcnf::Arg;
    use clean_kernel::{Expr, Name};
    let recorder = ObservationRecorder::new(ObservationLimits::default());
    let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
    let value = LetValue::Const {
        name: Name::from_string("ordinaryConsumer"),
        levels: vec![],
        args: vec![Arg::Type(Expr::mdata(Default::default(), Expr::prop()))],
    };
    assert!(frame.value("actual opaque payload", &value).is_none());
    let trace = recorder.finish();
    assert!(matches!(trace.gaps(), [ObservationGap::Unobserved { .. }]));
    assert!(trace.artifacts().is_empty());
    let recorder =
        ObservationRecorder::new(ObservationLimits::new(100, 100, 1, 1000000, 1000000).unwrap());
    let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
    let mut code = Code::Return(FVarId::new(1));
    for _ in 0..258 {
        code = Code::let_bind(
            crate::lcnf::LetDecl::new(FVarId::new(1), Name::anon(), Expr::prop(), LetValue::Erased),
            code,
        );
    }
    assert!(frame.code("actual deep payload", &code).is_none());
    let trace = recorder.finish();
    assert!(trace
        .gaps()
        .iter()
        .any(|gap| matches!(gap, ObservationGap::Truncated(ObservationLimit::Depth))));
}
