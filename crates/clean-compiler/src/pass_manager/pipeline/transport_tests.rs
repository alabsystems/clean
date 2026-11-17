// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig, TrustIrError};
use crate::lcnf::{Code, DeclValue, LetDecl, LetValue};
use clean_kernel::{BinderInfo, Declaration, Expr, FVarId, Name};

fn fixture() -> (
    Environment,
    crate::RuntimeBindingClosure,
    Decl,
    TrustIrConfig,
) {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("pipelineDataIdentity32");
    let ty = Expr::const_str("UInt32");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(ty.clone(), ty.clone()),
        value: Expr::lam(BinderInfo::Default, ty, Expr::bvar(0)),
        is_reducible: false,
    })
    .unwrap();
    let closure = crate::RuntimeBindingClosure::check(&env, std::slice::from_ref(&name)).unwrap();
    let decl =
        crate::constant_to_decl_in_runtime_closure(&env, env.get_const(&name).unwrap(), &closure)
            .unwrap()
            .unwrap();
    let emit = TrustIrConfig {
        module_name: "pipeline_data_association".to_owned(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    (env, closure, decl, emit)
}

#[test]
fn pipeline_data_retains_the_actual_stages_module_and_full_tv_result() {
    let (env, closure, decl, emit) = fixture();
    let decls = [decl];
    let data = compile_lcnf_to_trust_ir_in_runtime_closure_with_artifacts(
        &decls,
        &env,
        &PipelineConfig::default(),
        &emit,
        &closure,
    )
    .unwrap();
    assert!(!data.artifacts.mono_decls.is_empty());
    assert!(!data.artifacts.boxed_ir_decls.is_empty());
    // TEST ONLY: independently emit the returned actual boxed stage and run
    // the same existing TV pass. The DATA API itself never repeats the passes.
    let emitted = data.artifacts.emit_trust_ir(&emit).unwrap();
    let (expected, report) = certify_trust_ir(emitted, &decls, &env, &emit).unwrap();
    assert_eq!(
        crate::emit_trust_ir::serialize_module_bytes(&data.module).unwrap(),
        crate::emit_trust_ir::serialize_module_bytes(&expected).unwrap(),
        "all module fields, bodies, headers and proof records belong to the returned stages",
    );
    assert_eq!(data.tv_report, report);
    let ordinary = compile_lcnf_to_trust_ir_in_runtime_closure(
        &decls,
        &env,
        &PipelineConfig::default(),
        &emit,
        &closure,
    )
    .unwrap();
    assert_eq!(
        crate::emit_trust_ir::serialize_module_bytes(&data.module).unwrap(),
        crate::emit_trust_ir::serialize_module_bytes(&ordinary).unwrap(),
    );
}

#[test]
fn pipeline_data_preserves_emitter_and_actual_tv_refusals() {
    let (env, closure, mut decl, mut emit) = fixture();
    let valid_emit = emit.clone();
    emit.target_info = None;
    let ordinary = compile_lcnf_to_trust_ir_in_runtime_closure(
        std::slice::from_ref(&decl),
        &env,
        &PipelineConfig::default(),
        &emit,
        &closure,
    )
    .unwrap_err();
    let retained = compile_lcnf_to_trust_ir_in_runtime_closure_with_artifacts(
        std::slice::from_ref(&decl),
        &env,
        &PipelineConfig::default(),
        &emit,
        &closure,
    )
    .unwrap_err();
    assert_eq!(ordinary.to_string(), retained.to_string());

    // Hold the original kernel identity fixed and deliberately propose zero
    // instead of its parameter. The actual existing kernel/TV pass must refuse.
    let result = FVarId::new(9_999);
    decl.body = DeclValue::Code(Box::new(Code::let_bind(
        LetDecl::new(
            result,
            Name::anon(),
            Expr::const_str("UInt32"),
            LetValue::nat(0),
        ),
        Code::Return(result),
    )));
    for error in [
        compile_lcnf_to_trust_ir_in_runtime_closure(
            std::slice::from_ref(&decl),
            &env,
            &PipelineConfig::default(),
            &valid_emit,
            &closure,
        )
        .unwrap_err(),
        compile_lcnf_to_trust_ir_in_runtime_closure_with_artifacts(
            &[decl],
            &env,
            &PipelineConfig::default(),
            &valid_emit,
            &closure,
        )
        .unwrap_err(),
    ] {
        assert!(
            matches!(
                error,
                PipelineError::TrustIr(TrustIrError::TranslationRefused(_))
            ),
            "{error:?}"
        );
    }
}
