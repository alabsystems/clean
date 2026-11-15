// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::pass_manager::{
    compile_lcnf_decls, compile_lcnf_decls_in_runtime_closure, PipelineConfig,
};
use clean_kernel::env::CompiledBefore;
use clean_kernel::{BinderInfo, Declaration};

fn n(s: &str) -> Name {
    Name::from_string(s)
}
fn identity() -> Expr {
    Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0))
}
fn call(name: &str) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app(Expr::const_str(name), Expr::bvar(0)),
    )
}
fn definition(env: &mut Environment, name: Name, value: Expr) {
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
        value,
        is_reducible: false,
    })
    .unwrap();
}
fn environment() -> Environment {
    let mut env = Environment::with_prelude();
    for name in [
        "chosen",
        "unrelated",
        "lateSlow",
        "lateFast",
        "runtime",
        "middle",
        "deep",
    ] {
        definition(&mut env, n(name), identity());
    }
    env.record_compiled_before(vec![
        (
            n("unrelated"),
            CompiledBefore {
                rebound: n("lateSlow"),
                via: n("lateSlow"),
            },
        ),
        (
            n("lateSlow"),
            CompiledBefore {
                rebound: n("lateSlow"),
                via: n("lateSlow"),
            },
        ),
    ]);
    env.register_implemented_by(n("lateSlow"), n("lateFast"));
    env
}
fn replace_value(env: &mut Environment, name: &str, value: Expr) {
    let mut info = env.get_const(&n(name)).unwrap().clone();
    info.value = Some(value);
    env.add_constant_unchecked_for_test(info);
}

#[test]
fn explicit_closure_accepts_irrelevant_records_but_every_legacy_entry_still_refuses() {
    let env = environment();
    let closure = RuntimeBindingClosure::check(&env, &[n("chosen")]).unwrap();
    let info = env.get_const(&n("chosen")).unwrap();
    assert!(matches!(
        crate::constant_to_decl(&env, info),
        Err(CompilerError::ImplementedByOrder { .. })
    ));
    let mut ctx = crate::to_lcnf::LcnfContext::new(&env);
    assert!(matches!(
        crate::expr_to_code(&mut ctx, info.value.as_ref().unwrap()),
        Err(CompilerError::ImplementedByOrder { .. })
    ));
    let decl = crate::constant_to_decl_in_runtime_closure(&env, info, &closure)
        .unwrap()
        .unwrap();
    assert!(compile_lcnf_decls(
        std::slice::from_ref(&decl),
        &env,
        &PipelineConfig::default()
    )
    .is_err());
    compile_lcnf_decls_in_runtime_closure(&[decl], &env, &PipelineConfig::default(), &closure)
        .unwrap();
    // The full record is retained; a scoped success cannot sanitize a later legacy call.
    assert!(crate::implemented_by_order(&env)
        .unwrap()
        .contains_key(&n("lateSlow")));
}

#[test]
fn selected_and_transitive_runtime_implementation_order_conflicts_refuse() {
    let mut env = environment();
    replace_value(&mut env, "chosen", call("lateSlow"));
    assert!(matches!(
        RuntimeBindingClosure::check(&env, &[n("chosen")]),
        Err(CompilerError::RuntimeBindingOrder { .. })
    ));
    replace_value(&mut env, "chosen", call("runtime"));
    env.register_implemented_by(n("runtime"), n("middle"));
    env.register_implemented_by(n("middle"), n("deep"));
    replace_value(&mut env, "deep", call("lateSlow"));
    // Neither root nor logical runtime body mentions the late name; its implementation does.
    assert!(matches!(
        RuntimeBindingClosure::check(&env, &[n("chosen")]),
        Err(CompilerError::RuntimeBindingOrder { .. })
    ));
    replace_value(&mut env, "deep", identity());
    RuntimeBindingClosure::check(&env, &[n("chosen")]).unwrap();
    env.record_compiled_before(vec![(
        n("deep"),
        CompiledBefore {
            rebound: n("deep"),
            via: n("deep"),
        },
    )]);
    assert!(RuntimeBindingClosure::check(&env, &[n("chosen")]).is_err());
}

#[test]
fn declaration_and_compiler_attribute_mutations_invalidate_the_actual_consumers() {
    let mut original = environment();
    replace_value(&mut original, "chosen", call("runtime"));
    original.register_implemented_by(n("runtime"), n("middle"));
    original.register_implemented_by(n("middle"), n("deep"));
    let closure = RuntimeBindingClosure::check(&original, &[n("chosen")]).unwrap();
    let info = original.get_const(&n("chosen")).unwrap();
    let decl = crate::constant_to_decl_in_runtime_closure(&original, info, &closure)
        .unwrap()
        .unwrap();
    let mut mutants = Vec::new();
    let mut changed = original.clone();
    replace_value(&mut changed, "deep", call("lateFast"));
    mutants.push(changed);
    let mut changed = original.clone();
    changed.register_implemented_by(n("runtime"), n("deep"));
    mutants.push(changed);
    let mut changed = original.clone();
    changed.register_extern(n("deep"), "changed_ffi".to_owned());
    mutants.push(changed);
    let mut changed = original.clone();
    changed.mark_noncomputable(n("deep"));
    mutants.push(changed);
    let mut changed = original.clone();
    changed.record_compiled_before(vec![(
        n("deep"),
        CompiledBefore {
            rebound: n("deep"),
            via: n("deep"),
        },
    )]);
    mutants.push(changed);
    for changed in mutants {
        assert!(crate::constant_to_decl_in_runtime_closure(
            &changed,
            changed.get_const(&n("chosen")).unwrap(),
            &closure
        )
        .is_err());
        assert!(compile_lcnf_decls_in_runtime_closure(
            std::slice::from_ref(&decl),
            &changed,
            &PipelineConfig::default(),
            &closure
        )
        .is_err());
    }
}

#[test]
fn structural_names_and_submitted_batch_references_cannot_expand_a_contract() {
    let mut env = environment();
    let structured = n("Shadow.name");
    let quoted = Name::anon().str("Shadow.name");
    assert_ne!(structured, quoted);
    definition(&mut env, structured.clone(), identity());
    definition(&mut env, quoted.clone(), identity());
    let closure = RuntimeBindingClosure::check(&env, std::slice::from_ref(&structured)).unwrap();
    assert!(crate::constant_to_decl_in_runtime_closure(
        &env,
        env.get_const(&quoted).unwrap(),
        &closure
    )
    .is_err());
    let mut decl = crate::constant_to_decl_in_runtime_closure(
        &env,
        env.get_const(&structured).unwrap(),
        &closure,
    )
    .unwrap()
    .unwrap();
    decl.body = DeclValue::Code(Box::new(Code::let_bind(
        crate::lcnf::LetDecl::new(
            clean_kernel::FVarId::new(900),
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::const_simple(n("lateSlow")),
        ),
        Code::Return(clean_kernel::FVarId::new(900)),
    )));
    assert!(compile_lcnf_decls_in_runtime_closure(
        &[decl],
        &env,
        &PipelineConfig::default(),
        &closure
    )
    .is_err());
    let mut shadowed = env.clone();
    let mut info = shadowed.get_const(&structured).unwrap().clone();
    info.value = Some(call("lateFast"));
    shadowed.add_constant_unchecked_for_test(info);
    assert!(closure
        .constant(&shadowed, shadowed.get_const(&structured).unwrap())
        .is_err());
}

#[test]
fn compiler_generated_stages_cannot_introduce_existing_order_names_or_shadow_helpers() {
    let mut env = environment();
    let closure = RuntimeBindingClosure::check(&env, &[n("chosen")]).unwrap();
    let chosen = crate::constant_to_decl_in_runtime_closure(
        &env,
        env.get_const(&n("chosen")).unwrap(),
        &closure,
    )
    .unwrap()
    .unwrap();
    let mut generated = chosen.clone();
    generated.name = n("chosen.generated");
    closure
        .transformed_declarations(&env, std::slice::from_ref(&generated))
        .unwrap();
    definition(&mut env, n("chosen.generated"), identity());
    assert!(
        closure
            .transformed_declarations(&env, &[generated])
            .is_err(),
        "a generated-name collision is a resident declaration, not a fresh helper"
    );
    let mut poisoned = chosen;
    poisoned.body = DeclValue::Code(Box::new(Code::let_bind(
        crate::lcnf::LetDecl::new(
            clean_kernel::FVarId::new(901),
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::const_simple(n("lateSlow")),
        ),
        Code::Return(clean_kernel::FVarId::new(901)),
    )));
    assert!(
        closure.transformed_declarations(&env, &[poisoned]).is_err(),
        "an optimizer cannot introduce an unchecked existing runtime binding"
    );
}

#[test]
fn submitted_kernel_value_cannot_use_the_generated_type_placeholder_exemption() {
    let env = environment();
    let closure = RuntimeBindingClosure::check(&env, &[n("chosen")]).unwrap();
    let mut payload = env.get_const(&n("chosen")).unwrap().clone();
    payload.value = Some(Expr::const_str("_"));
    assert!(
        matches!(
            crate::constant_to_decl_in_runtime_closure(&env, &payload, &closure),
            Err(CompilerError::RuntimeBindingClosure { .. })
        ),
        "the policy guard must reject the out-of-closure kernel payload before lowering"
    );
}

#[test]
fn unsafe_and_partial_registry_changes_cannot_reuse_a_plain_root_contract() {
    let original = environment();
    let closure = RuntimeBindingClosure::check(&original, &[n("chosen")]).unwrap();
    let info = original.get_const(&n("chosen")).unwrap();
    let decl = crate::constant_to_decl_in_runtime_closure(&original, info, &closure)
        .unwrap()
        .unwrap();
    let mut unsafe_ = original.clone();
    unsafe_.mark_unsafe(n("chosen"));
    let mut partial = original;
    partial.mark_partial(n("chosen"));
    for changed in [unsafe_, partial] {
        assert!(crate::constant_to_decl_in_runtime_closure(
            &changed,
            changed.get_const(&n("chosen")).unwrap(),
            &closure
        )
        .is_err());
        assert!(compile_lcnf_decls_in_runtime_closure(
            std::slice::from_ref(&decl),
            &changed,
            &PipelineConfig::default(),
            &closure
        )
        .is_err());
    }
}
