// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::pass_manager::{
    compile_lcnf_decls, compile_lcnf_decls_in_runtime_closure, PipelineConfig,
};
use clean_kernel::env::{
    CompiledBefore, CompilerExternArity, CompilerExternDescriptor, CompilerExternEntry,
    CompilerExternIncomplete, CompilerExternMetadata,
};
use clean_kernel::{BinderInfo, Declaration};

fn n(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn checked_execution_binds_proof_bodies_without_compiling_their_implementations() {
    let mut base = Environment::with_prelude();
    for helper in ["proofHelper", "unsafeProofHelper"] {
        base.add_decl(Declaration::Definition {
            name: n(helper),
            level_params: vec![],
            type_: Expr::const_str("True"),
            value: Expr::const_str("True.intro"),
            is_reducible: false,
        })
        .unwrap();
    }
    base.mark_unsafe(n("unsafeProofHelper"));
    base.register_implemented_by(n("proofHelper"), n("unsafeProofHelper"));
    let program = |proof_body: &str, arg: &str| {
        let mut env = base.clone();
        env.add_decl(Declaration::Theorem {
            name: n("checkedProof"),
            level_params: vec![],
            type_: Expr::const_str("True"),
            value: Expr::const_str(proof_body),
        })
        .unwrap();
        env.add_decl(Declaration::Definition {
            name: n("entry"),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: Expr::app(
                Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str("True"),
                    Expr::nat_lit(7),
                ),
                Expr::const_str(arg),
            ),
            is_reducible: false,
        })
        .unwrap();
        env
    };
    let roots = [n("entry")];
    let env = program("proofHelper", "checkedProof");
    assert!(matches!(
        RuntimeBindingClosure::check(&env, &roots),
        Err(CompilerError::ImplementedByUnsafeTarget { .. })
    ));
    let checked = RuntimeBindingClosure::check_executable(&env, &roots).unwrap();
    assert!(checked.attributes.contains_key(&n("checkedProof")));
    assert!(!checked.attributes.contains_key(&n("proofHelper")));
    assert!(checked
        .references(&env, BTreeSet::from([n("proofHelper")]), true)
        .is_err());
    assert!(checked
        .recheck(&program("True.intro", "checkedProof"))
        .is_err());
    assert!(matches!(
        RuntimeBindingClosure::check_executable(&program("True.intro", "proofHelper"), &roots),
        Err(CompilerError::ImplementedByUnsafeTarget { .. })
    ));
}
#[test]
fn checked_execution_keeps_type_index_bindings_out_of_runtime_calls() {
    let mut env = Environment::with_prelude();
    for helper in ["index", "unsafeIndex"] {
        env.add_decl(Declaration::Definition {
            name: n(helper),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: Expr::nat_lit(3),
            is_reducible: false,
        })
        .unwrap();
    }
    env.mark_unsafe(n("unsafeIndex"));
    env.register_implemented_by(n("index"), n("unsafeIndex"));
    let index = Expr::const_str("index");
    let indexed_proof = Expr::apps(
        Expr::const_(
            n("Eq"),
            vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
        ),
        [Expr::const_str("Nat"), index.clone(), index.clone()],
    );
    for (entry, body) in [("typed", Expr::nat_lit(5)), ("live", index)] {
        env.add_decl(Declaration::Definition {
            name: n(entry),
            level_params: vec![],
            type_: Expr::arrow(indexed_proof.clone(), Expr::const_str("Nat")),
            value: Expr::lam(BinderInfo::Default, indexed_proof.clone(), body),
            is_reducible: false,
        })
        .unwrap();
    }
    let checked = RuntimeBindingClosure::check_executable(&env, &[n("typed")]).unwrap();
    assert!(checked.annotation_members.contains(&n("index")));
    assert!(!checked.attributes.contains_key(&n("index")));
    checked
        .constant(&env, env.get_const(&n("typed")).unwrap())
        .unwrap();
    let mut decl = crate::constant_to_decl_in_runtime_closure(
        &env,
        env.get_const(&n("typed")).unwrap(),
        &checked,
    )
    .unwrap()
    .unwrap();
    checked
        .declarations(&env, std::slice::from_ref(&decl))
        .unwrap();
    let result = clean_kernel::FVarId::new(999);
    decl.body = DeclValue::Code(Box::new(Code::let_bind(
        crate::lcnf::LetDecl::new(
            result,
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::const_simple(n("index")),
        ),
        Code::Return(result),
    )));
    assert!(checked
        .declarations(&env, std::slice::from_ref(&decl))
        .is_err());
    assert!(checked.transformed_declarations(&env, &[decl]).is_err());
    assert!(matches!(
        RuntimeBindingClosure::check_executable(&env, &[n("live")]),
        Err(CompilerError::ImplementedByUnsafeTarget { .. })
    ));
    assert!(matches!(
        RuntimeBindingClosure::check(&env, &[n("typed")]),
        Err(CompilerError::ImplementedByUnsafeTarget { .. })
    ));
    replace_value(&mut env, "index", Expr::nat_lit(4));
    assert!(checked.recheck(&env).is_err());
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

fn declaration_with_annotation(env: &Environment, annotation: Expr) -> Decl {
    let closure = RuntimeBindingClosure::check(env, &[n("chosen")]).unwrap();
    let mut decl = crate::constant_to_decl_in_runtime_closure(
        env,
        env.get_const(&n("chosen")).unwrap(),
        &closure,
    )
    .unwrap()
    .unwrap();
    decl.ty = Expr::arrow(annotation.clone(), annotation.clone());
    decl.params[0].ty = annotation;
    decl
}

#[test]
fn exact_internal_markers_only_in_private_compiler_stage_type_slots() {
    let mut env = environment();
    // Genuine Init also has resident compiler-marker axioms. A resident name
    // must remain a dependency in original source/kernel inputs; the private
    // compiler-stage annotation grammar is a distinct role, not a name allowlist.
    for name in ["lcAny", "lcErased"] {
        definition(&mut env, n(name), identity());
    }
    let closure = RuntimeBindingClosure::check(&env, &[n("chosen")]).unwrap();
    for annotation in [crate::to_mono::any_expr(), crate::to_mono::erased_expr()] {
        let declaration = declaration_with_annotation(&env, annotation);
        assert!(closure
            .declarations(&env, std::slice::from_ref(&declaration))
            .is_err());
        closure
            .transformed_declarations(&env, &[declaration])
            .unwrap();
    }
}

#[test]
fn internal_marker_spelling_does_not_exempt_a_resident_or_attributed_binding() {
    for name in ["lcAny", "lcErased"] {
        let mut resident = environment();
        definition(&mut resident, n(name), identity());
        let closure = RuntimeBindingClosure::check(&resident, &[n("chosen")]).unwrap();
        let declaration = declaration_with_annotation(&resident, Expr::const_str(name));
        assert!(closure.declarations(&resident, &[declaration]).is_err());

        let mut attributed = environment();
        attributed.register_extern(n(name), "not_an_internal_type".to_owned());
        let closure = RuntimeBindingClosure::check(&attributed, &[n("chosen")]).unwrap();
        let declaration = declaration_with_annotation(&attributed, Expr::const_str(name));
        assert!(closure.declarations(&attributed, &[declaration]).is_err());
    }
}

#[test]
fn marker_names_in_runtime_calls_or_original_kernel_payloads_are_not_exempt() {
    let mut env = environment();
    for name in ["lcAny", "lcErased"] {
        definition(&mut env, n(name), identity());
    }
    let closure = RuntimeBindingClosure::check(&env, &[n("chosen")]).unwrap();
    for name in ["lcAny", "lcErased"] {
        let mut declaration = declaration_with_annotation(&env, Expr::const_str("Nat"));
        declaration.body = DeclValue::Code(Box::new(Code::let_bind(
            crate::lcnf::LetDecl::new(
                clean_kernel::FVarId::new(999),
                Name::anon(),
                Expr::const_str("Nat"),
                LetValue::const_simple(n(name)),
            ),
            Code::Return(clean_kernel::FVarId::new(999)),
        )));
        assert!(closure
            .declarations(&env, std::slice::from_ref(&declaration))
            .is_err());
        assert!(closure
            .transformed_declarations(&env, &[declaration])
            .is_err());

        let mut original = env.get_const(&n("chosen")).unwrap().clone();
        original.type_ = Expr::const_str(name);
        assert!(closure.constant(&env, &original).is_err());
    }
}

#[test]
fn applied_universe_instantiated_and_term_position_markers_remain_dependencies() {
    let mut env = environment();
    for name in ["lcAny", "lcErased"] {
        definition(&mut env, n(name), identity());
    }
    let closure = RuntimeBindingClosure::check(&env, &[n("chosen")]).unwrap();
    for name in ["lcAny", "lcErased"] {
        let marker = Expr::const_str(name);
        for annotation in [
            Expr::const_(n(name), vec![clean_kernel::Level::zero()]),
            Expr::app(marker.clone(), Expr::const_str("Nat")),
            Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), marker),
        ] {
            let declaration = declaration_with_annotation(&env, annotation);
            assert!(closure
                .declarations(&env, std::slice::from_ref(&declaration))
                .is_err());
            assert!(closure
                .transformed_declarations(&env, &[declaration])
                .is_err());
        }
    }
}

#[test]
fn compiler_marker_type_role_never_exempts_owned_declaration_headers() {
    let mut env = environment();
    for name in ["lcAny", "lcErased"] {
        definition(&mut env, n(name), identity());
    }
    let closure = RuntimeBindingClosure::check(&env, &[n("chosen")]).unwrap();
    for name in ["lcAny", "lcErased"] {
        let mut declaration = declaration_with_annotation(&env, crate::to_mono::any_expr());
        declaration.name = n(name);
        assert!(closure
            .declarations(&env, std::slice::from_ref(&declaration))
            .is_err());
        assert!(closure
            .transformed_declarations(&env, &[declaration])
            .is_err());
        assert!(closure
            .constant(&env, env.get_const(&n(name)).unwrap())
            .is_err());
    }
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

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK through CLEAN_LEAN436_LIB"]
fn stable_list_cases_on_keeps_the_open_major_in_its_source_closure() {
    let env = stable_sdk_module("Init.Prelude");
    let name = n("List.casesOn");
    let closure =
        RuntimeBindingClosure::check_executable(&env, std::slice::from_ref(&name)).unwrap();
    let info = env.get_const(&name).expect("stable recursor wrapper");
    let mut decl = crate::constant_to_decl_in_runtime_closure(&env, info, &closure)
        .unwrap()
        .expect("real recursor body");
    closure
        .declarations(&env, std::slice::from_ref(&decl))
        .expect("open List α major comes from the List.casesOn binder");
    decl.ty = Expr::const_str("Object");
    let err = closure
        .declarations(&env, &[decl])
        .expect_err("an injected Object is still outside the checked source");
    assert!(err.to_string().contains("Object"), "{err}");
}

fn extern_descriptor() -> CompilerExternDescriptor {
    CompilerExternDescriptor {
        arity: CompilerExternArity::Legacy(Some(1)),
        entries: vec![
            CompilerExternEntry::Standard {
                backend: n("llvm"),
                symbol: "same-label".into(),
            },
            CompilerExternEntry::Standard {
                backend: n("backend").num(7),
                symbol: "second-symbol".into(),
            },
            CompilerExternEntry::Adhoc { backend: n("cpp") },
        ],
    }
}

fn extern_environment(metadata: CompilerExternMetadata) -> Environment {
    let mut env = environment();
    replace_value(&mut env, "chosen", call("deep"));
    env.register_extern_metadata(n("deep"), metadata)
        .expect("represented annotation data, not native admission");
    env
}

fn assert_extern_drift_refuses(env: &Environment, closure: &RuntimeBindingClosure, decl: &Decl) {
    assert!(matches!(
        crate::constant_to_decl_in_runtime_closure(
            env,
            env.get_const(&n("chosen")).expect("actual root"),
            closure,
        ),
        Err(CompilerError::RuntimeBindingClosure { .. })
    ));
    assert!(matches!(
        compile_lcnf_decls_in_runtime_closure(
            std::slice::from_ref(decl),
            env,
            &PipelineConfig::default(),
            closure,
        ),
        Err(crate::pass_manager::PipelineError::Compiler(
            CompilerError::RuntimeBindingClosure { .. }
        ))
    ));
}

#[test]
fn unchanged_complete_and_incomplete_extern_metadata_preserves_the_checked_contract() {
    for metadata in [
        CompilerExternMetadata::Complete(extern_descriptor()),
        CompilerExternMetadata::from("same-label".to_owned()),
        CompilerExternMetadata::Incomplete {
            diagnostic: "same-label".into(),
            reason: CompilerExternIncomplete::UnspecifiedSourceBinding,
        },
    ] {
        let mut env = extern_environment(metadata.clone());
        let closure = RuntimeBindingClosure::check(&env, &[n("chosen")]).expect("closure");
        let decl = crate::constant_to_decl_in_runtime_closure(
            &env,
            env.get_const(&n("chosen")).expect("root"),
            &closure,
        )
        .expect("unchanged closure")
        .expect("ordinary root body");
        env.register_extern_metadata(n("deep"), metadata.clone())
            .expect("identical metadata registration");
        assert_eq!(
            env.extern_metadata(&n("deep")).expect("metadata"),
            Some(metadata)
        );
        closure
            .recheck(&env)
            .expect("unchanged annotation contract");
        compile_lcnf_decls_in_runtime_closure(&[decl], &env, &PipelineConfig::default(), &closure)
            .expect("ordinary caller pipeline remains available");
        // Checking custody never permits lowering the extern's logical body.
        assert!(matches!(
            crate::constant_to_decl_in_runtime_closure(
                &env,
                env.get_const(&n("deep")).expect("extern declaration"),
                &closure,
            ),
            Err(CompilerError::ExternWithBody { .. })
        ));
    }
}

#[test]
fn same_diagnostic_typed_extern_changes_invalidate_actual_closure_consumers() {
    let original = extern_environment(CompilerExternMetadata::Complete(extern_descriptor()));
    let closure = RuntimeBindingClosure::check(&original, &[n("chosen")]).expect("closure");
    let decl = crate::constant_to_decl_in_runtime_closure(
        &original,
        original.get_const(&n("chosen")).expect("root"),
        &closure,
    )
    .expect("ordinary caller")
    .expect("runtime body");
    let mut descriptors = Vec::new();
    for arity in [
        CompilerExternArity::Legacy(None),
        CompilerExternArity::Unspecified,
    ] {
        let mut changed = extern_descriptor();
        changed.arity = arity;
        descriptors.push(changed);
    }
    let mut changed = extern_descriptor();
    let CompilerExternEntry::Standard { backend, .. } = &mut changed.entries[1] else {
        panic!("standard fixture")
    };
    let display_twin = n("backend").str("7");
    assert_eq!(backend.to_string(), display_twin.to_string());
    assert_ne!(*backend, display_twin);
    *backend = display_twin;
    descriptors.push(changed);
    let mut changed = extern_descriptor();
    changed.entries[1] = CompilerExternEntry::Foreign {
        backend: n("backend").num(7),
        symbol: "second-symbol".into(),
    };
    descriptors.push(changed);
    let mut changed = extern_descriptor();
    changed.entries.swap(1, 2);
    descriptors.push(changed);
    let mut changed = extern_descriptor();
    let CompilerExternEntry::Standard { symbol, .. } = &mut changed.entries[1] else {
        panic!("standard fixture")
    };
    *symbol = "changed-second-symbol".into();
    descriptors.push(changed);

    let mutations = descriptors
        .into_iter()
        .map(CompilerExternMetadata::Complete)
        .chain([CompilerExternMetadata::Incomplete {
            diagnostic: "same-label".into(),
            reason: CompilerExternIncomplete::UnspecifiedSourceBinding,
        }]);
    for metadata in mutations {
        assert_eq!(metadata.diagnostic(), "same-label");
        let mut changed = original.clone();
        changed
            .register_extern_metadata(n("deep"), metadata)
            .expect("different represented metadata");
        assert_eq!(
            changed.get_extern(&n("deep")),
            original.get_extern(&n("deep"))
        );
        RuntimeBindingClosure::check(&changed, &[n("chosen")])
            .expect("the changed data can form its own contract");
        assert_extern_drift_refuses(&changed, &closure, &decl);
    }
    let mut legacy = original.clone();
    legacy.register_extern(n("deep"), "same-label".into());
    assert_extern_drift_refuses(&legacy, &closure, &decl);
    let legacy_closure =
        RuntimeBindingClosure::check(&legacy, &[n("chosen")]).expect("legacy contract");
    legacy
        .register_extern_metadata(
            n("deep"),
            CompilerExternMetadata::Incomplete {
                diagnostic: "same-label".into(),
                reason: CompilerExternIncomplete::UnspecifiedSourceBinding,
            },
        )
        .expect("different incomplete status");
    assert_extern_drift_refuses(&legacy, &legacy_closure, &decl);
}

#[test]
fn malformed_reached_extern_carrier_refuses_closure_creation_and_recheck() {
    let original = extern_environment(CompilerExternMetadata::Complete(extern_descriptor()));
    let normalize = |mut projection: clean_kernel::env::JsonEnvironment| {
        // Only these outer vectors came from maps. Name ordering is structural;
        // declaration records, descriptor order and raw carrier bytes stay exact.
        projection.constants.sort_by(|a, b| a.name.cmp(&b.name));
        projection
            .constant_origins
            .sort_by(|a, b| a.name.cmp(&b.name));
        projection.inductives.sort_by(|a, b| a.name.cmp(&b.name));
        projection.constructors.sort_by(|a, b| a.name.cmp(&b.name));
        projection.recursors.sort_by(|a, b| a.name.cmp(&b.name));
        projection.quotients.sort_by(|a, b| a.name.cmp(&b.name));
        projection
            .structure_fields
            .sort_by(|a, b| a.struct_name.cmp(&b.struct_name));
        projection.extern_bindings.sort_by(|a, b| a.0.cmp(&b.0));
        projection
    };
    let marker = |bytes: &[u8]| {
        format!(
            "\"Object\":[{}",
            bytes
                .iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join(",")
        )
    };
    // Corrupt the actual registered raw carrier through the public JSON
    // transport. Its outer reader retains opaque bytes; metadata must refuse.
    // Retain the actual checked dependency declarations and registered carrier
    // without serializing unrelated, deeply nested Prelude declarations.
    let reached = original
        .dependency_closure(&n("chosen"))
        .expect("actual checked dependencies");
    let retained: HashSet<_> = reached.iter().cloned().collect();
    let assert_declarations = |actual: &Environment| {
        assert_eq!(
            actual
                .dependency_closure(&n("chosen"))
                .expect("closed restored declarations"),
            reached,
            "the complete reached membership must survive"
        );
        for name in &reached {
            assert_eq!(
                actual.get_const(name),
                original.get_const(name),
                "constant {name:?}"
            );
            assert_eq!(
                actual.get_inductive(name),
                original.get_inductive(name),
                "inductive {name:?}"
            );
            assert_eq!(
                actual.get_constructor(name),
                original.get_constructor(name),
                "constructor {name:?}"
            );
            assert_eq!(
                actual.get_recursor(name),
                original.get_recursor(name),
                "recursor {name:?}"
            );
            assert_eq!(
                actual.get_quot(name),
                original.get_quot(name),
                "quotient {name:?}"
            );
        }
    };
    let mut carrier = original.json_observation();
    carrier
        .constants
        .retain(|info| retained.contains(&info.name));
    carrier
        .constant_origins
        .retain(|info| retained.contains(&info.name));
    carrier
        .inductives
        .retain(|info| retained.contains(&info.name));
    carrier
        .constructors
        .retain(|info| retained.contains(&info.name));
    carrier
        .recursors
        .retain(|info| retained.contains(&info.name));
    carrier
        .quotients
        .retain(|info| retained.contains(&info.name));
    carrier
        .structure_fields
        .retain(|info| retained.contains(&info.struct_name));
    let json = serde_json::to_string(&carrier).expect("actual environment transport");
    let restored = Environment::from_json(&json).expect("uncorrupted compact carrier");
    assert_declarations(&restored);
    let expected_projection = normalize(carrier);
    assert_eq!(normalize(restored.json_observation()), expected_projection);
    assert_eq!(restored.lean_level_profile(), original.lean_level_profile());
    for name in &reached {
        assert_eq!(
            restored.get_extern(name),
            original.get_extern(name),
            "diagnostic {name:?}"
        );
        assert_eq!(
            restored
                .extern_metadata(name)
                .expect("decoded typed metadata"),
            original
                .extern_metadata(name)
                .expect("original typed metadata"),
            "full typed metadata {name:?}"
        );
    }
    // JSON does not encode every compiler attribute or environment mode. Form
    // the policy baseline from the compared projected data, not an unsupported
    // claim that the original full Environment survived this transport.
    let closure = RuntimeBindingClosure::check(&restored, &[n("chosen")])
        .expect("legitimate restored baseline");
    let unchanged = Environment::from_json(&json).expect("second uncorrupted restore");
    assert_declarations(&unchanged);
    assert_eq!(normalize(unchanged.json_observation()), expected_projection);
    closure
        .recheck(&unchanged)
        .expect("unchanged decoded data preserves its own checked contract");
    let decl = crate::constant_to_decl_in_runtime_closure(
        &unchanged,
        unchanged.get_const(&n("chosen")).expect("restored root"),
        &closure,
    )
    .expect("positive restored lowering consumer")
    .expect("runtime body");
    compile_lcnf_decls_in_runtime_closure(
        std::slice::from_ref(&decl),
        &unchanged,
        &PipelineConfig::default(),
        &closure,
    )
    .expect("positive restored pipeline consumer");
    let old_marker = marker(b"Clean.compilerExtern.v1\0");
    assert_eq!(
        json.matches(old_marker.as_str()).count(),
        1,
        "one actual raw carrier"
    );
    let corrupted = json.replacen(
        old_marker.as_str(),
        &marker(b"Clean.compilerExtern.v2\0"),
        1,
    );
    assert_ne!(
        corrupted, json,
        "the registered carrier must actually change"
    );
    let damaged = Environment::from_json(&corrupted).expect("raw carrier restoration");
    assert_declarations(&damaged);
    let mut damaged_projection = normalize(damaged.json_observation());
    let damaged_storage = damaged_projection.compiler_extern_storage.take();
    assert_ne!(damaged_storage, expected_projection.compiler_extern_storage);
    let mut expected_noncarrier = expected_projection;
    expected_noncarrier.compiler_extern_storage = None;
    assert_eq!(
        damaged_projection, expected_noncarrier,
        "only the raw carrier changes"
    );
    assert!(damaged.extern_metadata(&n("deep")).is_err());
    assert!(matches!(
        RuntimeBindingClosure::check(&damaged, &[n("chosen")]),
        Err(CompilerError::RuntimeBindingClosure { detail })
            if detail.contains("extern metadata") && detail.contains("malformed carrier")
    ));
    assert_extern_drift_refuses(&damaged, &closure, &decl);
}

fn stable_sdk_module(module: &str) -> Environment {
    let lib =
        std::path::PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").expect("official SDK"));
    let mut env = Environment::new();
    clean_olean::declare_environment_world(&mut env, clean_kernel::LeanWorld::Lean436.tag())
        .unwrap();
    clean_olean::load_module_with_deps(&mut env, module, &[lib]).unwrap();
    env
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK through CLEAN_LEAN436_LIB"]
fn stable_decidable_conditionals_and_elimination_keep_the_bool_field() {
    use crate::lcnf::Cases;
    use clean_kernel::FVarId;

    let env = stable_sdk_module("Init.Prelude");
    let root = n("Char.ofNat");
    let closure =
        RuntimeBindingClosure::check_executable(&env, std::slice::from_ref(&root)).unwrap();
    let info = env.get_const(&root).expect("stable dependent conditional");
    let decl = crate::constant_to_decl_in_runtime_closure(&env, info, &closure)
        .unwrap()
        .expect("Char.ofNat has a value");
    closure
        .declarations(&env, std::slice::from_ref(&decl))
        .expect("stable dite may only refer to operations in the actual SDK source");
    let DeclValue::Code(code) = &decl.body else {
        panic!("expected a conditional")
    };
    let mut names = Names::new(&env);
    names.code(code);
    for ctor in ["Bool.true", "Bool.false"] {
        assert!(names.found.contains(&n(ctor)), "missing {ctor}");
    }
    for old in ["Decidable.isTrue", "Decidable.isFalse"] {
        assert!(
            !names.found.contains(&n(old)),
            "fabricated constructor {old}"
        );
    }

    let decision = FVarId::new(10);
    let field = FVarId::new(11);
    let proof = FVarId::new(12);
    let params = vec![
        Param {
            fvar_id: field,
            name: n("bit"),
            ty: Expr::const_str("Bool"),
            borrow: false,
        },
        Param {
            fvar_id: proof,
            name: n("reflected"),
            ty: Expr::prop(),
            borrow: false,
        },
    ];
    let cases = Cases::new(
        n("Decidable"),
        Expr::const_str("Bool"),
        decision,
        vec![Alt::ctor(n("Decidable.intro"), params, Code::ret(field))],
    );
    let code = crate::to_mono::cases_to_mono(
        &cases,
        &mut crate::to_mono::ToMonoState::new(),
        &mut 20,
        &env,
    );
    let mut curr = &code;
    let mut used_field = false;
    while let Code::Let(decl, rest) = curr {
        if decl.fvar_id == field {
            assert!(
                matches!(&decl.value, LetValue::FVar { fvar, args } if *fvar == decision && args.is_empty())
            );
            used_field = true;
        }
        curr = rest;
    }
    assert!(used_field);
    assert!(matches!(curr, Code::Return(id) if *id == field));
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK through CLEAN_LEAN436_LIB"]
fn stable_decidable_or_keeps_its_bool_and_erases_its_scoped_reflection_theorem() {
    let env = stable_sdk_module("Init.Prelude");
    let root = n("instDecidableOr");
    let reflection = n("instDecidableOr._proof_1");
    let source = env.get_const(&root).unwrap();
    let mut source_names = HashSet::new();
    source
        .value
        .as_ref()
        .unwrap()
        .used_constants_dag(UsedConstants::ValuePositions, &mut source_names);
    assert!(source_names.contains(&reflection));
    let closure =
        RuntimeBindingClosure::check_executable(&env, std::slice::from_ref(&root)).unwrap();
    let decl = crate::constant_to_decl_in_runtime_closure(&env, source, &closure)
        .unwrap()
        .unwrap();
    closure
        .declarations(&env, std::slice::from_ref(&decl))
        .unwrap();
    let DeclValue::Code(code) = decl.body else {
        panic!("expected a compiled dictionary");
    };
    let calls = crate::to_lcnf::code_called_constant_names(&code);
    assert!(
        !calls.contains(&reflection),
        "proof scheduled as executable: {calls:?}"
    );
    assert!(
        calls.contains(&n("Decidable.decide"))
            || calls.contains(&n("Bool.or"))
            || calls.contains(&n("Bool.Internal.or")),
        "lost the Boolean calculation: {calls:?}"
    );
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK through CLEAN_LEAN436_LIB"]
fn stable_format_join_separator_erases_the_closed_sparse_match_proof() {
    let env = stable_sdk_module("Init.Data.Format.Basic");
    let root = n("_private.Init.Data.Format.Basic")
        .num(0)
        .str("Std")
        .str("Format")
        .str("joinSep")
        .str("_sparseCasesOn_1");
    let proof = n("Nat.ne_of_beq_eq_false");
    let source = env.get_const(&root).unwrap();
    let mut source_names = HashSet::new();
    source
        .value
        .as_ref()
        .unwrap()
        .used_constants_dag(UsedConstants::ValuePositions, &mut source_names);
    assert!(source_names.contains(&proof));
    let closure =
        RuntimeBindingClosure::check_executable(&env, std::slice::from_ref(&root)).unwrap();
    let decl = crate::constant_to_decl_in_runtime_closure(&env, source, &closure)
        .unwrap()
        .unwrap();
    closure
        .declarations(&env, std::slice::from_ref(&decl))
        .unwrap();
    let DeclValue::Code(code) = decl.body else {
        panic!("expected the executable list matcher");
    };
    assert!(!crate::to_lcnf::code_called_constant_names(&code).contains(&proof));
}
