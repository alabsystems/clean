// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The shared projection rule must read the actual instance field, keep
//! runtime-substituted meanings opaque, and leave unsupported shapes intact.

use super::projection::instance_field_is_argument;
use super::*;
use crate::lcnf::Param;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY};

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn fv(id: u64) -> Arg {
    Arg::FVar(FVarId::new(id))
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn probe(instance: &str, inst_args: Vec<Arg>, method_args: Vec<Arg>) -> Decl {
    let call = |name: &str, args| LetValue::Const {
        name: n(name),
        levels: vec![],
        args,
    };
    Decl {
        name: n("project_instance_probe"),
        level_params: vec![],
        ty: Expr::arrow(nat(), Expr::arrow(nat(), nat())),
        params: vec![
            Param::new(FVarId::new(1), n("index"), nat()),
            Param::new(FVarId::new(2), n("value"), nat()),
        ],
        body: DeclValue::Code(Box::new(Code::Let(
            LetDecl::new(
                FVarId::new(3),
                n("dict"),
                Expr::const_str("lcAny"),
                call(instance, inst_args),
            ),
            Box::new(Code::Let(
                LetDecl::new(
                    FVarId::new(4),
                    n("result"),
                    nat(),
                    call("OfNat.ofNat", method_args),
                ),
                Box::new(Code::Return(FVarId::new(4))),
            )),
        ))),
        recursive: false,
    }
}

fn prelude_probe() -> Decl {
    probe("instOfNatNat", vec![fv(2)], vec![Arg::Erased, fv(2), fv(3)])
}

/// Close the two Nat parameters at different values. The ordinary pipeline's
/// new rule is deliberately the existing parameter-free Fragment-5 scope.
fn close_probe(mut decl: Decl) -> Decl {
    let DeclValue::Code(mut body) = decl.body else {
        panic!("probe is code");
    };
    for (param, value) in decl.params.drain(..).zip([7, 11]).rev() {
        body = Box::new(Code::Let(
            LetDecl::new(param.fvar_id, param.name, param.ty, LetValue::nat(value)),
            body,
        ));
    }
    decl.ty = nat();
    decl.body = DeclValue::Code(body);
    decl
}

fn assert_forwards_value(env: &Environment, decl: &Decl) {
    let out = resolve_known_instances(&close_probe(decl.clone()), env);
    let DeclValue::Code(code) = out.body else {
        panic!("probe remains code");
    };
    let Code::Let(value, body) = *code else {
        panic!("the actual value binding should survive");
    };
    assert_eq!(value.fvar_id, FVarId::new(2));
    assert_eq!(value.value, LetValue::nat(11));
    let Code::Let(result, body) = *body else {
        panic!("only the forwarded result should follow the value binding");
    };
    assert_eq!(result.fvar_id, FVarId::new(4));
    assert_eq!(
        result.value,
        LetValue::FVar {
            fvar: FVarId::new(2),
            args: vec![],
        },
        "forward the actual field argument, not the numeral's index"
    );
    assert_eq!(*body, Code::Return(FVarId::new(4)));
}

fn assert_unchanged(env: &Environment, decl: &Decl) {
    let decl = close_probe(decl.clone());
    assert_eq!(
        resolve_known_instances(&decl, env),
        decl,
        "an unsupported or substituted application remains exactly intact"
    );
}

#[test]
fn test_project_instance_argument_keeps_open_declarations_on_the_existing_path() {
    let env = Environment::with_prelude();
    let decl = prelude_probe();
    assert_eq!(resolve_known_instances(&decl, &env), decl);
}

fn register(env: &mut Environment, name: &str) {
    env.register_instance(KernelInstanceInfo {
        name: n(name),
        class_name: n("OfNat"),
        priority: DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
}

fn clone_definition(env: &mut Environment, from: &str, to: &str) {
    let info = env
        .get_const(&n(from))
        .expect("existing definition")
        .clone();
    env.add_decl(Declaration::Definition {
        name: n(to),
        level_params: info.level_params,
        type_: info.type_,
        value: info.value.expect("definition value"),
        is_reducible: true,
    })
    .expect("the renamed definition kernel-checks");
}

/// A kernel-checked instance whose numeral index n and returned value m are
/// different parameters. A spelling-based OfNat rewrite would pick n.
fn add_two_argument_instance(env: &mut Environment, name: &str, field: Expr) {
    let ofnat = |index| {
        Expr::apps(
            Expr::const_(n("OfNat"), vec![Level::zero()]),
            [nat(), index],
        )
    };
    let ctor = Expr::apps(
        Expr::const_(n("OfNat.mk"), vec![Level::zero()]),
        [nat(), Expr::bvar(1), field],
    );
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_: Expr::arrow(nat(), Expr::arrow(nat(), ofnat(Expr::bvar(1)))),
        value: Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(BinderInfo::Default, nat(), ctor),
        ),
        is_reducible: true,
    })
    .expect("the two-argument instance kernel-checks");
    register(env, name);
}

#[test]
fn test_project_instance_argument_normalizes_the_actual_prelude() {
    let env = Environment::with_prelude();
    assert!(!env.is_class(&n("OfNat")));
    assert_forwards_value(&env, &prelude_probe());
}

#[test]
fn test_project_instance_argument_reads_a_different_field_parameter() {
    let mut env = Environment::with_prelude();
    add_two_argument_instance(&mut env, "fieldIsSecondArgument", Expr::bvar(0));
    assert_forwards_value(
        &env,
        &probe(
            "fieldIsSecondArgument",
            vec![fv(1), fv(2)],
            vec![Arg::Erased, fv(1), fv(3)],
        ),
    );
}

#[test]
fn test_project_instance_argument_keeps_a_computed_field_dynamic() {
    let mut env = Environment::with_prelude();
    add_two_argument_instance(
        &mut env,
        "computedField",
        Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
    );
    assert_unchanged(
        &env,
        &probe(
            "computedField",
            vec![fv(1), fv(2)],
            vec![Arg::Erased, fv(1), fv(3)],
        ),
    );
}

#[test]
fn test_project_instance_argument_requires_registered_instance_custody() {
    let mut env = Environment::with_prelude();
    clone_definition(&mut env, "instOfNatNat", "renamedInstance");
    let decl = probe(
        "renamedInstance",
        vec![fv(2)],
        vec![Arg::Erased, fv(2), fv(3)],
    );
    assert_unchanged(&env, &decl);
    register(&mut env, "renamedInstance");
    assert_forwards_value(&env, &decl);
}

#[test]
fn test_project_instance_argument_refuses_runtime_substitutions_on_both_sides() {
    for original in ["OfNat.ofNat", "instOfNatNat"] {
        let mut by_impl = Environment::with_prelude();
        clone_definition(&mut by_impl, original, "replacement");
        by_impl.register_implemented_by(n(original), n("replacement"));
        assert_unchanged(&by_impl, &prelude_probe());

        let mut by_extern = Environment::with_prelude();
        by_extern.register_extern(n(original), "external_replacement".to_string());
        assert_unchanged(&by_extern, &prelude_probe());
    }
}

#[test]
fn test_project_instance_argument_requires_both_applications_saturated() {
    let env = Environment::with_prelude();
    for inst_args in [vec![], vec![fv(1), fv(2)]] {
        assert_unchanged(
            &env,
            &probe("instOfNatNat", inst_args, vec![Arg::Erased, fv(2), fv(3)]),
        );
    }
    for method_args in [
        vec![Arg::Erased, fv(2)],
        vec![Arg::Erased, fv(2), fv(3), fv(1)],
    ] {
        assert_unchanged(&env, &probe("instOfNatNat", vec![fv(2)], method_args));
    }
    assert_unchanged(
        &env,
        &probe(
            "instOfNatNat",
            vec![Arg::Erased],
            vec![Arg::Erased, fv(2), fv(3)],
        ),
    );
}

#[test]
fn test_project_instance_argument_does_not_reintroduce_noncomputable_content() {
    for original in ["OfNat.ofNat", "instOfNatNat"] {
        let mut env = Environment::with_prelude();
        env.mark_noncomputable(n(original));
        assert_unchanged(&env, &prelude_probe());
    }
}

#[test]
fn test_project_instance_argument_refuses_an_out_of_range_field() {
    let env = Environment::with_prelude();
    for field in [1, u32::MAX] {
        assert_eq!(
            instance_field_is_argument(&env, &n("instOfNatNat"), &n("OfNat"), field, 1),
            None
        );
    }
}

/// The prelude census reaches this exact source definition. Normalizing a
/// dictionary must preserve the scalar representation at UInt32.ofBitVec.
#[test]
fn test_project_instance_argument_preserves_real_char_of_nat_representation() {
    use crate::pass_manager::{compile_lcnf_decls, PassManager, PipelineConfig};

    let env = Environment::with_prelude();
    let info = env
        .get_const(&n("Char.ofNat"))
        .expect("actual prelude source");
    let decl = crate::to_lcnf::constant_to_decl(&env, info)
        .expect("Char.ofNat lowers to LCNF")
        .expect("Char.ofNat is computational");
    for pipeline in [
        PipelineConfig::default(),
        PipelineConfig {
            opt: crate::opt::OptConfig::aggressive(),
            rc: crate::rc::RCConfig::aggressive(),
            boxing: crate::boxing::BoxingConfig::default(),
        },
    ] {
        let artifacts = compile_lcnf_decls(std::slice::from_ref(&decl), &env, &pipeline)
            .unwrap_or_else(|e| {
                let manager =
                    PassManager::default_pipeline_with_config(&pipeline.opt, &pipeline.rc);
                let rc = manager.run(&decl, &env).expect("LCNF passes complete");
                panic!("actual Char.ofNat representation must lower: {e}\nRC LCNF: {rc:#?}")
            });
        assert!(
            artifacts
                .boxed_ir_decls
                .iter()
                .any(|d| d.name == n("Char.ofNat")),
            "the actual source root must survive lowering"
        );
    }
}
