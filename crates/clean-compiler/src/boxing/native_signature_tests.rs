// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sparse native calls preserve actual scalar operands without inventing casts.

use super::native_signature::checked_uint_signature;
use super::{explicit_boxing_with_config, explicit_boxing_with_kernel_env, BoxingConfig};
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};

fn call(name: &str, args: &[u32]) -> IRExpr {
    IRExpr::Apply {
        fn_id: FnId(Name::from_string(name)),
        args: args.iter().map(|v| IRArg::Var(VarId(*v))).collect(),
    }
}

fn subject(param: IRType, result: IRType) -> IRDecl {
    IRDecl {
        name: Name::from_string("sparseMask"),
        params: vec![(VarId(0), param.clone()), (VarId(1), param)],
        return_type: result.clone(),
        body: IRBody::VDecl {
            var: VarId(2),
            ty: result,
            value: call("UInt32.land", &[0, 1]),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    }
}

#[test]
fn native_signature_reads_all_checked_fixed_width_primitive_declarations() {
    let env = Environment::with_prelude();
    for (width, ty) in [
        (8, IRType::UInt8),
        (16, IRType::UInt16),
        (32, IRType::UInt32),
        (64, IRType::UInt64),
    ] {
        let mut operations = vec!["add", "sub", "mul", "land", "lor"];
        if cfg!(feature = "trust-ir-backend") {
            operations.extend(["decEq", "decLt", "decLe"]);
        }
        for op in operations {
            let name = Name::from_string(&format!("UInt{width}.{op}"));
            assert_eq!(
                checked_uint_signature(&env, &name),
                Some((
                    ty.clone(),
                    if op.starts_with("dec") {
                        IRType::Bool
                    } else {
                        ty.clone()
                    }
                )),
                "{name}"
            );
        }
    }
}

#[test]
fn native_signature_sparse_nested_mask_preserves_existing_scalar_operands() {
    let env = Environment::with_prelude();
    let mut decl = subject(IRType::UInt32, IRType::UInt32);
    let IRBody::VDecl { rest, .. } = &mut decl.body else {
        panic!("fixture")
    };
    **rest = IRBody::VDecl {
        var: VarId(3),
        ty: IRType::UInt32,
        value: call("UInt32.lor", &[2, 1]),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
    };
    let config = BoxingConfig::minimal();
    let boxed = explicit_boxing_with_kernel_env(std::slice::from_ref(&decl), &env, &config);
    assert_eq!(
        boxed,
        vec![decl.clone()],
        "no Box, Unbox, or synthetic provider is needed"
    );
    let unknown = explicit_boxing_with_config(std::slice::from_ref(&decl), &config);
    assert_ne!(
        unknown[0].body, decl.body,
        "the old unknown-callee path boxes its operands"
    );
}

fn checked_metadata(name: Name, ty: Expr, levels: Vec<Name>) -> Environment {
    let mut env = Environment::default();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("UInt32"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("checked type declaration");
    env.add_decl(Declaration::Axiom {
        name,
        level_params: levels,
        type_: ty,
    })
    .expect("the deliberately different source signature is itself checked");
    env
}

#[test]
fn native_signature_refuses_missing_mismatched_dependent_and_universe_metadata() {
    let name = Name::from_string("UInt32.land");
    let u = Expr::const_str("UInt32");
    let binary = Expr::arrow(u.clone(), Expr::arrow(u.clone(), u.clone()));
    assert!(checked_uint_signature(&Environment::default(), &name).is_none());
    for (ty, levels) in [
        (Expr::arrow(u.clone(), u.clone()), vec![]),
        (Expr::arrow(u.clone(), binary.clone()), vec![]),
        (
            Expr::arrow(u.clone(), Expr::arrow(u.clone(), Expr::type_())),
            vec![],
        ),
        (
            Expr::pi(
                BinderInfo::Default,
                Expr::type_(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
            vec![],
        ),
        (binary.clone(), vec![Name::from_string("u")]),
    ] {
        let env = checked_metadata(name.clone(), ty, levels);
        assert!(checked_uint_signature(&env, &name).is_none());
    }
    let twin = Name::anon().str("UInt32.land");
    assert_ne!(twin, name);
    let env = checked_metadata(twin.clone(), binary, vec![]);
    assert!(
        checked_uint_signature(&env, &twin).is_none(),
        "display is not source identity"
    );
}

#[test]
fn native_signature_does_not_unbox_unknown_operands_or_repair_a_wrong_result() {
    let env = Environment::with_prelude();
    for (param, result) in [
        (IRType::Object, IRType::UInt32),
        (IRType::UInt64, IRType::UInt32),
        (IRType::UInt32, IRType::Object),
    ] {
        let decl = subject(param, result);
        let config = BoxingConfig::minimal();
        let original = explicit_boxing_with_config(std::slice::from_ref(&decl), &config);
        let checked = explicit_boxing_with_kernel_env(std::slice::from_ref(&decl), &env, &config);
        assert_eq!(
            checked, original,
            "keep every original type refusal; no new cast"
        );
        #[cfg(feature = "trust-ir-backend")]
        {
            let cfg = crate::emit_trust_ir::TrustIrConfig {
                runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
                ..Default::default()
            };
            crate::emit_trust_ir::emit_trust_ir_with_config(&checked, &cfg)
                .expect_err("the emitter/independent validator must still refuse this mismatch");
        }
    }
}

#[test]
fn native_signature_preserves_partial_and_zero_argument_boxed_value_paths() {
    let env = Environment::with_prelude();
    for value in [
        IRExpr::PartialApply {
            fn_id: FnId(Name::from_string("UInt32.land")),
            arity: 2,
            args: vec![IRArg::Var(VarId(0))],
        },
        call("UInt32.land", &[]),
    ] {
        let mut decl = subject(IRType::UInt32, IRType::Object);
        let IRBody::VDecl { value: target, .. } = &mut decl.body else {
            panic!("fixture")
        };
        *target = value;
        let config = BoxingConfig::minimal();
        assert_eq!(
            explicit_boxing_with_kernel_env(std::slice::from_ref(&decl), &env, &config),
            explicit_boxing_with_config(std::slice::from_ref(&decl), &config),
            "no signature stub may redirect a native primitive's boxed value ABI"
        );
    }
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn native_signature_decision_requires_actual_checked_predicate_and_body() {
    let name = Name::from_string("UInt32.decLt");
    let mut env = Environment::with_prelude();
    let original = env.get_const(&name).unwrap().clone();
    env.forget_decl(&name);
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: original.type_.clone(),
    })
    .unwrap();
    assert!(
        checked_uint_signature(&env, &name).is_none(),
        "an assumed signature cannot supply a checked native definition"
    );
    env.forget_decl(&name);
    let le = env
        .get_const(&Name::from_string("UInt32.decLe"))
        .unwrap()
        .clone();
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: le.type_,
        value: Expr::const_str("UInt32.decLe"),
        is_reducible: true,
    })
    .unwrap();
    assert!(
        checked_uint_signature(&env, &name).is_none(),
        "the same primitive name cannot turn a different checked predicate into LT"
    );
    env.forget_decl(&name);
    let u = Expr::const_str("UInt32");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), Expr::const_str("Bool"))),
        value: Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::lam(BinderInfo::Default, u, Expr::const_str("Bool.true")),
        ),
        is_reducible: true,
    })
    .unwrap();
    assert!(
        checked_uint_signature(&env, &name).is_none(),
        "an arbitrary Bool function is not a Decidable erasure"
    );
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn native_signature_sparse_decision_preserves_scalars_and_bool_result() {
    let env = Environment::with_prelude();
    let mut decl = subject(IRType::UInt32, IRType::Bool);
    let IRBody::VDecl { value, .. } = &mut decl.body else {
        unreachable!()
    };
    *value = call("UInt32.decLt", &[0, 1]);
    let boxed = explicit_boxing_with_kernel_env(
        std::slice::from_ref(&decl),
        &env,
        &BoxingConfig::minimal(),
    );
    assert_eq!(
        boxed,
        vec![decl],
        "no synthetic unbox, cast, result repair or provider body"
    );
}
