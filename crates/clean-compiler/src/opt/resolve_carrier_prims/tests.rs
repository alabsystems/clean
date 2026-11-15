// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Comparison-only representation lowering shares the full resolver's actual
//! value-chain checks, but must not enable its other rules in ordinary code.

use super::*;
use crate::lcnf::Param;
use clean_kernel::{BinderInfo, Declaration, Level};

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn add_alias(env: &mut Environment, alias: &str, target: &str, eta: bool) {
    let info = env.get_const(&name(target)).expect("checked target");
    let ty = info.type_.clone();
    let value = if eta {
        let ExprKind::Pi(_, first_ty, rest) = ty.kind() else {
            panic!("binary comparison type");
        };
        let ExprKind::Pi(_, second_ty, _) = rest.kind() else {
            panic!("binary comparison type");
        };
        Expr::lam(
            BinderInfo::Default,
            first_ty.as_ref().clone(),
            Expr::lam(
                BinderInfo::Default,
                second_ty.as_ref().clone(),
                Expr::apps(Expr::const_str(target), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        )
    } else {
        Expr::const_str(target)
    };
    env.add_decl(Declaration::Definition {
        name: name(alias),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("checked identity alias");
}

fn call_decl(callee: &str, width: &str, args: Vec<Arg>, levels: Vec<Level>) -> Decl {
    let uint = Expr::const_str(width);
    let bool_ty = Expr::const_str("Bool");
    Decl::new(
        name("comparison_caller"),
        vec![],
        Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), bool_ty.clone())),
        vec![
            Param::new(FVarId::new(0), name("a"), uint.clone()),
            Param::new(FVarId::new(1), name("b"), uint),
        ],
        Code::Let(
            LetDecl::new(
                FVarId::new(2),
                name("decision"),
                bool_ty,
                LetValue::Const {
                    name: name(callee),
                    levels,
                    args,
                },
            ),
            Box::new(Code::Return(FVarId::new(2))),
        ),
        false,
    )
}

fn operands() -> Vec<Arg> {
    vec![Arg::FVar(FVarId::new(0)), Arg::FVar(FVarId::new(1))]
}

fn projected_shift(
    env: &Environment,
    instance: &Name,
    direction: &str,
    scope: ResolutionScope,
) -> Option<LetValue> {
    projected_shift_args(env, instance, direction, scope, &operands())
}

fn projected_shift_args(
    env: &Environment,
    instance: &Name,
    direction: &str,
    scope: ResolutionScope,
    operands: &[Arg],
) -> Option<LetValue> {
    let dict = FVarId::new(10);
    let bridge = FVarId::new(11);
    let apps = HashMap::from([
        (dict, (instance.clone(), vec![])),
        (
            bridge,
            (
                name(&format!("instHShift{direction}")),
                vec![Arg::Erased, Arg::FVar(dict)],
            ),
        ),
    ]);
    let mut args = vec![Arg::Erased, Arg::Erased, Arg::Erased, Arg::FVar(bridge)];
    args.extend_from_slice(operands);
    CarrierFolder {
        env,
        nat_handles: false,
        scope,
        apps,
        rewrites: 0,
    }
    .resolve_projected_instance(
        &name(&format!("HShift{direction}.hShift{direction}")),
        &args,
    )
}

#[test]
fn projected_instance_bridges_read_both_checked_dictionary_fields() {
    let env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        for direction in ["Left", "Right"] {
            let instance = name(&format!("instShift{direction}UInt{width}"));
            assert_eq!(
                projected_shift(&env, &instance, direction, ResolutionScope::All),
                Some(LetValue::Const {
                    name: name(&format!("UInt{width}.shift{direction}")),
                    levels: vec![],
                    args: operands()
                })
            );
            assert!(
                projected_shift(&env, &instance, direction, ResolutionScope::UIntComparisons)
                    .is_none()
            );
            for operands in [
                vec![],
                vec![Arg::FVar(FVarId::new(0))],
                vec![
                    Arg::FVar(FVarId::new(0)),
                    Arg::FVar(FVarId::new(1)),
                    Arg::Erased,
                ],
            ] {
                assert!(
                    projected_shift_args(
                        &env,
                        &instance,
                        direction,
                        ResolutionScope::All,
                        &operands
                    )
                    .is_none(),
                    "partial and overapplied bridge calls stay unresolved"
                );
            }
        }
    }
    for target in [
        "instHShiftRight",
        "HShiftRight.mk",
        "HShiftRight.hShiftRight",
        "ShiftRight.shiftRight",
        "ShiftRight.mk",
        "instShiftRightUInt64",
        "UInt64.shiftRight",
    ] {
        let mut external = env.clone();
        external.register_extern(name(target), "external_replacement".into());
        assert!(
            projected_shift(
                &external,
                &name("instShiftRightUInt64"),
                "Right",
                ResolutionScope::All
            )
            .is_none(),
            "{target}"
        );
        let mut replacement = env.clone();
        replacement.register_implemented_by(name(target), name("UInt64.sub"));
        assert!(
            projected_shift(
                &replacement,
                &name("instShiftRightUInt64"),
                "Right",
                ResolutionScope::All
            )
            .is_none(),
            "{target}"
        );
        let mut noncomputable = env.clone();
        noncomputable.mark_noncomputable(name(target));
        assert!(
            projected_shift(
                &noncomputable,
                &name("instShiftRightUInt64"),
                "Right",
                ResolutionScope::All
            )
            .is_none(),
            "{target}"
        );
    }
}

#[test]
fn projected_instance_resolution_follows_fields_and_refuses_runtime_substitution() {
    use clean_kernel::{KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY};
    let mut env = Environment::with_prelude();
    let instance = name("aShiftInstanceThatActuallyAdds");
    env.add_decl(Declaration::Definition {
        name: instance.clone(),
        level_params: vec![],
        type_: Expr::app(
            Expr::const_(name("ShiftRight"), vec![Level::zero()]),
            Expr::const_str("UInt64"),
        ),
        value: Expr::apps(
            Expr::const_(name("ShiftRight.mk"), vec![Level::zero()]),
            [Expr::const_str("UInt64"), Expr::const_str("UInt64.add")],
        ),
        is_reducible: true,
    })
    .expect("actual checked dictionary, different operation");
    let resolve =
        |env: &Environment| projected_shift(env, &instance, "Right", ResolutionScope::All);
    assert!(
        resolve(&env).is_none(),
        "unregistered constructor values stay outside this instance rule"
    );
    env.register_instance(KernelInstanceInfo {
        name: instance.clone(),
        class_name: name("ShiftRight"),
        priority: DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
    assert_eq!(
        resolve(&env),
        Some(LetValue::Const {
            name: name("UInt64.add"),
            levels: vec![],
            args: operands()
        })
    );
    for target in [instance.clone(), name("ShiftRight.mk"), name("UInt64.add")] {
        let mut external = env.clone();
        external.register_extern(target.clone(), "external_replacement".into());
        assert!(resolve(&external).is_none());
        let mut replacement = env.clone();
        replacement.register_implemented_by(target.clone(), name("UInt64.sub"));
        assert!(resolve(&replacement).is_none());
        let mut noncomputable = env.clone();
        noncomputable.mark_noncomputable(target);
        assert!(resolve(&noncomputable).is_none());
    }
}

#[test]
fn ordinary_comparison_aliases_read_bare_and_eta_values_at_every_width() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        for op in ["decEq", "decLt", "decLe"] {
            let carrier = format!("UInt{width}");
            let target = format!("{carrier}.{op}");
            let bare = format!("renamed{width}{op}");
            let eta = format!("eta{width}{op}");
            add_alias(&mut env, &bare, &target, false);
            add_alias(&mut env, &eta, &bare, true);
            let decl = call_decl(&eta, &carrier, operands(), vec![]);
            let result = resolve_uint_comparison_aliases(&decl, &env);
            let DeclValue::Code(code) = result.body else {
                panic!("code");
            };
            let Code::Let(binding, _) = *code else {
                panic!("comparison retained");
            };
            assert_eq!(
                binding.value,
                LetValue::Const {
                    name: name(&target),
                    levels: vec![],
                    args: operands()
                },
                "{eta} must preserve both operands in order"
            );
            assert_eq!(binding.ty, Expr::const_str("Bool"));
        }
    }
}

#[test]
fn ordinary_comparison_resolution_preserves_partial_and_overapplied_calls() {
    let env = Environment::with_prelude();
    for args in [
        vec![],
        vec![Arg::FVar(FVarId::new(0))],
        vec![
            Arg::FVar(FVarId::new(0)),
            Arg::FVar(FVarId::new(1)),
            Arg::Erased,
        ],
    ] {
        let decl = call_decl("instDecidableUInt8Lt", "UInt8", args, vec![]);
        assert_eq!(resolve_uint_comparison_aliases(&decl, &env), decl);
    }
    let decl = call_decl(
        "instDecidableUInt8Lt",
        "UInt8",
        operands(),
        vec![Level::zero()],
    );
    assert_eq!(resolve_uint_comparison_aliases(&decl, &env), decl);
}

#[test]
fn ordinary_scope_does_not_enable_bool_nat_arithmetic_or_class_rules() {
    let env = Environment::with_prelude();
    let folder = CarrierFolder {
        env: &env,
        nat_handles: false,
        scope: ResolutionScope::UIntComparisons,
        apps: HashMap::new(),
        rewrites: 0,
    };
    for callee in [
        "and",
        "or",
        "decide",
        "instDecidableEqBool",
        "instDecidableEqNat",
        "UInt64.add",
        "HAdd.hAdd",
        "OfNat.ofNat",
        "BEq.beq",
    ] {
        assert!(
            folder.resolve_alias(&name(callee), &operands()).is_none(),
            "{callee}"
        );
    }
    // In particular the narrow folder must not invoke rule 2 or rule 3.
    // Unknown/class calls, including erased dictionaries, stay byte-for-byte.
    for callee in ["HAdd.hAdd", "OfNat.ofNat", "BEq.beq", "unknownComparison"] {
        let decl = call_decl(callee, "UInt64", vec![Arg::Erased, Arg::Erased], vec![]);
        assert_eq!(resolve_uint_comparison_aliases(&decl, &env), decl);
    }
    // The existing full resolver still resolves the non-comparison Bool alias.
    let full = CarrierFolder {
        scope: ResolutionScope::All,
        ..folder
    };
    assert!(matches!(full.resolve_alias(&name("and"), &operands()),
        Some(LetValue::Const { name: target, .. }) if target == name("Bool.and")));
}

#[test]
fn comparison_alias_walk_remains_bounded_and_rejects_non_identity_eta() {
    let mut env = Environment::with_prelude();
    let mut target = "UInt64.decLt".to_owned();
    for depth in 1..=MAX_ALIAS_STEPS + 1 {
        let alias = format!("chain{depth}");
        add_alias(&mut env, &alias, &target, false);
        let decl = call_decl(&alias, "UInt64", operands(), vec![]);
        let result = resolve_uint_comparison_aliases(&decl, &env);
        assert_eq!(result != decl, depth <= MAX_ALIAS_STEPS, "depth {depth}");
        target = alias;
    }
    let uint = Expr::const_str("UInt64");
    let swapped = Expr::lam(
        BinderInfo::Default,
        uint.clone(),
        Expr::lam(
            BinderInfo::Default,
            uint.clone(),
            Expr::apps(
                Expr::const_str("UInt64.decLt"),
                [Expr::bvar(0), Expr::bvar(1)],
            ),
        ),
    );
    let duplicated = Expr::lam(
        BinderInfo::Default,
        uint.clone(),
        Expr::lam(
            BinderInfo::Default,
            uint,
            Expr::apps(
                Expr::const_str("UInt64.decLt"),
                [Expr::bvar(1), Expr::bvar(1)],
            ),
        ),
    );
    assert!(eta_alias(&swapped).is_none());
    assert!(eta_alias(&duplicated).is_none());
}
