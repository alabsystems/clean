// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Controls for exact decision-value normalization and compiled-meaning refusals.

use super::*;
use crate::to_lcnf::mentions::code_called_constant_names;
use clean_kernel::{Declaration, FVarId};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn call(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}

fn context(env: &Environment, width: u32, meaning: CodeMeaning) -> LcnfContext<'_> {
    let mut ctx = LcnfContext::with_meaning(env, meaning);
    for _ in 0..3 {
        ctx.push_typed_binder(&c(&format!("UInt{width}")));
    }
    ctx
}

fn terms(width: u32, strict: bool, direct: bool) -> (Expr, Expr, Expr) {
    let a = call(&format!("UInt{width}.sub"), [Expr::bvar(2), Expr::bvar(1)]);
    let b = Expr::bvar(0);
    let relation = if strict { "lt" } else { "le" };
    let p = if direct {
        call(&format!("UInt{width}.{relation}"), [a.clone(), b.clone()])
    } else {
        let class = if strict { "LT" } else { "LE" };
        Expr::apps(
            Expr::const_(
                Name::from_string(&format!("{class}.{relation}")),
                vec![Level::zero()],
            ),
            [
                c(&format!("UInt{width}")),
                c(&format!("inst{class}UInt{width}")),
                a.clone(),
                b.clone(),
            ],
        )
    };
    let op = if strict { "decLt" } else { "decLe" };
    let da = call(&format!("UInt{width}.toNat"), [a.clone()]);
    let db = call(&format!("UInt{width}.toNat"), [b.clone()]);
    (
        p,
        call(
            if strict {
                "instDecidableNatLt"
            } else {
                "instDecidableNatLe"
            },
            [da, db],
        ),
        call(&format!("UInt{width}.{op}"), [a, b]),
    )
}

#[test]
fn computed_uint_decisions_normalize_only_by_exact_kernel_value_equality_all_widths() {
    let env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let ctx = context(&env, width, CodeMeaning::LeanCompiled);
        for strict in [false, true] {
            for direct in [false, true] {
                let (p, original, expected) = terms(width, strict, direct);
                assert_eq!(normalize(&ctx, &p, &original), Some(expected.clone()));
                assert_eq!(normalize(&ctx, &p, &expected), Some(expected.clone()));
                // Exercise the alternative instance spelling on actual
                // unfolded toNat/subtraction terms, not Nat placeholders.
                let args = original.get_app_args();
                let tc = TypeChecker::with_mode(&env, env.mode());
                let unfolded = call(
                    if strict {
                        "instDecidableNatLt"
                    } else {
                        "instDecidableNatLe"
                    },
                    [tc.whnf(args[0]), tc.whnf(args[1])],
                );
                assert_eq!(normalize(&ctx, &p, &unfolded), Some(expected));
            }
        }
    }
}

#[test]
fn ordinary_ite_and_dite_lowering_call_the_checked_scalar_candidate() {
    let env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        for dependent in [false, true] {
            let mut ctx = context(&env, width, CodeMeaning::LeanCompiled);
            let (p, original, _) = terms(width, true, false);
            let (head, yes, no) = if dependent {
                (
                    "dite",
                    Expr::lam(BinderInfo::Default, p.clone(), Expr::bvar(3)),
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::arrow(p.clone(), c("False")),
                        Expr::bvar(2),
                    ),
                )
            } else {
                ("ite", Expr::bvar(2), Expr::bvar(1))
            };
            let body = Expr::apps(
                Expr::const_(Name::from_string(head), vec![Level::succ(Level::zero())]),
                [c(&format!("UInt{width}")), p, original, yes, no],
            );
            let code =
                crate::to_lcnf::expr_to_code(&mut ctx, &body).expect("actual ordinary LCNF funnel");
            let names = code_called_constant_names(&code);
            assert!(names.contains(&Name::from_string(&format!("UInt{width}.decLt"))));
            assert!(!names.contains(&Name::from_string("instDecidableNatLt")));
        }
    }
}

#[test]
fn typed_local_decidable_unknown_scope_and_malformed_values_are_not_discarded() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("counterfeit.decLt"),
        level_params: vec![],
        type_: c("Bool"),
        value: c("Bool.true"),
        is_reducible: true,
    })
    .expect("a checked Bool definition is not a Decidable value");
    let mut ctx = context(&env, 8, CodeMeaning::LeanCompiled);
    let (p, original, expected) = terms(8, true, false);
    for bad in [
        c("counterfeit.decLt"),
        call("UInt16.decLt", [Expr::bvar(2), Expr::bvar(1)]),
        call("instDecidableNatLt", [Expr::nat_lit(0u64)]),
        Expr::apps(
            Expr::const_(Name::from_string("UInt8.decLt"), vec![Level::zero()]),
            expected.get_app_args().into_iter().cloned(),
        ),
        Expr::fvar(FVarId::new(999_999)),
    ] {
        assert!(normalize(&ctx, &p, &bad).is_none());
    }
    // An arbitrary LOCAL Decidable p is not definitionally this procedure.
    ctx.push_typed_binder(&Expr::app(c("Decidable"), p.clone()));
    assert!(normalize(&ctx, &p.lift(1), &Expr::bvar(0)).is_none());
    ctx.pop_binder();
    let stale = ctx.push_typed_binder(&c("UInt8"));
    ctx.pop_binder();
    let bad_p = call("UInt8.lt", [Expr::fvar(stale), Expr::bvar(0)]);
    assert!(ctx.local_type(stale).is_some());
    assert!(normalize(&ctx, &bad_p, &original).is_none());
    // Even an irrelevant untyped active binder must not be invented a type.
    ctx.push_binder();
    assert!(normalize(&ctx, &p.lift(1), &original.lift(1)).is_none());
}

#[test]
fn actual_custom_predicate_and_decision_cannot_be_replaced_from_lt_syntax() {
    let env = Environment::with_prelude();
    let ctx = context(&env, 8, CodeMeaning::LeanCompiled);
    let (p, original, _) = terms(8, true, false);
    let args = p.get_app_args();
    // A legitimate LT dictionary whose relation is constantly False, with
    // an actual isFalse decision. This is not an ill-typed input twin.
    let dictionary = Expr::apps(
        Expr::const_(Name::from_string("LT.mk"), vec![Level::zero()]),
        [
            c("UInt8"),
            Expr::lam(
                BinderInfo::Default,
                c("UInt8"),
                Expr::lam(BinderInfo::Default, c("UInt8"), c("False")),
            ),
        ],
    );
    let changed_p = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [c("UInt8"), dictionary, args[2].clone(), args[3].clone()],
    );
    let not_false = Expr::lam(BinderInfo::Default, c("False"), Expr::bvar(0));
    let decision = call("Decidable.isFalse", [c("False"), not_false]);
    let judgment = close(&ctx, &changed_p, &decision, &decision).unwrap();
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&judgment.original, &judgment.expected)
        .expect("actual custom decision type");
    assert!(normalize(&ctx, &changed_p, &decision).is_none());
    assert!(normalize(&ctx, &changed_p, &original).is_none());
}

#[test]
fn compiled_overrides_are_guarded_transitively_without_changing_kernel_value_mode() {
    for external in [false, true] {
        let mut env = Environment::with_prelude();
        let ty = env
            .get_const(&Name::from_string("UInt8.sub"))
            .unwrap()
            .type_
            .clone();
        env.add_decl(Declaration::Definition {
            name: Name::from_string("wrappedSub"),
            level_params: vec![],
            type_: ty.clone(),
            value: c("UInt8.sub"),
            is_reducible: true,
        })
        .unwrap();
        env.add_decl(Declaration::Definition {
            name: Name::from_string("runtimeSub"),
            level_params: vec![],
            type_: ty,
            value: c("UInt8.add"),
            is_reducible: true,
        })
        .unwrap();
        if external {
            env.register_extern(
                Name::from_string("UInt8.sub"),
                "alternate_sub_runtime".to_owned(),
            );
        } else {
            env.register_implemented_by(
                Name::from_string("UInt8.sub"),
                Name::from_string("runtimeSub"),
            );
        }
        let operand = call("wrappedSub", [Expr::bvar(2), Expr::bvar(1)]);
        let p = call("UInt8.lt", [operand.clone(), Expr::bvar(0)]);
        let original = call(
            "instDecidableNatLt",
            [
                call("UInt8.toNat", [operand.clone()]),
                call("UInt8.toNat", [Expr::bvar(0)]),
            ],
        );
        let compiled = context(&env, 8, CodeMeaning::LeanCompiled);
        assert!(normalize(&compiled, &p, &original).is_none());
        let kernel = context(&env, 8, CodeMeaning::KernelValue);
        assert_eq!(
            normalize(&kernel, &p, &original),
            Some(call("UInt8.decLt", [operand, Expr::bvar(0)]))
        );
    }
}

#[test]
fn missing_types_wrong_universes_and_exhausted_budget_preserve_original_lowering() {
    let mut env = Environment::with_prelude();
    let (p, original, _) = terms(8, true, false);
    {
        let ctx = context(&env, 8, CodeMeaning::LeanCompiled);
        let args = p.get_app_args().into_iter().cloned();
        let wrong_p = Expr::apps(Expr::const_str("LT.lt"), args);
        assert!(normalize(&ctx, &wrong_p, &original).is_none());
    }
    env.set_option("maxHeartbeats".to_owned(), Some("1".to_owned()));
    let ctx = context(&env, 8, CodeMeaning::LeanCompiled);
    assert!(normalize(&ctx, &p, &original).is_none());
}

#[test]
fn compiled_mode_does_not_erase_a_used_local_callback_by_kernel_beta_reduction() {
    let env = Environment::with_prelude();
    let mut compiled = context(&env, 8, CodeMeaning::LeanCompiled);
    compiled.push_typed_binder(&Expr::arrow(c("UInt8"), c("UInt8")));
    let (p, _, expected) = terms(8, true, false);
    let p = p.lift(1);
    let expected = expected.lift(1);
    // The kernel drops the lambda argument. In compiled code the unknown
    // callback call may be evaluated before entering that lambda.
    let original = Expr::app(
        Expr::lam(BinderInfo::Default, c("UInt8"), expected.lift(1)),
        Expr::apps(Expr::bvar(0), [Expr::bvar(3)]),
    );
    assert!(normalize(&compiled, &p, &original).is_none());
    let mut kernel = context(&env, 8, CodeMeaning::KernelValue);
    kernel.push_typed_binder(&Expr::arrow(c("UInt8"), c("UInt8")));
    assert_eq!(normalize(&kernel, &p, &original), Some(expected));
}
