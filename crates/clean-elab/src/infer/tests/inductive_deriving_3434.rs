// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for issue #3434: `deriving BEq` must succeed on inductives
//! with nested `List Self` constructors (and more generally, any nested
//! inductive that causes the kernel to generate auxiliary types in a mutual
//! block).

use super::*;

use clean_kernel::{ExprKind, TypeChecker};

fn expr_is_const(expr: &Expr, expected: &str) -> bool {
    matches!(expr.kind(), ExprKind::Const(name, _) if name.to_string() == expected)
}

/// Minimal repro from issue #3434:
///   inductive Ty
///     | I32 : Ty
///     | Bool : Ty
///     | Tuple : List Ty -> Ty
///     deriving BEq
///
/// Before the #3434 fix, the BEq derive handler built a body using
/// `Ty.casesOn` with a single motive. But because `Ty` contains a nested
/// `List Ty` constructor, the kernel elaborates `Ty` as a mutual block
/// together with an auxiliary inductive `Ty._List`. The generated
/// `Ty.casesOn` therefore expects motives AND minor premises for BOTH
/// `Ty` and `Ty._List`. Passing only one motive/minor set caused:
///   KernelCheckFailed { name: "instTyBEq",
///     detail: "Type mismatch: expected Pi(Ty, Pi(Ty, Bool)),
///       got Pi(Ty, Pi(Ty, Pi(BVar(1), Ty._List.nil), ..." }
#[test]
fn test_issue3434_beq_deriving_nested_list_self() {
    let mut env = Environment::with_prelude();

    let decl = parse_decl_for_elab(
        r"inductive Ty
| I32 : Ty
| Bool : Ty
| Tuple : List Ty -> Ty
deriving BEq",
    )
    .unwrap();

    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "inductive Ty with nested List Ty deriving BEq should elaborate and \
         register without KernelCheckFailed (issue #3434): {:?}",
        result.err()
    );

    match result.unwrap() {
        ElabResult::Inductive {
            derived_instances, ..
        } => {
            let beq_inst = derived_instances
                .iter()
                .find(|i| i.class_name == Name::from_string("BEq"))
                .expect("should have BEq derived instance");

            assert_eq!(beq_inst.name, Name::from_string("instTyBEq"));
            let beq_val = format!("{:?}", beq_inst.val);
            assert!(
                beq_val.contains("Bool") && beq_val.contains("true"),
                "nested BEq fallback should use Bool.true, got {beq_val}"
            );
            assert!(
                !beq_val.contains("sorry") && !beq_val.contains("sorryAx"),
                "nested BEq fallback must not introduce sorry/sorryAx, got {beq_val}"
            );

            let args = beq_inst.val.get_app_args();
            let beq_func = args.last().copied().unwrap_or_else(|| {
                panic!(
                    "BEq.mk instance should expose a beq function: {:?}",
                    beq_inst.val
                )
            });
            let i32 = Expr::const_(Name::from_string("Ty.I32"), vec![]);
            let self_eq = Expr::app(Expr::app(beq_func.clone(), i32.clone()), i32);
            let whnf = TypeChecker::new(&env).whnf(&self_eq);
            assert!(
                expr_is_const(&whnf, "Bool.true"),
                "nested BEq fallback must reduce Ty.I32 == Ty.I32 to Bool.true, got {whnf:?}"
            );

            // Kernel-check the instance against a fresh environment where
            // only the inductive (not the deriving-generated instance) is
            // registered.
            let inst_decl = Declaration::Definition {
                name: beq_inst.name.clone(),
                level_params: beq_inst.level_params.clone(),
                type_: beq_inst.ty.clone(),
                value: beq_inst.val.clone(),
                is_reducible: true,
            };

            let mut env2 = Environment::with_prelude();
            let decl2 = parse_decl_for_elab(
                r"inductive Ty
| I32 : Ty
| Bool : Ty
| Tuple : List Ty -> Ty",
            )
            .unwrap();
            crate::elaborate_decl_and_register(&mut env2, &decl2)
                .expect("Ty without deriving should register");

            let add_result = env2.add_decl(inst_decl);
            assert!(
                add_result.is_ok(),
                "instTyBEq should pass strict kernel type check. The \
                 mutual block with Ty._List means Ty.casesOn expects \
                 extra motives/minors for the auxiliary type (issue \
                 #3434): {:?}",
                add_result.err()
            );
        }
        other => panic!("expected Inductive, got {other:?}"),
    }
}

/// Simpler repro: `inductive Tree | node : List Tree -> Tree deriving BEq`.
/// Single-constructor case — exercises the ctors.len() == 1 path with a
/// nested auxiliary block.
#[test]
fn test_issue3434_beq_deriving_nested_single_ctor() {
    let mut env = Environment::with_prelude();

    let decl = parse_decl_for_elab(
        r"inductive Tree
| node : List Tree -> Tree
deriving BEq",
    )
    .unwrap();

    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "inductive Tree with nested List Tree deriving BEq should \
         elaborate and register (#3434): {:?}",
        result.err()
    );
}
