// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::denote_function;
use trust_ir::inst::{BinOp, Inst};
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, FuncTyId, Function, InstrNode, Module, Ty, ValueId,
};

fn emitted(width: u32, op: BinOp) -> TvDenotation {
    let ty = match width {
        8 => Ty::U8,
        16 => Ty::U16,
        32 => Ty::U32,
        64 => Ty::U64,
        _ => panic!("fixture width"),
    };
    let mut module = Module::new("source_equation");
    module.func_types.push(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(FuncId::new(0), "actual", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())];
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("actual IR fixture");
    denote_function(&module, &module.functions[0]).expect("denote the actual emitted instruction")
}

fn add_source(env: &mut Environment, width: u32, name: &str, operation: &str) -> Name {
    let uint = Expr::const_(Name::from_string(&format!("UInt{width}")), vec![]);
    let name = Name::from_string(name);
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
        value: Expr::lam(
            BinderInfo::Default,
            uint.clone(),
            Expr::lam(
                BinderInfo::Default,
                uint,
                Expr::apps(
                    Expr::const_(
                        Name::from_string(&format!("UInt{width}.{operation}")),
                        vec![],
                    ),
                    [Expr::bvar(1), Expr::bvar(0)],
                ),
            ),
        ),
        is_reducible: true,
    })
    .expect("the actual source definition kernel-checks");
    name
}

#[test]
fn source_equation_proves_actual_checked_definition_against_actual_ir_at_all_widths() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        for (operation, op) in [
            ("add", BinOp::Add),
            ("mul", BinOp::Mul),
            ("sub", BinOp::Sub),
            ("land", BinOp::And),
            ("lor", BinOp::Or),
        ] {
            let source = add_source(
                &mut env,
                width,
                &format!("SourceEquation.{operation}{width}"),
                operation,
            );
            let before = env.closure_digest(&source).unwrap();
            let equation = check_uint_source_equation(
                &env,
                &source,
                &emitted(width, op),
                Name::from_string("SourceEquation.checked")
                    .str(operation)
                    .num(u64::from(width)),
            )
            .expect(
                "the kernel checks the equation about the ACTUAL UInt function, not two Nat models",
            );
            assert_eq!(equation.source(), &source);
            assert_eq!(equation.source_closure_digest(), &before);
            assert_eq!(env.closure_digest(&source), Ok(before));
            let mut replay = env.clone();
            replay
                .add_decl(equation.declaration().clone())
                .expect("replay the exact equation and proof in the original source environment");
            let Declaration::Theorem { name, .. } = equation.declaration() else {
                panic!("a theorem")
            };
            assert!(replay.axiom_deps(name).unwrap().is_empty());
            assert_eq!(
                replay.closure_digest(name).unwrap(),
                *equation.equation_closure_digest()
            );
        }
    }
}

#[test]
fn source_equation_xor_checks_actual_source_and_replays_without_domain_axioms() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let source = add_source(
            &mut env,
            width,
            &format!("SourceEquation.actualXor{width}"),
            "xor",
        );
        // This is a proposed scalar equation, not an emitted-IR license.
        // The emitted-side denominator still refuses Xor until the independent
        // TrustIR mirror and compiler producer have been qualified together.
        let denotation = TvDenotation {
            width,
            arity: 2,
            body: Expr::apps(Expr::const_str("Nat.xor"), [Expr::bvar(1), Expr::bvar(0)]),
            callees: vec![],
        };
        let before = env.closure_digest(&source).unwrap();
        let equation = check_uint_source_equation(
            &env,
            &source,
            &denotation,
            Name::from_string("SourceEquation.checkedXor").num(u64::from(width)),
        )
        .expect("the original UInt XOR definition satisfies its actual Nat equation");
        assert_eq!(env.closure_digest(&source), Ok(before));
        assert_eq!(equation.source_closure_digest(), &before);
        let mut replay = env.clone();
        replay
            .add_decl(equation.declaration().clone())
            .expect("replay the exact source proof");
        let Declaration::Theorem { name, .. } = equation.declaration() else {
            panic!("a checked theorem")
        };
        assert!(replay.axiom_deps(name).unwrap().is_empty());
        assert_eq!(
            replay.closure_digest(name).unwrap(),
            *equation.equation_closure_digest()
        );
        for (label, body) in [
            (
                "and",
                Expr::apps(Expr::const_str("Nat.land"), [Expr::bvar(1), Expr::bvar(0)]),
            ),
            (
                "or",
                Expr::apps(Expr::const_str("Nat.lor"), [Expr::bvar(1), Expr::bvar(0)]),
            ),
            (
                "duplicate",
                Expr::apps(Expr::const_str("Nat.xor"), [Expr::bvar(1), Expr::bvar(1)]),
            ),
            ("constant", Expr::nat_lit(0)),
        ] {
            check_uint_source_equation(
                &env,
                &source,
                &TvDenotation {
                    body,
                    ..denotation.clone()
                },
                Name::from_string("SourceEquation.wrongXor")
                    .str(label)
                    .num(u64::from(width)),
            )
            .expect_err("wrong operators, operands and constants cannot prove the original XOR");
        }
    }
}

#[test]
fn source_equation_wrapping_xor_arithmetic_checks_actual_fnv_low_step_and_controls() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let prefix = format!("UInt{width}");
        let uint = Expr::const_str(&prefix);
        let factor = if width == 64 { 315 } else { 3 };
        let call = |name: &str, args: Vec<Expr>| Expr::apps(Expr::const_str(name), args);
        let literal = |n| call(&format!("{prefix}.ofNat"), vec![Expr::nat_lit(n)]);
        for with_add in [false, true] {
            let source = Name::from_string("SourceEquation.actualFnvLow")
                .num(u64::from(width))
                .num(u64::from(with_add));
            let xor = call(&format!("{prefix}.xor"), vec![Expr::bvar(1), Expr::bvar(0)]);
            let mut value = call(&format!("{prefix}.mul"), vec![xor, literal(factor)]);
            if with_add {
                value = call(&format!("{prefix}.add"), vec![value, literal(3)]);
            }
            env.add_decl(Declaration::Definition {
                name: source.clone(),
                level_params: vec![],
                type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
                value: Expr::lam(
                    BinderInfo::Default,
                    uint.clone(),
                    Expr::lam(BinderInfo::Default, uint.clone(), value),
                ),
                is_reducible: true,
            })
            .expect("the actual wrapping XOR/multiply source definition kernel-checks");
            let model = |op: &str, multiplier: u64, modulus: Expr| {
                let xor = call(op, vec![Expr::bvar(1), Expr::bvar(0)]);
                let product = call("Nat.mul", vec![xor, Expr::nat_lit(multiplier)]);
                let mut body = call("Nat.mod", vec![product, modulus.clone()]);
                if with_add {
                    body = call(
                        "Nat.mod",
                        vec![call("Nat.add", vec![body, Expr::nat_lit(3)]), modulus],
                    );
                }
                TvDenotation {
                    width,
                    arity: 2,
                    body,
                    callees: vec![],
                }
            };
            let before = env.closure_digest(&source).unwrap();
            let checked = check_uint_source_equation(
                &env,
                &source,
                &model("Nat.xor", factor, crate::modulus(width)),
                source.clone().str("checked"),
            )
            .expect("the actual UInt source satisfies the wrapping bitwise/arithmetic equation");
            assert_eq!(env.closure_digest(&source), Ok(before));
            let mut replay = env.clone();
            replay
                .add_decl(checked.declaration().clone())
                .expect("replay the exact proof");
            let Declaration::Theorem { name, .. } = checked.declaration() else {
                panic!("theorem")
            };
            assert!(replay.axiom_deps(name).unwrap().is_empty());
            assert_eq!(
                replay.closure_digest(name).unwrap(),
                *checked.equation_closure_digest()
            );
            for (label, wrong) in [
                ("operator", model("Nat.land", factor, crate::modulus(width))),
                (
                    "multiplier",
                    model("Nat.xor", factor + 1, crate::modulus(width)),
                ),
                (
                    "modulus",
                    model("Nat.xor", factor, Expr::nat_lit_u128((1u128 << width) - 1)),
                ),
            ] {
                check_uint_source_equation(&env, &source, &wrong, source.clone().str(label))
                    .expect_err("wrong operator, multiplier and modulus must reject the original source equation");
            }
        }
    }
}

#[test]
fn source_equation_right_shift_checks_actual_modulo_width_semantics_and_controls() {
    let mut env = Environment::with_prelude();
    for width in [8u32, 16, 32, 64] {
        let prefix = format!("UInt{width}");
        let uint = Expr::const_str(&prefix);
        let call = |name: &str, args: Vec<Expr>| Expr::apps(Expr::const_str(name), args);
        let literal = |n| call(&format!("{prefix}.ofNat"), vec![Expr::nat_lit(n)]);
        for amount in [0, width / 2, width - 1, width, width + 1] {
            let source = Name::from_string("SourceEquation.actualWrappedShiftRight")
                .num(u64::from(width))
                .num(u64::from(amount));
            let xor = call(&format!("{prefix}.xor"), vec![Expr::bvar(1), Expr::bvar(0)]);
            let product = call(&format!("{prefix}.mul"), vec![xor, literal(3)]);
            let shifted = call(
                &format!("{prefix}.shiftRight"),
                vec![product, literal(u64::from(amount))],
            );
            let value = call(&format!("{prefix}.add"), vec![shifted, literal(1)]);
            env.add_decl(Declaration::Definition {
                name: source.clone(),
                level_params: vec![],
                type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
                value: Expr::lam(
                    BinderInfo::Default,
                    uint.clone(),
                    Expr::lam(BinderInfo::Default, uint.clone(), value),
                ),
                is_reducible: true,
            })
            .expect("the actual UInt right shift kernel-checks, including masked amounts");
            // UInt.shiftRight's canonical source definition uses div/pow;
            // Nat.shiftRight's separate prelude axiom is never introduced.
            let model = |divisor: u128| {
                let xor = call("Nat.xor", vec![Expr::bvar(1), Expr::bvar(0)]);
                let product = call(
                    "Nat.mod",
                    vec![
                        call("Nat.mul", vec![xor, Expr::nat_lit(3)]),
                        crate::modulus(width),
                    ],
                );
                let shifted = call("Nat.div", vec![product, Expr::nat_lit_u128(divisor)]);
                TvDenotation {
                    width,
                    arity: 2,
                    callees: vec![],
                    body: call(
                        "Nat.mod",
                        vec![
                            call("Nat.add", vec![shifted, Expr::nat_lit(1)]),
                            crate::modulus(width),
                        ],
                    ),
                }
            };
            let divisor = 1u128 << (amount % width);
            let checked = check_uint_source_equation(
                &env,
                &source,
                &model(divisor),
                source.clone().str("checked"),
            )
            .expect("kernel proves actual modulo-width right shift inside wrapping arithmetic");
            let mut replay = env.clone();
            replay
                .add_decl(checked.declaration().clone())
                .expect("replay exact source theorem");
            let Declaration::Theorem { name, .. } = checked.declaration() else {
                panic!("theorem")
            };
            assert!(replay.axiom_deps(name).unwrap().is_empty());
            assert_eq!(
                replay.closure_digest(name).unwrap(),
                *checked.equation_closure_digest()
            );
            for (label, wrong_divisor) in [
                ("amount", 1u128 << ((amount + 1) % width)),
                ("zeroDivisor", 0),
            ] {
                check_uint_source_equation(
                    &env,
                    &source,
                    &model(wrong_divisor),
                    source.clone().str(label),
                )
                .expect_err(
                    "changed shift amount or zero divisor must refuse the original equation",
                );
            }
            if amount >= width {
                check_uint_source_equation(
                    &env,
                    &source,
                    &model(1u128 << amount),
                    source.clone().str("unmasked"),
                )
                .expect_err("an unmasked machine-shift model is not Lean's modulo-width shift");
            }
        }
    }
}

#[test]
fn source_equation_fnv_high_checks_complete_wrapping_definition_and_controls() {
    let mut env = Environment::with_prelude();
    let uint = Expr::const_str("UInt64");
    let call = |name: &str, args: Vec<Expr>| Expr::apps(Expr::const_str(name), args);
    let literal = |n| call("UInt64.ofNat", vec![Expr::nat_lit(n)]);
    // Independent source syntax for the high step: hi, lo, byte, with actual
    // UInt primitives. This is not a production-file elaboration claim.
    let mixed = call("UInt64.xor", vec![Expr::bvar(1), Expr::bvar(0)]);
    let low_product = call(
        "UInt64.mul",
        vec![
            call("UInt64.land", vec![mixed.clone(), literal(4294967295)]),
            literal(315),
        ],
    );
    let high_product = call(
        "UInt64.add",
        vec![
            call(
                "UInt64.mul",
                vec![
                    call("UInt64.shiftRight", vec![mixed.clone(), literal(32)]),
                    literal(315),
                ],
            ),
            call("UInt64.shiftRight", vec![low_product, literal(32)]),
        ],
    );
    let value = call(
        "UInt64.add",
        vec![
            call(
                "UInt64.add",
                vec![
                    call("UInt64.mul", vec![Expr::bvar(2), literal(315)]),
                    call("UInt64.shiftLeft", vec![mixed, literal(24)]),
                ],
            ),
            call("UInt64.shiftRight", vec![high_product, literal(32)]),
        ],
    );
    let source = Name::from_string("SourceEquation.completeFnvHigh");
    env.add_decl(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: Expr::arrow(
            uint.clone(),
            Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            uint.clone(),
            Expr::lam(
                BinderInfo::Default,
                uint.clone(),
                Expr::lam(BinderInfo::Default, uint.clone(), value),
            ),
        ),
        is_reducible: true,
    })
    .expect("the complete original UInt high-step expression kernel-checks");
    // Proposed Nat dataflow. Keep the actual shift operation: substituting
    // multiplication for it requires a separate checked equality proof.
    let model =
        |left_amount: u64, multiplier: u64, carry_divisor: u128, mask: u64, exact_shift: bool| {
            let wrap = |x| call("Nat.mod", vec![x, crate::modulus(64)]);
            let mul = |a, b| wrap(call("Nat.mul", vec![a, b]));
            let add = |a, b| wrap(call("Nat.add", vec![a, b]));
            let div = |a| call("Nat.div", vec![a, Expr::nat_lit_u128(carry_divisor)]);
            let mixed = call("Nat.xor", vec![Expr::bvar(1), Expr::bvar(0)]);
            let low_product = mul(
                call("Nat.land", vec![mixed.clone(), Expr::nat_lit(mask)]),
                Expr::nat_lit(multiplier),
            );
            let high_product = add(
                mul(div(mixed.clone()), Expr::nat_lit(multiplier)),
                div(low_product),
            );
            let shifted = wrap(if exact_shift {
                call("Nat.shiftLeft", vec![mixed, Expr::nat_lit(left_amount)])
            } else {
                // The existing independent TrustIR checker uses this spelling.
                // Acceptance requires the checked induction, not conversion.
                call(
                    "Nat.mul",
                    vec![
                        mixed,
                        call(
                            "Nat.pow",
                            vec![Expr::nat_lit(2), Expr::nat_lit(left_amount)],
                        ),
                    ],
                )
            });
            TvDenotation {
                width: 64,
                arity: 3,
                callees: vec![],
                body: add(
                    add(mul(Expr::bvar(2), Expr::nat_lit(multiplier)), shifted),
                    div(high_product),
                ),
            }
        };
    for exact_shift in [true, false] {
        let checked = check_uint_source_equation(
            &env,
            &source,
            &model(24, 315, 1u128 << 32, 4294967295, exact_shift),
            source.clone().str("checked").num(u64::from(exact_shift)),
        )
        .expect("kernel checks the complete FNV high-step source equation");
        let mut replay = env.clone();
        replay
            .add_decl(checked.declaration().clone())
            .expect("replay exact high-step proof");
        let Declaration::Theorem { name, .. } = checked.declaration() else {
            panic!("theorem")
        };
        assert!(replay.axiom_deps(name).unwrap().is_empty());
        assert_eq!(
            replay.closure_digest(name).unwrap(),
            *checked.equation_closure_digest()
        );
        for (label, wrong) in [
            (
                "leftAmount",
                model(25, 315, 1u128 << 32, 4294967295, exact_shift),
            ),
            (
                "multiplier",
                model(24, 314, 1u128 << 32, 4294967295, exact_shift),
            ),
            (
                "carry",
                model(24, 315, 1u128 << 31, 4294967295, exact_shift),
            ),
            ("mask", model(24, 315, 1u128 << 32, 4294967294, exact_shift)),
        ] {
            check_uint_source_equation(&env, &source, &wrong, source.clone().str(label)).expect_err(
            "wrong shift, multiplier, carry or mask must refuse the complete high-step equation",
        );
        }
    }
}

#[test]
fn source_equation_bitwise_refuses_changed_operator_operand_and_width() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        for (operation, correct_op, wrong_op) in [
            ("land", BinOp::And, BinOp::Or),
            ("lor", BinOp::Or, BinOp::And),
        ] {
            let source = add_source(
                &mut env,
                width,
                &format!("SourceEquation.bitwiseControls{operation}{width}"),
                operation,
            );
            let correct = emitted(width, correct_op);
            for (label, denotation) in [
                ("operator", emitted(width, wrong_op)),
                (
                    "operand",
                    TvDenotation {
                        body: correct
                            .body
                            .instantiate_rev(&[Expr::bvar(1), Expr::bvar(1)]),
                        ..correct.clone()
                    },
                ),
                (
                    "width",
                    TvDenotation {
                        width: if width == 32 { 64 } else { 32 },
                        ..correct
                    },
                ),
            ] {
                check_uint_source_equation(
                    &env,
                    &source,
                    &denotation,
                    Name::from_string("SourceEquation.bitwiseWrong")
                        .str(operation)
                        .str(label)
                        .num(u64::from(width)),
                )
                .expect_err("actual original bitwise goal rejects a different result");
            }
        }
    }
}

#[test]
fn source_equation_wrapping_subtraction_refuses_wrong_operations_and_operands() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let source = add_source(
            &mut env,
            width,
            &format!("SourceEquation.subControls{width}"),
            "sub",
        );
        let correct = emitted(width, BinOp::Sub);
        for (label, denotation) in [
            ("add", emitted(width, BinOp::Add)),
            ("mul", emitted(width, BinOp::Mul)),
            (
                "swapped",
                TvDenotation {
                    body: correct
                        .body
                        .instantiate_rev(&[Expr::bvar(1), Expr::bvar(0)]),
                    ..correct.clone()
                },
            ),
            (
                "width",
                TvDenotation {
                    width: if width == 32 { 64 } else { 32 },
                    ..correct
                },
            ),
        ] {
            check_uint_source_equation(
                &env,
                &source,
                &denotation,
                Name::from_string("SourceEquation.subWrong")
                    .str(label)
                    .num(u64::from(width)),
            )
            .expect_err("the actual original subtraction goal must reject a different result");
        }
    }
}

#[test]
fn source_equation_kernel_refuses_wrong_actual_operator_and_parameter_order() {
    let mut env = Environment::with_prelude();
    let source = add_source(&mut env, 32, "SourceEquation.actualAdd", "add");
    let error = check_uint_source_equation(
        &env,
        &source,
        &emitted(32, BinOp::Mul),
        Name::from_string("SourceEquation.wrongOperator"),
    )
    .expect_err("wrong IR operator cannot prove the actual source equation");
    assert!(error.to_string().contains("TypeMismatch"), "{error:?}");
    let uint = Expr::const_str("UInt32");
    let source = Name::from_string("SourceEquation.first");
    env.add_decl(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
        value: Expr::lam(
            BinderInfo::Default,
            uint.clone(),
            Expr::lam(BinderInfo::Default, uint, Expr::bvar(1)),
        ),
        is_reducible: true,
    })
    .expect("checked noncommutative parameter control");
    let first = TvDenotation {
        arity: 2,
        width: 32,
        body: Expr::bvar(1),
        callees: vec![],
    };
    check_uint_source_equation(
        &env,
        &source,
        &first,
        Name::from_string("SourceEquation.firstCorrect"),
    )
    .expect("the first source parameter keeps its position");
    let second = TvDenotation {
        body: Expr::bvar(0),
        ..first
    };
    let error = check_uint_source_equation(
        &env,
        &source,
        &second,
        Name::from_string("SourceEquation.swapped"),
    )
    .expect_err("the second input is not the first");
    assert!(error.to_string().contains("TypeMismatch"), "{error:?}");
}

#[test]
fn source_equation_does_not_capture_free_variables_or_guess_width_arity_and_calls() {
    let mut env = Environment::with_prelude();
    let source = add_source(&mut env, 32, "SourceEquation.shape", "add");
    let base = emitted(32, BinOp::Add);
    for mutation in 0..7 {
        let mut denotation = base.clone();
        match mutation {
            0 => denotation.width = 128,
            1 => denotation.width = 64,
            2 => denotation.arity = 1,
            3 => denotation.arity = 65,
            4 => denotation.callees.push(("source".into(), 2)),
            5 => {
                denotation.body =
                    Expr::app(Expr::const_str("UInt32.toNat"), Expr::fvar(FVarId::new(0)))
            }
            6 => denotation.body = Expr::bvar(2),
            _ => unreachable!("bounded fixture mutation"),
        }
        check_uint_source_equation(
            &env,
            &source,
            &denotation,
            Name::from_string("SourceEquation.badShape").num(mutation),
        )
        .expect_err("unsupported or ill-typed input must refuse");
    }
    check_uint_source_equation(
        &env,
        &Name::from_string("SourceEquation.missing"),
        &base,
        Name::from_string("SourceEquation.missingProof"),
    )
    .expect_err("an unknown source cannot be invented");
}

#[test]
fn source_equation_refuses_even_a_true_equation_that_uses_a_domain_axiom() {
    let mut env = Environment::with_prelude();
    let uint = Expr::const_str("UInt32");
    let oracle = Name::from_string("SourceEquation.unprovedValue");
    env.add_decl(Declaration::Axiom {
        name: oracle.clone(),
        level_params: vec![],
        type_: uint.clone(),
    })
    .expect("the negative control explicitly introduces a domain axiom");
    let source = Name::from_string("SourceEquation.usesUnprovedValue");
    env.add_decl(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: Expr::arrow(uint.clone(), uint.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            uint,
            Expr::const_(oracle.clone(), vec![]),
        ),
        is_reducible: true,
    })
    .expect("a definition can type-check while depending on an unproved axiom");
    let denotation = TvDenotation {
        arity: 1,
        width: 32,
        callees: vec![],
        body: Expr::app(
            Expr::const_str("UInt32.toNat"),
            Expr::const_(oracle, vec![]),
        ),
    };
    let error = check_uint_source_equation(
        &env,
        &source,
        &denotation,
        Name::from_string("SourceEquation.unprovedEquation"),
    )
    .expect_err("kernel acceptance of a relative theorem cannot erase its domain assumption");
    assert!(
        error.to_string().contains("NonFoundationalAxiom"),
        "{error:?}"
    );
}

#[test]
fn source_equation_refuses_unverified_imports_in_source_and_separate_proof_dependencies() {
    use clean_kernel::ConstantOrigin;
    let mut env = Environment::with_prelude();
    let source = add_source(&mut env, 32, "SourceEquation.importControl", "add");
    let mut imported = env.clone();
    assert!(imported.set_constant_origin(source.clone(), ConstantOrigin::olean_import(None)));
    let error = check_uint_source_equation(
        &imported,
        &source,
        &emitted(32, BinOp::Add),
        Name::from_string("SourceEquation.uncheckedSource"),
    )
    .expect_err("matching definition bytes do not promote a structural source import");
    assert!(error.to_string().contains("NeedsRecheck"), "{error:?}");
    let alias = Name::from_string("SourceEquation.modelAdd");
    let nat = Expr::const_str("Nat");
    env.add_decl(Declaration::Definition {
        name: alias.clone(),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat)),
        value: Expr::const_str("Nat.add"),
        is_reducible: true,
    })
    .expect("a real checked denotation alias");
    let denotation = TvDenotation {
        width: 32,
        arity: 2,
        callees: vec![],
        body: Expr::apps(
            Expr::const_str("Nat.mod"),
            [
                Expr::apps(
                    Expr::const_(alias.clone(), vec![]),
                    [Expr::bvar(1), Expr::bvar(0)],
                ),
                crate::modulus(32),
            ],
        ),
    };
    check_uint_source_equation(
        &env,
        &source,
        &denotation,
        Name::from_string("SourceEquation.checkedAlias"),
    )
    .expect("the original checked alias preserves the exact equation");
    let source_digest = env.closure_digest(&source).unwrap();
    assert!(env.set_constant_origin(alias, ConstantOrigin::olean_import(None)));
    assert_eq!(
        env.closure_digest(&source).unwrap(),
        source_digest,
        "the proof-only alias is deliberately outside the source dependency closure"
    );
    let error = check_uint_source_equation(
        &env,
        &source,
        &denotation,
        Name::from_string("SourceEquation.uncheckedAlias"),
    )
    .expect_err("all proof dependencies need checked provenance too");
    assert!(error.to_string().contains("NeedsRecheck"), "{error:?}");
}

#[test]
fn source_equation_rejects_counterfeit_foundation_names_and_no_origin_structural_values() {
    let mut env = Environment::with_prelude();
    let uint = Expr::const_str("UInt32");
    let counterfeit = Name::from_string("propext");
    env.forget_decl(&counterfeit);
    env.add_decl(Declaration::Axiom {
        name: counterfeit.clone(),
        level_params: vec![],
        type_: uint.clone(),
    })
    .expect("a well-typed axiom can have a counterfeit foundational name");
    let source = Name::from_string("SourceEquation.counterfeit");
    env.add_decl(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: uint.clone(),
        value: Expr::const_(counterfeit.clone(), vec![]),
        is_reducible: true,
    })
    .expect("the source really depends on the counterfeit axiom");
    let denotation = TvDenotation {
        arity: 0,
        width: 32,
        callees: vec![],
        body: Expr::app(
            Expr::const_str("UInt32.toNat"),
            Expr::const_(counterfeit, vec![]),
        ),
    };
    let error = check_uint_source_equation(
        &env,
        &source,
        &denotation,
        Name::from_string("SourceEquation.counterfeitProof"),
    )
    .expect_err("a relative reflexive equation cannot hide counterfeit foundation contents");
    assert!(
        error.to_string().contains("NonCanonicalFoundation"),
        "{error:?}"
    );

    let mut env = Environment::with_prelude();
    let source = Name::from_string("SourceEquation.structural");
    env.add_decl_structural(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: uint,
        value: Expr::nat_lit(0u64),
        is_reducible: true,
    })
    .expect("structural admission deliberately does not check the ill-typed stored body");
    assert!(
        !env.constant_needs_recheck(&source),
        "no imported-origin marker is present"
    );
    let denotation = TvDenotation {
        arity: 0,
        width: 32,
        callees: vec![],
        body: Expr::app(
            Expr::const_str("UInt32.toNat"),
            Expr::const_(source.clone(), vec![]),
        ),
    };
    let error = check_uint_source_equation(
        &env,
        &source,
        &denotation,
        Name::from_string("SourceEquation.structuralProof"),
    )
    .expect_err("literal reflexivity cannot certify an unverified declaration closure");
    assert!(error.to_string().contains("StructuralOnly"), "{error:?}");
}

#[test]
fn source_equation_does_not_treat_axiom_only_import_success_as_proof_checking() {
    use clean_kernel::{set_mm_axiom_only, MmAxiomOnlyGuard};
    let mut env = Environment::with_prelude();
    let source = add_source(&mut env, 32, "SourceEquation.axiomOnly", "add");
    let _guard = MmAxiomOnlyGuard::enter();
    set_mm_axiom_only(true);
    let error = check_uint_source_equation(
        &env,
        &source,
        &emitted(32, BinOp::Mul),
        Name::from_string("SourceEquation.axiomOnlyWrong"),
    )
    .expect_err(
        "the original wrong judgment must fail even when add_decl can park theorems as axioms",
    );
    assert!(error.to_string().contains("TypeMismatch"), "{error:?}");
    check_uint_source_equation(&env, &source, &emitted(32, BinOp::Add),
        Name::from_string("SourceEquation.axiomOnlyRight"))
        .expect_err("a valid judgment still cannot receive a theorem-closure receipt for an axiom-only admission");
}
