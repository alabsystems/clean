// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::Environment;
use trust_ir::{Block, BlockId, FuncTy, FuncTyId, InstrNode, ValueId};

fn fixture(arity: usize) -> Module {
    let mut module = Module::new("uint32_boxed_entry");
    for (params, returns) in [
        (vec![Ty::Ptr], vec![Ty::U32]),
        (vec![Ty::U32], vec![Ty::Ptr]),
        (vec![Ty::U32; arity], vec![Ty::U32]),
        (vec![Ty::Ptr; arity], vec![Ty::Ptr]),
    ] {
        module.func_types.push(FuncTy {
            params,
            returns,
            is_vararg: false,
            abi: None,
        });
    }
    let v = ValueId::new;
    for (id, name, sig) in [
        (0, "clean_unbox_uint32", 0),
        (1, "clean_box_uint32", 1),
        (2, "scalar", 2),
        (3, "boxed", 3),
        (4, "other_scalar", 2),
    ] {
        let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(sig), BlockId::new(0));
        if id == 2 || id == 4 {
            let mut b = Block::new(BlockId::new(0));
            b.params = (0..arity).map(|i| (v(i as u32), Ty::U32)).collect();
            b.body
                .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
            f.blocks.push(b);
        }
        if id == 3 {
            let mut b = Block::new(BlockId::new(0));
            b.params = (0..arity).map(|i| (v(i as u32), Ty::Ptr)).collect();
            for i in 0..arity {
                b.body.push(
                    InstrNode::new(Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![v(i as u32)],
                    })
                    .with_result(v((arity + i) as u32)),
                );
            }
            for i in 0..arity {
                b.body
                    .push(InstrNode::new(Inst::Release { ptr: v(i as u32) }));
            }
            b.body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(2),
                    args: (arity..2 * arity).map(|i| v(i as u32)).collect(),
                })
                .with_result(v((2 * arity) as u32)),
            );
            b.body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![v((2 * arity) as u32)],
                })
                .with_result(v((2 * arity + 1) as u32)),
            );
            b.body.push(InstrNode::new(Inst::Return {
                values: vec![v((2 * arity + 1) as u32)],
            }));
            f.blocks.push(b);
        }
        module.try_add_function(f).expect("fixture function");
    }
    module
}

fn check(module: &Module) -> Result<UInt32BoxedEntry, ReflectError> {
    check_uint32_boxed_entry(module, FuncId::new(3), FuncId::new(2))
}

#[test]
fn boxed_entry_checks_actual_order_and_kernel_checks_a_conditional_axiom_free_lemma() {
    for arity in [1, 2, MAX_UINT32_BOXED_ENTRY_ARGS] {
        let module = fixture(arity);
        let before = module.clone();
        let shape = check(&module).expect("the exact bounded choreography");
        assert_eq!(shape.arity(), arity);
        assert_eq!(shape.functions(), [3, 2, 0, 1].map(FuncId::new));
        let mut env = Environment::with_prelude();
        let name = Name::from_string("BoxedEntry.conditional").num(arity as u64);
        env.add_decl(shape.conditional_composition_theorem(name.clone()))
            .expect("kernel checks the universally quantified round-trip implication");
        assert!(env.axiom_deps(&name).is_some_and(|deps| deps.is_empty()));
        assert_eq!(
            module, before,
            "no obligation, certificate or body license is minted"
        );
    }
}

#[test]
fn boxed_entry_refuses_wrong_reads_releases_call_result_and_return() {
    for mutation in 0..10 {
        let mut module = fixture(2);
        let b = &mut module.functions[3].blocks[0].body;
        match mutation {
            0 => {
                b.swap(0, 2);
            }
            1 => {
                b.remove(2);
            }
            2 => {
                b[3] = b[2].clone();
            }
            3 => {
                let Inst::Call { args, .. } = &mut b[0].inst else {
                    panic!("fixture")
                };
                args[0] = ValueId::new(1);
            }
            4 => {
                let Inst::Call { args, .. } = &mut b[4].inst else {
                    panic!("fixture")
                };
                args.swap(0, 1);
            }
            5 => {
                let Inst::Call { callee, .. } = &mut b[4].inst else {
                    panic!("fixture")
                };
                *callee = FuncId::new(4);
            }
            6 => {
                let Inst::Call { args, .. } = &mut b[5].inst else {
                    panic!("fixture")
                };
                args[0] = ValueId::new(2);
            }
            7 => {
                b[6].inst = Inst::Return {
                    values: vec![ValueId::new(0)],
                };
            }
            8 => {
                b[1].results = b[0].results.clone();
            }
            9 => {
                b[2].results.push(ValueId::new(90));
            }
            _ => unreachable!("bounded mutation selector"),
        }
        assert!(
            matches!(check(&module), Err(ReflectError::WrongEmission(_))),
            "mutation {mutation}"
        );
    }
}

#[test]
fn boxed_entry_does_not_trust_names_signatures_or_ambiguous_identity() {
    for mutation in 0..8 {
        let mut module = fixture(2);
        match mutation {
            0 => module.functions[0].name = "different_decoder".to_string(),
            1 => module.func_types[0].returns = vec![Ty::U64],
            2 => module.func_types[1].is_vararg = true,
            3 => module.functions[0].blocks = module.functions[2].blocks.clone(),
            4 => module.functions[1].name = module.functions[0].name.clone(),
            5 => module.functions[4].id = module.functions[0].id,
            6 => module.functions[3].blocks[0].params[1].0 = ValueId::new(0),
            7 => module.functions[0].calling_conv = CallingConv::Fast,
            _ => unreachable!("bounded mutation selector"),
        }
        assert!(
            matches!(check(&module), Err(ReflectError::WrongEmission(_))),
            "mutation {mutation}"
        );
    }
}

#[test]
fn boxed_entry_keeps_other_widths_mixed_carriers_and_arities_unsupported() {
    for arity in [0, MAX_UINT32_BOXED_ENTRY_ARGS + 1] {
        assert!(matches!(
            check(&fixture(arity)),
            Err(ReflectError::Unsupported { .. })
        ));
    }
    let mut module = fixture(2);
    module.func_types[2].params[0] = Ty::U64;
    assert!(matches!(
        check(&module),
        Err(ReflectError::Unsupported { .. })
    ));
}

#[test]
fn boxed_entry_conditional_lemma_does_not_accept_an_invented_proof() {
    let shape = check(&fixture(2)).expect("fixture");
    let Declaration::Theorem {
        name,
        level_params,
        type_,
        ..
    } = shape.conditional_composition_theorem(Name::from_string("BoxedEntry.forged"))
    else {
        panic!("the conditional proposition is a theorem")
    };
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Theorem {
        name,
        level_params,
        type_,
        value: Expr::const_str("True.intro"),
    })
    .expect_err("a shape/status is no proof of even the conditional equation");
}

#[test]
fn boxed_entry_round_trip_premise_is_satisfiable_and_cannot_be_silently_dropped() {
    let shape = check(&fixture(2)).expect("fixture");
    let mut env = Environment::with_prelude();
    let lemma = Name::from_string("BoxedEntry.conditionalInstance");
    env.add_decl(shape.conditional_composition_theorem(lemma.clone()))
        .expect("conditional composition lemma");
    let nat = Expr::const_str("Nat");
    let identity = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));
    let refl = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat.clone(), Expr::bvar(0)],
        ),
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat.clone(), Expr::nat_lit(5u64), Expr::nat_lit(5u64)],
    );
    let instance = |encode| {
        Expr::apps(
            Expr::const_(lemma.clone(), vec![]),
            [
                nat.clone(),
                nat.clone(),
                identity.clone(),
                encode,
                refl.clone(),
                Expr::const_str("Nat.sub"),
                Expr::nat_lit(9u64),
                Expr::nat_lit(4u64),
            ],
        )
    };
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("BoxedEntry.satisfiableModel"),
        level_params: vec![],
        type_: goal.clone(),
        value: instance(identity.clone()),
    })
    .expect("identity boxes witness a satisfiable ABSTRACT premise, not runtime fidelity");
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("BoxedEntry.badRoundTrip"),
        level_params: vec![],
        type_: goal,
        value: instance(Expr::const_str("Nat.succ")),
    })
    .expect_err("encode=succ cannot use the identity decoder's round-trip proof");
}
