// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fragment-2 denotation tests: the two maps agree on the corpus decl, the
//! kernel genuinely DECIDES the equation (accepts the honest one, refuses the
//! miscompiled one), and everything outside the fragment fails closed.

use super::*;
use clean_kernel::{BinderInfo, Declaration, Environment};
use trust_ir::{BlockId, FuncId, FuncTy, FuncTyId, Function, InstrNode, ValueId};

#[test]
fn bounded_shift_denotation_requires_actual_nonzero_and_range_facts() {
    let m = modulus(8);
    for op in [BinOp::Shl, BinOp::LShr] {
        for amount in [
            Expr::bvar(0),
            Expr::nat_lit(8),
            Expr::nat_lit(9),
            nat_app2("Nat.mod", Expr::bvar(0), Expr::nat_lit(0)),
            nat_app2("Nat.mod", Expr::bvar(0), Expr::nat_lit(9)),
        ] {
            assert!(denote_binop(op, Expr::bvar(1), amount, &m).is_err());
        }
        for amount in [
            Expr::nat_lit(0),
            Expr::nat_lit(7),
            nat_app2("Nat.mod", Expr::bvar(0), Expr::nat_lit(8)),
        ] {
            assert!(denote_binop(op, Expr::bvar(1), amount, &m).is_ok());
        }
    }
    for divisor in [Expr::nat_lit(0), Expr::bvar(0)] {
        assert!(denote_binop(BinOp::URem, Expr::bvar(1), divisor, &m).is_err());
    }
}

#[test]
fn addressable_storage_never_denotes_initialized_uint_cells() {
    let mut module = Module::new("storage_is_geometry_only");
    assert_eq!(alloc_cells(&module, &Ty::U8, 8, 32).unwrap(), vec![32]);
    for (size, alignment) in [(0, 8), (1, 1), (8, 8)] {
        let storage = Ty::Storage(trust_ir::StorageLayout::new(size, alignment));
        assert_eq!(width_of_ty(&storage), None);
        assert!(matches!(
            alloc_cells(&module, &storage, 8, 32),
            Err(ReflectError::Unsupported { .. })
        ));
        let element = trust_ir::TyId::new(u32::try_from(module.types.len()).unwrap());
        module.types.push(storage);
        for length in [0, 4] {
            assert!(
                matches!(
                    alloc_cells(&module, &Ty::Array(element, length), 8, 32),
                    Err(ReflectError::Unsupported { .. })
                ),
                "even an empty storage array cannot mint initialized scalar cells"
            );
        }
    }
}

#[test]
fn tensor_storage_never_denotes_initialized_uint_cells() {
    let mut module = Module::new("tensor_storage_is_not_scalar_storage");
    for rank in [0, 1, 2, u32::MAX] {
        let tensor = Ty::Tensor(Box::new(Ty::U32), rank);
        assert_eq!(width_of_ty(&tensor), None);
        assert!(matches!(
            alloc_cells(&module, &tensor, 32, 0),
            Err(ReflectError::Unsupported { .. })
        ));
        let element = trust_ir::TyId::new(u32::try_from(module.types.len()).unwrap());
        module.types.push(tensor);
        assert!(matches!(
            alloc_cells(&module, &Ty::Array(element, 0), 32, 0),
            Err(ReflectError::Unsupported { .. })
        ));
    }
}

#[test]
fn tensor_operations_are_refused_by_reflection_and_both_scalar_readers() {
    let v = ValueId::new;
    let ty = || Ty::Tensor(Box::new(Ty::U32), 1);
    let instructions = [
        Inst::TensorContract {
            ty: ty(),
            lhs: v(0),
            rhs: v(1),
            batch: vec![],
            contract: vec![(0, 0)],
        },
        Inst::TensorMap {
            ty: ty(),
            args: vec![v(0)],
            body: vec![trust_ir::TensorMapNode::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                lhs: 0,
                rhs: 0,
            }],
        },
        Inst::TensorReduce {
            ty: ty(),
            src: v(0),
            op: trust_ir::TensorReduceOp::Add,
            axes: vec![0],
            order: trust_ir::TensorReduceOrder::RowMajor,
        },
        Inst::TensorView {
            ty: ty(),
            src: v(0),
            params: vec![],
            exprs: vec![
                trust_ir::TensorIndexExpr::SrcExtent(0),
                trust_ir::TensorIndexExpr::Coord(0),
            ],
            shape: vec![0],
            index: vec![1],
            fill: None,
        },
        Inst::TensorGather {
            ty: ty(),
            data: v(0),
            coords: vec![v(1)],
        },
        Inst::TensorScatter {
            ty: ty(),
            init: v(0),
            src: v(1),
            coords: vec![v(2)],
        },
    ];
    for inst in instructions {
        let error = crate::reflect_inst(&inst).unwrap_err();
        assert!(matches!(error, ReflectError::Unsupported { .. }));
        assert!(error.to_string().contains("tensor instruction"));

        // Keep the existing UInt signature so each reader reaches the opcode
        // refusal, rather than rejecting a tensor signature before its body.
        // An unsupported instruction must never disappear from a scalar model.
        let mut module = tv_demo_module();
        module.functions[0].blocks[0].body[1] = InstrNode::new(inst).with_result(v(2));
        for error in [
            denote_function(&module, &module.functions[0]).unwrap_err(),
            denote_scalar_function(&module, &module.functions[0]).unwrap_err(),
        ] {
            assert!(matches!(error, ReflectError::Unsupported { .. }));
            assert!(error.to_string().contains("tensor instruction"));
        }
    }
}

#[test]
fn source_instance_field_hadd_must_follow_the_checked_dictionary() {
    use clean_kernel::Level;
    let u = Expr::const_str("UInt32");
    let levels = vec![Level::zero(); 3];
    let dictionary = Expr::apps(
        Expr::const_(Name::from_string("HAdd.mk"), levels.clone()),
        [
            u.clone(),
            u.clone(),
            u.clone(),
            Expr::const_str("UInt32.sub"),
        ],
    );
    let source = Expr::lam(
        BinderInfo::Default,
        u.clone(),
        Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("HAdd.hAdd"), levels),
                [
                    u.clone(),
                    u.clone(),
                    u.clone(),
                    dictionary,
                    Expr::bvar(1),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    let expected = Expr::lam(
        BinderInfo::Default,
        u.clone(),
        Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::apps(
                Expr::const_str("UInt32.sub"),
                [Expr::bvar(1), Expr::bvar(0)],
            ),
        ),
    );
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TVTest.customHAdd"),
        level_params: vec![],
        type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), u)),
        value: source.clone(),
        is_reducible: true,
    })
    .expect("the non-additive HAdd dictionary is a valid checked source");
    assert_eq!(
        denote_source(&source, 32, &[], &RecordVocab::empty())
            .unwrap()
            .body,
        denote_source(&expected, 32, &[], &RecordVocab::empty())
            .unwrap()
            .body,
        "a class method's name does not determine its dictionary's operation",
    );
}

#[test]
fn source_instance_field_ofnat_must_follow_the_checked_dictionary() {
    use clean_kernel::Level;
    let u = Expr::const_str("UInt32");
    let value = Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(8));
    let dictionary = Expr::apps(
        Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]),
        [u.clone(), Expr::nat_lit(7), value],
    );
    let source = Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [u.clone(), Expr::nat_lit(7), dictionary],
    );
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TVTest.customOfNat"),
        level_params: vec![],
        type_: u,
        value: source.clone(),
        is_reducible: true,
    })
    .expect("an OfNat index does not constrain its checked value to that numeral");
    assert_eq!(
        denote_source(&source, 32, &[], &RecordVocab::empty())
            .unwrap()
            .body,
        Expr::nat_lit(8),
        "reflection must read the dictionary's field, not its class index",
    );
}

#[test]
fn source_instance_field_conditional_follows_order_field_and_records_proof_requirement() {
    use clean_kernel::Level;
    let u = Expr::const_str("UInt32");
    let order = Expr::apps(
        Expr::const_(Name::from_string("LT.mk"), vec![Level::zero()]),
        [u.clone(), Expr::const_str("UInt32.le")],
    );
    let predicate = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [u.clone(), order, Expr::bvar(1), Expr::bvar(0)],
    );
    let conditional = Expr::lam(
        BinderInfo::Default,
        u.clone(),
        Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
                [
                    u.clone(),
                    predicate,
                    Expr::apps(
                        Expr::const_str("UInt32.decLe"),
                        [Expr::bvar(1), Expr::bvar(0)],
                    ),
                    Expr::bvar(1),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TVTest.orderFieldConditional"),
        level_params: vec![],
        type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), u.clone())),
        value: conditional.clone(),
        is_reducible: true,
    })
    .expect("an LT dictionary may actually contain the le relation");
    let proposed =
        denote_source_with_requirements(&conditional, 32, &[], &RecordVocab::empty(), Some(&env))
            .unwrap();
    assert!(proposed.requires_original_source_equation);
    assert!(denote_source(&conditional, 32, &[], &RecordVocab::empty()).is_err());
    assert!(
        denote_source_in_environment(&conditional, 32, &[], &RecordVocab::empty(), &env).is_err()
    );
    assert_eq!(
        proposed.denotation.body,
        ite_nat(
            nat_app2("Nat.ble", Expr::bvar(1), Expr::bvar(0)),
            Expr::bvar(1),
            Expr::bvar(0),
        )
    );

    // Hide the ite inside a named HAdd field. A scan of just the original
    // source's constants cannot see it; the actual dictionary walk must flag it.
    let levels = vec![Level::zero(); 3];
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TVTest.hiddenConditionalDictionary"),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(Name::from_string("HAdd"), levels.clone()),
            [u.clone(), u.clone(), u.clone()],
        ),
        value: Expr::apps(
            Expr::const_(Name::from_string("HAdd.mk"), levels.clone()),
            [u.clone(), u.clone(), u.clone(), conditional],
        ),
        is_reducible: true,
    })
    .unwrap();
    let source = Expr::lam(
        BinderInfo::Default,
        u.clone(),
        Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("HAdd.hAdd"), levels),
                [
                    u.clone(),
                    u.clone(),
                    u,
                    Expr::const_str("TVTest.hiddenConditionalDictionary"),
                    Expr::bvar(1),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    let hidden =
        denote_source_with_requirements(&source, 32, &[], &RecordVocab::empty(), Some(&env))
            .unwrap();
    assert!(hidden.requires_original_source_equation);
    assert_eq!(hidden.denotation.body, proposed.denotation.body);
    assert!(
        denote_source_with_requirements(&source, 32, &[], &RecordVocab::empty(), None).is_err()
    );
}

#[test]
fn source_instance_field_conditional_cannot_erase_a_malformed_decision_obligation() {
    use clean_kernel::Level;
    let u = Expr::const_str("UInt32");
    let source = Expr::lam(
        BinderInfo::Default,
        u.clone(),
        Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
                [
                    u.clone(),
                    Expr::apps(Expr::const_str("UInt32.lt"), [Expr::bvar(1), Expr::bvar(0)]),
                    Expr::const_str("Bool.true"),
                    Expr::bvar(1),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    let mut env = Environment::with_prelude();
    assert!(
        env.add_decl(Declaration::Definition {
            name: Name::from_string("TVTest.invalidConditionalDecision"),
            level_params: vec![],
            type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), u)),
            value: source.clone(),
            is_reducible: true,
        })
        .is_err(),
        "a proposed Nat model cannot make an ill-typed source a checked definition"
    );
    let proposal =
        denote_source_with_requirements(&source, 32, &[], &RecordVocab::empty(), None).unwrap();
    assert!(proposal.requires_original_source_equation);
    for legacy in [
        denote_source(&source, 32, &[], &RecordVocab::empty()),
        denote_source_in_environment(&source, 32, &[], &RecordVocab::empty(), &env),
    ] {
        assert!(
            legacy.is_err(),
            "no legacy caller may silently lose the source judgment"
        );
    }
}

/// Build the emitted-side corpus fixture: `fn tv_demo(x: u32) -> u32` with body
/// `c7 = const 7; a = add x c7; c3 = const 3; m = mul a c3; ret m` — exactly
/// what `clean-compiler`'s backend emits for `(x + 7) * 3` at `UInt32`.
fn tv_demo_module() -> Module {
    let mut module = Module::new("tv_demo_fixture");
    module.func_types.push(FuncTy {
        params: vec![Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut func = Function::new(FuncId::new(0), "tv_demo", FuncTyId::new(0), BlockId::new(0));
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U32));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(3),
        })
        .with_result(ValueId::new(3)),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Mul,
            ty: Ty::U32,
            lhs: ValueId::new(2),
            rhs: ValueId::new(3),
        })
        .with_result(ValueId::new(4)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The source-side corpus fixture: the ORIGINAL kernel definition
/// `fun (x : UInt32) => UInt32.mul (UInt32.add x (UInt32.ofNat 7)) (UInt32.ofNat 3)`.
fn tv_demo_source() -> Expr {
    let of_nat = |k: u64| Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
    let add = Expr::apps(Expr::const_str("UInt32.add"), [Expr::bvar(0), of_nat(7)]);
    let mul = Expr::apps(Expr::const_str("UInt32.mul"), [add, of_nat(3)]);
    Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), mul)
}

/// The expected shared-vocabulary denotation of the corpus decl:
/// `Nat.mod (Nat.mul (Nat.mod (Nat.add x 7) 2^32) 3) 2^32`.
fn expected_corpus_body() -> Expr {
    let m = modulus(32);
    let add = Expr::apps(
        Expr::const_str("Nat.add"),
        [Expr::bvar(0), Expr::nat_lit(7)],
    );
    let wrapped_add = Expr::apps(Expr::const_str("Nat.mod"), [add, m.clone()]);
    let mul = Expr::apps(Expr::const_str("Nat.mul"), [wrapped_add, Expr::nat_lit(3)]);
    Expr::apps(Expr::const_str("Nat.mod"), [mul, m])
}

#[test]
fn test_emitted_side_denotes_corpus_decl() {
    let module = tv_demo_module();
    let den = denote_function(&module, &module.functions[0]).expect("in-fragment");
    assert_eq!(den.arity, 1);
    assert_eq!(den.width, 32);
    assert_eq!(den.body, expected_corpus_body());
}

#[test]
fn test_source_side_denotes_corpus_decl_identically() {
    // THE AGREEMENT: both maps land on the SAME Expr, so the kernel equation
    // is decided by definitional equality (here even syntactic identity).
    let den =
        denote_source(&tv_demo_source(), 32, &[], &RecordVocab::empty()).expect("in-fragment");
    assert_eq!(den.arity, 1);
    assert_eq!(den.width, 32);
    assert_eq!(den.body, expected_corpus_body());
}

#[test]
fn test_source_side_hadd_dispatcher_form_denotes_identically() {
    // The elaborator-shaped `HAdd.hAdd UInt32 UInt32 UInt32 inst a b` form
    // denotes the same as bare `UInt32.add a b`.
    let u32c = || Expr::const_str("UInt32");
    let of_nat = |k: u64| Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
    let add = Expr::apps(
        Expr::const_str("HAdd.hAdd"),
        [
            u32c(),
            u32c(),
            u32c(),
            Expr::apps(
                Expr::const_str("HAdd.mk"),
                [u32c(), u32c(), u32c(), Expr::const_str("UInt32.add")],
            ),
            Expr::bvar(0),
            of_nat(7),
        ],
    );
    let mul = Expr::apps(
        Expr::const_str("HMul.hMul"),
        [
            u32c(),
            u32c(),
            u32c(),
            Expr::apps(
                Expr::const_str("HMul.mk"),
                [u32c(), u32c(), u32c(), Expr::const_str("UInt32.mul")],
            ),
            add,
            of_nat(3),
        ],
    );
    let defn = Expr::lam(BinderInfo::Default, u32c(), mul);
    let den = denote_source(&defn, 32, &[], &RecordVocab::empty())
        .expect("dispatcher form is in-fragment");
    assert_eq!(den.body, expected_corpus_body());
}

/// Declare the TV theorem for (lhs, rhs) in a fresh prelude env; Ok iff the
/// kernel ACCEPTS the equation (this is the same `add_decl` gate the
/// trust-ir-build re-checker runs).
fn kernel_decides(
    arity: usize,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<(), clean_kernel::KernelEnvError> {
    kernel_decides_with(&[], arity, lhs, rhs)
}

/// As [`kernel_decides`] but with pinned callee-symbol binders (Fragment-3b).
/// The Fragment-4 heap vocabulary is installed unconditionally — three
/// definitional combinators, inert for heap-free equations.
fn kernel_decides_with(
    callee_arities: &[usize],
    arity: usize,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<(), clean_kernel::KernelEnvError> {
    let mut env = Environment::with_prelude();
    for decl in heap_vocab_declarations() {
        env.add_decl(decl).expect("heap vocabulary installs");
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(&tv_theorem_name("tv_demo")),
        level_params: vec![],
        type_: tv_statement(callee_arities, arity, lhs, rhs),
        value: tv_proof_term(callee_arities, arity, lhs),
    })
}

#[test]
fn test_kernel_accepts_the_honest_corpus_equation() {
    let module = tv_demo_module();
    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let rhs = denote_source(&tv_demo_source(), 32, &[], &RecordVocab::empty()).unwrap();
    assert_eq!(lhs.arity, rhs.arity);
    kernel_decides(lhs.arity, &lhs.body, &rhs.body)
        .expect("the kernel must decide the honest equation");
}

#[test]
fn test_kernel_refuses_the_miscompiled_equation() {
    // MISCOMPILE DETECTOR: patch the emitted Add to Sub (a real wrong-code
    // bug) and the kernel must REFUSE the equation against the original.
    let mut module = tv_demo_module();
    let Inst::BinOp { op, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
        panic!("fixture layout: node 1 is the Add");
    };
    *op = BinOp::Sub;

    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let rhs = denote_source(&tv_demo_source(), 32, &[], &RecordVocab::empty()).unwrap();
    assert!(
        kernel_decides(lhs.arity, &lhs.body, &rhs.body).is_err(),
        "the kernel must refuse: (x - 7) * 3 does not denote (x + 7) * 3"
    );
}

#[test]
fn test_wrapping_sub_vocabulary_matches_hardware_semantics() {
    // Closed-term sanity for the sub arm: at U8, `1 - 2` must denote 255
    // (two's-complement wraparound), NOT Nat-monus 0. The kernel REDUCES the
    // denotation to decide it — this pins the vocabulary to trust-ir's
    // ratified wrapping semantics on an actual wrap case.
    let m = modulus(8);
    let den = denote_binop(BinOp::Sub, Expr::nat_lit(1), Expr::nat_lit(2), &m).unwrap();
    kernel_decides(0, &den, &Expr::nat_lit(255))
        .expect("kernel must reduce ((1 + 256) - 2) mod 256 to 255");
    assert!(
        kernel_decides(0, &den, &Expr::nat_lit(0)).is_err(),
        "monus semantics (0) must be REFUSED — the fragment denotes wrapping sub"
    );
}

#[test]
fn test_out_of_fragment_function_fails_closed() {
    // A memory/pseudo op (here `Copy`) is out of the arithmetic fragment —
    // fail-closed. (Direct `Call`s are now Fragment-3b; see the calls tests.)
    let mut module = tv_demo_module();
    module.functions[0].blocks[0].body[1] = InstrNode::new(Inst::Copy {
        ty: Ty::U32,
        operand: ValueId::new(0),
    })
    .with_result(ValueId::new(2));
    let err =
        denote_function(&module, &module.functions[0]).expect_err("a Copy must be out of fragment");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
}

/// trust-ir v50: an `ArraySplat` (`n` copies of one register) and a `Const`
/// carrying a `Constant::Splat` are both outside every fragment, so each fails
/// closed. Neither refusal reads the length: `n = 1` and `n = u64::MAX` give
/// the SAME error, and the huge one returns at once (a denotation that walked
/// or materialized the lanes would not).
#[test]
fn test_uniform_arrays_fail_closed_whatever_their_length() {
    let with_array_splat = |len| {
        let mut module = tv_demo_module();
        module.functions[0].blocks[0].body[1] = InstrNode::new(Inst::ArraySplat {
            ty: Ty::Array(trust_ir::TyId::new(0), len),
            value: ValueId::new(0),
        })
        .with_result(ValueId::new(2));
        denote_function(&module, &module.functions[0])
            .expect_err("an ArraySplat must be out of fragment")
    };
    let (small, huge) = (with_array_splat(1), with_array_splat(u64::MAX));
    let ReflectError::Unsupported { construct } = &small else {
        panic!("expected Unsupported, got {small:?}");
    };
    assert!(
        construct.contains("ArraySplat"),
        "the refusal should name the construct, got: {construct}"
    );
    assert_eq!(
        format!("{small:?}"),
        format!("{huge:?}"),
        "the refusal must not depend on the lane count"
    );

    let with_const_splat = |len| {
        let mut module = tv_demo_module();
        let Inst::Const { value, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
            panic!("fixture layout: node 0 is a Const");
        };
        *value = Constant::Splat {
            elem: Box::new(Constant::Int(7)),
            len,
        };
        denote_function(&module, &module.functions[0])
            .expect_err("a splat constant must be out of fragment")
    };
    let (small, huge) = (with_const_splat(2), with_const_splat(u64::MAX));
    assert!(
        matches!(small, ReflectError::Unsupported { .. }),
        "expected Unsupported, got {small:?}"
    );
    assert_eq!(
        format!("{small:?}"),
        format!("{huge:?}"),
        "the refusal must not depend on the lane count"
    );
}

#[test]
fn test_out_of_fragment_source_fails_closed() {
    // `Nat.add` in the source is NOT the fixed-width fragment (Nat is
    // arbitrary-precision) — fail-closed, never silently re-interpreted.
    let defn = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::apps(
            Expr::const_str("Nat.add"),
            [Expr::bvar(0), Expr::nat_lit(7)],
        ),
    );
    let err = denote_source(&defn, 32, &[], &RecordVocab::empty())
        .expect_err("Nat.add is out of the source fragment");
    assert!(matches!(err, ReflectError::Unsupported { .. }));
}

#[test]
fn test_oversized_constant_fails_closed() {
    let mut module = tv_demo_module();
    let Inst::Const { value, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
        panic!("fixture layout: node 0 is a Const");
    };
    *value = Constant::Int(1 << 33); // out of U32 range
    let err = denote_function(&module, &module.functions[0])
        .expect_err("an out-of-range constant is out of fragment");
    assert!(matches!(err, ReflectError::Unsupported { .. }));
}

#[test]
fn test_escaping_bvar_in_source_fails_closed() {
    // A bvar past the parameter telescope would be a malformed definition;
    // the map refuses instead of producing an ill-scoped denotation.
    let defn = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::bvar(1),
    );
    let err = denote_source(&defn, 32, &[], &RecordVocab::empty())
        .expect_err("escaping bvar must fail closed");
    assert!(matches!(err, ReflectError::Unsupported { .. }));
}

// ===========================================================================
// Fragment-3a — control flow (one CondBr, two return paths)
// ===========================================================================

/// The emitted-side control-flow fixture: `fn cf(x: u32) -> u32` compiled from
/// `fun x => if x < 10 then x + 1 else x` as a 3-block CFG:
///   entry(x): c10 = const 10; c = icmp ult x c10; condbr c, then, else
///   then:     c1 = const 1; r = add x c1; ret r
///   else:     ret x
fn cf_demo_module() -> Module {
    use trust_ir::inst::ICmpOp;
    let mut module = Module::new("cf_demo_fixture");
    module.func_types.push(FuncTy {
        params: vec![Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut func = Function::new(FuncId::new(0), "cf", FuncTyId::new(0), BlockId::new(0));

    let mut entry = trust_ir::Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U32));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(10),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ult,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(2),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));

    let mut then_blk = trust_ir::Block::new(BlockId::new(1));
    then_blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(3)),
    );
    then_blk.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(3),
        })
        .with_result(ValueId::new(4)),
    );
    then_blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));

    let mut else_blk = trust_ir::Block::new(BlockId::new(2));
    else_blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));

    func.blocks.push(entry);
    func.blocks.push(then_blk);
    func.blocks.push(else_blk);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The source-side control-flow fixture: the ORIGINAL kernel definition
/// `fun (x : UInt32) => cond (UInt32.blt x (UInt32.ofNat 10))
///                          (UInt32.add x (UInt32.ofNat 1)) x`.
fn cf_demo_source() -> Expr {
    let of_nat = |k: u64| Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
    let cond = Expr::apps(Expr::const_str("UInt32.blt"), [Expr::bvar(0), of_nat(10)]);
    let then_e = Expr::apps(Expr::const_str("UInt32.add"), [Expr::bvar(0), of_nat(1)]);
    let else_e = Expr::bvar(0);
    let ite = Expr::apps(
        Expr::const_str("cond"),
        [Expr::const_str("UInt32"), cond, then_e, else_e],
    );
    Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), ite)
}

/// Expected shared-vocabulary denotation of the control-flow decl:
/// `Bool.rec (λ_:Bool => Nat) x (Nat.mod (Nat.add x 1) 2^32) (Nat.blt x 10)`.
fn expected_cf_body() -> Expr {
    let m = modulus(32);
    let x = Expr::bvar(0);
    let add = Expr::apps(Expr::const_str("Nat.add"), [x.clone(), Expr::nat_lit(1)]);
    let then_e = Expr::apps(Expr::const_str("Nat.mod"), [add, m]);
    let cond = Expr::apps(Expr::const_str("Nat.blt"), [x.clone(), Expr::nat_lit(10)]);
    ite_nat(cond, then_e, x)
}

#[test]
fn test_emitted_side_denotes_control_flow_decl() {
    let module = cf_demo_module();
    let den = denote_function(&module, &module.functions[0]).expect("in Fragment-3a");
    assert_eq!(den.arity, 1);
    assert_eq!(den.width, 32);
    assert_eq!(den.body, expected_cf_body());
}

#[test]
fn test_source_side_denotes_control_flow_decl_identically() {
    let den =
        denote_source(&cf_demo_source(), 32, &[], &RecordVocab::empty()).expect("in Fragment-3a");
    assert_eq!(den.body, expected_cf_body());
}

#[test]
fn test_kernel_accepts_the_honest_control_flow_equation() {
    let module = cf_demo_module();
    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let rhs = denote_source(&cf_demo_source(), 32, &[], &RecordVocab::empty()).unwrap();
    assert_eq!(lhs.arity, rhs.arity);
    kernel_decides(lhs.arity, &lhs.body, &rhs.body)
        .expect("the kernel must decide the honest control-flow equation");
}

#[test]
fn test_kernel_refuses_swapped_branch_arms() {
    // MISCOMPILE DETECTOR (control flow): swap the then/else arms — the emitted
    // CFG returns `x` when it should return `x + 1` and vice-versa. Over an OPEN
    // scrutinee the two `Bool.rec` neutrals are not def-eq, so the kernel REFUSES.
    let mut module = cf_demo_module();
    // Swap by re-pointing the CondBr targets.
    let Inst::CondBr {
        then_target,
        else_target,
        ..
    } = &mut module.functions[0].blocks[0].body[2].inst
    else {
        panic!("fixture layout: node 2 of entry is the CondBr");
    };
    std::mem::swap(then_target, else_target);

    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let rhs = denote_source(&cf_demo_source(), 32, &[], &RecordVocab::empty()).unwrap();
    assert!(
        kernel_decides(lhs.arity, &lhs.body, &rhs.body).is_err(),
        "the kernel must refuse: swapping the branch arms is a miscompile"
    );
}

#[test]
fn test_kernel_refuses_flipped_condition() {
    // MISCOMPILE DETECTOR (control flow): compile `x < 10` as `x > 10` (Ult ->
    // Ugt). The condition denotation flips (`Nat.blt x 10` -> `Nat.blt 10 x`),
    // so the two `Bool.rec` neutrals differ and the kernel REFUSES.
    use trust_ir::inst::ICmpOp;
    let mut module = cf_demo_module();
    let Inst::ICmp { op, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
        panic!("fixture layout: node 1 of entry is the ICmp");
    };
    *op = ICmpOp::Ugt;

    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let rhs = denote_source(&cf_demo_source(), 32, &[], &RecordVocab::empty()).unwrap();
    assert!(
        kernel_decides(lhs.arity, &lhs.body, &rhs.body).is_err(),
        "the kernel must refuse: flipping the comparison is a miscompile"
    );
}

#[test]
fn test_control_flow_out_of_fragment_switch_fails_closed() {
    // A `Switch` terminator (n-way) is not the recognized CondBr diamond —
    // fail-closed rather than mis-denote.
    use trust_ir::inst::SwitchCase;
    let mut module = cf_demo_module();
    module.functions[0].blocks[0].body[2] = InstrNode::new(Inst::Switch {
        value: ValueId::new(2),
        cases: vec![SwitchCase {
            value: Constant::Int(0),
            target: BlockId::new(1),
            args: vec![],
        }],
        default: BlockId::new(2),
        default_args: vec![],
        exhaustive_enum_unreachable: false,
    });
    let err =
        denote_function(&module, &module.functions[0]).expect_err("a Switch is out of Fragment-3a");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "got {err:?}"
    );
}

#[test]
fn test_control_flow_arm_with_call_fails_closed() {
    // A `Call` inside a branch arm keeps the function out of the (call-free)
    // Fragment-3a — fail-closed.
    let mut module = cf_demo_module();
    module.functions[0].blocks[1].body[0] = InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(0)],
    })
    .with_result(ValueId::new(3));
    let err = denote_function(&module, &module.functions[0])
        .expect_err("a Call in an arm is out of Fragment-3a");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "got {err:?}"
    );
}

// ===========================================================================
// Fragment-3b — calls (compositional translation validation)
// ===========================================================================

/// The emitted-side calls fixture: a helper `g(y: u32) -> u32 { y }` (FuncId 0)
/// and a caller `caller(x: u32) -> u32 { g(x) + 1 }` (FuncId 1) as a single
/// straight-line block `r = call g(x); c1 = const 1; s = add r c1; ret s`.
fn calls_demo_module() -> Module {
    let mut module = Module::new("calls_demo_fixture");
    module.func_types.push(FuncTy {
        params: vec![Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });

    // g (id 0): identity.
    let mut g = Function::new(FuncId::new(0), "g", FuncTyId::new(0), BlockId::new(0));
    let mut gb = trust_ir::Block::new(BlockId::new(0));
    gb.params.push((ValueId::new(0), Ty::U32));
    gb.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    g.blocks.push(gb);
    module
        .try_add_function(g)
        .expect("Module::try_add_function: test fixture");

    // caller (id 1): g(x) + 1.
    let mut caller = Function::new(FuncId::new(1), "caller", FuncTyId::new(0), BlockId::new(0));
    let mut cb = trust_ir::Block::new(BlockId::new(0));
    cb.params.push((ValueId::new(0), Ty::U32));
    cb.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    cb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(2)),
    );
    cb.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: ValueId::new(1),
            rhs: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
    );
    cb.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    caller.blocks.push(cb);
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The caller's source: `fun (x : UInt32) => UInt32.add (g x) (UInt32.ofNat 1)`.
fn calls_demo_source() -> Expr {
    let of_nat = |k: u64| Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
    let gx = Expr::app(Expr::const_str("g"), Expr::bvar(0));
    let add = Expr::apps(Expr::const_str("UInt32.add"), [gx, of_nat(1)]);
    Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), add)
}

/// Expected caller denotation: `Nat.mod (Nat.add (G_g x) 1) 2^32`, with
/// `G_g = bvar(1)` (the pinned callee symbol, outer binder) and `x = bvar(0)`.
fn expected_calls_body() -> Expr {
    let m = modulus(32);
    let gx = Expr::app(Expr::bvar(1), Expr::bvar(0));
    let add = Expr::apps(Expr::const_str("Nat.add"), [gx, Expr::nat_lit(1)]);
    Expr::apps(Expr::const_str("Nat.mod"), [add, m])
}

#[test]
fn test_emitted_side_denotes_call_decl() {
    let module = calls_demo_module();
    let den = denote_function(&module, &module.functions[1]).expect("in Fragment-3b");
    assert_eq!(den.arity, 1);
    assert_eq!(den.callees, vec![("g".to_string(), 1)]);
    assert_eq!(den.body, expected_calls_body());
}

#[test]
fn test_source_side_denotes_call_decl_identically() {
    let callees = vec![("g".to_string(), 1)];
    let den = denote_source(&calls_demo_source(), 32, &callees, &RecordVocab::empty())
        .expect("in Fragment-3b");
    assert_eq!(den.body, expected_calls_body());
}

#[test]
fn test_kernel_accepts_the_honest_call_equation() {
    let module = calls_demo_module();
    let lhs = denote_function(&module, &module.functions[1]).unwrap();
    let rhs = denote_source(
        &calls_demo_source(),
        32,
        &lhs.callees,
        &RecordVocab::empty(),
    )
    .unwrap();
    let arities: Vec<usize> = lhs.callees.iter().map(|(_, a)| *a).collect();
    kernel_decides_with(&arities, lhs.arity, &lhs.body, &rhs.body)
        .expect("the kernel must decide the honest compositional equation");
}

#[test]
fn test_kernel_refuses_miscompiled_call_composition() {
    // MISCOMPILE DETECTOR (calls): compile `g(x) + 1` as `g(x) + 2`. The
    // pinned symbol G_g is identical on both sides, but `(G_g x) + 2` is not
    // def-eq to `(G_g x) + 1` — the kernel REFUSES.
    let mut module = calls_demo_module();
    let Inst::Const { value, .. } = &mut module.functions[1].blocks[0].body[1].inst else {
        panic!("fixture layout: caller node 1 is the const 1");
    };
    *value = Constant::Int(2);

    let lhs = denote_function(&module, &module.functions[1]).unwrap();
    let rhs = denote_source(
        &calls_demo_source(),
        32,
        &lhs.callees,
        &RecordVocab::empty(),
    )
    .unwrap();
    let arities: Vec<usize> = lhs.callees.iter().map(|(_, a)| *a).collect();
    assert!(
        kernel_decides_with(&arities, lhs.arity, &lhs.body, &rhs.body).is_err(),
        "the kernel must refuse: (g x) + 2 does not denote (g x) + 1"
    );
}

#[test]
fn test_calls_out_of_fragment_indirect_call_fails_closed() {
    // An indirect call is out of Fragment-3b (direct calls only) — fail-closed.
    // (`Copy` in the caller body is another out-of-fragment op; either suffices.)
    let mut module = calls_demo_module();
    module.functions[1].blocks[0].body[0] = InstrNode::new(Inst::Copy {
        ty: Ty::U32,
        operand: ValueId::new(0),
    })
    .with_result(ValueId::new(1));
    let err = denote_function(&module, &module.functions[1])
        .expect_err("a Copy in the caller body is out of Fragment-3b");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "got {err:?}"
    );
}

// --- Fragment-4 (closed-address computing heap) -------------------------------

use trust_ir::ty::{FieldDef, StructDef, StructRepr};
use trust_ir::StructId;

/// `Pair { x: U32 @0, y: U32 @4 }` — the corpus record layout.
fn pair_struct() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "x".to_string(),
                ty: Ty::U32,
                offset: Some(0),
            },
            FieldDef {
                name: "y".to_string(),
                ty: Ty::U32,
                offset: Some(4),
            },
        ],
        size: Some(8),
        align: Some(4),
        repr: StructRepr::Rust,
        origin: None,
    }
}

/// The emitted-side heap fixture: `fn pair_first(a b: u32) -> u32` lowering
/// `Pair.x (Pair.mk a b)` as the alloc/store/load choreography (hand-built —
/// the native ctor lowering to this shape is future work, like the
/// Fragment-3a fixture):
///
/// ```text
/// v2 = HeapAlloc Pair (CleanHeap)          ; base 0, cells {0, 4}
/// v3 = const u64 0 ; v4 = GEP i8 v2 [v3]   ; folds to 0
/// Store v0 -> v4
/// v5 = const u64 4 ; v6 = GEP i8 v2 [v5]   ; folds to 4
/// Store v1 -> v6
/// v7 = Load v4
/// Release v2 ; Return v7                   ; the cell's only release (count 1)
/// ```
fn heap_pair_module() -> Module {
    let mut module = Module::new("heap_pair_fixture");
    module.structs.push(pair_struct());
    module.func_types.push(FuncTy {
        params: vec![Ty::U32, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut func = Function::new(
        FuncId::new(0),
        "pair_first",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U32));
    block.params.push((ValueId::new(1), Ty::U32));
    block.body.push(
        InstrNode::new(Inst::HeapAlloc {
            ty: Ty::Struct(StructId::new(0)),
            count: None,
            align: None,
            origin: AllocOrigin::CleanHeap,
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(3)),
    );
    block.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I8,
            base: ValueId::new(2),
            indices: vec![ValueId::new(3)],
            inbounds: true,
        })
        .with_result(ValueId::new(4)),
    );
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U32,
        ptr: ValueId::new(4),
        value: ValueId::new(0),
        volatile: false,
        align: None,
    }));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(4),
        })
        .with_result(ValueId::new(5)),
    );
    block.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I8,
            base: ValueId::new(2),
            indices: vec![ValueId::new(5)],
            inbounds: true,
        })
        .with_result(ValueId::new(6)),
    );
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U32,
        ptr: ValueId::new(6),
        value: ValueId::new(1),
        volatile: false,
        align: None,
    }));
    block.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U32,
            ptr: ValueId::new(4),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(7)),
    );
    block.body.push(InstrNode::new(Inst::Release {
        ptr: ValueId::new(2),
    }));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(7)],
    }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// `fun (a b : UInt32) => Pair.x (Pair.mk a b)` — the heap fixture's source.
fn heap_pair_source() -> Expr {
    let mk = Expr::apps(Expr::const_str("Pair.mk"), [Expr::bvar(1), Expr::bvar(0)]);
    let proj = Expr::app(Expr::const_str("Pair.x"), mk);
    Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), proj),
    )
}

/// The expected emitted-side tower for the heap fixture:
/// `hread (hwrite (hwrite hempty 0 a) 4 b) 0` over `a = bvar 1`, `b = bvar 0`.
fn expected_pair_first_body() -> Expr {
    let h = hwrite(
        hwrite(hempty(), Expr::nat_lit(0), Expr::bvar(1)),
        Expr::nat_lit(4),
        Expr::bvar(0),
    );
    hread(h, Expr::nat_lit(0))
}

#[test]
fn test_heap_vocab_declarations_install_in_kernel() {
    // The three combinators are honest DEFINITIONS: they type-check into the
    // bare prelude environment and add no axioms.
    let mut env = Environment::with_prelude();
    for decl in heap_vocab_declarations() {
        env.add_decl(decl)
            .expect("definitional combinator installs");
    }
}

#[test]
fn test_kernel_reduces_heap_tower() {
    // The design note's reduction story, directly: reads over a two-write
    // tower normalize to the stored OPEN value (Nat.beq on literals computes,
    // Bool.rec selects), and a wrong readback REFUSES.
    let h = hwrite(
        hwrite(hempty(), Expr::nat_lit(0), Expr::bvar(1)),
        Expr::nat_lit(8),
        Expr::bvar(0),
    );
    kernel_decides(2, &hread(h.clone(), Expr::nat_lit(8)), &Expr::bvar(0))
        .expect("read of the top write reduces to its value");
    kernel_decides(2, &hread(h.clone(), Expr::nat_lit(0)), &Expr::bvar(1))
        .expect("read past the top write reduces to the earlier value");
    assert!(
        kernel_decides(2, &hread(h, Expr::nat_lit(8)), &Expr::bvar(1)).is_err(),
        "reading the WRONG value must refuse"
    );
    // `hempty` is a total function that reduces to 0 — pinned here for the
    // VOCAB's computational behavior only. The WALKER never lets a load of an
    // unwritten cell denote (uninitialized read is UB in trust-ir semantics;
    // see test_walker_refuses_load_of_unwritten_cell), so this 0 is
    // unreachable as a denotation.
    kernel_decides(0, &hread(hempty(), Expr::nat_lit(16)), &Expr::nat_lit(0))
        .expect("hempty reduces to 0 (vocab computation, never a denotation)");
}

#[test]
fn test_emitted_side_denotes_heap_pair_decl() {
    let module = heap_pair_module();
    let den = denote_function(&module, &module.functions[0]).expect("in Fragment-4");
    assert_eq!(den.arity, 2);
    assert_eq!(den.width, 32);
    assert!(den.callees.is_empty());
    assert_eq!(den.body, expected_pair_first_body());
}

#[test]
fn test_source_side_denotes_projection_of_ctor() {
    // Pure substitution: `Pair.x (Pair.mk a b)` denotes to `[[a]]` directly —
    // the source side never sees the heap.
    let module = heap_pair_module();
    let vocab = RecordVocab::from_module(&module);
    let den = denote_source(&heap_pair_source(), 32, &[], &vocab).expect("in fragment");
    assert_eq!(den.arity, 2);
    assert_eq!(den.body, Expr::bvar(1));
}

#[test]
fn test_kernel_accepts_the_honest_heap_equation() {
    let module = heap_pair_module();
    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let vocab = RecordVocab::from_module(&module);
    let rhs = denote_source(&heap_pair_source(), 32, &[], &vocab).unwrap();
    kernel_decides(lhs.arity, &lhs.body, &rhs.body)
        .expect("the heap tower must iota-reduce away and the kernel decide the equation");
}

#[test]
fn test_kernel_refuses_wrong_offset_load() {
    // MISCOMPILE DETECTOR: the load reads offset 4 (field y) while the source
    // projects field x — both valid cells, so the WALKER accepts and the
    // KERNEL refuses (the design note's wrong-offset case).
    let mut module = heap_pair_module();
    let Inst::Load { ptr, .. } = &mut module.functions[0].blocks[0].body[7].inst else {
        panic!("fixture layout: node 7 is the Load");
    };
    *ptr = ValueId::new(6); // the y-field pointer
    let lhs = denote_function(&module, &module.functions[0]).expect("still in fragment");
    let vocab = RecordVocab::from_module(&module);
    let rhs = denote_source(&heap_pair_source(), 32, &[], &vocab).unwrap();
    assert!(
        kernel_decides(lhs.arity, &lhs.body, &rhs.body).is_err(),
        "reading field y does not denote projecting field x"
    );
}

#[test]
fn test_two_allocations_get_distinct_block_bases() {
    // Two Pair allocations: bases 0 and BLOCK=16 (smallest multiple of 8
    // strictly larger than the 8-byte allocation) — non-overlapping by model
    // construction. The x-field Load is moved AFTER the second allocation's
    // store, so if the bases ever collided (base-assignment regression), the
    // second store of `b` would land on the first allocation's cell 0 and the
    // load would read `b`, refusing the equation below.
    let mut module = heap_pair_module();
    let body = &mut module.functions[0].blocks[0].body;
    // Splice before the Load: v8 = alloc; v9 = const 0; v10 = gep;
    // store v1 -> v10; release v8 — then the original load/release/ret.
    let ret = body.pop().unwrap();
    let release = body.pop().unwrap();
    let load = body.pop().unwrap();
    body.push(
        InstrNode::new(Inst::HeapAlloc {
            ty: Ty::Struct(StructId::new(0)),
            count: None,
            align: None,
            origin: AllocOrigin::CleanHeap,
        })
        .with_result(ValueId::new(8)),
    );
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(9)),
    );
    body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I8,
            base: ValueId::new(8),
            indices: vec![ValueId::new(9)],
            inbounds: true,
        })
        .with_result(ValueId::new(10)),
    );
    body.push(InstrNode::new(Inst::Store {
        ty: Ty::U32,
        ptr: ValueId::new(10),
        value: ValueId::new(1),
        volatile: false,
        align: None,
    }));
    body.push(InstrNode::new(Inst::Release {
        ptr: ValueId::new(8),
    }));
    body.push(load);
    body.push(release);
    body.push(ret);

    let den = denote_function(&module, &module.functions[0]).expect("in Fragment-4");
    // The load's snapshot now includes the second allocation's write: its
    // store of `b` landed at literal 16, NOT over the first allocation's
    // cells {0, 4} — so the load at 0 still reads `a`. Under a base
    // collision it would read `b` (bvar 0) and this refuses.
    kernel_decides(den.arity, &den.body, &Expr::bvar(1))
        .expect("the first allocation's field x still reads a");
}

#[test]
fn test_walker_refuses_load_of_unwritten_cell() {
    // SOUNDNESS: drop the x-field store — the load then reads a never-written
    // cell. An uninitialized read is UB in trust-ir semantics; if it denoted
    // to hempty's 0, a lowering that dropped a store of LITERAL 0 would still
    // certify `0 = 0`. The walker must refuse it as a wrong emission.
    let mut module = heap_pair_module();
    module.functions[0].blocks[0].body.remove(3); // the `store a -> cell 0`
    let err = denote_function(&module, &module.functions[0])
        .expect_err("load of a never-written cell must refuse");
    assert!(
        matches!(err, ReflectError::WrongEmission(_)),
        "must be WrongEmission (escalates to REFUSED at the mint gate), got: {err:?}"
    );
}

#[test]
fn test_walker_refuses_out_of_bounds_field_offset() {
    // SOUNDNESS: a field recorded OUTSIDE the recorded struct size would
    // place its cell at/past the next allocation's BLOCK base, aliasing
    // another allocation in the model — refuse the inconsistent layout.
    let mut module = heap_pair_module();
    module.structs[0].fields[1].offset = Some(16); // recorded size stays 8
    let err = denote_function(&module, &module.functions[0])
        .expect_err("field offset outside the recorded struct size must refuse");
    assert!(
        matches!(err, ReflectError::WrongEmission(_)),
        "got: {err:?}"
    );
}

#[test]
fn test_walker_refuses_overlapping_field_offsets() {
    // SOUNDNESS: overlapping recorded U32 fields share machine bytes the
    // model would treat as two independent Nat cells — refuse.
    let mut module = heap_pair_module();
    module.structs[0].fields[1].offset = Some(2); // overlaps the U32 at 0
    let err = denote_function(&module, &module.functions[0])
        .expect_err("overlapping recorded field offsets must refuse");
    assert!(
        matches!(err, ReflectError::WrongEmission(_)),
        "got: {err:?}"
    );
}

#[test]
fn test_walker_refuses_aliased_release() {
    // The fragment requires `Release` to cite the allocation's own result
    // value (the same shape the emit gate's balance check counts), so a
    // release through a GEP-0 alias is OUT OF FRAGMENT (a skip at the gate)
    // — not a false "wrong-code emission". The balance gate does not count
    // such a `Release` (it is not a `HeapAlloc` result), so this refusal is
    // the only thing standing between an aliased release and a certificate.
    let mut module = heap_pair_module();
    let Inst::Release { ptr } = &mut module.functions[0].blocks[0].body[8].inst else {
        panic!("fixture layout: node 8 is the Release");
    };
    *ptr = ValueId::new(4); // the GEP-0 alias of the base
    let err = denote_function(&module, &module.functions[0])
        .expect_err("aliased Release is out of fragment");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "aliased release must be Unsupported (an out-of-fragment skip), got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("Release pointer is not the allocation's own HeapAlloc result value"),
        "the walker must refuse the aliased Release by name, got: {msg}"
    );
}

#[test]
fn test_walker_refuses_aliased_second_release() {
    // The soundness case the own-result rule exists for: after the balanced
    // `Release v2` (node 8) frees the count-1 cell, a SECOND `Release`
    // spelled through the GEP-0 alias `v4` is the RC underflow — a double
    // free. The balance gate deliberately does not count it (it is not a
    // `HeapAlloc` result), and the liveness kill is idempotent, so only the
    // walker's own-result check refuses it; a walker that resolved the
    // `Release` owner through the GEP address fold would denote this body.
    let mut module = heap_pair_module();
    let body = &mut module.functions[0].blocks[0].body;
    assert!(
        matches!(body[8].inst, Inst::Release { ptr } if ptr == ValueId::new(2)),
        "fixture layout: node 8 is `Release v2`"
    );
    body.insert(
        9,
        InstrNode::new(Inst::Release {
            ptr: ValueId::new(4),
        }),
    );
    let err = denote_function(&module, &module.functions[0])
        .expect_err("an aliased second Release must not denote");
    let msg = err.to_string();
    assert!(
        msg.contains("Release pointer is not the allocation's own HeapAlloc result value"),
        "the walker must refuse the aliased second Release by name, got: {msg}"
    );
}

#[test]
fn test_walker_refuses_dealloc_of_a_heap_cell() {
    // A Fragment-4 cell is a reference-counted `CleanHeap` cell: trust-ir's
    // SPEC ("A reference-counted cell is released by `Release`, never by
    // `Dealloc`") makes a `Dealloc` of it undefined behaviour. Re-spelling the
    // fixture's release as `Dealloc` of the allocation's own result value must
    // be a NAMED `WrongEmission` (the mint gate REFUSES it) — not an
    // `Unsupported` (which the mint gate would SKIP), and not a denotation.
    let mut module = heap_pair_module();
    let node = &mut module.functions[0].blocks[0].body[8];
    assert!(
        matches!(node.inst, Inst::Release { .. }),
        "fixture layout: node 8 is the Release"
    );
    *node = InstrNode::new(Inst::Dealloc {
        ptr: ValueId::new(2),
    });
    let err = denote_function(&module, &module.functions[0])
        .expect_err("a Dealloc-freed CleanHeap cell must not denote");
    assert!(
        matches!(err, ReflectError::WrongEmission(_)),
        "must be WrongEmission (escalates to REFUSED at the mint gate), got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("Dealloc") && msg.contains("undefined behaviour"),
        "the walker must refuse the Dealloc BY NAME, got: {msg}"
    );
}

#[test]
fn test_walker_refuses_use_after_release() {
    // The walker's `Release` arm KILLS the cell's liveness, and every later
    // `Load` / `Store` through it is refused by `resolve_cell`. Moving the
    // `Release` (node 8) in front of the projection `Load` (node 7), or in
    // front of the second `Store` (node 6), keeps the value equation and the
    // balance (one `Release` of `v2`) intact, so only the liveness kill can
    // see it.
    for (to, op) in [(7, "Load"), (6, "Store")] {
        let mut module = heap_pair_module();
        let body = &mut module.functions[0].blocks[0].body;
        let release = body.remove(8);
        assert!(
            matches!(release.inst, Inst::Release { .. }),
            "fixture layout: node 8 is the Release"
        );
        body.insert(to, release);
        let err = denote_function(&module, &module.functions[0])
            .expect_err("a use after the Release must not denote");
        let msg = err.to_string();
        assert!(
            msg.contains(&format!("{op} touches a released allocation")),
            "a {op} after the Release must be refused by the walker, got: {msg}"
        );
    }
}

#[test]
fn test_source_bare_ctor_fails_closed() {
    // A ctor application NOT under a matching projection has no denotation.
    let module = heap_pair_module();
    let vocab = RecordVocab::from_module(&module);
    let mk = Expr::apps(Expr::const_str("Pair.mk"), [Expr::bvar(1), Expr::bvar(0)]);
    let defn = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), mk),
    );
    let err = denote_source(&defn, 32, &[], &vocab).expect_err("bare ctor is out of fragment");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "got {err:?}"
    );
}

#[test]
fn test_source_projection_of_non_ctor_fails_closed() {
    let module = heap_pair_module();
    let vocab = RecordVocab::from_module(&module);
    let proj = Expr::app(Expr::const_str("Pair.x"), Expr::bvar(0));
    let defn = Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), proj);
    let err = denote_source(&defn, 32, &[], &vocab)
        .expect_err("projection of a non-ctor value is out of fragment");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "got {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("non-constructor"),
        "auditable label, got: {msg}"
    );
}

#[test]
fn test_heap_op_in_3a_entry_fails_closed() {
    // Heap use must stay within one arm: a HeapAlloc in the CondBr ENTRY
    // prefix is out of fragment (fail-closed).
    let mut module = heap_pair_module();
    module.func_types.push(FuncTy {
        params: vec![Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut func = Function::new(
        FuncId::new(1),
        "entry_heap",
        FuncTyId::new(1),
        BlockId::new(0),
    );
    let mut entry = trust_ir::Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U32));
    entry.body.push(
        InstrNode::new(Inst::HeapAlloc {
            ty: Ty::Struct(StructId::new(0)),
            count: None,
            align: None,
            origin: AllocOrigin::CleanHeap,
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ult,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(2),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));
    let mut then_blk = trust_ir::Block::new(BlockId::new(1));
    then_blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    let mut else_blk = trust_ir::Block::new(BlockId::new(2));
    else_blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    func.blocks.push(entry);
    func.blocks.push(then_blk);
    func.blocks.push(else_blk);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let err = denote_function(&module, &module.functions[1])
        .expect_err("heap op in the 3a entry prefix is out of fragment");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "got {err:?}"
    );
    let msg = err.to_string();
    assert!(msg.contains("heap-capable"), "auditable label, got: {msg}");
}

// ---------------------------------------------------------------------------
// Fragment-5 OWNERSHIP BALANCE (trust-ir SPEC "A reference-counted cell is
// released by `Release`, never by `Dealloc`", clause 4). Every shape below is
// admitted by the VALUE walker (`denote_closed_zeroary`), which cannot see
// reference counting; before the balance each refused shape denoted — and a
// kernel judgment over it would have certified a program that frees a
// reference it still uses, frees one twice, or leaks one.
// ---------------------------------------------------------------------------

/// A Fragment-5 fixture module: bodyless runtime rows declared on first use
/// (with their Clean runtime signatures), and bodied `() -> Ptr` functions.
struct F5Fx {
    module: Module,
    rows: BTreeMap<&'static str, FuncId>,
}

/// One straight-line body under construction.
struct F5Body {
    nodes: Vec<InstrNode>,
    next: u32,
}

impl F5Fx {
    fn new() -> Self {
        F5Fx {
            module: Module::new("f5_balance"),
            rows: BTreeMap::new(),
        }
    }

    fn func_ty(&mut self, params: Vec<Ty>, returns: Vec<Ty>) -> FuncTyId {
        self.module.func_types.push(FuncTy {
            params,
            returns,
            is_vararg: false,
            abi: None,
        });
        FuncTyId::new(u32::try_from(self.module.func_types.len() - 1).unwrap())
    }

    fn next_fid(&self) -> FuncId {
        FuncId::new(u32::try_from(self.module.functions.len()).unwrap())
    }

    /// The bodyless runtime row `name`, declared once.
    fn row(&mut self, name: &'static str) -> FuncId {
        if let Some(fid) = self.rows.get(name) {
            return *fid;
        }
        let (params, returns) = match name {
            "clean_box_uint64" | "clean_nat_of_u64" => (vec![Ty::U64], vec![Ty::Ptr]),
            "clean_nat_big" => (vec![Ty::U64, Ty::U64], vec![Ty::Ptr]),
            "clean_unbox_uint64" => (vec![Ty::Ptr], vec![Ty::U64]),
            "l_Nat_add" | "l_Nat_mul" | "l_Nat_sub" => (vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr]),
            other => panic!("fixture row `{other}` has no signature here"),
        };
        let ty = self.func_ty(params, returns);
        let fid = self.next_fid();
        self.module
            .try_add_function(Function::new(fid, name, ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");
        self.rows.insert(name, fid);
        fid
    }

    /// Define the `() -> Ptr` function `name` with `body`, returning `ret`.
    fn define(&mut self, name: &str, mut body: F5Body, ret: ValueId) -> FuncId {
        body.nodes
            .push(InstrNode::new(Inst::Return { values: vec![ret] }));
        let ty = self.func_ty(vec![], vec![Ty::Ptr]);
        let fid = self.next_fid();
        let mut func = Function::new(fid, name, ty, BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body = body.nodes;
        func.blocks.push(block);
        self.module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        fid
    }

    fn function(&self, name: &str) -> &Function {
        self.module
            .functions
            .iter()
            .find(|f| f.name == name)
            .expect("fixture function")
    }

    fn denote(&self, name: &str) -> Result<TvDenotation, ReflectError> {
        denote_function(&self.module, self.function(name))
    }
}

impl F5Body {
    fn new() -> Self {
        F5Body {
            nodes: Vec::new(),
            next: 0,
        }
    }

    fn push(&mut self, inst: Inst) -> ValueId {
        let v = ValueId::new(self.next);
        self.next += 1;
        self.nodes.push(InstrNode::new(inst).with_result(v));
        v
    }

    fn konst(&mut self, k: i128) -> ValueId {
        self.push(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(k),
        })
    }

    fn call(&mut self, callee: FuncId, args: &[ValueId]) -> ValueId {
        self.push(Inst::Call {
            callee,
            args: args.to_vec(),
        })
    }

    /// `row(k)` for a one-`u64` boxing row.
    fn boxed(&mut self, fx: &mut F5Fx, row: &'static str, k: i128) -> ValueId {
        let c = self.konst(k);
        let callee = fx.row(row);
        self.call(callee, &[c])
    }

    fn copy(&mut self, v: ValueId) -> ValueId {
        self.push(Inst::Copy {
            ty: Ty::Ptr,
            operand: v,
        })
    }

    fn retain(&mut self, v: ValueId) {
        self.nodes.push(InstrNode::new(Inst::Retain { ptr: v }));
    }

    fn release(&mut self, v: ValueId) {
        self.nodes.push(InstrNode::new(Inst::Release { ptr: v }));
    }
}

/// The balance refuses `name` as a WRONG EMISSION whose reason names `class`.
#[track_caller]
fn assert_balance_refuses(fx: &F5Fx, name: &str, class: &str) -> String {
    match fx.denote(name) {
        Err(ReflectError::WrongEmission(reason)) => {
            assert!(
                reason.contains("Fragment-5 ownership balance") && reason.contains(class),
                "`{name}`: the refusal must name `{class}`, got: {reason}"
            );
            reason
        }
        other => panic!("`{name}` must be refused as a wrong emission, got {other:?}"),
    }
}

/// A use or give-up of a reference after its last reference is gone.
const USE_AFTER_FREE: &str = "after its last reference is gone (use after free / count underflow)";
/// A reference still held when the body returns.
const LEAK: &str = "when the body returns (a leak)";

/// H1: the returned box is released first — use after free on the return.
#[test]
fn f5_balance_refuses_release_of_the_returned_box() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_box_uint64", 256);
    b.release(x);
    fx.define("demo", b, x);
    let reason = assert_balance_refuses(&fx, "demo", USE_AFTER_FREE);
    assert!(reason.contains("the Return"), "{reason}");
}

/// H2: a temporary released twice — a count underflow (double free).
#[test]
fn f5_balance_refuses_a_double_release() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_box_uint64", 256);
    let t = b.boxed(&mut fx, "clean_box_uint64", 7);
    b.release(t);
    b.release(t);
    fx.define("demo", b, x);
    let reason = assert_balance_refuses(&fx, "demo", USE_AFTER_FREE);
    assert!(reason.contains("a Release"), "{reason}");
}

/// H3: a retain nothing gives up — the returned box leaks at count 1.
#[test]
fn f5_balance_refuses_a_retained_leak() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_box_uint64", 256);
    b.retain(x);
    fx.define("demo", b, x);
    let reason = assert_balance_refuses(&fx, "demo", LEAK);
    assert!(reason.contains("count 1"), "{reason}");
}

/// H4: `x * x` with ONE reference — `l_Nat_mul` decs both operands, so the
/// second dec underflows. No RC instruction at all: only a balance that
/// counts the runtime's argument consumption refuses it.
#[test]
fn f5_balance_refuses_a_double_consume() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_nat_of_u64", 3);
    let mul = fx.row("l_Nat_mul");
    let r = b.call(mul, &[x, x]);
    fx.define("demo", b, r);
    let reason = assert_balance_refuses(&fx, "demo", USE_AFTER_FREE);
    assert!(reason.contains("an argument of `l_Nat_mul`"), "{reason}");
}

/// H5: an operand released, then consumed — use after free.
#[test]
fn f5_balance_refuses_release_then_consume() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_nat_of_u64", 2);
    let y = b.boxed(&mut fx, "clean_nat_of_u64", 3);
    b.release(x);
    let mul = fx.row("l_Nat_mul");
    let r = b.call(mul, &[x, y]);
    fx.define("demo", b, r);
    let reason = assert_balance_refuses(&fx, "demo", USE_AFTER_FREE);
    assert!(reason.contains("an argument of `l_Nat_mul`"), "{reason}");
}

/// H6: an inlined 0-ary helper releases the box it returns. The caller is
/// balanced on its own; the helper is held to the rule on ITS body.
#[test]
fn f5_balance_refuses_a_helper_that_releases_its_return() {
    let mut fx = F5Fx::new();
    let mut h = F5Body::new();
    let x = h.boxed(&mut fx, "clean_box_uint64", 256);
    h.release(x);
    let helper = fx.define("helper", h, x);
    let mut b = F5Body::new();
    let r = b.call(helper, &[]);
    fx.define("demo", b, r);
    let reason = assert_balance_refuses(&fx, "demo", USE_AFTER_FREE);
    assert!(
        reason.contains("in `helper`") && reason.contains("the Return"),
        "the refusal names the helper's own return: {reason}"
    );
}

/// H7: a `Copy` names the same reference, so releasing the copy frees the
/// box the body then returns.
#[test]
fn f5_balance_refuses_release_through_a_copy() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_box_uint64", 256);
    let c = b.copy(x);
    b.release(c);
    fx.define("demo", b, x);
    let reason = assert_balance_refuses(&fx, "demo", USE_AFTER_FREE);
    assert!(reason.contains("the Return"), "{reason}");
}

/// H8: an operand `l_Nat_add` consumed is returned — use after free on the
/// return. No RC instruction at all.
#[test]
fn f5_balance_refuses_return_of_a_consumed_operand() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_nat_of_u64", 2);
    let y = b.boxed(&mut fx, "clean_nat_of_u64", 3);
    let add = fx.row("l_Nat_add");
    let _sum = b.call(add, &[x, y]);
    fx.define("demo", b, x);
    let reason = assert_balance_refuses(&fx, "demo", USE_AFTER_FREE);
    assert!(reason.contains("the Return"), "{reason}");
}

/// The k2 Perceus shape Clean really emits for `let x := 2^64; x * x`: one
/// `retain` because `l_Nat_mul` consumes both operands. Balanced.
#[test]
fn f5_balance_admits_the_perceus_retain_shape() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let lo = b.konst(0);
    let hi = b.konst(1);
    let big = fx.row("clean_nat_big");
    let x = b.call(big, &[lo, hi]);
    b.retain(x);
    let mul = fx.row("l_Nat_mul");
    let r = b.call(mul, &[x, x]);
    fx.define("demo", b, r);
    let d = fx.denote("demo").expect("the Perceus shape is balanced");
    assert_eq!(d.arity, 0);
    assert!(d.callees.is_empty());
}

/// A boxed temporary built and released before the constant is returned.
#[test]
fn f5_balance_admits_a_released_temporary() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_box_uint64", 256);
    let t = b.boxed(&mut fx, "clean_box_uint64", 7);
    b.release(t);
    fx.define("demo", b, x);
    fx.denote("demo").expect("a released temporary is balanced");
}

/// `retain x; release x; ret x`: the count goes 1 -> 2 -> 1 -> 0.
#[test]
fn f5_balance_admits_retain_then_release() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_box_uint64", 256);
    b.retain(x);
    b.release(x);
    fx.define("demo", b, x);
    fx.denote("demo").expect("retain-then-release is balanced");
}

/// An `unbox` only READS its argument: `u = unbox_uint64 x` then returning
/// `x` is balanced, and a `Release` of the scalar `u` is outside the fragment
/// (a skip, never a refusal).
#[test]
fn f5_balance_unbox_borrows_and_rc_of_a_scalar_is_out_of_fragment() {
    let mut fx = F5Fx::new();
    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_box_uint64", 256);
    let unbox = fx.row("clean_unbox_uint64");
    let _u = b.call(unbox, &[x]);
    fx.define("borrow", b, x);
    fx.denote("borrow").expect("an unbox argument is only read");

    let mut b = F5Body::new();
    let x = b.boxed(&mut fx, "clean_box_uint64", 256);
    let u = b.call(unbox, &[x]);
    b.release(u);
    fx.define("scalar_rc", b, x);
    let err = fx
        .denote("scalar_rc")
        .expect_err("a Release of a scalar is out of fragment");
    assert!(
        matches!(&err, ReflectError::Unsupported { construct } if construct.contains("not a boxed reference")),
        "a Release of a non-reference is a skip, got {err:?}"
    );
}

#[test]
fn source_instance_named_requires_its_original_environment() {
    use clean_kernel::Level;
    let u = Expr::const_str("UInt32");
    let levels = vec![Level::zero(); 3];
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TVTest.namedDictionary"),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(Name::from_string("HAdd"), levels.clone()),
            [u.clone(), u.clone(), u.clone()],
        ),
        value: Expr::apps(
            Expr::const_(Name::from_string("HAdd.mk"), levels.clone()),
            [
                u.clone(),
                u.clone(),
                u.clone(),
                Expr::const_str("UInt32.sub"),
            ],
        ),
        is_reducible: true,
    })
    .expect("a checked named non-additive dictionary");
    let source = Expr::lam(
        BinderInfo::Default,
        u.clone(),
        Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("HAdd.hAdd"), levels),
                [
                    u.clone(),
                    u.clone(),
                    u.clone(),
                    Expr::const_str("TVTest.namedDictionary"),
                    Expr::bvar(1),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    let error = denote_source(&source, 32, &[], &RecordVocab::empty())
        .expect_err("a name without its defining environment grants no meaning");
    assert!(
        error.to_string().contains("source instance dictionary"),
        "{error}"
    );
    let actual =
        denote_source_in_environment(&source, 32, &[], &RecordVocab::empty(), &env).unwrap();
    let expected = denote_binop(BinOp::Sub, Expr::bvar(1), Expr::bvar(0), &modulus(32)).unwrap();
    assert_eq!(actual.body, expected);
}

#[test]
fn source_instance_canonical_named_dictionaries_retain_all_uint_widths() {
    use clean_kernel::Level;
    let env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let u = Expr::const_str(&format!("UInt{width}"));
        let numeral = Expr::apps(
            Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
            [
                u.clone(),
                Expr::nat_lit(7),
                Expr::app(
                    Expr::const_str(&format!("instOfNatUInt{width}")),
                    Expr::nat_lit(7),
                ),
            ],
        );
        let body = Expr::apps(
            Expr::const_(Name::from_string("HAdd.hAdd"), vec![Level::zero(); 3]),
            [
                u.clone(),
                u.clone(),
                u.clone(),
                Expr::const_str(&format!("instHAddUInt{width}")),
                Expr::bvar(0),
                numeral,
            ],
        );
        let source = Expr::lam(BinderInfo::Default, u, body);
        let actual =
            denote_source_in_environment(&source, width, &[], &RecordVocab::empty(), &env).unwrap();
        assert_eq!(
            actual.body,
            denote_binop(BinOp::Add, Expr::bvar(0), Expr::nat_lit(7), &modulus(width)).unwrap()
        );
    }
}

#[test]
fn source_instance_nat_literal_uses_the_field_and_refuses_unknown_names() {
    use clean_kernel::Level;
    let n = Expr::const_str("Nat");
    let dictionary = Expr::apps(
        Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]),
        [n.clone(), Expr::nat_lit(7), Expr::nat_lit(8)],
    );
    let source = Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [n.clone(), Expr::nat_lit(7), dictionary],
    );
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TVTest.natOfNat"),
        level_params: vec![],
        type_: n.clone(),
        value: source.clone(),
        is_reducible: true,
    })
    .unwrap();
    assert_eq!(
        denote_source_nat(&source, &[]).unwrap().body,
        Expr::nat_lit(8)
    );
    let unknown = Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            n,
            Expr::nat_lit(7),
            Expr::const_str("TVTest.unknownDictionary"),
        ],
    );
    assert!(denote_source_nat(&unknown, &[])
        .unwrap_err()
        .to_string()
        .contains("source instance dictionary"));
}

fn checked_review_hadd_dictionary(field: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("HAdd.mk"), vec![Level::zero(); 3]),
        [
            Expr::const_str("UInt32"),
            Expr::const_str("UInt32"),
            Expr::const_str("UInt32"),
            field,
        ],
    )
}

fn checked_review_named_dictionary_source(env: &mut Environment, dictionary: Expr) -> Expr {
    let u = Expr::const_str("UInt32");
    let name = Name::from_string("TVReview.dictionary");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(Name::from_string("HAdd"), vec![Level::zero(); 3]),
            [u.clone(), u.clone(), u.clone()],
        ),
        value: dictionary,
        is_reducible: true,
    })
    .expect("the named dictionary must be checked by the actual kernel");
    let source = Expr::lam(
        BinderInfo::Default,
        u.clone(),
        Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("HAdd.hAdd"), vec![Level::zero(); 3]),
                [
                    u.clone(),
                    u.clone(),
                    u.clone(),
                    Expr::const_(name, vec![]),
                    Expr::bvar(1),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TVReview.source"),
        level_params: vec![],
        type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), u)),
        value: source.clone(),
        is_reducible: true,
    })
    .expect("the complete original source must be kernel checked");
    source
}

#[test]
fn source_instance_hidden_primitive_display_twin_refuses() {
    let mut env = Environment::with_prelude();
    let u = Expr::const_str("UInt32");
    let hidden = Name::anon().str("UInt32.add");
    assert_ne!(hidden, Name::from_string("UInt32.add"));
    assert_eq!(hidden.to_string(), "UInt32.add");
    env.add_decl(Declaration::Definition {
        name: hidden.clone(),
        level_params: vec![],
        type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), u)),
        value: Expr::const_str("UInt32.sub"),
        is_reducible: true,
    })
    .expect("the distinct escaped definition really denotes subtraction");
    let source = checked_review_named_dictionary_source(
        &mut env,
        checked_review_hadd_dictionary(Expr::const_(hidden, vec![])),
    );
    let error = denote_source_in_environment(&source, 32, &[], &RecordVocab::empty(), &env)
        .expect_err("unfolding must not give a display twin the ordinary primitive's meaning");
    assert!(error.to_string().contains("escaped typed names"), "{error}");
}

#[test]
fn source_instance_hidden_constructor_display_twin_refuses() {
    let mut env = Environment::with_prelude();
    let u = Expr::const_str("UInt32");
    let field_ty = Expr::arrow(u.clone(), Expr::arrow(u.clone(), u.clone()));
    let dictionary_ty = Expr::apps(
        Expr::const_(Name::from_string("HAdd"), vec![Level::zero(); 3]),
        [u.clone(), u.clone(), u.clone()],
    );
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let ty = (0..3).fold(Expr::arrow(field_ty.clone(), dictionary_ty), |body, _| {
        Expr::arrow(type0.clone(), body)
    });
    // This checked function ignores its apparent operation argument and stores
    // subtraction. It is a definition with the same DISPLAY as the constructor.
    let value = (0..3).fold(
        Expr::lam(
            BinderInfo::Default,
            field_ty,
            checked_review_hadd_dictionary(Expr::const_str("UInt32.sub")),
        ),
        |body, _| Expr::lam(BinderInfo::Default, type0.clone(), body),
    );
    let hidden = Name::anon().str("HAdd.mk");
    assert_ne!(hidden, Name::from_string("HAdd.mk"));
    env.add_decl(Declaration::Definition {
        name: hidden.clone(),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("the constructor's display twin is a valid distinct function");
    let dictionary = Expr::apps(
        Expr::const_(hidden, vec![]),
        [u.clone(), u.clone(), u, Expr::const_str("UInt32.add")],
    );
    let source = checked_review_named_dictionary_source(&mut env, dictionary);
    let error = denote_source_in_environment(&source, 32, &[], &RecordVocab::empty(), &env)
        .expect_err("a display twin must neither stop reduction nor supply constructor fields");
    assert!(error.to_string().contains("escaped typed names"), "{error}");
}

#[test]
fn source_instance_hidden_nat_field_head_refuses() {
    let mut env = Environment::with_prelude();
    let n = Expr::const_str("Nat");
    let hidden = Name::anon().str("Nat.add");
    env.add_decl(Declaration::Definition {
        name: hidden.clone(),
        level_params: vec![],
        type_: Expr::arrow(n.clone(), Expr::arrow(n.clone(), n.clone())),
        value: Expr::const_str("Nat.sub"),
        is_reducible: true,
    })
    .unwrap();
    let name = Name::from_string("TVReview.natDictionary");
    let of_nat = |name: &str| Expr::const_(Name::from_string(name), vec![Level::zero()]);
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::apps(of_nat("OfNat"), [n.clone(), Expr::nat_lit(7)]),
        value: Expr::apps(
            of_nat("OfNat.mk"),
            [
                n.clone(),
                Expr::nat_lit(7),
                Expr::apps(
                    Expr::const_(hidden, vec![]),
                    [Expr::nat_lit(10), Expr::nat_lit(3)],
                ),
            ],
        ),
        is_reducible: true,
    })
    .unwrap();
    let source = Expr::apps(
        of_nat("OfNat.ofNat"),
        [n.clone(), Expr::nat_lit(7), Expr::const_(name, vec![])],
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TVReview.natSource"),
        level_params: vec![],
        type_: n,
        value: source.clone(),
        is_reducible: true,
    })
    .expect("the original Nat source is kernel checked");
    let error = denote_source_nat_in_environment(&source, &[], &env)
        .expect_err("an unfolded Nat field must not reinterpret a display twin");
    assert!(error.to_string().contains("escaped typed names"), "{error}");
}

#[test]
fn source_instance_hidden_condition_head_refuses_but_exact_beta_field_denotes() {
    let u = Expr::const_str("UInt32");
    // The minimal kernel prelude has UInt carriers/arithmetic but does not
    // install the elaborator's comparison overlay. State its real definition
    // here and kernel-check it, rather than using an unresolved fixture name.
    let install_beq = |env: &mut Environment| {
        let to_nat = |x| Expr::app(Expr::const_str("UInt32.toNat"), x);
        env.add_decl(Declaration::Definition {
            name: Name::from_string("UInt32.beq"),
            level_params: vec![],
            type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), Expr::const_str("Bool"))),
            value: Expr::lam(
                BinderInfo::Default,
                u.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    u.clone(),
                    Expr::apps(
                        Expr::const_str("Nat.beq"),
                        [to_nat(Expr::bvar(1)), to_nat(Expr::bvar(0))],
                    ),
                ),
            ),
            is_reducible: true,
        })
        .expect("the actual UInt32 comparison definition kernel-checks");
    };
    let field = |head: Name| {
        let condition = Expr::apps(Expr::const_(head, vec![]), [Expr::bvar(1), Expr::bvar(0)]);
        let literal = |k| Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
        Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::lam(
                BinderInfo::Default,
                u.clone(),
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Bool.rec"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [
                        Expr::lam(BinderInfo::Default, Expr::const_str("Bool"), u.clone()),
                        literal(2),
                        literal(1),
                        condition,
                    ],
                ),
            ),
        )
    };
    let mut env = Environment::with_prelude();
    install_beq(&mut env);
    let hidden = Name::anon().str("UInt32.blt");
    env.add_decl(Declaration::Definition {
        name: hidden.clone(),
        level_params: vec![],
        type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), Expr::const_str("Bool"))),
        value: Expr::const_str("UInt32.beq"),
        is_reducible: true,
    })
    .unwrap();
    let source = checked_review_named_dictionary_source(
        &mut env,
        checked_review_hadd_dictionary(field(hidden)),
    );
    let error = denote_source_in_environment(&source, 32, &[], &RecordVocab::empty(), &env)
        .expect_err("comparison heads exposed inside a field must retain exact identity");
    assert!(error.to_string().contains("escaped typed names"), "{error}");
    let mut honest_env = Environment::with_prelude();
    install_beq(&mut honest_env);
    let source = checked_review_named_dictionary_source(
        &mut honest_env,
        checked_review_hadd_dictionary(field(Name::from_string("UInt32.beq"))),
    );
    let actual =
        denote_source_in_environment(&source, 32, &[], &RecordVocab::empty(), &honest_env).unwrap();
    assert_eq!(
        actual.body,
        ite_nat(
            nat_app2("Nat.beq", Expr::bvar(1), Expr::bvar(0)),
            Expr::nat_lit(1),
            Expr::nat_lit(2)
        )
    );
}
