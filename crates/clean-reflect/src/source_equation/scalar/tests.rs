// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use trust_ir::inst::{BinOp, Inst};
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, FuncTyId, Function, InstrNode, Module, Ty, ValueId,
};

fn boolean_model(op: BinOp) -> ScalarDenotation {
    let mut module = Module::new("actual_typed_boolean_equation");
    module.func_types.push(FuncTy {
        params: vec![Ty::Bool, Ty::Bool],
        returns: vec![Ty::Bool],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(FuncId::new(0), "actual", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), Ty::Bool), (ValueId::new(1), Ty::Bool)];
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::Bool,
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
        .expect("actual typed Boolean IR");
    crate::denote_scalar_function(&module, &module.functions[0]).expect("typed actual IR reader")
}

fn source(env: &mut Environment, primitive: &str) -> Name {
    let name = Name::from_string("actualBooleanSource");
    let bool_ty = Expr::const_str("Bool");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(
            bool_ty.clone(),
            Expr::arrow(bool_ty.clone(), bool_ty.clone()),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            bool_ty.clone(),
            Expr::lam(
                BinderInfo::Default,
                bool_ty,
                Expr::apps(Expr::const_str(primitive), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        ),
        is_reducible: true,
    })
    .expect("kernel checked original definition");
    name
}

#[test]
fn typed_boolean_equation_binds_actual_operation_and_replays_proof() {
    let mut env = Environment::with_prelude();
    let name = source(&mut env, "Bool.xor");
    let model = boolean_model(BinOp::BXor);
    let checked = check_scalar_source_equation(
        &env,
        &name,
        &model,
        Name::from_string("actualBooleanEquation"),
    )
    .expect("original source equation");
    let Declaration::Theorem { value, .. } = checked.declaration() else {
        panic!("theorem")
    };
    check_scalar_source_equation_with_proof(
        &env,
        &name,
        &model,
        Name::from_string("replayedBooleanEquation"),
        value.clone(),
    )
    .expect("same original goal");
    assert!(check_scalar_source_equation(
        &env,
        &name,
        &boolean_model(BinOp::BAnd),
        Name::from_string("wrongAndEquation")
    )
    .is_err());
    assert!(check_scalar_source_equation_with_proof(
        &env,
        &name,
        &model,
        Name::from_string("wrongProof"),
        Expr::const_str("Bool.true")
    )
    .is_err());
    assert!(check_scalar_source_equation_with_proof(
        &env,
        &name,
        &model,
        Name::from_string("openProof"),
        Expr::fvar(FVarId::new(999))
    )
    .is_err());
}

#[test]
fn boolean_elimination_constructs_a_universal_cic_proof() {
    let mut env = Environment::with_prelude();
    let name = source(&mut env, "Bool.xor");
    let model = boolean_model(BinOp::BXor);
    let (statement, proof) = telescope(&name, &model, &mut vec![], true);
    assert!(!proof.has_fvar_quick());
    certify_equation(
        &env,
        &name,
        env.closure_digest(&name).expect("source closure"),
        Name::from_string("booleanCasesEquation"),
        statement,
        proof,
    )
    .expect("kernel checks every case");
}

#[test]
fn rex_four_boolean_source_equation_checks_the_actual_typed_ir() {
    use trust_ir::constant::Constant;
    use trust_ir::inst::ICmpOp;
    let mut module = Module::new("actual_rex_source_equation");
    module.func_types.push(FuncTy {
        params: vec![Ty::Bool; 4],
        returns: vec![Ty::U8],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(FuncId::new(0), "rex", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = (0..4).map(|i| (ValueId::new(i), Ty::Bool)).collect();
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(true),
        })
        .with_result(ValueId::new(4)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(5)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(64),
        })
        .with_result(ValueId::new(6)),
    );
    let mut result = ValueId::new(6);
    let mut source_body = Expr::app(Expr::const_str("UInt8.ofNat"), Expr::nat_lit(64));
    for (i, mask) in [8, 4, 2, 1].into_iter().enumerate() {
        let id = 7 + 4 * i as u32;
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(mask),
            })
            .with_result(ValueId::new(id)),
        );
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::Bool,
                lhs: ValueId::new(i as u32),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(id + 1)),
        );
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::U8,
                cond: ValueId::new(id + 1),
                then_val: ValueId::new(id),
                else_val: ValueId::new(5),
            })
            .with_result(ValueId::new(id + 2)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Or,
                ty: Ty::U8,
                lhs: result,
                rhs: ValueId::new(id + 2),
            })
            .with_result(ValueId::new(id + 3)),
        );
        result = ValueId::new(id + 3);
        let selected = Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str("Bool"),
                    Expr::const_str("UInt8"),
                ),
                Expr::app(Expr::const_str("UInt8.ofNat"), Expr::nat_lit(0)),
                Expr::app(Expr::const_str("UInt8.ofNat"), Expr::nat_lit(mask as u64)),
                Expr::bvar(3 - i as u32),
            ],
        );
        source_body = Expr::apps(Expr::const_str("UInt8.lor"), [source_body, selected]);
    }
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));
    function.blocks.push(block);
    module.try_add_function(function).expect("actual Rex IR");
    let mut signature = Expr::const_str("UInt8");
    for _ in 0..4 {
        signature = Expr::arrow(Expr::const_str("Bool"), signature);
        source_body = Expr::lam(BinderInfo::Default, Expr::const_str("Bool"), source_body);
    }
    let mut env = Environment::with_prelude();
    let name = Name::from_string("actualRexSource");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: signature,
        value: source_body,
        is_reducible: true,
    })
    .expect("actual mixed Bool/UInt source definition");
    let model = crate::denote_scalar_function(&module, &module.functions[0])
        .expect("actual Rex denotation");
    let checked =
        check_scalar_source_equation(&env, &name, &model, Name::from_string("actualRexEquation"))
            .expect("universal four-Bool to UInt8 original-source proof");
    export::write("rex_bool4_u8", &module, &env, &name, &checked);
    let Declaration::Theorem { value, .. } = checked.declaration() else {
        panic!("theorem")
    };
    let mut changed = module.clone();
    let Inst::Const { value: base, .. } = &mut changed.functions[0].blocks[0].body[2].inst else {
        panic!("base")
    };
    *base = Constant::Int(65);
    let wrong = crate::denote_scalar_function(&changed, &changed.functions[0])
        .expect("well typed changed base");
    assert!(check_scalar_source_equation_with_proof(
        &env,
        &name,
        &wrong,
        Name::from_string("wrongRexBase"),
        value.clone()
    )
    .is_err());
}

#[test]
fn uint_to_boolean_source_conditional_uses_its_actual_decision() {
    use trust_ir::constant::Constant;
    use trust_ir::inst::ICmpOp;
    for (width, ty) in [(8, Ty::U8), (16, Ty::U16), (32, Ty::U32), (64, Ty::U64)] {
        let mut module = Module::new("actual_extended_register_predicate");
        module.func_types.push(FuncTy {
            params: vec![ty.clone()],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        });
        let mut function = Function::new(
            FuncId::new(0),
            "extended",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        let mut block = Block::new(BlockId::new(0));
        block.params = vec![(ValueId::new(0), ty.clone())];
        block.body = vec![
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Int(8),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ult,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Select {
                ty: Ty::Bool,
                cond: ValueId::new(2),
                then_val: ValueId::new(3),
                else_val: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ];
        function.blocks.push(block);
        module
            .try_add_function(function)
            .expect("actual mixed scalar IR");
        let uint = Expr::const_str(&format!("UInt{width}"));
        let literal = Expr::app(
            Expr::const_str(&format!("UInt{width}.ofNat")),
            Expr::nat_lit(8),
        );
        let predicate = Expr::apps(
            Expr::const_str(&format!("UInt{width}.lt")),
            [Expr::bvar(0), literal.clone()],
        );
        let decision = Expr::apps(
            Expr::const_str(&format!("UInt{width}.decLt")),
            [Expr::bvar(0), literal],
        );
        let body = Expr::apps(
            Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
            [
                Expr::const_str("Bool"),
                predicate,
                decision,
                Expr::const_str("Bool.false"),
                Expr::const_str("Bool.true"),
            ],
        );
        let mut env = Environment::with_prelude();
        let source = Name::from_string("actualExtendedSource").num(width);
        env.add_decl(Declaration::Definition {
            name: source.clone(),
            level_params: vec![],
            type_: Expr::arrow(uint.clone(), Expr::const_str("Bool")),
            value: Expr::lam(BinderInfo::Default, uint, body),
            is_reducible: true,
        })
        .expect("actual source decision kernel checks");
        let model = crate::denote_scalar_function(&module, &module.functions[0])
            .expect("actual typed model");
        let checked = check_scalar_source_equation(
            &env,
            &source,
            &model,
            Name::from_string("actualExtendedEquation").num(width),
        )
        .expect("actual decision and Nat order transport");
        export::write(
            &format!("extended_u{width}_bool"),
            &module,
            &env,
            &source,
            &checked,
        );
        let Declaration::Theorem { value, .. } = checked.declaration() else {
            panic!("theorem")
        };
        let Inst::ICmp { op, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
            panic!("comparison")
        };
        *op = ICmpOp::Ule;
        let wrong = crate::denote_scalar_function(&module, &module.functions[0])
            .expect("changed well typed comparison");
        assert!(check_scalar_source_equation_with_proof(
            &env,
            &source,
            &wrong,
            Name::from_string("wrongExtendedEquation").num(width),
            value.clone()
        )
        .is_err());
    }
}
