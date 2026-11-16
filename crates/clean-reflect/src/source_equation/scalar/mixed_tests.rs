// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Preserve actual mixed binders and refuse malformed typed SSA, independently
//! of the Root carrier reader and of an original-source proof's existence.
use super::*;
use trust_ir::constant::Constant;
use trust_ir::inst::{ICmpOp, Inst};
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, FuncTyId, Function, InstrNode, Module, Ty, ValueId,
};

fn fixture(width: u64, ty: Ty) -> (Module, Environment, Name) {
    let mut module = Module::new("mixed_parameter_equation");
    module.func_types.push(FuncTy {
        params: vec![ty.clone(), Ty::Bool, ty.clone(), Ty::Bool],
        returns: vec![ty.clone()],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(FuncId::new(0), "mixed", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = module.func_types[0]
        .params
        .iter()
        .enumerate()
        .map(|(i, ty)| (ValueId::new(i as u32), ty.clone()))
        .collect();
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(true),
        })
        .with_result(ValueId::new(4)),
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::Bool,
            lhs: ValueId::new(1),
            rhs: ValueId::new(4),
        })
        .with_result(ValueId::new(5)),
        InstrNode::new(Inst::Select {
            ty,
            cond: ValueId::new(5),
            then_val: ValueId::new(0),
            else_val: ValueId::new(2),
        })
        .with_result(ValueId::new(6)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(6)],
        }),
    ];
    function.blocks.push(block);
    module.try_add_function(function).expect("mixed actual IR");
    let uint = Expr::const_str(&format!("UInt{width}"));
    let sorts = [
        uint.clone(),
        Expr::const_str("Bool"),
        uint.clone(),
        Expr::const_str("Bool"),
    ];
    let mut body = Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, Expr::const_str("Bool"), uint.clone()),
            Expr::bvar(1),
            Expr::bvar(3),
            Expr::bvar(2),
        ],
    );
    let mut signature = uint;
    for sort in sorts.into_iter().rev() {
        body = Expr::lam(BinderInfo::Default, sort.clone(), body);
        signature = Expr::arrow(sort, signature);
    }
    let source = Name::from_string("mixedOriginalSource").num(width);
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: signature,
        value: body,
        is_reducible: true,
    })
    .expect("kernel checks the actual mixed source definition");
    (module, env, source)
}

#[test]
fn mixed_parameter_equation_preserves_order_and_refuses_carrier_and_ssa_mutants() {
    for (width, ty) in [(8, Ty::U8), (16, Ty::U16), (32, Ty::U32), (64, Ty::U64)] {
        let (module, env, source) = fixture(width, ty);
        let read = |m: &Module| crate::denote_scalar_function(m, &m.functions[0]);
        let model = read(&module).expect("independent mixed typed reader");
        let checked = check_scalar_source_equation(
            &env,
            &source,
            &model,
            Name::from_string("mixedSourceEquation").num(width),
        )
        .expect("universal original mixed source equation");
        export::write(
            &format!("mixed_u{width}_bool_u{width}_bool"),
            &module,
            &env,
            &source,
            &checked,
        );
        let Declaration::Theorem { value, .. } = checked.declaration() else {
            panic!("theorem")
        };

        let mut wrong = module.clone();
        let Inst::Return { values } = &mut wrong.functions[0].blocks[0].body[3].inst else {
            panic!("return")
        };
        values[0] = ValueId::new(0);
        // Remove the now-dead prefix so this remains well-formed and genuinely
        // tests the equation, rather than stopping at the SSA/live-cone guard.
        wrong.functions[0].blocks[0].body.drain(..3);
        let wrong_model = read(&wrong).expect("different valid UInt return");
        assert!(check_scalar_source_equation_with_proof(
            &env,
            &source,
            &wrong_model,
            Name::from_string("wrongMixedReturn").num(width),
            value.clone()
        )
        .is_err());

        let mut wrong = module.clone();
        wrong.func_types[0].params[3] = Ty::U8;
        wrong.functions[0].blocks[0].params[3].1 = Ty::U8;
        let wrong_model = read(&wrong).expect("changed unused argument is valid IR");
        assert!(check_scalar_source_equation_with_proof(
            &env,
            &source,
            &wrong_model,
            Name::from_string("wrongUnusedCarrier").num(width),
            value.clone()
        )
        .is_err());

        let mut wrong = module.clone();
        wrong.functions[0].blocks[0].body[0].results[0] = ValueId::new(0);
        assert!(read(&wrong).is_err(), "SSA definition shadows a parameter");
        let mut wrong = module.clone();
        let Inst::Select { cond, .. } = &mut wrong.functions[0].blocks[0].body[2].inst else {
            panic!("select")
        };
        *cond = ValueId::new(0);
        assert!(
            read(&wrong).is_err(),
            "UInt cannot serve as a Boolean condition"
        );
        let mut wrong = module.clone();
        let Inst::ICmp { rhs, .. } = &mut wrong.functions[0].blocks[0].body[1].inst else {
            panic!("comparison")
        };
        *rhs = ValueId::new(99);
        assert!(read(&wrong).is_err(), "undefined/forward operand");
        let mut wrong = module.clone();
        wrong.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            })
            .with_result(ValueId::new(99)),
        );
        assert!(read(&wrong).is_err(), "hidden dead instruction");
    }
}
