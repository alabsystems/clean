// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// G18-2: `Ty::Closure` is no longer INTRODUCTION-ONLY.
//
// Before this, a closure value could be built (`Const` + per-capture
// `InsertField`) and projected (`ExtractField` reads a capture, in capture
// order) but never APPLIED: `Inst::CallIndirect` required a `Ty::Func` callee,
// and `ExtractField` deliberately does not expose the closure's `func` lane, so
// the code pointer inside a closure value was unreachable BY CONSTRUCTION. A
// first-class function type whose values can be introduced and destructured but
// never eliminated is not a function type.
//
// The rule added:
//
//   * a `CallIndirect` whose callee has type `Ty::Closure(c)` declares
//     `sig == closure_types[c].func` — the APPARENT signature, the one a caller
//     sees. `args` is checked against it verbatim, by the same rule that
//     already governs a `Ty::Func` edge.
//   * the captured environment is supplied by the ABI as LEADING arguments,
//     spread in capture order, so the target function's physical signature must
//     be `captures ++ apparent params -> apparent returns`.
//
// The `Ty::Func` rule is untouched: this file's last two tests pin that a
// function-pointer edge still rejects a mismatched signature and still rejects
// a non-function callee, i.e. nothing was relaxed to make room for closures.

#![allow(clippy::needless_range_loop)]

use trust_ir::inst::{BinOp, Inst};
use trust_ir::interpret::Interpreter;
use trust_ir::node::InstrNode;
use trust_ir::value::{BlockId, ClosureTyId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, ClosureTy, Constant, FuncTy, Function, Module, Ty};

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
fn b(i: u32) -> BlockId {
    BlockId::new(i)
}

/// Build `add_env(env: I32, x: I32) -> I32 { env + x }` plus a host that
/// materializes `closure { func: add_env, captures: [env_value] }` and applies
/// it to `arg_value`.
///
/// `target_params` lets a caller deliberately mis-declare the target's physical
/// signature so the fail-closed path can be exercised; `captures` likewise.
struct Fixture {
    module: Module,
    apparent: FuncTyId,
}

fn build(target_params: Vec<Ty>, captures: Vec<Ty>, apparent_params: Vec<Ty>) -> Fixture {
    let mut module = Module::new("closure-apply");

    // The closure's APPARENT signature: what a caller sees.
    let apparent = module
        .add_func_type(FuncTy {
            params: apparent_params,
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    // The TARGET's physical signature.
    let target_ty = module
        .add_func_type(FuncTy {
            params: target_params,
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let host_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let _closure = module
        .add_closure_type(ClosureTy {
            func: apparent,
            captures,
        })
        .expect("Module::add_closure_type: test fixture");

    // fn host() -> i32
    let mut host = Function::new(FuncId::new(0), "host", host_ty, b(0));
    let mut hb = Block::new(b(0));
    hb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Closure(_closure),
            value: Constant::Closure {
                func: FuncId::new(1),
                captures: vec![Constant::Int(7)],
            },
        })
        .with_result(v(0)),
    );
    hb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(35),
        })
        .with_result(v(1)),
    );
    hb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: apparent,
            args: vec![v(1)],
            calling_conv: trust_ir::CallingConv::Rust,
        })
        .with_result(v(2)),
    );
    hb.body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    host.blocks.push(hb);
    module
        .try_add_function(host)
        .expect("Module::try_add_function: test fixture");

    // fn add_env(env, x) -> i32 { env + x }
    let mut target = Function::new(FuncId::new(1), "add_env", target_ty, b(0));
    let mut tb = Block::new(b(0));
    let param_count = module.func_types[target_ty.as_usize()].params.len();
    for i in 0..param_count {
        tb.params.push((
            v(i as u32),
            module.func_types[target_ty.as_usize()].params[i].clone(),
        ));
    }
    // Sum every parameter (1 or 2 of them) so the body is total for both shapes.
    let mut acc = v(0);
    for i in 1..param_count {
        let out = v(100 + i as u32);
        tb.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: acc,
                rhs: v(i as u32),
            })
            .with_result(out),
        );
        acc = out;
    }
    tb.body
        .push(InstrNode::new(Inst::Return { values: vec![acc] }));
    target.blocks.push(tb);
    module
        .try_add_function(target)
        .expect("Module::try_add_function: test fixture");

    Fixture { module, apparent }
}

/// The well-formed shape: captures `[I32]`, apparent `(I32) -> I32`, target
/// `(I32, I32) -> I32`. The capture (7) is the LEADING argument, the call
/// argument (35) follows.
#[test]
fn closure_is_applied_with_captures_as_leading_arguments() {
    let f = build(vec![Ty::I32, Ty::I32], vec![Ty::I32], vec![Ty::I32]);
    let out = Interpreter::with_module(&f.module)
        .execute_func(FuncId::new(0), [])
        .expect("a well-formed closure application executes");
    assert_eq!(out.returns.len(), 1);
    assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 42);
}

/// The zero-capture closure degenerates to the apparent signature exactly —
/// `captures ++ params == params` — so it must still apply.
#[test]
fn zero_capture_closure_applies_with_the_apparent_signature() {
    let mut module = Module::new("bare-closure");
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let host_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let closure = module
        .add_closure_type(ClosureTy::bare(apparent))
        .expect("Module::add_closure_type: test fixture");

    let mut host = Function::new(FuncId::new(0), "host", host_ty, b(0));
    let mut hb = Block::new(b(0));
    hb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Closure(closure),
            value: Constant::Closure {
                func: FuncId::new(1),
                captures: vec![],
            },
        })
        .with_result(v(0)),
    );
    hb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(42),
        })
        .with_result(v(1)),
    );
    hb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: apparent,
            args: vec![v(1)],
            calling_conv: trust_ir::CallingConv::Rust,
        })
        .with_result(v(2)),
    );
    hb.body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    host.blocks.push(hb);
    module
        .try_add_function(host)
        .expect("Module::try_add_function: test fixture");

    let mut id = Function::new(FuncId::new(1), "id", apparent, b(0));
    let mut ib = Block::new(b(0));
    ib.params.push((v(0), Ty::I32));
    ib.body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    id.blocks.push(ib);
    module
        .try_add_function(id)
        .expect("Module::try_add_function: test fixture");

    let out = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("a zero-capture closure applies");
    assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 42);
}

/// FAIL CLOSED: the target does not carry the capture in its leading position.
/// Under a "captures are dropped" reading this would silently call
/// `add_env(35)`; the interpreter must refuse instead.
#[test]
fn closure_target_missing_the_environment_parameter_is_refused() {
    let f = build(vec![Ty::I32], vec![Ty::I32], vec![Ty::I32]);
    let err = Interpreter::with_module(&f.module)
        .execute_func(FuncId::new(0), [])
        .expect_err("a target lacking the environment parameter must be refused");
    let msg = format!("{err}");
    assert!(
        msg.contains("closure target") && msg.contains("closure ABI") || msg.contains("requires"),
        "unexpected diagnostic: {msg}"
    );
}

/// FAIL CLOSED: the capture type disagrees with the target's leading parameter.
#[test]
fn closure_target_with_the_wrong_environment_type_is_refused() {
    let f = build(vec![Ty::I64, Ty::I32], vec![Ty::I32], vec![Ty::I32]);
    let err = Interpreter::with_module(&f.module)
        .execute_func(FuncId::new(0), [])
        .expect_err("a target whose env parameter has the wrong type must be refused");
    assert!(format!("{err}").contains("requires"), "{err}");
}

/// FAIL CLOSED: the edge declares a signature that is not the closure's
/// apparent one. `functy` ids are compared by identity — the same strictness
/// the `Ty::Func` edge applies — so a structurally-identical-but-distinct
/// signature is refused rather than guessed at.
#[test]
fn closure_edge_declaring_a_foreign_signature_is_refused() {
    let mut f = build(vec![Ty::I32, Ty::I32], vec![Ty::I32], vec![Ty::I32]);
    // A second, structurally identical apparent signature.
    let twin = f
        .module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert_ne!(twin, f.apparent);
    for block in &mut f.module.functions[0].blocks {
        for node in &mut block.body {
            if let Inst::CallIndirect { sig, .. } = &mut node.inst {
                *sig = twin;
            }
        }
    }
    let err = Interpreter::with_module(&f.module)
        .execute_func(FuncId::new(0), [])
        .expect_err("a foreign declared signature must be refused");
    assert!(
        format!("{err}").contains("apparent signature"),
        "unexpected diagnostic: {err}"
    );
}

/// FAIL CLOSED: a closure type id that names no entry in the module's table.
#[test]
fn closure_edge_over_an_undefined_closure_type_is_refused() {
    let f = build(vec![Ty::I32, Ty::I32], vec![Ty::I32], vec![Ty::I32]);
    let mut module = f.module;
    let bogus = ClosureTyId::new(u32::try_from(module.closure_types.len()).unwrap() + 3);
    for block in &mut module.functions[0].blocks {
        for node in &mut block.body {
            if let Inst::Const { ty, .. } = &mut node.inst
                && matches!(ty, Ty::Closure(_))
            {
                *ty = Ty::Closure(bogus);
            }
        }
    }
    let err = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect_err("an undefined closure type must be refused");
    assert!(format!("{err}").contains("closure type"), "{err}");
}

/// The `Ty::Func` edge is UNCHANGED: a function-pointer callee whose value
/// signature differs from the declared one is still refused.
#[test]
fn func_pointer_edge_still_refuses_a_signature_mismatch() {
    let mut module = Module::new("fnptr-unchanged");
    let sig_a = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let sig_b = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let host_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut host = Function::new(FuncId::new(0), "host", host_ty, b(0));
    let mut hb = Block::new(b(0));
    hb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Func(sig_a),
            value: Constant::FnDef(FuncId::new(1)),
        })
        .with_result(v(0)),
    );
    hb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(1)),
    );
    hb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            // Declared as the TWIN signature, not the value's own.
            sig: sig_b,
            args: vec![v(1)],
            calling_conv: trust_ir::CallingConv::Rust,
        })
        .with_result(v(2)),
    );
    hb.body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    host.blocks.push(hb);
    module
        .try_add_function(host)
        .expect("Module::try_add_function: test fixture");

    let mut id = Function::new(FuncId::new(1), "id", sig_a, b(0));
    let mut ib = Block::new(b(0));
    ib.params.push((v(0), Ty::I32));
    ib.body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    id.blocks.push(ib);
    module
        .try_add_function(id)
        .expect("Module::try_add_function: test fixture");

    let err = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect_err("the Ty::Func signature-identity rule is unchanged");
    assert!(
        format!("{err}").contains("callee value has signature"),
        "{err}"
    );
}

/// The `Ty::Func` edge is UNCHANGED: a callee that is neither a function
/// pointer nor a closure is still refused as a non-function type.
#[test]
fn func_pointer_edge_still_refuses_a_non_function_callee() {
    let mut module = Module::new("nonfn-unchanged");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let host_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut host = Function::new(FuncId::new(0), "host", host_ty, b(0));
    let mut hb = Block::new(b(0));
    hb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(9),
        })
        .with_result(v(0)),
    );
    hb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig,
            args: vec![],
            calling_conv: trust_ir::CallingConv::Rust,
        })
        .with_result(v(1)),
    );
    hb.body
        .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
    host.blocks.push(hb);
    module
        .try_add_function(host)
        .expect("Module::try_add_function: test fixture");

    let err = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect_err("a non-function callee is still refused");
    assert!(format!("{err}").contains("non-function type"), "{err}");
}
