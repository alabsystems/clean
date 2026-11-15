// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Amendment D, Part 1 (`docs/SPEC_RATIFICATIONS.md` §20 rule 3, NORMATIVE):
//! a resolved `drop T, %p` IS `call glue(T)(%p)` and nothing more; an
//! unresolved drop is refused (`UnsupportedInstruction`), never stepped as a
//! no-op; `DropInvoke` runs its glue and takes the normal edge, never the
//! unwind edge (the panic=abort projection). Lean twins:
//! `ExecutableFixtures.lean`, `drop_*_stable`; the cross-engine matrix is
//! `lean_exec_differential.rs::drop_glue_execution_agrees_across_engines`.

use super::*;
use crate::inst::{AllocOrigin, BinOp, CastOp};
use crate::ty::{FieldDef, FuncTy, StructDef};
use crate::value::StructId;
use crate::{Block, Function, Global, Linkage, Module};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
fn result(inst: Inst, value: ValueId) -> InstrNode {
    InstrNode::new(inst).with_result(value)
}
fn void(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}
fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}
fn konst(ty: Ty, value: i128, out: u32) -> InstrNode {
    result(
        Inst::Const {
            ty,
            value: Constant::Int(value),
        },
        v(out),
    )
}
fn load(ty: Ty, ptr: u32, out: u32) -> InstrNode {
    result(
        Inst::Load {
            ty,
            ptr: v(ptr),
            volatile: false,
            align: None,
        },
        v(out),
    )
}
fn store(ty: Ty, ptr: u32, value: u32) -> InstrNode {
    void(Inst::Store {
        ty,
        ptr: v(ptr),
        value: v(value),
        volatile: false,
        align: None,
    })
}
fn ret(values: Vec<u32>) -> InstrNode {
    void(Inst::Return {
        values: values.into_iter().map(v).collect(),
    })
}

/// A module with `structs` owning structs `S<i>` (`{ data: ptr }`) and the
/// signature table `functy.0 = (ptr) -> ()`.
fn module(structs: u32) -> Module {
    let mut m = Module::new("drop_glue_semantics");
    for id in 0..structs {
        m.add_struct(StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: vec![FieldDef {
                name: "data".into(),
                ty: Ty::Ptr,
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
    }
    m.add_func_type(FuncTy {
        abi: None,
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");
    m
}

/// A glue `(ptr) -> ()` at `id` with `body` over its parameter `%0`
/// (`body` ends in its own terminator).
fn add_glue(m: &mut Module, id: u32, name: &str, body: Vec<InstrNode>) -> FuncId {
    let mut glue = Function::new(FuncId::new(id), name, FuncTyId::new(0), b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::Ptr));
    block.body = body;
    glue.blocks.push(block);
    m.try_add_function(glue)
        .expect("Module::try_add_function: test fixture");
    FuncId::new(id)
}

/// A glue that writes `x * 10 + digit` over the `i64` cell at its place
/// (`%0`): a run of drops leaves their ORDER in the cell.
fn digit_glue(m: &mut Module, id: u32, digit: i128) -> FuncId {
    add_glue(
        m,
        id,
        &format!("drop_digit_{digit}"),
        vec![
            load(Ty::I64, 0, 1),
            konst(Ty::I64, 10, 2),
            result(
                Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: v(1),
                    rhs: v(2),
                },
                v(3),
            ),
            konst(Ty::I64, digit, 4),
            result(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(3),
                    rhs: v(4),
                },
                v(5),
            ),
            store(Ty::I64, 0, 5),
            ret(vec![]),
        ],
    )
}

/// The entry `run() -> i64` at `id`: an `i64` cell `%0` holding `init`,
/// then `drops` over it (each `Drop` names `%0`), then `ret (load %0)`.
fn add_run(m: &mut Module, id: u32, init: i128, drops: Vec<InstrNode>) -> FuncId {
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(id), "run", sig, b(0));
    let mut block = Block::new(b(0));
    block.body.push(result(
        Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        },
        v(0),
    ));
    block.body.push(konst(Ty::I64, init, 1));
    block.body.push(store(Ty::I64, 0, 1));
    block.body.extend(drops);
    block.body.push(load(Ty::I64, 0, 2));
    block.body.push(ret(vec![2]));
    f.blocks.push(block);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    FuncId::new(id)
}

fn drop_of(ty: Ty) -> InstrNode {
    void(Inst::Drop { ty, ptr: v(0) })
}

fn returned_i64(m: &Module, entry: FuncId) -> i128 {
    let outcome = Interpreter::with_module(m)
        .execute_func(entry, [])
        .expect("the run completes");
    outcome.returns[0].as_int().expect("an i64").as_signed()
}

#[test]
fn a_resolved_drop_calls_its_glue_with_the_pointer() {
    // The glue stores 1 into the dropped cell; the caller loads 1 back.
    let mut m = module(1);
    let glue = add_glue(
        &mut m,
        0,
        "drop_s0",
        vec![konst(Ty::I64, 1, 1), store(Ty::I64, 0, 1), ret(vec![])],
    );
    let run = add_run(&mut m, 1, 7, vec![drop_of(s(0))]);
    m.set_drop_glue(s(0), glue).unwrap();
    assert_eq!(returned_i64(&m, run), 1);
}

#[test]
fn an_unresolved_drop_is_unsupported_instruction_never_a_no_op() {
    // Replaces the crystal lane's `inst_drop_is_refused_not_stepped`: the
    // dropped object is a live, initialised cell, so a no-op model would have
    // returned 7. With a module but no row, and with no module at all, the
    // drop is refused BEFORE its pointer is read.
    let mut m = module(1);
    let run = add_run(&mut m, 0, 7, vec![drop_of(s(0))]);
    let error = Interpreter::with_module(&m)
        .execute_func(run, [])
        .expect_err("an unresolved drop must be refused, not stepped");
    assert_eq!(error.code, InterpretErrorCode::UnsupportedInstruction);
    assert!(
        error.message.contains("has no drop_glue row"),
        "{}",
        error.message
    );
    assert!(
        error.message.contains("never run as a no-op"),
        "{}",
        error.message
    );
    // A row for ANOTHER type resolves nothing here.
    let mut m2 = m.clone();
    let other = add_glue(&mut m2, 1, "drop_other", vec![ret(vec![])]);
    m2.add_struct(StructDef {
        id: StructId::new(1),
        name: "S1".into(),
        fields: vec![],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    m2.set_drop_glue(s(1), other).unwrap();
    let error = Interpreter::with_module(&m2)
        .execute_func(run, [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedInstruction);
    // DropInvoke: the same refusal.
    let mut m3 = module(1);
    add_drop_invoke_run(&mut m3, 0);
    let error = Interpreter::with_module(&m3)
        .execute_func(FuncId::new(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedInstruction);
    assert!(
        error.message.starts_with("DropInvoke:"),
        "{}",
        error.message
    );
}

#[test]
fn drop_does_not_deinitialize_the_place() {
    // A glue that does nothing: the cell still holds 7 after the drop, so a
    // drop by itself neither frees nor de-initializes its place.
    let mut m = module(1);
    let glue = add_glue(&mut m, 0, "drop_s0", vec![ret(vec![])]);
    let run = add_run(&mut m, 1, 7, vec![drop_of(s(0)), drop_of(s(0))]);
    m.set_drop_glue(s(0), glue).unwrap();
    assert_eq!(returned_i64(&m, run), 7);
}

#[test]
fn drops_run_in_instruction_order() {
    let mut m = module(2);
    let one = digit_glue(&mut m, 0, 1);
    let two = digit_glue(&mut m, 1, 2);
    m.set_drop_glue(s(0), one).unwrap();
    m.set_drop_glue(s(1), two).unwrap();
    let mut forward = m.clone();
    let run = add_run(&mut forward, 2, 0, vec![drop_of(s(0)), drop_of(s(1))]);
    assert_eq!(returned_i64(&forward, run), 12);
    let mut backward = m;
    let run = add_run(&mut backward, 2, 0, vec![drop_of(s(1)), drop_of(s(0))]);
    assert_eq!(returned_i64(&backward, run), 21);
}

/// A singly linked list node `S0 = { next: ptr }` whose glue counts itself
/// in the module global `count` and then drops `*next` through the table
/// when it is non-null: recursion through the table.
fn list_module(len: u32) -> Module {
    let mut m = module(1);
    m.globals.push(Global {
        name: "count".into(),
        ty: Ty::I64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let mut glue = Function::new(FuncId::new(0), "drop_node", FuncTyId::new(0), b(0));
    let mut entry = Block::new(b(0));
    entry.params.push((v(0), Ty::Ptr));
    entry.body = vec![
        result(
            Inst::GlobalAddr {
                global: GlobalId::new(0),
            },
            v(1),
        ),
        load(Ty::I64, 1, 2),
        konst(Ty::I64, 1, 3),
        result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(2),
                rhs: v(3),
            },
            v(4),
        ),
        store(Ty::I64, 1, 4),
        load(Ty::Ptr, 0, 5),
        result(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::U64,
                operand: v(5),
            },
            v(6),
        ),
        konst(Ty::U64, 0, 7),
        result(
            Inst::ICmp {
                op: crate::inst::ICmpOp::Eq,
                ty: Ty::U64,
                lhs: v(6),
                rhs: v(7),
            },
            v(8),
        ),
        void(Inst::CondBr {
            cond: v(8),
            then_target: b(2),
            then_args: vec![],
            else_target: b(1),
            else_args: vec![],
        }),
    ];
    glue.blocks.push(entry);
    let mut recurse = Block::new(b(1));
    recurse.body = vec![
        void(Inst::Drop {
            ty: s(0),
            ptr: v(5),
        }),
        ret(vec![]),
    ];
    glue.blocks.push(recurse);
    let mut done = Block::new(b(2));
    done.body = vec![ret(vec![])];
    glue.blocks.push(done);
    m.try_add_function(glue)
        .expect("Module::try_add_function: test fixture");
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();

    // run() -> i64: `len` nodes, each a `ptr` cell holding the next node's
    // address (the last holds null), drop the head, return `count`.
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(1), "run", sig, b(0));
    let mut block = Block::new(b(0));
    let mut next_value = 100u32;
    let mut fresh = || {
        next_value += 1;
        next_value
    };
    let null = fresh();
    block.body.push(result(Inst::NullPtr, v(null)));
    let mut next = null;
    for _ in 0..len {
        let node = fresh();
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::Ptr,
                count: None,
                align: None,
            },
            v(node),
        ));
        block.body.push(store(Ty::Ptr, node, next));
        next = node;
    }
    block.body.push(void(Inst::Drop {
        ty: s(0),
        ptr: v(next),
    }));
    let addr = fresh();
    let count = fresh();
    block.body.push(result(
        Inst::GlobalAddr {
            global: GlobalId::new(0),
        },
        v(addr),
    ));
    block.body.push(load(Ty::I64, addr, count));
    block.body.push(ret(vec![count]));
    f.blocks.push(block);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

#[test]
fn a_recursive_type_drops_through_the_table_within_the_call_depth() {
    let m = list_module(3);
    assert_eq!(
        returned_i64(&m, FuncId::new(1)),
        3,
        "every node dropped once"
    );
    // Recursion through the table is bounded by the call depth exactly as
    // calls are: a list deeper than the budget is OUT OF FUEL (coverage is
    // lost, correctness never), and the same list within a larger budget
    // drops every node. (Small budgets keep the host stack shallow.)
    let deep = list_module(10);
    let budget = |depth| {
        Interpreter::with_module(&deep).with_options(InterpretOptions {
            fuel: 100_000,
            max_call_depth: depth,
            ..InterpretOptions::default()
        })
    };
    let error = budget(4)
        .execute_func(FuncId::new(1), [])
        .expect_err("past the call depth");
    assert_eq!(error.code, InterpretErrorCode::OutOfFuel, "{error:?}");
    assert!(error.message.contains("call depth"), "{}", error.message);
    let outcome = budget(16)
        .execute_func(FuncId::new(1), [])
        .expect("within the call depth");
    assert_eq!(outcome.returns[0].as_int().unwrap().as_signed(), 10);
}

#[test]
fn a_poison_drop_pointer_is_undefined_behavior_at_the_glue_boundary() {
    let mut m = module(1);
    let glue = add_glue(&mut m, 0, "drop_s0", vec![ret(vec![])]);
    m.set_drop_glue(s(0), glue).unwrap();
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(1), "run", sig, b(0));
    let mut block = Block::new(b(0));
    block.body = vec![
        result(Inst::Undef { ty: Ty::Ptr }, v(0)),
        drop_of(s(0)),
        ret(vec![]),
    ];
    f.blocks.push(block);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    let error = Interpreter::with_module(&m)
        .execute_func(FuncId::new(1), [])
        .expect_err("poison at the call boundary");
    assert_eq!(
        error.code,
        InterpretErrorCode::UndefinedBehavior,
        "{error:?}"
    );
}

#[test]
fn a_bodyless_glue_is_a_host_call_or_unsupported_call() {
    let mut m = module(1);
    m.try_add_function(Function::new(
        FuncId::new(0),
        "drop_s0_extern",
        FuncTyId::new(0),
        b(0),
    ))
    .expect("Module::try_add_function: test fixture");
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let run = add_run(&mut m, 1, 7, vec![drop_of(s(0))]);
    let error = Interpreter::with_module(&m)
        .execute_func(run, [])
        .expect_err("no host model is installed");
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall, "{error:?}");
}

/// `run() -> i64` at `id`: `%0 = alloca i64; store 5; drop_invoke S0, %0 to
/// bb1(%0) unwind bb2`; `bb1(%9: ptr)` returns `load %9`; `bb2` is a cleanup
/// pad that stores 99 and resumes (never reached under panic=abort).
fn add_drop_invoke_run(m: &mut Module, id: u32) -> FuncId {
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(id), "run_invoke", sig, b(0));
    let mut entry = Block::new(b(0));
    entry.body = vec![
        result(
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
            v(0),
        ),
        konst(Ty::I64, 5, 1),
        store(Ty::I64, 0, 1),
        void(Inst::DropInvoke {
            ty: s(0),
            ptr: v(0),
            normal_dest: b(1),
            normal_args: vec![v(0)],
            unwind_dest: b(2),
        }),
    ];
    f.blocks.push(entry);
    let mut normal = Block::new(b(1));
    normal.params.push((v(9), Ty::Ptr));
    normal.body = vec![load(Ty::I64, 9, 10), ret(vec![10])];
    f.blocks.push(normal);
    let mut pad = Block::new(b(2));
    pad.body = vec![
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![v(20), v(21)]),
        void(Inst::Resume { exn: v(20) }),
    ];
    f.blocks.push(pad);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    FuncId::new(id)
}

#[test]
fn drop_invoke_takes_the_normal_edge_and_never_the_unwind_edge() {
    let mut m = module(1);
    let glue = digit_glue(&mut m, 0, 3);
    m.set_drop_glue(s(0), glue).unwrap();
    let run = add_drop_invoke_run(&mut m, 1);
    // The glue ran (5 * 10 + 3), and the normal edge passed the place on.
    assert_eq!(returned_i64(&m, run), 53);
}

#[test]
fn a_panic_in_glue_propagates_through_drop_and_drop_invoke() {
    let failing = |m: &mut Module| {
        add_glue(
            m,
            0,
            "drop_panics",
            vec![
                result(
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(false),
                    },
                    v(1),
                ),
                void(Inst::Assert {
                    cond: v(1),
                    kind: crate::inst::AssertKind::NullPtr,
                    site: None,
                }),
                ret(vec![]),
            ],
        )
    };
    let mut m = module(1);
    let glue = failing(&mut m);
    m.set_drop_glue(s(0), glue).unwrap();
    let run = add_run(&mut m, 1, 7, vec![drop_of(s(0))]);
    let plain = Interpreter::with_module(&m)
        .execute_func(run, [])
        .unwrap_err();
    assert_eq!(plain.code, InterpretErrorCode::Panic, "{plain:?}");

    let mut m = module(1);
    let glue = failing(&mut m);
    m.set_drop_glue(s(0), glue).unwrap();
    let run = add_drop_invoke_run(&mut m, 1);
    let invoked = Interpreter::with_module(&m)
        .execute_func(run, [])
        .unwrap_err();
    // The same panic, message for message: under the projection the unwind
    // edge is never taken, so the glue's panic propagates out of the frame.
    assert_eq!(invoked.code, InterpretErrorCode::Panic);
    assert_eq!(invoked.message, plain.message);
}

#[test]
fn glue_releasing_a_clean_heap_cell_frees_it_and_a_second_drop_is_undefined_behavior() {
    // The place holds a pointer to a CleanHeap cell; the glue releases it.
    let mut m = module(1);
    let glue = add_glue(
        &mut m,
        0,
        "drop_rc",
        vec![
            load(Ty::Ptr, 0, 1),
            void(Inst::Release { ptr: v(1) }),
            ret(vec![]),
        ],
    );
    m.set_drop_glue(s(0), glue).unwrap();
    let body = |drops: usize| {
        let mut nodes = vec![
            result(
                Inst::HeapAlloc {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                    origin: AllocOrigin::CleanHeap,
                },
                v(1),
            ),
            result(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: None,
                },
                v(0),
            ),
            store(Ty::Ptr, 0, 1),
        ];
        nodes.extend((0..drops).map(|_| drop_of(s(0))));
        nodes.push(ret(vec![]));
        nodes
    };
    for (drops, ok) in [(1, true), (2, false)] {
        let mut m = m.clone();
        let sig = m
            .add_func_type(FuncTy {
                abi: None,
                params: vec![],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(1), "run", sig, b(0));
        let mut block = Block::new(b(0));
        block.body = body(drops);
        f.blocks.push(block);
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        let outcome = Interpreter::with_module(&m).execute_func(FuncId::new(1), []);
        if ok {
            outcome.expect("one drop releases the cell to count 0");
        } else {
            let error = outcome.expect_err("the second release is of a freed cell");
            assert_eq!(
                error.code,
                InterpretErrorCode::UndefinedBehavior,
                "{error:?}"
            );
        }
    }
}
