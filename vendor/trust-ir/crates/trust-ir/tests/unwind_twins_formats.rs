// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment D, Part 2 (wire v56, `docs/SPEC_RATIFICATIONS.md` §21): the
// FORMAT half of `Inst::InvokeIndirect` outside the binary codec (whose tag 69
// is pinned in `src/binary/unwind_twins_tests.rs`):
//
//   * text: `invoke_indirect %f(functy.K)(%a, ..) [cc=X] to bbN(..) unwind
//     bbM` — `call_indirect`'s spelling (the convention only when it is not
//     the default), then `invoke`'s successors;
//   * JSON / MessagePack: the externally tagged `InvokeIndirect` with
//     `CallIndirect`'s fields then `Invoke`'s; `calling_conv` defaults on
//     read, as `CallIndirect`'s does.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::value::FuncTyId;
use trust_ir::{
    Block, BlockId, CallingConv, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// `f(%0: ptr, %1: i64) -> i64` invokes `%0` at `functy.0 = (i64) -> i64`
/// with `%1`; the normal edge returns the result, the unwind edge enters a
/// cleanup pad that resumes.
fn module(conv: CallingConv) -> Module {
    let mut m = Module::new("unwind_twins_formats");
    let callee_sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let f_sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", f_sig, b(0));
    let mut entry = Block::new(b(0));
    entry.params.push((v(0), Ty::Ptr));
    entry.params.push((v(1), Ty::I64));
    entry.body.push(
        InstrNode::new(Inst::InvokeIndirect {
            callee: v(0),
            sig: callee_sig,
            args: vec![v(1)],
            calling_conv: conv,
            normal_dest: b(1),
            normal_args: vec![v(3)],
            unwind_dest: b(2),
        })
        .with_results(vec![v(3)]),
    );
    f.blocks.push(entry);
    // Canonically numbered (block parameters first), so the text round trip
    // is the identity on the blocks.
    let mut normal = Block::new(b(1));
    normal.params.push((v(2), Ty::I64));
    normal
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    f.blocks.push(normal);
    let mut pad = Block::new(b(2));
    pad.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![v(4), v(5)]),
    );
    pad.body.push(InstrNode::new(Inst::Resume { exn: v(4) }));
    f.blocks.push(pad);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

#[test]
fn invoke_indirect_round_trips_through_text_json_and_msgpack() {
    for (conv, spelling) in [
        (
            CallingConv::C,
            "%3 = invoke_indirect %0(functy.0)(%1) to bb1(%3) unwind bb2",
        ),
        (
            CallingConv::Fast,
            "%3 = invoke_indirect %0(functy.0)(%1) cc=fastcc to bb1(%3) unwind bb2",
        ),
    ] {
        let m = module(conv);

        let text = trust_ir::format::canonical_checked(&m).expect("text carries the twin");
        assert!(text.contains(spelling), "missing `{spelling}`: {text}");
        let parsed = trust_ir::parser::parse_module(&text).expect("the parser reads it back");
        assert_eq!(parsed.functions[0].blocks, m.functions[0].blocks, "{conv}");
        assert_eq!(trust_ir::format::canonical(&parsed), text, "idempotent");
        assert!(trust_ir::format::text_losses(&m).is_empty());

        let json = serde_json::to_string(&m).expect("json");
        let back: Module = serde_json::from_str(&json).expect("json decode");
        assert_eq!(back, m);
        let mp = rmp_serde::to_vec(&m).expect("msgpack");
        let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
        assert_eq!(back, m);
    }

    let value: serde_json::Value =
        serde_json::from_str(&serde_json::to_string(&module(CallingConv::C)).unwrap()).unwrap();
    assert_eq!(
        value["functions"][0]["blocks"][0]["body"][0]["inst"],
        serde_json::json!({ "InvokeIndirect": {
            "callee": 0, "sig": 0, "args": [1], "calling_conv": "C",
            "normal_dest": 1, "normal_args": [3], "unwind_dest": 2 } })
    );
}

#[test]
fn an_invoke_indirect_without_a_calling_conv_reads_as_the_default() {
    // `calling_conv` is `serde(default)` on the twin, as on `CallIndirect`.
    let json = serde_json::json!({ "InvokeIndirect": {
        "callee": 0, "sig": 0, "args": [1],
        "normal_dest": 1, "normal_args": [2], "unwind_dest": 2 } });
    let inst: Inst = serde_json::from_value(json).expect("decodes");
    assert_eq!(
        inst,
        Inst::InvokeIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![v(1)],
            calling_conv: CallingConv::C,
            normal_dest: b(1),
            normal_args: vec![v(2)],
            unwind_dest: b(2),
        }
    );
}

#[test]
fn the_text_parser_refuses_a_malformed_invoke_indirect() {
    let text = trust_ir::format::canonical(&module(CallingConv::C));
    for (what, broken) in [
        ("no unwind edge", text.replace(" unwind bb2", "")),
        ("no normal edge", text.replace(" to bb1(%3)", "")),
        (
            "unknown convention",
            text.replace("(%1) to bb1", "(%1) cc=nonsense to bb1"),
        ),
    ] {
        assert_ne!(broken, text, "{what}: the mutation applies");
        assert!(
            trust_ir::parser::parse_module(&broken).is_err(),
            "{what} must not parse"
        );
    }
}
