// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Amendment D, Part 2 (`docs/SPEC_RATIFICATIONS.md` §21): `Inst::InvokeIndirect`
//! (Inst tag 69), `CallIndirect`'s unwinding twin, read-gated on
//! `UNWIND_TWINS_FORMAT_VERSION`.

use super::*;
use crate::{Block, Function, InstrNode};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

fn relabel(bytes: &[u8], version: u32) -> Vec<u8> {
    let mut forged = bytes.to_vec();
    forged[8..12].copy_from_slice(&version.to_le_bytes());
    forged
}

/// `f(%0: ptr) -> i64`: an indirect call of `%0` at `functy.0 = () -> i64`,
/// either a plain `CallIndirect` then `ret`, or (`invoke`) an
/// `InvokeIndirect` whose normal edge returns the result and whose unwind
/// edge enters a cleanup pad that resumes. `conv` is the call-site
/// convention.
fn indirect_module(invoke: bool, conv: CallingConv) -> Module {
    let mut module = Module::new("unwind_twins_codec");
    let callee_sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let f_sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", f_sig, b(0));
    let mut entry = Block::new(b(0));
    entry.params.push((v(0), Ty::Ptr));
    if invoke {
        entry.body.push(
            InstrNode::new(Inst::InvokeIndirect {
                callee: v(0),
                sig: callee_sig,
                args: vec![],
                calling_conv: conv,
                normal_dest: b(1),
                normal_args: vec![v(1)],
                unwind_dest: b(2),
            })
            .with_results(vec![v(1)]),
        );
        f.blocks.push(entry);
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
            .with_results(vec![v(3), v(4)]),
        );
        pad.body.push(InstrNode::new(Inst::Resume { exn: v(3) }));
        f.blocks.push(pad);
    } else {
        entry.body.push(
            InstrNode::new(Inst::CallIndirect {
                callee: v(0),
                sig: callee_sig,
                args: vec![],
                calling_conv: conv,
            })
            .with_results(vec![v(1)]),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        f.blocks.push(entry);
    }
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

fn the_invoke(module: &Module) -> &Inst {
    &module.functions[0].blocks[0].body[0].inst
}

#[test]
fn invoke_indirect_round_trips_at_its_version() {
    for conv in [CallingConv::C, CallingConv::Fast, CallingConv::SysV64] {
        let module = indirect_module(true, conv);
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        let expected = if conv.is_abi_surface() {
            UNWIND_TWINS_FORMAT_VERSION.max(ABI_SURFACE_FORMAT_VERSION)
        } else {
            UNWIND_TWINS_FORMAT_VERSION
        };
        assert_eq!(header_version(&bytes), expected, "{conv}");
        assert_eq!(deserialize_module(&bytes).expect("lossless twin"), module);
    }
}

/// The exact tag-69 spelling: `CallIndirect`'s tag-19 payload, then
/// `Invoke`'s successors. Pinned byte for byte so a reordering is a failure,
/// not a silent re-encoding.
#[test]
fn unwind_twin_wire_spelling_is_pinned() {
    let module = indirect_module(true, CallingConv::C);
    let encoded = SealedStringPool::by_replay(|pool, bytes| {
        write_inst(bytes, pool, None, the_invoke(&module));
    });
    // tag 69 | callee %0 | functy.0 | 0 args | calling conv C (0) |
    // normal bb1 | 1 normal arg %1 | unwind bb2
    assert_eq!(encoded, vec![69, 0, 0, 0, 0, 1, 1, 1, 2]);
    // CallIndirect's own payload is exactly the prefix after the tag.
    let plain = indirect_module(false, CallingConv::C);
    let plain_encoded = SealedStringPool::by_replay(|pool, bytes| {
        write_inst(bytes, pool, None, the_invoke(&plain));
    });
    assert_eq!(plain_encoded[0], 19);
    assert_eq!(&plain_encoded[1..], &encoded[1..5]);
}

#[test]
fn unwind_twin_tags_are_read_gated() {
    let bytes = serialize_module(&indirect_module(true, CallingConv::C))
        .expect("serialize_module: test fixture");
    for version in MIN_READ_VERSION..UNWIND_TWINS_FORMAT_VERSION {
        // v26..=v28 are refused before any tag is read (ambiguous lineage).
        if AMBIGUOUS_LINEAGE_VERSIONS.contains(&version) {
            continue;
        }
        assert_eq!(
            deserialize_module(&relabel(&bytes, version)),
            Err(BinaryError::InvalidTag(69)),
            "a v{version} label carrying Inst tag 69 is refused"
        );
    }
}

#[test]
fn a_module_without_invoke_indirect_keeps_its_bytes_and_digest() {
    // A plain `CallIndirect` module is written exactly as before: its version
    // is untouched by v56.
    let plain = indirect_module(false, CallingConv::C);
    let bytes = serialize_module(&plain).expect("serialize_module: test fixture");
    assert!(header_version(&bytes) < UNWIND_TWINS_FORMAT_VERSION);
    assert_eq!(header_version(&bytes), BASE_FORMAT_VERSION);
    assert_eq!(deserialize_module(&bytes).unwrap(), plain);
    assert_eq!(
        plain.stable_digest(),
        deserialize_module(&bytes).unwrap().stable_digest()
    );
}

#[test]
fn the_digests_separate_invoke_indirect_from_call_indirect() {
    let plain = indirect_module(false, CallingConv::C);
    let twin = indirect_module(true, CallingConv::C);
    assert_ne!(plain.stable_digest(), twin.stable_digest());
    assert_ne!(
        plain.executable_content_digest_v1(),
        twin.executable_content_digest_v1()
    );
    let back =
        deserialize_module(&serialize_module(&twin).expect("serialize_module: test fixture"))
            .unwrap();
    assert_eq!(twin.stable_digest(), back.stable_digest());
    assert_eq!(
        twin.executable_content_digest_v1(),
        back.executable_content_digest_v1()
    );
}

#[test]
fn v38_projections_refuse_invoke_indirect() {
    let twin = indirect_module(true, CallingConv::C);
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        let options = ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(&twin, options).err(),
            Some(BinaryProjectionError::UnwindTwinsRequiresV56)
        );
        assert!(
            ProjectedModuleBinaryPlan::try_new(&indirect_module(false, CallingConv::C), options)
                .is_ok()
        );
    }
}
