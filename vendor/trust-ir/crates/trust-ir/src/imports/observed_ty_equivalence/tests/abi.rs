// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    unused_imports,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::signature_abi::*;
fn abi_pair() -> (Module, Ty, Module, Ty) {
    let mut a = Module::new("a");
    let mut b = Module::new("b");
    a.func_types.push(abi_fixtures::fixture());
    b.func_types.push(a.func_types[0].clone());
    (a, Ty::Func(FuncTyId::new(0)), b, Ty::Func(FuncTyId::new(0)))
}
#[test]
fn function_vararg_parameters_returns_and_missing_abi_are_compared_in_full() {
    let (a, ta, b, tb) = abi_pair();
    equal(&a, &ta, &b, &tb);
    for change in 0..6 {
        let mut b = b.clone();
        let sig = &mut b.func_types[0];
        match change {
            0 => sig.is_vararg = !sig.is_vararg,
            1 => sig.params.swap(0, 1),
            2 => sig.params.push(Ty::Bool),
            3 => sig.returns[0] = Ty::I64,
            4 => sig.returns.push(Ty::Unit),
            _ => sig.abi = None,
        }
        unequal(&a, &ta, &b, &tb);
    }
    let mut a = a;
    let mut b = b;
    a.func_types[0].abi = None;
    b.func_types[0].abi = None;
    equal(&a, &ta, &b, &tb);
    b.func_types.clear();
    unequal(&a, &ta, &b, &tb);
}
#[test]
fn raw_abi_all_string_target_flags_order_and_duplicate_metadata_affect_identity() {
    let (a, ta, b, tb) = abi_pair();
    let edits: Vec<fn(&mut SignatureAbi)> = vec![
        |x| x.target.triple.push('x'),
        |x| x.target.data_layout.push('x'),
        |x| x.target.abi.push('x'),
        |x| x.target.cpu.push('x'),
        |x| x.target.features.swap(0, 1),
        |x| {
            x.target.features.pop();
        },
        |x| x.target.target_spec.push('x'),
        |x| x.target.pointer_bytes += 1,
        |x| x.target.little_endian = false,
        |x| x.frontend.name.push('x'),
        |x| x.frontend.revision.push('x'),
        |x| x.convention.push('x'),
        |x| x.source_abi.push('x'),
        |x| x.can_unwind = true,
        |x| x.variadic = true,
        |x| x.fixed_count += 1,
        |x| x.lowered_convention = crate::CallingConv::Rust,
    ];
    for edit in edits {
        let mut b = b.clone();
        edit(b.func_types[0].abi.as_mut().unwrap());
        unequal(&a, &ta, &b, &tb);
    }
}
#[test]
fn raw_abi_argument_modes_bindings_and_result_data_are_not_revalidated_or_omitted() {
    let (a, ta, b, tb) = abi_pair();
    let edits: Vec<fn(&mut SignatureAbi)> = vec![
        |x| x.arguments.swap(0, 1),
        |x| {
            x.arguments.pop();
        },
        |x| x.arguments[0].size += 1,
        |x| x.arguments[0].align += 1,
        |x| x.arguments[0].mode = AbiPassMode::Direct(abi_fixtures::scalar()),
        |x| x.arguments[0].bindings[0].source_offset += 1,
        |x| x.arguments[0].bindings[0].source_bytes += 1,
        |x| x.arguments[0].bindings[0].carrier_offset += 1,
        |x| x.arguments[0].bindings[0].carrier_bytes += 1,
        |x| x.arguments[0].bindings[0].place = AbiBindingPlace::Result(0),
        |x| x.result.size += 1,
        |x| x.result.align += 1,
        |x| x.result.mode = AbiPassMode::Direct(abi_fixtures::scalar()),
    ];
    for edit in edits {
        let mut b = b.clone();
        edit(b.func_types[0].abi.as_mut().unwrap());
        unequal(&a, &ta, &b, &tb);
    }
    let reference = baseline(&a, &ta, &b, &tb);
    assert!(reference.events.iter().any(|e| e.copy_bytes > 0));
}
