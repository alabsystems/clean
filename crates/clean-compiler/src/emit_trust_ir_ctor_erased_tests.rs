// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An erased constructor field keeps its object slot (LX0 battery,
//! `layout_punit_*`).
//!
//! `emit_c` passes every constructor argument to `clean_alloc_ctor`, an erased
//! one as `clean_box(0)`, and `CtorInfo::num_objects` counts that slot. The
//! trust-ir emitter used to drop erased arguments, so `(PUnit.unit, 5)` was
//! allocated with two object slots and one operand. The runtime then read an
//! uninitialized pointer for the missing field: the battery program printed a
//! garbage second component at exit 0, and `some PUnit.unit` crashed.

use super::*;
use crate::ir::{CtorInfo, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
use trust_ir::inst::Inst;

fn extern_config() -> TrustIrConfig {
    TrustIrConfig {
        module_name: "ctor_erased_test".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

/// `Prod.mk PUnit.unit x`: two object fields, the first erased.
fn punit_pair_ctor() -> CtorInfo {
    CtorInfo {
        name: Name::from_string("Prod.mk"),
        tag: 0,
        num_scalars: 0,
        num_objects: 2,
        field_types: vec![IRType::Erased, IRType::Object],
    }
}

/// Operand count of the one call `function` makes to the runtime symbol `sym`.
fn runtime_call_arity(module: &Module, function: &str, sym: &str) -> usize {
    let callee = module
        .functions
        .iter()
        .find(|f| f.name == sym)
        .unwrap_or_else(|| panic!("module declares `{sym}`"))
        .id;
    module
        .functions
        .iter()
        .find(|f| f.name == function)
        .unwrap_or_else(|| panic!("module emits `{function}`"))
        .instructions()
        .find_map(|n| match &n.inst {
            Inst::Call { callee: c, args } if *c == callee => Some(args.len()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("`{function}` calls `{sym}`"))
}

#[test]
fn test_emit_trust_ir_ctor_erased_field_keeps_its_object_slot() {
    let decl = IRDecl {
        name: Name::from_string("pair"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: punit_pair_ctor(),
                args: vec![IRArg::Erased, IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let module = emit_trust_ir_with_config(&[decl], &extern_config())
        .expect("a constructor with an erased field lowers in ExternCalls mode");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validation errors: {errors:?}");
    // tag, num_objs, scalar_sz, then BOTH fields: the erased one boxed.
    assert_eq!(
        runtime_call_arity(&module, "pair", "clean_alloc_ctor"),
        3 + 2
    );
}

#[test]
fn test_emit_trust_ir_reuse_erased_field_keeps_its_object_slot() {
    let decl = IRDecl {
        name: Name::from_string("repair"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::Reuse {
                var: VarId(0),
                ctor: punit_pair_ctor(),
                args: vec![IRArg::Erased, IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    };
    let module = emit_trust_ir_with_config(&[decl], &extern_config())
        .expect("a reuse with an erased field lowers in ExternCalls mode");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validation errors: {errors:?}");
    // slot, tag, num_objs, scalar_sz, then both fields.
    assert_eq!(runtime_call_arity(&module, "repair", "clean_reuse"), 4 + 2);
}

/// Negative control for the guard that would have refused the old lowering:
/// fewer field operands than object slots is refused by name, never emitted.
#[test]
fn test_emit_trust_ir_ctor_short_operands_refused() {
    let err = ensure_object_operands("obj.ctor", 1, &punit_pair_ctor())
        .expect_err("one operand for two object slots must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("Prod.mk") && msg.contains("uninitialized read"),
        "the refusal names the constructor and the hazard: {msg}"
    );
    ensure_object_operands("obj.ctor", 2, &punit_pair_ctor())
        .expect("a full operand list is admitted");
}
