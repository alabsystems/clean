// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_existing_plan_shape_matches_actual_original_first_match_visitor() {
    for inst in all() {
        for needle in [1, 2, 3, 4, 5, 90, 99, u32::MAX] {
            run(&inst, v(needle));
        }
    }
}
#[test]
fn first_matching_prefix_does_not_walk_arbitrary_argument_tail() {
    let a = Inst::CallIndirect {
        callee: v(1),
        sig: FuncTyId::new(99),
        args: vec![],
        calling_conv: crate::CallingConv::C,
    };
    let mut b = a.clone();
    if let Inst::CallIndirect { args, .. } = &mut b {
        args.extend(core::iter::repeat_n(v(2), 100000));
    }
    let (_, a) = run(&a, v(1));
    let (_, b) = run(&b, v(1));
    assert_eq!(a.events, b.events);
}
#[test]
fn matching_branch_condition_does_not_visit_any_branch_argument_payload() {
    let a = Inst::CondBr {
        cond: v(1),
        then_target: BlockId::new(10),
        then_args: vec![],
        else_target: BlockId::new(11),
        else_args: vec![],
    };
    let mut b = a.clone();
    if let Inst::CondBr {
        then_args,
        else_args,
        ..
    } = &mut b
    {
        then_args.extend(core::iter::repeat_n(v(2), 10000));
        else_args.extend(core::iter::repeat_n(v(3), 10000));
    }
    assert_eq!(run(&a, v(1)).1.events, run(&b, v(1)).1.events);
}
#[test]
fn switch_selector_stops_before_default_or_case_payloads() {
    assert_eq!(
        run(&switch(false, 0), v(1)).1.events,
        run(&switch(false, 10000), v(1)).1.events
    );
}
#[test]
fn absent_needle_visits_actual_empty_switch_cases_instead_of_skipping_their_work() {
    let (_, small) = run(&switch(true, 0), v(99));
    let (_, large) = run(&switch(true, 100), v(99));
    assert!(large.events.len() > small.events.len());
    assert!(large.work > small.work);
}
#[test]
fn assertion_condition_kind_location_then_normal_operand_order_is_preserved() {
    let mut inst = invocations().pop().unwrap();
    assert!(run(&inst, v(4)).0);
    let baseline = run(&inst, v(1)).1;
    if let Inst::AssertInvoke {
        normal_args,
        kind,
        site,
        ..
    } = &mut inst
    {
        *kind = AssertKind::MisalignedPtr {
            required: v(8),
            found: v(9),
        };
        site.location = PanicLocation::Value(v(10));
        normal_args.extend(core::iter::repeat_n(v(11), 10000));
    }
    assert_eq!(baseline.events, run(&inst, v(1)).1.events);
    for needle in [8, 9, 10, 11, 99] {
        run(&inst, v(needle));
    }
}
#[test]
fn constants_definition_ids_and_global_panic_location_are_not_ssa_operands() {
    let inst = Inst::Const {
        ty: Ty::Func(FuncTyId::new(99)),
        value: Constant::FnDef(FuncId::new(99)),
    };
    assert!(!run(&inst, v(99)).0);
    let inst = Inst::Assert {
        cond: v(1),
        kind: AssertKind::NullPtr,
        site: Some(PanicSite {
            entry: FuncId::new(99),
            location: PanicLocation::Global(GlobalId::new(99)),
        }),
    };
    assert!(!run(&inst, v(99)).0);
}
#[test]
fn duplicates_and_last_matching_operand_keep_original_membership_without_normalization() {
    let inst = Inst::Return {
        values: ids(&[1, 1, 2, 2, 3]),
    };
    assert!(run(&inst, v(3)).0);
    assert!(!run(&inst, v(4)).0);
    let first = Inst::Return { values: ids(&[1]) };
    assert_eq!(run(&first, v(1)).1.events, run(&inst, v(1)).1.events);
}
