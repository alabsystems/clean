// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual original first-match visitor, not full collection.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
mod custody;
mod parity;
mod stops;
fn run(inst: &Inst, needle: ValueId) -> (bool, Observer) {
    let expected = inst
        .try_visit_value_operands(|value| {
            if value == needle {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        })
        .is_break();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual = inst
        .uses_value_operand_observed(needle, &mut s, site())
        .unwrap();
    assert_eq!(actual, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<bool>()
        }
    );
    (actual, o)
}
fn all() -> Vec<Inst> {
    let mut nodes = invocations();
    nodes.extend([
        Inst::Const {
            ty: Ty::U64,
            value: Constant::FnDef(FuncId::new(99)),
        },
        Inst::Borrow { ptr: v(1) },
        Inst::Store {
            ty: Ty::U8,
            ptr: v(1),
            value: v(2),
            volatile: false,
            align: None,
        },
        Inst::Select {
            ty: Ty::U8,
            cond: v(1),
            then_val: v(2),
            else_val: v(3),
        },
        Inst::Alloca {
            ty: Ty::U8,
            count: Some(v(1)),
            align: None,
        },
        Inst::Alloca {
            ty: Ty::U8,
            count: None,
            align: None,
        },
        Inst::CondBr {
            cond: v(1),
            then_target: BlockId::new(10),
            then_args: ids(&[2, 3]),
            else_target: BlockId::new(11),
            else_args: ids(&[4, 1]),
        },
        switch(false, 2),
        switch(true, 2),
    ]);
    nodes
}
