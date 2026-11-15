// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Plan<'a> {
    Empty,
    One(ValueId),
    Two(ValueId, ValueId),
    Three(ValueId, ValueId, ValueId),
    Optional(&'a Option<ValueId>),
    Lists {
        prefix: Option<ValueId>,
        first: &'a [ValueId],
        second: &'a [ValueId],
    },
    Branch {
        condition: ValueId,
        first: &'a [ValueId],
        second: &'a [ValueId],
    },
    Switch {
        selector: ValueId,
        default: &'a [ValueId],
        cases: &'a [SwitchCase],
    },
    Assert {
        condition: ValueId,
        kind: &'a AssertKind,
        site: Option<&'a PanicSite>,
        normal: &'a [ValueId],
    },
}

// This is a fixed-header projection, not an ordinary visitor or prewalk.
// Exhaustive: a future instruction cannot silently become an operand-free op.
pub(super) fn for_instruction(instruction: &Inst) -> Plan<'_> {
    match instruction {
        Inst::Drop { ptr, .. } => Plan::One(*ptr),
        Inst::DropInvoke {
            ptr, normal_args, ..
        } => Plan::Lists {
            prefix: Some(*ptr),
            first: normal_args,
            second: &[],
        },
        Inst::BinOp { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. } => Plan::Two(*lhs, *rhs),
        Inst::SeqMapAddK { seq, .. } | Inst::SeqMapNot { seq, .. } | Inst::SeqMap { seq, .. } => {
            Plan::One(*seq)
        }
        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } | Inst::Copy { operand, .. } => {
            Plan::One(*operand)
        }
        Inst::Load { ptr, .. }
        | Inst::PtrData { ptr, .. }
        | Inst::PtrMetadata { ptr, .. }
        | Inst::AtomicLoad { ptr, .. }
        | Inst::Borrow { ptr }
        | Inst::BorrowMut { ptr }
        | Inst::Retain { ptr }
        | Inst::Release { ptr }
        | Inst::IsUnique { ptr }
        | Inst::Dealloc { ptr } => Plan::One(*ptr),
        Inst::Store { ptr, value, .. }
        | Inst::AtomicStore { ptr, value, .. }
        | Inst::AtomicRMW { ptr, value, .. } => Plan::Two(*ptr, *value),
        Inst::MemCopy {
            dst, src, bytes, ..
        } => Plan::Three(*dst, *src, *bytes),
        Inst::MemSet { dst, byte, bytes } => Plan::Three(*dst, *byte, *bytes),
        Inst::Alloca { count, .. } | Inst::HeapAlloc { count, .. } => Plan::Optional(count),
        Inst::GEP { base, indices, .. } => Plan::Lists {
            prefix: Some(*base),
            first: indices,
            second: &[],
        },
        Inst::PtrFromParts { data, metadata, .. } => Plan::Two(*data, *metadata),
        Inst::CmpXchg {
            ptr,
            expected,
            desired,
            ..
        } => Plan::Three(*ptr, *expected, *desired),
        Inst::Br { args, .. } | Inst::Call { args, .. } | Inst::CallCannotUnwind { args, .. } => {
            Plan::Lists {
                prefix: None,
                first: args,
                second: &[],
            }
        }
        Inst::CondBr {
            cond,
            then_args,
            else_args,
            ..
        } => Plan::Branch {
            condition: *cond,
            first: then_args,
            second: else_args,
        },
        Inst::Switch {
            value,
            default_args,
            cases,
            ..
        } => Plan::Switch {
            selector: *value,
            default: default_args,
            cases,
        },
        Inst::CallIndirect { callee, args, .. }
        | Inst::CallIndirectCannotUnwind { callee, args, .. } => Plan::Lists {
            prefix: Some(*callee),
            first: args,
            second: &[],
        },
        Inst::Return { values } => Plan::Lists {
            prefix: None,
            first: values,
            second: &[],
        },
        Inst::MakeAggregate { fields, .. }
        | Inst::MakeClosure {
            captures: fields, ..
        } => Plan::Lists {
            prefix: None,
            first: fields,
            second: &[],
        },
        Inst::ArraySplat { value, .. } => Plan::One(*value),
        Inst::TensorContract { lhs, rhs, .. } => Plan::Two(*lhs, *rhs),
        Inst::TensorMap { args, .. } => Plan::Lists {
            prefix: None,
            first: args,
            second: &[],
        },
        Inst::TensorReduce { src, .. } => Plan::One(*src),
        // The source, the parameters in order, then the fill.
        Inst::TensorView {
            src, params, fill, ..
        } => Plan::Lists {
            prefix: Some(*src),
            first: params,
            second: fill.as_slice(),
        },
        // The data, then the coordinate tensors in axis order.
        Inst::TensorGather { data, coords, .. } => Plan::Lists {
            prefix: Some(*data),
            first: coords,
            second: &[],
        },
        // The initial tensor, the source, then the coordinate tensors.
        Inst::TensorScatter {
            init, src, coords, ..
        } => Plan::Lists {
            prefix: Some(*init),
            first: core::slice::from_ref(src),
            second: coords,
        },
        Inst::ExtractField { aggregate, .. } => Plan::One(*aggregate),
        Inst::InsertField {
            aggregate, value, ..
        } => Plan::Two(*aggregate, *value),
        Inst::ExtractElement { array, index, .. } => Plan::Two(*array, *index),
        Inst::InsertElement {
            array,
            index,
            value,
            ..
        } => Plan::Three(*array, *index, *value),
        Inst::Assume { cond } => Plan::One(*cond),
        Inst::Assert { cond, kind, site } => Plan::Assert {
            condition: *cond,
            kind,
            site: site.as_ref(),
            normal: &[],
        },
        Inst::AssertInvoke {
            cond,
            kind,
            site,
            normal_args,
            ..
        } => Plan::Assert {
            condition: *cond,
            kind,
            site: Some(site),
            normal: normal_args,
        },
        Inst::Select {
            cond,
            then_val,
            else_val,
            ..
        } => Plan::Three(*cond, *then_val, *else_val),
        Inst::EndBorrow { borrow_ptr } => Plan::One(*borrow_ptr),
        Inst::BindSlot { frame, value, .. } | Inst::CoroSuspend { frame, value, .. } => {
            Plan::Two(*frame, *value)
        }
        Inst::LoadSlot { frame, .. } | Inst::CloseFrame { frame } => Plan::One(*frame),
        Inst::Invoke {
            args, normal_args, ..
        } => Plan::Lists {
            prefix: None,
            first: args,
            second: normal_args,
        },
        Inst::InvokeIndirect {
            callee,
            args,
            normal_args,
            ..
        } => Plan::Lists {
            prefix: Some(*callee),
            first: args,
            second: normal_args,
        },
        Inst::Resume { exn } => Plan::One(*exn),
        Inst::DialectOp(operation) => Plan::Lists {
            prefix: None,
            first: &operation.operands,
            second: &[],
        },
        Inst::Fence { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Unreachable
        | Inst::OpenFrame { .. }
        | Inst::LandingPad { .. } => Plan::Empty,
    }
}
