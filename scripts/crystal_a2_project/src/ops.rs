// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The six operator alphabets, `trust_ir` spelling to core spelling.
//!
//! Kept 1:1 with `clean-verify`'s `ir_mint::shape` tables: a name that appears
//! here and not there (or the reverse) is a hole in the pipeline, and the
//! `shape_table_is_a_bijection_in_both_directions` test on the Clean side is
//! what makes such a hole fail rather than silently mint the wrong operator.
//! Anything without a Clean image refuses; nothing is approximated.

use super::R;

pub(super) fn binop(op: trust_ir::inst::BinOp) -> R<&'static str> {
    use trust_ir::inst::BinOp as B;
    Ok(match op {
        B::Add => "add",
        B::Sub => "sub",
        B::Mul => "mul",
        B::UDiv => "udiv",
        B::SDiv => "sdiv",
        B::URem => "urem",
        B::SRem => "srem",
        B::FAdd => "fadd",
        B::FSub => "fsub",
        B::FMul => "fmul",
        B::FDiv => "fdiv",
        B::FRem => "frem",
        B::FMin => "fmin",
        B::FMax => "fmax",
        B::And => "and",
        B::Or => "or",
        B::Xor => "xor",
        B::Shl => "shl",
        B::LShr => "lshr",
        B::AShr => "ashr",
        other => return Err(format!("no IRBinOp image for {other:?}")),
    })
}

pub(super) fn unop(op: trust_ir::inst::UnOp) -> R<&'static str> {
    use trust_ir::inst::UnOp as U;
    Ok(match op {
        U::Neg => "neg",
        U::FNeg => "fneg",
        U::FAbs => "fabs",
        U::FSqrt => "fsqrt",
        U::FFloor => "ffloor",
        U::FCeil => "fceil",
        U::FTrunc => "ftrunc",
        U::Not => "not",
        U::CtPop => "ctpop",
    })
}

pub(super) fn ovop(op: trust_ir::inst::OverflowOp) -> &'static str {
    use trust_ir::inst::OverflowOp as O;
    match op {
        O::AddOverflow => "addoverflow",
        O::SubOverflow => "suboverflow",
        O::MulOverflow => "muloverflow",
    }
}

pub(super) fn icmp(op: trust_ir::inst::ICmpOp) -> &'static str {
    use trust_ir::inst::ICmpOp as I;
    match op {
        I::Eq => "eq",
        I::Ne => "ne",
        I::Ult => "ult",
        I::Ule => "ule",
        I::Ugt => "ugt",
        I::Uge => "uge",
        I::Slt => "slt",
        I::Sle => "sle",
        I::Sgt => "sgt",
        I::Sge => "sge",
    }
}

pub(super) fn fcmp(op: trust_ir::inst::FCmpOp) -> &'static str {
    use trust_ir::inst::FCmpOp as F;
    match op {
        F::OEq => "oeq",
        F::ONe => "one",
        F::OLt => "olt",
        F::OLe => "ole",
        F::OGt => "ogt",
        F::OGe => "oge",
        F::UEq => "ueq",
        F::UNe => "une",
        F::ULt => "ult",
        F::ULe => "ule",
        F::UGt => "ugt",
        F::UGe => "uge",
    }
}

pub(super) fn cast(op: trust_ir::inst::CastOp) -> R<&'static str> {
    use trust_ir::inst::CastOp as C;
    Ok(match op {
        C::Trunc => "trunc",
        C::ZExt => "zext",
        C::SExt => "sext",
        C::FPTrunc => "fptrunc",
        C::FPExt => "fpext",
        C::FPToUI => "fptoui",
        C::FPToSI => "fptosi",
        C::UIToFP => "uitofp",
        C::SIToFP => "sitofp",
        C::PtrToInt => "ptrtoint",
        C::IntToPtr => "inttoptr",
        C::PtrToPtr => "ptrtoptr",
        C::Bitcast => "bitcast",
        C::Transmute => "transmute",
        C::ReifyFnPointer => "reifyfnpointer",
        other => return Err(format!("no IRCastOp image for {other:?}")),
    })
}

pub(super) fn cc(c: trust_ir::CallingConv) -> u32 {
    c as u32
}
