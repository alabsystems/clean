// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The one table.** Every instruction, type, constant and operator of the
//! core fragment is declared here exactly once, with its core mnemonic, its
//! Clean constructor and its argument kinds in order.
//!
//! The reader, the printer, the minter and the decoder all read this table, so
//! they cannot disagree about an instruction's arity or field order — only
//! about its content, which is what the gate compares. It is also the
//! name-parity table: `super::tests` fails closed if any Clean `IRInst`,
//! `IRTy`, `IRConst` or operator constructor is missing an entry, or if any
//! entry names a constructor the specification does not declare.

/// What one argument slot of an instruction holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Arg {
    /// A type S-expression.
    Ty,
    /// An SSA value id.
    Val,
    /// A block id.
    Blk,
    /// A bare natural (a field index, a callee id, a calling convention).
    Nat,
    /// A machine DATUM rather than a structural index: a type's bit WIDTH, or
    /// an integer/float constant's VALUE.
    ///
    /// The distinction is the numeral policy, and it is not cosmetic. Every
    /// `Arg::Nat` slot names a position in this module -- an SSA id, a block
    /// id, a field index, a function id -- and those are small by construction,
    /// so they render through the registered `ir_d0..ir_d16` atom pool and a
    /// numeral outside it is a REFUSAL: a `(func 20 ...)` that minted as a bare
    /// `20` would be a module nothing in the spec had named. A datum is not a
    /// position: `u32`'s width is 32 and `SimpPriority::Default`'s value is
    /// 1000, neither is bounded by the pool, and both are exactly what
    /// `IRTy.uint_` and `IRConst.int_` take. Those render as decimal `Nat`
    /// literals, which Clean's parser already accepts (`ir_mt_amt : Nat := 63`)
    /// and which reader C reads back through `ExprKind::Lit`.
    ///
    /// Values at or below 16 still render as `ir_dN`, so every artifact minted
    /// before this kind existed is byte-identical after it.
    Data,
    /// A boolean flag.
    Flag,
    /// An `IRList Nat`, written `(<head> a b ...)`.
    Vals(&'static str),
    /// The switch arm list.
    Cases,
    /// A constant S-expression.
    Const,
    /// An `IROption Nat`, written `(some n)` or `(none)`.
    OptVal,
    /// An operator drawn from the named alphabet.
    Op(&'static str),
}

/// One instruction's declared shape.
#[derive(Debug, Clone, Copy)]
pub(crate) struct InstShape {
    /// The core mnemonic.
    pub(crate) core: &'static str,
    /// The Clean `IRInst` constructor.
    pub(crate) clean: &'static str,
    /// The argument kinds, in order.
    pub(crate) args: &'static [Arg],
}

macro_rules! shape {
    ($core:literal, $clean:literal, [$($a:expr),*]) => {
        InstShape { core: $core, clean: $clean, args: &[$($a),*] }
    };
}

/// All 28 instruction shapes — one per `IRInst` constructor, no more and no
/// fewer. Order is `IRInst`'s declaration order.
pub(crate) const INSTS: &[InstShape] = &[
    shape!(
        "binop",
        "IRInst.binop",
        [Arg::Op("binop"), Arg::Ty, Arg::Val, Arg::Val]
    ),
    shape!("unop", "IRInst.unop", [Arg::Op("unop"), Arg::Ty, Arg::Val]),
    shape!(
        "overflow",
        "IRInst.overflow",
        [Arg::Op("overflow"), Arg::Ty, Arg::Val, Arg::Val]
    ),
    shape!(
        "icmp",
        "IRInst.icmp",
        [Arg::Op("icmp"), Arg::Ty, Arg::Val, Arg::Val]
    ),
    shape!(
        "fcmp",
        "IRInst.fcmp",
        [Arg::Op("fcmp"), Arg::Ty, Arg::Val, Arg::Val]
    ),
    shape!(
        "cast",
        "IRInst.cast",
        [Arg::Op("cast"), Arg::Ty, Arg::Ty, Arg::Val]
    ),
    shape!("load", "IRInst.load", [Arg::Ty, Arg::Val, Arg::Flag]),
    shape!(
        "store",
        "IRInst.store",
        [Arg::Ty, Arg::Val, Arg::Val, Arg::Flag]
    ),
    shape!("alloca", "IRInst.alloca", [Arg::Ty, Arg::OptVal]),
    shape!(
        "gep",
        "IRInst.gep",
        [Arg::Ty, Arg::Val, Arg::Vals("idx"), Arg::Flag]
    ),
    shape!("ptrdata", "IRInst.ptrdata", [Arg::Ty, Arg::Val]),
    shape!(
        "ptrmetadata",
        "IRInst.ptrmetadata",
        [Arg::Ty, Arg::Ty, Arg::Val]
    ),
    shape!(
        "ptrfromparts",
        "IRInst.ptrfromparts",
        [Arg::Ty, Arg::Ty, Arg::Val, Arg::Val]
    ),
    shape!("br", "IRInst.br", [Arg::Blk, Arg::Vals("args")]),
    shape!(
        "condbr",
        "IRInst.condbr",
        [
            Arg::Val,
            Arg::Blk,
            Arg::Vals("args"),
            Arg::Blk,
            Arg::Vals("args")
        ]
    ),
    shape!(
        "switch",
        "IRInst.switch",
        [Arg::Val, Arg::Blk, Arg::Vals("args"), Arg::Cases, Arg::Flag]
    ),
    shape!("call", "IRInst.call", [Arg::Nat, Arg::Vals("args")]),
    shape!(
        "callindirect",
        "IRInst.callindirect",
        [Arg::Val, Arg::Nat, Arg::Vals("args"), Arg::Nat]
    ),
    shape!("ret", "IRInst.ret", [Arg::Vals("vals")]),
    shape!(
        "extractfield",
        "IRInst.extractfield",
        [Arg::Ty, Arg::Val, Arg::Nat]
    ),
    shape!(
        "insertfield",
        "IRInst.insertfield",
        [Arg::Ty, Arg::Val, Arg::Nat, Arg::Val]
    ),
    shape!(
        "extractelement",
        "IRInst.extractelement",
        [Arg::Ty, Arg::Val, Arg::Val]
    ),
    shape!("const", "IRInst.const_", [Arg::Ty, Arg::Const]),
    shape!("globaladdr", "IRInst.globaladdr", [Arg::Nat]),
    shape!("undef", "IRInst.undef", [Arg::Ty]),
    shape!("assert", "IRInst.assert", [Arg::Val]),
    shape!("unreachable", "IRInst.unreachable", []),
    shape!(
        "select",
        "IRInst.select",
        [Arg::Ty, Arg::Val, Arg::Val, Arg::Val]
    ),
];

/// One type shape: core mnemonic, Clean constructor, and the kinds of its
/// arguments (`Arg::Ty` for a pointee, `Arg::Data` for a width, `Arg::Nat` for
/// an interning id).
#[derive(Debug, Clone, Copy)]
pub(crate) struct TyShape {
    /// The core mnemonic.
    pub(crate) core: &'static str,
    /// The Clean `IRTy` constructor.
    pub(crate) clean: &'static str,
    /// The argument kinds, in order.
    pub(crate) args: &'static [Arg],
}

/// All 18 type shapes — one per `IRTy` constructor.
pub(crate) const TYS: &[TyShape] = &[
    TyShape {
        core: "bool",
        clean: "IRTy.bool_",
        args: &[],
    },
    TyShape {
        core: "int",
        clean: "IRTy.int_",
        args: &[Arg::Data],
    },
    TyShape {
        core: "uint",
        clean: "IRTy.uint_",
        args: &[Arg::Data],
    },
    TyShape {
        core: "float",
        clean: "IRTy.float_",
        args: &[Arg::Data],
    },
    TyShape {
        core: "ptr",
        clean: "IRTy.ptr_",
        args: &[],
    },
    TyShape {
        core: "ref",
        clean: "IRTy.ref_",
        args: &[Arg::Ty],
    },
    TyShape {
        core: "refmut",
        clean: "IRTy.refmut_",
        args: &[Arg::Ty],
    },
    TyShape {
        core: "rawconst",
        clean: "IRTy.rawconst_",
        args: &[Arg::Ty],
    },
    TyShape {
        core: "rawmut",
        clean: "IRTy.rawmut_",
        args: &[Arg::Ty],
    },
    TyShape {
        core: "rc",
        clean: "IRTy.rc_",
        args: &[Arg::Ty],
    },
    TyShape {
        core: "fatptr",
        clean: "IRTy.fatptr_",
        args: &[Arg::Ty],
    },
    TyShape {
        core: "unit",
        clean: "IRTy.unit_",
        args: &[],
    },
    TyShape {
        core: "never",
        clean: "IRTy.never_",
        args: &[],
    },
    TyShape {
        core: "tuple",
        clean: "IRTy.tuple_",
        args: &[Arg::Nat],
    },
    TyShape {
        core: "array",
        clean: "IRTy.array_",
        args: &[Arg::Ty, Arg::Nat],
    },
    TyShape {
        core: "struct",
        clean: "IRTy.struct_",
        args: &[Arg::Nat],
    },
    TyShape {
        core: "enum",
        clean: "IRTy.enum_",
        args: &[Arg::Nat],
    },
    TyShape {
        core: "func",
        clean: "IRTy.func_",
        args: &[Arg::Nat],
    },
];

/// One constant shape.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ConstShape {
    /// The core mnemonic.
    pub(crate) core: &'static str,
    /// The Clean `IRConst` constructor.
    pub(crate) clean: &'static str,
    /// The argument kinds, in order. `agg` is variadic and handled separately.
    pub(crate) args: &'static [Arg],
}

/// The eight constant shapes. They cover ten `IRConst` constructors: `aggv`
/// carries its element list as the inline `vnil`/`vcons` spine, which the
/// minter builds and the decoder reads.
pub(crate) const CONSTS: &[ConstShape] = &[
    ConstShape {
        core: "int",
        clean: "IRConst.int_",
        args: &[Arg::Data],
    },
    ConstShape {
        core: "bool",
        clean: "IRConst.bool_",
        args: &[Arg::Flag],
    },
    ConstShape {
        core: "unit",
        clean: "IRConst.unit_",
        args: &[],
    },
    ConstShape {
        core: "null",
        clean: "IRConst.null_",
        args: &[],
    },
    ConstShape {
        core: "undef",
        clean: "IRConst.undef_",
        args: &[],
    },
    ConstShape {
        core: "float",
        clean: "IRConst.float_",
        args: &[Arg::Data],
    },
    ConstShape {
        core: "cfunc",
        clean: "IRConst.func_",
        args: &[Arg::Nat],
    },
    ConstShape {
        core: "agg",
        clean: "IRConst.aggv",
        args: &[],
    },
];

/// `(core mnemonic, Clean constructor)` for one operator alphabet.
pub(crate) type OpRow = (&'static str, &'static str);

/// The six operator alphabets, keyed by the name [`Arg::Op`] carries.
#[must_use]
pub(crate) fn alphabet(name: &str) -> &'static [OpRow] {
    match name {
        "binop" => BINOP,
        "unop" => UNOP,
        "overflow" => OVERFLOW,
        "icmp" => ICMP,
        "fcmp" => FCMP,
        "cast" => CAST,
        _ => &[],
    }
}

/// 20/20 of `IRBinOp`.
pub(crate) const BINOP: &[OpRow] = &[
    ("add", "IRBinOp.add"),
    ("sub", "IRBinOp.sub"),
    ("mul", "IRBinOp.mul"),
    ("udiv", "IRBinOp.udiv"),
    ("sdiv", "IRBinOp.sdiv"),
    ("urem", "IRBinOp.urem"),
    ("srem", "IRBinOp.srem"),
    ("fadd", "IRBinOp.fadd"),
    ("fsub", "IRBinOp.fsub"),
    ("fmul", "IRBinOp.fmul"),
    ("fdiv", "IRBinOp.fdiv"),
    ("frem", "IRBinOp.frem"),
    ("fmin", "IRBinOp.fmin"),
    ("fmax", "IRBinOp.fmax"),
    ("and", "IRBinOp.and_"),
    ("or", "IRBinOp.or_"),
    ("xor", "IRBinOp.xor_"),
    ("shl", "IRBinOp.shl"),
    ("lshr", "IRBinOp.lshr"),
    ("ashr", "IRBinOp.ashr"),
];

/// 9/9 of `IRUnOp`.
pub(crate) const UNOP: &[OpRow] = &[
    ("neg", "IRUnOp.neg"),
    ("fneg", "IRUnOp.fneg"),
    ("fabs", "IRUnOp.fabs"),
    ("fsqrt", "IRUnOp.fsqrt"),
    ("ffloor", "IRUnOp.ffloor"),
    ("fceil", "IRUnOp.fceil"),
    ("ftrunc", "IRUnOp.ftrunc"),
    ("not", "IRUnOp.not_"),
    ("ctpop", "IRUnOp.ctpop"),
];

/// 3/3 of `IROverflowOp`.
pub(crate) const OVERFLOW: &[OpRow] = &[
    ("addoverflow", "IROverflowOp.addoverflow"),
    ("suboverflow", "IROverflowOp.suboverflow"),
    ("muloverflow", "IROverflowOp.muloverflow"),
];

/// 10/10 of `IRICmpOp`.
pub(crate) const ICMP: &[OpRow] = &[
    ("eq", "IRICmpOp.eq_"),
    ("ne", "IRICmpOp.ne_"),
    ("ult", "IRICmpOp.ult"),
    ("ule", "IRICmpOp.ule"),
    ("ugt", "IRICmpOp.ugt"),
    ("uge", "IRICmpOp.uge"),
    ("slt", "IRICmpOp.slt"),
    ("sle", "IRICmpOp.sle"),
    ("sgt", "IRICmpOp.sgt"),
    ("sge", "IRICmpOp.sge"),
];

/// 12/12 of `IRFCmpOp`.
pub(crate) const FCMP: &[OpRow] = &[
    ("oeq", "IRFCmpOp.oeq"),
    ("one", "IRFCmpOp.one_"),
    ("olt", "IRFCmpOp.olt"),
    ("ole", "IRFCmpOp.ole"),
    ("ogt", "IRFCmpOp.ogt"),
    ("oge", "IRFCmpOp.oge"),
    ("ueq", "IRFCmpOp.ueq"),
    ("une", "IRFCmpOp.une"),
    ("ult", "IRFCmpOp.ult"),
    ("ule", "IRFCmpOp.ule"),
    ("ugt", "IRFCmpOp.ugt"),
    ("uge", "IRFCmpOp.uge"),
];

/// 17/17 of `IRCastOp`.
pub(crate) const CAST: &[OpRow] = &[
    ("trunc", "IRCastOp.trunc"),
    ("zext", "IRCastOp.zext"),
    ("sext", "IRCastOp.sext"),
    ("fptrunc", "IRCastOp.fptrunc"),
    ("fpext", "IRCastOp.fpext"),
    ("fptoui", "IRCastOp.fptoui"),
    ("fptosi", "IRCastOp.fptosi"),
    ("uitofp", "IRCastOp.uitofp"),
    ("sitofp", "IRCastOp.sitofp"),
    ("ptrtoint", "IRCastOp.ptrtoint"),
    ("inttoptr", "IRCastOp.inttoptr"),
    ("ptrtoptr", "IRCastOp.ptrtoptr"),
    ("bitcast", "IRCastOp.bitcast"),
    ("transmute", "IRCastOp.transmute"),
    ("reifyfnpointer", "IRCastOp.reifyfnpointer"),
    ("fptosisat", "IRCastOp.fptosisat"),
    ("fptouisat", "IRCastOp.fptouisat"),
];

/// Look up an instruction shape by its core mnemonic.
#[must_use]
pub(crate) fn inst(core: &str) -> Option<&'static InstShape> {
    INSTS.iter().find(|s| s.core == core)
}

/// Look up a type shape by its core mnemonic.
#[must_use]
pub(crate) fn ty(core: &str) -> Option<&'static TyShape> {
    TYS.iter().find(|s| s.core == core)
}

/// Look up a constant shape by its core mnemonic.
#[must_use]
pub(crate) fn cst(core: &str) -> Option<&'static ConstShape> {
    CONSTS.iter().find(|s| s.core == core)
}
