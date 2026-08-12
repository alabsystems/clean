// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — syntax layer (job **C3** of the crystal program).
//!
//! This is the Clean-side object language for trust-ir: types, constants,
//! operator alphabets, instructions, blocks, functions and modules, all
//! registered as Clean inductives so the semantics in
//! [`super::eval_ir_semantics`] can be an ordinary kernel-checked recursive
//! function over them.
//!
//! ## Why a Clean-side semantics exists at all
//!
//! trust-ir already ships a Lean 4 operational semantics
//! (the sibling trust-ir checkout's `lean/trust_ir-semantics/`). It cannot serve as the crystal's
//! semantics, for a reason that is measurable at source: the Lean model is
//! **byte-addressable**, so every load first asks for the pointee's byte size —
//!
//! ```text
//! Ty.byteSize : Ty -> Option Nat
//!   ...
//!   | _ => none        -- Never, Tuple, Enum, Struct, Array, Func: context-dependent
//! ```
//! (`TrustIr/Semantics/Memory.lean:89-116`), and `semLoad` turns that `none`
//! into `Sem.throwTypeError "Load: type has no byte size"` (`:431-433`).
//!
//! The crystal's target, `clean_kernel::Level::is_zero`, is a `&self` method on
//! a five-variant **enum** whose recursive edges are `LevelArc(Option<Arc<Level>>)`.
//! Every step of it loads a `Ty::Enum`. So the Lean model rejects the crystal's
//! central operation by construction. Per the standing extend-don't-descope
//! rule, that is a build item, and this module is it: a **cell-addressed**
//! semantics in which a memory cell holds a *value*, not a byte string, so
//! loading an enum needs no size.
//!
//! Lean stays the reference. Nothing here is generated from it and no Lean
//! enters this crate; divergence between the two is caught by the Lean-model
//! adequacy stream in the sibling trust-ir checkout, not by coupling the builds. The
//! divergences deliberately taken are listed in [`super::eval_ir_semantics`].
//!
//! ## Coverage, as a fraction
//!
//! `IRInst` has **28 constructors, one per `Inst` variant the lowerer actually
//! constructs**. Measured at HEAD in the sibling trust checkout's `crates/trust-thir-lower/src` by
//! per-occurrence classification: 34 `Inst::` variants are referenced, six of
//! them only in pattern position and never constructed — `Assume`, `Copy`,
//! `HeapAlloc`, `InsertElement`, `Invoke`, `NullPtr` — leaving **28
//! constructed**. Those six are deliberately absent here; the fraction is
//! 28/28 of the emitted set and 28/57 of the full `Inst` enum.
//!
//! The operator alphabets are complete against their Rust enums: `IRBinOp`
//! 20/20, `IRUnOp` 9/9, `IRICmpOp` 10/10, `IRFCmpOp` 12/12, `IRCastOp` 17/17,
//! `IROverflowOp` 3/3. `IRTy` is **not** complete against `Ty` (**37**
//! variants, counted at HEAD from `crates/trust-ir/src/ty.rs:84`'s enum body —
//! the crystal design doc's §3.2 says 38, which no longer matches);
//! it carries the scalar, pointer-like and aggregate-by-id forms the emitted
//! fragment observes, and names aggregates by id rather than by structure —
//! see the `IRTy` registration comment for the exact list and why the
//! semantics does not need more.
//!
//! ## Two structural constraints this design is shaped by
//!
//! 1. **No nested or mutual inductives.** The elaborator registers neither; the
//!    tree models both by *encoding* them at the object level instead
//!    (`rose_schema.rs`, `mutual_schema.rs`). That constraint is exactly what
//!    shapes `IRScalar`: a structured value cannot carry an `IRList IRScalar`
//!    field, because that is a NESTED inductive. So the payload spine lives
//!    INSIDE the family as two more of its own constructors — `vnil` and
//!    `vcons` — and `aggv sp` is a struct / tuple / array / enum whose fields
//!    are the spine `sp`. Structured values are therefore INLINE: there is no
//!    separate store and no handle to resolve. That also settles the aliasing
//!    question a by-value aggregate would raise, by immutability rather than by
//!    indirection — a value read out of memory before a Store still denotes
//!    what it denoted then, with no deep copy and nothing to invalidate.
//! 2. **Single-scrutinee `match` only.** Multi-scrutinee dispatch goes through
//!    an explicit `.rec` with a function-valued motive, the `level_eqb` idiom.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Register the `EvalIR` syntax layer: lists/options, the type and constant
    /// algebras, the six operator alphabets, `IRInst` (28), and the
    /// block/function/module structure.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_syntax(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Containers.
        // =========================================================
        //
        // EvalIR carries its OWN list/option families rather than reusing
        // `ListType` / `OptionType`. Those are registered inside the
        // `expr_model` / `rec_env` stages, which also register KExpr and the
        // whole reduction substrate; depending on them would make the EvalIR
        // stage — and the minimal bundle its tests build — drag in the entire
        // metatheory lane for two container types. `IRList` / `IROption` are
        // byte-identical in shape; nothing is shared and nothing conflicts.
        self.add_inductive(
            r"inductive IRList (α : Type) : Type
| nil : IRList α
| cons : α → IRList α → IRList α",
            "EvalIR list container. Shape-identical to ListType; registered separately so the \
             EvalIR stage depends only on foundation types (Nat/Bool/Eq) and not on the KExpr \
             reduction substrate.",
        )?;

        self.add_inductive(
            r"inductive IROption (α : Type) : Type
| none : IROption α
| some : α → IROption α",
            "EvalIR option container. Shape-identical to OptionType; registered separately for \
             the same stage-independence reason as IRList.",
        )?;

        // =========================================================
        // Types.
        // =========================================================
        //
        // Faithful to `trust_ir::Ty` for everything the emitted fragment's
        // SEMANTICS observes, and deliberately coarser elsewhere:
        //
        //  - integers carry their bit width as a Nat and their signedness as
        //    the constructor choice (`int_` signed / `uint_` unsigned), which is
        //    exactly what `Ty::I8..I128` / `Ty::U8..U128` encode as ten separate
        //    variants;
        //  - floats carry width only; there is no float value domain (see
        //    eval_ir_semantics' exclusion list), so nothing observes more;
        //  - the pointer-like family (`Ref`/`RefMut`/`PtrConst`/`PtrMut`/`Rc`/
        //    `FatPtr`) keeps its pointee, because `PtrMetadata` dispatches on
        //    thin-vs-fat;
        //  - aggregates are named by ID (`struct_`/`enum_`/`tuple_`/`func_`),
        //    NOT by structure. A structural `tuple_ : IRList IRTy` would be a
        //    NESTED inductive, which the elaborator does not register; and the
        //    cell-addressed semantics never needs an aggregate's field types —
        //    a load returns the stored value whatever its shape. This is the
        //    single place where the byte-size wall the Lean model hits is
        //    designed out rather than worked around.
        self.add_inductive(
            r"inductive IRTy : Type
| bool_ : IRTy
| int_ : Nat → IRTy
| uint_ : Nat → IRTy
| float_ : Nat → IRTy
| ptr_ : IRTy
| ref_ : IRTy → IRTy
| refmut_ : IRTy → IRTy
| rawconst_ : IRTy → IRTy
| rawmut_ : IRTy → IRTy
| rc_ : IRTy → IRTy
| fatptr_ : IRTy → IRTy
| unit_ : IRTy
| never_ : IRTy
| tuple_ : Nat → IRTy
| array_ : IRTy → Nat → IRTy
| struct_ : Nat → IRTy
| enum_ : Nat → IRTy
| func_ : Nat → IRTy",
            "EvalIR types. Mirrors trust_ir::Ty over the emitted fragment: scalars by width, the \
             pointer-like family with its pointee (PtrMetadata dispatches thin-vs-fat), and \
             aggregates named by ID. Aggregates are NOT structural — a structural tuple would be \
             a nested inductive, and the cell-addressed semantics never inspects an aggregate's \
             field types.",
        )?;

        // =========================================================
        // Constants.
        // =========================================================
        self.add_inductive(
            r"inductive IRConst : Type
| int_ : Nat → IRConst
| bool_ : Bool → IRConst
| unit_ : IRConst
| null_ : IRConst
| undef_ : IRConst
| float_ : Nat → IRConst
| func_ : Nat → IRConst",
            "EvalIR constants: the `Inst::Const` payload. `float_` carries an opaque bit pattern \
             — it can be BUILT and COMPARED for syntactic identity but no float arithmetic is \
             modelled (see the eval_ir_semantics exclusion list). `func_` is a function id, the \
             constant form a CallIndirect callee resolves through.",
        )?;

        // =========================================================
        // Operator alphabets — complete against their Rust enums.
        // =========================================================
        self.add_inductive(
            r"inductive IRBinOp : Type
| add : IRBinOp
| sub : IRBinOp
| mul : IRBinOp
| udiv : IRBinOp
| sdiv : IRBinOp
| urem : IRBinOp
| srem : IRBinOp
| fadd : IRBinOp
| fsub : IRBinOp
| fmul : IRBinOp
| fdiv : IRBinOp
| frem : IRBinOp
| fmin : IRBinOp
| fmax : IRBinOp
| and_ : IRBinOp
| or_ : IRBinOp
| xor_ : IRBinOp
| shl : IRBinOp
| lshr : IRBinOp
| ashr : IRBinOp",
            "EvalIR binary operators — 20/20 of trust_ir::BinOp, in declaration order.",
        )?;

        self.add_inductive(
            r"inductive IRUnOp : Type
| neg : IRUnOp
| fneg : IRUnOp
| fabs : IRUnOp
| fsqrt : IRUnOp
| ffloor : IRUnOp
| fceil : IRUnOp
| ftrunc : IRUnOp
| not_ : IRUnOp
| ctpop : IRUnOp",
            "EvalIR unary operators — 9/9 of trust_ir::UnOp, in declaration order.",
        )?;

        self.add_inductive(
            r"inductive IRICmpOp : Type
| eq_ : IRICmpOp
| ne_ : IRICmpOp
| ult : IRICmpOp
| ule : IRICmpOp
| ugt : IRICmpOp
| uge : IRICmpOp
| slt : IRICmpOp
| sle : IRICmpOp
| sgt : IRICmpOp
| sge : IRICmpOp",
            "EvalIR integer comparisons — 10/10 of trust_ir::ICmpOp, in declaration order.",
        )?;

        self.add_inductive(
            r"inductive IRFCmpOp : Type
| oeq : IRFCmpOp
| one_ : IRFCmpOp
| olt : IRFCmpOp
| ole : IRFCmpOp
| ogt : IRFCmpOp
| oge : IRFCmpOp
| ueq : IRFCmpOp
| une : IRFCmpOp
| ult : IRFCmpOp
| ule : IRFCmpOp
| ugt : IRFCmpOp
| uge : IRFCmpOp",
            "EvalIR float comparisons — 12/12 of trust_ir::FCmpOp, in declaration order. Present \
             so the FCmp instruction has a well-typed operator argument; the semantics of every \
             one of them is the explicit `unmodelled` outcome (no float value domain).",
        )?;

        self.add_inductive(
            r"inductive IRCastOp : Type
| trunc : IRCastOp
| zext : IRCastOp
| sext : IRCastOp
| fptrunc : IRCastOp
| fpext : IRCastOp
| fptoui : IRCastOp
| fptosi : IRCastOp
| uitofp : IRCastOp
| sitofp : IRCastOp
| ptrtoint : IRCastOp
| inttoptr : IRCastOp
| ptrtoptr : IRCastOp
| bitcast : IRCastOp
| transmute : IRCastOp
| reifyfnpointer : IRCastOp
| fptosisat : IRCastOp
| fptouisat : IRCastOp",
            "EvalIR casts — 17/17 of trust_ir::CastOp, in declaration order.",
        )?;

        self.add_inductive(
            r"inductive IROverflowOp : Type
| addoverflow : IROverflowOp
| suboverflow : IROverflowOp
| muloverflow : IROverflowOp",
            "EvalIR checked-arithmetic operators — 3/3 of trust_ir::OverflowOp.",
        )?;

        // =========================================================
        // Switch cases.
        // =========================================================
        self.add_inductive(
            r"inductive IRSwitchCase : Type
| mk : Nat → Nat → IRList Nat → IRSwitchCase",
            "One arm of a Switch: the selector value it matches, the target block id, and the \
             block arguments. Mirrors trust_ir::SwitchCase.",
        )?;

        // =========================================================
        // Instructions — 28, one per CONSTRUCTED Inst variant.
        // =========================================================
        //
        // Field-shape notes where this deviates from `trust_ir::Inst`, each an
        // erasure that the Lean-model-adequacy stream owns as a separate
        // obligation (the same class of gap as `Alloca.align`,
        // `Switch.exhaustive_enum_unreachable` and `CallIndirect.calling_conv`
        // being absent from their Lean counterparts):
        //
        //  - `align : Option<u64>` is ERASED from load/store/alloca. The
        //    cell-addressed model has no byte offsets, so alignment is not
        //    observable in it. Erasure, not modelling.
        //  - `Switch.exhaustive_enum_unreachable` is KEPT (the Bool field): it
        //    is a trust-bearing flag set only by a TyCtxt-vetted check, so a
        //    model that dropped it could not state what it licenses.
        //  - `CallIndirect.calling_conv` is KEPT as a Nat tag. Nothing in the
        //    semantics dispatches on it; it is retained so the instruction's
        //    arity matches the Rust variant and an adequacy theorem has
        //    something to quantify over.
        //  - `GEP.inbounds` is KEPT (the Bool field): it licenses no-wrap
        //    folding, so it is load-bearing for any later optimisation
        //    argument.
        self.add_inductive(
            r"inductive IRInst : Type
| binop : IRBinOp → IRTy → Nat → Nat → IRInst
| unop : IRUnOp → IRTy → Nat → IRInst
| overflow : IROverflowOp → IRTy → Nat → Nat → IRInst
| icmp : IRICmpOp → IRTy → Nat → Nat → IRInst
| fcmp : IRFCmpOp → IRTy → Nat → Nat → IRInst
| cast : IRCastOp → IRTy → IRTy → Nat → IRInst
| load : IRTy → Nat → Bool → IRInst
| store : IRTy → Nat → Nat → Bool → IRInst
| alloca : IRTy → IROption Nat → IRInst
| gep : IRTy → Nat → IRList Nat → Bool → IRInst
| ptrdata : IRTy → Nat → IRInst
| ptrmetadata : IRTy → IRTy → Nat → IRInst
| ptrfromparts : IRTy → IRTy → Nat → Nat → IRInst
| br : Nat → IRList Nat → IRInst
| condbr : Nat → Nat → IRList Nat → Nat → IRList Nat → IRInst
| switch : Nat → Nat → IRList Nat → IRList IRSwitchCase → Bool → IRInst
| call : Nat → IRList Nat → IRInst
| callindirect : Nat → Nat → IRList Nat → Nat → IRInst
| ret : IRList Nat → IRInst
| extractfield : IRTy → Nat → Nat → IRInst
| insertfield : IRTy → Nat → Nat → Nat → IRInst
| extractelement : IRTy → Nat → Nat → IRInst
| const_ : IRTy → IRConst → IRInst
| globaladdr : Nat → IRInst
| undef : IRTy → IRInst
| assert : Nat → IRInst
| unreachable : IRInst
| select : IRTy → Nat → Nat → Nat → IRInst",
            "EvalIR instructions: 28 constructors, one per trust_ir::Inst variant the THIR \
             lowerer actually constructs (34 referenced minus the six pattern-position-only \
             Assume/Copy/HeapAlloc/InsertElement/Invoke/NullPtr). SSA operands are Nat value \
             ids; the result of a value-producing instruction is bound at the machine's fresh \
             next-value-id, mirroring the Lean model's bindFresh. `align` is erased from \
             load/store/alloca (not observable in a cell-addressed model); \
             Switch.exhaustive_enum_unreachable, GEP.inbounds and CallIndirect.calling_conv are \
             retained.",
        )?;

        // =========================================================
        // Program structure.
        // =========================================================
        // A block body is a list of NODES, not of bare instructions: in
        // `trust_ir` an `InstrNode` is `{ inst, results : Vec<ValueId>, .. }`
        // (`crates/trust-ir/src/node.rs:11-23`), so an instruction's result SSA
        // ids are DECLARED STATICALLY, per node.
        //
        // This is a place where following the Rust IR and following the Lean
        // reference semantics give different answers, and the Rust IR wins: the
        // Lean model erases `results` and mints ids from a `nextValueId`
        // counter instead (`MachineState.bindValue`,
        // `State/MachineState.lean:56-61`). That erasure is unsound for any
        // block executed more than once — a loop body would bind its results to
        // different ids on the second pass, so the ids its own instructions
        // refer to would no longer resolve. Since the crystal target is
        // recursive and the theorem is about the artifact the RUST producer
        // emits, `IRNode` carries `results` and the machine has no id counter
        // at all. (Recorded as a Lean-model-adequacy item for the Phase-B
        // stream that owns the sibling trust-ir checkout.)
        self.add_inductive(
            r"inductive IRNode : Type
| mk : IRInst → IRList Nat → IRNode",
            "One instruction node: the instruction and the SSA ids its results are bound to. \
             Mirrors trust_ir::InstrNode's `inst` + `results`; `proofs`, `span` and \
             `proof_context` are erased (they carry no operational meaning). A value-producing \
             instruction whose result list is empty is evaluated and its value discarded.",
        )?;

        self.add_inductive(
            r"inductive IRBlock : Type
| mk : Nat → IRList Nat → IRList IRNode → IRBlock",
            "A basic block: its id, its block parameters (SSA ids bound on entry from the \
             predecessor's branch arguments), and its node list. The terminator is the last \
             node; running off the end of a block is a stuck state, not a fallthrough.",
        )?;

        self.add_inductive(
            r"inductive IRFunc : Type
| mk : Nat → IRList Nat → Nat → IRList IRBlock → IRFunc",
            "A function: its id, its parameter SSA ids, its entry block id, and its blocks.",
        )?;

        self.add_inductive(
            r"inductive IRGlobal : Type
| mk : Nat → IRConst → IRGlobal",
            "A module-level global: its id and its initializer constant. `Inst::GlobalAddr` \
             yields a pointer to the cell the machine materializes for it at start-up.",
        )?;

        self.add_inductive(
            r"inductive IRModule : Type
| mk : IRList IRFunc → IRList IRGlobal → IRModule",
            "A module: its functions and its globals. The unit an artifact digest is taken over \
             (Phase-A job A1); EvalIR itself never hashes anything.",
        )?;

        Ok(())
    }
}
