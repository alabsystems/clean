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
//! `IRInst` has **33 constructors**: thirty cover the `trust_ir::Inst`
//! variants the two producers construct and the legacy machine models, and
//! the U64 and Usize fetch-add constructors name narrow sequential ByteV1
//! operations that the legacy cell machine explicitly refuses. Their presence is syntax
//! coverage, not legacy execution coverage or a concurrent-atomic theorem.
//! Twenty-eight come from the THIR lowerer (`crates/trust-thir-lower/src`);
//! `borrow` and `copy` come from the OTHER producer, the trust-ir bridge
//! (`crates/trust-ir-bridge/src/lower.rs`), which is what emits the Phase-B
//! callee sidecar whose bodies carry them.
//!
//! The modelled set is a SUBSET of the constructed set, and the difference is
//! PUBLISHED rather than implied. The older sentence here — "34 `Inst::`
//! variants are referenced, six of them only in pattern position" — was a
//! `grep -roh "Inst::[A-Za-z0-9_]*"` over one producer, and it was measurably
//! false: that recipe yields 61 distinct tokens, and `Inst::InsertElement` is
//! CONSTRUCTED at eight sites in `crates/trust-thir-lower/src/lib.rs`
//! (`InstrNode::new(Inst::InsertElement {`, measured 2026-09-10 at trust
//! `0dd9d3e2d7`) while `insertelement` sat in `NOT_EMITTED` under a comment
//! promising this test would notice. `data/irinst_producer_census.json` (B2C) is the
//! parse-based two-producer scan that replaces the recipe; until it is minted,
//! quote no fraction of the full `Inst` enum from here.
//!
//! `IRBinOp` has twenty canonical operators, not an injective mirror of the
//! `trust_ir::BinOp` spellings. The ByteV1 reflector maps validated scalar Bool
//! `BAnd/BOr/BXor` to typed `and_/or_/xor_`, retaining `IRTy.bool_` and the
//! original module identity separately. This is not a discriminant mapping or
//! authority for the separate Lean integer model.
//!
//! No coverage fraction against a `trust_ir` enum is restated in this comment:
//! the ones it carried went stale unnoticed (`IRUnOp` "9/9" after trust-ir
//! 4f09dab8 grew `UnOp` to 13 variants, `Ty` "37" at 40). Each registered
//! description (`IRTy` and the six operator alphabets) states its split against
//! the `trust_ir` enum it names, and `tests/eval_ir/trust_ir_parity.rs` holds
//! every such statement, and the constructor order, against the enum itself —
//! through exhaustive matches, so a variant trust-ir adds fails to compile
//! there until someone classifies it. `IRTy` is **not** complete against `Ty`;
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
    /// algebras, the six operator alphabets, `IRInst` (33, Release-retaining syntax epoch), `IREnc`, and the
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
        //  - floats carry width only, and the width is now SEMANTIC INPUT: the
        //    binary64 value domain (`eval_ir_float`, 2026-08-15) decides `w = 64`
        //    and gives every other width the tagged unmodelled outcome, because
        //    binary32 and binary16 are different formats with different exponent
        //    fields. Nothing observes more than the width: there is no per-format
        //    layout table here, only the one this module's boundary constants fix;
        //  - the thin pointer family keeps its pointee. The legacy `fatptr_`
        //    remains untouched, while appended ByteV1 kinds distinguish Str,
        //    Slice (with its element type), Dyn (with its trait identity),
        //    ContainerLen and ContainerVtable. No invented pointee marker
        //    identifies these nominally distinct types;
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
| func_ : Nat → IRTy
| usize_ : Nat → IRTy
| fatstr_ : IRTy
| fatslice_ : IRTy → IRTy
| fatdyn_ : Nat → IRTy
| containerlen_ : IRTy
| containervtable_ : IRTy",
            "EvalIR types. Mirrors the 42 trust_ir::Ty variants over the emitted fragment, NOT \
             one-to-one: scalars by width, the pointer-like family with its pointee \
             (PtrMetadata dispatches thin-vs-fat), and aggregates named by ID. Aggregates are NOT structural — a structural tuple would be \
             a nested inductive, and the cell-addressed semantics never inspects an aggregate's \
             field types. Appended Usize and five distinct fat-pointer kinds preserve \
             target width, slice element and trait identity. ByteV1 supplies their typed \
             operations; legacy untyped pointer-part helpers remain unchanged. The old fatptr_ remains \
             distinct and Byte-refused; fat-pointer memory, casts and native ABI are not \
             admitted by these syntax additions. Storage describes addressable, possibly \
             uninitialized geometry and has no IRTy image; it grants no initialized-value \
             semantics or admitted storage operations. Tensor (trust-ir v67) has no IRTy \
             image either: no tensor value, instruction or weight blob is admitted.",
        )?;

        // =========================================================
        // Constants.
        // =========================================================
        //
        // AGGREGATE CONSTANTS, and why the last three constructors look like
        // `IRScalar`'s. `trust_ir::Constant::Aggregate(Vec<Constant>)` is the
        // spelling every enum-returning body uses for a by-value result —
        // MEASURED at HEAD, not assumed:
        //
        // ```text
        // mode::CleanMode::from_source_system      %3 = const enum.13  { 0 }
        // <tc::ExprPathStep as Clone>::clone       %4 = const enum.181 { 0 }
        // ```
        //
        // Both are `Constant::Aggregate([Constant::Int(k)])`: arity ONE,
        // element kind `Int`, nesting depth ONE. The producer's convention
        // (`trust-ir/src/interpret.rs:1712-1766`) is that an enum-typed
        // aggregate constant carries its discriminant at element 0 and the
        // selected variant's fields at `1..`, which is the same tag-at-slot-0
        // convention `ir_var` already builds for values.
        //
        // A structural `agg : IRList IRConst -> IRConst` is a NESTED inductive
        // and the elaborator does not register one. So the element spine lives
        // INSIDE the family as two more of its own constructors — exactly the
        // `IRScalar` `aggv`/`vnil`/`vcons` precedent (`eval_ir_state.rs`, whose
        // module doc records the measured `ProbeNested` FAIL / `ProbeSpine`
        // PASS pair that established it). `IRConst.aggv sp` is an aggregate
        // whose elements are the `vnil`/`vcons` chain `sp`.
        //
        // The junk inhabitants are named rather than left in a commit message,
        // as they were for `IRScalar`: a bare `vnil` / `vcons a b` is a
        // representable `IRConst` that is not a constant of any type, and
        // `aggv (int_ 3)` is an aggregate with a non-spine element list. Every
        // verdict on them is fail-closed inside the existing fault alphabet —
        // `ir_const_eval` gives a bare spine node `type_error not_agg`, and a
        // non-spine payload materializes to a value whose `ir_vals_len` is
        // zero, so `ExtractField` on it is `bad_field`.
        self.add_inductive(
            r"inductive IRConst : Type
| int_ : Nat → IRConst
| bool_ : Bool → IRConst
| unit_ : IRConst
| null_ : IRConst
| undef_ : IRConst
| float_ : Nat → IRConst
| func_ : Nat → IRConst
| aggv : IRConst → IRConst
| vnil : IRConst
| vcons : IRConst → IRConst → IRConst
| phantomdata : IRConst",
            "EvalIR constants: the `Inst::Const` payload. `phantomdata` is trust_ir::Constant::PhantomData, the ZERO-SIZED marker, added 2026-09-16 because `tc::heartbeat::tick_heartbeat` -- the one callee whose absence makes infer_type's call closure cyclic -- emits `const () phantomdata`, and reader A REFUSED to project it (\"no Clean IRConst image for PhantomData\"). A SEPARATE constructor rather than an alias for `unit_`, because the producer keeps it separate (trust_ir constant.rs:140) and the emitted text prints it by its own name; it EVALUATES to IRScalar.unit_, which is faithful -- the emitted type is already `()` and a zero-sized type has no other value. `float_` carries an IEEE 754 binary64 \
             bit pattern. As of 2026-08-15 float arithmetic IS partly modelled — see \
             super::eval_ir_float for exactly which fragment and the measured reason the rest is \
             refused; this comment previously said \"no float arithmetic is modelled\" and was \
             true when it was written. `func_` is a function id, the \
             constant form a CallIndirect callee resolves through. `aggv`/`vnil`/`vcons` are \
             `trust_ir::Constant::Aggregate`, carried as an INLINE element spine because a \
             structural `IRList IRConst` field would be a nested inductive the elaborator does \
             not register — the same shape, and the same reason, as `IRScalar`'s payload spine.",
        )?;

        // =========================================================
        // Canonical typed operator alphabets; not Rust enum discriminants.
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
            "EvalIR binary operators: twenty typed semantic constructors, one each for 20 of \
             the 26 trust_ir::BinOp variants, in declaration order; not a \
             discriminant-preserving mirror. ByteV1 maps validated scalar Bool BAnd/BOr/BXor \
             to and_/or_/xor_ while retaining IRTy.bool_ and the original module identity \
             separately. RotL, RotR and FCopySign (trust-ir WS3.20) have NO constructor: a \
             projection that meets one refuses it by name, never approximates.",
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
            "EvalIR unary operators: one constructor each for 9 of the 13 trust_ir::UnOp \
             variants, in declaration order. CtLz, CtTz, BSwap and BitReverse (trust-ir WS3.20) \
             have NO constructor: a projection that meets one refuses it by name, never \
             approximates.",
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
            "EvalIR float comparisons — 12/12 of trust_ir::FCmpOp, in declaration order. All 12 \
             have REAL semantics on the classified binary64 fragment since 2026-08-25 \
             (super::eval_ir_fcmp, plan W4). The refusal that stood here until then — 'no body \
             in clean-kernel emits an FCmp that lowers (`reduce_float_beq/blt/ble::{closure#0}` \
             are all `unsupported: shim: Inst::FCmp`), so an FCmp semantics would be modelling \
             with no artifact to be about' — was true when written and predates B3-SELECT: as \
             the ratified definitional semantics of the trust-ir waist, EvalIR's subject is \
             every constructed-Inst module, not only the bodies clean-kernel emits \
             (docs/analysis/evalir-completion-plan-2026-08-24.md section 0), and the W4 \
             synthetic lane is the artifact the comparisons are about.",
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
        // Instructions — 30, one per CONSTRUCTED-and-MODELLED Inst variant.
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
        //  - `Copy.ty` is KEPT and READ. The reference's arm calls
        //    `expect_ty(operand, ty)` and raises a `type_error` when the two
        //    disagree (trust-ir interpret.rs, `Inst::Copy`), so this is a slot
        //    that decides ACCEPT-versus-FAULT: an irrelevance theorem for it
        //    would be an adequacy claim the reference refutes. The machine
        //    models the check at the granularity the model can decide —
        //    `ir_copy_eval`'s shape agreement — and the residual coarseness
        //    (widths, signedness, aggregate ids) is a DECLARED DELTA
        //    (`copy-type-check-coarse` in data/evalir_adequacy_grid.json),
        //    never an irrelevance row.
        //  - `Borrow` carries only its operand: the reference's arm is
        //    `expect_pointer`, a dereference-time PROVENANCE check, which the
        //    machine models by resolving the address in memory
        //    (`ir_borrow_eval`).
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
| select : IRTy → Nat → Nat → Nat → IRInst
| borrow : Nat → IRInst
| copy : IRTy → Nat → IRInst
| atomic_fetch_add_relaxed_u64_seq : Nat → Nat → IRInst
| atomic_fetch_add_relaxed_usize_seq : Nat → Nat → Nat → IRInst
| release : Nat → IRInst",
            "EvalIR instructions: 33 constructors in the Release-retaining syntax epoch. Thirty cover trust_ir::Inst variants that the two \
             producers of the executed bundle construct AND the legacy machine models — the THIR \
             lowerer (crates/trust-thir-lower/src) for 28 of them, the trust-ir bridge \
             (crates/trust-ir-bridge/src/lower.rs) for `borrow` and `copy`, which the Phase-B \
             callee sidecar's own bodies carry. The modelled set is a SUBSET of the constructed \
             set; B2C will publish that difference by minting \
             data/irinst_producer_census.json, which does not exist yet, so quote no fraction \
             of the full Inst enum from this string either. SSA operands are Nat value \
             ids; the result of a value-producing instruction is bound at the machine's fresh \
             next-value-id, mirroring the Lean model's bindFresh. `align` is erased from \
             load/store/alloca (not observable in a cell-addressed model); \
             Switch.exhaustive_enum_unreachable, GEP.inbounds and CallIndirect.calling_conv are \
             retained. The APPENDED atomic_fetch_add_relaxed_u64_seq constructor carries the \
             pointer and increment SSA ids, preserving every prior constructor position. It \
             names only sequential relaxed u64 fetch-add for the byte profile, not general \
             AtomicRMW or concurrent execution. The legacy cell-addressed ir_exec refuses it \
             explicitly. The appended usize operation retains a distinct target-bit-width \
             index before its two SSA operands; only width 64 executes in ByteV1. The appended \
             IRTy.usize_ is not an alias of uint_, and adding syntax grants no source or \
             concurrent atomic execution authority. The APPENDED release constructor retains exactly \
             one SSA pointer id and is result-free at its node/site. All three evaluators \
             explicitly halt unmodelled; this is syntax retention, not ARC execution.",
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

        // The ENCODINGS TABLE (Phase B, link 3). A row says how the byte image
        // of one aggregate id decodes into the model's inline-aggregate value,
        // for exactly the two shapes the crystal chain loads:
        //
        //  - `nicheptr K none some T` — enum id K is NICHE-encoded over a
        //    pointer-shaped payload of type T: word 0 is variant `none`, every
        //    other word is variant `some` carrying the payload. That is the
        //    reference's word decode at `niche_start = 0` over an empty
        //    variant range, and the thirteen F9 clauses (design
        //    `semantics_rule`) are what a DERIVED row must satisfy before it
        //    may be minted — the model cannot read `niche_start` /
        //    `niche_variants_*`, so the requirement that they not be ignored
        //    is met at the derivation rule, not here.
        //  - `ptrwrap S i c T` — struct id S has `c` fields, all zero-sized
        //    except field `i`, which carries the payload of type T. Its byte
        //    image IS the payload's, so the model's aggregate value is the
        //    payload at slot `i` and `aggv vnil` (the image `decode_value`
        //    returns for a zero-FIELD aggregate) elsewhere.
        //
        // A row is keyed on `(KIND, id)`, never on the id alone: the crystal's
        // own table has `(enum 0)` and `(struct 0)`, so an id-only key would
        // refuse the chain it exists for. `ir_enc_matches` keys nicheptr on
        // `IRTy.enum_` and ptrwrap on `IRTy.struct_`, which is why the
        // semantics never had that defect.
        self.add_inductive(
            r"inductive IREnc : Type
| nicheptr : Nat → Nat → Nat → IRTy → IREnc
| ptrwrap : Nat → Nat → Nat → IRTy → IREnc",
            "One row of a module's encodings table: how the byte image of an aggregate id \
             decodes into a cell-addressed value. `nicheptr K none some T` is a two-variant \
             niche-encoded enum over a pointer payload (word 0 = the `none` variant, any other \
             word = the `some` variant carrying a payload of type T); `ptrwrap S i c T` is a \
             c-field struct whose only non-ZST field is `i`, of type T. Rows are DERIVED from \
             the artifact's layout descriptors and refused clause by clause (design F9); a \
             hand-typed row is never a pin.",
        )?;

        // `mkv` is ADDITIVE, and that is the whole conservativity argument.
        // Every module minted before Phase B is an `IRModule.mk`, and
        // `ir_mod_encs` sends `mk` to the EMPTY table, so the encoding-aware
        // load view iota-reduces to the identity on every one of them — an
        // `Eq.refl` at an abstract module, not an argument. A module that
        // carries a derived table is an `IRModule.mkv`.
        self.add_inductive(
            r"inductive IRModule : Type
| mk : IRList IRFunc → IRList IRGlobal → IRModule
| mkv : IRList IRFunc → IRList IRGlobal → IRList IREnc → IRModule",
            "A module: its functions, its globals, and (in the `mkv` form) its DERIVED \
             encodings table. The unit an artifact digest is taken over (Phase-A job A1); \
             EvalIR itself never hashes anything. `mk` is retained rather than widened so the \
             eighteen chains minted before Phase B keep their exact terms, and `ir_mod_encs \
             (IRModule.mk fs gs)` is the empty table by definition — the load view is then the \
             identity on them by iota, which is what makes this extension conservative. \
             SCOPE, stated rather than implied: as of B2 `mkv` has NO producer. The minter \
             (crates/clean-verify/src/ir_mint/mint.rs) still renders `IRModule.mk` with an \
             empty global list and the decoder still reads `IRModule.mk`, because the minter's \
             globals rendering that `mkv` extends is Phase-A job A:S6, which is not in this \
             worktree; the minter/decoder arms move with it in B4/B5. Until then the only \
             terms of this form in the environment are the three registered witnesses \
             ir_load_view_mkv_reads_ty, ir_view_ptr0_is_none and ir_view_agg_is_identity — a \
             capability whose caller arrives later, recorded here so it is a stated gap and \
             not a silent one.",
        )?;

        Ok(())
    }
}
