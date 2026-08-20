// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded executable reference interpreter for a value-only core TrustIr slice.
//!
//! This module is the first Rust callable execution surface for downstream
//! tools that need deterministic behavior without invoking the Lean model.
//! It deliberately covers a bounded subset: constants, integer arithmetic,
//! integer comparisons, select, aggregate/vector element operations, basic
//! block control flow, bounded direct/indirect function calls, executable
//! integer/float casts, scalar/vector float operations, and simple
//! allocation-aware memory operations. Dialect ops, intentionally excluded
//! casts/float widths, borrow/ARC, binding frames, and multi-threaded atomics
//! return stable unsupported codes instead of pretending to execute.
//!
//! Alignment gap with `lean/trust_ir-semantics`: Lean remains the source of truth
//! for the full operational semantics, especially memory, permission state,
//! excluded casts/float widths, atomics, and proof-carrying effects. The Rust
//! memory slice below mirrors Lean's allocation-aware checks for live
//! allocations, bounds, initialized bytes, and base-pointer deallocation, but
//! intentionally keeps layout conservative: scalar, pointer, unit, fixed
//! integer/bool vectors, and module-backed arrays have byte layouts, while
//! structs, enums, fat pointers, records, sets, sequences, closures, and
//! packed/ABI aggregate layout still report `type_error`. Volatile load/store
//! flags are deterministic no-ops in this single-threaded interpreter;
//! explicit alignment operands and natural scalar/vector alignment are checked.

use std::collections::BTreeMap;

use crate::constant::Constant;
use crate::dialect::DialectInst;
use crate::dialect::vector::{self, VectorSpec};
use crate::inst::{AtomicRMWOp, BinOp, CastOp, FCmpOp, ICmpOp, Inst, OverflowOp, UnOp};
use crate::node::InstrNode;
use crate::ty::{FuncTy, Ty};
use crate::value::{BlockId, FuncId, FuncTyId, GlobalId, TyId, ValueId};
use crate::{Block, Function, Module};

/// Stable high-level reason codes returned by the interpreter.
///
/// These are intended to be more stable than diagnostic text. Match on this
/// enum or on [`InterpretErrorCode::as_str`] in tests and downstream tooling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterpretErrorCode {
    UnsupportedDialectOp,
    UnsupportedCall,
    UnsupportedMemory,
    UnsupportedVectorShape,
    UnsupportedInstruction,
    UnsupportedCast,
    UnsupportedFloat,
    TypeError,
    UndefinedBehavior,
    Panic,
    OutOfFuel,
    /// A single allocation (or the running total) exceeded the interpreter's
    /// space budget (`InterpretOptions::mem_budget`). This is the *space*
    /// analogue of `OutOfFuel`: an incapacity/limit code, NOT a trap and NOT a
    /// lowering defect. It exists so the interpreter is a TOTAL function in
    /// memory — an in-IR allocation size (e.g. a sampled `Alloca`/`HeapAlloc`
    /// `count`) can never be turned into an unbounded host allocation that
    /// wedges the machine. Differential consumers treat it as coverage-only.
    OutOfMemory,
    MissingFunction,
    InvalidFunctionPointer,
    SignatureMismatch,
    MissingBlock,
    MissingValue,
    MalformedInstruction,
}

impl InterpretErrorCode {
    pub const fn as_str(self) -> &'static str {
        match self {
            InterpretErrorCode::UnsupportedDialectOp => "unsupported_dialect_op",
            InterpretErrorCode::UnsupportedCall => "unsupported_call",
            InterpretErrorCode::UnsupportedMemory => "unsupported_memory",
            InterpretErrorCode::UnsupportedVectorShape => "unsupported_vector_shape",
            InterpretErrorCode::UnsupportedInstruction => "unsupported_instruction",
            InterpretErrorCode::UnsupportedCast => "unsupported_cast",
            InterpretErrorCode::UnsupportedFloat => "unsupported_float",
            InterpretErrorCode::TypeError => "type_error",
            InterpretErrorCode::UndefinedBehavior => "undefined_behavior",
            InterpretErrorCode::Panic => "panic",
            InterpretErrorCode::OutOfFuel => "out_of_fuel",
            InterpretErrorCode::OutOfMemory => "out_of_memory",
            InterpretErrorCode::MissingFunction => "missing_function",
            InterpretErrorCode::InvalidFunctionPointer => "invalid_function_pointer",
            InterpretErrorCode::SignatureMismatch => "signature_mismatch",
            InterpretErrorCode::MissingBlock => "missing_block",
            InterpretErrorCode::MissingValue => "missing_value",
            InterpretErrorCode::MalformedInstruction => "malformed_instruction",
        }
    }
}

impl core::fmt::Display for InterpretErrorCode {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Structured interpreter failure with a stable reason code and optional IR
/// coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpretError {
    pub code: InterpretErrorCode,
    pub message: String,
    pub block: Option<BlockId>,
    pub value: Option<ValueId>,
}

impl InterpretError {
    pub fn new(code: InterpretErrorCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            block: None,
            value: None,
        }
    }

    pub fn with_block(mut self, block: BlockId) -> Self {
        self.block = Some(block);
        self
    }

    pub fn with_value(mut self, value: ValueId) -> Self {
        self.value = Some(value);
        self
    }
}

impl core::fmt::Display for InterpretError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match (self.block, self.value) {
            (Some(block), Some(value)) => {
                write!(
                    f,
                    "{} at bb{}:%{}: {}",
                    self.code, block.0, value.0, self.message
                )
            }
            (Some(block), None) => write!(f, "{} at bb{}: {}", self.code, block.0, self.message),
            (None, Some(value)) => write!(f, "{} at %{}: {}", self.code, value.0, self.message),
            (None, None) => write!(f, "{}: {}", self.code, self.message),
        }
    }
}

impl std::error::Error for InterpretError {}

pub type InterpretResult<T> = Result<T, InterpretError>;

/// Execution limits. Fuel is consumed per instruction node; call depth is
/// consumed per direct or indirect interprocedural call; `mem_budget` bounds
/// the bytes a single `execute_function` run may allocate.
///
/// `mem_budget` makes the interpreter a TOTAL function in *space*, exactly as
/// `fuel` makes it total in *time*. Without it, a single `Alloca`/`HeapAlloc`
/// whose `count` comes from a runtime/sampled value (e.g. an `i128::MAX`
/// boundary input fed into a real-MIR oracle) is materialized directly as a
/// host `Vec`, so one instruction can exhaust all RAM+swap and panic the
/// machine — independent of how much fuel remains. Fuel bounds the *number* of
/// instructions; it cannot bound the *cost of one*. An allocation that would
/// breach the budget fails closed with `InterpretErrorCode::OutOfMemory`
/// (an incapacity, never a verdict) instead of touching the host allocator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InterpretOptions {
    pub fuel: u64,
    pub max_call_depth: u64,
    /// Max bytes one `execute_function` run may allocate across all stack/heap/
    /// global allocations, before any host memory is touched. Default 256 MiB —
    /// orders of magnitude above any legitimate interpreted body (these allocate
    /// at most a few stack slots) yet far below what could wedge a host.
    pub mem_budget: u64,
}

impl Default for InterpretOptions {
    fn default() -> Self {
        Self {
            fuel: 10_000,
            max_call_depth: 64,
            mem_budget: 256 * 1024 * 1024,
        }
    }
}

/// Result of executing a function to a `return` terminator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpretOutcome {
    pub returns: Vec<InterpretValue>,
    pub steps: u64,
}

/// Fixed-width integer runtime payload.
///
/// `raw` is always masked to `bits`. Signedness is carried so public helpers
/// can decode the same bit pattern the way the source type intended.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InterpretInt {
    pub bits: u32,
    pub signed: bool,
    pub raw: u128,
}

impl InterpretInt {
    pub fn from_i128(bits: u32, signed: bool, value: i128) -> Option<Self> {
        Some(Self {
            bits,
            signed,
            raw: (value as u128) & int_mask(bits)?,
        })
    }

    pub fn from_raw(bits: u32, signed: bool, raw: u128) -> Option<Self> {
        Some(Self {
            bits,
            signed,
            raw: raw & int_mask(bits)?,
        })
    }

    pub fn as_unsigned(self) -> u128 {
        self.raw
    }

    pub fn as_signed(self) -> i128 {
        if self.bits == 128 {
            return self.raw as i128;
        }

        let mask = int_mask(self.bits).expect("validated integer width");
        let sign_bit = 1u128 << (self.bits - 1);
        if self.raw & sign_bit == 0 {
            self.raw as i128
        } else {
            let magnitude = ((!self.raw & mask) + 1) & mask;
            -(magnitude as i128)
        }
    }
}

/// Provenance-carrying runtime pointer.
///
/// The interpreter stores both a synthetic allocation id and a byte offset.
/// Human-facing diagnostics use the allocation's deterministic address, but
/// all validity checks are allocation-aware so stale and interior pointers do
/// not silently alias unrelated allocations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InterpretPointer {
    pub allocation: u64,
    pub offset: u64,
}

/// Typed runtime value used by the reference interpreter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpretValue {
    pub ty: Ty,
    pub kind: InterpretValueKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterpretValueKind {
    Int(InterpretInt),
    FloatBits(u64),
    Bool(bool),
    Ptr(InterpretPointer),
    Vector(Vec<InterpretValue>),
    Aggregate(Vec<InterpretValue>),
    Array(Vec<InterpretValue>),
    Sequence(Vec<InterpretValue>),
    Set(Vec<InterpretValue>),
    Record(Vec<(String, InterpretValue)>),
    Closure {
        func: FuncId,
        captures: Vec<InterpretValue>,
    },
    /// B2 (RFC TRUST_IR_V2): a FAT pointer value — the (data, metadata) pair of a
    /// `Ty::FatPtr`. `data` is a thin pointer value (`Ptr`/`NullPtr` kind); `metadata`
    /// is the kind's metadata value (a pointer-sized unsigned length for
    /// `Slice`/`Str`, a thin vtable pointer for `TraitObject`). Deliberately a
    /// DISTINCT kind (not a 2-element `Aggregate`) so a fat pointer can never be
    /// confused with a real 2-tuple by `extract_field`/`insert_field` — the only
    /// projections are `PtrData`/`PtrMetadata`, mirroring the format.
    FatPtr {
        data: Box<InterpretValue>,
        metadata: Box<InterpretValue>,
    },
    FnDef(FuncId),
    PhantomData,
    NullPtr,
    Unit,
    /// Handle to an open binding frame (the result of `Inst::OpenFrame`),
    /// carrying the frame id into `BindSlot`/`LoadSlot`/`CloseFrame`. Not a
    /// storable value: it is never encoded to or decoded from memory.
    Frame(u64),
    /// A PARTIALLY-INITIALIZED scalar image — the copy-propagates-poison value
    /// (LLVM `poison` / Miri "uninitialized bytes"). Produced by a non-strict
    /// (plain, non-atomic, non-volatile) scalar `Load` whose byte range covers
    /// one or more never-written bytes — the classic whole-lane copy of an
    /// aggregate that reads struct-tail padding or an inactive niche-enum
    /// variant's payload (the two triage cases). The vector carries every byte
    /// of the load, `None` for the uninitialized bytes.
    ///
    /// It is an INERT transport value: it may only be moved verbatim by `Copy`
    /// or written back verbatim by a (non-strict) `Store` — both preserve which
    /// bytes are uninitialized, so a later reload observes the same poison. ANY
    /// operation that INSPECTS its content (arithmetic, comparison, cast, a
    /// branch/switch condition, a call argument or return, a field projection)
    /// is undefined behaviour and faults at that true use site (`reject_partial`).
    /// The Lean mirror is `Value.partial` beside `Value.undef`; see the follow-up
    /// ladder in the commit message.
    PartialBytes(Vec<Option<u8>>),
    /// A NONZERO pointer VALUE that resolves to no live allocation — the
    /// no-provenance ("dangling") pointer. This is the sibling of the poison
    /// transport-vs-use distinction, for pointers: `NonNull::dangling()` /
    /// `ptr::without_provenance(align)` (the sentinel data pointer of an empty
    /// collection: `Vec::new`, `&[]`, len-0 slice) is a legal integer-address
    /// pointer that is NEVER dereferenced. It may be CREATED (`IntToPtr`, a
    /// load of pointer bytes that name no allocation, an empty slice's fat data
    /// lane), STORED, COPIED, and COMPARED (`PtrToInt` round-trip); the
    /// "has no allocation provenance" error moves from CREATION time to
    /// DEREFERENCE time — a `Load`/`Store`/ARC/atomic THROUGH it faults in
    /// `expect_pointer`. `NullPtr` is the zero case; this is the nonzero case.
    /// The Lean mirror is a no-provenance `Addr` pointer value whose deref alone
    /// is UB; see the follow-up ladder in the commit message.
    DanglingPtr(u64),
}

impl InterpretValue {
    pub fn int(ty: Ty, value: i128) -> InterpretResult<Self> {
        let (bits, signed) = int_shape(&ty).ok_or_else(|| {
            InterpretError::new(
                InterpretErrorCode::TypeError,
                format!("expected integer type, got {ty}"),
            )
        })?;
        let int = InterpretInt::from_i128(bits, signed, value).ok_or_else(|| {
            InterpretError::new(
                InterpretErrorCode::TypeError,
                format!("unsupported integer width {bits}"),
            )
        })?;
        Ok(Self {
            ty,
            kind: InterpretValueKind::Int(int),
        })
    }

    pub fn bool(value: bool) -> Self {
        Self {
            ty: Ty::Bool,
            kind: InterpretValueKind::Bool(value),
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self.kind {
            InterpretValueKind::Bool(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<InterpretInt> {
        match self.kind {
            InterpretValueKind::Int(value) => Some(value),
            _ => None,
        }
    }

    /// The lanes of a vector value (in lane order), or `None` for non-vectors.
    pub fn as_vector(&self) -> Option<&[InterpretValue]> {
        match &self.kind {
            InterpretValueKind::Vector(lanes) => Some(lanes),
            _ => None,
        }
    }
}

/// Deterministic interpreter for the bounded core subset.
#[derive(Debug, Clone, Copy)]
pub struct Interpreter<'m> {
    module: Option<&'m Module>,
    options: InterpretOptions,
}

impl<'m> Interpreter<'m> {
    pub fn new() -> Self {
        Self {
            module: None,
            options: InterpretOptions::default(),
        }
    }

    pub fn with_module(module: &'m Module) -> Self {
        Self {
            module: Some(module),
            options: InterpretOptions::default(),
        }
    }

    pub fn with_options(mut self, options: InterpretOptions) -> Self {
        self.options = options;
        self
    }

    fn pointer_bits(&self) -> u32 {
        self.module
            .and_then(|module| module.target_info.as_ref())
            .and_then(|target| target.pointer_size.checked_mul(8))
            .unwrap_or(crate::shape::DEFAULT_POINTER_BITS)
    }

    /// The executable memory model represents addresses as 64-bit lanes.
    /// Refuse a fat-pointer operation on any explicitly narrower/wider target
    /// instead of silently applying the 16-byte 64-bit layout to it.
    fn require_fat_pointer_layout(&self, block: BlockId) -> InterpretResult<()> {
        let pointer_bits = self.pointer_bits();
        let little_endian = self
            .module
            .and_then(|module| module.target_info.as_ref())
            .is_none_or(|target| target.endianness == crate::Endianness::Little);
        if pointer_bits == crate::shape::DEFAULT_POINTER_BITS && little_endian {
            Ok(())
        } else {
            Err(err(
                InterpretErrorCode::UnsupportedMemory,
                block,
                format!(
                    "fat-pointer execution is pinned to the {}-bit little-endian target; \
                     got {pointer_bits}-bit {}-endian",
                    crate::shape::DEFAULT_POINTER_BITS,
                    if little_endian { "little" } else { "big" }
                ),
            ))
        }
    }

    fn validate_fat_pointer_value(
        &self,
        kind: &crate::FatPtrKind,
        value: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<()> {
        self.require_fat_pointer_layout(block)?;
        let InterpretValueKind::FatPtr { data, metadata } = &value.kind else {
            return Err(type_error(
                block,
                format!("fat pointer type carries non-fat value {}", value.ty),
            ));
        };
        expect_ty(data, &Ty::Ptr, block)?;
        if !matches!(
            data.kind,
            InterpretValueKind::Ptr(_)
                | InterpretValueKind::NullPtr
                | InterpretValueKind::DanglingPtr(_)
        ) {
            return Err(type_error(
                block,
                "fat-pointer data lane is not a thin pointer",
            ));
        }
        let canonical = kind
            .metadata_ty(self.pointer_bits())
            .ok_or_else(|| type_error(block, format!("{} has no metadata type", value.ty)))?;
        expect_ty(metadata, &canonical, block)?;
        let metadata_shape_matches = match (&canonical, &metadata.kind) {
            (Ty::U64, InterpretValueKind::Int(int)) => int.bits == 64 && !int.signed,
            (Ty::Ptr, InterpretValueKind::Ptr(_) | InterpretValueKind::NullPtr) => true,
            _ => false,
        };
        if !metadata_shape_matches {
            return Err(type_error(
                block,
                format!("fat-pointer metadata does not inhabit canonical type {canonical}"),
            ));
        }
        Ok(())
    }

    pub fn execute_func(
        &self,
        func: FuncId,
        args: impl IntoIterator<Item = InterpretValue>,
    ) -> InterpretResult<InterpretOutcome> {
        let module = self.module.ok_or_else(|| {
            InterpretError::new(
                InterpretErrorCode::MissingFunction,
                "execute_func requires an interpreter with a module",
            )
        })?;
        let function = module.function_by_id(func).ok_or_else(|| {
            InterpretError::new(
                InterpretErrorCode::MissingFunction,
                format!("function {func} not found"),
            )
        })?;
        self.execute_function(function, args)
    }

    pub fn execute_function(
        &self,
        function: &Function,
        args: impl IntoIterator<Item = InterpretValue>,
    ) -> InterpretResult<InterpretOutcome> {
        let mut state = ExecState {
            values: BTreeMap::new(),
            memory: MemoryState::with_budget(self.options.mem_budget),
            globals: BTreeMap::new(),
            frames: BTreeMap::new(),
            next_frame_id: 0,
            steps: 0,
            remaining_fuel: self.options.fuel,
        };
        let returns = self.execute_function_inner(
            function,
            args.into_iter().collect(),
            &mut state,
            self.options.max_call_depth,
        )?;

        Ok(InterpretOutcome {
            returns,
            steps: state.steps,
        })
    }

    fn execute_function_inner(
        &self,
        function: &Function,
        args: Vec<InterpretValue>,
        state: &mut ExecState,
        call_depth: u64,
    ) -> InterpretResult<Vec<InterpretValue>> {
        self.check_function_args(function, &args, function.entry)?;
        let mut current = function.entry;
        let mut incoming = args;

        loop {
            let block = function.block(current).ok_or_else(|| {
                err(
                    InterpretErrorCode::MissingBlock,
                    current,
                    format!("block {current} not found"),
                )
            })?;
            let block_args = std::mem::take(&mut incoming);
            bind_block_params(state, block, block_args)?;

            let mut jumped = false;
            for node in &block.body {
                state.tick(block.id)?;
                match self.execute_node(block.id, node, state, call_depth)? {
                    Step::Continue => {}
                    Step::Jump { target, args } => {
                        current = target;
                        incoming = args;
                        jumped = true;
                        break;
                    }
                    Step::Return(values) => {
                        self.check_function_returns(function, &values, block.id)?;
                        return Ok(values);
                    }
                }
            }

            if !jumped {
                return Err(err(
                    InterpretErrorCode::MalformedInstruction,
                    block.id,
                    "block ended without a terminator",
                ));
            }
        }
    }

    fn execute_node(
        &self,
        block: BlockId,
        node: &InstrNode,
        state: &mut ExecState,
        call_depth: u64,
    ) -> InterpretResult<Step> {
        match &node.inst {
            Inst::Const { ty, value } => {
                let value = self.constant_to_value(ty, value, block)?;
                bind_results(state, block, node, [value])?;
                Ok(Step::Continue)
            }
            Inst::NullPtr => {
                bind_results(
                    state,
                    block,
                    node,
                    [InterpretValue {
                        ty: Ty::Ptr,
                        kind: InterpretValueKind::NullPtr,
                    }],
                )?;
                Ok(Step::Continue)
            }
            Inst::GlobalAddr { global } => {
                let pointer = self.global_pointer(*global, state, block)?;
                bind_results(
                    state,
                    block,
                    node,
                    [InterpretValue {
                        ty: Ty::Ptr,
                        kind: InterpretValueKind::Ptr(pointer),
                    }],
                )?;
                Ok(Step::Continue)
            }
            Inst::Undef { .. } => Err(err(
                InterpretErrorCode::UndefinedBehavior,
                block,
                "executing undef would read an undefined value",
            )),
            Inst::BinOp { op, ty, lhs, rhs } => {
                let lhs = state.value(block, *lhs)?;
                let rhs = state.value(block, *rhs)?;
                let result = self.eval_binop(*op, ty, lhs, rhs, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::UnOp { op, ty, operand } => {
                let operand = state.value(block, *operand)?;
                let result = self.eval_unop(*op, ty, operand, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                let lhs = state.value(block, *lhs)?;
                let rhs = state.value(block, *rhs)?;
                let (result, overflow) = self.eval_overflow(*op, ty, lhs, rhs, block)?;
                bind_results(state, block, node, [result, InterpretValue::bool(overflow)])?;
                Ok(Step::Continue)
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let lhs = state.value(block, *lhs)?;
                let rhs = state.value(block, *rhs)?;
                let result = self.eval_icmp(*op, ty, lhs, rhs, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::FCmp { op, ty, lhs, rhs } => {
                let lhs = state.value(block, *lhs)?;
                let rhs = state.value(block, *rhs)?;
                let result = self.eval_fcmp(*op, ty, lhs, rhs, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::Copy { ty, operand } => {
                let operand = state.value(block, *operand)?;
                expect_ty(operand, ty, block)?;
                bind_results(state, block, node, [operand.clone()])?;
                Ok(Step::Continue)
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                let cond = state.value(block, *cond)?;
                let then_val = state.value(block, *then_val)?;
                let else_val = state.value(block, *else_val)?;
                let result = self.eval_select(ty, cond, then_val, else_val, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => {
                let aggregate = state.value(block, *aggregate)?;
                let result = self.eval_extract_field(ty, aggregate, *field, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => {
                let aggregate = state.value(block, *aggregate)?;
                let value = state.value(block, *value)?;
                let result = self.eval_insert_field(ty, aggregate, *field, value, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::ExtractElement { ty, array, index } => {
                let array = state.value(block, *array)?;
                let index = state.value(block, *index)?;
                let result = self.eval_extract_element(ty, array, index, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::InsertElement {
                ty,
                array,
                index,
                value,
            } => {
                let array = state.value(block, *array)?;
                let index = state.value(block, *index)?;
                let value = state.value(block, *value)?;
                let result = self.eval_insert_element(ty, array, index, value, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::SeqMapAddK { ty, seq, k } => {
                // loopFwd: every element of the sequence is incremented by the constant k
                // (width-preserving wrap). The canonical forward function of `for x in
                // &mut l { *x += k }`; the give-back elaborator OBSERVES this fixed semantics.
                let seq_val = state.value(block, *seq)?;
                let elems = match &seq_val.kind {
                    InterpretValueKind::Sequence(elems) => elems.clone(),
                    _ => {
                        return Err(type_error(
                            block,
                            format!("seq_map_add_k requires a sequence, got {}", seq_val.ty),
                        ));
                    }
                };
                let mut mapped = Vec::with_capacity(elems.len());
                for e in elems {
                    match &e.kind {
                        InterpretValueKind::Int(i) => {
                            let inc =
                                InterpretInt::from_raw(i.bits, i.signed, i.raw.wrapping_add(u128::from(*k)))
                                    .ok_or_else(|| {
                                        type_error(block, "seq_map_add_k: invalid integer width")
                                    })?;
                            mapped.push(InterpretValue {
                                ty: e.ty.clone(),
                                kind: InterpretValueKind::Int(inc),
                            });
                        }
                        _ => {
                            return Err(type_error(
                                block,
                                "seq_map_add_k requires a sequence of integers",
                            ));
                        }
                    }
                }
                bind_results(
                    state,
                    block,
                    node,
                    [InterpretValue {
                        ty: ty.clone(),
                        kind: InterpretValueKind::Sequence(mapped),
                    }],
                )?;
                Ok(Step::Continue)
            }
            Inst::SeqMapNot { ty, seq } => {
                // loopFwd for the boolean-flip loop: negate (Bool.not) every element. The
                // second observable element op (self-inverse), alongside SeqMapAddK.
                let seq_val = state.value(block, *seq)?;
                let elems = match &seq_val.kind {
                    InterpretValueKind::Sequence(elems) => elems.clone(),
                    _ => {
                        return Err(type_error(
                            block,
                            format!("seq_map_not requires a sequence, got {}", seq_val.ty),
                        ));
                    }
                };
                let mut mapped = Vec::with_capacity(elems.len());
                for e in elems {
                    match &e.kind {
                        InterpretValueKind::Bool(b) => {
                            mapped.push(InterpretValue {
                                ty: e.ty.clone(),
                                kind: InterpretValueKind::Bool(!*b),
                            });
                        }
                        _ => {
                            return Err(type_error(
                                block,
                                "seq_map_not requires a sequence of booleans",
                            ));
                        }
                    }
                }
                bind_results(
                    state,
                    block,
                    node,
                    [InterpretValue {
                        ty: ty.clone(),
                        kind: InterpretValueKind::Sequence(mapped),
                    }],
                )?;
                Ok(Step::Continue)
            }
            Inst::SeqMap { ty, seq, fwd } => {
                // General element-op loopFwd: apply the element function
                // `fwd : fn(&mut elem)` to every element via the CALL MACHINERY.
                // Each element round-trips through a fresh per-element memory
                // cell (alloca -> store -> call fwd(&mut cell) -> load back).
                // ONE call-depth level bounds the WHOLE map: per-element calls
                // are sequential, so depth bounds NESTING, not sequence length
                // (mirrors the Lean SeqMapReq runner in Semantics/Eval.lean).
                let seq_val = state.value(block, *seq)?.clone();
                let elems = match &seq_val.kind {
                    InterpretValueKind::Sequence(elems) => elems.clone(),
                    _ => {
                        return Err(type_error(
                            block,
                            format!("seq_map requires a sequence, got {}", seq_val.ty),
                        ));
                    }
                };
                ensure_call_depth(block, call_depth)?;
                let module = self.module_context(block, "seq_map")?;
                let callee = module.function_by_id(*fwd).ok_or_else(|| {
                    err(
                        InterpretErrorCode::MissingFunction,
                        block,
                        format!("seq_map: undefined element function {fwd}"),
                    )
                })?;
                // The element function must be the single-&mut form
                // `fn(&mut elem)` with no returns (Aeneas forward view:
                // elem -> elem).
                let sig = self
                    .function_signature(callee, block)?
                    .expect("module-backed seq_map has function type context");
                let elem_ty = match (sig.params.as_slice(), sig.returns.as_slice()) {
                    ([Ty::RefMut(elem)], []) if !sig.is_vararg => (**elem).clone(),
                    _ => {
                        return Err(type_error(
                            block,
                            format!(
                                "seq_map: element function {} must have signature fn(&mut elem)",
                                callee.name
                            ),
                        ));
                    }
                };
                let mut mapped = Vec::with_capacity(elems.len());
                for elem in elems {
                    // Type guard (fail-closed): the element value must match
                    // the element function's pointee type.
                    if elem.ty != elem_ty {
                        return Err(type_error(
                            block,
                            format!(
                                "seq_map: element of type {} does not match the element \
                                 function's pointee type {elem_ty}",
                                elem.ty
                            ),
                        ));
                    }
                    // Per-element cell: alloc, write the element in. Internal
                    // scratch — exact-size (no heap slack).
                    let cell = self.eval_alloca(&elem_ty, None, None, state, block, false)?;
                    self.eval_store(&elem_ty, &cell, &elem, None, state, block, false)?;
                    // Call fwd(&mut cell) through the standard call machinery
                    // (argument typed as &mut elem so the signature check holds).
                    let arg = InterpretValue {
                        ty: Ty::RefMut(Box::new(elem_ty.clone())),
                        kind: cell.kind.clone(),
                    };
                    self.execute_direct_call(block, *fwd, vec![arg], state, call_depth)?;
                    // Read the mutated element back out of the cell.
                    let new_elem = self.eval_load(&elem_ty, &cell, None, state, block, false)?;
                    mapped.push(new_elem);
                }
                bind_results(
                    state,
                    block,
                    node,
                    [InterpretValue {
                        ty: ty.clone(),
                        kind: InterpretValueKind::Sequence(mapped),
                    }],
                )?;
                Ok(Step::Continue)
            }
            Inst::Assume { cond } => {
                let cond = state.value(block, *cond)?;
                reject_partial(cond, block, "assume")?;
                match cond.as_bool() {
                    Some(true) => Ok(Step::Continue),
                    Some(false) => Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        "assume condition evaluated to false",
                    )),
                    None => Err(type_error(
                        block,
                        format!("assume requires bool, got {}", cond.ty),
                    )),
                }
            }
            Inst::Assert { cond } => {
                let cond = state.value(block, *cond)?;
                reject_partial(cond, block, "assert")?;
                match cond.as_bool() {
                    Some(true) => Ok(Step::Continue),
                    Some(false) => Err(err(
                        InterpretErrorCode::Panic,
                        block,
                        "assert condition evaluated to false",
                    )),
                    None => Err(type_error(
                        block,
                        format!("assert requires bool, got {}", cond.ty),
                    )),
                }
            }
            Inst::Br { target, args } => Ok(Step::Jump {
                target: *target,
                args: eval_args(state, block, args)?,
            }),
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => {
                let cond = state.value(block, *cond)?;
                reject_partial(cond, block, "cond_br")?;
                match cond.as_bool() {
                    Some(true) => Ok(Step::Jump {
                        target: *then_target,
                        args: eval_args(state, block, then_args)?,
                    }),
                    Some(false) => Ok(Step::Jump {
                        target: *else_target,
                        args: eval_args(state, block, else_args)?,
                    }),
                    None => Err(type_error(
                        block,
                        format!("cond_br requires bool, got {}", cond.ty),
                    )),
                }
            }
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                ..
            } => {
                let value = state.value(block, *value)?;
                reject_partial(value, block, "switch")?;
                for case in cases {
                    let case_value = self.constant_to_value(&value.ty, &case.value, block)?;
                    if &case_value == value {
                        return Ok(Step::Jump {
                            target: case.target,
                            args: eval_args(state, block, &case.args)?,
                        });
                    }
                }
                Ok(Step::Jump {
                    target: *default,
                    args: eval_args(state, block, default_args)?,
                })
            }
            Inst::Return { values } => Ok(Step::Return(eval_args(state, block, values)?)),
            Inst::CoroSuspend {
                frame,
                state_slot,
                next_state,
                value,
            } => {
                // Save the resume state index into frame[state_slot] (an I64
                // element), then return the yielded value — exactly the
                // store(state)+return(value) sequence backends macro-expand to.
                let frame_ptr = state.value(block, *frame)?.clone();
                let slot_index = InterpretValue::int(Ty::I64, i128::from(*state_slot))
                    .map_err(|e| e.with_block(block))?;
                let slot_ptr =
                    self.eval_gep(&Ty::I64, &frame_ptr, std::slice::from_ref(&slot_index), block)?;
                let next = InterpretValue::int(Ty::I64, i128::from(*next_state))
                    .map_err(|e| e.with_block(block))?;
                self.eval_store(&Ty::I64, &slot_ptr, &next, None, state, block, false)?;
                let yielded = state.value(block, *value)?.clone();
                Ok(Step::Return(vec![yielded]))
            }
            Inst::Unreachable => Err(err(
                InterpretErrorCode::UndefinedBehavior,
                block,
                "executed unreachable",
            )),
            Inst::Call { callee, args } => {
                let args = eval_args(state, block, args)?;
                let returns = self.execute_direct_call(block, *callee, args, state, call_depth)?;
                bind_results(state, block, node, returns)?;
                Ok(Step::Continue)
            }
            Inst::Invoke {
                callee,
                args,
                normal_dest,
                normal_args,
                unwind_dest: _,
            } => {
                // The interpreter models "the callee returns normally" (it does
                // not raise host exceptions), so an invoke runs the call exactly
                // like `Inst::Call` and always takes the NORMAL edge; the
                // `unwind_dest` landing pad is unreachable under interpretation.
                // The callee's return values bind the invoke's own `node.results`
                // (the same shape as `Inst::Call`), and control then jumps to
                // `normal_dest` passing `normal_args`. This is sound for the
                // non-throwing case the end-to-end harness exercises.
                let call_args = eval_args(state, block, args)?;
                let returns =
                    self.execute_direct_call(block, *callee, call_args, state, call_depth)?;
                bind_results(state, block, node, returns)?;
                let edge_args = eval_args(state, block, normal_args)?;
                Ok(Step::Jump {
                    target: *normal_dest,
                    args: edge_args,
                })
            }
            Inst::LandingPad {
                is_cleanup: _,
                catch_type_indices: _,
            } => {
                // A landing pad is only entered via an `Invoke`'s unwind edge,
                // which interpretation never takes (it models no thrown
                // exception). If reached directly it yields a NULL exception
                // pointer and a zero type selector — the produced values are
                // unobservable because the pad is unreachable under
                // interpretation, but binding them keeps the interpreter total.
                let exn_ptr = InterpretValue {
                    ty: Ty::Ptr,
                    kind: InterpretValueKind::NullPtr,
                };
                let selector = InterpretValue::int(Ty::I32, 0).map_err(|e| e.with_block(block))?;
                bind_results(state, block, node, [exn_ptr, selector])?;
                Ok(Step::Continue)
            }
            Inst::Resume { exn: _ } => {
                // `Resume` re-raises an in-flight exception to the host
                // unwinder. The interpreter does not model host unwinding, and a
                // resume is only reachable after an unwind edge has been taken
                // (which never happens here), so reaching it is undefined under
                // interpretation.
                Err(err(
                    InterpretErrorCode::UnsupportedInstruction,
                    block,
                    "resume: the interpreter does not model in-flight host exceptions",
                ))
            }
            Inst::CallIndirect {
                callee, sig, args, ..
            } => {
                let callee = state.value(block, *callee)?.clone();
                let args = eval_args(state, block, args)?;
                let returns =
                    self.execute_indirect_call(block, &callee, *sig, args, state, call_depth)?;
                bind_results(state, block, node, returns)?;
                Ok(Step::Continue)
            }
            Inst::Load {
                ty,
                ptr,
                volatile,
                align,
            } => {
                let ptr = state.value(block, *ptr)?.clone();
                // A volatile load keeps the strict all-initialized discipline; a
                // plain load participates in copy-propagates-poison.
                let result = self.eval_load(ty, &ptr, *align, state, block, *volatile)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            } => {
                let ptr = state.value(block, *ptr)?.clone();
                let value = state.value(block, *value)?.clone();
                self.eval_store(ty, &ptr, &value, *align, state, block, *volatile)?;
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            Inst::Alloca { ty, count, align } => {
                let count = count
                    .map(|count| state.value(block, count).cloned())
                    .transpose()?;
                // Stack allocation: exact-size bounds (no heap usable-size slack).
                let result = self.eval_alloca(ty, count.as_ref(), *align, state, block, false)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::HeapAlloc {
                ty,
                count,
                align,
                origin: _,
            } => {
                // Single-threaded model: a heap region is allocated like a stack
                // region but WITH a readable usable-size slack tail (see
                // `eval_alloca`'s `heap` path) — the model of `__rust_alloc`'s
                // over-allocation that hashbrown's group scan reads into. The
                // `origin` rides in the IR for the backend and the (deferred)
                // Dealloc origin check. Double-free / use-after-free are already
                // caught by the shared allocator.
                let count = count
                    .map(|count| state.value(block, count).cloned())
                    .transpose()?;
                let result = self.eval_alloca(ty, count.as_ref(), *align, state, block, true)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                .. // inbounds: backend optimization hint, no runtime effect
            } => {
                let base = state.value(block, *base)?.clone();
                let indices = eval_args(state, block, indices)?;
                let result = self.eval_gep(pointee_ty, &base, &indices, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::PtrData { ptr_ty, ptr } => {
                let ptr = state.value(block, *ptr)?;
                let result = self.eval_ptr_data(ptr_ty, ptr, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            } => {
                let ptr = state.value(block, *ptr)?;
                let result = self.eval_ptr_metadata(ptr_ty, metadata_ty, ptr, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            } => {
                let data = state.value(block, *data)?;
                let metadata = state.value(block, *metadata)?;
                let result =
                    self.eval_ptr_from_parts(ptr_ty, metadata_ty, data, metadata, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::Dealloc { ptr } => {
                let ptr = state.value(block, *ptr)?.clone();
                self.eval_dealloc(&ptr, state, block)?;
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            // Atomics — single-threaded reference model: with one thread every
            // memory ordering collapses to sequential consistency, so an atomic
            // access is its plain-memory counterpart and a Fence is a no-op.
            // (The multi-thread happens-before model lives in the Lean
            // semantics; this is the executable single-thread reference.)
            Inst::AtomicLoad { ty, ptr, .. } => {
                let ptr = state.value(block, *ptr)?.clone();
                let result = self.eval_load(ty, &ptr, None, state, block, true)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::AtomicStore {
                ty, ptr, value, ..
            } => {
                let ptr = state.value(block, *ptr)?.clone();
                let value = state.value(block, *value)?.clone();
                self.eval_store(ty, &ptr, &value, None, state, block, true)?;
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            Inst::AtomicRMW {
                op, ty, ptr, value, ..
            } => {
                let ptr = state.value(block, *ptr)?.clone();
                let operand = state.value(block, *value)?.clone();
                // Read old, compute new = old <op> operand, write back, return old.
                let old = self.eval_load(ty, &ptr, None, state, block, true)?;
                let new = self.eval_atomic_rmw(*op, ty, &old, &operand, block)?;
                self.eval_store(ty, &ptr, &new, None, state, block, true)?;
                bind_results(state, block, node, [old])?;
                Ok(Step::Continue)
            }
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                ..
            } => {
                let ptr = state.value(block, *ptr)?.clone();
                let expected = state.value(block, *expected)?.clone();
                let desired = state.value(block, *desired)?.clone();
                let current = self.eval_load(ty, &ptr, None, state, block, true)?;
                let success = current == expected;
                if success {
                    self.eval_store(ty, &ptr, &desired, None, state, block, true)?;
                }
                // Result is (loaded_value, success_bool), matching LLVM cmpxchg.
                bind_results(state, block, node, [current, InterpretValue::bool(success)])?;
                Ok(Step::Continue)
            }
            Inst::Fence { .. } => {
                // No observable effect in the single-threaded reference model.
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            Inst::DialectOp(op) => {
                let values = self.eval_dialect_op(op, state, block)?;
                bind_results(state, block, node, values)?;
                Ok(Step::Continue)
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let operand = state.value(block, *operand)?.clone();
                let result = self.eval_cast(*op, src_ty, dst_ty, &operand, state, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            // Borrow / BorrowMut produce a reference to the pointee place: at
            // runtime a reference IS the pointer's address, so a borrow yields
            // the same pointer value. This sequential reference interpreter does
            // not enforce borrow-checking (that is the validator's / the formal
            // BorrowProps model's job); it must agree on the runtime value, and
            // the address of `&x`/`&mut x` is the address of `x`. EndBorrow ends
            // the lexical region and has no runtime value.
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                let pointee = state.value(block, *ptr)?.clone();
                // A Borrow over a FAT pointer value is the same pure
                // pass-through as over a thin one: a reborrow of a fat pointer
                // (`&*p` for `p: &str` / `&[T]` / `&dyn Tr`) is the identity
                // on the (data, metadata) pair. The value is passed through
                // VERBATIM — same ty, both lanes untouched. Neither lane is
                // read or re-validated here: a `FatPtr` value is validated at
                // every construction site (`eval_ptr_from_parts` /
                // `decode_value`), and this arm constructs nothing.
                let result = if matches!(pointee.kind, InterpretValueKind::FatPtr { .. }) {
                    pointee
                } else {
                    let ptr = expect_pointer(&pointee, block, "Borrow")?;
                    InterpretValue {
                        ty: Ty::Ptr,
                        kind: InterpretValueKind::Ptr(ptr),
                    }
                };
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::EndBorrow { .. } => {
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            // ARC reference counting (single-threaded exact counts).
            Inst::Retain { ptr } => {
                let ptr = expect_pointer(state.value(block, *ptr)?, block, "Retain")?;
                state.memory.retain(ptr, block)?;
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            Inst::Release { ptr } => {
                let ptr = expect_pointer(state.value(block, *ptr)?, block, "Release")?;
                state.memory.release(ptr, block)?;
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            Inst::IsUnique { ptr } => {
                let ptr = expect_pointer(state.value(block, *ptr)?, block, "IsUnique")?;
                let unique = state.memory.is_unique(ptr, block)?;
                bind_results(state, block, node, [InterpretValue::bool(unique)])?;
                Ok(Step::Continue)
            }
            // Binding frames — typed scoped slot arrays for quantifier lowering.
            Inst::OpenFrame { def } => {
                let id = state.next_frame_id;
                state.next_frame_id = id
                    .checked_add(1)
                    .ok_or_else(|| ub(block, "OpenFrame: frame id overflow"))?;
                state.frames.insert(id, vec![None; def.slots.len()]);
                let handle = InterpretValue {
                    ty: Ty::Unit,
                    kind: InterpretValueKind::Frame(id),
                };
                bind_results(state, block, node, [handle])?;
                Ok(Step::Continue)
            }
            Inst::BindSlot {
                frame,
                slot,
                value,
            } => {
                let id = expect_frame(state.value(block, *frame)?, block)?;
                let value = state.value(block, *value)?.clone();
                let slots = state
                    .frames
                    .get_mut(&id)
                    .ok_or_else(|| ub(block, "BindSlot: frame is not open"))?;
                let slot_idx = *slot as usize;
                if slot_idx >= slots.len() {
                    return Err(ub(
                        block,
                        format!("BindSlot: slot {slot} out of range for frame of {} slots", slots.len()),
                    ));
                }
                slots[slot_idx] = Some(value);
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            Inst::LoadSlot { frame, slot, ty } => {
                let id = expect_frame(state.value(block, *frame)?, block)?;
                let slots = state
                    .frames
                    .get(&id)
                    .ok_or_else(|| ub(block, "LoadSlot: frame is not open"))?;
                let slot_idx = *slot as usize;
                let value = slots
                    .get(slot_idx)
                    .ok_or_else(|| {
                        ub(
                            block,
                            format!("LoadSlot: slot {slot} out of range for frame of {} slots", slots.len()),
                        )
                    })?
                    .clone()
                    .ok_or_else(|| ub(block, format!("LoadSlot: slot {slot} read before bound")))?;
                expect_ty(&value, ty, block)?;
                bind_results(state, block, node, [value])?;
                Ok(Step::Continue)
            }
            Inst::CloseFrame { frame } => {
                let id = expect_frame(state.value(block, *frame)?, block)?;
                if state.frames.remove(&id).is_none() {
                    return Err(ub(block, "CloseFrame: frame is not open (double close)"));
                }
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
        }
    }

    fn execute_direct_call(
        &self,
        block: BlockId,
        callee: FuncId,
        args: Vec<InterpretValue>,
        state: &mut ExecState,
        call_depth: u64,
    ) -> InterpretResult<Vec<InterpretValue>> {
        ensure_call_depth(block, call_depth)?;
        let module = self.module_context(block, "direct call")?;
        let callee_function = module.function_by_id(callee).ok_or_else(|| {
            err(
                InterpretErrorCode::MissingFunction,
                block,
                format!("Call: undefined function {callee}"),
            )
        })?;
        self.check_function_args(callee_function, &args, block)?;
        self.execute_callee(block, callee_function, args, state, call_depth)
    }

    fn execute_indirect_call(
        &self,
        block: BlockId,
        callee: &InterpretValue,
        sig: FuncTyId,
        args: Vec<InterpretValue>,
        state: &mut ExecState,
        call_depth: u64,
    ) -> InterpretResult<Vec<InterpretValue>> {
        let value_sig = match &callee.ty {
            Ty::Func(sig) => *sig,
            _ => {
                return Err(invalid_function_pointer(
                    block,
                    format!("CallIndirect: callee has non-function type {}", callee.ty),
                ));
            }
        };
        if value_sig != sig {
            return Err(signature_mismatch(
                block,
                format!(
                    "CallIndirect: callee value has signature functy.{}, call expects functy.{}",
                    value_sig.0, sig.0
                ),
            ));
        }
        let pointer = match &callee.kind {
            InterpretValueKind::FnDef(func) => *func,
            InterpretValueKind::NullPtr => {
                return Err(invalid_function_pointer(
                    block,
                    "CallIndirect: null function pointer",
                ));
            }
            _ => {
                return Err(invalid_function_pointer(
                    block,
                    format!(
                        "CallIndirect: callee is not a function pointer ({})",
                        callee.ty
                    ),
                ));
            }
        };

        ensure_call_depth(block, call_depth)?;
        let module = self.module_context(block, "indirect call")?;
        let expected_sig = module.func_type(sig).ok_or_else(|| {
            signature_mismatch(
                block,
                format!("CallIndirect: undefined function type functy.{}", sig.0),
            )
        })?;
        if expected_sig.is_vararg {
            return Err(signature_mismatch(
                block,
                format!(
                    "CallIndirect: vararg signature functy.{} is not executable",
                    sig.0
                ),
            ));
        }

        let callee_id = self.function_pointer_target(module, pointer, block)?;
        let callee_function = module.function_by_id(callee_id).ok_or_else(|| {
            err(
                InterpretErrorCode::MissingFunction,
                block,
                format!("CallIndirect: undefined function {callee_id}"),
            )
        })?;
        let callee_sig = self
            .function_signature(callee_function, block)?
            .expect("module-backed call has function type context");
        if callee_sig.is_vararg
            || expected_sig.params != callee_sig.params
            || expected_sig.returns != callee_sig.returns
        {
            return Err(signature_mismatch(
                block,
                format!("CallIndirect: indirect call signature mismatch for function {callee_id}"),
            ));
        }

        check_signature_values(block, "CallIndirect arguments", &args, &expected_sig.params)?;
        self.execute_callee(block, callee_function, args, state, call_depth)
    }

    fn execute_callee(
        &self,
        block: BlockId,
        callee: &Function,
        args: Vec<InterpretValue>,
        state: &mut ExecState,
        call_depth: u64,
    ) -> InterpretResult<Vec<InterpretValue>> {
        ensure_call_depth(block, call_depth)?;

        let caller_values = std::mem::take(&mut state.values);
        let result = self.execute_function_inner(callee, args, state, call_depth - 1);
        state.values = caller_values;
        result
    }

    fn module_context(&self, block: BlockId, purpose: &str) -> InterpretResult<&'m Module> {
        self.module.ok_or_else(|| {
            err(
                InterpretErrorCode::MissingFunction,
                block,
                format!("{purpose} requires an interpreter with a module"),
            )
        })
    }

    fn function_pointer_target(
        &self,
        module: &Module,
        pointer: FuncId,
        block: BlockId,
    ) -> InterpretResult<FuncId> {
        if module.function_by_id(pointer).is_some() {
            Ok(pointer)
        } else {
            Err(invalid_function_pointer(
                block,
                format!("CallIndirect: invalid function pointer {pointer}"),
            ))
        }
    }

    fn function_signature(
        &self,
        function: &Function,
        block: BlockId,
    ) -> InterpretResult<Option<&'m FuncTy>> {
        let Some(module) = self.module else {
            return Ok(None);
        };
        module.func_type(function.ty).map(Some).ok_or_else(|| {
            signature_mismatch(
                block,
                format!(
                    "function {} references undefined signature functy.{}",
                    function.id.0, function.ty.0
                ),
            )
        })
    }

    fn check_function_args(
        &self,
        function: &Function,
        args: &[InterpretValue],
        block: BlockId,
    ) -> InterpretResult<()> {
        let Some(sig) = self.function_signature(function, block)? else {
            return Ok(());
        };
        if sig.is_vararg {
            return Err(signature_mismatch(
                block,
                format!(
                    "function {} has non-executable vararg signature",
                    function.id.0
                ),
            ));
        }
        check_signature_values(block, "Call arguments", args, &sig.params)
    }

    fn check_function_returns(
        &self,
        function: &Function,
        returns: &[InterpretValue],
        block: BlockId,
    ) -> InterpretResult<()> {
        let Some(sig) = self.function_signature(function, block)? else {
            return Ok(());
        };
        check_signature_values(block, "Call returns", returns, &sig.returns)
    }

    fn constant_to_value(
        &self,
        ty: &Ty,
        value: &Constant,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        match (ty, value) {
            (ty, Constant::Int(value)) if int_shape(ty).is_some() => {
                InterpretValue::int(ty.clone(), *value).map_err(|e| e.with_block(block))
            }
            // THE NULL POINTER CONSTANT. `shape_matches_ty` has admitted
            // `(Constant::Int(_), Ty::Ptr)` since the initial commit
            // (`shape.rs`), so this pairing is already encodable, already
            // validator-accepted, and already present in the on-disk format —
            // but the interpreter had no arm for it, and `int_shape(Ty::Ptr)`
            // is `None`, so it fell through to the type-error arm below. That
            // was a genuine disagreement between two authorities about what
            // inhabits `Ty::Ptr`, with the VALIDATOR as the loose side. This
            // arm removes the disagreement rather than widening the format:
            // no new constructor, no new `Ty`, no serialised-shape change.
            //
            // ZERO ONLY, and the restriction is the whole point. A NONZERO
            // integer at `Ty::Ptr` would be a fabricated address with no
            // provenance and no allocation behind it; it stays fail-closed on
            // the type-error arm (`a_nonzero_int_at_ptr_is_still_a_type_error`).
            // Zero is different in kind: `InterpretValueKind::NullPtr` is a
            // DISTINGUISHED, already-modelled value — `Inst::NullPtr` produces
            // exactly this, and the type relation already admits it at
            // `Ty::Ptr` (`(Ty::Ptr, Ptr(_) | NullPtr) => true`). So this mints
            // no new value kind either; it only lets a constant reach one that
            // an instruction could already produce.
            //
            // SOUND UNDER THE DIFFERENTIAL GATE, which is why this pairing and
            // not `SymbolAddr`. `constant_materializes_uncomparable_identity`
            // classifies `Constant::Int(_)` as comparable
            // (`trust-thir-lower/src/differential.rs`), so a body seeded this
            // way stays gate-comparable — whereas `SymbolAddr`/`FnDef`/
            // `Closure` are module/linker-local identities the gate refuses
            // syntactically, and an interpreter arm for those would buy no
            // verdicts without first deleting that refusal, which is the
            // unsound step. Every observation channel for a null is LOUD: a
            // deref faults in `expect_pointer`, and a returned `NullPtr`
            // against the oracle's `Ptr(..)` is a cross-kind pair reported as
            // a real divergence. A placeholder that is silently wrong is the
            // hazard; this one cannot be silently anything.
            (Ty::Ptr, Constant::Int(0)) => Ok(InterpretValue {
                ty: Ty::Ptr,
                kind: InterpretValueKind::NullPtr,
            }),
            // v24: a canonical U128 constant (value > i128::MAX) is only
            // faithfully representable at width 128 - narrower declared
            // types fall through to the type-error arm (fail closed).
            (Ty::U128, Constant::U128(value)) => {
                let int = InterpretInt::from_raw(128, false, *value).ok_or_else(|| {
                    err(
                        InterpretErrorCode::TypeError,
                        block,
                        "u128 constant width unsupported".to_string(),
                    )
                })?;
                Ok(InterpretValue {
                    ty: Ty::U128,
                    kind: InterpretValueKind::Int(int),
                })
            }
            (Ty::Bool, Constant::Bool(value)) => Ok(InterpretValue::bool(*value)),
            (Ty::F16 | Ty::F32 | Ty::F64, Constant::Float(value)) => Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::FloatBits(float_bits_from_f64(ty, *value, block)?),
            }),
            (Ty::Vector(elem_ty, lanes), Constant::Vector(values)) => {
                if *lanes == 0 || values.len() != *lanes as usize {
                    return Err(err(
                        InterpretErrorCode::UnsupportedVectorShape,
                        block,
                        format!(
                            "vector constant has {} lanes, declared type requires {lanes}",
                            values.len()
                        ),
                    ));
                }
                let lanes = values
                    .iter()
                    .map(|v| self.constant_to_value(elem_ty, v, block))
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Vector(lanes),
                })
            }
            (Ty::Tuple(elem_tys), Constant::Aggregate(values)) => {
                if elem_tys.len() != values.len() {
                    return Err(type_error(
                        block,
                        format!(
                            "tuple constant has {} fields, declared type requires {}",
                            values.len(),
                            elem_tys.len()
                        ),
                    ));
                }
                let values = elem_tys
                    .iter()
                    .zip(values)
                    .map(|(ty, value)| self.constant_to_value(ty, value, block))
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            // A struct-typed aggregate constant is the positional counterpart
            // of the tuple arm above: field types are resolved from the
            // module's `StructDef` (declaration order), each field constant is
            // converted recursively (nested structs/tuples included), and the
            // result is the same in-register `Aggregate` value a struct built
            // via `InsertField` would produce — so struct constants flow
            // through `ExtractField`/`Store`/`Load` identically. Arity or
            // per-field type mismatches fail closed via the recursive
            // conversion, never a mis-typed value.
            (Ty::Struct(sid), Constant::Aggregate(values)) => {
                let module = self.module.ok_or_else(|| {
                    err(
                        InterpretErrorCode::TypeError,
                        block,
                        "struct constants require module type context",
                    )
                })?;
                let def = module.struct_def(*sid).ok_or_else(|| {
                    type_error(block, format!("struct id {} not found in module", sid.0))
                })?;
                if def.fields.len() != values.len() {
                    return Err(type_error(
                        block,
                        format!(
                            "struct constant has {} fields, declared type {} requires {}",
                            values.len(),
                            ty,
                            def.fields.len()
                        ),
                    ));
                }
                let values = def
                    .fields
                    .iter()
                    .zip(values)
                    .map(|(field, value)| self.constant_to_value(&field.ty, value, block))
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            // An enum-typed aggregate constant follows the tag + payload
            // convention (the existing `Constant::Aggregate` pattern, no new
            // codec surface): element 0 is the discriminant VALUE
            // (`Constant::Int`, matched against the variants' effective
            // discriminants), the remaining elements are the selected
            // variant's fields in order. The result is an in-register
            // `Aggregate([tag, fields...])` whose tag lane has the canonical
            // tag type, so it stores/loads through the tagged-union memory
            // layout and the tag extracts positionally as field 0.
            (Ty::Enum(_), Constant::Aggregate(values)) => {
                let layout = self.enum_layout(ty, block)?;
                let Some((tag_const, field_consts)) = values.split_first() else {
                    return Err(type_error(
                        block,
                        format!("enum constant for {ty} needs a leading discriminant element"),
                    ));
                };
                let Constant::Int(disc) = tag_const else {
                    return Err(type_error(
                        block,
                        format!(
                            "enum constant discriminant must be an integer constant, got {tag_const:?}"
                        ),
                    ));
                };
                let variant_idx = layout.variant_by_discriminant(*disc).ok_or_else(|| {
                    type_error(
                        block,
                        format!("discriminant {disc} does not name a variant of {ty}"),
                    )
                })?;
                let fields = &layout.variant_field_offsets[variant_idx];
                if field_consts.len() != fields.len() {
                    return Err(type_error(
                        block,
                        format!(
                            "enum constant has {} payload fields, variant {} of {} requires {}",
                            field_consts.len(),
                            variant_idx,
                            ty,
                            fields.len()
                        ),
                    ));
                }
                let mut converted = Vec::with_capacity(values.len());
                converted.push(
                    InterpretValue::int(layout.tag_ty.clone(), *disc)
                        .map_err(|e| e.with_block(block))?,
                );
                for ((_, field_ty), value) in fields.iter().zip(field_consts) {
                    converted.push(self.constant_to_value(field_ty, value, block)?);
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(converted),
                })
            }
            // v25 Bytes: the byte-array payload — executable as an Array of
            // U8 ints when the declared element type IS U8 (anything else is
            // malformed; the validator rejects it — fail closed here too).
            (Ty::Array(elem, len), Constant::Bytes { data, .. }) => {
                if data.len() != *len as usize {
                    return Err(type_error(
                        block,
                        format!(
                            "bytes constant has {} bytes, declared type requires {len}",
                            data.len()
                        ),
                    ));
                }
                let elem_ty = self.resolve_ty(*elem, block)?;
                if elem_ty != Ty::U8 {
                    return Err(type_error(
                        block,
                        format!(
                            "bytes constant requires a [u8; N] declared type, got element {elem_ty}"
                        ),
                    ));
                }
                let values = data
                    .iter()
                    .map(|b| InterpretValue::int(Ty::U8, *b as i128))
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Array(values),
                })
            }
            (Ty::Array(elem, len), Constant::Array(values)) => {
                if values.len() != *len as usize {
                    return Err(type_error(
                        block,
                        format!(
                            "array constant has {} elements, declared type requires {len}",
                            values.len()
                        ),
                    ));
                }
                let elem_ty = self.resolve_ty(*elem, block)?;
                let values = values
                    .iter()
                    .map(|value| self.constant_to_value(&elem_ty, value, block))
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Array(values),
                })
            }
            (Ty::Sequence(elem), Constant::Sequence(values)) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                let values = values
                    .iter()
                    .map(|value| self.constant_to_value(&elem_ty, value, block))
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Sequence(values),
                })
            }
            (Ty::Set(elem, _), Constant::Set(values)) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                let values = values
                    .iter()
                    .map(|value| self.constant_to_value(&elem_ty, value, block))
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Set(values),
                })
            }
            (Ty::Record(record_id), Constant::Record(fields)) => {
                let module = self.module.ok_or_else(|| {
                    err(
                        InterpretErrorCode::TypeError,
                        block,
                        "record constants require module type context",
                    )
                })?;
                let record = module.record_def(*record_id).ok_or_else(|| {
                    type_error(block, format!("record definition {record_id} not found"))
                })?;
                if fields.len() != record.fields.len() {
                    return Err(type_error(
                        block,
                        format!(
                            "record constant has {} fields, declared type requires {}",
                            fields.len(),
                            record.fields.len()
                        ),
                    ));
                }
                let mut values = Vec::with_capacity(fields.len());
                for (name, value) in fields {
                    let field = record
                        .fields
                        .iter()
                        .find(|field| field.name == *name)
                        .ok_or_else(|| {
                            type_error(block, format!("record field {name} not declared"))
                        })?;
                    values.push((
                        name.clone(),
                        self.constant_to_value(&field.ty, value, block)?,
                    ));
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Record(values),
                })
            }
            (Ty::Closure(closure_id), Constant::Closure { func, captures }) => {
                let module = self.module.ok_or_else(|| {
                    err(
                        InterpretErrorCode::TypeError,
                        block,
                        "closure constants require module type context",
                    )
                })?;
                let closure_ty = module.closure_type(*closure_id).ok_or_else(|| {
                    type_error(block, format!("closure type {closure_id} not found"))
                })?;
                if captures.len() != closure_ty.captures.len() {
                    return Err(type_error(
                        block,
                        format!(
                            "closure constant has {} captures, declared type requires {}",
                            captures.len(),
                            closure_ty.captures.len()
                        ),
                    ));
                }
                let captures = closure_ty
                    .captures
                    .iter()
                    .zip(captures)
                    .map(|(ty, value)| self.constant_to_value(ty, value, block))
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Closure {
                        func: *func,
                        captures,
                    },
                })
            }
            (Ty::Func(_), Constant::FnDef(func)) => Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::FnDef(*func),
            }),
            // `Constant::PhantomData` is the canonical constant spelling for
            // `Ty::Unit` (there is no separate `Constant::Unit`).  Materialize
            // that pair as the interpreter's real unit value so it remains
            // encodable by `Store` and round-trips through memory.  Retain the
            // generic phantom marker for any non-Unit metadata use.
            (Ty::Unit, Constant::PhantomData) => Ok(InterpretValue {
                ty: Ty::Unit,
                kind: InterpretValueKind::Unit,
            }),
            (_, Constant::PhantomData) => Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::PhantomData,
            }),
            _ => Err(type_error(
                block,
                format!("constant {value:?} does not match declared type {ty}"),
            )),
        }
    }

    fn resolve_ty(&self, id: TyId, block: BlockId) -> InterpretResult<Ty> {
        let module = self.module.ok_or_else(|| {
            err(
                InterpretErrorCode::TypeError,
                block,
                "TyId-backed aggregate constants require module type context",
            )
        })?;
        module
            .ty(id)
            .cloned()
            .ok_or_else(|| type_error(block, format!("type id {id} not found")))
    }

    /// Resolve a module global to a backing pointer, lazily allocating its
    /// storage on first use and writing its initializer (if present). Repeated
    /// `GlobalAddr` of the same global returns the cached pointer so they alias.
    fn global_pointer(
        &self,
        global: GlobalId,
        state: &mut ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretPointer> {
        if let Some(pointer) = state.globals.get(&global) {
            return Ok(*pointer);
        }
        let module = self.module_context(block, "GlobalAddr")?;
        let def = module.globals.get(global.as_usize()).ok_or_else(|| {
            err(
                InterpretErrorCode::MissingValue,
                block,
                format!("GlobalAddr: global #{} is out of range", global.index()),
            )
        })?;
        let size = self.byte_size(&def.ty, block)?;
        // Placement alignment for the global's backing allocation. A global's
        // `Ty` is frequently a BYTE-IMAGE lowering (`Array(U8, N)`) that
        // UNDER-reports its real alignment as 1 — e.g. the RandomState KEYS
        // `(u64,u64)` thread-local, whose `keys.0` is later read with a
        // natural-align-8 `load u64`. Placing such a global on an odd base makes
        // that legitimate aligned load spuriously fault. Model the object file's
        // section alignment as a sound OVER-approximation: the max of the type's
        // natural alignment, any DECLARED over-alignment (`GlobalDef.align` — the
        // producer's `#[repr(align)]` / SIMD-static channel), and a conservative
        // floor of the target's maximum fundamental (`max_align_t`) alignment.
        // Over-alignment is always sound: a program can never require a global to
        // be UNDER-aligned, and it does not observe a global's absolute low bits,
        // so a more-aligned base only ever admits more valid accesses — it never
        // changes a computed value. (Scoped to globals; `Alloca`/`HeapAlloc`
        // already honor their own explicit `align`.)
        const GLOBAL_SECTION_ALIGN: u64 = 16;
        let natural = self.byte_align(&def.ty, block)?;
        let declared = def
            .align
            .map(u64::from)
            .filter(|a| a.is_power_of_two())
            .unwrap_or(1);
        let align = natural.max(declared).max(GLOBAL_SECTION_ALIGN);
        let pointer = state.memory.alloc(size, align, block)?;
        if let Some(init) = &def.initializer {
            let value = self.constant_to_value(&def.ty, init, block)?;
            let bytes = self.encode_value(&value, state, block)?;
            state
                .memory
                .write(pointer, &bytes, align, block, "GlobalAddr")?;
        } else {
            // A NO-INITIALIZER global is BSS / `.tbss` (a writable or thread-local
            // static with no explicit initializer, or one initialized to all
            // zeros): the loader ZERO-FILLS its backing store — it is never
            // uninitialized at first access. Model that here so a load of such a
            // static reads a defined zero, not poison. (Example: the RandomState
            // hash-seed thread-local `Storage`, whose `State` discriminant byte is
            // zero-initialized to `Uninitialized` and switched on in `get_or_init`.)
            // Deliberately scoped to GLOBALS only — stack `Alloca` / `HeapAlloc`
            // stay uninitialized so genuine use-of-uninit UB is still caught.
            state.memory.write(
                pointer,
                &vec![0u8; size as usize],
                align,
                block,
                "GlobalAddr",
            )?;
        }
        state.globals.insert(global, pointer);
        Ok(pointer)
    }

    fn eval_alloca(
        &self,
        ty: &Ty,
        count: Option<&InterpretValue>,
        align: Option<u64>,
        state: &mut ExecState,
        block: BlockId,
        heap: bool,
    ) -> InterpretResult<InterpretValue> {
        let elem_size = self.byte_size(ty, block)?;
        let count = match count {
            Some(value) => {
                let int = expect_int_value(value, block)?;
                if int.signed && int.as_signed() <= 0 {
                    return Err(ub(block, "Alloca: count must be positive"));
                }
                if !int.signed && int.as_unsigned() == 0 {
                    return Err(ub(block, "Alloca: count must be positive"));
                }
                u64::try_from(int.as_unsigned()).map_err(|_| {
                    ub(
                        block,
                        format!("Alloca: count {} does not fit u64", int.as_unsigned()),
                    )
                })?
            }
            None => 1,
        };
        let size = elem_size
            .checked_mul(count)
            .ok_or_else(|| ub(block, "Alloca: allocation size overflow"))?;
        let natural_align = self.byte_align(ty, block)?;
        let align = checked_align(align.unwrap_or(natural_align), block)?;
        // HEAP allocations (`__rust_alloc` / `HeapAlloc`) get a readable,
        // defined usable-size slack tail so hashbrown's SIMD control-byte group
        // scan — which reads a full `Group` up to `Group::WIDTH` bytes past the
        // logical `ctrl` array — lands in modeled allocator slack instead of
        // faulting, exactly as it does against a real allocator. `Group::WIDTH`
        // is 8 (NEON `uint8x8_t`) or 16 (SSE2 `__m128i`); pad by 16 to cover the
        // widest group. STACK `Alloca` and globals get NO slack (exact bounds),
        // so their OOB/uninit detection is unchanged.
        const HEAP_USABLE_SLACK: u64 = 16;
        let slack = if heap { HEAP_USABLE_SLACK } else { 0 };
        let pointer = state.memory.alloc_with_slack(size, align, slack, block)?;
        Ok(InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::Ptr(pointer),
        })
    }

    /// Load a value of `ty` from `ptr`.
    ///
    /// `strict` selects the initialization discipline. A `strict` load (atomic
    /// or volatile) requires EVERY byte of the access to be initialized — an
    /// uninitialized byte is undefined behaviour, surfaced with its exact
    /// offset. A non-strict (plain) scalar load implements copy-propagates-
    /// poison: if the byte range has any uninitialized byte it yields an inert
    /// `PartialBytes` transport value instead of faulting, so a whole-lane
    /// aggregate copy that reads padding or an inactive niche payload can move
    /// those bytes verbatim to their destination. The value only faults if it
    /// is later INSPECTED (see `reject_partial`).
    fn eval_load(
        &self,
        ty: &Ty,
        ptr: &InterpretValue,
        align: Option<u64>,
        state: &ExecState,
        block: BlockId,
        strict: bool,
    ) -> InterpretResult<InterpretValue> {
        let size = self.byte_size(ty, block)?;
        let natural_align = self.byte_align(ty, block)?;
        let align = checked_align(align.unwrap_or(natural_align), block)?;
        let ptr = expect_pointer(ptr, block, "Load")?;
        if strict {
            let bytes = state.memory.read(ptr, size, align, block, "Load")?;
            return self.decode_value(ty, &bytes, state, block);
        }
        let opt_bytes = state
            .memory
            .read_maybe_uninit(ptr, size, align, block, "Load")?;
        if opt_bytes.iter().all(Option::is_some) {
            let bytes: Vec<u8> = opt_bytes
                .into_iter()
                .map(|b| b.expect("all init"))
                .collect();
            return self.decode_value(ty, &bytes, state, block);
        }
        // Some byte is uninitialized. A SCALAR load transports the partially-
        // initialized image as poison; an aggregate/other load keeps the strict
        // discipline (`read` re-reports the first uninitialized byte with its
        // exact offset, matching the historical message).
        if partial_load_ty(ty) {
            Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::PartialBytes(opt_bytes),
            })
        } else {
            state.memory.read(ptr, size, align, block, "Load")?;
            unreachable!("read must fail when read_maybe_uninit saw an uninitialized byte")
        }
    }

    /// Store `value` of `ty` to `ptr`.
    ///
    /// `strict` (atomic or volatile) requires a fully-initialized value: a
    /// `PartialBytes` poison value may not be stored strictly and faults. A
    /// non-strict store of a `PartialBytes` value writes its byte image VERBATIM
    /// (uninitialized bytes stay uninitialized at the destination) — the store
    /// half of copy-propagates-poison.
    #[allow(clippy::too_many_arguments)] // Mirrors the load/store instruction fields explicitly.
    fn eval_store(
        &self,
        ty: &Ty,
        ptr: &InterpretValue,
        value: &InterpretValue,
        align: Option<u64>,
        state: &mut ExecState,
        block: BlockId,
        strict: bool,
    ) -> InterpretResult<()> {
        // Copy-propagates-poison transport: a partially-initialized scalar image
        // moves to memory verbatim (non-strict stores only).
        if let InterpretValueKind::PartialBytes(opt_bytes) = &value.kind {
            if strict {
                return Err(reject_partial_error(block, "Store (atomic/volatile)"));
            }
            expect_ty(value, ty, block)?;
            let size = self.byte_size(ty, block)?;
            if opt_bytes.len() != size as usize {
                return Err(type_error(
                    block,
                    format!(
                        "Store: partial image size {} does not match type size {size}",
                        opt_bytes.len()
                    ),
                ));
            }
            let natural_align = self.byte_align(ty, block)?;
            let align = checked_align(align.unwrap_or(natural_align), block)?;
            let ptr = expect_pointer(ptr, block, "Store")?;
            return state
                .memory
                .write_maybe_uninit(ptr, opt_bytes, align, block, "Store");
        }
        expect_ty(value, ty, block)?;
        if let Ty::FatPtr(kind) = ty {
            self.validate_fat_pointer_value(kind, value, block)?;
        }
        let size = self.byte_size(ty, block)?;
        let natural_align = self.byte_align(ty, block)?;
        let align = checked_align(align.unwrap_or(natural_align), block)?;
        let ptr = expect_pointer(ptr, block, "Store")?;
        let bytes = self.encode_value(value, state, block)?;
        if bytes.len() != size as usize {
            return Err(type_error(
                block,
                format!(
                    "Store: encoded size {} does not match type size {size}",
                    bytes.len()
                ),
            ));
        }
        state.memory.write(ptr, &bytes, align, block, "Store")
    }

    /// Compute the new value of an `AtomicRMW`: `old <op> operand`, on integer
    /// operands. Add/Sub/And/Or/Xor reuse the wrapping integer binop semantics;
    /// Max/Min are signed, UMax/UMin unsigned; Xchg ignores `old`.
    fn eval_atomic_rmw(
        &self,
        op: AtomicRMWOp,
        ty: &Ty,
        old: &InterpretValue,
        operand: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let a = expect_int_value(old, block)?;
        let b = expect_int_value(operand, block)?;
        let result = match op {
            AtomicRMWOp::Xchg => b,
            AtomicRMWOp::Add => eval_int_binop(BinOp::Add, a, b, block)?,
            AtomicRMWOp::Sub => eval_int_binop(BinOp::Sub, a, b, block)?,
            AtomicRMWOp::And => eval_int_binop(BinOp::And, a, b, block)?,
            AtomicRMWOp::Or => eval_int_binop(BinOp::Or, a, b, block)?,
            AtomicRMWOp::Xor => eval_int_binop(BinOp::Xor, a, b, block)?,
            AtomicRMWOp::Max => {
                if a.as_signed() >= b.as_signed() {
                    a
                } else {
                    b
                }
            }
            AtomicRMWOp::Min => {
                if a.as_signed() <= b.as_signed() {
                    a
                } else {
                    b
                }
            }
            AtomicRMWOp::UMax => {
                if a.as_unsigned() >= b.as_unsigned() {
                    a
                } else {
                    b
                }
            }
            AtomicRMWOp::UMin => {
                if a.as_unsigned() <= b.as_unsigned() {
                    a
                } else {
                    b
                }
            }
        };
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Int(result),
        })
    }

    fn eval_gep(
        &self,
        pointee_ty: &Ty,
        base: &InterpretValue,
        indices: &[InterpretValue],
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let elem_size = self.byte_size(pointee_ty, block)?;
        // Accumulate the byte delta from the indices first — this is pure
        // address arithmetic and needs no provenance from the base.
        let mut delta: u64 = 0;
        for index in indices {
            let index = expect_int_value(index, block)?;
            if index.signed && index.as_signed() < 0 {
                return Err(ub(
                    block,
                    format!("GEP: negative index {}", index.as_signed()),
                ));
            }
            let index = u64::try_from(index.as_unsigned()).map_err(|_| {
                ub(
                    block,
                    format!("GEP: index {} does not fit u64", index.as_unsigned()),
                )
            })?;
            let byte_offset = elem_size
                .checked_mul(index)
                .ok_or_else(|| ub(block, "GEP: byte offset overflow"))?;
            delta = delta
                .checked_add(byte_offset)
                .ok_or_else(|| ub(block, "GEP: pointer offset overflow"))?;
        }
        // GEP is pointer ARITHMETIC, not a dereference: it is legal on a
        // no-provenance pointer and yields another no-provenance pointer (an
        // empty-collection iterator advancing its dangling cursor). Real
        // pointers keep their allocation provenance.
        if let InterpretValueKind::DanglingPtr(addr) = base.kind {
            let addr = addr
                .checked_add(delta)
                .ok_or_else(|| ub(block, "GEP: pointer offset overflow"))?;
            return Ok(InterpretValue {
                ty: Ty::Ptr,
                kind: InterpretValueKind::DanglingPtr(addr),
            });
        }
        let base = expect_pointer(base, block, "GEP")?;
        let offset = base
            .offset
            .checked_add(delta)
            .ok_or_else(|| ub(block, "GEP: pointer offset overflow"))?;
        Ok(InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::Ptr(InterpretPointer {
                allocation: base.allocation,
                offset,
            }),
        })
    }

    fn eval_dealloc(
        &self,
        ptr: &InterpretValue,
        state: &mut ExecState,
        block: BlockId,
    ) -> InterpretResult<()> {
        let ptr = expect_pointer(ptr, block, "Dealloc")?;
        state.memory.dealloc(ptr, block)
    }

    fn eval_ptr_data(
        &self,
        ptr_ty: &Ty,
        ptr: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        expect_ty(ptr, ptr_ty, block)?;
        match ptr_ty {
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
                Ok(InterpretValue {
                    ty: Ty::Ptr,
                    kind: ptr.kind.clone(),
                })
            }
            // B2: project the data lane of a fat value (built by `PtrFromParts`,
            // which typed the lane as a thin `Ty::Ptr` — checked, not assumed).
            Ty::FatPtr(kind) => {
                self.validate_fat_pointer_value(kind, ptr, block)?;
                match &ptr.kind {
                    InterpretValueKind::FatPtr { data, .. } => Ok((**data).clone()),
                    _ => Err(type_error(
                        block,
                        format!("PtrData: fat pointer type carries non-fat value {}", ptr.ty),
                    )),
                }
            }
            _ => Err(type_error(
                block,
                format!("PtrData: expected pointer-like type, got {ptr_ty}"),
            )),
        }
    }

    fn eval_ptr_metadata(
        &self,
        ptr_ty: &Ty,
        metadata_ty: &Ty,
        ptr: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        expect_ty(ptr, ptr_ty, block)?;
        match ptr_ty {
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
                if metadata_ty != &Ty::Unit {
                    return Err(type_error(
                        block,
                        format!("PtrMetadata: thin pointer metadata is unit, got {metadata_ty}"),
                    ));
                }
                Ok(InterpretValue {
                    ty: Ty::Unit,
                    kind: InterpretValueKind::Unit,
                })
            }
            // B2: project the metadata lane. The node's declared `metadata_ty` must
            // BE the kind's canonical metadata type (`FatPtrKind::metadata_ty` at the
            // pinned 64-bit target: a pointer-sized unsigned length for Slice/Str, a
            // thin Ptr for TraitObject), and the stored lane must carry it.
            Ty::FatPtr(kind) => {
                self.validate_fat_pointer_value(kind, ptr, block)?;
                let canonical = kind.metadata_ty(self.pointer_bits()).ok_or_else(|| {
                    type_error(block, format!("PtrMetadata: {ptr_ty} has no metadata type"))
                })?;
                if metadata_ty != &canonical {
                    return Err(type_error(
                        block,
                        format!(
                            "PtrMetadata: declared metadata type {metadata_ty} does not match \
                             the fat kind's canonical {canonical}"
                        ),
                    ));
                }
                match &ptr.kind {
                    InterpretValueKind::FatPtr { metadata, .. } => {
                        expect_ty(metadata, &canonical, block)?;
                        Ok((**metadata).clone())
                    }
                    _ => Err(type_error(
                        block,
                        format!(
                            "PtrMetadata: fat pointer type carries non-fat value {}",
                            ptr.ty
                        ),
                    )),
                }
            }
            _ => Err(type_error(
                block,
                format!("PtrMetadata: expected pointer-like type, got {ptr_ty}"),
            )),
        }
    }

    fn eval_ptr_from_parts(
        &self,
        ptr_ty: &Ty,
        metadata_ty: &Ty,
        data: &InterpretValue,
        metadata: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        match ptr_ty {
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
                if metadata_ty != &Ty::Unit {
                    return Err(type_error(
                        block,
                        format!("PtrFromParts: thin pointer metadata is unit, got {metadata_ty}"),
                    ));
                }
                expect_ty(metadata, &Ty::Unit, block)?;
                expect_ty(data, &Ty::Ptr, block)?;
                Ok(InterpretValue {
                    ty: ptr_ty.clone(),
                    kind: data.kind.clone(),
                })
            }
            // B2: assemble a fat value. The data operand must be a thin pointer
            // value; the metadata operand must carry the kind's canonical metadata
            // type (declared `metadata_ty` cross-checked against it, fail-closed).
            Ty::FatPtr(kind) => {
                self.require_fat_pointer_layout(block)?;
                let canonical = kind.metadata_ty(self.pointer_bits()).ok_or_else(|| {
                    type_error(
                        block,
                        format!("PtrFromParts: {ptr_ty} has no metadata type"),
                    )
                })?;
                if metadata_ty != &canonical {
                    return Err(type_error(
                        block,
                        format!(
                            "PtrFromParts: declared metadata type {metadata_ty} does not match \
                             the fat kind's canonical {canonical}"
                        ),
                    ));
                }
                expect_ty(data, &Ty::Ptr, block)?;
                expect_ty(metadata, &canonical, block)?;
                let result = InterpretValue {
                    ty: ptr_ty.clone(),
                    kind: InterpretValueKind::FatPtr {
                        data: Box::new(data.clone()),
                        metadata: Box::new(metadata.clone()),
                    },
                };
                self.validate_fat_pointer_value(kind, &result, block)?;
                Ok(result)
            }
            _ => Err(type_error(
                block,
                format!("PtrFromParts: expected pointer-like type, got {ptr_ty}"),
            )),
        }
    }

    fn byte_size(&self, ty: &Ty, block: BlockId) -> InterpretResult<u64> {
        match ty {
            Ty::Bool => Ok(1),
            Ty::I8 | Ty::U8 => Ok(1),
            Ty::I16 | Ty::U16 | Ty::F16 => Ok(2),
            Ty::I32 | Ty::U32 | Ty::F32 => Ok(4),
            Ty::I64 | Ty::U64 | Ty::F64 => Ok(8),
            Ty::I128 | Ty::U128 => Ok(16),
            // Pointer-width integers occupy pointer bytes at the pinned 64-bit
            // reference target (`int_shape` executes them at 64 bits); char is a
            // 32-bit unsigned carrier. Mirrors `shape::layout`'s PointerInt rules.
            Ty::Isize | Ty::Usize => Ok(8),
            Ty::Char => Ok(4),
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
                Ok(8)
            }
            // B2: a fat pointer is two pointer lanes at the pinned 64-bit target
            // (data + metadata), matching `Ty::bit_width_with(64)` = 128 and the
            // shape module's fat `PointerLayoutShape`.
            Ty::FatPtr(_) => {
                self.require_fat_pointer_layout(block)?;
                Ok(16)
            }
            Ty::Unit => Ok(0),
            Ty::Vector(elem, lanes) => {
                if *lanes == 0 {
                    return Err(err(
                        InterpretErrorCode::UnsupportedVectorShape,
                        block,
                        "zero-lane vectors are not executable",
                    ));
                }
                self.byte_size(elem, block)?
                    .checked_mul(u64::from(*lanes))
                    .ok_or_else(|| type_error(block, "vector byte size overflow"))
            }
            Ty::Array(elem, len) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                self.byte_size(&elem_ty, block)?
                    .checked_mul(*len)
                    .ok_or_else(|| type_error(block, "array byte size overflow"))
            }
            // A `Ty::Struct` has a finite, in-memory C-style layout: each field
            // is placed at the next offset aligned to the field's natural
            // alignment, and the total size is rounded up to the struct's
            // alignment (the max field alignment). This is the heap-faithful
            // counterpart to the SSA `Aggregate` value model: a recursive ADT
            // (e.g. `Box<Level>`) stays finite because its recursive payload
            // field is a pointer (`Ty::Ptr`, 8 bytes), not an inline struct.
            Ty::Struct(_) => Ok(self.struct_layout(ty, block)?.size),
            // A `Ty::Tuple` has the same finite C-style layout as a struct: each
            // element placed at its aligned offset, the total rounded up to the
            // tuple alignment. This is the in-memory counterpart to the
            // in-register `Aggregate` value model and is what lets a tuple be
            // `Alloca`'d / `Store`d / `Load`ed faithfully.
            Ty::Tuple(_) => Ok(self.tuple_layout(ty, block)?.size),
            // A `Ty::Enum` has trust-ir's canonical tagged-union layout (tag at
            // offset 0 + shared max-sized payload region) — see `enum_layout`.
            Ty::Enum(_) => Ok(self.enum_layout(ty, block)?.size),
            _ => Err(type_error(block, format!("{ty} has no byte layout"))),
        }
    }

    /// Byte layout (field offsets, total size, alignment) of a `Ty::Struct`.
    ///
    /// # A producer-declared layout is NORMATIVE — the same rule `enum_layout` follows
    ///
    /// `StructDef::size`, `StructDef::align` and `FieldDef::offset` ARE the struct
    /// analogue of [`crate::ty::EnumLayoutDescriptor`]: a producer that knows the
    /// concrete layout fills all three from its own authority (for the rustc
    /// front-ends, `layout_of` — which REORDERS `repr(Rust)` fields), and
    /// `Module::ty_layout_shape` in `shape` has always consumed exactly those three
    /// fields. When they are present this function uses them VERBATIM, after the
    /// structural re-validation below, instead of synthesizing a layout.
    ///
    /// Before this existed, this function ignored `FieldDef::offset` entirely and
    /// recomputed a declaration-order C layout, so a module could be executed against
    /// a byte image its own producer contradicts. That is not hypothetical: for
    /// `struct Mixed { a: u8, b: u64, c: u8 }` rustc lays out `b@0 a@8 c@9` (size 16)
    /// and the producer emits `gep inbounds i8, ptr %0, 9` for `&s.c`, while the
    /// synthesized layout placed `c` at 16 and `b` at [8,16) — so byte 9 named a
    /// byte inside a DIFFERENT field. Crate-wide in clean-kernel a large minority of
    /// struct defs carrying rustc offsets disagreed with the synthesized rule. The
    /// disagreement was held off the verdict ledger only by coverage gates, never by
    /// a layout invariant; deriving both sides from ONE source removes it at the
    /// root rather than keeping it unobservable.
    ///
    /// # Absent, complete, and in between
    ///
    /// * `size`/`align` absent and no field offset declared — nothing was claimed.
    ///   Synthesize the canonical declaration-order C layout (below), byte-for-byte
    ///   as before. Producers that legitimately cannot know a layout (generic /
    ///   pre-monomorphization / verifier-lane defs) live here and are unaffected.
    /// * `size`/`align` present — the layout is DECLARED and is used. A field whose
    ///   own `offset` is absent is admitted only when it occupies NO BYTES, which is
    ///   the one case where the missing number is information-free: a zero-sized
    ///   field addresses nothing, so any in-range placement is the same placement,
    ///   and it is placed at 0. (This is exactly the state a producer creates when
    ///   it drops a rustc offset that equals the struct size — rustc's legal
    ///   placement for a zero-sized field. MEASURED on clean-kernel: 275 of 1,299
    ///   struct defs are in that state, so treating it as an incoherent descriptor
    ///   would refuse a fifth of the crate for a number that names no byte.) A
    ///   field with no declared offset that DOES occupy bytes is unplaceable and
    ///   fails closed.
    /// * Anything else — a `size` without an `align` (or the reverse), or field
    ///   offsets with no declared struct size — is a contradiction no producer in
    ///   this tree emits. It fails closed rather than being silently completed.
    ///
    /// # Re-validation
    ///
    /// Modules may be interpreted without validation, so — exactly as `enum_layout`
    /// does for its descriptor — every structural fact is re-checked here before any
    /// byte slice is formed: a positive power-of-two alignment, a size that is a
    /// multiple of it, each field in bounds, each field aligned for its own type
    /// (clamped by `StructRepr::Packed`, which is precisely a declaration that field
    /// alignment is clamped), no field over-aligned for the struct, and no two
    /// fields overlapping. A declared layout that fails any of them is an error, not
    /// a fallback: falling back would hide the producer's contradiction behind a
    /// synthesized number, which is the defect this path exists to remove.
    ///
    /// This is the single source of layout truth shared by `byte_size`,
    /// `byte_align`, `encode_value`, and `decode_value`, so the heap round-trip
    /// of a struct value (`HeapAlloc`/`Store`/`Load`) is internally consistent.
    fn struct_layout(&self, ty: &Ty, block: BlockId) -> InterpretResult<StructLayout> {
        let sid = match ty {
            Ty::Struct(sid) => *sid,
            _ => return Err(type_error(block, format!("{ty} is not a struct"))),
        };
        let module = self.module_context(block, "struct layout")?;
        let def = module
            .struct_def(sid)
            .ok_or_else(|| type_error(block, format!("struct id {} not found in module", sid.0)))?;
        match (def.size, def.align) {
            (Some(size), Some(align)) => self.declared_struct_layout(ty, def, size, align, block),
            (None, None) => {
                if let Some(index) = def.fields.iter().position(|field| field.offset.is_some()) {
                    return Err(type_error(
                        block,
                        format!(
                            "struct {ty} declares a byte offset for field {index} but no struct size or alignment"
                        ),
                    ));
                }
                self.aggregate_layout(def.fields.iter().map(|field| &field.ty), block, "struct")
            }
            (Some(_), None) | (None, Some(_)) => Err(type_error(
                block,
                format!("struct {ty} declares a size without an alignment, or the reverse"),
            )),
        }
    }

    /// The producer-declared branch of [`Self::struct_layout`]: re-validate the
    /// declared `size`/`align`/`FieldDef::offset` triple and hand it back verbatim.
    ///
    /// Split out only so the layout rules stay readable; it has no other caller and
    /// must not acquire one that skips the presence dispatch above.
    fn declared_struct_layout(
        &self,
        ty: &Ty,
        def: &crate::ty::StructDef,
        size: u64,
        align: u64,
        block: BlockId,
    ) -> InterpretResult<StructLayout> {
        if align == 0 || !align.is_power_of_two() || !size.is_multiple_of(align) {
            return Err(type_error(
                block,
                format!("struct {ty} declares an incoherent size {size} / alignment {align}"),
            ));
        }
        // `repr(packed(N))` IS a declaration that every field's alignment is clamped
        // to N, so the natural-alignment checks below must be taken against the
        // clamped value or a correct packed layout would be rejected as misaligned.
        let clamp = match def.repr {
            crate::ty::StructRepr::Packed(packed) => u64::from(packed),
            _ => u64::MAX,
        };
        let mut field_offsets: Vec<(u64, Ty)> = Vec::with_capacity(def.fields.len());
        let mut field_sizes: Vec<u64> = Vec::with_capacity(def.fields.len());
        for (index, field) in def.fields.iter().enumerate() {
            let field_size = self.byte_size(&field.ty, block)?;
            let field_align = self.byte_align(&field.ty, block)?.max(1).min(clamp);
            let offset = match field.offset {
                Some(offset) => {
                    if !offset.is_multiple_of(field_align)
                        || field_align > align
                        || offset.checked_add(field_size).is_none_or(|end| end > size)
                    {
                        return Err(type_error(
                            block,
                            format!(
                                "struct {ty} field {index} at declared offset {offset} ({field_size} bytes, align {field_align}) is out of bounds, misaligned, or over-aligned for declared size {size} / align {align}"
                            ),
                        ));
                    }
                    offset
                }
                // Information-free ONLY at zero size — see the doc comment.
                None => {
                    if field_size != 0 {
                        return Err(type_error(
                            block,
                            format!(
                                "struct {ty} field {index} occupies {field_size} bytes but the declared layout gives it no offset"
                            ),
                        ));
                    }
                    0
                }
            };
            field_offsets.push((offset, field.ty.clone()));
            field_sizes.push(field_size);
        }
        for left in 0..field_offsets.len() {
            for right in left + 1..field_offsets.len() {
                if byte_ranges_overlap(
                    field_offsets[left].0,
                    field_sizes[left],
                    field_offsets[right].0,
                    field_sizes[right],
                ) {
                    return Err(type_error(
                        block,
                        format!(
                            "struct {ty} declared layout has overlapping fields {left} and {right}"
                        ),
                    ));
                }
            }
        }
        Ok(StructLayout {
            size,
            align,
            field_offsets,
        })
    }

    /// C-style layout (field offsets, total size, alignment) of a `Ty::Tuple`,
    /// computed directly from its inline element types. Fields are laid out in
    /// order; each is aligned to its natural alignment; the tuple size is
    /// rounded up to the tuple alignment (max field alignment, min 1). An empty
    /// tuple is size 0, alignment 1.
    ///
    /// A tuple shares the exact same layout algorithm as a `Ty::Struct` (via
    /// `aggregate_layout`), so the heap/stack round-trip of a tuple value
    /// (`Alloca`/`Store`/`Load`) is internally consistent: `byte_size`,
    /// `byte_align`, `encode_value`, and `decode_value` all read field offsets
    /// from this one source.
    fn tuple_layout(&self, ty: &Ty, block: BlockId) -> InterpretResult<StructLayout> {
        let elems = match ty {
            Ty::Tuple(elems) => elems,
            _ => return Err(type_error(block, format!("{ty} is not a tuple"))),
        };
        self.aggregate_layout(elems.iter(), block, "tuple")
    }

    /// The single C-style aggregate layout algorithm shared by `struct_layout`
    /// and `tuple_layout`. Each field is placed at the next offset aligned up to
    /// its natural alignment; the total size is rounded up to the aggregate
    /// alignment (max field alignment, min 1). A field whose type has no byte
    /// layout (e.g. an unsupported nested type) fails closed via `byte_align` /
    /// `byte_size`, so a partial / wrong layout is never produced.
    fn aggregate_layout<'a>(
        &self,
        fields: impl ExactSizeIterator<Item = &'a Ty>,
        block: BlockId,
        kind: &str,
    ) -> InterpretResult<StructLayout> {
        let mut offset: u64 = 0;
        let mut max_align: u64 = 1;
        let mut field_offsets = Vec::with_capacity(fields.len());
        for field_ty in fields {
            let f_align = self.byte_align(field_ty, block)?.max(1);
            let f_size = self.byte_size(field_ty, block)?;
            offset = align_up(offset, f_align, block)?;
            field_offsets.push((offset, field_ty.clone()));
            offset = offset
                .checked_add(f_size)
                .ok_or_else(|| type_error(block, format!("{kind} byte size overflow")))?;
            max_align = max_align.max(f_align);
        }
        let size = align_up(offset, max_align, block)?;
        Ok(StructLayout {
            size,
            align: max_align,
            field_offsets,
        })
    }

    /// trust-ir's **canonical tagged-union layout** of a `Ty::Enum`, in byte
    /// units, computed from the module's `EnumDef` (the interpreter mirror of
    /// `Module::enum_layout_shape` in `shape` — same rules, byte-denominated):
    ///
    /// * tag (the `EnumDef::canonical_tag_repr` integer) at offset 0;
    /// * each variant's fields laid out C-style via the shared
    ///   `aggregate_layout` (offsets RELATIVE to the payload region);
    /// * payload region at `align_up(tag_size, payload_align)` where
    ///   `payload_align` = max variant alignment (min 1), spanning the largest
    ///   variant;
    /// * enum align = max(tag align, payload align); enum size =
    ///   `align_up(payload_offset + payload_size, align)`.
    ///
    /// This is trust-ir's CANONICAL layout, not a claim of rustc layout parity
    /// (no niche optimization / variant reordering — a producer mapping rustc
    /// enums must bridge deliberately). Fail-closed: a missing def, an
    /// unresolvable discriminant assignment, an uninhabited (zero-variant)
    /// enum, or an unlayoutable field type all error before any offset is
    /// committed. As with `struct_layout`, a recursive payload must be broken
    /// by a pointer (`Ty::Ptr`) to stay finite — the M2 `Box`-recursion shape.
    fn enum_layout(&self, ty: &Ty, block: BlockId) -> InterpretResult<EnumLayout> {
        let eid = match ty {
            Ty::Enum(eid) => *eid,
            _ => return Err(type_error(block, format!("{ty} is not an enum"))),
        };
        let module = self.module_context(block, "enum layout")?;
        let def = module
            .enum_def(eid)
            .ok_or_else(|| type_error(block, format!("enum id {} not found in module", eid.0)))?;
        let discriminants = def.effective_discriminants().ok_or_else(|| {
            type_error(
                block,
                format!(
                    "enum {} has no canonical discriminant assignment (duplicate or overflowing values)",
                    ty
                ),
            )
        })?;
        let tag = def.canonical_tag_repr().ok_or_else(|| {
            type_error(
                block,
                format!(
                    "enum {} has no canonical tag (uninhabited, discriminants beyond 64-bit, or a repr hint too narrow)",
                    ty
                ),
            )
        })?;
        let tag_ty = tag.ty();
        let tag_size = self.byte_size(&tag_ty, block)?;
        let tag_align = self.byte_align(&tag_ty, block)?;

        // A producer-provided descriptor is normative. Modules may be
        // interpreted without validation, so repeat structural checks before
        // forming any byte slice.
        if let Some(desc) = &def.layout {
            if desc.align == 0
                || !desc.align.is_power_of_two()
                || !desc.size.is_multiple_of(desc.align)
                || desc.variant_field_offsets.len() != def.variants.len()
            {
                return Err(type_error(
                    block,
                    format!("enum {ty} has an incoherent layout descriptor"),
                ));
            }
            let mut variant_field_offsets = Vec::with_capacity(def.variants.len());
            for (variant_idx, (variant, offsets)) in def
                .variants
                .iter()
                .zip(&desc.variant_field_offsets)
                .enumerate()
            {
                if offsets.len() != variant.fields.len() {
                    return Err(type_error(
                        block,
                        format!(
                            "enum {ty} layout descriptor variant {variant_idx} has {} offsets for {} fields",
                            offsets.len(),
                            variant.fields.len()
                        ),
                    ));
                }
                let mut fields = Vec::with_capacity(offsets.len());
                for (field_ty, offset) in variant.fields.iter().zip(offsets) {
                    let field_size = self.byte_size(field_ty, block)?;
                    let field_align = self.byte_align(field_ty, block)?;
                    if !offset.is_multiple_of(field_align)
                        || field_align > desc.align
                        || offset
                            .checked_add(field_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(type_error(
                            block,
                            format!(
                                "enum {ty} layout descriptor variant {variant_idx} field at offset {offset} ({field_size} bytes, align {field_align}) is out of bounds, misaligned, or over-aligned for descriptor align {}",
                                desc.align,
                            ),
                        ));
                    }
                    fields.push((*offset, field_ty.clone()));
                }
                for left in 0..fields.len() {
                    let left_size = self.byte_size(&fields[left].1, block)?;
                    for right in left + 1..fields.len() {
                        let right_size = self.byte_size(&fields[right].1, block)?;
                        if byte_ranges_overlap(
                            fields[left].0,
                            left_size,
                            fields[right].0,
                            right_size,
                        ) {
                            return Err(type_error(
                                block,
                                format!(
                                    "enum {ty} layout descriptor variant {variant_idx} has overlapping fields {left} and {right}"
                                ),
                            ));
                        }
                    }
                }
                variant_field_offsets.push(fields);
            }
            let byte_view = match &desc.encoding {
                // v37 `Untagged`. No tag bytes exist, so the tag-placement and
                // tag/field-overlap checks the other two arms perform are
                // vacuous here. What is NOT vacuous is that the descriptor must
                // name exactly one variant to be untagged about: a multi-variant
                // enum with no tag could not be discriminated at runtime, so
                // accepting one would let a Load invent a variant. Fail closed.
                crate::ty::EnumTagEncoding::Untagged => {
                    if def.variants.len() != 1 {
                        return Err(type_error(
                            block,
                            format!(
                                "enum {ty} declares the untagged encoding but has {} variants; \
                                 an untagged layout can only describe a single-variant enum",
                                def.variants.len()
                            ),
                        ));
                    }
                    EnumByteView::Untagged { variant: 0 }
                }
                crate::ty::EnumTagEncoding::Direct { tag_offset } => {
                    if tag_align > desc.align
                        || !tag_offset.is_multiple_of(tag_align)
                        || tag_offset
                            .checked_add(tag_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(type_error(
                            block,
                            format!(
                                "enum {ty} layout descriptor tag at offset {tag_offset} ({tag_size} bytes, align {tag_align}) is out of bounds, misaligned, or over-aligned for descriptor align {}",
                                desc.align,
                            ),
                        ));
                    }
                    for (variant_idx, fields) in variant_field_offsets.iter().enumerate() {
                        for (field_idx, (field_offset, field_ty)) in fields.iter().enumerate() {
                            let field_size = self.byte_size(field_ty, block)?;
                            if byte_ranges_overlap(*tag_offset, tag_size, *field_offset, field_size)
                            {
                                return Err(type_error(
                                    block,
                                    format!(
                                        "enum {ty} layout descriptor direct tag overlaps variant {variant_idx} field {field_idx}"
                                    ),
                                ));
                            }
                        }
                    }
                    EnumByteView::Direct {
                        tag_offset: *tag_offset,
                    }
                }
                crate::ty::EnumTagEncoding::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_variants_end,
                    niche_start,
                    niche_offset,
                    niche_ty,
                } => {
                    let variant_count = u32::try_from(def.variants.len()).map_err(|_| {
                        type_error(
                            block,
                            format!("enum {ty} has too many variants for a niche encoding"),
                        )
                    })?;
                    let niche_size = self.byte_size(&niche_ty.ty(), block)?;
                    let niche_align = self.byte_align(&niche_ty.ty(), block)?;
                    let niche_bits = (niche_size * 8) as u32;
                    let niche_mask = int_mask(niche_bits).ok_or_else(|| {
                        type_error(block, format!("unsupported niche lane width {niche_bits}"))
                    })?;
                    let niche_span = niche_variants_end
                        .checked_sub(*niche_variants_start)
                        .map(u128::from);
                    let covers_every_variant = niche_span.is_some_and(|span| {
                        let extra_untagged = if (*niche_variants_start..=*niche_variants_end)
                            .contains(untagged_variant)
                        {
                            0
                        } else {
                            1
                        };
                        span.checked_add(1)
                            .and_then(|covered| covered.checked_add(extra_untagged))
                            == Some(u128::from(variant_count))
                    });
                    if *untagged_variant >= variant_count
                        || niche_variants_start > niche_variants_end
                        || *niche_variants_end >= variant_count
                        || !covers_every_variant
                        || *niche_start > niche_mask
                        || niche_span.is_none_or(|span| span > niche_mask)
                        || niche_align > desc.align
                        || !niche_offset.is_multiple_of(niche_align)
                        || niche_offset
                            .checked_add(niche_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(type_error(
                            block,
                            format!("enum {ty} has an incoherent niche encoding"),
                        ));
                    }
                    let untagged_fields = &variant_field_offsets[*untagged_variant as usize];
                    let lane_is_covered = untagged_fields.iter().any(|(field_offset, field_ty)| {
                        self.byte_size(field_ty, block).is_ok_and(|field_size| {
                            field_size > 0
                                && *field_offset <= *niche_offset
                                && field_offset
                                    .checked_add(field_size)
                                    .is_some_and(|field_end| {
                                        niche_offset
                                            .checked_add(niche_size)
                                            .is_some_and(|niche_end| field_end >= niche_end)
                                    })
                        })
                    });
                    if !lane_is_covered {
                        return Err(type_error(
                            block,
                            format!(
                                "enum {ty} niche lane is not covered by the untagged variant payload"
                            ),
                        ));
                    }
                    for variant_idx in *niche_variants_start..=*niche_variants_end {
                        if variant_idx == *untagged_variant {
                            continue;
                        }
                        for (field_idx, (field_offset, field_ty)) in variant_field_offsets
                            [variant_idx as usize]
                            .iter()
                            .enumerate()
                        {
                            let field_size = self.byte_size(field_ty, block)?;
                            if byte_ranges_overlap(
                                *niche_offset,
                                niche_size,
                                *field_offset,
                                field_size,
                            ) {
                                return Err(type_error(
                                    block,
                                    format!(
                                        "enum {ty} niche lane overlaps niche-tagged variant {variant_idx} field {field_idx}"
                                    ),
                                ));
                            }
                        }
                    }
                    EnumByteView::Niche {
                        untagged_variant: *untagged_variant as usize,
                        niche_variants_start: *niche_variants_start,
                        niche_variants_end: *niche_variants_end,
                        niche_start: *niche_start,
                        niche_offset: *niche_offset,
                        niche_size,
                    }
                }
            };
            return Ok(EnumLayout {
                tag_ty,
                tag_size,
                payload_offset: 0,
                size: desc.size,
                align: desc.align,
                discriminants,
                variant_field_offsets,
                byte_view,
            });
        }

        let mut payload_size: u64 = 0;
        let mut payload_align: u64 = 1;
        let mut variant_field_offsets = Vec::with_capacity(def.variants.len());
        for variant in &def.variants {
            let layout = self.aggregate_layout(variant.fields.iter(), block, "enum variant")?;
            payload_size = payload_size.max(layout.size);
            payload_align = payload_align.max(layout.align);
            variant_field_offsets.push(layout.field_offsets);
        }

        let payload_offset = align_up(tag_size, payload_align, block)?;
        let align = tag_align.max(payload_align);
        let size = align_up(
            payload_offset
                .checked_add(payload_size)
                .ok_or_else(|| type_error(block, "enum byte size overflow"))?,
            align,
            block,
        )?;
        Ok(EnumLayout {
            tag_ty,
            tag_size,
            payload_offset,
            size,
            align,
            discriminants,
            variant_field_offsets,
            byte_view: EnumByteView::Direct { tag_offset: 0 },
        })
    }

    /// Resolve the C-style layout of an aggregate-typed value, dispatching to
    /// `struct_layout` for `Ty::Struct` and `tuple_layout` for `Ty::Tuple`.
    /// Shared by `encode_value` and `decode_value` so both directions of the
    /// memory round-trip agree on field offsets.
    fn aggregate_value_layout(&self, ty: &Ty, block: BlockId) -> InterpretResult<StructLayout> {
        match ty {
            Ty::Struct(_) => self.struct_layout(ty, block),
            Ty::Tuple(_) => self.tuple_layout(ty, block),
            _ => Err(type_error(
                block,
                format!("{ty} is not an aggregate with a memory layout"),
            )),
        }
    }

    fn byte_align(&self, ty: &Ty, block: BlockId) -> InterpretResult<u64> {
        match ty {
            Ty::Bool | Ty::I8 | Ty::U8 => Ok(1),
            Ty::I16 | Ty::U16 | Ty::F16 => Ok(2),
            // Char is a 32-bit unsigned carrier; isize/usize take pointer
            // alignment at the pinned 64-bit reference target (with the I64/
            // Ptr group below). Mirrors `byte_size` and `shape::layout`.
            Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => Ok(4),
            Ty::I64
            | Ty::U64
            | Ty::F64
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_) => Ok(8),
            Ty::Isize | Ty::Usize => Ok(8),
            // B2: fat pointers align to one pointer lane (8), not their 16-byte size.
            Ty::FatPtr(_) => {
                self.require_fat_pointer_layout(block)?;
                Ok(8)
            }
            Ty::I128 | Ty::U128 => Ok(16),
            Ty::Unit => Ok(1),
            Ty::Vector(elem, lanes) => {
                if *lanes == 0 {
                    return Err(err(
                        InterpretErrorCode::UnsupportedVectorShape,
                        block,
                        "zero-lane vectors are not executable",
                    ));
                }
                self.byte_align(elem, block)
            }
            Ty::Array(elem, _) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                self.byte_align(&elem_ty, block)
            }
            // Struct alignment is the max of its field alignments (min 1).
            Ty::Struct(_) => Ok(self.struct_layout(ty, block)?.align),
            // Tuple alignment is the max of its element alignments (min 1), so
            // an empty tuple is alignment 1 — matching `Ty::Unit`.
            Ty::Tuple(_) => Ok(self.tuple_layout(ty, block)?.align),
            // Enum alignment is max(tag alignment, payload alignment) — see
            // `enum_layout` for the canonical rules.
            Ty::Enum(_) => Ok(self.enum_layout(ty, block)?.align),
            _ => Err(type_error(block, format!("{ty} has no byte alignment"))),
        }
    }

    fn encode_value(
        &self,
        value: &InterpretValue,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<Vec<u8>> {
        match &value.kind {
            InterpretValueKind::Int(int) => {
                let byte_len = self.byte_size(&value.ty, block)? as usize;
                Ok(int.raw.to_le_bytes()[..byte_len].to_vec())
            }
            InterpretValueKind::Bool(value) => Ok(vec![u8::from(*value)]),
            InterpretValueKind::Ptr(ptr) => Ok(state
                .memory
                .address(*ptr, block, "Store")?
                .to_le_bytes()
                .to_vec()),
            InterpretValueKind::NullPtr => Ok(0u64.to_le_bytes().to_vec()),
            // A no-provenance pointer stores its raw integer address verbatim,
            // so a later load reconstructs the same dangling value.
            InterpretValueKind::DanglingPtr(addr) => Ok(addr.to_le_bytes().to_vec()),
            // B2: a fat pointer's byte image is its two lanes back to back —
            // data address (8 LE bytes) then metadata (8 LE bytes: the raw
            // length int for Slice/Str, the vtable address for TraitObject).
            // Exact inverse of the `decode_value` FatPtr arm.
            InterpretValueKind::FatPtr { data, metadata } => {
                let mut bytes = self.encode_value(data, state, block)?;
                bytes.extend(self.encode_value(metadata, state, block)?);
                if bytes.len() != 16 {
                    return Err(type_error(
                        block,
                        format!(
                            "Store: fat pointer image is {} bytes, expected 16",
                            bytes.len()
                        ),
                    ));
                }
                Ok(bytes)
            }
            InterpretValueKind::Unit => Ok(Vec::new()),
            InterpretValueKind::FloatBits(bits) => {
                let byte_len = self.byte_size(&value.ty, block)? as usize;
                Ok(bits.to_le_bytes()[..byte_len].to_vec())
            }
            // A `<N x bool>` value is a LOGICAL SIMD mask. Its PHYSICAL byte
            // image — what a reinterpret / bitcast to an integer vector reads,
            // e.g. hashbrown's NEON `Group::match_full`
            // (`vreinterpret_u64_u8` over the `<8 x i8> icmp sge ctrl, 0` mask) —
            // is ALL-ONES per true lane, NOT the scalar `0x01`. NEON / Rust
            // `simd` comparison masks (and trust-cg's binary, which is correct
            // vs native) use the all-ones convention: a true lane is `0xFF..`
            // across its whole byte width, a false lane is `0x00..`. Encode a
            // bool-mask vector that way so the reinterpret matches; a plain
            // integer/float vector encodes lane-by-lane as before.
            InterpretValueKind::Vector(values) if matches!(&value.ty, Ty::Vector(elem, _) if **elem == Ty::Bool) =>
            {
                let lane_bytes = self.byte_size(&Ty::Bool, block)? as usize;
                let mut bytes = Vec::with_capacity(self.byte_size(&value.ty, block)? as usize);
                for lane in values {
                    let set = lane.as_bool().ok_or_else(|| {
                        type_error(block, "vector bool mask lane is not a bool value")
                    })?;
                    let fill = if set { 0xFFu8 } else { 0x00u8 };
                    bytes.extend(std::iter::repeat_n(fill, lane_bytes));
                }
                Ok(bytes)
            }
            InterpretValueKind::Vector(values) | InterpretValueKind::Array(values) => {
                let mut bytes = Vec::with_capacity(self.byte_size(&value.ty, block)? as usize);
                for value in values {
                    bytes.extend(self.encode_value(value, state, block)?);
                }
                Ok(bytes)
            }
            // Encode an aggregate value (an `Aggregate` of its fields) to its
            // C-layout byte image: each field is written at its computed offset;
            // inter-field padding stays zero. Both `Ty::Struct` (layout from the
            // module `StructDef`) and `Ty::Tuple` (layout from the inline element
            // types) share the same offset math, so the field offsets used here
            // are byte-for-byte identical to those `byte_size` / `decode_value`
            // compute.
            InterpretValueKind::Aggregate(fields)
                if matches!(value.ty, Ty::Struct(_) | Ty::Tuple(_)) =>
            {
                let layout = self.aggregate_value_layout(&value.ty, block)?;
                if fields.len() != layout.field_offsets.len() {
                    return Err(type_error(
                        block,
                        format!(
                            "Store: aggregate {} has {} fields but value has {}",
                            value.ty,
                            layout.field_offsets.len(),
                            fields.len()
                        ),
                    ));
                }
                let mut bytes = vec![0u8; layout.size as usize];
                for (field_val, (offset, field_ty)) in fields.iter().zip(&layout.field_offsets) {
                    expect_ty(field_val, field_ty, block)?;
                    let field_bytes = self.encode_value(field_val, state, block)?;
                    let start = *offset as usize;
                    bytes[start..start + field_bytes.len()].copy_from_slice(&field_bytes);
                }
                Ok(bytes)
            }
            // Encode an enum value (`Aggregate([tag, fields...])`, the tag +
            // payload convention) to its canonical tagged-union byte image:
            // the tag at offset 0, the selected variant's fields at their
            // payload-relative offsets shifted by `payload_offset`, all other
            // bytes (inter-field padding and the unused tail of the shared
            // payload region) zero.
            InterpretValueKind::Aggregate(elems) if matches!(value.ty, Ty::Enum(_)) => {
                let layout = self.enum_layout(&value.ty, block)?;
                let Some((tag_val, field_vals)) = elems.split_first() else {
                    return Err(type_error(
                        block,
                        format!("Store: enum value {} is missing its tag lane", value.ty),
                    ));
                };
                expect_ty(tag_val, &layout.tag_ty, block)?;
                let disc = tag_int_discriminant(expect_int_value(tag_val, block)?);
                let variant_idx = layout.variant_by_discriminant(disc).ok_or_else(|| {
                    type_error(
                        block,
                        format!("Store: tag {disc} does not name a variant of {}", value.ty),
                    )
                })?;
                let fields = &layout.variant_field_offsets[variant_idx];
                if field_vals.len() != fields.len() {
                    return Err(type_error(
                        block,
                        format!(
                            "Store: enum {} variant {} has {} fields but value has {}",
                            value.ty,
                            variant_idx,
                            fields.len(),
                            field_vals.len()
                        ),
                    ));
                }
                let mut bytes = vec![0u8; layout.size as usize];
                match &layout.byte_view {
                    // The byte image carries NO tag lane. The value model is
                    // unchanged — the tag is still an operand and was still
                    // checked against `tag_ty` above — it simply does not
                    // survive the round trip through memory, because the sole
                    // variant makes it recoverable without being stored.
                    EnumByteView::Untagged { variant } => {
                        if variant_idx != *variant {
                            return Err(type_error(
                                block,
                                format!(
                                    "Store: enum {} is untagged over variant {variant} but the \
                                     value names variant {variant_idx}",
                                    value.ty
                                ),
                            ));
                        }
                    }
                    EnumByteView::Direct { tag_offset } => {
                        let tag_bytes = self.encode_value(tag_val, state, block)?;
                        let start = *tag_offset as usize;
                        bytes[start..start + tag_bytes.len()].copy_from_slice(&tag_bytes);
                    }
                    EnumByteView::Niche {
                        untagged_variant,
                        niche_variants_start,
                        niche_start,
                        niche_offset,
                        niche_size,
                        ..
                    } => {
                        if variant_idx != *untagged_variant {
                            let relative = (variant_idx as u128)
                                .wrapping_sub(u128::from(*niche_variants_start));
                            let lane_bits = (*niche_size * 8) as u32;
                            let mask = int_mask(lane_bits).ok_or_else(|| {
                                type_error(
                                    block,
                                    format!("unsupported niche lane width {lane_bits}"),
                                )
                            })?;
                            let lane_value = niche_start.wrapping_add(relative) & mask;
                            let start = *niche_offset as usize;
                            bytes[start..start + *niche_size as usize]
                                .copy_from_slice(&lane_value.to_le_bytes()[..*niche_size as usize]);
                        }
                    }
                }
                for (field_val, (rel_offset, field_ty)) in field_vals.iter().zip(fields) {
                    expect_ty(field_val, field_ty, block)?;
                    let field_bytes = self.encode_value(field_val, state, block)?;
                    let start = (layout.payload_offset + rel_offset) as usize;
                    bytes[start..start + field_bytes.len()].copy_from_slice(&field_bytes);
                }
                if let EnumByteView::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_variants_end,
                    niche_start,
                    niche_offset,
                    niche_size,
                } = &layout.byte_view
                    && variant_idx == *untagged_variant
                {
                    let start = *niche_offset as usize;
                    let mut raw = [0u8; 16];
                    raw[..*niche_size as usize]
                        .copy_from_slice(&bytes[start..start + *niche_size as usize]);
                    let lane_bits = (*niche_size * 8) as u32;
                    let mask = int_mask(lane_bits).ok_or_else(|| {
                        type_error(block, format!("unsupported niche lane width {lane_bits}"))
                    })?;
                    let relative = u128::from_le_bytes(raw).wrapping_sub(*niche_start) & mask;
                    let range_len = u128::from(*niche_variants_end - *niche_variants_start);
                    if relative <= range_len {
                        return Err(type_error(
                            block,
                            format!(
                                "Store: enum {} untagged payload occupies a reserved niche value",
                                value.ty
                            ),
                        ));
                    }
                }
                Ok(bytes)
            }
            _ => Err(type_error(
                block,
                format!("Store: cannot encode value of type {}", value.ty),
            )),
        }
    }

    fn decode_value(
        &self,
        ty: &Ty,
        bytes: &[u8],
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        if bytes.len() != self.byte_size(ty, block)? as usize {
            return Err(type_error(
                block,
                format!(
                    "Load: byte count {} does not match type size {}",
                    bytes.len(),
                    self.byte_size(ty, block)?
                ),
            ));
        }
        match ty {
            Ty::Bool => Ok(InterpretValue::bool(
                bytes.first().copied().unwrap_or(0) != 0,
            )),
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            // B1 faithful scalars decode through the same `int_shape` register
            // shape (isize/usize at the pinned 64 bits, char at its 32-bit
            // carrier) — `byte_size` already sized the image to match.
            | Ty::Isize
            | Ty::Usize
            | Ty::Char => {
                let (bits, signed) = int_shape(ty).expect("integer type");
                let mut raw = [0u8; 16];
                raw[..bytes.len()].copy_from_slice(bytes);
                let int = InterpretInt::from_raw(bits, signed, u128::from_le_bytes(raw))
                    .ok_or_else(|| {
                        type_error(block, format!("unsupported integer width {bits}"))
                    })?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Int(int),
                })
            }
            Ty::F16 | Ty::F32 | Ty::F64 => {
                let mut raw = [0u8; 8];
                raw[..bytes.len()].copy_from_slice(bytes);
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::FloatBits(u64::from_le_bytes(raw)),
                })
            }
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
                let mut raw = [0u8; 8];
                raw.copy_from_slice(bytes);
                let addr = u64::from_le_bytes(raw);
                // A loaded pointer whose address names no allocation is a
                // no-provenance value (`DanglingPtr`), not an error — the
                // provenance check is deferred to dereference (`expect_pointer`).
                let kind = state.memory.resolve_pointer_kind(addr);
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind,
                })
            }
            // B2: decode a fat pointer's two-lane image (byte count pre-checked
            // as 16 by the size gate above): data address then metadata. The
            // metadata decodes at the kind's canonical type (pointer-sized
            // unsigned length for Slice/Str, thin Ptr for TraitObject).
            Ty::FatPtr(kind) => {
                self.require_fat_pointer_layout(block)?;
                let mut raw = [0u8; 8];
                raw.copy_from_slice(&bytes[..8]);
                let addr = u64::from_le_bytes(raw);
                // An empty slice / len-0 `&[T]` carries a dangling data lane
                // (`NonNull::dangling`); resolve it as a no-provenance value.
                let data_kind = state.memory.resolve_pointer_kind(addr);
                let data = InterpretValue { ty: Ty::Ptr, kind: data_kind };
                let canonical = kind.metadata_ty(self.pointer_bits()).ok_or_else(|| {
                    type_error(block, format!("Load: {ty} has no metadata type"))
                })?;
                let metadata = self.decode_value(&canonical, &bytes[8..], state, block)?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::FatPtr {
                        data: Box::new(data),
                        metadata: Box::new(metadata),
                    },
                })
            }
            Ty::Unit => Ok(InterpretValue {
                ty: Ty::Unit,
                kind: InterpretValueKind::Unit,
            }),
            Ty::Vector(elem, lanes) => {
                let elem_size = self.byte_size(elem, block)? as usize;
                let mut values = Vec::with_capacity(*lanes as usize);
                if elem_size == 0 {
                    for _ in 0..*lanes {
                        values.push(self.decode_value(elem, &[], state, block)?);
                    }
                } else {
                    for chunk in bytes.chunks_exact(elem_size) {
                        values.push(self.decode_value(elem, chunk, state, block)?);
                    }
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Vector(values),
                })
            }
            Ty::Array(elem, len) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                let elem_size = self.byte_size(&elem_ty, block)? as usize;
                let mut values = Vec::with_capacity(*len as usize);
                if elem_size == 0 {
                    for _ in 0..*len {
                        values.push(self.decode_value(&elem_ty, &[], state, block)?);
                    }
                } else {
                    for chunk in bytes.chunks_exact(elem_size) {
                        values.push(self.decode_value(&elem_ty, chunk, state, block)?);
                    }
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Array(values),
                })
            }
            // Decode an aggregate's C-layout byte image back into an `Aggregate`
            // value: read each field from its computed offset. The byte image
            // size was already checked against `byte_size(ty)` above, so each
            // field slice is in range. `Ty::Struct` and `Ty::Tuple` use the same
            // layout (via `aggregate_value_layout`), so this is the exact inverse
            // of `encode_value` — the field offsets match byte-for-byte.
            Ty::Struct(_) | Ty::Tuple(_) => {
                let layout = self.aggregate_value_layout(ty, block)?;
                let mut values = Vec::with_capacity(layout.field_offsets.len());
                for (offset, field_ty) in &layout.field_offsets {
                    let f_size = self.byte_size(field_ty, block)? as usize;
                    let start = *offset as usize;
                    let chunk = &bytes[start..start + f_size];
                    values.push(self.decode_value(field_ty, chunk, state, block)?);
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            // Decode an enum's canonical tagged-union byte image: read the tag
            // at offset 0, resolve the variant it names, then decode that
            // variant's fields from the shared payload region — the exact
            // inverse of the enum `encode_value` arm. A tag value matching no
            // variant discriminant is a corrupted/foreign image and fails
            // closed (never a mis-tagged value).
            Ty::Enum(_) => {
                let layout = self.enum_layout(ty, block)?;
                let (variant_idx, tag_val) = match &layout.byte_view {
                    // No tag lane exists to read: the sole variant IS the
                    // answer, and the tag operand is synthesized from it. This
                    // is total — unlike the tagged arms there is no byte
                    // pattern that could name a variant the enum does not have.
                    EnumByteView::Untagged { variant } => {
                        (*variant, synthesized_tag_value(&layout, *variant, block)?)
                    }
                    EnumByteView::Direct { tag_offset } => {
                        let start = *tag_offset as usize;
                        let tag_val = self.decode_value(
                            &layout.tag_ty,
                            &bytes[start..start + layout.tag_size as usize],
                            state,
                            block,
                        )?;
                        let disc = tag_int_discriminant(expect_int_value(&tag_val, block)?);
                        let variant_idx = layout.variant_by_discriminant(disc).ok_or_else(|| {
                            type_error(
                                block,
                                format!(
                                    "Load: enum tag value {disc} does not match any variant discriminant of {ty}"
                                ),
                            )
                        })?;
                        (variant_idx, tag_val)
                    }
                    EnumByteView::Niche {
                        untagged_variant,
                        niche_variants_start,
                        niche_variants_end,
                        niche_start,
                        niche_offset,
                        niche_size,
                    } => {
                        let start = *niche_offset as usize;
                        let mut raw = [0u8; 16];
                        raw[..*niche_size as usize]
                            .copy_from_slice(&bytes[start..start + *niche_size as usize]);
                        let lane_bits = (*niche_size * 8) as u32;
                        let mask = int_mask(lane_bits).ok_or_else(|| {
                            type_error(block, format!("unsupported niche lane width {lane_bits}"))
                        })?;
                        let relative = u128::from_le_bytes(raw).wrapping_sub(*niche_start) & mask;
                        let range_len = u128::from(*niche_variants_end - *niche_variants_start);
                        let variant_idx = if relative <= range_len {
                            let candidate = *niche_variants_start as usize + relative as usize;
                            if candidate == *untagged_variant {
                                return Err(type_error(
                                    block,
                                    format!(
                                        "Load: enum {ty} byte image uses the untagged variant's dead niche value"
                                    ),
                                ));
                            }
                            candidate
                        } else {
                            *untagged_variant
                        };
                        let tag_val = synthesized_tag_value(&layout, variant_idx, block)?;
                        (variant_idx, tag_val)
                    }
                };
                let fields = &layout.variant_field_offsets[variant_idx];
                let mut values = Vec::with_capacity(fields.len() + 1);
                values.push(tag_val);
                for (rel_offset, field_ty) in fields {
                    let f_size = self.byte_size(field_ty, block)? as usize;
                    let start = (layout.payload_offset + rel_offset) as usize;
                    let chunk = &bytes[start..start + f_size];
                    values.push(self.decode_value(field_ty, chunk, state, block)?);
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            _ => Err(type_error(block, format!("Load: cannot decode type {ty}"))),
        }
    }

    fn eval_binop(
        &self,
        op: BinOp,
        ty: &Ty,
        lhs: &InterpretValue,
        rhs: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        if ty.is_vector() {
            return self.eval_vector_binop(op, ty, lhs, rhs, block);
        }

        expect_ty(lhs, ty, block)?;
        expect_ty(rhs, ty, block)?;
        if ty.is_float() {
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::FloatBits(eval_float_binop(
                    op,
                    ty,
                    expect_float_bits(lhs, block)?,
                    expect_float_bits(rhs, block)?,
                    block,
                )?),
            });
        }
        if matches!(ty, Ty::Bool) {
            return Ok(InterpretValue::bool(eval_bool_binop(
                op,
                expect_bool_value(lhs, block)?,
                expect_bool_value(rhs, block)?,
                block,
            )?));
        }
        let lhs = expect_int_value(lhs, block)?;
        let rhs = expect_int_value(rhs, block)?;
        let result = eval_int_binop(op, lhs, rhs, block)?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Int(result),
        })
    }

    fn eval_vector_binop(
        &self,
        op: BinOp,
        ty: &Ty,
        lhs: &InterpretValue,
        rhs: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let (elem_ty, lane_count) = ty.vector_shape().ok_or_else(|| {
            err(
                InterpretErrorCode::TypeError,
                block,
                format!("vector operation on non-vector type {ty}"),
            )
        })?;

        if lane_count == 0 {
            return Err(err(
                InterpretErrorCode::UnsupportedVectorShape,
                block,
                "zero-lane vectors are not executable",
            ));
        }
        expect_ty(lhs, ty, block)?;
        expect_ty(rhs, ty, block)?;
        let lhs_lanes = expect_vector_lanes(lhs, lane_count, block)?;
        let rhs_lanes = expect_vector_lanes(rhs, lane_count, block)?;
        let mut lanes = Vec::with_capacity(lane_count as usize);
        for (lhs, rhs) in lhs_lanes.iter().zip(rhs_lanes) {
            expect_ty(lhs, elem_ty, block)?;
            expect_ty(rhs, elem_ty, block)?;
            if matches!(elem_ty, Ty::Bool) {
                lanes.push(InterpretValue::bool(eval_bool_binop(
                    op,
                    expect_bool_value(lhs, block)?,
                    expect_bool_value(rhs, block)?,
                    block,
                )?));
            } else if elem_ty.is_float() {
                lanes.push(InterpretValue {
                    ty: elem_ty.clone(),
                    kind: InterpretValueKind::FloatBits(eval_float_binop(
                        op,
                        elem_ty,
                        expect_float_bits(lhs, block)?,
                        expect_float_bits(rhs, block)?,
                        block,
                    )?),
                });
            } else {
                let lhs = expect_int_value(lhs, block)?;
                let rhs = expect_int_value(rhs, block)?;
                lanes.push(InterpretValue {
                    ty: elem_ty.clone(),
                    kind: InterpretValueKind::Int(eval_int_binop(op, lhs, rhs, block)?),
                });
            }
        }
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Vector(lanes),
        })
    }

    fn eval_unop(
        &self,
        op: UnOp,
        ty: &Ty,
        operand: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        if let Ty::Vector(elem_ty, lanes) = ty {
            if *lanes == 0 {
                return Err(err(
                    InterpretErrorCode::UnsupportedVectorShape,
                    block,
                    "zero-lane vectors are not executable",
                ));
            }
            expect_ty(operand, ty, block)?;
            let lane_values = expect_vector_lanes(operand, *lanes, block)?;
            let lanes = lane_values
                .iter()
                .map(|lane| {
                    expect_ty(lane, elem_ty, block)?;
                    if matches!(elem_ty.as_ref(), Ty::Bool) {
                        if op != UnOp::Not {
                            return Err(type_error(
                                block,
                                format!("{op} is not a boolean unary operation"),
                            ));
                        }
                        Ok(InterpretValue::bool(!expect_bool_value(lane, block)?))
                    } else if elem_ty.is_float() {
                        Ok(InterpretValue {
                            ty: elem_ty.as_ref().clone(),
                            kind: InterpretValueKind::FloatBits(eval_float_unop(
                                op,
                                elem_ty,
                                expect_float_bits(lane, block)?,
                                block,
                            )?),
                        })
                    } else {
                        let int = expect_int_value(lane, block)?;
                        Ok(InterpretValue {
                            ty: elem_ty.as_ref().clone(),
                            kind: InterpretValueKind::Int(eval_int_unop(op, int, block)?),
                        })
                    }
                })
                .collect::<InterpretResult<Vec<_>>>()?;
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Vector(lanes),
            });
        }

        expect_ty(operand, ty, block)?;
        if ty.is_float() {
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::FloatBits(eval_float_unop(
                    op,
                    ty,
                    expect_float_bits(operand, block)?,
                    block,
                )?),
            });
        }
        let int = expect_int_value(operand, block)?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Int(eval_int_unop(op, int, block)?),
        })
    }

    fn eval_overflow(
        &self,
        op: OverflowOp,
        ty: &Ty,
        lhs: &InterpretValue,
        rhs: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<(InterpretValue, bool)> {
        expect_ty(lhs, ty, block)?;
        expect_ty(rhs, ty, block)?;
        let lhs = expect_int_value(lhs, block)?;
        let rhs = expect_int_value(rhs, block)?;
        let (value, overflow) = eval_int_overflow(op, lhs, rhs, block)?;
        Ok((
            InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Int(value),
            },
            overflow,
        ))
    }

    fn eval_icmp(
        &self,
        op: ICmpOp,
        ty: &Ty,
        lhs: &InterpretValue,
        rhs: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        if let Ty::Vector(elem_ty, lanes) = ty {
            if *lanes == 0 {
                return Err(err(
                    InterpretErrorCode::UnsupportedVectorShape,
                    block,
                    "zero-lane vectors are not executable",
                ));
            }
            expect_ty(lhs, ty, block)?;
            expect_ty(rhs, ty, block)?;
            let lhs_lanes = expect_vector_lanes(lhs, *lanes, block)?;
            let rhs_lanes = expect_vector_lanes(rhs, *lanes, block)?;
            let mut result = Vec::with_capacity(*lanes as usize);
            for (lhs, rhs) in lhs_lanes.iter().zip(rhs_lanes) {
                expect_ty(lhs, elem_ty, block)?;
                expect_ty(rhs, elem_ty, block)?;
                if matches!(elem_ty.as_ref(), Ty::Bool) {
                    result.push(InterpretValue::bool(eval_bool_icmp(
                        op,
                        expect_bool_value(lhs, block)?,
                        expect_bool_value(rhs, block)?,
                    )));
                    continue;
                }
                result.push(InterpretValue::bool(eval_int_icmp(
                    op,
                    expect_int_value(lhs, block)?,
                    expect_int_value(rhs, block)?,
                )));
            }
            return Ok(InterpretValue {
                ty: ty.comparison_result_ty(),
                kind: InterpretValueKind::Vector(result),
            });
        }

        expect_ty(lhs, ty, block)?;
        expect_ty(rhs, ty, block)?;
        if matches!(ty, Ty::Bool) {
            return Ok(InterpretValue::bool(eval_bool_icmp(
                op,
                expect_bool_value(lhs, block)?,
                expect_bool_value(rhs, block)?,
            )));
        }
        Ok(InterpretValue::bool(eval_int_icmp(
            op,
            expect_int_value(lhs, block)?,
            expect_int_value(rhs, block)?,
        )))
    }

    fn eval_fcmp(
        &self,
        op: FCmpOp,
        ty: &Ty,
        lhs: &InterpretValue,
        rhs: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        if let Ty::Vector(elem_ty, lanes) = ty {
            if *lanes == 0 {
                return Err(err(
                    InterpretErrorCode::UnsupportedVectorShape,
                    block,
                    "zero-lane vectors are not executable",
                ));
            }
            expect_ty(lhs, ty, block)?;
            expect_ty(rhs, ty, block)?;
            let lhs_lanes = expect_vector_lanes(lhs, *lanes, block)?;
            let rhs_lanes = expect_vector_lanes(rhs, *lanes, block)?;
            let mut result = Vec::with_capacity(*lanes as usize);
            for (lhs, rhs) in lhs_lanes.iter().zip(rhs_lanes) {
                expect_ty(lhs, elem_ty, block)?;
                expect_ty(rhs, elem_ty, block)?;
                result.push(InterpretValue::bool(eval_float_fcmp(
                    op,
                    elem_ty,
                    expect_float_bits(lhs, block)?,
                    expect_float_bits(rhs, block)?,
                    block,
                )?));
            }
            return Ok(InterpretValue {
                ty: ty.comparison_result_ty(),
                kind: InterpretValueKind::Vector(result),
            });
        }

        expect_ty(lhs, ty, block)?;
        expect_ty(rhs, ty, block)?;
        Ok(InterpretValue::bool(eval_float_fcmp(
            op,
            ty,
            expect_float_bits(lhs, block)?,
            expect_float_bits(rhs, block)?,
            block,
        )?))
    }

    fn eval_cast(
        &self,
        op: CastOp,
        src_ty: &Ty,
        dst_ty: &Ty,
        operand: &InterpretValue,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        reject_partial(operand, block, &format!("{op}"))?;
        expect_ty(operand, src_ty, block)?;
        let kind = match op {
            CastOp::Trunc => {
                let int = expect_integer_resize_value(operand, block)?;
                if *dst_ty == Ty::Bool {
                    InterpretValueKind::Bool(int.raw & 1 != 0)
                } else {
                    let (dst_bits, dst_signed) = int_shape(dst_ty).ok_or_else(|| {
                        type_error(block, format!("{op}: destination {dst_ty} is not integer"))
                    })?;
                    InterpretValueKind::Int(
                        InterpretInt::from_raw(dst_bits, dst_signed, int.raw).ok_or_else(|| {
                            type_error(block, format!("unsupported integer width {dst_bits}"))
                        })?,
                    )
                }
            }
            CastOp::ZExt => {
                let int = expect_integer_resize_value(operand, block)?;
                let (dst_bits, dst_signed) = int_shape(dst_ty).ok_or_else(|| {
                    type_error(block, format!("{op}: destination {dst_ty} is not integer"))
                })?;
                InterpretValueKind::Int(
                    InterpretInt::from_raw(dst_bits, dst_signed, int.raw).ok_or_else(|| {
                        type_error(block, format!("unsupported integer width {dst_bits}"))
                    })?,
                )
            }
            CastOp::SExt => {
                let int = expect_integer_resize_value(operand, block)?;
                let (dst_bits, dst_signed) = int_shape(dst_ty).ok_or_else(|| {
                    type_error(block, format!("{op}: destination {dst_ty} is not integer"))
                })?;
                InterpretValueKind::Int(
                    InterpretInt::from_i128(dst_bits, dst_signed, int.as_signed()).ok_or_else(
                        || type_error(block, format!("unsupported integer width {dst_bits}")),
                    )?,
                )
            }
            CastOp::FPTrunc | CastOp::FPExt => {
                if !src_ty.is_float() || !dst_ty.is_float() {
                    return Err(type_error(
                        block,
                        format!("{op}: expected float-to-float cast, got {src_ty} to {dst_ty}"),
                    ));
                }
                let value = float_as_f64(src_ty, expect_float_bits(operand, block)?, block)?;
                InterpretValueKind::FloatBits(float_bits_from_f64(dst_ty, value, block)?)
            }
            CastOp::FPToUI | CastOp::FPToSI => {
                if !src_ty.is_float() {
                    return Err(type_error(
                        block,
                        format!("{op}: source {src_ty} is not float"),
                    ));
                }
                let (dst_bits, dst_signed) = int_shape(dst_ty).ok_or_else(|| {
                    type_error(block, format!("{op}: destination {dst_ty} is not integer"))
                })?;
                let value = float_as_f64(src_ty, expect_float_bits(operand, block)?, block)?;
                // Float->int on NaN or an out-of-range magnitude is UNDEFINED
                // (matches LLVM fptoui/fptosi; see docs/ub-numerics-policy.md
                // §2). We do NOT saturate or map NaN to 0 — a frontend must
                // discharge the range obligation or insert explicit saturation.
                if value.is_nan() {
                    return Err(ub(
                        block,
                        format!("{op}: NaN cannot be converted to integer"),
                    ));
                }
                let (lo, hi) = if matches!(op, CastOp::FPToUI) {
                    (0.0_f64, 2f64.powi(dst_bits as i32))
                } else {
                    let half = 2f64.powi(dst_bits as i32 - 1);
                    (-half, half)
                };
                if value < lo || value >= hi {
                    return Err(ub(
                        block,
                        format!("{op}: {value} out of range for {dst_ty}"),
                    ));
                }
                let raw = if matches!(op, CastOp::FPToUI) {
                    float_to_u128(value)
                } else {
                    float_to_i128(value) as u128
                };
                InterpretValueKind::Int(
                    InterpretInt::from_raw(dst_bits, dst_signed, raw).ok_or_else(|| {
                        type_error(block, format!("unsupported integer width {dst_bits}"))
                    })?,
                )
            }
            CastOp::FPToUISat | CastOp::FPToSISat => {
                if !src_ty.is_float() {
                    return Err(type_error(
                        block,
                        format!("{op}: source {src_ty} is not float"),
                    ));
                }
                let (dst_bits, dst_signed) = int_shape(dst_ty).ok_or_else(|| {
                    type_error(block, format!("{op}: destination {dst_ty} is not integer"))
                })?;
                let value = float_as_f64(src_ty, expect_float_bits(operand, block)?, block)?;
                // Rust's `f as iN` / `f as uN` is SATURATING (stabilized 1.45;
                // codegen lowers it to LLVM fptosi.sat / fptoui.sat). Unlike the
                // raw FPToUI/FPToSI above (out-of-range/NaN is UB), NaN maps to 0
                // and out-of-range magnitudes clamp to the destination's
                // MIN/MAX. Boundary: `hi` (= 2^(N-1) signed / 2^N unsigned) is
                // NOT representable in the destination, so `value >= hi`
                // saturates to MAX; `lo` (= -2^(N-1) signed / 0 unsigned) IS
                // representable, so `value == lo` truncates in-range while
                // `value < lo` saturates to MIN. See docs/ub-numerics-policy.md §2.
                let signed = matches!(op, CastOp::FPToSISat);
                let raw: u128 = if value.is_nan() {
                    0
                } else {
                    let (lo, hi) = if signed {
                        let half = 2f64.powi(dst_bits as i32 - 1);
                        (-half, half)
                    } else {
                        (0.0_f64, 2f64.powi(dst_bits as i32))
                    };
                    if value >= hi {
                        // Saturate to the destination maximum.
                        if signed {
                            // iN::MAX = 2^(N-1) - 1  ->  0b0111…1
                            if dst_bits >= 128 {
                                i128::MAX as u128
                            } else {
                                (1u128 << (dst_bits - 1)) - 1
                            }
                        } else {
                            // uN::MAX = 2^N - 1  ->  0b111…1
                            if dst_bits >= 128 {
                                u128::MAX
                            } else {
                                (1u128 << dst_bits) - 1
                            }
                        }
                    } else if value < lo {
                        // Saturate to the destination minimum.
                        if signed {
                            // iN::MIN = -2^(N-1)  ->  0b1000…0 (two's complement)
                            1u128 << (dst_bits - 1)
                        } else {
                            0
                        }
                    } else {
                        // In range: truncate toward zero (exact, no rounding).
                        if signed {
                            float_to_i128(value) as u128
                        } else {
                            float_to_u128(value)
                        }
                    }
                };
                InterpretValueKind::Int(
                    InterpretInt::from_raw(dst_bits, dst_signed, raw).ok_or_else(|| {
                        type_error(block, format!("unsupported integer width {dst_bits}"))
                    })?,
                )
            }
            CastOp::UIToFP | CastOp::SIToFP => {
                if !dst_ty.is_float() {
                    return Err(type_error(
                        block,
                        format!("{op}: destination {dst_ty} is not float"),
                    ));
                }
                let int = expect_int_value(operand, block)?;
                let value = if matches!(op, CastOp::UIToFP) {
                    int.as_unsigned() as f64
                } else {
                    int.as_signed() as f64
                };
                InterpretValueKind::FloatBits(float_bits_from_f64(dst_ty, value, block)?)
            }
            CastOp::PtrToInt => {
                let (dst_bits, dst_signed) = int_shape(dst_ty).ok_or_else(|| {
                    type_error(block, format!("{op}: destination {dst_ty} is not integer"))
                })?;
                let address = match operand.kind {
                    InterpretValueKind::NullPtr => 0,
                    InterpretValueKind::Ptr(ptr) => state.memory.address(ptr, block, "PtrToInt")?,
                    // A no-provenance pointer exposes its raw address (this is
                    // exactly how empty-collection iterators compare begin==end).
                    InterpretValueKind::DanglingPtr(addr) => addr,
                    _ => {
                        return Err(type_error(
                            block,
                            format!("{op}: source {src_ty} is not pointer-like"),
                        ));
                    }
                };
                InterpretValueKind::Int(
                    InterpretInt::from_raw(dst_bits, dst_signed, u128::from(address)).ok_or_else(
                        || type_error(block, format!("unsupported integer width {dst_bits}")),
                    )?,
                )
            }
            CastOp::IntToPtr => {
                if !is_pointer_like_ty(dst_ty) {
                    return Err(type_error(
                        block,
                        format!("{op}: destination {dst_ty} is not pointer-like"),
                    ));
                }
                let int = expect_int_value(operand, block)?;
                let address = u64::try_from(int.as_unsigned()).map_err(|_| {
                    ub(
                        block,
                        format!("{op}: address {} does not fit u64", int.as_unsigned()),
                    )
                })?;
                // A nonzero address that names no allocation becomes a legal
                // no-provenance pointer VALUE (`NonNull::dangling`); the
                // provenance check is deferred to dereference.
                state.memory.resolve_pointer_kind(address)
            }
            CastOp::PtrToPtr => {
                if !is_pointer_like_ty(src_ty) || !is_pointer_like_ty(dst_ty) {
                    return Err(type_error(
                        block,
                        format!("{op}: expected pointer-like cast, got {src_ty} to {dst_ty}"),
                    ));
                }
                match operand.kind {
                    InterpretValueKind::Ptr(ptr) => InterpretValueKind::Ptr(ptr),
                    InterpretValueKind::NullPtr => InterpretValueKind::NullPtr,
                    InterpretValueKind::DanglingPtr(addr) => InterpretValueKind::DanglingPtr(addr),
                    _ => {
                        return Err(type_error(
                            block,
                            format!("{op}: source {src_ty} is not pointer-like"),
                        ));
                    }
                }
            }
            CastOp::Bitcast => {
                // Pointer-like operands have a target-dependent width; resolve
                // it from the module's target, falling back to the default
                // pointer width when no target is pinned.
                let pointer_bits = self.pointer_bits();
                let src_bits = src_ty.bit_width_with(pointer_bits).ok_or_else(|| {
                    type_error(block, format!("{op}: source {src_ty} has no bit width"))
                })?;
                let dst_bits = dst_ty.bit_width_with(pointer_bits).ok_or_else(|| {
                    type_error(
                        block,
                        format!("{op}: destination {dst_ty} has no bit width"),
                    )
                })?;
                if src_bits != dst_bits {
                    return Err(type_error(
                        block,
                        format!("{op}: bit width mismatch {src_bits} vs {dst_bits}"),
                    ));
                }
                self.eval_bitcast(src_ty, dst_ty, operand, state, block)?
            }
            CastOp::Transmute | CastOp::ReifyFnPointer => {
                return Err(err(
                    InterpretErrorCode::UnsupportedCast,
                    block,
                    format!("cast op {op} is intentionally excluded from this interpreter slice"),
                ));
            }
        };
        Ok(InterpretValue {
            ty: dst_ty.clone(),
            kind,
        })
    }

    fn eval_bitcast(
        &self,
        src_ty: &Ty,
        dst_ty: &Ty,
        operand: &InterpretValue,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretValueKind> {
        if src_ty == dst_ty {
            return Ok(operand.kind.clone());
        }
        if let Some((bits, signed)) = int_shape(dst_ty) {
            let raw = match operand.kind {
                InterpretValueKind::Int(int) => int.raw,
                InterpretValueKind::FloatBits(bits) => u128::from(bits),
                InterpretValueKind::Ptr(ptr) => {
                    u128::from(state.memory.address(ptr, block, "Bitcast")?)
                }
                InterpretValueKind::NullPtr => 0,
                InterpretValueKind::DanglingPtr(addr) => u128::from(addr),
                _ => {
                    return Err(type_error(
                        block,
                        format!("Bitcast: unsupported source type {src_ty}"),
                    ));
                }
            };
            return Ok(InterpretValueKind::Int(
                InterpretInt::from_raw(bits, signed, raw).ok_or_else(|| {
                    type_error(block, format!("unsupported integer width {bits}"))
                })?,
            ));
        }
        if dst_ty.is_float() {
            let raw = match operand.kind {
                InterpretValueKind::Int(int) => int.raw,
                InterpretValueKind::FloatBits(bits) => u128::from(bits),
                _ => {
                    return Err(type_error(
                        block,
                        format!("Bitcast: unsupported source type {src_ty}"),
                    ));
                }
            };
            return Ok(InterpretValueKind::FloatBits(float_bits_from_raw(
                dst_ty, raw, block,
            )?));
        }
        if is_pointer_like_ty(dst_ty) {
            return match operand.kind {
                InterpretValueKind::Ptr(ptr) => Ok(InterpretValueKind::Ptr(ptr)),
                InterpretValueKind::NullPtr => Ok(InterpretValueKind::NullPtr),
                InterpretValueKind::DanglingPtr(addr) => Ok(InterpretValueKind::DanglingPtr(addr)),
                InterpretValueKind::Int(int) => {
                    let address = u64::try_from(int.as_unsigned()).map_err(|_| {
                        ub(
                            block,
                            format!("Bitcast: address {} does not fit u64", int.as_unsigned()),
                        )
                    })?;
                    Ok(state.memory.resolve_pointer_kind(address))
                }
                _ => Err(type_error(
                    block,
                    format!("Bitcast: unsupported destination type {dst_ty}"),
                )),
            };
        }
        Err(type_error(
            block,
            format!("Bitcast: unsupported destination type {dst_ty}"),
        ))
    }

    fn eval_select(
        &self,
        ty: &Ty,
        cond: &InterpretValue,
        then_val: &InterpretValue,
        else_val: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        // The condition is inspected; the arms are transported (either may be a
        // poison value passed through unchanged), so only `cond` is gated here.
        reject_partial(cond, block, "select")?;
        expect_ty(then_val, ty, block)?;
        expect_ty(else_val, ty, block)?;

        if let Ty::Vector(_, lanes) = ty {
            if *lanes == 0 {
                return Err(err(
                    InterpretErrorCode::UnsupportedVectorShape,
                    block,
                    "zero-lane vectors are not executable",
                ));
            }
            let expected_cond_ty = ty.select_condition_ty();
            expect_ty(cond, &expected_cond_ty, block)?;
            let cond_lanes = expect_vector_lanes(cond, *lanes, block)?;
            let then_lanes = expect_vector_lanes(then_val, *lanes, block)?;
            let else_lanes = expect_vector_lanes(else_val, *lanes, block)?;
            let mut result = Vec::with_capacity(*lanes as usize);
            for ((cond, then_val), else_val) in cond_lanes.iter().zip(then_lanes).zip(else_lanes) {
                match cond.as_bool() {
                    Some(true) => result.push(then_val.clone()),
                    Some(false) => result.push(else_val.clone()),
                    None => {
                        return Err(type_error(
                            block,
                            format!("vector select condition lane must be bool, got {}", cond.ty),
                        ));
                    }
                }
            }
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Vector(result),
            });
        }

        match cond.as_bool() {
            Some(true) => Ok(then_val.clone()),
            Some(false) => Ok(else_val.clone()),
            None => Err(type_error(
                block,
                format!("select over {ty} requires bool condition, got {}", cond.ty),
            )),
        }
    }

    fn eval_extract_field(
        &self,
        field_ty: &Ty,
        aggregate: &InterpretValue,
        field: u32,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        reject_partial(aggregate, block, "extract_field")?;
        let value = match &aggregate.kind {
            InterpretValueKind::Aggregate(values) => values.get(field as usize),
            InterpretValueKind::Record(values) => {
                values.get(field as usize).map(|(_, value)| value)
            }
            // B6 (RFC TRUST_IR_V2): a first-class closure value exposes its CAPTURES
            // as fields, in capture order — the register-level read a by-value
            // closure-env consumer emits. The `func` is not a field (it has no
            // runtime layout for a non-dyn closure); captures are typed against
            // the resolved ClosureTy by construction (`constant_to_value` /
            // `eval_insert_field`), and `expect_ty` below re-checks the read.
            InterpretValueKind::Closure { captures, .. } => captures.get(field as usize),
            _ => {
                return Err(type_error(
                    block,
                    format!(
                        "extract_field requires aggregate or record, got {}",
                        aggregate.ty
                    ),
                ));
            }
        }
        .ok_or_else(|| {
            err(
                InterpretErrorCode::UndefinedBehavior,
                block,
                format!("field {field} is out of bounds for {}", aggregate.ty),
            )
        })?;
        expect_ty(value, field_ty, block)?;
        Ok(value.clone())
    }

    fn eval_insert_field(
        &self,
        aggregate_ty: &Ty,
        aggregate: &InterpretValue,
        field: u32,
        value: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        reject_partial(aggregate, block, "insert_field")?;
        reject_partial(value, block, "insert_field value")?;
        expect_ty(aggregate, aggregate_ty, block)?;
        match &aggregate.kind {
            InterpretValueKind::Aggregate(values) => {
                let Some(existing) = values.get(field as usize) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("field {field} is out of bounds for {}", aggregate.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let mut values = values.clone();
                values[field as usize] = value.clone();
                Ok(InterpretValue {
                    ty: aggregate_ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            InterpretValueKind::Record(values) => {
                let Some((_, existing)) = values.get(field as usize) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("field {field} is out of bounds for {}", aggregate.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let mut values = values.clone();
                values[field as usize].1 = value.clone();
                Ok(InterpretValue {
                    ty: aggregate_ty.clone(),
                    kind: InterpretValueKind::Record(values),
                })
            }
            // B6: a closure value's captures are writable fields (capture order) —
            // the register-level construct lane (seed + per-capture InsertField).
            // The replacement is typed against the EXISTING capture (itself typed
            // against the ClosureTy at materialization); `func` is untouched.
            InterpretValueKind::Closure { func, captures } => {
                let Some(existing) = captures.get(field as usize) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("field {field} is out of bounds for {}", aggregate.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let mut captures = captures.clone();
                captures[field as usize] = value.clone();
                Ok(InterpretValue {
                    ty: aggregate_ty.clone(),
                    kind: InterpretValueKind::Closure {
                        func: *func,
                        captures,
                    },
                })
            }
            _ => Err(type_error(
                block,
                format!(
                    "insert_field requires aggregate or record, got {}",
                    aggregate.ty
                ),
            )),
        }
    }

    fn eval_extract_element(
        &self,
        elem_ty: &Ty,
        array: &InterpretValue,
        index: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let index = runtime_index(index, block)?;
        let value = match &array.kind {
            InterpretValueKind::Vector(values)
            | InterpretValueKind::Array(values)
            | InterpretValueKind::Sequence(values)
            | InterpretValueKind::Aggregate(values) => values.get(index),
            _ => {
                return Err(type_error(
                    block,
                    format!(
                        "extract_element requires vector/array/sequence, got {}",
                        array.ty
                    ),
                ));
            }
        }
        .ok_or_else(|| {
            err(
                InterpretErrorCode::UndefinedBehavior,
                block,
                format!("element {index} is out of bounds for {}", array.ty),
            )
        })?;
        expect_ty(value, elem_ty, block)?;
        Ok(value.clone())
    }

    fn eval_insert_element(
        &self,
        result_ty: &Ty,
        array: &InterpretValue,
        index: &InterpretValue,
        value: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        expect_ty(array, result_ty, block)?;
        let index = runtime_index(index, block)?;
        match &array.kind {
            InterpretValueKind::Vector(values) => {
                let Some(existing) = values.get(index) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("element {index} is out of bounds for {}", array.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let mut values = values.clone();
                values[index] = value.clone();
                Ok(InterpretValue {
                    ty: result_ty.clone(),
                    kind: InterpretValueKind::Vector(values),
                })
            }
            InterpretValueKind::Array(values) => {
                let Some(existing) = values.get(index) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("element {index} is out of bounds for {}", array.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let mut values = values.clone();
                values[index] = value.clone();
                Ok(InterpretValue {
                    ty: result_ty.clone(),
                    kind: InterpretValueKind::Array(values),
                })
            }
            InterpretValueKind::Sequence(values) => {
                let Some(existing) = values.get(index) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("element {index} is out of bounds for {}", array.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let mut values = values.clone();
                values[index] = value.clone();
                Ok(InterpretValue {
                    ty: result_ty.clone(),
                    kind: InterpretValueKind::Sequence(values),
                })
            }
            InterpretValueKind::Aggregate(values) => {
                let Some(existing) = values.get(index) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("element {index} is out of bounds for {}", array.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let mut values = values.clone();
                values[index] = value.clone();
                Ok(InterpretValue {
                    ty: result_ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            _ => Err(type_error(
                block,
                format!(
                    "insert_element requires vector/array/sequence, got {}",
                    array.ty
                ),
            )),
        }
    }

    fn eval_dialect_op(
        &self,
        op: &DialectInst,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<Vec<InterpretValue>> {
        if op.dialect != vector::DIALECT {
            return Err(unsupported_dialect_op(block, op));
        }

        let operands = eval_args(state, block, &op.operands)?;
        let operand_tys = operands
            .iter()
            .map(|value| value.ty.clone())
            .collect::<Vec<_>>();
        let spec = vector::decode_with_operand_tys(op, &operand_tys)
            .map_err(|reason| vector_dialect_error(block, op, reason))?;

        match spec {
            VectorSpec::PackLanes(spec) => {
                let mut lanes = Vec::with_capacity(spec.lanes as usize);
                for operand in operands {
                    expect_ty(&operand, &spec.elem_ty, block)?;
                    lanes.push(operand);
                }
                Ok(vec![InterpretValue {
                    ty: spec.vector_ty,
                    kind: InterpretValueKind::Vector(lanes),
                }])
            }
            VectorSpec::ExtractLane(spec) => {
                let vector = &operands[0];
                expect_ty(vector, &spec.vector_ty, block)?;
                let lanes = expect_vector_lanes(vector, spec.lanes, block)?;
                let lane = lanes.get(spec.lane as usize).ok_or_else(|| {
                    err(
                        InterpretErrorCode::UnsupportedVectorShape,
                        block,
                        format!(
                            "{} lane {} is out of range for runtime vector value",
                            op.qualified_name(),
                            spec.lane
                        ),
                    )
                })?;
                expect_ty(lane, &spec.elem_ty, block)?;
                Ok(vec![lane.clone()])
            }
            VectorSpec::InsertLane(spec) => {
                let vector = &operands[0];
                let value = &operands[1];
                expect_ty(vector, &spec.vector_ty, block)?;
                expect_ty(value, &spec.elem_ty, block)?;
                let mut lanes = expect_vector_lanes(vector, spec.lanes, block)?.to_vec();
                let lane = lanes.get_mut(spec.lane as usize).ok_or_else(|| {
                    err(
                        InterpretErrorCode::UnsupportedVectorShape,
                        block,
                        format!(
                            "{} lane {} is out of range for runtime vector value",
                            op.qualified_name(),
                            spec.lane
                        ),
                    )
                })?;
                *lane = value.clone();
                Ok(vec![InterpretValue {
                    ty: spec.vector_ty,
                    kind: InterpretValueKind::Vector(lanes),
                }])
            }
            VectorSpec::MaskToBits(spec) => {
                let mask = &operands[0];
                expect_ty(mask, &spec.mask_ty, block)?;
                let lanes = expect_vector_lanes(mask, spec.lanes, block)?;
                let mut raw = 0u128;
                for (index, lane) in lanes.iter().enumerate() {
                    match lane.as_bool() {
                        Some(true) => raw |= 1u128 << index,
                        Some(false) => {}
                        None => {
                            return Err(type_error(
                                block,
                                format!(
                                    "{} mask lane {index} must be bool, got {}",
                                    op.qualified_name(),
                                    lane.ty
                                ),
                            ));
                        }
                    }
                }
                let (bits, signed) = int_shape(&spec.result_ty).ok_or_else(|| {
                    type_error(
                        block,
                        format!(
                            "{} result type {} is not an integer",
                            op.qualified_name(),
                            spec.result_ty
                        ),
                    )
                })?;
                Ok(vec![InterpretValue {
                    ty: spec.result_ty,
                    kind: InterpretValueKind::Int(
                        InterpretInt::from_raw(bits, signed, raw).ok_or_else(|| {
                            type_error(block, format!("unsupported integer width {bits}"))
                        })?,
                    ),
                }])
            }
            VectorSpec::Reduce(spec) => {
                let vector = &operands[0];
                expect_ty(vector, &spec.vector_ty, block)?;
                let lanes = expect_vector_lanes(vector, spec.lanes, block)?;
                let (bits, signed) = int_shape(&spec.elem_ty).ok_or_else(|| {
                    type_error(
                        block,
                        format!(
                            "{} element type {} is not an integer",
                            op.qualified_name(),
                            spec.elem_ty
                        ),
                    )
                })?;
                // Identity-seeded left fold. Both `add` (wrapping) and `or`
                // are associative + commutative with identity `0`, so the
                // lane order is observationally irrelevant: this scalar agrees
                // with any tree reduction a backend emits.
                let mut acc = 0u128;
                for (index, lane) in lanes.iter().enumerate() {
                    let lane_int = lane.as_int().ok_or_else(|| {
                        type_error(
                            block,
                            format!(
                                "{} reduce lane {index} must be {}, got {}",
                                op.qualified_name(),
                                spec.elem_ty,
                                lane.ty
                            ),
                        )
                    })?;
                    acc = match spec.kind {
                        vector::ReduceKind::Add => acc.wrapping_add(lane_int.as_unsigned()),
                        vector::ReduceKind::Or => acc | lane_int.as_unsigned(),
                    };
                }
                Ok(vec![InterpretValue {
                    ty: spec.elem_ty,
                    kind: InterpretValueKind::Int(
                        InterpretInt::from_raw(bits, signed, acc).ok_or_else(|| {
                            type_error(block, format!("unsupported integer width {bits}"))
                        })?,
                    ),
                }])
            }
            VectorSpec::Shuffle(spec) => {
                let vector = &operands[0];
                expect_ty(vector, &spec.vector_ty, block)?;
                let lanes = expect_vector_lanes(vector, spec.lanes, block)?;
                // `decode` already range-checked every index against `lanes`,
                // so each `get` below resolves; the explicit error keeps the
                // interpreter total even on a hand-built spec.
                let mut shuffled = Vec::with_capacity(spec.indices.len());
                for (result_lane, &source) in spec.indices.iter().enumerate() {
                    let lane = lanes.get(usize::from(source)).ok_or_else(|| {
                        err(
                            InterpretErrorCode::UnsupportedVectorShape,
                            block,
                            format!(
                                "{} shuffle index {source} for result lane {result_lane} is out of range for runtime vector value",
                                op.qualified_name()
                            ),
                        )
                    })?;
                    shuffled.push(lane.clone());
                }
                Ok(vec![InterpretValue {
                    ty: spec.vector_ty,
                    kind: InterpretValueKind::Vector(shuffled),
                }])
            }
            VectorSpec::Fma(spec) => {
                let a = &operands[0];
                let b = &operands[1];
                let c = &operands[2];
                expect_ty(a, &spec.vector_ty, block)?;
                expect_ty(b, &spec.vector_ty, block)?;
                expect_ty(c, &spec.vector_ty, block)?;
                let a_lanes = expect_vector_lanes(a, spec.lanes, block)?;
                let b_lanes = expect_vector_lanes(b, spec.lanes, block)?;
                let c_lanes = expect_vector_lanes(c, spec.lanes, block)?;
                let mut out = Vec::with_capacity(spec.lanes as usize);
                for index in 0..spec.lanes as usize {
                    let a_bits = expect_float_bits(&a_lanes[index], block)?;
                    let b_bits = expect_float_bits(&b_lanes[index], block)?;
                    let c_bits = expect_float_bits(&c_lanes[index], block)?;
                    // Single-rounding fused multiply-add (`a*b + c`) per lane,
                    // matching IEEE-754 fma / hardware VFMADD semantics.
                    let result_bits = match spec.elem_ty {
                        Ty::F32 => {
                            let value = f32::from_bits(a_bits as u32).mul_add(
                                f32::from_bits(b_bits as u32),
                                f32::from_bits(c_bits as u32),
                            );
                            u64::from(value.to_bits())
                        }
                        Ty::F64 => {
                            let value = f64::from_bits(a_bits)
                                .mul_add(f64::from_bits(b_bits), f64::from_bits(c_bits));
                            value.to_bits()
                        }
                        ref other => {
                            return Err(type_error(
                                block,
                                format!(
                                    "{} unsupported fma element type {other}",
                                    op.qualified_name()
                                ),
                            ));
                        }
                    };
                    out.push(InterpretValue {
                        ty: spec.elem_ty.clone(),
                        kind: InterpretValueKind::FloatBits(result_bits),
                    });
                }
                Ok(vec![InterpretValue {
                    ty: spec.vector_ty,
                    kind: InterpretValueKind::Vector(out),
                }])
            }
        }
    }
}

impl Default for Interpreter<'_> {
    fn default() -> Self {
        Self::new()
    }
}

struct ExecState {
    values: BTreeMap<ValueId, InterpretValue>,
    memory: MemoryState,
    /// Lazily-materialized storage for module-level globals addressed by
    /// `Inst::GlobalAddr`. The first address-of a given global allocates a
    /// backing region (writing its initializer, if any) and caches the
    /// pointer here so repeated `GlobalAddr` of the same global alias the
    /// same storage and stores through a `mutable` global persist.
    globals: BTreeMap<GlobalId, InterpretPointer>,
    /// Open binding frames (quantifier-lowering scopes) keyed by frame id. Each
    /// frame is a fixed slot vector sized at `OpenFrame` time; `BindSlot` writes,
    /// `LoadSlot` reads, `CloseFrame` removes. The `OpenFrame` result value is a
    /// `Frame(id)` handle.
    frames: BTreeMap<u64, Vec<Option<InterpretValue>>>,
    next_frame_id: u64,
    steps: u64,
    remaining_fuel: u64,
}

impl ExecState {
    fn tick(&mut self, block: BlockId) -> InterpretResult<()> {
        if self.remaining_fuel == 0 {
            return Err(err(
                InterpretErrorCode::OutOfFuel,
                block,
                "interpreter fuel exhausted",
            ));
        }
        self.remaining_fuel -= 1;
        self.steps += 1;
        Ok(())
    }

    fn value(&self, block: BlockId, value: ValueId) -> InterpretResult<&InterpretValue> {
        self.values.get(&value).ok_or_else(|| {
            err(
                InterpretErrorCode::MissingValue,
                block,
                format!("value %{value} is not defined"),
            )
            .with_value(value)
        })
    }
}

#[derive(Debug, Clone)]
struct MemoryState {
    allocations: BTreeMap<u64, Allocation>,
    next_alloc_id: u64,
    next_addr: u64,
    /// Bytes this run is permitted to allocate in total (the space analogue of
    /// fuel). `u64::MAX` means unbounded — only the explicit `with_budget`
    /// constructor lowers it, so `Default` stays backwards compatible.
    budget: u64,
    /// Bytes allocated so far in this run; checked against `budget` *before* any
    /// host storage is materialized.
    allocated: u64,
}

impl Default for MemoryState {
    fn default() -> Self {
        Self {
            allocations: BTreeMap::new(),
            next_alloc_id: 0,
            next_addr: 1024,
            budget: u64::MAX,
            allocated: 0,
        }
    }
}

impl MemoryState {
    fn with_budget(budget: u64) -> Self {
        Self {
            budget,
            ..Self::default()
        }
    }

    /// Exact-size allocation: no usable-size slack. Used for stack `Alloca`,
    /// internal scratch cells, and module globals — their bounds stay strict so
    /// any out-of-bounds or uninitialized read is still caught.
    fn alloc(
        &mut self,
        size: u64,
        align: u64,
        block: BlockId,
    ) -> InterpretResult<InterpretPointer> {
        self.alloc_with_slack(size, align, 0, block)
    }

    /// Allocation with `slack` readable, DEFINED-but-unspecified tail bytes
    /// beyond the `size` requested bytes — the interpreter's model of a real
    /// allocator's usable-size guarantee (`__rust_alloc` / `malloc` hand back a
    /// block at least as large as requested, and often larger). hashbrown's
    /// SwissTable control-byte scan deliberately reads a full SIMD `Group` that
    /// can extend `Group::WIDTH` bytes past the logical `ctrl` array into that
    /// slack, then masks the slack lanes out of the match — a documented sound
    /// invariant that relies on the allocator's slack being READABLE. The first
    /// `size` bytes stay uninitialized (poison discipline intact); the `slack`
    /// tail bytes are filled with `SLACK_FILL` so a group read of them returns a
    /// defined value (never `PartialBytes`) and does NOT trip the
    /// poison-consumption UB. A read BEYOND `size + slack` still faults, and
    /// stack/global allocations pass `slack = 0`, so this only ever ADMITS the
    /// heap tail-slack window — it never weakens OOB/uninit detection elsewhere.
    fn alloc_with_slack(
        &mut self,
        size: u64,
        align: u64,
        slack: u64,
        block: BlockId,
    ) -> InterpretResult<InterpretPointer> {
        // hashbrown's EMPTY control byte. Filling heap slack with EMPTY (rather
        // than 0x00, which is a FULL control byte with h2 == 0 and would present
        // a spurious match to `match_full` before masking) keeps the group scan
        // clean: the slack lanes simply never match. It is the deterministic,
        // program-correct choice for the fill value the author left open.
        const SLACK_FILL: u8 = 0xFF;

        // The total footprint (requested + slack) counts against the budget.
        let footprint = size.saturating_add(slack);
        let total = match self.allocated.checked_add(footprint) {
            Some(total) if total <= self.budget => total,
            _ => {
                return Err(err(
                    InterpretErrorCode::OutOfMemory,
                    block,
                    format!(
                        "allocation of {size} byte(s) would exceed the interpreter \
                         memory budget of {} byte(s) ({} already allocated)",
                        self.budget, self.allocated
                    ),
                ));
            }
        };
        self.allocated = total;

        let base = align_addr(self.next_addr, align)
            .ok_or_else(|| ub(block, "Alloca: base address overflow"))?;
        let id = self.next_alloc_id;
        self.next_alloc_id = self
            .next_alloc_id
            .checked_add(1)
            .ok_or_else(|| ub(block, "Alloca: allocation id overflow"))?;
        let bump = footprint.max(1);
        self.next_addr = base
            .checked_add(bump)
            .ok_or_else(|| ub(block, "Alloca: next address overflow"))?;
        let byte_len = usize::try_from(footprint)
            .map_err(|_| ub(block, "Alloca: allocation size does not fit usize"))?;
        let size_len = size as usize;
        let mut bytes = vec![None; byte_len];
        // The slack tail is defined (readable, poison-free); the requested
        // region stays uninitialized until written.
        for b in bytes.iter_mut().skip(size_len) {
            *b = Some(SLACK_FILL);
        }
        self.allocations.insert(
            id,
            Allocation {
                base,
                // Bounds cover the slack tail: a group read into it succeeds, a
                // read past `size + slack` still faults.
                size: footprint,
                alive: true,
                bytes,
                ref_count: 1,
            },
        );
        Ok(InterpretPointer {
            allocation: id,
            offset: 0,
        })
    }

    /// ARC `Retain`: increment the pointee allocation's reference count. The
    /// pointer must address a live allocation at its base (offset 0).
    fn retain(&mut self, ptr: InterpretPointer, block: BlockId) -> InterpretResult<()> {
        let allocation = self.arc_allocation_mut(ptr, block, "Retain")?;
        allocation.ref_count = allocation
            .ref_count
            .checked_add(1)
            .ok_or_else(|| ub(block, "Retain: reference count overflow"))?;
        Ok(())
    }

    /// ARC `Release`: decrement the reference count; free the allocation when it
    /// reaches zero (the last owner released). Releasing a zero-count (already
    /// freed) allocation is UB.
    fn release(&mut self, ptr: InterpretPointer, block: BlockId) -> InterpretResult<()> {
        let allocation = self.arc_allocation_mut(ptr, block, "Release")?;
        if allocation.ref_count == 0 {
            return Err(ub(
                block,
                "Release: reference count underflow (double free)",
            ));
        }
        allocation.ref_count -= 1;
        if allocation.ref_count == 0 {
            allocation.alive = false;
        }
        Ok(())
    }

    /// ARC `IsUnique`: true iff the pointee allocation has exactly one owner.
    fn is_unique(&self, ptr: InterpretPointer, block: BlockId) -> InterpretResult<bool> {
        let allocation = self.allocations.get(&ptr.allocation).ok_or_else(|| {
            ub(
                block,
                "IsUnique: pointer does not reference a known allocation",
            )
        })?;
        if !allocation.alive {
            return Err(ub(block, "IsUnique: pointer references a freed allocation"));
        }
        Ok(allocation.ref_count == 1)
    }

    fn arc_allocation_mut(
        &mut self,
        ptr: InterpretPointer,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<&mut Allocation> {
        let allocation = self.allocations.get_mut(&ptr.allocation).ok_or_else(|| {
            ub(
                block,
                format!("{op}: pointer does not reference a known allocation"),
            )
        })?;
        if !allocation.alive {
            return Err(ub(
                block,
                format!("{op}: pointer references a freed allocation"),
            ));
        }
        Ok(allocation)
    }

    fn read(
        &self,
        ptr: InterpretPointer,
        size: u64,
        align: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<Vec<u8>> {
        let allocation = self.checked_access(ptr, size, align, block, op)?;
        let start = ptr.offset as usize;
        let end = start + size as usize;
        allocation.bytes[start..end]
            .iter()
            .enumerate()
            .map(|(index, byte)| {
                byte.ok_or_else(|| {
                    ub(
                        block,
                        format!(
                            "{op}: reading uninitialized byte at offset {}",
                            start + index
                        ),
                    )
                })
            })
            .collect()
    }

    /// Read `size` bytes as their raw per-byte init state, WITHOUT failing on
    /// uninitialized bytes. Performs the same bounds / liveness / alignment
    /// check as `read`, but returns the byte range verbatim: `Some(b)` for an
    /// initialized byte, `None` for a never-written one. The copy-propagates-
    /// poison `Load` path (`eval_load`, non-strict) uses this to decide between
    /// a fully-initialized decode and a `PartialBytes` transport value.
    fn read_maybe_uninit(
        &self,
        ptr: InterpretPointer,
        size: u64,
        align: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<Vec<Option<u8>>> {
        let allocation = self.checked_access(ptr, size, align, block, op)?;
        let start = ptr.offset as usize;
        let end = start + size as usize;
        Ok(allocation.bytes[start..end].to_vec())
    }

    fn write(
        &mut self,
        ptr: InterpretPointer,
        bytes: &[u8],
        align: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<()> {
        self.checked_access(ptr, bytes.len() as u64, align, block, op)?;
        let allocation = self.allocations.get_mut(&ptr.allocation).expect("checked");
        let start = ptr.offset as usize;
        for (index, byte) in bytes.iter().copied().enumerate() {
            allocation.bytes[start + index] = Some(byte);
        }
        Ok(())
    }

    /// Write a partially-initialized byte image VERBATIM: `Some(b)` sets the
    /// byte, `None` leaves (restores) the destination byte uninitialized. This
    /// is the store half of copy-propagates-poison — the uninitialized-ness of
    /// the source lane is preserved at the destination, so the round-trip of a
    /// padding/niche lane never fabricates a defined value.
    fn write_maybe_uninit(
        &mut self,
        ptr: InterpretPointer,
        bytes: &[Option<u8>],
        align: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<()> {
        self.checked_access(ptr, bytes.len() as u64, align, block, op)?;
        let allocation = self.allocations.get_mut(&ptr.allocation).expect("checked");
        let start = ptr.offset as usize;
        for (index, byte) in bytes.iter().copied().enumerate() {
            allocation.bytes[start + index] = byte;
        }
        Ok(())
    }

    fn dealloc(&mut self, ptr: InterpretPointer, block: BlockId) -> InterpretResult<()> {
        if ptr.offset != 0 {
            return Err(ub(block, "Dealloc: pointer must reference allocation base"));
        }
        let allocation = self.allocations.get_mut(&ptr.allocation).ok_or_else(|| {
            ub(
                block,
                format!("Dealloc: unknown allocation {}", ptr.allocation),
            )
        })?;
        if !allocation.alive {
            return Err(ub(block, "Dealloc: allocation is already dead"));
        }
        allocation.alive = false;
        Ok(())
    }

    fn address(&self, ptr: InterpretPointer, block: BlockId, op: &str) -> InterpretResult<u64> {
        let allocation = self.allocations.get(&ptr.allocation).ok_or_else(|| {
            ub(
                block,
                format!("{op}: unknown allocation {}", ptr.allocation),
            )
        })?;
        allocation
            .base
            .checked_add(ptr.offset)
            .ok_or_else(|| ub(block, format!("{op}: pointer address overflow")))
    }

    /// Resolve a raw address to a provenance-carrying `InterpretPointer`, or
    /// `None` if it names no live allocation. Prefers an in-bounds allocation;
    /// falls back to a one-past-the-end match (a legal interior/end pointer).
    fn try_pointer_from_address(&self, address: u64) -> Option<InterpretPointer> {
        for (id, allocation) in &self.allocations {
            let Some(end) = allocation.base.checked_add(allocation.size) else {
                continue;
            };
            if address >= allocation.base && address < end {
                return Some(InterpretPointer {
                    allocation: *id,
                    offset: address - allocation.base,
                });
            }
        }
        for (id, allocation) in &self.allocations {
            let Some(end) = allocation.base.checked_add(allocation.size) else {
                continue;
            };
            if address == end {
                return Some(InterpretPointer {
                    allocation: *id,
                    offset: address - allocation.base,
                });
            }
        }
        None
    }

    /// Turn a raw pointer address into a runtime pointer VALUE kind. Zero is the
    /// null pointer; an address with allocation provenance is a real `Ptr`; any
    /// other nonzero address is a no-provenance `DanglingPtr` — a legal pointer
    /// value whose only undefined use is a dereference (deferred to
    /// `expect_pointer`, so creation/store/copy/compare all succeed).
    fn resolve_pointer_kind(&self, address: u64) -> InterpretValueKind {
        if address == 0 {
            InterpretValueKind::NullPtr
        } else if let Some(ptr) = self.try_pointer_from_address(address) {
            InterpretValueKind::Ptr(ptr)
        } else {
            InterpretValueKind::DanglingPtr(address)
        }
    }

    fn checked_access(
        &self,
        ptr: InterpretPointer,
        size: u64,
        align: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<&Allocation> {
        let allocation = self.allocations.get(&ptr.allocation).ok_or_else(|| {
            ub(
                block,
                format!("{op}: unknown allocation {}", ptr.allocation),
            )
        })?;
        if !allocation.alive {
            return Err(ub(block, format!("{op}: use after dealloc")));
        }
        let address = allocation
            .base
            .checked_add(ptr.offset)
            .ok_or_else(|| ub(block, format!("{op}: pointer address overflow")))?;
        if address % align != 0 {
            return Err(ub(
                block,
                format!("{op}: pointer address {address} is not aligned to {align}"),
            ));
        }
        let end = ptr
            .offset
            .checked_add(size)
            .ok_or_else(|| ub(block, format!("{op}: access range overflow")))?;
        if end > allocation.size {
            return Err(ub(
                block,
                format!(
                    "{op}: access [{}..{}) is out of bounds for allocation size {}",
                    ptr.offset, end, allocation.size
                ),
            ));
        }
        Ok(allocation)
    }
}

#[derive(Debug, Clone)]
struct Allocation {
    base: u64,
    size: u64,
    alive: bool,
    bytes: Vec<Option<u8>>,
    /// Reference count for the ARC model (`Retain`/`Release`/`IsUnique`). Every
    /// allocation starts uniquely owned (1). `Retain` increments, `Release`
    /// decrements (freeing at 0); `IsUnique` is `ref_count == 1`. In this
    /// single-threaded reference interpreter the count is exact, not atomic.
    ref_count: u64,
}

enum Step {
    Continue,
    Jump {
        target: BlockId,
        args: Vec<InterpretValue>,
    },
    Return(Vec<InterpretValue>),
}

fn bind_block_params(
    state: &mut ExecState,
    block: &Block,
    args: Vec<InterpretValue>,
) -> InterpretResult<()> {
    if block.params.len() != args.len() {
        return Err(err(
            InterpretErrorCode::MalformedInstruction,
            block.id,
            format!(
                "block parameter arity mismatch: expected {}, got {}",
                block.params.len(),
                args.len()
            ),
        ));
    }
    for ((value, ty), arg) in block.params.iter().zip(args) {
        expect_ty(&arg, ty, block.id)?;
        state.values.insert(*value, arg);
    }
    Ok(())
}

fn bind_results(
    state: &mut ExecState,
    block: BlockId,
    node: &InstrNode,
    values: impl IntoIterator<Item = InterpretValue>,
) -> InterpretResult<()> {
    let values = values.into_iter().collect::<Vec<_>>();
    if node.results.len() != values.len() {
        return Err(err(
            InterpretErrorCode::MalformedInstruction,
            block,
            format!(
                "instruction result arity mismatch: node declares {}, interpreter produced {}",
                node.results.len(),
                values.len()
            ),
        ));
    }
    for (result, value) in node.results.iter().copied().zip(values) {
        state.values.insert(result, value);
    }
    Ok(())
}

fn eval_args(
    state: &ExecState,
    block: BlockId,
    args: &[ValueId],
) -> InterpretResult<Vec<InterpretValue>> {
    args.iter()
        .map(|value| state.value(block, *value).cloned())
        .collect()
}

fn expect_ty(value: &InterpretValue, ty: &Ty, block: BlockId) -> InterpretResult<()> {
    if &value.ty == ty {
        Ok(())
    } else {
        Err(type_error(
            block,
            format!("expected value of type {ty}, got {}", value.ty),
        ))
    }
}

fn check_signature_values(
    block: BlockId,
    label: &str,
    values: &[InterpretValue],
    expected_tys: &[Ty],
) -> InterpretResult<()> {
    if values.len() != expected_tys.len() {
        return Err(signature_mismatch(
            block,
            format!(
                "{label} arity mismatch: expected {}, got {}",
                expected_tys.len(),
                values.len()
            ),
        ));
    }
    for (index, (value, expected_ty)) in values.iter().zip(expected_tys).enumerate() {
        // A poison value may not cross a call/return boundary — that is an
        // inspection of its (uninitialized) content, undefined behaviour.
        reject_partial(value, block, label)?;
        if &value.ty != expected_ty {
            return Err(signature_mismatch(
                block,
                format!(
                    "{label} type mismatch at argument {index}: expected {expected_ty}, got {}",
                    value.ty
                ),
            ));
        }
    }
    Ok(())
}

fn ensure_call_depth(block: BlockId, call_depth: u64) -> InterpretResult<()> {
    if call_depth == 0 {
        Err(err(
            InterpretErrorCode::OutOfFuel,
            block,
            "interpreter call depth exhausted",
        ))
    } else {
        Ok(())
    }
}

fn expect_int_value(value: &InterpretValue, block: BlockId) -> InterpretResult<InterpretInt> {
    reject_partial(value, block, "integer use")?;
    value
        .as_int()
        .ok_or_else(|| type_error(block, format!("expected integer value, got {}", value.ty)))
}

/// Integer-resize casts also admit `Bool` as their canonical one-bit lane.
fn expect_integer_resize_value(
    value: &InterpretValue,
    block: BlockId,
) -> InterpretResult<InterpretInt> {
    match value.kind {
        InterpretValueKind::Int(int) => Ok(int),
        InterpretValueKind::Bool(value) => Ok(InterpretInt {
            bits: 1,
            signed: false,
            raw: u128::from(value),
        }),
        _ => Err(type_error(
            block,
            format!("expected integer or bool value, got {}", value.ty),
        )),
    }
}

fn expect_bool_value(value: &InterpretValue, block: BlockId) -> InterpretResult<bool> {
    reject_partial(value, block, "bool use")?;
    value
        .as_bool()
        .ok_or_else(|| type_error(block, format!("expected bool value, got {}", value.ty)))
}

fn expect_float_bits(value: &InterpretValue, block: BlockId) -> InterpretResult<u64> {
    reject_partial(value, block, "float use")?;
    match value.kind {
        InterpretValueKind::FloatBits(bits) => Ok(bits),
        _ => Err(type_error(
            block,
            format!("expected float value, got {}", value.ty),
        )),
    }
}

fn expect_pointer(
    value: &InterpretValue,
    block: BlockId,
    op: &str,
) -> InterpretResult<InterpretPointer> {
    reject_partial(value, block, op)?;
    match value.kind {
        InterpretValueKind::Ptr(ptr) => Ok(ptr),
        InterpretValueKind::NullPtr => Err(ub(block, format!("{op}: null pointer dereference"))),
        // DEREFERENCE-time provenance check: a no-provenance pointer is a legal
        // value, but reaching through it (Load/Store/ARC/atomic) has no
        // allocation to touch — the "no allocation provenance" error lives here,
        // not at the pointer's creation.
        InterpretValueKind::DanglingPtr(addr) => Err(ub(
            block,
            format!("{op}: pointer value {addr} has no allocation provenance"),
        )),
        _ => Err(type_error(
            block,
            format!("{op}: expected pointer value, got {}", value.ty),
        )),
    }
}

/// Extract the binding-frame id from an `OpenFrame` handle value.
fn expect_frame(value: &InterpretValue, block: BlockId) -> InterpretResult<u64> {
    reject_partial(value, block, "frame handle use")?;
    match value.kind {
        InterpretValueKind::Frame(id) => Ok(id),
        _ => Err(type_error(
            block,
            format!("expected a binding-frame handle, got {}", value.ty),
        )),
    }
}

fn expect_vector_lanes(
    value: &InterpretValue,
    lanes: u32,
    block: BlockId,
) -> InterpretResult<&[InterpretValue]> {
    reject_partial(value, block, "vector use")?;
    match &value.kind {
        InterpretValueKind::Vector(values) if values.len() == lanes as usize => Ok(values),
        InterpretValueKind::Vector(values) => Err(err(
            InterpretErrorCode::UnsupportedVectorShape,
            block,
            format!(
                "vector value has {} lanes, declared shape requires {lanes}",
                values.len()
            ),
        )),
        _ => Err(type_error(
            block,
            format!("expected vector value, got {}", value.ty),
        )),
    }
}

fn checked_align(align: u64, block: BlockId) -> InterpretResult<u64> {
    if align == 0 || !align.is_power_of_two() {
        Err(type_error(
            block,
            format!("alignment {align} must be a non-zero power of two"),
        ))
    } else {
        Ok(align)
    }
}

fn align_addr(address: u64, align: u64) -> Option<u64> {
    let mask = align.checked_sub(1)?;
    address.checked_add(mask).map(|value| value & !mask)
}

/// Round `value` up to the next multiple of `align` (a power of two), erroring
/// on overflow. Used by the struct C-layout computation in `struct_layout`.
fn align_up(value: u64, align: u64, block: BlockId) -> InterpretResult<u64> {
    align_addr(value, align).ok_or_else(|| type_error(block, "struct layout offset overflow"))
}

fn byte_ranges_overlap(a_offset: u64, a_size: u64, b_offset: u64, b_size: u64) -> bool {
    if a_size == 0 || b_size == 0 {
        return false;
    }
    let Some(a_end) = a_offset.checked_add(a_size) else {
        return true;
    };
    let Some(b_end) = b_offset.checked_add(b_size) else {
        return true;
    };
    a_offset < b_end && b_offset < a_end
}

/// Computed C-style layout of a `Ty::Struct`: total size, alignment, and the
/// `(byte offset, field type)` of each field in declaration order.
struct StructLayout {
    size: u64,
    align: u64,
    field_offsets: Vec<(u64, Ty)>,
}

/// Computed canonical tagged-union layout of a `Ty::Enum` (byte units). See
/// `Interpreter::enum_layout` for the rules and the explicit note that this
/// is trust-ir's canonical layout, not rustc parity.
struct EnumLayout {
    /// Integer type of the logical in-register tag lane.
    tag_ty: Ty,
    /// Tag size in bytes.
    tag_size: u64,
    /// Byte offset of the shared payload region.
    payload_offset: u64,
    /// Total enum size in bytes.
    size: u64,
    /// Enum alignment in bytes.
    align: u64,
    /// Effective discriminant per variant, in variant order.
    discriminants: Vec<i128>,
    /// Per-variant field offsets RELATIVE to `payload_offset`, with types.
    variant_field_offsets: Vec<Vec<(u64, Ty)>>,
    /// Encoding of the enum's byte image.
    byte_view: EnumByteView,
}

#[derive(Debug, Clone)]
enum EnumByteView {
    /// v37: the memory image is the payload alone — no tag bytes are read or
    /// written. The variant is a static fact of the type, carried here so
    /// decode can name it without touching memory.
    Untagged {
        variant: usize,
    },
    Direct {
        tag_offset: u64,
    },
    Niche {
        untagged_variant: usize,
        niche_variants_start: u32,
        niche_variants_end: u32,
        niche_start: u128,
        niche_offset: u64,
        niche_size: u64,
    },
}

impl EnumLayout {
    /// The variant index whose effective discriminant equals `disc`.
    fn variant_by_discriminant(&self, disc: i128) -> Option<usize> {
        self.discriminants.iter().position(|d| *d == disc)
    }
}

/// The `i128` discriminant value carried by an interpreted tag integer
/// (signed tags sign-extend; unsigned tags zero-extend — `u64::MAX` fits
/// `i128` losslessly).
fn tag_int_discriminant(int: InterpretInt) -> i128 {
    if int.signed {
        int.as_signed()
    } else {
        int.as_unsigned() as i128
    }
}

/// Rebuild the logical tag operand for `variant_idx` from the layout's own
/// discriminant table.
///
/// The interpreter's enum VALUE is always `Aggregate([tag, fields..])`, but
/// two encodings store no tag lane in the byte image — niche (for the untagged
/// variant) and v37 `Untagged` (for every variant, because there is only one).
/// Those decode paths recover the variant first and then synthesize the tag the
/// value model expects, rather than reading it.
fn synthesized_tag_value(
    layout: &EnumLayout,
    variant_idx: usize,
    block: BlockId,
) -> InterpretResult<InterpretValue> {
    let disc = layout.discriminants[variant_idx];
    let (bits, signed) = int_shape(&layout.tag_ty).expect("enum tag is an integer type");
    let tag_mask = int_mask(bits)
        .ok_or_else(|| type_error(block, format!("unsupported integer width {bits}")))?;
    let tag_int = InterpretInt::from_raw(bits, signed, (disc as u128) & tag_mask)
        .ok_or_else(|| type_error(block, format!("unsupported integer width {bits}")))?;
    Ok(InterpretValue {
        ty: layout.tag_ty.clone(),
        kind: InterpretValueKind::Int(tag_int),
    })
}

fn runtime_index(value: &InterpretValue, block: BlockId) -> InterpretResult<usize> {
    let int = expect_int_value(value, block)?;
    if int.signed && int.as_signed() < 0 {
        return Err(err(
            InterpretErrorCode::UndefinedBehavior,
            block,
            format!("negative element index {}", int.as_signed()),
        ));
    }
    usize::try_from(int.as_unsigned()).map_err(|_| {
        err(
            InterpretErrorCode::UndefinedBehavior,
            block,
            format!("element index {} does not fit usize", int.as_unsigned()),
        )
    })
}

fn eval_int_binop(
    op: BinOp,
    lhs: InterpretInt,
    rhs: InterpretInt,
    block: BlockId,
) -> InterpretResult<InterpretInt> {
    if lhs.bits != rhs.bits {
        return Err(type_error(
            block,
            format!("integer widths differ: {} vs {}", lhs.bits, rhs.bits),
        ));
    }
    let mask = int_mask(lhs.bits).expect("validated integer width");
    let raw = match op {
        BinOp::Add => lhs.raw.wrapping_add(rhs.raw),
        BinOp::Sub => lhs.raw.wrapping_sub(rhs.raw),
        BinOp::Mul => lhs.raw.wrapping_mul(rhs.raw),
        BinOp::And => lhs.raw & rhs.raw,
        BinOp::Or => lhs.raw | rhs.raw,
        BinOp::Xor => lhs.raw ^ rhs.raw,
        // Boolean connectives on the 0/1 carrier. These MUST agree with
        // `semIntBinOp`'s `.BAnd`/`.BOr`/`.BXor` arms in
        // `lean/trust_ir-semantics/TrustIr/Semantics/Arith.lean` exactly: any
        // nonzero operand counts as true, and the result is the canonical 0 or 1
        // (total, no UB guard, no wrap needed). A divergence here would make the
        // interpreter and the Lean semantics disagree about the same program.
        BinOp::BAnd => u128::from(lhs.raw != 0 && rhs.raw != 0),
        BinOp::BOr => u128::from(lhs.raw != 0 || rhs.raw != 0),
        BinOp::BXor => u128::from((lhs.raw != 0) != (rhs.raw != 0)),
        BinOp::UDiv => {
            if rhs.raw == 0 {
                return Err(ub(block, "unsigned division by zero"));
            }
            lhs.raw / rhs.raw
        }
        BinOp::URem => {
            if rhs.raw == 0 {
                return Err(ub(block, "unsigned remainder by zero"));
            }
            lhs.raw % rhs.raw
        }
        BinOp::SDiv => {
            let rhs_signed = rhs.as_signed();
            if rhs_signed == 0 {
                return Err(ub(block, "signed division by zero"));
            }
            let lhs_signed = lhs.as_signed();
            if signed_div_overflows(lhs.bits, lhs_signed, rhs_signed) {
                return Err(ub(block, "signed division overflow"));
            }
            (lhs_signed / rhs_signed) as u128
        }
        BinOp::SRem => {
            let rhs_signed = rhs.as_signed();
            if rhs_signed == 0 {
                return Err(ub(block, "signed remainder by zero"));
            }
            let lhs_signed = lhs.as_signed();
            if signed_div_overflows(lhs.bits, lhs_signed, rhs_signed) {
                return Err(ub(block, "signed remainder overflow"));
            }
            (lhs_signed % rhs_signed) as u128
        }
        BinOp::Shl => {
            let amount = shift_amount(rhs, lhs.bits, block)?;
            lhs.raw << amount
        }
        BinOp::LShr => {
            let amount = shift_amount(rhs, lhs.bits, block)?;
            lhs.raw >> amount
        }
        BinOp::AShr => {
            let amount = shift_amount(rhs, lhs.bits, block)?;
            (lhs.as_signed() >> amount) as u128
        }
        BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax => {
            return Err(err(
                InterpretErrorCode::UnsupportedInstruction,
                block,
                format!("floating binop {op} is outside this interpreter slice"),
            ));
        }
    } & mask;
    Ok(InterpretInt {
        bits: lhs.bits,
        signed: lhs.signed,
        raw,
    })
}

fn eval_bool_binop(op: BinOp, lhs: bool, rhs: bool, block: BlockId) -> InterpretResult<bool> {
    match op {
        BinOp::And => Ok(lhs & rhs),
        BinOp::Or => Ok(lhs | rhs),
        BinOp::Xor => Ok(lhs ^ rhs),
        // The dedicated boolean connectives. WITHOUT these arms the catch-all
        // below would reject them on precisely the type they exist for: the
        // validator requires `BAnd`/`BOr`/`BXor` to be Bool-typed, so every
        // well-typed use would land in the error branch.
        BinOp::BAnd => Ok(lhs & rhs),
        BinOp::BOr => Ok(lhs | rhs),
        BinOp::BXor => Ok(lhs ^ rhs),
        _ => Err(type_error(
            block,
            format!("{op} is not a boolean binary operation"),
        )),
    }
}

fn eval_int_unop(op: UnOp, value: InterpretInt, block: BlockId) -> InterpretResult<InterpretInt> {
    let mask = int_mask(value.bits).expect("validated integer width");
    let raw = match op {
        UnOp::Neg => 0u128.wrapping_sub(value.raw),
        UnOp::Not => !value.raw,
        UnOp::CtPop => u128::from(value.raw.count_ones()),
        UnOp::FNeg => {
            return Err(err(
                InterpretErrorCode::UnsupportedInstruction,
                block,
                "floating negation is outside this interpreter slice",
            ));
        }
        UnOp::FAbs => {
            return Err(err(
                InterpretErrorCode::UnsupportedInstruction,
                block,
                "floating absolute value is outside this interpreter slice",
            ));
        }
        UnOp::FSqrt => {
            return Err(err(
                InterpretErrorCode::UnsupportedInstruction,
                block,
                "floating square root is outside this interpreter slice",
            ));
        }
        UnOp::FFloor => {
            return Err(err(
                InterpretErrorCode::UnsupportedInstruction,
                block,
                "floating floor is outside this interpreter slice",
            ));
        }
        UnOp::FCeil => {
            return Err(err(
                InterpretErrorCode::UnsupportedInstruction,
                block,
                "floating ceil is outside this interpreter slice",
            ));
        }
        UnOp::FTrunc => {
            return Err(err(
                InterpretErrorCode::UnsupportedInstruction,
                block,
                "floating trunc is outside this interpreter slice",
            ));
        }
    } & mask;
    Ok(InterpretInt {
        bits: value.bits,
        signed: value.signed,
        raw,
    })
}

fn eval_int_overflow(
    op: OverflowOp,
    lhs: InterpretInt,
    rhs: InterpretInt,
    block: BlockId,
) -> InterpretResult<(InterpretInt, bool)> {
    if lhs.bits != rhs.bits {
        return Err(type_error(
            block,
            format!("integer widths differ: {} vs {}", lhs.bits, rhs.bits),
        ));
    }
    let result = eval_int_binop(
        match op {
            OverflowOp::AddOverflow => BinOp::Add,
            OverflowOp::SubOverflow => BinOp::Sub,
            OverflowOp::MulOverflow => BinOp::Mul,
        },
        lhs,
        rhs,
        block,
    )?;

    let overflow = if lhs.signed {
        signed_overflow(op, lhs, rhs)
    } else {
        unsigned_overflow(op, lhs, rhs)
    };
    Ok((result, overflow))
}

fn eval_int_icmp(op: ICmpOp, lhs: InterpretInt, rhs: InterpretInt) -> bool {
    match op {
        ICmpOp::Eq => lhs.raw == rhs.raw,
        ICmpOp::Ne => lhs.raw != rhs.raw,
        ICmpOp::Ult => lhs.raw < rhs.raw,
        ICmpOp::Ule => lhs.raw <= rhs.raw,
        ICmpOp::Ugt => lhs.raw > rhs.raw,
        ICmpOp::Uge => lhs.raw >= rhs.raw,
        ICmpOp::Slt => lhs.as_signed() < rhs.as_signed(),
        ICmpOp::Sle => lhs.as_signed() <= rhs.as_signed(),
        ICmpOp::Sgt => lhs.as_signed() > rhs.as_signed(),
        ICmpOp::Sge => lhs.as_signed() >= rhs.as_signed(),
    }
}

fn eval_bool_icmp(op: ICmpOp, lhs: bool, rhs: bool) -> bool {
    let lhs = InterpretInt {
        bits: 1,
        signed: false,
        raw: if lhs { 1 } else { 0 },
    };
    let rhs = InterpretInt {
        bits: 1,
        signed: false,
        raw: if rhs { 1 } else { 0 },
    };
    eval_int_icmp(op, lhs, rhs)
}

fn eval_float_binop(
    op: BinOp,
    ty: &Ty,
    lhs_bits: u64,
    rhs_bits: u64,
    block: BlockId,
) -> InterpretResult<u64> {
    match ty {
        Ty::F32 => {
            let lhs = f32::from_bits(lhs_bits as u32);
            let rhs = f32::from_bits(rhs_bits as u32);
            let value = match op {
                BinOp::FAdd => lhs + rhs,
                BinOp::FSub => lhs - rhs,
                BinOp::FMul => lhs * rhs,
                BinOp::FDiv => lhs / rhs,
                BinOp::FRem => lhs % rhs,
                BinOp::FMin => lhs.min(rhs),
                BinOp::FMax => lhs.max(rhs),
                _ => {
                    return Err(type_error(
                        block,
                        format!("integer binop {op} on float operands"),
                    ));
                }
            };
            Ok(u64::from(value.to_bits()))
        }
        Ty::F64 => {
            let lhs = f64::from_bits(lhs_bits);
            let rhs = f64::from_bits(rhs_bits);
            let value = match op {
                BinOp::FAdd => lhs + rhs,
                BinOp::FSub => lhs - rhs,
                BinOp::FMul => lhs * rhs,
                BinOp::FDiv => lhs / rhs,
                BinOp::FRem => lhs % rhs,
                BinOp::FMin => lhs.min(rhs),
                BinOp::FMax => lhs.max(rhs),
                _ => {
                    return Err(type_error(
                        block,
                        format!("integer binop {op} on float operands"),
                    ));
                }
            };
            Ok(value.to_bits())
        }
        Ty::F16 => Err(unsupported_float(block, "f16 arithmetic is not executable")),
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

fn eval_float_unop(op: UnOp, ty: &Ty, operand_bits: u64, block: BlockId) -> InterpretResult<u64> {
    match ty {
        Ty::F32 => {
            let operand = f32::from_bits(operand_bits as u32);
            let value = match op {
                UnOp::FNeg => -operand,
                // IEEE 754 required/recommended operations with exact or
                // correctly-rounded results — deterministic under `f32`'s
                // host semantics, matching the float binop slice above.
                UnOp::FAbs => operand.abs(),
                UnOp::FSqrt => operand.sqrt(),
                UnOp::FFloor => operand.floor(),
                UnOp::FCeil => operand.ceil(),
                UnOp::FTrunc => operand.trunc(),
                _ => {
                    return Err(type_error(
                        block,
                        format!("integer unary op {op} on float operand"),
                    ));
                }
            };
            Ok(u64::from(value.to_bits()))
        }
        Ty::F64 => {
            let operand = f64::from_bits(operand_bits);
            let value = match op {
                UnOp::FNeg => -operand,
                // IEEE 754 required/recommended operations with exact or
                // correctly-rounded results — deterministic under `f64`'s
                // host semantics, matching the float binop slice above.
                UnOp::FAbs => operand.abs(),
                UnOp::FSqrt => operand.sqrt(),
                UnOp::FFloor => operand.floor(),
                UnOp::FCeil => operand.ceil(),
                UnOp::FTrunc => operand.trunc(),
                _ => {
                    return Err(type_error(
                        block,
                        format!("integer unary op {op} on float operand"),
                    ));
                }
            };
            Ok(value.to_bits())
        }
        Ty::F16 => Err(unsupported_float(block, "f16 arithmetic is not executable")),
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

fn eval_float_fcmp(
    op: FCmpOp,
    ty: &Ty,
    lhs_bits: u64,
    rhs_bits: u64,
    block: BlockId,
) -> InterpretResult<bool> {
    match ty {
        Ty::F32 => Ok(eval_fcmp_f32(
            op,
            f32::from_bits(lhs_bits as u32),
            f32::from_bits(rhs_bits as u32),
        )),
        Ty::F64 => Ok(eval_fcmp_f64(
            op,
            f64::from_bits(lhs_bits),
            f64::from_bits(rhs_bits),
        )),
        Ty::F16 => Err(unsupported_float(
            block,
            "f16 comparisons are not executable",
        )),
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

fn eval_fcmp_f32(op: FCmpOp, lhs: f32, rhs: f32) -> bool {
    let unordered = lhs.is_nan() || rhs.is_nan();
    match op {
        FCmpOp::OEq => !unordered && lhs == rhs,
        FCmpOp::ONe => !unordered && lhs != rhs,
        FCmpOp::OLt => !unordered && lhs < rhs,
        FCmpOp::OLe => !unordered && lhs <= rhs,
        FCmpOp::OGt => !unordered && lhs > rhs,
        FCmpOp::OGe => !unordered && lhs >= rhs,
        FCmpOp::UEq => unordered || lhs == rhs,
        FCmpOp::UNe => unordered || lhs != rhs,
        FCmpOp::ULt => unordered || lhs < rhs,
        FCmpOp::ULe => unordered || lhs <= rhs,
        FCmpOp::UGt => unordered || lhs > rhs,
        FCmpOp::UGe => unordered || lhs >= rhs,
    }
}

fn eval_fcmp_f64(op: FCmpOp, lhs: f64, rhs: f64) -> bool {
    let unordered = lhs.is_nan() || rhs.is_nan();
    match op {
        FCmpOp::OEq => !unordered && lhs == rhs,
        FCmpOp::ONe => !unordered && lhs != rhs,
        FCmpOp::OLt => !unordered && lhs < rhs,
        FCmpOp::OLe => !unordered && lhs <= rhs,
        FCmpOp::OGt => !unordered && lhs > rhs,
        FCmpOp::OGe => !unordered && lhs >= rhs,
        FCmpOp::UEq => unordered || lhs == rhs,
        FCmpOp::UNe => unordered || lhs != rhs,
        FCmpOp::ULt => unordered || lhs < rhs,
        FCmpOp::ULe => unordered || lhs <= rhs,
        FCmpOp::UGt => unordered || lhs > rhs,
        FCmpOp::UGe => unordered || lhs >= rhs,
    }
}

fn float_bits_from_f64(ty: &Ty, value: f64, block: BlockId) -> InterpretResult<u64> {
    match ty {
        Ty::F32 => Ok(u64::from((value as f32).to_bits())),
        Ty::F64 => Ok(value.to_bits()),
        Ty::F16 => Err(unsupported_float(
            block,
            "f16 constants require an explicit half-precision codec",
        )),
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

fn float_bits_from_raw(ty: &Ty, raw: u128, block: BlockId) -> InterpretResult<u64> {
    match ty {
        Ty::F32 => Ok((raw as u32) as u64),
        Ty::F64 => Ok(raw as u64),
        Ty::F16 => Err(unsupported_float(
            block,
            "f16 bitcasts require an explicit half-precision codec",
        )),
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

fn float_as_f64(ty: &Ty, bits: u64, block: BlockId) -> InterpretResult<f64> {
    match ty {
        Ty::F32 => Ok(f32::from_bits(bits as u32) as f64),
        Ty::F64 => Ok(f64::from_bits(bits)),
        Ty::F16 => Err(unsupported_float(
            block,
            "f16 casts require an explicit half-precision codec",
        )),
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

fn float_to_u128(value: f64) -> u128 {
    if value.is_nan() || value <= 0.0 {
        0
    } else if value >= u128::MAX as f64 {
        u128::MAX
    } else {
        value.trunc() as u128
    }
}

fn float_to_i128(value: f64) -> i128 {
    if value.is_nan() {
        0
    } else if value <= i128::MIN as f64 {
        i128::MIN
    } else if value >= i128::MAX as f64 {
        i128::MAX
    } else {
        value.trunc() as i128
    }
}

fn unsigned_overflow(op: OverflowOp, lhs: InterpretInt, rhs: InterpretInt) -> bool {
    let mask = int_mask(lhs.bits).expect("validated integer width");
    match op {
        OverflowOp::AddOverflow => {
            let (sum, overflow) = lhs.raw.overflowing_add(rhs.raw);
            overflow || sum > mask
        }
        OverflowOp::SubOverflow => lhs.raw < rhs.raw,
        OverflowOp::MulOverflow => {
            let (product, overflow) = lhs.raw.overflowing_mul(rhs.raw);
            overflow || product > mask || (rhs.raw != 0 && lhs.raw > mask / rhs.raw)
        }
    }
}

fn signed_overflow(op: OverflowOp, lhs: InterpretInt, rhs: InterpretInt) -> bool {
    let (min, max) = signed_bounds(lhs.bits);
    let lhs = lhs.as_signed();
    let rhs = rhs.as_signed();
    let checked = match op {
        OverflowOp::AddOverflow => lhs.checked_add(rhs),
        OverflowOp::SubOverflow => lhs.checked_sub(rhs),
        OverflowOp::MulOverflow => lhs.checked_mul(rhs),
    };
    !matches!(checked, Some(value) if value >= min && value <= max)
}

fn signed_div_overflows(bits: u32, lhs: i128, rhs: i128) -> bool {
    let (min, _) = signed_bounds(bits);
    lhs == min && rhs == -1
}

fn shift_amount(rhs: InterpretInt, bits: u32, block: BlockId) -> InterpretResult<u32> {
    if rhs.raw >= u128::from(bits) {
        return Err(ub(
            block,
            format!(
                "shift amount {} is out of range for {bits}-bit integer",
                rhs.raw
            ),
        ));
    }
    Ok(rhs.raw as u32)
}

fn int_shape(ty: &Ty) -> Option<(u32, bool)> {
    match ty {
        Ty::I8 => Some((8, true)),
        Ty::I16 => Some((16, true)),
        Ty::I32 => Some((32, true)),
        Ty::I64 => Some((64, true)),
        Ty::I128 => Some((128, true)),
        Ty::U8 => Some((8, false)),
        Ty::U16 => Some((16, false)),
        Ty::U32 => Some((32, false)),
        Ty::U64 => Some((64, false)),
        Ty::U128 => Some((128, false)),
        // v25 B1 scalars: the reference interpreter models the 64-bit
        // targets (the same fixed pointer width the fat-pointer len word and
        // trust-mc's HOST_POINTER_BITS use), so pointer-width integers
        // execute at 64 bits. Char is a 32-bit unsigned carrier; its
        // 0..=0x10FFFF valid range is the VALIDATOR's claim to check, not an
        // arithmetic property.
        Ty::Isize => Some((64, true)),
        Ty::Usize => Some((64, false)),
        Ty::Char => Some((32, false)),
        _ => None,
    }
}

fn is_pointer_like_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_)
    )
}

/// Low-`bits`-set mask for an integer width, or `None` for `bits == 0` or
/// `bits > 128`.
///
/// PRECONDITION for the `int_mask(..).expect("validated integer width")` call
/// sites: `bits` originates from `IntValue` (`from_i128`/`from_raw`), whose
/// width is one of the closed set {8, 16, 32, 64, 128} taken from the `Ty`
/// integer variants via `int_shape`. For every value in that set this returns
/// `Some`, so the `expect`s are unreachable today — they guard against a future
/// width being added to `IntValue` without an `int_mask` arm, turning a silent
/// wrong-mask into a loud panic.
fn int_mask(bits: u32) -> Option<u128> {
    match bits {
        1..=127 => Some((1u128 << bits) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

fn signed_bounds(bits: u32) -> (i128, i128) {
    if bits == 128 {
        return (i128::MIN, i128::MAX);
    }
    let sign = 1u128 << (bits - 1);
    (-(sign as i128), (sign - 1) as i128)
}

fn type_error(block: BlockId, message: impl Into<String>) -> InterpretError {
    err(InterpretErrorCode::TypeError, block, message)
}

fn unsupported_dialect_op(block: BlockId, op: &DialectInst) -> InterpretError {
    err(
        InterpretErrorCode::UnsupportedDialectOp,
        block,
        format!(
            "dialect op {} is not lowered into executable core TrustIr",
            op.qualified_name()
        ),
    )
}

fn vector_dialect_error(
    block: BlockId,
    op: &DialectInst,
    reason: impl Into<String>,
) -> InterpretError {
    let reason = reason.into();
    let message = format!("{} is not executable: {reason}", op.qualified_name());
    if reason.contains("supports only") {
        err(InterpretErrorCode::UnsupportedVectorShape, block, message)
    } else if reason.contains("type") || reason.contains("Ty attribute") {
        type_error(block, message)
    } else {
        err(InterpretErrorCode::UnsupportedDialectOp, block, message)
    }
}

fn unsupported_float(block: BlockId, message: impl Into<String>) -> InterpretError {
    err(InterpretErrorCode::UnsupportedFloat, block, message)
}

fn invalid_function_pointer(block: BlockId, message: impl Into<String>) -> InterpretError {
    err(InterpretErrorCode::InvalidFunctionPointer, block, message)
}

fn signature_mismatch(block: BlockId, message: impl Into<String>) -> InterpretError {
    err(InterpretErrorCode::SignatureMismatch, block, message)
}

fn ub(block: BlockId, message: impl Into<String>) -> InterpretError {
    err(InterpretErrorCode::UndefinedBehavior, block, message)
}

/// The set of load result types that participate in copy-propagates-poison: a
/// non-strict load of one of these whose byte range has an uninitialized byte
/// yields a `PartialBytes` transport value instead of faulting. These are the
/// SCALAR types `decode_value` turns into a single runtime value (integers,
/// floats, bool, and thin pointers). Aggregates and fat pointers are excluded —
/// their loads keep the strict discipline (a decode only touches live field
/// bytes, and an uninitialized field byte stays undefined behaviour).
fn partial_load_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_)
    )
}

/// The undefined-behaviour error raised when a partially-initialized (poison)
/// value is INSPECTED rather than merely transported. `op` names the true use
/// site (the arithmetic/comparison/cast/branch/call that consumed it).
fn reject_partial_error(block: BlockId, op: &str) -> InterpretError {
    ub(
        block,
        format!(
            "{op}: use of an uninitialized value — a load read uninitialized bytes \
             (poison); poison may only be copied or stored, never inspected"
        ),
    )
}

/// Fault if `value` is a `PartialBytes` poison value; otherwise a no-op. Every
/// content-inspecting operation gates on this so the undefined behaviour is
/// reported at the true use site, not silently miscomputed.
fn reject_partial(value: &InterpretValue, block: BlockId, op: &str) -> InterpretResult<()> {
    if let InterpretValueKind::PartialBytes(_) = value.kind {
        Err(reject_partial_error(block, op))
    } else {
        Ok(())
    }
}

fn err(code: InterpretErrorCode, block: BlockId, message: impl Into<String>) -> InterpretError {
    InterpretError::new(code, message).with_block(block)
}

#[cfg(test)]
mod bool_connective_tests {
    //! The boolean connectives `BAnd`/`BOr`/`BXor`, pinned against the Lean
    //! semantics they must agree with.
    //!
    //! `semIntBinOp` in `lean/trust_ir-semantics/TrustIr/Semantics/Arith.lean`
    //! defines them as, e.g., `.BAnd => .ok (if (lhs != 0) && (rhs != 0) then 1
    //! else 0)`. Two evaluators here must match that: `eval_int_binop` on the
    //! 0/1 Int carrier and `eval_bool_binop` on native bools. A divergence in
    //! either would mean the interpreter and the semantics disagree about the
    //! same program, which no test elsewhere would catch.

    use super::*;

    fn int1(raw: u128) -> InterpretInt {
        InterpretInt {
            bits: 8,
            signed: false,
            raw,
        }
    }

    #[test]
    fn int_carrier_matches_the_lean_semantics() {
        let block = BlockId(0);
        for (a, b) in [(0u128, 0u128), (0, 1), (1, 0), (1, 1)] {
            let and = eval_int_binop(BinOp::BAnd, int1(a), int1(b), block).unwrap();
            let or = eval_int_binop(BinOp::BOr, int1(a), int1(b), block).unwrap();
            let xor = eval_int_binop(BinOp::BXor, int1(a), int1(b), block).unwrap();
            assert_eq!(and.raw, u128::from(a != 0 && b != 0), "BAnd({a},{b})");
            assert_eq!(or.raw, u128::from(a != 0 || b != 0), "BOr({a},{b})");
            assert_eq!(xor.raw, u128::from((a != 0) != (b != 0)), "BXor({a},{b})");
        }
    }

    /// Totality on operands OUTSIDE {0,1}: the Lean arms test `!= 0`, not `== 1`,
    /// so any nonzero counts as true and nothing is undefined. This is what lets
    /// them join `binop_progress`'s total-op case with no proof obligation.
    #[test]
    fn nonzero_operands_count_as_true_and_never_error() {
        let block = BlockId(0);
        let and = eval_int_binop(BinOp::BAnd, int1(7), int1(200), block).unwrap();
        assert_eq!(and.raw, 1, "any two nonzero operands are both true");
        let xor = eval_int_binop(BinOp::BXor, int1(7), int1(200), block).unwrap();
        assert_eq!(xor.raw, 0, "true xor true is false");
        let or = eval_int_binop(BinOp::BOr, int1(0), int1(200), block).unwrap();
        assert_eq!(or.raw, 1);
    }

    /// The Bool path must accept them. Before this arm existed the catch-all in
    /// `eval_bool_binop` rejected these on exactly the type the validator
    /// REQUIRES for them, so every well-typed use would have errored.
    #[test]
    fn bool_carrier_accepts_the_connectives() {
        let block = BlockId(0);
        for (a, b) in [(false, false), (false, true), (true, false), (true, true)] {
            assert_eq!(eval_bool_binop(BinOp::BAnd, a, b, block).unwrap(), a && b);
            assert_eq!(eval_bool_binop(BinOp::BOr, a, b, block).unwrap(), a || b);
            assert_eq!(eval_bool_binop(BinOp::BXor, a, b, block).unwrap(), a ^ b);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{DialectInst, vector as vector_dialect};
    use crate::inst::{BindingFrameDef, BindingSlot, SwitchCase};
    use crate::ty::FuncTy;
    use crate::value::BindingFrameId;
    use crate::{Block, Function, Module};

    fn v(index: u32) -> ValueId {
        ValueId::new(index)
    }

    fn b(index: u32) -> BlockId {
        BlockId::new(index)
    }

    fn result(inst: Inst, value: ValueId) -> InstrNode {
        InstrNode::new(inst).with_result(value)
    }

    fn void(inst: Inst) -> InstrNode {
        InstrNode::new(inst)
    }

    fn module_with_function(function: Function, returns: Vec<Ty>) -> Module {
        let mut module = Module::new("interp-test");
        module.add_func_type(FuncTy {
            params: Vec::new(),
            returns,
            is_vararg: false,
        });
        module.add_function(function);
        module
    }

    fn int_signed(value: &InterpretValue) -> i128 {
        value.as_int().expect("integer value").as_signed()
    }

    fn int_unsigned(value: &InterpretValue) -> u128 {
        value.as_int().expect("integer value").as_unsigned()
    }

    fn float_f64(value: &InterpretValue) -> f64 {
        match (&value.ty, value.kind.clone()) {
            (Ty::F32, InterpretValueKind::FloatBits(bits)) => f32::from_bits(bits as u32) as f64,
            (Ty::F64, InterpretValueKind::FloatBits(bits)) => f64::from_bits(bits),
            other => panic!("expected float, got {other:?}"),
        }
    }

    fn vector_signed(value: &InterpretValue) -> Vec<i128> {
        match &value.kind {
            InterpretValueKind::Vector(lanes) => lanes.iter().map(int_signed).collect(),
            other => panic!("expected vector, got {other:?}"),
        }
    }

    fn bool_vector(value: &InterpretValue) -> Vec<bool> {
        match &value.kind {
            InterpretValueKind::Vector(lanes) => lanes
                .iter()
                .map(|lane| lane.as_bool().expect("bool lane"))
                .collect(),
            other => panic!("expected vector, got {other:?}"),
        }
    }

    fn float_vector(value: &InterpretValue) -> Vec<f64> {
        match &value.kind {
            InterpretValueKind::Vector(lanes) => lanes.iter().map(float_f64).collect(),
            other => panic!("expected vector, got {other:?}"),
        }
    }

    fn float_const(value: impl Into<f64>) -> Constant {
        Constant::Float(value.into())
    }

    #[test]
    fn executes_constants_integer_compare_and_select() {
        let mut function = Function::new(FuncId::new(0), "select", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(40),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(2),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(50),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(2),
                rhs: v(3),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            },
            v(5),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(9),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::Select {
                ty: Ty::I32,
                cond: v(4),
                then_val: v(5),
                else_val: v(6),
            },
            v(7),
        ));
        block.body.push(void(Inst::Return { values: vec![v(7)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("function executes");

        assert_eq!(outcome.steps, 9);
        assert_eq!(int_signed(&outcome.returns[0]), 1);
    }

    #[test]
    fn executes_vector_element_ops_and_vector_select() {
        let mut function = Function::new(FuncId::new(0), "vector", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v2_i64(),
                value: Constant::v2_i64([1, 4]),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v2_i64(),
                value: Constant::v2_i64([3, 2]),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::v2_i64(),
                lhs: v(0),
                rhs: v(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::v2_i64(),
                lhs: v(2),
                rhs: v(1),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::Select {
                ty: Ty::v2_i64(),
                cond: v(3),
                then_val: v(2),
                else_val: v(1),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(1),
            },
            v(5),
        ));
        block.body.push(result(
            Inst::ExtractElement {
                ty: Ty::I64,
                array: v(4),
                index: v(5),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(-7),
            },
            v(7),
        ));
        block.body.push(result(
            Inst::InsertElement {
                ty: Ty::v2_i64(),
                array: v(4),
                index: v(5),
                value: v(7),
            },
            v(8),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(3), v(6), v(8)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::v2_bool(), Ty::I64, Ty::v2_i64()]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("function executes");

        assert_eq!(bool_vector(&outcome.returns[0]), vec![true, true]);
        assert_eq!(int_signed(&outcome.returns[1]), 6);
        assert_eq!(vector_signed(&outcome.returns[2]), vec![4, -7]);
    }

    #[test]
    fn interprets_vector_dialect_lane_ops() {
        let mut function = Function::new(
            FuncId::new(0),
            "vector_dialect",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        for (index, value) in [(0, 1), (1, -2), (2, 30), (3, 4)] {
            block.body.push(result(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(value),
                },
                v(index),
            ));
        }
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::pack_lanes(
                Ty::v4_i32(),
                [v(0), v(1), v(2), v(3)],
            ))),
            v(4),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::extract_lane(
                Ty::v4_i32(),
                v(4),
                2,
            ))),
            v(5),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(99),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::insert_lane(
                Ty::v4_i32(),
                v(4),
                1,
                v(6),
            ))),
            v(7),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(10),
            },
            v(8),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(11),
            },
            v(9),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::pack_lanes(
                Ty::v2_i64(),
                [v(8), v(9)],
            ))),
            v(10),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::extract_lane(
                Ty::v2_i64(),
                v(10),
                1,
            ))),
            v(11),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(-5),
            },
            v(12),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::insert_lane(
                Ty::v2_i64(),
                v(10),
                0,
                v(12),
            ))),
            v(13),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(5), v(7), v(11), v(13)],
        }));
        function.blocks.push(block);

        let module =
            module_with_function(function, vec![Ty::I32, Ty::v4_i32(), Ty::I64, Ty::v2_i64()]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("vector dialect lane ops execute");

        assert_eq!(int_signed(&outcome.returns[0]), 30);
        assert_eq!(vector_signed(&outcome.returns[1]), vec![1, 99, 30, 4]);
        assert_eq!(int_signed(&outcome.returns[2]), 11);
        assert_eq!(vector_signed(&outcome.returns[3]), vec![-5, 11]);
    }

    #[test]
    fn interprets_vector_dialect_mask_to_bits_lane0_lsb() {
        let mut function = Function::new(
            FuncId::new(0),
            "vector_masks",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v4_bool(),
                value: Constant::Vector(vec![
                    Constant::Bool(true),
                    Constant::Bool(false),
                    Constant::Bool(true),
                    Constant::Bool(true),
                ]),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::mask_to_bits(
                Ty::v4_bool(),
                v(0),
                Ty::I32,
            ))),
            v(1),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v2_bool(),
                value: Constant::Vector(vec![Constant::Bool(false), Constant::Bool(true)]),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::mask_to_bits(
                Ty::v2_bool(),
                v(2),
                Ty::I64,
            ))),
            v(3),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v8_bool(),
                value: Constant::v8_bool_mask([true; 8]),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::mask_to_bits(
                Ty::v8_bool(),
                v(4),
                Ty::I32,
            ))),
            v(5),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v16_bool(),
                value: Constant::v16_bool_mask([
                    true, true, true, true, true, true, true, true, true, true, true, true, true,
                    true, true, true,
                ]),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::mask_to_bits(
                Ty::v16_bool(),
                v(6),
                Ty::I32,
            ))),
            v(7),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(1), v(3), v(5), v(7)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32, Ty::I64, Ty::I32, Ty::I32]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("vector mask_to_bits ops execute");

        assert_eq!(int_unsigned(&outcome.returns[0]), 0b1101);
        assert_eq!(int_unsigned(&outcome.returns[1]), 0b10);
        assert_eq!(int_unsigned(&outcome.returns[2]), 0xff);
        assert_eq!(int_unsigned(&outcome.returns[3]), 0xffff);
    }

    #[test]
    fn interprets_vector_dialect_reduce_add_and_or() {
        let mut function = Function::new(
            FuncId::new(0),
            "vector_reduce",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // <4 x i32> = [1, -2, 30, 4]; reduce-add = 33.
        block.body.push(result(
            Inst::Const {
                ty: Ty::v4_i32(),
                value: Constant::v4_i32([1, -2, 30, 4]),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::reduce(
                Ty::v4_i32(),
                v(0),
                vector_dialect::ReduceKind::Add,
            ))),
            v(1),
        ));
        // <2 x i64> = [0b0011, 0b1100]; reduce-or = 0b1111 = 15.
        block.body.push(result(
            Inst::Const {
                ty: Ty::v2_i64(),
                value: Constant::v2_i64([0b0011, 0b1100]),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::reduce(
                Ty::v2_i64(),
                v(2),
                vector_dialect::ReduceKind::Or,
            ))),
            v(3),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(1), v(3)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32, Ty::I64]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("vector reduce ops execute");

        assert_eq!(int_signed(&outcome.returns[0]), 33);
        assert_eq!(int_unsigned(&outcome.returns[1]), 0b1111);
    }

    #[test]
    fn interprets_vector_dialect_reduce_add_wraps_modulo_lane_width() {
        let mut function = Function::new(
            FuncId::new(0),
            "vector_reduce_wrap",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // i32::MAX + 1 + 1 wraps to i32::MIN + 1 (modular arithmetic).
        block.body.push(result(
            Inst::Const {
                ty: Ty::v4_i32(),
                value: Constant::v4_i32([i32::MAX, 1, 1, 0]),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::reduce(
                Ty::v4_i32(),
                v(0),
                vector_dialect::ReduceKind::Add,
            ))),
            v(1),
        ));
        block.body.push(void(Inst::Return { values: vec![v(1)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("wrapping reduce executes");

        let expected = (i32::MAX).wrapping_add(1).wrapping_add(1).wrapping_add(0);
        assert_eq!(int_signed(&outcome.returns[0]), i128::from(expected));
        assert_eq!(expected, i32::MIN + 1);
    }

    #[test]
    fn interprets_vector_dialect_shuffle_static_permutation() {
        let mut function = Function::new(
            FuncId::new(0),
            "vector_shuffle",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // Reverse a <4 x i32> via the static index mask [3, 2, 1, 0].
        block.body.push(result(
            Inst::Const {
                ty: Ty::v4_i32(),
                value: Constant::v4_i32([10, 20, 30, 40]),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::shuffle(
                Ty::v4_i32(),
                v(0),
                [3u8, 2, 1, 0],
            ))),
            v(1),
        ));
        // Broadcast lane 1 of a <2 x i64> into both result lanes via [1, 1].
        block.body.push(result(
            Inst::Const {
                ty: Ty::v2_i64(),
                value: Constant::v2_i64([7, -9]),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::shuffle(
                Ty::v2_i64(),
                v(2),
                [1u8, 1],
            ))),
            v(3),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(1), v(3)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::v4_i32(), Ty::v2_i64()]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("vector shuffle ops execute");

        assert_eq!(vector_signed(&outcome.returns[0]), vec![40, 30, 20, 10]);
        assert_eq!(vector_signed(&outcome.returns[1]), vec![-9, -9]);
    }

    #[test]
    fn interprets_vector_dialect_fma_per_lane() {
        // Pick a lane whose unfused (a*b rounded, then +c) result differs from
        // the fused single-rounding result, so the assertion actually pins
        // fusion rather than two-step f32 arithmetic. (1 + 2^-12)^2 - 1 rounds
        // differently under one rounding step vs two.
        let a0 = 1.0_f32 + 2.0_f32.powi(-12);
        let b0 = a0;
        let c0 = -1.0_f32;
        let fused = a0.mul_add(b0, c0);
        let unfused = (a0 * b0) + c0;
        assert_ne!(
            fused.to_bits(),
            unfused.to_bits(),
            "test vector must exercise the fused vs unfused difference"
        );

        let mut function =
            Function::new(FuncId::new(0), "vector_fma", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        let f32_vec = |xs: [f32; 4]| Constant::Vector(xs.iter().map(|x| float_const(*x)).collect());
        block.body.push(result(
            Inst::Const {
                ty: Ty::v4_f32(),
                value: f32_vec([a0, 2.0, 3.0, 0.5]),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v4_f32(),
                value: f32_vec([b0, 3.0, 0.0, 8.0]),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v4_f32(),
                value: f32_vec([c0, 4.0, 9.0, 1.0]),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::fma(
                Ty::v4_f32(),
                v(0),
                v(1),
                v(2),
            ))),
            v(3),
        ));
        // <2 x f64>: [2*3+4, 1.5*2+0.5] = [10.0, 3.5].
        let f64_vec = |xs: [f64; 2]| Constant::Vector(xs.iter().map(|x| float_const(*x)).collect());
        block.body.push(result(
            Inst::Const {
                ty: Ty::v2_f64(),
                value: f64_vec([2.0, 1.5]),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v2_f64(),
                value: f64_vec([3.0, 2.0]),
            },
            v(5),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v2_f64(),
                value: f64_vec([4.0, 0.5]),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::fma(
                Ty::v2_f64(),
                v(4),
                v(5),
                v(6),
            ))),
            v(7),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(3), v(7)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::v4_f32(), Ty::v2_f64()]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("vector fma ops execute");

        let v4 = float_vector(&outcome.returns[0]);
        // Lane 0 must equal the fused single-rounding result bit-for-bit.
        assert_eq!((v4[0] as f32).to_bits(), fused.to_bits());
        assert_eq!(v4[1], 10.0); // 2*3 + 4
        assert_eq!(v4[2], 9.0); // 3*0 + 9
        assert_eq!(v4[3], 5.0); // 0.5*8 + 1

        let v2 = float_vector(&outcome.returns[1]);
        assert_eq!(v2, vec![10.0, 3.5]);
    }

    #[test]
    fn vector_dialect_ops_fail_closed_for_invalid_payloads() {
        let mut bad_lane_fn =
            Function::new(FuncId::new(0), "bad_lane", crate::FuncTyId::new(0), b(0));
        let mut bad_lane_block = Block::new(b(0));
        bad_lane_block.body.push(result(
            Inst::Const {
                ty: Ty::v4_i32(),
                value: Constant::v4_i32([1, 2, 3, 4]),
            },
            v(0),
        ));
        bad_lane_block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::extract_lane(
                Ty::v4_i32(),
                v(0),
                4,
            ))),
            v(1),
        ));
        bad_lane_fn.blocks.push(bad_lane_block);
        let bad_lane_module = module_with_function(bad_lane_fn, vec![Ty::I32]);
        let error = Interpreter::with_module(&bad_lane_module)
            .execute_func(FuncId::new(0), [])
            .expect_err("out-of-range vector dialect lane is rejected");
        assert_eq!(error.code, InterpretErrorCode::UnsupportedDialectOp);

        let mut bad_lane_type_fn = Function::new(
            FuncId::new(0),
            "bad_lane_type",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut bad_lane_type_block = Block::new(b(0));
        bad_lane_type_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            },
            v(0),
        ));
        bad_lane_type_block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
            },
            v(1),
        ));
        bad_lane_type_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(3),
            },
            v(2),
        ));
        bad_lane_type_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(4),
            },
            v(3),
        ));
        bad_lane_type_block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::pack_lanes(
                Ty::v4_i32(),
                [v(0), v(1), v(2), v(3)],
            ))),
            v(4),
        ));
        bad_lane_type_fn.blocks.push(bad_lane_type_block);
        let bad_lane_type_module = module_with_function(bad_lane_type_fn, vec![Ty::v4_i32()]);
        let error = Interpreter::with_module(&bad_lane_type_module)
            .execute_func(FuncId::new(0), [])
            .expect_err("mismatched lane operand type is rejected");
        assert_eq!(error.code, InterpretErrorCode::TypeError);

        let mut bad_mask_fn =
            Function::new(FuncId::new(0), "bad_mask", crate::FuncTyId::new(0), b(0));
        let mut bad_mask_block = Block::new(b(0));
        bad_mask_block.body.push(result(
            Inst::Const {
                ty: Ty::v4_i32(),
                value: Constant::v4_i32([1, 0, 1, 1]),
            },
            v(0),
        ));
        bad_mask_block.body.push(result(
            Inst::DialectOp(Box::new(vector_dialect::mask_to_bits(
                Ty::v4_i32(),
                v(0),
                Ty::I32,
            ))),
            v(1),
        ));
        bad_mask_fn.blocks.push(bad_mask_block);
        let bad_mask_module = module_with_function(bad_mask_fn, vec![Ty::I32]);
        let error = Interpreter::with_module(&bad_mask_module)
            .execute_func(FuncId::new(0), [])
            .expect_err("non-bool mask is rejected");
        assert_eq!(error.code, InterpretErrorCode::UnsupportedVectorShape);
    }

    #[test]
    fn executes_alloca_store_gep_load_and_dealloc() {
        let mut function = Function::new(FuncId::new(0), "memory", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(2),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I32,
                count: Some(v(0)),
                align: Some(16),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            },
            v(2),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I32,
            ptr: v(1),
            value: v(2),
            volatile: true,
            align: Some(4),
        }));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(1),
                indices: vec![v(3)],
                inbounds: false,
            },
            v(4),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(32),
            },
            v(5),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I32,
            ptr: v(4),
            value: v(5),
            volatile: false,
            align: Some(4),
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: true,
                align: Some(4),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(4),
                volatile: false,
                align: Some(4),
            },
            v(7),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(6),
                rhs: v(7),
            },
            v(8),
        ));
        block.body.push(void(Inst::Dealloc { ptr: v(1) }));
        block.body.push(void(Inst::Return { values: vec![v(8)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("memory program executes");

        assert_eq!(int_signed(&outcome.returns[0]), 42);
    }

    /// Copy-propagates-poison, case-A shape (struct-tail padding): a whole-lane
    /// `Load i64` reads one initialized byte (a bool niche at offset 0) plus
    /// seven never-written padding bytes, producing a `PartialBytes` transport
    /// value. Storing it verbatim into a fresh slot preserves the initialized
    /// byte, and a narrow reload of that byte succeeds — the program COMPLETES
    /// (no undefined behaviour) because the poison is only transported, never
    /// inspected.
    #[test]
    fn poison_padding_lane_copy_round_trips() {
        let mut function =
            Function::new(FuncId::new(0), "poison_pad", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        // src: 16-byte, 8-aligned region; dst: 8-byte, 8-aligned region.
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(2),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(0)),
                align: Some(8),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(2)),
                align: Some(8),
            },
            v(3),
        ));
        // Initialize ONLY byte 0 of src (the bool niche); bytes 1..7 stay uninit.
        block.body.push(result(
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(7),
            },
            v(4),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I8,
            ptr: v(1),
            value: v(4),
            volatile: false,
            align: Some(1),
        }));
        // Whole-lane load: byte 0 init, 1..7 uninit -> PartialBytes.
        block.body.push(result(
            Inst::Load {
                ty: Ty::I64,
                ptr: v(1),
                volatile: false,
                align: Some(8),
            },
            v(5),
        ));
        // Transport the poison verbatim into dst (preserves uninit-ness).
        block.body.push(void(Inst::Store {
            ty: Ty::I64,
            ptr: v(3),
            value: v(5),
            volatile: false,
            align: Some(8),
        }));
        // Narrow reload of the surviving initialized byte succeeds.
        block.body.push(result(
            Inst::Load {
                ty: Ty::I8,
                ptr: v(3),
                volatile: false,
                align: Some(1),
            },
            v(6),
        ));
        block.body.push(void(Inst::Return { values: vec![v(6)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I8]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("padding-lane copy completes");
        assert_eq!(int_signed(&outcome.returns[0]), 7);
    }

    /// Copy-propagates-poison, case-B shape (inactive niche-enum payload): a
    /// 16-byte value has an initialized niche word at 0..7 and a fully
    /// uninitialized inactive-variant payload at 8..15. A whole-image copy moves
    /// both lanes; the payload lane loads as `PartialBytes`, is passed through a
    /// `Copy` (transport), and stored verbatim. The program COMPLETES and the
    /// surviving niche word reads back intact.
    #[test]
    fn poison_niche_enum_payload_lane_copy_round_trips() {
        let mut function = Function::new(
            FuncId::new(0),
            "poison_niche",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(2),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(0)),
                align: Some(8),
            },
            v(1),
        )); // src, 16 bytes
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(2),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(2)),
                align: Some(8),
            },
            v(3),
        )); // dst, 16 bytes
        // Niche word at 0..7 initialized; payload at 8..15 left uninit.
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
            v(4),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I64,
            ptr: v(1),
            value: v(4),
            volatile: false,
            align: Some(8),
        }));
        // Lane 0 (fully initialized) copy: src+0 -> dst+0.
        block.body.push(result(
            Inst::Load {
                ty: Ty::I64,
                ptr: v(1),
                volatile: false,
                align: Some(8),
            },
            v(5),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I64,
            ptr: v(3),
            value: v(5),
            volatile: false,
            align: Some(8),
        }));
        // Lane 1 (uninitialized payload) copy: src+8 -> Copy -> dst+8.
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(1),
                indices: vec![v(6)],
                inbounds: false,
            },
            v(7),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I64,
                ptr: v(7),
                volatile: false,
                align: Some(8),
            },
            v(8),
        )); // PartialBytes (all 8 bytes uninit)
        block.body.push(result(
            Inst::Copy {
                ty: Ty::I64,
                operand: v(8),
            },
            v(9),
        )); // Copy transports poison verbatim
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            },
            v(10),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(3),
                indices: vec![v(10)],
                inbounds: false,
            },
            v(11),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I64,
            ptr: v(11),
            value: v(9),
            volatile: false,
            align: Some(8),
        }));
        // The surviving niche word reads back intact.
        block.body.push(result(
            Inst::Load {
                ty: Ty::I64,
                ptr: v(3),
                volatile: false,
                align: Some(8),
            },
            v(12),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(12)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I64]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("niche-payload copy completes");
        assert_eq!(int_signed(&outcome.returns[0]), 0);
    }

    /// Copy-propagates-poison is NOT a blanket relaxation: INSPECTING a
    /// `PartialBytes` value (here an integer `Add`) is undefined behaviour, and
    /// faults at the true use site rather than silently miscomputing.
    #[test]
    fn poison_arithmetic_consumption_is_undefined_behavior() {
        let mut function =
            Function::new(FuncId::new(0), "poison_use", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: Some(8),
            },
            v(0),
        ));
        // Initialize only byte 0; bytes 1..7 stay uninit.
        block.body.push(result(
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(5),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I8,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(1),
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I64,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            v(2),
        )); // PartialBytes
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(2),
                rhs: v(2),
            },
            v(3),
        )); // inspects poison -> UB
        block.body.push(void(Inst::Return { values: vec![v(3)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I64]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("arithmetic on a partially-initialized value is UB");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(
            error.message.contains("uninitialized"),
            "unexpected message: {}",
            error.message
        );
    }

    /// A NO-INITIALIZER global is BSS / `.tbss`: the loader zero-fills it, so a
    /// load of it reads a DEFINED zero, never poison. (The RandomState hash-seed
    /// thread-local `Storage` relies on this: its zero `State` discriminant means
    /// "Uninitialized", switched on in `get_or_init`.)
    #[test]
    fn no_initializer_global_reads_as_defined_zero() {
        let mut function =
            Function::new(FuncId::new(0), "bss_global", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::GlobalAddr {
                global: GlobalId::new(0),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            v(1),
        ));
        block.body.push(void(Inst::Return { values: vec![v(1)] }));
        function.blocks.push(block);

        let mut module = module_with_function(function, vec![Ty::U64]);
        module.globals.push(crate::Global {
            name: "BSS".to_string(),
            ty: Ty::U64,
            mutable: true,
            initializer: None,
            linkage: crate::Linkage::Internal,
            tls: None,
            align: None,
        });
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("no-initializer global reads as defined zero");
        assert_eq!(int_unsigned(&outcome.returns[0]), 0);
    }

    /// Regression guard: the BSS zero-fill is scoped to GLOBALS only. A heap
    /// (`HeapAlloc`) region stays uninitialized, so a load of it still yields
    /// poison and consuming it is still undefined behaviour — genuine
    /// use-of-uninit is not masked by the global zero-fill.
    #[test]
    fn bss_zero_fill_does_not_leak_into_heap_alloc() {
        let mut function =
            Function::new(FuncId::new(0), "heap_uninit", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::HeapAlloc {
                ty: Ty::U64,
                count: None,
                align: Some(8),
                origin: crate::inst::AllocOrigin::RustHeap,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            v(1),
        )); // PartialBytes — heap is not zero-filled
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: v(1),
                rhs: v(1),
            },
            v(2),
        )); // inspects poison -> UB
        block.body.push(void(Inst::Return { values: vec![v(2)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::U64]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("uninitialized heap load consumed is UB");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(
            error.message.contains("uninitialized"),
            "unexpected message: {}",
            error.message
        );
    }

    /// A global gets a base honoring more than its byte-image `Ty` alignment: a
    /// `(u64,u64)`-style static lowered to `Array(U8, 24)` reports natural
    /// alignment 1, yet `keys.0` is read with a natural-align-8 `load u64`. The
    /// global allocator must place it on an aligned base even after a prior
    /// odd-sized allocation left the bump cursor misaligned — otherwise the
    /// aligned load spuriously faults ("pointer address N is not aligned to 8").
    #[test]
    fn byte_image_global_gets_aligned_base_for_natural_aligned_load() {
        let mut function = Function::new(
            FuncId::new(0),
            "global_align",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // Misalign the bump cursor first: a 3-byte stack allocation leaves the
        // next base at an odd address.
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(3),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::U8,
                count: Some(v(0)),
                align: Some(1),
            },
            v(1),
        ));
        // Now the byte-image global (align-1 `Ty`, no declared align): its base
        // must still be >= 8-aligned so the u64 load below is legal.
        block.body.push(result(
            Inst::GlobalAddr {
                global: GlobalId::new(0),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(2),
                volatile: false,
                align: Some(8),
            },
            v(3),
        ));
        block.body.push(void(Inst::Return { values: vec![v(3)] }));
        function.blocks.push(block);

        let mut module = module_with_function(function, vec![Ty::U64]);
        let u8_ty = module.add_type(Ty::U8);
        module.globals.push(crate::Global {
            name: "KEYS".to_string(),
            ty: Ty::Array(u8_ty, 24),
            mutable: true,
            initializer: None,
            linkage: crate::Linkage::Internal,
            tls: None,
            align: None,
        });
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("natural-align-8 load from a byte-image global succeeds");
        assert_eq!(int_unsigned(&outcome.returns[0]), 0);
    }

    /// Build a one-block function that allocates an 8-byte region (heap or
    /// stack), then loads a `u64` at `read_off` through it. Models hashbrown's
    /// group scan reading into the allocator's usable-size slack.
    fn over_read_program(heap: bool, read_off: i128) -> Module {
        let mut function =
            Function::new(FuncId::new(0), "over_read", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        let alloc_inst = if heap {
            Inst::HeapAlloc {
                ty: Ty::U64,
                count: None,
                align: Some(8),
                origin: crate::inst::AllocOrigin::RustHeap,
            }
        } else {
            Inst::Alloca {
                ty: Ty::U64,
                count: None,
                align: Some(8),
            }
        };
        block.body.push(result(alloc_inst, v(0)));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(read_off),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(2),
                volatile: false,
                align: Some(1),
            },
            v(3),
        ));
        block.body.push(void(Inst::Return { values: vec![v(3)] }));
        function.blocks.push(block);
        module_with_function(function, vec![Ty::U64])
    }

    /// A HEAP allocation carries a readable, defined usable-size slack tail: a
    /// group-style read just past the 8 requested bytes (offset 8, inside the
    /// 16-byte slack) succeeds and returns the defined slack fill (0xFF bytes),
    /// NOT poison — modelling `__rust_alloc`'s over-allocation that hashbrown's
    /// control-byte scan reads into.
    #[test]
    fn heap_alloc_usable_slack_is_readable_defined() {
        let module = over_read_program(true, 8);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("heap slack read succeeds");
        // Eight 0xFF slack bytes little-endian == u64::MAX.
        assert_eq!(int_unsigned(&outcome.returns[0]), u128::from(u64::MAX));
    }

    /// Heap-only scoping: a STACK `Alloca` of the SAME size has NO slack, so the
    /// identical over-read (offset 8, past the 8 requested bytes) still faults —
    /// stack OOB detection is not weakened by the heap slack model.
    #[test]
    fn stack_alloca_over_read_still_faults() {
        let module = over_read_program(false, 8);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("stack over-read is OOB");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(
            error.message.contains("out of bounds"),
            "unexpected message: {}",
            error.message
        );
    }

    /// The heap slack is BOUNDED: a read past `requested + slack` (offset 24 =
    /// 8 requested + 16 slack) still faults, so the model admits only the tail
    /// window, not unbounded over-reads.
    #[test]
    fn heap_read_past_slack_faults() {
        let module = over_read_program(true, 24);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("heap read past the slack tail is OOB");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(
            error.message.contains("out of bounds"),
            "unexpected message: {}",
            error.message
        );
    }

    /// A `<N x bool>` SIMD comparison mask reinterpreted to an integer uses the
    /// ALL-ONES per-lane convention (0xFF for a true byte lane), not scalar
    /// `0x01` — this is the core of hashbrown's NEON `Group::match_full`
    /// (`vreinterpret_u64_u8 ∘ vcgez_s8`, i.e. `<8 x i8> icmp sge ctrl, 0`
    /// reinterpreted to `u64`). Input lanes `[0,-1,2,-3,4,-5,6,-7]` are `>= 0`
    /// at the even lanes, so the packed little-endian mask is `0x00FF00FF00FF00FF`.
    #[test]
    fn vector_bool_mask_reinterprets_as_all_ones_per_lane() {
        let v8i8 = Ty::Vector(Box::new(Ty::I8), 8);
        let mut function = Function::new(FuncId::new(0), "mask", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: v8i8.clone(),
                value: Constant::Vector(
                    [0, -1, 2, -3, 4, -5, 6, -7]
                        .into_iter()
                        .map(Constant::Int)
                        .collect(),
                ),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: v8i8.clone(),
                value: Constant::Vector(std::iter::repeat_n(Constant::Int(0), 8).collect()),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::ICmp {
                op: ICmpOp::Sge,
                ty: v8i8.clone(),
                lhs: v(0),
                rhs: v(1),
            },
            v(2),
        )); // -> Vector(Bool, 8)
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::U64,
                count: None,
                align: Some(8),
            },
            v(3),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::Vector(Box::new(Ty::Bool), 8),
            ptr: v(3),
            value: v(2),
            volatile: false,
            align: Some(1),
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(3),
                volatile: false,
                align: Some(8),
            },
            v(4),
        ));
        block.body.push(void(Inst::Return { values: vec![v(4)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::U64]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("mask reinterpret executes");
        assert_eq!(int_unsigned(&outcome.returns[0]), 0x00FF_00FF_00FF_00FF);
    }

    /// No-provenance ("dangling") pointer VALUES are first-class: `IntToPtr(8)`
    /// (a `NonNull::dangling`-style sentinel) can be created, STORED to memory,
    /// LOADED back, COPIED, and COMPARED via a `PtrToInt` round-trip + `ICmp`.
    /// None of these dereference the pointer, so none fault.
    #[test]
    fn dangling_pointer_creates_stores_loads_copies_and_compares() {
        let mut function = Function::new(
            FuncId::new(0),
            "dangling_value",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // IntToPtr(8) -> a no-provenance pointer value.
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: v(0),
            },
            v(1),
        ));
        // Store it, then load it back (round-trips through the 8-byte image).
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::Ptr,
                count: None,
                align: Some(8),
            },
            v(2),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(2),
            value: v(1),
            volatile: false,
            align: Some(8),
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::Ptr,
                ptr: v(2),
                volatile: false,
                align: Some(8),
            },
            v(3),
        ));
        // Copy (transport), then PtrToInt + ICmp (the empty-iterator compare).
        block.body.push(result(
            Inst::Copy {
                ty: Ty::Ptr,
                operand: v(3),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: v(4),
            },
            v(5),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: v(5),
                rhs: v(6),
            },
            v(7),
        ));
        block.body.push(void(Inst::Return { values: vec![v(7)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::Bool]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("dangling pointer create/store/load/copy/compare succeeds");
        assert_eq!(outcome.returns[0].as_bool(), Some(true));
    }

    /// A LOAD *through* a no-provenance pointer faults — the provenance error
    /// moved from creation time to dereference time.
    #[test]
    fn dangling_pointer_load_through_faults_with_provenance_error() {
        let mut function = Function::new(
            FuncId::new(0),
            "dangling_load",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: v(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I64,
                ptr: v(1),
                volatile: false,
                align: Some(8),
            },
            v(2),
        ));
        block.body.push(void(Inst::Return { values: vec![v(2)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I64]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("load through a dangling pointer is UB");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(
            error.message.contains("no allocation provenance") && error.message.contains('8'),
            "unexpected message: {}",
            error.message
        );
    }

    /// A STORE *through* a no-provenance pointer faults for the same reason.
    #[test]
    fn dangling_pointer_store_through_faults_with_provenance_error() {
        let mut function = Function::new(
            FuncId::new(0),
            "dangling_store",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: v(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            },
            v(2),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I64,
            ptr: v(1),
            value: v(2),
            volatile: false,
            align: Some(8),
        }));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("store through a dangling pointer is UB");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(
            error.message.contains("no allocation provenance"),
            "unexpected message: {}",
            error.message
        );
    }

    /// B2 fat pointers round-trip END TO END: assemble a str-kind fat pointer
    /// over an alloca'd byte buffer (`PtrFromParts`), store/load the 16-byte
    /// two-lane image through MEMORY, re-project both lanes (`PtrData` +
    /// `PtrMetadata`), and read an element back through the data lane (GEP +
    /// Load) — the full producer-side value path for `&[T]`/`&str`.
    #[test]
    fn fat_pointer_parts_memory_round_trip() {
        use crate::FatPtrKind;
        let fat_ty = Ty::FatPtr(FatPtrKind::Str);
        let meta_ty = Ty::U64;
        let mut module = Module::new("b2");
        let sig = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U8, Ty::U64],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "b2_fat", sig, b(0));
        let mut block = Block::new(b(0));
        // buffer[2] = {0x61, 0x62}
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0x61),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::U8,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        // len = 1; fat = PtrFromParts(buf, len)
        block.body.push(result(
            Inst::Const {
                ty: meta_ty.clone(),
                value: Constant::Int(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::PtrFromParts {
                ptr_ty: fat_ty.clone(),
                metadata_ty: meta_ty.clone(),
                data: v(0),
                metadata: v(2),
            },
            v(3),
        ));
        // store/load the fat value through memory
        block.body.push(result(
            Inst::Alloca {
                ty: fat_ty.clone(),
                count: None,
                align: None,
            },
            v(4),
        ));
        block.body.push(void(Inst::Store {
            ty: fat_ty.clone(),
            ptr: v(4),
            value: v(3),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: fat_ty.clone(),
                ptr: v(4),
                volatile: false,
                align: None,
            },
            v(5),
        ));
        // re-project + read the element through the data lane
        block.body.push(result(
            Inst::PtrData {
                ptr_ty: fat_ty.clone(),
                ptr: v(5),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::PtrMetadata {
                ptr_ty: fat_ty.clone(),
                metadata_ty: meta_ty.clone(),
                ptr: v(5),
            },
            v(7),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U8,
                ptr: v(6),
                volatile: false,
                align: None,
            },
            v(8),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(8), v(7)],
        }));
        function.blocks.push(block);
        module.functions.push(function);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("fat pointer program executes");
        assert_eq!(int_signed(&outcome.returns[0]), 0x61);
        assert_eq!(int_signed(&outcome.returns[1]), 1);
    }

    /// B2-3 trait-object fat pointers round-trip END TO END: unlike the
    /// slice/str kinds the metadata lane is a POINTER (a vtable stand-in),
    /// not a length — `metadata_ty` is `Ty::Ptr`. Assemble the fat value over
    /// a live data allocation with a second live allocation as the vtable
    /// address, store/load the 16-byte two-lane image through MEMORY,
    /// re-project both lanes, and prove the metadata lane survived as a
    /// dereferenceable pointer by loading a sentinel byte back through it.
    #[test]
    fn trait_object_fat_pointer_memory_round_trip() {
        use crate::FatPtrKind;
        use crate::ty::stable_trait_object_id;
        let fat_ty = Ty::FatPtr(FatPtrKind::TraitObject {
            trait_id: stable_trait_object_id("core::fmt::Debug"),
        });
        let meta_ty = Ty::Ptr;
        let mut module = Module::new("b2_dyn");
        let sig = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U8, Ty::U8],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "b2_dyn_fat", sig, b(0));
        let mut block = Block::new(b(0));
        // data byte = 0x61; vtable stand-in byte = 0x7f
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0x61),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::U8,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: None,
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0x7f),
            },
            v(3),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::U8,
            ptr: v(2),
            value: v(3),
            volatile: false,
            align: None,
        }));
        // fat = PtrFromParts(data, vtable-ptr)
        block.body.push(result(
            Inst::PtrFromParts {
                ptr_ty: fat_ty.clone(),
                metadata_ty: meta_ty.clone(),
                data: v(0),
                metadata: v(2),
            },
            v(4),
        ));
        // store/load the fat value through memory
        block.body.push(result(
            Inst::Alloca {
                ty: fat_ty.clone(),
                count: None,
                align: None,
            },
            v(5),
        ));
        block.body.push(void(Inst::Store {
            ty: fat_ty.clone(),
            ptr: v(5),
            value: v(4),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: fat_ty.clone(),
                ptr: v(5),
                volatile: false,
                align: None,
            },
            v(6),
        ));
        // re-project both lanes; read a byte back through EACH pointer
        block.body.push(result(
            Inst::PtrData {
                ptr_ty: fat_ty.clone(),
                ptr: v(6),
            },
            v(7),
        ));
        block.body.push(result(
            Inst::PtrMetadata {
                ptr_ty: fat_ty.clone(),
                metadata_ty: meta_ty.clone(),
                ptr: v(6),
            },
            v(8),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U8,
                ptr: v(7),
                volatile: false,
                align: None,
            },
            v(9),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U8,
                ptr: v(8),
                volatile: false,
                align: None,
            },
            v(10),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(9), v(10)],
        }));
        function.blocks.push(block);
        module.functions.push(function);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("trait-object fat pointer program executes");
        assert_eq!(int_signed(&outcome.returns[0]), 0x61);
        assert_eq!(int_signed(&outcome.returns[1]), 0x7f);
    }

    /// The executable fat-pointer model is deliberately the same fixed
    /// 64-bit model as the Lean semantics. A validator may describe a valid
    /// 32-bit wire module, but this interpreter must reject that target rather
    /// than silently execute it with the 64-bit two-lane layout.
    #[test]
    fn fat_pointer_execution_rejects_non_64_bit_target() {
        use crate::FatPtrKind;

        let fat_ty = Ty::FatPtr(FatPtrKind::Str);
        let mut module = Module::new("b2-32-bit-rejected");
        module.target_info = Some(crate::TargetInfo {
            triple: "i686-unknown-linux-gnu".into(),
            pointer_size: 4,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        let sig = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "fat32", sig, b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(1),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::PtrFromParts {
                ptr_ty: fat_ty,
                metadata_ty: Ty::U32,
                data: v(0),
                metadata: v(1),
            },
            v(2),
        ));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.functions.push(function);

        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("32-bit fat-pointer execution must fail closed");
        assert_eq!(error.code, InterpretErrorCode::UnsupportedMemory);
        assert!(error.message.contains("64-bit little-endian"), "{error:?}");

        module.target_info.as_mut().expect("target").pointer_size = 8;
        module.target_info.as_mut().expect("target").endianness = crate::Endianness::Big;
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("big-endian fat-pointer execution must fail closed");
        assert_eq!(error.code, InterpretErrorCode::UnsupportedMemory);
        assert!(error.message.contains("big-endian"), "{error:?}");
    }

    #[test]
    fn fat_pointer_from_parts_rejects_malformed_metadata_shape() {
        use crate::FatPtrKind;

        let fat_ty = Ty::FatPtr(FatPtrKind::Str);
        let mut module = Module::new("malformed-fatptr-parts");
        let sig = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::U64],
            returns: vec![fat_ty.clone()],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "from_parts", sig, b(0));
        let mut block = Block::new(b(0))
            .with_param(v(0), Ty::Ptr)
            .with_param(v(1), Ty::U64);
        block.body.push(result(
            Inst::PtrFromParts {
                ptr_ty: fat_ty,
                metadata_ty: Ty::U64,
                data: v(0),
                metadata: v(1),
            },
            v(2),
        ));
        block.body.push(void(Inst::Return { values: vec![v(2)] }));
        function.blocks.push(block);
        module.functions.push(function);

        let data = InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::NullPtr,
        };
        let malformed_metadata = InterpretValue {
            ty: Ty::U64,
            kind: InterpretValueKind::Bool(true),
        };
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [data, malformed_metadata])
            .expect_err("PtrFromParts must reject a malformed internal metadata shape");
        assert_eq!(error.code, InterpretErrorCode::TypeError);
        assert!(
            error.message.contains("metadata does not inhabit"),
            "{error:?}"
        );
    }

    #[test]
    fn borrow_of_fat_pointer_value_is_a_verbatim_pass_through() {
        use crate::FatPtrKind;

        // A fat reborrow round-trips: assemble a fat `&str` value over a real
        // one-byte allocation, `Borrow` it (the `_0 = &(*_1)` mir_built
        // reborrow shape), `BorrowMut` the result (the `&mut` spelling of the
        // same pass-through), and prove the value survived VERBATIM — the
        // returned value still carries the fat ty and both lanes: the data
        // lane still loads the stored byte and the metadata lane is still the
        // length. Before this arm the interpreter refused with
        // "Borrow: expected pointer value, got fatptr<str>".
        let fat_ty = Ty::FatPtr(FatPtrKind::Str);
        let mut module = Module::new("borrow-of-fat");
        let sig = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![fat_ty.clone(), fat_ty.clone(), Ty::U8, Ty::U64],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "reborrow", sig, b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(42),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::U8,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::PtrFromParts {
                ptr_ty: fat_ty.clone(),
                metadata_ty: Ty::U64,
                data: v(0),
                metadata: v(2),
            },
            v(3),
        ));
        block.body.push(result(Inst::Borrow { ptr: v(3) }, v(4)));
        block.body.push(result(Inst::BorrowMut { ptr: v(4) }, v(5)));
        // Observe both lanes THROUGH the doubly-reborrowed value.
        block.body.push(result(
            Inst::PtrData {
                ptr_ty: fat_ty.clone(),
                ptr: v(5),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::U8,
                ptr: v(6),
                volatile: false,
                align: None,
            },
            v(7),
        ));
        block.body.push(result(
            Inst::PtrMetadata {
                ptr_ty: fat_ty.clone(),
                metadata_ty: Ty::U64,
                ptr: v(5),
            },
            v(8),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(3), v(5), v(7), v(8)],
        }));
        function.blocks.push(block);
        module.functions.push(function);

        let out = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("a fat reborrow executes as a pure pass-through");
        // The reborrowed value IS the assembled fat value, verbatim.
        assert_eq!(out.returns[0], out.returns[1]);
        assert_eq!(out.returns[1].ty, fat_ty);
        assert!(matches!(
            out.returns[1].kind,
            InterpretValueKind::FatPtr { .. }
        ));
        // Data lane: loading through it still reads the stored byte.
        assert_eq!(out.returns[2].as_int().unwrap().as_unsigned(), 42);
        // Metadata lane: still the length.
        assert_eq!(out.returns[3].as_int().unwrap().as_unsigned(), 1);
    }

    #[test]
    fn fat_pointer_store_rejects_malformed_internal_metadata_shape() {
        use crate::FatPtrKind;

        let fat_ty = Ty::FatPtr(FatPtrKind::Str);
        let mut module = Module::new("malformed-fatptr");
        let sig = module.add_func_type(FuncTy {
            params: vec![fat_ty.clone()],
            returns: vec![],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "store", sig, b(0));
        let mut block = Block::new(b(0)).with_param(v(0), fat_ty.clone());
        block.body.push(result(
            Inst::Alloca {
                ty: fat_ty.clone(),
                count: None,
                align: None,
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: fat_ty.clone(),
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: None,
        }));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.functions.push(function);

        let malformed = InterpretValue {
            ty: fat_ty,
            kind: InterpretValueKind::FatPtr {
                data: Box::new(InterpretValue {
                    ty: Ty::Ptr,
                    kind: InterpretValueKind::NullPtr,
                }),
                metadata: Box::new(InterpretValue {
                    ty: Ty::U64,
                    kind: InterpretValueKind::Bool(true),
                }),
            },
        };
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [malformed])
            .expect_err("malformed internal metadata must fail closed");
        assert_eq!(error.code, InterpretErrorCode::TypeError);
        assert!(
            error.message.contains("metadata does not inhabit"),
            "{error:?}"
        );
    }

    /// B6 closure captures round-trip at REGISTER level: a closure value seeds
    /// via `Constant::Closure`, rewrites a capture with `InsertField`, and reads
    /// it back with `ExtractField` — the by-value closure-env lane (no memory
    /// transit; a closure type still has no byte layout, fail-closed elsewhere).
    #[test]
    fn closure_captures_insert_extract_round_trip() {
        let mut module = Module::new("b6");
        let callee_sig = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let clo_ty_id = module.add_closure_type(crate::ClosureTy {
            func: callee_sig,
            captures: vec![Ty::I32, Ty::Bool],
        });
        let clo_ty = Ty::Closure(clo_ty_id);
        let main_sig = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        // A body for the closure's FuncId(0) so the module is self-contained.
        let mut callee = Function::new(FuncId::new(0), "clo", callee_sig, b(0));
        let mut cb = Block::new(b(0));
        cb.params.push((v(0), Ty::I32));
        cb.body.push(void(Inst::Return { values: vec![v(0)] }));
        callee.blocks.push(cb);
        module.functions.push(callee);

        let mut function = Function::new(FuncId::new(1), "b6_regs", main_sig, b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: clo_ty.clone(),
                value: Constant::Closure {
                    func: FuncId::new(0),
                    captures: vec![Constant::Int(0), Constant::Bool(false)],
                },
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(41),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::InsertField {
                ty: clo_ty.clone(),
                aggregate: v(1),
                field: 0,
                value: v(2),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(3),
                field: 0,
            },
            v(4),
        ));
        block.body.push(void(Inst::Return { values: vec![v(4)] }));
        function.blocks.push(block);
        module.functions.push(function);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(1), [])
            .expect("closure register program executes");
        assert_eq!(int_signed(&outcome.returns[0]), 41);
    }

    /// B1 faithful scalars round-trip through MEMORY: `byte_size`/`byte_align`
    /// must lay out `Isize`/`Usize` at pointer bytes (the pinned 64-bit
    /// reference target) and `Char` at its 32-bit carrier — `int_shape` alone
    /// covers registers, not the Alloca/Store/Load encode path.
    #[test]
    fn executes_faithful_scalar_alloca_store_load_round_trips() {
        for (ty, raw, expect) in [
            (Ty::Isize, -5i64 as u64 as i128, -5i128),
            (Ty::Usize, 7, 7),
            (Ty::Char, 0x61, 0x61),
        ] {
            let mut function =
                Function::new(FuncId::new(0), "b1_mem", crate::FuncTyId::new(0), b(0));
            let mut block = Block::new(b(0));
            block.body.push(result(
                Inst::Alloca {
                    ty: ty.clone(),
                    count: None,
                    align: None,
                },
                v(0),
            ));
            block.body.push(result(
                Inst::Const {
                    ty: ty.clone(),
                    value: Constant::Int(raw),
                },
                v(1),
            ));
            block.body.push(void(Inst::Store {
                ty: ty.clone(),
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }));
            block.body.push(result(
                Inst::Load {
                    ty: ty.clone(),
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
                v(2),
            ));
            block.body.push(void(Inst::Return { values: vec![v(2)] }));
            function.blocks.push(block);

            let module = module_with_function(function, vec![ty.clone()]);
            let outcome = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .unwrap_or_else(|e| panic!("{ty} memory program executes: {e:?}"));
            assert_eq!(int_signed(&outcome.returns[0]), expect, "{ty}");
        }
    }

    #[test]
    fn executes_x86_shaped_vector_load_store() {
        let mut function = Function::new(
            FuncId::new(0),
            "vector_memory",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::v4_i32(),
                count: None,
                align: Some(16),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::v4_i32(),
                value: Constant::Vector(vec![
                    Constant::Int(1),
                    Constant::Int(2),
                    Constant::Int(3),
                    Constant::Int(4),
                ]),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::v4_i32(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(16),
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::v4_i32(),
                ptr: v(0),
                volatile: false,
                align: Some(16),
            },
            v(2),
        ));
        block.body.push(void(Inst::Return { values: vec![v(2)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::v4_i32()]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("vector memory program executes");

        assert_eq!(vector_signed(&outcome.returns[0]), vec![1, 2, 3, 4]);
    }

    #[test]
    fn null_load_reports_undefined_behavior_code() {
        let mut function =
            Function::new(FuncId::new(0), "null_load", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(Inst::NullPtr, v(0)));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(1),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("null load is UB");

        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert_eq!(error.code.as_str(), "undefined_behavior");
    }

    #[test]
    fn out_of_bounds_load_reports_undefined_behavior_code() {
        let mut function = Function::new(FuncId::new(0), "oob_load", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(2),
                volatile: false,
                align: Some(4),
            },
            v(3),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("oob load is UB");

        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert_eq!(error.code.as_str(), "undefined_behavior");
    }

    #[test]
    fn misaligned_load_reports_undefined_behavior_code() {
        let mut function =
            Function::new(FuncId::new(0), "misaligned", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(2),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I32,
                count: Some(v(0)),
                align: Some(4),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(1),
                indices: vec![v(2)],
                inbounds: false,
            },
            v(3),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(3),
                volatile: false,
                align: Some(8),
            },
            v(4),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("misaligned load is UB");

        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert_eq!(error.code.as_str(), "undefined_behavior");
    }

    #[test]
    fn use_after_dealloc_reports_undefined_behavior_code() {
        let mut function = Function::new(FuncId::new(0), "uaf", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(void(Inst::Dealloc { ptr: v(0) }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(1),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("use after dealloc is UB");

        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert_eq!(error.code.as_str(), "undefined_behavior");
    }

    /// A STRICT (volatile) load keeps the all-initialized discipline: reading
    /// uninitialized memory is undefined behaviour, reported immediately. (The
    /// non-strict plain-load path now yields a `PartialBytes` poison value
    /// instead — see the `poison_*` copy-propagates-poison tests above.)
    #[test]
    fn uninitialized_load_reports_undefined_behavior_code() {
        let mut function =
            Function::new(FuncId::new(0), "uninit_load", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: true,
                align: None,
            },
            v(1),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("uninitialized volatile load is UB");

        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert_eq!(error.code.as_str(), "undefined_behavior");
    }

    #[test]
    fn unit_phantom_constant_stores_and_loads_as_unit() {
        let mut function =
            Function::new(FuncId::new(0), "unit_memory", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::Unit,
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::Unit,
                value: Constant::PhantomData,
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::Unit,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::Unit,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(2),
        ));
        block.body.push(void(Inst::Return { values: vec![v(2)] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::Unit]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("unit phantom constant must round-trip through memory");

        assert!(matches!(outcome.returns[0].kind, InterpretValueKind::Unit));
    }

    #[test]
    fn executes_aggregate_field_ops() {
        let tuple_ty = Ty::Tuple(vec![Ty::I32, Ty::Bool]);
        let mut function =
            Function::new(FuncId::new(0), "aggregate", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: tuple_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(7), Constant::Bool(false)]),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::Bool,
                aggregate: v(0),
                field: 1,
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::InsertField {
                ty: tuple_ty.clone(),
                aggregate: v(0),
                field: 1,
                value: v(2),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::Bool,
                aggregate: v(3),
                field: 1,
            },
            v(4),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(1), v(4)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::Bool, Ty::Bool]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("function executes");

        assert_eq!(outcome.returns[0].as_bool(), Some(false));
        assert_eq!(outcome.returns[1].as_bool(), Some(true));
    }

    #[test]
    fn executes_basic_control_flow_switch_and_block_args() {
        let mut function = Function::new(FuncId::new(0), "control", crate::FuncTyId::new(0), b(0));

        let mut entry = Block::new(b(0));
        entry.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(2),
            },
            v(0),
        ));
        entry.body.push(void(Inst::Switch {
            value: v(0),
            default: b(2),
            default_args: vec![v(0)],
            cases: vec![SwitchCase {
                value: Constant::Int(2),
                target: b(1),
                args: vec![v(0)],
            }],
            exhaustive_enum_unreachable: false,
        }));

        let mut then_block = Block::new(b(1)).with_param(v(1), Ty::I32);
        then_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(40),
            },
            v(2),
        ));
        then_block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(1),
                rhs: v(2),
            },
            v(3),
        ));
        then_block
            .body
            .push(void(Inst::Return { values: vec![v(3)] }));

        let mut default_block = Block::new(b(2)).with_param(v(4), Ty::I32);
        default_block
            .body
            .push(void(Inst::Return { values: vec![v(4)] }));

        function.blocks.push(entry);
        function.blocks.push(then_block);
        function.blocks.push(default_block);

        let module = module_with_function(function, vec![Ty::I32]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("function executes");

        assert_eq!(int_signed(&outcome.returns[0]), 42);
    }

    #[test]
    fn direct_call_executes_callee_frame_and_binds_return() {
        let mut module = Module::new("direct-call");
        let add_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let main_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut main = Function::new(FuncId::new(0), "main", main_ty, b(0));
        let mut main_block = Block::new(b(0));
        main_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(40),
            },
            v(0),
        ));
        main_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(2),
            },
            v(1),
        ));
        main_block.body.push(result(
            Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(0), v(1)],
            },
            v(2),
        ));
        main_block
            .body
            .push(void(Inst::Return { values: vec![v(2)] }));
        main.blocks.push(main_block);

        let mut add = Function::new(FuncId::new(1), "add", add_ty, b(0));
        let mut add_block = Block::new(b(0))
            .with_param(v(0), Ty::I32)
            .with_param(v(1), Ty::I32);
        add_block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            v(2),
        ));
        add_block
            .body
            .push(void(Inst::Return { values: vec![v(2)] }));
        add.blocks.push(add_block);

        module.add_function(main);
        module.add_function(add);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("direct call executes");

        assert_eq!(int_signed(&outcome.returns[0]), 42);
    }

    #[test]
    fn executes_integer_float_and_pointer_casts() {
        // Lean alignment gap: Lean currently axiomatizes float casts through
        // `Float` and pointer casts through raw addresses. The Rust fixture
        // only asserts finite in-range numeric casts and #92 provenance
        // recovery, where both models have matching observable results.
        let mut function = Function::new(FuncId::new(0), "casts", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I16,
                value: Constant::Int(0x12ff),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I16,
                dst_ty: Ty::U8,
                operand: v(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U8,
                dst_ty: Ty::U32,
                operand: v(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(-2),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: v(3),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::UIToFP,
                src_ty: Ty::U32,
                dst_ty: Ty::F64,
                operand: v(2),
            },
            v(5),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I32,
                operand: v(5),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            },
            v(7),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::U64,
                operand: v(7),
            },
            v(8),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::U64,
                dst_ty: Ty::Ptr,
                operand: v(8),
            },
            v(9),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::PtrConst(Box::new(Ty::I32)),
                operand: v(9),
            },
            v(10),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I32,
            ptr: v(10),
            value: v(6),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(7),
                volatile: false,
                align: None,
            },
            v(11),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(1), v(2), v(4), v(5), v(11)],
        }));
        function.blocks.push(block);

        let module =
            module_with_function(function, vec![Ty::U8, Ty::U32, Ty::I32, Ty::F64, Ty::I32]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("cast program executes");

        assert_eq!(int_unsigned(&outcome.returns[0]), 0xff);
        assert_eq!(int_unsigned(&outcome.returns[1]), 0xff);
        assert_eq!(int_signed(&outcome.returns[2]), -2);
        assert_eq!(float_f64(&outcome.returns[3]), 255.0);
        assert_eq!(int_signed(&outcome.returns[4]), 255);
    }

    #[test]
    fn executes_bool_integer_resize_casts_as_one_bit_lanes() {
        let mut function = Function::new(
            FuncId::new(0),
            "bool_resize_casts",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::U8,
                operand: v(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I8,
                operand: v(0),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(2),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I8,
                dst_ty: Ty::Bool,
                operand: v(3),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(3),
            },
            v(5),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I8,
                dst_ty: Ty::Bool,
                operand: v(5),
            },
            v(6),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(1), v(2), v(4), v(6)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::U8, Ty::I8, Ty::Bool, Ty::Bool]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("Bool resize casts execute");

        assert_eq!(int_unsigned(&outcome.returns[0]), 1);
        assert_eq!(int_signed(&outcome.returns[1]), -1);
        assert_eq!(outcome.returns[2].as_bool(), Some(false));
        assert_eq!(outcome.returns[3].as_bool(), Some(true));
    }

    #[test]
    fn executes_float_ops_and_ordered_unordered_compares() {
        // Lean alignment gap: the formal model uses Lean `Float` (f64) for
        // float ops. Rust executes f32/f64 directly and keeps f16 unsupported
        // until both sides share an explicit half-precision codec.
        let mut function = Function::new(FuncId::new(0), "floats", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(1.5),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(2.25),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::UnOp {
                op: UnOp::FNeg,
                ty: Ty::F64,
                operand: v(2),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::FCmp {
                op: FCmpOp::OLt,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(f64::NAN),
            },
            v(5),
        ));
        block.body.push(result(
            Inst::FCmp {
                op: FCmpOp::OEq,
                ty: Ty::F64,
                lhs: v(5),
                rhs: v(5),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::FCmp {
                op: FCmpOp::UEq,
                ty: Ty::F64,
                lhs: v(5),
                rhs: v(5),
            },
            v(7),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(5.5),
            },
            v(8),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(2.0),
            },
            v(9),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::FRem,
                ty: Ty::F64,
                lhs: v(8),
                rhs: v(9),
            },
            v(10),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(-5.5),
            },
            v(11),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::FRem,
                ty: Ty::F64,
                lhs: v(11),
                rhs: v(9),
            },
            v(12),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F32,
                value: Constant::Float(5.5),
            },
            v(13),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F32,
                value: Constant::Float(2.0),
            },
            v(14),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::FRem,
                ty: Ty::F32,
                lhs: v(13),
                rhs: v(14),
            },
            v(15),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(2), v(3), v(4), v(6), v(7), v(10), v(12), v(15)],
        }));
        function.blocks.push(block);

        let module = module_with_function(
            function,
            vec![
                Ty::F64,
                Ty::F64,
                Ty::Bool,
                Ty::Bool,
                Ty::Bool,
                Ty::F64,
                Ty::F64,
                Ty::F32,
            ],
        );
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("float program executes");

        assert_eq!(float_f64(&outcome.returns[0]), 3.75);
        assert_eq!(float_f64(&outcome.returns[1]), -3.75);
        assert_eq!(outcome.returns[2].as_bool(), Some(true));
        assert_eq!(outcome.returns[3].as_bool(), Some(false));
        assert_eq!(outcome.returns[4].as_bool(), Some(true));
        assert_eq!(float_f64(&outcome.returns[5]), 1.5);
        assert_eq!(float_f64(&outcome.returns[6]), -1.5);
        assert_eq!(float_f64(&outcome.returns[7]), 1.5);
    }

    #[test]
    fn executes_float_unary_ops() {
        // FAbs/FSqrt/FFloor/FCeil/FTrunc are IEEE 754 exact or
        // correctly-rounded operations, so executing them with the host
        // float methods is deterministic — the same contract as the float
        // binop slice. (The emit-each battery's fc_float program reaches all
        // five through `trust-ir run`.)
        let mut function =
            Function::new(FuncId::new(0), "float_unops", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(-2.25),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::UnOp {
                op: UnOp::FAbs,
                ty: Ty::F64,
                operand: v(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::UnOp {
                op: UnOp::FSqrt,
                ty: Ty::F64,
                operand: v(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::UnOp {
                op: UnOp::FFloor,
                ty: Ty::F64,
                operand: v(0),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::UnOp {
                op: UnOp::FCeil,
                ty: Ty::F64,
                operand: v(0),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::UnOp {
                op: UnOp::FTrunc,
                ty: Ty::F64,
                operand: v(0),
            },
            v(5),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::F32,
                value: Constant::Float(9.0),
            },
            v(6),
        ));
        block.body.push(result(
            Inst::UnOp {
                op: UnOp::FSqrt,
                ty: Ty::F32,
                operand: v(6),
            },
            v(7),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(1), v(2), v(3), v(4), v(5), v(7)],
        }));
        function.blocks.push(block);

        let module = module_with_function(
            function,
            vec![Ty::F64, Ty::F64, Ty::F64, Ty::F64, Ty::F64, Ty::F32],
        );
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("float unop program executes");

        assert_eq!(float_f64(&outcome.returns[0]), 2.25);
        assert_eq!(float_f64(&outcome.returns[1]), 1.5);
        assert_eq!(float_f64(&outcome.returns[2]), -3.0);
        assert_eq!(float_f64(&outcome.returns[3]), -2.0);
        assert_eq!(float_f64(&outcome.returns[4]), -2.0);
        assert_eq!(
            outcome.returns[5].kind,
            InterpretValueKind::FloatBits(u64::from(3.0f32.to_bits()))
        );
    }

    #[test]
    fn indirect_call_executes_registered_function_pointer() {
        let mut module = Module::new("indirect-call");
        let add_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let main_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut main = Function::new(FuncId::new(0), "main", main_ty, b(0));
        let mut main_block = Block::new(b(0));
        main_block.body.push(result(
            Inst::Const {
                ty: Ty::Func(add_ty),
                value: Constant::FnDef(FuncId::new(1)),
            },
            v(0),
        ));
        main_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            },
            v(1),
        ));
        main_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(32),
            },
            v(2),
        ));
        main_block.body.push(result(
            Inst::CallIndirect {
                callee: v(0),
                sig: add_ty,
                args: vec![v(1), v(2)],
                calling_conv: crate::CallingConv::C,
            },
            v(3),
        ));
        main_block
            .body
            .push(void(Inst::Return { values: vec![v(3)] }));
        main.blocks.push(main_block);

        let mut add = Function::new(FuncId::new(1), "add", add_ty, b(0));
        let mut add_block = Block::new(b(0))
            .with_param(v(0), Ty::I32)
            .with_param(v(1), Ty::I32);
        add_block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            v(2),
        ));
        add_block
            .body
            .push(void(Inst::Return { values: vec![v(2)] }));
        add.blocks.push(add_block);

        module.add_function(main);
        module.add_function(add);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("indirect call executes");

        assert_eq!(int_signed(&outcome.returns[0]), 42);
    }

    #[test]
    fn recursive_call_exhausts_shared_fuel() {
        let mut module = Module::new("recursive-fuel");
        let recurse_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "recurse", recurse_ty, b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Call {
                callee: FuncId::new(0),
                args: Vec::new(),
            },
            v(0),
        ));
        block.body.push(void(Inst::Return { values: vec![v(0)] }));
        function.blocks.push(block);
        module.add_function(function);

        let error = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                fuel: 3,
                ..InterpretOptions::default()
            })
            .execute_func(FuncId::new(0), [])
            .expect_err("recursive call exhausts fuel");

        assert_eq!(error.code, InterpretErrorCode::OutOfFuel);
        assert_eq!(error.code.as_str(), "out_of_fuel");
    }

    #[test]
    fn call_depth_limit_has_stable_code() {
        let mut module = Module::new("call-depth");
        let callee_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let main_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut main = Function::new(FuncId::new(0), "main", main_ty, b(0));
        let mut main_block = Block::new(b(0));
        main_block.body.push(result(
            Inst::Call {
                callee: FuncId::new(1),
                args: Vec::new(),
            },
            v(0),
        ));
        main_block
            .body
            .push(void(Inst::Return { values: vec![v(0)] }));
        main.blocks.push(main_block);

        let mut callee = Function::new(FuncId::new(1), "callee", callee_ty, b(0));
        let mut callee_block = Block::new(b(0));
        callee_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            },
            v(0),
        ));
        callee_block
            .body
            .push(void(Inst::Return { values: vec![v(0)] }));
        callee.blocks.push(callee_block);

        module.add_function(main);
        module.add_function(callee);

        let error = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                fuel: 10,
                max_call_depth: 0,
                ..InterpretOptions::default()
            })
            .execute_func(FuncId::new(0), [])
            .expect_err("call depth limit rejects the call");

        assert_eq!(error.code, InterpretErrorCode::OutOfFuel);
        assert_eq!(error.code.as_str(), "out_of_fuel");
    }

    #[test]
    fn undefined_direct_callee_has_stable_code() {
        let mut function = Function::new(FuncId::new(0), "call", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Call {
                callee: FuncId::new(99),
                args: Vec::new(),
            },
            v(0),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("direct callee is undefined");

        assert_eq!(error.code, InterpretErrorCode::MissingFunction);
        assert_eq!(error.code.as_str(), "missing_function");
    }

    #[test]
    fn invalid_indirect_function_pointer_has_stable_code() {
        let mut module = Module::new("invalid-pointer");
        let callee_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let main_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut main = Function::new(FuncId::new(0), "main", main_ty, b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::Func(callee_ty),
                value: Constant::FnDef(FuncId::new(99)),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::CallIndirect {
                callee: v(0),
                sig: callee_ty,
                args: Vec::new(),
                calling_conv: crate::CallingConv::C,
            },
            v(1),
        ));
        main.blocks.push(block);
        module.add_function(main);

        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("function pointer is not registered");

        assert_eq!(error.code, InterpretErrorCode::InvalidFunctionPointer);
        assert_eq!(error.code.as_str(), "invalid_function_pointer");
    }

    #[test]
    fn indirect_signature_mismatch_has_stable_code() {
        let mut module = Module::new("signature-mismatch");
        let callee_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let wrong_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let main_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut main = Function::new(FuncId::new(0), "main", main_ty, b(0));
        let mut main_block = Block::new(b(0));
        main_block.body.push(result(
            Inst::Const {
                ty: Ty::Func(callee_ty),
                value: Constant::FnDef(FuncId::new(1)),
            },
            v(0),
        ));
        main_block.body.push(result(
            Inst::CallIndirect {
                callee: v(0),
                sig: wrong_ty,
                args: Vec::new(),
                calling_conv: crate::CallingConv::C,
            },
            v(1),
        ));
        main.blocks.push(main_block);

        let mut callee = Function::new(FuncId::new(1), "needs_i32", callee_ty, b(0));
        let mut callee_block = Block::new(b(0)).with_param(v(0), Ty::I32);
        callee_block
            .body
            .push(void(Inst::Return { values: vec![v(0)] }));
        callee.blocks.push(callee_block);

        module.add_function(main);
        module.add_function(callee);

        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("indirect signature mismatches callee");

        assert_eq!(error.code, InterpretErrorCode::SignatureMismatch);
        assert_eq!(error.code.as_str(), "signature_mismatch");
    }

    #[test]
    fn unsupported_dialect_op_has_stable_code() {
        let mut function = Function::new(FuncId::new(0), "dialect", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::DialectOp(Box::new(
                DialectInst::new("example", "opaque").with_result_ty(Ty::I32),
            )),
            v(0),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("dialect ops are unsupported");

        assert_eq!(error.code, InterpretErrorCode::UnsupportedDialectOp);
        assert_eq!(error.code.as_str(), "unsupported_dialect_op");
    }

    #[test]
    fn borrow_arc_binding_frame_execute_in_the_reference_interpreter() {
        // These were once "unsupported slice" gaps (#84); the single-threaded
        // reference interpreter now executes them. Each sub-test exercises the
        // real behavior end-to-end.

        // Borrow: alloca an i32 slot, store 42, borrow the slot (yields a
        // reference = the same address), load through the borrow, return it.
        let mut borrow_fn = Function::new(FuncId::new(0), "borrow", crate::FuncTyId::new(0), b(0));
        let mut bb = Block::new(b(0));
        bb.body.push(result(
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            },
            v(0),
        ));
        bb.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            },
            v(1),
        ));
        bb.body.push(void(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        bb.body.push(result(Inst::Borrow { ptr: v(0) }, v(2)));
        bb.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(2),
                volatile: false,
                align: None,
            },
            v(3),
        ));
        bb.body.push(void(Inst::Return { values: vec![v(3)] }));
        borrow_fn.blocks.push(bb);
        let m = module_with_function(borrow_fn, vec![Ty::I32]);
        let out = Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), [])
            .expect("borrow executes");
        assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 42);

        // ARC: alloca, retain (count 1->2), IsUnique = false, release (2->1),
        // IsUnique = true.
        let mut arc_fn = Function::new(FuncId::new(0), "arc", crate::FuncTyId::new(0), b(0));
        let mut ab = Block::new(b(0));
        ab.body.push(result(
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            },
            v(0),
        ));
        ab.body.push(void(Inst::Retain { ptr: v(0) }));
        ab.body.push(result(Inst::IsUnique { ptr: v(0) }, v(1))); // false (count 2)
        ab.body.push(void(Inst::Release { ptr: v(0) }));
        ab.body.push(result(Inst::IsUnique { ptr: v(0) }, v(2))); // true (count 1)
        ab.body.push(void(Inst::Return {
            values: vec![v(1), v(2)],
        }));
        arc_fn.blocks.push(ab);
        let m = module_with_function(arc_fn, vec![Ty::Bool, Ty::Bool]);
        let out = Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), [])
            .expect("arc executes");
        assert_eq!(format!("{:?}", out.returns[0].kind), "Bool(false)");
        assert_eq!(format!("{:?}", out.returns[1].kind), "Bool(true)");

        // Binding frame: open a 1-slot frame, bind slot 0 = 7, load it back,
        // close the frame, return the loaded value.
        let mut frame_fn = Function::new(FuncId::new(0), "frame", crate::FuncTyId::new(0), b(0));
        let mut fb = Block::new(b(0));
        fb.body.push(result(
            Inst::OpenFrame {
                def: BindingFrameDef::new(
                    BindingFrameId::new(0),
                    "q",
                    vec![BindingSlot::new("i", Ty::I32)],
                ),
            },
            v(0),
        ));
        fb.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(7),
            },
            v(1),
        ));
        fb.body.push(void(Inst::BindSlot {
            frame: v(0),
            slot: 0,
            value: v(1),
        }));
        fb.body.push(result(
            Inst::LoadSlot {
                frame: v(0),
                slot: 0,
                ty: Ty::I32,
            },
            v(2),
        ));
        fb.body.push(void(Inst::CloseFrame { frame: v(0) }));
        fb.body.push(void(Inst::Return { values: vec![v(2)] }));
        frame_fn.blocks.push(fb);
        let m = module_with_function(frame_fn, vec![Ty::I32]);
        let out = Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), [])
            .expect("binding frame executes");
        assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 7);
    }

    #[test]
    fn intentionally_excluded_casts_and_float_widths_have_stable_codes() {
        let mut cast_fn = Function::new(FuncId::new(0), "transmute", crate::FuncTyId::new(0), b(0));
        let mut cast_block = Block::new(b(0));
        cast_block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(7),
            },
            v(0),
        ));
        cast_block.body.push(result(
            Inst::Cast {
                op: CastOp::Transmute,
                src_ty: Ty::I32,
                dst_ty: Ty::I32,
                operand: v(0),
            },
            v(1),
        ));
        cast_fn.blocks.push(cast_block);
        let cast_module = module_with_function(cast_fn, vec![Ty::I32]);
        let error = Interpreter::with_module(&cast_module)
            .execute_func(FuncId::new(0), [])
            .expect_err("transmute is intentionally excluded");
        assert_eq!(error.code, InterpretErrorCode::UnsupportedCast);
        assert_eq!(error.code.as_str(), "unsupported_cast");

        let mut f16_fn = Function::new(FuncId::new(0), "f16", crate::FuncTyId::new(0), b(0));
        let mut f16_block = Block::new(b(0));
        f16_block.body.push(result(
            Inst::Const {
                ty: Ty::F16,
                value: Constant::Float(1.0),
            },
            v(0),
        ));
        f16_fn.blocks.push(f16_block);
        let f16_module = module_with_function(f16_fn, vec![Ty::F16]);
        let error = Interpreter::with_module(&f16_module)
            .execute_func(FuncId::new(0), [])
            .expect_err("f16 has no executable codec");
        assert_eq!(error.code, InterpretErrorCode::UnsupportedFloat);
        assert_eq!(error.code.as_str(), "unsupported_float");
    }

    #[test]
    fn type_error_has_stable_code() {
        let mut function =
            Function::new(FuncId::new(0), "type_error", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            v(2),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("mismatched binop operand type");

        assert_eq!(error.code, InterpretErrorCode::TypeError);
        assert_eq!(error.code.as_str(), "type_error");
    }

    /// Regression (2026-06-16 whole-machine OOM): an `Alloca` whose element
    /// count is a large in-IR value used to be materialized directly as
    /// `vec![None; elem*count]`, so a single instruction could exhaust RAM+swap
    /// and panic the kernel (the failure mode that bricked the dev machine while
    /// the THIR→trust-ir differential interpreted a real-MIR oracle on boundary
    /// samples). With the space budget, the interpreter is now TOTAL in memory:
    /// the allocation fails closed with `OutOfMemory` BEFORE any host bytes are
    /// touched. This test itself would OOM the test runner if the guard were
    /// removed — its passing is the proof the guard holds.
    #[test]
    fn unbounded_alloca_hits_memory_budget_not_host_oom() {
        let mut function =
            Function::new(FuncId::new(0), "huge_alloca", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        // 2^40 elements of i64 ⇒ ~8 TiB requested — fits u64, passes the
        // checked_mul overflow guard, and is exactly what a sampled boundary
        // count would look like reaching `MemoryState::alloc`.
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1i128 << 40),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(0)),
                align: None,
            },
            v(1),
        ));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("oversized allocation must fail closed, not allocate");

        assert_eq!(error.code, InterpretErrorCode::OutOfMemory);
        assert_eq!(error.code.as_str(), "out_of_memory");
    }

    /// The budget must not regress legitimate small allocations: a handful of
    /// elements is far under the default 256 MiB and interprets cleanly.
    #[test]
    fn bounded_alloca_under_budget_succeeds() {
        let mut function = Function::new(
            FuncId::new(0),
            "small_alloca",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(4),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(0)),
                align: None,
            },
            v(1),
        ));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![]);
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("a 32-byte allocation is well under the default budget");
    }

    #[test]
    fn unsupported_zero_lane_vector_has_stable_code() {
        let mut function =
            Function::new(FuncId::new(0), "bad_vector", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::Vector(Box::new(Ty::I32), 0),
                value: Constant::Vector(Vec::new()),
            },
            v(0),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::Vector(Box::new(Ty::I32), 0)]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("zero-lane vector unsupported");

        assert_eq!(error.code, InterpretErrorCode::UnsupportedVectorShape);
        assert_eq!(error.code.as_str(), "unsupported_vector_shape");
    }

    #[test]
    fn out_of_fuel_has_stable_code() {
        let mut function = Function::new(FuncId::new(0), "loop", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(void(Inst::Br {
            target: b(0),
            args: Vec::new(),
        }));
        function.blocks.push(block);

        let module = module_with_function(function, Vec::new());
        let error = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                fuel: 1,
                ..InterpretOptions::default()
            })
            .execute_func(FuncId::new(0), [])
            .expect_err("loop exhausts fuel");

        assert_eq!(error.code, InterpretErrorCode::OutOfFuel);
        assert_eq!(error.code.as_str(), "out_of_fuel");
    }

    #[test]
    fn division_by_zero_reports_undefined_behavior_code() {
        let mut function = Function::new(FuncId::new(0), "ub", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(9),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::BinOp {
                op: BinOp::SDiv,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            v(2),
        ));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32]);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("division by zero");

        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert_eq!(error.code.as_str(), "undefined_behavior");
    }

    // M2 heap-faithful recursive-ADT support: a `Ty::Struct` now has a finite
    // C-layout, so it can be `HeapAlloc`'d, `Store`d, and `Load`ed back as a
    // byte image. This is the operational core the Rust->trust-ir M2 frontend
    // relies on (Box<Level> = a heap pointer to a tagged struct).
    #[test]
    fn heap_alloc_store_load_struct_round_trips_through_memory() {
        use crate::ty::{FieldDef, StructDef};
        use crate::value::StructId;

        // struct.0 = { tag: i32, p0: ptr, p1: ptr }  (the M2 MicroLevel shape).
        let sid = StructId::new(0);
        let struct_ty = Ty::Struct(sid);

        let mut module = Module::new("heap-struct-test");
        module.add_struct(StructDef {
            id: sid,
            name: "MicroLevel".into(),
            fields: vec![
                FieldDef {
                    name: "tag".into(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "p0".into(),
                    ty: Ty::Ptr,
                    offset: None,
                },
                FieldDef {
                    name: "p1".into(),
                    ty: Ty::Ptr,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut function =
            Function::new(FuncId::new(0), "heap_struct", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        // %0 = heap_alloc struct.0  (faithful Box::new of a tagged struct)
        block.body.push(result(
            Inst::HeapAlloc {
                ty: struct_ty.clone(),
                count: None,
                align: None,
                origin: crate::inst::AllocOrigin::RustHeap,
            },
            v(0),
        ));
        // Construct each field in place through a byte-offset GEP (the design's
        // "explicit byte-offset GEP over an I8 pointee" for struct field stores),
        // then read the whole struct back with a single Load(struct).
        // tag @0:  tag_ptr = gep i8 %0, [0] ; store i32 2 -> tag_ptr
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(1)],
                inbounds: true,
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(2),
            },
            v(3),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I32,
            ptr: v(2),
            value: v(3),
            volatile: false,
            align: None,
        }));
        // p0 @8: store null
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(4)],
                inbounds: true,
            },
            v(5),
        ));
        block.body.push(result(Inst::NullPtr, v(6)));
        block.body.push(void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(5),
            value: v(6),
            volatile: false,
            align: None,
        }));
        // p1 @16: store null
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(16),
            },
            v(7),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(7)],
                inbounds: true,
            },
            v(8),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(8),
            value: v(6),
            volatile: false,
            align: None,
        }));
        // Read the discriminant back the faithful way: a typed Load of the tag
        // field through its own field-offset GEP (no whole-struct load, so the
        // inter-field padding is never read). %9 = load i32 %2 ; return %9
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(2),
                volatile: false,
                align: None,
            },
            v(9),
        ));
        block.body.push(void(Inst::Return { values: vec![v(9)] }));
        function.blocks.push(block);
        module.add_function(function);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("heap struct round-trip executes");
        assert_eq!(
            int_signed(&outcome.returns[0]),
            2,
            "loaded tag survives the heap round-trip"
        );
    }

    #[test]
    fn struct_layout_is_c_style_with_field_padding() {
        use crate::ty::{FieldDef, StructDef};
        use crate::value::StructId;

        let sid = StructId::new(0);
        let mut module = Module::new("layout-test");
        // { tag: i32 (4B @0), p0: ptr (8B @8), p1: ptr (8B @16) } => size 24, align 8.
        module.add_struct(StructDef {
            id: sid,
            name: "MicroLevel".into(),
            fields: vec![
                FieldDef {
                    name: "tag".into(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "p0".into(),
                    ty: Ty::Ptr,
                    offset: None,
                },
                FieldDef {
                    name: "p1".into(),
                    ty: Ty::Ptr,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let interp = Interpreter::with_module(&module);
        let layout = interp
            .struct_layout(&Ty::Struct(sid), b(0))
            .expect("layout");
        assert_eq!(layout.align, 8);
        assert_eq!(layout.size, 24);
        assert_eq!(layout.field_offsets[0].0, 0);
        assert_eq!(layout.field_offsets[1].0, 8);
        assert_eq!(layout.field_offsets[2].0, 16);
    }

    // ===================================================================
    // The DECLARED struct layout (`StructDef::size`/`align` +
    // `FieldDef::offset`) — the struct analogue of `EnumLayoutDescriptor`.
    // ===================================================================

    /// `field(name, ty, offset)` — a `FieldDef` without the ceremony.
    fn fdef(name: &str, ty: Ty, offset: Option<u64>) -> crate::ty::FieldDef {
        crate::ty::FieldDef {
            name: name.into(),
            ty,
            offset,
        }
    }

    /// A `StructDef` with an explicitly declared (or explicitly absent) layout.
    fn sdef_with_layout(
        id: u32,
        name: &str,
        fields: Vec<crate::ty::FieldDef>,
        size: Option<u64>,
        align: Option<u64>,
        repr: crate::ty::StructRepr,
    ) -> crate::ty::StructDef {
        crate::ty::StructDef {
            id: crate::value::StructId::new(id),
            name: name.into(),
            fields,
            size,
            align,
            repr,
        }
    }

    /// THE WITNESS, as source. `struct Mixed { a: u8, b: u64, c: u8 }` is laid
    /// out by rustc as `b@0 a@8 c@9`, size 16 — it REORDERS by decreasing
    /// alignment. The declaration-order rule says `a@0 b@8 c@16`, size 24, so
    /// the producer's `gep inbounds i8, ptr %0, 9` for `&s.c` used to name a
    /// byte inside `b`. The declared layout is normative and must win.
    #[test]
    fn struct_layout_uses_the_declared_offsets_not_declaration_order() {
        let mut module = Module::new("declared-layout");
        module.add_struct(sdef_with_layout(
            0,
            "Mixed",
            vec![
                fdef("a", Ty::U8, Some(8)),
                fdef("b", Ty::U64, Some(0)),
                fdef("c", Ty::U8, Some(9)),
            ],
            Some(16),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        // Byte-identical field types, no declared layout: the canonical rule.
        module.add_struct(sdef_with_layout(
            1,
            "MixedUndeclared",
            vec![
                fdef("a", Ty::U8, None),
                fdef("b", Ty::U64, None),
                fdef("c", Ty::U8, None),
            ],
            None,
            None,
            crate::ty::StructRepr::Rust,
        ));

        let interp = Interpreter::with_module(&module);
        let declared = interp
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
            .expect("declared layout");
        assert_eq!(declared.size, 16, "the declared size is rustc's");
        assert_eq!(declared.align, 8);
        assert_eq!(
            declared
                .field_offsets
                .iter()
                .map(|(offset, _)| *offset)
                .collect::<Vec<_>>(),
            vec![8, 0, 9],
            "rustc's reordered offsets, verbatim"
        );

        // The control: without a declared layout NOTHING changes, and it is a
        // DIFFERENT answer — so the assertion above cannot be passing by
        // accident of the two rules agreeing.
        let canonical = interp
            .struct_layout(&Ty::Struct(crate::value::StructId::new(1)), b(0))
            .expect("canonical layout");
        assert_eq!(canonical.size, 24);
        assert_eq!(
            canonical
                .field_offsets
                .iter()
                .map(|(offset, _)| *offset)
                .collect::<Vec<_>>(),
            vec![0, 8, 16],
        );
    }

    /// The witness EXECUTED, not argued: store `0xAB` through a byte GEP at the
    /// producer's own displacement for `&s.c` (9) and read `c` back out of the
    /// whole-struct `Load`. Under the declaration-order rule byte 9 is interior
    /// to `b`, so `c` would read 0 and `b` would be corrupted.
    #[test]
    fn declared_struct_layout_round_trips_a_value_at_the_declared_offsets() {
        let mut module = Module::new("declared-layout-exec");
        module.add_struct(sdef_with_layout(
            0,
            "Mixed",
            vec![
                fdef("a", Ty::U8, Some(8)),
                fdef("b", Ty::U64, Some(0)),
                fdef("c", Ty::U8, Some(9)),
            ],
            Some(16),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        let struct_ty = Ty::Struct(crate::value::StructId::new(0));
        module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::U8, Ty::U64],
            is_vararg: false,
        });

        let mut function = Function::new(
            FuncId::new(0),
            "declared_offsets",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // %0 = heap_alloc Mixed
        block.body.push(result(
            Inst::HeapAlloc {
                ty: struct_ty.clone(),
                count: None,
                align: None,
                origin: crate::inst::AllocOrigin::RustHeap,
            },
            v(0),
        ));
        // Initialize the WHOLE 16-byte image first (padding included, so the
        // whole-struct Load below never reads an uninitialized byte): two
        // zeroing u64 stores at +0 and +8.
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(1)],
                inbounds: true,
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(0),
            },
            v(3),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::U64,
            ptr: v(2),
            value: v(3),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            },
            v(4),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(4)],
                inbounds: true,
            },
            v(5),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::U64,
            ptr: v(5),
            value: v(3),
            volatile: false,
            align: None,
        }));
        // c @9 = 0xAB — the producer's displacement for `&s.c`.
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(9),
            },
            v(7),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(7)],
                inbounds: true,
            },
            v(8),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0xAB),
            },
            v(9),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::U8,
            ptr: v(8),
            value: v(9),
            volatile: false,
            align: None,
        }));
        // %10 = load Mixed %0 ; return (c, b)
        block.body.push(result(
            Inst::Load {
                ty: struct_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(10),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::U8,
                aggregate: v(10),
                field: 2,
            },
            v(11),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::U64,
                aggregate: v(10),
                field: 1,
            },
            v(12),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(11), v(12)],
        }));
        function.blocks.push(block);
        module.add_function(function);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("declared-layout round trip executes");
        assert_eq!(
            int_signed(&outcome.returns[0]) & 0xFF,
            0xAB,
            "the byte written at the producer's displacement 9 IS field c"
        );
        assert_eq!(
            int_signed(&outcome.returns[1]),
            0,
            "field b at [0,8) is untouched by that write"
        );
    }

    /// A field the producer left with NO offset is admitted when — and only
    /// when — it occupies no bytes. That is the shape rustc's legal
    /// zero-sized-field placement (`offset == size`) makes producers emit:
    /// `Arc<T> { ptr, PhantomData, Allocator }` declares size 8 with one real
    /// offset. MEASURED: 275 of 1,299 clean-kernel struct defs are in this
    /// state, so it is the common case, not an edge.
    #[test]
    fn declared_struct_layout_admits_an_offsetless_zero_sized_field() {
        let mut module = Module::new("declared-zst");
        module.add_struct(sdef_with_layout(
            0,
            "ArcLike",
            vec![
                fdef("ptr", Ty::Ptr, Some(0)),
                fdef("phantom", Ty::Unit, None),
            ],
            Some(8),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        let layout = Interpreter::with_module(&module)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
            .expect("zero-sized field needs no declared offset");
        assert_eq!(layout.size, 8);
        assert_eq!(layout.field_offsets[0].0, 0);
        assert_eq!(
            layout.field_offsets[1].0, 0,
            "a zero-byte field addresses no byte; its placement is information-free"
        );
    }

    /// …and the discrimination control: a field that DOES occupy bytes cannot
    /// be placed by guessing. Without this the rule above would be "ignore
    /// missing offsets", which is the silent-divergence direction.
    #[test]
    fn declared_struct_layout_refuses_an_offsetless_sized_field() {
        let mut module = Module::new("declared-missing-offset");
        module.add_struct(sdef_with_layout(
            0,
            "Half",
            vec![fdef("a", Ty::U64, Some(0)), fdef("b", Ty::U64, None)],
            Some(16),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        let err = match Interpreter::with_module(&module)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
        {
            Ok(layout) => panic!(
                "a sized field with no declared offset is unplaceable, got size {}",
                layout.size
            ),
            Err(err) => err.to_string(),
        };
        assert!(err.contains("no offset"), "unexpected error: {err}");
    }

    /// Every structural fact is re-checked before a byte slice is formed —
    /// modules are interpretable without validation, exactly as for the enum
    /// descriptor.
    #[test]
    fn declared_struct_layout_refuses_incoherent_declarations() {
        let cases: Vec<(&str, crate::ty::StructDef, &str)> = vec![
            (
                "out of bounds",
                sdef_with_layout(
                    0,
                    "OOB",
                    vec![fdef("a", Ty::U64, Some(16))],
                    Some(16),
                    Some(8),
                    crate::ty::StructRepr::Rust,
                ),
                "out of bounds",
            ),
            (
                "overlap",
                sdef_with_layout(
                    0,
                    "Overlap",
                    vec![fdef("a", Ty::U64, Some(0)), fdef("b", Ty::U64, Some(0))],
                    Some(16),
                    Some(8),
                    crate::ty::StructRepr::Rust,
                ),
                "overlapping fields",
            ),
            (
                "misaligned",
                sdef_with_layout(
                    0,
                    "Misaligned",
                    vec![fdef("a", Ty::U64, Some(4))],
                    Some(16),
                    Some(8),
                    crate::ty::StructRepr::Rust,
                ),
                "misaligned",
            ),
            (
                "over-aligned field",
                sdef_with_layout(
                    0,
                    "OverAligned",
                    vec![fdef("a", Ty::U64, Some(0))],
                    Some(8),
                    Some(1),
                    crate::ty::StructRepr::Rust,
                ),
                "over-aligned",
            ),
            (
                "align is not a power of two",
                sdef_with_layout(
                    0,
                    "BadAlign",
                    vec![fdef("a", Ty::U8, Some(0))],
                    Some(6),
                    Some(3),
                    crate::ty::StructRepr::Rust,
                ),
                "incoherent size",
            ),
            (
                "size is not a multiple of align",
                sdef_with_layout(
                    0,
                    "BadSize",
                    vec![fdef("a", Ty::U8, Some(0))],
                    Some(9),
                    Some(8),
                    crate::ty::StructRepr::Rust,
                ),
                "incoherent size",
            ),
            (
                "size without align",
                sdef_with_layout(
                    0,
                    "HalfDeclared",
                    vec![fdef("a", Ty::U8, Some(0))],
                    Some(8),
                    None,
                    crate::ty::StructRepr::Rust,
                ),
                "without an alignment",
            ),
            (
                "field offsets with no declared size",
                sdef_with_layout(
                    0,
                    "OffsetsOnly",
                    vec![fdef("a", Ty::U8, Some(0))],
                    None,
                    None,
                    crate::ty::StructRepr::Rust,
                ),
                "no struct size",
            ),
        ];
        for (label, def, needle) in cases {
            let mut module = Module::new("declared-incoherent");
            module.add_struct(def);
            let err = match Interpreter::with_module(&module)
                .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
            {
                Ok(layout) => panic!(
                    "{label}: expected a refusal, got size {} align {}",
                    layout.size, layout.align
                ),
                Err(err) => err.to_string(),
            };
            assert!(
                err.contains(needle),
                "{label}: refusal did not name '{needle}': {err}"
            );
        }
    }

    /// `repr(packed(N))` IS a declaration that field alignment is clamped, so a
    /// packed layout's "misaligned" offsets are correct and must be admitted.
    /// Without this control the misalignment refusal above would be indistinct
    /// from a gate that refuses every non-natural offset.
    #[test]
    fn declared_struct_layout_admits_packed_offsets() {
        let mut module = Module::new("declared-packed");
        module.add_struct(sdef_with_layout(
            0,
            "Packed",
            vec![fdef("a", Ty::U8, Some(0)), fdef("b", Ty::U64, Some(1))],
            Some(9),
            Some(1),
            crate::ty::StructRepr::Packed(1),
        ));
        let layout = Interpreter::with_module(&module)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
            .expect("a repr(packed) layout is not misaligned");
        assert_eq!(layout.size, 9);
        assert_eq!(layout.align, 1);
        assert_eq!(layout.field_offsets[1].0, 1);
    }

    /// The declared size composes: a nested struct contributes ITS declared
    /// size to the outer bounds check, not a re-synthesized one. `Inner`
    /// declares 16 bytes while the declaration-order rule would say 9.
    #[test]
    fn declared_struct_layout_composes_through_a_nested_struct() {
        let mut module = Module::new("declared-nested");
        module.add_struct(sdef_with_layout(
            0,
            "Inner",
            vec![fdef("a", Ty::U8, Some(8)), fdef("b", Ty::U64, Some(0))],
            Some(16),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        module.add_struct(sdef_with_layout(
            1,
            "Outer",
            vec![
                fdef("inner", Ty::Struct(crate::value::StructId::new(0)), Some(0)),
                fdef("tail", Ty::U64, Some(16)),
            ],
            Some(24),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        let layout = Interpreter::with_module(&module)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(1)), b(0))
            .expect("nested declared layout");
        assert_eq!(layout.size, 24);
        assert_eq!(layout.field_offsets[1].0, 16);

        // The negative half: if the nested struct's declared 16 bytes were
        // ignored and its 9-byte declaration-order size used instead, a `tail`
        // at 8 would look fine. It must not.
        let mut bad = Module::new("declared-nested-bad");
        bad.add_struct(sdef_with_layout(
            0,
            "Inner",
            vec![fdef("a", Ty::U8, Some(8)), fdef("b", Ty::U64, Some(0))],
            Some(16),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        bad.add_struct(sdef_with_layout(
            1,
            "Outer",
            vec![
                fdef("inner", Ty::Struct(crate::value::StructId::new(0)), Some(0)),
                fdef("tail", Ty::U64, Some(8)),
            ],
            Some(24),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        if let Ok(layout) = Interpreter::with_module(&bad)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(1)), b(0))
        {
            panic!(
                "the nested struct's DECLARED 16 bytes must bound the outer field, got size {}",
                layout.size
            );
        }
    }

    // Aggregates-in-memory: a `Ty::Tuple` has a finite C-style layout (each
    // element placed at its aligned offset, total rounded up to the tuple
    // align), so it can be `Alloca`'d / `Store`d / `Load`ed faithfully. A tuple
    // needs no module `StructDef`, so layout queries work on a module-less
    // interpreter.
    #[test]
    fn tuple_layout_is_c_style_with_field_padding() {
        let interp = Interpreter::new();

        // (i32, i32) => both 4B-aligned, contiguous, size 8 align 4.
        let packed = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        assert_eq!(interp.byte_size(&packed, b(0)).expect("size"), 8);
        assert_eq!(interp.byte_align(&packed, b(0)).expect("align"), 4);
        let packed_layout = interp.tuple_layout(&packed, b(0)).expect("layout");
        assert_eq!(packed_layout.field_offsets[0].0, 0);
        assert_eq!(packed_layout.field_offsets[1].0, 4);

        // (i8, i32) => i32 needs 4B alignment, so it sits at offset 4 (not 1)
        // and the size is 8 (not 5): a padded layout, identical to Rust/C repr.
        let padded = Ty::Tuple(vec![Ty::I8, Ty::I32]);
        assert_eq!(interp.byte_size(&padded, b(0)).expect("size"), 8);
        assert_eq!(interp.byte_align(&padded, b(0)).expect("align"), 4);
        let padded_layout = interp.tuple_layout(&padded, b(0)).expect("layout");
        assert_eq!(padded_layout.field_offsets[0].0, 0, "i8 at offset 0");
        assert_eq!(padded_layout.field_offsets[1].0, 4, "i32 aligned up to 4");

        // The trailing-padding case (i32, i8) rounds the total up to the tuple
        // align (4): size 8, not 5.
        let trailing = Ty::Tuple(vec![Ty::I32, Ty::I8]);
        assert_eq!(interp.byte_size(&trailing, b(0)).expect("size"), 8);
        assert_eq!(interp.byte_align(&trailing, b(0)).expect("align"), 4);

        // The empty tuple is size 0, align 1 — consistent with `Ty::Unit`.
        let empty = Ty::Tuple(Vec::new());
        assert_eq!(interp.byte_size(&empty, b(0)).expect("size"), 0);
        assert_eq!(interp.byte_align(&empty, b(0)).expect("align"), 1);
    }

    // The operational core: `Alloca` a `(i32, i32)` slot, `Store` an in-register
    // `Aggregate([1, 2])` into it, `Load` it back as a `Ty::Tuple`, and confirm
    // the decoded aggregate equals what was stored. This exercises
    // `encode_value` / `decode_value` for `Ty::Tuple` end-to-end against the
    // shared offset layout.
    #[test]
    fn alloca_store_load_tuple_round_trips_through_memory() {
        let tuple_ty = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let mut function =
            Function::new(FuncId::new(0), "tuple_mem", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        // %0 = alloca (i32, i32)
        block.body.push(result(
            Inst::Alloca {
                ty: tuple_ty.clone(),
                count: None,
                align: None,
            },
            v(0),
        ));
        // %1 = const (i32, i32) { 1, 2 }
        block.body.push(result(
            Inst::Const {
                ty: tuple_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
            },
            v(1),
        ));
        // store (i32, i32) %1 -> %0   (whole-tuple store: exercises encode_value)
        block.body.push(void(Inst::Store {
            ty: tuple_ty.clone(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        // %2 = load (i32, i32) %0     (whole-tuple load: exercises decode_value)
        block.body.push(result(
            Inst::Load {
                ty: tuple_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(2),
        ));
        // Pull each field back out so we can assert the round-trip values.
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(2),
                field: 0,
            },
            v(3),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(2),
                field: 1,
            },
            v(4),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(3), v(4)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I32, Ty::I32]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("tuple memory round-trip executes");
        assert_eq!(
            int_signed(&outcome.returns[0]),
            1,
            "field 0 survives memory round-trip"
        );
        assert_eq!(
            int_signed(&outcome.returns[1]),
            2,
            "field 1 survives memory round-trip"
        );
    }

    // A nested tuple `(i8, (i32, i8))` round-trips through memory: the inner
    // tuple is laid out (and encoded/decoded) recursively, and the outer offset
    // math aligns the inner aggregate to its own alignment.
    #[test]
    fn nested_tuple_round_trips_through_memory() {
        let inner_ty = Ty::Tuple(vec![Ty::I32, Ty::I8]); // size 8, align 4
        let outer_ty = Ty::Tuple(vec![Ty::I8, inner_ty.clone()]); // i8@0, inner@4, size 12, align 4

        // Sanity-check the layout the round-trip relies on.
        let interp = Interpreter::new();
        assert_eq!(interp.byte_align(&outer_ty, b(0)).expect("align"), 4);
        assert_eq!(interp.byte_size(&outer_ty, b(0)).expect("size"), 12);
        let outer_layout = interp.tuple_layout(&outer_ty, b(0)).expect("layout");
        assert_eq!(outer_layout.field_offsets[0].0, 0, "i8 at 0");
        assert_eq!(
            outer_layout.field_offsets[1].0, 4,
            "inner tuple aligned to 4"
        );

        let mut function = Function::new(
            FuncId::new(0),
            "nested_tuple_mem",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: outer_ty.clone(),
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: outer_ty.clone(),
                value: Constant::Aggregate(vec![
                    Constant::Int(9),
                    Constant::Aggregate(vec![Constant::Int(42), Constant::Int(7)]),
                ]),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: outer_ty.clone(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: outer_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(2),
        ));
        // outer.0 (i8)
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I8,
                aggregate: v(2),
                field: 0,
            },
            v(3),
        ));
        // outer.1 (inner tuple), then inner.0 and inner.1
        block.body.push(result(
            Inst::ExtractField {
                ty: inner_ty.clone(),
                aggregate: v(2),
                field: 1,
            },
            v(4),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(4),
                field: 0,
            },
            v(5),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I8,
                aggregate: v(4),
                field: 1,
            },
            v(6),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(3), v(5), v(6)],
        }));
        function.blocks.push(block);

        let module = module_with_function(function, vec![Ty::I8, Ty::I32, Ty::I8]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("nested tuple memory round-trip executes");
        assert_eq!(int_signed(&outcome.returns[0]), 9, "outer i8 survives");
        assert_eq!(int_signed(&outcome.returns[1]), 42, "inner i32 survives");
        assert_eq!(int_signed(&outcome.returns[2]), 7, "inner i8 survives");
    }

    // Fail-closed: a tuple containing a field type with no byte layout
    // (`Ty::Never`) must not produce a (wrong) size — `byte_size` errors before
    // any offset is committed, never returning a bogus layout.
    #[test]
    fn tuple_with_unlayoutable_field_fails_closed() {
        let interp = Interpreter::new();
        let bad = Ty::Tuple(vec![Ty::I32, Ty::Never]);
        assert!(
            interp.byte_size(&bad, b(0)).is_err(),
            "a tuple with an unlayoutable field must not produce a size"
        );
        assert!(
            interp.byte_align(&bad, b(0)).is_err(),
            "a tuple with an unlayoutable field must not produce an alignment"
        );
        assert!(
            interp.tuple_layout(&bad, b(0)).is_err(),
            "a tuple with an unlayoutable field must not produce a layout"
        );
    }

    // --- roadmap §1.5 (second half): struct-typed aggregate constants ---

    /// Module with `struct.0 = Mixed { a: i8, b: i32 }` and one nullary
    /// function returning `returns`.
    fn struct_const_module(returns: Vec<Ty>) -> Module {
        use crate::ty::{FieldDef, StructDef};
        use crate::value::StructId;

        let mut module = Module::new("struct-const-test");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Mixed".into(),
            fields: vec![
                FieldDef {
                    name: "a".into(),
                    ty: Ty::I8,
                    offset: None,
                },
                FieldDef {
                    name: "b".into(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        module.add_func_type(FuncTy {
            params: Vec::new(),
            returns,
            is_vararg: false,
        });
        module
    }

    // A struct-typed `Constant::Aggregate` resolves its field types from the
    // module `StructDef` and interprets to the same in-register `Aggregate`
    // value `InsertField` would build: fields extract back positionally.
    #[test]
    fn struct_aggregate_constant_interprets_by_struct_def() {
        let struct_ty = Ty::Struct(crate::value::StructId::new(0));
        let mut function = Function::new(
            FuncId::new(0),
            "struct_const",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // %0 = const struct.0 { 7, 1000 }
        block.body.push(result(
            Inst::Const {
                ty: struct_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(7), Constant::Int(1000)]),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I8,
                aggregate: v(0),
                field: 0,
            },
            v(1),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(0),
                field: 1,
            },
            v(2),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(1), v(2)],
        }));
        function.blocks.push(block);

        let mut module = struct_const_module(vec![Ty::I8, Ty::I32]);
        module.add_function(function);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("struct constant executes");
        assert_eq!(
            int_signed(&outcome.returns[0]),
            7,
            "field a (i8) via StructDef"
        );
        assert_eq!(
            int_signed(&outcome.returns[1]),
            1000,
            "field b (i32) via StructDef"
        );
    }

    // A nested struct constant (`Outer { inner: Inner { x }, y }`) converts
    // recursively AND round-trips through memory (Alloca/Store/Load) — the
    // constant path composes with the aggregates-in-memory layout work.
    #[test]
    fn nested_struct_aggregate_constant_round_trips_through_memory() {
        use crate::ty::{FieldDef, StructDef};
        use crate::value::StructId;

        let inner_id = StructId::new(0);
        let outer_id = StructId::new(1);
        let inner_ty = Ty::Struct(inner_id);
        let outer_ty = Ty::Struct(outer_id);

        let mut module = Module::new("nested-struct-const");
        module.add_struct(StructDef {
            id: inner_id,
            name: "Inner".into(),
            fields: vec![FieldDef {
                name: "x".into(),
                ty: Ty::I32,
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
        });
        module.add_struct(StructDef {
            id: outer_id,
            name: "Outer".into(),
            fields: vec![
                FieldDef {
                    name: "inner".into(),
                    ty: inner_ty.clone(),
                    offset: None,
                },
                FieldDef {
                    name: "y".into(),
                    ty: Ty::I8,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32, Ty::I8],
            is_vararg: false,
        });

        let mut function = Function::new(
            FuncId::new(0),
            "nested_struct_const",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // %0 = alloca struct.1
        block.body.push(result(
            Inst::Alloca {
                ty: outer_ty.clone(),
                count: None,
                align: None,
            },
            v(0),
        ));
        // %1 = const struct.1 { { 42 }, 9 }
        block.body.push(result(
            Inst::Const {
                ty: outer_ty.clone(),
                value: Constant::Aggregate(vec![
                    Constant::Aggregate(vec![Constant::Int(42)]),
                    Constant::Int(9),
                ]),
            },
            v(1),
        ));
        // Whole-struct store + load (exercises encode/decode of the value the
        // constant path produced).
        block.body.push(void(Inst::Store {
            ty: outer_ty.clone(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: outer_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(2),
        ));
        // outer.inner.x and outer.y
        block.body.push(result(
            Inst::ExtractField {
                ty: inner_ty.clone(),
                aggregate: v(2),
                field: 0,
            },
            v(3),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(3),
                field: 0,
            },
            v(4),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I8,
                aggregate: v(2),
                field: 1,
            },
            v(5),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(4), v(5)],
        }));
        function.blocks.push(block);
        module.add_function(function);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("nested struct constant executes and round-trips memory");
        assert_eq!(int_signed(&outcome.returns[0]), 42, "inner.x survives");
        assert_eq!(int_signed(&outcome.returns[1]), 9, "outer.y survives");
    }

    /// Negative-control scaffold: run one `Const` instruction of type
    /// `struct.0` with `value` and return the resulting error.
    fn struct_const_error(value: Constant) -> InterpretError {
        let struct_ty = Ty::Struct(crate::value::StructId::new(0));
        let mut function = Function::new(
            FuncId::new(0),
            "bad_struct_const",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: struct_ty,
                value,
            },
            v(0),
        ));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        let mut module = struct_const_module(vec![]);
        module.add_function(function);
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("mismatched struct constant must not interpret")
    }

    // Negative controls: arity and per-field type mismatches fail closed with
    // a TypeError — never a silently mis-typed value.
    #[test]
    fn struct_aggregate_constant_mismatches_fail_closed() {
        // Arity: one field constant for a two-field struct.
        let arity = struct_const_error(Constant::Aggregate(vec![Constant::Int(7)]));
        assert_eq!(arity.code, InterpretErrorCode::TypeError);

        // Field type: bool constant where field 0 is i8.
        let field_ty = struct_const_error(Constant::Aggregate(vec![
            Constant::Bool(true),
            Constant::Int(3),
        ]));
        assert_eq!(field_ty.code, InterpretErrorCode::TypeError);

        // Unknown struct id: constant typed `struct.9` with no such def.
        let mut function = Function::new(
            FuncId::new(0),
            "unknown_struct",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::Struct(crate::value::StructId::new(9)),
                value: Constant::Aggregate(vec![]),
            },
            v(0),
        ));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        let mut module = struct_const_module(vec![]);
        module.add_function(function);
        let missing = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("unknown struct id must not interpret");
        assert_eq!(missing.code, InterpretErrorCode::TypeError);
    }

    // --- canonical enum layout: byte layout + memory round-trip ---

    /// Module with `enum.0 = OptionI32 { None, Some(i32) }` and one nullary
    /// function returning `returns`.
    fn option_enum_module(returns: Vec<Ty>) -> Module {
        use crate::ty::{EnumDef, EnumVariant};
        use crate::value::EnumId;

        let mut module = Module::new("enum-interp-test");
        module.add_enum(EnumDef::new(
            EnumId::new(0),
            "OptionI32",
            vec![
                EnumVariant {
                    name: "None".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Some".into(),
                    fields: vec![Ty::I32],
                    field_names: Vec::new(),
                },
            ],
        ));
        module.add_func_type(FuncTy {
            params: Vec::new(),
            returns,
            is_vararg: false,
        });
        module
    }

    // The canonical byte layout: tag u8 @0, i32 payload at its 4-byte-aligned
    // offset, total 8 bytes align 4 — agreeing with `Module::enum_layout_shape`
    // (bits) on every count.
    #[test]
    fn enum_byte_layout_matches_canonical_shape_layout() {
        let module = option_enum_module(vec![]);
        let enum_ty = Ty::Enum(crate::value::EnumId::new(0));
        let interp = Interpreter::with_module(&module);
        assert_eq!(interp.byte_size(&enum_ty, b(0)).expect("size"), 8);
        assert_eq!(interp.byte_align(&enum_ty, b(0)).expect("align"), 4);

        let shape_layout = module
            .enum_layout_shape(crate::value::EnumId::new(0))
            .expect("shape layout");
        assert_eq!(shape_layout.size_bits, 64);
        assert_eq!(shape_layout.align_bits, 32);
        assert_eq!(shape_layout.payload_offset_bits, 32);

        let rt_layout = interp.enum_layout(&enum_ty, b(0)).expect("rt layout");
        assert_eq!(rt_layout.size, 8);
        assert_eq!(rt_layout.align, 4);
        assert_eq!(rt_layout.payload_offset, 4);
        assert_eq!(rt_layout.tag_ty, Ty::U8);
        assert_eq!(rt_layout.discriminants, vec![0, 1]);
    }

    // The operational core: both variants of `Option<i32>` — payload-carrying
    // `Some(42)` and fieldless `None` — round-trip through
    // Alloca/Store/Load, and the tag extracts positionally as field 0.
    #[test]
    fn enum_constant_store_load_round_trips_both_variants() {
        let enum_ty = Ty::Enum(crate::value::EnumId::new(0));

        // Variant Some (tag 1, payload 42): store + load, extract tag+payload.
        let mut function =
            Function::new(FuncId::new(0), "enum_some", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: enum_ty.clone(),
                count: None,
                align: None,
            },
            v(0),
        ));
        // %1 = const enum.0 { 1, 42 }   (tag + payload convention)
        block.body.push(result(
            Inst::Const {
                ty: enum_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(42)]),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: enum_ty.clone(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: enum_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(2),
        ));
        // tag (field 0, u8) and payload (field 1, i32)
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::U8,
                aggregate: v(2),
                field: 0,
            },
            v(3),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(2),
                field: 1,
            },
            v(4),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(3), v(4)],
        }));
        function.blocks.push(block);
        let mut module = option_enum_module(vec![Ty::U8, Ty::I32]);
        module.add_function(function);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("Some round-trips through memory");
        assert_eq!(int_unsigned(&outcome.returns[0]), 1, "tag survives");
        assert_eq!(int_signed(&outcome.returns[1]), 42, "payload survives");

        // Variant None (tag 0, no payload).
        let mut function =
            Function::new(FuncId::new(0), "enum_none", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: enum_ty.clone(),
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: enum_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(0)]),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: enum_ty.clone(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: enum_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(2),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::U8,
                aggregate: v(2),
                field: 0,
            },
            v(3),
        ));
        block.body.push(void(Inst::Return { values: vec![v(3)] }));
        function.blocks.push(block);
        let mut module = option_enum_module(vec![Ty::U8]);
        module.add_function(function);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("None round-trips through memory");
        assert_eq!(int_unsigned(&outcome.returns[0]), 0, "None tag survives");
    }

    #[test]
    fn enum_descriptors_drive_direct_and_niche_byte_funnels() {
        use crate::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant};
        use crate::value::EnumId;

        let state = ExecState {
            values: BTreeMap::new(),
            memory: MemoryState::default(),
            globals: BTreeMap::new(),
            frames: BTreeMap::new(),
            next_frame_id: 0,
            steps: 0,
            remaining_fuel: u64::MAX,
        };
        let enum_ty = Ty::Enum(crate::value::EnumId::new(0));

        let mut direct_module = option_enum_module(vec![]);
        direct_module.enums[0].layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 8 },
            size: 12,
            align: 4,
            variant_field_offsets: vec![vec![], vec![0]],
        });
        let direct_value = InterpretValue {
            ty: enum_ty.clone(),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::U8, 1).expect("tag"),
                InterpretValue::int(Ty::I32, 42).expect("payload"),
            ]),
        };
        let direct = Interpreter::with_module(&direct_module);
        let bytes = direct
            .encode_value(&direct_value, &state, b(0))
            .expect("direct encode");
        assert_eq!(&bytes[..4], &42i32.to_le_bytes());
        assert_eq!(bytes[8], 1);
        assert_eq!(
            direct
                .decode_value(&enum_ty, &bytes, &state, b(0))
                .expect("direct decode"),
            direct_value
        );

        let mut niche_module = option_enum_module(vec![]);
        niche_module.enums[0].layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 1000,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U32,
            },
            size: 4,
            align: 4,
            variant_field_offsets: vec![vec![], vec![0]],
        });
        let niche_value = InterpretValue {
            ty: enum_ty.clone(),
            kind: InterpretValueKind::Aggregate(vec![InterpretValue::int(Ty::U8, 0).expect("tag")]),
        };
        let niche = Interpreter::with_module(&niche_module);
        let bytes = niche
            .encode_value(&niche_value, &state, b(0))
            .expect("niche encode");
        assert_eq!(bytes.as_slice(), &1000u32.to_le_bytes());
        assert_eq!(
            niche
                .decode_value(&enum_ty, &bytes, &state, b(0))
                .expect("niche decode"),
            niche_value
        );
        let shape = niche_module
            .enum_layout_shape(crate::value::EnumId::new(0))
            .expect("descriptor shape");
        assert_eq!((shape.size_bits, shape.align_bits), (32, 32));
        assert!(shape.descriptor.is_some());

        let mut wrapped_module = Module::new("wrapped-niche");
        let mut wrapped_def = EnumDef::new(
            EnumId::new(0),
            "Wrapped",
            vec![
                EnumVariant {
                    name: "Low".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Data".into(),
                    fields: vec![Ty::U8],
                    field_names: vec!["data".into()],
                },
                EnumVariant {
                    name: "High".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
        );
        wrapped_def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 2,
                niche_start: 254,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U8,
            },
            size: 1,
            align: 1,
            variant_field_offsets: vec![vec![], vec![0], vec![]],
        });
        wrapped_module.add_enum(wrapped_def);
        let wrapped_ty = Ty::Enum(EnumId::new(0));
        wrapped_module
            .enum_layout_shape(EnumId::new(0))
            .expect("wrapped niche descriptor shape");
        let wrapped = Interpreter::with_module(&wrapped_module);
        let values = [
            (
                InterpretValue {
                    ty: wrapped_ty.clone(),
                    kind: InterpretValueKind::Aggregate(vec![
                        InterpretValue::int(Ty::U8, 0).expect("low tag"),
                    ]),
                },
                254,
            ),
            (
                InterpretValue {
                    ty: wrapped_ty.clone(),
                    kind: InterpretValueKind::Aggregate(vec![
                        InterpretValue::int(Ty::U8, 1).expect("data tag"),
                        InterpretValue::int(Ty::U8, 42).expect("data payload"),
                    ]),
                },
                42,
            ),
            (
                InterpretValue {
                    ty: wrapped_ty.clone(),
                    kind: InterpretValueKind::Aggregate(vec![
                        InterpretValue::int(Ty::U8, 2).expect("high tag"),
                    ]),
                },
                0,
            ),
        ];
        for (value, expected_byte) in values {
            let bytes = wrapped
                .encode_value(&value, &state, b(0))
                .expect("wrapped niche encode");
            assert_eq!(bytes.as_slice(), &[expected_byte]);
            assert_eq!(
                wrapped
                    .decode_value(&wrapped_ty, &bytes, &state, b(0))
                    .expect("wrapped niche decode"),
                value
            );
        }
        for reserved_payload in [254, 255, 0] {
            let invalid_untagged = InterpretValue {
                ty: wrapped_ty.clone(),
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(Ty::U8, 1).expect("data tag"),
                    InterpretValue::int(Ty::U8, reserved_payload).expect("data payload"),
                ]),
            };
            assert_eq!(
                wrapped
                    .encode_value(&invalid_untagged, &state, b(0))
                    .expect_err("untagged payload must not occupy a reserved niche")
                    .code,
                InterpretErrorCode::TypeError
            );
        }
        assert_eq!(
            wrapped
                .decode_value(&wrapped_ty, &[255], &state, b(0))
                .expect_err("the untagged variant's dead niche byte must be rejected")
                .code,
            InterpretErrorCode::TypeError
        );

        let mut misaligned_field = direct_module.clone();
        let descriptor = misaligned_field.enums[0].layout.as_mut().unwrap();
        descriptor.variant_field_offsets[1][0] = 2;
        assert!(misaligned_field.enum_layout_shape(EnumId::new(0)).is_err());
        assert!(
            Interpreter::with_module(&misaligned_field)
                .enum_layout(&enum_ty, b(0))
                .is_err(),
            "the interpreter must reject a descriptor with a misaligned field"
        );

        let mut underaligned = direct_module.clone();
        underaligned.enums[0].layout.as_mut().unwrap().align = 2;
        assert!(underaligned.enum_layout_shape(EnumId::new(0)).is_err());
        assert!(
            Interpreter::with_module(&underaligned)
                .enum_layout(&enum_ty, b(0))
                .is_err(),
            "the interpreter must reject an under-aligned descriptor"
        );

        let mut misaligned_tag = direct_module.clone();
        misaligned_tag.enums[0].repr = Some(EnumTagRepr::U32);
        let descriptor = misaligned_tag.enums[0].layout.as_mut().unwrap();
        descriptor.encoding = EnumTagEncoding::Direct { tag_offset: 2 };
        descriptor.variant_field_offsets[1][0] = 8;
        assert!(misaligned_tag.enum_layout_shape(EnumId::new(0)).is_err());
        assert!(
            Interpreter::with_module(&misaligned_tag)
                .enum_layout(&enum_ty, b(0))
                .is_err(),
            "the interpreter must reject a misaligned direct tag lane"
        );

        let mut underaligned_niche = niche_module;
        underaligned_niche.enums[0].layout.as_mut().unwrap().align = 2;
        assert!(
            underaligned_niche
                .enum_layout_shape(EnumId::new(0))
                .is_err()
        );
        assert!(
            Interpreter::with_module(&underaligned_niche)
                .enum_layout(&enum_ty, b(0))
                .is_err(),
            "niche lane alignment must agree across the interpreter and shape API"
        );
    }

    /// v37: an `Untagged` descriptor is the byte image WITHOUT a tag lane —
    /// the shape rustc gives a single-inhabited-variant `repr(Rust)` enum
    /// (`enum UnOp { Not(Vec<()>) }` IS its 24-byte payload). The tag survives
    /// in the VALUE and is recovered on decode from the sole variant, so the
    /// round trip is total even though nothing about it is stored.
    ///
    /// The contrast that motivates the encoding is asserted directly: the same
    /// def WITHOUT a descriptor gets the canonical tagged-union layout, which
    /// budgets a tag and is therefore strictly larger. That canonical layout is
    /// not wrong — it is trust-ir's own, deliberately not a rustc model — which
    /// is exactly why a rustc-derived producer has to say `Untagged` instead of
    /// declining to describe the def.
    #[test]
    fn untagged_descriptor_is_the_payload_alone() {
        use crate::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumVariant};
        use crate::value::EnumId;

        let state = ExecState {
            values: BTreeMap::new(),
            memory: MemoryState::default(),
            globals: BTreeMap::new(),
            frames: BTreeMap::new(),
            next_frame_id: 0,
            steps: 0,
            remaining_fuel: u64::MAX,
        };
        let build = |layout: Option<EnumLayoutDescriptor>| {
            let mut module = Module::new("untagged");
            let mut def = EnumDef::new(
                EnumId::new(0),
                "UnOp",
                vec![EnumVariant {
                    name: "Not".into(),
                    fields: vec![Ty::U64],
                    field_names: vec!["operand".into()],
                }],
            );
            def.layout = layout;
            module.add_enum(def);
            module
        };
        let enum_ty = Ty::Enum(EnumId::new(0));
        let value = InterpretValue {
            ty: enum_ty.clone(),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::U8, 0).expect("tag"),
                InterpretValue::int(Ty::U64, 0x0102_0304_0506_0708).expect("payload"),
            ]),
        };

        let module = build(Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![0]],
        }));
        let shape = module
            .enum_layout_shape(EnumId::new(0))
            .expect("untagged descriptor shape");
        assert_eq!((shape.size_bits, shape.align_bits), (64, 64));
        let interp = Interpreter::with_module(&module);
        let bytes = interp
            .encode_value(&value, &state, b(0))
            .expect("untagged encode");
        assert_eq!(
            bytes.as_slice(),
            &0x0102_0304_0506_0708u64.to_le_bytes(),
            "the image is the payload alone — no tag byte anywhere"
        );
        assert_eq!(
            interp
                .decode_value(&enum_ty, &bytes, &state, b(0))
                .expect("untagged decode"),
            value,
            "the tag is synthesized from the sole variant, not read"
        );

        // Every 8-byte image decodes: unlike a tagged encoding there is no bit
        // pattern that could name a variant this enum does not have.
        for image in [[0u8; 8], [0xff; 8]] {
            interp
                .decode_value(&enum_ty, &image, &state, b(0))
                .expect("an untagged image cannot be mis-tagged");
        }

        // Same def, no descriptor: the canonical layout budgets a tag, so it is
        // BIGGER. This is the disagreement that made `Option<UnOp>` fail to
        // validate before the encoding existed.
        let canonical = build(None);
        let canonical_shape = canonical
            .enum_layout_shape(EnumId::new(0))
            .expect("canonical shape");
        assert!(
            canonical_shape.size_bits > shape.size_bits,
            "canonical {} must exceed untagged {} — it stores a tag",
            canonical_shape.size_bits,
            shape.size_bits
        );

        // Fail closed on the one claim that has content: nothing in the image
        // discriminates, so more than one variant is undiscriminable. The
        // shape API and the interpreter must agree.
        let mut multi = build(Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![0], vec![]],
        }));
        multi.enums[0].variants.push(EnumVariant {
            name: "Nop".into(),
            fields: vec![],
            field_names: Vec::new(),
        });
        assert!(multi.enum_layout_shape(EnumId::new(0)).is_err());
        let multi_interp = Interpreter::with_module(&multi);
        assert_eq!(
            multi_interp
                .enum_layout(&enum_ty, b(0))
                .err()
                .expect("a multi-variant untagged descriptor is undiscriminable")
                .code,
            InterpretErrorCode::TypeError
        );
    }

    /// B3/E6 0a: an ENUM-TYPED PARAM binds at function entry and executes —
    /// the exact call path the differential's per-side sample construction
    /// relies on (`execute_func` -> `check_function_args` ->
    /// `check_signature_values` -> `bind_block_params`). The def uses
    /// `#[repr(i16)] { Neg = -5, Pos = 7 }`-style EXPLICIT discriminants so a
    /// variant-INDEX-valued tag could never pass silently: the body returns
    /// the tag lane, and the assertion pins the EFFECTIVE value.
    #[test]
    fn enum_param_execute_func_entry_binding() {
        use crate::ty::{EnumDef, EnumTagRepr, EnumVariant};
        use crate::value::EnumId;

        let mut module = Module::new("e6");
        module.add_enum(
            EnumDef::new(
                EnumId::new(0),
                "Tagged",
                vec![
                    EnumVariant {
                        name: "Neg".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "Pos".into(),
                        fields: vec![Ty::I32],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(-5), Some(7)])
            .with_repr(EnumTagRepr::I16),
        );
        let enum_ty = Ty::Enum(EnumId::new(0));
        module.add_func_type(FuncTy {
            params: vec![enum_ty.clone()],
            returns: vec![Ty::I16],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "read_tag", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), enum_ty.clone()));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I16,
                aggregate: v(0),
                field: 0,
            },
            v(1),
        ));
        block.body.push(void(Inst::Return { values: vec![v(1)] }));
        function.blocks.push(block);
        module.add_function(function);

        // Fieldless variant: Aggregate([tag]) only.
        let neg = InterpretValue {
            ty: enum_ty.clone(),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::I16, -5).expect("i16 tag"),
            ]),
        };
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [neg])
            .expect("fieldless enum param binds and executes");
        assert_eq!(
            int_signed(&outcome.returns[0]),
            -5,
            "EFFECTIVE disc, not index 0"
        );

        // Payload variant: Aggregate([tag, field]).
        let pos = InterpretValue {
            ty: enum_ty.clone(),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::I16, 7).expect("i16 tag"),
                InterpretValue::int(Ty::I32, 42).expect("i32 payload"),
            ]),
        };
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [pos])
            .expect("payload enum param binds and executes");
        assert_eq!(
            int_signed(&outcome.returns[0]),
            7,
            "EFFECTIVE disc, not index 1"
        );
    }

    /// B3/E6 0b (negative): a value typed at the WRONG module-local EnumId is a
    /// SignatureMismatch at entry — raw-id Ty equality is the check, which is
    /// exactly why the differential must construct samples PER SIDE.
    #[test]
    fn enum_param_wrong_module_id_signature_mismatch() {
        use crate::ty::{EnumDef, EnumVariant};
        use crate::value::EnumId;

        let mut module = Module::new("e6b");
        for (i, name) in [(0u32, "A"), (1u32, "B")] {
            module.add_enum(EnumDef::new(
                EnumId::new(i),
                name,
                vec![EnumVariant {
                    name: "V".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                }],
            ));
        }
        module.add_func_type(FuncTy {
            params: vec![Ty::Enum(EnumId::new(0))],
            returns: vec![],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "takes_a", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Enum(EnumId::new(0))));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.add_function(function);

        let wrong = InterpretValue {
            ty: Ty::Enum(EnumId::new(1)),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::U8, 0).expect("u8 tag"),
            ]),
        };
        let err = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [wrong])
            .expect_err("wrong module-local enum id must not bind");
        assert_eq!(err.code, InterpretErrorCode::SignatureMismatch);
    }

    /// B3/E6 0c (probe): entry binding does NOT validate the Aggregate against
    /// the EnumDef — an index-valued/mistyped tag flows to first use and traps
    /// there. Documents that the differential's obligation to sample only
    /// EnumDef-VALID values is real, not enforced for it by the interpreter.
    #[test]
    fn enum_param_malformed_tag_traps_at_first_use_not_entry() {
        use crate::ty::{EnumDef, EnumTagRepr, EnumVariant};
        use crate::value::EnumId;

        let mut module = Module::new("e6c");
        module.add_enum(
            EnumDef::new(
                EnumId::new(0),
                "Tagged",
                vec![
                    EnumVariant {
                        name: "Neg".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "Pos".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(-5), Some(7)])
            .with_repr(EnumTagRepr::I16),
        );
        let enum_ty = Ty::Enum(EnumId::new(0));
        module.add_func_type(FuncTy {
            params: vec![enum_ty.clone()],
            returns: vec![],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "store_it", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), enum_ty.clone()));
        block.body.push(result(
            Inst::Alloca {
                ty: enum_ty.clone(),
                count: None,
                align: None,
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: enum_ty.clone(),
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: None,
        }));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.add_function(function);

        // Tag = 1 (a variant INDEX; neither -5 nor 7 — no variant has disc 1).
        let malformed = InterpretValue {
            ty: enum_ty.clone(),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::I16, 1).expect("i16 tag"),
            ]),
        };
        let err = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [malformed])
            .expect_err("index-valued tag must trap at the Store variant re-check");
        assert_eq!(err.code, InterpretErrorCode::TypeError);
        assert_eq!(
            err.message, "Store: tag 1 does not name a variant of enum.0",
            "the malformed value must pass entry binding and fail at the Store tag check"
        );
    }

    /// B3-1b T1: the PRODUCER-CONVENTION construct — a zero-seeded
    /// `Constant::Aggregate([Int(disc), seeds])` overwritten by positional
    /// `InsertField` at `1 + i` — round-trips through MEMORY and re-projects
    /// both lanes. This is the exact instruction sequence the oracle bridge's
    /// first-class enum construction arm emits (mirroring
    /// `lower_enum_construct_general`), so the memory path it takes must be
    /// pinned by test before any body relies on it.
    #[test]
    fn enum_producer_convention_construct_memory_round_trip() {
        let enum_ty = Ty::Enum(crate::value::EnumId::new(0));
        let mut function =
            Function::new(FuncId::new(0), "enum_ctor", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        // %0 = const enum.0 { 1, 0 }   (Some, zero seed)
        block.body.push(result(
            Inst::Const {
                ty: enum_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0)]),
            },
            v(0),
        ));
        // %1 = const i32 42 ; %2 = insertfield %0[1] <- %1
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::InsertField {
                ty: enum_ty.clone(),
                aggregate: v(0),
                field: 1,
                value: v(1),
            },
            v(2),
        ));
        // memory round-trip
        block.body.push(result(
            Inst::Alloca {
                ty: enum_ty.clone(),
                count: None,
                align: None,
            },
            v(3),
        ));
        block.body.push(void(Inst::Store {
            ty: enum_ty.clone(),
            ptr: v(3),
            value: v(2),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: enum_ty.clone(),
                ptr: v(3),
                volatile: false,
                align: None,
            },
            v(4),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::U8,
                aggregate: v(4),
                field: 0,
            },
            v(5),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(4),
                field: 1,
            },
            v(6),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(5), v(6)],
        }));
        function.blocks.push(block);
        let mut module = option_enum_module(vec![Ty::U8, Ty::I32]);
        module.add_function(function);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("producer-convention construct round-trips");
        assert_eq!(int_unsigned(&outcome.returns[0]), 1, "tag survives");
        assert_eq!(
            int_signed(&outcome.returns[1]),
            42,
            "inserted payload survives"
        );
    }

    /// B3-1b T2 (negative): `InsertField{field: 0}` rewriting the TAG to a
    /// variant of DIFFERENT arity has no interpreter-side validation at the
    /// insert itself — the corruption is caught at the next whole-enum Store's
    /// variant/arity re-check. Documents WHY the bridge's SetDiscriminant arm
    /// is whole-value-only (a tag-only rewrite leaving stale payload lanes is
    /// exactly this failure).
    #[test]
    fn enum_tag_only_rewrite_fails_at_store_arity_check() {
        let enum_ty = Ty::Enum(crate::value::EnumId::new(0));
        let mut function = Function::new(
            FuncId::new(0),
            "enum_bad_tag",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        // Some(42): [1, 42]
        block.body.push(result(
            Inst::Const {
                ty: enum_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(42)]),
            },
            v(0),
        ));
        // tag-only rewrite to None (arity 0) — leaves the stale payload lane
        block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0),
            },
            v(1),
        ));
        block.body.push(result(
            Inst::InsertField {
                ty: enum_ty.clone(),
                aggregate: v(0),
                field: 0,
                value: v(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: enum_ty.clone(),
                count: None,
                align: None,
            },
            v(3),
        ));
        block.body.push(void(Inst::Store {
            ty: enum_ty.clone(),
            ptr: v(3),
            value: v(2),
            volatile: false,
            align: None,
        }));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        let mut module = option_enum_module(vec![]);
        module.add_function(function);
        let err = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("tag/arity-inconsistent enum value must fail at Store");
        let msg = format!("{err:?}");
        assert!(
            msg.contains("payload") || msg.contains("arity") || msg.contains("variant"),
            "failure names the variant/arity check: {msg}"
        );
    }

    // Explicit discriminants drive the tag VALUE (not the variant index): an
    // enum `{ A = 10, B }` constant tagged 11 selects B and round-trips with
    // tag value 11 in a u8 lane.
    #[test]
    fn enum_explicit_discriminants_tag_by_value_not_index() {
        use crate::ty::{EnumDef, EnumVariant};
        use crate::value::EnumId;

        let mut module = Module::new("enum-disc-test");
        module.add_enum(
            EnumDef::new(
                EnumId::new(0),
                "Sparse",
                vec![
                    EnumVariant {
                        name: "A".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "B".into(),
                        fields: vec![Ty::I8],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(10)]),
        );
        module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::U8, Ty::I8],
            is_vararg: false,
        });

        let enum_ty = Ty::Enum(EnumId::new(0));
        let mut function =
            Function::new(FuncId::new(0), "sparse_enum", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: enum_ty.clone(),
                count: None,
                align: None,
            },
            v(0),
        ));
        // B's effective discriminant is 11 (10 + 1).
        block.body.push(result(
            Inst::Const {
                ty: enum_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(11), Constant::Int(-3)]),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: enum_ty.clone(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: enum_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(2),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::U8,
                aggregate: v(2),
                field: 0,
            },
            v(3),
        ));
        block.body.push(result(
            Inst::ExtractField {
                ty: Ty::I8,
                aggregate: v(2),
                field: 1,
            },
            v(4),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(3), v(4)],
        }));
        function.blocks.push(block);
        module.add_function(function);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("sparse-discriminant enum round-trips");
        assert_eq!(int_unsigned(&outcome.returns[0]), 11, "tag is the VALUE 11");
        assert_eq!(int_signed(&outcome.returns[1]), -3, "payload survives");
    }

    /// Negative-control scaffold: run one enum-typed `Const` and return the
    /// resulting error.
    fn enum_const_error(value: Constant) -> InterpretError {
        let enum_ty = Ty::Enum(crate::value::EnumId::new(0));
        let mut function = Function::new(
            FuncId::new(0),
            "bad_enum_const",
            crate::FuncTyId::new(0),
            b(0),
        );
        let mut block = Block::new(b(0));
        block
            .body
            .push(result(Inst::Const { ty: enum_ty, value }, v(0)));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        let mut module = option_enum_module(vec![]);
        module.add_function(function);
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("mismatched enum constant must not interpret")
    }

    // Negative controls: an unknown discriminant, a payload-arity mismatch, a
    // missing tag, and a corrupted in-memory tag all fail closed.
    #[test]
    fn enum_mismatches_fail_closed() {
        // Discriminant 7 names no variant of Option<i32> (tags 0, 1).
        let unknown = enum_const_error(Constant::Aggregate(vec![Constant::Int(7)]));
        assert_eq!(unknown.code, InterpretErrorCode::TypeError);

        // Variant None (tag 0) takes no payload.
        let arity = enum_const_error(Constant::Aggregate(vec![
            Constant::Int(0),
            Constant::Int(1),
        ]));
        assert_eq!(arity.code, InterpretErrorCode::TypeError);

        // An empty aggregate has no tag lane.
        let empty = enum_const_error(Constant::Aggregate(vec![]));
        assert_eq!(empty.code, InterpretErrorCode::TypeError);

        // A non-integer tag element.
        let bad_tag = enum_const_error(Constant::Aggregate(vec![Constant::Bool(true)]));
        assert_eq!(bad_tag.code, InterpretErrorCode::TypeError);

        // Corrupted memory image: store Some(42), overwrite the tag byte with
        // 9 (no variant), then whole-enum Load must refuse to decode.
        let enum_ty = Ty::Enum(crate::value::EnumId::new(0));
        let mut function =
            Function::new(FuncId::new(0), "corrupt_tag", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Alloca {
                ty: enum_ty.clone(),
                count: None,
                align: None,
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Const {
                ty: enum_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(42)]),
            },
            v(1),
        ));
        block.body.push(void(Inst::Store {
            ty: enum_ty.clone(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        // Overwrite the tag byte (offset 0) with 9.
        block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(9),
            },
            v(2),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::U8,
            ptr: v(0),
            value: v(2),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: enum_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(3),
        ));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        let mut module = option_enum_module(vec![]);
        module.add_function(function);
        let corrupted = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("a tag matching no discriminant must not decode");
        assert_eq!(corrupted.code, InterpretErrorCode::TypeError);
    }

    // Fail-closed layout controls: uninhabited enums and unresolvable
    // discriminant assignments have no byte layout.
    #[test]
    fn enum_without_canonical_layout_fails_closed() {
        use crate::ty::{EnumDef, EnumVariant};
        use crate::value::EnumId;

        let mut module = Module::new("bad-enums");
        module.add_enum(EnumDef::new(EnumId::new(0), "Uninhabited", vec![]));
        module.add_enum(
            EnumDef::new(
                EnumId::new(1),
                "Dup",
                vec![
                    EnumVariant {
                        name: "A".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "B".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(3), Some(3)]),
        );
        let interp = Interpreter::with_module(&module);
        assert!(
            interp.byte_size(&Ty::Enum(EnumId::new(0)), b(0)).is_err(),
            "uninhabited enums have no byte layout"
        );
        assert!(
            interp.byte_size(&Ty::Enum(EnumId::new(1)), b(0)).is_err(),
            "duplicate discriminants have no canonical layout"
        );
        // A module-less interpreter cannot lay out enums at all.
        assert!(
            Interpreter::new()
                .byte_size(&Ty::Enum(EnumId::new(0)), b(0))
                .is_err(),
            "enum layout requires module type context"
        );
    }

    // -----------------------------------------------------------------
    // SeqMap (general element-op loop): Rust side of the Lean agreement
    // pins in lean/trust_ir-semantics/TrustIr/Semantics/ExecutableFixtures.lean
    // (the `seq_map_*` native_decide fixtures). Success values, the element
    // type-error case, and the depth cases must stay in lock-step with the
    // Lean SeqMapReq runner.
    // -----------------------------------------------------------------

    /// `incr_all(l: Seq<i32>) -> Seq<i32> { seq_map l, @incr_elem }` plus the
    /// single-&mut element function `incr_elem(x: &mut i32) { *x += 1 }`.
    fn seq_map_module() -> Module {
        let mut module = Module::new("seq-map");
        let i32_id = module.add_type(Ty::I32);
        let seq_ty = Ty::Sequence(i32_id);
        let loop_ty = module.add_func_type(FuncTy {
            params: vec![seq_ty.clone()],
            returns: vec![seq_ty.clone()],
            is_vararg: false,
        });
        let elem_fn_ty = module.add_func_type(FuncTy {
            params: vec![Ty::RefMut(Box::new(Ty::I32))],
            returns: vec![],
            is_vararg: false,
        });

        let mut incr_all = Function::new(FuncId::new(0), "incr_all", loop_ty, b(0));
        let mut entry = Block::new(b(0)).with_param(v(0), seq_ty.clone());
        entry.body.push(result(
            Inst::SeqMap {
                ty: seq_ty.clone(),
                seq: v(0),
                fwd: FuncId::new(1),
            },
            v(1),
        ));
        entry.body.push(void(Inst::Return { values: vec![v(1)] }));
        incr_all.blocks.push(entry);

        let mut incr_elem = Function::new(FuncId::new(1), "incr_elem", elem_fn_ty, b(0));
        let mut eb = Block::new(b(0)).with_param(v(0), Ty::RefMut(Box::new(Ty::I32)));
        eb.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(1),
        ));
        eb.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            },
            v(2),
        ));
        eb.body.push(result(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(1),
                rhs: v(2),
            },
            v(3),
        ));
        eb.body.push(void(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(3),
            volatile: false,
            align: None,
        }));
        eb.body.push(void(Inst::Return { values: vec![] }));
        incr_elem.blocks.push(eb);

        module.add_function(incr_all);
        module.add_function(incr_elem);
        module
    }

    fn i32_seq_value(seq_ty: Ty, elems: &[i128]) -> InterpretValue {
        InterpretValue {
            ty: seq_ty,
            kind: InterpretValueKind::Sequence(
                elems
                    .iter()
                    .map(|&n| InterpretValue::int(Ty::I32, n).expect("i32 element"))
                    .collect(),
            ),
        }
    }

    /// Lean pin `seq_map_incr_all_eval_stable`: 3 elements at max_call_depth 1
    /// SUCCEED — call depth bounds NESTING, not sequence length (the map is
    /// ONE call-depth level; per-element calls are sequential).
    #[test]
    fn seq_map_applies_element_function_at_depth_one() {
        let module = seq_map_module();
        let seq_ty = Ty::Sequence(TyId::new(0));
        let outcome = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                max_call_depth: 1,
                ..InterpretOptions::default()
            })
            .execute_func(FuncId::new(0), [i32_seq_value(seq_ty, &[1, 2, 3])])
            .expect("seq_map applies the element function to every element");

        let InterpretValueKind::Sequence(elems) = &outcome.returns[0].kind else {
            panic!(
                "seq_map must return a sequence, got {:?}",
                outcome.returns[0]
            );
        };
        let mapped: Vec<i128> = elems.iter().map(int_signed).collect();
        assert_eq!(mapped, vec![2, 3, 4]);
    }

    /// Lean pin `seq_map_empty_sequence_eval_stable`.
    #[test]
    fn seq_map_empty_sequence_maps_to_empty() {
        let module = seq_map_module();
        let seq_ty = Ty::Sequence(TyId::new(0));
        let outcome = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                max_call_depth: 1,
                ..InterpretOptions::default()
            })
            .execute_func(FuncId::new(0), [i32_seq_value(seq_ty, &[])])
            .expect("empty sequence maps to empty sequence");
        let InterpretValueKind::Sequence(elems) = &outcome.returns[0].kind else {
            panic!("seq_map must return a sequence");
        };
        assert!(elems.is_empty());
    }

    /// Lean pin `seq_map_element_type_error_code_stable`: a Bool element
    /// against `fn(&mut i32)` fails closed with a TYPE error.
    #[test]
    fn seq_map_element_type_mismatch_has_stable_code() {
        let module = seq_map_module();
        let seq_ty = Ty::Sequence(TyId::new(0));
        let bad_seq = InterpretValue {
            ty: seq_ty,
            kind: InterpretValueKind::Sequence(vec![
                InterpretValue::int(Ty::I32, 1).expect("i32 element"),
                InterpretValue::bool(true),
            ]),
        };
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [bad_seq])
            .expect_err("a bool element does not match fn(&mut i32)");
        assert_eq!(error.code, InterpretErrorCode::TypeError);
        assert_eq!(error.code.as_str(), "type_error");
    }

    /// Lean pin `seq_map_depth_limit_code_stable`: at max_call_depth 0 the
    /// whole map is out of depth before any element runs.
    #[test]
    fn seq_map_depth_zero_has_stable_code() {
        let module = seq_map_module();
        let seq_ty = Ty::Sequence(TyId::new(0));
        let error = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                max_call_depth: 0,
                ..InterpretOptions::default()
            })
            .execute_func(FuncId::new(0), [i32_seq_value(seq_ty, &[1])])
            .expect_err("seq_map costs one call-depth level");
        assert_eq!(error.code, InterpretErrorCode::OutOfFuel);
        assert_eq!(error.code.as_str(), "out_of_fuel");
    }

    /// Lean pin `seq_map_undefined_fwd_code_stable` (Rust surfaces the
    /// missing-function code where the Lean table lookup is a type error —
    /// the per-side stable-code convention used by Call).
    #[test]
    fn seq_map_undefined_fwd_has_stable_code() {
        let mut module = seq_map_module();
        // Point the SeqMap at a function id that does not exist.
        let Inst::SeqMap { fwd, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
            panic!("first body inst is the seq_map");
        };
        *fwd = FuncId::new(99);
        let seq_ty = Ty::Sequence(TyId::new(0));
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [i32_seq_value(seq_ty, &[1])])
            .expect_err("undefined element function");
        assert_eq!(error.code, InterpretErrorCode::MissingFunction);
    }

    /// Lean pin `seq_map_bad_fwd_signature_code_stable`: an element function
    /// that is not the single-&mut form `fn(&mut elem)` is rejected.
    #[test]
    fn seq_map_bad_fwd_signature_has_stable_code() {
        let mut module = Module::new("seq-map-bad-sig");
        let i32_id = module.add_type(Ty::I32);
        let seq_ty = Ty::Sequence(i32_id);
        let loop_ty = module.add_func_type(FuncTy {
            params: vec![seq_ty.clone()],
            returns: vec![seq_ty.clone()],
            is_vararg: false,
        });
        // By-value fn(i32) -> i32: NOT the &mut element form.
        let by_value_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut incr_all = Function::new(FuncId::new(0), "incr_all", loop_ty, b(0));
        let mut entry = Block::new(b(0)).with_param(v(0), seq_ty.clone());
        entry.body.push(result(
            Inst::SeqMap {
                ty: seq_ty.clone(),
                seq: v(0),
                fwd: FuncId::new(1),
            },
            v(1),
        ));
        entry.body.push(void(Inst::Return { values: vec![v(1)] }));
        incr_all.blocks.push(entry);

        let mut identity = Function::new(FuncId::new(1), "identity", by_value_ty, b(0));
        let mut ib = Block::new(b(0)).with_param(v(0), Ty::I32);
        ib.body.push(void(Inst::Return { values: vec![v(0)] }));
        identity.blocks.push(ib);

        module.add_function(incr_all);
        module.add_function(identity);

        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [i32_seq_value(Ty::Sequence(i32_id), &[1])])
            .expect_err("by-value element function is rejected");
        assert_eq!(error.code, InterpretErrorCode::TypeError);
    }

    /// Lean pin `seq_map_non_sequence_operand_code_stable`.
    #[test]
    fn seq_map_non_sequence_operand_has_stable_code() {
        let mut module = seq_map_module();
        // Rewire incr_all to take (and map) an i32 instead of a sequence.
        let i32_loop_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::Sequence(TyId::new(0))],
            is_vararg: false,
        });
        module.functions[0].ty = i32_loop_ty;
        module.functions[0].blocks[0].params[0].1 = Ty::I32;
        let error = Interpreter::with_module(&module)
            .execute_func(
                FuncId::new(0),
                [InterpretValue::int(Ty::I32, 7).expect("i32 arg")],
            )
            .expect_err("seq_map requires a sequence operand");
        assert_eq!(error.code, InterpretErrorCode::TypeError);
    }

    /// Build a one-block function that returns `const <ty> <value>`.
    fn returns_const(ty: Ty, value: Constant) -> Module {
        let mut function = Function::new(FuncId::new(0), "k", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: ty.clone(),
                value,
            },
            v(0),
        ));
        block.body.push(void(Inst::Return { values: vec![v(0)] }));
        function.blocks.push(block);
        module_with_function(function, vec![ty])
    }

    /// THE ACCEPT CONTROL. `shape_matches_ty` has admitted `(Constant::Int(_),
    /// Ty::Ptr)` since the initial commit, so this pairing was always
    /// encodable and validator-accepted — the interpreter simply had no arm
    /// and it died on the type-error path, which is a disagreement between two
    /// authorities about what inhabits `Ty::Ptr`. Without this control the two
    /// tests below would pass vacuously against an interpreter that still
    /// refuses every `Int` at `Ty::Ptr`.
    #[test]
    fn a_zero_int_constant_at_ptr_is_the_null_pointer() {
        let module = returns_const(Ty::Ptr, Constant::Int(0));
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("a null-pointer constant must execute");
        assert!(
            matches!(outcome.returns[0].kind, InterpretValueKind::NullPtr),
            "expected NullPtr, got {:?}",
            outcome.returns[0].kind,
        );
        assert_eq!(outcome.returns[0].ty, Ty::Ptr);
    }

    /// ZERO ONLY, and this is the wall that makes the arm safe. A NONZERO
    /// integer at `Ty::Ptr` is a fabricated address with no allocation and no
    /// provenance behind it; admitting it would be exactly the silent
    /// wrongness the null case avoids by being loud. It stays fail-closed.
    #[test]
    fn a_nonzero_int_at_ptr_is_still_a_type_error() {
        for raw in [1_i128, -1, 8, 4096, i128::from(u32::MAX)] {
            let module = returns_const(Ty::Ptr, Constant::Int(raw));
            let error = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .expect_err("a nonzero address constant has no provenance and must fail closed");
            assert_eq!(
                error.code,
                InterpretErrorCode::TypeError,
                "raw {raw} must stay on the type-error path, got {error:?}",
            );
        }
    }

    /// THE SPLIT IS BY TYPE, NOT BY VALUE. `Constant::Int(0)` at an INTEGER
    /// type must still be an integer zero — the new arm sits after the
    /// `int_shape(ty).is_some()` guard and must not shadow it. `int_shape`
    /// answers `None` only for `Ty::Ptr`, and this pins that.
    #[test]
    fn a_zero_int_at_an_integer_ty_is_still_an_integer() {
        for ty in [Ty::I32, Ty::I64, Ty::U8, Ty::Usize, Ty::Isize] {
            let module = returns_const(ty.clone(), Constant::Int(0));
            let outcome = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .expect("an integer zero must execute");
            assert!(
                matches!(outcome.returns[0].kind, InterpretValueKind::Int(_)),
                "{ty:?} zero must stay an integer, got {:?}",
                outcome.returns[0].kind,
            );
        }
    }
}
