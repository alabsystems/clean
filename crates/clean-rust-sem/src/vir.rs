// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MIR-derived CFG IR for Rust Value Translation (VIR)
//!
//! This module defines a MIR-derived control-flow graph IR that captures
//! Rust value translation steps explicitly. The design mirrors rustc's MIR
//! at the control-flow granularity while remaining decoupled from rustc types.
//!
//! ## Design Goals
//!
//! 1. Preserve MIR control-flow structure (basic blocks, statements, terminators)
//! 2. Model per-edge effects explicitly for dataflow analysis
//! 3. Keep cleanup semantics visible (is_cleanup, unwind edges)
//! 4. Remain backend-agnostic for targeting proof terms or external oracles
//!
//! ## References
//!
//! - Rust Compiler Dev Guide: <https://rustc-dev-guide.rust-lang.org/mir/index.html>
//! - RFC 1211 MIR: <https://rust-lang.github.io/rfcs/1211-mir.html>
//! - MIR dataflow: <https://rustc-dev-guide.rust-lang.org/mir/dataflow.html>
//!
//! See: `designs/2026-02-02-mir-derived-cfg-ir.md`

use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Index into the function's basic block list
pub type BasicBlockId = u32;

/// Index into the function's local variable list
pub type LocalId = u32;

/// Index for a block parameter within a basic block
pub type BlockParamIdx = u32;

/// A block parameter (SSA phi argument at block entry).
///
/// Block parameters are the tMIR/functional SSA equivalent of phi nodes.
/// Each predecessor passes arguments via Goto/SwitchInt that bind to
/// these parameters when control enters the block.
///
/// This design follows tMIR for cross-project compatibility:
/// - tMIR: `crates/tmir-func/src/lib.rs` BlockParam
/// - See: designs/2026-02-02-mir-derived-cfg-ir.md
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockParam {
    /// The local that receives the parameter value
    pub local: LocalId,
    /// Type of the parameter
    pub ty: RustType,
    /// Debug name (may be empty)
    pub name: Option<String>,
}

impl BlockParam {
    /// Create a new block parameter
    pub fn new(local: LocalId, ty: RustType) -> Self {
        Self {
            local,
            ty,
            name: None,
        }
    }

    /// Set the debug name
    #[must_use]
    pub fn with_name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }
}

/// A function body in the VIR representation.
///
/// Contains an ordered list of basic blocks and local variable declarations.
/// The entry block is always block 0.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Body {
    /// Ordered list of basic blocks. Block 0 is the entry point.
    pub blocks: Vec<BasicBlock>,
    /// Local variable declarations (arguments, temporaries, return place).
    /// Local 0 is the return place.
    pub locals: Vec<LocalDecl>,
    /// Number of function arguments (locals 1..=arg_count are arguments)
    pub arg_count: u32,
}

impl Body {
    /// Create a new empty function body
    pub fn new() -> Self {
        Self {
            blocks: Vec::new(),
            locals: Vec::new(),
            arg_count: 0,
        }
    }

    /// Get a basic block by ID
    pub fn block(&self, id: BasicBlockId) -> Option<&BasicBlock> {
        self.blocks.get(id as usize)
    }

    /// Get a basic block mutably by ID
    pub fn block_mut(&mut self, id: BasicBlockId) -> Option<&mut BasicBlock> {
        self.blocks.get_mut(id as usize)
    }

    /// Get a local declaration by ID
    pub fn local(&self, id: LocalId) -> Option<&LocalDecl> {
        self.locals.get(id as usize)
    }

    /// Add a new basic block and return its ID
    pub fn add_block(&mut self, block: BasicBlock) -> BasicBlockId {
        let id = self.blocks.len() as BasicBlockId;
        self.blocks.push(block);
        id
    }

    /// Add a new local variable and return its ID
    pub fn add_local(&mut self, decl: LocalDecl) -> LocalId {
        let id = self.locals.len() as LocalId;
        self.locals.push(decl);
        id
    }

    /// Validate that all terminator args match target block param counts.
    ///
    /// Returns a list of (source_block, target_block, expected, actual) for mismatches.
    /// Empty list means all edges are valid.
    pub fn validate_block_args(&self) -> Vec<(BasicBlockId, BasicBlockId, usize, usize)> {
        let mut errors = Vec::new();

        for (src_idx, block) in self.blocks.iter().enumerate() {
            let src = src_idx as BasicBlockId;
            match &block.terminator {
                Term::Goto { target, args } => {
                    if let Some(tgt_block) = self.block(*target) {
                        let expected = tgt_block.params.len();
                        if args.len() != expected {
                            errors.push((src, *target, expected, args.len()));
                        }
                    }
                }
                Term::SwitchInt { targets, .. } => {
                    for switch_tgt in targets.values.values() {
                        if let Some(tgt_block) = self.block(switch_tgt.block) {
                            let expected = tgt_block.params.len();
                            if switch_tgt.args.len() != expected {
                                errors.push((
                                    src,
                                    switch_tgt.block,
                                    expected,
                                    switch_tgt.args.len(),
                                ));
                            }
                        }
                    }
                    // Check otherwise
                    if let Some(tgt_block) = self.block(targets.otherwise.block) {
                        let expected = tgt_block.params.len();
                        if targets.otherwise.args.len() != expected {
                            errors.push((
                                src,
                                targets.otherwise.block,
                                expected,
                                targets.otherwise.args.len(),
                            ));
                        }
                    }
                }
                Term::Call {
                    target,
                    target_args,
                    ..
                } => {
                    if let Some(tgt) = target {
                        if let Some(tgt_block) = self.block(*tgt) {
                            let expected = tgt_block.params.len();
                            if target_args.len() != expected {
                                errors.push((src, *tgt, expected, target_args.len()));
                            }
                        }
                    }
                }
                Term::Assert {
                    target,
                    target_args,
                    ..
                }
                | Term::Drop {
                    target,
                    target_args,
                    ..
                } => {
                    if let Some(tgt_block) = self.block(*target) {
                        let expected = tgt_block.params.len();
                        if target_args.len() != expected {
                            errors.push((src, *target, expected, target_args.len()));
                        }
                    }
                }
                Term::Yield {
                    resume,
                    resume_args,
                    ..
                } => {
                    if let Some(tgt_block) = self.block(*resume) {
                        let expected = tgt_block.params.len();
                        if resume_args.len() != expected {
                            errors.push((src, *resume, expected, resume_args.len()));
                        }
                    }
                }
                // Return/Unreachable exit the function; unwind terminators transfer control
                // out of this CFG. None of these carry block args within the function.
                Term::Return | Term::Unreachable | Term::UnwindResume | Term::UnwindTerminate => {}
            }
        }
        errors
    }
}

impl Default for Body {
    fn default() -> Self {
        Self::new()
    }
}

/// A basic block containing statements followed by a terminator.
///
/// Mirrors MIR basic block structure: linear sequence of statements
/// with a single terminator that determines control flow.
///
/// ## Block Parameters (SSA phi arguments)
///
/// The `params` field provides tMIR-style block-parameter SSA, where
/// predecessors pass arguments via Goto/SwitchInt that bind to these
/// parameters when control enters the block. This is equivalent to
/// phi nodes but more explicit about data flow.
///
/// Example in pseudo-IR:
/// ```text
/// bb1(x: i32, y: i32):    // Block parameters
///   ...
///   goto bb2(x, y+1)      // Arguments passed to bb2
///
/// bb2(a: i32, b: i32):    // Receives from bb1's goto
///   ...
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BasicBlock {
    /// Block parameters (SSA phi arguments at entry).
    /// Predecessors must pass matching arguments in their terminators.
    pub params: Vec<BlockParam>,
    /// Sequential statements in this block
    pub statements: Vec<Stmt>,
    /// Block terminator (required - determines successors)
    pub terminator: Term,
    /// Whether this is a cleanup block (for unwinding)
    pub is_cleanup: bool,
}

impl BasicBlock {
    /// Create a new basic block with a terminator
    pub fn new(terminator: Term) -> Self {
        Self {
            params: Vec::new(),
            statements: Vec::new(),
            terminator,
            is_cleanup: false,
        }
    }

    /// Create a basic block with parameters (SSA entry arguments)
    pub fn with_params(params: Vec<BlockParam>, terminator: Term) -> Self {
        Self {
            params,
            statements: Vec::new(),
            terminator,
            is_cleanup: false,
        }
    }

    /// Create a cleanup block
    pub fn cleanup(terminator: Term) -> Self {
        Self {
            params: Vec::new(),
            statements: Vec::new(),
            terminator,
            is_cleanup: true,
        }
    }

    /// Add a statement to this block
    pub fn add_statement(&mut self, stmt: Stmt) {
        self.statements.push(stmt);
    }

    /// Add a block parameter
    pub fn add_param(&mut self, param: BlockParam) {
        self.params.push(param);
    }
}

/// Local variable declaration.
///
/// Covers function arguments, return place, and temporaries.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalDecl {
    /// Type of this local
    pub ty: RustType,
    /// Debug name (may be empty for temporaries)
    pub name: Option<String>,
    /// Mutability (for analysis purposes)
    pub mutability: Mutability,
    /// Source span for diagnostics (opaque index)
    pub span: Option<u32>,
}

impl LocalDecl {
    /// Create a new local declaration
    pub fn new(ty: RustType, mutability: Mutability) -> Self {
        Self {
            ty,
            name: None,
            mutability,
            span: None,
        }
    }

    /// Set the debug name
    #[must_use]
    pub fn with_name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }
}

/// A statement in a basic block.
///
/// Statements have exactly one successor (fall-through to next statement
/// or the block's terminator).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Stmt {
    /// Assign an rvalue to a place: `place = rvalue`
    Assign { place: Place, rvalue: Rvalue },
    /// Set the discriminant of an enum variant
    SetDiscriminant { place: Place, variant_index: u32 },
    /// Call storage-live for a local (marks allocation point)
    StorageLive(LocalId),
    /// Call storage-dead for a local (marks deallocation point)
    StorageDead(LocalId),
    /// Retag for Stacked Borrows/Tree Borrows semantics
    Retag { kind: RetagKind, place: Place },
    /// No-operation (placeholder)
    Nop,
}

/// Kind of retag operation for borrow semantics
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RetagKind {
    /// Function entry retag
    FnEntry,
    /// Two-phase borrow
    TwoPhase,
    /// Raw pointer creation
    Raw(Mutability),
    /// Default retag
    Default,
}

/// Block terminator determining control flow.
///
/// Each terminator has a list of successor edges, potentially with
/// per-edge effects for dataflow analysis.
///
/// ## Block Arguments (SSA phi arguments)
///
/// Terminators that branch to blocks can carry arguments via `args` fields.
/// These arguments are bound to the target block's parameters on entry.
/// This enables functional SSA style data flow without explicit phi nodes.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Term {
    /// Normal return from function
    Return,
    /// Unconditional branch with arguments
    Goto {
        target: BasicBlockId,
        /// Arguments to pass to target block's parameters
        args: Vec<Operand>,
    },
    /// Conditional branch based on bool operand
    SwitchInt {
        discriminant: Operand,
        /// Map from value to target block with arguments
        targets: SwitchTargets,
    },
    /// Function/method call
    Call {
        /// Function to call
        func: Operand,
        /// Arguments to the call
        args: Vec<Operand>,
        /// Place for return value
        destination: Place,
        /// Target block on successful return
        target: Option<BasicBlockId>,
        /// Arguments to pass to target block's parameters
        target_args: Vec<Operand>,
        /// Target block on unwind/panic
        unwind: UnwindAction,
    },
    /// Assert condition or panic
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertMessage,
        target: BasicBlockId,
        /// Arguments to pass to target block's parameters
        target_args: Vec<Operand>,
        unwind: UnwindAction,
    },
    /// Drop a value (run destructor)
    Drop {
        place: Place,
        target: BasicBlockId,
        /// Arguments to pass to target block's parameters
        target_args: Vec<Operand>,
        unwind: UnwindAction,
    },
    /// Yield from generator (suspend point)
    Yield {
        value: Operand,
        resume: BasicBlockId,
        /// Arguments to pass to resume block's parameters
        resume_args: Vec<Operand>,
        resume_arg: Place,
        drop: Option<BasicBlockId>,
    },
    /// Unreachable code (UB to execute)
    Unreachable,
    /// Resume unwinding (in cleanup blocks)
    UnwindResume,
    /// Terminate unwinding (abort)
    UnwindTerminate,
}

impl Term {
    /// Get all successor block IDs
    pub fn successors(&self) -> Vec<BasicBlockId> {
        match self {
            Term::Return | Term::Unreachable | Term::UnwindResume | Term::UnwindTerminate => {
                vec![]
            }
            Term::Goto { target, .. } => vec![*target],
            Term::SwitchInt { targets, .. } => targets.all_targets(),
            Term::Call { target, unwind, .. } => {
                let mut succs = vec![];
                if let Some(t) = target {
                    succs.push(*t);
                }
                if let UnwindAction::Cleanup(b) = unwind {
                    succs.push(*b);
                }
                succs
            }
            Term::Assert { target, unwind, .. } | Term::Drop { target, unwind, .. } => {
                let mut succs = vec![*target];
                if let UnwindAction::Cleanup(b) = unwind {
                    succs.push(*b);
                }
                succs
            }
            Term::Yield { resume, drop, .. } => {
                let mut succs = vec![*resume];
                if let Some(d) = drop {
                    succs.push(*d);
                }
                succs
            }
        }
    }
}

/// A switch target with block arguments
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwitchTarget {
    /// Target block
    pub block: BasicBlockId,
    /// Arguments to pass to target block's parameters
    pub args: Vec<Operand>,
}

impl SwitchTarget {
    /// Create a new switch target
    pub fn new(block: BasicBlockId) -> Self {
        Self {
            block,
            args: Vec::new(),
        }
    }

    /// Create a new switch target with arguments
    pub fn with_args(block: BasicBlockId, args: Vec<Operand>) -> Self {
        Self { block, args }
    }
}

/// Switch targets for SwitchInt terminator
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwitchTargets {
    /// Map from discriminant value to target with args
    pub values: BTreeMap<u128, SwitchTarget>,
    /// Default target if value not in map
    pub otherwise: SwitchTarget,
}

impl SwitchTargets {
    /// Create new switch targets with a default
    pub fn new(otherwise: BasicBlockId) -> Self {
        Self {
            values: BTreeMap::new(),
            otherwise: SwitchTarget::new(otherwise),
        }
    }

    /// Create new switch targets with a default and arguments
    pub fn with_args(otherwise: BasicBlockId, args: Vec<Operand>) -> Self {
        Self {
            values: BTreeMap::new(),
            otherwise: SwitchTarget::with_args(otherwise, args),
        }
    }

    /// Add a value-to-target mapping (no args)
    pub fn add(&mut self, value: u128, target: BasicBlockId) {
        self.values.insert(value, SwitchTarget::new(target));
    }

    /// Add a value-to-target mapping with arguments
    pub fn add_with_args(&mut self, value: u128, target: BasicBlockId, args: Vec<Operand>) {
        self.values
            .insert(value, SwitchTarget::with_args(target, args));
    }

    /// Get all target block IDs (including otherwise)
    pub fn all_targets(&self) -> Vec<BasicBlockId> {
        let mut targets: Vec<_> = self.values.values().map(|t| t.block).collect();
        targets.push(self.otherwise.block);
        targets
    }

    /// Iterate over all targets with discriminant values (including otherwise).
    ///
    /// Returns an iterator over (discriminant_value, &SwitchTarget) pairs.
    /// The otherwise target has discriminant value `None`.
    pub fn iter_targets(&self) -> impl Iterator<Item = (Option<u128>, &SwitchTarget)> {
        self.values
            .iter()
            .map(|(v, t)| (Some(*v), t))
            .chain(std::iter::once((None, &self.otherwise)))
    }

    /// Get the number of switch cases (excluding otherwise)
    pub fn case_count(&self) -> usize {
        self.values.len()
    }
}

/// Unwind action for terminators that can panic
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum UnwindAction {
    /// Continue unwinding (propagate panic)
    Continue,
    /// Jump to cleanup block
    Cleanup(BasicBlockId),
    /// Abort on unwind (no cleanup)
    Terminate,
    /// Unwinding is UB (marked nounwind)
    Unreachable,
}

/// Assert failure message
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AssertMessage {
    /// Bounds check failed
    BoundsCheck { len: Operand, index: Operand },
    /// Overflow in arithmetic
    Overflow(BinOp, Operand, Operand),
    /// Overflow in negation
    OverflowNeg(Operand),
    /// Division by zero
    DivisionByZero(Operand),
    /// Remainder by zero
    RemainderByZero(Operand),
    /// Misaligned pointer
    MisalignedPointerDereference { required: Operand, found: Operand },
    /// Custom message
    Custom(String),
}

/// An rvalue (right-hand side of assignment).
///
/// Produces a value that can be assigned to a place.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Rvalue {
    /// Use an operand directly
    Use(Operand),
    /// Repeat operand N times: `[operand; count]`
    Repeat { operand: Operand, count: u64 },
    /// Take reference to a place
    Ref {
        borrow_kind: BorrowKind,
        place: Place,
    },
    /// Create thread-local reference
    ThreadLocalRef(String),
    /// Get address of a place (raw pointer)
    AddressOf {
        mutability: Mutability,
        place: Place,
    },
    /// Get length of a slice/array
    Len(Place),
    /// Cast operand to type
    Cast {
        kind: CastKind,
        operand: Operand,
        ty: RustType,
    },
    /// Binary operation
    BinaryOp {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
    },
    /// Checked binary operation (returns (result, overflow_flag))
    CheckedBinaryOp {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
    },
    /// Null binary operation (like Eq but for pointers)
    NullaryOp { op: NullOp, ty: RustType },
    /// Unary operation
    UnaryOp { op: UnOp, operand: Operand },
    /// Discriminant of enum value
    Discriminant(Place),
    /// Aggregate construction (struct, tuple, array, etc.)
    Aggregate {
        kind: AggregateKind,
        operands: Vec<Operand>,
    },
    /// Shallow initialization check for unsafe code
    ShallowInitBox { operand: Operand, ty: RustType },
    /// Copy for unsized value
    CopyForDeref(Place),
    /// A fresh, nondeterministic value of the given type.
    ///
    /// This rvalue carries *no* information about the value it produces: the
    /// destination place is known only to be (re)initialized to *some* value of
    /// `ty`. It is the sound over-approximation used when an operation may write
    /// an arbitrary value that the verifier must not assume anything about —
    /// most notably inline-assembly output/clobber effects, where the asm may
    /// set a register (and hence its bound place) to any value.
    ///
    /// Using an opaque value (rather than a concrete [`Constant`]) is required
    /// for soundness: assigning a determinate constant would let downstream
    /// verification assume that exact value, an under-approximation that could
    /// prove a false property. An opaque value only forgets information, which
    /// is sound (at worst incomplete).
    Opaque { ty: RustType },
}

/// Kind of borrow (reference creation)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BorrowKind {
    /// Shared borrow (&T)
    Shared,
    /// Shallow borrow (for match guards)
    Shallow,
    /// Mutable borrow (&mut T)
    Mut {
        /// Two-phase borrow flag
        kind: MutBorrowKind,
    },
}

/// Sub-kind of mutable borrow
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MutBorrowKind {
    /// Default mutable borrow
    Default,
    /// Two-phase borrow (for method receivers)
    TwoPhaseBorrow,
    /// Closure capture borrow
    ClosureCapture,
}

/// Kind of type cast
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CastKind {
    /// Pointer to pointer
    PtrToPtr,
    /// Integer to integer
    IntToInt,
    /// Float to integer
    FloatToInt,
    /// Integer to float
    IntToFloat,
    /// Float to float
    FloatToFloat,
    /// Pointer to address
    PointerExposeAddress,
    /// Address to pointer
    PointerFromExposedAddress,
    /// Function item to function pointer
    FnPtrToPtr,
    /// Transmute (reinterpret bits)
    Transmute,
    /// Unsized coercion: `&T` → `&dyn Trait`, `Box<T>` → `Box<dyn Trait>`, etc.
    PointerUnsize,
}

/// Nullary operation (takes type, not operand)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum NullOp {
    /// Size of type
    SizeOf,
    /// Alignment of type
    AlignOf,
    /// Offset of field in type (field indices path)
    OffsetOf(Vec<(u32, u32)>),
}

/// Binary operation for VIR.
///
/// Note: This is separate from `values::BinOp` intentionally.
/// VIR models MIR which includes unchecked operations (`AddUnchecked`, etc.)
/// that don't exist in the runtime value evaluation model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    /// Unchecked add (UB on overflow)
    AddUnchecked,
    /// Unchecked sub (UB on overflow)
    SubUnchecked,
    /// Unchecked mul (UB on overflow)
    MulUnchecked,
    /// Unchecked shift left
    ShlUnchecked,
    /// Unchecked shift right
    ShrUnchecked,
    /// Pointer offset
    Offset,
}

/// Unary operation for VIR.
///
/// Note: Same variants as `values::UnOp` - kept separate for module isolation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnOp {
    /// Logical/bitwise NOT
    Not,
    /// Arithmetic negation
    Neg,
}

/// Kind of aggregate being constructed
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AggregateKind {
    /// Array literal
    Array(RustType),
    /// Tuple
    Tuple,
    /// Struct or union
    Adt { name: String, variant_index: u32 },
    /// Closure (captures and kind)
    Closure { def_id: String },
    /// Generator
    Generator { def_id: String },
}

/// An operand (used in rvalues and some terminators).
///
/// Either a copy of a place, a move from a place, or a constant.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Operand {
    /// Copy value from place (for Copy types)
    Copy(Place),
    /// Move value from place (invalidates source)
    Move(Place),
    /// Constant value
    Constant(Constant),
}

impl Operand {
    /// Create a copy operand
    pub fn copy(place: Place) -> Self {
        Operand::Copy(place)
    }

    /// Create a move operand
    pub fn mov(place: Place) -> Self {
        Operand::Move(place)
    }

    /// Create a constant operand
    pub fn constant(c: Constant) -> Self {
        Operand::Constant(c)
    }
}

/// A constant value
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Constant {
    /// Scalar value (integer, float, bool, char)
    Scalar(ScalarValue),
    /// Zero-sized type value
    ZeroSized,
    /// Static reference
    Static(String),
    /// String literal
    Str(String),
    /// Byte string literal
    ByteStr(Vec<u8>),
    /// Function item
    FnDef {
        name: String,
        /// Generic arguments as types
        substs: Vec<RustType>,
    },
    /// Composite (aggregate) constant: a tuple, fixed-size array, struct, or
    /// enum literal whose components are themselves constants.
    ///
    /// Composite literals such as `(1, 2)`, `[1, 2, 3]`, `Point { x: 1, y: 2 }`,
    /// or `Option::Some(3)` are usually built as an [`Rvalue::Aggregate`] from
    /// individual operands. When every component is a constant, the whole
    /// literal is itself a constant and can be materialized as an
    /// [`Operand::Constant`] directly, without spilling each element into a
    /// temporary. This variant captures that case faithfully and recursively.
    ///
    /// Note: all-`u8` arrays are still represented as the more specific
    /// [`Constant::ByteStr`] fast-path; this variant covers the remaining
    /// composite shapes.
    Aggregate(Box<AggregateConst>),
}

/// A composite constant: the kind plus its constituent constants.
///
/// Boxed inside [`Constant::Aggregate`] so that `Constant` stays small for the
/// common scalar case.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AggregateConst {
    /// The shape of this aggregate (tuple, array, struct, or enum).
    pub kind: ConstAggregateKind,
    /// The constituent constants, in declaration order.
    ///
    /// For [`ConstAggregateKind::Struct`] and the struct form of
    /// [`ConstAggregateKind::Enum`], element `i` corresponds to the field name
    /// at index `i` recorded on the kind; for tuples, arrays, and tuple-variant
    /// enums the elements are positional.
    pub elements: Vec<Constant>,
}

impl AggregateConst {
    /// Create a tuple constant from positional element constants.
    pub fn tuple(elements: Vec<Constant>) -> Self {
        Self {
            kind: ConstAggregateKind::Tuple,
            elements,
        }
    }

    /// Create a fixed-size array constant from element constants.
    pub fn array(element_ty: RustType, elements: Vec<Constant>) -> Self {
        Self {
            kind: ConstAggregateKind::Array(element_ty),
            elements,
        }
    }
}

/// Shape of a composite constant.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConstAggregateKind {
    /// Tuple literal: elements are positional.
    Tuple,
    /// Fixed-size array literal: elements are positional, all of `element_ty`.
    Array(RustType),
    /// Struct literal: `field_names[i]` names `elements[i]`.
    Struct {
        /// Struct type name.
        name: String,
        /// Field names aligned with the element constants.
        field_names: Vec<String>,
    },
    /// Enum variant literal.
    Enum {
        /// Enum type name.
        name: String,
        /// Variant name.
        variant: String,
        /// Field names for a struct-style variant; empty for a tuple-style or
        /// unit variant (where elements are positional / absent).
        field_names: Vec<String>,
    },
}

/// Scalar constant value
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ScalarValue {
    Bool(bool),
    Char(char),
    Int(i128),
    Uint(u128),
    Float32(f32),
    Float64(f64),
}

/// Per-edge effect for dataflow analysis.
///
/// Captures effects that happen on a specific CFG edge (e.g., call return,
/// unwind edge) rather than in a statement or at block entry/exit.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeEffect {
    /// Source block
    pub from: BasicBlockId,
    /// Target block
    pub to: BasicBlockId,
    /// Kind of effect
    pub kind: EdgeEffectKind,
}

/// Kind of edge effect
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EdgeEffectKind {
    /// Move value to destination on call return
    CallReturnMove { destination: Place },
    /// Initialize locals on function entry edge
    InitializeLocals(Vec<LocalId>),
    /// Drop value on unwind edge
    UnwindDrop(Place),
    /// Custom effect (for extensibility)
    Custom(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::UintType;

    #[test]
    fn test_body_construction() {
        let mut body = Body::new();

        // Add return place (local 0)
        let ret_decl = LocalDecl::new(RustType::Unit, Mutability::Mutable);
        body.add_local(ret_decl);

        // Add a simple block that just returns
        let block = BasicBlock::new(Term::Return);
        let block_id = body.add_block(block);

        assert_eq!(block_id, 0);
        assert_eq!(body.blocks.len(), 1);
        assert_eq!(body.locals.len(), 1);
    }

    #[test]
    fn test_basic_block_construction() {
        let mut block = BasicBlock::new(Term::Return);

        // Add an assignment
        let place = Place::Local(0);
        let rvalue = Rvalue::Use(Operand::Constant(Constant::Scalar(ScalarValue::Uint(42))));
        block.add_statement(Stmt::Assign { place, rvalue });

        assert_eq!(block.statements.len(), 1);
        assert!(!block.is_cleanup);
    }

    #[test]
    fn test_switch_targets() {
        let mut targets = SwitchTargets::new(5); // default to block 5
        targets.add(0, 1);
        targets.add(1, 2);
        targets.add(2, 3);

        let all = targets.all_targets();
        assert!(all.contains(&1));
        assert!(all.contains(&2));
        assert!(all.contains(&3));
        assert!(all.contains(&5)); // otherwise
    }

    #[test]
    fn test_terminator_successors() {
        // Return has no successors
        assert!(Term::Return.successors().is_empty());

        // Goto has one successor
        let goto = Term::Goto {
            target: 1,
            args: vec![],
        };
        assert_eq!(goto.successors(), vec![1]);

        // Call with target and cleanup
        let call = Term::Call {
            func: Operand::Constant(Constant::FnDef {
                name: "foo".to_string(),
                substs: vec![],
            }),
            args: vec![],
            destination: Place::Local(0),
            target: Some(2),
            target_args: vec![],
            unwind: UnwindAction::Cleanup(3),
        };
        let succs = call.successors();
        assert!(succs.contains(&2));
        assert!(succs.contains(&3));
    }

    #[test]
    fn test_local_decl_builder() {
        let decl =
            LocalDecl::new(RustType::Uint(UintType::U32), Mutability::Mutable).with_name("counter");

        assert_eq!(decl.name, Some("counter".to_string()));
        assert_eq!(decl.ty, RustType::Uint(UintType::U32));
    }

    #[test]
    fn test_rvalue_varieties() {
        // Use operand
        let use_rv = Rvalue::Use(Operand::Copy(Place::Local(0)));

        // Binary operation
        let binop_rv = Rvalue::BinaryOp {
            op: BinOp::Add,
            lhs: Operand::Copy(Place::Local(1)),
            rhs: Operand::Constant(Constant::Scalar(ScalarValue::Int(1))),
        };

        // Reference
        let ref_rv = Rvalue::Ref {
            borrow_kind: BorrowKind::Shared,
            place: Place::Local(2),
        };

        // All should construct without panic
        drop((use_rv, binop_rv, ref_rv));
    }

    #[test]
    fn test_cleanup_block() {
        let cleanup = BasicBlock::cleanup(Term::UnwindResume);
        assert!(cleanup.is_cleanup);
    }

    #[test]
    fn test_block_params() {
        // Create block parameters
        let param1 = BlockParam::new(0, RustType::Uint(UintType::U32)).with_name("x");
        let param2 = BlockParam::new(1, RustType::Uint(UintType::U32));

        assert_eq!(param1.name, Some("x".to_string()));
        assert_eq!(param1.local, 0);
        assert_eq!(
            param2.name, None,
            "unnamed BlockParam should have name None"
        );
    }

    #[test]
    fn test_block_with_params() {
        // Create a block that receives two parameters
        let params = vec![
            BlockParam::new(0, RustType::Uint(UintType::U32)),
            BlockParam::new(1, RustType::Uint(UintType::U32)),
        ];
        let block = BasicBlock::with_params(params, Term::Return);

        assert_eq!(block.params.len(), 2);
        assert!(!block.is_cleanup);
        assert!(block.statements.is_empty());
    }

    #[test]
    fn test_goto_with_args() {
        // Goto passing arguments to target block
        let goto = Term::Goto {
            target: 1,
            args: vec![
                Operand::Copy(Place::Local(0)),
                Operand::Constant(Constant::Scalar(ScalarValue::Uint(42))),
            ],
        };

        assert_eq!(goto.successors(), vec![1]);
        if let Term::Goto { args, .. } = goto {
            assert_eq!(args.len(), 2);
        }
    }

    #[test]
    fn test_switch_targets_with_args() {
        // Create switch targets with arguments
        let mut targets = SwitchTargets::with_args(5, vec![Operand::Copy(Place::Local(0))]);
        targets.add_with_args(0, 1, vec![Operand::Copy(Place::Local(1))]);
        targets.add(1, 2); // No args

        let all = targets.all_targets();
        assert!(all.contains(&1));
        assert!(all.contains(&2));
        assert!(all.contains(&5));

        // Check args on otherwise
        assert_eq!(targets.otherwise.args.len(), 1);

        // Check args on case 0
        let case0 = targets.values.get(&0).unwrap();
        assert_eq!(case0.args.len(), 1);

        // Check case 1 has no args
        let case1 = targets.values.get(&1).unwrap();
        assert!(case1.args.is_empty());
    }

    #[test]
    fn test_ssa_style_cfg() {
        // Build a simple SSA-style CFG:
        // bb0: goto bb1(x=local0, y=42)
        // bb1(x: u32, y: u32): return

        let mut body = Body::new();

        // Add locals
        let local0 = body.add_local(
            LocalDecl::new(RustType::Uint(UintType::U32), Mutability::Mutable).with_name("input"),
        );
        let local_x = body.add_local(
            LocalDecl::new(RustType::Uint(UintType::U32), Mutability::Mutable).with_name("x"),
        );
        let local_y = body.add_local(
            LocalDecl::new(RustType::Uint(UintType::U32), Mutability::Mutable).with_name("y"),
        );

        // Entry block: goto bb1 with args
        let bb0 = BasicBlock::new(Term::Goto {
            target: 1,
            args: vec![
                Operand::Copy(Place::Local(local0)),
                Operand::Constant(Constant::Scalar(ScalarValue::Uint(42))),
            ],
        });
        body.add_block(bb0);

        // Target block with parameters
        let bb1_params = vec![
            BlockParam::new(local_x, RustType::Uint(UintType::U32)).with_name("x"),
            BlockParam::new(local_y, RustType::Uint(UintType::U32)).with_name("y"),
        ];
        let bb1 = BasicBlock::with_params(bb1_params, Term::Return);
        body.add_block(bb1);

        // Verify structure
        assert_eq!(body.blocks.len(), 2);
        assert_eq!(body.block(0).unwrap().params.len(), 0); // Entry has no params
        assert_eq!(body.block(1).unwrap().params.len(), 2); // bb1 has 2 params

        // Verify goto has args
        if let Term::Goto { args, .. } = &body.block(0).unwrap().terminator {
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected Goto terminator");
        }

        // Validate that args match params
        let errors = body.validate_block_args();
        assert!(
            errors.is_empty(),
            "Expected valid SSA, got errors: {:?}",
            errors
        );
    }

    #[test]
    fn test_validate_block_args_mismatch() {
        // Test that validation catches arg/param count mismatches
        let mut body = Body::new();

        // Block with 2 params
        let params = vec![
            BlockParam::new(0, RustType::Uint(UintType::U32)),
            BlockParam::new(1, RustType::Uint(UintType::U32)),
        ];
        body.add_block(BasicBlock::with_params(params, Term::Return));

        // Goto with wrong number of args (1 instead of 2)
        body.add_block(BasicBlock::new(Term::Goto {
            target: 0,
            args: vec![Operand::Constant(Constant::Scalar(ScalarValue::Uint(42)))],
        }));

        let errors = body.validate_block_args();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0], (1, 0, 2, 1)); // source=1, target=0, expected=2, actual=1
    }

    #[test]
    fn test_switch_targets_iter() {
        let mut targets = SwitchTargets::new(5);
        targets.add(0, 1);
        targets.add(1, 2);

        // Collect all targets via iterator
        let all: Vec<_> = targets.iter_targets().collect();
        assert_eq!(all.len(), 3);

        // Check that we get discriminant values
        assert!(all.iter().any(|(v, t)| *v == Some(0) && t.block == 1));
        assert!(all.iter().any(|(v, t)| *v == Some(1) && t.block == 2));
        assert!(all.iter().any(|(v, t)| v.is_none() && t.block == 5));

        // Check case_count
        assert_eq!(targets.case_count(), 2);
    }
}
