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
//! integer/float casts, scalar/vector float operations at every carried
//! width (binary16 included, WS2.15: computed at a wider precision and
//! rounded ONCE by [`f64_to_f16_bits`]), integer tensor contraction
//! (`Inst::TensorContract` over [`InterpretValueKind::Tensor`] values,
//! PKG-U13a: the shape is part of the value, paired extents that differ and a
//! result count `usize` cannot hold are undefined behaviour, and the node
//! costs one fuel unit however many elements it materializes), and simple
//! allocation-aware memory operations. Dialect ops, intentionally excluded
//! casts, borrow/ARC, binding
//! frames, and multi-threaded atomics return stable unsupported codes instead
//! of pretending to execute. A
//! VARIADIC signature is two cases (WS2.15): a call to a variadic
//! declaration is a host call carrying the full argument list, and a
//! variadic definition is refused (`SignatureMismatch`, "non-executable
//! vararg signature") because no instruction reads a variadic argument. A
//! variadic declaration of a symbol the installed host models at a FIXED
//! arity is refused with the same code and reason, because it is a forged
//! signature and not an unmodelled symbol ([`HostCalls::models_fixed_arity`]).
//!
//! A call to a BODYLESS declaration is not executable in-format: it is
//! `UnsupportedCall` unless an installed [`HostCalls`] model serves it
//! ([`Interpreter::with_host`], WS2.12). A host model is a trusted-base row,
//! not evidence, so every run it serves is counted in
//! [`InterpretOutcome::host_calls`]; runtime handles (`Ty::Handle`) exist only
//! as host-minted, transport-only [`InterpretValueKind::Handle`] values. A
//! reference-counting runtime's entry points are the one host-served shape
//! that touches memory: the host only CLASSIFIES them ([`HostCalls::rc_op`],
//! WS2.13) and the interpreter counts its own `HeapAlloc { origin }` cells.
//! The reference models of the pinned runtimes live in `trust-ir-build`
//! (`host::PinnedHandleHost`), keyed by the validator's pin tables.
//!
//! Alignment gap with `lean/trust_ir-semantics`: Lean remains the source of truth
//! for the full operational semantics, especially memory, permission state,
//! excluded casts/float widths, atomics, and proof-carrying effects. The Rust
//! memory slice below mirrors Lean's allocation-aware checks for live
//! allocations, bounds, initialized bytes, and base-pointer deallocation, but
//! intentionally keeps layout conservative: scalar, pointer, unit, fixed
//! integer/bool vectors, and module-backed arrays have byte layouts, while
//! structs, enums, fat pointers, records, sets, sequences, tensors (which have
//! no memory layout at all), closures, and packed/ABI aggregate layout still
//! report `type_error`. Volatile load/store
//! flags are deterministic no-ops in this single-threaded interpreter;
//! explicit alignment operands and natural scalar/vector alignment are checked.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

mod array_value;
mod byte_image;
mod observation_word;
mod observed;
#[cfg(test)]
mod reconciled_execution;
pub(crate) use observed::btree as observed_btree;
mod module_policy;
mod rope;
mod scalar_bool;
mod tensor_gather_scatter;
mod tensor_region;
pub use module_policy::InterpreterModule;
use module_policy::ModulePreflight;

pub use observation_word::{ObservationWord, WordLengthOverflow};

pub use observed::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, InstructionSite,
    ObservationRefusal, ObservationStopped, ObservedExit, ObservedReport, ObservedSession,
    ObservedValueError,
};

pub use array_value::{
    ArrayNode, ArrayNodeKind, ArrayStructure, ArrayStructureId, ArrayStructureNode, ArrayValue,
};
use byte_image::{ByteStore, Image};

use crate::constant::Constant;
use crate::dialect::DialectInst;
use crate::dialect::vector::{self, VectorSpec};
use crate::inst::{
    AllocOrigin, AssertKind, AtomicRMWOp, BinOp, CastOp, FCmpOp, ICmpOp, Inst, OverflowOp,
    PanicLocation, PanicSite, UnOp,
};
use crate::node::InstrNode;
use crate::ty::{FatPtrKind, FuncTy, Ty};
use crate::value::{BlockId, EnumId, FuncId, FuncTyId, GlobalId, StructId, TyId, ValueId};
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
    /// A float operation the interpreter could not compute at the operand's
    /// precision. Until WS2.15 every `F16` arithmetic, comparison, constant,
    /// cast, bitcast and image reported it; all of those now execute
    /// ([`f64_to_f16_bits`]), so the interpreter currently has NO producer of
    /// this code. It is retained as the stable mirror of the Lean model's
    /// `unsupported.float` (which refuses observable NaN payloads at every
    /// width) and for the next width the format carries before the model does.
    /// Both engines execute binary16; versioned subset/native admission is
    /// still pending.
    UnsupportedFloat,
    TypeError,
    UndefinedBehavior,
    /// An `Inst::Assume` condition evaluated to `false` (WS2.11, the
    /// "Harness inputs" ratification in `docs/SPEC_RATIFICATIONS.md`).
    ///
    /// Still an error, and still a refusal: an execution past a false
    /// assumption has no defined meaning, because the assumption is a premise
    /// of every proof about the function, so nothing downstream may treat the
    /// continuation as a result. The distinct code exists so a harness driver
    /// can classify "this input is outside the assumed domain" (a vacuity
    /// filter over the universally quantified entry parameters) apart from
    /// "the program itself hit UB". A POISON assume condition is not this
    /// code: inspecting poison is [`UndefinedBehavior`]
    /// (`docs/ub-numerics-policy.md` §4), the same as any other inspection.
    ///
    /// NOT a claim about Lean. The Lean executable model does not refuse a
    /// false assumption at all — `Semantics/Step.lean` runs `Assume` as a
    /// no-op (`assume_always_succeeds`) for a false condition and a poison one
    /// alike. That is the pre-existing `Assume` model split recorded in
    /// `docs/ub-numerics-policy.md` §4; WS2.11 renames the reference
    /// interpreter's verdict and neither widens nor narrows that split.
    ///
    /// [`UndefinedBehavior`]: InterpretErrorCode::UndefinedBehavior
    AssumeViolated,
    Panic,
    OutOfFuel,
    /// The program's ADDRESS SPACE is exhausted: an allocation whose last
    /// byte no target pointer can name (a 32-bit target has 4 GiB), or a host
    /// model's own incapacity (`trust-ir-build`'s bignum model). An
    /// incapacity code, NOT a trap and NOT a lowering defect; differential
    /// consumers treat it as coverage-only.
    ///
    /// It is no longer a host-memory budget. Allocations are SPARSE
    /// (`ByteStore`: an allocation of any size is one run until something is
    /// written, a stored splat stays one run, and a copy shares the nodes it
    /// copies), so an in-IR allocation size — a sampled `Alloca`/`HeapAlloc`
    /// `count` included — costs O(1) host memory, and the `mem_budget` cap
    /// that used to refuse large allocations is gone.
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
            InterpretErrorCode::AssumeViolated => "assume_violated",
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
    /// The structured panic when `code` is [`InterpretErrorCode::Panic`]
    /// (plan item P): WHICH Rust panic a failed `Inst::Assert` is, and the
    /// operand values its message prints. `None` for every other code.
    ///
    /// Boxed (amendment P): the resolved panic site would otherwise make every
    /// `InterpretResult` carry it inline.
    pub panic: Option<Box<InterpretPanic>>,
}

/// The panic outcome of a failed `Inst::Assert` (plan item P, wire v52):
/// the assert's [`AssertKind`] with its operands RESOLVED to the values they
/// held when the check failed. `message()` is the text `core` prints for
/// that panic, byte for byte, and is also the error's `message`; the Lean
/// executable model throws the same text (`Semantics/Step.lean`, `.Assert`),
/// so the two engines agree on WHICH panic, not only that one happened.
///
/// Amendment P (wire v54, `docs/SPEC_RATIFICATIONS.md` §19.1): the NORMATIVE
/// outcome is the tuple (kind, operand values, entry, resolved location) —
/// two runs agree only if all four agree. The message is the kind's
/// rendering; the text a program prints is its entry's, which the reference
/// engines never execute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpretPanic {
    /// The failed assert's kind, its operand `ValueId`s as written.
    pub kind: AssertKind,
    /// `[index, len]` (`BoundsCheck`) or `[required, found]`
    /// (`MisalignedPtr`) as unsigned values; `None` for every other kind.
    pub operands: Option<[u128; 2]>,
    /// The failed check's panic site with its location RESOLVED, or `None`
    /// for an unsited assert (a panic of unknown realization).
    pub site: Option<InterpretPanicSite>,
}

/// A failed sited check's realization (amendment P): the entry it calls and
/// the location it passes, resolved when the check failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InterpretPanicSite {
    /// The site's entry, as written (never executed by the interpreter).
    pub entry: FuncId,
    /// The location the entry would receive.
    pub location: PanicLocationValue,
}

/// A panic location resolved at the failure (amendment P, §19.1 rule 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PanicLocationValue {
    /// Byte `offset` of module global `global`: a `Global(g)` location
    /// (offset 0, the global NOT materialized), or a `Value` pointer into
    /// the allocation of a materialized global.
    Global { global: GlobalId, offset: u64 },
    /// A live pointer outside every global's allocation.
    Other,
}

impl InterpretPanic {
    /// The panic message `core` prints (`"assertion failed"` for
    /// `AssertKind::Unspecified`, which has no Rust message).
    pub fn message(&self) -> String {
        self.kind.panic_message(self.operands.unwrap_or([0, 0]))
    }
}

impl InterpretError {
    pub fn new(code: InterpretErrorCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            block: None,
            value: None,
            panic: None,
        }
    }

    /// The structured panic of a failed assert, if this error is one.
    pub fn panic(&self) -> Option<&InterpretPanic> {
        self.panic.as_deref()
    }

    pub fn with_block(mut self, block: BlockId) -> Self {
        self.block = Some(block);
        self
    }

    pub fn with_value(mut self, value: ValueId) -> Self {
        self.value = Some(value);
        self
    }

    /// The symbol of the bodyless declaration this error refused to enter
    /// because no host model served it (WS2.12), or `None` for any other
    /// error — including a host call refused for another reason, and an error
    /// a host model itself returned.
    ///
    /// The message is owned by this module, so this is the one place its
    /// shape is parsed: a tool that wants to name the unhosted callee (the
    /// `trust-ir run` refusal at a pinned trusted-runtime entry point) asks
    /// here instead of matching diagnostic text.
    pub fn unhosted_callee(&self) -> Option<&str> {
        if self.code != InterpretErrorCode::UnsupportedCall {
            return None;
        }
        self.message
            .strip_prefix(BODYLESS_CALL_PREFIX)?
            .strip_suffix(NO_HOST_MODEL_SUFFIX)
            .filter(|name| !name.is_empty())
    }
}

/// Prefix of the [`InterpretErrorCode::UnsupportedCall`] message for a call
/// to a bodyless declaration; the callee symbol follows it.
const BODYLESS_CALL_PREFIX: &str = "call to bodyless declaration @";

/// Suffix of that message when no host model served the call — the case
/// [`InterpretError::unhosted_callee`] reports.
const NO_HOST_MODEL_SUFFIX: &str = ": no host model (declarations are not executable in-format)";

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
/// consumed per direct or indirect interprocedural call.
///
/// There is deliberately NO memory budget. The host memory a run uses
/// follows the instructions it EXECUTES, never the sizes, counts or lengths
/// they name. Byte images and array / vector values are persistent ropes with
/// shared structure (`interpret::rope`): an allocation is a sparse byte store
/// (O(1) whatever its size); a `MemSet` or a stored splat is one run; a
/// `MemCopy` stores the source's image as one run SHARING its nodes (a
/// doubling copy adds a node, not the bytes); a load decodes the image's
/// structure (a repeating run is decoded once per period, whatever element
/// type it is read back at); `ArraySplat` of any length is one node and
/// `InsertElement` copies one path; lane-wise vector arithmetic runs on the
/// same structure. The `mem_budget` field that used to refuse allocations
/// above 256 MiB (because they were materialized as host `Vec`s) was a patch
/// over that representation and was deleted with it.
///
/// What is still proportional to a length is only what the program paid for
/// or asked for: literal bytes it wrote one by one, the elements of a list it
/// spelled, a copy that reads `r` separately written runs (O(r · height)
/// nodes), and a load that reads a repeating run at a stride its period does
/// not divide, which decodes `min(p, s) / gcd(p, s)` distinct elements for
/// period `p` and stride `s` — that many DISTINCT values exist, and a
/// materialized value holds each.
///
/// One instruction is the exception to "follows the instructions it
/// executes": `Inst::TensorContract` (PKG-U13a) materializes its `N` result
/// elements from ONE node, charged one fuel unit like every node (SemR's
/// `run` charges the same), and does `N · K` multiply-adds for `K` the
/// product of the contracted extents. `N` is bounded only by the target
/// (`N < 2^pointer_bits`, else undefined behaviour, decided before anything
/// is allocated); when some contracted extent is 0 every sum is empty and the
/// all-zero result is one uniform node, O(1) whatever `N`.
///
/// `panic_strategy` names which panic runtime the run models (amendment D,
/// Part 2, `docs/SPEC_RATIFICATIONS.md` §21). The default is
/// [`PanicStrategy::Abort`], the panic=abort projection every earlier run
/// executed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InterpretOptions {
    pub fuel: u64,
    pub max_call_depth: u64,
    pub panic_strategy: PanicStrategy,
}

impl Default for InterpretOptions {
    fn default() -> Self {
        Self {
            fuel: 10_000,
            max_call_depth: 64,
            panic_strategy: PanicStrategy::Abort,
        }
    }
}

/// Which panic runtime a run models (amendment D, Part 2,
/// `docs/SPEC_RATIFICATIONS.md` §21 rule 2). Mirrors the Lean model's
/// `PanicStrategy` (the `strat` argument of `stepNWithContext` /
/// `evalFunctionInContext`, default `.abort`).
///
/// * [`PanicStrategy::Abort`] (the default) is the panic=abort projection
///   (`docs/ub-numerics-policy.md` §4): a failed `Assert` / `AssertInvoke` is
///   the terminal panic, and no unwind edge is ever taken.
/// * [`PanicStrategy::Unwind`]: a failed check RAISES an exception object;
///   the unwinding leaves every frame up to the first `Invoke`,
///   `InvokeIndirect`, resolved `DropInvoke` or failing `AssertInvoke`,
///   which transfers it to its landing pad; `Resume` re-raises it; one that
///   escapes the entry ends the run as the same `Panic` the Abort run
///   reports.
///
/// A verdict computed under `Unwind` covers panic=unwind and panic=abort
/// builds (up to its first raise the Abort run IS the Unwind run, §21 rule
/// 7); one computed under `Abort` covers panic=abort only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum PanicStrategy {
    /// The panic=abort projection: unwind edges are never taken.
    #[default]
    Abort,
    /// Unwinding is an exit: raise, catch, landing pads and `Resume`.
    Unwind,
}

/// Result of executing a function to a `return` terminator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpretOutcome {
    pub returns: Vec<InterpretValue>,
    pub steps: u64,
    /// How many calls to a bodyless declaration a [`HostCalls`] model served
    /// during this run (WS2.12). Zero means the run was executed ENTIRELY
    /// in-format. A nonzero count marks the run HOST-ASSISTED: part of its
    /// behaviour came from a host model, which is a trusted-base row
    /// (`TRUST.md` item 9), never from the module's own semantics, so a
    /// consumer must not present such a run as in-format execution evidence.
    /// Counted by the interpreter, not by the host, so a host cannot hide a
    /// call it served. The must-refuse corpus cannot express the presenting
    /// rule (`refuse/host_assisted_run_not_in_format_evidence`): it is a
    /// reporting act, not a module; the counter on this type is its rung.
    pub host_calls: u64,
}

/// A host model of bodyless declarations (WS2.12): the interpreter's ONLY way
/// to execute a call whose callee has no body in the module.
///
/// # Fail-closed default
///
/// A call to a declaration ([`Function::is_declaration`]) is refused with
/// [`InterpretErrorCode::UnsupportedCall`] ("no host model (declarations are
/// not executable in-format)") unless an installed host returns `Some` for it.
/// There is no default behaviour: an interpreter without a host (the default)
/// executes exactly the in-format subset, and a host that returns `None`
/// ("not mine") is indistinguishable from no host.
///
/// # A host is a TRUSTED model, not evidence
///
/// Whatever a host computes is the host's claim about the external symbol, not
/// a consequence of the module. It is outside the proven subset by construction
/// (`bridge.rs` keeps `Ty::Handle` excluded, and nothing in this module is
/// mirrored in Lean). Every run it serves is counted in
/// [`InterpretOutcome::host_calls`], so host-assisted execution can always be
/// told apart from in-format execution.
///
/// # What the interpreter still checks
///
/// The arguments are checked against the declaration's signature before the
/// host sees them. The host's results are checked against the declared return
/// types (a mismatch is [`InterpretErrorCode::SignatureMismatch`]), and each
/// result must be a well-formed value of its type: an integer of exactly the
/// declared width and signedness (a `char` only a Unicode scalar value), a
/// `Bool`, an `F16`/`F32`/`F64` bit pattern, `Unit`,
/// or a LIVE handle this execution minted at exactly the declared
/// [`crate::ty::HandleTy`]. Any other result type (pointers, aggregates) is
/// refused with `UnsupportedCall`: a host has no access to interpreter memory,
/// so a pointer it returned would carry forged provenance. An error a host
/// returns is re-worded "host model for @name: ...", so a host's claim (say,
/// `UndefinedBehavior`) is never mistaken for a verdict about the module.
///
/// `Sync` so that an [`Interpreter`] holding a host stays `Send + Sync`; a host
/// keeps its mutable tables in the per-execution [`HostState`], never in
/// itself.
///
/// # Reference-counting runtimes (WS2.13)
///
/// A host cannot touch interpreter memory, so it cannot itself model a
/// runtime whose entry points read and write a refcount through a pointer
/// (`clean_inc(Ptr)` and its siblings). [`HostCalls::rc_op`] is the second
/// hook for exactly that: the host only CLASSIFIES a declaration as the
/// `retain` / `release` / `is_unique` entry of the runtime owning one
/// [`AllocOrigin`], and the INTERPRETER performs the operation on its own
/// per-allocation reference count — the same count `Inst::Retain` /
/// `Inst::Release` / `Inst::IsUnique` maintain — after checking that the
/// pointer addresses a live cell of that origin at offset 0. The host never
/// sees the pointer. Such a call is host-assisted too (counted in
/// [`InterpretOutcome::host_calls`]): which runtime a symbol names is the
/// host's claim.
pub trait HostCalls: Sync {
    /// Execute `callee` (a bodyless declaration, declared with the signature
    /// `sig`) on `args`. Return `None` when this host does not model `callee`
    /// — including when it models the symbol but `sig` is not the signature
    /// its model is written against, so a mis-declared entry point is never
    /// served under a signature the model did not mean.
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        args: &[InterpretValue],
        host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>>;

    /// Classify `callee` (a bodyless declaration with signature `sig`) as an
    /// entry point of a reference-counting runtime the interpreter models
    /// with its own refcounts, or `None` (the default: no such claim). The
    /// interpreter consults this BEFORE [`HostCalls::call`]; a `Some` answer
    /// is final, and the pointer argument is never handed to the host.
    fn rc_op(&self, callee: &Function, sig: &FuncTy) -> Option<HostRcOp> {
        let _ = (callee, sig);
        None
    }

    /// Whether this host models `callee`'s link-time symbol, at `callee`'s
    /// calling convention, as a FIXED-ARITY entry point, whatever signature
    /// `callee` declares. The default is `false`, meaning no such claim.
    ///
    /// The interpreter asks only about a VARIADIC declaration, and asks
    /// before [`HostCalls::rc_op`] and [`HostCalls::call`] (WS2.15). A symbol
    /// has one definition, so a variadic declaration of an entry point the
    /// host models at a fixed arity declares a type incompatible with it (a
    /// prototype with an ellipsis is never compatible with one without).
    /// That call is refused as [`InterpretErrorCode::SignatureMismatch`]
    /// ("non-executable vararg signature"), and the host is never asked to
    /// serve it. The refusal names the forgery, where "no host model" would
    /// misreport a modelled symbol as unmodelled. Any other mis-declaration
    /// of a modelled symbol stays the host's `None` and becomes
    /// `UnsupportedCall` (WS2.13).
    fn models_fixed_arity(&self, callee: &Function) -> bool {
        let _ = callee;
        false
    }
}

/// Which reference-counting operation a runtime entry point performs
/// ([`HostCalls::rc_op`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HostRcRole {
    /// `Inst::Retain`: increment the cell's count. Signature `(Ptr) -> ()`.
    Retain,
    /// `Inst::Release`: decrement the cell's count, freeing it at zero.
    /// Signature `(Ptr) -> ()`.
    Release,
    /// `Inst::IsUnique`: whether the count is exactly one. Signature
    /// `(Ptr) -> (T)` with `T` an integer type (`1`/`0`) or `Bool`.
    IsUnique,
}

/// A host's classification of a bodyless declaration as one operation of the
/// reference-counting runtime that owns the cells of `origin`
/// ([`HostCalls::rc_op`], WS2.13).
///
/// The interpreter executes it on its own allocation table and refuses, as
/// [`InterpretErrorCode::UndefinedBehavior`], a pointer that is null, does not
/// address a live allocation, is not at the allocation's base (a runtime
/// object pointer names the object, not a field of it), or addresses a cell
/// that was NOT allocated with `HeapAlloc { origin }` — a `RustHeap` cell or a
/// stack slot handed to `clean_inc` is the "no ownership transfer between
/// heaps" convention violated (`TRUST.md` item 13(c)), and this is the one
/// place it is observable. A declaration whose `sig` is not the shape the
/// role needs is refused as [`InterpretErrorCode::UnsupportedCall`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HostRcOp {
    pub role: HostRcRole,
    /// The `HeapAlloc` origin whose cells this runtime counts.
    pub origin: AllocOrigin,
}

/// One minted runtime handle (WS2.12): its exact identity, the host model that
/// minted it, whether it has been released, and the model's private payload.
struct HostHandle {
    ty: crate::ty::HandleTy,
    owner: String,
    released: bool,
    payload: Box<dyn std::any::Any>,
}

/// Per-execution state a [`HostCalls`] model keeps between calls (WS2.12).
///
/// A fresh `HostState` is created by every [`Interpreter::execute_function`]
/// run and dropped at its end, so there is no state shared across runs and the
/// interpreter's determinism is unaffected (the tables are ordered maps and
/// ids come from a counter).
///
/// # Handles
///
/// A runtime handle ([`Ty::Handle`]) is opaque: only a host creates one
/// ([`HostState::mint_handle`]) or consumes one ([`HostState::handle`],
/// [`HostState::release_handle`]). Three facts close the cross-runtime
/// confusion a bare numeric id would allow:
///
/// 1. ids come from ONE counter shared by every model, so no two handles of
///    one execution share an id, whichever model minted them;
/// 2. the table records each id's exact `HandleTy` and owning model, and every
///    consumer names the `HandleTy` its entry point expects: a handle minted at
///    another runtime is [`InterpretErrorCode::UndefinedBehavior`] ("handle of
///    runtime R1 passed to R2"), as is one minted by another model, one never
///    minted in this execution, one used after its release, and one whose
///    value type was relabelled after minting;
/// 3. the interpreter's call boundary compares every argument's type with the
///    declared parameter type exactly, and a handle value's type is the
///    `HandleTy` it was minted at.
pub struct HostState {
    next_handle_id: u64,
    handles: BTreeMap<u64, HostHandle>,
}

impl core::fmt::Debug for HostState {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let handles: Vec<_> = self
            .handles
            .iter()
            .map(|(id, handle)| (id, &handle.ty, &handle.owner, handle.released))
            .collect();
        f.debug_struct("HostState")
            .field("next_handle_id", &self.next_handle_id)
            .field("handles", &handles)
            .finish()
    }
}

impl HostState {
    fn new() -> Self {
        Self {
            next_handle_id: 0,
            handles: BTreeMap::new(),
        }
    }

    /// Mint a fresh handle of type `ty`, owned by the host model `owner`, with
    /// `payload` as the model's private representation of the runtime object.
    pub fn mint_handle<T: std::any::Any>(
        &mut self,
        ty: crate::ty::HandleTy,
        owner: &str,
        payload: T,
    ) -> InterpretResult<InterpretValue> {
        let id = self.next_handle_id;
        // One id per mint, never reused: when the 64-bit id space is spent
        // (fuel makes that unreachable in practice) minting fails closed
        // rather than wrapping onto a live id.
        self.next_handle_id = self.next_handle_id.checked_add(1).ok_or_else(|| {
            InterpretError::new(
                InterpretErrorCode::OutOfMemory,
                "host handle id space exhausted",
            )
        })?;
        let value = InterpretValue {
            ty: Ty::Handle(Box::new(ty.clone())),
            kind: InterpretValueKind::Handle { id },
        };
        self.handles.insert(
            id,
            HostHandle {
                ty,
                owner: owner.to_owned(),
                released: false,
                payload: Box::new(payload),
            },
        );
        Ok(value)
    }

    /// Resolve `value` as a live handle of type `expected` minted by the model
    /// `requester`, and return that model's payload for it.
    pub fn handle<T: std::any::Any>(
        &self,
        value: &InterpretValue,
        expected: &crate::ty::HandleTy,
        requester: &str,
    ) -> InterpretResult<&T> {
        let (_, handle) = self.resolve(value, expected, requester)?;
        handle.payload.downcast_ref::<T>().ok_or_else(|| {
            InterpretError::new(
                InterpretErrorCode::TypeError,
                format!(
                    "host model {requester}: payload of handle of runtime {} is not the \
                     type this model reads",
                    expected.runtime
                ),
            )
        })
    }

    /// Release the handle `value` (the runtime's `drop`): after this every use
    /// of it, including a second release, is undefined behaviour.
    pub fn release_handle(
        &mut self,
        value: &InterpretValue,
        expected: &crate::ty::HandleTy,
        requester: &str,
    ) -> InterpretResult<()> {
        let (id, _) = self.resolve(value, expected, requester)?;
        let handle = self
            .handles
            .get_mut(&id)
            .expect("resolve returned a recorded handle id");
        handle.released = true;
        Ok(())
    }

    /// How many minted handles are not yet released.
    pub fn live_handles(&self) -> usize {
        self.handles.values().filter(|h| !h.released).count()
    }

    fn resolve(
        &self,
        value: &InterpretValue,
        expected: &crate::ty::HandleTy,
        requester: &str,
    ) -> InterpretResult<(u64, &HostHandle)> {
        let InterpretValueKind::Handle { id } = value.kind else {
            return Err(InterpretError::new(
                InterpretErrorCode::TypeError,
                format!(
                    "host model {requester}: expected a handle of runtime {}, got a {} value",
                    expected.runtime, value.ty
                ),
            ));
        };
        let recorded = self.recorded(id, &value.ty)?;
        if &recorded.ty != expected {
            return Err(InterpretError::new(
                InterpretErrorCode::UndefinedBehavior,
                format!(
                    "handle of runtime {} passed to {} (minted as {}, entry point expects {})",
                    recorded.ty.runtime,
                    expected.runtime,
                    Ty::Handle(Box::new(recorded.ty.clone())),
                    Ty::Handle(Box::new(expected.clone())),
                ),
            ));
        }
        if recorded.owner != requester {
            return Err(InterpretError::new(
                InterpretErrorCode::UndefinedBehavior,
                format!(
                    "handle of runtime {} minted by host model {} passed to host model {requester}",
                    recorded.ty.runtime, recorded.owner
                ),
            ));
        }
        Ok((id, recorded))
    }

    /// The live record of handle `id`, whose value claims type `value_ty`.
    fn recorded(&self, id: u64, value_ty: &Ty) -> InterpretResult<&HostHandle> {
        let Some(recorded) = self.handles.get(&id) else {
            return Err(InterpretError::new(
                InterpretErrorCode::UndefinedBehavior,
                format!("handle #{id} ({value_ty}) was never minted in this execution"),
            ));
        };
        if !matches!(value_ty, Ty::Handle(ty) if **ty == recorded.ty) {
            return Err(InterpretError::new(
                InterpretErrorCode::UndefinedBehavior,
                format!(
                    "handle #{id} is typed {value_ty} but was minted as {}",
                    Ty::Handle(Box::new(recorded.ty.clone()))
                ),
            ));
        }
        if recorded.released {
            return Err(InterpretError::new(
                InterpretErrorCode::UndefinedBehavior,
                format!(
                    "handle #{id} of runtime {} used after release",
                    recorded.ty.runtime
                ),
            ));
        }
        Ok(recorded)
    }
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

impl InterpretPointer {
    /// Is this pointer at offset 0 of the allocation it was derived from —
    /// the OBJECT BASE a runtime object pointer names? The one predicate the
    /// reference-counted operations read (SPEC "An ARC operation counts only
    /// a reference-counted cell", clause 3): the instruction path
    /// (`MemoryState::arc_allocation_mut`, `MemoryState::is_unique`) and the
    /// pinned-runtime host path (`MemoryState::check_rc_cell`) both refuse
    /// any other offset, because the pinned runtime reads its header at the
    /// object base.
    pub(crate) fn is_object_base(self) -> bool {
        self.offset == 0
    }
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
    /// A vector value: its lanes, held like an array's elements
    /// ([`ArrayValue`]) — a vector loaded from a `MemSet` or a stored splat
    /// is one uniform node whatever its lane count, and lane-wise arithmetic
    /// runs on that structure.
    Vector(ArrayValue),
    Aggregate(Vec<InterpretValue>),
    /// An array value: a persistent rope whose uniform and repeating runs are
    /// single nodes ([`ArrayValue`]), so `ArraySplat` / `Constant::Splat` of
    /// any length is O(1) and `InsertElement` never copies the array.
    Array(ArrayValue),
    /// A sequence value, held like an array ([`ArrayValue`]): `InsertElement`
    /// copies one root-to-leaf path and shares the rest, so an insert never
    /// copies the sequence, and the element-wise `SeqMapAddK` / `SeqMapNot`
    /// map each stored value once.
    Sequence(ArrayValue),
    /// A set value: its elements in their constant order, held like a
    /// sequence (no instruction inserts into a set; the shared
    /// representation keeps the two collection kinds one payload type).
    Set(ArrayValue),
    /// A tensor value (PKG-U13a), the runtime image of a
    /// `Ty::Tensor(elem, rank)`, which fixes only the element type and the
    /// rank: the SHAPE is part of the value. Well-formed when `dims` has one
    /// extent per axis (`dims.len() == rank`), each below `2^pointer_bits`,
    /// and `elems` holds exactly `∏ dims` elements, each an `Int` of exactly
    /// `elem`; rank 0 is one element under no extents. Those invariants are
    /// checked where a tensor is CONSUMED (`Inst::TensorContract`'s operand
    /// check, a `TypeError`), and an entry argument's extents are range-checked
    /// on entry. No byte layout: a tensor is never stored to memory.
    Tensor {
        /// The extent of each axis, outermost first.
        dims: Vec<u64>,
        /// The elements in row-major order (last axis fastest), held like an
        /// array's elements ([`ArrayValue`]), so an all-zero contraction
        /// result is one uniform node whatever its count.
        elems: ArrayValue,
    },
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
    /// A binding-frame handle: the result of `Inst::OpenFrame` or of a
    /// functional `Inst::BindSlot`. The handle IS the frame value (Lean
    /// `Value.frame`): `slots` is this handle's own immutable snapshot, so a
    /// `BindSlot` yields a NEW handle with one slot replaced and every older
    /// handle keeps reading its prior contents. `lineage` names the
    /// `OpenFrame` the handle descends from; the interpreter tracks which
    /// lineages are OPEN, and `CloseFrame` through any handle of a lineage
    /// closes all of them. An unbound slot is `None`. Not a storable value:
    /// it is never encoded to or decoded from memory.
    Frame {
        lineage: u64,
        /// `Arc`, not `Rc`: an `InterpretOutcome` / `InterpretError` must stay
        /// `Send` (the `trust-ir run` CLI executes on a worker thread).
        slots: Arc<[Option<InterpretValue>]>,
    },
    /// A PARTIALLY-INITIALIZED scalar image — the copy-propagates-poison value
    /// (LLVM `poison` / Miri "uninitialized bytes"). Produced by a non-strict
    /// (plain, non-atomic, non-volatile) scalar `Load` whose byte range covers
    /// one or more never-written bytes — the classic whole-lane copy of an
    /// aggregate that reads struct-tail padding or an inactive niche-enum
    /// variant's payload (the two triage cases). The vector carries every byte
    /// of the load, `None` for the uninitialized bytes. It is ALSO the value
    /// `Inst::Undef` and a `LoadSlot` of an unbound slot bind at a scalar type
    /// (every byte `None`): `Undef` is poison, never eager UB
    /// (ub-numerics-policy §4, roadmap WS2.10). At a non-scalar type both fail
    /// closed with `UndefinedBehavior` — aggregate poison is not modelled.
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
    /// An opaque runtime handle (WS2.12), typed at the exact
    /// `Ty::Handle(HandleTy)` it was minted at. Only a [`HostCalls`] model
    /// creates one ([`HostState::mint_handle`]); `id` names its row in that
    /// execution's [`HostState`]. It is TRANSPORT-ONLY, the v43 transport set:
    /// `Copy`, `Select`, block arguments, call arguments and returns move it
    /// verbatim. Every other use (arithmetic, comparison, any cast including
    /// the identity `Bitcast`, aggregate insertion, `BindSlot`, `Store`) is a
    /// `TypeError`, and it is never stored to memory,
    /// so there is no in-memory handle image to forge. Never pointer-like.
    Handle {
        id: u64,
    },
    /// Crystal lane (E3b): an UNWRITTEN struct/tuple LANE, the runtime image of `Constant::Uninit`.
    /// `ty` (on the enclosing `InterpretValue`) is the lane's type; there is no payload,
    /// because there is no value.
    ///
    /// It exists ONLY as an element of an `Aggregate` whose own type is a `Ty::Struct` or
    /// `Ty::Tuple`, and nothing ever binds it as an SSA value. `InsertField` replaces it;
    /// `ExtractField` of it is undefined behaviour (MIR's typed read of an uninitialised
    /// place); the enclosing aggregate is transported whole (copy, select arms, block and call
    /// arguments, returns). A `Store` writes its bytes UNINITIALISED and records them as
    /// unwritten-lane bytes, and a whole-aggregate `Load` whose only uninitialised COVERED
    /// bytes (WS2.14's covered-byte mask: padding and an inactive variant's tail are
    /// don't-care) are such recorded lanes gives the lane back unwritten. Anything else that meets it (an
    /// encode for a cast, a standalone use) fails closed. A program with no `Constant::Uninit`
    /// never produces it, so every such program executes exactly as it did before it existed.
    Uninit,
}

impl InterpretValue {
    /// An integer value of `ty`. A pointer-width `ty` (`Isize`/`Usize`) is
    /// sized at the width of the execution running on this thread, and at the
    /// 64-bit reference width outside one; [`Self::int_at`] names the width.
    pub fn int(ty: Ty, value: i128) -> InterpretResult<Self> {
        Self::int_at(ty, value, EXEC_POINTER_BITS.with(core::cell::Cell::get))
    }

    /// An integer value of `ty` with pointer-width integers sized at
    /// `pointer_bits` (WS2.16) — e.g. a wasm32 `usize` is `int_at(Ty::Usize,
    /// v, 32)`. Entry arguments built with [`Self::int`] are re-narrowed to the
    /// target width by `execute_function`, so this is needed only to compare
    /// a result value-for-value.
    pub fn int_at(ty: Ty, value: i128, pointer_bits: u32) -> InterpretResult<Self> {
        let (bits, signed) = int_shape_at(&ty, pointer_bits).ok_or_else(|| {
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

    /// The lanes of a vector value, or `None` for non-vectors.
    pub fn as_vector(&self) -> Option<&ArrayValue> {
        match &self.kind {
            InterpretValueKind::Vector(lanes) => Some(lanes),
            _ => None,
        }
    }
}

/// Deterministic interpreter for the bounded core subset.
#[derive(Clone, Copy)]
pub struct Interpreter<'m> {
    module: Option<&'m Module>,
    /// Borrowed only from an `InterpreterModule` for this exact immutable module.
    module_preflight: Option<&'m std::sync::OnceLock<ModulePreflight>>,
    options: InterpretOptions,
    /// The host model of bodyless declarations (WS2.12); `None` = every call to
    /// a declaration is `UnsupportedCall`.
    host: Option<&'m dyn HostCalls>,
    /// Output-only witness for the format's opposite-signed-zero min/max
    /// choice. `true` means the actual result selected the left operand.
    float_zero_choice_observer: Option<&'m (dyn Fn(bool) + Sync)>,
}

impl core::fmt::Debug for Interpreter<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Interpreter")
            .field("module", &self.module.map(|module| &module.name))
            .field("options", &self.options)
            .field("host", &self.host.map(|_| "<host model>"))
            .field(
                "float_zero_choice_observer",
                &self.float_zero_choice_observer.map(|_| "<choice witness>"),
            )
            .finish()
    }
}

impl<'m> Interpreter<'m> {
    pub fn new() -> Self {
        Self {
            module: None,
            module_preflight: None,
            options: InterpretOptions::default(),
            host: None,
            float_zero_choice_observer: None,
        }
    }

    pub fn with_module(module: &'m Module) -> Self {
        Self {
            module: Some(module),
            module_preflight: None,
            options: InterpretOptions::default(),
            host: None,
            float_zero_choice_observer: None,
        }
    }

    pub fn with_options(mut self, options: InterpretOptions) -> Self {
        self.options = options;
        self
    }

    /// Install a host model of bodyless declarations (WS2.12). See
    /// [`HostCalls`]: a run it serves is host-assisted
    /// ([`InterpretOutcome::host_calls`] > 0), never in-format evidence.
    pub fn with_host(mut self, host: &'m dyn HostCalls) -> Self {
        self.host = Some(host);
        self
    }

    /// Observe the actual choices of successful `FMin`/`FMax` operations
    /// between opposite signed zeros, in execution order, including nested
    /// calls and every logical lane of a completed vector operation.
    /// The observer receives `true` when the result has the left operand's
    /// sign and `false` for the right. Equal-sign zeros and all other inputs
    /// produce no event. The callback does not choose or replace a result.
    /// A failed vector operation produces no events for that instruction.
    ///
    /// A semantic model can replay this witness while also admitting every
    /// other choice the format permits. Ordinary execution installs no
    /// observer and retains the same results, budgets and host-call count.
    pub fn with_float_zero_choice_observer(mut self, observer: &'m (dyn Fn(bool) + Sync)) -> Self {
        self.float_zero_choice_observer = Some(observer);
        self
    }

    fn pointer_bits(&self) -> u32 {
        self.module
            .and_then(|module| module.target_info.as_ref())
            .and_then(|target| target.pointer_size.checked_mul(8))
            .unwrap_or(crate::shape::DEFAULT_POINTER_BITS)
    }

    /// Pointer width in bytes (`pointer_bits / 8`): the size of a `Ptr`, an
    /// `Isize`/`Usize`, and each of a fat pointer's two words (WS2.16).
    fn pointer_bytes(&self) -> u64 {
        u64::from(self.pointer_bits() / 8)
    }

    /// The interpreter's executable byte model is a POINTER-WIDTH-PARAMETRIC
    /// little-endian layout over the canonical scalar table (WS2.16, F-036). A
    /// target-free module selects the 64-bit reference model; an explicit
    /// target must be little-endian, sit in the canonical scalar table
    /// (`Module::target_has_canonical_scalar_layout`), and have 32- or 64-bit
    /// pointers. That admits wasm32 (`pointer_size == 4`) alongside the 64-bit
    /// targets: `Ptr`/`Isize`/`Usize` are `pointer_bits / 8` bytes, addresses
    /// are range-checked to `2^pointer_bits`, fat pointers are two pointer
    /// words, and GEP faults past the address space. A triple plus pointer
    /// width still does not carry enough information to guess i686/AVR scalar
    /// ABI alignment (i686 aligns `i64` to 4), so those modules — and every
    /// big-endian one — stay transportable but not executable here, refused
    /// by name with `UnsupportedMemory`.
    ///
    /// Executability alone is not subset membership. Subsetv5 also selects
    /// the target-indexed Lean model for wasm32; unrelated construct
    /// exclusions remain authoritative (`Module::check_conformance_subset`).
    fn require_reference_execution_layout(&self, block: BlockId) -> InterpretResult<()> {
        let Some(module) = self.module else {
            return Ok(());
        };
        let Some(target) = &module.target_info else {
            return Ok(());
        };
        let pointer_bits = self.pointer_bits();
        if matches!(pointer_bits, 32 | 64)
            && target.endianness == crate::Endianness::Little
            && module.target_has_canonical_scalar_layout()
        {
            Ok(())
        } else {
            Err(err(
                InterpretErrorCode::UnsupportedMemory,
                block,
                format!(
                    "reference execution requires a canonical-scalar-table target with a 32- or \
                     64-bit little-endian layout; got {:?} with {pointer_bits}-bit pointers and \
                     {}-endian byte order",
                    target.triple, target.endianness
                ),
            ))
        }
    }

    /// A fat pointer is two pointer words at the executable target's width.
    /// Every width the executable layout admits (32/64-bit little-endian, see
    /// [`Self::require_reference_execution_layout`]) is a fat-pointer width,
    /// so this is that gate — kept as a named hook so every fat-pointer site
    /// states the dependency.
    fn require_fat_pointer_layout(&self, block: BlockId) -> InterpretResult<()> {
        self.require_reference_execution_layout(block)
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
            (Ty::U32 | Ty::U64, InterpretValueKind::Int(int)) => {
                int_shape(&canonical) == Some((int.bits, int.signed))
            }
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

    /// Keep code words disjoint from every ordinary or observed data allocation.
    /// Uncalled declarations occupy module positions in the code namespace too.
    fn initial_memory(&self, block: BlockId) -> InterpretResult<MemoryState> {
        let pointer_bits = self.pointer_bits();
        // Function pointers occupy symbolic addresses 1..=function_count.
        // Reserve that namespace before globals/stack/heap allocations so a
        // data address can never decode as a registered function pointer.
        let function_count = self
            .module
            .map_or(0, |module| module.functions.len() as u64);
        let first_data_address = function_count
            .checked_add(1)
            .filter(|address| *address <= max_address_for(pointer_bits))
            .ok_or_else(|| {
                invalid_function_pointer(
                    block,
                    "function address namespace exceeds target pointer width",
                )
            })?;
        Ok(MemoryState {
            next_addr: 1024.max(first_data_address),
            max_address: max_address_for(pointer_bits),
            ..MemoryState::default()
        })
    }

    pub fn execute_function(
        &self,
        function: &Function,
        args: impl IntoIterator<Item = InterpretValue>,
    ) -> InterpretResult<InterpretOutcome> {
        // Typed ABI records describe transport that this value interpreter
        // does not implement yet (fresh by-value copies, extension and hidden
        // results). Refuse the entire module before executing any body or host
        // callback, including unused/FnPtr-only typed signatures.
        let preflight = self.module.map_or(ModulePreflight::Ready, |module| {
            self.module_preflight.map_or_else(
                || ModulePreflight::inspect(module),
                |owner| *owner.get_or_init(|| ModulePreflight::inspect(module)),
            )
        });
        if matches!(preflight, ModulePreflight::UnsupportedAbi) {
            return Err(err(
                InterpretErrorCode::UnsupportedCall,
                function.entry,
                "typed signature ABI transport is not implemented by the reference interpreter",
            ));
        }
        if matches!(preflight, ModulePreflight::InvalidStorage) {
            return Err(type_error(
                function.entry,
                "storage-only geometry cannot be a typed value or malformed layout",
            ));
        }
        // The public API also accepts an explicitly supplied Function. It may
        // not borrow the module's policy result for a different body.
        let empty;
        let module = match self.module {
            Some(module) => module,
            None => {
                empty = Module::new("standalone-storage-policy");
                &empty
            }
        };
        let member = module
            .functions
            .get(function.id.as_usize())
            .is_some_and(|candidate| core::ptr::eq(candidate, function));
        if !member {
            let layouts = module.layout_table();
            let mut invalid = false;
            module.visit_function_storage_violations(function, 0, &layouts, |_| invalid = true);
            if invalid {
                return Err(type_error(
                    function.entry,
                    "storage-only type is not a value",
                ));
            }
        }
        self.require_reference_execution_layout(function.entry)?;
        let pointer_bits = self.pointer_bits();
        // Every pointer-width integer minted during this run (`int_shape`) is
        // `pointer_bits` wide; the scope restores the enclosing width on exit.
        let _pointer_width = PointerWidthScope::enter(pointer_bits);
        let memory = self.initial_memory(function.entry)?;
        let mut state = ExecState {
            values: BTreeMap::new(),
            memory,
            globals: BTreeMap::new(),
            frames: BTreeSet::new(),
            next_frame_id: 0,
            steps: 0,
            remaining_fuel: self.options.fuel,
            host: HostState::new(),
            host_calls: 0,
            drop_glue: self.module.map(Module::drop_glue_index),
            unwind: UnwindState::default(),
        };
        let mut args: Vec<InterpretValue> = args.into_iter().collect();
        // An embedder builds an entry argument OUTSIDE the run, where
        // `InterpretValue::int` sizes `Isize`/`Usize` at the 64-bit reference
        // width. Re-express each at this target's pointer width, refusing (by
        // `TypeError`) a value the narrower width cannot represent rather than
        // truncating it.
        // The sparse walk follows stored payloads, including hostile kind/type
        // mismatches. Such a payload cannot introduce Char UB into a declared
        // Char-free entry: it is malformed transport, hence a TypeError. Use
        // the same by-value reach predicate as the source-origin subset.
        let layouts = self.module.map(Module::layout_table);
        let signature = self.module.and_then(|module| module.func_type(function.ty));
        for (index, arg) in args.iter_mut().enumerate() {
            let char_allowed = if let (Some(layouts), Some(signature)) = (&layouts, signature) {
                // A variadic declaration's tail has no fixed formal type.
                // Preserve its existing dynamic carrier/Unicode checks; this
                // is not a Char-free declared-parameter absence claim.
                (function.is_declaration()
                    && signature.is_vararg
                    && index >= signature.params.len())
                    || signature
                        .params
                        .get(index)
                        .is_some_and(|ty| *ty == arg.ty && layouts.type_contains_char_by_value(ty))
            } else {
                // Standalone execution has no nominal declaration authority;
                // retain its existing payload checks, without claiming a
                // module-scoped Char-free entry contract.
                self.module.is_none()
            };
            narrow_pointer_width_ints(arg, pointer_bits, function.entry, char_allowed)?;
        }
        // A handle is minted by a host INSIDE one execution, so none can exist
        // before it starts. Refusing one in the entry arguments keeps an
        // embedder-built `Handle { id }` from aliasing the handle a host later
        // mints under the same id in this run.
        // The TYPE is checked as well as the payload: a non-handle payload
        // typed as a handle passes the type-only signature check and would
        // otherwise be transported (and returned) as if it were one.
        if let Some(forged) = args.iter().find_map(first_handle) {
            let what = match forged.kind {
                InterpretValueKind::Handle { id } => format!("handle #{id}"),
                _ => format!("a {} value with a non-handle payload", forged.ty),
            };
            return Err(ub(
                function.entry,
                format!(
                    "entry argument carries {what}, which was never minted in this execution \
                     (a handle exists only inside the run whose host minted it)"
                ),
            ));
        }
        let returns = if function.is_declaration() {
            // A bodyless ENTRY is a host call too: it has no block 0 to enter,
            // so reporting `MissingBlock` for it would be a structural code on
            // well-formed IR.
            self.check_function_args(function, &args, function.entry)?;
            self.execute_host_call(function.entry, function, args, &mut state)?
        } else {
            self.execute_function_inner(function, args, &mut state, self.options.max_call_depth)?
        };

        Ok(InterpretOutcome {
            returns,
            steps: state.steps,
            host_calls: state.host_calls,
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
                    Step::Unwind { exception, target } => {
                        self.enter_landing_pad(function, block.id, exception, target, state)?;
                        current = target;
                        jumped = true;
                        break;
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
            // Amendment D (`docs/SPEC_RATIFICATIONS.md` §20 rule 3, NORMATIVE): a
            // drop RESOLVES through the module's drop-glue table, and a resolved
            // `drop T, %p` IS `call glue(%p)` -- exactly the `Call` path below
            // (call depth, `MissingFunction`, argument checking: poison or a
            // partial pointer is UB at the boundary, a bodyless glue is a host
            // call or `UnsupportedCall`), yielding no value. Resolution comes
            // FIRST, so an unresolved drop reads nothing. An UNRESOLVED drop
            // states no destructor and is refused (`UnsupportedInstruction`),
            // never run as a no-op: that would interpret a DIFFERENT program, in
            // the direction that invents agreement. The drop has no other
            // effect: it frees nothing and de-initializes nothing (a glue that
            // deallocates makes a second drop UB through the existing rules).
            Inst::Drop { ty, ptr } => {
                let glue = resolve_drop_glue(state, block, "Drop", ty)?;
                let args = eval_args(state, block, std::slice::from_ref(ptr))?;
                let returns = self.execute_direct_call(block, glue, args, state, call_depth)?;
                bind_results(state, block, node, returns)?;
                Ok(Step::Continue)
            }
            // The unwinding twin, exactly as `Invoke` (below): the glue runs as
            // for `Drop`, then control takes the normal edge. Under
            // `PanicStrategy::Abort` `unwind_dest` is never taken; under
            // `Unwind` an unwinding out of the glue enters it (§21).
            Inst::DropInvoke {
                ty,
                ptr,
                normal_dest,
                normal_args,
                unwind_dest,
            } => {
                let glue = resolve_drop_glue(state, block, "DropInvoke", ty)?;
                let args = eval_args(state, block, std::slice::from_ref(ptr))?;
                let returns = match self.execute_direct_call(block, glue, args, state, call_depth) {
                    Ok(returns) => returns,
                    Err(error) => return self.catch_unwinding(state, error, *unwind_dest),
                };
                bind_results(state, block, node, returns)?;
                Ok(Step::Jump {
                    target: *normal_dest,
                    args: eval_args(state, block, normal_args)?,
                })
            }
            Inst::Const { ty, value } => {
                // Crystal lane (E3b): the validator's placement rule, re-checked fail-closed here
                // so an unvalidated module cannot smuggle an unwritten lane anywhere but a direct
                // lane of a struct/tuple aggregate constant.
                check_uninit_lane_placement(ty, value, block)?;
                // v70 (§27 rule C1): a content-addressed tensor is read only
                // as the WHOLE value of a `Const`; `constant_to_value_in`
                // refuses one anywhere else (a lane, a payload, a capture, a
                // global initializer, a switch case).
                let value = match (ty, value) {
                    (Ty::Tensor(elem, rank), Constant::TensorBlob { digest, dims }) => {
                        self.tensor_blob_value(ty, elem, *rank, digest, dims, block)?
                    }
                    _ => self.constant_to_value_in(ty, value, Some(state), block)?,
                };
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
            Inst::Undef { ty } => {
                // `Undef` binds a POISON value (ub-numerics-policy §4, roadmap
                // WS2.10): executing it is not undefined behaviour; INSPECTING
                // the value is, at the true use site (`reject_partial`).
                let poison = self.scalar_poison(ty, block, "undef")?;
                bind_results(state, block, node, [poison])?;
                Ok(Step::Continue)
            }
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
                let result = self.eval_icmp(*op, ty, lhs, rhs, state, block)?;
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
            Inst::MakeAggregate {
                ty,
                variant,
                fields,
            } => {
                let mut lanes = Vec::with_capacity(fields.len());
                for field in fields {
                    lanes.push(state.value(block, *field)?.clone());
                }
                let result = self.eval_make_aggregate(ty, *variant, lanes, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::MakeClosure { ty, func, captures } => {
                let mut values = Vec::with_capacity(captures.len());
                for capture in captures { values.push(state.value(block, *capture)?.clone()); }
                let value = self.eval_make_closure(*ty, *func, values, block)?;
                bind_results(state, block, node, [value])?;
                Ok(Step::Continue)
            }
            // v50: `n` copies of one register value — one uniform node, O(1)
            // in `n`.
            Inst::ArraySplat { ty, value } => {
                let value = state.value(block, *value)?;
                reject_handle(value, block, "ArraySplat")?;
                let result = self.eval_array_splat(ty, value, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            // PKG-U13a: an integer tensor contraction. One node, one fuel unit
            // (the per-node tick in `execute_function_inner`, as SemR's `run`
            // charges one per node), however many elements it materializes.
            Inst::TensorContract {
                ty,
                lhs,
                rhs,
                batch,
                contract,
            } => {
                let lhs = state.value(block, *lhs)?;
                let rhs = state.value(block, *rhs)?;
                let result = self.eval_tensor_contract(ty, lhs, rhs, batch, contract, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            // PKG-U13c: the map, the reduction and the view. One node, one
            // fuel unit each, however many elements they materialize.
            Inst::TensorMap { ty, args, body } => {
                let args = args
                    .iter()
                    .map(|arg| state.value(block, *arg))
                    .collect::<InterpretResult<Vec<_>>>()?;
                let result = self.eval_tensor_map(ty, &args, body, state, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::TensorReduce {
                ty,
                src,
                op,
                axes,
                order,
            } => {
                let src = state.value(block, *src)?;
                let result = self.eval_tensor_reduce(ty, src, *op, axes, *order, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::TensorView {
                ty,
                src,
                params,
                exprs,
                shape,
                index,
                fill,
            } => {
                let src = state.value(block, *src)?;
                let params = params
                    .iter()
                    .map(|param| state.value(block, *param))
                    .collect::<InterpretResult<Vec<_>>>()?;
                let fill = fill.map(|fill| state.value(block, fill)).transpose()?;
                let result = self.eval_tensor_view(
                    ty,
                    src,
                    &params,
                    &tensor_region::ViewFunction {
                        exprs,
                        shape,
                        index,
                    },
                    fill,
                    block,
                )?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            // PKG-U13d: the gather and the scatter. One node, one fuel unit
            // each, however many elements they read or write.
            Inst::TensorGather { ty, data, coords } => {
                let data = state.value(block, *data)?;
                let coords = coords
                    .iter()
                    .map(|coord| state.value(block, *coord))
                    .collect::<InterpretResult<Vec<_>>>()?;
                let result = self.eval_tensor_gather(ty, data, &coords, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::TensorScatter {
                ty,
                init,
                src,
                coords,
            } => {
                let init = state.value(block, *init)?;
                let src = state.value(block, *src)?;
                let coords = coords
                    .iter()
                    .map(|coord| state.value(block, *coord))
                    .collect::<InterpretResult<Vec<_>>>()?;
                let result = self.eval_tensor_scatter(ty, init, src, &coords, block)?;
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
                reject_handle(value, block, "InsertField")?;
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
                reject_handle(value, block, "InsertElement")?;
                let result = self.eval_insert_element(ty, array, index, value, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            Inst::SeqMapAddK { ty, seq, k } => {
                // loopFwd: every element of the sequence is incremented by the constant k
                // (width-preserving wrap). The canonical forward function of `for x in
                // &mut l { *x += k }`; the give-back elaborator OBSERVES this fixed semantics.
                let seq_val = state.value(block, *seq)?;
                let InterpretValueKind::Sequence(elems) = &seq_val.kind else {
                    return Err(type_error(
                        block,
                        format!("seq_map_add_k requires a sequence, got {}", seq_val.ty),
                    ));
                };
                // Element-wise and pure: each STORED value is mapped once, so a
                // uniform run costs one addition whatever its length.
                let mapped = elems.try_map(|e| match &e.kind {
                    InterpretValueKind::Int(i) => {
                        let inc =
                            InterpretInt::from_raw(i.bits, i.signed, i.raw.wrapping_add(u128::from(*k)))
                                .ok_or_else(|| {
                                    type_error(block, "seq_map_add_k: invalid integer width")
                                })?;
                        Ok(InterpretValue {
                            ty: e.ty.clone(),
                            kind: InterpretValueKind::Int(inc),
                        })
                    }
                    _ => Err(type_error(
                        block,
                        "seq_map_add_k requires a sequence of integers",
                    )),
                })?;
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
                let InterpretValueKind::Sequence(elems) = &seq_val.kind else {
                    return Err(type_error(
                        block,
                        format!("seq_map_not requires a sequence, got {}", seq_val.ty),
                    ));
                };
                // Element-wise and pure: each stored value is mapped once.
                let mapped = elems.try_map(|e| match &e.kind {
                    InterpretValueKind::Bool(b) => Ok(InterpretValue {
                        ty: e.ty.clone(),
                        kind: InterpretValueKind::Bool(!*b),
                    }),
                    _ => Err(type_error(
                        block,
                        "seq_map_not requires a sequence of booleans",
                    )),
                })?;
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
                // One call PER ELEMENT, in order: the element function is
                // arbitrary code (it allocates, consumes fuel, may fault), so
                // unlike the fixed maps above it is not mapped once per
                // stored value. Each result lands in the new sequence as it
                // is produced.
                let mapped = ArrayValue::try_from_elements(elems.iter().map(|elem| {
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
                    self.eval_store(&elem_ty, &cell, elem, None, state, block, false)?;
                    // Call fwd(&mut cell) through the standard call machinery
                    // (argument typed as &mut elem so the signature check holds).
                    let arg = InterpretValue {
                        ty: Ty::RefMut(Box::new(elem_ty.clone())),
                        kind: cell.kind.clone(),
                    };
                    self.execute_direct_call(block, *fwd, vec![arg], state, call_depth)?;
                    // Read the mutated element back out of the cell.
                    self.eval_load(&elem_ty, &cell, None, state, block, false)
                }))?;
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
                    // WS2.11: a false assumption is the harness's vacuity
                    // filter — the input lies outside the assumed domain. It
                    // is still an error (UB in the Lean model), but named
                    // apart from program UB so a driver can classify it.
                    Some(false) => Err(err(
                        InterpretErrorCode::AssumeViolated,
                        block,
                        "assume condition evaluated to false: the input lies outside the assumed domain",
                    )),
                    None => Err(type_error(
                        block,
                        format!("assume requires bool, got {}", cond.ty),
                    )),
                }
            }
            Inst::Assert { cond, kind, site } => {
                let cond = state.value(block, *cond)?;
                reject_partial(cond, block, "assert")?;
                match cond.as_bool() {
                    Some(true) => Ok(Step::Continue),
                    // §21 rule 3: under `Unwind` the failure RAISES; the
                    // error travels up the frames as the exception in flight.
                    Some(false) => {
                        let error = assert_panic(state, block, kind, site.as_ref())?;
                        if self.options.panic_strategy == PanicStrategy::Unwind {
                            let exception = raise_exception(state, block, &error)?;
                            state.unwind.in_flight = Some(exception);
                        }
                        Err(error)
                    }
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
                    self.eval_gep(
                    &Ty::I64,
                    &frame_ptr,
                    std::slice::from_ref(&slot_index),
                    &state.memory,
                    block,
                )?;
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
            Inst::CallCannotUnwind { .. } | Inst::CallIndirectCannotUnwind { .. } => {
                Err(InterpretError::new(InterpretErrorCode::UnsupportedInstruction,
                    "Inst::CallCannotUnwind/CallIndirectCannotUnwind: no host-unwind boundary model").with_block(block))
            }
            Inst::Invoke {
                callee,
                args,
                normal_dest,
                normal_args,
                unwind_dest,
            } => {
                // An invoke runs the call exactly like `Inst::Call`: the
                // callee's return values bind the invoke's own `node.results`,
                // and control jumps to `normal_dest` passing `normal_args`.
                // Under `PanicStrategy::Abort` (the default; the panic=abort
                // projection, `docs/ub-numerics-policy.md` §4 "Unwinding") the
                // unwind edge is NEVER taken: a callee that traps (a failed
                // `Assert`, a reached `Unreachable`, any interpreter error)
                // propagates that trap straight out, and that propagation IS
                // the panic=abort semantics. Under `PanicStrategy::Unwind`
                // (§21) an UNWINDING out of the callee, and only that, is
                // caught below and enters `unwind_dest`; every other error
                // propagates as before. A verdict computed under `Abort`
                // covers panic=abort only; `ModuleValidationReport::
                // unwind_surface` names the functions a panic=unwind consumer
                // must not rely on it for.
                let call_args = eval_args(state, block, args)?;
                let returns =
                    match self.execute_direct_call(block, *callee, call_args, state, call_depth) {
                        Ok(returns) => returns,
                        // §21 rule 4: under `Unwind` an unwinding out of the
                        // callee is caught here; no result binds and the
                        // normal-edge arguments are not evaluated.
                        Err(error) => return self.catch_unwinding(state, error, *unwind_dest),
                    };
                bind_results(state, block, node, returns)?;
                let edge_args = eval_args(state, block, normal_args)?;
                Ok(Step::Jump {
                    target: *normal_dest,
                    args: edge_args,
                })
            }
            // Amendment P (wire v54): a sited check with an unwind edge. A
            // passing check jumps to `normal_dest(normal_args)`. Under
            // `PanicStrategy::Abort` (the panic=abort projection, exactly as
            // `Invoke`) a failing one is the terminal sited panic and
            // `unwind_dest` is never taken; under `Unwind` it raises into
            // `unwind_dest` (§21).
            Inst::AssertInvoke {
                cond,
                kind,
                site,
                normal_dest,
                normal_args,
                unwind_dest,
            } => {
                let cond = state.value(block, *cond)?;
                reject_partial(cond, block, "assert")?;
                match cond.as_bool() {
                    Some(true) => Ok(Step::Jump {
                        target: *normal_dest,
                        args: eval_args(state, block, normal_args)?,
                    }),
                    // §21 rules 3-4: under `Unwind` a failing check raises
                    // and is caught by its own unwind edge, in this frame.
                    Some(false) => {
                        let error = assert_panic(state, block, kind, Some(site))?;
                        if self.options.panic_strategy == PanicStrategy::Unwind {
                            let exception = raise_exception(state, block, &error)?;
                            return Ok(Step::Unwind {
                                exception,
                                target: *unwind_dest,
                            });
                        }
                        Err(error)
                    }
                    None => Err(type_error(
                        block,
                        format!("assert requires bool, got {}", cond.ty),
                    )),
                }
            }
            Inst::LandingPad {
                is_cleanup: _,
                catch_type_indices: _,
            } => {
                // §21 rule 5: under `Unwind`, a pad entered by U(e, d) binds
                // the exception and its selector, and clears the hand.
                if self.options.panic_strategy == PanicStrategy::Unwind
                    && let Some((exception, selector)) = state.unwind.in_hand.take()
                {
                    let selector = InterpretValue::int(Ty::I32, i128::from(selector))
                        .map_err(|e| e.with_block(block))?;
                    bind_results(
                        state,
                        block,
                        node,
                        [
                            InterpretValue {
                                ty: Ty::Ptr,
                                kind: InterpretValueKind::Ptr(exception),
                            },
                            selector,
                        ],
                    )?;
                    return Ok(Step::Continue);
                }
                // A landing pad is only entered via an invoke-family unwind edge,
                // which the panic=abort projection never takes (see the `Invoke`
                // arm), and which leaves the exception in hand under `Unwind`
                // (above). Reaching one any other way — a `Br` into a pad block,
                // a pad in the entry block, a pad mid-block — is a module the
                // validator refuses (`MisplacedLandingPad`), and the pad's two
                // results would read registers no unwinder loaded. FAIL CLOSED:
                // fabricating `(null, 0)` for them would fill a missing value
                // and let execution continue as if an exception were in hand.
                Err(err(
                    InterpretErrorCode::UnsupportedInstruction,
                    block,
                    "landingpad entered without an unwind edge (unwinding is not modelled; panic=abort)",
                ))
            }
            // §21 rule 6: under `Unwind`, `Resume` re-raises the exception
            // whose object is at its operand's ADDRESS; any other value is UB.
            Inst::Resume { exn } if self.options.panic_strategy == PanicStrategy::Unwind => {
                let value = state.value(block, *exn)?;
                reject_partial(value, block, "resume")?;
                let not_an_exception = || {
                    ub(
                        block,
                        "resume: the value is not an exception object a landing pad produced",
                    )
                };
                let address = match value.kind {
                    InterpretValueKind::Ptr(pointer) => state
                        .memory
                        .address(pointer, block, "resume")
                        .map_err(|_| not_an_exception())?,
                    InterpretValueKind::DanglingPtr(address) => address,
                    _ => return Err(not_an_exception()),
                };
                let Some((_, error)) = state.unwind.exceptions.get(&address) else {
                    return Err(not_an_exception());
                };
                let error = error.clone();
                state.unwind.in_flight = Some(address);
                Err(error)
            }
            Inst::Resume { exn: _ } => {
                // Under `PanicStrategy::Abort`: `Resume` re-raises an in-flight
                // exception to the host unwinder, and a resume is only
                // reachable after an unwind edge has been taken (which never
                // happens under the panic=abort projection), so it is refused.
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
            // Amendment D, Part 2 (wire v56): `CallIndirect`'s unwinding twin,
            // exactly as `Invoke` (above): the call runs as `CallIndirect`'s,
            // its returns bind this node's results, then control takes the
            // normal edge. Under `PanicStrategy::Abort` `unwind_dest` is never
            // taken; under `Unwind` an unwinding out of the callee enters it.
            Inst::InvokeIndirect {
                callee,
                sig,
                args,
                normal_dest,
                normal_args,
                unwind_dest,
                ..
            } => {
                let callee = state.value(block, *callee)?.clone();
                let args = eval_args(state, block, args)?;
                let returns =
                    match self.execute_indirect_call(block, &callee, *sig, args, state, call_depth)
                    {
                        Ok(returns) => returns,
                        Err(error) => return self.catch_unwinding(state, error, *unwind_dest),
                    };
                bind_results(state, block, node, returns)?;
                Ok(Step::Jump {
                    target: *normal_dest,
                    args: eval_args(state, block, normal_args)?,
                })
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
                // WS2.12: `Store` is outside the handle transport set, so there
                // is never an in-memory handle image to forge.
                reject_handle(&value, block, "Store")?;
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
                origin,
            } => {
                // Single-threaded model: a heap region is allocated like a stack
                // region but WITH a readable usable-size slack tail (see
                // `eval_alloca`'s `heap` path) — the model of `__rust_alloc`'s
                // over-allocation that hashbrown's group scan reads into. The
                // `origin` is RECORDED on the allocation (WS2.13): a pinned
                // RC-runtime host model (`HostCalls::rc_op`) counts only the
                // cells of its own origin, so a cell of another heap handed to
                // it is undefined behaviour here, as it is in the runtime.
                // `Dealloc` reads the same record: freeing a `SwiftHeap` /
                // `CleanHeap` cell is undefined behaviour (`MemoryState::
                // dealloc`), since a reference-counted cell is released by the
                // `Release` that takes its count to zero. So do the ARC
                // instructions: `Retain` / `Release` / `IsUnique` count only a
                // `SwiftHeap` / `CleanHeap` cell, and on a `RustHeap` /
                // `CMalloc` cell (or any non-heap allocation) they are
                // undefined behaviour (`arc_allocation_mut`, `is_unique`).
                // Double-free / use-after-free are already caught by the
                // shared allocator.
                let count = count
                    .map(|count| state.value(block, count).cloned())
                    .transpose()?;
                let result = self.eval_alloca(ty, count.as_ref(), *align, state, block, true)?;
                if let InterpretValueKind::Ptr(ptr) = &result.kind {
                    state.memory.record_origin(*ptr, *origin);
                }
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
                let result = self.eval_gep(pointee_ty, &base, &indices, &state.memory, block)?;
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
            // WS3.20 bulk memory (F-057). Byte-granular; see `eval_mem_copy`
            // / `eval_mem_set` for the value + init-state + provenance rule.
            Inst::MemCopy {
                dst,
                src,
                bytes,
                overlap,
            } => {
                let dst = state.value(block, *dst)?.clone();
                let src = state.value(block, *src)?.clone();
                let bytes = state.value(block, *bytes)?.clone();
                self.eval_mem_copy(&dst, &src, &bytes, *overlap, state, block)?;
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            Inst::MemSet { dst, byte, bytes } => {
                let dst = state.value(block, *dst)?.clone();
                let byte = state.value(block, *byte)?.clone();
                let bytes = state.value(block, *bytes)?.clone();
                self.eval_mem_set(&dst, &byte, &bytes, state, block)?;
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
            // Trust (crystal D3): REFUSED, deliberately, and never stepped as strong. A weak
            // compare-exchange may fail SPURIOUSLY -- report `false` and store nothing even
            // when the loaded value equals `expected` -- so its outcome is not a function of
            // the state. This interpreter is deterministic and has no oracle to choose with;
            // stepping it as strong would execute ONE of its two legal outcomes and call that
            // its semantics, deleting the other, which is the unsound direction. Same
            // discipline, same channel as `Inst::Drop` above, and the Lean executable model
            // refuses it identically (`error:unsupported.weak_cmpxchg`).
            Inst::CmpXchg { weak: true, .. } => Err(type_error(
                block,
                "Inst::CmpXchg weak: a spurious failure is nondeterministic and the reference \
                 interpreter has no oracle",
            )),
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                weak: false,
                ..
            } => {
                let ptr = state.value(block, *ptr)?.clone();
                let expected = state.value(block, *expected)?.clone();
                let desired = state.value(block, *desired)?.clone();
                let current = self.eval_load(ty, &ptr, None, state, block, true)?;
                // The comparison INSPECTS `expected`: a poison `expected` is
                // UB, never a silent "unequal" (roadmap WS2.10 review; Lean
                // `semCmpXchg` mirrors it).
                reject_partial(&expected, block, "cmpxchg expected")?;
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
                // WS2.12: no cast is handle transport, not even the identity
                // `Bitcast` at the handle's own type (which `eval_bitcast`
                // would otherwise pass through verbatim).
                reject_handle(&operand, block, &op.to_string())?;
                let result = self.eval_cast(*op, src_ty, dst_ty, &operand, state, block)?;
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            // Borrow / BorrowMut produce a reference to the pointee place: at
            // runtime a reference IS the pointer's address, so a borrow yields
            // the same pointer value. This sequential reference interpreter does
            // not enforce borrow-checking; it must agree on the runtime value,
            // and the address of `&x`/`&mut x` is the address of `x`. EndBorrow
            // ends the lexical region and has no runtime value. The validator
            // decides borrow STRUCTURE (WS2.7: no `BorrowMut` through a shared
            // reference, `EndBorrow` only of a borrow); borrow LIVENESS (one
            // `EndBorrow` per path, no two live `BorrowMut`, no use after
            // `EndBorrow`) is a producer obligation (TRUST.md item 12), so a
            // module that breaks it can validate and still run here. The one
            // liveness consequence decided at run time is the free (SPEC
            // "Freeing an allocation under a live borrow is undefined
            // behaviour"): a thin borrow of an address inside a live
            // allocation's requested bytes raises that allocation's
            // live-borrow count, an `EndBorrow` naming it lowers it, and only
            // `Dealloc` reads it. No borrow instruction faults on this account.
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                let pointee = state.value(block, *ptr)?.clone();
                // A Borrow over a FAT pointer value is the same pure
                // pass-through as over a thin one: a reborrow of a fat pointer
                // (`&*p` for `p: &str` / `&[T]` / `&dyn Tr`) is the identity
                // on the (data, metadata) pair. The value is passed through
                // VERBATIM — same ty, both lanes untouched. Neither lane is
                // read or re-validated here: a `FatPtr` value is validated at
                // every construction site (`eval_ptr_from_parts` /
                // `decode_leaf`), and this arm constructs nothing.
                let result = if matches!(pointee.kind, InterpretValueKind::FatPtr { .. }) {
                    pointee
                } else {
                    let ptr = expect_pointer(&pointee, block, "Borrow")?;
                    if let Some(live) = state.memory.borrow_count_mut(ptr) {
                        *live = live.saturating_add(1);
                    }
                    InterpretValue {
                        ty: Ty::Ptr,
                        kind: InterpretValueKind::Ptr(ptr),
                    }
                };
                bind_results(state, block, node, [result])?;
                Ok(Step::Continue)
            }
            // Ends one live borrow of the allocation its operand names, by
            // the same rule the borrow counted it (`borrow_count_mut`). It
            // reads the operand through `values.get`, not `value`, so it adds
            // no missing-value fault, and past zero the count stays 0.
            Inst::EndBorrow { borrow_ptr } => {
                let ended = match state.values.get(borrow_ptr) {
                    Some(InterpretValue {
                        kind: InterpretValueKind::Ptr(ptr),
                        ..
                    }) => Some(*ptr),
                    _ => None,
                };
                if let Some(live) = ended.and_then(|p| state.memory.borrow_count_mut(p)) {
                    *live = live.saturating_sub(1);
                }
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
            // ARC reference counting (single-threaded exact counts), defined
            // only on a reference-counted cell — a `HeapAlloc { origin:
            // SwiftHeap | CleanHeap }` result — through a pointer at its
            // object base. On any other live allocation, and at any other
            // offset of the cell, each of the three is undefined behaviour
            // (SPEC "An ARC operation counts only a reference-counted cell";
            // `arc_allocation_mut`).
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
                // Mint a fresh LINEAGE; every slot starts unbound.
                let lineage = state.next_frame_id;
                state.next_frame_id = lineage
                    .checked_add(1)
                    .ok_or_else(|| ub(block, "OpenFrame: frame id overflow"))?;
                state.frames.insert(lineage);
                let slots: Arc<[Option<InterpretValue>]> = vec![None; def.slots.len()].into();
                bind_results(state, block, node, [frame_handle(lineage, slots)])?;
                Ok(Step::Continue)
            }
            Inst::BindSlot {
                frame,
                slot,
                value,
            } => {
                // FUNCTIONAL update (`inst.rs` `Inst::BindSlot` docs; Lean
                // `semBindSlot`, `Semantics/Frame.lean`): the result is a NEW
                // frame handle whose slot `slot` holds `value`, and the input
                // handle stays valid with its PRIOR slot contents. The
                // validator's result table (`bridge.rs` `result_tys`) counts
                // one result for this op, so a builder-emitted node declares
                // one; an in-place write producing nothing was the measured
                // disagreement (a validated, in-subset module could not
                // execute). The new handle stays in the input's LINEAGE, so
                // closing either closes both.
                let (lineage, slots) = expect_open_frame(state, block, *frame, "BindSlot")?;
                let value = state.value(block, *value)?.clone();
                // WS2.12: a frame slot is not in the handle transport set; a
                // bound handle would ride inside a `Frame` value exactly as
                // `InsertField` would put it inside an aggregate.
                reject_handle(&value, block, "BindSlot")?;
                let slot_idx = *slot as usize;
                if slot_idx >= slots.len() {
                    return Err(ub(
                        block,
                        format!("BindSlot: slot {slot} out of range for frame of {} slots", slots.len()),
                    ));
                }
                let mut next = slots.to_vec();
                next[slot_idx] = Some(value);
                bind_results(state, block, node, [frame_handle(lineage, next.into())])?;
                Ok(Step::Continue)
            }
            Inst::LoadSlot { frame, slot, ty } => {
                // Reads the HANDLE'S OWN snapshot: an older handle sees the
                // slots it had, never a later bind made through another one.
                let (_, slots) = expect_open_frame(state, block, *frame, "LoadSlot")?;
                let slot_idx = *slot as usize;
                let value = slots
                    .get(slot_idx)
                    .ok_or_else(|| {
                        ub(
                            block,
                            format!("LoadSlot: slot {slot} out of range for frame of {} slots", slots.len()),
                        )
                    })?
                    .clone();
                // An UNBOUND slot reads as the same scalar poison `Undef`
                // binds (Lean `initFrame` seeds every slot with `.undef`):
                // the read itself is not UB, inspecting the value is.
                let value = match value {
                    Some(value) => value,
                    None => self.scalar_poison(
                        ty,
                        block,
                        &format!("LoadSlot: slot {slot} read before bound: poison"),
                    )?,
                };
                expect_ty(&value, ty, block)?;
                bind_results(state, block, node, [value])?;
                Ok(Step::Continue)
            }
            Inst::CloseFrame { frame } => {
                // Closes the LINEAGE: every handle descending from the same
                // `OpenFrame` is dead afterwards, whichever one was named.
                let (lineage, _) = expect_frame(state.value(block, *frame)?, block)?;
                if !state.frames.remove(&lineage) {
                    return Err(ub(block, "CloseFrame: frame is not open (double close)"));
                }
                bind_results(state, block, node, [])?;
                Ok(Step::Continue)
            }
        }
    }

    /// §21 rule 4, the catch half of an invoke-family terminator: under
    /// `PanicStrategy::Unwind`, an error that IS the exception in flight is
    /// caught and transfers to `unwind_dest`; every other error (and every
    /// error under `Abort`) propagates unchanged.
    fn catch_unwinding(
        &self,
        state: &mut ExecState,
        error: InterpretError,
        unwind_dest: BlockId,
    ) -> InterpretResult<Step> {
        if self.options.panic_strategy == PanicStrategy::Unwind
            && let Some(exception) = state.unwind.in_flight.take()
        {
            return Ok(Step::Unwind {
                exception,
                target: unwind_dest,
            });
        }
        Err(error)
    }

    /// U(e, d) (§21 rule 5): the landing pad heading `target` decides, first
    /// match: a clause other than 0 (a typed catch, or a filter) is refused
    /// (the format has no typeinfo model); a clause 0 (catch-all) puts (e, 1)
    /// in hand; a cleanup pad puts (e, 0) in hand; a pad with neither
    /// re-propagates the same exception out of this frame. The selectors are
    /// trust-cg's convention for functions without typed catches.
    fn enter_landing_pad(
        &self,
        function: &Function,
        block: BlockId,
        exception: u64,
        target: BlockId,
        state: &mut ExecState,
    ) -> InterpretResult<()> {
        let pad = function.block(target).ok_or_else(|| {
            err(
                InterpretErrorCode::MissingBlock,
                block,
                format!("unwind destination {target} not found"),
            )
        })?;
        let Some(Inst::LandingPad {
            is_cleanup,
            catch_type_indices,
        }) = pad.body.first().map(|node| &node.inst)
        else {
            return Err(err(
                InterpretErrorCode::MalformedInstruction,
                block,
                format!("unwind destination {target} does not begin with a landingpad"),
            ));
        };
        let (pointer, raised) = state
            .unwind
            .exceptions
            .get(&exception)
            .cloned()
            .ok_or_else(|| {
                err(
                    InterpretErrorCode::MalformedInstruction,
                    block,
                    "an unwinding carries an exception this run never raised",
                )
            })?;
        if let Some(clause) = catch_type_indices.iter().find(|&&clause| clause != 0) {
            return Err(err(
                InterpretErrorCode::UnsupportedInstruction,
                target,
                format!(
                    "landingpad: a typed catch clause (type index {clause}) needs a typeinfo \
                     model the format does not have"
                ),
            ));
        }
        let selector = if catch_type_indices.contains(&0) {
            1
        } else if *is_cleanup {
            0
        } else {
            // No action: the frame is skipped and the unwinding continues.
            state.unwind.in_flight = Some(exception);
            return Err(raised);
        };
        state.unwind.in_hand = Some((pointer, selector));
        Ok(())
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

    /// Apply a first-class closure value through `Inst::CallIndirect` (G18-2).
    ///
    /// # Why this is not a widening of the `Ty::Func` rule
    ///
    /// `Ty::Closure` used to be INTRODUCTION-ONLY: a closure could be built
    /// (`Const` + per-capture `InsertField`) and projected (`ExtractField`
    /// reads a capture) but never APPLIED, because `execute_indirect_call`
    /// required `Ty::Func` and `ExtractField` deliberately does NOT expose the
    /// `func` lane as a field. The code pointer inside a closure value was
    /// unreachable by construction. This is a SEPARATE arm, reached only when
    /// the callee's declared type is `Ty::Closure`; the `Ty::Func` arm is
    /// untouched and is not consulted here. Every obligation the `Ty::Func` arm
    /// discharges is discharged here too, plus the capture/parameter split.
    ///
    /// # The declared `sig` is the APPARENT signature
    ///
    /// `CallIndirect { callee, sig, args }` over a closure declares the
    /// closure's *apparent* signature — the one a caller sees, i.e.
    /// `ClosureTy.func` — so `args` is checked against it verbatim, by exactly
    /// the rule that already governs a `Ty::Func` edge. The captured
    /// environment is NOT in `args`; this ABI supplies it. Reading `sig` as the
    /// target's PHYSICAL (env-inclusive) signature was considered and rejected:
    /// it would make `args.len() == sig.params.len()` false at every closure
    /// call site, which is precisely the existing arity rule this must not
    /// weaken.
    ///
    /// # The ABI: captures are LEADING arguments, spread, in capture order
    ///
    /// `ClosureTy` models the environment as N explicit typed values —
    /// "captures are explicit values, not an implicit env pointer"
    /// ([`crate::ty::Ty::Closure`]'s own doc, the ty#4145 lesson) — and the
    /// value model has no env object to point at: `InterpretValueKind::Closure`
    /// holds the capture VALUES, not an address. So the faithful application
    /// rule is the spread one: the target function's signature must be
    /// `captures ++ apparent_params -> apparent_returns`. Synthesizing a
    /// one-argument env tuple instead would require minting a `Ty::Tuple` that
    /// appears nowhere in the module — a type the format never stated. A
    /// producer that wants the pointer-env ABI keeps spelling it exactly as it
    /// does today (an explicit env struct plus a `Ty::Func` pointer); this
    /// change does not touch that path.
    fn eval_make_closure(
        &self,
        ty: crate::value::ClosureTyId,
        func: FuncId,
        captures: Vec<InterpretValue>,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let module = self.module_context(block, "MakeClosure")?;
        let closure = module.closure_type(ty).ok_or_else(|| {
            type_error(block, format!("MakeClosure: undefined closure type {ty}"))
        })?;
        let apparent = module.func_type(closure.func).ok_or_else(|| {
            signature_mismatch(block, "MakeClosure: undefined apparent signature")
        })?;
        let target = self.function_pointer_target(module, func, block)?;
        let function = module.function_by_id(target).ok_or_else(|| {
            err(
                InterpretErrorCode::MissingFunction,
                block,
                format!("MakeClosure: undefined function {target}"),
            )
        })?;
        let physical = self
            .function_signature(function, block)?
            .expect("module-backed construction has function type context");
        let params: Vec<Ty> = closure
            .captures
            .iter()
            .chain(&apparent.params)
            .cloned()
            .collect();
        if apparent.is_vararg
            || physical.is_vararg
            || physical.params != params
            || physical.returns != apparent.returns
            || physical.abi != apparent.abi
        {
            return Err(signature_mismatch(
                block,
                "MakeClosure: target signature must be captures followed by apparent parameters, with apparent returns",
            ));
        }
        check_signature_values(block, "MakeClosure captures", &captures, &closure.captures)?;
        for value in &captures {
            reject_handle(value, block, "MakeClosure")?;
        }
        Ok(InterpretValue {
            ty: Ty::Closure(ty),
            kind: InterpretValueKind::Closure { func, captures },
        })
    }

    fn execute_closure_call(
        &self,
        block: BlockId,
        callee: &InterpretValue,
        sig: FuncTyId,
        args: Vec<InterpretValue>,
        state: &mut ExecState,
        call_depth: u64,
    ) -> InterpretResult<Vec<InterpretValue>> {
        ensure_call_depth(block, call_depth)?;
        let module = self.module_context(block, "closure call")?;

        // Re-read the closure type id from the callee's DECLARED type rather
        // than taking it as a parameter: there is exactly one authority for it,
        // so a caller cannot pass a type id that disagrees with the value.
        let Ty::Closure(closure_ty_id) = &callee.ty else {
            return Err(invalid_function_pointer(
                block,
                format!("CallIndirect: callee has non-closure type {}", callee.ty),
            ));
        };
        let closure_ty_id = *closure_ty_id;
        let closure_ty = module.closure_type(closure_ty_id).ok_or_else(|| {
            type_error(
                block,
                format!("CallIndirect: undefined closure type {closure_ty_id}"),
            )
        })?;

        // The edge's declared signature must be the closure type's APPARENT
        // signature, by id — the same strictness the `Ty::Func` arm applies to
        // `value_sig != sig`. A laxer (structural) rule here would make the
        // closure edge weaker than the function-pointer edge it sits beside.
        if closure_ty.func != sig {
            return Err(signature_mismatch(
                block,
                format!(
                    "CallIndirect: closure value has apparent signature functy.{}, call \
                     expects functy.{}",
                    closure_ty.func.0, sig.0
                ),
            ));
        }

        let InterpretValueKind::Closure {
            func: target,
            captures,
        } = &callee.kind
        else {
            return Err(invalid_function_pointer(
                block,
                format!(
                    "CallIndirect: value typed {} is not a closure value",
                    callee.ty
                ),
            ));
        };

        let apparent = module.func_type(sig).ok_or_else(|| {
            signature_mismatch(
                block,
                format!("CallIndirect: undefined function type functy.{}", sig.0),
            )
        })?;
        if apparent.is_vararg {
            // A closure's apparent signature is never variadic in any
            // producer; the capture-spread ABI has no place for a variadic
            // tail, so the edge stays refused by name (WS2.15 opened only the
            // direct and function-pointer edges to a variadic DECLARATION).
            return Err(signature_mismatch(
                block,
                format!(
                    "CallIndirect: closure apparent signature functy.{} is variadic, which \
                     is not executable",
                    sig.0
                ),
            ));
        }

        let target_id = self.function_pointer_target(module, *target, block)?;
        let target_function = module.function_by_id(target_id).ok_or_else(|| {
            err(
                InterpretErrorCode::MissingFunction,
                block,
                format!("CallIndirect: undefined function {target_id}"),
            )
        })?;
        let target_sig = self
            .function_signature(target_function, block)?
            .expect("module-backed call has function type context");

        // The physical contract: captures ++ apparent params -> apparent
        // returns. Checked against the DECLARED closure type's capture list,
        // not against the runtime capture values, so a closure whose value was
        // rebuilt by `InsertField` is held to the same signature.
        let expected_params: Vec<Ty> = closure_ty
            .captures
            .iter()
            .cloned()
            .chain(apparent.params.iter().cloned())
            .collect();
        if target_sig.is_vararg
            || target_sig.params != expected_params
            || target_sig.returns != apparent.returns
        {
            return Err(signature_mismatch(
                block,
                format!(
                    "CallIndirect: closure target {} declares functy.{} ({}) -> ({}), but \
                     closure.{} requires ({}) -> ({}) [{} capture(s) then {} apparent \
                     parameter(s)]",
                    target_id,
                    target_function.ty.0,
                    format_ty_list(&target_sig.params),
                    format_ty_list(&target_sig.returns),
                    closure_ty_id.0,
                    format_ty_list(&expected_params),
                    format_ty_list(&apparent.returns),
                    closure_ty.captures.len(),
                    apparent.params.len(),
                ),
            ));
        }

        // The runtime capture values must still inhabit the declared capture
        // slots. They are typed at materialization and re-typed by
        // `eval_insert_field`, so this is a redundancy — kept because it is the
        // one check that fails closed if either of those paths ever drifts.
        check_signature_values(block, "closure captures", captures, &closure_ty.captures)?;
        check_signature_values(block, "CallIndirect arguments", &args, &apparent.params)?;

        let full_args: Vec<InterpretValue> = captures.iter().cloned().chain(args).collect();
        self.execute_callee(block, target_function, full_args, state, call_depth)
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
        // G18-2: a `Ty::Closure` callee is applied by `execute_closure_call`,
        // which supplies the captured environment as leading arguments. The
        // `Ty::Func` rule below is reached only for a non-closure callee and is
        // unchanged.
        if matches!(&callee.ty, Ty::Closure(_)) {
            return self.execute_closure_call(block, callee, sig, args, state, call_depth);
        }
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
        // WS2.15: variadicity is part of the signature the pointer must
        // agree on, exactly like the parameter and return lists (before this
        // any vararg edge was refused outright).
        if callee_sig.is_vararg != expected_sig.is_vararg
            || expected_sig.params != callee_sig.params
            || expected_sig.returns != callee_sig.returns
            || expected_sig.abi != callee_sig.abi
        {
            // Name the variadicity disagreement when that is the (only new)
            // reason, so a pointer type that adds or drops a variadic tail
            // is refused BY NAME rather than as an anonymous mismatch.
            let why = if callee_sig.is_vararg != expected_sig.is_vararg {
                format!(
                    " (pointer signature functy.{} is {}, callee functy.{} is {})",
                    sig.0,
                    if expected_sig.is_vararg {
                        "variadic"
                    } else {
                        "not variadic"
                    },
                    callee_function.ty.0,
                    if callee_sig.is_vararg {
                        "variadic"
                    } else {
                        "not variadic"
                    },
                )
            } else {
                String::new()
            };
            return Err(signature_mismatch(
                block,
                format!(
                    "CallIndirect: indirect call signature mismatch for function {callee_id}{why}"
                ),
            ));
        }

        if expected_sig.is_vararg {
            // The same two-way rule as a direct call (`check_function_args`):
            // a variadic declaration is a host call with the full argument
            // list, a variadic definition is refused by name.
            if !callee_function.is_declaration() {
                return Err(signature_mismatch(
                    block,
                    format!(
                        "CallIndirect: function {callee_id} has non-executable vararg \
                         signature: it is a variadic DEFINITION, and no instruction reads a \
                         variadic argument (LIMITATIONS.md)"
                    ),
                ));
            }
            check_vararg_declaration_args(block, &args, &expected_sig.params)?;
        } else {
            check_signature_values(block, "CallIndirect arguments", &args, &expected_sig.params)?;
        }
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
        if callee.is_declaration() {
            // Every caller (direct, indirect, closure, `Invoke`, `SeqMap`) has
            // already checked `args` against the callee's signature.
            return self.execute_host_call(block, callee, args, state);
        }

        let caller_values = std::mem::take(&mut state.values);
        let result = self.execute_function_inner(callee, args, state, call_depth - 1);
        state.values = caller_values;
        result
    }

    /// Execute a call to the bodyless declaration `callee` through the host
    /// model (WS2.12), or refuse it with `UnsupportedCall`.
    fn execute_host_call(
        &self,
        block: BlockId,
        callee: &Function,
        args: Vec<InterpretValue>,
        state: &mut ExecState,
    ) -> InterpretResult<Vec<InterpretValue>> {
        let no_host_model = || {
            err(
                InterpretErrorCode::UnsupportedCall,
                block,
                format!(
                    "{BODYLESS_CALL_PREFIX}{}{NO_HOST_MODEL_SUFFIX}",
                    callee.name
                ),
            )
        };
        let Some(host) = self.host else {
            return Err(no_host_model());
        };
        // The declared signature is what a host's results are checked
        // against; without a module there is none, so nothing a host returned
        // could be checked. Refuse before the host runs.
        let Some(sig) = self.function_signature(callee, block)? else {
            return Err(err(
                InterpretErrorCode::UnsupportedCall,
                block,
                format!(
                    "{BODYLESS_CALL_PREFIX}{}: a host call needs the module's declared \
                     signature to check the host's results",
                    callee.name
                ),
            ));
        };
        // WS2.15 x WS2.13: a variadic declaration is a host call only at its
        // variadic signature. When the host models this symbol at a FIXED
        // arity, the declaration has the wrong type for the entry point. It
        // is refused by name, before the host is asked to serve it
        // (`HostCalls::models_fixed_arity`). "No host model" would be wrong
        // here, because the host does model the symbol.
        if sig.is_vararg && host.models_fixed_arity(callee) {
            return Err(signature_mismatch(
                block,
                format!(
                    "{BODYLESS_CALL_PREFIX}{name}: non-executable vararg signature {sig}: the \
                     installed host models @{name} as a fixed-arity entry point, and a variadic \
                     declaration of it is not that entry point's type",
                    name = callee.name,
                    sig = format_sig(sig),
                ),
            ));
        }
        // A reference-counting entry point is executed HERE, on the
        // interpreter's own refcounts (`HostCalls::rc_op`): the host names the
        // runtime, and never sees the pointer.
        if let Some(op) = host.rc_op(callee, sig) {
            state.host_calls += 1;
            let returns = self.execute_host_rc_op(block, callee, sig, op, &args, state)?;
            self.check_function_returns(callee, &returns, block)?;
            return Ok(returns);
        }
        let Some(result) = host.call(callee, sig, &args, &mut state.host) else {
            return Err(no_host_model());
        };
        state.host_calls += 1;
        // A host's error is the HOST's claim, not a verdict about the module,
        // and the error path carries no `host_calls` count, so the message
        // names the model it came from.
        let returns = result.map_err(|mut error| {
            error.message = format!("host model for @{}: {}", callee.name, error.message);
            if error.block.is_none() {
                error.with_block(block)
            } else {
                error
            }
        })?;
        // A buggy host cannot smuggle an ill-typed value: first the declared
        // types (SignatureMismatch), then each value's own well-formedness.
        self.check_function_returns(callee, &returns, block)?;
        for (index, value) in returns.iter().enumerate() {
            check_host_result(value, &sig.returns[index], &state.host, block, index)?;
        }
        Ok(returns)
    }

    /// Execute the reference-counting operation a host classified `callee`
    /// as (WS2.13) on the interpreter's own allocation table. The declared
    /// signature must be the shape the role needs (`UnsupportedCall`
    /// otherwise), and the pointer must address a live cell of the runtime's
    /// origin at its base (`UndefinedBehavior` otherwise) — see [`HostRcOp`].
    fn execute_host_rc_op(
        &self,
        block: BlockId,
        callee: &Function,
        sig: &FuncTy,
        op: HostRcOp,
        args: &[InterpretValue],
        state: &mut ExecState,
    ) -> InterpretResult<Vec<InterpretValue>> {
        let name = &callee.name;
        let shape_ok = sig.params.as_slice() == [Ty::Ptr]
            && !sig.is_vararg
            && match op.role {
                HostRcRole::Retain | HostRcRole::Release => sig.returns.is_empty(),
                HostRcRole::IsUnique => matches!(
                    sig.returns.as_slice(),
                    [ty] if *ty == Ty::Bool || int_shape(ty).is_some()
                ),
            };
        if !shape_ok {
            return Err(err(
                InterpretErrorCode::UnsupportedCall,
                block,
                format!(
                    "{BODYLESS_CALL_PREFIX}{name}: the host names it the {:?} entry point of the \
                     {:?} reference-counting runtime, but its declared signature {} is not that \
                     entry point's shape",
                    op.role,
                    op.origin,
                    format_sig(sig)
                ),
            ));
        }
        let [arg] = args else {
            return Err(signature_mismatch(
                block,
                format!("host RC call @{name}: expected exactly one argument"),
            ));
        };
        let ptr = match &arg.kind {
            InterpretValueKind::Ptr(ptr) => *ptr,
            InterpretValueKind::NullPtr => {
                return Err(ub(block, format!("@{name}: null object pointer")));
            }
            other => {
                return Err(type_error(
                    block,
                    format!("@{name}: expected a pointer argument, got {other:?}"),
                ));
            }
        };
        state.memory.check_rc_cell(ptr, op.origin, name, block)?;
        Ok(match op.role {
            HostRcRole::Retain => {
                state.memory.retain(ptr, block)?;
                Vec::new()
            }
            HostRcRole::Release => {
                state.memory.release(ptr, block)?;
                Vec::new()
            }
            HostRcRole::IsUnique => {
                let unique = state.memory.is_unique(ptr, block)?;
                let ty = &sig.returns[0];
                vec![if *ty == Ty::Bool {
                    InterpretValue::bool(unique)
                } else {
                    InterpretValue::int(ty.clone(), i128::from(unique))
                        .map_err(|error| error.with_block(block))?
                }]
            }
        })
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
            // WS2.15: a variadic DECLARATION (`printf`) is a host call with
            // the full argument list — the host model reads the variadic
            // tail. A variadic DEFINITION stays refused, by name: no
            // instruction reads a variadic argument (`va_arg` has no
            // spelling), so a body could not observe the tail it was passed
            // and executing it would be executing a different function
            // (`LIMITATIONS.md`, ratified out of scope).
            if !function.is_declaration() {
                return Err(signature_mismatch(
                    block,
                    format!(
                        "function {} has non-executable vararg signature: it is a variadic \
                         DEFINITION, and no instruction reads a variadic argument \
                         (LIMITATIONS.md)",
                        function.id.0
                    ),
                ));
            }
            return check_vararg_declaration_args(block, args, &sig.params);
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

    /// [`Self::constant_to_value_in`] with no execution state: a constant that
    /// needs one (a WS3.8 symbol address) fails closed.
    fn constant_to_value(
        &self,
        ty: &Ty,
        value: &Constant,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        self.constant_to_value_in(ty, value, None, block)
    }

    /// Convert a constant to a runtime value. `state` is the execution state a
    /// WS3.8 non-null pointer constant resolves its global in; `None` (a
    /// `Switch` case) refuses one.
    fn constant_to_value_in(
        &self,
        ty: &Ty,
        value: &Constant,
        mut state: Option<&mut ExecState>,
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
            // unsound step. (WS3.8's `SymbolAddr` arms below, at typed
            // references and `str`/slice fat pointers, leave that refusal in
            // place: they resolve a MODULE global the validator already
            // pinned, and there is still no `(Ty::Ptr, SymbolAddr)` arm.)
            // Every observation channel for a null is LOUD: a
            // deref faults in `expect_pointer`, and a returned `NullPtr`
            // against the oracle's `Ptr(..)` is a cross-kind pair reported as
            // a real divergence. A placeholder that is silently wrong is the
            // hazard; this one cannot be silently anything.
            (Ty::Ptr, Constant::Int(0)) => Ok(InterpretValue {
                ty: Ty::Ptr,
                kind: InterpretValueKind::NullPtr,
            }),
            // Trust (wave-FS): the NULL FAT POINTER — the `Ty::FatPtr` twin of the
            // `(Ty::Ptr, Constant::Int(0))` arm directly above, and admitted on the same
            // ZERO-ONLY terms. `(data, metadata)` are both the integer zero: the data word is
            // a `NullPtr` exactly as the thin arm produces, and the metadata word is the zero
            // of the kind's metadata type (a zero length for `Slice`/`Str`/`ContainerLen`, a
            // null vtable for `TraitObject`/`ContainerVtable`). A NONZERO data word would
            // fabricate an address with no provenance and stays a type error, which is the
            // whole reason the thin arm is zero-only too.
            //
            // WHY IT IS NEEDED: `Inst::Const` is the only way to ORIGINATE an aggregate, so a
            // `&str` / `&[T]` / `&dyn Tr` leaf inside an aggregate seed had no representable
            // originator at all — before this arm neither authority had a `Ty::FatPtr` case
            // (`shape_matches_ty` has one now; the `(_, PhantomData)` wildcard below was never
            // an escape, because that function's `PhantomData` arm is `Ty::Unit`-only). The
            // producer seeds such a field only where the seed is provably OVERWRITTEN before
            // any read, so the null never denotes a live reference.
            (Ty::FatPtr(kind), Constant::Aggregate(elems))
                if matches!(elems.as_slice(), [Constant::Int(0), Constant::Int(0)]) =>
            {
                // The metadata word is the ZERO OF ITS OWN TYPE, which is not always an
                // integer: `Slice`/`Str`/`ContainerLen` carry a pointer-sized unsigned LENGTH,
                // while `TraitObject` and `ContainerVtable` carry a thin VTABLE POINTER
                // (`Ty::Ptr`). A null vtable is the honest zero there; writing an integer 0 into
                // it would be a type confusion. `metadata_ty` returning `None` means the kind has
                // no representable metadata type at this pointer width, and that FAILS CLOSED
                // rather than guessing a width.
                let Some(metadata_ty) = kind.metadata_ty(self.pointer_bits()) else {
                    return Err(type_error(
                        block,
                        "fat-pointer constant: the pointer kind has no representable metadata \
                         type at this pointer width",
                    ));
                };
                let metadata = match metadata_ty {
                    Ty::Ptr => InterpretValue {
                        ty: Ty::Ptr,
                        kind: InterpretValueKind::NullPtr,
                    },
                    int_ty => InterpretValue::int(int_ty, 0)?,
                };
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::FatPtr {
                        data: Box::new(InterpretValue {
                            ty: Ty::Ptr,
                            kind: InterpretValueKind::NullPtr,
                        }),
                        metadata: Box::new(metadata),
                    },
                })
            }
            // WS3.8 (F-049): a NON-NULL typed-reference constant — the address
            // of one module global. The value is a real pointer into the
            // global's own allocation (provenance kept, never a bare integer),
            // so a deref reads the global's initialized bytes. The validator
            // owns the admission rule (`PointerConstantRefused`); this arm
            // re-checks only what it needs to never fabricate an address:
            // one global of that name, not thread-local, window in bounds.
            (
                Ty::Ref(_) | Ty::PtrConst(_) | Ty::PtrMut(_),
                Constant::SymbolAddr { symbol, addend },
            ) => {
                let pointer = self.symbol_pointer(symbol, *addend, 0, state, block)?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Ptr(pointer),
                })
            }
            // WS3.8 (F-049): a NON-NULL `&str` / `&[T]` constant — the data word
            // points `addend` bytes into one module global, the metadata word
            // is the element count. Other fat kinds keep the null pair only.
            (
                Ty::FatPtr(kind @ (FatPtrKind::Str | FatPtrKind::Slice(_))),
                Constant::Aggregate(elems),
            ) if matches!(
                elems.as_slice(),
                [Constant::SymbolAddr { .. }, Constant::Int(_)]
            ) =>
            {
                let [
                    Constant::SymbolAddr { symbol, addend },
                    Constant::Int(length),
                ] = elems.as_slice()
                else {
                    return Err(type_error(
                        block,
                        "fat-pointer constant: expected [symaddr, int]",
                    ));
                };
                let count = u64::try_from(*length).map_err(|_| {
                    type_error(
                        block,
                        format!("fat-pointer constant: negative length {length}"),
                    )
                })?;
                let element_size = match kind {
                    FatPtrKind::Slice(element) => {
                        let element = self.resolve_ty(*element, block)?;
                        self.byte_size(&element, block)?
                    }
                    _ => 1,
                };
                let extent = count.checked_mul(element_size).ok_or_else(|| {
                    type_error(block, "fat-pointer constant: window size overflows")
                })?;
                let pointer = self.symbol_pointer(symbol, *addend, extent, state, block)?;
                let Some(metadata_ty) = kind.metadata_ty(self.pointer_bits()) else {
                    return Err(type_error(
                        block,
                        "fat-pointer constant: the pointer kind has no representable metadata \
                         type at this pointer width",
                    ));
                };
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::FatPtr {
                        data: Box::new(InterpretValue {
                            ty: Ty::Ptr,
                            kind: InterpretValueKind::Ptr(pointer),
                        }),
                        metadata: Box::new(
                            InterpretValue::int(metadata_ty, i128::from(count))
                                .map_err(|e| e.with_block(block))?,
                        ),
                    },
                })
            }
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
                if !matches!(
                    elem_ty.as_ref(),
                    Ty::Bool
                        | Ty::I8
                        | Ty::I16
                        | Ty::I32
                        | Ty::I64
                        | Ty::U8
                        | Ty::U16
                        | Ty::U32
                        | Ty::U64
                        | Ty::F16
                        | Ty::F32
                        | Ty::F64
                ) {
                    return Err(type_error(
                        block,
                        "vector constant requires an admitted scalar lane type",
                    ));
                }
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
                let lanes =
                    ArrayValue::try_from_elements(values.iter().map(|v| {
                        self.constant_to_value_in(elem_ty, v, state.as_deref_mut(), block)
                    }))?;
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
                    .map(|(ty, value)| {
                        self.lane_constant_to_value_in(ty, value, state.as_deref_mut(), block)
                    })
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
                    .map(|(field, value)| {
                        self.lane_constant_to_value_in(
                            &field.ty,
                            value,
                            state.as_deref_mut(),
                            block,
                        )
                    })
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
            // tag type, and the tag extracts positionally as field 0. A
            // register value needs no byte layout: even an inactive variant
            // may carry sequences or other types without a byte image.
            (Ty::Enum(_), Constant::Aggregate(values)) => {
                let shape = self.enum_register_shape(ty, block)?;
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
                let variant_idx = shape.variant_by_discriminant(*disc).ok_or_else(|| {
                    type_error(
                        block,
                        format!("discriminant {disc} does not name a variant of {ty}"),
                    )
                })?;
                // WS3.14: the validator refuses this as
                // `UninhabitedVariantConstructed`; an unvalidated module fails
                // closed here too.
                shape.refuse_uninhabited(variant_idx, ty, "Const", block)?;
                let fields = &shape.definition.variants[variant_idx].fields;
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
                    InterpretValue::int(shape.tag_ty.clone(), *disc)
                        .map_err(|e| e.with_block(block))?,
                );
                for (field_ty, value) in fields.iter().zip(field_consts) {
                    converted.push(self.constant_to_value_in(
                        field_ty,
                        value,
                        state.as_deref_mut(),
                        block,
                    )?);
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
                let values = ArrayValue::try_from_elements(
                    data.iter().map(|b| InterpretValue::int(Ty::U8, *b as i128)),
                )?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Array(values),
                })
            }
            // v50 Splat: `len` copies of ONE converted element — a single
            // uniform node, O(1) in `len`. The element is converted (and so
            // type-checked) once, exactly as the validator checks it once.
            (
                Ty::Array(elem, len),
                Constant::Splat {
                    elem: value,
                    len: count,
                },
            ) => {
                if count != len {
                    return Err(type_error(
                        block,
                        format!(
                            "splat constant has {count} elements, declared type requires {len}"
                        ),
                    ));
                }
                let elem_ty = self.resolve_ty(*elem, block)?;
                let value =
                    self.constant_to_value_in(&elem_ty, value, state.as_deref_mut(), block)?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Array(ArrayValue::splat(value, *len)),
                })
            }
            // The legacy Aggregate spelling at an array type has the same
            // element/length contract as Array (validator and §3.1). Keep
            // strict element conversion: this is not a struct/tuple lane
            // context and does not admit an Uninit element.
            (Ty::Array(elem, len), Constant::Array(values) | Constant::Aggregate(values)) => {
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
                let values = ArrayValue::try_from_elements(values.iter().map(|value| {
                    self.constant_to_value_in(&elem_ty, value, state.as_deref_mut(), block)
                }))?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Array(values),
                })
            }
            (Ty::Sequence(elem), Constant::Sequence(values)) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                let values = ArrayValue::try_from_elements(values.iter().map(|value| {
                    self.constant_to_value_in(&elem_ty, value, state.as_deref_mut(), block)
                }))?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Sequence(values),
                })
            }
            (Ty::Set(elem, _), Constant::Set(values)) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                let values = ArrayValue::try_from_elements(values.iter().map(|value| {
                    self.constant_to_value_in(&elem_ty, value, state.as_deref_mut(), block)
                }))?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Set(values),
                })
            }
            // The validator also admits the legacy positional Aggregate
            // spelling. Resolve field types and names from the declaration,
            // yielding the same record value as a named Record constant.
            (Ty::Record(record_id), Constant::Aggregate(fields)) => {
                let module = self.module.ok_or_else(|| {
                    type_error(block, "record constants require module type context")
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
                let values = record
                    .fields
                    .iter()
                    .zip(fields)
                    .map(|(field, value)| {
                        Ok((
                            field.name.clone(),
                            self.constant_to_value_in(
                                &field.ty,
                                value,
                                state.as_deref_mut(),
                                block,
                            )?,
                        ))
                    })
                    .collect::<InterpretResult<Vec<_>>>()?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Record(values),
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
                let mut names = std::collections::BTreeSet::new();
                for (name, value) in fields {
                    if !names.insert(name.as_str()) {
                        return Err(type_error(
                            block,
                            format!("record field {name} is duplicated"),
                        ));
                    }
                    let field = record
                        .fields
                        .iter()
                        .find(|field| field.name == *name)
                        .ok_or_else(|| {
                            type_error(block, format!("record field {name} not declared"))
                        })?;
                    values.push((
                        name.clone(),
                        self.constant_to_value_in(&field.ty, value, state.as_deref_mut(), block)?,
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
                    .map(|(ty, value)| {
                        self.constant_to_value_in(ty, value, state.as_deref_mut(), block)
                    })
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
            // encodable by `Store` and round-trips through memory. This is
            // the only admitted type: a generic marker would let a malformed,
            // unused constant bypass the validator's Unit-only shape rule.
            (Ty::Unit, Constant::PhantomData) => Ok(InterpretValue {
                ty: Ty::Unit,
                kind: InterpretValueKind::Unit,
            }),
            // v70 (PKG-U13e, SPEC_RATIFICATIONS §27 rule C1): a
            // content-addressed tensor is read only as the whole value of an
            // `Inst::Const` (`execute_inst` reads it there, before this
            // walk), so every blob this walk reaches is misplaced.
            (_, Constant::TensorBlob { .. }) => Err(type_error(
                block,
                "misplaced tensor blob constant: a content-addressed tensor stands only as \
                 the whole value of a Const"
                    .to_string(),
            )),
            _ => Err(type_error(
                block,
                format!("constant {value:?} does not match declared type {ty}"),
            )),
        }
    }

    /// The tensor a `Constant::TensorBlob` names (PKG-U13e, §27), checked in
    /// the one order SemR's `blobVal` checks it, each failure a `TypeError`
    /// (the constant is not a value of its type): an integer element; one
    /// extent per axis, each below `2^pointer_bits`; a row for the digest;
    /// bytes that hash to the digest; exactly `∏ dims × width/8` bytes (so
    /// the element count is below `2^pointer_bits` too). The elements are
    /// the bytes read little-endian at the element's width, row-major.
    fn tensor_blob_value(
        &self,
        ty: &Ty,
        elem: &Ty,
        rank: u32,
        digest: &crate::blob::BlobDigest,
        dims: &[u64],
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let pointer_bits = self.pointer_bits();
        let Some((bits, signed)) = int_shape_at(elem, pointer_bits) else {
            return Err(type_error(
                block,
                format!("tensor blob constant: element type {elem} has no integer shape"),
            ));
        };
        if dims.len() as u64 != u64::from(rank) {
            return Err(type_error(
                block,
                format!(
                    "tensor blob constant: {} extents, but its type {ty} has rank {rank}",
                    dims.len()
                ),
            ));
        }
        let usize_limit = 1u128.checked_shl(pointer_bits).unwrap_or(u128::MAX);
        if let Some(dim) = dims.iter().find(|dim| u128::from(**dim) >= usize_limit) {
            return Err(type_error(
                block,
                format!(
                    "tensor blob constant: extent {dim} does not fit the target's \
                     {pointer_bits}-bit usize"
                ),
            ));
        }
        let Some(row) = self.module.and_then(|module| module.blob(digest)) else {
            return Err(type_error(
                block,
                format!("tensor blob constant: the module holds no blob {digest}"),
            ));
        };
        if !row.digest_matches() {
            return Err(type_error(
                block,
                format!("tensor blob constant: the bytes of blob {digest} do not hash to it"),
            ));
        }
        let width = u128::from(bits / 8);
        let count = exact_product_below(dims, usize_limit);
        if count.and_then(|count| u128::from(count).checked_mul(width))
            != Some(row.data.len() as u128)
        {
            return Err(type_error(
                block,
                format!(
                    "tensor blob constant: blob {digest} holds {} bytes, not {dims:?} \
                     elements of {elem}",
                    row.data.len()
                ),
            ));
        }
        let elems =
            ArrayValue::try_from_elements(row.data.chunks_exact(width as usize).map(|chunk| {
                let raw = chunk
                    .iter()
                    .rev()
                    .fold(0u128, |acc, byte| (acc << 8) | u128::from(*byte));
                InterpretInt::from_raw(bits, signed, raw)
                    .map(|int| InterpretValue {
                        ty: elem.clone(),
                        kind: InterpretValueKind::Int(int),
                    })
                    .ok_or_else(|| {
                        type_error(
                            block,
                            format!("tensor blob constant: element type {elem} has no width"),
                        )
                    })
            }))?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Tensor {
                dims: dims.to_vec(),
                elems,
            },
        })
    }

    /// One LANE of a struct/tuple aggregate constant (crystal lane, E3b): an unwritten lane
    /// (`Constant::Uninit`) becomes `InterpretValueKind::Uninit` at the lane's declared type,
    /// and every other lane converts exactly as `constant_to_value_in` always converted it.
    /// Only the two struct/tuple arms call this, so `Constant::Uninit` anywhere else still
    /// reaches `constant_to_value_in`'s type-error catch-all.
    fn lane_constant_to_value_in(
        &self,
        lane_ty: &Ty,
        lane: &Constant,
        state: Option<&mut ExecState>,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        match lane {
            Constant::Uninit => Ok(InterpretValue {
                ty: lane_ty.clone(),
                kind: InterpretValueKind::Uninit,
            }),
            other => self.constant_to_value_in(lane_ty, other, state, block),
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

    /// WS3.8: the pointer a `SymbolAddr { symbol, addend }` pointer constant
    /// denotes — `addend` bytes into the allocation of the ONE module global
    /// named `symbol`, with `extent` further bytes that must stay inside it.
    /// Fails closed without execution state, on a missing, repeated or
    /// thread-local global, and on an out-of-bounds window.
    fn symbol_pointer(
        &self,
        symbol: &str,
        addend: i64,
        extent: u64,
        state: Option<&mut ExecState>,
        block: BlockId,
    ) -> InterpretResult<InterpretPointer> {
        let Some(state) = state else {
            return Err(type_error(
                block,
                format!("symaddr<{symbol}>: a pointer constant needs execution state"),
            ));
        };
        let module = self.module_context(block, "a pointer constant")?;
        let mut named = module
            .globals
            .iter()
            .enumerate()
            .filter(|(_, global)| global.name == symbol);
        let (Some((index, global)), None) = (named.next(), named.next()) else {
            return Err(type_error(
                block,
                format!("symaddr<{symbol}>: does not name exactly one module global"),
            ));
        };
        if global.tls.is_some() {
            return Err(type_error(
                block,
                format!("symaddr<{symbol}>: a thread-local global has no constant address"),
            ));
        }
        let size = self.byte_size(&global.ty, block)?;
        let offset = u64::try_from(addend)
            .ok()
            .filter(|offset| offset.checked_add(extent).is_some_and(|end| end <= size))
            .ok_or_else(|| {
                type_error(
                    block,
                    format!(
                        "symaddr<{symbol} + {addend}>: a {extent}-byte window does not fit the \
                         {size}-byte global"
                    ),
                )
            })?;
        let index = u32::try_from(index)
            .map_err(|_| type_error(block, "global index exceeds the id space"))?;
        let base = self.global_pointer(GlobalId::new(index), state, block)?;
        Ok(InterpretPointer {
            allocation: base.allocation,
            offset: base.offset + offset,
        })
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
        // Cached BEFORE the initializer is evaluated: a WS3.8 pointer constant
        // in it may take this global's own address (or reach it through a
        // cycle of globals), and must see this allocation, not allocate again.
        state.globals.insert(global, pointer);
        if let Some(init) = &def.initializer {
            // Crystal lane (E3b): a global's bytes are its initializer; an unwritten lane has
            // no bytes to give it (trust-ir-build refuses the placement too).
            if constant_mentions_uninit(init) {
                return Err(type_error(
                    block,
                    "GlobalAddr: a global initializer cannot carry an unwritten lane (uninit)",
                ));
            }
            let value = self.constant_to_value_in(&def.ty, init, Some(state), block)?;
            // A global's image is loaded from the object file, where padding
            // is ZERO, not uninitialized: the compact image's uncovered bytes
            // become defined zeros (structurally — a splat initializer of any
            // length stays one run).
            let image = self.encode_image(&value, state, block)?.zero_uninit();
            state
                .memory
                .write_image(pointer, &image, align, block, "GlobalAddr")?;
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
            // One zero run, whatever the size.
            state.memory.write_image(
                pointer,
                &Image::fill(Some(0), size),
                align,
                block,
                "GlobalAddr",
            )?;
        }
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
    /// or volatile) requires every COVERED byte of the access to be
    /// initialized — an uninitialized covered byte is undefined behaviour,
    /// surfaced with its exact offset. For a scalar every byte is covered. A
    /// non-strict (plain) scalar load implements copy-propagates-poison: if the
    /// byte range has any uninitialized byte it yields an inert `PartialBytes`
    /// transport value instead of faulting, so a whole-lane aggregate copy
    /// that reads padding or an inactive niche payload can move those bytes
    /// verbatim to their destination. The value only faults if it is later
    /// INSPECTED (see `reject_partial`).
    ///
    /// WS2.14 (F-030): an aggregate load — strict or not — requires exactly
    /// the bytes a live field of the decoded value covers to be initialized
    /// (`first_uninit_covered`: struct/tuple fields, array elements, the enum
    /// tag lane plus the ACTIVE variant's fields). Padding and the
    /// inactive-variant tail are don't-care: `decode_image` never reads them,
    /// so a rustc-style
    /// field-wise initialization followed by a whole-value move is defined, as
    /// it is in Rust (`read_volatile::<S>` included). An uninitialized covered
    /// byte keeps its undefined-behaviour report. The `Array(U8, N)` union
    /// carrier covers every byte, so a by-value move of a partially initialized
    /// carrier stays undefined behaviour (F-050 is a separate decision).
    fn eval_load(
        &self,
        ty: &Ty,
        ptr: &InterpretValue,
        align: Option<u64>,
        state: &ExecState,
        block: BlockId,
        strict: bool,
    ) -> InterpretResult<InterpretValue> {
        if matches!(ty, Ty::Storage(_)) {
            return Err(type_error(block, "storage-only type has no typed load"));
        }
        let size = self.byte_size(ty, block)?;
        let natural_align = self.byte_align(ty, block)?;
        let align = checked_align(align.unwrap_or(natural_align), block)?;
        let ptr = expect_pointer(ptr, block, "Load")?;
        // A COMPACT image of the range: a load of a stored splat reads one
        // repeating run, whatever the length.
        let image = state.memory.read_image(ptr, size, align, block, "Load")?;
        if image.first_uninit().is_none() {
            return self.decode_image(ty, &image, state, block);
        }
        // Some byte is uninitialized. A non-strict SCALAR load transports the
        // partially-initialized image as poison.
        if !strict && partial_load_ty(ty) {
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::PartialBytes(image.to_vec()),
            });
        }
        // Every other load requires the bytes a live field covers (WS2.14).
        // The first uninitialized covered byte is reported with its exact
        // allocation offset, in the historical `read` message.
        if let Some(index) = self.first_uninit_covered(ty, &image, state, block)? {
            // Crystal lane (E3b): every uninitialised COVERED byte here may have been left so
            // by a store of an UNWRITTEN lane; the aggregate then comes back with those lanes
            // unwritten. Any other uninitialised covered byte keeps the WS2.14 report below.
            if matches!(ty, Ty::Struct(_) | Ty::Tuple(_))
                && self.only_unwritten_lanes_uninit(ty, ptr, &image, state, block)?
            {
                return self.decode_image_with_unwritten_lanes(ty, &image, state, block);
            }
            return Err(ub(
                block,
                format!(
                    "Load: reading uninitialized byte at offset {}",
                    ptr.offset + index
                ),
            ));
        }
        // Only uncovered bytes (padding, the inactive-variant tail) are
        // uninitialized, and `decode_image` never reads them: reading them as
        // zero is unobservable.
        self.decode_image(ty, &image, state, block)
    }

    /// The poison value `Undef` / an unbound `LoadSlot` binds at `ty`
    /// (roadmap WS2.10): the WHOLLY-uninitialized `PartialBytes` image, exactly
    /// what a non-strict load of never-written memory yields, so it transports
    /// and faults on inspection like any other poison value.
    ///
    /// Only the [`partial_load_ty`] scalars have a poison carrier. Every other
    /// type FAILS CLOSED with `UndefinedBehavior`: an aggregate poison value is
    /// not modelled, and spelling one as a "complete" value would be a lie
    /// (roadmap §2.2 ruling 5). `what` prefixes the refusal.
    fn scalar_poison(
        &self,
        ty: &Ty,
        block: BlockId,
        what: &str,
    ) -> InterpretResult<InterpretValue> {
        if partial_load_ty(ty) {
            let size = self.byte_size(ty, block)?;
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::PartialBytes(vec![None; size as usize]),
            });
        }
        Err(ub(
            block,
            format!(
                "{what} of non-scalar type {ty} is not executable (aggregate poison unmodelled)"
            ),
        ))
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
        if matches!(ty, Ty::Storage(_)) {
            return Err(type_error(block, "storage-only type has no typed store"));
        }
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
        // Crystal lane (E3b): an aggregate carrying UNWRITTEN lanes stores those lanes' bytes
        // uninitialised (recorded as unwritten-lane bytes) and every other byte exactly as the
        // WS2.14 aggregate store below does: live-field bytes written, padding and an inactive
        // variant's tail written UNINITIALISED (and not recorded, so they stay don't-care).
        if value_carries_uninit_lane(value) {
            if strict {
                return Err(ub(
                    block,
                    "Store (atomic/volatile): the stored aggregate has an unwritten lane (uninit)",
                ));
            }
            expect_ty(value, ty, block)?;
            let size = self.byte_size(ty, block)?;
            let natural_align = self.byte_align(ty, block)?;
            let align = checked_align(align.unwrap_or(natural_align), block)?;
            let ptr = expect_pointer(ptr, block, "Store")?;
            // The image is `encode_image`'s (padding uninitialised, WS2.14) with each unwritten
            // lane one uninitialised run; `lanes` names exactly those runs, and is the record.
            let mut lanes = Vec::new();
            let image =
                self.encode_image_with_unwritten_lanes(value, 0, &mut lanes, state, block)?;
            if image.len() != size {
                return Err(type_error(
                    block,
                    format!(
                        "Store: aggregate image is {} bytes, type size is {size}",
                        image.len()
                    ),
                ));
            }
            return state
                .memory
                .write_with_unwritten_lanes(ptr, &image, &lanes, align, block, "Store");
        }
        expect_ty(value, ty, block)?;
        if let Ty::FatPtr(kind) = ty {
            self.validate_fat_pointer_value(kind, value, block)?;
        }
        let size = self.byte_size(ty, block)?;
        let natural_align = self.byte_align(ty, block)?;
        let align = checked_align(align.unwrap_or(natural_align), block)?;
        let ptr = expect_pointer(ptr, block, "Store")?;
        // WS2.14 (F-030): the image leaves every byte no live field covers
        // (inter-field padding, the inactive-variant tail) UNINITIALIZED —
        // see `encode_image`. It is compact: a splat of any length is one
        // repeating run of the allocation.
        let image = self.encode_image(value, state, block)?;
        if image.len() != size {
            return Err(type_error(
                block,
                format!(
                    "Store: encoded size {} does not match type size {size}",
                    image.len()
                ),
            ));
        }
        state.memory.write_image(ptr, &image, align, block, "Store")
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
        memory: &MemoryState,
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
            let addr = memory.check_address(addr, block, "GEP")?;
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
        // WS2.16: the result must be an address the target can name. At 64
        // bits this is vacuous (the u64 offset arithmetic above is the whole
        // check, byte-identical to before); on wasm32 a GEP whose result
        // lands past `2^32 - 1` is UB rather than a silently wider pointer.
        if memory.max_address != u64::MAX {
            let base_address = memory.address(base, block, "GEP")?;
            let address = base_address
                .checked_add(delta)
                .ok_or_else(|| ub(block, "GEP: pointer offset overflow"))?;
            memory.check_address(address, block, "GEP")?;
        }
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

    /// `MemCopy` (WS3.20): copy `bytes` bytes from `src` to `dst`.
    ///
    /// The copied image is the destination's byte-for-byte replacement —
    /// VALUE and INIT STATE both (`read_image` / `write_image`, the pair a
    /// non-strict scalar `Load`+`Store` uses to propagate poison), so an
    /// uninitialized source byte stays uninitialized at the
    /// destination and is never laundered into a defined zero. Pointer
    /// PROVENANCE survives for free: this model stores a pointer as its
    /// address bytes and recovers provenance on decode by address lookup
    /// (`resolve_pointer_kind`), so a pointer copied through here still
    /// dereferences (pinned by `crates/trust-ir/tests/bulk_memory_ops.rs`).
    ///
    /// UB (faults): a poison count; either range outside a live allocation
    /// (`checked_access`, alignment 1 — the copy is byte-granular); and, with
    /// `overlap == false` (memcpy), source and destination ranges of the SAME
    /// allocation that overlap. With `overlap == true` (memmove) the copy is
    /// as-if through a temporary — which it literally is here. A zero count is
    /// a no-op and does not touch either pointer, matching `memcpy(p, q, 0)`
    /// on a dangling or null `p`/`q`.
    fn eval_mem_copy(
        &self,
        dst: &InterpretValue,
        src: &InterpretValue,
        bytes: &InterpretValue,
        overlap: bool,
        state: &mut ExecState,
        block: BlockId,
    ) -> InterpretResult<()> {
        let op = if overlap {
            "MemCopy(overlap)"
        } else {
            "MemCopy"
        };
        let count = self.bulk_byte_count(bytes, block, op)?;
        if count == 0 {
            return Ok(());
        }
        let dst = expect_pointer(dst, block, op)?;
        let src = expect_pointer(src, block, op)?;
        if !overlap
            && dst.allocation == src.allocation
            && byte_ranges_overlap(dst.offset, count, src.offset, count)
        {
            return Err(ub(
                block,
                format!(
                    "MemCopy: source [{}..{}) and destination [{}..{}) overlap and the copy is \
                     not marked `overlap` (memmove)",
                    src.offset,
                    src.offset.saturating_add(count),
                    dst.offset,
                    dst.offset.saturating_add(count)
                ),
            ));
        }
        // Read the whole source image first (bounds-checked), then write it:
        // the temporary makes an overlapping memmove trivially correct. The
        // image SHARES the source's nodes and is stored as one run, so a copy
        // costs O(runs read × height) new nodes, never the dynamic `count`:
        // copying a region onto its neighbourhood (`<[T]>::repeat`) adds a
        // node per copy, not the bytes copied.
        let image = state.memory.read_image(src, count, 1, block, op)?;
        state.memory.write_image(dst, &image, 1, block, op)
    }

    /// `MemSet` (WS3.20): write `byte` to each of `bytes` bytes at `dst`.
    /// Every written byte becomes INITIALIZED with that value (a stored
    /// pointer whose bytes are overwritten is destroyed, as under a byte
    /// store). UB (faults): a poison count or fill byte; a range outside a
    /// live allocation. A zero count is a no-op.
    fn eval_mem_set(
        &self,
        dst: &InterpretValue,
        byte: &InterpretValue,
        bytes: &InterpretValue,
        state: &mut ExecState,
        block: BlockId,
    ) -> InterpretResult<()> {
        let count = self.bulk_byte_count(bytes, block, "MemSet")?;
        reject_partial(byte, block, "MemSet fill byte")?;
        expect_ty(byte, &Ty::U8, block)?;
        let fill = expect_int_value(byte, block)?;
        if count == 0 {
            return Ok(());
        }
        let dst = expect_pointer(dst, block, "MemSet")?;
        // Bounds-checked BEFORE any image exists: `count` is attacker-chosen
        // (a `u64::MAX` fill must fault, never try to allocate).
        state
            .memory
            .fill(dst, fill.raw as u8, count, block, "MemSet")
    }

    /// The dynamic byte count of a bulk op: an initialized integer of the
    /// pointer-width unsigned type (`Usize`, or `U64` when the module pins no
    /// target — the validator's rule; here any unsigned integer value is
    /// accepted and its magnitude used).
    fn bulk_byte_count(
        &self,
        bytes: &InterpretValue,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<u64> {
        reject_partial(bytes, block, &format!("{op} byte count"))?;
        let count = expect_int_value(bytes, block)?;
        if count.signed {
            return Err(type_error(
                block,
                format!(
                    "{op}: byte count must be an unsigned integer, got {}",
                    bytes.ty
                ),
            ));
        }
        u64::try_from(count.raw)
            .map_err(|_| ub(block, format!("{op}: byte count {} exceeds u64", count.raw)))
    }

    fn eval_ptr_data(
        &self,
        ptr_ty: &Ty,
        ptr: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        expect_ty(ptr, ptr_ty, block)?;
        // Projecting a pointer's parts inspects it (Lean `semPtrData` has no
        // poison arm either; roadmap WS2.10 review).
        reject_partial(ptr, block, "PtrData")?;
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
        reject_partial(ptr, block, "PtrMetadata")?;
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
            // running target: a pointer-sized unsigned length for Slice/Str, a
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
        // Assembling a pointer inspects both parts: a poison data pointer or
        // metadata word is refused here, as Lean `semPtrFromParts` refuses it
        // (roadmap WS2.10 review) — never re-labelled as a pointer value.
        reject_partial(data, block, "PtrFromParts data")?;
        reject_partial(metadata, block, "PtrFromParts metadata")?;
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

    fn closure_storage_binding(
        &self,
        id: crate::ClosureTyId,
        block: BlockId,
    ) -> InterpretResult<crate::closure_storage::ClosureStorageBinding<'m>> {
        let module = self.module_context(block, "closure storage")?;
        module
            .closure_storage_binding(id)
            .map_err(|error| type_error(block, error))
    }

    fn byte_size(&self, ty: &Ty, block: BlockId) -> InterpretResult<u64> {
        self.byte_size_in(ty, block, &mut Vec::new())
    }

    /// Run `layout` with `key` marked as being laid out, refusing re-entry.
    ///
    /// Roadmap WS2.4 (F-045): a type that contains itself BY VALUE — `struct
    /// Node { next: Node }`, a `Ty::Array` whose `TyId` resolves back to itself,
    /// an enum whose variant carries the enum inline — has no finite layout.
    /// `validate_module` refuses such a module (`InlineAggregateCycle`), but
    /// modules may be interpreted without validation (binary decode and the
    /// text parser run no validator), and without this guard `byte_size` →
    /// `struct_layout` → `aggregate_layout` → `byte_size(field)` recursed until
    /// the host stack overflowed — a crash, not an error. `visiting` is the
    /// stack of nominal / table-indexed types on the current layout path, the
    /// nodes the layout table (`layout_table`) guards against re-entry; re-entry is
    /// a fail-closed `TypeError`. Only by-value edges push a key: a pointer
    /// arm returns a fixed size without looking at its pointee, so `*mut Node`
    /// inside `Node` is never re-entered.
    fn with_layout_visit<T>(
        &self,
        key: LayoutVisit,
        ty: &Ty,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
        layout: impl FnOnce(&mut Vec<LayoutVisit>) -> InterpretResult<T>,
    ) -> InterpretResult<T> {
        if visiting.contains(&key) {
            return Err(type_error(
                block,
                format!("type {ty} contains itself by value (no finite layout)"),
            ));
        }
        visiting.push(key);
        let result = layout(visiting);
        // Pop on EVERY path: `enum_layout`'s niche check probes field sizes with
        // `is_ok_and` and keeps going after an error, so a leaked key would
        // poison a sibling's layout.
        visiting.pop();
        result
    }

    fn byte_size_in(
        &self,
        ty: &Ty,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<u64> {
        match ty {
            Ty::Closure(id) => self
                .closure_storage_binding(*id, block)
                .map(|binding| binding.layout.size),

            Ty::Storage(layout) => {
                if layout.is_well_formed(self.pointer_bits()) {
                    Ok(layout.size_bytes)
                } else {
                    Err(type_error(block, "invalid storage-only layout"))
                }
            }
            Ty::Bool => Ok(1),
            Ty::I8 | Ty::U8 => Ok(1),
            Ty::I16 | Ty::U16 | Ty::F16 => Ok(2),
            Ty::I32 | Ty::U32 | Ty::F32 => Ok(4),
            Ty::I64 | Ty::U64 | Ty::F64 => Ok(8),
            Ty::I128 | Ty::U128 => Ok(16),
            // Pointer-width integers occupy pointer bytes at the running target
            // (`int_shape` executes them at its pointer width, WS2.16); char is a
            // 32-bit unsigned carrier. Mirrors `shape::layout`'s PointerInt rules.
            Ty::Isize | Ty::Usize => Ok(self.pointer_bytes()),
            Ty::Char => Ok(4),
            Ty::Func(_)
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_) => Ok(self.pointer_bytes()),
            // B2: a fat pointer is two pointer words (data + metadata),
            // matching `Ty::bit_width_with(pointer_bits)` and the shape
            // module's fat `PointerLayoutShape` — 16 bytes at 64 bits, 8 on
            // wasm32 (WS2.16).
            Ty::FatPtr(_) => {
                self.require_fat_pointer_layout(block)?;
                Ok(2 * self.pointer_bytes())
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
                self.byte_size_in(elem, block, visiting)?
                    .checked_mul(u64::from(*lanes))
                    .ok_or_else(|| type_error(block, "vector byte size overflow"))
            }
            Ty::Array(elem, len) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                self.with_layout_visit(LayoutVisit::Ty(*elem), ty, block, visiting, |visiting| {
                    self.byte_size_in(&elem_ty, block, visiting)
                })?
                .checked_mul(*len)
                .ok_or_else(|| type_error(block, "array byte size overflow"))
            }
            // A `Ty::Struct` has a finite, in-memory C-style layout: each field
            // is placed at the next offset aligned to the field's natural
            // alignment, and the total size is rounded up to the struct's
            // alignment (the max field alignment). This is the heap-faithful
            // counterpart to the SSA `Aggregate` value model: a recursive ADT
            // (e.g. `Box<Level>`) stays finite because its recursive payload
            // field is a pointer (`Ty::Ptr`, one pointer word), not an inline struct.
            Ty::Struct(_) => Ok(self.struct_layout_in(ty, block, visiting)?.size),
            // A `Ty::Tuple` has the same finite C-style layout as a struct: each
            // element placed at its aligned offset, the total rounded up to the
            // tuple alignment. This is the in-memory counterpart to the
            // in-register `Aggregate` value model and is what lets a tuple be
            // `Alloca`'d / `Store`d / `Load`ed faithfully.
            Ty::Tuple(_) => Ok(self.tuple_layout_in(ty, block, visiting)?.size),
            // A `Ty::Enum` has trust-ir's canonical tagged-union layout (tag at
            // offset 0 + shared max-sized payload region) — see `enum_layout`.
            Ty::Enum(_) => Ok(self.enum_layout_in(ty, block, visiting)?.size),
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
    /// `byte_align`, `encode_image`, and `decode_image`, so the heap round-trip
    /// of a struct value (`HeapAlloc`/`Store`/`Load`) is internally consistent.
    fn struct_layout(&self, ty: &Ty, block: BlockId) -> InterpretResult<StructLayout> {
        self.struct_layout_in(ty, block, &mut Vec::new())
    }

    /// [`Self::struct_layout`] on a layout path: the struct is marked visiting
    /// for both the declared and the synthesized branch (a declared layout
    /// sizes its fields too, so it recurses exactly like the synthesized one).
    fn struct_layout_in(
        &self,
        ty: &Ty,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<StructLayout> {
        let sid = match ty {
            Ty::Struct(sid) => *sid,
            _ => return Err(type_error(block, format!("{ty} is not a struct"))),
        };
        self.with_layout_visit(LayoutVisit::Struct(sid), ty, block, visiting, |visiting| {
            self.struct_layout_unguarded(ty, sid, block, visiting)
        })
    }

    fn struct_layout_unguarded(
        &self,
        ty: &Ty,
        sid: StructId,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<StructLayout> {
        let module = self.module_context(block, "struct layout")?;
        let def = module
            .struct_def(sid)
            .ok_or_else(|| type_error(block, format!("struct id {} not found in module", sid.0)))?;
        match (def.size, def.align) {
            (Some(size), Some(align)) => {
                self.declared_struct_layout(ty, def, size, align, block, visiting)
            }
            (None, None) => {
                if let Some(index) = def.fields.iter().position(|field| field.offset.is_some()) {
                    return Err(type_error(
                        block,
                        format!(
                            "struct {ty} declares a byte offset for field {index} but no struct size or alignment"
                        ),
                    ));
                }
                self.aggregate_layout(
                    def.fields.iter().map(|field| &field.ty),
                    block,
                    "struct",
                    visiting,
                )
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
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<StructLayout> {
        self.require_reference_execution_layout(block)?;
        if align == 0 || !align.is_power_of_two() || !size.is_multiple_of(align) {
            return Err(type_error(
                block,
                format!("struct {ty} declares an incoherent size {size} / alignment {align}"),
            ));
        }
        // `repr(packed(N))` IS a declaration that every field's alignment is clamped
        // to N, so the natural-alignment checks below must be taken against the
        // clamped value or a correct packed layout would be rejected as misaligned.
        //
        // Trust (wave-SG): AND THE CLAMP ITSELF IS RE-VALIDATED, for the same reason
        // every other fact here is — "modules may be interpreted without validation".
        // `StructRepr::Packed(N)`'s doc says `N` is "a power of two", and
        // `validate_module` refuses one that is not (`PackedReprInvalidAlign`), but a
        // module reaches this function through `binary::deserialize_module` (whose
        // repr tag 3 reads a bare `read_v32`) and through the text parser, and neither
        // runs the validator. An unchecked clamp is not a harmless oddity: it is the
        // MODULUS every field-alignment check below is taken against. `Packed(3)`
        // makes a `u64`'s effective alignment `min(8, 3) = 3` and so ADMITS that
        // `u64` at byte 3 — a misaligned scalar access on the pinned target, accepted
        // by the one component that executes bytes. `Packed(0)` is worse in a quieter
        // way: `min(_, 0) = 0` makes `is_multiple_of(0)` accept offset 0 and nothing
        // else, and makes `field_align > align` unfalsifiable, so the over-alignment
        // check silently stops existing. Refuse the descriptor instead; a `Packed(N)`
        // this tree emits always comes from `rustc`'s `repr().pack`, which is a
        // power of two by construction, so this refuses nothing real.
        let clamp = match def.repr {
            crate::ty::StructRepr::Packed(packed) => {
                if packed == 0 || !packed.is_power_of_two() {
                    return Err(type_error(
                        block,
                        format!(
                            "struct {ty} declares repr(packed({packed})): the alignment clamp must be a non-zero power of two"
                        ),
                    ));
                }
                u64::from(packed)
            }
            _ => u64::MAX,
        };
        if align > clamp {
            return Err(type_error(
                block,
                format!(
                    "struct {ty} declares alignment {align} above its repr(packed({clamp})) clamp"
                ),
            ));
        }
        let mut field_offsets: Vec<(u64, Ty)> = Vec::with_capacity(def.fields.len());
        let mut field_sizes: Vec<u64> = Vec::with_capacity(def.fields.len());
        let mut transparent_carrier = None;
        let mut transparent_nontrivial = 0usize;
        for (index, field) in def.fields.iter().enumerate() {
            let field_size = self.byte_size_in(&field.ty, block, visiting)?;
            let field_align = self
                .byte_align_in(&field.ty, block, visiting)?
                .max(1)
                .min(clamp);
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
            if def.repr == crate::ty::StructRepr::Transparent
                && (field_size != 0 || field_align != 1)
            {
                transparent_nontrivial += 1;
                transparent_carrier = Some((field_size, field_align, offset));
            }
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
                    // WS3.18 (F-050): the refusal names the ratified union
                    // spelling, because overlapping struct fields are the
                    // natural (wrong) way a producer spells a union.
                    return Err(type_error(
                        block,
                        format!(
                            "struct {ty} declared layout has overlapping fields {left} and {right} \
                             (a union is not a struct: spell it on the byte-overlap carrier, \
                             lowering-target-subset.md \"Unions\")"
                        ),
                    ));
                }
            }
        }
        if def.repr == crate::ty::StructRepr::Transparent {
            // `repr(transparent)` inherits the exact layout of its sole
            // non-1-ZST field, if any. Size-zero but over-aligned fields are
            // non-trivial here; counting only bytes would silently admit two
            // competing ABI carriers. With no carrier, the wrapper is a 1-ZST.
            let (carrier_size, carrier_align, carrier_offset) =
                transparent_carrier.unwrap_or((0, 1, 0));
            if transparent_nontrivial > 1
                || size != carrier_size
                || align != carrier_align
                || carrier_offset != 0
            {
                return Err(type_error(
                    block,
                    format!(
                        "struct {ty} declares repr(transparent) but its size {size}, alignment {align}, field count, or representation-bearing field offset does not match its sole non-1-ZST field"
                    ),
                ));
            }
        }
        Ok(StructLayout {
            size,
            align,
            field_offsets,
        })
    }

    /// Declared tuple layout when present; otherwise the legacy internal
    /// C-style layout (field offsets, total size, alignment) of a `Ty::Tuple`,
    /// computed directly from its inline element types. Fields are laid out in
    /// order; each is aligned to its natural alignment; the tuple size is
    /// rounded up to the tuple alignment (max field alignment, min 1). An empty
    /// tuple is size 0, alignment 1.
    ///
    /// A tuple shares the exact same layout algorithm as a `Ty::Struct` (via
    /// `aggregate_layout`), so the heap/stack round-trip of a tuple value
    /// (`Alloca`/`Store`/`Load`) is internally consistent: `byte_size`,
    /// `byte_align`, `encode_image`, and `decode_image` all read field offsets
    /// from this one source.
    ///
    /// # THIS IS trust-ir's CANONICAL LAYOUT, **NOT** rustc's
    ///
    /// The same non-parity disclaimer [`EnumLayoutShape`] carries applies here,
    /// and it was missing: this is declaration ORDER, and rustc REORDERS
    /// `repr(Rust)` tuple fields. Measured, not supposed:
    ///
    /// ```text
    /// (u8, u64, u8)   rustc:   field0@8  field1@0  field2@9   size 16
    ///                 here:    field0@0  field1@8  field2@16  size 24
    /// ```
    ///
    /// Every offset and the size disagree. Internal consistency is exactly
    /// enough for what this function is scoped to — a value written and read
    /// back through this one layout — and it is a WRONG-VALUE bug the moment a
    /// tuple offset addresses memory a rustc-derived value also addresses:
    /// `&mut t.1`, `offset_of!`, an `ExtractField` that lowers to a real MIR
    /// projection, or any native codegen.
    ///
    /// Nothing crosses that line today, because every producer path that would
    /// need a tuple offset declines earlier — `field_byte_offset` requires
    /// `ty::Adt(_).is_struct()` before it consults a layout at all, so a tuple
    /// never reaches `struct_interior_offset_admissible`, the gate that exists
    /// to make an emitted offset AGREE with a rustc-filled declared descriptor.
    /// Concrete evidence now lives in `Module::tuple_layouts`. This function
    /// validates that table before honoring it. With no descriptor, the
    /// legacy internal image below still supplies no source-layout evidence.
    ///
    /// So: do not lift one of those declines and reach for this function. A
    /// tuple that needs a rustc-faithful ADDRESS needs a declaration first.
    fn tuple_layout(&self, ty: &Ty, block: BlockId) -> InterpretResult<StructLayout> {
        self.tuple_layout_in(ty, block, &mut Vec::new())
    }

    /// [`Self::tuple_layout`] on a layout path. A tuple is inline and has no
    /// identity of its own to mark: a cycle through one must pass through a
    /// struct, enum or `TyId`, and is caught there.
    fn tuple_layout_in(
        &self,
        ty: &Ty,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<StructLayout> {
        let elems = match ty {
            Ty::Tuple(elems) => elems,
            _ => return Err(type_error(block, format!("{ty} is not a tuple"))),
        };
        if let Some(module) = self.module {
            module
                .validate_tuple_layouts()
                .map_err(|error| type_error(block, error.to_string()))?;
            if let Some(desc) = module
                .tuple_layout_descriptor(ty)
                .map_err(|error| type_error(block, error.to_string()))?
            {
                return Ok(StructLayout {
                    size: desc.size,
                    align: desc.align,
                    field_offsets: desc
                        .field_offsets
                        .iter()
                        .copied()
                        .zip(elems.iter().cloned())
                        .collect(),
                });
            }
        }
        self.aggregate_layout(elems.iter(), block, "tuple", visiting)
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
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<StructLayout> {
        let mut offset: u64 = 0;
        let mut max_align: u64 = 1;
        let mut field_offsets = Vec::with_capacity(fields.len());
        for field_ty in fields {
            let f_align = self.byte_align_in(field_ty, block, visiting)?.max(1);
            let f_size = self.byte_size_in(field_ty, block, visiting)?;
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
    /// Byte size of an enum payload field under a producer DESCRIPTOR.
    ///
    /// WS3.14: a `!` field (rustc's `B(!)`) is size 0 / align 1, as in rustc.
    /// `Ty::Never` has no byte layout anywhere else — it cannot be allocated,
    /// stored or loaded — and the canonical enum layout keeps refusing it; the
    /// descriptor is the only place a producer states where a field of an
    /// uninhabited variant would sit, and no value of that variant is ever
    /// encoded or decoded (both directions refuse it).
    fn descriptor_field_size(
        &self,
        ty: &Ty,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<u64> {
        match ty {
            Ty::Never => Ok(0),
            _ => self.byte_size_in(ty, block, visiting),
        }
    }

    /// Byte alignment companion of [`Self::descriptor_field_size`].
    fn descriptor_field_align(
        &self,
        ty: &Ty,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<u64> {
        match ty {
            Ty::Never => Ok(1),
            _ => self.byte_align_in(ty, block, visiting),
        }
    }

    /// Logical enum shape for register construction. Byte size, field offsets
    /// and physical descriptors are the validator/byte paths' concern; reading
    /// them here would refuse valid values with non-layoutable payload types.
    fn enum_register_shape(
        &self,
        ty: &Ty,
        block: BlockId,
    ) -> InterpretResult<EnumRegisterShape<'m>> {
        let Ty::Enum(eid) = ty else {
            return Err(type_error(block, format!("{ty} is not an enum")));
        };
        let module = self.module_context(block, "enum value")?;
        let definition = module
            .enum_def(*eid)
            .ok_or_else(|| type_error(block, format!("enum id {} not found in module", eid.0)))?;
        let discriminants = definition.effective_discriminants().ok_or_else(|| {
            type_error(
                block,
                format!(
                    "enum {} has no canonical discriminant assignment (duplicate or overflowing values)",
                    ty
                ),
            )
        })?;
        let tag = definition.canonical_tag_repr().ok_or_else(|| {
            type_error(
                block,
                format!(
                    "enum {} has no canonical tag (uninhabited, discriminants beyond 64-bit, or a repr hint too narrow)",
                    ty
                ),
            )
        })?;
        Ok(EnumRegisterShape {
            module,
            definition,
            tag_ty: tag.ty(),
            discriminants,
        })
    }

    fn enum_layout(&self, ty: &Ty, block: BlockId) -> InterpretResult<EnumLayout> {
        self.enum_layout_in(ty, block, &mut Vec::new())
    }

    /// [`Self::enum_layout`] on a layout path: the enum is marked visiting
    /// while its variant fields (descriptor or canonical) are sized.
    fn enum_layout_in(
        &self,
        ty: &Ty,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<EnumLayout> {
        let eid = match ty {
            Ty::Enum(eid) => *eid,
            _ => return Err(type_error(block, format!("{ty} is not an enum"))),
        };
        self.with_layout_visit(LayoutVisit::Enum(eid), ty, block, visiting, |visiting| {
            self.enum_layout_unguarded(ty, eid, block, visiting)
        })
    }

    fn enum_layout_unguarded(
        &self,
        ty: &Ty,
        eid: EnumId,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<EnumLayout> {
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
        let tag_size = self.byte_size_in(&tag_ty, block, visiting)?;
        let tag_align = self.byte_align_in(&tag_ty, block, visiting)?;
        // One inhabitedness memo for every variant: each node the variants
        // reach is decided once (`Module::variant_is_uninhabited` per variant
        // would re-decide what they share).
        let mut inhabit = crate::inhabit::InhabitMemo::default();
        let uninhabited_variants: Vec<bool> = def
            .variants
            .iter()
            .map(|variant| inhabit.variant_is_uninhabited(module, variant))
            .collect();

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
                if matches!(desc.encoding, crate::ty::EnumTagEncoding::SingleInhabited { variant } if usize::try_from(variant).ok() != Some(variant_idx))
                {
                    if !offsets.is_empty() {
                        return Err(type_error(
                            block,
                            format!(
                                "enum {ty} inactive variant {variant_idx} has a physical offset row"
                            ),
                        ));
                    }
                    variant_field_offsets.push(Vec::new());
                    continue;
                }
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
                    let field_size = self.descriptor_field_size(field_ty, block, visiting)?;
                    let field_align = self.descriptor_field_align(field_ty, block, visiting)?;
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
                    let left_size = self.descriptor_field_size(&fields[left].1, block, visiting)?;
                    for right in left + 1..fields.len() {
                        let right_size =
                            self.descriptor_field_size(&fields[right].1, block, visiting)?;
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
                crate::ty::EnumTagEncoding::SingleInhabited { variant } => {
                    let active = usize::try_from(*variant)
                        .ok()
                        .filter(|index| *index < def.variants.len())
                        .ok_or_else(|| {
                            type_error(
                                block,
                                format!("enum {ty} single-inhabited selector is out of range"),
                            )
                        })?;
                    if uninhabited_variants[active]
                        || uninhabited_variants
                            .iter()
                            .enumerate()
                            .any(|(index, absent)| index != active && !absent)
                    {
                        return Err(type_error(
                            block,
                            format!(
                                "enum {ty} single-inhabited selection does not identify exactly one inhabited variant"
                            ),
                        ));
                    }
                    EnumByteView::Untagged { variant: active }
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
                            let field_size =
                                self.descriptor_field_size(field_ty, block, visiting)?;
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
                    let niche_size = self.byte_size_in(&niche_ty.ty(), block, visiting)?;
                    let niche_align = self.byte_align_in(&niche_ty.ty(), block, visiting)?;
                    let niche_bits = (niche_size * 8) as u32;
                    let niche_mask = int_mask(niche_bits).ok_or_else(|| {
                        type_error(block, format!("unsupported niche lane width {niche_bits}"))
                    })?;
                    let niche_span = niche_variants_end
                        .checked_sub(*niche_variants_start)
                        .map(u128::from);
                    // WS3.14: every INHABITED variant is the untagged one or
                    // lies in the niche interval; an uninhabited variant needs
                    // no encoding (decode below refuses any image naming one).
                    // The same rule as the validator and `shape`
                    // (`Module::niche_unencoded_inhabited_variant`), read off
                    // the verdicts decided above.
                    let covers_every_variant = niche_span.is_some()
                        && uninhabited_variants
                            .iter()
                            .enumerate()
                            .all(|(index, uninhabited)| {
                                *uninhabited
                                    || u32::try_from(index).is_ok_and(|index| {
                                        index == *untagged_variant
                                            || (*niche_variants_start..=*niche_variants_end)
                                                .contains(&index)
                                    })
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
                        self.byte_size_in(field_ty, block, visiting)
                            .is_ok_and(|field_size| {
                                field_size > 0
                                    && *field_offset <= *niche_offset
                                    && field_offset.checked_add(field_size).is_some_and(
                                        |field_end| {
                                            niche_offset
                                                .checked_add(niche_size)
                                                .is_some_and(|niche_end| field_end >= niche_end)
                                        },
                                    )
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
                            let field_size =
                                self.descriptor_field_size(field_ty, block, visiting)?;
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
                uninhabited_variants,
            });
        }

        let mut payload_size: u64 = 0;
        let mut payload_align: u64 = 1;
        let mut variant_field_offsets = Vec::with_capacity(def.variants.len());
        for variant in &def.variants {
            let layout =
                self.aggregate_layout(variant.fields.iter(), block, "enum variant", visiting)?;
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
            uninhabited_variants,
        })
    }

    /// Resolve the C-style layout of an aggregate-typed value, dispatching to
    /// `struct_layout` for `Ty::Struct` and `tuple_layout` for `Ty::Tuple`.
    /// Shared by `encode_image` and `decode_image` so both directions of the
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
        self.byte_align_in(ty, block, &mut Vec::new())
    }

    fn byte_align_in(
        &self,
        ty: &Ty,
        block: BlockId,
        visiting: &mut Vec<LayoutVisit>,
    ) -> InterpretResult<u64> {
        match ty {
            Ty::Closure(id) => self
                .closure_storage_binding(*id, block)
                .map(|binding| binding.layout.align),

            Ty::Storage(layout) => {
                if layout.is_well_formed(self.pointer_bits()) {
                    Ok(layout.align_bytes)
                } else {
                    Err(type_error(block, "invalid storage-only layout"))
                }
            }
            Ty::Bool | Ty::I8 | Ty::U8 => Ok(1),
            Ty::I16 | Ty::U16 | Ty::F16 => Ok(2),
            // Char is a 32-bit unsigned carrier; isize/usize and every
            // pointer take pointer alignment at the running target (WS2.16:
            // 8 at 64 bits, 4 on wasm32). Mirrors `byte_size` and
            // `shape::layout`.
            Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => Ok(4),
            Ty::I64 | Ty::U64 | Ty::F64 => Ok(8),
            Ty::Func(_)
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_) => Ok(self.pointer_bytes()),
            Ty::Isize | Ty::Usize => Ok(self.pointer_bytes()),
            // B2: fat pointers align to one pointer word, not their two-word size.
            Ty::FatPtr(_) => {
                self.require_fat_pointer_layout(block)?;
                Ok(self.pointer_bytes())
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
                self.byte_align_in(elem, block, visiting)
            }
            Ty::Array(elem, _) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                self.with_layout_visit(LayoutVisit::Ty(*elem), ty, block, visiting, |visiting| {
                    self.byte_align_in(&elem_ty, block, visiting)
                })
            }
            // Struct alignment is the max of its field alignments (min 1).
            Ty::Struct(_) => Ok(self.struct_layout_in(ty, block, visiting)?.align),
            // Tuple alignment is the max of its element alignments (min 1), so
            // an empty tuple is alignment 1 — matching `Ty::Unit`.
            Ty::Tuple(_) => Ok(self.tuple_layout_in(ty, block, visiting)?.align),
            // Enum alignment is max(tag alignment, payload alignment) — see
            // `enum_layout` for the canonical rules.
            Ty::Enum(_) => Ok(self.enum_layout_in(ty, block, visiting)?.align),
            _ => Err(type_error(block, format!("{ty} has no byte alignment"))),
        }
    }

    /// A pointer's byte image: the low `pointer_bytes` bytes of `address`,
    /// little-endian (WS2.16). The caller has range-checked `address`.
    fn pointer_image(&self, address: u64) -> Vec<u8> {
        address.to_le_bytes()[..self.pointer_bytes() as usize].to_vec()
    }

    /// Inverse of [`Self::pointer_image`]: read one pointer word.
    fn pointer_from_image(&self, bytes: &[u8], block: BlockId) -> InterpretResult<u64> {
        if bytes.len() as u64 != self.pointer_bytes() {
            return Err(type_error(
                block,
                format!(
                    "Load: pointer image is {} bytes, expected {}",
                    bytes.len(),
                    self.pointer_bytes()
                ),
            ));
        }
        let mut raw = [0u8; 8];
        raw[..bytes.len()].copy_from_slice(bytes);
        Ok(u64::from_le_bytes(raw))
    }

    /// Module-local symbolic code addresses are one target pointer word.
    /// Zero is null, 1..=functions.len() names the exact module entry. These
    /// are interpreter addresses, never host executable addresses or raw IDs.
    fn function_pointer_address(&self, target: FuncId, block: BlockId) -> InterpretResult<u64> {
        let module = self.module_context(block, "function pointer Store")?;
        let index = module
            .functions
            .iter()
            .position(|function| function.id == target)
            .ok_or_else(|| {
                invalid_function_pointer(
                    block,
                    format!("Store: undefined function pointer {target}"),
                )
            })?;
        let address = (index as u64)
            .checked_add(1)
            .filter(|address| *address <= max_address_for(self.pointer_bits()))
            .ok_or_else(|| {
                invalid_function_pointer(
                    block,
                    "Store: function address exceeds target pointer width",
                )
            })?;
        Ok(address)
    }

    fn function_pointer_from_address(
        &self,
        address: u64,
        block: BlockId,
    ) -> InterpretResult<InterpretValueKind> {
        if address == 0 {
            return Ok(InterpretValueKind::NullPtr);
        }
        let module = self.module_context(block, "function pointer Load")?;
        let index = usize::try_from(address - 1).map_err(|_| {
            invalid_function_pointer(block, "Load: invalid function pointer address")
        })?;
        let function = module.functions.get(index).ok_or_else(|| {
            invalid_function_pointer(block, "Load: unregistered function pointer address")
        })?;
        Ok(InterpretValueKind::FnDef(function.id))
    }

    /// The byte image of a non-aggregate value (a scalar, pointer, fat
    /// pointer, unit or vector): every byte initialized. Aggregates go
    /// through [`Self::encode_image`].
    fn encode_leaf(
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
            // A pointer's byte image is its address in `pointer_bytes` LE
            // bytes (WS2.16); `address` / `check_address` already refused an
            // address the target width cannot hold, so the slice is lossless.
            InterpretValueKind::Ptr(ptr) => {
                let address = state.memory.address(*ptr, block, "Store")?;
                Ok(self.pointer_image(address))
            }
            InterpretValueKind::FnDef(target) => {
                if !matches!(value.ty, Ty::Func(_)) {
                    return Err(type_error(
                        block,
                        "Store: function pointer has non-function type",
                    ));
                }
                Ok(self.pointer_image(self.function_pointer_address(*target, block)?))
            }
            InterpretValueKind::NullPtr => Ok(self.pointer_image(0)),
            // A no-provenance pointer stores its raw integer address verbatim,
            // so a later load reconstructs the same dangling value.
            InterpretValueKind::DanglingPtr(addr) => {
                let address = state.memory.check_address(*addr, block, "Store")?;
                Ok(self.pointer_image(address))
            }
            // B2: a fat pointer's byte image is its two words back to back —
            // data address then metadata (the raw length int for Slice/Str,
            // the vtable address for TraitObject), each `pointer_bytes` LE
            // bytes. Exact inverse of the `decode_leaf` FatPtr arm.
            InterpretValueKind::FatPtr { data, metadata } => {
                let mut bytes = self.encode_leaf(data, state, block)?;
                bytes.extend(self.encode_leaf(metadata, state, block)?);
                let expected = 2 * self.pointer_bytes();
                if bytes.len() as u64 != expected {
                    return Err(type_error(
                        block,
                        format!(
                            "Store: fat pointer image is {} bytes, expected {expected}",
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
            // A vector is encoded lane by lane, structurally, by
            // `encode_image`; it has no single leaf image.
            _ => Err(type_error(
                block,
                format!("Store: cannot encode value of type {}", value.ty),
            )),
        }
    }

    /// The byte image a typed `Store` writes for `value`: a COMPACT image
    /// (`Image`) whose size follows the value's structure, not its length.
    ///
    /// WS2.14 (F-030): a typed aggregate value has no padding — it carries no
    /// byte image beyond its live fields. Every byte no live field covers
    /// (inter-field padding, the inactive-variant tail of an enum) is
    /// therefore UNINITIALIZED in the image, never a made-up zero, so a whole
    /// `Load` of never-written padding followed by this `Store` cannot launder
    /// uninitialized bytes into defined ones. (The covered bytes are exactly
    /// the ones [`Self::decode_image`] reads.)
    ///
    /// An array or vector is encoded on its value's STRUCTURE
    /// ([`super::rope::Rope::try_flat_map`]): a run of equal elements is one
    /// repeat of the element's image, a repeating run of values one repeat of
    /// the images of its period, and each stored value is encoded once — so
    /// a splat of any length encodes in O(1) and a store of it is one run of
    /// the allocation.
    fn encode_image(
        &self,
        value: &InterpretValue,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<Image> {
        match &value.kind {
            InterpretValueKind::Closure { func, captures } => {
                let Ty::Closure(id) = value.ty else {
                    return Err(type_error(block, "closure value has a non-closure type"));
                };
                let binding = self.closure_storage_binding(id, block)?;
                if *func != binding.target || captures.len() != binding.captures.len() {
                    return Err(type_error(
                        block,
                        "closure Store target or capture count mismatch",
                    ));
                }
                let mut image = ByteStore::new(binding.layout.size, None);
                for ((capture, ty), offset) in captures
                    .iter()
                    .zip(binding.captures)
                    .zip(&binding.layout.capture_offsets)
                {
                    expect_ty(capture, ty, block)?;
                    image.write(*offset, &self.encode_image(capture, state, block)?);
                }
                Ok(image.read(0, binding.layout.size))
            }

            InterpretValueKind::Array(values) => {
                let Ty::Array(elem, len) = &value.ty else {
                    return Err(type_error(
                        block,
                        format!("Store: array value carries non-array type {}", value.ty),
                    ));
                };
                if values.len() != *len {
                    return Err(type_error(
                        block,
                        format!(
                            "Store: array {} has {len} elements but the value has {}",
                            value.ty,
                            values.len()
                        ),
                    ));
                }
                let elem_ty = self.resolve_ty(*elem, block)?;
                values.rope().try_flat_map(|element| {
                    expect_ty(element, &elem_ty, block)?;
                    self.encode_image(element, state, block)
                })
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
            // integer/float vector encodes lane by lane.
            InterpretValueKind::Vector(lanes) => {
                let Ty::Vector(elem_ty, lane_count) = &value.ty else {
                    return Err(type_error(
                        block,
                        format!("Store: vector value carries non-vector type {}", value.ty),
                    ));
                };
                if lanes.len() != u64::from(*lane_count) {
                    return Err(type_error(
                        block,
                        format!(
                            "Store: vector {} has {lane_count} lanes but the value has {}",
                            value.ty,
                            lanes.len()
                        ),
                    ));
                }
                let mask = **elem_ty == Ty::Bool;
                let lane_bytes = self.byte_size(elem_ty, block)?;
                lanes.rope().try_flat_map(|lane| {
                    if mask {
                        let set = lane.as_bool().ok_or_else(|| {
                            type_error(block, "vector bool mask lane is not a bool value")
                        })?;
                        Ok(Image::fill(Some(if set { 0xFF } else { 0x00 }), lane_bytes))
                    } else {
                        Ok(Image::init_bytes(&self.encode_leaf(lane, state, block)?))
                    }
                })
            }
            // A struct / tuple image: each field's image at its computed
            // offset on an uninitialized background. `Ty::Struct` (layout from
            // the module `StructDef`) and `Ty::Tuple` (layout from the inline
            // element types) share the offset math `decode_image` uses.
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
                let mut image = ByteStore::new(layout.size, None);
                for (field_val, (offset, field_ty)) in fields.iter().zip(&layout.field_offsets) {
                    expect_ty(field_val, field_ty, block)?;
                    let field_image = self.encode_image(field_val, state, block)?;
                    image.write(*offset, &field_image);
                }
                Ok(image.read(0, layout.size))
            }
            // An enum value (`Aggregate([tag, fields...])`, the tag + payload
            // convention) to its canonical tagged-union image: the tag lane
            // (direct tag bytes, or the niche lane of a niche variant), then
            // the selected variant's fields at their payload-relative offsets
            // shifted by `payload_offset`; every other byte uninitialized.
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
                layout.refuse_uninhabited(variant_idx, &value.ty, "Store", block)?;
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
                let mut image = ByteStore::new(layout.size, None);
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
                        let tag_bytes = self.encode_leaf(tag_val, state, block)?;
                        image.write(*tag_offset, &Image::init_bytes(&tag_bytes));
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
                            image.write(
                                *niche_offset,
                                &Image::init_bytes(
                                    &lane_value.to_le_bytes()[..*niche_size as usize],
                                ),
                            );
                        }
                    }
                }
                for (field_val, (rel_offset, field_ty)) in field_vals.iter().zip(fields) {
                    expect_ty(field_val, field_ty, block)?;
                    let field_image = self.encode_image(field_val, state, block)?;
                    image.write(layout.payload_offset + rel_offset, &field_image);
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
                    let lane = image.read(*niche_offset, *niche_size).to_vec();
                    let mut raw = [0u8; 16];
                    for (slot, byte) in raw.iter_mut().zip(&lane) {
                        *slot = byte.unwrap_or(0);
                    }
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
                Ok(image.read(0, layout.size))
            }
            // Crystal lane (E3b): an unwritten lane has no bytes to encode as INITIALISED. A store
            // takes `encode_image_with_unwritten_lanes` before reaching here; any other encode
            // (a cast's reinterpretation) would read uninitialised memory.
            InterpretValueKind::Uninit => Err(ub(
                block,
                format!(
                    "encoding an unwritten lane (uninit) of type {} as initialized bytes",
                    value.ty
                ),
            )),
            _ => Ok(Image::init_bytes(&self.encode_leaf(value, state, block)?)),
        }
    }

    /// Crystal lane (E3b): the byte image of a value that may carry UNWRITTEN lanes, and the
    /// byte ranges (`(offset, len)`, relative to the value's first byte at `base`) those lanes
    /// occupy. An unwritten lane is one uninitialized run of its type's size; a struct/tuple
    /// aggregate lays its lanes out exactly as [`Self::encode_image`] does (padding
    /// uninitialized, WS2.14); every other value is `encode_image`'s image. Compact: a lane of
    /// any size is one run and one recorded range.
    fn encode_image_with_unwritten_lanes(
        &self,
        value: &InterpretValue,
        base: u64,
        lanes: &mut Vec<(u64, u64)>,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<Image> {
        match &value.kind {
            InterpretValueKind::Uninit => {
                let size = self.byte_size(&value.ty, block)?;
                lanes.push((base, size));
                Ok(Image::fill(None, size))
            }
            InterpretValueKind::Aggregate(fields)
                if matches!(value.ty, Ty::Struct(_) | Ty::Tuple(_))
                    && fields.iter().any(value_carries_uninit_lane) =>
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
                let mut image = ByteStore::new(layout.size, None);
                for (field_val, (offset, field_ty)) in fields.iter().zip(&layout.field_offsets) {
                    expect_ty(field_val, field_ty, block)?;
                    let field_image = self.encode_image_with_unwritten_lanes(
                        field_val,
                        base + offset,
                        lanes,
                        state,
                        block,
                    )?;
                    image.write(*offset, &field_image);
                }
                Ok(image.read(0, layout.size))
            }
            _ => self.encode_image(value, state, block),
        }
    }

    /// Crystal lane (E3b): true iff every uninitialised COVERED byte of `image` (the `ty`
    /// read at `ptr`) lies in a recorded unwritten lane. Structural: the recorded lanes
    /// overlapping the range are defined over a copy of the image (one run each) and the
    /// WS2.14 covered-byte search asked again, so the check costs the image's runs and the
    /// lanes, never its length. False, without touching the image, when the allocation has
    /// no recorded lane (every program with no `Constant::Uninit`).
    fn only_unwritten_lanes_uninit(
        &self,
        ty: &Ty,
        ptr: InterpretPointer,
        image: &Image,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<bool> {
        let lanes = state.memory.unwritten_lanes_in(ptr, image.len());
        if lanes.is_empty() {
            return Ok(false);
        }
        let mut defined = ByteStore::new(image.len(), None);
        defined.write(0, image);
        for (start, len) in lanes {
            defined.write(start, &Image::fill(Some(0), len));
        }
        let defined = defined.read(0, image.len());
        Ok(self
            .first_uninit_covered(ty, &defined, state, block)?
            .is_none())
    }

    /// Crystal lane (E3b): decode a struct/tuple whose uninitialised COVERED bytes are all
    /// recorded unwritten-lane bytes (the caller checked). A lane whose every byte is
    /// uninitialised comes back UNWRITTEN; a lane none of whose COVERED bytes is uninitialised
    /// decodes as [`Self::decode_image`] decodes it (its uncovered bytes — padding, an inactive
    /// variant's tail — are never read, exactly as the WS2.14 `eval_load` treats them); a
    /// struct/tuple lane with both recurses; any other lane with an uninitialised covered byte
    /// is undefined behaviour, exactly the discipline a partially initialised scalar inside an
    /// aggregate has always met. A zero-sized lane has no bytes and decodes to its type's one
    /// value. Each lane is a slice of the image (shared nodes), so this costs the lanes and the
    /// image's runs, never a lane's length.
    fn decode_image_with_unwritten_lanes(
        &self,
        ty: &Ty,
        image: &Image,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let layout = self.aggregate_value_layout(ty, block)?;
        if image.len() != layout.size {
            return Err(type_error(
                block,
                format!(
                    "Load: byte count {} does not match type size {}",
                    image.len(),
                    layout.size
                ),
            ));
        }
        let mut lanes = Vec::with_capacity(layout.field_offsets.len());
        for (offset, field_ty) in &layout.field_offsets {
            let len = self.byte_size(field_ty, block)?;
            let slice = image.slice(*offset, len);
            if len > 0 && slice.find_first(Option::is_some).is_none() {
                lanes.push(InterpretValue {
                    ty: field_ty.clone(),
                    kind: InterpretValueKind::Uninit,
                });
                continue;
            }
            match self.first_uninit_covered(field_ty, &slice, state, block)? {
                None => lanes.push(self.decode_image(field_ty, &slice, state, block)?),
                Some(_) if matches!(field_ty, Ty::Struct(_) | Ty::Tuple(_)) => {
                    lanes.push(
                        self.decode_image_with_unwritten_lanes(field_ty, &slice, state, block)?,
                    );
                }
                Some(first) => {
                    return Err(ub(
                        block,
                        format!(
                            "Load: reading uninitialized byte at offset {} of a partially \
                             written {field_ty} lane",
                            offset + first
                        ),
                    ));
                }
            }
        }
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Aggregate(lanes),
        })
    }

    /// The dense byte image of `value` with every uncovered byte (padding,
    /// an inactive enum tail) spelled `0`. For tests of the byte funnel; the
    /// execution paths write [`Self::encode_image`] directly.
    #[cfg(test)]
    fn encode_value(
        &self,
        value: &InterpretValue,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<Vec<u8>> {
        Ok(self
            .encode_image(value, state, block)?
            .to_vec()
            .into_iter()
            .map(|byte| byte.unwrap_or(0))
            .collect())
    }

    /// Decode a fully initialized byte image of `ty` (the dense form of
    /// [`Self::decode_image`]), for tests of the byte funnel.
    #[cfg(test)]
    fn decode_value(
        &self,
        ty: &Ty,
        bytes: &[u8],
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        self.decode_image(ty, &Image::init_bytes(bytes), state, block)
    }

    /// Decode a `ty` value from its byte image, reading only the bytes a
    /// live field covers (an uncovered byte — padding, an inactive enum
    /// tail — is never read; an UNINITIALIZED covered byte must have been
    /// refused by the caller, see `first_uninit_covered`, and reads as `0`
    /// here).
    ///
    /// An array or vector decodes on the image's STRUCTURE
    /// ([`super::rope::Rope::chunk_map`]): a uniform run of memory decodes
    /// its element once, a repeating run decodes one period of elements —
    /// whatever element type it is read back at, so a stored `[u16; N]` read
    /// as `[u8; 2N]` is two decodes — and a copy's shared nodes decode once.
    /// Only literal bytes decode one element at a time. A zero-size element
    /// decodes once, whatever the length.
    fn decode_image(
        &self,
        ty: &Ty,
        image: &Image,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let size = self.byte_size(ty, block)?;
        if image.len() != size {
            return Err(type_error(
                block,
                format!(
                    "Load: byte count {} does not match type size {size}",
                    image.len()
                ),
            ));
        }
        match ty {
            Ty::Closure(id) => {
                let binding = self.closure_storage_binding(*id, block)?;
                let mut captures = Vec::with_capacity(binding.captures.len());
                for (ty, offset) in binding.captures.iter().zip(&binding.layout.capture_offsets) {
                    let field = image.slice(*offset, self.byte_size(ty, block)?);
                    captures.push(self.decode_image(ty, &field, state, block)?);
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Closure {
                        func: binding.target,
                        captures,
                    },
                })
            }

            Ty::Array(elem, len) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                let values = self.decode_elements(&elem_ty, *len, image, state, block)?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Array(values),
                })
            }
            Ty::Vector(elem_ty, lanes) => {
                let values =
                    self.decode_elements(elem_ty, u64::from(*lanes), image, state, block)?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Vector(values),
                })
            }
            // Decode an aggregate's C-layout image back into an `Aggregate`
            // value: read each field from its computed offset. `Ty::Struct`
            // and `Ty::Tuple` use the same layout (via
            // `aggregate_value_layout`), so this is the exact inverse of
            // `encode_image` — the field offsets match byte-for-byte.
            Ty::Struct(_) | Ty::Tuple(_) => {
                let layout = self.aggregate_value_layout(ty, block)?;
                let mut values = Vec::with_capacity(layout.field_offsets.len());
                for (offset, field_ty) in &layout.field_offsets {
                    let f_size = self.byte_size(field_ty, block)?;
                    let field = image.slice(*offset, f_size);
                    values.push(self.decode_image(field_ty, &field, state, block)?);
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            // Decode an enum's canonical tagged-union image: read the tag
            // lane, resolve the variant it names, then decode that variant's
            // fields from the shared payload region — the exact inverse of the
            // enum `encode_image` arm. A tag value matching no variant
            // discriminant is a corrupted/foreign image and fails closed
            // (never a mis-tagged value).
            Ty::Enum(_) => {
                let layout = self.enum_layout(ty, block)?;
                let (variant_idx, tag_val) =
                    self.enum_image_variant(&layout, ty, image, state, block)?;
                layout.refuse_uninhabited(variant_idx, ty, "Load", block)?;
                let fields = &layout.variant_field_offsets[variant_idx];
                let mut values = Vec::with_capacity(fields.len() + 1);
                values.push(tag_val);
                for (rel_offset, field_ty) in fields {
                    let f_size = self.byte_size(field_ty, block)?;
                    let field = image.slice(layout.payload_offset + rel_offset, f_size);
                    values.push(self.decode_image(field_ty, &field, state, block)?);
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            _ => {
                let bytes: Vec<u8> = image
                    .to_vec()
                    .into_iter()
                    .map(|byte| byte.unwrap_or(0))
                    .collect();
                self.decode_leaf(ty, &bytes, state, block)
            }
        }
    }

    /// The `count` elements of type `elem_ty` an array or vector image holds,
    /// decoded on the image's structure (see [`Self::decode_image`]).
    fn decode_elements(
        &self,
        elem_ty: &Ty,
        count: u64,
        image: &Image,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<ArrayValue> {
        let stride = self.byte_size(elem_ty, block)?;
        if count == 0 {
            return Ok(ArrayValue::from_vec(Vec::new()));
        }
        if stride == 0 {
            let value = self.decode_image(elem_ty, &Image::empty(), state, block)?;
            return Ok(ArrayValue::splat(value, count));
        }
        let rope = image.chunk_map(stride, &mut |element: &Image| {
            self.decode_image(elem_ty, element, state, block)
        })?;
        Ok(ArrayValue::from_rope(rope))
    }

    /// Decode a non-aggregate value (scalar, pointer, fat pointer, unit)
    /// from its initialized byte image.
    fn decode_leaf(
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
            // shape (isize/usize at the target pointer width, char at its 32-bit
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
                let addr = self.pointer_from_image(bytes, block)?;
                // A loaded pointer whose address names no allocation is a
                // no-provenance value (`DanglingPtr`), not an error — the
                // provenance check is deferred to dereference (`expect_pointer`).
                let kind = state.memory.resolve_pointer_kind(addr);
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind,
                })
            }
            Ty::Func(_) => {
                let address = self.pointer_from_image(bytes, block)?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: self.function_pointer_from_address(address, block)?,
                })
            }
            // B2: decode a fat pointer's two-lane image (byte count pre-checked
            // by the size gate above): data address then metadata. The
            // metadata decodes at the kind's canonical type (pointer-sized
            // unsigned length for Slice/Str, thin Ptr for TraitObject).
            Ty::FatPtr(kind) => {
                self.require_fat_pointer_layout(block)?;
                let word = self.pointer_bytes() as usize;
                let addr = self.pointer_from_image(&bytes[..word], block)?;
                // An empty slice / len-0 `&[T]` carries a dangling data lane
                // (`NonNull::dangling`); resolve it as a no-provenance value.
                let data_kind = state.memory.resolve_pointer_kind(addr);
                let data = InterpretValue { ty: Ty::Ptr, kind: data_kind };
                let canonical = kind.metadata_ty(self.pointer_bits()).ok_or_else(|| {
                    type_error(block, format!("Load: {ty} has no metadata type"))
                })?;
                let metadata = self.decode_leaf(&canonical, &bytes[word..], state, block)?;
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
            _ => Err(type_error(block, format!("Load: cannot decode type {ty}"))),
        }
    }

    /// Resolve the active variant (and the logical tag operand) named by an
    /// enum byte image under `layout`. Reads ONLY the tag lane — the direct tag
    /// bytes or the niche lane; an untagged image reads nothing. Shared by
    /// `decode_image` and `first_uninit_covered`, so the variant whose fields a
    /// load decodes is exactly the variant whose field bytes the WS2.14
    /// covered-byte rule requires to be initialized. An uninitialized tag-lane
    /// byte reads as `0` here; the covered-byte rule refuses it first.
    fn enum_image_variant(
        &self,
        layout: &EnumLayout,
        ty: &Ty,
        image: &Image,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<(usize, InterpretValue)> {
        let lane = |offset: u64, size: u64| -> Vec<u8> {
            image
                .slice(offset, size)
                .to_vec()
                .into_iter()
                .map(|byte| byte.unwrap_or(0))
                .collect()
        };
        match &layout.byte_view {
            // No tag lane exists to read: the sole variant IS the answer, and
            // the tag operand is synthesized from it. This is total — unlike
            // the tagged arms there is no byte pattern that could name a
            // variant the enum does not have.
            EnumByteView::Untagged { variant } => {
                Ok((*variant, synthesized_tag_value(layout, *variant, block)?))
            }
            EnumByteView::Direct { tag_offset } => {
                let tag_val = self.decode_leaf(
                    &layout.tag_ty,
                    &lane(*tag_offset, layout.tag_size),
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
                Ok((variant_idx, tag_val))
            }
            EnumByteView::Niche {
                untagged_variant,
                niche_variants_start,
                niche_variants_end,
                niche_start,
                niche_offset,
                niche_size,
            } => {
                let mut raw = [0u8; 16];
                raw[..*niche_size as usize].copy_from_slice(&lane(*niche_offset, *niche_size));
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
                let tag_val = synthesized_tag_value(layout, variant_idx, block)?;
                Ok((variant_idx, tag_val))
            }
        }
    }

    /// WS2.14 (F-030): the offset of the first UNINITIALIZED byte of a `ty`
    /// image that a LIVE field of the value covers — a byte `decode_image`
    /// reads — or `None` when every covered byte is initialized.
    ///
    /// - A scalar, pointer, fat pointer or vector covers every byte.
    /// - A struct / tuple covers the union of its fields' covered bytes, at the
    ///   declared (or canonical) field offsets; bytes no field covers are
    ///   padding.
    /// - An array covers each element's covered bytes (an `Array(U8, N)` union
    ///   carrier therefore covers every byte: each byte IS an element). It is
    ///   decided on the image's structure, exactly as `decode_image` decodes
    ///   it (`Rope::chunk_map`): one answer per distinct element image, so a
    ///   stored splat is checked once, whatever its length.
    /// - An enum covers its tag lane (the direct tag bytes, or the niche lane)
    ///   plus the fields of the ACTIVE variant the tag names. When a tag byte is
    ///   itself uninitialized the active variant is unknowable, so only the tag
    ///   lane is covered: a load then reports that byte. Inactive-variant tail
    ///   bytes and inter-field padding are not covered.
    ///
    /// Only bytes a decode never reads are left uncovered, so a load that
    /// reads them as zero observes nothing it made up; and a typed aggregate
    /// `Store` that writes them as uninitialized loses nothing the value
    /// carries.
    fn first_uninit_covered(
        &self,
        ty: &Ty,
        image: &Image,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<Option<u64>> {
        match ty {
            Ty::Closure(id) => {
                let binding = self.closure_storage_binding(*id, block)?;
                let mut first: Option<u64> = None;
                for (ty, offset) in binding.captures.iter().zip(&binding.layout.capture_offsets) {
                    let field = image.slice(*offset, self.byte_size(ty, block)?);
                    if let Some(at) = self.first_uninit_covered(ty, &field, state, block)? {
                        let at = offset + at;
                        first = Some(first.map_or(at, |first| first.min(at)));
                    }
                }
                Ok(first)
            }

            Ty::Struct(_) | Ty::Tuple(_) => {
                let layout = self.aggregate_value_layout(ty, block)?;
                let mut first: Option<u64> = None;
                for (offset, field_ty) in &layout.field_offsets {
                    let f_size = self.byte_size(field_ty, block)?;
                    let field = image.slice(*offset, f_size);
                    if let Some(at) = self.first_uninit_covered(field_ty, &field, state, block)? {
                        let at = offset + at;
                        first = Some(first.map_or(at, |first: u64| first.min(at)));
                    }
                }
                Ok(first)
            }
            Ty::Array(elem, len) => {
                let elem_ty = self.resolve_ty(*elem, block)?;
                let stride = self.byte_size(&elem_ty, block)?;
                if stride == 0 || *len == 0 {
                    return Ok(None);
                }
                // One answer per element, on the image's structure; the first
                // element with an uninitialized covered byte holds the
                // lowest such offset (elements do not overlap).
                let answers = image.chunk_map(stride, &mut |element: &Image| {
                    self.first_uninit_covered(&elem_ty, element, state, block)
                })?;
                Ok(answers
                    .find_first(Option::is_some)
                    .map(|(index, at)| index * stride + at.expect("found by is_some")))
            }
            Ty::Enum(_) => {
                let layout = self.enum_layout(ty, block)?;
                let tag_lane = match &layout.byte_view {
                    EnumByteView::Untagged { .. } => None,
                    EnumByteView::Direct { tag_offset } => Some((*tag_offset, layout.tag_size)),
                    EnumByteView::Niche {
                        niche_offset,
                        niche_size,
                        ..
                    } => Some((*niche_offset, *niche_size)),
                };
                if let Some((offset, size)) = tag_lane
                    && let Some(at) = image.slice(offset, size).first_uninit()
                {
                    return Ok(Some(offset + at));
                }
                let (variant_idx, _) = self.enum_image_variant(&layout, ty, image, state, block)?;
                layout.refuse_uninhabited(variant_idx, ty, "Load", block)?;
                let mut first: Option<u64> = None;
                for (rel_offset, field_ty) in &layout.variant_field_offsets[variant_idx] {
                    let offset = layout.payload_offset + rel_offset;
                    let f_size = self.byte_size(field_ty, block)?;
                    let field = image.slice(offset, f_size);
                    if let Some(at) = self.first_uninit_covered(field_ty, &field, state, block)? {
                        let at = offset + at;
                        first = Some(first.map_or(at, |first: u64| first.min(at)));
                    }
                }
                Ok(first)
            }
            _ => Ok(image.first_uninit()),
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
                kind: InterpretValueKind::FloatBits(self.eval_float_binop(
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
        // Lane-wise, on the operands' structure: a splat operand combines
        // with each stored lane of the other once.
        let lanes = lhs_lanes.try_zip_with(rhs_lanes, |lhs, rhs| {
            expect_ty(lhs, elem_ty, block)?;
            expect_ty(rhs, elem_ty, block)?;
            if matches!(elem_ty, Ty::Bool) {
                Ok(InterpretValue::bool(eval_bool_binop(
                    op,
                    expect_bool_value(lhs, block)?,
                    expect_bool_value(rhs, block)?,
                    block,
                )?))
            } else if elem_ty.is_float() {
                Ok(InterpretValue {
                    ty: elem_ty.clone(),
                    kind: InterpretValueKind::FloatBits(eval_float_binop(
                        op,
                        elem_ty,
                        expect_float_bits(lhs, block)?,
                        expect_float_bits(rhs, block)?,
                        block,
                    )?),
                })
            } else {
                let lhs = expect_int_value(lhs, block)?;
                let rhs = expect_int_value(rhs, block)?;
                Ok(InterpretValue {
                    ty: elem_ty.clone(),
                    kind: InterpretValueKind::Int(eval_int_binop(op, lhs, rhs, block)?),
                })
            }
        })?;
        // The arithmetic above keeps the rope's compressed traversal. A
        // requested witness describes logical lanes, so only this optional
        // observation walks them all (including repeated/splat lanes).
        if self.float_zero_choice_observer.is_some()
            && matches!(op, BinOp::FMin | BinOp::FMax)
            && elem_ty.is_float()
        {
            for ((left, right), result) in lhs_lanes.iter().zip(rhs_lanes.iter()).zip(lanes.iter())
            {
                if let (
                    InterpretValueKind::FloatBits(left),
                    InterpretValueKind::FloatBits(right),
                    InterpretValueKind::FloatBits(result),
                ) = (&left.kind, &right.kind, &result.kind)
                {
                    self.observe_float_zero_choice(op, elem_ty, *left, *right, *result);
                }
            }
        }
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Vector(lanes),
        })
    }

    fn eval_float_binop(
        &self,
        op: BinOp,
        ty: &Ty,
        lhs_bits: u64,
        rhs_bits: u64,
        block: BlockId,
    ) -> InterpretResult<u64> {
        let result = eval_float_binop(op, ty, lhs_bits, rhs_bits, block)?;
        self.observe_float_zero_choice(op, ty, lhs_bits, rhs_bits, result);
        Ok(result)
    }

    fn observe_float_zero_choice(
        &self,
        op: BinOp,
        ty: &Ty,
        lhs_bits: u64,
        rhs_bits: u64,
        result: u64,
    ) {
        if matches!(op, BinOp::FMin | BinOp::FMax)
            && let Some(observer) = self.float_zero_choice_observer
        {
            let width = match ty {
                Ty::F16 => 16,
                Ty::F32 => 32,
                Ty::F64 => 64,
                _ => return,
            };
            let sign = 1u64 << (width - 1);
            let mask = sign | (sign - 1);
            let left = lhs_bits & mask;
            let right = rhs_bits & mask;
            if left & (sign - 1) == 0 && right & (sign - 1) == 0 && left != right {
                observer(result & mask == left);
            }
        }
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
            let lanes = lane_values.try_map(|lane| {
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
            })?;
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
        state: &ExecState,
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
            let result = lhs_lanes.try_zip_with(rhs_lanes, |lhs, rhs| {
                expect_ty(lhs, elem_ty, block)?;
                expect_ty(rhs, elem_ty, block)?;
                if matches!(elem_ty.as_ref(), Ty::Bool) {
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
            })?;
            return Ok(InterpretValue {
                ty: ty.comparison_result_ty(),
                kind: InterpretValueKind::Vector(result),
            });
        }

        expect_ty(lhs, ty, block)?;
        expect_ty(rhs, ty, block)?;
        if matches!(ty, Ty::Ptr) {
            reject_partial(lhs, block, "pointer comparison")?;
            reject_partial(rhs, block, "pointer comparison")?;
            let pointer_int = |value: &InterpretValue| -> InterpretResult<InterpretInt> {
                // Use the same numeric address as PtrToInt, rather than the
                // allocation id: aliases may carry different provenance.
                let address = match value.kind {
                    InterpretValueKind::NullPtr => 0,
                    InterpretValueKind::Ptr(ptr) => state.memory.address(ptr, block, "ICmp")?,
                    InterpretValueKind::DanglingPtr(address) => address,
                    _ => return Err(type_error(block, "ICmp: expected pointer value")),
                };
                let address = state.memory.check_address(address, block, "ICmp")?;
                InterpretInt::from_raw(self.pointer_bits(), false, u128::from(address))
                    .ok_or_else(|| type_error(block, "ICmp: unsupported target pointer width"))
            };
            return Ok(InterpretValue::bool(eval_int_icmp(
                op,
                pointer_int(lhs)?,
                pointer_int(rhs)?,
            )));
        }
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
            let result = lhs_lanes.try_zip_with(rhs_lanes, |lhs, rhs| {
                expect_ty(lhs, elem_ty, block)?;
                expect_ty(rhs, elem_ty, block)?;
                Ok(InterpretValue::bool(eval_float_fcmp(
                    op,
                    elem_ty,
                    expect_float_bits(lhs, block)?,
                    expect_float_bits(rhs, block)?,
                    block,
                )?))
            })?;
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
                // Round the EXACT integer to the destination width once
                // (Rust `as`, RNE). An `f32` destination must not go through
                // an `f64` intermediate: `(2^60 + 2^36 + 1) as f64` rounds to
                // the binary32 halfway point, which then ties to even and
                // loses the `+1` that makes the exact value round up
                // (docs/ub-numerics-policy.md §2; WS2.23 cross-engine table).
                let bits = match dst_ty {
                    Ty::F32 => u64::from(
                        if matches!(op, CastOp::UIToFP) {
                            int.as_unsigned() as f32
                        } else {
                            int.as_signed() as f32
                        }
                        .to_bits(),
                    ),
                    // WS2.15: an `F16` destination goes through `f64`, and
                    // that IS a single rounding: an integer below `2^53` is
                    // exact in binary64, and one at or above it is at or
                    // above `2^53` after the binary64 rounding (monotone,
                    // `2^53` representable), which `f64_to_f16_bits` takes to
                    // `±inf` exactly as the exact value would round (the
                    // binary16 overflow threshold is `65520`).
                    Ty::F16 | Ty::F64 => {
                        let value = if matches!(op, CastOp::UIToFP) {
                            int.as_unsigned() as f64
                        } else {
                            int.as_signed() as f64
                        };
                        float_bits_from_f64(dst_ty, value, block)?
                    }
                    _ => {
                        return Err(type_error(
                            block,
                            format!("{op}: destination {dst_ty} is not float"),
                        ));
                    }
                };
                InterpretValueKind::FloatBits(bits)
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
                let address = state.memory.check_address(address, block, "IntToPtr")?;
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
            CastOp::Transmute => {
                // Executed exactly where the Lean `semCast .Transmute` arm
                // executes (`TrustIr/Semantics/Cast.lean`): over the subset-v3
                // scalar set (`I8`-`I128` / `U8`-`U128` / `Ptr`), int<->int at
                // one width, int<->ptr, and ptr<->ptr. Every other shape —
                // float or bool on EITHER side, aggregates, vectors,
                // pointer-width ints, `Char` — keeps `UnsupportedCast`, which
                // is what the Lean model also answers. The sanctioned
                // replacement for an int<->float reinterpret is `Bitcast`,
                // which both engines model through the IEEE bit pattern.
                if !(crate::bridge::transmute_scalar_ty(src_ty)
                    && crate::bridge::transmute_scalar_ty(dst_ty))
                {
                    return Err(err(
                        InterpretErrorCode::UnsupportedCast,
                        block,
                        format!(
                            "Transmute {src_ty} -> {dst_ty} is outside the executable scalar set \
                             (I8-I128 / U8-U128 / Ptr)"
                        ),
                    ));
                }
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
            CastOp::ReifyFnPointer => {
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
                    let address = state.memory.check_address(address, block, "Bitcast")?;
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
            // Lane-wise on the three operands' structure: the arms are paired
            // first, then each pair is chosen by its condition lane.
            let arms = then_lanes
                .rope()
                .try_zip_with(else_lanes.rope(), |then_val, else_val| {
                    Ok::<_, InterpretError>((then_val.clone(), else_val.clone()))
                })?;
            let result = ArrayValue::from_rope(cond_lanes.rope().try_zip_with(
                &arms,
                |cond, (then_val, else_val)| match cond.as_bool() {
                    Some(true) => Ok(then_val.clone()),
                    Some(false) => Ok(else_val.clone()),
                    None => Err(type_error(
                        block,
                        format!("vector select condition lane must be bool, got {}", cond.ty),
                    )),
                },
            )?);
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

    /// The ACTIVE variant of an in-register enum value `[tag, fields..]`: its
    /// name and declared field types, decoded from lane 0 through
    /// `EnumDef::effective_discriminants` (roadmap WS2.2 item 5).
    ///
    /// Only an interpreted `Aggregate` over a `Ty::Enum` reaches this. A tag
    /// that names no variant cannot arise from `Const` or a memory decode (both
    /// refuse it), so it is reported as a type error rather than guessed.
    fn enum_active_variant(
        &self,
        enum_ty: &Ty,
        values: &[InterpretValue],
        block: BlockId,
    ) -> InterpretResult<(&'m str, &'m [Ty])> {
        let Ty::Enum(eid) = enum_ty else {
            return Err(type_error(block, format!("{enum_ty} is not an enum")));
        };
        let module = self.module_context(block, "enum projection")?;
        let def = module
            .enum_def(*eid)
            .ok_or_else(|| type_error(block, format!("enum id {} not found in module", eid.0)))?;
        let discriminants = def.effective_discriminants().ok_or_else(|| {
            type_error(
                block,
                format!("enum {enum_ty} has no canonical discriminant assignment"),
            )
        })?;
        let tag = values
            .first()
            .and_then(InterpretValue::as_int)
            .ok_or_else(|| {
                type_error(
                    block,
                    format!("enum {enum_ty} value has no integer tag lane"),
                )
            })?;
        let disc = tag_int_discriminant(tag);
        let variant_idx = discriminants
            .iter()
            .position(|d| *d == disc)
            .ok_or_else(|| {
                type_error(
                    block,
                    format!("enum {enum_ty} value carries tag {disc}, which names no variant"),
                )
            })?;
        let variant = &def.variants[variant_idx];
        Ok((variant.name.as_str(), variant.fields.as_slice()))
    }

    /// WS2.2 item 5: lane `field >= 1` of an enum value must be a field of its
    /// ACTIVE variant, at `access_ty`. Projecting a lane of another variant is
    /// undefined behaviour (`docs/ub-numerics-policy.md` §4); the validator
    /// admits any lane SOME variant carries, because which variant is active
    /// is not a static fact of the type. Honest limit: a lane with the same
    /// type in the active and the intended variant is invisible here too — the
    /// flat form states no expected variant.
    fn check_enum_payload_lane(
        &self,
        enum_ty: &Ty,
        values: &[InterpretValue],
        field: u32,
        access_ty: &Ty,
        block: BlockId,
    ) -> InterpretResult<()> {
        let (name, fields) = self.enum_active_variant(enum_ty, values, block)?;
        let lane_ty = fields.get(field as usize - 1);
        if lane_ty != Some(access_ty) {
            let detail = match lane_ty {
                Some(lane_ty) => {
                    format!(" (lane {field} of {name} is {lane_ty}; the access is at {access_ty})")
                }
                None => format!(" ({name} has {} field(s))", fields.len()),
            };
            return Err(err(
                InterpretErrorCode::UndefinedBehavior,
                block,
                format!(
                    "enum {enum_ty}: lane {field} belongs to no field of active variant \
                     {name}{detail}"
                ),
            ));
        }
        Ok(())
    }

    /// WS3.5: build a fully-initialised aggregate VALUE from register lanes.
    ///
    /// The result is byte-for-byte the value the corresponding `Const` would
    /// produce for the same type — `Aggregate`/`Array`/`Record` over the same
    /// lanes, and for an enum the `[tag, fields..]` image whose lane 0 is
    /// `discriminants[variant]` at the canonical tag type — so everything
    /// downstream (`ExtractField`, `Store`/`Load`, the byte funnel) reads it
    /// identically. The difference is only where the lanes come from: SSA
    /// values, which `Constant` cannot spell for `Rc`/`&`/`&mut`/`*const`/
    /// `*mut` (F-049).
    ///
    /// `validate_module` refuses every ill-shaped case ahead of this; an
    /// UNVALIDATED module still fails closed here, never silently building a
    /// mistyped or partially-initialised value. In particular a poison lane is
    /// rejected: the result is documented as fully initialised, so it may not
    /// be assembled out of an uninitialised part.
    /// `ArraySplat { ty: Array(e, n), value }`: the array whose `n` elements
    /// are all `value`. Embedding a value in a lane INSPECTS it (a poison
    /// element is refused, as `make_aggregate` refuses a poison lane); the
    /// element type is held to `e` exactly. O(1) in `n`: the result is
    /// [`ArrayValue::splat`], one uniform node.
    fn eval_array_splat(
        &self,
        ty: &Ty,
        value: &InterpretValue,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        reject_partial(value, block, "array_splat")?;
        let Ty::Array(elem, len) = ty else {
            return Err(type_error(
                block,
                format!("array_splat builds an array type, got {ty}"),
            ));
        };
        let elem_ty = self.resolve_ty(*elem, block)?;
        expect_ty(value, &elem_ty, block)?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Array(ArrayValue::splat(value.clone(), *len)),
        })
    }

    fn eval_make_aggregate(
        &self,
        ty: &Ty,
        variant: Option<u32>,
        lanes: Vec<InterpretValue>,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        for lane in &lanes {
            reject_partial(lane, block, "make_aggregate")?;
        }
        let expect_no_variant = |kind: &str| -> InterpretResult<()> {
            if variant.is_some() {
                return Err(type_error(
                    block,
                    format!("make_aggregate of a {kind} ({ty}) carries no variant index"),
                ));
            }
            Ok(())
        };
        let check_arity = |declared: usize| -> InterpretResult<()> {
            if lanes.len() != declared {
                return Err(type_error(
                    block,
                    format!(
                        "make_aggregate {ty} has {} lanes, declared type requires {declared}",
                        lanes.len()
                    ),
                ));
            }
            Ok(())
        };
        let check_lane_tys = |declared: &[Ty]| -> InterpretResult<()> {
            for (lane, declared) in lanes.iter().zip(declared) {
                expect_ty(lane, declared, block)?;
            }
            Ok(())
        };
        match ty {
            Ty::Tuple(elem_tys) => {
                expect_no_variant("tuple")?;
                check_arity(elem_tys.len())?;
                check_lane_tys(elem_tys)?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(lanes),
                })
            }
            Ty::Struct(sid) => {
                expect_no_variant("struct")?;
                let module = self.module.ok_or_else(|| {
                    type_error(block, "make_aggregate of a struct requires module context")
                })?;
                let def = module.struct_def(*sid).ok_or_else(|| {
                    type_error(block, format!("struct id {} not found in module", sid.0))
                })?;
                check_arity(def.fields.len())?;
                let declared: Vec<Ty> = def.fields.iter().map(|f| f.ty.clone()).collect();
                check_lane_tys(&declared)?;
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(lanes),
                })
            }
            Ty::Record(record_id) => {
                expect_no_variant("record")?;
                let module = self.module.ok_or_else(|| {
                    type_error(block, "make_aggregate of a record requires module context")
                })?;
                let def = module.record_def(*record_id).ok_or_else(|| {
                    type_error(block, format!("record definition {record_id} not found"))
                })?;
                check_arity(def.fields.len())?;
                let declared: Vec<Ty> = def.fields.iter().map(|f| f.ty.clone()).collect();
                check_lane_tys(&declared)?;
                let named = def
                    .fields
                    .iter()
                    .map(|field| field.name.clone())
                    .zip(lanes)
                    .collect();
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Record(named),
                })
            }
            Ty::Array(elem, len) => {
                expect_no_variant("array")?;
                check_arity(*len as usize)?;
                let elem_ty = self.resolve_ty(*elem, block)?;
                for lane in &lanes {
                    expect_ty(lane, &elem_ty, block)?;
                }
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Array(ArrayValue::from_vec(lanes)),
                })
            }
            Ty::Enum(_) => {
                let Some(variant) = variant else {
                    return Err(type_error(
                        block,
                        format!("make_aggregate of enum {ty} requires a variant index"),
                    ));
                };
                let shape = self.enum_register_shape(ty, block)?;
                let variant_idx = variant as usize;
                let Some(variant_def) = shape.definition.variants.get(variant_idx) else {
                    return Err(type_error(
                        block,
                        format!(
                            "variant {variant} is out of range for {ty} ({} variants)",
                            shape.definition.variants.len()
                        ),
                    ));
                };
                // WS3.14: the same refusal `Const` gets. No value of an
                // uninhabited variant exists, and a niche layout may give it
                // no encoding at all.
                shape.refuse_uninhabited(variant_idx, ty, "make_aggregate", block)?;
                check_arity(variant_def.fields.len())?;
                check_lane_tys(&variant_def.fields)?;
                let disc = *shape.discriminants.get(variant_idx).ok_or_else(|| {
                    type_error(
                        block,
                        format!("variant {variant} has no discriminant in {ty}"),
                    )
                })?;
                let mut values = Vec::with_capacity(lanes.len() + 1);
                values.push(
                    InterpretValue::int(shape.tag_ty.clone(), disc)
                        .map_err(|e| e.with_block(block))?,
                );
                values.extend(lanes);
                Ok(InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Aggregate(values),
                })
            }
            // Vectors keep `InsertElement`, fat pointers keep `PtrFromParts`,
            // and closures/sequences/sets/dialects/handles have no lane rule
            // yet. `validate_module` refuses each by name
            // (`InvalidMakeAggregate`); an unvalidated module fails closed.
            _ => Err(type_error(
                block,
                format!("make_aggregate does not build {ty}"),
            )),
        }
    }

    /// `TensorContract { ty, lhs, rhs, batch, contract }` (PKG-U13a, XLA
    /// `DotGeneral`'s shape). The checks run in the order both engines share
    /// (SemR spells the same verdicts):
    ///
    /// 1. a poison operand is undefined behaviour (`reject_partial`), and a
    ///    runtime handle is refused (`reject_handle`);
    /// 2. the static rules, on the instruction and the operand VALUE types
    ///    (`TypeError`, which `validate_module` refuses ahead of this as
    ///    `InvalidTensorContract`): `ty`, `lhs` and `rhs` are tensors of one
    ///    integer element type; every paired axis is in range for its side;
    ///    no axis is paired twice on one side; and the result rank is
    ///    `|batch| + |left free| + |right free|`;
    /// 3. each operand's well-formedness, left then right (`TypeError`,
    ///    [`tensor_operand`]);
    /// 4. extent agreement, batch pairs in order then contract pairs in
    ///    order (undefined behaviour: shape agreement is a precondition of
    ///    the operation, never a type);
    /// 5. the result count `N`: `N >= 2^pointer_bits` is undefined behaviour,
    ///    decided exactly (a zero extent makes `N` 0) BEFORE anything is
    ///    allocated;
    /// 6. the elements.
    ///
    /// The result's axes are the batch axes (pair order), then the left free
    /// axes, then the right free axes (each ascending). Each result element,
    /// in row-major order, is a LEFT FOLD from 0 at the element type, over
    /// the contracted multi-index in row-major order (the first contract pair
    /// outermost), of `acc + l * r` through [`eval_int_binop`]'s wrapping
    /// `BinOp::Add` / `BinOp::Mul` (`docs/ub-numerics-policy.md` §1), with
    /// pointer-width elements at this run's pointer width. When some
    /// contracted extent is 0 every sum is empty, and the all-zero result is
    /// ONE uniform node ([`ArrayValue::splat`]), O(1) whatever `N`.
    fn eval_tensor_contract(
        &self,
        ty: &Ty,
        lhs: &InterpretValue,
        rhs: &InterpretValue,
        batch: &[(u32, u32)],
        contract: &[(u32, u32)],
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        reject_partial(lhs, block, "tensor_contract")?;
        reject_partial(rhs, block, "tensor_contract")?;
        reject_handle(lhs, block, "TensorContract")?;
        reject_handle(rhs, block, "TensorContract")?;

        // Static rule 1: three tensor types over one integer element type.
        let Ty::Tensor(result_elem, result_rank) = ty else {
            return Err(type_error(
                block,
                format!("tensor contraction: the result type {ty} is not a tensor type"),
            ));
        };
        let Ty::Tensor(lhs_elem, lhs_rank) = &lhs.ty else {
            return Err(type_error(
                block,
                format!(
                    "tensor contraction: the left operand has type {}, not a tensor type",
                    lhs.ty
                ),
            ));
        };
        let Ty::Tensor(rhs_elem, rhs_rank) = &rhs.ty else {
            return Err(type_error(
                block,
                format!(
                    "tensor contraction: the right operand has type {}, not a tensor type",
                    rhs.ty
                ),
            ));
        };
        if lhs_elem != result_elem || rhs_elem != result_elem {
            return Err(type_error(
                block,
                format!(
                    "tensor contraction: element types differ (result {result_elem}, left \
                     {lhs_elem}, right {rhs_elem})"
                ),
            ));
        }
        let elem: &Ty = result_elem;
        if !elem.is_integer() {
            return Err(type_error(
                block,
                format!("tensor contraction: element type {elem} is not an integer type"),
            ));
        }
        let (p, q, r) = (*lhs_rank, *rhs_rank, *result_rank);

        // Static rule 2: every paired axis is in range for its side.
        for &(a, b) in batch.iter().chain(contract) {
            if a >= p {
                return Err(type_error(
                    block,
                    format!("tensor contraction: left axis {a} is out of range for rank {p}"),
                ));
            }
            if b >= q {
                return Err(type_error(
                    block,
                    format!("tensor contraction: right axis {b} is out of range for rank {q}"),
                ));
            }
        }
        // Static rule 3: no axis is paired twice on one side.
        let mut lhs_paired = BTreeSet::new();
        let mut rhs_paired = BTreeSet::new();
        for &(a, b) in batch.iter().chain(contract) {
            if !lhs_paired.insert(a) {
                return Err(type_error(
                    block,
                    format!("tensor contraction: left axis {a} is paired twice"),
                ));
            }
            if !rhs_paired.insert(b) {
                return Err(type_error(
                    block,
                    format!("tensor contraction: right axis {b} is paired twice"),
                ));
            }
        }
        // Static rule 4: the result rank. Rules 2 and 3 make the paired axes
        // distinct and in range on each side, so `paired <= p` and
        // `paired <= q`: the subtractions cannot underflow, and nothing here
        // allocates in the (unchecked) ranks.
        let paired = (batch.len() + contract.len()) as u64;
        let expected = batch.len() as u64 + (u64::from(p) - paired) + (u64::from(q) - paired);
        if u64::from(r) != expected {
            return Err(type_error(
                block,
                format!(
                    "tensor contraction: the result rank is {r}, but {} batch, {} left free and \
                     {} right free axes make {expected}",
                    batch.len(),
                    u64::from(p) - paired,
                    u64::from(q) - paired
                ),
            ));
        }

        // Runtime well-formedness of each operand, left then right.
        let pointer_bits = self.pointer_bits();
        let (lhs_dims, lhs_elems) = tensor_operand(
            lhs,
            "tensor contraction",
            "left",
            elem,
            p,
            pointer_bits,
            block,
        )?;
        let (rhs_dims, rhs_elems) = tensor_operand(
            rhs,
            "tensor contraction",
            "right",
            elem,
            q,
            pointer_bits,
            block,
        )?;

        // The precondition: paired axes agree, batch pairs then contract
        // pairs. Every index is in range (rule 2, `dims.len() == rank`).
        for &(a, b) in batch.iter().chain(contract) {
            if lhs_dims[a as usize] != rhs_dims[b as usize] {
                return Err(ub(block, TENSOR_EXTENT_MISMATCH));
            }
        }

        // The result shape, and its count, decided before anything is
        // allocated. Free axes are O(rank), which the operand payloads (one
        // extent per axis, checked above) already hold.
        let lhs_free: Vec<u32> = (0..p).filter(|a| !lhs_paired.contains(a)).collect();
        let rhs_free: Vec<u32> = (0..q).filter(|b| !rhs_paired.contains(b)).collect();
        let result_dims: Vec<u64> = batch
            .iter()
            .map(|&(a, _)| lhs_dims[a as usize])
            .chain(lhs_free.iter().map(|&a| lhs_dims[a as usize]))
            .chain(rhs_free.iter().map(|&b| rhs_dims[b as usize]))
            .collect();
        let usize_limit = 1u128.checked_shl(pointer_bits).unwrap_or(u128::MAX);
        let count = exact_product_below(&result_dims, usize_limit)
            .ok_or_else(|| ub(block, TENSOR_RESULT_TOO_LARGE))?;

        let (bits, signed) = int_shape_at(elem, pointer_bits).ok_or_else(|| {
            type_error(
                block,
                format!("tensor contraction: element type {elem} has no integer shape"),
            )
        })?;
        let zero = InterpretInt::from_raw(bits, signed, 0).ok_or_else(|| {
            type_error(
                block,
                format!("tensor contraction: unsupported integer width {bits}"),
            )
        })?;
        let contracted: Vec<u64> = contract
            .iter()
            .map(|&(a, _)| lhs_dims[a as usize])
            .collect();
        if count == 0 || contracted.contains(&0) {
            // No element, or every sum empty: one uniform node of zeros.
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Tensor {
                    dims: result_dims,
                    elems: ArrayValue::splat(
                        InterpretValue {
                            ty: elem.clone(),
                            kind: InterpretValueKind::Int(zero),
                        },
                        count,
                    ),
                },
            });
        }

        // From here every result extent and every contracted extent is
        // nonzero, so every extent of both operands is (each axis is a batch,
        // contracted or free axis): every stride and the term count are at
        // most an operand's element count, a `u64`. The `TypeError`s below
        // are unreachable defences, not verdicts.
        let overflow = || {
            type_error(
                block,
                "tensor contraction: operand strides exceed the element count",
            )
        };
        let terms = exact_product_below(&contracted, 1u128 << 64).ok_or_else(overflow)?;
        let lhs_strides = row_major_strides(lhs_dims).ok_or_else(overflow)?;
        let rhs_strides = row_major_strides(rhs_dims).ok_or_else(overflow)?;
        // Per result axis, the stride it advances in each operand (0 where it
        // is not that operand's axis); per contract pair, the same.
        let mut out_lhs = Vec::with_capacity(result_dims.len());
        let mut out_rhs = Vec::with_capacity(result_dims.len());
        for &(a, b) in batch {
            out_lhs.push(lhs_strides[a as usize]);
            out_rhs.push(rhs_strides[b as usize]);
        }
        for &a in &lhs_free {
            out_lhs.push(lhs_strides[a as usize]);
            out_rhs.push(0);
        }
        for &b in &rhs_free {
            out_lhs.push(0);
            out_rhs.push(rhs_strides[b as usize]);
        }
        let sum_lhs: Vec<u64> = contract
            .iter()
            .map(|&(a, _)| lhs_strides[a as usize])
            .collect();
        let sum_rhs: Vec<u64> = contract
            .iter()
            .map(|&(_, b)| rhs_strides[b as usize])
            .collect();
        let fetch = |elems: &ArrayValue, at: u64| -> InterpretResult<InterpretInt> {
            elems
                .get(at)
                .and_then(InterpretValue::as_int)
                .ok_or_else(|| {
                    type_error(block, "tensor contraction: an operand element is missing")
                })
        };
        let elems = ArrayValue::try_from_elements((0..count).map(|flat| -> InterpretResult<_> {
            let (lhs_base, rhs_base) = row_major_offsets(flat, &result_dims, &out_lhs, &out_rhs);
            let mut acc = zero;
            for term in 0..terms {
                let (lhs_at, rhs_at) = row_major_offsets(term, &contracted, &sum_lhs, &sum_rhs);
                let left = fetch(lhs_elems, lhs_base + lhs_at)?;
                let right = fetch(rhs_elems, rhs_base + rhs_at)?;
                let product = eval_int_binop(BinOp::Mul, left, right, block)?;
                acc = eval_int_binop(BinOp::Add, acc, product, block)?;
            }
            Ok(InterpretValue {
                ty: elem.clone(),
                kind: InterpretValueKind::Int(acc),
            })
        }))?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Tensor {
                dims: result_dims,
                elems,
            },
        })
    }

    fn eval_extract_field(
        &self,
        field_ty: &Ty,
        aggregate: &InterpretValue,
        field: u32,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        reject_partial(aggregate, block, "extract_field")?;
        if let (Ty::Enum(_), InterpretValueKind::Aggregate(values)) =
            (&aggregate.ty, &aggregate.kind)
            && field >= 1
        {
            self.check_enum_payload_lane(&aggregate.ty, values, field, field_ty, block)?;
        }
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
        // Crystal lane (E3b): reading a lane the program never wrote is MIR's typed read of an
        // uninitialised place -- undefined behaviour, reported where the read happens.
        if matches!(value.kind, InterpretValueKind::Uninit) {
            return Err(ub(
                block,
                format!(
                    "extract_field: field {field} of {} is an unwritten lane (uninit); reading \
                     it is a read of uninitialized memory",
                    aggregate.ty
                ),
            ));
        }
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
        if let (Ty::Enum(_), InterpretValueKind::Aggregate(values)) =
            (&aggregate.ty, &aggregate.kind)
        {
            // WS2.2 item 2: a variant is constructed whole with `Const`; a
            // re-tag would leave the old variant's payload under the new tag.
            // Lean's `semInsertField` refuses the same write.
            if field == 0 {
                return Err(err(
                    InterpretErrorCode::UndefinedBehavior,
                    block,
                    format!(
                        "insert_field cannot rewrite an enum discriminant (lane 0 of \
                         {aggregate_ty}); construct the variant with Const"
                    ),
                ));
            }
            self.check_enum_payload_lane(&aggregate.ty, values, field, &value.ty, block)?;
        }
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
            // O(height) whatever the length: a splat answers from its root.
            InterpretValueKind::Array(values)
            | InterpretValueKind::Vector(values)
            | InterpretValueKind::Sequence(values) => values.get(index as u64),
            InterpretValueKind::Aggregate(values) => values.get(index),
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
        // Embedding a value in a lane INSPECTS it, exactly as `insert_field`
        // does: a poison lane inside an otherwise-defined array / vector /
        // sequence would carry poison past every top-level check — out of a
        // call or return (`check_signature_values` sees only the aggregate)
        // and into a strict store (roadmap WS2.10 review).
        reject_partial(value, block, "insert_element value")?;
        match &array.kind {
            // PERSISTENT update: one root-to-leaf path is copied and every
            // other node is shared with the input (which SSA keeps alive), so
            // an insert costs O(height), never a copy of the array or vector.
            InterpretValueKind::Vector(values) => {
                let Some(existing) = values.get(index as u64) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("element {index} is out of bounds for {}", array.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let values = values
                    .set(index as u64, value.clone())
                    .expect("the index was just found in bounds");
                Ok(InterpretValue {
                    ty: result_ty.clone(),
                    kind: InterpretValueKind::Vector(values),
                })
            }
            InterpretValueKind::Array(values) => {
                let Some(existing) = values.get(index as u64) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("element {index} is out of bounds for {}", array.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let values = values
                    .set(index as u64, value.clone())
                    .expect("the index was just found in bounds");
                Ok(InterpretValue {
                    ty: result_ty.clone(),
                    kind: InterpretValueKind::Array(values),
                })
            }
            InterpretValueKind::Sequence(values) => {
                let Some(existing) = values.get(index as u64) else {
                    return Err(err(
                        InterpretErrorCode::UndefinedBehavior,
                        block,
                        format!("element {index} is out of bounds for {}", array.ty),
                    ));
                };
                expect_ty(value, &existing.ty, block)?;
                let values = values
                    .set(index as u64, value.clone())
                    .expect("the index was just found in bounds");
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

        // Every `vector` dialect op is decoded at one of the dialect's FIXED
        // shapes (at most 16 lanes, `vector::decode_with_operand_tys`), so its
        // lanes are handled as a dense list here.
        match spec {
            VectorSpec::PackLanes(spec) => {
                let mut lanes = Vec::with_capacity(spec.lanes as usize);
                for operand in operands {
                    expect_ty(&operand, &spec.elem_ty, block)?;
                    // A lane is embedded, so it is inspected: poison may not
                    // hide inside a vector (see `eval_insert_element`).
                    reject_partial(&operand, block, &op.qualified_name())?;
                    lanes.push(operand);
                }
                Ok(vec![InterpretValue {
                    ty: spec.vector_ty,
                    kind: InterpretValueKind::Vector(ArrayValue::from_vec(lanes)),
                }])
            }
            VectorSpec::ExtractLane(spec) => {
                let vector = &operands[0];
                expect_ty(vector, &spec.vector_ty, block)?;
                let lanes = expect_vector_lanes(vector, spec.lanes, block)?;
                let lane = lanes.get(u64::from(spec.lane)).ok_or_else(|| {
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
                reject_partial(value, block, &op.qualified_name())?;
                let lanes = expect_vector_lanes(vector, spec.lanes, block)?
                    .set(u64::from(spec.lane), value.clone())
                    .ok_or_else(|| {
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
                Ok(vec![InterpretValue {
                    ty: spec.vector_ty,
                    kind: InterpretValueKind::Vector(lanes),
                }])
            }
            VectorSpec::MaskToBits(spec) => {
                let mask = &operands[0];
                expect_ty(mask, &spec.mask_ty, block)?;
                let lanes = expect_vector_lanes(mask, spec.lanes, block)?.to_vec();
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
                let lanes = expect_vector_lanes(vector, spec.lanes, block)?.to_vec();
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
                let lanes = expect_vector_lanes(vector, spec.lanes, block)?.to_vec();
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
                    kind: InterpretValueKind::Vector(ArrayValue::from_vec(shuffled)),
                }])
            }
            VectorSpec::Fma(spec) => {
                let a = &operands[0];
                let b = &operands[1];
                let c = &operands[2];
                expect_ty(a, &spec.vector_ty, block)?;
                expect_ty(b, &spec.vector_ty, block)?;
                expect_ty(c, &spec.vector_ty, block)?;
                let a_lanes = expect_vector_lanes(a, spec.lanes, block)?.to_vec();
                let b_lanes = expect_vector_lanes(b, spec.lanes, block)?.to_vec();
                let c_lanes = expect_vector_lanes(c, spec.lanes, block)?.to_vec();
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
                    kind: InterpretValueKind::Vector(ArrayValue::from_vec(out)),
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
    /// The OPEN binding-frame lineages (quantifier-lowering scopes). The slot
    /// contents live in the handles themselves (`InterpretValueKind::Frame`),
    /// which are FUNCTIONAL like Lean's `Value.frame`: `OpenFrame` mints a
    /// lineage, `BindSlot` checks it is open and yields a new handle with one
    /// slot replaced (the input handle keeps its prior slots), `LoadSlot`
    /// checks it is open and reads the handle's own snapshot, `CloseFrame`
    /// removes the lineage (a second close is UB). An unbound slot is `None`:
    /// loading it is UB here, where the Lean model initialises it to `undef`
    /// — what an unbound read yields is WS2.10's decision (B3 depth ledger).
    frames: BTreeSet<u64>,
    next_frame_id: u64,
    steps: u64,
    remaining_fuel: u64,
    /// The host model's per-execution tables (WS2.12).
    host: HostState,
    /// Calls a host model served in this run (`InterpretOutcome::host_calls`).
    /// Counted here, outside `HostState`, so a host cannot alter it.
    host_calls: u64,
    /// The module's drop-glue table, indexed once per run (amendment D,
    /// `docs/SPEC_RATIFICATIONS.md` §20). `None` without a module: every drop
    /// is then unresolvable.
    drop_glue: Option<crate::DropGlueIndex>,
    /// Exceptions in flight and in hand (amendment D, Part 2, §21); empty for
    /// every run under `PanicStrategy::Abort`.
    unwind: UnwindState,
}

/// The run's exceptions (amendment D, Part 2, `docs/SPEC_RATIFICATIONS.md`
/// §21). Only `PanicStrategy::Unwind` ever writes it.
#[derive(Debug, Clone, Default)]
struct UnwindState {
    /// Every exception object raised in this run, by the ADDRESS of its
    /// (dead) one-byte allocation: its pointer and the `Panic` error its raise
    /// reported. A `Resume` identifies its operand by address, so a stored
    /// and reloaded exception pointer (a no-provenance pointer once its
    /// allocation is dead) is the same exception.
    exceptions: BTreeMap<u64, (InterpretPointer, InterpretError)>,
    /// The exception being propagated, set by a raise, a `Resume` or a pad
    /// that re-propagates, and taken by the catch that receives it. No
    /// instruction runs between the raise and the catch (an error propagates
    /// through `?` only), so while this is `Some` the error travelling up the
    /// frames IS that exception's.
    in_flight: Option<u64>,
    /// The (exception, selector) the landing pad an unwind edge entered binds
    /// and clears.
    in_hand: Option<(InterpretPointer, i32)>,
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
    /// The highest address this run's pointers can name: `2^pointer_bits - 1`
    /// (WS2.16). `u64::MAX` at 64 bits, where every check against it is
    /// vacuous and the model is byte-identical to the pre-WS2.16 one.
    max_address: u64,
    /// Crystal lane (E3b): per allocation, the byte RANGES a `Store` left uninitialised because
    /// the stored aggregate's lane there was UNWRITTEN (`InterpretValueKind::Uninit`), as
    /// disjoint `start -> end` (exclusive) entries: one entry per lane, whatever its size. A
    /// later whole-aggregate `Load` whose only uninitialised COVERED bytes are such lanes gives
    /// the lanes back unwritten; every other uninitialised covered byte keeps the WS2.14
    /// aggregate-load discipline. Any write over a byte forgets it (a `MemSet` fill and a
    /// `MemCopy` destination included); a `MemCopy` does NOT carry the record to its
    /// destination, so a copied unwritten lane reloads as ordinary uninitialised bytes (fail
    /// closed; pinned by `a_memcopy_does_not_carry_the_unwritten_lane_record`). Empty for every
    /// program with no `Constant::Uninit`, so no such program's memory behaviour changes.
    unwritten_lane_bytes: BTreeMap<u64, BTreeMap<u64, u64>>,
}

impl Default for MemoryState {
    fn default() -> Self {
        Self {
            allocations: BTreeMap::new(),
            next_alloc_id: 0,
            next_addr: 1024,
            max_address: u64::MAX,
            unwritten_lane_bytes: BTreeMap::new(),
        }
    }
}

impl MemoryState {
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

        let footprint = size.checked_add(slack).ok_or_else(|| {
            err(
                InterpretErrorCode::OutOfMemory,
                block,
                format!("allocation of {size} byte(s) plus slack overflows the address space"),
            )
        })?;

        // Exhausting the ADDRESS SPACE is an incapacity of the model, not UB
        // in the program (a real allocator returns null / aborts there).
        let exhausted = || {
            err(
                InterpretErrorCode::OutOfMemory,
                block,
                format!("allocation of {size} byte(s) exhausts the address space"),
            )
        };
        let base = align_addr(self.next_addr, align).ok_or_else(exhausted)?;
        let id = self.next_alloc_id;
        self.next_alloc_id = self
            .next_alloc_id
            .checked_add(1)
            .ok_or_else(|| ub(block, "Alloca: allocation id overflow"))?;
        let bump = footprint.max(1);
        let next_addr = base.checked_add(bump).ok_or_else(exhausted)?;
        // The allocation's last byte must be nameable by a target pointer
        // (WS2.16): a 32-bit target has a 4 GiB address space, and an
        // allocation past it has no address a `Ptr` could store.
        if next_addr - 1 > self.max_address {
            return Err(err(
                InterpretErrorCode::OutOfMemory,
                block,
                format!(
                    "allocation of {size} byte(s) at address {base:#x} exceeds the target's \
                     address space (highest address {:#x})",
                    self.max_address
                ),
            ));
        }
        self.next_addr = next_addr;
        // SPARSE: the requested region is one uninitialized run and the slack
        // tail one defined run, whatever the size — host memory follows what
        // the program writes, not what it declares.
        let mut bytes = ByteStore::new(footprint, None);
        bytes.write(size, &Image::fill(Some(SLACK_FILL), slack));
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
                origin: None,
                requested: size,
                live_borrows: 0,
            },
        );
        Ok(InterpretPointer {
            allocation: id,
            offset: 0,
        })
    }

    /// Record that the allocation `ptr` names was made by `HeapAlloc` with
    /// `origin` (WS2.13). Only called right after `alloc_with_slack` returned
    /// `ptr`, so the allocation exists.
    fn record_origin(&mut self, ptr: InterpretPointer, origin: AllocOrigin) {
        if let Some(allocation) = self.allocations.get_mut(&ptr.allocation) {
            allocation.origin = Some(origin);
        }
    }

    /// The precondition of a pinned RC runtime's entry point on its object
    /// pointer (WS2.13, [`HostRcOp`]): `ptr` addresses a live allocation, at
    /// its base, that `HeapAlloc { origin }` produced. Anything else is UB in
    /// the runtime and is refused here by name.
    fn check_rc_cell(
        &self,
        ptr: InterpretPointer,
        origin: AllocOrigin,
        entry: &str,
        block: BlockId,
    ) -> InterpretResult<()> {
        let Some(allocation) = self.allocations.get(&ptr.allocation) else {
            return Err(ub(
                block,
                format!("@{entry}: pointer does not reference a known allocation"),
            ));
        };
        if !allocation.alive {
            return Err(ub(
                block,
                format!("@{entry}: pointer references a freed allocation"),
            ));
        }
        if allocation.origin != Some(origin) {
            let actual = match allocation.origin {
                Some(other) => format!("a {other:?} heap cell"),
                None => "a stack or global allocation".to_owned(),
            };
            return Err(ub(
                block,
                format!(
                    "@{entry}: pointer addresses {actual}, not a cell of the {origin:?} heap \
                     this runtime counts (no ownership transfer between heaps)"
                ),
            ));
        }
        if !ptr.is_object_base() {
            return Err(ub(
                block,
                format!(
                    "@{entry}: pointer is at offset {} of its allocation, not at the object \
                     base a runtime object pointer names",
                    ptr.offset
                ),
            ));
        }
        Ok(())
    }

    /// ARC `Retain`: increment the pointee allocation's reference count. The
    /// pointer must address a live reference-counted cell AT ITS OBJECT BASE
    /// (`arc_allocation_mut`); "the cell" is the allocation the pointer was
    /// derived from (SPEC "A pointer operand names the allocation it was
    /// derived from"), and any other offset of it is undefined behaviour, as
    /// on the pinned runtime path (`check_rc_cell`): one predicate,
    /// `InterpretPointer::is_object_base` (SPEC "An ARC operation counts only
    /// a reference-counted cell", clause 3).
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

    /// ARC `IsUnique`: true iff the pointee reference-counted cell has exactly
    /// one owner. The cell rule is `arc_allocation_mut`'s, checked here too.
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
        // SPEC "An ARC operation counts only a reference-counted cell": see
        // `arc_allocation_mut`, which states the rule for `Retain` / `Release`.
        if !allocation
            .origin
            .is_some_and(AllocOrigin::is_reference_counted)
        {
            let actual = match allocation.origin {
                Some(other) => format!("a {other:?} heap cell"),
                None => "a stack, global or interpreter-internal allocation".to_owned(),
            };
            return Err(ub(
                block,
                format!(
                    "IsUnique: pointer addresses {actual}, not a reference-counted cell \
                     (Retain / Release / IsUnique are defined only on a HeapAlloc of origin \
                     SwiftHeap or CleanHeap; Lean requireArcRef)"
                ),
            ));
        }
        // SPEC "An ARC operation counts only a reference-counted cell",
        // clause 3: at the cell's object base only (see `arc_allocation_mut`).
        if !ptr.is_object_base() {
            return Err(ub(
                block,
                format!(
                    "IsUnique: pointer is at offset {} of its cell, not at the object base a \
                     runtime object pointer names",
                    ptr.offset
                ),
            ));
        }
        Ok(allocation.ref_count == 1)
    }

    /// The allocation a `Retain` / `Release` names, after the cell rule: the
    /// pointer's allocation is known, live, and a REFERENCE-COUNTED CELL — a
    /// `HeapAlloc { origin: SwiftHeap | CleanHeap }` result. On any other live
    /// allocation (a stack `Alloca`, a `RustHeap` or `CMalloc` cell, a
    /// global's reservation, an interpreter-internal cell) the three ARC
    /// instructions are undefined behaviour (SPEC "An ARC operation counts only
    /// a reference-counted cell"). Lean's `requireArcRef` refuses the same
    /// allocations (only an RC-origin `semHeapAlloc` grants `arcRef`), and the
    /// pinned runtime would read or write a header such a cell does not have.
    /// "The allocation" is the one the pointer was derived from, and the
    /// pointer must be at its OBJECT BASE (`InterpretPointer::is_object_base`,
    /// clause 3 of the same SPEC section): `clean_inc` / `clean_dec` /
    /// `clean_is_exclusive` read the header at the object pointer they are
    /// given, so an interior or past-the-end operand has no lowering. The
    /// offset is checked AFTER the origin, so an operand whose provenance is
    /// not a reference-counted cell keeps "not a reference-counted cell".
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
        if !allocation
            .origin
            .is_some_and(AllocOrigin::is_reference_counted)
        {
            let actual = match allocation.origin {
                Some(other) => format!("a {other:?} heap cell"),
                None => "a stack, global or interpreter-internal allocation".to_owned(),
            };
            return Err(ub(
                block,
                format!(
                    "{op}: pointer addresses {actual}, not a reference-counted cell \
                     (Retain / Release / IsUnique are defined only on a HeapAlloc of origin \
                     SwiftHeap or CleanHeap; Lean requireArcRef)"
                ),
            ));
        }
        if !ptr.is_object_base() {
            return Err(ub(
                block,
                format!(
                    "{op}: pointer is at offset {} of its cell, not at the object base a runtime \
                     object pointer names",
                    ptr.offset
                ),
            ));
        }
        Ok(allocation)
    }

    /// The compact image of `size` bytes at `ptr`, after the bounds /
    /// liveness / alignment check (`checked_access`). It shares the covering
    /// runs' nodes: O(runs touched × height), whatever `size` is — a load of a
    /// stored splat reads one repeating run.
    fn read_image(
        &self,
        ptr: InterpretPointer,
        size: u64,
        align: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<Image> {
        let allocation = self.checked_access(ptr, size, align, block, op)?;
        Ok(allocation.bytes.read(ptr.offset, size))
    }

    /// Write a compact image VERBATIM at `ptr` (`None` bytes become
    /// uninitialized), after the same access check as `write`. O(pieces +
    /// literal bytes): a repeating piece is stored as one run.
    fn write_image(
        &mut self,
        ptr: InterpretPointer,
        image: &Image,
        align: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<()> {
        self.checked_access(ptr, image.len(), align, block, op)?;
        let allocation = self.allocations.get_mut(&ptr.allocation).expect("checked");
        allocation.bytes.write(ptr.offset, image);
        // Crystal lane (E3b): any write over an unwritten-lane byte writes it, so the
        // record goes (a `MemSet` fill, a `MemCopy` destination and a poison transport
        // included: their uninitialised bytes are ordinary uninitialised bytes).
        self.forget_unwritten_lane_bytes(ptr, image.len());
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
        self.write_image(ptr, &Image::literal(bytes.to_vec()), align, block, op)
    }

    /// Fill `count` bytes at `ptr` with `byte`, every one INITIALIZED (the
    /// `MemSet` store, WS3.20). The bounds / liveness check runs BEFORE any
    /// image is materialized: the count is a DYNAMIC operand a hostile module
    /// can set to `u64::MAX`, and building a `vec![byte; count]` first would
    /// abort the process on capacity overflow instead of faulting the module
    /// (review finding, 2026-09-21). A count that does not fit the allocation
    /// therefore faults with the ordinary out-of-bounds UB, never allocates.
    fn fill(
        &mut self,
        ptr: InterpretPointer,
        byte: u8,
        count: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<()> {
        // One run, whatever `count` is (the access check proved it fits).
        self.write_image(ptr, &Image::fill(Some(byte), count), 1, block, op)
    }

    /// Crystal lane (E3b): store the byte image of an aggregate that carries UNWRITTEN lanes.
    /// `image` is the image to write (padding and the unwritten lanes already uninitialised);
    /// `lanes` names the unwritten lanes' byte ranges (`(offset, len)` relative to `ptr`), which
    /// are recorded as unwritten-lane bytes, so a whole-aggregate reload returns them unwritten.
    /// Any record the range held before is forgotten first (by the write).
    fn write_with_unwritten_lanes(
        &mut self,
        ptr: InterpretPointer,
        image: &Image,
        lanes: &[(u64, u64)],
        align: u64,
        block: BlockId,
        op: &str,
    ) -> InterpretResult<()> {
        self.write_image(ptr, image, align, block, op)?;
        let holes: Vec<(u64, u64)> = lanes
            .iter()
            .filter(|(_, len)| *len > 0)
            .map(|(start, len)| (ptr.offset + start, ptr.offset + start + len))
            .collect();
        if !holes.is_empty() {
            self.unwritten_lane_bytes
                .entry(ptr.allocation)
                .or_default()
                .extend(holes);
        }
        Ok(())
    }

    /// Forget the unwritten-lane record of `len` bytes at `ptr` (any write over them). The
    /// recorded ranges are disjoint and sorted, so the ones meeting the write are a suffix of
    /// those starting before its end: O(ranges met × log ranges), never the byte count.
    fn forget_unwritten_lane_bytes(&mut self, ptr: InterpretPointer, len: u64) {
        let Some(holes) = self.unwritten_lane_bytes.get_mut(&ptr.allocation) else {
            return;
        };
        let (lo, hi) = (ptr.offset, ptr.offset.saturating_add(len));
        let met: Vec<(u64, u64)> = holes
            .range(..hi)
            .rev()
            .take_while(|(_, end)| **end > lo)
            .map(|(start, end)| (*start, *end))
            .collect();
        for (start, end) in met {
            holes.remove(&start);
            if start < lo {
                holes.insert(start, lo);
            }
            if end > hi {
                holes.insert(hi, end);
            }
        }
        if holes.is_empty() {
            self.unwritten_lane_bytes.remove(&ptr.allocation);
        }
    }

    /// The recorded unwritten-lane ranges meeting the `len` bytes at `ptr`, clipped to them
    /// and relative to `ptr` (`(offset, len)`). Empty for an allocation with no record.
    fn unwritten_lanes_in(&self, ptr: InterpretPointer, len: u64) -> Vec<(u64, u64)> {
        let Some(holes) = self.unwritten_lane_bytes.get(&ptr.allocation) else {
            return Vec::new();
        };
        let (lo, hi) = (ptr.offset, ptr.offset.saturating_add(len));
        let mut met: Vec<(u64, u64)> = holes
            .range(..hi)
            .rev()
            .take_while(|(_, end)| **end > lo)
            .map(|(start, end)| {
                let (start, end) = ((*start).max(lo), (*end).min(hi));
                (start - lo, end - start)
            })
            .collect();
        met.reverse();
        met
    }

    /// The live-borrow count a thin `Borrow` / `BorrowMut` / `EndBorrow`
    /// operand moves (SPEC "Freeing an allocation under a live borrow is
    /// undefined behaviour", clause 2): the count of the allocation the
    /// pointer was derived from, and only while that allocation is live and
    /// the offset lies inside the bytes it requested. Anywhere else (one past
    /// the end, the heap slack tail, a zero-size or freed allocation) `None`,
    /// and the instruction moves no count. Never faults: it must stay free of
    /// every UB site, because trust-cg's fsym call graph follows it.
    fn borrow_count_mut(&mut self, ptr: InterpretPointer) -> Option<&mut u64> {
        self.allocations
            .get_mut(&ptr.allocation)
            .filter(|a| a.alive && ptr.offset < a.requested)
            .map(|a| &mut a.live_borrows)
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
        // One meaning for `Dealloc` of a reference-counted cell (SPEC "A
        // reference-counted cell is released by `Release`, never by
        // `Dealloc`"): a `SwiftHeap` / `CleanHeap` cell is released only by
        // the `Release` that takes its count to zero (or, under a host model,
        // by the call the host classifies as that runtime's release role).
        // Freeing it here would free it under a live owner. Lean's
        // `semDealloc` refuses the same cell (its `arcRef` permission cannot
        // deallocate), so both engines call this undefined behaviour — Lean
        // for a scalar-typed cell; an aggregate `HeapAlloc` is
        // `unsupported.layout` there, so for one this check alone decides.
        if let Some(origin) = allocation
            .origin
            .filter(|origin| origin.is_reference_counted())
        {
            return Err(ub(
                block,
                format!(
                    "Dealloc of a {origin:?} cell: a reference-counted cell is released only \
                     by the Release that takes its count to zero (Lean semDealloc)"
                ),
            ));
        }
        // SPEC "Freeing an allocation under a live borrow is undefined
        // behaviour": a `Borrow` / `BorrowMut` not yet ended by an `EndBorrow`
        // forbids the free, as Lean's `semDealloc` refuses a `sharedBorrow n` /
        // `uniqueBorrow` permission (`Permission.canDealloc`).
        if allocation.live_borrows > 0 {
            return Err(ub(
                block,
                format!(
                    "Dealloc: allocation is under a live borrow ({} Borrow / BorrowMut not \
                     ended by EndBorrow; Lean semDealloc)",
                    allocation.live_borrows
                ),
            ));
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
            .filter(|address| *address <= self.max_address)
            .ok_or_else(|| ub(block, format!("{op}: pointer address overflow")))
    }

    /// Refuse an address a target pointer cannot hold (WS2.16): past
    /// `2^pointer_bits - 1` a pointer value has no byte image. Vacuous at 64
    /// bits.
    fn check_address(&self, address: u64, block: BlockId, op: &str) -> InterpretResult<u64> {
        if address <= self.max_address {
            Ok(address)
        } else {
            Err(ub(
                block,
                format!(
                    "{op}: address {address:#x} is outside the target's address space \
                     (highest address {:#x})",
                    self.max_address
                ),
            ))
        }
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
    /// The allocation's bytes, SPARSE: runs of compact images tiling
    /// `[0, size)` (`None` = uninitialized).
    bytes: ByteStore,
    /// Reference count for the ARC model (`Retain`/`Release`/`IsUnique`).
    /// Every allocation carries the field and starts at 1, but only a
    /// reference-counted cell (`origin` `SwiftHeap` / `CleanHeap`) is ever
    /// counted: on any other allocation the three instructions are undefined
    /// behaviour before they read it (`arc_allocation_mut`, `is_unique`), so
    /// there the field is inert. `Retain` increments, `Release` decrements
    /// (freeing at 0); `IsUnique` is `ref_count == 1`. In this single-threaded
    /// reference interpreter the count is exact, not atomic.
    ref_count: u64,
    /// The `HeapAlloc` origin this cell was allocated with (WS2.13), or `None`
    /// for a stack slot, a scratch cell or a module global. A pinned RC
    /// runtime's host model (`HostCalls::rc_op`) counts only the cells of its
    /// own origin; the ARC instructions count only a `SwiftHeap` / `CleanHeap`
    /// cell; and `Dealloc` refuses a `SwiftHeap` / `CleanHeap` cell as
    /// undefined behaviour (it is released by `Release`, as in Lean).
    origin: Option<AllocOrigin>,
    /// The bytes the program REQUESTED: `size` without the heap slack tail.
    /// Only `borrow_count_mut` reads it: a borrow operand is counted only
    /// inside `[0, requested)`, where Lean's address lookup names this same
    /// allocation.
    requested: u64,
    /// `Borrow` / `BorrowMut` of this allocation not yet ended by an
    /// `EndBorrow` (SPEC "Freeing an allocation under a live borrow is
    /// undefined behaviour"): Lean's permission count, read ONLY by
    /// `Dealloc`, which refuses a nonzero count. Moved by
    /// `borrow_count_mut`; it saturates and never faults.
    live_borrows: u64,
}

enum Step {
    Continue,
    Jump {
        target: BlockId,
        args: Vec<InterpretValue>,
    },
    Return(Vec<InterpretValue>),
    /// Amendment D, Part 2 (§21 rule 4): an unwinding caught at this
    /// terminator transfers by U(exception, target) in this frame. Produced
    /// only under `PanicStrategy::Unwind`.
    Unwind {
        exception: u64,
        target: BlockId,
    },
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
        check_char_validity(&arg, block.id)?;
        state.values.insert(*value, arg);
    }
    Ok(())
}

/// The `Char` validity invariant (subset v4, WS2.17): a `Ty::Char` value must
/// be a **Unicode scalar value** — `0..=0x10FFFF` minus the surrogate block
/// `0xD800..=0xDFFF`. Mirrors the Lean `validChar` predicate
/// (`TrustIr/Basic.lean`).
///
/// `Ty::Char`'s 32-bit carrier admits surrogates and values past U+10FFFF,
/// and nothing in the arithmetic model rules them out, so the invariant is
/// checked HERE — at every site that binds a value to an SSA name — rather
/// than at each of the dozen instructions that can produce one. A violation
/// is UNDEFINED BEHAVIOUR, never a silently-carried integer: the format
/// promises `char`'s Rust/Lean meaning, and a consumer that indexes a
/// jump table or a UTF-8 encoder by it would be miscompiled by a surrogate.
///
/// The lowering-target subset's structural condition 6
/// ([`crate::bridge::ConformanceSubset::char_origin_excluded`]) is the
/// STATIC half of the same invariant: it keeps a conforming producer's
/// `Char` origins to a range-validated `Const` and `ZExt` of a `U8`, both of
/// which satisfy this check by construction. This check is the dynamic half,
/// and it runs on every module the interpreter executes, in subset or not.
fn check_char_validity(value: &InterpretValue, block: BlockId) -> InterpretResult<()> {
    if value.ty != Ty::Char {
        return Ok(());
    }
    let InterpretValueKind::Int(int) = &value.kind else {
        return Ok(());
    };
    if u32::try_from(int.raw).is_ok_and(|raw| char::from_u32(raw).is_some()) {
        return Ok(());
    }
    Err(err(
        InterpretErrorCode::UndefinedBehavior,
        block,
        format!(
            "`char` value {:#x} is not a Unicode scalar value (surrogate, or above U+10FFFF)",
            int.raw
        ),
    ))
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
        check_char_validity(&value, block)?;
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

/// Render a type list as `a, b, c` for a signature-mismatch diagnostic.
fn format_ty_list(tys: &[Ty]) -> String {
    tys.iter()
        .map(|t| format!("{t}"))
        .collect::<Vec<_>>()
        .join(", ")
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

/// Check the arguments of a call to a variadic DECLARATION (WS2.15): the
/// fixed prefix exactly as `check_signature_values` does, and the variadic
/// tail by what the format actually promises about it — nothing beyond each
/// value being a whole, non-poison value of its own type. A tail slot has no
/// declared type, so it cannot carry a runtime handle (the v43 rule is
/// exact-typed transport only; the validator refuses the same shape as
/// `InvalidHandleUse`).
fn check_vararg_declaration_args(
    block: BlockId,
    args: &[InterpretValue],
    fixed: &[Ty],
) -> InterpretResult<()> {
    if args.len() < fixed.len() {
        return Err(signature_mismatch(
            block,
            format!(
                "Call arguments arity mismatch: variadic callee expects at least {}, got {}",
                fixed.len(),
                args.len()
            ),
        ));
    }
    check_signature_values(block, "Call arguments", &args[..fixed.len()], fixed)?;
    for (offset, value) in args[fixed.len()..].iter().enumerate() {
        let index = fixed.len() + offset;
        reject_partial(value, block, "Call arguments")?;
        if first_handle(value).is_some() {
            return Err(type_error(
                block,
                format!(
                    "Call arguments: variadic argument {index} carries a runtime handle \
                     ({}), and a variadic slot has no exact type to transport one at",
                    value.ty
                ),
            ));
        }
    }
    Ok(())
}

/// Integer representation invariant, shared by host returns and external entry
/// values. Source-width pointer integers pass their actual source width here.
fn integer_carrier_matches(int: &InterpretInt, bits: u32, signed: bool) -> bool {
    int.bits == bits
        && int.signed == signed
        && int_mask(bits).is_some_and(|mask| int.raw & !mask == 0)
}

/// Host result admission additionally requires a Unicode scalar for Char.
/// At external entry, invalid Unicode retains the existing Char UB contract.
fn integer_payload_matches(ty: &Ty, int: &InterpretInt, bits: u32, signed: bool) -> bool {
    integer_carrier_matches(int, bits, signed)
        && (*ty != Ty::Char
            || u32::try_from(int.raw).is_ok_and(|raw| char::from_u32(raw).is_some()))
}

/// Check that `value`, the `index`th result a host model returned, is a
/// well-formed value of its declared type `declared` (WS2.12). The caller has
/// already checked `value.ty == declared`; this checks the value's KIND agrees
/// with its type, which `check_signature_values` does not look at.
fn check_host_result(
    value: &InterpretValue,
    declared: &Ty,
    host: &HostState,
    block: BlockId,
    index: usize,
) -> InterpretResult<()> {
    let malformed = || {
        type_error(
            block,
            format!(
                "host result {index} is not a well-formed {declared} value ({:?})",
                value.kind
            ),
        )
    };
    match (declared, &value.kind) {
        (ty, InterpretValueKind::Int(int)) if int_shape(ty).is_some() => {
            let (bits, signed) = int_shape(ty).expect("guarded by is_some");
            if integer_payload_matches(ty, int, bits, signed) {
                Ok(())
            } else {
                Err(malformed())
            }
        }
        (ty, _) if int_shape(ty).is_some() => Err(malformed()),
        (Ty::Bool, InterpretValueKind::Bool(_)) | (Ty::Unit, InterpretValueKind::Unit) => Ok(()),
        (Ty::F64, InterpretValueKind::FloatBits(_)) => Ok(()),
        (Ty::F32, InterpretValueKind::FloatBits(bits)) if *bits <= u64::from(u32::MAX) => Ok(()),
        // WS2.15: a binary16 result is its 16-bit pattern in the low bits.
        (Ty::F16, InterpretValueKind::FloatBits(bits)) if *bits <= u64::from(u16::MAX) => Ok(()),
        (Ty::Bool | Ty::Unit | Ty::F16 | Ty::F32 | Ty::F64, _) => Err(malformed()),
        (Ty::Handle(_), InterpretValueKind::Handle { id }) => {
            host.recorded(*id, &value.ty).map_err(|error| {
                err(
                    error.code,
                    block,
                    format!("host result {index}: {}", error.message),
                )
            })?;
            Ok(())
        }
        (Ty::Handle(_), _) => Err(malformed()),
        _ => Err(err(
            InterpretErrorCode::UnsupportedCall,
            block,
            format!(
                "host result {index} has type {declared}, which a host model may not return: \
                 a host has no access to interpreter memory or aggregates, so only integer, \
                 bool, f32/f64, unit and handle results are admitted"
            ),
        )),
    }
}

/// The first runtime handle inside `value` (WS2.12): a value whose payload is
/// a `Handle` OR whose type is `Ty::Handle`, searching every nested value.
fn first_handle(value: &InterpretValue) -> Option<&InterpretValue> {
    if matches!(value.ty, Ty::Handle(_)) {
        return Some(value);
    }
    match &value.kind {
        InterpretValueKind::Handle { .. } => Some(value),
        // Each distinct stored value once (O(nodes)), never each element.
        InterpretValueKind::Array(values)
        | InterpretValueKind::Vector(values)
        | InterpretValueKind::Sequence(values)
        | InterpretValueKind::Set(values)
        | InterpretValueKind::Tensor { elems: values, .. } => {
            match values.try_for_each_stored(|value| match first_handle(value) {
                Some(handle) => core::ops::ControlFlow::Break(handle),
                None => core::ops::ControlFlow::Continue(()),
            }) {
                core::ops::ControlFlow::Break(handle) => Some(handle),
                core::ops::ControlFlow::Continue(()) => None,
            }
        }
        InterpretValueKind::Aggregate(values)
        | InterpretValueKind::Closure {
            captures: values, ..
        } => values.iter().find_map(first_handle),
        InterpretValueKind::Record(fields) => {
            fields.iter().find_map(|(_, value)| first_handle(value))
        }
        InterpretValueKind::FatPtr { data, metadata } => {
            first_handle(data).or_else(|| first_handle(metadata))
        }
        InterpretValueKind::Frame { slots, .. } => slots.iter().flatten().find_map(first_handle),
        InterpretValueKind::Int(_)
        | InterpretValueKind::FloatBits(_)
        | InterpretValueKind::Bool(_)
        | InterpretValueKind::Ptr(_)
        | InterpretValueKind::FnDef(_)
        | InterpretValueKind::PhantomData
        | InterpretValueKind::NullPtr
        | InterpretValueKind::Unit
        | InterpretValueKind::PartialBytes(_)
        | InterpretValueKind::DanglingPtr(_)
        // Crystal lane (E3b): an unwritten lane holds no value, so no handle.
        | InterpretValueKind::Uninit => None,
    }
}

/// A runtime handle is transport-only (WS2.12): refuse it as the operand of
/// `op`, which would place it inside an aggregate or a binding frame, give it
/// a memory image, or reinterpret it by a cast.
fn reject_handle(value: &InterpretValue, block: BlockId, op: &str) -> InterpretResult<()> {
    if let InterpretValueKind::Handle { .. } = value.kind {
        Err(type_error(
            block,
            format!(
                "{op}: a runtime handle ({}) is transport-only (copy, select, branch, call, \
                 return): it cannot be placed in an aggregate or a binding frame, stored to \
                 memory, or cast",
                value.ty
            ),
        ))
    } else {
        Ok(())
    }
}

/// The undefined-behaviour message of a contraction whose paired axes have
/// different extents (PKG-U13a). NORMATIVE text: SemR spells it byte for byte,
/// and the differential compares UB verdicts by message.
const TENSOR_EXTENT_MISMATCH: &str = "tensor contraction: paired axes have different extents";

/// The undefined-behaviour message of a contraction whose result count is
/// `2^pointer_bits` or more (PKG-U13a). NORMATIVE text, as
/// [`TENSOR_EXTENT_MISMATCH`].
const TENSOR_RESULT_TOO_LARGE: &str =
    "tensor contraction: the result has more elements than usize holds";

/// The extents and elements of `value`, the `side` operand of the tensor
/// instruction `op` (its diagnostic name) whose static rules already hold, so its type is `Tensor(elem, rank)` with
/// `elem` an integer type (PKG-U13a runtime well-formedness): a tensor
/// payload, one extent per axis, each below `2^pointer_bits`, exactly
/// `∏ dims` elements (a zero extent makes that 0, the empty product is 1),
/// and every element an `Int` carrier of exactly `elem` at this run's pointer
/// width. Each STORED element is checked once, never each element, so a
/// uniform run of any count costs one check. Any failure is a `TypeError`:
/// the value is not a value of its type.
fn tensor_operand<'v>(
    value: &'v InterpretValue,
    op: &str,
    side: &str,
    elem: &Ty,
    rank: u32,
    pointer_bits: u32,
    block: BlockId,
) -> InterpretResult<(&'v [u64], &'v ArrayValue)> {
    let InterpretValueKind::Tensor { dims, elems } = &value.kind else {
        return Err(type_error(
            block,
            format!(
                "{op}: the {side} operand ({}) carries no tensor payload",
                value.ty
            ),
        ));
    };
    if dims.len() as u64 != u64::from(rank) {
        return Err(type_error(
            block,
            format!(
                "{op}: the {side} operand carries {} extents, but its type {} has \
                 rank {rank}",
                dims.len(),
                value.ty
            ),
        ));
    }
    let usize_limit = 1u128.checked_shl(pointer_bits).unwrap_or(u128::MAX);
    if let Some(dim) = dims.iter().find(|dim| u128::from(**dim) >= usize_limit) {
        return Err(type_error(
            block,
            format!(
                "{op}: the {side} operand's extent {dim} does not fit the \
                 target's {pointer_bits}-bit usize"
            ),
        ));
    }
    if exact_product_below(dims, 1u128 << 64) != Some(elems.len()) {
        return Err(type_error(
            block,
            format!(
                "{op}: the {side} operand's extents {dims:?} do not describe its {} \
                 elements",
                elems.len()
            ),
        ));
    }
    let (bits, signed) = int_shape_at(elem, pointer_bits).ok_or_else(|| {
        type_error(
            block,
            format!("{op}: element type {elem} has no integer shape"),
        )
    })?;
    let stray = elems.try_for_each_stored(|element| {
        let carried = element.ty == *elem
            && matches!(
                element.kind,
                InterpretValueKind::Int(int) if integer_carrier_matches(&int, bits, signed)
            );
        if carried {
            core::ops::ControlFlow::Continue(())
        } else {
            core::ops::ControlFlow::Break(element)
        }
    });
    if let core::ops::ControlFlow::Break(element) = stray {
        return Err(type_error(
            block,
            format!(
                "{op}: the {side} operand carries a {} element that is not a {elem} \
                 integer",
                element.ty
            ),
        ));
    }
    Ok((dims.as_slice(), elems))
}

/// The exact product of `dims` when it is below `limit`, else `None`. A zero
/// extent makes the product 0 whatever the others (decided first, so a large
/// prefix cannot overflow before the zero is reached), and the empty product
/// is 1 (a rank-0 tensor has one element). Exact, as SemR's `Nat` product is.
fn exact_product_below(dims: &[u64], limit: u128) -> Option<u64> {
    let product = if dims.contains(&0) {
        0
    } else {
        // Every factor is at least 1, so a partial product at or above
        // `limit` stays there: stop at the first.
        dims.iter().try_fold(1u128, |product, &dim| {
            product
                .checked_mul(u128::from(dim))
                .filter(|product| *product < limit)
        })?
    };
    if product < limit {
        u64::try_from(product).ok()
    } else {
        None
    }
}

/// The row-major stride of each axis of `dims` (`∏ dims[i+1..]`; the last
/// axis is fastest), or `None` if one does not fit a `u64`.
fn row_major_strides(dims: &[u64]) -> Option<Vec<u64>> {
    let mut strides = vec![0u64; dims.len()];
    let mut stride = 1u64;
    for (slot, &dim) in strides.iter_mut().zip(dims).rev() {
        *slot = stride;
        stride = stride.checked_mul(dim)?;
    }
    Some(strides)
}

/// Decode `flat`, a row-major position over the NONZERO extents `dims` (last
/// axis fastest), and return its offsets `(Σ index[i] · lhs[i], Σ index[i] ·
/// rhs[i])` under the two per-axis stride lists. The caller's indices name
/// real elements, so neither sum exceeds an operand's element count.
fn row_major_offsets(mut flat: u64, dims: &[u64], lhs: &[u64], rhs: &[u64]) -> (u64, u64) {
    let (mut lhs_offset, mut rhs_offset) = (0u64, 0u64);
    for ((&dim, &lhs_stride), &rhs_stride) in dims.iter().zip(lhs).zip(rhs).rev() {
        let index = flat % dim;
        flat /= dim;
        lhs_offset += index * lhs_stride;
        rhs_offset += index * rhs_stride;
    }
    (lhs_offset, rhs_offset)
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

/// The `OpenFrame` / `BindSlot` result handle: lineage `lineage`, holding
/// the slot snapshot `slots`.
///
/// Typed `Ty::Ptr`, the type every other party gives these results
/// (`bridge.rs` `InstrNode::result_tys`, the validator's `value_type`, the
/// `inst.rs` "frame-handle SSA value of type `Ptr`" discipline), so a handle
/// crosses a `Ptr` block parameter — the documented loop-carried quantifier
/// lowering — exactly as the validator admits. The handle was once typed
/// `Ty::Unit`, which made every such edge a `TypeError` here ("expected
/// value of type ptr, got ()") on a module that validated. The KIND stays
/// `Frame`: it is still not a pointer to any interpreter operation that
/// dereferences, compares or stores one (`expect_pointer`, `encode_image`).
fn frame_handle(lineage: u64, slots: Arc<[Option<InterpretValue>]>) -> InterpretValue {
    InterpretValue {
        ty: Ty::Ptr,
        kind: InterpretValueKind::Frame { lineage, slots },
    }
}

/// Extract the lineage and slot snapshot from an `OpenFrame` / `BindSlot`
/// handle value.
fn expect_frame(
    value: &InterpretValue,
    block: BlockId,
) -> InterpretResult<(u64, Arc<[Option<InterpretValue>]>)> {
    reject_partial(value, block, "frame handle use")?;
    match &value.kind {
        InterpretValueKind::Frame { lineage, slots } => Ok((*lineage, Arc::clone(slots))),
        _ => Err(type_error(
            block,
            format!("expected a binding-frame handle, got {}", value.ty),
        )),
    }
}

/// [`expect_frame`] on the value `frame`, additionally requiring that the
/// handle's lineage is still OPEN (a use after `CloseFrame` through ANY handle
/// of the lineage is UB).
fn expect_open_frame(
    state: &ExecState,
    block: BlockId,
    frame: ValueId,
    op: &str,
) -> InterpretResult<(u64, Arc<[Option<InterpretValue>]>)> {
    let (lineage, slots) = expect_frame(state.value(block, frame)?, block)?;
    if !state.frames.contains(&lineage) {
        return Err(ub(block, format!("{op}: frame is not open")));
    }
    Ok((lineage, slots))
}

fn expect_vector_lanes(
    value: &InterpretValue,
    lanes: u32,
    block: BlockId,
) -> InterpretResult<&ArrayValue> {
    reject_partial(value, block, "vector use")?;
    match &value.kind {
        InterpretValueKind::Vector(values) if values.len() == u64::from(lanes) => Ok(values),
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

/// A nominal or table-indexed type on the current layout path — the interpreter
/// twin of `shape`'s struct / enum / `TyId` visiting sets. See
/// `Interpreter::with_layout_visit` (roadmap WS2.4, F-045).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LayoutVisit {
    Struct(StructId),
    Enum(EnumId),
    Ty(TyId),
}

/// Computed C-style layout of a `Ty::Struct`: total size, alignment, and the
/// `(byte offset, field type)` of each field in declaration order.
struct StructLayout {
    size: u64,
    align: u64,
    field_offsets: Vec<(u64, Ty)>,
}

/// Logical enum information for register values, independent of whether any
/// variant has a byte layout. Physical encoding remains `EnumLayout`'s job.
struct EnumRegisterShape<'m> {
    module: &'m Module,
    definition: &'m crate::ty::EnumDef,
    tag_ty: Ty,
    discriminants: Vec<i128>,
}

impl EnumRegisterShape<'_> {
    fn variant_by_discriminant(&self, disc: i128) -> Option<usize> {
        self.discriminants.iter().position(|d| *d == disc)
    }

    fn refuse_uninhabited(
        &self,
        variant_idx: usize,
        ty: &Ty,
        op: &str,
        block: BlockId,
    ) -> InterpretResult<()> {
        if let Some(variant) = self.definition.variants.get(variant_idx) {
            let mut inhabit = crate::inhabit::InhabitMemo::default();
            if inhabit.variant_is_uninhabited(self.module, variant) {
                return Err(type_error(
                    block,
                    format!(
                        "{op}: enum {ty} variant {variant_idx} is uninhabited; no value of it exists"
                    ),
                ));
            }
        }
        Ok(())
    }
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
    /// WS3.14: per variant, whether it is uninhabited
    /// (`Module::variant_is_uninhabited`). No value of such a variant exists,
    /// so neither direction of the byte funnel may produce or accept one.
    uninhabited_variants: Vec<bool>,
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

    /// WS3.14: refuse `variant_idx` when it is uninhabited. An uninhabited
    /// variant has no value, so a Store of one or a Load of a byte image that
    /// names one (a direct tag equal to its discriminant, or a niche value in
    /// its slot of the interval) is an invalid value, never a variant to
    /// materialize.
    fn refuse_uninhabited(
        &self,
        variant_idx: usize,
        ty: &Ty,
        op: &str,
        block: BlockId,
    ) -> InterpretResult<()> {
        if self
            .uninhabited_variants
            .get(variant_idx)
            .copied()
            .unwrap_or(false)
        {
            return Err(type_error(
                block,
                format!(
                    "{op}: enum {ty} variant {variant_idx} is uninhabited; no value of it exists"
                ),
            ));
        }
        Ok(())
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

pub(crate) fn eval_int_binop(
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
        // WS3.20 rotates: TOTAL. The amount is reduced modulo the width (Rust
        // `rotate_left`, LLVM `fshl(x, x, n)`), so unlike the shifts there is
        // no out-of-range poison. `rotate_at_width` masks to `bits` itself.
        // MUST agree with `semIntBinOp .RotL/.RotR` (Arith.lean).
        BinOp::RotL => rotate_at_width(lhs.raw, lhs.bits, rhs.raw, true),
        BinOp::RotR => rotate_at_width(lhs.raw, lhs.bits, rhs.raw, false),
        BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax
        | BinOp::FCopySign => {
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
        BinOp::And => Ok(scalar_bool::conjunction(lhs, rhs)),
        BinOp::Or => Ok(lhs | rhs),
        BinOp::Xor => Ok(lhs ^ rhs),
        // The dedicated boolean connectives. WITHOUT these arms the catch-all
        // below would reject them on precisely the type they exist for: the
        // validator requires `BAnd`/`BOr`/`BXor` to be Bool-typed, so every
        // well-typed use would land in the error branch.
        BinOp::BAnd => Ok(scalar_bool::conjunction(lhs, rhs)),
        BinOp::BOr => Ok(lhs | rhs),
        BinOp::BXor => Ok(lhs ^ rhs),
        _ => Err(type_error(
            block,
            format!("{op} is not a boolean binary operation"),
        )),
    }
}

pub(crate) fn eval_int_unop(
    op: UnOp,
    value: InterpretInt,
    block: BlockId,
) -> InterpretResult<InterpretInt> {
    let mask = int_mask(value.bits).expect("validated integer width");
    let raw = match op {
        UnOp::Neg => 0u128.wrapping_sub(value.raw),
        UnOp::Not => !value.raw,
        UnOp::CtPop => u128::from(value.raw.count_ones()),
        // WS3.20 bit intrinsics (F-057). All TOTAL at the operand width, and
        // each MUST agree with its `semIntUnOp` arm in Arith.lean:
        //   ctlz 0 = cttz 0 = width (the one spelling: no poison operand);
        //   bswap reverses the width/8 bytes (identity at 8 bits);
        //   bitreverse reverses all `width` bits.
        // `value.raw` is already masked to `bits`, so the high `128 - bits`
        // bits are zero and the leading-zero count is shifted by them.
        UnOp::CtLz => u128::from(value.raw.leading_zeros() - (128 - value.bits)),
        UnOp::CtTz => u128::from(value.raw.trailing_zeros().min(value.bits)),
        UnOp::BSwap => value.raw.swap_bytes() >> (128 - value.bits),
        UnOp::BitReverse => value.raw.reverse_bits() >> (128 - value.bits),
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

pub(crate) fn eval_int_overflow(
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

pub(crate) fn eval_int_icmp(op: ICmpOp, lhs: InterpretInt, rhs: InterpretInt) -> bool {
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
                // WS3.20: IEEE copySign — exact, quiet, sign bit of `rhs`
                // (a NaN keeps its payload). Same execution status as `FNeg`.
                BinOp::FCopySign => lhs.copysign(rhs),
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
                BinOp::FCopySign => lhs.copysign(rhs),
                _ => {
                    return Err(type_error(
                        block,
                        format!("integer binop {op} on float operands"),
                    ));
                }
            };
            Ok(value.to_bits())
        }
        // WS2.15: binary16 arithmetic, computed in binary32 and rounded ONCE
        // to binary16. This is the exact IEEE binary16 result, not an
        // approximation: binary32 carries 24 significand bits and 24 >= 2*11
        // + 2, so for `+ - * /` the binary32 rounding of the exact result
        // never lands on a binary16 rounding boundary it was not already on
        // (Figueroa's innocuous double rounding, the same argument
        // `docs/ub-numerics-policy.md` §2 makes for the f32-in-f64 case in
        // reverse). `FRem` is exact in the operands' format, so the binary32
        // remainder of two binary16 values is already a binary16 value, and
        // `FMin`/`FMax` return an operand. The final rounding is therefore
        // the ONLY rounding, and `f16_cross_engine_table` (conformance
        // `interpret_f16`) pins it at the overflow tie, the subnormal floor
        // and the signed zeros. `FCopySign` (WS3.20) is a sign-bit
        // operation on the binary16 pattern itself, exactly like `FNeg` /
        // `FAbs` in `eval_float_unop`: no rounding, NaN payload kept.
        Ty::F16 => {
            if op == BinOp::FCopySign {
                let magnitude = (lhs_bits as u16) & 0x7FFF;
                let sign = (rhs_bits as u16) & 0x8000;
                return Ok(u64::from(magnitude | sign));
            }
            let lhs = f16_bits_to_f32(lhs_bits);
            let rhs = f16_bits_to_f32(rhs_bits);
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
            Ok(u64::from(f64_to_f16_bits(f64::from(value))))
        }
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

/// Widen a binary16 bit pattern (the low 16 bits of an `F16` value's
/// `FloatBits`) to binary32, exactly.
fn f16_bits_to_f32(bits: u64) -> f32 {
    // Exact: every binary16 value (NaN payloads included, see
    // `f16_bits_to_f64`) is a binary32 value.
    f16_bits_to_f64(bits as u16) as f32
}

/// Decode an IEEE 754 binary16 bit pattern to the binary64 value it denotes
/// (WS2.15). Exact for every pattern: binary16's 11-bit significand and
/// exponent range `2^-24 ..= 65504` sit inside binary64's. A NaN keeps its
/// sign, quiet bit and payload, left-aligned into the binary64 fraction (the
/// compiler-rt `__extendhfsf2` shape), so `f64_to_f16_bits` recovers the
/// same pattern.
pub fn f16_bits_to_f64(bits: u16) -> f64 {
    let negative = bits & 0x8000 != 0;
    let exponent = (bits >> 10) & 0x1F;
    let fraction = bits & 0x3FF;
    let magnitude = match exponent {
        // Subnormal (or zero): `fraction * 2^-24`, exact in binary64.
        0 => f64::from(fraction) * 2f64.powi(-24),
        0x1F if fraction == 0 => f64::INFINITY,
        0x1F => {
            let payload = u64::from(fraction) << (52 - 10);
            return f64::from_bits((u64::from(negative) << 63) | (0x7FFu64 << 52) | payload);
        }
        // Normal: `(1 + fraction/2^10) * 2^(exponent - 15)`.
        exponent => (1.0 + f64::from(fraction) / 1024.0) * 2f64.powi(i32::from(exponent) - 15),
    };
    if negative { -magnitude } else { magnitude }
}

/// Round a binary64 value to the nearest IEEE 754 binary16 bit pattern, ties
/// to even, with gradual underflow and overflow to `±inf` (WS2.15). This is
/// the ONE rounding every `F16` result takes; the arithmetic that feeds it
/// (`eval_float_binop` / `eval_float_unop`) is exact or innocuously
/// double-rounded, so the result is the correctly rounded binary16 value.
///
/// Integer arithmetic throughout (no host `f16` type is used): the binary64
/// significand is shifted right to 11 bits with a round bit and a sticky bit,
/// which is what makes the overflow tie observable — `65520` (the exact sum
/// `65504 + 16`) lies halfway between `65504` (odd significand `0x7FF`) and
/// `65536` (the first value past the format), so ties-to-even rounds it UP
/// and the result is `+inf`, while `65512 = 65504 + 8` is below the halfway
/// point and rounds DOWN to `65504`. A NaN keeps its sign, is quieted, and
/// keeps the top ten payload bits (compiler-rt `__truncdfhf2`'s shape).
pub fn f64_to_f16_bits(value: f64) -> u16 {
    const F16_INFINITY: u16 = 0x7C00;
    const F16_QUIET: u16 = 0x0200;
    let bits = value.to_bits();
    let sign = ((bits >> 63) as u16) << 15;
    let exponent = ((bits >> 52) & 0x7FF) as i32;
    let fraction = bits & ((1u64 << 52) - 1);
    if exponent == 0x7FF {
        if fraction == 0 {
            return sign | F16_INFINITY;
        }
        let payload = (fraction >> (52 - 10)) as u16 & 0x3FF;
        return sign | F16_INFINITY | F16_QUIET | payload;
    }
    if exponent == 0 {
        // ±0, or a binary64 subnormal (below 2^-1022, so far below half the
        // smallest binary16 subnormal 2^-25): rounds to the signed zero.
        return sign;
    }
    // `value = significand * 2^(unbiased - 52)` with the implicit leading 1.
    let significand = fraction | (1u64 << 52);
    let unbiased = exponent - 1023;
    if unbiased > 15 {
        // `>= 2^16`, past the largest finite binary16 and past the overflow
        // threshold 65520 by any margin.
        return sign | F16_INFINITY;
    }
    if unbiased >= -14 {
        // Normal range: keep 11 significand bits (drop 42), then renormalize
        // a carry out of the top bit (`0x7FF` + 1 rounds to the next binade,
        // and out of the format when that binade is `2^16`).
        let (mut mantissa, mut binade) = (round_shift_rne(significand, 42), unbiased);
        if mantissa == 1 << 11 {
            mantissa >>= 1;
            binade += 1;
        }
        if binade > 15 {
            return sign | F16_INFINITY;
        }
        return sign | (((binade + 15) as u16) << 10) | (mantissa as u16 & 0x3FF);
    }
    // Subnormal range: the result is a whole number of 2^-24 units, so shift
    // to that scale and round once. A shift past the 53-bit significand
    // (`unbiased <= -26`, `value < 2^-25`) leaves nothing but the sticky bit,
    // which rounds to zero; the `>= 64` guard only keeps the shift defined.
    let shift = 28 - unbiased;
    if shift >= 64 {
        return sign;
    }
    // A carry into bit 10 is exactly the smallest normal (`0x0400`), which is
    // the correct pattern for a subnormal that rounded up to `2^-14`.
    sign | (round_shift_rne(significand, shift) as u16)
}

/// `significand >> shift`, rounded to nearest with ties to even, for
/// `1 <= shift <= 63`.
fn round_shift_rne(significand: u64, shift: i32) -> u64 {
    debug_assert!((1..=63).contains(&shift));
    let truncated = significand >> shift;
    let remainder = significand & ((1u64 << shift) - 1);
    let half = 1u64 << (shift - 1);
    if remainder > half || (remainder == half && truncated & 1 == 1) {
        truncated + 1
    } else {
        truncated
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
        // WS2.15: `FNeg`/`FAbs` are sign-bit operations on the binary16
        // pattern itself (IEEE 754 §5.5.1 — bit-exact, NaN payload kept).
        // `FSqrt` is computed in binary32 and rounded once (24 >= 2*11 + 2,
        // the same innocuous-double-rounding argument as `eval_float_binop`);
        // `FFloor`/`FCeil`/`FTrunc` of a binary16 value are integers no larger
        // than the operand's binade, so they are binary16 values already and
        // the final rounding is the identity.
        Ty::F16 => {
            let bits = operand_bits as u16;
            let value = match op {
                UnOp::FNeg => return Ok(u64::from(bits ^ 0x8000)),
                UnOp::FAbs => return Ok(u64::from(bits & 0x7FFF)),
                UnOp::FSqrt => f16_bits_to_f32(operand_bits).sqrt(),
                UnOp::FFloor => f16_bits_to_f32(operand_bits).floor(),
                UnOp::FCeil => f16_bits_to_f32(operand_bits).ceil(),
                UnOp::FTrunc => f16_bits_to_f32(operand_bits).trunc(),
                _ => {
                    return Err(type_error(
                        block,
                        format!("integer unary op {op} on float operand"),
                    ));
                }
            };
            Ok(u64::from(f64_to_f16_bits(f64::from(value))))
        }
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
        // WS2.15: the ordered/unordered predicates compare VALUES, and the
        // binary32 widening is exact, so the binary32 comparison is the
        // binary16 one (NaN-ness included).
        Ty::F16 => Ok(eval_fcmp_f32(
            op,
            f16_bits_to_f32(lhs_bits),
            f16_bits_to_f32(rhs_bits),
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
        // WS2.15: a `Constant::Float(f64)` at `F16` (the codec's carrier for
        // every float width) and an `FPTrunc` into `F16` both narrow the
        // binary64 value with one RNE rounding. `FPTrunc` from `F32` widens
        // exactly first, so it is a single rounding too.
        Ty::F16 => Ok(u64::from(f64_to_f16_bits(value))),
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

fn float_bits_from_raw(ty: &Ty, raw: u128, block: BlockId) -> InterpretResult<u64> {
    match ty {
        Ty::F32 => Ok((raw as u32) as u64),
        Ty::F64 => Ok(raw as u64),
        // WS2.15: a `Bitcast` into `F16` reinterprets the low 16 bits as the
        // binary16 pattern, exactly as the `F32` arm takes the low 32.
        Ty::F16 => Ok(u64::from(raw as u16)),
        _ => Err(type_error(block, format!("expected float type, got {ty}"))),
    }
}

fn float_as_f64(ty: &Ty, bits: u64, block: BlockId) -> InterpretResult<f64> {
    match ty {
        Ty::F32 => Ok(f32::from_bits(bits as u32) as f64),
        Ty::F64 => Ok(f64::from_bits(bits)),
        // WS2.15: exact (every binary16 value is a binary64 value), so an
        // `FPExt` out of `F16` and a float->int cast from `F16` see the value
        // itself.
        Ty::F16 => Ok(f16_bits_to_f64(bits as u16)),
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

/// Rotate the low `bits` bits of `value` by `amount % bits` positions
/// (left when `left`, else right). Total: the amount is reduced modulo the
/// width, and the result is masked to `bits`. The bit-level definition is the
/// one `semIntBinOp .RotL/.RotR` (Arith.lean) states:
/// `rotl(x, n) = (x << n | x >> (w - n)) mod 2^w` with `n = amount mod w`.
fn rotate_at_width(value: u128, bits: u32, amount: u128, left: bool) -> u128 {
    let mask = int_mask(bits).expect("validated integer width");
    let value = value & mask;
    let n = (amount % u128::from(bits)) as u32;
    if n == 0 {
        return value;
    }
    let (hi_shift, lo_shift) = if left { (n, bits - n) } else { (bits - n, n) };
    ((value << hi_shift) | (value >> lo_shift)) & mask
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

thread_local! {
    /// The pointer width of the execution running on this thread (WS2.16).
    /// `int_shape` is a free function reached from value constructors that
    /// carry no interpreter handle (`InterpretValue::int`, host-result
    /// checks, enum tag synthesis), so the width of `Isize`/`Usize` is read
    /// from here. Outside any execution it is the 64-bit reference width, so
    /// every pre-WS2.16 path (and every 64-bit run) is byte-identical.
    static EXEC_POINTER_BITS: core::cell::Cell<u32> =
        const { core::cell::Cell::new(crate::shape::DEFAULT_POINTER_BITS) };
}

/// Sets [`EXEC_POINTER_BITS`] for the lifetime of one execution and restores
/// the enclosing value on drop, so a host model that re-enters another
/// interpreter (on another module, at another width) cannot leak its width
/// into the caller's run.
struct PointerWidthScope {
    previous: u32,
}

impl PointerWidthScope {
    fn enter(pointer_bits: u32) -> Self {
        Self {
            previous: EXEC_POINTER_BITS.with(|bits| bits.replace(pointer_bits)),
        }
    }
}

impl Drop for PointerWidthScope {
    fn drop(&mut self) {
        EXEC_POINTER_BITS.with(|bits| bits.set(self.previous));
    }
}

/// The highest address a `pointer_bits`-wide pointer can name.
fn max_address_for(pointer_bits: u32) -> u64 {
    if pointer_bits >= 64 {
        u64::MAX
    } else {
        (1u64 << pointer_bits) - 1
    }
}

/// Validate stored integer carriers and re-express pointer-width integers at
/// `pointer_bits`, or explain why they do not fit. This is the existing sparse
/// entry-argument walk, not a new per-instruction/deep-value validation pass.
fn narrow_pointer_width_ints(
    value: &mut InterpretValue,
    pointer_bits: u32,
    block: BlockId,
    char_allowed: bool,
) -> InterpretResult<()> {
    let malformed = |message: String| type_error(block, format!("entry argument: {message}"));
    if let Some((bits, signed)) = int_shape_at(&value.ty, pointer_bits) {
        // Leave poison and unminted handles to the existing ownership/use
        // guards, which retain their UndefinedBehavior precedence. A stored
        // integer is checked before ANY signed decode, shift or mask.
        if matches!(
            value.kind,
            InterpretValueKind::PartialBytes(_)
                | InterpretValueKind::Uninit
                | InterpretValueKind::Handle { .. }
        ) {
            return Ok(());
        }
        let InterpretValueKind::Int(int) = &value.kind else {
            return Err(malformed(format!(
                "{} value has no integer payload",
                value.ty
            )));
        };
        let pointer_sized = matches!(value.ty, Ty::Isize | Ty::Usize);
        // Pointer-width entry integers are self-described at their source
        // width; fixed-width integers must already match their nominal type.
        let stored_bits = if pointer_sized { int.bits } else { bits };
        if !integer_carrier_matches(int, stored_bits, signed) {
            return Err(malformed(format!(
                "malformed {} integer payload: {} bits, signed={}, raw={}",
                value.ty, int.bits, int.signed, int.raw
            )));
        }
        if value.ty == Ty::Char && !char_allowed {
            return Err(malformed(
                "Char payload is not declared by this entry parameter".into(),
            ));
        }
        check_char_validity(value, block)?;
        if pointer_sized && int.bits != pointer_bits {
            let fits = if signed {
                let (lo, hi) = signed_bounds(pointer_bits);
                (lo..=hi).contains(&int.as_signed())
            } else {
                int_mask(pointer_bits).is_some_and(|mask| int.raw <= mask)
            };
            // An unsigned source's top bit is NOT a sign bit. In particular
            // u32::MAX must widen to 4294967295, never u64::MAX.
            let resized = if signed {
                InterpretInt::from_i128(pointer_bits, true, int.as_signed())
            } else {
                InterpretInt::from_raw(pointer_bits, false, int.raw)
            };
            let narrowed = resized.filter(|_| fits).ok_or_else(|| {
                malformed(format!(
                    "{} value {} does not fit the target's {pointer_bits}-bit pointer width",
                    value.ty,
                    if signed {
                        int.as_signed().to_string()
                    } else {
                        int.raw.to_string()
                    }
                ))
            })?;
            value.kind = InterpretValueKind::Int(narrowed);
        }
        return Ok(());
    }
    match &mut value.kind {
        // Each stored node once: O(nodes), never O(len).
        InterpretValueKind::Array(items)
        | InterpretValueKind::Vector(items)
        | InterpretValueKind::Sequence(items)
        | InterpretValueKind::Set(items) => {
            *items = items.try_map(|item| {
                let mut item = item.clone();
                narrow_pointer_width_ints(&mut item, pointer_bits, block, char_allowed)
                    .map(|()| item)
            })?;
            Ok(())
        }
        InterpretValueKind::Aggregate(items)
        | InterpretValueKind::Closure {
            captures: items, ..
        } => items.iter_mut().try_for_each(|item| {
            narrow_pointer_width_ints(item, pointer_bits, block, char_allowed)
        }),
        InterpretValueKind::Record(fields) => fields.iter_mut().try_for_each(|(_, item)| {
            narrow_pointer_width_ints(item, pointer_bits, block, char_allowed)
        }),
        InterpretValueKind::FatPtr { data, metadata } => {
            narrow_pointer_width_ints(data, pointer_bits, block, char_allowed)?;
            narrow_pointer_width_ints(metadata, pointer_bits, block, char_allowed)
        }
        // A tensor's extents are `usize` values it carries (PKG-U13a): one
        // the target's pointer width cannot hold is refused here, and its
        // elements are re-expressed like an array's (each stored node once).
        // The rest of its well-formedness (one extent per axis, `∏ dims`
        // elements of exactly its element type) is checked where it is
        // consumed (`tensor_operand`), as for a tensor an instruction built.
        InterpretValueKind::Tensor { dims, elems } => {
            let usize_limit = 1u128.checked_shl(pointer_bits).unwrap_or(u128::MAX);
            if let Some(dim) = dims.iter().find(|dim| u128::from(**dim) >= usize_limit) {
                return Err(malformed(format!(
                    "{} extent {dim} does not fit the target's {pointer_bits}-bit usize",
                    value.ty
                )));
            }
            *elems = elems.try_map(|item| {
                let mut item = item.clone();
                narrow_pointer_width_ints(&mut item, pointer_bits, block, char_allowed)
                    .map(|()| item)
            })?;
            Ok(())
        }
        _ => Ok(()),
    }
}

fn int_shape(ty: &Ty) -> Option<(u32, bool)> {
    int_shape_at(ty, EXEC_POINTER_BITS.with(core::cell::Cell::get))
}

/// [`int_shape`] at an explicit pointer width.
fn int_shape_at(ty: &Ty, pointer_bits: u32) -> Option<(u32, bool)> {
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
        // v25 B1 scalars: pointer-width integers execute at the running
        // target's pointer width (WS2.16: 64 on the reference target and
        // every 64-bit canonical target, 32 on wasm32). Char is a 32-bit
        // unsigned carrier; its 0..=0x10FFFF valid range is the VALIDATOR's
        // claim to check, not an arithmetic property.
        Ty::Isize => Some((pointer_bits, true)),
        Ty::Usize => Some((pointer_bits, false)),
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
/// Internal decoding requires a validated width: constructors check this,
/// host returns use `integer_payload_matches`, and external entry carriers
/// pass `integer_carrier_matches` before any decode, then the Char UB guard.
/// Pointer source widths remain self-described in 1..=128; fixed-width carriers must match their nominal Ty.
/// Public InterpretInt fields by themselves do not establish this invariant.
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

fn invalid_function_pointer(block: BlockId, message: impl Into<String>) -> InterpretError {
    err(InterpretErrorCode::InvalidFunctionPointer, block, message)
}

fn signature_mismatch(block: BlockId, message: impl Into<String>) -> InterpretError {
    err(InterpretErrorCode::SignatureMismatch, block, message)
}

fn ub(block: BlockId, message: impl Into<String>) -> InterpretError {
    err(InterpretErrorCode::UndefinedBehavior, block, message)
}

/// `(p1, p2) -> (r1)` rendering of a signature for diagnostics.
fn format_sig(sig: &FuncTy) -> String {
    let list = |tys: &[Ty]| {
        tys.iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "({}{}) -> ({})",
        list(&sig.params),
        if sig.is_vararg { ", ..." } else { "" },
        list(&sig.returns)
    )
}

/// The set of load result types that participate in copy-propagates-poison: a
/// non-strict load of one of these whose byte range has an uninitialized byte
/// yields a `PartialBytes` transport value instead of faulting. These are the
/// SCALAR types `decode_leaf` turns into a single runtime value (integers,
/// floats, bool, and thin pointers). Aggregates and fat pointers are excluded —
/// their loads require every COVERED byte (WS2.14, `first_uninit_covered`): a
/// decode only touches live field bytes, padding is don't-care, and an
/// uninitialized field byte stays undefined behaviour.
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

/// The undefined-behaviour error raised when a poison value (a partially-
/// initialized load, `Undef`, or an unbound `LoadSlot`) is INSPECTED rather
/// than merely transported. `op` names the true use site (the
/// arithmetic/comparison/cast/branch/call that consumed it).
fn reject_partial_error(block: BlockId, op: &str) -> InterpretError {
    ub(
        block,
        format!(
            "{op}: use of an uninitialized value — poison (uninitialized bytes, \
             `undef`, or an unbound slot) may only be copied or stored, never inspected"
        ),
    )
}

/// Fault if `value` is a `PartialBytes` poison value; otherwise a no-op. Every
/// content-inspecting operation gates on this so the undefined behaviour is
/// reported at the true use site, not silently miscomputed.
fn reject_partial(value: &InterpretValue, block: BlockId, op: &str) -> InterpretResult<()> {
    match value.kind {
        InterpretValueKind::PartialBytes(_) => Err(reject_partial_error(block, op)),
        // Crystal lane (E3b): an unwritten lane is never a value of its own. No instruction can bind
        // one (`ExtractField` of it is UB), so this arm is a defence in depth, not a path.
        InterpretValueKind::Uninit => Err(ub(
            block,
            format!("{op}: use of an unwritten aggregate lane (uninit) as a value"),
        )),
        _ => Ok(()),
    }
}

/// Crystal lane (E3b): `Constant::Uninit` may stand ONLY as a direct lane of a `Ty::Struct` /
/// `Ty::Tuple` aggregate constant of an `Inst::Const` -- trust-ir-build's placement rule,
/// mirrored fail-closed so an unvalidated module cannot reach the lane conversion with one
/// anywhere else (as the whole constant, one aggregate deeper, or under any other type).
fn check_uninit_lane_placement(ty: &Ty, value: &Constant, block: BlockId) -> InterpretResult<()> {
    let direct_lanes: &[Constant] = match (ty, value) {
        (Ty::Struct(_) | Ty::Tuple(_), Constant::Aggregate(lanes)) => lanes,
        _ => &[],
    };
    let misplaced = if direct_lanes.is_empty() {
        constant_mentions_uninit(value)
    } else {
        direct_lanes
            .iter()
            .any(|lane| !matches!(lane, Constant::Uninit) && constant_mentions_uninit(lane))
    };
    if misplaced {
        Err(type_error(
            block,
            format!(
                "Const: `uninit` may stand only as a direct lane of a struct/tuple aggregate \
                 constant; {ty} constant {value:?} carries one elsewhere"
            ),
        ))
    } else {
        Ok(())
    }
}

/// True iff `constant` or any descendant is `Constant::Uninit`.
fn constant_mentions_uninit(constant: &Constant) -> bool {
    constant
        .try_visit_constants(|c| {
            if matches!(c, Constant::Uninit) {
                core::ops::ControlFlow::Break(())
            } else {
                core::ops::ControlFlow::Continue(())
            }
        })
        .is_break()
}

/// True iff `value` is an aggregate that carries an unwritten lane at any depth.
fn value_carries_uninit_lane(value: &InterpretValue) -> bool {
    match &value.kind {
        InterpretValueKind::Uninit => true,
        InterpretValueKind::Aggregate(lanes) => lanes.iter().any(value_carries_uninit_lane),
        _ => false,
    }
}

fn err(code: InterpretErrorCode, block: BlockId, message: impl Into<String>) -> InterpretError {
    InterpretError::new(code, message).with_block(block)
}

/// The glue a drop at `ty` runs (amendment D, §20 rule 2): the one drop-glue
/// row whose key equals `ty`. With no module there is no table
/// (`UnsupportedInstruction`, deliberately not `module_context`'s
/// `MissingFunction`, so it matches the Lean model's bare-step
/// `unsupported.destructor`); with no row the drop is UNRESOLVED
/// (`UnsupportedInstruction`, never a no-op); two rows can only occur in an
/// unvalidated module (`MalformedInstruction`).
fn resolve_drop_glue(
    state: &ExecState,
    block: BlockId,
    op: &str,
    ty: &Ty,
) -> InterpretResult<FuncId> {
    let Some(index) = state.drop_glue.as_ref() else {
        return Err(err(
            InterpretErrorCode::UnsupportedInstruction,
            block,
            format!("{op}: no module, so no drop-glue table"),
        ));
    };
    match index.resolve(ty) {
        crate::DropResolution::Resolved(glue) => Ok(glue),
        crate::DropResolution::Unresolved => Err(err(
            InterpretErrorCode::UnsupportedInstruction,
            block,
            format!(
                "{op}: {ty} has no drop_glue row (an unresolved drop states no destructor and is \
                 never run as a no-op)"
            ),
        )),
        crate::DropResolution::Ambiguous => Err(err(
            InterpretErrorCode::MalformedInstruction,
            block,
            format!("{op}: {ty} has more than one drop_glue row"),
        )),
    }
}

/// The panic a FAILED assert of `kind` raises (plan item P). The kind's
/// operands are read only now, on failure, exactly as the Lean model reads
/// them: each must be a non-poison integer (a validated module types them
/// `usize`), and its unsigned value is what the message prints.
/// §21 rule 3: allocate the exception object of a failed check's `error` (a
/// fresh one-byte allocation, dead from birth, so every memory operation
/// through it is UB by the existing rules), record it with the error, and
/// return its address. Running out of address space here is a non-raise
/// (`OutOfMemory`), never an unwinding.
fn raise_exception(
    state: &mut ExecState,
    block: BlockId,
    error: &InterpretError,
) -> InterpretResult<u64> {
    let pointer = state.memory.alloc(1, 1, block)?;
    if let Some(allocation) = state.memory.allocations.get_mut(&pointer.allocation) {
        allocation.alive = false;
    }
    let address = state.memory.address(pointer, block, "raise")?;
    state
        .unwind
        .exceptions
        .insert(address, (pointer, error.clone()));
    Ok(address)
}

fn assert_panic(
    state: &ExecState,
    block: BlockId,
    kind: &AssertKind,
    site: Option<&PanicSite>,
) -> InterpretResult<InterpretError> {
    let operands = match (kind.operands(), kind.operand_roles()) {
        (Some(ids), Some(roles)) => {
            let mut values = [0u128; 2];
            for ((slot, id), role) in values.iter_mut().zip(ids).zip(roles) {
                let value = state.value(block, id)?;
                reject_partial(value, block, "assert")?;
                *slot = value
                    .as_int()
                    .map(InterpretInt::as_unsigned)
                    .ok_or_else(|| {
                        type_error(
                            block,
                            format!(
                                "assert {} `{role}` requires an integer, got {}",
                                kind.keyword(),
                                value.ty
                            ),
                        )
                    })?;
            }
            Some(values)
        }
        _ => None,
    };
    // Amendment P: the location is resolved AFTER the operands, so a bad
    // operand is the reported fault even when the location is bad too.
    let site = match site {
        None => None,
        Some(site) => Some(InterpretPanicSite {
            entry: site.entry,
            location: resolve_panic_location(state, block, &site.location)?,
        }),
    };
    let panic = InterpretPanic {
        kind: *kind,
        operands,
        site,
    };
    let mut error = err(InterpretErrorCode::Panic, block, panic.message());
    error.panic = Some(Box::new(panic));
    Ok(error)
}

/// Resolve a FAILED sited check's location (amendment P, wire v54;
/// `docs/SPEC_RATIFICATIONS.md` §19.1 rule 4). The Lean twin is
/// `resolvePanicLocation` (`Semantics/Step.lean`).
///
/// * `Global(g)` is `Global { global: g, offset: 0 }`: the global is NOT
///   materialized — no allocation, no initializer read, no state change.
/// * `Value(v)`: poison is UB; a non-pointer is a `TypeError`; null, a
///   pointer with no provenance, one into an unknown or freed allocation, or
///   one outside the bytes its allocation requested is UB ("null or
///   dangling"). A live pointer into a materialized global's allocation is
///   that global at its byte offset; any other live pointer is `Other`.
fn resolve_panic_location(
    state: &ExecState,
    block: BlockId,
    location: &PanicLocation,
) -> InterpretResult<PanicLocationValue> {
    let value = match location {
        PanicLocation::Global(global) => {
            return Ok(PanicLocationValue::Global {
                global: *global,
                offset: 0,
            });
        }
        PanicLocation::Value(value) => state.value(block, *value)?,
    };
    reject_partial(value, block, "assert")?;
    let dangling = || ub(block, "assert: panic location is null or dangling");
    let pointer = match &value.kind {
        InterpretValueKind::Ptr(pointer) => *pointer,
        InterpretValueKind::NullPtr | InterpretValueKind::DanglingPtr(_) => {
            return Err(dangling());
        }
        _ => {
            return Err(type_error(
                block,
                format!("assert panic location requires a pointer, got {}", value.ty),
            ));
        }
    };
    let live = state
        .memory
        .allocations
        .get(&pointer.allocation)
        .is_some_and(|allocation| allocation.alive && pointer.offset < allocation.requested);
    if !live {
        return Err(dangling());
    }
    Ok(state
        .globals
        .iter()
        .find(|(_, base)| base.allocation == pointer.allocation)
        .map_or(PanicLocationValue::Other, |(global, base)| {
            PanicLocationValue::Global {
                global: *global,
                offset: pointer.offset.saturating_sub(base.offset),
            }
        }))
}

#[cfg(test)]
mod pointer_comparison_tests {
    use super::*;

    const OPS: [ICmpOp; 10] = [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ];

    fn state(pointer_bits: u32) -> ExecState {
        ExecState {
            values: BTreeMap::new(),
            memory: MemoryState {
                max_address: max_address_for(pointer_bits),
                ..MemoryState::default()
            },
            globals: BTreeMap::new(),
            frames: BTreeSet::new(),
            next_frame_id: 0,
            steps: 0,
            remaining_fuel: u64::MAX,
            host: HostState::new(),
            host_calls: 0,
            drop_glue: None,
            unwind: UnwindState::default(),
        }
    }

    fn pointer(kind: InterpretValueKind) -> InterpretValue {
        InterpretValue { ty: Ty::Ptr, kind }
    }

    fn module(pointer_bits: u32) -> Module {
        let mut module = Module::new("pointer-icmp-width");
        module.target_info = Some(crate::TargetInfo {
            triple: if pointer_bits == 32 {
                "wasm32-unknown-unknown"
            } else {
                "x86_64-unknown-linux-gnu"
            }
            .into(),
            pointer_size: pointer_bits / 8,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        module
    }

    #[test]
    fn pointer_icmp_compares_addresses_for_null_live_and_aliases() {
        let interpreter = Interpreter::new();
        let mut state = state(64);
        let block = BlockId(0);
        let first = state.memory.alloc(8, 1, block).unwrap();
        let second = state.memory.alloc(8, 1, block).unwrap();
        let first_address = state.memory.address(first, block, "test").unwrap();
        let null = pointer(InterpretValueKind::NullPtr);
        let first_value = pointer(InterpretValueKind::Ptr(first));
        let alias = first_value.clone();
        let second_value = pointer(InterpretValueKind::Ptr(second));
        let one_past = pointer(InterpretValueKind::Ptr(InterpretPointer {
            offset: 8,
            ..first
        }));
        let raw_alias = pointer(InterpretValueKind::DanglingPtr(first_address));
        let equal = [
            true, false, false, true, false, true, false, true, false, true,
        ];
        let less = [
            false, true, true, true, false, false, true, true, false, false,
        ];
        let greater = [
            false, true, false, false, true, true, false, false, true, true,
        ];
        for (lhs, rhs, expected) in [
            (&null, &null, equal),
            (&null, &first_value, less),
            (&first_value, &null, greater),
            (&first_value, &alias, equal),
            (&first_value, &second_value, less),
            // Adjacent allocations have distinct ids but the first's end
            // and the second's start expose the same numeric address.
            (&one_past, &second_value, equal),
            (&raw_alias, &first_value, equal),
        ] {
            for (op, expected) in OPS.into_iter().zip(expected) {
                assert_eq!(
                    interpreter
                        .eval_icmp(op, &Ty::Ptr, lhs, rhs, &state, block)
                        .unwrap()
                        .as_bool(),
                    Some(expected),
                    "{op:?}: {lhs:?}, {rhs:?}"
                );
            }
        }
        // Address exposure, like PtrToInt, does not dereference the pointer.
        state
            .memory
            .allocations
            .get_mut(&first.allocation)
            .unwrap()
            .alive = false;
        assert_eq!(
            interpreter
                .eval_icmp(ICmpOp::Eq, &Ty::Ptr, &first_value, &alias, &state, block)
                .unwrap()
                .as_bool(),
            Some(true)
        );
    }

    #[test]
    fn pointer_icmp_uses_target_width_signed_address_bits() {
        for bits in [32, 64] {
            let module = module(bits);
            let interpreter = Interpreter::with_module(&module);
            let _width = PointerWidthScope::enter(bits);
            let mut state = state(bits);
            state.memory.next_addr = 1u64 << (bits - 1);
            let block = BlockId(0);
            let high = pointer(InterpretValueKind::Ptr(
                state.memory.alloc(1, 1, block).unwrap(),
            ));
            let null = pointer(InterpretValueKind::NullPtr);
            let high_int = interpreter
                .eval_cast(CastOp::PtrToInt, &Ty::Ptr, &Ty::Usize, &high, &state, block)
                .unwrap();
            let zero_int = InterpretValue::int(Ty::Usize, 0).unwrap();
            for (op, expected) in OPS.into_iter().zip([
                false, true, false, false, true, true, true, true, false, false,
            ]) {
                let direct = interpreter
                    .eval_icmp(op, &Ty::Ptr, &high, &null, &state, block)
                    .unwrap();
                let via_integer = interpreter
                    .eval_icmp(op, &Ty::Usize, &high_int, &zero_int, &state, block)
                    .unwrap();
                assert_eq!(direct.as_bool(), Some(expected), "{bits}-bit {op:?}");
                assert_eq!(direct, via_integer, "PtrToInt agreement: {bits}-bit {op:?}");
            }
        }
    }

    #[test]
    fn pointer_icmp_refuses_poison_unknown_allocations_and_out_of_target_addresses() {
        let module = module(32);
        let interpreter = Interpreter::with_module(&module);
        let state = state(32);
        let null = pointer(InterpretValueKind::NullPtr);
        for value in [
            pointer(InterpretValueKind::PartialBytes(vec![None; 4])),
            pointer(InterpretValueKind::Ptr(InterpretPointer {
                allocation: 99,
                offset: 0,
            })),
            pointer(InterpretValueKind::DanglingPtr(u64::from(u32::MAX) + 1)),
        ] {
            for (lhs, rhs) in [(&value, &null), (&null, &value)] {
                let error = interpreter
                    .eval_icmp(ICmpOp::Eq, &Ty::Ptr, lhs, rhs, &state, BlockId(0))
                    .unwrap_err();
                assert_eq!(
                    error.code,
                    InterpretErrorCode::UndefinedBehavior,
                    "{value:?}"
                );
            }
        }
    }
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
            assert_eq!(eval_bool_binop(BinOp::And, a, b, block).unwrap(), a && b);
            assert_eq!(eval_bool_binop(BinOp::BAnd, a, b, block).unwrap(), a && b);
            assert_eq!(eval_bool_binop(BinOp::BOr, a, b, block).unwrap(), a || b);
            assert_eq!(eval_bool_binop(BinOp::BXor, a, b, block).unwrap(), a ^ b);
        }
    }
}

#[cfg(test)]
mod assert_panic_kind_tests {
    //! Plan item P (wire v52): a failed `Inst::Assert` yields
    //! `Panic { kind }` — the structured `InterpretPanic` and `core`'s exact
    //! message. Lean twins: `ExecutableFixtures.lean`, `assert_*_message_stable`
    //! (the same strings, byte for byte).

    use super::*;
    use crate::inst::AssertOverflowOp;
    use crate::ty::FuncTy;

    fn v(index: u32) -> ValueId {
        ValueId::new(index)
    }

    /// `check(c: bool, a: usize, b: usize)`: one assert of `c` with `kind`
    /// (operands over `a`/`b`), then return.
    fn module(kind: AssertKind) -> Module {
        let mut module = Module::new("assert_panic_kind");
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Bool, Ty::Usize, Ty::Usize],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "check", ft, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry
            .params
            .extend([(v(0), Ty::Bool), (v(1), Ty::Usize), (v(2), Ty::Usize)]);
        entry.body.push(InstrNode::new(Inst::Assert {
            cond: v(0),
            kind,
            site: None,
        }));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(entry);
        module.functions.push(func);
        module
    }

    fn run(kind: AssertKind, cond: bool, a: i128, b: i128) -> InterpretResult<InterpretOutcome> {
        let module = module(kind);
        Interpreter::with_module(&module).execute_func(
            FuncId::new(0),
            [
                InterpretValue::bool(cond),
                InterpretValue::int(Ty::Usize, a).expect("usize"),
                InterpretValue::int(Ty::Usize, b).expect("usize"),
            ],
        )
    }

    /// Every kind's panic: the code, the structured kind, the resolved
    /// operands and `core`'s message.
    #[test]
    fn a_failed_assert_panics_with_its_kind_and_cores_message() {
        let bounds = AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        };
        let misaligned = AssertKind::MisalignedPtr {
            required: v(2),
            found: v(1),
        };
        let mut cases: Vec<(AssertKind, Option<[u128; 2]>, String)> =
            vec![
            (AssertKind::Unspecified, None, "assertion failed".into()),
            (AssertKind::DivByZero, None, "attempt to divide by zero".into()),
            (
                AssertKind::RemByZero,
                None,
                "attempt to calculate the remainder with a divisor of zero".into(),
            ),
            (
                AssertKind::NullPtr,
                None,
                "null pointer dereference occurred".into(),
            ),
            (
                bounds,
                Some([4097, 8]),
                "index out of bounds: the len is 8 but the index is 4097".into(),
            ),
            (
                misaligned,
                Some([8, 4097]),
                "misaligned pointer dereference: address must be a multiple of 0x8 but is 0x1001"
                    .into(),
            ),
        ];
        let overflow = [
            (AssertOverflowOp::Add, "attempt to add with overflow"),
            (AssertOverflowOp::Sub, "attempt to subtract with overflow"),
            (AssertOverflowOp::Mul, "attempt to multiply with overflow"),
            (AssertOverflowOp::Div, "attempt to divide with overflow"),
            (
                AssertOverflowOp::Rem,
                "attempt to calculate the remainder with overflow",
            ),
            (AssertOverflowOp::Shl, "attempt to shift left with overflow"),
            (
                AssertOverflowOp::Shr,
                "attempt to shift right with overflow",
            ),
            (AssertOverflowOp::Neg, "attempt to negate with overflow"),
        ];
        for (op, message) in overflow {
            cases.push((AssertKind::Overflow(op), None, message.into()));
        }
        for (kind, operands, message) in cases {
            let error = run(kind, false, 4097, 8).expect_err("a false assert panics");
            assert_eq!(error.code, InterpretErrorCode::Panic, "{kind:?}");
            assert_eq!(error.message, message, "{kind:?}");
            let panic = error.panic().expect("a panic carries its kind");
            assert_eq!(panic.kind, kind);
            assert_eq!(panic.operands, operands, "{kind:?}");
            assert_eq!(panic.message(), message);
        }
    }

    /// The negative twin: a TRUE assert of every kind continues, and carries
    /// no panic; only the panic code ever carries one.
    #[test]
    fn a_passing_assert_of_any_kind_continues() {
        for kind in [
            AssertKind::Unspecified,
            AssertKind::Overflow(AssertOverflowOp::Add),
            AssertKind::BoundsCheck {
                index: v(1),
                len: v(2),
            },
            AssertKind::NullPtr,
        ] {
            assert!(run(kind, true, 1, 2).is_ok(), "{kind:?}");
        }
        assert_eq!(
            InterpretError::new(InterpretErrorCode::Panic, "x").panic(),
            None
        );
    }

    /// The operands are read ONLY on failure, as the Lean model reads them: a
    /// passing check whose operand is poison continues; a failing one is UB
    /// (inspecting poison), not a panic.
    #[test]
    fn kind_operands_are_inspected_only_when_the_check_fails() {
        let mut module = module(AssertKind::BoundsCheck {
            index: v(3),
            len: v(2),
        });
        let entry = &mut module.functions[0].blocks[0];
        entry.body.insert(
            0,
            InstrNode::new(Inst::Undef { ty: Ty::Usize }).with_result(v(3)),
        );
        let args = |cond: bool| {
            [
                InterpretValue::bool(cond),
                InterpretValue::int(Ty::Usize, 0).expect("usize"),
                InterpretValue::int(Ty::Usize, 1).expect("usize"),
            ]
        };
        let interpreter = Interpreter::with_module(&module);
        assert!(interpreter.execute_func(FuncId::new(0), args(true)).is_ok());
        let error = interpreter
            .execute_func(FuncId::new(0), args(false))
            .expect_err("a failing check reads its poison operand");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert_eq!(error.panic(), None);
    }
}

#[cfg(test)]
mod panic_site_tests {
    //! Amendment P (wire v54, `docs/SPEC_RATIFICATIONS.md` §19.1): a failed
    //! sited check is the terminal panic (kind, operand values, entry,
    //! resolved location); the entry is never executed. Lean twins:
    //! `ExecutableFixtures.lean`, `assert_site_*_stable` /
    //! `assert_invoke_*_stable`.

    use super::*;
    use crate::inst::{PanicLocation, PanicSite};
    use crate::ty::FuncTy;
    use crate::{Global, Linkage};

    fn v(index: u32) -> ValueId {
        ValueId::new(index)
    }

    fn b(index: u32) -> BlockId {
        BlockId::new(index)
    }

    fn global(name: &str, initializer: Option<Constant>) -> Global {
        Global {
            name: name.to_owned(),
            ty: Ty::U64,
            mutable: false,
            initializer,
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        }
    }

    /// Function 0 is the bodyless entry `panic_entry(usize, usize, ptr)`;
    /// function 1 is the bodyless location-only entry `panic_loc(ptr)`;
    /// global 0 is the location record `loc` (a `u64`, 7).
    fn base_module(name: &str) -> Module {
        let mut module = Module::new(name);
        let two_ops = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Usize, Ty::Usize, Ty::Ptr],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let loc_only = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Ptr],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions.push(Function::new(
            FuncId::new(0),
            "panic_entry",
            two_ops,
            BlockId::new(0),
        ));
        module.functions.push(Function::new(
            FuncId::new(1),
            "panic_loc",
            loc_only,
            BlockId::new(0),
        ));
        module.globals.push(global("loc", Some(Constant::Int(7))));
        module
    }

    fn bounds() -> AssertKind {
        AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        }
    }

    fn site(entry: u32, location: PanicLocation) -> PanicSite {
        PanicSite {
            entry: FuncId::new(entry),
            location,
        }
    }

    /// Function 2, `check(c: bool, i: usize, n: usize, p: ptr)`: `prelude`,
    /// then one assert of `c` with `kind` and `site`, then return.
    fn check_module(kind: AssertKind, site: PanicSite, prelude: Vec<InstrNode>) -> Module {
        let mut module = base_module("panic_site");
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Bool, Ty::Usize, Ty::Usize, Ty::Ptr],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(2), "check", ft, b(0));
        let mut entry = Block::new(b(0));
        entry.params.extend([
            (v(0), Ty::Bool),
            (v(1), Ty::Usize),
            (v(2), Ty::Usize),
            (v(3), Ty::Ptr),
        ]);
        entry.body.extend(prelude);
        entry.body.push(InstrNode::new(Inst::Assert {
            cond: v(0),
            kind,
            site: Some(site),
        }));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(entry);
        module.functions.push(func);
        module
    }

    fn args(cond: bool, pointer: InterpretValue) -> [InterpretValue; 4] {
        [
            InterpretValue::bool(cond),
            InterpretValue::int(Ty::Usize, 9).expect("usize"),
            InterpretValue::int(Ty::Usize, 4).expect("usize"),
            pointer,
        ]
    }

    fn null() -> InterpretValue {
        InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::NullPtr,
        }
    }

    fn run(module: &Module, cond: bool) -> InterpretResult<InterpretOutcome> {
        Interpreter::with_module(module).execute_func(FuncId::new(2), args(cond, null()))
    }

    fn panic_of(error: &InterpretError) -> &InterpretPanic {
        assert_eq!(error.code, InterpretErrorCode::Panic, "{error:?}");
        error.panic().expect("a failed assert carries its panic")
    }

    /// The outcome names the kind, its operand values, the entry and the
    /// resolved location; the message is the kind's rendering.
    #[test]
    fn a_failed_sited_assert_panics_with_its_entry_and_location() {
        let module = check_module(
            bounds(),
            site(0, PanicLocation::Global(GlobalId::new(0))),
            vec![],
        );
        let error = run(&module, false).expect_err("a false check panics");
        let panic = panic_of(&error);
        assert_eq!(panic.kind, bounds());
        assert_eq!(panic.operands, Some([9, 4]));
        assert_eq!(
            panic.site,
            Some(InterpretPanicSite {
                entry: FuncId::new(0),
                location: PanicLocationValue::Global {
                    global: GlobalId::new(0),
                    offset: 0,
                },
            })
        );
        assert_eq!(
            error.message,
            "index out of bounds: the len is 4 but the index is 9"
        );
    }

    /// A location-only entry on an `Unspecified` check: the site is reported
    /// with the historical message (MIR's coroutine-resume kinds).
    #[test]
    fn a_failed_unkinded_sited_assert_reports_its_site() {
        let module = check_module(
            AssertKind::Unspecified,
            site(1, PanicLocation::Global(GlobalId::new(0))),
            vec![],
        );
        let error = run(&module, false).expect_err("a false check panics");
        let panic = panic_of(&error);
        assert_eq!(panic.kind, AssertKind::Unspecified);
        assert_eq!(panic.operands, None);
        assert_eq!(
            panic.site.map(|site| site.entry),
            Some(FuncId::new(1)),
            "the location-only entry"
        );
        assert_eq!(error.message, "assertion failed");
    }

    /// A passing check reads only its condition: poison operands and a
    /// poison location are never inspected, and the run returns.
    #[test]
    fn a_passing_sited_assert_reads_neither_operands_nor_location() {
        let poison = |id: u32, ty: Ty| InstrNode::new(Inst::Undef { ty }).with_result(v(id));
        let module = check_module(
            AssertKind::BoundsCheck {
                index: v(10),
                len: v(11),
            },
            site(0, PanicLocation::Value(v(12))),
            vec![
                poison(10, Ty::Usize),
                poison(11, Ty::Usize),
                poison(12, Ty::Ptr),
            ],
        );
        assert!(run(&module, true).is_ok(), "a true check continues");
        // The control: the same module failing inspects them (UB).
        let error = run(&module, false).expect_err("a false check reads its operands");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    }

    /// A `Global` location resolves WITHOUT materializing its global: no
    /// allocation, no initializer read. Two witnesses: an id with no global
    /// behind it, and a global whose initializer could not be materialized
    /// (a `SymbolAddr` naming no global) both still yield the panic.
    #[test]
    fn a_static_location_is_resolved_without_materializing_its_global() {
        let module = check_module(
            AssertKind::DivByZero,
            site(1, PanicLocation::Global(GlobalId::new(7))),
            vec![],
        );
        let panic = panic_of(&run(&module, false).expect_err("panics")).clone();
        assert_eq!(
            panic.site.map(|site| site.location),
            Some(PanicLocationValue::Global {
                global: GlobalId::new(7),
                offset: 0,
            })
        );
        let mut module = check_module(
            AssertKind::DivByZero,
            site(1, PanicLocation::Global(GlobalId::new(0))),
            vec![],
        );
        module.globals[0].initializer = Some(Constant::SymbolAddr {
            symbol: "no_such_symbol".into(),
            addend: 0,
        });
        let error = run(&module, false).expect_err("panics");
        assert!(panic_of(&error).site.is_some());
        // The control: ADDRESSING that global does materialize it and fails.
        let mut addressed = module.clone();
        addressed.functions[2].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(v(20)),
        );
        let error = run(&addressed, false).expect_err("materializing fails first");
        assert_ne!(error.code, InterpretErrorCode::Panic, "{error:?}");
    }

    /// `#[track_caller]` forwarding: the location is the pointer the caller
    /// passed. One into a materialized global resolves to that global at its
    /// byte offset.
    #[test]
    fn a_value_location_resolves_to_the_global_it_addresses() {
        for offset in [0u64, 4] {
            let prelude = vec![
                InstrNode::new(Inst::GlobalAddr {
                    global: GlobalId::new(0),
                })
                .with_result(v(20)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(offset as i128),
                })
                .with_result(v(21)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: v(20),
                    indices: vec![v(21)],
                    inbounds: true,
                })
                .with_result(v(22)),
            ];
            let module = check_module(bounds(), site(0, PanicLocation::Value(v(22))), prelude);
            let panic = panic_of(&run(&module, false).expect_err("panics")).clone();
            assert_eq!(
                panic.site.map(|site| site.location),
                Some(PanicLocationValue::Global {
                    global: GlobalId::new(0),
                    offset,
                }),
                "offset {offset}"
            );
        }
    }

    /// A live pointer outside every global (a stack slot) resolves to `Other`.
    #[test]
    fn a_value_location_outside_every_global_is_other() {
        let prelude = vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::U64,
                count: None,
                align: None,
            })
            .with_result(v(20)),
        ];
        let module = check_module(bounds(), site(0, PanicLocation::Value(v(20))), prelude);
        let panic = panic_of(&run(&module, false).expect_err("panics")).clone();
        assert_eq!(
            panic.site.map(|site| site.location),
            Some(PanicLocationValue::Other)
        );
    }

    /// On failure a null, dangling or poison location is UB, not a panic; the
    /// kind's operands are read FIRST, so a poison operand is the reported
    /// fault even when the location is bad too.
    #[test]
    fn a_null_dangling_or_poison_location_on_failure_is_ub() {
        // Null: the caller passes a null pointer as `p` (%3).
        let module = check_module(bounds(), site(0, PanicLocation::Value(v(3))), vec![]);
        let error = run(&module, false).expect_err("UB");
        assert_eq!(
            error.code,
            InterpretErrorCode::UndefinedBehavior,
            "{error:?}"
        );
        assert!(
            error.message.contains("panic location"),
            "{}",
            error.message
        );
        assert_eq!(error.panic(), None);
        // Dangling: a no-provenance address, and a freed heap cell.
        let dangling = InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::DanglingPtr(4096),
        };
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(2), args(false, dangling))
            .expect_err("UB");
        assert_eq!(
            error.code,
            InterpretErrorCode::UndefinedBehavior,
            "{error:?}"
        );
        let freed = vec![
            InstrNode::new(Inst::HeapAlloc {
                ty: Ty::U64,
                count: None,
                align: None,
                origin: crate::inst::AllocOrigin::RustHeap,
            })
            .with_result(v(20)),
            InstrNode::new(Inst::Dealloc { ptr: v(20) }),
        ];
        let module = check_module(bounds(), site(0, PanicLocation::Value(v(20))), freed);
        let error = run(&module, false).expect_err("UB");
        assert_eq!(
            error.code,
            InterpretErrorCode::UndefinedBehavior,
            "{error:?}"
        );
        assert!(
            error.message.contains("panic location"),
            "{}",
            error.message
        );
        // Poison location.
        let poison = vec![InstrNode::new(Inst::Undef { ty: Ty::Ptr }).with_result(v(20))];
        let module = check_module(bounds(), site(0, PanicLocation::Value(v(20))), poison);
        let error = run(&module, false).expect_err("UB");
        assert_eq!(
            error.code,
            InterpretErrorCode::UndefinedBehavior,
            "{error:?}"
        );
        // Operands first: a poison INDEX with a null location reports the
        // operand, not the location.
        let module = check_module(
            AssertKind::BoundsCheck {
                index: v(20),
                len: v(2),
            },
            site(0, PanicLocation::Value(v(3))),
            vec![InstrNode::new(Inst::Undef { ty: Ty::Usize }).with_result(v(20))],
        );
        let error = run(&module, false).expect_err("UB");
        assert_eq!(
            error.code,
            InterpretErrorCode::UndefinedBehavior,
            "{error:?}"
        );
        assert!(
            !error.message.contains("panic location"),
            "the operand is read before the location: {}",
            error.message
        );
    }

    /// Function 2, `guarded(c: bool, x: usize) -> usize`: bb0 is
    /// `assert_invoke %c, div_by_zero, panic @func.1 at @global.0 to bb1(%x)
    /// unwind bb2`; bb1 returns its parameter; bb2 is a cleanup pad that
    /// resumes.
    fn assert_invoke_module() -> Module {
        let mut module = base_module("assert_invoke");
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Bool, Ty::Usize],
                returns: vec![Ty::Usize],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(2), "guarded", ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.params.extend([(v(0), Ty::Bool), (v(1), Ty::Usize)]);
        bb0.body.push(InstrNode::new(Inst::AssertInvoke {
            cond: v(0),
            kind: AssertKind::DivByZero,
            site: site(1, PanicLocation::Global(GlobalId::new(0))),
            normal_dest: b(1),
            normal_args: vec![v(1)],
            unwind_dest: b(2),
        }));
        let mut bb1 = Block::new(b(1));
        bb1.params.push((v(2), Ty::Usize));
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results(vec![v(3), v(4)]),
        );
        bb2.body.push(InstrNode::new(Inst::Resume { exn: v(3) }));
        func.blocks.extend([bb0, bb1, bb2]);
        module.functions.push(func);
        module
    }

    fn run_guarded(module: &Module, cond: bool) -> InterpretResult<InterpretOutcome> {
        Interpreter::with_module(module).execute_func(
            FuncId::new(2),
            [
                InterpretValue::bool(cond),
                InterpretValue::int(Ty::Usize, 42).expect("usize"),
            ],
        )
    }

    #[test]
    fn assert_invoke_takes_its_normal_edge_when_the_check_passes() {
        let module = assert_invoke_module();
        let outcome = run_guarded(&module, true).expect("a true check takes the normal edge");
        assert_eq!(
            outcome.returns,
            vec![InterpretValue::int(Ty::Usize, 42).expect("usize")]
        );
    }

    /// The panic=abort projection: a failing `AssertInvoke` is the sited
    /// panic, and its pad is never entered (entering it would be the
    /// `UnsupportedInstruction` a directly-entered landing pad is).
    #[test]
    fn assert_invoke_failure_is_the_sited_panic_and_never_enters_its_pad() {
        let module = assert_invoke_module();
        let error = run_guarded(&module, false).expect_err("a false check panics");
        let panic = panic_of(&error);
        assert_eq!(panic.kind, AssertKind::DivByZero);
        assert_eq!(
            panic.site,
            Some(InterpretPanicSite {
                entry: FuncId::new(1),
                location: PanicLocationValue::Global {
                    global: GlobalId::new(0),
                    offset: 0,
                },
            })
        );
        assert_eq!(error.message, "attempt to divide by zero");
    }

    /// A panic raised in a callee leaves through `Call` and `Invoke`
    /// unchanged: the caller observes the callee's sited outcome.
    #[test]
    fn a_sited_panic_propagates_unchanged_through_call_and_invoke() {
        let mut module = assert_invoke_module();
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Bool, Ty::Usize],
                returns: vec![Ty::Usize],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        // fn 3: `call guarded`; fn 4: `invoke guarded`, with a cleanup pad.
        let mut caller = Function::new(FuncId::new(3), "caller", ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.params.extend([(v(0), Ty::Bool), (v(1), Ty::Usize)]);
        bb0.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(2),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        caller.blocks.push(bb0);
        module.functions.push(caller);
        let mut invoker = Function::new(FuncId::new(4), "invoker", ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.params.extend([(v(0), Ty::Bool), (v(1), Ty::Usize)]);
        bb0.body.push(
            InstrNode::new(Inst::Invoke {
                callee: FuncId::new(2),
                args: vec![v(0), v(1)],
                normal_dest: b(1),
                normal_args: vec![v(2)],
                unwind_dest: b(2),
            })
            .with_result(v(2)),
        );
        let mut bb1 = Block::new(b(1));
        bb1.params.push((v(3), Ty::Usize));
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results(vec![v(4), v(5)]),
        );
        bb2.body.push(InstrNode::new(Inst::Resume { exn: v(4) }));
        invoker.blocks.extend([bb0, bb1, bb2]);
        module.functions.push(invoker);
        let direct = run_guarded(&module, false).expect_err("panics");
        for outer in [3, 4] {
            let error = Interpreter::with_module(&module)
                .execute_func(
                    FuncId::new(outer),
                    [
                        InterpretValue::bool(false),
                        InterpretValue::int(Ty::Usize, 42).expect("usize"),
                    ],
                )
                .expect_err("the callee's panic propagates");
            assert_eq!(error.code, InterpretErrorCode::Panic);
            assert_eq!(error.panic, direct.panic, "fn {outer}");
            assert_eq!(error.message, direct.message, "fn {outer}");
        }
    }
}

#[cfg(test)]
#[path = "interpret_uninit_tests.rs"]
mod uninit_lane_tests;

#[cfg(test)]
#[path = "interpret_drop_glue_tests.rs"]
mod drop_glue_tests;

#[cfg(test)]
#[path = "interpret_float_choice_tests.rs"]
mod float_choice_tests;

#[cfg(test)]
#[path = "interpret_tensor_contract_tests.rs"]
mod tensor_contract_tests;

#[cfg(test)]
#[path = "interpret_tensor_gather_scatter_tests.rs"]
mod tensor_gather_scatter_tests;

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
        module
            .add_func_type(FuncTy {
                abi: None,
                params: Vec::new(),
                returns,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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

            section: None,
            visibility: Default::default(),
            retained: false,
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

    /// One meaning for `Dealloc` of a reference-counted cell (SPEC "A
    /// reference-counted cell is released by `Release`, never by
    /// `Dealloc`"): `HeapAlloc { origin: CleanHeap | SwiftHeap }` + `Dealloc`
    /// is undefined behaviour naming the rule, as Lean's `semDealloc` refuses
    /// the cell's `arcRef` permission (`semDealloc_arcRef_is_ub`). Every other
    /// allocation keeps its meaning: `RustHeap`, `CMalloc` and a stack
    /// `Alloca` are freed at their base and the program runs to the loaded
    /// value.
    #[test]
    fn dealloc_of_a_reference_counted_cell_is_undefined_behavior() {
        use crate::inst::AllocOrigin;
        // `None` = a stack `Alloca`.
        let cases: [(Option<AllocOrigin>, bool); 5] = [
            (Some(AllocOrigin::CleanHeap), true),
            (Some(AllocOrigin::SwiftHeap), true),
            (Some(AllocOrigin::RustHeap), false),
            (Some(AllocOrigin::CMalloc), false),
            (None, false),
        ];
        for (origin, is_ub) in cases {
            let mut function =
                Function::new(FuncId::new(0), "free_cell", crate::FuncTyId::new(0), b(0));
            let mut block = Block::new(b(0));
            let alloc = match origin {
                Some(origin) => Inst::HeapAlloc {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                    origin,
                },
                None => Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
            };
            block.body.push(result(alloc, v(0)));
            block.body.push(result(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                },
                v(1),
            ));
            block.body.push(void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(4),
            }));
            block.body.push(result(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(0),
                    volatile: false,
                    align: Some(4),
                },
                v(2),
            ));
            block.body.push(void(Inst::Dealloc { ptr: v(0) }));
            block.body.push(void(Inst::Return { values: vec![v(2)] }));
            function.blocks.push(block);

            let module = module_with_function(function, vec![Ty::I32]);
            let outcome = Interpreter::with_module(&module).execute_func(FuncId::new(0), []);
            if is_ub {
                let error = outcome.expect_err("Dealloc of a reference-counted cell is UB");
                assert_eq!(
                    error.code,
                    InterpretErrorCode::UndefinedBehavior,
                    "{origin:?}: {}",
                    error.message
                );
                assert!(
                    error.message.contains("reference-counted"),
                    "{origin:?}: the refusal must name the rule, got: {}",
                    error.message
                );
            } else {
                let outcome = outcome.unwrap_or_else(|e| {
                    panic!("{origin:?}: Dealloc of a non-RC allocation executes: {e}")
                });
                assert_eq!(int_signed(&outcome.returns[0]), 7, "{origin:?}");
            }
        }
    }

    /// SPEC "Freeing an allocation under a live borrow is undefined
    /// behaviour": `Dealloc` reads the allocation's live-borrow count, which
    /// every thin `Borrow` / `BorrowMut` of an address inside its requested
    /// bytes raises and every `EndBorrow` naming it lowers. Over a stack slot
    /// and both non-RC heap origins. The one-past-the-end row pins the scope
    /// clause (for a heap cell that offset is the slack tail, which moves no
    /// count either), and the extra-`EndBorrow` row pins that `EndBorrow`
    /// never faults and the count never goes below zero.
    #[test]
    fn dealloc_under_a_live_borrow_is_undefined_behavior() {
        use crate::inst::AllocOrigin;
        #[derive(Clone, Copy, Debug)]
        enum Op {
            /// `Borrow` of the allocation at this byte offset.
            Shared(u64),
            /// `BorrowMut` of the allocation at this byte offset.
            Unique(u64),
            /// `Borrow` of the n-th borrow value taken so far (a reborrow).
            Reborrow(usize),
            /// `EndBorrow` of the n-th borrow value taken so far.
            End(usize),
        }
        use Op::{End, Reborrow, Shared, Unique};
        let cases: &[(&str, &[Op], bool)] = &[
            ("shared, live", &[Shared(0)], true),
            ("unique, live", &[Unique(0)], true),
            ("interior shared, live", &[Shared(4)], true),
            ("shared, ended", &[Shared(0), End(0)], false),
            ("unique, ended", &[Unique(0), End(0)], false),
            (
                "two shared, one ended",
                &[Shared(0), Shared(0), End(0)],
                true,
            ),
            (
                "two shared, both ended",
                &[Shared(0), Shared(0), End(1), End(0)],
                false,
            ),
            (
                "ended, then borrowed again",
                &[Shared(0), End(0), Unique(0)],
                true,
            ),
            (
                "reborrow chain, ended",
                &[Shared(0), Reborrow(0), End(1), End(0)],
                false,
            ),
            (
                "reborrow chain, outer live",
                &[Shared(0), Reborrow(0), End(1)],
                true,
            ),
            ("one past the end: not counted", &[Shared(8)], false),
            (
                "EndBorrow past zero never faults",
                &[Shared(0), End(0), End(0)],
                false,
            ),
        ];
        // `None` = a stack `Alloca`.
        let regions = [
            None,
            Some(AllocOrigin::RustHeap),
            Some(AllocOrigin::CMalloc),
        ];
        for region in regions {
            for (name, ops, is_ub) in cases {
                let mut function = Function::new(
                    FuncId::new(0),
                    "free_borrowed",
                    crate::FuncTyId::new(0),
                    b(0),
                );
                let mut block = Block::new(b(0));
                let alloc = match region {
                    Some(origin) => Inst::HeapAlloc {
                        ty: Ty::I64,
                        count: None,
                        align: Some(8),
                        origin,
                    },
                    None => Inst::Alloca {
                        ty: Ty::I64,
                        count: None,
                        align: Some(8),
                    },
                };
                block.body.push(result(alloc, v(0)));
                block.body.push(result(
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(7),
                    },
                    v(1),
                ));
                block.body.push(void(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(0),
                    value: v(1),
                    volatile: false,
                    align: Some(8),
                }));
                block.body.push(result(
                    Inst::Load {
                        ty: Ty::I64,
                        ptr: v(0),
                        volatile: false,
                        align: Some(8),
                    },
                    v(2),
                ));
                let mut next = 10u32;
                let mut fresh = || {
                    next += 1;
                    v(next)
                };
                let mut borrows = Vec::new();
                for op in ops.iter() {
                    match *op {
                        Shared(offset) | Unique(offset) => {
                            let index = fresh();
                            block.body.push(result(
                                Inst::Const {
                                    ty: Ty::U64,
                                    value: Constant::Int(i128::from(offset)),
                                },
                                index,
                            ));
                            let at = fresh();
                            block.body.push(result(
                                Inst::GEP {
                                    pointee_ty: Ty::U8,
                                    base: v(0),
                                    indices: vec![index],
                                    inbounds: false,
                                },
                                at,
                            ));
                            let borrow = fresh();
                            let inst = if matches!(op, Shared(_)) {
                                Inst::Borrow { ptr: at }
                            } else {
                                Inst::BorrowMut { ptr: at }
                            };
                            block.body.push(result(inst, borrow));
                            borrows.push(borrow);
                        }
                        Reborrow(n) => {
                            let borrow = fresh();
                            block
                                .body
                                .push(result(Inst::Borrow { ptr: borrows[n] }, borrow));
                            borrows.push(borrow);
                        }
                        End(n) => {
                            block.body.push(void(Inst::EndBorrow {
                                borrow_ptr: borrows[n],
                            }));
                        }
                    }
                }
                block.body.push(void(Inst::Dealloc { ptr: v(0) }));
                block.body.push(void(Inst::Return { values: vec![v(2)] }));
                function.blocks.push(block);

                let module = module_with_function(function, vec![Ty::I64]);
                let outcome = Interpreter::with_module(&module).execute_func(FuncId::new(0), []);
                if *is_ub {
                    let error = match outcome {
                        Ok(ran) => panic!(
                            "{region:?}, {name}: Dealloc under a live borrow is UB, but it ran \
                             to {:?}",
                            ran.returns
                        ),
                        Err(error) => error,
                    };
                    assert_eq!(
                        error.code,
                        InterpretErrorCode::UndefinedBehavior,
                        "{region:?}, {name}: {}",
                        error.message
                    );
                    assert!(
                        error.message.contains("under a live borrow"),
                        "{region:?}, {name}: the refusal must name the rule, got: {}",
                        error.message
                    );
                } else {
                    let outcome = outcome.unwrap_or_else(|e| {
                        panic!("{region:?}, {name}: Dealloc with no live borrow executes: {e}")
                    });
                    assert_eq!(int_signed(&outcome.returns[0]), 7, "{region:?}, {name}");
                }
            }
        }
    }

    /// One meaning for the ARC trio on an allocation that is not
    /// reference-counted (SPEC "An ARC operation counts only a
    /// reference-counted cell"): `Retain`, `Release` and `IsUnique` are defined
    /// only on a `HeapAlloc { origin: SwiftHeap | CleanHeap }` cell. On a stack
    /// `Alloca`, a `RustHeap` or `CMalloc` cell and a global's reservation each
    /// is undefined behaviour naming the rule, as Lean's `requireArcRef`
    /// refuses the `owned` permission those allocations hold. The positive
    /// rows run the RC life cycle (`Retain`: 1 -> 2, `IsUnique` false,
    /// `Release`: 2 -> 1, `IsUnique` true, `Release`: 1 -> 0 frees) on both RC
    /// origins.
    #[test]
    fn arc_operation_on_a_non_reference_counted_allocation_is_undefined_behavior() {
        use crate::inst::AllocOrigin;
        #[derive(Clone, Copy, Debug)]
        enum Region {
            Heap(AllocOrigin),
            Stack,
            Global,
        }
        #[derive(Clone, Copy, Debug)]
        enum Op {
            Retain,
            Release,
            IsUnique,
        }
        fn region_inst(region: Region) -> Inst {
            match region {
                Region::Heap(origin) => Inst::HeapAlloc {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                    origin,
                },
                Region::Stack => Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                Region::Global => Inst::GlobalAddr {
                    global: GlobalId::new(0),
                },
            }
        }
        fn with_global(mut module: Module) -> Module {
            module.globals.push(crate::Global {
                name: "CELL".to_string(),
                ty: Ty::I32,
                mutable: true,
                initializer: None,
                linkage: crate::Linkage::Internal,
                tls: None,
                align: None,
                section: None,
                visibility: Default::default(),
                retained: false,
            });
            module
        }

        let non_rc = [
            Region::Stack,
            Region::Heap(AllocOrigin::RustHeap),
            Region::Heap(AllocOrigin::CMalloc),
            Region::Global,
        ];
        for region in non_rc {
            for op in [Op::Retain, Op::Release, Op::IsUnique] {
                let mut function =
                    Function::new(FuncId::new(0), "arc_cell", crate::FuncTyId::new(0), b(0));
                let mut block = Block::new(b(0));
                block.body.push(result(region_inst(region), v(0)));
                let returns = match op {
                    Op::Retain => {
                        block.body.push(void(Inst::Retain { ptr: v(0) }));
                        block.body.push(void(Inst::Return { values: vec![] }));
                        vec![]
                    }
                    Op::Release => {
                        block.body.push(void(Inst::Release { ptr: v(0) }));
                        block.body.push(void(Inst::Return { values: vec![] }));
                        vec![]
                    }
                    Op::IsUnique => {
                        block.body.push(result(Inst::IsUnique { ptr: v(0) }, v(1)));
                        block.body.push(void(Inst::Return { values: vec![v(1)] }));
                        vec![Ty::Bool]
                    }
                };
                function.blocks.push(block);
                let module = with_global(module_with_function(function, returns));
                let error = Interpreter::with_module(&module)
                    .execute_func(FuncId::new(0), [])
                    .expect_err("an ARC operation on a non-reference-counted allocation is UB");
                assert_eq!(
                    error.code,
                    InterpretErrorCode::UndefinedBehavior,
                    "{region:?} x {op:?}: {}",
                    error.message
                );
                assert!(
                    error.message.contains("not a reference-counted cell"),
                    "{region:?} x {op:?}: the refusal must name the rule, got: {}",
                    error.message
                );
            }
        }

        // The positive rows: the RC life cycle on both RC origins.
        for origin in [AllocOrigin::CleanHeap, AllocOrigin::SwiftHeap] {
            let mut function =
                Function::new(FuncId::new(0), "rc_cell", crate::FuncTyId::new(0), b(0));
            let mut block = Block::new(b(0));
            block
                .body
                .push(result(region_inst(Region::Heap(origin)), v(0)));
            block.body.push(void(Inst::Retain { ptr: v(0) }));
            block.body.push(result(Inst::IsUnique { ptr: v(0) }, v(1)));
            block.body.push(void(Inst::Release { ptr: v(0) }));
            block.body.push(result(Inst::IsUnique { ptr: v(0) }, v(2)));
            block.body.push(void(Inst::Release { ptr: v(0) }));
            block.body.push(void(Inst::Return {
                values: vec![v(1), v(2)],
            }));
            function.blocks.push(block);
            let module = module_with_function(function, vec![Ty::Bool, Ty::Bool]);
            let outcome = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .unwrap_or_else(|e| panic!("{origin:?}: the RC life cycle executes: {e}"));
            assert_eq!(
                format!("{:?}", outcome.returns[0].kind),
                "Bool(false)",
                "{origin:?}: count 2 is not unique"
            );
            assert_eq!(
                format!("{:?}", outcome.returns[1].kind),
                "Bool(true)",
                "{origin:?}: count 1 is unique"
            );
        }
    }

    /// SPEC "An ARC operation counts only a reference-counted cell", clause 3
    /// (decided 2026-09-30): `Retain` / `Release` / `IsUnique` are defined only
    /// through a pointer at the OBJECT BASE of the reference-counted cell it
    /// was derived from. Each operation, on a `CleanHeap` and a `SwiftHeap`
    /// `i64` cell, through the cell's base advanced by 4 bytes (interior), 8
    /// (one past the end), 20 (inside the heap slack tail) and 32 (past the
    /// slack, where the next allocation sits), is undefined behaviour naming
    /// the offset — the refusal the pinned runtime path (`check_rc_cell`)
    /// already made. The base itself is the positive control.
    #[test]
    fn arc_operand_off_its_cell_base_is_undefined_behavior() {
        use crate::inst::AllocOrigin;
        #[derive(Clone, Copy, Debug)]
        enum Op {
            Retain,
            Release,
            IsUnique,
        }
        fn run(origin: AllocOrigin, op: Op, offset: i128) -> InterpretResult<InterpretOutcome> {
            let mut function =
                Function::new(FuncId::new(0), "arc_offset", crate::FuncTyId::new(0), b(0));
            let mut block = Block::new(b(0));
            block.body.push(result(
                Inst::HeapAlloc {
                    ty: Ty::I64,
                    count: None,
                    align: Some(8),
                    origin,
                },
                v(0),
            ));
            // A second cell after the first, so a past-the-slack operand has a
            // reference-counted neighbour to (wrongly) count.
            block.body.push(result(
                Inst::HeapAlloc {
                    ty: Ty::I64,
                    count: None,
                    align: Some(8),
                    origin,
                },
                v(1),
            ));
            block.body.push(result(
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(offset),
                },
                v(2),
            ));
            block.body.push(result(
                Inst::GEP {
                    pointee_ty: Ty::I8,
                    base: v(0),
                    indices: vec![v(2)],
                    inbounds: false,
                },
                v(3),
            ));
            let returns = match op {
                Op::Retain => {
                    block.body.push(void(Inst::Retain { ptr: v(3) }));
                    block.body.push(void(Inst::Return { values: vec![] }));
                    vec![]
                }
                Op::Release => {
                    block.body.push(void(Inst::Release { ptr: v(3) }));
                    block.body.push(void(Inst::Return { values: vec![] }));
                    vec![]
                }
                Op::IsUnique => {
                    block.body.push(result(Inst::IsUnique { ptr: v(3) }, v(4)));
                    block.body.push(void(Inst::Return { values: vec![v(4)] }));
                    vec![Ty::Bool]
                }
            };
            function.blocks.push(block);
            let module = module_with_function(function, returns);
            Interpreter::with_module(&module).execute_func(FuncId::new(0), [])
        }

        for origin in [AllocOrigin::CleanHeap, AllocOrigin::SwiftHeap] {
            for op in [Op::Retain, Op::Release, Op::IsUnique] {
                run(origin, op, 0).unwrap_or_else(|e| {
                    panic!("{origin:?} x {op:?}: the cell's base is the object pointer: {e}")
                });
                for offset in [4, 8, 20, 32] {
                    let error = run(origin, op, offset)
                        .expect_err("an ARC operand off its cell's base is UB");
                    assert_eq!(
                        error.code,
                        InterpretErrorCode::UndefinedBehavior,
                        "{origin:?} x {op:?} at +{offset}: {}",
                        error.message
                    );
                    assert!(
                        error.message.contains(&format!(
                            "pointer is at offset {offset} of its cell, not at the object base"
                        )),
                        "{origin:?} x {op:?} at +{offset}: the refusal must name the rule, got: {}",
                        error.message
                    );
                }
            }
        }
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
        let u8_ty = module
            .add_type(Ty::U8)
            .expect("Module::add_type: test fixture");
        module.globals.push(crate::Global {
            name: "KEYS".to_string(),
            ty: Ty::Array(u8_ty, 24),
            mutable: true,
            initializer: None,
            linkage: crate::Linkage::Internal,
            tls: None,
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
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
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U8, Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U8, Ty::U8],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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

    /// v40 `ContainerVtable` at the constant funnel: the null fat pointer's
    /// metadata lane is the ZERO OF ITS OWN TYPE. For the dyn-tail container
    /// kind that type is the vtable word (`Ty::Ptr`), exactly as for
    /// `TraitObject` -- a `NullPtr`, never an integer 0 -- while the slice-tail
    /// twin `ContainerLen` gets a zero LENGTH. Pins that the interpreter
    /// classifies the new kind by what its metadata MEANS, not by name.
    #[test]
    fn container_tail_null_fat_pointer_constants_zero_their_own_metadata_type() {
        use crate::FatPtrKind;
        for (kind, want_meta_ty) in [
            (FatPtrKind::ContainerVtable, Ty::Ptr),
            (FatPtrKind::TraitObject { trait_id: 7 }, Ty::Ptr),
            (FatPtrKind::ContainerLen, Ty::U64),
        ] {
            let fat_ty = Ty::FatPtr(kind);
            let mut function = Function::new(FuncId::new(0), "null_fat", FuncTyId::new(0), b(0));
            let mut block = Block::new(b(0));
            block.body.push(result(
                Inst::Const {
                    ty: fat_ty.clone(),
                    value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
                },
                v(0),
            ));
            block.body.push(void(Inst::Return { values: vec![v(0)] }));
            function.blocks.push(block);
            let module = module_with_function(function, vec![fat_ty.clone()]);

            let outcome = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .unwrap_or_else(|e| panic!("null {kind:?} constant program executes: {e:?}"));
            let value = &outcome.returns[0];
            assert_eq!(value.ty, fat_ty);
            let InterpretValueKind::FatPtr { data, metadata } = &value.kind else {
                panic!("expected a fat pointer value for {kind:?}, got {value:?}");
            };
            assert_eq!(data.kind, InterpretValueKind::NullPtr);
            assert_eq!(metadata.ty, want_meta_ty, "{kind:?}");
            match want_meta_ty {
                Ty::Ptr => assert_eq!(
                    metadata.kind,
                    InterpretValueKind::NullPtr,
                    "{kind:?}: the metadata zero is a null VTABLE, not an integer 0"
                ),
                _ => assert_eq!(int_unsigned(metadata), 0, "{kind:?}: a zero LENGTH"),
            }
        }
    }

    /// A validator may describe a valid i686 wire module, but i686 is outside
    /// the canonical scalar table (its ABI aligns `i64` to 4), so this
    /// interpreter must reject that target rather than guess its layout —
    /// WS2.16 admits only canonical-table 32-bit targets (wasm32). Big-endian
    /// targets stay refused at every width.
    #[test]
    fn fat_pointer_execution_rejects_non_canonical_and_big_endian_targets() {
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
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
    fn scalar_only_execution_also_rejects_a_non_reference_target() {
        let mut module = Module::new("scalar-32-bit-rejected");
        module.target_info = Some(crate::TargetInfo {
            triple: "i686-unknown-linux-gnu".into(),
            pointer_size: 4,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "scalar32", sig, b(0));
        let mut block = Block::new(b(0));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.functions.push(function);

        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("the reference interpreter must not guess a 32-bit ABI");
        assert_eq!(error.code, InterpretErrorCode::UnsupportedMemory);
        assert!(error.message.contains("64-bit little-endian"), "{error:?}");
    }

    #[test]
    fn external_fat_pointer_parts_metadata_is_rejected_before_the_instruction() {
        use crate::FatPtrKind;

        let fat_ty = Ty::FatPtr(FatPtrKind::Str);
        let mut module = Module::new("malformed-fatptr-parts");
        let sig = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::U64],
                returns: vec![fat_ty.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
            .expect_err("entry validation must reject malformed external metadata");
        assert_eq!(error.code, InterpretErrorCode::TypeError);
        assert!(
            error.message == "entry argument: u64 value has no integer payload",
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
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![fat_ty.clone(), fat_ty.clone(), Ty::U8, Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
    fn external_fat_pointer_store_metadata_is_rejected_before_the_instruction() {
        use crate::FatPtrKind;

        let fat_ty = Ty::FatPtr(FatPtrKind::Str);
        let mut module = Module::new("malformed-fatptr");
        let sig = module
            .add_func_type(FuncTy {
                params: vec![fat_ty.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
            .expect_err("entry validation must reject malformed nested external metadata");
        assert_eq!(error.code, InterpretErrorCode::TypeError);
        assert!(
            error.message == "entry argument: u64 value has no integer payload",
            "{error:?}"
        );
    }

    #[test]
    fn fat_pointer_instruction_helpers_reject_malformed_internal_metadata() {
        // Bypass the external-entry validator deliberately: these are the
        // exact helpers used by PtrFromParts and Store, which must keep their
        // own guard even when an internal value has a malformed payload.
        let interpreter = Interpreter::new();
        let ty = Ty::FatPtr(crate::FatPtrKind::Str);
        let data = InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::NullPtr,
        };
        let metadata = InterpretValue {
            ty: Ty::U64,
            kind: InterpretValueKind::Bool(true),
        };
        let parts_error = interpreter
            .eval_ptr_from_parts(&ty, &Ty::U64, &data, &metadata, b(0))
            .expect_err("the instruction must validate its own metadata");
        assert_eq!(parts_error.code, InterpretErrorCode::TypeError);
        assert!(parts_error.message.contains("metadata does not inhabit"));

        let malformed = InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::FatPtr {
                data: Box::new(data.clone()),
                metadata: Box::new(metadata),
            },
        };
        let mut state = ExecState {
            values: BTreeMap::new(),
            memory: MemoryState::default(),
            globals: BTreeMap::new(),
            frames: BTreeSet::new(),
            next_frame_id: 0,
            steps: 0,
            remaining_fuel: u64::MAX,
            host: HostState::new(),
            host_calls: 0,
            drop_glue: None,
            unwind: UnwindState::default(),
        };
        let store_error = interpreter
            .eval_store(&ty, &data, &malformed, None, &mut state, b(0), false)
            .expect_err("metadata validation must precede the invalid null destination");
        assert_eq!(store_error.code, InterpretErrorCode::TypeError);
        assert!(store_error.message.contains("metadata does not inhabit"));
        assert!(state.memory.allocations.is_empty());
    }

    /// B6 closure captures round-trip at REGISTER level: a closure value seeds
    /// via `Constant::Closure`, rewrites a capture with `InsertField`, and reads
    /// it back with `ExtractField` — the by-value closure-env lane (no memory
    /// transit; a closure type still has no byte layout, fail-closed elsewhere).
    #[test]
    fn closure_captures_insert_extract_round_trip() {
        let mut module = Module::new("b6");
        let callee_sig = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let clo_ty_id = module
            .add_closure_type(crate::ClosureTy {
                func: callee_sig,
                captures: vec![Ty::I32, Ty::Bool],
            })
            .expect("Module::add_closure_type: test fixture");
        let clo_ty = Ty::Closure(clo_ty_id);
        let main_sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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

    /// WS2.18 review: the reference half of the Lean fixtures
    /// `switch_u128_case_taken_stable` / `switch_symbol_addr_case_refused_stable`
    /// / `switch_match_before_symbol_addr_case_taken_stable`
    /// (lean/trust_ir-semantics/TrustIr/Semantics/ExecutableFixtures.lean). A
    /// `U128` switch whose case is the canonical `Constant::U128` spelling of a
    /// value above `i128::MAX` is scanned in order: `cases[0]` decides which
    /// block runs. Returns 1 from the case block, 0 from the default block.
    fn run_u128_switch(cases: Vec<Constant>) -> InterpretResult<u128> {
        let big = (1u128 << 127) + 9;
        let mut function = Function::new(FuncId::new(0), "sw128", crate::FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.body.push(result(
            Inst::Const {
                ty: Ty::U128,
                value: Constant::u128(big),
            },
            v(0),
        ));
        entry.body.push(void(Inst::Switch {
            value: v(0),
            default: b(2),
            default_args: Vec::new(),
            cases: cases
                .into_iter()
                .map(|value| SwitchCase {
                    value,
                    target: b(1),
                    args: Vec::new(),
                })
                .collect(),
            exhaustive_enum_unreachable: false,
        }));
        let mut case_block = Block::new(b(1));
        case_block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(1),
            },
            v(1),
        ));
        case_block
            .body
            .push(void(Inst::Return { values: vec![v(1)] }));
        let mut default_block = Block::new(b(2));
        default_block.body.push(result(
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0),
            },
            v(2),
        ));
        default_block
            .body
            .push(void(Inst::Return { values: vec![v(2)] }));
        function.blocks.push(entry);
        function.blocks.push(case_block);
        function.blocks.push(default_block);
        let module = module_with_function(function, vec![Ty::U8]);
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .map(|outcome| int_unsigned(&outcome.returns[0]))
    }

    #[test]
    fn switch_takes_a_canonical_u128_case_and_refuses_a_symbol_addr_case() {
        let big = (1u128 << 127) + 9;
        let symbol = || Constant::SymbolAddr {
            symbol: "f".to_string(),
            addend: 0,
        };
        // An equal canonical U128 case is TAKEN (the Lean scan used to miss it).
        assert_eq!(run_u128_switch(vec![Constant::u128(big)]).expect("runs"), 1);
        // An unequal one misses to the default edge.
        assert_eq!(
            run_u128_switch(vec![Constant::u128(big + 1)]).expect("runs"),
            0
        );
        // A link-time address REACHED by the in-order scan is an error, never a
        // miss that falls through to a later case or to the default edge ...
        let error = run_u128_switch(vec![symbol(), Constant::u128(big)])
            .expect_err("a symbol-address case has no compile-time value");
        assert_eq!(error.code, InterpretErrorCode::TypeError);
        // ... while a case that matches before the scan reaches it is taken.
        assert_eq!(
            run_u128_switch(vec![Constant::u128(big), symbol()]).expect("runs"),
            1
        );
    }

    #[test]
    fn direct_call_executes_callee_frame_and_binds_return() {
        let mut module = Module::new("direct-call");
        let add_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let main_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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

        module
            .try_add_function(main)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(add)
            .expect("Module::try_add_function: test fixture");

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
        // float ops. Rust executes f32/f64 directly; f16 executes too since
        // WS2.15 (conformance `interpret_f16`) but the Lean model still
        // refuses it, so `F16` stays outside the proven subset.
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
        let add_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let main_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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

        module
            .try_add_function(main)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(add)
            .expect("Module::try_add_function: test fixture");

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("indirect call executes");

        assert_eq!(int_signed(&outcome.returns[0]), 42);
    }

    #[test]
    fn recursive_call_exhausts_shared_fuel() {
        let mut module = Module::new("recursive-fuel");
        let recurse_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

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
        let callee_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let main_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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

        module
            .try_add_function(main)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");

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
        let callee_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let main_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(main)
            .expect("Module::try_add_function: test fixture");

        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("function pointer is not registered");

        assert_eq!(error.code, InterpretErrorCode::InvalidFunctionPointer);
        assert_eq!(error.code.as_str(), "invalid_function_pointer");
    }

    #[test]
    fn indirect_signature_mismatch_has_stable_code() {
        let mut module = Module::new("signature-mismatch");
        let callee_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let wrong_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let main_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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

        module
            .try_add_function(main)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");

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

        // ARC: a `CleanHeap` cell (the ARC trio is defined only on a
        // reference-counted cell; on an `Alloca` it is UB, see
        // `arc_operation_on_a_non_reference_counted_allocation_is_undefined_behavior`),
        // retain (count 1->2), IsUnique = false, release (2->1), IsUnique = true.
        let mut arc_fn = Function::new(FuncId::new(0), "arc", crate::FuncTyId::new(0), b(0));
        let mut ab = Block::new(b(0));
        ab.body.push(result(
            Inst::HeapAlloc {
                ty: Ty::I32,
                count: None,
                align: None,
                origin: crate::inst::AllocOrigin::CleanHeap,
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

        // Binding frame: open a 1-slot frame, bind slot 0 = 7 (producing the
        // new handle %3), load it back THROUGH THAT HANDLE, close the frame,
        // return the loaded value. `BindSlot` is functional and yields one
        // result (`inst.rs`; Lean `semBindSlot`; the validator's result
        // table) — the earlier spelling of this test bound it as a void node
        // and read through the pre-bind handle, which no validated module
        // can do.
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
        fb.body.push(result(
            Inst::BindSlot {
                frame: v(0),
                slot: 0,
                value: v(1),
            },
            v(3),
        ));
        fb.body.push(result(
            Inst::LoadSlot {
                frame: v(3),
                slot: 0,
                ty: Ty::I32,
            },
            v(2),
        ));
        fb.body.push(void(Inst::CloseFrame { frame: v(3) }));
        fb.body.push(void(Inst::Return { values: vec![v(2)] }));
        frame_fn.blocks.push(fb);
        let m = module_with_function(frame_fn, vec![Ty::I32]);
        let out = Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), [])
            .expect("binding frame executes");
        assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 7);
    }

    /// `BindSlot` is FUNCTIONAL: each bind yields a fresh handle and the
    /// input handle keeps its prior slot contents (`inst.rs`; Lean
    /// `loadSlot_bindSlot_same` / `Frame.lean` `bindSlot` is `List.set` on a
    /// copy). Bind 7 through `%f0` to get `%f1`, then 9 through `%f1` to get
    /// `%f2`: `%f1` still reads 7, `%f2` reads 9, and the never-bound `%f0`
    /// slot is still unbound: it reads as poison (roadmap WS2.10, the Lean
    /// model's `undef`), which faults only when inspected.
    #[test]
    fn bind_slot_is_functional_and_prior_handles_keep_prior_slots() {
        fn frame_module(load_from: ValueId) -> Module {
            let mut f = Function::new(FuncId::new(0), "frame", crate::FuncTyId::new(0), b(0));
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
            fb.body.push(result(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(9),
                },
                v(2),
            ));
            // %3 = bind_slot %0, 0, 7 ; %4 = bind_slot %3, 0, 9
            fb.body.push(result(
                Inst::BindSlot {
                    frame: v(0),
                    slot: 0,
                    value: v(1),
                },
                v(3),
            ));
            fb.body.push(result(
                Inst::BindSlot {
                    frame: v(3),
                    slot: 0,
                    value: v(2),
                },
                v(4),
            ));
            fb.body.push(result(
                Inst::LoadSlot {
                    frame: load_from,
                    slot: 0,
                    ty: Ty::I32,
                },
                v(5),
            ));
            fb.body.push(void(Inst::CloseFrame { frame: v(4) }));
            fb.body.push(void(Inst::Return { values: vec![v(5)] }));
            f.blocks.push(fb);
            module_with_function(f, vec![Ty::I32])
        }

        for (handle, expected) in [(v(3), 7), (v(4), 9)] {
            let out = Interpreter::with_module(&frame_module(handle))
                .execute_func(FuncId::new(0), [])
                .expect("bound handle executes");
            assert_eq!(out.returns[0].as_int().unwrap().as_signed(), expected);
        }

        // The pre-bind handle was never written: reading it is not "the
        // latest write" (that would be the in-place model this test retires)
        // but an unbound slot, which reads as poison (WS2.10). Returning the
        // poison is an inspection at the call boundary, so it is UB THERE —
        // never the value 9 (or 7) a later bind wrote through another handle.
        let error = Interpreter::with_module(&frame_module(v(0)))
            .execute_func(FuncId::new(0), [])
            .expect_err("the pre-bind handle's slot is unbound poison");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(
            error
                .to_string()
                .contains("Call returns: use of an uninitialized value"),
            "unexpected error: {error}"
        );

        // A void `BindSlot` node — the retired in-place spelling — is a
        // malformed node, not a silently tolerated one.
        let mut m = frame_module(v(4));
        m.functions[0].blocks[0].body[3].results.clear();
        let error = Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), [])
            .expect_err("a result-less bind_slot is malformed");
        assert_eq!(error.code, InterpretErrorCode::MalformedInstruction);
    }

    /// One `Transmute` over a constant operand, returning the cast result.
    fn transmute_module(src_ty: Ty, src: Constant, dst_ty: Ty) -> Module {
        let mut cast_fn = Function::new(FuncId::new(0), "transmute", crate::FuncTyId::new(0), b(0));
        let mut cast_block = Block::new(b(0));
        cast_block.body.push(result(
            Inst::Const {
                ty: src_ty.clone(),
                value: src,
            },
            v(0),
        ));
        cast_block.body.push(result(
            Inst::Cast {
                op: CastOp::Transmute,
                src_ty,
                dst_ty: dst_ty.clone(),
                operand: v(0),
            },
            v(1),
        ));
        cast_block
            .body
            .push(void(Inst::Return { values: vec![v(1)] }));
        cast_fn.blocks.push(cast_block);
        module_with_function(cast_fn, vec![dst_ty])
    }

    /// WS2.9 (subset v3): `Transmute` executes exactly where the Lean
    /// `semCast .Transmute` arm executes — integer/pointer scalars on both
    /// sides — and answers `UnsupportedCast` everywhere else.
    #[test]
    fn transmute_executes_on_the_integer_pointer_scalar_set() {
        // Positive: i32 -> u32 reinterprets the bit pattern (-1 -> u32::MAX).
        let module = transmute_module(Ty::I32, Constant::Int(-1), Ty::U32);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("transmute i32 -> u32 executes");
        assert_eq!(outcome.returns[0].ty, Ty::U32);
        assert_eq!(int_unsigned(&outcome.returns[0]), u128::from(u32::MAX));

        // Positive: the same-type identity and the int -> ptr reinterpret
        // (the Lean `transmute_i64_identity_stable` / `transmute_i64_to_ptr_stable`
        // fixtures) execute too.
        let module = transmute_module(Ty::I64, Constant::Int(42), Ty::I64);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("transmute i64 -> i64 executes");
        assert_eq!(int_signed(&outcome.returns[0]), 42);
        let module = transmute_module(Ty::I64, Constant::Int(42), Ty::Ptr);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("transmute i64 -> ptr executes");
        assert_eq!(outcome.returns[0].ty, Ty::Ptr);

        // Twins: a float or bool on EITHER side is `UnsupportedCast` — the
        // destination cases are the Lean mistranslation control (before v3
        // the model bound an integer at a float/bool type there). The same
        // reinterpretation spelled as `Bitcast` is the sanctioned carrier.
        for (src_ty, src, dst_ty) in [
            (Ty::F32, Constant::Float(1.5), Ty::U32),
            (Ty::U32, Constant::Int(0x3fc0_0000), Ty::F32),
            (Ty::U8, Constant::Int(2), Ty::Bool),
            (Ty::Bool, Constant::Bool(true), Ty::U8),
        ] {
            let module = transmute_module(src_ty.clone(), src, dst_ty.clone());
            let error = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .expect_err("float/bool transmute is outside the executable scalar set");
            assert_eq!(
                error.code,
                InterpretErrorCode::UnsupportedCast,
                "Transmute {src_ty} -> {dst_ty}: {error:?}"
            );
            assert_eq!(error.code.as_str(), "unsupported_cast");
        }
        // Mutation control: a width mismatch inside the scalar set is a
        // TYPE error (validator territory), never a silent reinterpret.
        let module = transmute_module(Ty::I32, Constant::Int(1), Ty::I64);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("transmute i32 -> i64 is a width mismatch");
        assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
    }

    /// `probe() -> dst { p = nullptr; q = ptrtoptr p : ptr -> src; r = transmute q : src -> dst; return r }`
    /// — a pointer-typed Transmute source reached through the ONE cast that
    /// mints a typed pointer, so the verdict is about the Transmute alone.
    fn pointer_transmute_module(src_ty: Ty, dst_ty: Ty) -> Module {
        let mut cast_fn = Function::new(FuncId::new(0), "transmute", crate::FuncTyId::new(0), b(0));
        let mut cast_block = Block::new(b(0));
        cast_block.body.push(result(Inst::NullPtr, v(0)));
        cast_block.body.push(result(
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: src_ty.clone(),
                operand: v(0),
            },
            v(1),
        ));
        cast_block.body.push(result(
            Inst::Cast {
                op: CastOp::Transmute,
                src_ty,
                dst_ty: dst_ty.clone(),
                operand: v(1),
            },
            v(2),
        ));
        cast_block
            .body
            .push(void(Inst::Return { values: vec![v(2)] }));
        cast_fn.blocks.push(cast_block);
        module_with_function(cast_fn, vec![dst_ty])
    }

    /// Review (WS2.9): the pointer member of the executable Transmute set is
    /// EXACTLY `Ty::Ptr`, in step with the subset's `transmute_scalar_ty` and
    /// Lean's `transmuteScalarTy`. A "pointer-like" test here would execute
    /// `*const u8 -> ptr` and `&u8 -> ptr` transmutes that the Lean model
    /// refuses — evidence for nothing. The thin `ptr -> ptr` transmute is
    /// executed and transports the pointer value (a null stays null).
    #[test]
    fn transmute_pointer_member_is_exactly_thin_ptr() {
        let module = pointer_transmute_module(Ty::Ptr, Ty::Ptr);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("transmute ptr -> ptr executes");
        assert_eq!(outcome.returns[0].ty, Ty::Ptr);
        assert!(
            matches!(outcome.returns[0].kind, InterpretValueKind::NullPtr),
            "{:?}",
            outcome.returns[0]
        );
        for (src_ty, dst_ty) in [
            (Ty::PtrConst(Box::new(Ty::U8)), Ty::Ptr),
            (Ty::PtrMut(Box::new(Ty::U8)), Ty::Ptr),
            (Ty::Ref(Box::new(Ty::U8)), Ty::Ptr),
            (Ty::Ptr, Ty::PtrConst(Box::new(Ty::U8))),
        ] {
            let module = pointer_transmute_module(src_ty.clone(), dst_ty.clone());
            let error = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .expect_err("a typed-pointer transmute is outside the executable scalar set");
            assert_eq!(
                error.code,
                InterpretErrorCode::UnsupportedCast,
                "Transmute {src_ty} -> {dst_ty}: {error:?}"
            );
        }
        // Mutation control: the same typed-pointer retag spelled as
        // `PtrToPtr` is the sanctioned carrier and executes.
        let mut retag_fn = Function::new(FuncId::new(0), "retag", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(Inst::NullPtr, v(0)));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::PtrConst(Box::new(Ty::U8)),
                operand: v(0),
            },
            v(1),
        ));
        block.body.push(void(Inst::Return { values: vec![v(1)] }));
        retag_fn.blocks.push(block);
        let module = module_with_function(retag_fn, vec![Ty::PtrConst(Box::new(Ty::U8))]);
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("ptrtoptr ptr -> *const u8 executes");
    }

    /// Review (WS2.9): a LIVE allocation's address survives
    /// `transmute ptr -> u64 -> ptr` with its provenance — the re-derived
    /// pointer is usable for a store and a load, exactly as the Lean model
    /// (`.ptr addr` -> `.int 64 addr` -> `.ptr addr`) says. A model that
    /// executed `Transmute` by minting a fresh dangling pointer from the
    /// integer would refuse the store here (`DanglingPtr`), and one that
    /// transported the operand unchanged would return a pointer at `u64`.
    #[test]
    fn transmute_round_trips_a_live_allocation_address() {
        let mut function =
            Function::new(FuncId::new(0), "round_trip", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
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
            Inst::Cast {
                op: CastOp::Transmute,
                src_ty: Ty::Ptr,
                dst_ty: Ty::U64,
                operand: v(1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::Cast {
                op: CastOp::Transmute,
                src_ty: Ty::U64,
                dst_ty: Ty::Ptr,
                operand: v(2),
            },
            v(3),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(-7),
            },
            v(4),
        ));
        block.body.push(void(Inst::Store {
            ty: Ty::I32,
            ptr: v(3),
            value: v(4),
            volatile: false,
            align: Some(4),
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: Some(4),
            },
            v(5),
        ));
        block.body.push(void(Inst::Return {
            values: vec![v(5), v(2)],
        }));
        function.blocks.push(block);
        let module = module_with_function(function, vec![Ty::I32, Ty::U64]);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("the re-derived pointer is usable");
        assert_eq!(int_signed(&outcome.returns[0]), -7);
        // The integer half IS an integer (not a re-tagged pointer) and is the
        // allocation's address — a nonzero u64.
        assert_eq!(outcome.returns[1].ty, Ty::U64);
        assert!(
            int_unsigned(&outcome.returns[1]) != 0,
            "{:?}",
            outcome.returns[1]
        );

        // Off-set IDENTITY transmutes (`bool -> bool`, `f64 -> f64`) are
        // refused: the gate is on the types, never on whether the
        // reinterpretation would change anything, so `eval_bitcast`'s
        // `src == dst` transport is unreachable for a type outside the set.
        // (Lean: `transmute_bool_identity_unsupported_stable` and the f64 twin.)
        for (ty, value) in [
            (Ty::Bool, Constant::Bool(true)),
            (Ty::F64, Constant::Float(1.5)),
        ] {
            let module = transmute_module(ty.clone(), value, ty.clone());
            let error = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .expect_err("an identity transmute on an off-set type is refused");
            assert_eq!(
                error.code,
                InterpretErrorCode::UnsupportedCast,
                "Transmute {ty} -> {ty}: {error:?}"
            );
        }
    }

    #[test]
    fn intentionally_excluded_casts_have_stable_codes_and_f16_executes() {
        // An aggregate transmute stays outside the executable set (the Lean
        // model has no byte buffer to reinterpret through).
        let cast_module = transmute_module(
            Ty::Tuple(vec![Ty::I32, Ty::I32]),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
            Ty::I64,
        );
        let error = Interpreter::with_module(&cast_module)
            .execute_func(FuncId::new(0), [])
            .expect_err("aggregate transmute is intentionally excluded");
        assert_eq!(error.code, InterpretErrorCode::UnsupportedCast);
        assert_eq!(error.code.as_str(), "unsupported_cast");

        // WS2.15: an `F16` constant is no longer `UnsupportedFloat`; the
        // `Constant::Float(f64)` carrier narrows to the binary16 pattern.
        let mut f16_fn = Function::new(FuncId::new(0), "f16", crate::FuncTyId::new(0), b(0));
        let mut f16_block = Block::new(b(0));
        f16_block.body.push(result(
            Inst::Const {
                ty: Ty::F16,
                value: Constant::Float(1.0),
            },
            v(0),
        ));
        f16_block
            .body
            .push(void(Inst::Return { values: vec![v(0)] }));
        f16_fn.blocks.push(f16_block);
        let f16_module = module_with_function(f16_fn, vec![Ty::F16]);
        let outcome = Interpreter::with_module(&f16_module)
            .execute_func(FuncId::new(0), [])
            .expect("an f16 constant executes (WS2.15)");
        assert_eq!(outcome.returns[0].ty, Ty::F16);
        assert_eq!(
            outcome.returns[0].kind,
            InterpretValueKind::FloatBits(0x3C00),
            "1.0 at binary16 is 0x3C00"
        );
        // The code itself stays stable for the Lean mirror.
        assert_eq!(
            InterpretErrorCode::UnsupportedFloat.as_str(),
            "unsupported_float"
        );
    }

    /// WS2.15: the binary16 rounder, at the edges a hardware `as f16` would
    /// have to get right — kept next to the codec so a change to it is
    /// reviewed against these first (the conformance `interpret_f16` table
    /// pins the same edges THROUGH the instructions).
    #[test]
    fn f16_codec_edge_vectors() {
        // Exact decode of every named pattern.
        for (bits, value) in [
            (0x0000u16, 0.0f64),
            (0x3C00, 1.0),
            (0x3E00, 1.5),
            (0x4080, 2.25),
            (0x4380, 3.75),
            (0x7BFF, 65504.0),
            (0x0001, 2f64.powi(-24)),
            (0x03FF, 1023.0 * 2f64.powi(-24)),
            (0x0400, 2f64.powi(-14)),
            (0xC000, -2.0),
        ] {
            assert_eq!(f16_bits_to_f64(bits), value, "decode {bits:#06x}");
            assert_eq!(f64_to_f16_bits(value), bits, "encode {value}");
        }
        assert_eq!(f64_to_f16_bits(-0.0).to_le_bytes(), [0x00, 0x80]);
        assert_eq!(f16_bits_to_f64(0x8000).to_bits(), (-0.0f64).to_bits());
        assert_eq!(f64_to_f16_bits(f64::INFINITY), 0x7C00);
        assert_eq!(f64_to_f16_bits(f64::NEG_INFINITY), 0xFC00);
        assert!(f16_bits_to_f64(0x7C00).is_infinite());
        // Overflow threshold: 65520 is the tie between 65504 and 2^16 and
        // rounds to even (up, out of the format); anything below it rounds
        // down to 65504.
        assert_eq!(f64_to_f16_bits(65520.0), 0x7C00);
        assert_eq!(f64_to_f16_bits(65519.999), 0x7BFF);
        assert_eq!(f64_to_f16_bits(65512.0), 0x7BFF);
        assert_eq!(f64_to_f16_bits(65536.0), 0x7C00);
        assert_eq!(f64_to_f16_bits(1e300), 0x7C00);
        // Ties to even inside the format: 1 + 2^-11 is the midpoint between
        // 1.0 (even) and 1 + 2^-10 (odd) -> 1.0; 1 + 3*2^-11 is the midpoint
        // between 1 + 2^-10 (odd) and 1 + 2^-9 (even) -> 1 + 2^-9.
        assert_eq!(f64_to_f16_bits(1.0 + 2f64.powi(-11)), 0x3C00);
        assert_eq!(f64_to_f16_bits(1.0 + 3.0 * 2f64.powi(-11)), 0x3C02);
        // Subnormal floor: 2^-25 is the tie between 0 and the smallest
        // subnormal -> 0 (even); anything above it rounds to 0x0001; below
        // it (including every binary64 subnormal) rounds to 0.
        assert_eq!(f64_to_f16_bits(2f64.powi(-25)), 0x0000);
        assert_eq!(f64_to_f16_bits(2f64.powi(-25) * 1.0001), 0x0001);
        assert_eq!(f64_to_f16_bits(2f64.powi(-26)), 0x0000);
        assert_eq!(f64_to_f16_bits(-2f64.powi(-26)), 0x8000);
        assert_eq!(f64_to_f16_bits(f64::from_bits(1)), 0x0000);
        // A subnormal that rounds up into the smallest normal.
        assert_eq!(f64_to_f16_bits(1023.75 * 2f64.powi(-24)), 0x0400);
        // NaN: sign and quiet bit kept, payload truncated to the top ten
        // bits, and a signalling payload is quieted.
        let quiet = f64_to_f16_bits(f64::NAN);
        assert_eq!(quiet & 0x7C00, 0x7C00);
        assert_ne!(quiet & 0x03FF, 0);
        assert_eq!(f64_to_f16_bits(f16_bits_to_f64(0x7E2A)), 0x7E2A);
        assert_eq!(f64_to_f16_bits(f16_bits_to_f64(0xFE2A)), 0xFE2A);
        assert_eq!(f64_to_f16_bits(f16_bits_to_f64(0x7C01)), 0x7E01);
        // Every 16-bit pattern round-trips through binary64 (NaNs quieted).
        for bits in 0..=u16::MAX {
            let back = f64_to_f16_bits(f16_bits_to_f64(bits));
            let expected = if bits & 0x7C00 == 0x7C00 && bits & 0x03FF != 0 {
                bits | 0x0200
            } else {
                bits
            };
            assert_eq!(back, expected, "round trip {bits:#06x}");
        }
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
    /// and panic the kernel; a 256 MiB `mem_budget` then refused such an
    /// allocation. Allocations are SPARSE now (one uninitialized run whatever
    /// the size), so the cap is gone and the program simply EXECUTES: an
    /// ~8 TiB `Alloca`, a store to its last element and a load back cost O(1)
    /// host memory. This test itself would OOM the runner if allocations were
    /// dense again — its passing is the proof they are not.
    #[test]
    fn huge_alloca_is_sparse_and_executes_without_host_oom() {
        let mut module = Module::new("huge-alloca");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "huge_alloca", ft, b(0));
        let mut block = Block::new(b(0));
        // 2^40 elements of i64 ⇒ ~8 TiB requested.
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
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int((1i128 << 40) - 1),
            },
            v(2),
        ));
        block.body.push(result(
            Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(1),
                indices: vec![v(2)],
                inbounds: true,
            },
            v(3),
        ));
        block.body.push(result(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            },
            v(4),
        ));
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(3),
            value: v(4),
            volatile: false,
            align: None,
        }));
        block.body.push(result(
            Inst::Load {
                ty: Ty::I64,
                ptr: v(3),
                volatile: false,
                align: None,
            },
            v(5),
        ));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
        function.blocks.push(block);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("a sparse 8 TiB allocation executes");
        assert_eq!(
            outcome.returns,
            vec![InterpretValue::int(Ty::I64, 42).unwrap()]
        );
    }

    /// What IS still refused is exhausting the ADDRESS SPACE — an allocation
    /// whose last byte no pointer can name — and it is an incapacity
    /// (`OutOfMemory`), never undefined behaviour in the program.
    #[test]
    fn allocation_past_the_address_space_is_out_of_memory() {
        let mut function =
            Function::new(FuncId::new(0), "huge_alloca", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(u64::MAX as i128),
            },
            v(0),
        ));
        block.body.push(result(
            Inst::Alloca {
                ty: Ty::U8,
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
            .expect_err("no pointer can name the last byte");

        assert_eq!(error.code, InterpretErrorCode::OutOfMemory);
        assert_eq!(error.code.as_str(), "out_of_memory");
    }

    /// A handful of elements interprets cleanly (the historical control of the
    /// deleted budget, kept as the small-allocation baseline).
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
            .expect("a 32-byte allocation executes");
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
            origin: None,
        });
        module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

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
            origin: None,
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
            origin: None,
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
        module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::U8, Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

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

    #[test]
    fn declared_struct_layout_enforces_the_exact_transparent_carrier() {
        let rejected = [
            sdef_with_layout(
                0,
                "ShiftedCarrier",
                vec![fdef("value", Ty::U64, Some(8))],
                Some(16),
                Some(8),
                crate::ty::StructRepr::Transparent,
            ),
            sdef_with_layout(
                0,
                "TwoCarriers",
                vec![
                    fdef("left", Ty::U32, Some(0)),
                    fdef("right", Ty::U32, Some(4)),
                ],
                Some(8),
                Some(4),
                crate::ty::StructRepr::Transparent,
            ),
        ];
        for def in rejected {
            let mut module = Module::new("bad-transparent");
            module.add_struct(def);
            let err = match Interpreter::with_module(&module)
                .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
            {
                Ok(_) => panic!("an incoherent transparent descriptor must fail closed"),
                Err(err) => err,
            };
            assert!(err.to_string().contains("repr(transparent)"), "{err}");
        }

        let mut module = Module::new("overaligned-transparent-zst");
        module.add_struct(sdef_with_layout(
            0,
            "Marker",
            vec![],
            Some(0),
            Some(8),
            crate::ty::StructRepr::Rust,
        ));
        module.add_struct(sdef_with_layout(
            1,
            "Wrapper",
            vec![
                fdef(
                    "marker",
                    Ty::Struct(crate::value::StructId::new(0)),
                    Some(0),
                ),
                fdef("unit", Ty::Unit, None),
            ],
            Some(0),
            Some(8),
            crate::ty::StructRepr::Transparent,
        ));
        let layout = Interpreter::with_module(&module)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(1)), b(0))
            .expect("an over-aligned ZST can be the sole transparent carrier");
        assert_eq!(layout.size, 0);
        assert_eq!(layout.align, 8);
    }

    /// Trust (wave-SG): **THE CLAMP IS THE MODULUS, so it is re-validated too.**
    ///
    /// The control above proves a `packed(1)` layout is admitted. That control is
    /// exactly what makes an UNVALIDATED clamp dangerous rather than merely odd:
    /// every field-alignment check in `declared_struct_layout` is taken modulo
    /// `min(natural, N)`, so a non-power-of-two `N` does not fail — it silently
    /// redefines what "aligned" means.
    ///
    /// `Packed(3)` is the case the class is named for: a `u64`'s effective
    /// alignment becomes `min(8, 3) = 3`, and the descriptor that places it at byte
    /// **3** is accepted by the one component in this tree that executes bytes.
    /// `Packed(0)` fails quieter and wider — `min(_, 0) = 0` makes
    /// `is_multiple_of(0)` true only at offset 0, and makes `field_align > align`
    /// unfalsifiable, so the over-alignment check stops existing altogether.
    ///
    /// `validate_module` refuses these (`PackedReprInvalidAlign`), but a module
    /// reaches the interpreter through `binary::deserialize_module` and through the
    /// text parser, and neither runs it — which is the same reason this whole path
    /// re-validates ("modules may be interpreted without validation").
    ///
    /// ACCEPT CONTROLS on every valid clamp, so a rule that refused all packing
    /// would fail here rather than pass the refusals.
    #[test]
    fn declared_struct_layout_refuses_a_packed_clamp_that_is_not_a_power_of_two() {
        for bad in [0u32, 3, 6, 7, 100] {
            let mut module = Module::new("declared-packed-bad");
            module.add_struct(sdef_with_layout(
                0,
                "BadPacked",
                vec![fdef("a", Ty::U8, Some(0)), fdef("b", Ty::U64, Some(3))],
                Some(11),
                Some(1),
                crate::ty::StructRepr::Packed(bad),
            ));
            let err = match Interpreter::with_module(&module)
                .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
            {
                Ok(layout) => panic!(
                    "packed({bad}): expected a refusal, got size {} align {} with field 1 at {}",
                    layout.size, layout.align, layout.field_offsets[1].0
                ),
                Err(err) => err.to_string(),
            };
            assert!(
                err.contains("must be a non-zero power of two"),
                "packed({bad}): refusal did not name the clamp: {err}"
            );
        }
        // ACCEPT CONTROLS: every VALID clamp still lays out, including the one that
        // makes byte 3 legal. The refusal above is about the clamp, not about packing.
        for good in [1u32, 2, 4, 8] {
            let mut module = Module::new("declared-packed-good");
            module.add_struct(sdef_with_layout(
                0,
                "GoodPacked",
                vec![fdef("a", Ty::U8, Some(0)), fdef("b", Ty::U8, Some(1))],
                Some(2),
                Some(1),
                crate::ty::StructRepr::Packed(good),
            ));
            Interpreter::with_module(&module)
                .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
                .unwrap_or_else(|e| panic!("packed({good}) must lay out: {e}"));
        }
    }

    /// Trust (wave-SG): the DISCRIMINATING half of the test above — the EXACT
    /// descriptor an unvalidated clamp admitted, derived rather than guessed.
    ///
    /// Two checks stand between a `u64` and byte 3, and the exploit has to clear
    /// BOTH: `offset.is_multiple_of(field_align)` and `field_align > align`. Under
    /// `packed(3)` the `u64`'s effective alignment is `min(8, 3) = 3`, so byte 3 is
    /// "aligned" — and the second check then only needs the struct's own declared
    /// `align` to be at least 3. At `align: 1` the descriptor is refused as
    /// over-aligned, which is why a naive probe reports a PASS that proves nothing;
    /// at `align: 4` — a perfectly ordinary power of two — nothing refuses it.
    ///
    /// MUTATION-PROVED against exactly this: with the clamp validation deleted, the
    /// interpreter accepts it and places field 1 at byte 3.
    #[test]
    fn a_packed_three_descriptor_admits_a_u64_at_byte_three_without_the_clamp_check() {
        let exploit = || {
            let mut module = Module::new("packed-three");
            module.add_struct(sdef_with_layout(
                0,
                "PackedThree",
                vec![fdef("a", Ty::U8, Some(0)), fdef("b", Ty::U64, Some(3))],
                Some(12),
                Some(4),
                crate::ty::StructRepr::Packed(3),
            ));
            module
        };
        let module = exploit();
        let err = match Interpreter::with_module(&module)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
        {
            Ok(layout) => panic!(
                "packed(3) must be refused before it can call byte 3 aligned; got field 1 at {}",
                layout.field_offsets[1].0
            ),
            Err(err) => err.to_string(),
        };
        assert!(err.contains("packed(3)"), "{err}");

        // DISCRIMINATION 1: the refusal is about the CLAMP, not about byte 3. The
        // same placement under the valid clamp `packed(1)` is legal Rust and lays out.
        let mut ok = Module::new("packed-one");
        ok.add_struct(sdef_with_layout(
            0,
            "PackedOne",
            vec![fdef("a", Ty::U8, Some(0)), fdef("b", Ty::U64, Some(3))],
            Some(11),
            Some(1),
            crate::ty::StructRepr::Packed(1),
        ));
        let layout = Interpreter::with_module(&ok)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
            .expect("packed(1) admits byte 3");
        assert_eq!(layout.field_offsets[1].0, 3);

        // DISCRIMINATION 2: `packed(0)` is the quieter half. `min(_, 0) = 0` makes
        // `is_multiple_of(0)` true at offset 0 and makes `field_align > align`
        // unfalsifiable, so a single over-aligned field sails through with the
        // over-alignment check silently disabled. A struct declaring align 1 while
        // storing a `u64` is exactly what that check exists to refuse.
        let mut zero = Module::new("packed-zero");
        zero.add_struct(sdef_with_layout(
            0,
            "PackedZero",
            vec![fdef("b", Ty::U64, Some(0))],
            Some(8),
            Some(1),
            crate::ty::StructRepr::Packed(0),
        ));
        let err = match Interpreter::with_module(&zero)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
        {
            Ok(layout) => panic!(
                "packed(0) must be refused; got align {} with field 0 at {}",
                layout.align, layout.field_offsets[0].0
            ),
            Err(err) => err.to_string(),
        };
        assert!(err.contains("packed(0)"), "{err}");
    }

    /// `repr(packed(N))` clamps the aggregate's alignment as well as its fields.
    /// The old reader checked only the field-side clamp, so a descriptor could
    /// claim `packed(1)` while retaining alignment 8 and be handed to consumers as
    /// though rustc had emitted it.
    #[test]
    fn declared_struct_layout_refuses_alignment_above_the_packed_clamp() {
        let mut module = Module::new("packed-aggregate-align");
        module.add_struct(sdef_with_layout(
            0,
            "PackedButOveraligned",
            vec![fdef("value", Ty::U64, Some(0))],
            Some(8),
            Some(8),
            crate::ty::StructRepr::Packed(1),
        ));
        let err = match Interpreter::with_module(&module)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
        {
            Ok(_) => panic!("packed(1) cannot declare aggregate alignment 8"),
            Err(err) => err.to_string(),
        };
        assert!(err.contains("above its repr(packed(1)) clamp"), "{err}");

        let mut control = Module::new("packed-aggregate-align-control");
        control.add_struct(sdef_with_layout(
            0,
            "PackedOne",
            vec![fdef("value", Ty::U64, Some(0))],
            Some(8),
            Some(1),
            crate::ty::StructRepr::Packed(1),
        ));
        Interpreter::with_module(&control)
            .struct_layout(&Ty::Struct(crate::value::StructId::new(0)), b(0))
            .expect("the same packed layout at aggregate alignment 1 is coherent");
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
            origin: None,
        });
        module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns,
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
            origin: None,
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
            origin: None,
        });
        module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32, Ty::I8],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
        module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns,
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
            frames: BTreeSet::new(),
            next_frame_id: 0,
            steps: 0,
            remaining_fuel: u64::MAX,
            host: HostState::new(),
            host_calls: 0,
            drop_glue: None,
            unwind: UnwindState::default(),
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
            frames: BTreeSet::new(),
            next_frame_id: 0,
            steps: 0,
            remaining_fuel: u64::MAX,
            host: HostState::new(),
            host_calls: 0,
            drop_glue: None,
            unwind: UnwindState::default(),
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
        module
            .add_func_type(FuncTy {
                params: vec![enum_ty.clone()],
                returns: vec![Ty::I16],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

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
        module
            .add_func_type(FuncTy {
                params: vec![Ty::Enum(EnumId::new(0))],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "takes_a", crate::FuncTyId::new(0), b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Enum(EnumId::new(0))));
        block.body.push(void(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

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
        module
            .add_func_type(FuncTy {
                params: vec![enum_ty.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
        module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::U8, Ty::I8],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
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
        let i32_id = module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        let seq_ty = Ty::Sequence(i32_id);
        let loop_ty = module
            .add_func_type(FuncTy {
                params: vec![seq_ty.clone()],
                returns: vec![seq_ty.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let elem_fn_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::RefMut(Box::new(Ty::I32))],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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

        module
            .try_add_function(incr_all)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(incr_elem)
            .expect("Module::try_add_function: test fixture");
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

    /// A sequence is a persistent rope, like an array (2026-09-30): a
    /// 2^40-element uniform sequence argument costs O(1); `InsertElement`
    /// copies one root-to-leaf path and leaves its input unchanged;
    /// `ExtractElement` reads either version; `SeqMapAddK` maps each stored
    /// value once. (As a `Vec`, this argument could not exist, and every
    /// insert copied the whole sequence.)
    ///
    /// The same program runs first at two small lengths, where the result's
    /// STORED values are counted: three (a run of ones, the inserted ten,
    /// a run of ones) whatever the length. An insert or a map that
    /// materialized element by element would store thousands there and fail
    /// in milliseconds, before the 2^40 run could grow host memory.
    #[test]
    fn a_sequence_insert_is_persistent_and_never_copies() {
        let run = |len: u64, at: i128| {
            let mut module = Module::new("seq-persistent");
            let i32_id = module
                .add_type(Ty::I32)
                .expect("Module::add_type: test fixture");
            let seq_ty = Ty::Sequence(i32_id);
            let fn_ty = module
                .add_func_type(FuncTy {
                    abi: None,
                    params: vec![seq_ty.clone()],
                    returns: vec![Ty::I32, Ty::I32, seq_ty.clone()],
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut f = Function::new(FuncId::new(0), "f", fn_ty, b(0));
            let mut entry = Block::new(b(0)).with_param(v(0), seq_ty.clone());
            entry.body.push(result(
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(at),
                },
                v(1),
            ));
            entry.body.push(result(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(9),
                },
                v(2),
            ));
            entry.body.push(result(
                Inst::InsertElement {
                    ty: seq_ty.clone(),
                    array: v(0),
                    index: v(1),
                    value: v(2),
                },
                v(3),
            ));
            entry.body.push(result(
                Inst::ExtractElement {
                    ty: Ty::I32,
                    array: v(3),
                    index: v(1),
                },
                v(4),
            ));
            entry.body.push(result(
                Inst::ExtractElement {
                    ty: Ty::I32,
                    array: v(0),
                    index: v(1),
                },
                v(5),
            ));
            entry.body.push(result(
                Inst::SeqMapAddK {
                    ty: seq_ty.clone(),
                    seq: v(3),
                    k: 1,
                },
                v(6),
            ));
            entry.body.push(void(Inst::Return {
                values: vec![v(4), v(5), v(6)],
            }));
            f.blocks.push(entry);
            module
                .try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            let zero = InterpretValue::int(Ty::I32, 0).expect("i32");
            let zeros = InterpretValue {
                ty: seq_ty,
                kind: InterpretValueKind::Sequence(ArrayValue::splat(zero, len)),
            };
            let outcome = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [zeros])
                .expect("a persistent insert, two reads and a map");
            assert_eq!(int_signed(&outcome.returns[0]), 9);
            assert_eq!(int_signed(&outcome.returns[1]), 0, "the input is unchanged");
            let InterpretValueKind::Sequence(mapped) = &outcome.returns[2].kind else {
                panic!("seq_map_add_k returns a sequence: {:?}", outcome.returns[2]);
            };
            assert_eq!(mapped.len(), len);
            assert_eq!(mapped.get(at as u64).map(int_signed), Some(10));
            assert_eq!(mapped.get(0).map(int_signed), Some(1));
            assert_eq!(mapped.get(len - 1).map(int_signed), Some(1));
            assert!(mapped.get(len).is_none());
            let mut stored = 0usize;
            let _ = mapped.try_for_each_stored(|_| {
                stored += 1;
                core::ops::ControlFlow::<()>::Continue(())
            });
            stored
        };
        assert_eq!(run(4096, 1234), 3);
        assert_eq!(run(1 << 16, 40_000), 3);
        assert_eq!(run(1 << 40, 123_456_789_012), 3);
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
            kind: InterpretValueKind::Sequence(
                vec![
                    InterpretValue::int(Ty::I32, 1).expect("i32 element"),
                    InterpretValue::bool(true),
                ]
                .into(),
            ),
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
        let i32_id = module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        let seq_ty = Ty::Sequence(i32_id);
        let loop_ty = module
            .add_func_type(FuncTy {
                params: vec![seq_ty.clone()],
                returns: vec![seq_ty.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        // By-value fn(i32) -> i32: NOT the &mut element form.
        let by_value_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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

        module
            .try_add_function(incr_all)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(identity)
            .expect("Module::try_add_function: test fixture");

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
        let i32_loop_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::Sequence(TyId::new(0))],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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

    #[test]
    fn a_phantom_constant_at_non_unit_is_rejected_before_any_use() {
        use crate::ty::SetRepr;
        for ty in [
            Ty::I8,
            Ty::I128,
            Ty::U128,
            Ty::Bool,
            Ty::F32,
            Ty::F64,
            Ty::Ptr,
            Ty::FatPtr(FatPtrKind::Str),
            Ty::Ref(Box::new(Ty::U8)),
            Ty::Tuple(vec![]),
            Ty::Array(TyId::new(0), 0),
            Ty::Sequence(TyId::new(0)),
            Ty::Set(TyId::new(0), SetRepr::Boxed),
            Ty::Never,
        ] {
            assert!(!Constant::PhantomData.shape_matches_ty(&ty));
            let mut function =
                Function::new(FuncId::new(0), "bad_phantom", crate::FuncTyId::new(0), b(0));
            let mut block = Block::new(b(0));
            block.body.push(result(
                Inst::Const {
                    ty: ty.clone(),
                    value: Constant::PhantomData,
                },
                v(0),
            ));
            block.body.push(void(Inst::Return { values: vec![] }));
            function.blocks.push(block);
            let module = module_with_function(function, vec![]);
            let error = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .expect_err("an unused constant must still obey its declared type");
            assert_eq!(
                error.code,
                InterpretErrorCode::TypeError,
                "{ty:?}: {error:?}"
            );
        }
    }

    #[test]
    fn vector_constants_reject_unadmitted_scalar_lanes_before_any_use() {
        for elem in [Ty::I128, Ty::U128, Ty::Isize, Ty::Usize, Ty::Char, Ty::Ptr] {
            let mut function = Function::new(
                FuncId::new(0),
                "bad_vector_lane",
                crate::FuncTyId::new(0),
                b(0),
            );
            let mut block = Block::new(b(0));
            block.body.push(result(
                Inst::Const {
                    ty: Ty::Vector(Box::new(elem.clone()), 2),
                    value: Constant::Vector(vec![Constant::Int(0), Constant::Int(0)]),
                },
                v(0),
            ));
            block.body.push(void(Inst::Return { values: vec![] }));
            function.blocks.push(block);
            let module = module_with_function(function, vec![]);
            let error = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .expect_err("invalid vector lane type must not create an unused value");
            assert_eq!(
                error.code,
                InterpretErrorCode::TypeError,
                "{elem:?}: {error:?}"
            );
        }
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

    /// Trust (crystal D3): the WEAK compare-exchange is refused, never stepped as strong, and
    /// the refusal does not depend on whether the comparison would succeed. The STRONG one
    /// over the same state steps to `(old, true)` and stores, exactly as before.
    #[test]
    fn weak_cmpxchg_is_refused_and_strong_cmpxchg_steps() {
        let build = |weak: bool| {
            let mut function = Function::new(FuncId::new(0), "cas", crate::FuncTyId::new(0), b(0));
            let mut block = Block::new(b(0));
            block.body.push(result(
                Inst::Alloca {
                    ty: Ty::I8,
                    count: None,
                    align: None,
                },
                v(0),
            ));
            block.body.push(result(
                Inst::Const {
                    ty: Ty::I8,
                    value: Constant::Int(7),
                },
                v(1),
            ));
            block.body.push(void(Inst::Store {
                ty: Ty::I8,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }));
            block.body.push(result(
                Inst::Const {
                    ty: Ty::I8,
                    value: Constant::Int(9),
                },
                v(2),
            ));
            block.body.push(
                InstrNode::new(Inst::CmpXchg {
                    ty: Ty::I8,
                    ptr: v(0),
                    expected: v(1),
                    desired: v(2),
                    success: crate::inst::Ordering::SeqCst,
                    failure: crate::inst::Ordering::SeqCst,
                    weak,
                })
                .with_result(v(3))
                .with_result(v(4)),
            );
            block.body.push(void(Inst::Return { values: vec![v(4)] }));
            function.blocks.push(block);
            module_with_function(function, vec![Ty::Bool])
        };

        let strong = build(false);
        let outcome = Interpreter::with_module(&strong)
            .execute_func(FuncId::new(0), [])
            .expect("a strong compare-exchange steps");
        assert_eq!(
            outcome.returns[0].as_bool(),
            Some(true),
            "expected == current: it succeeds"
        );

        let weak = build(true);
        let err = Interpreter::with_module(&weak)
            .execute_func(FuncId::new(0), [])
            .expect_err("a weak compare-exchange must be refused, not stepped as strong");
        assert_eq!(err.code, InterpretErrorCode::TypeError);
        assert!(
            err.message.contains("Inst::CmpXchg weak"),
            "{}",
            err.message
        );
    }
}

#[cfg(test)]
#[path = "interpret/single_inhabited_tests.rs"]
mod single_inhabited_tests;
