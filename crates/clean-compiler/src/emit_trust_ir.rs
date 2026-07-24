// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Experimental L5IR -> trust-ir backend (feature `trust-ir-backend`).
//!
//! # Status and trust claims
//!
//! This module is an **experimental, unverified, non-TCB** backend. It lowers
//! the same `&[IRDecl]` slice that [`crate::emit_c::emit_c`] consumes into a
//! `trust_ir::Module` built with `trust-ir-build`'s `ModuleBuilder` /
//! `FunctionBuilder`. Its only guarantee is that, when it returns `Ok`, the
//! resulting module is **syntactically valid** trust-ir: every finalized
//! module carries a pinned [`trust_ir::TargetInfo`] and must pass
//! `trust_ir_build::validate_module` with zero errors before it is returned
//! (see [`finalize_module`]); a module that fails is rejected fail-closed as
//! [`TrustIrError::Invalid`] rather than handed to the caller. `ExternCalls`
//! (the handoff mode) additionally **self-gates on trust-ir's versioned
//! lowering-target conformance subset** (subset v1, the ratified producer
//! contract of `docs/lowering-target-subset.md`) — an out-of-subset construct
//! is rejected as [`TrustIrError::OutOfLoweringSubset`], never handed off —
//! and callers may opt in to the stricter core bridge gate
//! (`Module::check_conformance_subset`) via
//! [`TrustIrConfig::enforce_handoff_subset`]. **No semantics-preservation
//! property is claimed**: this lowering is NOT part of the trusted computing
//! base, does NOT carry a soundness proof, and must not be relied on for
//! verification. It exists to exercise the trust-ir surface and to make the
//! "easy 80%" of L5IR expressible while clearly fencing off the parts that are
//! still speculative.
//!
//! # What is lowered
//!
//! - Scalar `IRType`s map to `Ty::{U8,U16,U32,U64,Bool,F32,F64}`; `USize` maps
//!   to `Ty::U64`; object/boxed types map to the thin `Ty::Ptr`.
//! - `IRExpr::Lit` -> `iconst`/`fconst`/`bool_const`.
//! - `IRExpr::Apply` -> `call` (functions are pre-declared so calls can
//!   forward-reference by `FuncId`). Call-site arguments align POSITIONALLY
//!   with the callee's lowered parameter list (C2): erased args are
//!   materialized (boxed unit / null), never dropped, and args beyond the
//!   parameter list are over-application, lowered through the runtime
//!   `clean_apply_N` chain on the saturated call's result — see
//!   [`emit_apply_user`]. In `ExternCalls` mode, an `Apply` target *absent*
//!   from the emitted slice (a dependency the clean-cli #14 boundary
//!   dropped to extern) is forward-declared as a bodyless `Linkage::External`
//!   import with the mangled symbol and the boxed all-Ptr signature (`emit_c`
//!   parity, resolved at link time) — fail-closed via
//!   [`declare_extern_fallbacks`]: an unfaithfully-typeable callee keeps the
//!   [`TrustIrError::UndefinedFunction`] refusal.
//! - `IRBody::VDecl`/`Ret`/`Unreachable` -> straight-line SSA + terminator.
//! - `IRBody::Case` -> `switch` over the scrutinee's tag when the scrutinee is
//!   a boxed object; an UNBOXED scalar scrutinee already *is* its own tag
//!   (`emit_c` parity: `CEmitter::is_unboxed_scalar`), so a `Bool` scrutinee
//!   lowers to a `CondBr` keyed on ctor tag (`true` = 1 -> then, `false` = 0
//!   -> else) and an integer scalar scrutinee to a `switch` on the value
//!   itself — never a `clean_obj_tag` read (C2 scalar-representation
//!   correctness; the tag read on a scalar was the miscompile class trust-ir's
//!   validator refused fail-closed).
//! - Join points (`JDecl`/`Jmp`) -> trust-ir blocks with block parameters,
//!   reached via `br` with arguments.
//! - Newtype-style projections OUT OF an unboxed scalar carrier (`Proj` /
//!   `SProj` whose base variable is itself a scalar, e.g. `Char.val` out of a
//!   `Char` lowered to `U32`, or `UInt8.toBitVec` out of a `U8`): the carrier
//!   *is* the single runtime field, so a same-width projection is the
//!   identity, and an object-typed projection re-boxes the scalar with the
//!   runtime's tagged `clean_box` convention (`ExternCalls`) — never a
//!   `clean_ctor_get*` call on a non-pointer (C2).
//!
//! # Native ARC (P1)
//!
//! Perceus RC ops do NOT ride the mode split below: `inc` / `dec` /
//! `IsShared` lower to trust-ir's native ARC instructions — `Retain` /
//! `Release` / `IsUnique` — in BOTH modes. Design (2026-07 "Native ARC",
//! Clean half):
//!
//! * The ops are core trust-ir (lowering-target subset v1 members), verified
//!   by the trust-ir Lean ARC model (`semRetain`/`semRelease`), so the IR
//!   consumers (validator, subset gate, interpreter, verifiers) see real RC
//!   semantics instead of opaque calls. `inc x n` unrolls to n `Retain`s
//!   (each is the +1 step); `IsShared` is `!IsUnique`, negated with a Bool
//!   `select` — **polarity**: `IsUnique` == `clean_is_exclusive`
//!   (refcount == 1), the exact opposite of `IsShared`.
//! * Machine code: trust-cg lowers ARC ops to calls of the RC runtime the
//!   module itself declares. `ExternCalls` modules therefore keep the
//!   bodyless-external RC **triple** (`clean_inc`/`clean_dec`/
//!   `clean_is_exclusive`) declared as provenance ([`RuntimeAbi`]) even
//!   though the emitter never calls it directly; ARC ops carry no origin
//!   field, so the declared triple is the routing contract (the analogue of
//!   `HeapAlloc`'s `AllocOrigin::CleanHeap`).
//! * Allocation stays `clean_alloc_ctor`: an RC cell needs its header + ctor
//!   metadata installed, which a bare `HeapAlloc` cannot express — trust-cg
//!   fails closed on `AllocOrigin::CleanHeap` for exactly this reason.
//!   `obj.reuse`/`obj.reset` likewise stay runtime calls (in-place reuse has
//!   no native trust-ir surface).
//!
//! # Two runtime-lowering modes
//!
//! [`RuntimeLowering`] selects how Clean's remaining managed-runtime ops
//! (reset/reuse, box/unbox, ctor allocation, tag/field reads, closures,
//! string literals) are lowered:
//!
//! - **`Dialect`** emits them as opaque `clean`-dialect `DialectInst` nodes via
//!   [`FunctionBuilder::dialect_op`]. These round-trip through trust-ir
//!   serialization without the core needing their semantics, but trust-cg
//!   cannot lower the `clean` dialect, so the module is not compilable to
//!   machine code. Closures (`PartialApply`/`ClosureApply`) are *rejected* with
//!   [`TrustIrError::Unsupported`] in this mode rather than guessed at, since
//!   there is no runtime to model their ABI.
//! - **`ExternCalls`** lowers every managed op to an `Inst::Call` targeting the
//!   same bodyless-`External` C runtime symbol `emit_c` calls
//!   (`clean_alloc_ctor`, `clean_alloc_closure`/`clean_apply_N`,
//!   `clean_mk_string`, …). trust-cg compiles these to undefined externals
//!   resolved at link time against the Clean runtime — real, compilable native
//!   code. Closures run via the closure ABI; string literals are emitted as
//!   read-only byte globals (see [`build_string_globals`]) and built with
//!   `clean_mk_string`. The crate's e2e tests link the result against the Clean
//!   runtime, run it, and a differential test asserts the exit code matches
//!   `emit_c` across managed/closure/string programs.
//!
//! # Source provenance
//!
//! When [`TrustIrConfig::source_file`] is set, the path is interned in the
//! module's debug-info file table (`Module::files`) and every emitted
//! instruction carries a file-granular [`SourceSpan`] (`line`/`col` are `0`,
//! i.e. "somewhere in this file" — the DWARF "no line" convention). This is
//! the honest maximum today: positions die at the surface -> kernel
//! elaboration boundary, and every downstream form (kernel `Expr`, L5CNF,
//! L5IR) is span-less, so finer granularity first requires threading spans
//! through elaboration. Missing provenance degrades cleanly: `None` (the
//! default) emits a span-less module exactly as before.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::emit_trust_ir_runtime::RuntimeAbi;
use crate::ir::{
    CtorInfo, FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::ir_checker::IRError;
use thiserror::Error;
use trust_ir::bridge::SubsetViolation;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{BinOp, CastOp, ICmpOp};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, FuncTyId, SourceSpan, ValueId};
use trust_ir::{Endianness, Module, TargetInfo};
use trust_ir_build::{validate_module, FunctionBuilder, ModuleBuilder, ValidationError};
use trust_ir_conformance::subset::{module_subset_violations, SUBSET_VERSION};

/// Errors surfaced by the experimental trust-ir backend.
///
/// Wraps [`IRError`] from the shared IR validity checker (so existing
/// diagnostics flow through unchanged) and adds an `Unsupported` variant for
/// L5IR constructs this phase-1 lowering deliberately does not model.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum TrustIrError {
    /// An L5IR construct is not supported by this experimental backend.
    #[error("trust-ir backend: unsupported construct: {0}")]
    Unsupported(String),
    /// A referenced function name was not declared in the input slice.
    #[error("trust-ir backend: undefined function: {0}")]
    UndefinedFunction(String),
    /// A referenced join point was not in scope where it was jumped to.
    #[error("trust-ir backend: undefined join point: jp{}", _0.0)]
    UndefinedJoinPoint(JoinPointId),
    /// A referenced variable had no SSA value bound where it was used.
    #[error("trust-ir backend: undefined variable: x{}", _0.0)]
    UndefinedVariable(VarId),
    /// An erased argument reached a position that requires a runtime value.
    #[error("trust-ir backend: erased argument in value position")]
    ErasedInValuePosition,
    /// The shared IR validity checker rejected the input.
    #[error(transparent)]
    Ir(#[from] IRError),
    /// The finalized module failed `trust_ir_build::validate_module`. The
    /// backend is fail-closed: a module that does not validate is never
    /// returned or serialized, and the full error list rides along for
    /// structured consumption (not just the rendered message).
    #[error(
        "trust-ir backend: emitted module failed validate_module ({} error(s)): {}",
        _0.len(),
        display_list(_0)
    )]
    Invalid(Vec<ValidationError>),
    /// The finalized module uses constructs outside trust-ir's pinned bridge
    /// conformance subset (`Module::check_conformance_subset`), and the config
    /// opted in to enforcing that handoff gate
    /// ([`TrustIrConfig::enforce_handoff_subset`]).
    #[error(
        "trust-ir backend: emitted module is outside the trust-ir conformance subset \
         ({} violation(s)): {}",
        _0.len(),
        display_list(_0)
    )]
    OutOfSubset(Vec<SubsetViolation>),
    /// The finalized module uses constructs outside trust-ir's *versioned*
    /// lowering-target conformance subset
    /// (`trust_ir_conformance::subset::module_subset_violations` — the
    /// machine-readable producer contract of trust-ir's
    /// `docs/lowering-target-subset.md`). `ExternCalls`, the handoff mode, is
    /// gated on it unconditionally at finalization (see [`finalize_module`]);
    /// `Dialect` mode (out-of-subset by design) is checked only under
    /// [`TrustIrConfig::enforce_handoff_subset`].
    #[error(
        "trust-ir backend: emitted module is outside trust-ir lowering-target subset \
         v{version} ({} violation(s)): {}",
        violations.len(),
        display_list(violations)
    )]
    OutOfLoweringSubset {
        /// The `trust_ir_conformance::subset::SUBSET_VERSION` checked against.
        version: u32,
        /// One human-readable line per out-of-subset construct.
        violations: Vec<String>,
    },
    /// The backend translation-validation minter
    /// ([`TrustIrConfig::certify_translation`], [`crate::emit_trust_ir_tv`])
    /// found an in-fragment decl whose emitted function the kernel REFUSED to
    /// equate with its source definition — a detected miscompile (or a
    /// denotation-map bug). Fail-closed: the compile is aborted rather than
    /// shipping an artifact that provably does not denote its source.
    #[error(
        "trust-ir backend: translation validation REFUSED for {} decl(s): {}",
        _0.len(),
        _0.iter().map(|(n, r)| format!("{n}: {r}")).collect::<Vec<_>>().join("; ")
    )]
    TranslationRefused(Vec<(String, String)>),
}

/// Join a diagnostic list into one `; `-separated string (a thiserror
/// `#[error]` payload must be a single formattable expression).
fn display_list<T: std::fmt::Display>(items: &[T]) -> String {
    items
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("; ")
}

/// How managed-runtime ops (RC, ctor, projections, …) are lowered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeLowering {
    /// Emit opaque `clean.*` `DialectInst` nodes. Valid, round-trippable
    /// trust-ir, but trust-cg cannot lower the `clean` dialect, so the module
    /// is not compilable to machine code.
    Dialect,
    /// Lower each managed-runtime op to an `Inst::Call` targeting the matching
    /// bodyless-`External` Clean-runtime symbol (`clean_alloc_ctor`,
    /// `clean_alloc_closure`/`clean_apply_N`, `clean_mk_string`, …; Perceus RC
    /// ops are native ARC instructions instead — see "Native ARC"). trust-cg
    /// compiles these to undefined externals resolved at link time against the
    /// Clean runtime — i.e. real, compilable, runnable native code. RC, box/unbox,
    /// ctor/proj/tag, sset, closures, and string literals are all modeled; the
    /// crate's e2e + differential tests link and run the result against `emit_c`.
    ///
    /// This mode is **dialect-free by contract** (trust-ir lowering-target
    /// subset v1 producer notes): an op the runtime ABI cannot express (e.g.
    /// a non-scalar `sproj`/`sset`) is refused fail-closed as
    /// [`TrustIrError::Unsupported`] instead of silently degrading to an
    /// out-of-subset `clean.*` `DialectOp`.
    ExternCalls,
}

/// Configuration for the experimental trust-ir backend.
#[derive(Debug, Clone)]
pub struct TrustIrConfig {
    /// Module name embedded in the produced `trust_ir::Module`.
    pub module_name: String,
    /// When a managed-runtime op falls back to the `clean` dialect, whether the
    /// dialect node is allowed (`true`, default) or rejected as
    /// [`TrustIrError::Unsupported`] (`false`, for testing the pure-core subset).
    pub use_clean_dialect: bool,
    /// How managed-runtime ops are lowered (default [`RuntimeLowering::Dialect`]).
    pub runtime_lowering: RuntimeLowering,
    /// Target identity pinned onto the emitted module (`Module::target_info`).
    ///
    /// trust-ir's ABI pinning requires `target_info` on any module with a
    /// bodyless external declaration (`ValidationError::TargetInfoRequired`) —
    /// which every `ExternCalls` module has, via the Clean-runtime imports.
    /// This backend is host-targeted by construction anyway (`USize` lowers to
    /// `U64`, and the emitted object links against the host Clean runtime), so
    /// the default is the host ([`host_target_info`]). `None` leaves the module
    /// target-independent, which the validation gate rejects fail-closed in
    /// `ExternCalls` mode.
    pub target_info: Option<TargetInfo>,
    /// Whether finalization also subset-gates `Dialect`-mode modules and runs
    /// the stricter core bridge gate, `Module::check_conformance_subset`.
    ///
    /// The 2026-07-04 trust-ir promotion audit ratified lowering-target
    /// subset v1; the 2026-07-21 re-audit tracked trust-ir's bump to v2
    /// (a strictly additive fat-pointer-certification expansion): `clean.*`
    /// ops stay excluded either way, and `Dialect` mode is a
    /// debug/round-trip surface *expected* to fail the
    /// subset. Since that ratification, `ExternCalls` — the handoff mode —
    /// self-gates on the versioned subset unconditionally at finalization
    /// (see [`finalize_module`]), so handoff paths no longer need this flag.
    /// Turning it on additionally (a) runs the same versioned check on
    /// `Dialect`-mode modules (which fail it by design, as
    /// [`TrustIrError::OutOfLoweringSubset`]) and (b) runs the stricter core
    /// bridge gate, which rejects e.g. every `DialectOp` (even trust-ir's
    /// allowlisted `vector.*`) and `PtrToPtr` casts as
    /// [`TrustIrError::OutOfSubset`]. Default `false`.
    pub enforce_handoff_subset: bool,
    /// Source provenance: the path of the Clean source file the lowered decls
    /// came from (default `None`). When set, the path is interned in the
    /// module's debug-info file table and every emitted instruction carries a
    /// file-granular span — see the module-level "Source provenance" docs for
    /// why file granularity is the current honest maximum.
    pub source_file: Option<String>,
    /// Whether the pipeline mints the backend TRANSLATION-VALIDATION
    /// certificate after finalization (see [`crate::emit_trust_ir_tv`]):
    /// for every in-fragment decl the kernel decides `⟦emitted⟧ = ⟦source⟧`
    /// and a `Certified` `TranslationValidation` obligation + `CleanCic`
    /// certificate is attached; a kernel REFUSAL (a detected miscompile)
    /// fails the compile as [`TrustIrError::TranslationRefused`];
    /// out-of-fragment decls are silently skipped. Default `true` since
    /// 2026-07-21 ("certified by default where fragments allow"): the
    /// out-of-fragment skip is a cheap structural walk (the full 891-root
    /// trust-cg census mints in <3 ms total), so certification-on is free
    /// where the fragment is empty and automatic where it is not; each
    /// decl that IS in-fragment costs a fresh prelude kernel environment
    /// + a def-eq judgment at mint time.
    /// Only honored by the pipeline entry points that have the kernel
    /// `Environment` in scope (`compile_lcnf_to_trust_ir`); the bare
    /// `emit_trust_ir*` entry points have no source-of-truth to certify
    /// against and ignore it.
    pub certify_translation: bool,
}

impl Default for TrustIrConfig {
    fn default() -> Self {
        Self {
            module_name: "clean_module".to_string(),
            use_clean_dialect: true,
            runtime_lowering: RuntimeLowering::Dialect,
            target_info: Some(host_target_info()),
            enforce_handoff_subset: false,
            source_file: None,
            certify_translation: true,
        }
    }
}

/// The host's [`TargetInfo`], with the canonical triple spelling for the
/// platforms Clean supports (64-bit aarch64/x86_64 on macOS or Linux — the
/// same set `host_trust_cg_target` accepts CLI-side). The pointer size is the
/// compiler host's, matching the backend's `USize -> U64` lowering on every
/// supported host.
#[must_use]
pub fn host_target_info() -> TargetInfo {
    let arch = std::env::consts::ARCH;
    let triple = match std::env::consts::OS {
        "macos" => format!("{arch}-apple-darwin"),
        "linux" => format!("{arch}-unknown-linux-gnu"),
        other => format!("{arch}-unknown-{other}"),
    };
    TargetInfo {
        triple,
        pointer_size: core::mem::size_of::<usize>() as u32,
        endianness: if cfg!(target_endian = "big") {
            Endianness::Big
        } else {
            Endianness::Little
        },
        abi: None,
        struct_passing: Default::default(),
    }
}

/// Serialize a [`Module`] into the `.tmbc` container the `trust-cg` CLI
/// consumes: the magic `b"tMBC"`, a little-endian `u32` version (`1`), then the
/// binary-serialized module. Lets callers (e.g. the `clean compile --emit obj`
/// path) produce a trust-cg input without depending on `trust_ir` directly.
#[must_use]
pub fn serialize_tmbc(module: &Module) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(8);
    bytes.extend_from_slice(b"tMBC");
    bytes.extend_from_slice(&1u32.to_le_bytes());
    bytes.extend_from_slice(&trust_ir::binary::serialize_module(module));
    bytes
}

/// Lower a slice of L5IR declarations into a `trust_ir::Module`.
///
/// Two conceptual passes: first every function name is registered in
/// declaration order so a deterministic [`FuncId`] is known for each (trust-ir
/// assigns ids sequentially, so `FuncId::new(index)` is the id of the
/// `index`-th declared function); then each body is emitted, so `Apply` calls
/// may forward-reference functions defined later in the slice.
pub fn emit_trust_ir(decls: &[IRDecl]) -> Result<Module, TrustIrError> {
    emit_trust_ir_with_config(decls, &TrustIrConfig::default())
}

/// Lower a slice of L5IR declarations into a `trust_ir::Module` with config.
pub fn emit_trust_ir_with_config(
    decls: &[IRDecl],
    config: &TrustIrConfig,
) -> Result<Module, TrustIrError> {
    // Synthesize native boxed-entry wrappers for fixed-width UInt arithmetic
    // primitives referenced only as function VALUES (`instHAddUInt8`'s
    // `PartialApply { UInt8.add, .. }`; see [`synthesize_uint_arith_wrappers`]).
    // Extending the slice here — before every downstream pass — gives each a
    // sequential FuncId in pass 1 and emits its native-`BinOp` body in pass 2,
    // so a value reference can close over the wrapper instead of an undefined
    // symbol. Empty (a zero-copy borrow) whenever no such reference exists, so
    // no existing program is perturbed.
    let uint_wrappers = synthesize_uint_arith_wrappers(decls);
    let decls: std::borrow::Cow<[IRDecl]> = if uint_wrappers.is_empty() {
        std::borrow::Cow::Borrowed(decls)
    } else {
        let mut v = decls.to_vec();
        v.extend(uint_wrappers);
        std::borrow::Cow::Owned(v)
    };
    let decls: &[IRDecl] = &decls;

    let mut mb = ModuleBuilder::new(config.module_name.clone());

    // Producer provenance (trust-ir binary v23): every function this backend
    // creates — user decls, runtime-ABI imports, dropped-callee externs — is
    // stamped `Producer::Clean`, so downstream consumers can attribute the
    // module's functions to this frontend without out-of-band context.
    mb.set_default_producer(trust_ir::Producer::Clean);

    // Source provenance: intern the source file (if any) once, and stamp a
    // file-granular span onto every node each function body emits. L5IR
    // carries no positions (they die at surface -> kernel elaboration), so
    // line/col stay 0 — honest file-level granularity, never invented lines.
    let span = config.source_file.as_deref().map(|path| SourceSpan {
        file: mb.intern_file(path),
        line: 0,
        col: 0,
    });

    // In `ExternCalls` mode, declare the Clean-runtime imports FIRST. trust-ir
    // assigns FuncIds sequentially, so the externs occupy `0..n_externs` and the
    // user functions follow at `n_externs..`. (`RuntimeAbi::declare` must run
    // before any `FunctionBuilder` is live, since one borrows the ModuleBuilder.)
    let abi = match config.runtime_lowering {
        RuntimeLowering::ExternCalls => Some(RuntimeAbi::declare(&mut mb)),
        RuntimeLowering::Dialect => None,
    };

    // --- Dropped-callee extern pre-pass (ExternCalls only; C1 boundary). ---
    //
    // The #14 dependency boundary (clean-cli `select_lcnf_decl`) drops
    // non-compilable dependencies from the slice; `emit_c` still emits calls to
    // their mangled symbols and lets the linker resolve them (runtime shims or
    // other objects). Parity here: forward-declare each such `Apply` target as
    // a bodyless `Linkage::External` function with the boxed all-Ptr signature,
    // fail-closed — a callee whose call sites do not certify that signature is
    // NOT declared and keeps the `UndefinedFunction` refusal at emit time.
    // Must run after `RuntimeAbi::declare` and before pass 1 (FuncIds are
    // sequential).
    let extern_fallbacks = declare_extern_fallbacks(&mut mb, decls, abi.is_some());

    let base = abi
        .as_ref()
        .map(RuntimeAbi::next_user_func_index)
        .unwrap_or(0)
        + extern_fallbacks.len() as u32;

    // --- Pass 1: predict every user function's FuncId by declaration index. ---
    //
    // `mb.function()` is called once per decl in order, so the i-th decl becomes
    // `FuncId::new(base + i)`. Recorded up front so calls in any body can resolve
    // a callee declared later.
    // Also intern each user function's signature now, so `PartialApply` can
    // materialize a callee's address (`fn_addr`) even before its body is built,
    // and record each decl's lowered shape so `Apply` call sites can align
    // their arguments with the callee's real parameter list (C2; see
    // [`emit_apply_user`]).
    let mut fn_ids: HashMap<String, FuncId> = HashMap::with_capacity(decls.len());
    let mut fn_sigs: HashMap<String, FuncTyId> = HashMap::with_capacity(decls.len());
    let mut fn_shapes: HashMap<String, FnShape> = HashMap::with_capacity(decls.len());
    for (idx, decl) in decls.iter().enumerate() {
        let name = decl.name.to_string();
        fn_ids.insert(name.clone(), FuncId::new(base + idx as u32));
        let param_tys: Vec<Ty> = decl.params.iter().map(|(_, t)| lower_ty(t)).collect();
        let ret_tys = lower_ret_tys(&decl.return_type);
        fn_shapes.insert(
            name.clone(),
            FnShape {
                returns_ptr: ret_tys == [Ty::Ptr],
                params: param_tys.clone(),
            },
        );
        fn_sigs.insert(name, mb.add_func_type(param_tys, ret_tys));
    }

    // --- String pre-pass (ExternCalls only). ---
    //
    // Emit one read-only, NUL-terminated byte global per distinct string
    // literal so the `String` arm can take its address (`global_addr`) and hand
    // it to `clean_mk_string`. Globals occupy their own index space, so this
    // does not perturb the FuncIds fixed in pass 1. Done before any
    // `FunctionBuilder` is live, since one borrows the ModuleBuilder.
    let string_globals = build_string_globals(&mut mb, decls, abi.is_some());

    // --- Pass 2: declare + emit each function body. ---
    for decl in decls {
        emit_decl(
            &mut mb,
            decl,
            &fn_ids,
            &fn_sigs,
            &fn_shapes,
            &extern_fallbacks,
            &abi,
            config,
            &string_globals,
            span,
        )?;
    }

    finalize_module(mb.build(), config)
}

/// Finalize an emitted module: pin the target, then gate it fail-closed.
///
/// This is the single point where a module leaves the backend (every emit
/// path funnels through `emit_trust_ir_with_config`), so the gates run here,
/// on the exact artifact handed to the caller:
///
/// 1. `Module::target_info` is pinned from the config. ABI pinning requires
///    it whenever the module has a bodyless external declaration — always the
///    case in `ExternCalls` mode (the Clean-runtime imports).
/// 2. `trust_ir_build::validate_module` must report zero errors, else the
///    module is rejected as [`TrustIrError::Invalid`] carrying the full error
///    list. Unconditional: no config can return an invalid module.
/// 3. The versioned lowering-target conformance subset
///    (`trust_ir_conformance::subset::module_subset_violations`, subset v1 —
///    the trust-ir producer contract, ratified 2026-07-04): unconditional in
///    `ExternCalls` mode (the handoff mode self-gates; after the dialect-
///    fallback refusal a violation here is an emission regression, never
///    expected output), opt-in via [`TrustIrConfig::enforce_handoff_subset`]
///    for `Dialect` mode (out-of-subset by design). Failures are
///    [`TrustIrError::OutOfLoweringSubset`].
/// 4. Opt-in ([`TrustIrConfig::enforce_handoff_subset`]): the stricter core
///    bridge gate `Module::check_conformance_subset`, else
///    [`TrustIrError::OutOfSubset`].
fn finalize_module(mut module: Module, config: &TrustIrConfig) -> Result<Module, TrustIrError> {
    module.target_info = config.target_info.clone();

    let errors = validate_module(&module);
    if !errors.is_empty() {
        return Err(TrustIrError::Invalid(errors));
    }

    if config.runtime_lowering == RuntimeLowering::ExternCalls || config.enforce_handoff_subset {
        let violations = module_subset_violations(&module);
        if !violations.is_empty() {
            return Err(TrustIrError::OutOfLoweringSubset {
                version: SUBSET_VERSION,
                violations,
            });
        }
    }

    if config.enforce_handoff_subset {
        if let Err(violations) = module.check_conformance_subset() {
            return Err(TrustIrError::OutOfSubset(violations));
        }
    }

    Ok(module)
}

/// Emit a read-only `[u8]` global (string bytes + NUL terminator) for every
/// distinct string literal in `decls`, returning a literal → [`GlobalId`] map.
///
/// Only runs when a runtime ABI is present (`ExternCalls` mode); in `Dialect`
/// mode there is no `clean_mk_string`, so the map stays empty and the `String`
/// arm keeps its dialect fallback. The returned ids are dense from 0 because
/// this is the sole producer of module globals.
fn build_string_globals(
    mb: &mut ModuleBuilder,
    decls: &[IRDecl],
    runtime_present: bool,
) -> HashMap<String, trust_ir::value::GlobalId> {
    let mut string_globals: HashMap<String, trust_ir::value::GlobalId> = HashMap::new();
    if !runtime_present {
        return string_globals;
    }
    // BTreeSet for a deterministic (reproducible) global order.
    let mut literals: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for decl in decls {
        collect_string_literals(&decl.body, &mut literals);
    }
    if literals.is_empty() {
        return string_globals;
    }
    let u8_ty = mb.add_type(Ty::U8);
    for (idx, s) in literals.into_iter().enumerate() {
        let mut bytes = s.clone().into_bytes();
        bytes.push(0); // NUL terminator for `const char*`
        let elems: Vec<trust_ir::constant::Constant> = bytes
            .iter()
            .map(|b| trust_ir::constant::Constant::Int(i128::from(*b)))
            .collect();
        let len = elems.len() as u64;
        let gid = trust_ir::value::GlobalId::new(idx as u32);
        mb.add_global(trust_ir::Global {
            name: format!("clean_str_{idx}"),
            ty: Ty::Array(u8_ty, len),
            mutable: false,
            initializer: Some(trust_ir::constant::Constant::Aggregate(elems)),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
        });
        string_globals.insert(s, gid);
    }
    string_globals
}

/// Collect every distinct string literal reachable from `body`. `IRExpr::String`
/// only ever appears as a `VDecl` value, so the walk just recurses the body tree.
fn collect_string_literals(body: &IRBody, out: &mut std::collections::BTreeSet<String>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::String(s) = value {
                out.insert(s.clone());
            }
            collect_string_literals(rest, out);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_string_literals(body, out);
            collect_string_literals(rest, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_string_literals(rest, out),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_string_literals(&alt.body, out);
            }
            if let Some(d) = default {
                collect_string_literals(d, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Forward-declare every faithfully-typeable *dropped* `Apply` callee as a
/// bodyless `Linkage::External` import, returning a callee-name →
/// ([`FuncId`], declared arity) map (C1 extern boundary; `emit_c` parity).
///
/// A "dropped" callee is an `Apply` target absent from the emitted slice: the
/// clean-cli #14 dependency boundary drops non-compilable dependencies
/// (denylisted runtime shims, non-lowerable consts) and expects the backend to
/// forward-declare them for link-time resolution, exactly as `emit_c` does by
/// emitting a call to the mangled symbol. The declared signature is the boxed
/// all-Ptr ABI of the C runtime shims: `arity × Ptr -> Ptr`, with arity taken
/// from the call site *including* erased args (emit_c passes `clean_box(0)`
/// for those, so the linked C symbol's arity counts them).
///
/// FAIL-CLOSED: a callee is declared only when EVERY call site certifies that
/// signature —
/// * the binding's declared result type lowers to `Ty::Ptr`,
/// * every non-erased argument's L5IR type lowers to `Ty::Ptr`,
/// * the arity reconciles across sites (C5a): a `PartialApply`'s `arity`
///   field certifies the FULL arity, every CALL site (n>0 args) must be at
///   least that saturated, and larger sites lower as over-applications
///   (saturated call + `clean_apply_N` extras). Without a certificate the
///   MINIMUM call-site arity is declared — an `Apply` with n args asserts
///   the true arity is <= n, so the minimum is the largest signature
///   consistent with every site. 0-arg `Apply`s are function-VALUE
///   references (#16: LCNF cannot assign an arity to env constants with a
///   `Sort`/`Prop` codomain, e.g. `Nat.le` stored in `instLENat`), so they
///   neither certify nor contradict it and lower as a closure over the
///   declared symbol when a call site fixed the arity,
/// * the mangled symbol collides with no slice decl and no other candidate.
///
/// Anything else is NOT declared and keeps the existing
/// [`TrustIrError::UndefinedFunction`] refusal at emit time — no guessed
/// signatures. Names the emitter lowers natively (`uint_arith_binop`) are
/// excluded: they are BinOps, never calls. `Dialect` mode (no runtime, no
/// link story) declares nothing and keeps the refusal unconditionally.
fn declare_extern_fallbacks(
    mb: &mut ModuleBuilder,
    decls: &[IRDecl],
    runtime_present: bool,
) -> HashMap<String, (FuncId, usize)> {
    let mut declared: HashMap<String, (FuncId, usize)> = HashMap::new();
    if !runtime_present {
        return declared;
    }

    let slice_names: HashSet<String> = decls.iter().map(|d| d.name.to_string()).collect();
    // BTreeMap for a deterministic (reproducible) declaration order.
    let mut candidates: BTreeMap<String, ExternCandidate> = BTreeMap::new();
    let mut poisoned: HashSet<String> = HashSet::new();
    for decl in decls {
        let mut var_tys: HashMap<VarId, IRType> = decl.params.iter().cloned().collect();
        collect_dropped_callees(
            &decl.body,
            &slice_names,
            &mut var_tys,
            &mut candidates,
            &mut poisoned,
        );
    }

    // Mangled-symbol collision guard (fail-closed): a candidate whose mangled
    // symbol collides with a slice decl's (verbatim) function name or with
    // another candidate's mangled symbol is dropped, not declared twice. Lean
    // name mangling is injective so this should be unreachable; it is kept as
    // a cheap defense because a duplicate module function name would only
    // surface later as a whole-module validation failure.
    let mut symbols: HashMap<String, String> = HashMap::new();
    for (name, cand) in &candidates {
        if slice_names.contains(&cand.mangled) {
            poisoned.insert(name.clone());
        }
        if let Some(prev) = symbols.insert(cand.mangled.clone(), name.clone()) {
            poisoned.insert(prev);
            poisoned.insert(name.clone());
        }
    }

    for (name, cand) in candidates {
        if poisoned.contains(&name) {
            continue;
        }
        // Resolve the declared arity from the collected observations
        // (order-independent):
        // * a `PartialApply`-certified FULL arity wins; every call site must
        //   be at least that saturated (larger sites are over-applications,
        //   lowered as saturated-call + `clean_apply` extras — the same
        //   discipline `emit_apply_user` implements for in-slice callees).
        //   A call site SMALLER than the certified full arity is an
        //   under-application with no faithful lowering: refuse fail-closed.
        // * without a certificate, declare the MINIMUM call-site arity: an
        //   `Apply` with n args asserts the callee's true arity is <= n, so
        //   the minimum is the largest signature consistent with EVERY
        //   observed site, and larger sites lower as over-applications.
        //   (Agreeing sites — the only shape the boundary accepted before
        //   over-application support — resolve to the identical declaration.)
        // * a value-ref-only candidate declares arity 0.
        let arity = match (cand.full_arity, cand.call_range) {
            (Some(full), Some((min, _max))) if min >= full => full,
            (Some(_), Some(_)) => continue, // under-application: refuse
            (Some(full), None) => full,
            (None, Some((min, _max))) => min,
            (None, None) => 0,
        };
        let ty = mb.add_func_type(vec![Ty::Ptr; arity], vec![Ty::Ptr]);
        let id = mb.function(cand.mangled, ty).build();
        declared.insert(name, (id, arity));
    }
    declared
}

/// A dropped-callee extern candidate: its mangled link symbol and the boxed
/// all-Ptr arity observations from its use sites (erased args included).
struct ExternCandidate {
    mangled: String,
    /// The callee's FULL arity as certified by a `PartialApply`'s `arity`
    /// field (`None` until one is seen).
    full_arity: Option<usize>,
    /// `(min, max)` argument counts over `Apply` CALL sites (n>0 args);
    /// `None` when only value references were seen.
    call_range: Option<(usize, usize)>,
}

/// Record one arity observation for a dropped-callee extern candidate.
///
/// `is_value_ref` marks a 0-arg `Apply` (a function-VALUE reference): it
/// creates/keeps the candidate but neither certifies nor contradicts any
/// arity. `is_full_arity` marks a `PartialApply` observation, whose `arity`
/// field is the callee's real full arity; two disagreeing full arities
/// poison the name. Call sites (`Apply` with n>0 args) are collected as a
/// range and reconciled at declaration time ([`declare_extern_fallbacks`]):
/// over-applications of a certified full arity are legal, anything
/// ambiguous or under-applied keeps the fail-closed refusal.
fn record_extern_arity(
    candidates: &mut BTreeMap<String, ExternCandidate>,
    poisoned: &mut HashSet<String>,
    fn_name: &clean_kernel::Name,
    arity: usize,
    is_value_ref: bool,
    is_full_arity: bool,
) {
    let name = fn_name.to_string();
    let entry = candidates
        .entry(name.clone())
        .or_insert_with(|| ExternCandidate {
            mangled: crate::mangle::mangle_name(fn_name),
            full_arity: None,
            call_range: None,
        });
    if is_value_ref {
        return;
    }
    if is_full_arity {
        match entry.full_arity {
            Some(prev) if prev != arity => {
                poisoned.insert(name);
            }
            _ => entry.full_arity = Some(arity),
        }
    } else {
        entry.call_range = Some(match entry.call_range {
            Some((min, max)) => (min.min(arity), max.max(arity)),
            None => (arity, arity),
        });
    }
}

/// The lowered signature shape of an in-slice user decl, recorded in pass 1.
///
/// Used by [`emit_apply_user`] to align call-site arguments positionally with
/// the callee's real parameter list (C2 erased-arity correctness): L5IR
/// `Apply` args are the full application spine, so `args[i]` binds
/// `params[i]`, erased args included.
struct FnShape {
    /// Lowered parameter types — one per L5IR decl param. Erased-origin
    /// params are present (they lower to `Ty::Ptr` like every object).
    params: Vec<Ty>,
    /// Whether the decl returns exactly one `Ty::Ptr` (a managed object —
    /// possibly a closure): the precondition for lowering an over-applied
    /// call through the runtime `clean_apply_N` chain.
    returns_ptr: bool,
}

/// Walk `body` collecting dropped-callee extern candidates (see
/// [`declare_extern_fallbacks`] for the certification rules), tracking each
/// variable's declared L5IR type (`params` + `VDecl` + join-point params) so
/// call-site argument types can be checked statically.
fn collect_dropped_callees(
    body: &IRBody,
    slice_names: &HashSet<String>,
    var_tys: &mut HashMap<VarId, IRType>,
    candidates: &mut BTreeMap<String, ExternCandidate>,
    poisoned: &mut HashSet<String>,
) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            // A `PartialApply` of a dropped callee references the symbol as a
            // CLOSURE; its `arity` field is the callee's full Pi arity, so it
            // certifies the extern signature exactly like an agreeing call
            // site (the fixed args must still be Ptr-typeable).
            if let IRExpr::PartialApply { fn_id, arity, args } = value {
                let name = fn_id.0.to_string();
                if !slice_names.contains(&name) && uint_arith_binop(&name).is_none() {
                    let result_ok = lower_ty(ty) == Ty::Ptr;
                    let args_ok = args.iter().all(|arg| match arg {
                        IRArg::Erased => true,
                        IRArg::Var(v) => var_tys.get(v).map(lower_ty).is_some_and(|t| t == Ty::Ptr),
                    });
                    if result_ok && args_ok {
                        record_extern_arity(
                            candidates,
                            poisoned,
                            &fn_id.0,
                            *arity as usize,
                            false,
                            true, // PartialApply arity IS the callee's full arity
                        );
                    } else {
                        poisoned.insert(name);
                    }
                }
            }
            if let IRExpr::Apply { fn_id, args } = value {
                let name = fn_id.0.to_string();
                // Skip in-slice callees (they keep their bodies — never
                // demoted) and native-arithmetic names (BinOps, never calls).
                if !slice_names.contains(&name) && uint_arith_binop(&name).is_none() {
                    let result_ok = lower_ty(ty) == Ty::Ptr;
                    // Erased args are materialized as boxed units at the call
                    // site (Ptr by construction); non-erased args must have a
                    // known Ptr-lowering type.
                    let args_ok = args.iter().all(|arg| match arg {
                        IRArg::Erased => true,
                        IRArg::Var(v) => var_tys.get(v).map(lower_ty).is_some_and(|t| t == Ty::Ptr),
                    });
                    if result_ok && args_ok {
                        // A 0-arg `Apply` is a function-VALUE reference (#16
                        // class: LCNF has no arity for env constants with a
                        // `Sort`/`Prop` codomain, e.g. `instLENat`'s `Nat.le`
                        // field), not a call — it never certifies or
                        // contradicts the arity. Real call sites (n>0) and
                        // `PartialApply` arities must all agree.
                        record_extern_arity(
                            candidates,
                            poisoned,
                            &fn_id.0,
                            args.len(),
                            args.is_empty(),
                            false,
                        );
                    } else {
                        poisoned.insert(name);
                    }
                }
            }
            var_tys.insert(*var, ty.clone());
            collect_dropped_callees(rest, slice_names, var_tys, candidates, poisoned);
        }
        IRBody::JDecl {
            params,
            body: jp_body,
            rest,
            ..
        } => {
            for (v, t) in params {
                var_tys.insert(*v, t.clone());
            }
            collect_dropped_callees(jp_body, slice_names, var_tys, candidates, poisoned);
            collect_dropped_callees(rest, slice_names, var_tys, candidates, poisoned);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_dropped_callees(rest, slice_names, var_tys, candidates, poisoned);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_dropped_callees(&alt.body, slice_names, var_tys, candidates, poisoned);
            }
            if let Some(d) = default {
                collect_dropped_callees(d, slice_names, var_tys, candidates, poisoned);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Emit one function declaration into the module under construction.
///
/// `span` is the decl's source span (file-granular today; see the module-level
/// "Source provenance" docs). When present it is stamped onto every node this
/// function's body emits, terminators included; `None` emits span-less.
#[allow(clippy::too_many_arguments)]
fn emit_decl(
    mb: &mut ModuleBuilder,
    decl: &IRDecl,
    fn_ids: &HashMap<String, FuncId>,
    fn_sigs: &HashMap<String, FuncTyId>,
    fn_shapes: &HashMap<String, FnShape>,
    extern_fallbacks: &HashMap<String, (FuncId, usize)>,
    abi: &Option<RuntimeAbi>,
    config: &TrustIrConfig,
    string_globals: &HashMap<String, trust_ir::value::GlobalId>,
    span: Option<SourceSpan>,
) -> Result<(), TrustIrError> {
    let param_tys: Vec<Ty> = decl.params.iter().map(|(_, t)| lower_ty(t)).collect();
    // Reuse the signature interned in pass 1 (falls back to interning if absent).
    let ty = match fn_sigs.get(&decl.name.to_string()) {
        Some(t) => *t,
        None => {
            let ret_tys = lower_ret_tys(&decl.return_type);
            mb.add_func_type(param_tys.clone(), ret_tys)
        }
    };

    let mut fb = mb.function(decl.name.to_string(), ty);

    // Stamp the decl's span onto every node emitted below (set once; the
    // builder threads it through all emit paths, terminators included).
    if let Some(span) = span {
        fb.set_span(span);
    }

    // The first created block is the default entry; it carries the SSA params.
    let entry = fb.create_block();
    let mut var_values: HashMap<VarId, ValueId> = HashMap::new();
    let mut var_tys: HashMap<VarId, IRType> = HashMap::new();
    for ((var, ir_ty), ty) in decl.params.iter().zip(param_tys.iter()) {
        let v = fb.add_block_param(entry, ty.clone());
        var_values.insert(*var, v);
        var_tys.insert(*var, ir_ty.clone());
    }
    fb.set_entry(entry);

    let mut ctx = FnCtx {
        fb: &mut fb,
        fn_ids,
        fn_sigs,
        fn_shapes,
        extern_fallbacks,
        config,
        abi: abi.clone(),
        var_values,
        var_tys,
        jp_blocks: HashMap::new(),
        string_globals,
        ret_ty: decl.return_type.clone(),
    };
    ctx.fb.switch_to_block(entry);
    // SOUNDNESS FIX (2026-07-12): the target-pinned USize/UInt64 decision
    // procedures (`.decEq`/`.decLt`/`.decLe`) lower to a DIRECT native `ICmp`
    // on the two u64 operands, bypassing the generic L5IR body whose
    // `clean_box((v<<1)|1)` tagged-immediate boxing truncates at bit 63 (e.g.
    // `decEq(2^63, 0)` wrongly computes `true`). See `native_uint_decision_op`
    // for the root-cause analysis; the guard there fires only for the exact
    // 2×{USize|UInt64} -> Bool shape, so no other decl changes shape.
    if let Some(cmp_op) = native_uint_decision_op(decl) {
        let lhs = ctx.value_of(decl.params[0].0)?;
        let rhs = ctx.value_of(decl.params[1].0)?;
        let result = ctx.fb.icmp(cmp_op, Ty::U64, lhs, rhs);
        ctx.fb.ret(vec![result]);
    } else {
        emit_body(&mut ctx, &decl.body)?;
    }

    fb.build();
    Ok(())
}

/// Per-function lowering context.
struct FnCtx<'a, 'b> {
    fb: &'a mut FunctionBuilder<'b>,
    fn_ids: &'a HashMap<String, FuncId>,
    fn_sigs: &'a HashMap<String, FuncTyId>,
    /// Lowered signature shape of every in-slice user decl (pass 1), for the
    /// `Apply` call-site/parameter alignment (C2; [`emit_apply_user`]).
    fn_shapes: &'a HashMap<String, FnShape>,
    /// Dropped-callee extern forward-declarations (C1 boundary): callee name →
    /// (the bodyless-`External` all-Ptr import declared by the pre-pass, its
    /// declared arity). Empty outside `ExternCalls` mode.
    extern_fallbacks: &'a HashMap<String, (FuncId, usize)>,
    config: &'a TrustIrConfig,
    /// Declared Clean-runtime imports, present in `ExternCalls` mode.
    abi: Option<RuntimeAbi>,
    /// SSA value currently bound to each L5IR variable.
    var_values: HashMap<VarId, ValueId>,
    /// Declared L5IR type of each in-scope variable (function params, `VDecl`
    /// bindings, join-point params). Drives the C2 scalar-representation
    /// dispatch: whether a `Case` scrutinee / projection base is an unboxed
    /// scalar (native `CondBr`/`switch`-on-value / identity) or a boxed
    /// object (`clean_obj_tag` / `clean_ctor_get*`) — `emit_c` parity with
    /// `CEmitter::var_types`.
    var_tys: HashMap<VarId, IRType>,
    /// trust-ir block + ordered param vars for each in-scope join point.
    jp_blocks: HashMap<JoinPointId, JoinPoint>,
    /// String literal → its read-only byte global (populated in ExternCalls mode).
    string_globals: &'a HashMap<String, trust_ir::value::GlobalId>,
    /// Declared L5IR return type of the decl being emitted. Drives the C2b
    /// return-representation alignment at `Ret` ([`align_return_value`]).
    ret_ty: IRType,
}

/// A lowered join point: its trust-ir block plus the order of its params.
struct JoinPoint {
    block: BlockId,
    /// L5IR param vars in declaration order (their SSA values live on `block`).
    params: Vec<VarId>,
}

impl FnCtx<'_, '_> {
    /// Resolve the SSA value bound to an L5IR variable.
    fn value_of(&self, var: VarId) -> Result<ValueId, TrustIrError> {
        self.var_values
            .get(&var)
            .copied()
            .ok_or(TrustIrError::UndefinedVariable(var))
    }

    /// Resolve the SSA value of an argument; erased args are a hard error in
    /// any value position (callers that tolerate erasure must filter first).
    fn value_of_arg(&self, arg: &IRArg) -> Result<ValueId, TrustIrError> {
        match arg {
            IRArg::Var(v) => self.value_of(*v),
            IRArg::Erased => Err(TrustIrError::ErasedInValuePosition),
        }
    }
}

/// Lower the body of a function (or join point / case arm) into the current
/// block. Every path must end by emitting a terminator.
fn emit_body(ctx: &mut FnCtx, body: &IRBody) -> Result<(), TrustIrError> {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let v = emit_expr(ctx, value, ty)?;
            ctx.var_values.insert(*var, v);
            ctx.var_tys.insert(*var, ty.clone());
            emit_body(ctx, rest)
        }

        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => {
            // In L5IR, control falls through a `JDecl` into `rest`, which may
            // `Jmp` to the join point; the join-point block itself is reachable
            // only via those jumps. trust-ir is basic-block SSA, so this needs
            // THREE blocks: the current predecessor (already active), the
            // join-point `block`, and a `cont` block holding `rest`. Critically,
            // the predecessor must be given a terminator branching to `cont` —
            // otherwise it is left dangling and `validate_module` rejects it.
            let block = ctx.fb.create_block();
            let mut jp_param_vars = Vec::with_capacity(params.len());
            for (pvar, pty) in params {
                let pv = ctx.fb.add_block_param(block, lower_ty(pty));
                ctx.var_values.insert(*pvar, pv);
                ctx.var_tys.insert(*pvar, pty.clone());
                jp_param_vars.push(*pvar);
            }
            ctx.jp_blocks.insert(
                *jp,
                JoinPoint {
                    block,
                    params: jp_param_vars,
                },
            );

            // Terminate the predecessor by falling through to `cont`.
            let cont = ctx.fb.create_block();
            ctx.fb.br(cont, vec![]);

            // Emit the join point's body into its own block. Done before `rest`
            // so its variable scope is exactly the bindings live at the `JDecl`
            // (plus its own params), not anything `rest` introduces.
            ctx.fb.switch_to_block(block);
            emit_body(ctx, body)?;

            // Emit `rest` (the fall-through continuation) into `cont`.
            ctx.fb.switch_to_block(cont);
            emit_body(ctx, rest)
        }

        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => emit_case(ctx, *scrutinee, alts, default.as_deref()),

        IRBody::Jmp { jp, args } => {
            let jp_info = ctx
                .jp_blocks
                .get(jp)
                .ok_or(TrustIrError::UndefinedJoinPoint(*jp))?;
            let target = jp_info.block;
            // Filter erased args: a join point param that was erased has no SSA
            // value. We pass arguments positionally for non-erased args only.
            let mut arg_vals = Vec::with_capacity(args.len());
            for arg in args {
                if let IRArg::Var(_) = arg {
                    arg_vals.push(ctx.value_of_arg(arg)?);
                }
            }
            ctx.fb.br(target, arg_vals);
            Ok(())
        }

        IRBody::Ret(arg) => {
            match arg {
                IRArg::Var(v) => {
                    let val = ctx.value_of(*v)?;
                    // A `Void`/`Erased` return type carries no runtime value:
                    // the lowered signature promises zero results
                    // (`lower_ret_tys` is empty), so a materialized value
                    // returned by variable — e.g. the erased `USize(0)`
                    // placeholder `Unit.unit` binds then returns — is DROPPED,
                    // exactly as the sibling `IRArg::Erased` arm drops. Emitting
                    // it would give the `ret` terminator arity 1 against a
                    // 0-result signature, the historical `Unit.unit` refusal
                    // "return arity mismatch: expected 0 values, got 1".
                    if lower_ret_tys(&ctx.ret_ty).is_empty() {
                        ctx.fb.ret(vec![]);
                    } else {
                        // C2b: align the returned value's representation with
                        // the decl's lowered return type before the terminator.
                        let val = align_return_value(ctx, *v, val)?;
                        ctx.fb.ret(vec![val]);
                    }
                }
                // An erased return is a void/ZST return in trust-ir terms —
                // unless the signature promises a managed pointer, in which
                // case the erased unit is boxed (`clean_box_uint64(0)`, the
                // same convention closure captures and erased arg slots use).
                IRArg::Erased => {
                    if lower_ret_tys(&ctx.ret_ty) == [Ty::Ptr] {
                        if let (RuntimeLowering::ExternCalls, Some(abi)) =
                            (ctx.config.runtime_lowering, ctx.abi.clone())
                        {
                            let unit = box_erased(ctx, &abi);
                            ctx.fb.ret(vec![unit]);
                            return Ok(());
                        }
                    }
                    ctx.fb.ret(vec![]);
                }
            }
            Ok(())
        }

        IRBody::Unreachable => {
            ctx.fb.unreachable();
            Ok(())
        }

        // --- Perceus RC ops: native trust-ir ARC instructions (P1), in BOTH
        // modes — `Retain`/`Release` are core ops needing neither the dialect
        // nor the runtime ABI. trust-cg routes them to the RC runtime the
        // module declares (the `clean_inc`/`clean_dec`/`clean_is_exclusive`
        // triple `RuntimeAbi` keeps declared in ExternCalls mode). ---
        IRBody::Inc { var, n, rest } => {
            let operand = ctx.value_of(*var)?;
            // `inc x n` is n retains: trust-ir `Retain` is the +1 operational
            // step (Lean `semRetain`), so the count unrolls structurally. n is
            // bounded by the extra owned copies Perceus inserts (uses in the
            // continuation), so the unroll is linear in the source body.
            // `inc x 0` historically still emitted one runtime inc
            // (`n <= 1 -> clean_inc`), so the count stays clamped to >= 1.
            for _ in 0..(*n).max(1) {
                ctx.fb.retain(operand);
            }
            emit_body(ctx, rest)
        }
        IRBody::Dec { var, rest } => {
            let operand = ctx.value_of(*var)?;
            // `dec x` is trust-ir `Release`: refcount -1, frees at zero
            // (Lean `semRelease` — same discipline as `clean_dec`).
            ctx.fb.release(operand);
            emit_body(ctx, rest)
        }
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => {
            let obj = ctx.value_of(*var)?;
            let val = ctx.value_of(*value)?;
            emit_clean_void(ctx, "obj.set", vec![obj, val], &[("idx", *idx as u64)])?;
            emit_body(ctx, rest)
        }
        IRBody::SetTag { var, tag, rest } => {
            let obj = ctx.value_of(*var)?;
            emit_clean_void(ctx, "obj.set_tag", vec![obj], &[("tag", *tag as u64)])?;
            emit_body(ctx, rest)
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => {
            let obj = ctx.value_of(*var)?;
            let val = ctx.value_of(*value)?;
            emit_clean_void(ctx, "obj.uset", vec![obj, val], &[("idx", *idx as u64)])?;
            emit_body(ctx, rest)
        }
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty: sty,
            rest,
        } => {
            let obj = ctx.value_of(*var)?;
            let val = ctx.value_of(*value)?;
            let handled = if let (RuntimeLowering::ExternCalls, Some(abi)) =
                (ctx.config.runtime_lowering, ctx.abi.clone())
            {
                let byte_off = 8 * (*n as u64) + (*offset as u64);
                emit_sset_extern(ctx, &abi, sty, obj, byte_off, val)
            } else {
                false
            };
            if !handled {
                emit_clean_void(
                    ctx,
                    "obj.sset",
                    vec![obj, val],
                    &[("n", *n as u64), ("offset", *offset as u64)],
                )?;
            }
            emit_body(ctx, rest)
        }
    }
}

/// Lower `IRBody::Case`, dispatching on the scrutinee's REPRESENTATION (C2).
///
/// * Boxed object scrutinee: the tag is read via `clean.obj.tag` /
///   `clean_obj_tag` (a `U32`) and dispatched with a `switch` — the historical
///   path, unchanged.
/// * Unboxed **integer scalar** scrutinee (`UInt8..UInt64`/`USize`): the value
///   already *is* the constructor tag (`emit_c` parity:
///   `CEmitter::is_unboxed_scalar` switches on the value), so the `switch`
///   runs directly on the scrutinee — a `clean_obj_tag` call on a non-pointer
///   was the invalid-IR miscompile class `validate_module` refused.
/// * Unboxed **`Bool`** scrutinee: two-way dispatch on the value itself via
///   `CondBr` ([`emit_case_bool`]); trust-ir keeps `Bool` distinct from the
///   integer types, so it is a branch, not a switch.
///
/// A scrutinee with no recorded type (not a param, `VDecl`, or join-point
/// binding — impossible for checker-clean input) conservatively keeps the
/// boxed-object path.
fn emit_case(
    ctx: &mut FnCtx,
    scrutinee: VarId,
    alts: &[crate::ir::IRAlt],
    default: Option<&IRBody>,
) -> Result<(), TrustIrError> {
    let scrut = ctx.value_of(scrutinee)?;
    match ctx.var_tys.get(&scrutinee) {
        Some(IRType::Bool) => emit_case_bool(ctx, scrut, alts, default),
        Some(IRType::UInt8 | IRType::UInt16 | IRType::UInt32 | IRType::UInt64 | IRType::USize) => {
            emit_case_switch(ctx, scrut, alts, default)
        }
        _ => {
            let tag = emit_clean_value(ctx, "obj.tag", vec![scrut], &[], Ty::U32)?;
            emit_case_switch(ctx, tag, alts, default)
        }
    }
}

/// Lower a `Case` whose dispatch value `discr` (a constructor tag — either a
/// `clean_obj_tag` read or an unboxed integer scalar scrutinee itself) is
/// already in hand, as a trust-ir `switch`.
///
/// Each alternative becomes a `switch` case targeting a block that emits the
/// alternative body. A `default` arm (or, absent one, a trap-to-`unreachable`
/// block) handles the fallthrough.
fn emit_case_switch(
    ctx: &mut FnCtx,
    discr: ValueId,
    alts: &[crate::ir::IRAlt],
    default: Option<&IRBody>,
) -> Result<(), TrustIrError> {
    use trust_ir::constant::Constant;
    use trust_ir::inst::SwitchCase;

    // Pre-create a block per alternative and the default block, then wire the
    // switch. Bodies are emitted after the terminator is in place (each body
    // block is independent and supplies its own terminator).
    let mut cases = Vec::with_capacity(alts.len());
    let mut arm_blocks = Vec::with_capacity(alts.len());
    for alt in alts {
        let blk = ctx.fb.create_block();
        cases.push(SwitchCase {
            value: Constant::Int(alt.ctor.tag as i128),
            target: blk,
            args: vec![],
        });
        arm_blocks.push(blk);
    }

    let default_block = ctx.fb.create_block();

    // Emit the switch terminator in the current (scrutinizing) block.
    ctx.fb.switch(discr, cases, default_block, vec![]);

    // Emit each alternative body into its block.
    for (alt, blk) in alts.iter().zip(arm_blocks.iter()) {
        ctx.fb.switch_to_block(*blk);
        emit_body(ctx, &alt.body)?;
    }

    // Emit the default arm. If the source has no default, the case is assumed
    // exhaustive: emit `unreachable`.
    ctx.fb.switch_to_block(default_block);
    match default {
        Some(d) => emit_body(ctx, d),
        None => {
            ctx.fb.unreachable();
            Ok(())
        }
    }
}

/// Lower a `Case` whose scrutinee is an unboxed `Bool`: a `CondBr` on the
/// scrutinee itself.
///
/// POLARITY is keyed on each alternative's constructor TAG, never on its
/// position in the alt list, so an upstream alt-order change cannot flip
/// branches: the kernel `Bool` ctor order fixes `Bool.false` = tag 0 and
/// `Bool.true` = tag 1, so tag 1 is the `then` edge and tag 0 the `else`
/// edge. A side covered by neither an alt nor the `default` arm is
/// unreachable for a well-formed exhaustive case and lowers to `unreachable`;
/// an alt carrying a non-Bool tag (or a duplicated tag) is refused
/// fail-closed rather than guessed at.
fn emit_case_bool(
    ctx: &mut FnCtx,
    scrut: ValueId,
    alts: &[crate::ir::IRAlt],
    default: Option<&IRBody>,
) -> Result<(), TrustIrError> {
    let mut false_body: Option<&IRBody> = None;
    let mut true_body: Option<&IRBody> = None;
    for alt in alts {
        let slot = match alt.ctor.tag {
            0 => &mut false_body,
            1 => &mut true_body,
            other => {
                return Err(TrustIrError::Unsupported(format!(
                    "bool case alternative `{}` carries non-bool ctor tag {other}",
                    alt.ctor.name
                )))
            }
        };
        if slot.replace(&alt.body).is_some() {
            return Err(TrustIrError::Unsupported(format!(
                "bool case with duplicate ctor tag {}",
                alt.ctor.tag
            )));
        }
    }

    let then_blk = ctx.fb.create_block();
    let else_blk = ctx.fb.create_block();
    ctx.fb.condbr(scrut, then_blk, vec![], else_blk, vec![]);

    // `true` (tag 1) → then. When only one side has an alt, the other takes
    // the `default` body (each side emits its own copy — the bodies are
    // independent blocks).
    ctx.fb.switch_to_block(then_blk);
    match true_body.or(default) {
        Some(b) => emit_body(ctx, b)?,
        None => ctx.fb.unreachable(),
    }

    // `false` (tag 0) → else.
    ctx.fb.switch_to_block(else_blk);
    match false_body.or(default) {
        Some(b) => emit_body(ctx, b)?,
        None => ctx.fb.unreachable(),
    }
    Ok(())
}

/// Lower a pure `IRExpr` into an SSA value, given the declared result type.
fn emit_expr(ctx: &mut FnCtx, expr: &IRExpr, ty: &IRType) -> Result<ValueId, TrustIrError> {
    match expr {
        // --- Easy core ops ---
        // A big Nat literal (>= 2^64) is inherently a heap Nat OBJECT, not a
        // machine-scalar const (RUNG B). ExternCalls builds it from two u64
        // limbs via the `clean_nat_big` runtime import; Dialect mode has no
        // faithful managed form here and refuses fail-closed.
        IRExpr::Lit(IRLiteral::NatBig(v)) => {
            if let (RuntimeLowering::ExternCalls, Some(abi)) =
                (ctx.config.runtime_lowering, ctx.abi.clone())
            {
                let lo = ctx.fb.iconst(Ty::U64, (*v as u64) as i128);
                let hi = ctx.fb.iconst(Ty::U64, ((*v >> 64) as u64) as i128);
                Ok(ctx.fb.call(abi.clean_nat_big, vec![lo, hi]))
            } else {
                Err(TrustIrError::Unsupported(
                    "big Nat literal (>= 2^64) has no Dialect-mode lowering; the \
                     ExternCalls runtime provides clean_nat_big"
                        .to_string(),
                ))
            }
        }
        IRExpr::Lit(lit) => Ok(emit_literal(ctx, lit)),

        IRExpr::Apply { fn_id, args } => {
            let name = fn_id.0.to_string();
            // A user declaration always wins; only an OTHERWISE-UNDEFINED
            // fixed-width arithmetic primitive lowers to a native BinOp below.
            if let Some(callee) = ctx.fn_ids.get(&name).copied() {
                return emit_apply_user(ctx, &name, callee, args);
            }
            // A 0-arg `Apply` of a fixed-width UInt arithmetic primitive is a
            // #16 function-VALUE reference, not a call: materialize a closure
            // over the primitive's synthesized native boxed-entry wrapper —
            // mirrors the dropped-callee 0-arg materialization below. Guarded on
            // `args.is_empty()` so saturated calls still take the native-BinOp
            // arm; on a present wrapper so it is only reached when the pre-pass
            // synthesized one.
            if args.is_empty() && uint_arith_binop(&name).is_some() {
                if let (Some(&wid), Some(abi)) = (
                    ctx.fn_ids.get(&uint_arith_wrapper_name(&name)),
                    ctx.abi.clone(),
                ) {
                    let fn_ptr = ctx.fb.fn_addr(abi.clean_fn_ty, wid);
                    let arity_c = ctx.fb.iconst(Ty::U32, 2);
                    let nfixed_c = ctx.fb.iconst(Ty::U32, 0);
                    return Ok(ctx
                        .fb
                        .call(abi.clean_alloc_closure, vec![fn_ptr, arity_c, nfixed_c]));
                }
            }
            // Fixed-width UInt arithmetic primitives (`UInt{8,16,32,64}.{add,sub,
            // mul}`) lower to native trust-ir `BinOp`s. This is semantically
            // exact, not an approximation: the kernel's UIntN ops are wraparound
            // mod 2^N (Fin-based), and trust-ir's integer `Add`/`Sub`/`Mul` are
            // ratified as two's-complement wrapping at the operand width
            // (trust-ir `docs/ub-numerics-policy.md`). Making these native (a) is
            // what the P2 semantics-preservation certificate certifies over
            // (`emit_trust_ir_tv`), and (b) lets trust-cg emit real machine
            // arithmetic instead of an undefined-extern call. Only reached when
            // the name is NOT a user decl, so no existing program changes shape.
            if let Some((op, bty)) = uint_arith_binop(&name) {
                let declared = lower_ty(ty);
                if declared != bty {
                    return Err(TrustIrError::Unsupported(format!(
                        "arithmetic primitive {name} produces {bty:?} but the \
                         declaration expects {declared:?}"
                    )));
                }
                let [a, b] = args.as_slice() else {
                    return Err(TrustIrError::Unsupported(format!(
                        "arithmetic primitive {name} expects exactly 2 arguments, \
                         got {}",
                        args.len()
                    )));
                };
                let lhs = ctx.value_of_arg(a)?;
                let rhs = ctx.value_of_arg(b)?;
                return Ok(ctx.fb.binop(op, bty, lhs, rhs));
            }
            // C1 EXTERN BOUNDARY (emit_c parity): a callee the #14 dependency
            // boundary dropped from the slice was forward-declared as a
            // bodyless external with the boxed all-Ptr signature by the
            // pre-pass ([`declare_extern_fallbacks`]) — call it; the symbol
            // resolves at link time (runtime shims for the denylisted names).
            // Erased args are materialized as boxed units, exactly like
            // emit_c passes `clean_box(0)`. A callee the pre-pass could not
            // faithfully type is absent here and stays on the fail-closed
            // refusal below.
            if let (Some(&(callee, arity)), Some(abi)) =
                (ctx.extern_fallbacks.get(&name), ctx.abi.clone())
            {
                // A 0-arg `Apply` against a declared arity n>0 is a
                // function-VALUE reference (#16), not a call: materialize the
                // closure over the declared symbol —
                // `clean_alloc_closure(sym, n, 0)` — exactly the
                // `PartialApply` lowering for in-slice callees.
                if args.is_empty() && arity > 0 {
                    let fn_ptr = ctx.fb.fn_addr(abi.clean_fn_ty, callee);
                    let arity_c = ctx.fb.iconst(Ty::U32, arity as i128);
                    let nfixed_c = ctx.fb.iconst(Ty::U32, 0);
                    return Ok(ctx
                        .fb
                        .call(abi.clean_alloc_closure, vec![fn_ptr, arity_c, nfixed_c]));
                }
                // Defensive fail-closed: certification guarantees every call
                // site is at least saturated; refuse an under-applied call
                // rather than emit one the validator would reject.
                if args.len() < arity {
                    return Err(TrustIrError::Unsupported(format!(
                        "call to dropped callee `{name}` with {} args, but its \
                         certified extern signature has arity {arity}",
                        args.len()
                    )));
                }
                // Args BEYOND the certified arity are OVER-application (a
                // `PartialApply`-certified full arity with larger call
                // sites): the saturated call returns a closure and the
                // extras are applied to it via the runtime `clean_apply_N` —
                // the same discipline `emit_apply_user` implements for
                // in-slice callees. The declared extern returns `Ptr` by
                // construction, so the result is always applicable.
                let (direct, extra) = args.split_at(arity);
                let mut arg_vals = Vec::with_capacity(direct.len());
                for arg in direct {
                    arg_vals.push(match arg {
                        IRArg::Var(_) => ctx.value_of_arg(arg)?,
                        IRArg::Erased => box_erased(ctx, &abi),
                    });
                }
                let result = ctx.fb.call(callee, arg_vals);
                if extra.is_empty() {
                    return Ok(result);
                }
                let mut extra_vals = Vec::with_capacity(extra.len());
                for arg in extra {
                    extra_vals.push(match arg {
                        IRArg::Var(_) => ctx.value_of_arg(arg)?,
                        IRArg::Erased => box_erased(ctx, &abi),
                    });
                }
                return emit_apply_runtime(ctx, &abi, result, extra_vals);
            }
            Err(TrustIrError::UndefinedFunction(name))
        }

        IRExpr::Tag(arg) => {
            let obj = ctx.value_of_arg(arg)?;
            emit_clean_value(ctx, "obj.tag", vec![obj], &[], Ty::U32)
        }

        IRExpr::IsShared(var) => {
            let obj = ctx.value_of(*var)?;
            // Native ARC (P1): trust-ir `IsUnique` answers the OPPOSITE
            // predicate — refcount == 1, exactly `clean_is_exclusive`'s
            // polarity (the Lean 4 `lean_is_exclusive` lineage) — so IsShared
            // is its negation. trust-ir has no Bool `not` (`xor` needs an
            // integer type, `icmp` rejects Bool), so negate with a Bool
            // `select`, the proven-lowering Bool inverter. Both modes: the
            // ops are core trust-ir, no dialect / runtime ABI involved.
            let unique = ctx.fb.is_unique(obj);
            let f = ctx.fb.bool_const(false);
            let t = ctx.fb.bool_const(true);
            Ok(ctx.fb.select(Ty::Bool, unique, f, t))
        }

        IRExpr::UProj { idx, var } => {
            let obj = ctx.value_of(*var)?;
            // C2: a projection out of an unboxed scalar carrier is the carrier
            // itself (see the `SProj` arm) — here the result is `USize`, so
            // only a `U64`-lowering carrier is faithful.
            if let Some(carrier) = ctx.var_tys.get(var).filter(|t| t.is_scalar()) {
                return if lower_ty(carrier) == Ty::U64 {
                    Ok(obj)
                } else {
                    Err(scalar_carrier_mismatch("uproj", carrier, &IRType::USize))
                };
            }
            emit_clean_value(
                ctx,
                "obj.uproj",
                vec![obj],
                &[("idx", *idx as u64)],
                Ty::U64,
            )
        }

        IRExpr::SProj {
            n,
            offset,
            var,
            ty: sty,
        } => {
            let obj = ctx.value_of(*var)?;
            // C2 scalar-representation correctness: when the base variable is
            // itself an unboxed scalar (a newtype-style carrier, e.g. `Char`
            // lowered to `U32`), the carrier IS the single scalar field —
            // `Char.val` is `sproj` on a `U32` — so a same-width projection is
            // the identity. The boxed-layout byte offsets (`n`/`offset`) are
            // meaningless for an unboxed carrier and a width-changing
            // projection has no faithful form: refused fail-closed (the old
            // `clean_ctor_get_*` call on a non-pointer was invalid IR).
            if let Some(carrier) = ctx.var_tys.get(var).filter(|t| t.is_scalar()) {
                return if lower_ty(carrier) == lower_ty(sty) {
                    Ok(obj)
                } else {
                    Err(scalar_carrier_mismatch("sproj", carrier, sty))
                };
            }
            emit_clean_value(
                ctx,
                "obj.sproj",
                vec![obj],
                &[("n", *n as u64), ("offset", *offset as u64)],
                lower_ty(sty),
            )
        }

        IRExpr::Proj { idx, ty: pty, arg } => {
            let obj = ctx.value_of_arg(arg)?;
            // C2: projection out of an unboxed scalar carrier (see `SProj`).
            // A same-width scalar projection is the identity; an OBJECT-typed
            // projection re-boxes the carrier (`UInt8.toBitVec` projecting the
            // runtime-`Nat` bitvec out of a `U8`; `Char.valid` projecting an
            // erased proof out of a `U32` — a boxed value is faithful for
            // both, and for the erased case any managed value would do).
            if let IRArg::Var(v) = arg {
                if let Some(carrier) = ctx.var_tys.get(v).filter(|t| t.is_scalar()).cloned() {
                    let declared = lower_ty(pty);
                    if declared == lower_ty(&carrier) {
                        return Ok(obj);
                    }
                    if declared == Ty::Ptr {
                        if let (RuntimeLowering::ExternCalls, Some(abi)) =
                            (ctx.config.runtime_lowering, ctx.abi.clone())
                        {
                            return Ok(box_scalar_tagged(ctx, &abi, &carrier, obj));
                        }
                        // Dialect mode: fall through to the opaque
                        // `clean.obj.proj` node — no runtime to box with, and
                        // dialect operands round-trip untyped by design.
                    } else {
                        return Err(scalar_carrier_mismatch("proj", &carrier, pty));
                    }
                }
            }
            emit_clean_value(
                ctx,
                "obj.proj",
                vec![obj],
                &[("idx", *idx as u64)],
                lower_ty(pty),
            )
        }

        // --- Managed-runtime / RC value-producing ops via the clean dialect ---
        IRExpr::Ctor { info, args } => emit_ctor(ctx, info, args, "obj.ctor"),

        IRExpr::Reuse { var, ctor, args } => {
            // The reused slot is a leading operand; the remaining operands are
            // the constructor fields.
            let slot = ctx.value_of(*var)?;
            let mut operands = vec![slot];
            for arg in args {
                if let IRArg::Var(_) = arg {
                    operands.push(ctx.value_of_arg(arg)?);
                }
            }
            emit_clean_value_with_ctor_attrs(ctx, "obj.reuse", operands, ctor, Ty::Ptr)
        }

        IRExpr::Reset(var) => {
            let obj = ctx.value_of(*var)?;
            emit_clean_value(ctx, "obj.reset", vec![obj], &[], Ty::Ptr)
        }

        IRExpr::Box { ty: bty, arg } => {
            let scalar = ctx.value_of_arg(arg)?;
            if let (RuntimeLowering::ExternCalls, Some(abi)) =
                (ctx.config.runtime_lowering, ctx.abi.clone())
            {
                return Ok(emit_box_extern(ctx, &abi, bty, scalar));
            }
            emit_clean_value(ctx, "obj.box", vec![scalar], &ty_attr(bty), Ty::Ptr)
        }

        IRExpr::Unbox { ty: uty, arg } => {
            let obj = ctx.value_of_arg(arg)?;
            if let (RuntimeLowering::ExternCalls, Some(abi)) =
                (ctx.config.runtime_lowering, ctx.abi.clone())
            {
                return Ok(emit_unbox_extern(ctx, &abi, uty, obj));
            }
            emit_clean_value(ctx, "obj.unbox", vec![obj], &ty_attr(uty), lower_ty(uty))
        }

        IRExpr::String(s) => {
            // ExternCalls mode: take the address of the literal's read-only byte
            // global (built in the string pre-pass) and build a managed string
            // with `clean_mk_string` — a real, runnable native call.
            if let (RuntimeLowering::ExternCalls, Some(abi)) =
                (ctx.config.runtime_lowering, ctx.abi.clone())
            {
                let gid = *ctx.string_globals.get(s).ok_or_else(|| {
                    TrustIrError::Unsupported(format!(
                        "string literal {s:?} missing from data-global pre-pass"
                    ))
                })?;
                let ptr = ctx.fb.global_addr(gid);
                return Ok(ctx.fb.call(abi.clean_mk_string, vec![ptr]));
            }
            // Dialect mode (no runtime): carry the bytes as a `clean.str.const`
            // op producing a managed string pointer.
            ensure_dialect(ctx)?;
            let op = DialectInst::new("clean", "str.const")
                .with_result_ty(Ty::Ptr)
                .with_attr("bytes", trust_ir::dialect::AttrValue::Str(s.clone()));
            single_result(ctx.fb.dialect_op(op))
        }

        // --- Closures: ExternCalls models them via the runtime; Dialect mode
        // (which has no runtime) still refuses them. ---
        IRExpr::PartialApply { fn_id, arity, args } => {
            if let (RuntimeLowering::ExternCalls, Some(abi)) =
                (ctx.config.runtime_lowering, ctx.abi.clone())
            {
                return emit_partial_apply_extern(ctx, &abi, fn_id, *arity, args);
            }
            Err(TrustIrError::Unsupported(format!(
                "PartialApply of `{}`: closures need ExternCalls mode (Dialect mode \
                 has no runtime to model the closure ABI)",
                fn_id.0
            )))
        }
        IRExpr::ClosureApply { closure, args } => {
            if let (RuntimeLowering::ExternCalls, Some(abi)) =
                (ctx.config.runtime_lowering, ctx.abi.clone())
            {
                return emit_closure_apply_extern(ctx, &abi, closure, args);
            }
            Err(TrustIrError::Unsupported(
                "ClosureApply: closures need ExternCalls mode (Dialect mode has no \
                 runtime to model dynamic application)"
                    .to_string(),
            ))
        }

        // `ty` is the declared result type for forms that do not otherwise need
        // it; named here to keep the signature honest without a warning.
        #[allow(unreachable_patterns)]
        _ => Err(TrustIrError::Unsupported(format!(
            "IRExpr variant not handled (declared type {ty:?})"
        ))),
    }
}

/// Lower an `Apply` whose callee is an in-slice user decl, aligning the
/// call-site arguments POSITIONALLY with the callee's lowered parameter list
/// (C2 erased-arity correctness).
///
/// L5IR `Apply` args are the full application spine of the call site, and the
/// callee decl's params are its definition's leading lambdas — so `args[i]`
/// binds `params[i]`, erased args included. Three consequences:
///
/// * An ERASED arg is **materialized** for its parameter slot (`ExternCalls`:
///   `clean_box_uint64(0)`, `emit_c`'s `clean_box(0)` parity; `Dialect`: a
///   `NullPtr` — no runtime exists to box with, and erased slots are never
///   inspected), never dropped. Dropping shifted every later argument one
///   slot left and changed the call's arity — the `And.symm`/`OfNat.ofNat`
///   miscompile class trust-ir's validator refused fail-closed.
/// * Args BEYOND the parameter list are OVER-application: the saturated call
///   returns the callee's result closure, and the extras are applied to it
///   via the runtime `clean_apply_N` — exactly the Lean/`emit_c` discipline
///   (`Functor.mapRev` calling the 2-param projection `Functor.map` with the
///   full 6-arg spine). Requires `ExternCalls` (the closure ABI) and a
///   `Ty::Ptr`-returning callee; anything else is refused fail-closed.
/// * UNDER-application of a known function without a `PartialApply` node has
///   no faithful lowering here and is refused fail-closed.
fn emit_apply_user(
    ctx: &mut FnCtx,
    name: &str,
    callee: FuncId,
    args: &[IRArg],
) -> Result<ValueId, TrustIrError> {
    // fn_ids and fn_shapes are populated together in pass 1, so a known callee
    // always has a shape; the refusal is defensive fail-closed anyway.
    let Some(shape) = ctx.fn_shapes.get(name) else {
        return Err(TrustIrError::UndefinedFunction(name.to_string()));
    };
    let n_params = shape.params.len();
    if args.len() < n_params {
        return Err(TrustIrError::Unsupported(format!(
            "call to `{name}` under-applies it ({} args for {n_params} params) \
             outside a PartialApply; no faithful lowering",
            args.len()
        )));
    }
    let returns_ptr = shape.returns_ptr;
    let (direct, extra) = args.split_at(n_params);

    // Saturated part: positional, erased args materialized per slot.
    let mut arg_vals = Vec::with_capacity(n_params);
    for (idx, (arg, param_ty)) in direct.iter().zip(shape.params.iter()).enumerate() {
        arg_vals.push(match arg {
            IRArg::Var(_) => ctx.value_of_arg(arg)?,
            IRArg::Erased => {
                if *param_ty != Ty::Ptr {
                    // An erased value has no scalar meaning; a non-pointer
                    // slot cannot faithfully receive one.
                    return Err(TrustIrError::Unsupported(format!(
                        "call to `{name}`: erased argument for non-pointer \
                         parameter slot {idx} ({param_ty:?})"
                    )));
                }
                erased_slot_value(ctx)
            }
        });
    }
    let result = ctx.fb.call(callee, arg_vals);
    if extra.is_empty() {
        return Ok(result);
    }

    // Over-application: apply the extras to the saturated call's result.
    if !returns_ptr {
        return Err(TrustIrError::Unsupported(format!(
            "call to `{name}` over-applies it ({} args for {n_params} params) \
             but the callee does not return a managed object to apply the rest to",
            args.len()
        )));
    }
    let Some(abi) = ctx.abi.clone() else {
        return Err(TrustIrError::Unsupported(format!(
            "call to `{name}` over-applies it ({} args for {n_params} params): \
             dynamic application needs ExternCalls mode (Dialect mode has no \
             runtime to model the closure ABI)",
            args.len()
        )));
    };
    let mut extra_vals = Vec::with_capacity(extra.len());
    for arg in extra {
        extra_vals.push(match arg {
            IRArg::Var(_) => ctx.value_of_arg(arg)?,
            IRArg::Erased => box_erased(ctx, &abi),
        });
    }
    emit_apply_runtime(ctx, &abi, result, extra_vals)
}

/// Materialize an erased argument for a `Ty::Ptr` parameter slot of an
/// in-slice callee: `ExternCalls` boxes a unit (`clean_box_uint64(0)`,
/// `emit_c`'s `clean_box(0)` parity — a valid managed pointer the callee may
/// even RC); `Dialect` mode has no runtime to box with and uses a `NullPtr`
/// (erased slots are never inspected; `Dialect` is the debug/round-trip
/// surface).
fn erased_slot_value(ctx: &mut FnCtx) -> ValueId {
    match (ctx.config.runtime_lowering, ctx.abi.clone()) {
        (RuntimeLowering::ExternCalls, Some(abi)) => box_erased(ctx, &abi),
        _ => ctx.fb.null_ptr(),
    }
}

/// Emit a constructor allocation as a `clean.<op>` dialect node.
fn emit_ctor(
    ctx: &mut FnCtx,
    info: &CtorInfo,
    args: &[IRArg],
    op: &str,
) -> Result<ValueId, TrustIrError> {
    let mut operands = Vec::with_capacity(args.len());
    for arg in args {
        if let IRArg::Var(_) = arg {
            operands.push(ctx.value_of_arg(arg)?);
        }
    }
    emit_clean_value_with_ctor_attrs(ctx, op, operands, info, Ty::Ptr)
}

/// Lower an `IRLiteral` to a constant SSA value.
fn emit_literal(ctx: &mut FnCtx, lit: &IRLiteral) -> ValueId {
    match lit {
        IRLiteral::Bool(b) => ctx.fb.bool_const(*b),
        IRLiteral::UInt8(v) => ctx.fb.iconst(Ty::U8, *v as i128),
        IRLiteral::UInt16(v) => ctx.fb.iconst(Ty::U16, *v as i128),
        IRLiteral::UInt32(v) => ctx.fb.iconst(Ty::U32, *v as i128),
        IRLiteral::UInt64(v) => ctx.fb.iconst(Ty::U64, *v as i128),
        IRLiteral::USize(v) => ctx.fb.iconst(Ty::U64, *v as i128),
        // A big Nat literal is an OBJECT (heap Nat), not a scalar const, and is
        // lowered at the `IRExpr::Lit` dispatch (via `clean_nat_big`) before this
        // scalar-only helper is ever reached.
        IRLiteral::NatBig(_) => {
            unreachable!("NatBig is lowered at the IRExpr::Lit dispatch, not emit_literal")
        }
        IRLiteral::Float32(v) => ctx.fb.fconst(Ty::F32, *v as f64),
        IRLiteral::Float64(v) => ctx.fb.fconst(Ty::F64, *v),
    }
}

/// Map an L5IR scalar/object type to a trust-ir `Ty`.
///
/// Objects, tagged objects, structs, unions, and erased values all become the
/// thin opaque pointer `Ty::Ptr`. `Void` becomes `Ty::Unit`.
fn lower_ty(ty: &IRType) -> Ty {
    match ty {
        IRType::Bool => Ty::Bool,
        IRType::UInt8 => Ty::U8,
        IRType::UInt16 => Ty::U16,
        IRType::UInt32 => Ty::U32,
        IRType::UInt64 => Ty::U64,
        IRType::USize => Ty::U64,
        IRType::Float32 => Ty::F32,
        IRType::Float64 => Ty::F64,
        IRType::Object
        | IRType::TObject
        | IRType::Struct(_)
        | IRType::Union(_)
        | IRType::Erased => Ty::Ptr,
        IRType::Void => Ty::Unit,
    }
}

/// The fixed-width UInt arithmetic primitives that lower to native trust-ir
/// `BinOp`s (P2 semantics-preservation fragment): `UInt{8,16,32,64}.{add,sub,
/// mul}` → wrapping `Add`/`Sub`/`Mul` at the matching unsigned width.
///
/// Deliberately EXCLUDED (fail through to `UndefinedFunction`, never guessed):
/// * `Nat.*` — Nat is arbitrary-precision (lowers to a runtime object); a
///   fixed-width BinOp would silently truncate.
/// * `USize.*` — host-pointer-width; a certificate over it would not be
///   target-stable.
/// * `.div` / `.mod` — division-by-zero has panic/runtime semantics that a
///   plain `UDiv`/`URem` BinOp does not model.
fn uint_arith_binop(name: &str) -> Option<(BinOp, Ty)> {
    let (prefix, suffix) = name.rsplit_once('.')?;
    let ty = match prefix {
        "UInt8" => Ty::U8,
        "UInt16" => Ty::U16,
        "UInt32" => Ty::U32,
        "UInt64" => Ty::U64,
        _ => return None,
    };
    let op = match suffix {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        _ => return None,
    };
    Some((op, ty))
}

/// The deterministic synthetic name of the native BOXED-entry wrapper for a
/// fixed-width UInt arithmetic primitive `p` (`UInt8.add` → the closure-ABI
/// entry that unboxes its two operands, applies the native wrapping `BinOp`,
/// and re-boxes the result). See [`synthesize_uint_arith_wrappers`].
fn uint_arith_wrapper_name(p: &str) -> String {
    format!("{p}.__clean_uint_arith_boxed")
}

/// The `IRType` of a [`uint_arith_binop`] primitive's operands/result, keyed
/// by the primitive's UInt-width prefix (mirrors that table's width arm).
fn uint_arith_ir_ty(p: &str) -> Option<IRType> {
    match p.rsplit_once('.')?.0 {
        "UInt8" => Some(IRType::UInt8),
        "UInt16" => Some(IRType::UInt16),
        "UInt32" => Some(IRType::UInt32),
        "UInt64" => Some(IRType::UInt64),
        _ => None,
    }
}

/// Collect the fixed-width UInt arithmetic primitives ([`uint_arith_binop`]
/// names) referenced as a function VALUE — a `PartialApply` closure or a 0-arg
/// `Apply` (#16 value reference) — anywhere in `body`, EXCLUDING names defined
/// in the slice (an in-slice decl of that name keeps its own body). A
/// saturated `Apply` (n≥1 args) is a direct call already lowered to the native
/// `BinOp` in place, so it is deliberately NOT collected.
fn collect_uint_value_refs(
    body: &IRBody,
    slice_names: &HashSet<String>,
    out: &mut BTreeSet<String>,
) {
    let mut note = |value: &IRExpr, out: &mut BTreeSet<String>| {
        let name = match value {
            IRExpr::PartialApply { fn_id, .. } => fn_id.0.to_string(),
            IRExpr::Apply { fn_id, args } if args.is_empty() => fn_id.0.to_string(),
            _ => return,
        };
        if !slice_names.contains(&name) && uint_arith_binop(&name).is_some() {
            out.insert(name);
        }
    };
    match body {
        IRBody::VDecl { value, rest, .. } => {
            note(value, out);
            collect_uint_value_refs(rest, slice_names, out);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            collect_uint_value_refs(jp_body, slice_names, out);
            collect_uint_value_refs(rest, slice_names, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_uint_value_refs(rest, slice_names, out),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_uint_value_refs(&alt.body, slice_names, out);
            }
            if let Some(d) = default {
                collect_uint_value_refs(d, slice_names, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Build a native BOXED-entry wrapper decl for every fixed-width UInt
/// arithmetic primitive referenced as a function VALUE (see
/// [`collect_uint_value_refs`]) but not defined in `decls`.
///
/// Without this, `instHAddUInt8 = HAdd.mk UInt8.add` lowers to a
/// `PartialApply { UInt8.add, 2, [] }` whose target has neither an in-slice
/// body nor a certified extern fallback (`uint_arith_binop` names are
/// deliberately kept out of the extern boundary — they are native BinOps, not
/// link-time symbols), so the closure resolves to nothing and the emit fails
/// `UndefinedFunction("UInt8.add")` (the 12 `instH{Add,Mul,Sub}UInt{8,16,32,
/// 64}` census stage-3 residue).
///
/// The synthesized wrapper is exactly the shape the boxing pass itself emits
/// for an in-slice `UInt8.add` (`l_UInt8_add___boxed`): unbox each of the two
/// boxed operands to the fixed width, apply the bare primitive — which, being
/// undefined as a user decl, takes the native wrapping `BinOp` path in
/// [`emit_expr`] — and re-box the result. It is a real, executable native
/// function (never a bodyless extern), so it is sound and interpreter-faithful
/// by construction. Fires only when the primitive is NOT an in-slice decl, so
/// no existing program (where the boxing pass already produced the wrapper)
/// changes shape.
fn synthesize_uint_arith_wrappers(decls: &[IRDecl]) -> Vec<IRDecl> {
    let slice_names: HashSet<String> = decls.iter().map(|d| d.name.to_string()).collect();
    let mut refs: BTreeSet<String> = BTreeSet::new();
    for d in decls {
        collect_uint_value_refs(&d.body, &slice_names, &mut refs);
    }
    let mut wrappers = Vec::new();
    for p in refs {
        let wname = uint_arith_wrapper_name(&p);
        // Defensive: never shadow an existing in-slice decl.
        if slice_names.contains(&wname) {
            continue;
        }
        let Some(ity) = uint_arith_ir_ty(&p) else {
            continue;
        };
        // fn <wrapper>(a: Object, b: Object) -> Object {
        //   let ua : ity    := Unbox{ity}(a);
        //   let ub : ity    := Unbox{ity}(b);
        //   dec a;                            -- Perceus: consume owned boxed arg
        //   dec b;                            -- Perceus: consume owned boxed arg
        //   let r  : ity    := <p>(ua, ub);   -- native wrapping BinOp
        //   let bx : Object := Box{ity}(r);
        //   ret bx
        // }
        //
        // PERCEUS OWNERSHIP (2026-07-12): the two `Object` params arrive OWNED —
        // `clean_apply_n` transfers arg ownership into the callee. `Unbox` only
        // READS the scalar out of the box; it does not consume it. Without the
        // two `dec`s a heap-boxed operand (a `UInt64 >= 2^63`, boxed via
        // `lean_box_uint64` into a real heap block) LEAKS +1 block per operand,
        // i.e. +2 per wrapper call. The `dec`s are placed AFTER both unboxes so
        // the scalars are already extracted, and they are sound for BOTH carrier
        // shapes: `clean_dec`/`lean_dec` is a no-op on a tagged immediate
        // (`v < 2^63`) and frees the heap block for a boxed `v >= 2^63`. Neither
        // box is ever forwarded, so nothing else can consume/alias it — no
        // double-free.
        let (a, b, ua, ub, r, bx) = (VarId(0), VarId(1), VarId(2), VarId(3), VarId(4), VarId(5));
        let body = IRBody::VDecl {
            var: ua,
            ty: ity.clone(),
            value: IRExpr::Unbox {
                ty: ity.clone(),
                arg: IRArg::Var(a),
            },
            rest: Box::new(IRBody::VDecl {
                var: ub,
                ty: ity.clone(),
                value: IRExpr::Unbox {
                    ty: ity.clone(),
                    arg: IRArg::Var(b),
                },
                rest: Box::new(IRBody::Dec {
                    var: a,
                    rest: Box::new(IRBody::Dec {
                        var: b,
                        rest: Box::new(IRBody::VDecl {
                            var: r,
                            ty: ity.clone(),
                            value: IRExpr::Apply {
                                fn_id: FnId(clean_kernel::Name::from_string(&p)),
                                args: vec![IRArg::Var(ua), IRArg::Var(ub)],
                            },
                            rest: Box::new(IRBody::VDecl {
                                var: bx,
                                ty: IRType::Object,
                                value: IRExpr::Box {
                                    ty: ity.clone(),
                                    arg: IRArg::Var(r),
                                },
                                rest: Box::new(IRBody::Ret(IRArg::Var(bx))),
                            }),
                        }),
                    }),
                }),
            }),
        };
        wrappers.push(IRDecl {
            name: clean_kernel::Name::from_string(&wname),
            params: vec![(a, IRType::Object), (b, IRType::Object)],
            return_type: IRType::Object,
            body,
        });
    }
    wrappers
}

/// The trust-ir `ICmpOp` a target-pinned `USize`/`UInt64` decision procedure
/// lowers to, or `None` if `decl` is not one of them.
///
/// SOUNDNESS FIX (2026-07-12) — the emit_trust_ir mirror of the emit_c
/// `usize_native_decision_op` fix. `USize`/`UInt64` `.decEq`/`.decLt`/`.decLe`
/// have no native lowering in `uint_arith_binop` (which handles only
/// `add`/`sub`/`mul`), so each is otherwise emitted with its generic L5IR body:
/// the operands are pushed through the runtime tagged-immediate box
/// `clean_box(v) = (v << 1) | 1` and compared as boxed Nats/BitVecs. That box
/// TRUNCATES for `v >= 2^63` (`2^63` and `0` both map to `1`), so the emitted
/// graph silently miscompiles at bit 63 — e.g. `decEq(2^63, 0)` computes
/// `true`. Confirmed on the trust-ir REFERENCE INTERPRETER: the faithful boxing
/// model returns `true` for `decEq(2^63, 0)`, the direct `icmp` returns the
/// correct `false`, and the real emitted graph routes through bodyless boxing
/// externs (uninterpretable in isolation).
///
/// `USize` and `UInt64` both lower to `Ty::U64` (`lower_ty`), and these
/// decision procedures are `(U64, U64) -> Bool`. The SOUND lowering is a DIRECT
/// trust-ir `ICmp` on the two `U64` operands — exactly the value the boxing
/// path was meant to compute, with no `clean_box` and no truncation across the
/// full 64-bit range. `decEq -> Eq`, `decLt -> Ult`, `decLe -> Ule` (unsigned,
/// since both carriers are unsigned). FAIL-CLOSED: fires only for the exact
/// 2×{`USize`|`UInt64`} -> `Bool` decision-procedure shape; any other decl (a
/// signed `IntN`, a `Nat`/boxed operand, a non-`Bool` result, a mis-arity)
/// keeps its generic body.
fn native_uint_decision_op(decl: &IRDecl) -> Option<ICmpOp> {
    // Both USize and UInt64 are pinned to a native u64 (`lower_ty`).
    fn is_u64_pinned(t: &IRType) -> bool {
        matches!(t, IRType::USize | IRType::UInt64)
    }
    if decl.params.len() != 2
        || !is_u64_pinned(&decl.params[0].1)
        || !is_u64_pinned(&decl.params[1].1)
        || decl.return_type != IRType::Bool
    {
        return None;
    }
    match decl.name.to_string().as_str() {
        "USize.decEq" | "UInt64.decEq" => Some(ICmpOp::Eq),
        "USize.decLt" | "UInt64.decLt" => Some(ICmpOp::Ult),
        "USize.decLe" | "UInt64.decLe" => Some(ICmpOp::Ule),
        _ => None,
    }
}

/// Compute the trust-ir return-type list for an L5IR return type.
///
/// `Void`/`Erased` returns produce no result values (a `ret` with no operands).
fn lower_ret_tys(ty: &IRType) -> Vec<Ty> {
    match ty {
        IRType::Void | IRType::Erased => vec![],
        other => vec![lower_ty(other)],
    }
}

/// Confirm the clean dialect is enabled, else refuse the op.
fn ensure_dialect(ctx: &FnCtx) -> Result<(), TrustIrError> {
    if ctx.config.use_clean_dialect {
        Ok(())
    } else {
        Err(TrustIrError::Unsupported(
            "managed-runtime op requires the `clean` dialect, which is disabled \
             by config"
                .to_string(),
        ))
    }
}

/// Structured fail-closed refusal for a managed op the `ExternCalls` runtime
/// ABI cannot express (e.g. a non-scalar `sproj`/`sset` — the scalar_get/set
/// symbol families are width-typed, so an object-typed field has no runtime
/// call form).
///
/// `ExternCalls` is dialect-free BY CONTRACT: trust-ir's lowering-target
/// subset v1 producer notes (ratified 2026-07-04) name the silent
/// `clean.obj.sproj`/`clean.obj.sset` fallback as the mode's one
/// out-of-subset leak and sanction exactly this refusal — a handoff module
/// must fail closed here, never quietly degrade to an out-of-subset
/// `clean.*` `DialectOp` that trust-cg cannot lower.
fn no_extern_lowering(op: &str) -> TrustIrError {
    TrustIrError::Unsupported(format!(
        "clean.{op} has no ExternCalls runtime-call lowering for this form (non-scalar \
         field access?); ExternCalls is dialect-free by contract, so the clean-dialect \
         fallback is refused fail-closed"
    ))
}

/// Emit a `clean.<op>` dialect node producing exactly one value of `result_ty`.
fn emit_clean_value(
    ctx: &mut FnCtx,
    op: &str,
    operands: Vec<ValueId>,
    attrs: &[(&str, u64)],
    result_ty: Ty,
) -> Result<ValueId, TrustIrError> {
    if ctx.config.runtime_lowering == RuntimeLowering::ExternCalls {
        if let Some(abi) = ctx.abi.clone() {
            if let Some(v) = emit_clean_value_extern(ctx, &abi, op, &operands, attrs, &result_ty)? {
                return Ok(v);
            }
        }
        return Err(no_extern_lowering(op));
    }
    ensure_dialect(ctx)?;
    let mut inst = DialectInst::new("clean", op).with_result_ty(result_ty);
    for operand in operands {
        inst = inst.with_operand(operand);
    }
    for (k, v) in attrs {
        inst = inst.with_attr(*k, trust_ir::dialect::AttrValue::U64(*v));
    }
    single_result(ctx.fb.dialect_op(inst))
}

/// Emit a `clean.<op>` dialect node that produces no result value.
fn emit_clean_void(
    ctx: &mut FnCtx,
    op: &str,
    operands: Vec<ValueId>,
    attrs: &[(&str, u64)],
) -> Result<(), TrustIrError> {
    if ctx.config.runtime_lowering == RuntimeLowering::ExternCalls {
        if let Some(abi) = ctx.abi.clone() {
            if emit_clean_void_extern(ctx, &abi, op, &operands, attrs)? {
                return Ok(());
            }
        }
        return Err(no_extern_lowering(op));
    }
    ensure_dialect(ctx)?;
    let mut inst = DialectInst::new("clean", op);
    for operand in operands {
        inst = inst.with_operand(operand);
    }
    for (k, v) in attrs {
        inst = inst.with_attr(*k, trust_ir::dialect::AttrValue::U64(*v));
    }
    // No result_tys => dialect_op allocates zero values.
    let _ = ctx.fb.dialect_op(inst);
    Ok(())
}

/// Emit a `clean.<op>` carrying constructor metadata as attributes.
fn emit_clean_value_with_ctor_attrs(
    ctx: &mut FnCtx,
    op: &str,
    operands: Vec<ValueId>,
    info: &CtorInfo,
    result_ty: Ty,
) -> Result<ValueId, TrustIrError> {
    if ctx.config.runtime_lowering == RuntimeLowering::ExternCalls {
        if let Some(abi) = ctx.abi.clone() {
            if let Some(v) = emit_ctor_extern(ctx, &abi, op, &operands, info)? {
                return Ok(v);
            }
        }
        return Err(no_extern_lowering(op));
    }
    ensure_dialect(ctx)?;
    let mut inst = DialectInst::new("clean", op).with_result_ty(result_ty);
    for operand in operands {
        inst = inst.with_operand(operand);
    }
    inst = inst
        .with_attr("tag", trust_ir::dialect::AttrValue::U64(info.tag as u64))
        .with_attr(
            "num_objects",
            trust_ir::dialect::AttrValue::U64(info.num_objects as u64),
        )
        .with_attr(
            "scalar_size",
            trust_ir::dialect::AttrValue::U64(info.scalar_size() as u64),
        );
    single_result(ctx.fb.dialect_op(inst))
}

/// Look up a `u64` attribute by key (0 if absent).
fn attr_u64(attrs: &[(&str, u64)], key: &str) -> u64 {
    attrs
        .iter()
        .find(|(k, _)| *k == key)
        .map(|&(_, v)| v)
        .unwrap_or(0)
}

/// `ExternCalls` lowering of a value-producing `clean.*` op to a runtime
/// `Inst::Call`. Returns `Ok(None)` for forms the runtime ABI cannot express
/// (e.g. a non-scalar `sproj`), which the caller then refuses fail-closed
/// ([`no_extern_lowering`]) — ExternCalls never falls back to the dialect.
fn emit_clean_value_extern(
    ctx: &mut FnCtx,
    abi: &RuntimeAbi,
    op: &str,
    operands: &[ValueId],
    attrs: &[(&str, u64)],
    result_ty: &Ty,
) -> Result<Option<ValueId>, TrustIrError> {
    let obj = match operands.first().copied() {
        Some(o) => o,
        None => return Ok(None),
    };
    let v = match op {
        "obj.tag" => {
            // clean_obj_tag returns U8; the op's contract (and `switch`
            // scrutinee) is U32, so zero-extend.
            let t = ctx.fb.call(abi.clean_obj_tag, vec![obj]);
            ctx.fb.zext(Ty::U8, Ty::U32, t)
        }
        "obj.proj" => {
            let idx = ctx.fb.iconst(Ty::U64, attr_u64(attrs, "idx") as i128);
            ctx.fb.call(abi.clean_ctor_get, vec![obj, idx])
        }
        "obj.uproj" => {
            let idx = ctx.fb.iconst(Ty::U32, attr_u64(attrs, "idx") as i128);
            ctx.fb.call(abi.clean_ctor_get_usize, vec![obj, idx])
        }
        "obj.sproj" => {
            let w = match RuntimeAbi::scalar_width(result_ty) {
                Some(w) => w,
                None => return Ok(None),
            };
            let byte_off = 8 * attr_u64(attrs, "n") + attr_u64(attrs, "offset");
            let off = ctx.fb.iconst(Ty::U32, byte_off as i128);
            ctx.fb.call(abi.scalar_get[w.idx()], vec![obj, off])
        }
        "obj.reset" => ctx.fb.call(abi.clean_reset, vec![obj]),
        // obj.box / obj.unbox are handled in their `IRExpr` arms (they need the
        // L5IR scalar type for width-correct dispatch + casts).
        _ => return Ok(None),
    };
    Ok(Some(v))
}

/// `ExternCalls` lowering of `Box`: widen the scalar to the runtime symbol's
/// parameter width, then call the matching **out-of-line** `clean_box_*` (so
/// the emitted object links against the Clean runtime without needing shims for
/// the header's `static inline clean_box`).
fn emit_box_extern(ctx: &mut FnCtx, abi: &RuntimeAbi, bty: &IRType, scalar: ValueId) -> ValueId {
    match bty {
        IRType::Float64 => ctx.fb.call(abi.clean_box_float, vec![scalar]),
        IRType::Float32 => {
            let d = ctx.fb.cast(CastOp::FPExt, Ty::F32, Ty::F64, scalar);
            ctx.fb.call(abi.clean_box_float, vec![d])
        }
        IRType::UInt64 | IRType::USize => ctx.fb.call(abi.clean_box_uint64, vec![scalar]),
        IRType::UInt32 => ctx.fb.call(abi.clean_box_uint32, vec![scalar]),
        IRType::UInt16 => {
            let w = ctx.fb.zext(Ty::U16, Ty::U32, scalar);
            ctx.fb.call(abi.clean_box_uint32, vec![w])
        }
        IRType::UInt8 => {
            let w = ctx.fb.zext(Ty::U8, Ty::U32, scalar);
            ctx.fb.call(abi.clean_box_uint32, vec![w])
        }
        IRType::Bool => {
            // trust-ir casts are integer<->integer; `Bool` is not an integer
            // type, so `zext bool -> u32` is INVALID IR (C2: the validator
            // refused it fail-closed). Widen with the proven Bool bridge
            // instead: a `select` over integer constants — the dual of the
            // `IsShared` Bool inverter.
            let one = ctx.fb.iconst(Ty::U32, 1);
            let zero = ctx.fb.iconst(Ty::U32, 0);
            let w = ctx.fb.select(Ty::U32, scalar, one, zero);
            ctx.fb.call(abi.clean_box_uint32, vec![w])
        }
        // C2b: an ERASED (or void) payload carries no runtime information —
        // its carrier SSA value is whatever placeholder the body materialized
        // (`PEmpty.elim`'s lifted motive lambda: a raw u64 from
        // `Lit(USize(0))` bound at type `Erased`), so passing it through
        // unboxed leaks a scalar into object position (the census
        // `return type mismatch: expected ptr, got u64` refusal). Box the
        // canonical erased unit instead — `clean_box_uint64(0)`, the same
        // convention closure captures use ([`box_erased`]).
        IRType::Erased | IRType::Void => box_erased(ctx, abi),
        // Non-scalar (already a managed pointer): nothing to box.
        _ => scalar,
    }
}

/// C2b: align a returned SSA value's representation with the decl's lowered
/// return type — the return-position mirror of C2's call-side alignment.
///
/// After `explicit_boxing` the declared type of a returned var normally
/// matches the declared return type, so this is a fail-closed belt for IR
/// that reaches the emitter without that reconciliation (direct
/// `emit_trust_ir*` API users, hand-built decls) and for the C4
/// `Object`-defaulted signatures:
///
/// * declared types agree (same lowered `Ty`) → return as-is;
/// * unboxed scalar returned where the signature says `Ptr` → re-box with the
///   runtime's tagged `clean_box` convention ([`box_scalar_tagged`], the same
///   discipline C2 uses for object-typed scalar-carrier projections); Dialect
///   mode carries the same fix as a `clean.obj.box` op;
/// * any other shape (object returned at a scalar signature, cross-width
///   scalars) has no faithful lowering → refuse, never emit invalid IR.
fn align_return_value(ctx: &mut FnCtx, var: VarId, val: ValueId) -> Result<ValueId, TrustIrError> {
    let sig_ret = lower_ret_tys(&ctx.ret_ty);
    // Void/Erased signature: `ret` carries no operands; arity is checked by
    // the validator (pre-existing class, unchanged here).
    let [want] = sig_ret.as_slice() else {
        return Ok(val);
    };
    // No declared type recorded for the var (defensive): emit as-is; the
    // trust-ir validator remains the backstop.
    let Some(var_ty) = ctx.var_tys.get(&var).cloned() else {
        return Ok(val);
    };
    if lower_ty(&var_ty) == *want {
        return Ok(val);
    }
    if var_ty.is_scalar() && *want == Ty::Ptr {
        if let (RuntimeLowering::ExternCalls, Some(abi)) =
            (ctx.config.runtime_lowering, ctx.abi.clone())
        {
            return Ok(box_scalar_tagged(ctx, &abi, &var_ty, val));
        }
        return emit_clean_value(ctx, "obj.box", vec![val], &ty_attr(&var_ty), Ty::Ptr);
    }
    Err(TrustIrError::Unsupported(format!(
        "return of a `{var_ty:?}`-typed value where the declared return type \
         is {:?} ({want:?}): only a same-representation return or a \
         scalar-into-object re-boxing is faithful",
        ctx.ret_ty
    )))
}

/// Box an unboxed scalar CARRIER as a managed object with the runtime's
/// tagged-pointer convention (`clean_box`), for C2 newtype-style projections
/// whose declared result is an object (`UInt{8,16,32,64}/USize.toBitVec`
/// projecting the runtime-`Nat` bitvec out of the scalar; `Char.valid`
/// projecting an erased proof).
///
/// `clean_box` (not `clean_box_uintN`) because the projected field's runtime
/// representation is a `Nat`, and the Clean runtime's `Nat` convention IS the
/// tagged immediate — the same `clean_box`/`clean_unbox` every `Nat` shim
/// uses (`l_Nat_add` et al.). For a `U64`/`USize` carrier the top bit is
/// truncated by the tag, exactly as it is everywhere else this runtime
/// handles `Nat`. Floats keep the runtime's boxed-double convention.
fn box_scalar_tagged(
    ctx: &mut FnCtx,
    abi: &RuntimeAbi,
    carrier: &IRType,
    scalar: ValueId,
) -> ValueId {
    match carrier {
        IRType::Float64 | IRType::Float32 => emit_box_extern(ctx, abi, carrier, scalar),
        IRType::Bool => {
            let one = ctx.fb.iconst(Ty::U64, 1);
            let zero = ctx.fb.iconst(Ty::U64, 0);
            let w = ctx.fb.select(Ty::U64, scalar, one, zero);
            ctx.fb.call(abi.clean_box, vec![w])
        }
        IRType::UInt8 | IRType::UInt16 | IRType::UInt32 => {
            let w = ctx.fb.zext(lower_ty(carrier), Ty::U64, scalar);
            ctx.fb.call(abi.clean_box, vec![w])
        }
        // U64-lowering carriers (`UInt64`/`USize`): a `Nat` carrier whose value
        // may reach bit 63, which the tagged `clean_box` `(v<<1)|1` would
        // truncate (`UInt64.toNat(2^63)` -> 0). Route through the sound
        // `clean_nat_of_u64` producer (RUNG B): tagged below 2^63, a heap Nat
        // cell at or above it. The UInt8/16/32 carriers above are always < 2^63,
        // so their tagged `clean_box` stays exact.
        IRType::UInt64 | IRType::USize => ctx.fb.call(abi.clean_nat_of_u64, vec![scalar]),
        _ => ctx.fb.call(abi.clean_box, vec![scalar]),
    }
}

/// Fail-closed refusal for a projection out of an unboxed scalar carrier
/// whose declared result type does not match the carrier's width (C2): the
/// carrier is the single runtime field, so any other shape has no faithful
/// lowering — refusing beats emitting the invalid `clean_ctor_get*`-on-scalar
/// call this class used to produce.
fn scalar_carrier_mismatch(op: &str, carrier: &IRType, declared: &IRType) -> TrustIrError {
    TrustIrError::Unsupported(format!(
        "clean.obj.{op} out of an unboxed scalar carrier ({carrier:?}) with \
         mismatched result type {declared:?}: the carrier is the single \
         runtime field, so only a same-width (identity) or object-typed \
         (re-boxing) projection is faithful"
    ))
}

/// `ExternCalls` lowering of `Unbox`: call the matching `clean_unbox*`, then
/// narrow back to the L5IR scalar width.
fn emit_unbox_extern(ctx: &mut FnCtx, abi: &RuntimeAbi, uty: &IRType, obj: ValueId) -> ValueId {
    match uty {
        IRType::Float64 => ctx.fb.call(abi.clean_unbox_float, vec![obj]),
        IRType::Float32 => {
            let d = ctx.fb.call(abi.clean_unbox_float, vec![obj]);
            ctx.fb.cast(CastOp::FPTrunc, Ty::F64, Ty::F32, d)
        }
        IRType::UInt64 | IRType::USize => ctx.fb.call(abi.clean_unbox_uint64, vec![obj]),
        IRType::UInt32 => ctx.fb.call(abi.clean_unbox_uint32, vec![obj]),
        IRType::UInt16 => {
            let w = ctx.fb.call(abi.clean_unbox, vec![obj]);
            ctx.fb.trunc(Ty::U64, Ty::U16, w)
        }
        IRType::UInt8 => {
            let w = ctx.fb.call(abi.clean_unbox, vec![obj]);
            ctx.fb.trunc(Ty::U64, Ty::U8, w)
        }
        IRType::Bool => {
            let w = ctx.fb.call(abi.clean_unbox, vec![obj]);
            let zero = ctx.fb.iconst(Ty::U64, 0);
            ctx.fb.icmp(ICmpOp::Ne, Ty::U64, w, zero)
        }
        _ => ctx.fb.call(abi.clean_unbox, vec![obj]),
    }
}

/// `ExternCalls` lowering of `SSet`: store a scalar field via the width-typed
/// `clean_ctor_set_scalar`. Returns `false` if `sty` is not a scalar.
fn emit_sset_extern(
    ctx: &mut FnCtx,
    abi: &RuntimeAbi,
    sty: &IRType,
    obj: ValueId,
    byte_off: u64,
    val: ValueId,
) -> bool {
    match RuntimeAbi::scalar_width(&lower_ty(sty)) {
        Some(w) => {
            let off = ctx.fb.iconst(Ty::U32, byte_off as i128);
            ctx.fb
                .call_void(abi.scalar_set[w.idx()], vec![obj, off, val]);
            true
        }
        None => false,
    }
}

/// `ExternCalls` lowering of a void `clean.*` op. Returns `true` if handled,
/// `false` for forms the runtime ABI cannot express, which the caller then
/// refuses fail-closed ([`no_extern_lowering`]).
fn emit_clean_void_extern(
    ctx: &mut FnCtx,
    abi: &RuntimeAbi,
    op: &str,
    operands: &[ValueId],
    attrs: &[(&str, u64)],
) -> Result<bool, TrustIrError> {
    let obj = match operands.first().copied() {
        Some(o) => o,
        None => return Ok(false),
    };
    match op {
        // rc.inc / rc.dec / rc.is_shared no longer reach here: Perceus RC ops
        // are native trust-ir ARC instructions in every mode (see the
        // `IRBody::Inc`/`Dec` and `IRExpr::IsShared` arms).
        "obj.set" => {
            let val = match operands.get(1).copied() {
                Some(v) => v,
                None => return Ok(false),
            };
            let idx = ctx.fb.iconst(Ty::U64, attr_u64(attrs, "idx") as i128);
            ctx.fb.call_void(abi.clean_ctor_set, vec![obj, idx, val]);
        }
        "obj.uset" => {
            let val = match operands.get(1).copied() {
                Some(v) => v,
                None => return Ok(false),
            };
            let idx = ctx.fb.iconst(Ty::U32, attr_u64(attrs, "idx") as i128);
            ctx.fb
                .call_void(abi.clean_ctor_set_usize, vec![obj, idx, val]);
        }
        "obj.set_tag" => {
            let tag = ctx.fb.iconst(Ty::U8, attr_u64(attrs, "tag") as i128);
            ctx.fb.call_void(abi.clean_ctor_set_tag, vec![obj, tag]);
        }
        // obj.sset reaches here only for a NON-scalar field (the scalar case
        // was handled by `emit_sset_extern` at the `IRBody::SSet` site); the
        // caller refuses it fail-closed rather than falling back to the dialect.
        _ => return Ok(false),
    }
    Ok(true)
}

/// `ExternCalls` lowering of `Ctor` / `Reuse` to `clean_alloc_ctor` /
/// `clean_reuse` (or `clean_box` for a fully-scalarless nullary ctor).
fn emit_ctor_extern(
    ctx: &mut FnCtx,
    abi: &RuntimeAbi,
    op: &str,
    operands: &[ValueId],
    info: &CtorInfo,
) -> Result<Option<ValueId>, TrustIrError> {
    let v = match op {
        "obj.ctor" => {
            if operands.is_empty() && info.scalar_size() == 0 {
                let tag = ctx.fb.iconst(Ty::U64, info.tag as i128);
                ctx.fb.call(abi.clean_box, vec![tag])
            } else {
                let tag = ctx.fb.iconst(Ty::U32, info.tag as i128);
                let nobj = ctx.fb.iconst(Ty::U32, info.num_objects as i128);
                let scalar = ctx.fb.iconst(Ty::U32, info.scalar_size() as i128);
                let mut args = vec![tag, nobj, scalar];
                args.extend_from_slice(operands);
                ctx.fb.call(abi.clean_alloc_ctor, args)
            }
        }
        "obj.reuse" => {
            let (slot, fields) = match operands.split_first() {
                Some((s, f)) => (*s, f),
                None => return Ok(None),
            };
            let tag = ctx.fb.iconst(Ty::U32, info.tag as i128);
            let nobj = ctx.fb.iconst(Ty::U32, info.num_objects as i128);
            let scalar = ctx.fb.iconst(Ty::U32, info.scalar_size() as i128);
            let mut args = vec![slot, tag, nobj, scalar];
            args.extend_from_slice(fields);
            ctx.fb.call(abi.clean_reuse, args)
        }
        _ => return Ok(None),
    };
    Ok(Some(v))
}

/// Box an erased argument as `clean_box_uint64(0)` (an out-of-line symbol) so
/// closure captures keep a valid managed pointer in every slot.
fn box_erased(ctx: &mut FnCtx, abi: &RuntimeAbi) -> ValueId {
    let z = ctx.fb.iconst(Ty::U64, 0);
    ctx.fb.call(abi.clean_box_uint64, vec![z])
}

/// `ExternCalls` lowering of `PartialApply` -> `clean_alloc_closure(fn, arity,
/// num_fixed, captured...)`. The function address is materialized via `fn_addr`
/// (`Ty::Func`) and bitcast to `Ty::Ptr` so it matches the runtime parameter.
fn emit_partial_apply_extern(
    ctx: &mut FnCtx,
    abi: &RuntimeAbi,
    fn_id: &FnId,
    arity: u16,
    args: &[IRArg],
) -> Result<ValueId, TrustIrError> {
    let name = fn_id.0.to_string();
    // In-slice callees first; a DROPPED callee closes over its certified
    // extern fallback declaration (C4: e.g. `Iff.symm`'s `PartialApply` of
    // `Iff.mpr`) — the pre-pass only declares it when every reference agreed
    // on the arity, so a declared-arity mismatch here is refused defensively.
    let callee = match ctx.fn_ids.get(&name) {
        Some(&id) => id,
        None => match ctx.extern_fallbacks.get(&name) {
            Some(&(id, declared_arity)) => {
                if declared_arity != arity as usize {
                    return Err(TrustIrError::Unsupported(format!(
                        "PartialApply of dropped callee `{name}` with arity \
                         {arity}, but its certified extern signature has \
                         arity {declared_arity}"
                    )));
                }
                id
            }
            // A fixed-width UInt arithmetic primitive referenced as a closure
            // value (`instHAddUInt8`'s `HAdd.mk UInt8.add`): close over its
            // synthesized native boxed-entry wrapper (unbox → native wrapping
            // BinOp → box) instead of refusing. The pre-pass
            // ([`synthesize_uint_arith_wrappers`]) guarantees the wrapper is
            // in-slice whenever the reference exists.
            None => match ctx.fn_ids.get(&uint_arith_wrapper_name(&name)) {
                Some(&wid) => wid,
                None => return Err(TrustIrError::UndefinedFunction(name.clone())),
            },
        },
    };
    // Materialize the callee's address with the runtime's canonical closure
    // fn-type, which is exactly `clean_alloc_closure`'s `fn` parameter type — so
    // it type-checks with no bitcast.
    //
    // KNOWN ISSUE: passing this `fn_addr` (`GlobalRef`) value as a call argument
    // hits a trust-cg call-arg parallel-move bug that drops the move of the
    // function-address into its argument register, so the runtime receives a
    // NULL fn and `clean_invoke` segfaults at run time. The emitted trust-ir is
    // valid and trust-cg compiles it; the fix belongs in trust-cg's call-arg
    // register assignment. Laundering through alloca/store/load does NOT help
    // (trust-cg folds it away), so it is left as the direct, correct lowering.
    let fn_ptr = ctx.fb.fn_addr(abi.clean_fn_ty, callee);
    let arity_c = ctx.fb.iconst(Ty::U32, arity as i128);
    let nfixed_c = ctx.fb.iconst(Ty::U32, args.len() as i128);
    let mut call_args = vec![fn_ptr, arity_c, nfixed_c];
    for a in args {
        let v = match a {
            IRArg::Var(_) => ctx.value_of_arg(a)?,
            IRArg::Erased => box_erased(ctx, abi),
        };
        call_args.push(v);
    }
    Ok(ctx.fb.call(abi.clean_alloc_closure, call_args))
}

/// `ExternCalls` lowering of `ClosureApply` -> `clean_apply_<n>(closure, a..)`
/// for n in 0..=18 (the specialized runtime entry points). See
/// [`emit_apply_runtime`] for why n>18 is refused fail-closed.
fn emit_closure_apply_extern(
    ctx: &mut FnCtx,
    abi: &RuntimeAbi,
    closure: &IRArg,
    args: &[IRArg],
) -> Result<ValueId, TrustIrError> {
    let clo = ctx.value_of_arg(closure)?;
    let mut arg_vals = Vec::with_capacity(args.len());
    for a in args {
        let v = match a {
            IRArg::Var(_) => ctx.value_of_arg(a)?,
            IRArg::Erased => box_erased(ctx, abi),
        };
        arg_vals.push(v);
    }
    emit_apply_runtime(ctx, abi, clo, arg_vals)
}

/// Emit a dynamic application of already-resolved argument values to a closure
/// `clean_obj*`, via the Clean runtime's `clean_apply_*` family.
///
/// n in 0..=32 -> positional `clean_apply_<n>(closure, a1, .., an)` (the
/// specialized fast-path entry points, matching `emit_c`'s dispatch range and
/// the R3-UAF-fixed ownership contract: the callee consumes each forwarded
/// arg; captures are forwarded by `clean_apply_consume_closure`).
///
/// n > 32 is refused **fail-closed**. It is NOT the specialized-wrapper gap
/// (the runtime has `clean_apply_n(closure, n, args)`); it is the runtime's
/// `clean_invoke` saturating-arity ceiling. `clean_invoke` dispatches
/// positionally only up to arity 32 (`default => clean_panic("arity exceeds
/// maximum supported (32)")` — a fixed-arity call cannot be spelled
/// variadically on AArch64/SysV, so each arity needs a concrete cast). The
/// 20/21 rung is exactly the shape the wide algebraic-hierarchy eliminators
/// emit (`DivisionRing.casesOn`/`recOn` apply a bare arity-20 minor-premise
/// closure, `Field.casesOn`/`recOn` arity 21), now emittable since the runtime
/// raised the `clean_invoke` ceiling to 32. A >32-arg apply that SATURATES its
/// closure would call `clean_invoke(fn, >32, ..)` and panic, so it stays
/// refused until the runtime raises the ceiling further. Kept in lockstep with
/// `to_lcnf`'s `MAX_RUNTIME_APPLY_ARGS`.
fn emit_apply_runtime(
    ctx: &mut FnCtx,
    abi: &RuntimeAbi,
    closure: ValueId,
    args: Vec<ValueId>,
) -> Result<ValueId, TrustIrError> {
    let n = args.len();
    if n > 32 {
        return Err(TrustIrError::Unsupported(format!(
            "ClosureApply with {n} args (>32): a saturating apply would call \
             clean_invoke at arity {n}, but the runtime's clean_invoke caps \
             saturating arity at 32 — refused fail-closed"
        )));
    }
    let mut call = Vec::with_capacity(n + 1);
    call.push(closure);
    call.extend(args);
    Ok(ctx.fb.call(abi.apply[n], call))
}

/// Build a single-`U64` type attribute list for box/unbox ops.
fn ty_attr(ty: &IRType) -> Vec<(&'static str, u64)> {
    vec![("scalar_bytes", ty.scalar_byte_size() as u64)]
}

/// Take exactly one result from a `dialect_op` invocation.
fn single_result(results: Vec<ValueId>) -> Result<ValueId, TrustIrError> {
    results.into_iter().next().ok_or_else(|| {
        TrustIrError::Unsupported("clean dialect op produced no result value".to_string())
    })
}

#[cfg(test)]
#[path = "emit_trust_ir_tests.rs"]
mod tests;

// Reference operational semantics for the Perceus reset/reuse discipline,
// modeled in core trust-ir ops and differentially checked with the reference
// interpreter (see the module docs for the honest boundary).
#[cfg(test)]
#[path = "perceus_reset_reuse_semantics_tests.rs"]
mod perceus_reset_reuse_semantics_tests;
