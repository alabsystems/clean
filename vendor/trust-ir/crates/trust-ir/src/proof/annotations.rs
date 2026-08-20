// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof annotations: [`ProofAnnotation`], the [`Divergence`] class, the
//! re-exported [`ProofTag`] custom tag, and the annotation classifier methods
//! (`is_memory_safety` / `is_arithmetic_safety` / `is_gpu_relevant` / etc.).

use crate::inst::Ordering;
use crate::value::ProofTag;

/// GPU thread-divergence class for a loop or function body.
///
/// TrustIr uses this to gate GPU eligibility. Uniform = all lanes take the
/// same path (ideal for GPU/ANE). Low = small, bounded divergence that GPU
/// hardware can tolerate via lane masking. High = unpredictable control
/// flow that disqualifies GPU execution under the default policy (TrustIr
/// will fall back to CPU or SIMD lanes).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Divergence {
    /// All GPU lanes execute the same control-flow path.
    /// Best case: no lane masking, maximum occupancy.
    Uniform,
    /// Minor divergence that hardware lane-masking absorbs cheaply.
    /// Safe for GPU execution; may reduce occupancy slightly.
    Low,
    /// Unpredictable control flow. Disqualifies GPU execution under the
    /// default conservative policy — TrustIr falls back to CPU/SIMD.
    High,
}

impl core::fmt::Display for Divergence {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Divergence::Uniform => "uniform",
            Divergence::Low => "low",
            Divergence::High => "high",
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofAnnotation {
    // Memory safety
    InBounds,
    NotNull,
    ValidBorrow,
    UniqueBorrow,
    SharedBorrow,
    ValidDealloc,

    // Arithmetic safety
    NoOverflow,
    NoWrap,
    DivNonZero,
    ShiftInRange,
    /// Modular (wrapping) integer arithmetic: wrap-around is the DEFINED
    /// result of this instruction (e.g. `wrapping_add`), not an error.
    ///
    /// Contrast `NoOverflow`/`NoWrap`, which CLAIM the operation never wraps
    /// and carry a dischargeable obligation. `Wrapping` is a semantic marker,
    /// not an obligation: it tells the verifier that no no-overflow obligation
    /// exists for this `BinOp` (two's-complement wrap is the intended value),
    /// so none should be generated or checked.
    Wrapping,

    // Functional correctness
    Pure,
    Terminates,
    Deterministic,
    Associative,
    Commutative,

    // Concurrency
    DataRaceFree,
    AtomicOrdering(Ordering),

    // Neural network bounds (gamma-crown)
    BoundedOutput {
        lo: f64,
        hi: f64,
    },
    Monotonic,

    // Aliasing
    /// Pointer does not alias any other pointer in scope.
    /// TrustIr uses this for cross-target register allocation and vectorization.
    NoAlias,
    /// Pointer is aligned to N bytes.
    /// TrustIr uses this for SIMD load/store synthesis.
    Aligned(u64),

    // Safety
    /// Function or instruction is panic-free.
    /// TrustIr requires this for GPU kernel synthesis (GPU has no unwinding).
    NoPanic,
    /// Value is not undef/poison.
    /// TrustIr requires this for translation validation.
    NoUndef,

    // Information flow (non-interference)
    /// This value derives from an untrusted source (e.g. PTY / network input)
    /// and must not reach a [`TrustedSink`](ProofAnnotation::TrustedSink)
    /// without an explicit declassify. The IR-level analog of
    /// aterm-provenance's `Origin::Pty` taint; lets `trust-ir-build` prove
    /// non-interference (no tainted value reaches a privileged sink).
    Tainted,
    /// This instruction is a privileged sink (spawn / exec / clipboard / fs /
    /// network) that must never consume a [`Tainted`](ProofAnnotation::Tainted)
    /// value. The non-interference obligation enforced by `trust-ir-build`.
    TrustedSink,

    // Memory role attributes (first-class GPU address-space hints)
    /// Immutable lookup table produced once and read many times.
    ///
    /// TrustIr lowering: Metal `constant` address space / NVPTX addrspace(4)
    /// (`.const`). Enables coalesced reads across the warp and frees the
    /// compiler from emitting memory barriers on the write path.
    ///
    /// Invariants TrustIr relies on:
    /// * The backing storage is not mutated after publication.
    /// * No aliasing writer exists in the same program.
    ReadonlyTable,
    /// Buffer that accepts appends but never overwrites existing entries.
    ///
    /// TrustIr lowering: Metal `device` address space / NVPTX addrspace(1)
    /// (`.global`). Appenders coordinate through an atomic bump-pointer
    /// but the tail is write-once, so readers do not need acquire fences
    /// for already-published slots.
    ///
    /// Invariants TrustIr relies on:
    /// * Writes extend the buffer monotonically.
    /// * Existing entries are immutable once published.
    AppendOnlyBuffer,
    /// Threadgroup-local set that supports concurrent atomic insertion
    /// with deduplication semantics.
    ///
    /// TrustIr lowering: Metal `threadgroup` address space / NVPTX
    /// addrspace(3) (`.shared`). Lives for the duration of a workgroup
    /// and is synchronised with threadgroup barriers; inserts compile to
    /// `atomic_compare_exchange_weak` or a `ballot`-backed reduction.
    ///
    /// Invariants TrustIr relies on:
    /// * Inserts are idempotent under the set's equivalence relation.
    /// * No cross-workgroup reads of the in-flight set.
    AtomicSetInsert,

    // Parallel / purity attributes
    /// Loop iterations are independent and may execute in any order, in
    /// parallel, or in a vectorised form.
    ///
    /// TrustIr uses this to authorise `parallel_for` lowering to Metal /
    /// NVPTX grids and to SIMD lanes on CPU fallbacks. Semantics: no
    /// loop-carried dependency, no ordering-sensitive side effects.
    ParallelMap,
    /// Loop iteration count is statically bounded by `n`.
    ///
    /// TrustIr uses this for GPU kernel synthesis (kernel launch needs a
    /// compile-time upper bound), for register allocation (spill budget
    /// tuning), and for loop unrolling heuristics.
    BoundedLoop(u64),
    /// GPU thread-divergence classification. Gates GPU eligibility:
    /// `Uniform` and `Low` are GPU-safe; `High` forces CPU/SIMD fallback.
    DivergenceClass(Divergence),

    /// Marks an [`Inst::Undef`](crate::Inst::Undef) whose consumer semantics are
    /// a fresh, unconstrained value.
    ///
    /// This marker is deliberately inert: it proves no proposition, authenticates
    /// no producer, and grants no authority to import constraints. It is public and
    /// survives binary serialization, so a proof-grade consumer may use it only to
    /// select an already-audited havoc interpretation that is an over-approximation
    /// of the producer operation. In particular, a consumer must independently
    /// reject or authenticate any `Assume`, pointer metadata, or other operation
    /// that could narrow the fresh value.
    FreshSymbolicHavoc,

    // Extensible
    Custom(ProofTag),

    // Proof-backed link (fast-1): this annotation occurrence is backed by a
    // discharged ProofObligation. A bare claim (e.g. NoOverflow) is unverified;
    // ProofRef(id) ties it to module proof state, which the validator requires
    // to be Discharged/Trusted.
    ProofRef(crate::value::ProofId),

    // Value facts (fast-3): claim-style optimization hints TrustCg consumes
    // (range strength-reduction, switch-table layout, known-bit folding). Like
    // the other annotations they are unverified claims unless paired with a
    // ProofRef to a discharged obligation.
    /// The annotated result's integer value lies in the inclusive range [lo, hi].
    ValueRange {
        #[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_i128"))]
        lo: i128,
        #[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_i128"))]
        hi: i128,
    },
    /// Known bits: `zeros` marks bits known to be 0, `ones` bits known to be 1.
    /// Well-formed iff `zeros & ones == 0` (no bit known both 0 and 1).
    KnownBits {
        #[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_u128"))]
        zeros: u128,
        #[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_u128"))]
        ones: u128,
    },
    /// Branch-weight codegen hint for a `CondBr` / `Switch` terminator node:
    /// relative execution frequencies of the outgoing edges, in the terminator's
    /// edge order. For `CondBr` that is `[taken, not_taken]`; for `Switch` it is
    /// the per-case weights followed by the default-edge weight (length
    /// `cases.len() + 1`). Like the other hints it is a claim TrustCg may use for
    /// block layout / register allocation; it carries no operational semantics
    /// (the reference interpreter ignores it) and no obligation.
    BranchWeights(Vec<u32>),

    // FUSION (design 2026-06-20-fusion-obligation-as-clean-expr): the
    // proposition this annotation discharges, carried as a Clean kernel
    // `Expr` and stamped at lowering. Subsumes the `ProofFormula` string and
    // the clean-reflect side-derivation: the goal IS the node's data, born
    // from the same fields that built the `Inst`. Boxed so the cheap-marker
    // case (NoOverflow, InBounds, ...) pays nothing. Feature-gated so the
    // default zero-dep trust-ir format build never sees clean-kernel.
    #[cfg(feature = "clean-expr")]
    Goal(Box<ExprObligation>),
}

/// An `Expr`-valued proof obligation resident ON a trust-ir node.
///
/// This is the fusion carrier: the obligation a node carries is LITERALLY a
/// `clean_kernel::Expr` — "Clean Expr = Trust type" — not a `ProofFormula`
/// string, not opaque bytes, not a side derivation in a bridge crate. It
/// mirrors `clean_kernel::vc_protocol::VcObligation` (`goal_type` +
/// `hypotheses`) so the kernel-native shape is the on-node shape.
///
/// The `goal` is kernel-checkable directly via `clean_kernel`'s
/// `TypeChecker::check_type(proof_term, &goal)` under
/// `Environment::with_prelude()` — the same gate `trust-certify` uses — with no
/// external `.lean` model.
#[cfg(feature = "clean-expr")]
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExprObligation {
    /// The proposition to prove, expressed in the Clean kernel's own AST.
    pub goal: clean_kernel::Expr,
    /// Node-sourced hypotheses (operand facts, guards), `VcHypothesis`-shaped:
    /// a name bound to its `Expr` type, pushed into the kernel `LocalContext`
    /// at discharge time.
    pub hypotheses: Vec<(String, clean_kernel::Expr)>,
}

#[cfg(feature = "clean-expr")]
impl ExprObligation {
    /// Construct an obligation from a goal and no hypotheses.
    #[must_use]
    pub fn new(goal: clean_kernel::Expr) -> Self {
        Self {
            goal,
            hypotheses: Vec::new(),
        }
    }

    /// Add a node-sourced hypothesis (operand fact / guard) to the obligation.
    #[must_use]
    pub fn with_hypothesis(mut self, name: impl Into<String>, ty: clean_kernel::Expr) -> Self {
        self.hypotheses.push((name.into(), ty));
        self
    }
}

impl ProofAnnotation {
    /// Stable variant name for coverage/corpus tooling.
    ///
    /// EXHAUSTIVE by design — no wildcard: a new `ProofAnnotation` variant
    /// must be named here (native cfg makes the feature-gated arms correct
    /// under every feature unification), which is the compile-time forcing
    /// function the conformance corpus coverage relies on. Keep it in sync
    /// with `trust-ir-conformance`'s `required_proof` list.
    pub fn kind_name(&self) -> &'static str {
        match self {
            ProofAnnotation::InBounds => "InBounds",
            ProofAnnotation::NotNull => "NotNull",
            ProofAnnotation::ValidBorrow => "ValidBorrow",
            ProofAnnotation::UniqueBorrow => "UniqueBorrow",
            ProofAnnotation::SharedBorrow => "SharedBorrow",
            ProofAnnotation::ValidDealloc => "ValidDealloc",
            ProofAnnotation::NoOverflow => "NoOverflow",
            ProofAnnotation::NoWrap => "NoWrap",
            ProofAnnotation::DivNonZero => "DivNonZero",
            ProofAnnotation::ShiftInRange => "ShiftInRange",
            ProofAnnotation::Wrapping => "Wrapping",
            ProofAnnotation::Pure => "Pure",
            ProofAnnotation::Terminates => "Terminates",
            ProofAnnotation::Deterministic => "Deterministic",
            ProofAnnotation::Associative => "Associative",
            ProofAnnotation::Commutative => "Commutative",
            ProofAnnotation::DataRaceFree => "DataRaceFree",
            ProofAnnotation::AtomicOrdering(_) => "AtomicOrdering",
            ProofAnnotation::BoundedOutput { .. } => "BoundedOutput",
            ProofAnnotation::Monotonic => "Monotonic",
            ProofAnnotation::NoAlias => "NoAlias",
            ProofAnnotation::Aligned(_) => "Aligned",
            ProofAnnotation::NoPanic => "NoPanic",
            ProofAnnotation::NoUndef => "NoUndef",
            ProofAnnotation::ReadonlyTable => "ReadonlyTable",
            ProofAnnotation::AppendOnlyBuffer => "AppendOnlyBuffer",
            ProofAnnotation::AtomicSetInsert => "AtomicSetInsert",
            ProofAnnotation::ParallelMap => "ParallelMap",
            ProofAnnotation::BoundedLoop(_) => "BoundedLoop",
            ProofAnnotation::DivergenceClass(_) => "DivergenceClass",
            ProofAnnotation::Custom(_) => "Custom",
            ProofAnnotation::ProofRef(_) => "ProofRef",
            ProofAnnotation::ValueRange { .. } => "ValueRange",
            ProofAnnotation::KnownBits { .. } => "KnownBits",
            ProofAnnotation::BranchWeights(_) => "BranchWeights",
            ProofAnnotation::Tainted => "Tainted",
            ProofAnnotation::TrustedSink => "TrustedSink",
            ProofAnnotation::FreshSymbolicHavoc => "FreshSymbolicHavoc",
            #[cfg(feature = "clean-expr")]
            ProofAnnotation::Goal(_) => "Goal",
        }
    }

    /// The [`ObligationKind`](crate::proof::ObligationKind) a *function-level*
    /// occurrence of this annotation gives rise to, or `None` when the
    /// annotation carries no dischargeable proof obligation.
    ///
    /// This is the mapping [`crate::Module::add_function`] uses to synthesize
    /// first-class proof-obligation table entries from a function's claims
    /// (roadmap §1.1 — obligation birth at construction, never a
    /// half-populated table). The kind assignment mirrors the claim⇄kind
    /// compatibility rule enforced by `trust_ir_build::validate`'s
    /// `proof_ref_kind_can_back`:
    ///
    /// * arithmetic-safety claims (`NoOverflow`, `NoWrap`, `DivNonZero`,
    ///   `ShiftInRange`) → [`ObligationKind::ArithmeticSafety`](crate::proof::ObligationKind::ArithmeticSafety)
    /// * `InBounds` → [`ObligationKind::BoundsCheck`](crate::proof::ObligationKind::BoundsCheck)
    ///   (a panic-freedom obligation, deliberately NOT `MemorySafety` — see the
    ///   `BoundsCheck` doc-comment)
    /// * the remaining memory-safety / aliasing / value-validity claims
    ///   (`NotNull`, `ValidBorrow`, `UniqueBorrow`, `SharedBorrow`,
    ///   `ValidDealloc`, `NoAlias`, `Aligned`, `NoUndef`) →
    ///   [`ObligationKind::MemorySafety`](crate::proof::ObligationKind::MemorySafety)
    /// * `NoPanic` → [`ObligationKind::PanicFreedom`](crate::proof::ObligationKind::PanicFreedom)
    /// * `Terminates` → [`ObligationKind::Liveness`](crate::proof::ObligationKind::Liveness)
    /// * `DataRaceFree` → [`ObligationKind::TemporalSafety`](crate::proof::ObligationKind::TemporalSafety)
    ///
    /// Everything else is `None`: semantic markers (`Wrapping`,
    /// `AtomicOrdering`), claim-style codegen/GPU/NN hints (`ValueRange`,
    /// `KnownBits`, `BranchWeights`, `BoundedLoop`, `DivergenceClass`,
    /// `ParallelMap`, memory-role hints, `BoundedOutput`, `Monotonic`),
    /// functional-property claims with no matching obligation kind (`Pure`,
    /// `Deterministic`, `Associative`, `Commutative`), information-flow labels
    /// (`Tainted`/`TrustedSink` — enforced module-wide by the validator, not
    /// per-function), back-references (`ProofRef`), and opaque tags (`Custom`).
    pub fn obligation_kind(&self) -> Option<crate::proof::ObligationKind> {
        use crate::proof::ObligationKind;
        match self {
            ProofAnnotation::NoOverflow
            | ProofAnnotation::NoWrap
            | ProofAnnotation::DivNonZero
            | ProofAnnotation::ShiftInRange => Some(ObligationKind::ArithmeticSafety),
            ProofAnnotation::InBounds => Some(ObligationKind::BoundsCheck),
            ProofAnnotation::NotNull
            | ProofAnnotation::ValidBorrow
            | ProofAnnotation::UniqueBorrow
            | ProofAnnotation::SharedBorrow
            | ProofAnnotation::ValidDealloc
            | ProofAnnotation::NoAlias
            | ProofAnnotation::Aligned(_)
            | ProofAnnotation::NoUndef => Some(ObligationKind::MemorySafety),
            ProofAnnotation::NoPanic => Some(ObligationKind::PanicFreedom),
            ProofAnnotation::Terminates => Some(ObligationKind::Liveness),
            ProofAnnotation::DataRaceFree => Some(ObligationKind::TemporalSafety),
            _ => None,
        }
    }

    /// Returns true if this annotation relates to memory safety.
    ///
    /// Memory safety annotations: InBounds, NotNull, ValidBorrow,
    /// UniqueBorrow, SharedBorrow, ValidDealloc.
    pub fn is_memory_safety(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::InBounds
                | ProofAnnotation::NotNull
                | ProofAnnotation::ValidBorrow
                | ProofAnnotation::UniqueBorrow
                | ProofAnnotation::SharedBorrow
                | ProofAnnotation::ValidDealloc
        )
    }

    /// Returns true if this annotation relates to arithmetic safety.
    ///
    /// Arithmetic safety annotations: NoOverflow, NoWrap, DivNonZero, ShiftInRange.
    pub fn is_arithmetic_safety(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::NoOverflow
                | ProofAnnotation::NoWrap
                | ProofAnnotation::DivNonZero
                | ProofAnnotation::ShiftInRange
        )
    }

    /// Returns true if this annotation relates to functional properties.
    ///
    /// Functional annotations: Pure, Terminates, Deterministic, Associative, Commutative.
    pub fn is_functional(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::Pure
                | ProofAnnotation::Terminates
                | ProofAnnotation::Deterministic
                | ProofAnnotation::Associative
                | ProofAnnotation::Commutative
        )
    }

    /// Returns true if this annotation is relevant for GPU/ANE/SIMD synthesis.
    ///
    /// TrustIr uses these annotations to determine which computations can be
    /// safely moved to GPU, ANE, or SIMD units. GPU-relevant annotations:
    /// Pure, InBounds, NoOverflow, Commutative, Associative, Deterministic,
    /// ValidBorrow, NoPanic, NoAlias, Aligned, all memory-role attributes
    /// (ReadonlyTable, AppendOnlyBuffer, AtomicSetInsert), ParallelMap,
    /// BoundedLoop, and DivergenceClass(Uniform | Low).
    ///
    /// DivergenceClass(High) is explicitly NOT GPU-relevant: it is a
    /// hazard marker that forces CPU/SIMD fallback.
    pub fn is_gpu_relevant(&self) -> bool {
        match self {
            ProofAnnotation::Pure
            | ProofAnnotation::InBounds
            | ProofAnnotation::NoOverflow
            | ProofAnnotation::Commutative
            | ProofAnnotation::Associative
            | ProofAnnotation::Deterministic
            | ProofAnnotation::ValidBorrow
            | ProofAnnotation::NoPanic
            | ProofAnnotation::NoAlias
            | ProofAnnotation::Aligned(_)
            | ProofAnnotation::ReadonlyTable
            | ProofAnnotation::AppendOnlyBuffer
            | ProofAnnotation::AtomicSetInsert
            | ProofAnnotation::ParallelMap
            | ProofAnnotation::BoundedLoop(_) => true,
            ProofAnnotation::DivergenceClass(d) => {
                matches!(d, Divergence::Uniform | Divergence::Low)
            }
            _ => false,
        }
    }

    /// Returns true if this annotation relates to concurrency properties.
    ///
    /// Concurrency annotations: DataRaceFree, AtomicOrdering, AtomicSetInsert.
    /// TrustIr uses these to determine safe concurrent access patterns
    /// during cross-target synthesis.
    pub fn is_concurrency(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::DataRaceFree
                | ProofAnnotation::AtomicOrdering(_)
                | ProofAnnotation::AtomicSetInsert
        )
    }

    /// Returns true if this annotation is a memory-role attribute.
    ///
    /// Memory role attributes declare the intended access pattern of a
    /// memory region so TrustIr can infer GPU address spaces without
    /// guessing. Variants: `ReadonlyTable`, `AppendOnlyBuffer`,
    /// `AtomicSetInsert`.
    pub fn is_memory_role(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::ReadonlyTable
                | ProofAnnotation::AppendOnlyBuffer
                | ProofAnnotation::AtomicSetInsert
        )
    }

    /// Returns true if this annotation relates to parallel-execution /
    /// iteration-bound / divergence properties.
    ///
    /// Parallel / purity annotations: `ParallelMap`, `BoundedLoop(_)`,
    /// `DivergenceClass(_)`. `Pure` is classified under `is_functional`
    /// rather than here.
    pub fn is_parallel(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::ParallelMap
                | ProofAnnotation::BoundedLoop(_)
                | ProofAnnotation::DivergenceClass(_)
        )
    }

    /// Returns true if this annotation relates to neural network verification.
    ///
    /// Neural network annotations: BoundedOutput, Monotonic.
    /// Used by gamma-crown integration for NN layer verification.
    pub fn is_neural_network(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::BoundedOutput { .. } | ProofAnnotation::Monotonic
        )
    }

    /// Returns true if this annotation relates to pointer aliasing.
    ///
    /// Aliasing annotations: NoAlias, ValidBorrow, UniqueBorrow, SharedBorrow.
    /// TrustIr uses these to determine safe pointer transformations during
    /// vectorization and cross-target register allocation.
    /// Obligation id this occurrence is backed by, if it is a `ProofRef`.
    pub fn backing_obligation(&self) -> Option<crate::value::ProofId> {
        match self {
            ProofAnnotation::ProofRef(id) => Some(*id),
            _ => None,
        }
    }

    /// True for fast-3 value-fact hints (`ValueRange` / `KnownBits`) — claim-style
    /// optimization metadata the backend may exploit.
    pub fn is_value_fact(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::ValueRange { .. } | ProofAnnotation::KnownBits { .. }
        )
    }

    /// True for the information-flow (non-interference) labels
    /// (`Tainted` / `TrustedSink`).
    pub fn is_information_flow(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::Tainted | ProofAnnotation::TrustedSink
        )
    }

    pub fn is_aliasing(&self) -> bool {
        matches!(
            self,
            ProofAnnotation::NoAlias
                | ProofAnnotation::ValidBorrow
                | ProofAnnotation::UniqueBorrow
                | ProofAnnotation::SharedBorrow
        )
    }
}

impl core::fmt::Display for ProofAnnotation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProofAnnotation::InBounds => f.write_str("in_bounds"),
            ProofAnnotation::NotNull => f.write_str("not_null"),
            ProofAnnotation::ValidBorrow => f.write_str("valid_borrow"),
            ProofAnnotation::UniqueBorrow => f.write_str("unique_borrow"),
            ProofAnnotation::SharedBorrow => f.write_str("shared_borrow"),
            ProofAnnotation::ValidDealloc => f.write_str("valid_dealloc"),
            ProofAnnotation::NoOverflow => f.write_str("no_overflow"),
            ProofAnnotation::NoWrap => f.write_str("no_wrap"),
            ProofAnnotation::DivNonZero => f.write_str("div_nonzero"),
            ProofAnnotation::ShiftInRange => f.write_str("shift_in_range"),
            ProofAnnotation::Wrapping => f.write_str("wrapping"),
            ProofAnnotation::Pure => f.write_str("pure"),
            ProofAnnotation::Terminates => f.write_str("terminates"),
            ProofAnnotation::Deterministic => f.write_str("deterministic"),
            ProofAnnotation::Associative => f.write_str("associative"),
            ProofAnnotation::Commutative => f.write_str("commutative"),
            ProofAnnotation::DataRaceFree => f.write_str("data_race_free"),
            ProofAnnotation::AtomicOrdering(ord) => write!(f, "atomic_ordering({ord})"),
            ProofAnnotation::BoundedOutput { lo, hi } => write!(f, "bounded_output({lo}, {hi})"),
            ProofAnnotation::Monotonic => f.write_str("monotonic"),
            ProofAnnotation::NoAlias => f.write_str("no_alias"),
            ProofAnnotation::Aligned(n) => write!(f, "aligned({n})"),
            ProofAnnotation::NoPanic => f.write_str("no_panic"),
            ProofAnnotation::NoUndef => f.write_str("no_undef"),
            ProofAnnotation::Tainted => f.write_str("tainted"),
            ProofAnnotation::TrustedSink => f.write_str("trusted_sink"),
            ProofAnnotation::FreshSymbolicHavoc => f.write_str("fresh_symbolic_havoc"),
            ProofAnnotation::ReadonlyTable => f.write_str("readonly_table"),
            ProofAnnotation::AppendOnlyBuffer => f.write_str("append_only_buffer"),
            ProofAnnotation::AtomicSetInsert => f.write_str("atomic_set_insert"),
            ProofAnnotation::ParallelMap => f.write_str("parallel_map"),
            ProofAnnotation::BoundedLoop(n) => write!(f, "bounded_loop({n})"),
            ProofAnnotation::DivergenceClass(d) => write!(f, "divergence_class({d})"),
            ProofAnnotation::ProofRef(id) => write!(f, "proof_ref({})", id.index()),
            ProofAnnotation::ValueRange { lo, hi } => write!(f, "value_range({lo},{hi})"),
            ProofAnnotation::KnownBits { zeros, ones } => write!(f, "known_bits({zeros},{ones})"),
            ProofAnnotation::BranchWeights(weights) => {
                f.write_str("branch_weights(")?;
                for (i, w) in weights.iter().enumerate() {
                    if i > 0 {
                        f.write_str(",")?;
                    }
                    write!(f, "{w}")?;
                }
                f.write_str(")")
            }
            ProofAnnotation::Custom(tag) => write!(f, "custom({})", tag.index()),
            #[cfg(feature = "clean-expr")]
            ProofAnnotation::Goal(ob) => {
                write!(f, "goal({} hyps)", ob.hypotheses.len())
            }
        }
    }
}

/// Category filters over a slice of [`ProofAnnotation`]s, shared by `Function`
/// and `InstrNode` so the per-category `*_proofs()` helpers have a single
/// implementation (previously duplicated across the two types, and drifted —
/// `Function` lacked the concurrency/aliasing filters). Each returns the
/// annotations in the slice whose corresponding `is_*` predicate holds.
pub trait ProofAnnotationFilters {
    fn memory_proofs(&self) -> Vec<&ProofAnnotation>;
    fn arithmetic_proofs(&self) -> Vec<&ProofAnnotation>;
    fn functional_proofs(&self) -> Vec<&ProofAnnotation>;
    fn concurrency_proofs(&self) -> Vec<&ProofAnnotation>;
    fn aliasing_proofs(&self) -> Vec<&ProofAnnotation>;
    fn gpu_proofs(&self) -> Vec<&ProofAnnotation>;
}

impl ProofAnnotationFilters for [ProofAnnotation] {
    fn memory_proofs(&self) -> Vec<&ProofAnnotation> {
        self.iter().filter(|p| p.is_memory_safety()).collect()
    }
    fn arithmetic_proofs(&self) -> Vec<&ProofAnnotation> {
        self.iter().filter(|p| p.is_arithmetic_safety()).collect()
    }
    fn functional_proofs(&self) -> Vec<&ProofAnnotation> {
        self.iter().filter(|p| p.is_functional()).collect()
    }
    fn concurrency_proofs(&self) -> Vec<&ProofAnnotation> {
        self.iter().filter(|p| p.is_concurrency()).collect()
    }
    fn aliasing_proofs(&self) -> Vec<&ProofAnnotation> {
        self.iter().filter(|p| p.is_aliasing()).collect()
    }
    fn gpu_proofs(&self) -> Vec<&ProofAnnotation> {
        self.iter().filter(|p| p.is_gpu_relevant()).collect()
    }
}
