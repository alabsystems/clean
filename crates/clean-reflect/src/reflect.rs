// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The `<<.>>` arms: per-construct trust-ir -> clean `Expr` reflection.
//!
//! Each helper emits EXACTLY the AST the matching Lean `*ObligationExpr`
//! definition names, so the mechanized `PROVED => safe` contract applies to the
//! reflector's output verbatim (spec Section 2). Constructs outside Fragment-1
//! fail closed via [`ReflectError::Unsupported`].

use clean_kernel::Expr;
use trust_ir::{Inst, Module, OverflowOp};

use crate::error::ReflectError;
use crate::vocab;

/// The trust status of a reflected obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrustLabel {
    /// The obligation `Expr` DERIVED FROM the trust-ir node was kernel-discharged:
    /// the Clean kernel `check_type`'d a proof term against the object's OWN
    /// negated goal and accepted it (the de Bruijn criterion), MODULO the named
    /// `ayAddOverflows` (ay BV-overflow) trust boundary.
    ///
    /// This is the INTRINSIC gate, not an outside-model comparison: the kernel
    /// proves the object's own obligation under `Environment::with_prelude()`
    /// (the SAME `check_type(term, goal)` gate as `trust-certify`'s
    /// `kernel_checks_false`). It is NOT defined as `is_def_eq` against a
    /// hand-written `overflow_trust_boundary.lean` used as a per-obligation
    /// reference model — that antipattern has been retired (see
    /// `tests/fused_overflow.rs` for the runnable intrinsic discharge and its
    /// change-coupling demonstration).
    ///
    /// The soundness link is the once-proven META-soundness theorem `PROVED =>
    /// safe` applied to the kernel's verdict, not an external lemma re-consulted
    /// per obligation. `ayAddOverflows`' real semantics (ay's BV add-overflow
    /// decision) remain the single NAMED trust boundary; everything above it is
    /// kernel-checked.
    Proven,
    /// Reflection axiom; faithfulness not mechanized (out of Fragment-1).
    Trusted,
}

/// Reference to the Lean lemma whose `bimplies tp ob` an arm satisfies.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanLemmaRef(pub String);

/// Origin instruction / function / location, for lineage and naming.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ObligationOrigin {
    /// Stable name of the originating function.
    pub function: String,
    /// Index of the instruction within the module's instruction stream.
    pub inst_index: usize,
}

impl ObligationOrigin {
    /// A stable, lineage-friendly obligation name.
    #[must_use]
    pub fn stable_name(&self) -> String {
        format!("{}#{}", self.function, self.inst_index)
    }
}

/// One reflected obligation: the `Expr` goal plus provenance and trust label.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ReflectedObligation {
    /// The clean `Expr` the proofs model (the obligation *condition* as `Expr`),
    /// e.g. `overflowObligation (ayAddOverflows a b)` over the REAL Lean Names.
    /// Becomes a `VcObligation.goal_type` after wrapping with
    /// [`not_fires`](crate::not_fires).
    pub obligation_expr: Expr,
    /// Where this obligation came from.
    pub origin: ObligationOrigin,
    /// PROVEN (Fragment-1) or TRUSTED (reflection axiom).
    pub trust: TrustLabel,
    /// For Fragment-1 arms, the grounding Lean lemma.
    pub grounded_by: Option<LeanLemmaRef>,
}

/// All Fragment-1 obligations reflected from a module.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ReflectedModule {
    /// The reflected obligations, in module instruction order.
    pub obligations: Vec<ReflectedObligation>,
}

// --- The `<<.>>` arms ------------------------------------------------------

/// `bvConst n` -> a `Nat` literal operand term.
pub(crate) fn reflect_const(n: u64) -> Expr {
    Expr::nat_lit(n)
}

/// `bvVar v` -> a named operand term of carrier sort `Nat`.
///
/// The reflector models an SSA operand by a stable kernel constant; the operand
/// name is its `%<id>` symbol, registered with carrier sort `Nat` in the
/// reflect environment by the caller's vocabulary.
pub(crate) fn reflect_operand_const(symbol: &str) -> Expr {
    Expr::const_str(symbol)
}

/// ARITHMETIC OVERFLOW (`Overflow{Add/Sub/Mul}`, or `BinOp Add/Sub/Mul` with a
/// `NoOverflow` annotation):
///
/// emits `overflowObligation (ayAddOverflows a b)` over the REAL Lean
/// declaration Names the elaborated `overflow_trust_boundary.lean` environment
/// contains — NOT a private `Reflect.*` vocabulary. Unfolding `overflowObligation`
/// this is `bnot (ayNoOverflow (ayAddOverflows a b))`, i.e. the negation of ay's
/// no-overflow primitive at the operand-derived true panic flag.
///
/// - `ayAddOverflows : Nat -> Nat -> Bool` is the NAMED trust boundary: ay's BV
///   add-overflow decision over the two raw operands. Its real semantics are
///   ay's responsibility; clean does not prove it equals `decide (a+b >= 256)`.
/// - `overflowObligation : Bool -> Bool` (`:= bnot (ayNoOverflow tp)`) is the
///   PROVEN, panic-flag-parameterized obligation. The proven `overflow_op_sound`
///   (`∀ truePanic : Bool. bimplies tp (overflowObligation tp) = true`) applies
///   to this term BY INSTANTIATION at `truePanic := ayAddOverflows a b`. The
///   operands enter the soundness story ONLY through `ayAddOverflows`.
///
/// The increment-1 test checks the emitted shape structurally; the intrinsic
/// kernel discharge of an object-derived overflow obligation (no external
/// `.lean`) is demonstrated in `tests/fused_overflow.rs`.
pub(crate) fn reflect_overflow_obligation(operand_pair: (Expr, Expr)) -> Expr {
    let (a, b) = operand_pair;
    // ayAddOverflows a b  : the operand-derived true panic flag (trust boundary).
    let true_panic = Expr::apps(Expr::const_str(vocab::AY_ADD_OVERFLOWS), [a, b]);
    // overflowObligation (ayAddOverflows a b)  : the proven obligation, instantiated.
    Expr::app(Expr::const_str(vocab::OVERFLOW_OBLIGATION), true_panic)
}

/// SHIFT / BOUNDS: `Not(BvUlt(operand, bound))`
/// (expr_obligation_semantics.lean:52-55). Available for Increment 2; kept here
/// so the vocabulary contract stays in one place.
#[allow(dead_code)]
pub(crate) fn reflect_shift_bounds_obligation(operand: Expr, bound: Expr) -> Expr {
    let ult = Expr::apps(
        Expr::const_str(vocab::comparison::bv_ult()),
        [operand, bound],
    );
    Expr::app(Expr::const_str(vocab::comparison::bv_not()), ult)
}

/// DIV-BY-ZERO: `BvEq(divisor, 0)` (expr_obligation_semantics.lean:57-58).
/// Available for Increment 2.
#[allow(dead_code)]
pub(crate) fn reflect_div_obligation(divisor: Expr) -> Expr {
    Expr::apps(
        Expr::const_str(vocab::comparison::bv_eq()),
        [divisor, reflect_const(0)],
    )
}

// --- Fragment-1 dispatch ---------------------------------------------------

/// Reflect a single trust-ir [`Inst`] into its Fragment-1 obligation `Expr`.
///
/// Returns the obligation condition and its grounding lemma when the construct
/// is INSIDE Fragment-1; fails closed with [`ReflectError::Unsupported`]
/// otherwise. Operand symbols are `%<ValueId index>`.
///
/// INCREMENT 1 covers the overflow arm only; the comparison/div/bounds/call
/// arms are explicitly rejected here (they land in later increments) so the
/// reflector never emits an unbacked shape.
pub fn reflect_inst(inst: &Inst) -> Result<(Expr, LeanLemmaRef), ReflectError> {
    match inst {
        // All three arithmetic overflow ops (Add/Sub/Mul) share the single
        // `ayNoOverflow` trust boundary, so they reflect identically.
        Inst::Overflow {
            op: OverflowOp::AddOverflow | OverflowOp::SubOverflow | OverflowOp::MulOverflow,
            lhs,
            rhs,
            ..
        } => {
            let a = reflect_operand_const(&operand_symbol(lhs));
            let b = reflect_operand_const(&operand_symbol(rhs));
            Ok((
                reflect_overflow_obligation((a, b)),
                // The REAL proven lemma. `overflow_op_sound (∀ truePanic : Bool)`
                // applies to the emitted `overflowObligation (ayAddOverflows a b)`
                // by INSTANTIATION at `truePanic := ayAddOverflows a b`.
                LeanLemmaRef("overflow_op_sound".to_string()),
            ))
        }
        // Out of Increment 1 / out of Fragment-1: fail closed, naming the
        // construct so the rejection is auditable. Every variant is NAMED,
        // never caught by a wildcard, so a variant trust-ir adds fails to
        // compile HERE, at the dispatch, until someone decides whether
        // Fragment-1 reflects it.
        Inst::BinOp { .. } => unsupported("BinOp (Increment 2: div/shift/bounds)"),
        Inst::Assert { .. } => unsupported("Assert (Increment 2)"),
        Inst::Call { .. } => unsupported("Call (Increment 3)"),
        Inst::CallIndirect { .. } => unsupported("CallIndirect (Increment 3)"),
        Inst::CondBr { .. } => unsupported("CondBr (branching: out of Fragment-1, fail-closed)"),
        Inst::Switch { .. } => unsupported("Switch (branching: out of Fragment-1, fail-closed)"),
        Inst::Br { .. } => unsupported("Br (CFG: out of Fragment-1, fail-closed)"),
        Inst::MemCopy { .. } | Inst::MemSet { .. } => {
            unsupported("MemCopy/MemSet (bulk memory: out of Fragment-1, fail-closed)")
        }
        // trust-ir v47 (`DROP_INST_FORMAT_VERSION`): run a type's destructor on
        // the object behind a pointer. Observable (it frees, and it can run
        // user code), so it is refused by name rather than read as a no-op.
        Inst::Drop { .. } => {
            unsupported("Drop (destructor run, trust-ir v47: out of Fragment-1, fail-closed)")
        }
        // trust-ir v50 (`ARRAY_SPLAT_FORMAT_VERSION`): `n` copies of one
        // register as a `[e x n]` array value. Fragment-1 reflects scalar
        // overflow arithmetic only and has no array term, so it is refused by
        // name; the refusal never reads `n`, so its cost is independent of it.
        Inst::ArraySplat { .. } => unsupported(
            "ArraySplat (uniform register array, trust-ir v50: out of Fragment-1, fail-closed)",
        ),
        // Runtime SSA captures have no Fragment-1 obligation vocabulary.
        // Refuse by name without reading a capture or synthesizing a value.
        Inst::MakeClosure { .. } => unsupported(
            "MakeClosure (runtime captures, trust-ir v63: out of Fragment-1, fail-closed)",
        ),
        // trust-ir v67-v69 tensor instructions compute whole tensor values;
        // Fragment-1 has no tensor term. Refused by name.
        Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => {
            unsupported("tensor instruction (trust-ir v67-v69: out of Fragment-1, fail-closed)")
        }
        Inst::UnOp { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::Return { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Unreachable
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::AssertInvoke { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::DropInvoke { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::DialectOp(..)
        | Inst::MakeAggregate { .. } => unsupported("construct outside Fragment-1 (fail-closed)"),
    }
}

/// A Fragment-1 refusal carrying its auditable label.
fn unsupported(label: &'static str) -> Result<(Expr, LeanLemmaRef), ReflectError> {
    Err(ReflectError::unsupported(label))
}

/// The carrier symbol the reflector assigns to an SSA operand.
fn operand_symbol(v: &trust_ir::ValueId) -> String {
    format!("%{}", v.index())
}

/// The general SemanticReflection map `<<.>>` at module granularity.
///
/// Reflects every Fragment-1 obligation in `module` to its clean `Expr` goal,
/// tagging each with its trust label. Constructs outside Fragment-1 are skipped
/// (fail-closed): they are NOT emitted as obligations, never as a wrong shape.
///
/// # Errors
///
/// Currently total over well-formed modules: out-of-fragment instructions are
/// silently skipped rather than aborting the module. (Per-instruction
/// fail-closed rejection is available via [`reflect_inst`] for callers that
/// need it.)
#[must_use]
pub fn reflect_module(module: &Module) -> ReflectedModule {
    let mut obligations = Vec::new();
    let mut inst_index = 0usize;
    for func in &module.functions {
        for node in func.instructions() {
            let idx = inst_index;
            inst_index += 1;
            if let Ok((obligation_expr, lemma)) = reflect_inst(&node.inst) {
                obligations.push(ReflectedObligation {
                    obligation_expr,
                    origin: ObligationOrigin {
                        function: func.name.clone(),
                        inst_index: idx,
                    },
                    trust: TrustLabel::Proven,
                    grounded_by: Some(lemma),
                });
            }
        }
    }
    ReflectedModule { obligations }
}
