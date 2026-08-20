// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::inst::Inst;
use crate::proof::{ProofAnnotation, ProofAnnotationFilters, ProofContext};
use crate::value::{SourceSpan, ValueId};

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InstrNode {
    pub inst: Inst,
    pub results: Vec<ValueId>,
    pub proofs: Vec<ProofAnnotation>,
    pub span: Option<SourceSpan>,
    /// Per-call-site proof context (B5); meaningful only on the call forms
    /// (Call / CallIndirect / Invoke — validation rejects it elsewhere).
    ///
    /// ALWAYS emitted by serde since v33 (no `skip_serializing_if`; `None`
    /// encodes as nil): the canonical MessagePack codec is POSITIONAL and a
    /// positional struct may carry at most ONE trailing conditionally-skipped
    /// field. `scope` is now that field, so `proof_context` must keep its index.
    #[cfg_attr(feature = "serde", serde(default))]
    pub proof_context: Option<ProofContext>,
    /// Trust (C2-scopes, v33): which entry of the function's
    /// [`crate::ScopeData`] table this instruction sits in — the trust-ir
    /// counterpart of MIR's `SourceInfo::scope`, where `span` is the other half.
    ///
    /// `None` means "unstamped", NOT "outermost": a consumer inherits the
    /// running scope, exactly as it already inherits the running span when
    /// `span` is `None`. That keeps a node whose location could not be
    /// reconstructed from silently jumping to the top of the tree.
    ///
    /// Declared LAST and `skip_serializing_if = Option::is_none` — the sole
    /// trailing optional, so positional MessagePack stays safe in both
    /// directions. When adding the NEXT optional field, repeat the move: make
    /// `scope` always-emitted and append the newcomer as the sole skipped one.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub scope: Option<u32>,
}

impl InstrNode {
    pub fn new(inst: Inst) -> Self {
        Self {
            inst,
            results: Vec::new(),
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        }
    }

    /// Attach a per-call-site proof context (B5).
    pub fn with_proof_context(mut self, ctx: ProofContext) -> Self {
        self.proof_context = Some(ctx);
        self
    }

    pub fn with_result(mut self, result: ValueId) -> Self {
        self.results.push(result);
        self
    }

    pub fn with_results(mut self, results: impl IntoIterator<Item = ValueId>) -> Self {
        self.results.extend(results);
        self
    }

    pub fn with_proof(mut self, proof: ProofAnnotation) -> Self {
        self.proofs.push(proof);
        self
    }

    pub fn with_span(mut self, span: SourceSpan) -> Self {
        self.span = Some(span);
        self
    }

    /// Attach the function-local lexical-scope index carried by this node.
    pub fn with_scope(mut self, scope: u32) -> Self {
        self.scope = Some(scope);
        self
    }

    /// Returns true if this instruction node has the given proof annotation.
    pub fn has_proof(&self, annotation: &ProofAnnotation) -> bool {
        self.proofs.contains(annotation)
    }

    /// Returns references to all memory safety proof annotations on this node.
    ///
    /// Useful for TrustIr to quickly extract memory safety guarantees when
    /// deciding whether a load/store can be moved to a different target.
    pub fn memory_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::memory_proofs(self.proofs.as_slice())
    }

    /// Returns references to all arithmetic safety proof annotations on this node.
    pub fn arithmetic_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::arithmetic_proofs(self.proofs.as_slice())
    }

    /// Returns references to all functional correctness proof annotations on this node.
    pub fn functional_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::functional_proofs(self.proofs.as_slice())
    }

    /// Returns references to all concurrency proof annotations on this node.
    ///
    /// TrustIr uses these to determine safe concurrent access patterns
    /// during cross-target synthesis (e.g., DataRaceFree enables lock-free GPU access).
    pub fn concurrency_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::concurrency_proofs(self.proofs.as_slice())
    }

    /// Returns references to all aliasing proof annotations on this node.
    ///
    /// TrustIr uses these for vectorization and cross-target register allocation.
    /// NoAlias + ValidBorrow enable zero-copy DMA between CPU and GPU.
    pub fn aliasing_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::aliasing_proofs(self.proofs.as_slice())
    }

    /// Returns references to all GPU-relevant proof annotations on this node.
    ///
    /// TrustIr uses these during cross-target synthesis to collect all annotations
    /// that enable GPU/ANE/SIMD execution in one pass.
    pub fn gpu_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::gpu_proofs(self.proofs.as_slice())
    }

    /// Returns true if this instruction has at least one GPU-relevant proof annotation.
    ///
    /// TrustIr uses this as a quick check during cross-target synthesis to determine
    /// whether an instruction has any proof annotations that enable GPU/ANE/SIMD
    /// execution.
    pub fn is_proven_safe_for_gpu(&self) -> bool {
        self.proofs.iter().any(|p| p.is_gpu_relevant())
    }

    pub fn has_side_effects(&self) -> bool {
        self.inst.has_side_effects()
    }

    pub fn is_terminator(&self) -> bool {
        self.inst.is_terminator()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constant::Constant;
    use crate::inst::*;
    use crate::proof::ProofAnnotation;
    use crate::ty::Ty;
    use crate::value::{BlockId, FuncId, SourceSpan, ValueId};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    #[test]
    fn new_creates_empty_node() {
        let inst = Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(42),
        };
        let node = InstrNode::new(inst.clone());
        assert_eq!(node.inst, inst);
        assert!(node.results.is_empty());
        assert!(node.proofs.is_empty());
        assert!(node.span.is_none());
    }

    #[test]
    fn with_result_adds_value() {
        let node = InstrNode::new(Inst::NullPtr).with_result(v(0));
        assert_eq!(node.results, vec![v(0)]);
    }

    #[test]
    fn with_results_adds_multiple() {
        let node = InstrNode::new(Inst::NullPtr)
            .with_result(v(0))
            .with_results([v(1), v(2)]);
        assert_eq!(node.results, vec![v(0), v(1), v(2)]);
    }

    #[test]
    fn with_proof_adds_annotation() {
        let node = InstrNode::new(Inst::NullPtr)
            .with_proof(ProofAnnotation::NotNull)
            .with_proof(ProofAnnotation::InBounds);
        assert_eq!(node.proofs.len(), 2);
        assert_eq!(node.proofs[0], ProofAnnotation::NotNull);
        assert_eq!(node.proofs[1], ProofAnnotation::InBounds);
    }

    #[test]
    fn with_span_sets_location() {
        let span = SourceSpan {
            file: 0,
            line: 10,
            col: 5,
        };
        let node = InstrNode::new(Inst::NullPtr).with_span(span);
        assert_eq!(node.span, Some(span));
    }

    #[test]
    fn with_scope_sets_lexical_scope() {
        let node = InstrNode::new(Inst::NullPtr).with_scope(3);
        assert_eq!(node.scope, Some(3));
    }

    #[test]
    fn has_side_effects_store() {
        let node = InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        });
        assert!(node.has_side_effects());
    }

    #[test]
    fn has_side_effects_call() {
        let node = InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        });
        assert!(node.has_side_effects());
    }

    #[test]
    fn has_side_effects_assert() {
        let node = InstrNode::new(Inst::Assert { cond: v(0) });
        assert!(node.has_side_effects());
    }

    #[test]
    fn has_side_effects_atomic_store() {
        let node = InstrNode::new(Inst::AtomicStore {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        });
        assert!(node.has_side_effects());
    }

    #[test]
    fn has_side_effects_atomic_rmw() {
        let node = InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        });
        assert!(node.has_side_effects());
    }

    #[test]
    fn has_side_effects_cmpxchg() {
        let node = InstrNode::new(Inst::CmpXchg {
            ty: Ty::I64,
            ptr: v(0),
            expected: v(1),
            desired: v(2),
            success: Ordering::SeqCst,
            failure: Ordering::SeqCst,
        });
        assert!(node.has_side_effects());
    }

    #[test]
    fn has_side_effects_fence() {
        let node = InstrNode::new(Inst::Fence {
            ordering: Ordering::SeqCst,
        });
        assert!(node.has_side_effects());
    }

    #[test]
    fn has_side_effects_call_indirect() {
        let node = InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: crate::value::FuncTyId::new(0),
            args: vec![],

            calling_conv: crate::CallingConv::C,
        });
        assert!(node.has_side_effects());
    }

    #[test]
    fn no_side_effects_binop() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_load() {
        let node = InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_const() {
        let node = InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_alloca() {
        let node = InstrNode::new(Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: None,
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_assume() {
        let node = InstrNode::new(Inst::Assume { cond: v(0) });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn is_terminator_br() {
        let node = InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        });
        assert!(node.is_terminator());
    }

    #[test]
    fn is_terminator_condbr() {
        let node = InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        });
        assert!(node.is_terminator());
    }

    #[test]
    fn is_terminator_switch() {
        let node = InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(3),
            default_args: vec![],
            cases: vec![],
            exhaustive_enum_unreachable: false,
        });
        assert!(node.is_terminator());
    }

    #[test]
    fn is_terminator_return() {
        let node = InstrNode::new(Inst::Return { values: vec![] });
        assert!(node.is_terminator());
    }

    #[test]
    fn is_terminator_unreachable() {
        let node = InstrNode::new(Inst::Unreachable);
        assert!(node.is_terminator());
    }

    #[test]
    fn not_terminator_binop() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_store() {
        let node = InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_call() {
        let node = InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_load() {
        let node = InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        });
        assert!(!node.is_terminator());
    }

    // --- has_proof tests ---

    #[test]
    fn has_proof_present() {
        let node = InstrNode::new(Inst::NullPtr)
            .with_proof(ProofAnnotation::NotNull)
            .with_proof(ProofAnnotation::InBounds);
        assert!(node.has_proof(&ProofAnnotation::NotNull));
        assert!(node.has_proof(&ProofAnnotation::InBounds));
    }

    #[test]
    fn has_proof_absent() {
        let node = InstrNode::new(Inst::NullPtr).with_proof(ProofAnnotation::NotNull);
        assert!(!node.has_proof(&ProofAnnotation::InBounds));
        assert!(!node.has_proof(&ProofAnnotation::Pure));
    }

    #[test]
    fn has_proof_empty() {
        let node = InstrNode::new(Inst::NullPtr);
        assert!(!node.has_proof(&ProofAnnotation::NotNull));
    }

    #[test]
    fn has_proof_multiple_annotations() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::Commutative)
        .with_proof(ProofAnnotation::Associative);
        assert!(node.has_proof(&ProofAnnotation::NoOverflow));
        assert!(node.has_proof(&ProofAnnotation::Commutative));
        assert!(node.has_proof(&ProofAnnotation::Associative));
        assert!(!node.has_proof(&ProofAnnotation::Pure));
    }

    // --- NEW NODE TESTS ---

    #[test]
    fn no_side_effects_copy() {
        let node = InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: v(0),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_select() {
        let node = InstrNode::new(Inst::Select {
            ty: Ty::I32,
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_undef() {
        let node = InstrNode::new(Inst::Undef { ty: Ty::I32 });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_icmp() {
        let node = InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_fcmp() {
        let node = InstrNode::new(Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F64,
            lhs: v(0),
            rhs: v(1),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_unop() {
        let node = InstrNode::new(Inst::UnOp {
            op: UnOp::Neg,
            ty: Ty::I32,
            operand: v(0),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_cast() {
        let node = InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I32,
            dst_ty: Ty::I64,
            operand: v(0),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_gep() {
        let node = InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I32,
            base: v(0),
            indices: vec![v(1)],
            inbounds: false,
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_null_ptr() {
        let node = InstrNode::new(Inst::NullPtr);
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_extract_field() {
        let node = InstrNode::new(Inst::ExtractField {
            ty: Ty::I32,
            aggregate: v(0),
            field: 0,
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn no_side_effects_overflow() {
        let node = InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        });
        assert!(!node.has_side_effects());
    }

    #[test]
    fn atomic_load_has_side_effects() {
        // An atomic load synchronizes-with other threads (and for SeqCst joins
        // the single total order), so it is observable and DCE must not remove
        // it — see docs/ub-numerics-policy.md §5. This holds for every ordering.
        for ordering in [Ordering::Relaxed, Ordering::Acquire, Ordering::SeqCst] {
            let node = InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: v(0),
                ordering,
            });
            assert!(
                node.has_side_effects(),
                "atomic load ({ordering:?}) is observable"
            );
        }
    }

    #[test]
    fn not_terminator_assume() {
        let node = InstrNode::new(Inst::Assume { cond: v(0) });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_assert() {
        let node = InstrNode::new(Inst::Assert { cond: v(0) });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_alloca() {
        let node = InstrNode::new(Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: None,
        });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_copy() {
        let node = InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: v(0),
        });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_select() {
        let node = InstrNode::new(Inst::Select {
            ty: Ty::I32,
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_fence() {
        let node = InstrNode::new(Inst::Fence {
            ordering: Ordering::SeqCst,
        });
        assert!(!node.is_terminator());
    }

    #[test]
    fn not_terminator_cmpxchg() {
        let node = InstrNode::new(Inst::CmpXchg {
            ty: Ty::I64,
            ptr: v(0),
            expected: v(1),
            desired: v(2),
            success: Ordering::SeqCst,
            failure: Ordering::Relaxed,
        });
        assert!(!node.is_terminator());
    }

    #[test]
    fn chained_builder_methods() {
        let span = SourceSpan {
            file: 1,
            line: 42,
            col: 10,
        };
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2))
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::NoWrap)
        .with_span(span);

        assert_eq!(node.results, vec![v(2)]);
        assert_eq!(node.proofs.len(), 2);
        assert_eq!(node.proofs[0], ProofAnnotation::NoOverflow);
        assert_eq!(node.proofs[1], ProofAnnotation::NoWrap);
        assert_eq!(node.span, Some(span));
    }

    // --- Proof filtering method tests ---

    #[test]
    fn memory_proofs_filters_correctly() {
        let node = InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_proof(ProofAnnotation::InBounds)
        .with_proof(ProofAnnotation::NotNull)
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::Pure);
        let mem = node.memory_proofs();
        assert_eq!(mem.len(), 2);
        assert!(mem.contains(&&ProofAnnotation::InBounds));
        assert!(mem.contains(&&ProofAnnotation::NotNull));
    }

    #[test]
    fn memory_proofs_empty_when_no_memory() {
        let node = InstrNode::new(Inst::NullPtr)
            .with_proof(ProofAnnotation::Pure)
            .with_proof(ProofAnnotation::NoOverflow);
        assert!(node.memory_proofs().is_empty());
    }

    #[test]
    fn arithmetic_proofs_filters_correctly() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::NoWrap)
        .with_proof(ProofAnnotation::Commutative);
        let arith = node.arithmetic_proofs();
        assert_eq!(arith.len(), 2);
        assert!(arith.contains(&&ProofAnnotation::NoOverflow));
        assert!(arith.contains(&&ProofAnnotation::NoWrap));
    }

    #[test]
    fn functional_proofs_filters_correctly() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::Commutative)
        .with_proof(ProofAnnotation::Associative)
        .with_proof(ProofAnnotation::Pure);
        let func = node.functional_proofs();
        assert_eq!(func.len(), 3);
        assert!(func.contains(&&ProofAnnotation::Commutative));
        assert!(func.contains(&&ProofAnnotation::Associative));
        assert!(func.contains(&&ProofAnnotation::Pure));
    }

    #[test]
    fn is_proven_safe_for_gpu_true() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_proof(ProofAnnotation::Pure)
        .with_proof(ProofAnnotation::NoOverflow);
        assert!(node.is_proven_safe_for_gpu());
    }

    #[test]
    fn is_proven_safe_for_gpu_false_no_proofs() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        });
        assert!(!node.is_proven_safe_for_gpu());
    }

    #[test]
    fn is_proven_safe_for_gpu_false_non_gpu_proofs() {
        let node = InstrNode::new(Inst::NullPtr)
            .with_proof(ProofAnnotation::DataRaceFree)
            .with_proof(ProofAnnotation::Monotonic);
        assert!(!node.is_proven_safe_for_gpu());
    }

    #[test]
    fn is_proven_safe_for_gpu_with_new_variants() {
        let node = InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_proof(ProofAnnotation::NoAlias)
        .with_proof(ProofAnnotation::NoPanic);
        assert!(node.is_proven_safe_for_gpu());
    }

    #[test]
    fn is_proven_safe_for_gpu_with_aligned() {
        let node = InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_proof(ProofAnnotation::Aligned(16));
        assert!(node.is_proven_safe_for_gpu());
    }

    // --- concurrency_proofs tests ---

    #[test]
    fn concurrency_proofs_filters_correctly() {
        let node = InstrNode::new(Inst::AtomicLoad {
            ty: Ty::I64,
            ptr: v(0),
            ordering: Ordering::SeqCst,
        })
        .with_proof(ProofAnnotation::DataRaceFree)
        .with_proof(ProofAnnotation::AtomicOrdering(Ordering::SeqCst))
        .with_proof(ProofAnnotation::NoAlias);
        let conc = node.concurrency_proofs();
        assert_eq!(conc.len(), 2);
        assert!(conc.contains(&&ProofAnnotation::DataRaceFree));
        assert!(conc.contains(&&ProofAnnotation::AtomicOrdering(Ordering::SeqCst)));
    }

    #[test]
    fn concurrency_proofs_empty_when_no_concurrency() {
        let node = InstrNode::new(Inst::NullPtr)
            .with_proof(ProofAnnotation::Pure)
            .with_proof(ProofAnnotation::NoOverflow);
        assert!(node.concurrency_proofs().is_empty());
    }

    // --- aliasing_proofs tests ---

    #[test]
    fn aliasing_proofs_filters_correctly() {
        let node = InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_proof(ProofAnnotation::NoAlias)
        .with_proof(ProofAnnotation::ValidBorrow)
        .with_proof(ProofAnnotation::InBounds)
        .with_proof(ProofAnnotation::Pure);
        let alias = node.aliasing_proofs();
        assert_eq!(alias.len(), 2);
        assert!(alias.contains(&&ProofAnnotation::NoAlias));
        assert!(alias.contains(&&ProofAnnotation::ValidBorrow));
    }

    #[test]
    fn aliasing_proofs_empty_when_no_aliasing() {
        let node = InstrNode::new(Inst::NullPtr)
            .with_proof(ProofAnnotation::Pure)
            .with_proof(ProofAnnotation::InBounds);
        assert!(node.aliasing_proofs().is_empty());
    }

    // --- gpu_proofs tests ---

    #[test]
    fn gpu_proofs_returns_all_gpu_relevant() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_proof(ProofAnnotation::Pure)
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::Commutative)
        .with_proof(ProofAnnotation::DataRaceFree) // not GPU-relevant
        .with_proof(ProofAnnotation::Monotonic); // not GPU-relevant
        let gpu = node.gpu_proofs();
        assert_eq!(gpu.len(), 3);
        assert!(gpu.contains(&&ProofAnnotation::Pure));
        assert!(gpu.contains(&&ProofAnnotation::NoOverflow));
        assert!(gpu.contains(&&ProofAnnotation::Commutative));
    }

    #[test]
    fn gpu_proofs_empty_when_no_gpu_annotations() {
        let node = InstrNode::new(Inst::NullPtr)
            .with_proof(ProofAnnotation::DataRaceFree)
            .with_proof(ProofAnnotation::Monotonic);
        assert!(node.gpu_proofs().is_empty());
    }

    #[test]
    fn gpu_proofs_includes_all_gpu_relevant_types() {
        let node = InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_proof(ProofAnnotation::Pure)
        .with_proof(ProofAnnotation::InBounds)
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::Commutative)
        .with_proof(ProofAnnotation::Associative)
        .with_proof(ProofAnnotation::Deterministic)
        .with_proof(ProofAnnotation::ValidBorrow)
        .with_proof(ProofAnnotation::NoPanic)
        .with_proof(ProofAnnotation::NoAlias)
        .with_proof(ProofAnnotation::Aligned(16));
        let gpu = node.gpu_proofs();
        assert_eq!(gpu.len(), 10);
    }
}
