// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Dialect lowering framework.
//!
//! A [`LoweringPass`] inspects a single [`InstrNode`] whose instruction is a
//! [`DialectInst`] and optionally rewrites it into a sequence of zero or more
//! replacement nodes (which may themselves be dialect ops in a lower-level
//! dialect, or plain core [`Inst`]s).
//!
//! [`lower_module`] walks every function and block, applies each pass in
//! registration order, and iterates until no pass reports a change or until
//! `max_iters` is exhausted. This is the classical MLIR fixpoint driver
//! shape, scoped to a single pass list.
//!
//! The framework deliberately makes no attempt to optimize pass ordering or
//! to do pattern matching beyond the `qualified_name()` string — that is the
//! pass author's responsibility. Keeping the core simple means every dialect
//! gets a predictable lowering contract.
//!
//! # Guarantees
//!
//! - Replacement nodes are spliced in place of the original node; the
//!   relative ordering of other nodes is preserved.
//! - A pass that returns [`RewriteOutcome::NoChange`] is treated as idempotent
//!   for fixpoint detection.
//! - A pass may return [`RewriteOutcome::Replace`] with an empty vector to
//!   delete a dialect op (useful for e.g. assertion erasure after proof
//!   discharge).
//! - If any pass returns [`RewriteOutcome::Err`] the whole lowering aborts
//!   with [`DialectError::LoweringFailed`].

use super::DialectError;
use super::inst::DialectInst;
use crate::Module;
use crate::inst::Inst;
use crate::node::InstrNode;
use crate::proof::ProofAnnotation;
use crate::value::ValueId;

/// Returns true if `annotation` may be auto-carried from a lowered dialect op
/// onto its (semantically different) trailing replacement node.
///
/// `lower_module`'s default metadata carry must be *conservative*: a dialect
/// op's instruction-scoped proof annotations describe **that op's**
/// computation, and lowering replaces the op with a different instruction (a
/// `Call`, a `Const`, an arithmetic/memory sequence). Transplanting a claim
/// like "this operation does not overflow" onto an unrelated trailing node
/// would assert a property that node does not have — an unsound carry.
///
/// The rule, by category:
///
/// - **Dropped** (instruction-scoped claims about the original op's
///   computation or operands): the memory-safety claims (`InBounds`,
///   `NotNull`, the borrow validity claims, `ValidDealloc`), the arithmetic
///   claims (`NoOverflow`, `NoWrap`, `DivNonZero`, `ShiftInRange`,
///   `Wrapping`), and the algebraic operator properties (`Associative`,
///   `Commutative`). These are true of the *original* op only; a pass that
///   re-establishes them on its replacement must emit them itself.
/// - **Carried** (facts about the produced *value* or the surrounding
///   *scope/region* that remain meaningful regardless of how the value is
///   computed): `ProofRef` (a link to discharged module proof state),
///   value facts (`ValueRange`, `KnownBits`, `BoundedOutput`, `Monotonic`),
///   `NoUndef`, aliasing/alignment hints (`NoAlias`, `Aligned`), the GPU
///   memory-role and parallel/divergence hints, behavioral region facts
///   (`Pure`, `Terminates`, `Deterministic`, `DataRaceFree`,
///   `AtomicOrdering`, `NoPanic`), and `Custom` (opaque; the producer owns
///   its meaning and the conservative choice is to preserve it).
///
/// This is intentionally a deny-list of the unsafe-to-transplant claims rather
/// than an allow-list, so that *adding* a new value/scope annotation defaults
/// to being preserved (matching the historical "do not silently drop facts"
/// intent) while the soundness-critical computation claims stay enumerated.
pub fn annotation_survives_lowering_transplant(annotation: &ProofAnnotation) -> bool {
    !matches!(
        annotation,
        // Memory-safety claims about the original op's pointer/operands.
        ProofAnnotation::InBounds
            | ProofAnnotation::NotNull
            | ProofAnnotation::ValidBorrow
            | ProofAnnotation::UniqueBorrow
            | ProofAnnotation::SharedBorrow
            | ProofAnnotation::ValidDealloc
            // Arithmetic claims about the original op's computation.
            | ProofAnnotation::NoOverflow
            | ProofAnnotation::NoWrap
            | ProofAnnotation::DivNonZero
            | ProofAnnotation::ShiftInRange
            | ProofAnnotation::Wrapping
            // Algebraic properties of the original operator.
            | ProofAnnotation::Associative
            | ProofAnnotation::Commutative
    )
}

/// Context for a single rewrite operation.
pub struct LoweringContext<'a> {
    next_value_id: &'a mut u32,
}

impl<'a> LoweringContext<'a> {
    /// Returns a fresh `ValueId` unique within the current function.
    pub fn alloc_value(&mut self) -> ValueId {
        let id = ValueId::new(*self.next_value_id);
        *self.next_value_id += 1;
        id
    }
}

/// Outcome of attempting to rewrite a single dialect op.
#[derive(Debug)]
pub enum RewriteOutcome {
    /// The pass does not apply — leave the op alone.
    NoChange,
    /// Replace the op with zero or more replacement nodes. The replacement
    /// nodes inherit the original node's position in the block — and, unless
    /// the producing pass overrides [`LoweringPass::preserves_metadata`], the
    /// trailing replacement node also inherits the original node's
    /// `proofs` / `proof_context` / `span` (see [`lower_module`]).
    Replace(Vec<InstrNode>),
    /// The pass applied but failed. Lowering aborts with this message.
    Err(String),
}

/// Summary of a `lower_module` run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweringResult {
    /// Number of fixpoint iterations performed.
    pub iterations: usize,
    /// Total number of individual rewrites applied across all iterations.
    pub rewrites_applied: usize,
    /// True iff a full sweep ran with zero rewrites applied (i.e. we reached
    /// a fixed point before exhausting `max_iters`).
    pub fixpoint_reached: bool,
}

/// A dialect-aware rewrite pass.
///
/// A single pass is typically specific to one dialect (sometimes to one op).
/// Passes are cheap by convention — they inspect a `DialectInst` and produce
/// at most a small constant number of replacement nodes.
pub trait LoweringPass: Send + Sync {
    /// Diagnostic name. Used in error messages and debug output.
    fn name(&self) -> &'static str;

    /// Whether [`lower_module`] should automatically carry the *original*
    /// node's proof metadata (`proofs`, `proof_context`, `span`, `scope`) onto the
    /// trailing replacement node produced by [`RewriteOutcome::Replace`].
    ///
    /// Defaults to `true`: lowering a dialect op toward the backend must not
    /// silently drop the scope/value facts and proof-context that downstream
    /// consumers (e.g. trust-cg's vectorization / parallel-map / range
    /// reasoning) depend on.
    ///
    /// # The carry is per-annotation, not blanket
    ///
    /// Even when this returns `true`, the auto-carry is **conservative**: it
    /// only transplants `span`, `scope`, `proof_context`, and the proof
    /// annotations that remain valid no matter *what* instruction the dialect
    /// op lowered to.
    /// **Instruction-scoped claims about the original op's computation are NOT
    /// carried** — see [`annotation_survives_lowering_transplant`]. For
    /// example, a `NoOverflow` / `NoWrap` claim describes the *original*
    /// operation's arithmetic; blindly stamping it onto a semantically
    /// different trailing node (a `Call`, a `Const`, a memory op) would assert
    /// a guarantee that does not hold there. Those claims die with the op; a
    /// pass that knows its replacement genuinely re-establishes them must emit
    /// them explicitly on the node it produces.
    ///
    /// A pass whose rewrite *intentionally invalidates even the carry-safe*
    /// facts returns `false` and takes full responsibility for whatever
    /// metadata it emits on its replacement nodes.
    fn preserves_metadata(&self) -> bool {
        true
    }

    /// Apply the pass to a single dialect op.
    ///
    /// `node` is the full original [`InstrNode`] being rewritten; its
    /// `proofs` / `proof_context` / `span` / `scope` are available so a pass can make
    /// metadata-aware decisions. By default those facts are also propagated
    /// onto the replacement automatically — see
    /// [`LoweringPass::preserves_metadata`]. `op` is the instruction payload
    /// (a convenience view of `node.inst`); `results` is the `ValueId` vector
    /// that the enclosing `InstrNode` attaches to the op's results (a
    /// convenience view of `node.results`). Passes that produce replacement
    /// nodes typically reuse these result IDs on the final node they emit so
    /// downstream uses remain valid.
    fn rewrite(
        &self,
        node: &InstrNode,
        op: &DialectInst,
        results: &[ValueId],
        context: &mut LoweringContext<'_>,
    ) -> RewriteOutcome;
}

/// Applies `passes` to every dialect op in `module` until a fixed point is
/// reached or `max_iters` is exceeded.
///
/// Returns [`DialectError::LoweringFailed`] on the first pass that returns
/// [`RewriteOutcome::Err`], or [`DialectError::FixpointNotReached`] if the
/// iteration limit is hit while passes are still producing changes.
pub fn lower_module(
    module: &mut Module,
    passes: &[Box<dyn LoweringPass>],
    max_iters: usize,
) -> Result<LoweringResult, DialectError> {
    let mut total_rewrites = 0usize;
    let mut iteration = 0usize;

    loop {
        if iteration >= max_iters {
            return Err(DialectError::FixpointNotReached { max_iters });
        }
        iteration += 1;

        let mut changed_this_iter = 0usize;

        for func in &mut module.functions {
            let mut next_value_id = func.max_value_id() + 1;

            for block in &mut func.blocks {
                // Walk indices manually: a replacement may splice in several
                // nodes, and we should re-scan them in the same iteration so
                // chained lowerings can collapse in one pass.
                //
                // `per_index_rewrites` caps the number of times we can
                // productively rewrite at a single index within one outer
                // iteration. Well-behaved chained lowerings need at most
                // `passes.len()` hits at a position per iteration: each pass
                // fires at most once before the payload is no longer matched.
                // If a pass keeps rewriting the same op back to itself we
                // advance `i` and rely on the outer iteration bound to detect
                // the non-fixpoint (so the caller sees `FixpointNotReached`
                // rather than a hang).
                let per_index_cap = passes.len().max(1);
                let mut i = 0;
                let mut rewrites_at_i = 0usize;
                while i < block.body.len() {
                    let op_ref = match &block.body[i].inst {
                        Inst::DialectOp(op) => op.as_ref(),
                        _ => {
                            i += 1;
                            rewrites_at_i = 0;
                            continue;
                        }
                    };

                    // Try each pass in registration order. First non-NoChange
                    // wins; passes are expected to be disjoint on their op
                    // space, mirroring MLIR's pattern benefit model.
                    let mut outcome = None;
                    let mut pass_name = "";
                    let mut pass_preserves_metadata = true;
                    for pass in passes {
                        let results = block.body[i].results.clone();
                        let mut ctx = LoweringContext {
                            next_value_id: &mut next_value_id,
                        };
                        match pass.rewrite(&block.body[i], op_ref, &results, &mut ctx) {
                            RewriteOutcome::NoChange => continue,
                            o => {
                                pass_name = pass.name();
                                pass_preserves_metadata = pass.preserves_metadata();
                                outcome = Some(o);
                                break;
                            }
                        }
                    }

                    match outcome {
                        None => {
                            i += 1;
                            rewrites_at_i = 0;
                        }
                        Some(RewriteOutcome::NoChange) => {
                            i += 1;
                            rewrites_at_i = 0;
                        }
                        Some(RewriteOutcome::Replace(mut replacement)) => {
                            // Proof/metadata preservation: lowering a dialect op
                            // toward the backend must not silently drop the
                            // scope/value facts, per-call-site proof context, or
                            // source span that trust-cg consumes (vectorization /
                            // parallel-map / range). Carry them onto the trailing
                            // (last) replacement node by default, unless the
                            // producing pass opted out via `preserves_metadata()`.
                            //
                            // The carry is *conservative and per-annotation*:
                            // only annotations that remain valid no matter what
                            // the op lowered to are transplanted (see
                            // `annotation_survives_lowering_transplant`).
                            // Instruction-scoped computation claims (NoOverflow /
                            // NoWrap / InBounds / ...) describe the ORIGINAL op
                            // and are dropped — stamping them on a semantically
                            // different trailing node would be unsound.
                            //
                            // The carry is additive and never clobbers metadata
                            // the pass set itself: `span` / `proof_context` are
                            // inherited only when the trailing node left them
                            // unset, and carry-safe `proofs` are unioned in
                            // (originals not already present are appended). An
                            // empty replacement (deletion/erasure) intentionally
                            // carries nothing — the metadata dies with the op.
                            if pass_preserves_metadata && let Some(last) = replacement.last_mut() {
                                let original = &block.body[i];
                                if last.span.is_none() {
                                    last.span = original.span;
                                }
                                if last.scope.is_none() {
                                    last.scope = original.scope;
                                }
                                if last.proof_context.is_none() {
                                    last.proof_context = original.proof_context.clone();
                                }
                                for proof in &original.proofs {
                                    if annotation_survives_lowering_transplant(proof)
                                        && !last.proofs.contains(proof)
                                    {
                                        last.proofs.push(proof.clone());
                                    }
                                }
                            }
                            let len = replacement.len();
                            block.body.splice(i..=i, replacement);
                            total_rewrites += 1;
                            changed_this_iter += 1;
                            rewrites_at_i += 1;
                            if rewrites_at_i >= per_index_cap {
                                i += len.max(1);
                                rewrites_at_i = 0;
                            }
                        }
                        Some(RewriteOutcome::Err(reason)) => {
                            return Err(DialectError::LoweringFailed {
                                pass: pass_name.to_string(),
                                reason,
                            });
                        }
                    }
                }
            }
        }

        if changed_this_iter == 0 {
            return Ok(LoweringResult {
                iterations: iteration,
                rewrites_applied: total_rewrites,
                fixpoint_reached: true,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inst::Inst;
    use crate::node::InstrNode;
    use crate::ty::Ty;
    use crate::value::{BlockId, FuncId, FuncTyId, ValueId};
    use crate::{Block, Function, Module};

    /// Pass that rewrites `test.noop` into zero replacement nodes (deletion).
    struct EraseNoop;
    impl LoweringPass for EraseNoop {
        fn name(&self) -> &'static str {
            "erase-noop"
        }
        fn rewrite(
            &self,
            _node: &InstrNode,
            op: &DialectInst,
            _results: &[ValueId],
            _ctx: &mut LoweringContext<'_>,
        ) -> RewriteOutcome {
            if op.qualified_name() == "test.noop" {
                RewriteOutcome::Replace(Vec::new())
            } else {
                RewriteOutcome::NoChange
            }
        }
    }

    /// Pass that rewrites `test.const42` into `Inst::Const { value: Int(42) }`.
    struct ConstLower;
    impl LoweringPass for ConstLower {
        fn name(&self) -> &'static str {
            "const-lower"
        }
        fn rewrite(
            &self,
            _node: &InstrNode,
            op: &DialectInst,
            results: &[ValueId],
            _ctx: &mut LoweringContext<'_>,
        ) -> RewriteOutcome {
            if op.qualified_name() != "test.const42" {
                return RewriteOutcome::NoChange;
            }
            let mut node = InstrNode::new(Inst::Const {
                value: crate::constant::Constant::Int(42),
                ty: Ty::I64,
            });
            node.results = results.to_vec();
            RewriteOutcome::Replace(vec![node])
        }
    }

    /// Pass that always fails.
    struct AlwaysErr;
    impl LoweringPass for AlwaysErr {
        fn name(&self) -> &'static str {
            "always-err"
        }
        fn rewrite(
            &self,
            _node: &InstrNode,
            op: &DialectInst,
            _results: &[ValueId],
            _ctx: &mut LoweringContext<'_>,
        ) -> RewriteOutcome {
            if op.qualified_name() == "test.fail" {
                RewriteOutcome::Err("intentional".to_string())
            } else {
                RewriteOutcome::NoChange
            }
        }
    }

    fn module_with_dialect_ops(ops: Vec<DialectInst>) -> Module {
        let mut module = Module::new("m");
        let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        for op in ops {
            block
                .body
                .push(InstrNode::new(Inst::DialectOp(Box::new(op))));
        }
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn lower_noop_deletes_node() {
        let mut module = module_with_dialect_ops(vec![DialectInst::new("test", "noop")]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(EraseNoop)];
        let result = lower_module(&mut module, &passes, 8).unwrap();
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 1);
        assert_eq!(module.functions[0].blocks[0].body.len(), 0);
    }

    #[test]
    fn lower_const_produces_core_inst() {
        let op = DialectInst::new("test", "const42").with_result_ty(Ty::I64);
        let mut module = module_with_dialect_ops(vec![op]);
        // Give the dialect op a result value.
        module.functions[0].blocks[0].body[0].results = vec![ValueId::new(0)];
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(ConstLower)];
        let result = lower_module(&mut module, &passes, 8).unwrap();
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 1);
        let node = &module.functions[0].blocks[0].body[0];
        assert!(matches!(node.inst, Inst::Const { .. }));
        assert_eq!(node.results, vec![ValueId::new(0)]);
    }

    #[test]
    fn lower_unrelated_dialect_ops_are_left_alone() {
        let mut module = module_with_dialect_ops(vec![DialectInst::new("other", "stay")]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(EraseNoop), Box::new(ConstLower)];
        let result = lower_module(&mut module, &passes, 4).unwrap();
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 0);
        assert_eq!(module.functions[0].blocks[0].body.len(), 1);
    }

    #[test]
    fn lower_reports_pass_error() {
        let mut module = module_with_dialect_ops(vec![DialectInst::new("test", "fail")]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(AlwaysErr)];
        let err = lower_module(&mut module, &passes, 4).unwrap_err();
        assert!(matches!(err, DialectError::LoweringFailed { .. }));
    }

    #[test]
    fn lower_respects_max_iters() {
        // A non-terminating pass that keeps rewriting `test.forever` into
        // itself. This only triggers `FixpointNotReached` if max_iters is 0.
        struct NeverFixpoint;
        impl LoweringPass for NeverFixpoint {
            fn name(&self) -> &'static str {
                "never"
            }
            fn rewrite(
                &self,
                _node: &InstrNode,
                op: &DialectInst,
                _r: &[ValueId],
                _ctx: &mut LoweringContext<'_>,
            ) -> RewriteOutcome {
                if op.qualified_name() == "test.forever" {
                    RewriteOutcome::Replace(vec![InstrNode::new(Inst::DialectOp(Box::new(
                        DialectInst::new("test", "forever"),
                    )))])
                } else {
                    RewriteOutcome::NoChange
                }
            }
        }
        let mut module = module_with_dialect_ops(vec![DialectInst::new("test", "forever")]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(NeverFixpoint)];
        let err = lower_module(&mut module, &passes, 3).unwrap_err();
        assert!(matches!(err, DialectError::FixpointNotReached { .. }));
    }

    #[test]
    fn lower_reaches_fixpoint_after_multiple_iterations() {
        // Two passes chained: `test.stage1` -> `test.stage2` -> core Const.
        struct Stage1To2;
        impl LoweringPass for Stage1To2 {
            fn name(&self) -> &'static str {
                "stage1-to-2"
            }
            fn rewrite(
                &self,
                _node: &InstrNode,
                op: &DialectInst,
                results: &[ValueId],
                _ctx: &mut LoweringContext<'_>,
            ) -> RewriteOutcome {
                if op.qualified_name() == "test.stage1" {
                    let mut node = InstrNode::new(Inst::DialectOp(Box::new(DialectInst::new(
                        "test", "stage2",
                    ))));
                    node.results = results.to_vec();
                    RewriteOutcome::Replace(vec![node])
                } else {
                    RewriteOutcome::NoChange
                }
            }
        }
        struct Stage2ToCore;
        impl LoweringPass for Stage2ToCore {
            fn name(&self) -> &'static str {
                "stage2-to-core"
            }
            fn rewrite(
                &self,
                _node: &InstrNode,
                op: &DialectInst,
                results: &[ValueId],
                _ctx: &mut LoweringContext<'_>,
            ) -> RewriteOutcome {
                if op.qualified_name() == "test.stage2" {
                    let mut node = InstrNode::new(Inst::Const {
                        value: crate::constant::Constant::Int(0),
                        ty: Ty::I64,
                    });
                    node.results = results.to_vec();
                    RewriteOutcome::Replace(vec![node])
                } else {
                    RewriteOutcome::NoChange
                }
            }
        }
        let mut module = module_with_dialect_ops(vec![DialectInst::new("test", "stage1")]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(Stage1To2), Box::new(Stage2ToCore)];
        let result = lower_module(&mut module, &passes, 8).unwrap();
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 2);
        assert!(matches!(
            module.functions[0].blocks[0].body[0].inst,
            Inst::Const { .. }
        ));
    }

    /// FIX 5 (conservative proof/metadata preservation): when a dialect op
    /// lowers to a core node, the original node's *carry-safe* proofs /
    /// proof_context / span / lexical scope survive onto the trailing replacement node — even
    /// when the pass emits none of its own — but instruction-scoped computation
    /// claims (e.g. `NoWrap` about the ORIGINAL op) are NOT transplanted onto a
    /// semantically different trailing node.
    #[test]
    fn lower_carries_proofs_context_and_span_onto_replacement() {
        use crate::proof::{ProofAnnotation, ProofContext};
        use crate::value::{ProofId, SourceSpan};

        struct ProvenLower;
        impl LoweringPass for ProvenLower {
            fn name(&self) -> &'static str {
                "proven-lower"
            }
            fn rewrite(
                &self,
                _node: &InstrNode,
                op: &DialectInst,
                results: &[ValueId],
                _ctx: &mut LoweringContext<'_>,
            ) -> RewriteOutcome {
                if op.qualified_name() != "test.proven" {
                    return RewriteOutcome::NoChange;
                }
                // Deliberately emits NO proofs/span/proof_context of its own.
                let mut node = InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(7),
                    ty: Ty::I64,
                });
                node.results = results.to_vec();
                RewriteOutcome::Replace(vec![node])
            }
        }

        let span = SourceSpan {
            file: 3,
            line: 11,
            col: 4,
        };
        let proof_ctx = ProofContext {
            assumes: vec![ProofId::new(1)],
            establishes: vec![ProofId::new(2)],
        };
        let mut module = module_with_dialect_ops(vec![DialectInst::new("test", "proven")]);
        {
            let node = &mut module.functions[0].blocks[0].body[0];
            node.results = vec![ValueId::new(0)];
            // `Pure` and `ParallelMap` are carry-safe scope/value facts.
            // `NoWrap` is an instruction-scoped arithmetic claim about the
            // original op and must NOT be carried onto the `Const`.
            node.proofs = vec![
                ProofAnnotation::NoWrap,
                ProofAnnotation::Pure,
                ProofAnnotation::ParallelMap,
            ];
            node.span = Some(span);
            node.scope = Some(7);
            node.proof_context = Some(proof_ctx.clone());
        }
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(ProvenLower)];
        let result = lower_module(&mut module, &passes, 8).unwrap();
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 1);

        let node = &module.functions[0].blocks[0].body[0];
        assert!(matches!(node.inst, Inst::Const { .. }));
        // Carry-safe proofs / proof_context / span survived the lowering.
        assert!(node.proofs.contains(&ProofAnnotation::Pure));
        assert!(node.proofs.contains(&ProofAnnotation::ParallelMap));
        // Instruction-scoped arithmetic claim was dropped (would be unsound on
        // the unrelated `Const`).
        assert!(!node.proofs.contains(&ProofAnnotation::NoWrap));
        assert_eq!(node.span, Some(span));
        assert_eq!(node.scope, Some(7));
        assert_eq!(node.proof_context, Some(proof_ctx));
        assert_eq!(node.results, vec![ValueId::new(0)]);
    }

    /// FIX 5 deny-list pinpoint: each instruction-scoped computation claim is
    /// classified as non-transplantable, and each value/scope fact as
    /// transplantable, by `annotation_survives_lowering_transplant`.
    #[test]
    fn annotation_transplant_classification_is_conservative() {
        use crate::inst::Ordering;
        use crate::proof::ProofAnnotation as P;

        // Dropped: claims about the original op's computation/operands.
        for a in [
            P::InBounds,
            P::NotNull,
            P::ValidBorrow,
            P::UniqueBorrow,
            P::SharedBorrow,
            P::ValidDealloc,
            P::NoOverflow,
            P::NoWrap,
            P::DivNonZero,
            P::ShiftInRange,
            P::Wrapping,
            P::Associative,
            P::Commutative,
        ] {
            assert!(
                !annotation_survives_lowering_transplant(&a),
                "{a:?} must not auto-transplant onto an unrelated node"
            );
        }

        // Carried: facts about the produced value or surrounding scope.
        for a in [
            P::Pure,
            P::Terminates,
            P::Deterministic,
            P::DataRaceFree,
            P::AtomicOrdering(Ordering::SeqCst),
            P::NoPanic,
            P::NoUndef,
            P::NoAlias,
            P::Aligned(16),
            P::ReadonlyTable,
            P::AppendOnlyBuffer,
            P::ParallelMap,
            P::BoundedLoop(8),
            P::Monotonic,
            P::ValueRange { lo: 0, hi: 7 },
            P::KnownBits { zeros: 0, ones: 0 },
        ] {
            assert!(
                annotation_survives_lowering_transplant(&a),
                "{a:?} should be preserved across lowering"
            );
        }
    }

    /// FIX 1 opt-out: a pass that declares `preserves_metadata() == false`
    /// intentionally invalidates the original node's proofs — the framework
    /// must NOT carry them onto the replacement.
    #[test]
    fn lower_opt_out_drops_original_proofs() {
        use crate::proof::ProofAnnotation;

        struct InvalidatingLower;
        impl LoweringPass for InvalidatingLower {
            fn name(&self) -> &'static str {
                "invalidating-lower"
            }
            fn preserves_metadata(&self) -> bool {
                false
            }
            fn rewrite(
                &self,
                _node: &InstrNode,
                op: &DialectInst,
                results: &[ValueId],
                _ctx: &mut LoweringContext<'_>,
            ) -> RewriteOutcome {
                if op.qualified_name() != "test.invalidate" {
                    return RewriteOutcome::NoChange;
                }
                let mut node = InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(0),
                    ty: Ty::I64,
                });
                node.results = results.to_vec();
                RewriteOutcome::Replace(vec![node])
            }
        }

        let mut module = module_with_dialect_ops(vec![DialectInst::new("test", "invalidate")]);
        {
            let node = &mut module.functions[0].blocks[0].body[0];
            node.results = vec![ValueId::new(0)];
            node.proofs = vec![ProofAnnotation::NoWrap];
        }
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(InvalidatingLower)];
        lower_module(&mut module, &passes, 8).unwrap();

        let node = &module.functions[0].blocks[0].body[0];
        assert!(matches!(node.inst, Inst::Const { .. }));
        // Opt-out: original proofs were intentionally dropped.
        assert!(node.proofs.is_empty());
    }

    /// FIX 1 union semantics: the carry is additive and does not clobber
    /// metadata the pass set itself. The pass's own proof + span win where they
    /// conflict; the original's extra proofs are unioned in (deduped).
    #[test]
    fn lower_unions_proofs_and_keeps_pass_metadata() {
        use crate::proof::ProofAnnotation;
        use crate::value::SourceSpan;

        let pass_span = SourceSpan {
            file: 9,
            line: 1,
            col: 1,
        };

        struct UnionLower {
            span: SourceSpan,
        }
        impl LoweringPass for UnionLower {
            fn name(&self) -> &'static str {
                "union-lower"
            }
            fn rewrite(
                &self,
                _node: &InstrNode,
                op: &DialectInst,
                results: &[ValueId],
                _ctx: &mut LoweringContext<'_>,
            ) -> RewriteOutcome {
                if op.qualified_name() != "test.union" {
                    return RewriteOutcome::NoChange;
                }
                let mut node = InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(0),
                    ty: Ty::I64,
                })
                .with_proof(ProofAnnotation::Pure)
                .with_span(self.span);
                node.results = results.to_vec();
                RewriteOutcome::Replace(vec![node])
            }
        }

        let mut module = module_with_dialect_ops(vec![DialectInst::new("test", "union")]);
        {
            let node = &mut module.functions[0].blocks[0].body[0];
            node.results = vec![ValueId::new(0)];
            // `ParallelMap` is a carry-safe scope fact (unioned in); `Pure` is
            // also carry-safe but the pass already emits it; `NoWrap` is an
            // instruction-scoped claim that must be dropped, not unioned.
            node.proofs = vec![
                ProofAnnotation::ParallelMap,
                ProofAnnotation::Pure,
                ProofAnnotation::NoWrap,
            ];
            node.span = Some(SourceSpan {
                file: 0,
                line: 0,
                col: 0,
            });
        }
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(UnionLower { span: pass_span })];
        lower_module(&mut module, &passes, 8).unwrap();

        let node = &module.functions[0].blocks[0].body[0];
        // Original's carry-safe ParallelMap unioned in.
        assert!(node.proofs.contains(&ProofAnnotation::ParallelMap));
        // Instruction-scoped NoWrap is NOT unioned in (would be unsound).
        assert!(!node.proofs.contains(&ProofAnnotation::NoWrap));
        // Pure appears exactly once (pass already had it; not duplicated).
        assert_eq!(
            node.proofs
                .iter()
                .filter(|p| **p == ProofAnnotation::Pure)
                .count(),
            1
        );
        // Pass-provided span is NOT clobbered by the original's span.
        assert_eq!(node.span, Some(pass_span));
    }
}
