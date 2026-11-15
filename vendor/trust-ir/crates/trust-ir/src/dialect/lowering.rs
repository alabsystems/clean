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
//! - Every applied replacement invalidates that function's
//!   [`crate::Function::source_provenance`], independently of instruction
//!   metadata preservation. Untouched functions retain their carriers.
//! - Only diagnostic span/scope metadata is automatically carried. Original
//!   proof claims are not evidence about replacement instructions. Rewriting
//!   required semantic/policy markers or a nonempty call contract is refused.
//!
//! This is not a verified rewrite transaction: pass-emitted claims are not
//! checked here, and function-level claims, module obligations, certificates,
//! and instruction-site backreferences are not repaired. Callers must separately
//! invalidate or re-establish that authority and validate the resulting module.
//! Errors retain any earlier applied rewrites; there is no module-wide rollback.

use super::DialectError;
use super::inst::DialectInst;
use crate::Module;
use crate::inst::Inst;
use crate::node::InstrNode;
use crate::proof::ProofAnnotation;
use crate::value::{FreshIds, IdSpaceExhausted, ValueId};

/// The generic driver has no subject/effect mapping or proof-transfer checker.
/// This exhaustive classification makes adding an annotation require an explicit
/// decision rather than silently granting transfer or erasure permission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AnnotationRewriteDisposition {
    /// Discard the original claim/hint, without authenticating replacement facts.
    DropClaimOrHint,
    /// Erasure and transplantation both require a mapping this driver lacks.
    RequiresMappedRewrite,
}

fn annotation_rewrite_disposition(annotation: &ProofAnnotation) -> AnnotationRewriteDisposition {
    use AnnotationRewriteDisposition::{DropClaimOrHint, RequiresMappedRewrite};
    match annotation {
        ProofAnnotation::InBounds
        | ProofAnnotation::NotNull
        | ProofAnnotation::ValidBorrow
        | ProofAnnotation::UniqueBorrow
        | ProofAnnotation::SharedBorrow
        | ProofAnnotation::ValidDealloc
        | ProofAnnotation::NoOverflow
        | ProofAnnotation::NoWrap
        | ProofAnnotation::DivNonZero
        | ProofAnnotation::ShiftInRange
        | ProofAnnotation::Pure
        | ProofAnnotation::Terminates
        | ProofAnnotation::Deterministic
        | ProofAnnotation::Associative
        | ProofAnnotation::Commutative
        | ProofAnnotation::DataRaceFree
        | ProofAnnotation::BoundedOutput { .. }
        | ProofAnnotation::Monotonic
        | ProofAnnotation::NoAlias
        | ProofAnnotation::Aligned(_)
        | ProofAnnotation::NoPanic
        | ProofAnnotation::NoUndef
        | ProofAnnotation::ParallelMap
        | ProofAnnotation::BoundedLoop(_)
        | ProofAnnotation::ValueRange { .. }
        | ProofAnnotation::KnownBits { .. }
        | ProofAnnotation::BranchWeights(_)
        | ProofAnnotation::ProofRef(_) => DropClaimOrHint,
        // These carry semantics, enforcement policy, outstanding obligations,
        // or opaque meaning. A copied marker on an arbitrary trailing node is
        // not a complete mapping; silently dropping it can remove enforcement.
        ProofAnnotation::Wrapping
        | ProofAnnotation::AtomicOrdering(_)
        | ProofAnnotation::Tainted
        | ProofAnnotation::TrustedSink
        | ProofAnnotation::ReadonlyTable
        | ProofAnnotation::AppendOnlyBuffer
        | ProofAnnotation::AtomicSetInsert
        | ProofAnnotation::DivergenceClass(_)
        | ProofAnnotation::FreshSymbolicHavoc
        | ProofAnnotation::RegionHavocStore
        | ProofAnnotation::Custom(_) => RequiresMappedRewrite,
        #[cfg(feature = "clean-expr")]
        ProofAnnotation::Goal(_) => RequiresMappedRewrite,
    }
}

/// Whether an original annotation may be automatically transplanted onto an
/// arbitrary replacement node. Always false: no annotation has that contract.
///
/// Retained for API compatibility. False does **not** authorize erasure:
/// [`lower_module`] refuses replacing original nodes carrying required
/// semantic/policy markers; ordinary claims/hints are invalidated instead. A pass may emit
/// metadata of its own, but this driver does not establish its correctness.
pub fn annotation_survives_lowering_transplant(annotation: &ProofAnnotation) -> bool {
    match annotation_rewrite_disposition(annotation) {
        AnnotationRewriteDisposition::DropClaimOrHint
        | AnnotationRewriteDisposition::RequiresMappedRewrite => false,
    }
}

fn unmapped_rewrite_requirement(node: &InstrNode) -> Option<&'static str> {
    if node
        .proof_context
        .as_ref()
        .is_some_and(|context| !context.assumes.is_empty() || !context.establishes.is_empty())
    {
        return Some("nonempty ProofContext");
    }
    node.proofs.iter().find_map(|annotation| {
        (annotation_rewrite_disposition(annotation)
            == AnnotationRewriteDisposition::RequiresMappedRewrite)
            .then(|| annotation.kind_name())
    })
}

/// Context for a single rewrite operation.
pub struct LoweringContext<'a> {
    fresh: &'a mut FreshIds<ValueId>,
    /// Set when [`Self::alloc_value`] refused, so [`lower_module`] reports the
    /// refusal as [`DialectError::ValueIdSpaceExhausted`] whatever the pass
    /// made of it.
    exhausted: Option<IdSpaceExhausted>,
}

impl<'a> LoweringContext<'a> {
    /// Returns a fresh `ValueId` unique within the current function: one past
    /// the highest id the function defines ([`crate::Function::fresh_value_ids`]).
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when no id is left (a definition holds
    /// `u32::MAX`); a pass returns [`RewriteOutcome::Err`] and [`lower_module`]
    /// refuses the function by name.
    pub fn alloc_value(&mut self) -> Result<ValueId, IdSpaceExhausted> {
        let taken = self.fresh.take();
        if let Err(exhausted) = taken {
            self.exhausted = Some(exhausted);
        }
        taken
    }
}

/// Outcome of attempting to rewrite a single dialect op.
#[derive(Debug)]
pub enum RewriteOutcome {
    /// The pass does not apply — leave the op alone.
    NoChange,
    /// Replace the op with zero or more replacement nodes. The replacement
    /// nodes inherit the original node's position in the block. The trailing
    /// node may inherit diagnostic span/scope, never proofs or proof context.
    /// Required markers/nonempty call contracts cause refusal even for deletion
    /// (see [`lower_module`]).
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

    /// Whether diagnostic `span` and `scope` are automatically inherited by the
    /// trailing replacement when the pass leaves them absent. Defaults to true.
    ///
    /// The historical name is retained for compatibility, but neither setting
    /// permits automatic proof/context transplantation or bypasses refusal for
    /// required semantic/policy markers. Pass-emitted metadata is left intact;
    /// its producer and independent consumers must establish its validity.
    fn preserves_metadata(&self) -> bool {
        true
    }

    /// Apply the pass to a single dialect op.
    ///
    /// `node` is the full original [`InstrNode`] being rewritten; its
    /// `proofs` / `proof_context` / `span` / `scope` are available so a pass can make
    /// metadata-aware decisions. Only diagnostic metadata may be propagated
    /// automatically — see [`LoweringPass::preserves_metadata`]. `op` is the instruction payload
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
/// [`RewriteOutcome::Err`] or attempts to replace a node with an unmapped
/// required marker/nonempty [`crate::proof::ProofContext`],
/// [`DialectError::ValueIdSpaceExhausted`] when a pass needed a fresh value id
/// the function does not have (a definition holds `u32::MAX`), or
/// [`DialectError::FixpointNotReached`] if the iteration limit is hit while
/// passes are still producing changes. A required-marker refusal occurs before
/// replacing that node, even for deletion or diagnostic-metadata opt-out.
///
/// Lowering mutates in place: an error does not roll back earlier rewrites.
/// Source provenance is invalidated before each replacement is applied, so
/// partially lowered functions cannot retain stale source authority on either
/// error path. This does not revalidate or rebind other proof metadata.
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
            // Fresh ids start one past the highest id the function defines
            // (0 for a function that defines none), and are refused — never
            // wrapped — when a definition already holds `u32::MAX`.
            let mut fresh_values = func.fresh_value_ids();
            let function = func.id;

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
                            fresh: &mut fresh_values,
                            exhausted: None,
                        };
                        let rewritten = pass.rewrite(&block.body[i], op_ref, &results, &mut ctx);
                        if ctx.exhausted.is_some() && !matches!(rewritten, RewriteOutcome::NoChange)
                        {
                            return Err(DialectError::ValueIdSpaceExhausted { function });
                        }
                        match rewritten {
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
                            // No mapping protocol exists here for policy,
                            // semantic markers or call contracts. Check before
                            // either mutation or diagnostic metadata transfer.
                            // NoChange remains untouched, including markers.
                            if let Some(requirement) = unmapped_rewrite_requirement(&block.body[i])
                            {
                                return Err(DialectError::LoweringFailed {
                                    pass: pass_name.to_string(),
                                    reason: format!(
                                        "cannot rewrite {requirement} without an explicit subject/effect mapping"
                                    ),
                                });
                            }
                            // Only non-semantic diagnostics have a generic
                            // carry rule. Never transplant original claims or
                            // proof context, and never overwrite pass metadata.
                            if pass_preserves_metadata && let Some(last) = replacement.last_mut() {
                                let original = &block.body[i];
                                if last.span.is_none() {
                                    last.span = original.span;
                                }
                                if last.scope.is_none() {
                                    last.scope = original.scope;
                                }
                            }
                            let len = replacement.len();
                            // A generic rewrite cannot authenticate a new body
                            // against the compiler's source-loop/place mapping.
                            // Invalidate before mutating, including deletions:
                            // later passes may fail and return this partial IR.
                            func.source_provenance = None;
                            // The license's evidence names the old body's
                            // digest (v61): drop it for the same reason
                            // (`Function::invalidate_gate_evidence`, spelled
                            // on the field: `block` borrows `func.blocks`).
                            if let Some(crate::BodyGate::Gated { evidence, .. }) =
                                &mut func.body_gate
                            {
                                *evidence = None;
                            }
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
#[path = "lowering_metadata_tests.rs"]
mod metadata_tests;

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

    /// Pass that rewrites `test.fresh` into a `Const` bound to ONE fresh id
    /// taken from the context.
    struct FreshConst;
    impl LoweringPass for FreshConst {
        fn name(&self) -> &'static str {
            "fresh-const"
        }
        fn rewrite(
            &self,
            _node: &InstrNode,
            op: &DialectInst,
            _results: &[ValueId],
            ctx: &mut LoweringContext<'_>,
        ) -> RewriteOutcome {
            if op.qualified_name() != "test.fresh" {
                return RewriteOutcome::NoChange;
            }
            match ctx.alloc_value() {
                Ok(fresh) => RewriteOutcome::Replace(vec![
                    InstrNode::new(Inst::Const {
                        value: crate::constant::Constant::Int(1),
                        ty: Ty::I64,
                    })
                    .with_result(fresh),
                ]),
                Err(exhausted) => RewriteOutcome::Err(exhausted.to_string()),
            }
        }
    }

    /// r11 sibling l (port of probe P9, evidence kind ii). A function that
    /// defines `ValueId(u32::MAX)` has no fresh value id. Before r11 the seed
    /// `max_value_id() + 1` was computed eagerly for EVERY function, so the
    /// probe's module (no dialect op at all) panicked in debug and wrapped to
    /// id 0 in release. Now the seed is the one fresh-id rule: a function that
    /// needs no fresh id lowers (laziness), and one that does is refused by
    /// name, typed. Mutation check: re-seeding with `max_value_id() + 1`
    /// panics on the first half.
    #[test]
    fn lowering_refuses_a_fresh_value_id_past_u32_max() {
        let block_at_max = |ops: Vec<InstrNode>| {
            let mut module = Module::new("r11_lower");
            let signature = module
                .add_func_type(crate::ty::FuncTy {
                    params: vec![Ty::I32],
                    returns: vec![Ty::I32],
                    is_vararg: false,
                    abi: None,
                })
                .expect("Module::add_func_type: test fixture");
            let mut function = Function::new(FuncId::new(0), "f", signature, BlockId::new(0));
            let mut block = Block::new(BlockId::new(0));
            block.params.push((ValueId::new(u32::MAX), Ty::I32));
            block.body.extend(ops);
            block.body.push(InstrNode::new(Inst::Return {
                values: vec![ValueId::new(u32::MAX)],
            }));
            function.blocks.push(block);
            module.functions.push(function);
            module
        };
        // The probe's module: nothing to lower, so no fresh id is needed.
        let mut quiet = block_at_max(Vec::new());
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(EraseNoop), Box::new(FreshConst)];
        assert!(lower_module(&mut quiet, &passes, 4).is_ok());

        // A pass that needs a fresh id: refused by name, typed.
        let mut needy = block_at_max(vec![InstrNode::new(Inst::DialectOp(Box::new(
            DialectInst::new("test", "fresh"),
        )))]);
        let refusal = lower_module(&mut needy, &passes, 4).expect_err("no fresh value id is left");
        assert_eq!(
            refusal,
            DialectError::ValueIdSpaceExhausted {
                function: FuncId::new(0)
            }
        );
        assert!(
            refusal
                .to_string()
                .contains("the ValueId id space is exhausted")
        );

        // A function that defines NO value gets id 0 first (the old seed was 1).
        let mut empty = module_with_dialect_ops(vec![DialectInst::new("test", "fresh")]);
        lower_module(&mut empty, &passes, 4).expect("id 0 is fresh");
        assert_eq!(
            empty.functions[0].blocks[0].body[0].results,
            vec![ValueId::new(0)]
        );
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    fn source_bound_module(function_ops: &[&[&str]]) -> Module {
        let mut module = Module::new("source_bound_lowering");
        let signature = module
            .add_func_type(crate::ty::FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for (index, ops) in function_ops.iter().enumerate() {
            let id = FuncId::new(u32::try_from(index).unwrap());
            let mut function = Function::new(id, format!("f{index}"), signature, BlockId::new(0));
            let mut block = Block::new(BlockId::new(0));
            for (value, op) in ops.iter().enumerate() {
                let mut dialect = DialectInst::new("test", *op);
                let results = if *op == "const42" {
                    dialect = dialect.with_result_ty(Ty::I64);
                    vec![ValueId::new(u32::try_from(value).unwrap())]
                } else {
                    Vec::new()
                };
                let mut node = InstrNode::new(Inst::DialectOp(Box::new(dialect)));
                node.results = results;
                block.body.push(node);
            }
            block.body.push(InstrNode::new(Inst::Br {
                target: BlockId::new(0),
                args: Vec::new(),
            }));
            function.blocks.push(block);
            module
                .try_add_function(function)
                .expect("Module::try_add_function: test fixture");
        }
        for index in 0..module.functions.len() {
            let digest = module
                .source_provenance_semantic_digest(module.functions[index].id)
                .unwrap();
            module.functions[index].source_provenance = Some(crate::SourceProvenance::new(
                crate::proof::ProofDigest::sha256([1; 32]),
                digest,
                vec![crate::SourceLoopProvenance {
                    source_loop_id: 0,
                    hir_local_id: 1,
                    header: BlockId::new(0),
                    bindings: Vec::new(),
                }],
            ));
            // v61: a license whose evidence names the body as built.
            let body_digest = module
                .function_body_digest(module.functions[index].id)
                .unwrap();
            module.functions[index].body_gate = Some(crate::BodyGate::Gated {
                authority: "clean-kernel-tv".into(),
                evidence: Some(crate::GateEvidence {
                    obligation: crate::ProofId::new(0),
                    body_digest,
                }),
            });
        }
        module
    }

    #[test]
    fn lower_replacements_and_deletions_invalidate_only_changed_source_provenance() {
        for op in ["const42", "noop"] {
            let mut module = source_bound_module(&[&[op], &["stay"]]);
            let original = module.clone();
            let passes: Vec<Box<dyn LoweringPass>> =
                vec![Box::new(ConstLower), Box::new(EraseNoop)];

            let result = lower_module(&mut module, &passes, 8).unwrap();

            assert_eq!(result.rewrites_applied, 1);
            assert_ne!(
                module.source_provenance_semantic_digest(FuncId::new(0)),
                original.source_provenance_semantic_digest(FuncId::new(0)),
                "the original carrier's body identity must no longer describe the rewrite"
            );
            assert!(module.functions[0].source_provenance.is_none());
            // The license survives the rewrite; its evidence, which names the
            // old body's digest, does not.
            assert_eq!(
                module.functions[0].body_gate,
                Some(crate::BodyGate::gated("clean-kernel-tv"))
            );
            assert_ne!(
                module.function_body_digest(FuncId::new(0)),
                original.function_body_digest(FuncId::new(0)),
                "control: the rewrite moved the body digest the evidence named"
            );
            assert_eq!(module.functions[1], original.functions[1]);
        }
    }

    #[test]
    fn lower_partial_error_invalidates_every_changed_function_and_preserves_untouched_ones() {
        let mut module = source_bound_module(&[&["const42"], &["noop", "fail"], &["const42"]]);
        let original = module.clone();
        let passes: Vec<Box<dyn LoweringPass>> = vec![
            Box::new(ConstLower),
            Box::new(EraseNoop),
            Box::new(AlwaysErr),
        ];

        let error = lower_module(&mut module, &passes, 8).unwrap_err();

        assert!(matches!(error, DialectError::LoweringFailed { .. }));
        assert!(matches!(
            module.functions[0].blocks[0].body[0].inst,
            Inst::Const { .. }
        ));
        assert!(module.functions[0].source_provenance.is_none());
        assert!(module.functions[1].source_provenance.is_none());
        assert_eq!(module.functions[2], original.functions[2]);
    }

    #[test]
    fn lower_no_change_and_failures_before_rewrite_preserve_source_provenance() {
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(ConstLower), Box::new(AlwaysErr)];
        for (op, max_iters) in [("stay", 8), ("fail", 8), ("const42", 0)] {
            let mut module = source_bound_module(&[&[op]]);
            let original = module.clone();

            let result = lower_module(&mut module, &passes, max_iters);

            assert_eq!(result.is_ok(), op == "stay");
            assert_eq!(module, original);
        }
    }

    #[test]
    fn lower_fixpoint_exhaustion_drops_changed_source_provenance() {
        let mut module = source_bound_module(&[&["const42"], &["stay"]]);
        let original = module.clone();
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(ConstLower)];

        let error = lower_module(&mut module, &passes, 1).unwrap_err();

        assert!(matches!(
            error,
            DialectError::FixpointNotReached { max_iters: 1 }
        ));
        assert!(matches!(
            module.functions[0].blocks[0].body[0].inst,
            Inst::Const { .. }
        ));
        assert!(module.functions[0].source_provenance.is_none());
        assert_eq!(module.functions[1], original.functions[1]);
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

    /// Only diagnostics survive automatically, even when the final result ID
    /// remains identical. An empty call context supplies no requirement.
    #[test]
    fn lower_carries_only_diagnostics_onto_replacement() {
        use crate::proof::{ProofAnnotation, ProofContext};
        use crate::value::SourceSpan;

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
        let proof_ctx = ProofContext::default();
        let mut module = module_with_dialect_ops(vec![DialectInst::new("test", "proven")]);
        {
            let node = &mut module.functions[0].blocks[0].body[0];
            node.results = vec![ValueId::new(0)];
            // None of these claims is automatically true of the replacement.
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
        assert!(node.proofs.is_empty());
        assert_eq!(node.span, Some(span));
        assert_eq!(node.scope, Some(7));
        assert_eq!(node.proof_context, None);
        assert_eq!(node.results, vec![ValueId::new(0)]);
    }

    /// Neither claims nor required markers can transfer without a mapping.
    #[test]
    fn annotation_transplant_classification_is_conservative() {
        use crate::inst::Ordering;
        use crate::proof::ProofAnnotation as P;

        // Claims about the original computation cannot be transplanted.
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

        // Value/scope claims and semantic markers cannot be transplanted either.
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
                !annotation_survives_lowering_transplant(&a),
                "{a:?} must not auto-transplant onto an unrelated node"
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

    /// Pass metadata is retained without adding original claims to it.
    #[test]
    fn lower_keeps_pass_metadata_without_unioning_original_claims() {
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
            // The pass emits Pure, but does not re-establish the other claims.
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
        assert!(!node.proofs.contains(&ProofAnnotation::ParallelMap));
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
