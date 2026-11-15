// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Driver-policy tests, not rewrite-refinement proofs. The generic driver can
//! receive unfinished IR; downstream module validation remains a separate gate.

use super::*;
use crate::constant::Constant;
use crate::inst::Ordering;
use crate::proof::{Divergence, ProofAnnotation as P, ProofContext, ProofDigest};
use crate::ty::{FuncTy, Ty};
use crate::value::{BlockId, FuncId, ProofId, ProofTag, SourceSpan};
use crate::{Block, Function};

fn claims() -> Vec<P> {
    vec![
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
        P::Pure,
        P::Terminates,
        P::Deterministic,
        P::Associative,
        P::Commutative,
        P::DataRaceFree,
        P::BoundedOutput { lo: 0.0, hi: 7.0 },
        P::Monotonic,
        P::NoAlias,
        P::Aligned(16),
        P::NoPanic,
        P::NoUndef,
        P::ParallelMap,
        P::BoundedLoop(8),
        P::ValueRange { lo: 0, hi: 7 },
        P::KnownBits { zeros: 0, ones: 1 },
        P::BranchWeights(vec![1, 2]),
        P::ProofRef(ProofId::new(3)),
    ]
}

fn required_markers() -> Vec<P> {
    vec![
        P::Wrapping,
        P::AtomicOrdering(Ordering::SeqCst),
        P::Tainted,
        P::TrustedSink,
        P::ReadonlyTable,
        P::AppendOnlyBuffer,
        P::AtomicSetInsert,
        P::DivergenceClass(Divergence::Uniform),
        P::DivergenceClass(Divergence::Low),
        P::DivergenceClass(Divergence::High),
        P::FreshSymbolicHavoc,
        P::RegionHavocStore,
        P::Custom(ProofTag::new(19)),
    ]
}

fn fixture() -> Module {
    let mut module = Module::new("rewrite_metadata");
    let signature = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "subject", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(
            DialectInst::new("test", "subject").with_result_ty(Ty::I64),
        )))
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let mut callee = Function::new(FuncId::new(1), "callee", signature, BlockId::new(0));
    let mut body = Block::new(BlockId::new(0));
    body.body.push(
        InstrNode::new(Inst::Const {
            value: Constant::Int(42),
            ty: Ty::I64,
        })
        .with_result(ValueId::new(0)),
    );
    body.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    callee.blocks.push(body);
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
    let semantic = module
        .source_provenance_semantic_digest(FuncId::new(0))
        .unwrap();
    module.functions[0].source_provenance = Some(crate::SourceProvenance::new(
        ProofDigest::sha256([7; 32]),
        semantic,
        Vec::new(),
    ));
    module
}

#[derive(Clone, Copy)]
enum Shape {
    Constant,
    Call,
    CallThenConstant,
    Erase,
    NoChange,
}

struct Rewrite {
    shape: Shape,
    carry_diagnostics: bool,
    proofs: Vec<P>,
    context: Option<ProofContext>,
    span: Option<SourceSpan>,
    scope: Option<u32>,
}

impl Rewrite {
    fn new(shape: Shape, carry_diagnostics: bool) -> Self {
        Self {
            shape,
            carry_diagnostics,
            proofs: Vec::new(),
            context: None,
            span: None,
            scope: None,
        }
    }
}

impl LoweringPass for Rewrite {
    fn name(&self) -> &'static str {
        "metadata-candidate"
    }

    fn preserves_metadata(&self) -> bool {
        self.carry_diagnostics
    }

    fn rewrite(
        &self,
        _node: &InstrNode,
        op: &DialectInst,
        results: &[ValueId],
        context: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        if op.qualified_name() != "test.subject" || matches!(self.shape, Shape::NoChange) {
            return RewriteOutcome::NoChange;
        }
        if matches!(self.shape, Shape::Erase) {
            return RewriteOutcome::Replace(Vec::new());
        }
        let instruction = if matches!(self.shape, Shape::Call | Shape::CallThenConstant) {
            Inst::Call {
                callee: FuncId::new(1),
                args: Vec::new(),
            }
        } else {
            Inst::Const {
                value: Constant::Int(42),
                ty: Ty::I64,
            }
        };
        let mut node = InstrNode::new(instruction).with_results(results.iter().copied());
        node.proofs = self.proofs.clone();
        node.proof_context = self.context.clone();
        node.span = self.span;
        node.scope = self.scope;
        let mut replacement = vec![node];
        if matches!(self.shape, Shape::CallThenConstant) {
            let fresh = match context.alloc_value() {
                Ok(fresh) => fresh,
                Err(exhausted) => return RewriteOutcome::Err(exhausted.to_string()),
            };
            replacement.push(
                InstrNode::new(Inst::Const {
                    value: Constant::Int(-1),
                    ty: Ty::I64,
                })
                .with_result(fresh),
            );
        }
        RewriteOutcome::Replace(replacement)
    }
}

fn run(module: &mut Module, rewrite: Rewrite) -> Result<LoweringResult, DialectError> {
    lower_module(module, &[Box::new(rewrite)], 8)
}

#[test]
fn metadata_disposition_census_has_no_automatic_transfer() {
    for annotation in claims() {
        assert_eq!(
            annotation_rewrite_disposition(&annotation),
            AnnotationRewriteDisposition::DropClaimOrHint
        );
        assert!(!annotation_survives_lowering_transplant(&annotation));
    }
    for annotation in required_markers() {
        assert_eq!(
            annotation_rewrite_disposition(&annotation),
            AnnotationRewriteDisposition::RequiresMappedRewrite
        );
        assert!(!annotation_survives_lowering_transplant(&annotation));
    }
}

#[test]
fn metadata_original_claims_do_not_follow_result_or_trailing_node() {
    let mut module = fixture();
    let source = &mut module.functions[0].blocks[0].body[0];
    source.proofs = claims();
    source.proof_context = Some(ProofContext::default());
    let span = SourceSpan {
        file: 2,
        line: 3,
        col: 4,
    };
    source.span = Some(span);
    source.scope = Some(9);
    run(&mut module, Rewrite::new(Shape::CallThenConstant, true)).unwrap();
    let body = &module.functions[0].blocks[0].body;
    assert!(matches!(body[0].inst, Inst::Call { .. }));
    assert_eq!(body[0].results, vec![ValueId::new(0)]);
    assert_ne!(body[1].results, body[0].results);
    for node in &body[..2] {
        assert!(node.proofs.is_empty());
        assert!(node.proof_context.is_none());
    }
    assert_eq!(body[1].span, Some(span));
    assert_eq!(body[1].scope, Some(9));
    assert!(module.functions[0].source_provenance.is_none());
}

#[test]
fn metadata_required_markers_refuse_rewrite_delete_and_opt_out() {
    for annotation in required_markers() {
        for shape in [Shape::Constant, Shape::Erase] {
            for carry in [false, true] {
                let mut module = fixture();
                module.functions[0].blocks[0].body[0]
                    .proofs
                    .push(annotation.clone());
                let original = module.clone();
                let error = run(&mut module, Rewrite::new(shape, carry)).unwrap_err();
                assert!(matches!(error, DialectError::LoweringFailed { .. }));
                assert!(
                    error.to_string().contains(annotation.kind_name()),
                    "{error}"
                );
                assert_eq!(
                    module, original,
                    "refused {annotation:?} must not mutate source"
                );
            }
        }
    }
}

#[test]
fn metadata_context_assumptions_and_requirements_refuse_all_replacements() {
    for context in [
        ProofContext {
            assumes: vec![ProofId::new(0)],
            establishes: Vec::new(),
        },
        ProofContext {
            assumes: Vec::new(),
            establishes: vec![ProofId::new(0)],
        },
    ] {
        for shape in [Shape::Constant, Shape::Erase] {
            for carry in [false, true] {
                let mut module = fixture();
                module.functions[0].blocks[0].body[0].proof_context = Some(context.clone());
                let original = module.clone();
                let error = run(&mut module, Rewrite::new(shape, carry)).unwrap_err();
                assert!(error.to_string().contains("nonempty ProofContext"));
                assert_eq!(module, original);
            }
        }
    }
}

#[test]
fn metadata_no_change_preserves_required_markers_and_context_exactly() {
    let mut module = fixture();
    let source = &mut module.functions[0].blocks[0].body[0];
    source.proofs = required_markers();
    source.proofs.extend(claims());
    source.proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(4)],
        establishes: vec![ProofId::new(5)],
    });
    let original = module.clone();
    let outcome = run(&mut module, Rewrite::new(Shape::NoChange, false)).unwrap();
    assert_eq!(outcome.rewrites_applied, 0);
    assert_eq!(module, original);
}

#[test]
fn metadata_explicit_replacement_claims_context_and_diagnostics_are_retained() {
    let mut module = fixture();
    let source = &mut module.functions[0].blocks[0].body[0];
    source.proofs = vec![P::Pure, P::NoAlias];
    source.span = Some(SourceSpan {
        file: 1,
        line: 1,
        col: 1,
    });
    source.scope = Some(1);
    let mut rewrite = Rewrite::new(Shape::Call, true);
    rewrite.proofs = vec![P::Tainted, P::NoPanic];
    rewrite.context = Some(ProofContext {
        assumes: vec![ProofId::new(9)],
        establishes: Vec::new(),
    });
    rewrite.span = Some(SourceSpan {
        file: 2,
        line: 2,
        col: 2,
    });
    rewrite.scope = Some(2);
    let expected_proofs = rewrite.proofs.clone();
    let expected_context = rewrite.context.clone();
    let expected_span = rewrite.span;
    run(&mut module, rewrite).unwrap();
    let node = &module.functions[0].blocks[0].body[0];
    assert_eq!(node.proofs, expected_proofs);
    assert_eq!(node.proof_context, expected_context);
    assert_eq!(node.span, expected_span);
    assert_eq!(node.scope, Some(2));
    // This driver preserves producer metadata; it does not authenticate the
    // intentionally unfinished obligation references in this policy fixture.
}

#[test]
fn metadata_explicit_copy_of_required_marker_is_not_a_mapping() {
    let mut module = fixture();
    module.functions[0].blocks[0].body[0].proofs = vec![P::TrustedSink];
    let original = module.clone();
    let mut rewrite = Rewrite::new(Shape::CallThenConstant, false);
    rewrite.proofs = vec![P::TrustedSink];
    assert!(run(&mut module, rewrite).is_err());
    assert_eq!(module, original);
}

#[test]
fn metadata_opt_out_controls_diagnostics_only() {
    let mut module = fixture();
    let source = &mut module.functions[0].blocks[0].body[0];
    source.proofs = vec![P::Pure];
    source.span = Some(SourceSpan {
        file: 1,
        line: 1,
        col: 1,
    });
    source.scope = Some(1);
    run(&mut module, Rewrite::new(Shape::Constant, false)).unwrap();
    let node = &module.functions[0].blocks[0].body[0];
    assert!(node.proofs.is_empty());
    assert!(node.span.is_none());
    assert!(node.scope.is_none());
}

#[test]
fn metadata_late_refusal_preserves_partial_mutation_contract() {
    let mut module = fixture();
    let mut second = module.functions[0].blocks[0].body[0].clone();
    second.results = vec![ValueId::new(1)];
    second.proofs = vec![P::RegionHavocStore];
    module.functions[0].blocks[0].body.insert(1, second.clone());
    assert!(run(&mut module, Rewrite::new(Shape::Constant, true)).is_err());
    assert!(matches!(
        module.functions[0].blocks[0].body[0].inst,
        Inst::Const { .. }
    ));
    assert_eq!(module.functions[0].blocks[0].body[1], second);
    assert!(module.functions[0].source_provenance.is_none());
}

#[cfg(feature = "clean-expr")]
#[test]
fn metadata_pending_kernel_goal_requires_mapping() {
    let goal = P::Goal(Box::new(crate::proof::ExprObligation::new(
        clean_kernel::Expr::bvar(0),
    )));
    for shape in [Shape::Constant, Shape::Erase] {
        let mut module = fixture();
        module.functions[0].blocks[0].body[0].proofs = vec![goal.clone()];
        let original = module.clone();
        let error = run(&mut module, Rewrite::new(shape, false)).unwrap_err();
        assert!(error.to_string().contains("Goal"));
        assert_eq!(module, original);
    }
}
