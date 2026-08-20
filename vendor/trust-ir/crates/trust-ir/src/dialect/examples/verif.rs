// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Feature-gated `verif` reference dialect.
//!
//! This module demonstrates builders, validation, and lowering for a
//! `verif.*` dialect. The stable contract is the serialized `DialectInst`
//! payload documented in `docs/dialects.md`; this module is helper/reference
//! surface only.
//!
//! Three ops are defined:
//!
//! - `verif.bfs_step` — advance a TLA+ BFS model checker by one step.
//!   Takes the current frontier as an operand, produces the next frontier.
//! - `verif.frontier_drain` — assert that a frontier is empty; lowers to a
//!   no-op once the assertion is discharged by a proof.
//! - `verif.fingerprint_batch` — hash a batch of states into a fingerprint
//!   set. Takes the state array, produces a set-reference.
//!
//! The dialect demonstrates three lowering shapes:
//!
//! 1. **Progressive lowering.** `bfs_step` lowers into a stage-2 internal op
//!    (`verif.bfs_step_lowered`), which a second pass rewrites into a
//!    generic `Inst::Call` to a runtime helper. This shows that dialect ops
//!    can target another dialect (or a stage of themselves) before bottoming
//!    out at core TrustIr.
//! 2. **Assertion erasure.** `frontier_drain` deletes once discharged —
//!    models the rule that proven invariants are removed from the executable
//!    IR but retained in the proof log.
//! 3. **Identity-to-core.** `fingerprint_batch` rewrites directly to a core
//!    `Inst::Call` with a conventional name.
//!
//! Real ty integration will use richer payloads (batch sizes, chunking,
//! GPU tags); this example keeps the shape minimal to stay readable.

use crate::dialect::lowering::LoweringContext;
use crate::dialect::{AttrValue, Dialect, DialectError, DialectInst, LoweringPass, RewriteOutcome};
use crate::inst::Inst;
use crate::node::InstrNode;
use crate::ty::Ty;
use crate::value::{FuncId, ValueId};

/// Qualified name of the BFS-step op.
pub const BFS_STEP: &str = "verif.bfs_step";

/// Qualified name of the frontier-drain op.
pub const FRONTIER_DRAIN: &str = "verif.frontier_drain";

/// Qualified name of the fingerprint-batch op.
pub const FINGERPRINT_BATCH: &str = "verif.fingerprint_batch";

/// Stage-2 internal op: not intended for frontend use.
const BFS_STEP_LOWERED: &str = "verif.bfs_step_lowered";

/// Builder for a `verif.bfs_step` op.
///
/// Operands: `frontier`, `seen_set`. Result: next frontier (Ptr).
/// Optional attribute `parallel` (bool) hints at GPU eligibility.
pub fn bfs_step(frontier: ValueId, seen_set: ValueId, parallel: bool) -> DialectInst {
    DialectInst::new("verif", "bfs_step")
        .with_operand(frontier)
        .with_operand(seen_set)
        .with_result_ty(Ty::Ptr)
        .with_attr("parallel", AttrValue::Bool(parallel))
}

/// Builder for a `verif.frontier_drain` op.
///
/// Operand: `frontier`. Produces nothing — semantically it asserts the
/// frontier is empty, which after proof discharge becomes a no-op.
pub fn frontier_drain(frontier: ValueId) -> DialectInst {
    DialectInst::new("verif", "frontier_drain").with_operand(frontier)
}

/// Builder for a `verif.fingerprint_batch` op.
///
/// Operands: `state_array`, `count`. Result: fingerprint set (Ptr).
pub fn fingerprint_batch(states: ValueId, count: ValueId) -> DialectInst {
    DialectInst::new("verif", "fingerprint_batch")
        .with_operand(states)
        .with_operand(count)
        .with_result_ty(Ty::Ptr)
}

/// The `verif` dialect.
///
/// Register with a `DialectRegistry` to enable lowering of `verif.*` ops.
#[derive(Default)]
pub struct VerifDialect;

impl Dialect for VerifDialect {
    fn name(&self) -> &'static str {
        "verif"
    }

    fn version(&self) -> u32 {
        1
    }

    fn ops(&self) -> &'static [&'static str] {
        &[
            "bfs_step",
            "bfs_step_lowered",
            "frontier_drain",
            "fingerprint_batch",
        ]
    }

    fn validate(&self, inst: &DialectInst) -> Result<(), DialectError> {
        inst.validate_names()?;
        if inst.dialect != "verif" {
            return Err(DialectError::NameMismatch {
                expected: "verif",
                got: inst.dialect.clone(),
            });
        }
        if inst.version != self.version() {
            return Err(DialectError::LoweringFailed {
                pass: "verif.validate".into(),
                reason: format!(
                    "verif dialect version {} is unsupported; expected {}",
                    inst.version,
                    self.version()
                ),
            });
        }
        if !self.has_op(&inst.op) {
            return Err(DialectError::UnknownOp {
                dialect: "verif",
                op: inst.op.clone(),
            });
        }
        // Op-specific invariants.
        let expected_operands = match inst.op.as_str() {
            "bfs_step" => Some(2),
            "frontier_drain" => Some(1),
            "fingerprint_batch" => Some(2),
            _ => None,
        };
        if let Some(expected) = expected_operands
            && inst.operands.len() != expected
        {
            return Err(DialectError::LoweringFailed {
                pass: "verif.validate".into(),
                reason: format!(
                    "verif.{} expects {} operands, got {}",
                    inst.op,
                    expected,
                    inst.operands.len()
                ),
            });
        }
        Ok(())
    }

    fn lowerings(&self) -> Vec<Box<dyn LoweringPass>> {
        vec![
            Box::new(FrontierDrainErase),
            Box::new(BfsStepStage1),
            Box::new(BfsStepStage2),
            Box::new(FingerprintBatchLower),
        ]
    }
}

/// Pass 1: erase `verif.frontier_drain`. Models proof-discharge.
struct FrontierDrainErase;
impl LoweringPass for FrontierDrainErase {
    fn name(&self) -> &'static str {
        "verif.frontier_drain_erase"
    }
    fn rewrite(
        &self,
        _node: &InstrNode,
        op: &DialectInst,
        _results: &[ValueId],
        _ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        if op.qualified_name() == FRONTIER_DRAIN {
            RewriteOutcome::Replace(Vec::new())
        } else {
            RewriteOutcome::NoChange
        }
    }
}

/// Pass 2: `verif.bfs_step` -> `verif.bfs_step_lowered`.
struct BfsStepStage1;
impl LoweringPass for BfsStepStage1 {
    fn name(&self) -> &'static str {
        "verif.bfs_step_stage1"
    }
    fn rewrite(
        &self,
        _node: &InstrNode,
        op: &DialectInst,
        results: &[ValueId],
        _ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        if op.qualified_name() != BFS_STEP {
            return RewriteOutcome::NoChange;
        }
        let mut lowered = DialectInst::new("verif", "bfs_step_lowered")
            .with_operands(op.operands.iter().copied());
        for t in &op.result_tys {
            lowered = lowered.with_result_ty(t.clone());
        }
        for a in &op.attrs {
            lowered = lowered.with_attr(a.name.clone(), a.value.clone());
        }
        let mut node = InstrNode::new(Inst::DialectOp(Box::new(lowered)));
        node.results = results.to_vec();
        RewriteOutcome::Replace(vec![node])
    }
}

/// Pass 3: `verif.bfs_step_lowered` -> runtime call.
///
/// ILLUSTRATIVE ONLY: the lowered op is replaced by a call to the hardcoded
/// function id `0`. This is a teaching stand-in for a runtime helper — there is
/// no real symbol table in this reference dialect. A production frontend/backend
/// resolves the callee BY NAME against the module's function table (returning a
/// lowering error when the helper is missing) instead of inventing a `FuncId`.
struct BfsStepStage2;
impl LoweringPass for BfsStepStage2 {
    fn name(&self) -> &'static str {
        "verif.bfs_step_stage2"
    }
    fn rewrite(
        &self,
        _node: &InstrNode,
        op: &DialectInst,
        results: &[ValueId],
        _ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        if op.qualified_name() != BFS_STEP_LOWERED {
            return RewriteOutcome::NoChange;
        }
        // Illustrative hardcoded callee — see the struct doc comment.
        let mut node = InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: op.operands.clone(),
        });
        node.results = results.to_vec();
        RewriteOutcome::Replace(vec![node])
    }
}

/// Pass 4: `verif.fingerprint_batch` -> runtime call.
///
/// ILLUSTRATIVE ONLY: like [`BfsStepStage2`], the callee `FuncId::new(1)` is a
/// hardcoded teaching stand-in, not a resolved symbol. A real frontend resolves
/// the fingerprint runtime helper by name; this example keeps the shape minimal.
struct FingerprintBatchLower;
impl LoweringPass for FingerprintBatchLower {
    fn name(&self) -> &'static str {
        "verif.fingerprint_batch_lower"
    }
    fn rewrite(
        &self,
        _node: &InstrNode,
        op: &DialectInst,
        results: &[ValueId],
        _ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        if op.qualified_name() != FINGERPRINT_BATCH {
            return RewriteOutcome::NoChange;
        }
        // Illustrative hardcoded callee — see the struct doc comment.
        let mut node = InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: op.operands.clone(),
        });
        node.results = results.to_vec();
        RewriteOutcome::Replace(vec![node])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{DialectRegistry, LoweringPass, lower_module};
    use crate::node::InstrNode;
    use crate::value::{BlockId, FuncId, FuncTyId, ValueId};
    use crate::{Block, Function, Module};

    fn module_with(ops: Vec<DialectInst>) -> Module {
        let mut m = Module::new("verif_test");
        let mut f = Function::new(FuncId::new(0), "main", FuncTyId::new(0), BlockId::new(0));
        let mut b = Block::new(BlockId::new(0));
        for (i, op) in ops.into_iter().enumerate() {
            let mut node = InstrNode::new(Inst::DialectOp(Box::new(op)));
            // Assign one result id per node so downstream passes can preserve it.
            node.results = vec![ValueId::new(i as u32 + 100)];
            b.body.push(node);
        }
        f.blocks.push(b);
        m.add_function(f);
        m
    }

    #[test]
    fn registry_accepts_verif_dialect() {
        let mut reg = DialectRegistry::new();
        reg.register(Box::new(VerifDialect));
        assert!(reg.is_registered("verif"));
        assert_eq!(reg.passes().len(), 4);
    }

    #[test]
    fn validate_accepts_well_formed_ops() {
        let d = VerifDialect;
        let bfs = bfs_step(ValueId::new(0), ValueId::new(1), true);
        assert!(d.validate(&bfs).is_ok());
        let fp = fingerprint_batch(ValueId::new(2), ValueId::new(3));
        assert!(d.validate(&fp).is_ok());
        let drain = frontier_drain(ValueId::new(4));
        assert!(d.validate(&drain).is_ok());
    }

    #[test]
    fn validate_rejects_wrong_operand_count() {
        let d = VerifDialect;
        let bad = DialectInst::new("verif", "bfs_step").with_operand(ValueId::new(0));
        assert!(d.validate(&bad).is_err());
    }

    #[test]
    fn validate_rejects_unknown_version() {
        let d = VerifDialect;
        let bad = DialectInst::new("verif", "fingerprint_batch")
            .with_operand(ValueId::new(0))
            .with_operand(ValueId::new(1))
            .with_result_ty(Ty::Ptr)
            .with_version(2);
        let err = d.validate(&bad).expect_err("version mismatch must fail");
        let msg = format!("{err}");
        assert!(
            msg.contains("unsupported"),
            "expected unsupported-version diagnostic, got: {msg}"
        );
    }

    #[test]
    fn frontier_drain_is_erased_by_lowering() {
        let mut reg = DialectRegistry::new();
        reg.register(Box::new(VerifDialect));
        let mut module = module_with(vec![frontier_drain(ValueId::new(0))]);
        let result = reg.lower(&mut module, 8).unwrap();
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 1);
        assert!(module.functions[0].blocks[0].body.is_empty());
    }

    #[test]
    fn bfs_step_lowers_in_two_stages_to_call() {
        let mut reg = DialectRegistry::new();
        reg.register(Box::new(VerifDialect));
        let mut module = module_with(vec![bfs_step(ValueId::new(0), ValueId::new(1), false)]);
        let result = reg.lower(&mut module, 8).unwrap();
        assert!(result.fixpoint_reached);
        // Exactly two rewrites: stage1 (bfs_step -> stage2 op) and stage2
        // (stage2 op -> call). Final body is one `Call` node.
        assert_eq!(result.rewrites_applied, 2);
        let body = &module.functions[0].blocks[0].body;
        assert_eq!(body.len(), 1);
        assert!(matches!(body[0].inst, Inst::Call { .. }));
        // Result ID preserved end-to-end.
        assert_eq!(body[0].results, vec![ValueId::new(100)]);
    }

    #[test]
    fn fingerprint_batch_lowers_to_call() {
        let mut reg = DialectRegistry::new();
        reg.register(Box::new(VerifDialect));
        let mut module = module_with(vec![fingerprint_batch(ValueId::new(0), ValueId::new(1))]);
        let result = reg.lower(&mut module, 8).unwrap();
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 1);
        let body = &module.functions[0].blocks[0].body;
        assert_eq!(body.len(), 1);
        if let Inst::Call { callee, args } = &body[0].inst {
            assert_eq!(*callee, FuncId::new(1));
            assert_eq!(args, &vec![ValueId::new(0), ValueId::new(1)]);
        } else {
            panic!("expected Call, got {:?}", body[0].inst);
        }
    }

    #[test]
    fn mixed_verif_module_fully_lowers() {
        let mut reg = DialectRegistry::new();
        reg.register(Box::new(VerifDialect));
        let mut module = module_with(vec![
            bfs_step(ValueId::new(0), ValueId::new(1), true),
            frontier_drain(ValueId::new(2)),
            fingerprint_batch(ValueId::new(3), ValueId::new(4)),
        ]);
        let result = reg.lower(&mut module, 16).unwrap();
        assert!(result.fixpoint_reached);
        // No dialect ops should remain.
        for block in &module.functions[0].blocks {
            for node in &block.body {
                assert!(
                    !matches!(node.inst, Inst::DialectOp(_)),
                    "unexpected dialect op survived: {:?}",
                    node.inst
                );
            }
        }
        // Two calls (bfs_step, fingerprint_batch); frontier_drain erased.
        let calls: usize = module.functions[0].blocks[0]
            .body
            .iter()
            .filter(|n| matches!(n.inst, Inst::Call { .. }))
            .count();
        assert_eq!(calls, 2);
    }

    #[test]
    fn lower_module_direct_also_works() {
        // Sanity check: verify we can use the standalone `lower_module` entry
        // point without going through the registry, as long as we assemble
        // the pass list ourselves.
        let dialect = VerifDialect;
        let passes: Vec<Box<dyn LoweringPass>> = dialect.lowerings();
        let mut module = module_with(vec![fingerprint_batch(ValueId::new(0), ValueId::new(1))]);
        let result = lower_module(&mut module, &passes, 8).unwrap();
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 1);
    }
}
