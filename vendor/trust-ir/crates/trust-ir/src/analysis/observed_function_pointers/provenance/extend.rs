// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn step<'f, O: ExecutionObserver>(
    child: ProvenanceState<'f>,
    step: ProvenanceStep<'f>,
    tree: &DominatorTree,
    work: &mut Work<'_, '_, O>,
) -> R<ProvenanceState<'f>> {
    work.admit(16, size_of::<ProvenanceState<'_>>())?;
    let ProvenanceState::Resolved(child) = child else {
        return Ok(ProvenanceState::Rejected);
    };
    let (ty, block, index, exact) = match step {
        ProvenanceStep::Copy {
            result_type,
            definition_block,
            definition_instruction,
            ..
        } => {
            let exact =
                child
                    .result_type
                    .structural_eq_observed(result_type, work.session, work.site)?
                    && carrier_for_signature(result_type, child.declared_signature).is_some();
            (result_type, definition_block, definition_instruction, exact)
        }
        ProvenanceStep::Reify {
            source_type,
            result_type,
            definition_block,
            definition_instruction,
            ..
        } => {
            let exact =
                child
                    .result_type
                    .structural_eq_observed(source_type, work.session, work.site)?
                    && matches!(
                        (source_type, result_type),
                        (Ty::Func(_), Ty::Ptr) | (Ty::Ptr, Ty::Func(_))
                    )
                    && carrier_for_signature(source_type, child.declared_signature).is_some()
                    && carrier_for_signature(result_type, child.declared_signature).is_some();
            (result_type, definition_block, definition_instruction, exact)
        }
    };
    if !exact
        || !tree.is_reachable_observed(block, work.session, work.site)?
        || !dominates(
            tree,
            child.definition_block,
            child.definition_instruction,
            block,
            index,
            work,
        )?
    {
        return Ok(ProvenanceState::Rejected);
    }
    work.admit(16, size_of::<ProvenanceState<'_>>())?;
    let Some(carrier) = carrier_for_signature(ty, child.declared_signature) else {
        return Ok(ProvenanceState::Rejected);
    };
    let Some(chain_definitions) = child.chain_definitions.checked_add(1) else {
        return Ok(ProvenanceState::Rejected);
    };
    Ok(ProvenanceState::Resolved(StaticProvenanceSummary {
        carrier,
        result_type: ty,
        definition_block: block,
        definition_instruction: index,
        chain_definitions,
        ..child
    }))
}
pub(in super::super) fn dominates<O: ExecutionObserver>(
    tree: &DominatorTree,
    definition_block: BlockId,
    definition_index: usize,
    use_block: BlockId,
    use_index: usize,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(4, size_of::<bool>())?;
    if definition_block == use_block {
        Ok(definition_index < use_index)
    } else {
        tree.strictly_dominates_observed(definition_block, use_block, work.session, work.site)
    }
}
