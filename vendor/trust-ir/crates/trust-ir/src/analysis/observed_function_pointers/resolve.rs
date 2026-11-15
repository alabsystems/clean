// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn run<'f, O: ExecutionObserver>(
    function: &'f Function,
    state: &mut State<'f>,
    value: ValueId,
    use_block: BlockId,
    index: usize,
    work: &mut Work<'_, '_, O>,
) -> R<Option<StaticFunctionPointerResolution>> {
    work.admit(1, size_of::<Option<StaticFunctionPointerResolution>>())?;
    if !state.use_built {
        state.build_uses(function, work)?;
    }
    let Some(block) = state.use_block(use_block, work)? else {
        return Ok(None);
    };
    let Some(node) = work.at(&block.body, index)? else {
        return Ok(None);
    };
    if !node
        .inst
        .uses_value_operand_observed(value, work.session, work.site)?
    {
        return Ok(None);
    }
    if state.is_parameter(use_block, value, work)? {
        return Ok(None);
    }
    if !state.provenance_built && prefilter::dynamic(block, value, index, work)? {
        return Ok(None);
    }
    if !state.definitions_built {
        state.build_definitions(function, work)?;
    }
    let Some(DefinitionState::Unique {
        instruction: Some(top),
        ..
    }) = work.read(&state.definitions, value.index())?
    else {
        return Ok(None);
    };
    // This helper only matches the outer instruction/type discriminants.
    work.admit(16, size_of::<Option<&Ty>>())?;
    if !matches!(
        static_pointer_definition_type(top),
        Some(Ty::Func(_) | Ty::Ptr)
    ) {
        return Ok(None);
    }
    if state.dominators.is_none() {
        work.admit(1, size_of::<Option<DominatorTree>>())?;
        state.dominators = Some(DominatorTree::new_observed(
            function,
            work.session,
            work.site,
        )?);
    }
    let tree = state
        .dominators
        .as_ref()
        .ok_or(ObservedValueError::InvalidRange)?;
    work.admit(1, size_of::<bool>())?;
    if !tree.is_well_formed() || !tree.is_reachable_observed(use_block, work.session, work.site)? {
        return Ok(None);
    }
    if !state.provenance_built {
        provenance::build(
            &state.definitions,
            tree,
            &mut state.provenances,
            &mut state.active,
            &mut state.path,
            work,
        )?;
        work.admit(1, size_of::<bool>())?;
        state.provenance_built = true;
    }
    let Some(ProvenanceState::Resolved(summary)) = work.read(&state.provenances, value.index())?
    else {
        return Ok(None);
    };
    if !provenance::dominates(
        tree,
        summary.definition_block,
        summary.definition_instruction,
        use_block,
        index,
        work,
    )? {
        return Ok(None);
    }
    work.admit(1, size_of::<StaticFunctionPointerResolution>())?;
    Ok(Some(StaticFunctionPointerResolution {
        containing_function: function.id,
        function: summary.function,
        declared_signature: summary.declared_signature,
        carrier: summary.carrier,
        queried_value: value,
        use_block,
        use_instruction_index: index,
        origin_value: summary.origin_value,
        origin_block: summary.origin_block,
        origin_instruction_index: summary.origin_instruction,
        chain_definitions: summary.chain_definitions,
    }))
}
