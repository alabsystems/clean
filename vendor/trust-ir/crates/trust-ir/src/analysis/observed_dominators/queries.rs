// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

impl DominatorTree {
    /// Original fail-closed reachable membership, under the original session.
    pub fn is_reachable_observed<O: ExecutionObserver>(
        &self,
        block: BlockId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        query(session, site, |work| reachable(self, block, work))
    }
    /// Original strict tour-interval query; no new traversal or authority.
    pub fn strictly_dominates_observed<O: ExecutionObserver>(
        &self,
        dominator: BlockId,
        block: BlockId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        query(session, site, |work| strict(self, dominator, block, work))
    }
    /// Original exact canonical-edge query, retaining parallel edge identities.
    pub fn edge_dominates_observed<O: ExecutionObserver>(
        &self,
        source: BlockId,
        successor: usize,
        block: BlockId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        query(session, site, |work| {
            edge(self, source, successor, block, work)
        })
    }
    /// Original coordinate-bounded definition availability, including only
    /// Invoke/InvokeIndirect results on their normal edge. This is no SSA proof.
    pub fn definition_available_at_observed<O: ExecutionObserver>(
        &self,
        definition: SsaDefinitionSite,
        use_site: SsaUseSite,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        query(session, site, |work| {
            available(self, definition, use_site, work)
        })
    }
}

fn query<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    operation: impl FnOnce(&mut Work<'_, '_, O>) -> R<bool>,
) -> R<bool> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<Work<'_, '_, O>>() + size_of::<bool>())?;
    match operation(&mut work) {
        Ok(value) => {
            work.publication(size_of::<bool>())?;
            Ok(value)
        }
        Err(error) => Err(work.terminal(error)),
    }
}

pub(super) fn reachable<O: ExecutionObserver>(
    tree: &DominatorTree,
    block: BlockId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.poll()?;
    if !tree.well_formed {
        return Ok(false);
    }
    work.contains(&tree.reachable, block.index())
}

fn strict<O: ExecutionObserver>(
    tree: &DominatorTree,
    dominator: BlockId,
    block: BlockId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.poll()?;
    if !tree.well_formed || dominator == block {
        return Ok(false);
    }
    let dom_in = work.read(&tree.preorder, &dominator.index())?;
    let dom_out = work.read(&tree.postorder, &dominator.index())?;
    let (Some(dom_in), Some(dom_out)) = (dom_in, dom_out) else {
        return Ok(false);
    };
    let block_in = work.read(&tree.preorder, &block.index())?;
    let block_out = work.read(&tree.postorder, &block.index())?;
    let (Some(block_in), Some(block_out)) = (block_in, block_out) else {
        return Ok(false);
    };
    Ok(dom_in < block_in && block_out < dom_out)
}

pub(super) fn dominates<O: ExecutionObserver>(
    tree: &DominatorTree,
    dominator: BlockId,
    block: BlockId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    Ok(reachable(tree, block, work)?
        && (dominator == block || strict(tree, dominator, block, work)?))
}

fn edge<O: ExecutionObserver>(
    tree: &DominatorTree,
    source: BlockId,
    successor: usize,
    block: BlockId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    match work.read(&tree.dominating_edges, &(source.index(), successor))? {
        Some(target) => dominates(tree, BlockId::new(target), block, work),
        None => Ok(false),
    }
}

fn available<O: ExecutionObserver>(
    tree: &DominatorTree,
    definition: SsaDefinitionSite,
    use_site: SsaUseSite,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let use_block = use_site.block();
    if !reachable(tree, use_block, work)? {
        return Ok(false);
    }
    let Some(count) = work.read(&tree.instruction_counts, &definition.block.index())? else {
        return Ok(false);
    };
    if definition.instruction.is_some_and(|index| index >= count) {
        return Ok(false);
    }
    let use_instruction = match use_site {
        SsaUseSite::BeforeInstruction { instruction, .. } => {
            if work
                .read(&tree.instruction_counts, &use_block.index())?
                .is_none_or(|count| instruction >= count)
            {
                return Ok(false);
            }
            instruction
        }
        SsaUseSite::InvokeNormalEdge { .. } => {
            let Some(instruction) = work.read(&tree.invoke_instructions, &use_block.index())?
            else {
                return Ok(false);
            };
            if definition.block == use_block && definition.instruction == Some(instruction) {
                return Ok(true);
            }
            instruction
        }
    };
    if let Some(index) = definition.instruction
        && work.read(&tree.invoke_instructions, &definition.block.index())? == Some(index)
    {
        return Ok(
            definition.block != use_block && edge(tree, definition.block, 0, use_block, work)?
        );
    }
    if definition.block == use_block {
        Ok(definition
            .instruction
            .is_none_or(|index| index < use_instruction))
    } else {
        strict(tree, definition.block, use_block, work)
    }
}
