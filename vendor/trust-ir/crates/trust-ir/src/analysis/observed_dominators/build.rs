// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

impl<'f> State<'f> {
    pub(super) fn build<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let entry = function.entry.index();
        for block in &function.blocks {
            work.poll()?;
            if !work.mark(&mut self.blocks, block.id.index())? {
                return Ok(false);
            }
        }
        if !work.contains(&self.blocks, entry)? {
            return Ok(false);
        }
        if !self.graph(function, work)? {
            return Ok(false);
        }
        self.reverse_postorder(entry, work)?;
        self.predecessors(work)?;
        if !self.solve(entry, work)? {
            return Ok(false);
        }
        self.children(work)?;
        if !self.tour(entry, work)? {
            return Ok(false);
        }
        work.remove(&mut self.tree.immediate_dominator, &entry)?;
        self.tree.well_formed = true;
        for block in &function.blocks {
            work.poll()?;
            work.insert(
                &mut self.tree.instruction_counts,
                block.id.index(),
                block.body.len(),
            )?;
            if let Some(last) = block.body.last()
                && matches!(last.inst, Inst::Invoke { .. } | Inst::InvokeIndirect { .. })
            {
                work.insert(
                    &mut self.tree.invoke_instructions,
                    block.id.index(),
                    block.body.len() - 1,
                )?;
            }
        }
        self.edge_dominators(entry, work)?;
        Ok(true)
    }
    fn graph<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        for block in &function.blocks {
            work.poll()?;
            let mut terminator = None;
            for (index, node) in block.body.iter().enumerate() {
                work.poll()?;
                if node.is_terminator() {
                    if index + 1 != block.body.len() || terminator.is_some() {
                        return Ok(false);
                    }
                    terminator = Some(node);
                }
            }
            let Some(terminator) = terminator else {
                return Ok(false);
            };
            self.edges = terminator
                .inst
                .successor_edges_observed(work.session, work.site)?;
            for edge in &self.edges {
                work.poll()?;
                let target = edge.target.index();
                if !work.contains(&self.blocks, target)? {
                    return Ok(false);
                }
                work.push(&mut self.targets, target)?;
            }
            work.retire_vec(take(&mut self.edges));
            work.poll()?;
            work.store_row(&mut self.successors, block.id.index(), &mut self.targets)?;
        }
        Ok(true)
    }
    fn reverse_postorder<O: ExecutionObserver>(
        &mut self,
        entry: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.mark(&mut self.tree.reachable, entry)?;
        work.push(&mut self.frames, (entry, 0))?;
        while let Some((block, next)) = self.frames.last().copied() {
            work.poll()?;
            let successor = work
                .row(&self.successors, block)?
                .and_then(|row| row.get(next))
                .copied();
            if let Some(successor) = successor {
                if let Some(frame) = self.frames.last_mut() {
                    frame.1 = frame
                        .1
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                }
                if work.mark(&mut self.tree.reachable, successor)? {
                    work.push(&mut self.frames, (successor, 0))?;
                }
            } else {
                work.push(&mut self.rpo, block)?;
                self.frames.pop();
            }
        }
        for index in 0..self.rpo.len() / 2 {
            work.admit(1, 2 * size_of::<u32>())?;
            let end = self.rpo.len() - 1 - index;
            self.rpo.swap(index, end);
        }
        for (index, &block) in self.rpo.iter().enumerate() {
            work.poll()?;
            work.insert(&mut self.rpo_number, block, index)?;
        }
        Ok(())
    }
    fn predecessors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        for &block in &self.rpo {
            work.poll()?;
            work.ensure_row(&mut self.predecessors, block)?;
        }
        let mut successors = work.entries(&self.successors)?;
        while let Some((&block, targets)) = successors.next(work)? {
            work.poll()?;
            if !work.contains(&self.tree.reachable, block)? {
                continue;
            }
            for &target in targets {
                work.poll()?;
                if work.contains(&self.tree.reachable, target)? {
                    work.append(&mut self.predecessors, target, block)?;
                }
            }
        }
        Ok(())
    }
    fn edge_dominators<O: ExecutionObserver>(
        &mut self,
        entry: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut successors = work.entries(&self.successors)?;
        while let Some((&source, targets)) = successors.next(work)? {
            work.poll()?;
            if !queries::reachable(&self.tree, BlockId::new(source), work)? {
                continue;
            }
            for (index, &target) in targets.iter().enumerate() {
                work.poll()?;
                if target == entry
                    || queries::dominates(
                        &self.tree,
                        BlockId::new(target),
                        BlockId::new(source),
                        work,
                    )?
                {
                    continue;
                }
                let value = if work.read(&self.edge_entries, &target)?.is_some() {
                    None
                } else {
                    Some((source, index))
                };
                work.insert(&mut self.edge_entries, target, value)?;
            }
        }
        let mut entries = work.entries(&self.edge_entries)?;
        while let Some((&target, &edge)) = entries.next(work)? {
            work.poll()?;
            if let Some(edge) = edge {
                work.insert(&mut self.tree.dominating_edges, edge, target)?;
            }
        }
        Ok(())
    }
}
