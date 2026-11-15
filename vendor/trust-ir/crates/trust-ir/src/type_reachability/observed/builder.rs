// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn prepare<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(6, 6 * size_of::<Bounds>() + size_of::<usize>())?;
        let mut next = 0usize;
        self.summary.tables.types = range(&mut next, module.types.len(), work)?;
        self.summary.tables.func_types = range(&mut next, module.func_types.len(), work)?;
        let structs = range(&mut next, module.structs.len(), work)?;
        let enums = range(&mut next, module.enums.len(), work)?;
        let records = range(&mut next, module.records.len(), work)?;
        self.summary.tables.closure_types = range(&mut next, module.closure_types.len(), work)?;
        let mut at = 0usize;
        while let Some(row) = work.at(&module.structs, at)? {
            work.admit(1, size_of::<u32>())?;
            let id = row.id.index();
            let vertex = work.add(structs.start, at)?;
            work.push(&mut self.summary.tables.structs, (id, vertex))?;
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(row) = work.at(&module.enums, at)? {
            work.admit(1, size_of::<u32>())?;
            let id = row.id.index();
            let vertex = work.add(enums.start, at)?;
            work.push(&mut self.summary.tables.enums, (id, vertex))?;
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(row) = work.at(&module.records, at)? {
            work.admit(1, size_of::<u32>())?;
            let id = row.id.index();
            let vertex = work.add(records.start, at)?;
            work.push(&mut self.summary.tables.records, (id, vertex))?;
            work.next(&mut at)?;
        }
        at = 0;
        loop {
            work.admit(1, 0)?;
            if at == next {
                break;
            }
            work.push(&mut self.heads, NO_EDGE)?;
            for axis in AXES {
                work.admit(1, size_of::<NominalAxis>())?;
                work.push(&mut self.summary.reachable[axis as usize], false)?;
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn dependency<O: ExecutionObserver>(
        &mut self,
        owner: usize,
        target: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, size_of::<ReverseEdge>() + size_of::<usize>())?;
        let head = *work
            .at(&self.heads, target)?
            .ok_or(ObservedValueError::InvalidRange)?;
        if owner >= self.heads.len() {
            return Err(ObservedValueError::InvalidRange);
        }
        work.reserve(&mut self.edges)?;
        work.admit(3, size_of::<ReverseEdge>() + size_of::<usize>())?;
        let index = self.edges.len();
        self.edges.push(ReverseEdge {
            dependent: owner,
            next: head,
        });
        // The target was bounds-checked before growth; no source mutation or
        // fallible work intervenes between this update and the paid append.
        self.heads[target] = index;
        Ok(())
    }
    pub(super) fn mark<O: ExecutionObserver>(
        &mut self,
        axis: NominalAxis,
        vertex: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<bool>())?;
        let old = *work
            .at(&self.summary.reachable[axis as usize], vertex)?
            .ok_or(ObservedValueError::InvalidRange)?;
        if !old {
            work.reserve(&mut self.pending[axis as usize])?;
            work.admit(2, size_of::<bool>() + size_of::<usize>())?;
            self.summary.reachable[axis as usize][vertex] = true;
            self.pending[axis as usize].push(vertex);
        }
        Ok(())
    }
    pub(super) fn solve<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        for axis in AXES {
            work.admit(1, size_of::<NominalAxis>())?;
            while let Some(target) = work.pop(&mut self.pending[axis as usize])? {
                work.admit(1, size_of::<usize>())?;
                let mut edge = *work
                    .at(&self.heads, target)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                loop {
                    work.admit(1, 0)?;
                    if edge == NO_EDGE {
                        break;
                    }
                    work.admit(1, size_of::<ReverseEdge>())?;
                    let row = *work
                        .at(&self.edges, edge)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    self.mark(axis, row.dependent, work)?;
                    work.admit(1, size_of::<usize>())?;
                    edge = row.next;
                }
            }
        }
        Ok(())
    }
}
fn range<O: ExecutionObserver>(
    next: &mut usize,
    len: usize,
    work: &mut Work<'_, '_, O>,
) -> R<Bounds> {
    work.admit(1, size_of::<Bounds>())?;
    let start = *next;
    *next = work.add(start, len)?;
    Ok(Bounds { start, len })
}
