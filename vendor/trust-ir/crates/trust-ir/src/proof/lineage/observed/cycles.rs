// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl Checking<'_> {
    pub(super) fn cycles<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        for id in self.nodes.keys() {
            push(&mut self.starts, *id, session, site)?;
        }
        for position in 0..self.starts.len() {
            admit(session, site, 1, 0)?;
            push(
                &mut self.stack,
                Frame::Enter(self.starts[position]),
                session,
                site,
            )?;
            while !self.stack.is_empty() {
                admit(session, site, 1, 0)?;
                let Some(frame) = self.stack.pop() else {
                    break;
                };
                match frame {
                    Frame::Enter(id) => self.enter(id, session, site)?,
                    Frame::Next(id, index) => self.next(id, index, session, site)?,
                }
            }
        }
        Ok(())
    }
    fn enter<O: ExecutionObserver>(
        &mut self,
        id: ProofLineageId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        lookup(self.marks.len(), session, site)?;
        match self.marks.get(&id).copied() {
            Some(Mark::Done) => return Ok(()),
            Some(Mark::Visiting) => {
                return self.error(ProofLineageError::Cycle { node: id }, session, site);
            }
            None => {}
        }
        map_insert(&mut self.marks, id, Mark::Visiting, session, site)?;
        push(&mut self.stack, Frame::Next(id, 0), session, site)
    }
    fn next<O: ExecutionObserver>(
        &mut self,
        id: ProofLineageId,
        index: usize,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        lookup(self.nodes.len(), session, site)?;
        let Some(node) = self.nodes.get(&id).copied() else {
            return Err(ObservedValueError::InvalidRange);
        };
        if let Some(dependency) = node.depends_on.get(index).copied() {
            let next = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            push(&mut self.stack, Frame::Next(id, next), session, site)?;
            lookup(self.nodes.len(), session, site)?;
            if self.nodes.contains_key(&dependency) {
                push(&mut self.stack, Frame::Enter(dependency), session, site)?;
            }
        } else {
            map_insert(&mut self.marks, id, Mark::Done, session, site)?;
        }
        Ok(())
    }
}
