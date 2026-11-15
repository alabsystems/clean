// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        m: &'m ProofLineageManifest,
        roots: &[ProofLineageId],
        source: Option<ProofDigest>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.collect(m, roots, Target::Reachable, w)?;
        let mut at = 0;
        while let Some(root) = w.at(roots, at)? {
            // Borrow the actual one root instead of an unobserved temporary
            // owning collection; collect still computes its ENTIRE closure.
            w.admit(1, size_of::<&[ProofLineageId]>())?;
            self.collect(m, core::slice::from_ref(root), Target::Current, w)?;
            w.admit(1, size_of::<Option<ProofDigest>>())?;
            let admitted = match source {
                None => true,
                Some(source) => w.contains(&self.current.sources, &source)?,
            };
            w.admit(1, size_of::<bool>())?;
            if admitted {
                self.out.bound.merge(&self.current, w)?;
            }
            self.current.retire(w);
            w.admit(0, 0)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn collect<O: ExecutionObserver>(
        &mut self,
        m: &'m ProofLineageManifest,
        roots: &[ProofLineageId],
        target: Target,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(2, 2 * size_of::<bool>())?;
        if !self.stack.is_empty() || !self.seen.is_empty() {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut at = 0;
        while let Some(root) = w.at(roots, at)? {
            w.push(&mut self.stack, root)?;
            w.next(&mut at)?;
        }
        loop {
            w.admit(1, size_of::<Option<ProofLineageId>>())?;
            let Some(id) = self.stack.pop() else {
                break;
            };
            if !w.insert(&mut self.seen, &id)? {
                continue;
            }
            let Some(node) = Self::last(m, &id, w)? else {
                continue;
            };
            match target {
                Target::Reachable => self.out.reachable.node(node, w)?,
                Target::Current => self.current.node(node, w)?,
            }
            let mut at = 0;
            while let Some(id) = w.at(&node.depends_on, at)? {
                w.push(&mut self.stack, id)?;
                w.next(&mut at)?;
            }
        }
        w.rows(&mut self.seen);
        w.rows(&mut self.stack);
        w.admit(0, 0)
    }
    fn last<O: ExecutionObserver>(
        m: &'m ProofLineageManifest,
        id: &ProofLineageId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'m ProofLineageNode>> {
        w.admit(1, size_of::<usize>())?;
        let mut at = m.nodes.len();
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == 0 {
                return Ok(None);
            }
            w.admit(1, size_of::<usize>())?;
            at -= 1;
            let node = w
                .at(&m.nodes, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if w.equal(&node.id, id)? {
                return Ok(Some(node));
            }
        }
    }
}
