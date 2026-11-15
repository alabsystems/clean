// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

mod expand;

#[derive(Default)]
struct Solve {
    local: BTreeMap<Node, usize>,
    nodes: Vec<Node>,
    open: Vec<usize>,
    watchers: Vec<Vec<usize>>,
    owner: Vec<usize>,
    satisfied: Vec<bool>,
    unexpanded: Vec<usize>,
    ready: Vec<usize>,
    verdict: Vec<bool>,
}

pub(super) fn run<O: ExecutionObserver>(
    module: &Module,
    roots: &[Node],
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, size_of::<Solve>())?;
    let mut solve = Solve::default();
    let mut literals = Vec::new();
    let result = (|| {
        for &root in roots {
            solve.intern(root, work)?;
        }
        while !solve.unexpanded.is_empty() {
            work.poll()?;
            let index = solve
                .unexpanded
                .pop()
                .ok_or(ObservedValueError::UnsupportedValue)?;
            solve.expand(module, index, &mut literals, work)?;
            if solve.open[index] == 0 {
                work.push(&mut solve.ready, index)?;
            }
        }
        solve.propagate(work)?;
        for index in 0..solve.nodes.len() {
            work.poll()?;
            work.tree::<Node, bool>(work.inhabitedness.len())?;
            work.inhabitedness
                .insert(solve.nodes[index], solve.verdict[index]);
        }
        Ok(())
    })();
    solve.retire(work);
    work.retire_copy_vec(literals);
    work.poll()?;
    result
}

impl Solve {
    fn intern<O: ExecutionObserver>(&mut self, node: Node, work: &mut Work<'_, '_, O>) -> R<usize> {
        work.lookup(self.local.len())?;
        if let Some(&index) = self.local.get(&node) {
            return Ok(index);
        }
        let index = self.nodes.len();
        work.push(&mut self.nodes, node)?;
        work.push(&mut self.open, 0)?;
        work.empty_row(&mut self.watchers)?;
        work.push(&mut self.unexpanded, index)?;
        work.tree::<Node, usize>(self.local.len())?;
        self.local.insert(node, index);
        Ok(index)
    }

    fn clause<'t, O: ExecutionObserver>(
        &mut self,
        module: &Module,
        owner: usize,
        tys: impl Iterator<Item = &'t Ty>,
        literals: &mut Vec<Node>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            literals
                .len()
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            0,
        )?;
        literals.clear();
        if super::literals(module, tys, literals, work)? {
            return Ok(());
        }
        for node in literals.iter() {
            work.lookup(work.inhabitedness.len())?;
            if work.inhabitedness.get(node) == Some(&true) {
                return Ok(());
            }
        }
        let clause = self.owner.len();
        work.push(&mut self.owner, owner)?;
        work.push(&mut self.satisfied, false)?;
        self.open[owner] = self.open[owner]
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        for &node in literals.iter() {
            work.lookup(work.inhabitedness.len())?;
            if work.inhabitedness.contains_key(&node) {
                continue;
            }
            let watched = self.intern(node, work)?;
            work.push(&mut self.watchers[watched], clause)?;
        }
        Ok(())
    }

    fn propagate<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        for _ in &self.nodes {
            work.push(&mut self.verdict, false)?;
        }
        for &index in &self.ready {
            work.poll()?;
            self.verdict[index] = true;
        }
        while !self.ready.is_empty() {
            work.poll()?;
            let index = self
                .ready
                .pop()
                .ok_or(ObservedValueError::UnsupportedValue)?;
            for at in 0..self.watchers[index].len() {
                work.poll()?;
                let clause = self.watchers[index][at];
                if self.satisfied[clause] {
                    continue;
                }
                self.satisfied[clause] = true;
                let owner = self.owner[clause];
                self.open[owner] -= 1;
                if self.open[owner] == 0 {
                    self.verdict[owner] = true;
                    work.push(&mut self.ready, owner)?;
                }
            }
        }
        Ok(())
    }

    fn retire<O: ExecutionObserver>(self, work: &mut Work<'_, '_, O>) {
        let Self {
            local,
            nodes,
            open,
            watchers,
            owner,
            satisfied,
            unexpanded,
            ready,
            verdict,
        } = self;
        work.retire_copy_map(local);
        work.retire_copy_vec(nodes);
        work.retire_copy_vec(open);
        work.retire_rows(watchers);
        work.retire_copy_vec(owner);
        work.retire_copy_vec(satisfied);
        work.retire_copy_vec(unexpanded);
        work.retire_copy_vec(ready);
        work.retire_copy_vec(verdict);
    }
}
