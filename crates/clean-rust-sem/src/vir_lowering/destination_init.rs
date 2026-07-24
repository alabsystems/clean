// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definite-initialization tracking for call destinations during VIR lowering.

use super::context::FunctionLoweringContext;
use crate::ownership::Place;
use crate::vir::{BasicBlockId, LocalId, Stmt as VirStmt, Term};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn local_has_prior_def(&self, local: LocalId) -> bool {
        let block_count = self.body.blocks.len();
        let current_block = self.current_block as usize;
        if current_block >= block_count {
            return false;
        }

        let (reachable, predecessors) = self.reachable_blocks_and_predecessors();
        if !reachable[current_block] {
            return false;
        }

        let after_statements = self.local_definition_fixpoint(local, &reachable, &predecessors);
        after_statements[current_block]
    }

    fn local_is_initialized_at_entry(&self, local: LocalId) -> bool {
        local != 0 && local <= self.body.arg_count
    }

    fn reachable_blocks_and_predecessors(&self) -> (Vec<bool>, Vec<Vec<BasicBlockId>>) {
        let mut predecessors = vec![Vec::new(); self.body.blocks.len()];
        let mut reachable = vec![false; self.body.blocks.len()];
        let mut worklist = vec![0u32];
        while let Some(block) = worklist.pop() {
            let block_idx = block as usize;
            if block_idx >= self.body.blocks.len() || reachable[block_idx] {
                continue;
            }
            reachable[block_idx] = true;
            for succ in self.body.blocks[block_idx].terminator.successors() {
                predecessors[succ as usize].push(block);
                worklist.push(succ);
            }
        }
        (reachable, predecessors)
    }

    fn local_definition_fixpoint(
        &self,
        local: LocalId,
        reachable: &[bool],
        predecessors: &[Vec<BasicBlockId>],
    ) -> Vec<bool> {
        let mut in_defined = vec![false; self.body.blocks.len()];
        let mut after_statements = vec![false; self.body.blocks.len()];
        let entry_defined = self.local_is_initialized_at_entry(local);
        in_defined[0] = entry_defined;
        after_statements[0] = self.local_definition_after_statements(0, local, entry_defined);

        let mut changed = true;
        while changed {
            changed = false;
            for block_idx in 0..self.body.blocks.len() {
                if !reachable[block_idx] {
                    continue;
                }

                let new_in = if block_idx == 0 {
                    entry_defined
                } else {
                    let preds = &predecessors[block_idx];
                    !preds.is_empty()
                        && preds.iter().all(|pred| {
                            self.local_definition_on_edge(
                                *pred,
                                block_idx as u32,
                                local,
                                &after_statements,
                            )
                        })
                };
                if in_defined[block_idx] != new_in {
                    in_defined[block_idx] = new_in;
                    changed = true;
                }

                let new_after =
                    self.local_definition_after_statements(block_idx as u32, local, new_in);
                if after_statements[block_idx] != new_after {
                    after_statements[block_idx] = new_after;
                    changed = true;
                }
            }
        }

        after_statements
    }

    fn local_definition_after_statements(
        &self,
        block: u32,
        local: LocalId,
        mut defined: bool,
    ) -> bool {
        for stmt in &self.body.blocks[block as usize].statements {
            defined = match stmt {
                VirStmt::Assign { place, .. } | VirStmt::SetDiscriminant { place, .. } => {
                    if matches!(place, Place::Local(place_local) if *place_local == local) {
                        true
                    } else {
                        defined
                    }
                }
                VirStmt::StorageLive(storage_local) | VirStmt::StorageDead(storage_local) => {
                    if *storage_local == local {
                        false
                    } else {
                        defined
                    }
                }
                VirStmt::Retag { .. } | VirStmt::Nop => defined,
            };
        }
        defined
    }

    fn local_definition_on_edge(
        &self,
        pred: u32,
        succ: u32,
        local: LocalId,
        after_statements: &[bool],
    ) -> bool {
        let mut defined = after_statements[pred as usize];
        if let Term::Call {
            destination: Place::Local(dest_local),
            target: Some(target),
            ..
        } = &self.body.blocks[pred as usize].terminator
        {
            if *target == succ && *dest_local == local {
                defined = true;
            }
        }
        defined
    }
}
