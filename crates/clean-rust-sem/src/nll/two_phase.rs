// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::liveness::{stmt_uses, term_uses};
use super::{BorrowIndex, NllBorrow, ProgramPoint, Region};
use crate::vir::{BasicBlockId, Body, BorrowKind, LocalId, MutBorrowKind, Stmt};
use std::collections::{BTreeSet, HashMap};

/// Two-phase borrow reservation/activation facts over VIR program points.
#[derive(Debug, Clone, Default)]
pub(crate) struct TwoPhaseInfo {
    activations: HashMap<BorrowIndex, BTreeSet<ProgramPoint>>,
    dominators: HashMap<ProgramPoint, BTreeSet<ProgramPoint>>,
}

impl TwoPhaseInfo {
    pub(crate) fn analyze(body: &Body, borrows: &[NllBorrow], regions: &[Region]) -> Self {
        let points = all_points(body);
        let activations = collect_activation_points(body, &points, borrows, regions);
        if activations.is_empty() {
            return Self::default();
        }

        Self {
            activations,
            dominators: compute_dominators(body, &points),
        }
    }

    pub(crate) fn effective_kind(
        &self,
        borrow_idx: BorrowIndex,
        borrow: &NllBorrow,
        point: ProgramPoint,
    ) -> BorrowKind {
        if matches!(
            borrow.kind,
            BorrowKind::Mut {
                kind: MutBorrowKind::TwoPhaseBorrow,
            }
        ) && !self.is_activated_at(borrow_idx, point)
        {
            BorrowKind::Shared
        } else {
            borrow.kind
        }
    }

    pub(crate) fn is_activation_point(&self, borrow_idx: BorrowIndex, point: ProgramPoint) -> bool {
        self.activations
            .get(&borrow_idx)
            .is_some_and(|points| points.contains(&point))
    }

    fn is_activated_at(&self, borrow_idx: BorrowIndex, point: ProgramPoint) -> bool {
        let Some(point_dominators) = self.dominators.get(&point) else {
            return false;
        };

        self.activations.get(&borrow_idx).is_some_and(|points| {
            points
                .iter()
                .any(|activation| point_dominators.contains(activation))
        })
    }
}

fn collect_activation_points(
    body: &Body,
    points: &[ProgramPoint],
    borrows: &[NllBorrow],
    regions: &[Region],
) -> HashMap<BorrowIndex, BTreeSet<ProgramPoint>> {
    let mut activations = HashMap::new();

    for (idx, borrow) in borrows.iter().enumerate() {
        if !matches!(
            borrow.kind,
            BorrowKind::Mut {
                kind: MutBorrowKind::TwoPhaseBorrow,
            }
        ) {
            continue;
        }

        let activation_points = points
            .iter()
            .copied()
            .filter(|point| {
                regions[idx].contains(point) && point_uses_local(body, *point, borrow.ref_local)
            })
            .collect::<BTreeSet<_>>();

        if !activation_points.is_empty() {
            activations.insert(idx, activation_points);
        }
    }

    activations
}

fn all_points(body: &Body) -> Vec<ProgramPoint> {
    let mut points = Vec::new();

    for (block_idx, block) in body.blocks.iter().enumerate() {
        let block_id = block_idx as BasicBlockId;
        for stmt_idx in 0..block.statements.len() {
            points.push(ProgramPoint::new(block_id, stmt_idx));
        }
        points.push(ProgramPoint::terminator(block_id, block.statements.len()));
    }

    points
}

fn block_entry_point(body: &Body, block: BasicBlockId) -> ProgramPoint {
    let stmt_count = body.blocks[block as usize].statements.len();
    if stmt_count == 0 {
        ProgramPoint::terminator(block, 0)
    } else {
        ProgramPoint::new(block, 0)
    }
}

fn point_successors(body: &Body, point: ProgramPoint) -> Vec<ProgramPoint> {
    let block = &body.blocks[point.block as usize];
    if point.statement_index < block.statements.len() {
        let next = point.statement_index + 1;
        if next < block.statements.len() {
            vec![ProgramPoint::new(point.block, next)]
        } else {
            vec![ProgramPoint::terminator(
                point.block,
                block.statements.len(),
            )]
        }
    } else {
        block
            .terminator
            .successors()
            .into_iter()
            .map(|succ| block_entry_point(body, succ))
            .collect()
    }
}

fn compute_predecessors(
    body: &Body,
    points: &[ProgramPoint],
) -> HashMap<ProgramPoint, BTreeSet<ProgramPoint>> {
    let mut predecessors = HashMap::<ProgramPoint, BTreeSet<ProgramPoint>>::new();

    for point in points.iter().copied() {
        predecessors.entry(point).or_default();
        for succ in point_successors(body, point) {
            predecessors.entry(succ).or_default().insert(point);
        }
    }

    predecessors
}

fn compute_dominators(
    body: &Body,
    points: &[ProgramPoint],
) -> HashMap<ProgramPoint, BTreeSet<ProgramPoint>> {
    if body.blocks.is_empty() {
        return HashMap::new();
    }

    let entry = block_entry_point(body, 0);
    let predecessors = compute_predecessors(body, points);
    let all_points = points.iter().copied().collect::<BTreeSet<_>>();
    let mut dominators = HashMap::<ProgramPoint, BTreeSet<ProgramPoint>>::new();

    for point in points.iter().copied() {
        let initial = if point == entry {
            BTreeSet::from([entry])
        } else {
            all_points.clone()
        };
        dominators.insert(point, initial);
    }

    let mut changed = true;
    while changed {
        changed = false;

        for point in points.iter().copied().filter(|point| *point != entry) {
            let preds = predecessors.get(&point).cloned().unwrap_or_default();
            let mut updated = if preds.is_empty() {
                BTreeSet::new()
            } else {
                let mut pred_iter = preds.into_iter();
                let first = dominators
                    .get(&pred_iter.next().expect("non-empty predecessors"))
                    .cloned()
                    .unwrap_or_default();
                pred_iter.fold(first, |acc, pred| {
                    let other = dominators.get(&pred).cloned().unwrap_or_default();
                    acc.intersection(&other).copied().collect()
                })
            };
            updated.insert(point);

            if dominators.get(&point) != Some(&updated) {
                dominators.insert(point, updated);
                changed = true;
            }
        }
    }

    dominators
}

fn point_uses_local(body: &Body, point: ProgramPoint, local: LocalId) -> bool {
    let block = &body.blocks[point.block as usize];
    let uses = if point.statement_index < block.statements.len() {
        match &block.statements[point.statement_index] {
            // Retag is stacked-borrows bookkeeping after the borrow is created,
            // not a semantic use that activates a pending two-phase borrow.
            Stmt::Retag { .. } => return false,
            stmt => stmt_uses(stmt),
        }
    } else {
        term_uses(&block.terminator)
    };
    uses.contains(&local)
}
