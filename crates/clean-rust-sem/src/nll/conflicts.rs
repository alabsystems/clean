// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NLL conflict checking: detects borrow violations at each program point.

use super::conflicts_term::{check_operand_access_conflicts, check_term_conflicts, AccessCtx};
use super::liveness::place_local;
use super::reborrow_chain::ReborrowMap;
use super::two_phase::TwoPhaseInfo;
use super::{BorrowIndex, NllBorrow, NllError, ProgramPoint, Region};
use crate::ownership::Place;
use crate::vir::{BasicBlockId, Body, BorrowKind, LocalId, Operand, Rvalue, Stmt};
use std::collections::HashSet;

/// Check all program points for borrow conflicts.
pub(crate) fn check_conflicts(
    body: &Body,
    borrows: &[NllBorrow],
    regions: &[Region],
    two_phase: &TwoPhaseInfo,
    reborrow_map: &ReborrowMap,
    moved_locals: &HashSet<LocalId>,
) -> Vec<NllError> {
    let mut errors = Vec::new();

    for (block_idx, block) in body.blocks.iter().enumerate() {
        let block_id = block_idx as BasicBlockId;

        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            let point = ProgramPoint::new(block_id, stmt_idx);
            check_stmt_conflicts(
                stmt,
                point,
                borrows,
                regions,
                two_phase,
                reborrow_map,
                moved_locals,
                &mut errors,
            );
        }

        let tp = ProgramPoint::terminator(block_id, block.statements.len());
        check_term_conflicts(
            &block.terminator,
            tp,
            borrows,
            regions,
            two_phase,
            reborrow_map,
            moved_locals,
            &mut errors,
        );
    }

    errors
}

/// Test whether two places conflict, after resolving reborrow chains
/// through the precomputed `ReborrowMap`. A `Deref(Local(L))` where `L`
/// was ref-assigned `&P` resolves to `P`, so a reborrow's
/// `borrowed_place` no longer aliases through a fresh anonymous local
/// that the prefix-based `Place::conflicts_with` cannot follow.
pub(super) fn places_conflict(a: &Place, b: &Place, reborrow_map: &ReborrowMap) -> bool {
    let resolved_a = reborrow_map.resolve(a);
    let resolved_b = reborrow_map.resolve(b);
    resolved_a.conflicts_with(&resolved_b)
}

/// True if the borrow at `borrow_place` is a reborrow of the borrow
/// whose ref-local is `parent_ref_local`. Reborrows of an existing
/// borrow are not independent — they share the same access path and
/// must not be reported as conflicting with their parent.
pub(super) fn is_reborrow_of(
    borrow_place: &Place,
    parent_ref_local: LocalId,
    reborrow_map: &ReborrowMap,
) -> bool {
    reborrow_map.place_reborrows_local(borrow_place, parent_ref_local)
}

pub(super) fn active_borrows_at<'a>(
    point: ProgramPoint,
    borrows: &'a [NllBorrow],
    regions: &'a [Region],
) -> Vec<(BorrowIndex, &'a NllBorrow)> {
    borrows
        .iter()
        .enumerate()
        .filter(|(idx, _)| regions[*idx].contains(&point))
        .collect()
}

/// Two borrows conflict if their places overlap and at least one is mutable.
fn borrows_conflict(existing: BorrowKind, new: BorrowKind) -> bool {
    // Shared + Shared = OK; Shallow + Shared = OK; Shallow + Shallow = OK
    // Any Mut involved = conflict
    matches!(existing, BorrowKind::Mut { .. }) || matches!(new, BorrowKind::Mut { .. })
}

/// True if reading `read_place` conflicts with the active mutable borrow at
/// `borrow` (index `borrow_idx`).
///
/// SOUNDNESS (hole 2): a read (`Operand::Copy`) is only invalid while a *mutable*
/// borrow of an overlapping place is live (rustc E0503). Shared borrows permit
/// concurrent reads, so this returns `false` for them. The effective kind is
/// consulted so an un-activated two-phase borrow (which behaves as shared until
/// activation) does not spuriously reject reservation-phase reads.
pub(super) fn place_read_conflicts_mut(
    read_place: &Place,
    borrow_idx: BorrowIndex,
    borrow: &NllBorrow,
    point: ProgramPoint,
    two_phase: &TwoPhaseInfo,
    reborrow_map: &ReborrowMap,
    moved_locals: &HashSet<LocalId>,
) -> bool {
    // If the borrow's reference was moved away (passed by value into a call),
    // the loan is transferred to the callee and our region over-approximates
    // its liveness — do not report a read conflict against it here.
    if moved_locals.contains(&borrow.ref_local) {
        return false;
    }
    let effective = two_phase.effective_kind(borrow_idx, borrow, point);
    matches!(effective, BorrowKind::Mut { .. })
        && places_conflict(read_place, &borrow.borrowed_place, reborrow_map)
}

#[allow(clippy::too_many_arguments)]
fn check_stmt_conflicts(
    stmt: &Stmt,
    point: ProgramPoint,
    borrows: &[NllBorrow],
    regions: &[Region],
    two_phase: &TwoPhaseInfo,
    reborrow_map: &ReborrowMap,
    moved_locals: &HashSet<LocalId>,
    errors: &mut Vec<NllError>,
) {
    let active = active_borrows_at(point, borrows, regions);
    if active.is_empty() {
        return;
    }

    check_activation_conflicts(point, &active, two_phase, reborrow_map, errors);

    match stmt {
        Stmt::Assign { place, rvalue } => {
            // Check ref-vs-ref conflicts: new borrow conflicting with active borrows
            if let Rvalue::Ref {
                borrow_kind: new_kind,
                place: new_place,
            } = rvalue
            {
                let effective_new_kind = borrows
                    .iter()
                    .enumerate()
                    .find(|(_, borrow)| borrow.origin == point)
                    .map_or(*new_kind, |(idx, borrow)| {
                        two_phase.effective_kind(idx, borrow, point)
                    });
                for (idx, borrow) in &active {
                    if borrow.origin == point {
                        continue;
                    }
                    // A new borrow that reborrows an active parent
                    // (e.g. `_4 = &mut (*_5)` where `_5` is a live mut
                    // borrow) shares the parent's access path — it is
                    // not an independent conflicting borrow.
                    if is_reborrow_of(new_place, borrow.ref_local, reborrow_map) {
                        continue;
                    }
                    let existing_kind = two_phase.effective_kind(*idx, borrow, point);
                    if places_conflict(new_place, &borrow.borrowed_place, reborrow_map)
                        && borrows_conflict(existing_kind, effective_new_kind)
                    {
                        errors.push(NllError::ConflictingBorrow {
                            place: new_place.clone(),
                            borrowed: borrow.borrowed_place.clone(),
                            origin: borrow.origin,
                        });
                    }
                }
            }

            if place_local(place).is_some() {
                for (_, borrow) in &active {
                    if borrow.origin == point {
                        continue;
                    }
                    // Writing through a reborrow's ref local is the
                    // legitimate use of the reborrow chain, not a
                    // conflicting write — skip.
                    if is_reborrow_of(place, borrow.ref_local, reborrow_map) {
                        continue;
                    }
                    if places_conflict(place, &borrow.borrowed_place, reborrow_map) {
                        errors.push(NllError::AssignWhileBorrowed {
                            place: place.clone(),
                            borrowed: borrow.borrowed_place.clone(),
                            origin: borrow.origin,
                        });
                    }
                }
            }
            check_rvalue_accesses(
                rvalue,
                point,
                &active,
                two_phase,
                reborrow_map,
                moved_locals,
                errors,
            );
        }
        Stmt::SetDiscriminant { place, .. } => {
            for (_, borrow) in &active {
                if places_conflict(place, &borrow.borrowed_place, reborrow_map) {
                    errors.push(NllError::AssignWhileBorrowed {
                        place: place.clone(),
                        borrowed: borrow.borrowed_place.clone(),
                        origin: borrow.origin,
                    });
                }
            }
        }
        Stmt::StorageDead(local) => {
            let lp = Place::Local(*local);
            for (_, borrow) in &active {
                if places_conflict(&lp, &borrow.borrowed_place, reborrow_map) {
                    errors.push(NllError::UseWhileBorrowed {
                        place: lp.clone(),
                        borrowed: borrow.borrowed_place.clone(),
                        origin: borrow.origin,
                    });
                }
            }
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn check_rvalue_accesses(
    rvalue: &Rvalue,
    point: ProgramPoint,
    active: &[(BorrowIndex, &NllBorrow)],
    two_phase: &TwoPhaseInfo,
    reborrow_map: &ReborrowMap,
    moved_locals: &HashSet<LocalId>,
    errors: &mut Vec<NllError>,
) {
    let operands: Vec<&Operand> = match rvalue {
        Rvalue::Use(op) | Rvalue::Repeat { operand: op, .. } => vec![op],
        Rvalue::Cast { operand: op, .. }
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::ShallowInitBox { operand: op, .. } => vec![op],
        Rvalue::BinaryOp { lhs, rhs, .. } | Rvalue::CheckedBinaryOp { lhs, rhs, .. } => {
            vec![lhs, rhs]
        }
        Rvalue::Aggregate { operands, .. } => operands.iter().collect(),
        _ => vec![],
    };

    let ctx = AccessCtx {
        point,
        active,
        two_phase,
        reborrow_map,
        moved_locals,
    };
    for op in operands {
        check_operand_access_conflicts(op, &ctx, errors);
    }
}

pub(super) fn check_activation_conflicts(
    point: ProgramPoint,
    active: &[(BorrowIndex, &NllBorrow)],
    two_phase: &TwoPhaseInfo,
    reborrow_map: &ReborrowMap,
    errors: &mut Vec<NllError>,
) {
    for (idx, borrow) in active {
        if !two_phase.is_activation_point(*idx, point) {
            continue;
        }

        let activating_kind = two_phase.effective_kind(*idx, borrow, point);
        for (other_idx, other) in active {
            if idx == other_idx {
                continue;
            }

            // If either borrow reborrows from the other, they are part
            // of the same logical access path — not independent
            // conflicting borrows.
            if is_reborrow_of(&borrow.borrowed_place, other.ref_local, reborrow_map)
                || is_reborrow_of(&other.borrowed_place, borrow.ref_local, reborrow_map)
            {
                continue;
            }

            let other_kind = two_phase.effective_kind(*other_idx, other, point);
            if places_conflict(&borrow.borrowed_place, &other.borrowed_place, reborrow_map)
                && borrows_conflict(activating_kind, other_kind)
            {
                errors.push(NllError::ConflictingBorrow {
                    place: borrow.borrowed_place.clone(),
                    borrowed: other.borrowed_place.clone(),
                    origin: other.origin,
                });
            }
        }
    }
}
