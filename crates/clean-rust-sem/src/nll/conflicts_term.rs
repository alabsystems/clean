// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NLL terminator conflict checking and operand move helpers.

use super::conflicts::{
    active_borrows_at, check_activation_conflicts, is_reborrow_of, place_read_conflicts_mut,
    places_conflict,
};
use super::reborrow_chain::ReborrowMap;
use super::two_phase::TwoPhaseInfo;
use super::{BorrowIndex, NllBorrow, NllError, ProgramPoint, Region};
use crate::vir::{AssertMessage, LocalId, Operand, Term};
use std::collections::HashSet;

/// Check terminator at a program point for borrow conflicts.
#[allow(clippy::too_many_arguments)]
pub(super) fn check_term_conflicts(
    term: &Term,
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

    let ctx = AccessCtx {
        point,
        active: &active,
        two_phase,
        reborrow_map,
        moved_locals,
    };

    match term {
        Term::Goto { args, .. } => {
            check_operand_accesses(args.iter(), &ctx, errors);
        }
        Term::SwitchInt {
            discriminant,
            targets,
        } => {
            check_operand_access_conflicts(discriminant, &ctx, errors);
            for (_, target) in targets.iter_targets() {
                check_operand_accesses(target.args.iter(), &ctx, errors);
            }
        }
        Term::Drop {
            place, target_args, ..
        } => {
            for (_, borrow) in &active {
                if places_conflict(place, &borrow.borrowed_place, reborrow_map) {
                    errors.push(NllError::MoveWhileBorrowed {
                        place: place.clone(),
                        borrowed: borrow.borrowed_place.clone(),
                        origin: borrow.origin,
                    });
                }
            }
            check_operand_accesses(target_args.iter(), &ctx, errors);
        }
        Term::Call {
            func,
            args,
            destination,
            target_args,
            ..
        } => {
            // The call destination is written on return — check for
            // write conflicts with active borrows.
            for (_, borrow) in &active {
                if places_conflict(destination, &borrow.borrowed_place, reborrow_map) {
                    errors.push(NllError::AssignWhileBorrowed {
                        place: destination.clone(),
                        borrowed: borrow.borrowed_place.clone(),
                        origin: borrow.origin,
                    });
                }
            }
            check_operand_access_conflicts(func, &ctx, errors);
            check_operand_accesses(args.iter(), &ctx, errors);
            check_operand_accesses(target_args.iter(), &ctx, errors);
        }
        Term::Assert {
            cond,
            msg,
            target_args,
            ..
        } => {
            check_operand_access_conflicts(cond, &ctx, errors);
            check_assert_message_accesses(msg, &ctx, errors);
            check_operand_accesses(target_args.iter(), &ctx, errors);
        }
        Term::Yield {
            value, resume_args, ..
        } => {
            check_operand_access_conflicts(value, &ctx, errors);
            check_operand_accesses(resume_args.iter(), &ctx, errors);
        }
        _ => {}
    }
}

/// Shared context for operand access-conflict checking at a program point.
pub(super) struct AccessCtx<'a> {
    pub point: ProgramPoint,
    pub active: &'a [(BorrowIndex, &'a NllBorrow)],
    pub two_phase: &'a TwoPhaseInfo,
    pub reborrow_map: &'a ReborrowMap,
    pub moved_locals: &'a HashSet<LocalId>,
}

fn check_operand_accesses<'a>(
    operands: impl IntoIterator<Item = &'a Operand>,
    ctx: &AccessCtx<'_>,
    errors: &mut Vec<NllError>,
) {
    for operand in operands {
        check_operand_access_conflicts(operand, ctx, errors);
    }
}

/// Check an operand access (move or copy read) against active borrows.
///
/// SOUNDNESS (hole 2): moving a place while it is borrowed at all is
/// `MoveWhileBorrowed` (unchanged). A *read* (`Operand::Copy`) of a place while
/// an active `&mut` borrow of that place — or an overlapping place — is live is
/// UB (rustc E0503) and now emits `UseWhileBorrowed`. Reads under only shared
/// (`&`) borrows are legal and never flagged; the effective-kind check (which
/// treats an un-activated two-phase borrow as shared) preserves that, so
/// two-phase reservation reads of the borrowed place are not rejected.
pub(super) fn check_operand_access_conflicts(
    operand: &Operand,
    ctx: &AccessCtx<'_>,
    errors: &mut Vec<NllError>,
) {
    match operand {
        Operand::Move(place) => {
            for (_, borrow) in ctx.active {
                if places_conflict(place, &borrow.borrowed_place, ctx.reborrow_map) {
                    errors.push(NllError::MoveWhileBorrowed {
                        place: place.clone(),
                        borrowed: borrow.borrowed_place.clone(),
                        origin: borrow.origin,
                    });
                }
            }
        }
        Operand::Copy(place) => {
            for (idx, borrow) in ctx.active {
                // Reading *through* a reborrow's own reference local (or the
                // reference local itself) is the legitimate use of the borrow,
                // not a conflicting access — skip those.
                if is_reborrow_of(place, borrow.ref_local, ctx.reborrow_map) {
                    continue;
                }
                if place_read_conflicts_mut(
                    place,
                    *idx,
                    borrow,
                    ctx.point,
                    ctx.two_phase,
                    ctx.reborrow_map,
                    ctx.moved_locals,
                ) {
                    errors.push(NllError::UseWhileBorrowed {
                        place: place.clone(),
                        borrowed: borrow.borrowed_place.clone(),
                        origin: borrow.origin,
                    });
                }
            }
        }
        Operand::Constant(_) => {}
    }
}

fn check_assert_message_accesses(
    msg: &AssertMessage,
    ctx: &AccessCtx<'_>,
    errors: &mut Vec<NllError>,
) {
    match msg {
        AssertMessage::BoundsCheck { len, index } => {
            check_operand_access_conflicts(len, ctx, errors);
            check_operand_access_conflicts(index, ctx, errors);
        }
        AssertMessage::Overflow(_, lhs, rhs) => {
            check_operand_access_conflicts(lhs, ctx, errors);
            check_operand_access_conflicts(rhs, ctx, errors);
        }
        AssertMessage::OverflowNeg(op)
        | AssertMessage::DivisionByZero(op)
        | AssertMessage::RemainderByZero(op) => {
            check_operand_access_conflicts(op, ctx, errors);
        }
        AssertMessage::MisalignedPointerDereference { required, found } => {
            check_operand_access_conflicts(required, ctx, errors);
            check_operand_access_conflicts(found, ctx, errors);
        }
        AssertMessage::Custom(_) => {}
    }
}
