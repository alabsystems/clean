// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-Lexical Lifetime (NLL) Borrow Checking
//!
//! Flow-sensitive borrow checking over the VIR control-flow graph.
//! Borrows are active only while the reference local is *live* (used on
//! some path before being overwritten), rather than for the entire
//! lexical scope.
//!
//! ## References
//!
//! - RFC 2094: Non-lexical lifetimes
//! - Polonius: <https://github.com/rust-lang/polonius>

mod conflicts;
mod conflicts_term;
pub(crate) mod liveness;
mod reborrow_chain;
#[cfg(test)]
mod test_helpers;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_borrow_conflicts;
#[cfg(test)]
mod tests_terminator_conflicts;
mod two_phase;
#[cfg(test)]
mod two_phase_tests;

use crate::ownership::Place;
use crate::vir::{BasicBlockId, Body, BorrowKind, LocalId, Operand, Rvalue, Stmt, Term};
use reborrow_chain::ReborrowMap;
use std::collections::{BTreeSet, HashMap, HashSet};
use thiserror::Error;
use two_phase::TwoPhaseInfo;

/// A program point: (block, statement_index).
///
/// `statement_index == block.statements.len()` refers to the terminator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProgramPoint {
    pub block: BasicBlockId,
    pub statement_index: usize,
}

impl ProgramPoint {
    pub fn new(block: BasicBlockId, statement_index: usize) -> Self {
        Self {
            block,
            statement_index,
        }
    }

    pub fn terminator(block: BasicBlockId, stmt_count: usize) -> Self {
        Self {
            block,
            statement_index: stmt_count,
        }
    }
}

/// Index into the borrow set.
pub type BorrowIndex = usize;

/// A borrow created by an `Rvalue::Ref` assignment.
#[derive(Debug, Clone)]
pub struct NllBorrow {
    pub borrowed_place: Place,
    pub ref_local: LocalId,
    pub kind: BorrowKind,
    pub origin: ProgramPoint,
}

/// Region: set of program points where a borrow is active.
pub type Region = BTreeSet<ProgramPoint>;

/// Result of liveness analysis for the entire body.
#[derive(Debug, Clone)]
pub struct LivenessResult {
    pub live_points: HashMap<LocalId, BTreeSet<ProgramPoint>>,
}

/// NLL borrow-check errors.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum NllError {
    #[error("cannot use `{place:?}`: borrowed (`{borrowed:?}` at {origin:?})")]
    UseWhileBorrowed {
        place: Place,
        borrowed: Place,
        origin: ProgramPoint,
    },

    #[error("conflicting borrow of `{place:?}` (`{borrowed:?}` at {origin:?})")]
    ConflictingBorrow {
        place: Place,
        borrowed: Place,
        origin: ProgramPoint,
    },

    #[error("cannot assign `{place:?}`: borrowed (`{borrowed:?}` at {origin:?})")]
    AssignWhileBorrowed {
        place: Place,
        borrowed: Place,
        origin: ProgramPoint,
    },

    #[error("cannot move `{place:?}`: borrowed (`{borrowed:?}` at {origin:?})")]
    MoveWhileBorrowed {
        place: Place,
        borrowed: Place,
        origin: ProgramPoint,
    },

    /// A borrow of a function-local place escapes into the return value
    /// (rustc E0515): the referent's storage is freed when the function
    /// returns, so the returned reference would dangle.
    #[error(
        "cannot return reference to local `{borrowed:?}`: \
         referent does not live long enough (borrow at {origin:?})"
    )]
    BorrowEscapesReferent {
        borrowed: Place,
        origin: ProgramPoint,
    },
}

/// Result of running NLL analysis on a VIR body.
#[derive(Debug)]
pub struct NllResult {
    pub borrows: Vec<NllBorrow>,
    pub regions: Vec<Region>,
    pub liveness: LivenessResult,
    pub errors: Vec<NllError>,
}

/// The return place is always local 0.
const RETURN_PLACE: LocalId = 0;

/// Run NLL borrow checking on a VIR body.
pub fn check_body(body: &Body) -> NllResult {
    let borrows = extract_borrows(body);
    let liveness = liveness::compute_liveness(body);
    let regions = compute_regions(&borrows, &liveness);
    let two_phase = TwoPhaseInfo::analyze(body, &borrows, &regions);
    let reborrow_map = ReborrowMap::from_body(body);
    let moved_locals = collect_moved_locals(body);
    let mut errors = conflicts::check_conflicts(
        body,
        &borrows,
        &regions,
        &two_phase,
        &reborrow_map,
        &moved_locals,
    );
    check_return_escapes(body, &borrows, &reborrow_map, &mut errors);

    NllResult {
        borrows,
        regions,
        liveness,
        errors,
    }
}

/// Detect borrows of a function-local place that escape into the return value
/// (rustc E0515 — "cannot return reference to local variable").
///
/// SOUNDNESS (hole 5): a reference assigned directly into the RETURN_PLACE
/// (`fn dangle() -> &u32 { let x = 5; &x }` lowers to
/// `_0 = &_1; StorageDead(_1); Return`) points at a local whose storage is
/// freed on return, so the returned reference dangles. We flag a borrow when
/// its reference local is the return place and, after resolving reborrow
/// chains, its referent roots at a *function-local* place: a local strictly
/// above the argument range (`> arg_count`; local 0 is the return place,
/// locals `1..=arg_count` are arguments). Arguments and statics outlive the
/// call, so borrowing them into the return is legitimate and never flagged.
/// This is conservative toward soundness: it reports the escaping-referent
/// case and abstains where the referent provably outlives the call.
fn check_return_escapes(
    body: &Body,
    borrows: &[NllBorrow],
    reborrow_map: &ReborrowMap,
    errors: &mut Vec<NllError>,
) {
    for borrow in borrows {
        if borrow.ref_local != RETURN_PLACE {
            continue;
        }
        // Resolve reborrow chains so `_0 = &(*_r)` is judged by the place `_r`
        // ultimately borrows, not the intermediate deref.
        let referent = reborrow_map.resolve(&borrow.borrowed_place);
        if referent_is_local_storage(body, &referent) {
            errors.push(NllError::BorrowEscapesReferent {
                borrowed: borrow.borrowed_place.clone(),
                origin: borrow.origin,
            });
        }
    }
}

/// True if `place` names a function-local's own stack storage that does not
/// outlive the call: it roots at a local strictly above the argument range AND
/// is a *direct* place (no `Deref`/`Index` projection).
///
/// SOUNDNESS: the `Deref` guard is essential. Borrowing `&(*p)` where `p` is a
/// (copy of an) argument reference produces a `Deref(Local(p))` referent whose
/// storage lives wherever `p` points — behind the pointer, not in `p`'s own
/// frame — so it must NOT be reported as escaping (that would false-positive on
/// `fn f(x: &u32) -> &u32 { let y = x; y }`). Only a direct `&local` of a
/// fresh local (as in `fn dangle() -> &u32 { let x = 5; &x }`) dangles.
/// Statics and arguments are excluded because they outlive the call.
fn referent_is_local_storage(body: &Body, place: &Place) -> bool {
    if place_has_deref(place) {
        return false;
    }
    match liveness::place_local(place) {
        Some(local) => local != RETURN_PLACE && local > body.arg_count,
        None => false,
    }
}

/// True if `place`'s projection chain crosses a pointer dereference.
fn place_has_deref(place: &Place) -> bool {
    match place {
        Place::Local(_) | Place::Static(_) => false,
        Place::Deref(_) => true,
        Place::Field { base, .. } | Place::Index { base, .. } | Place::Downcast { base, .. } => {
            place_has_deref(base)
        }
    }
}

/// Extract borrows from `Rvalue::Ref` assignments in the VIR body.
///
/// SOUNDNESS (hole 3): a reference destination need not be a bare `Local`.
/// `holder.r = &mut x` lowers to `Assign { place: Field { base: Local(h), .. },
/// rvalue: Ref { .. } }`. Keying the borrow only on `Place::Local` LHSs silently
/// dropped every projected-destination loan, so no conflict was ever detected
/// against it. We instead key the borrow's region on the destination place's
/// *base local* (`place_local`) regardless of projection, so its liveness is
/// computed and later reads/writes/moves conflict against it. Using the base
/// local for a field destination conservatively keeps the loan live for the
/// whole enclosing object's lifetime, which is sound (an over-approximation of
/// the reference's liveness — never an under-approximation).
fn extract_borrows(body: &Body) -> Vec<NllBorrow> {
    let mut borrows = Vec::new();
    for (block_idx, block) in body.blocks.iter().enumerate() {
        let block_id = block_idx as BasicBlockId;
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            if let Stmt::Assign {
                place,
                rvalue:
                    Rvalue::Ref {
                        borrow_kind,
                        place: borrowed_place,
                    },
            } = stmt
            {
                if let Some(ref_local) = liveness::place_local(place) {
                    borrows.push(NllBorrow {
                        borrowed_place: borrowed_place.clone(),
                        ref_local,
                        kind: *borrow_kind,
                        origin: ProgramPoint::new(block_id, stmt_idx),
                    });
                }
            }
        }
    }
    borrows
}

/// Collect every local that is consumed by an `Operand::Move` anywhere in the
/// body — i.e. passed *by value* (typically into a call).
///
/// SOUNDNESS (hole 2 false-positive guard): when a `&mut` reference is moved
/// into a call (`restock(&mut inventory, ..)`, the two-phase pattern), the loan
/// is transferred to the callee; after the call returns, the caller may read
/// the referent again. Our liveness over-approximates such a reference's region
/// because the reference's `Drop` in cleanup blocks keeps it live. So we do not
/// let a *read* conflict be reported against a borrow whose reference local was
/// moved away. This only relaxes the new Copy-read check (hole 2); a genuine
/// `let r = &mut x; let y = x; *r = 5;` never moves `r`, so it is still caught.
fn collect_moved_locals(body: &Body) -> HashSet<LocalId> {
    let mut moved = HashSet::new();
    let mut note = |op: &Operand| {
        if let Operand::Move(place) = op {
            if let Some(local) = liveness::place_local(place) {
                moved.insert(local);
            }
        }
    };
    for block in &body.blocks {
        for stmt in &block.statements {
            if let Stmt::Assign { rvalue, .. } = stmt {
                for op in rvalue_operands(rvalue) {
                    note(op);
                }
            }
        }
        for op in term_operands(&block.terminator) {
            note(op);
        }
    }
    moved
}

/// Operands directly held by an rvalue.
fn rvalue_operands(rvalue: &Rvalue) -> Vec<&Operand> {
    match rvalue {
        Rvalue::Use(op) | Rvalue::Repeat { operand: op, .. } => vec![op],
        Rvalue::Cast { operand: op, .. }
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::ShallowInitBox { operand: op, .. } => vec![op],
        Rvalue::BinaryOp { lhs, rhs, .. } | Rvalue::CheckedBinaryOp { lhs, rhs, .. } => {
            vec![lhs, rhs]
        }
        Rvalue::Aggregate { operands, .. } => operands.iter().collect(),
        _ => vec![],
    }
}

/// Operands directly held by a terminator.
fn term_operands(term: &Term) -> Vec<&Operand> {
    match term {
        Term::Goto { args, .. } => args.iter().collect(),
        Term::SwitchInt {
            discriminant,
            targets,
        } => {
            let mut ops = vec![discriminant];
            for (_, target) in targets.iter_targets() {
                ops.extend(target.args.iter());
            }
            ops
        }
        Term::Call {
            func,
            args,
            target_args,
            ..
        } => {
            let mut ops = vec![func];
            ops.extend(args.iter());
            ops.extend(target_args.iter());
            ops
        }
        Term::Assert {
            cond, target_args, ..
        } => {
            let mut ops = vec![cond];
            ops.extend(target_args.iter());
            ops
        }
        Term::Drop { target_args, .. } => target_args.iter().collect(),
        Term::Yield {
            value, resume_args, ..
        } => {
            let mut ops = vec![value];
            ops.extend(resume_args.iter());
            ops
        }
        _ => vec![],
    }
}

/// Compute borrow regions from liveness. Includes the origin point.
fn compute_regions(borrows: &[NllBorrow], liveness: &LivenessResult) -> Vec<Region> {
    borrows
        .iter()
        .map(|borrow| {
            let mut region = liveness
                .live_points
                .get(&borrow.ref_local)
                .cloned()
                .unwrap_or_default();
            region.insert(borrow.origin);
            region
        })
        .collect()
}

/// Check whether a borrow is active at a program point.
pub fn is_borrow_active(borrow_idx: BorrowIndex, point: ProgramPoint, regions: &[Region]) -> bool {
    regions.get(borrow_idx).is_some_and(|r| r.contains(&point))
}
