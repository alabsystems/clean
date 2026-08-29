// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sink a recursor arm's induction-hypothesis binding to the local function
//! that uses it.
//!
//! # Why this exists
//!
//! [`super::lower::build_rec_arm_body`] materializes each recursive field's
//! induction hypothesis as a `let ih := go(.., field)` at the TOP of the arm,
//! before the minor premise's body is lowered — the recursor's own reading, in
//! which the minor receives the IH as an already-computed *value*.
//!
//! That reading is sound for a lazy or world-token `IO`. It is NOT sound for
//! this compiler's `IO`, whose effects fire when the emitted C function is
//! CALLED (`clean-cli/src/native_build.rs` § *IO lowering*: "Effects fire in
//! source order"). Under that model a hoisted self-call is a hoisted *effect*,
//! and
//!
//! ```lean
//! def dump : List String -> IO Unit
//!   | []        => pure ()
//!   | s :: rest => do IO.println s; dump rest
//! ```
//!
//! emitted `_x5 = go(rest); _x6 = IO.println(s); Bind.bind(_x6, fun _ => _x5)`
//! — the whole tail printed before the head, `dump ["a","b","c"]` printing
//! `c b a` with status 0.
//!
//! # What this does
//!
//! The IH is moved to the position the SOURCE gives it: the body of the local
//! function that consumes it. That is also what a direct-recursive-call
//! compilation emits, so the transform does not invent an ordering — it
//! restores the one the recursor spelling erased.
//!
//! Movement is **only ever later**, never earlier, and only past code that does
//! not use the binding, so the IH still runs before every use of it. When the
//! uses do not all sit inside one local function the binding stops at the first
//! node that mentions it, which is at worst where it already was.
//!
//! # What this deliberately does not do
//!
//! * **Join points are not sunk into.** A join point may be jumped to more than
//!   once, so a binding moved inside its body would run once per jump. `to_lcnf`
//!   does not build join points (`join_point_lower` runs later), so excluding
//!   them costs nothing and keeps the pass safe if that changes.
//! * **`Cases` alternatives are not sunk into.** Making the recursive call
//!   conditional on a branch is a larger semantic move than restoring a source
//!   position, and no measured defect asks for it.

use crate::lcnf::{Alt, Arg, Cases, Code, LetDecl, LetValue};
use clean_kernel::FVarId;

/// Sink each of `ihs` to the local function that uses it, if there is one.
///
/// `ihs` are the induction-hypothesis bindings the caller placed at the head of
/// `code`'s top-level chain. Bindings that are absent, unused, or already in
/// place are left exactly where they are.
pub(super) fn sink_ih_bindings(mut code: Code, ihs: &[FVarId]) -> Code {
    for ih in ihs {
        code = sink_one(code, *ih);
    }
    code
}

/// Find `target`'s binding in `code`'s top-level chain and re-place it.
///
/// Only the chain is searched: the caller binds the IH there, so a miss means
/// some other pass already moved it and this pass declines to guess.
fn sink_one(code: Code, target: FVarId) -> Code {
    match code {
        Code::Let(decl, rest) if decl.fvar_id == target => place(*rest, decl),
        Code::Let(decl, rest) => Code::Let(decl, Box::new(sink_one(*rest, target))),
        Code::Fun(decl, rest) => Code::Fun(decl, Box::new(sink_one(*rest, target))),
        Code::JoinPoint(decl, rest) => Code::JoinPoint(decl, Box::new(sink_one(*rest, target))),
        other => other,
    }
}

/// Re-attach `decl` at the deepest point of `rest` that still dominates every
/// use of it.
fn place(rest: Code, decl: LetDecl) -> Code {
    let target = decl.fvar_id;
    let total = uses_in_code(&rest, target);
    if total == 0 {
        // Unused: leave it alone. Deleting it is DCE's decision, not this
        // pass's — and under the eager-effect model deleting a self-call is a
        // semantic change, not a cleanup.
        return Code::Let(decl, Box::new(rest));
    }
    match rest {
        // The binding may move past a `let` that does not read it.
        Code::Let(other, tail) if uses_in_let_value(&other.value, target) == 0 => {
            Code::Let(other, Box::new(place(*tail, decl)))
        }
        // Every use inside one local function: that function's body is the
        // source position of the call, so sink into it and keep going.
        Code::Fun(mut fd, tail) if uses_in_code(&fd.body, target) == total => {
            let body = std::mem::replace(fd.body.as_mut(), Code::Return(target));
            *fd.body = place(body, decl);
            Code::Fun(fd, tail)
        }
        // A local function that never reads it is just more chain to walk.
        Code::Fun(fd, tail) if uses_in_code(&fd.body, target) == 0 => {
            Code::Fun(fd, Box::new(place(*tail, decl)))
        }
        Code::JoinPoint(fd, tail) if uses_in_code(&fd.body, target) == 0 => {
            Code::JoinPoint(fd, Box::new(place(*tail, decl)))
        }
        other => Code::Let(decl, Box::new(other)),
    }
}

/// Count use-position occurrences of `target` in `code`.
///
/// Binding occurrences (a `LetDecl`/`FunDecl` fvar, a parameter) are not uses.
/// Ids are globally fresh in L5CNF, so there is no shadowing to track.
fn uses_in_code(code: &Code, target: FVarId) -> usize {
    match code {
        Code::Let(decl, body) => {
            uses_in_let_value(&decl.value, target) + uses_in_code(body, target)
        }
        Code::Fun(decl, body) | Code::JoinPoint(decl, body) => {
            uses_in_code(&decl.body, target) + uses_in_code(body, target)
        }
        Code::Cases(cases) => uses_in_cases(cases, target),
        Code::Jmp { jp, args } => usize::from(*jp == target) + uses_in_args(args, target),
        Code::Return(fvar) => usize::from(*fvar == target),
        Code::Unreachable(_) => 0,
    }
}

fn uses_in_cases(cases: &Cases, target: FVarId) -> usize {
    let mut n = usize::from(cases.scrutinee == target);
    for alt in &cases.alts {
        n += uses_in_code(alt.body(), target);
        if let Alt::Ctor { .. } = alt {
            // Constructor-alt params are binders, never uses.
        }
    }
    n
}

fn uses_in_let_value(value: &LetValue, target: FVarId) -> usize {
    match value {
        LetValue::Proj { structure, .. } => usize::from(*structure == target),
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => uses_in_args(args, target),
        LetValue::FVar { fvar, args } => usize::from(*fvar == target) + uses_in_args(args, target),
        LetValue::Reuse { slot, args, .. } => {
            usize::from(*slot == target) + uses_in_args(args, target)
        }
        LetValue::Lit(_) | LetValue::Erased => 0,
    }
}

fn uses_in_args(args: &[Arg], target: FVarId) -> usize {
    args.iter()
        .filter(|arg| matches!(arg, Arg::FVar(id) if *id == target))
        .count()
}
