// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Whether pinned Lean's `Init` synthesizes `Inhabited T` where Clean's own
//! instance search may not: Clean's prelude lacks many of Lean's instances
//! (`Int`, `Char`, `UInt8`, `Float`, `Array`, `Prod`, `Fin (n+1)`, `True`,
//! `Sort u`, the function types, the monads …).
//!
//! Two callers ask, and each takes the answer it can afford (review r6's fix
//! round; docs/DECISIONS.md R134, R137):
//!
//! * a body-less `opaque` is ACCEPTED only on [`LeanInhabited::Yes`]: the
//!   kernel registers it as an axiom, so `Yes` is said only of types that are
//!   inhabited by an instance both pinned Leans have;
//! * `deriving Inhabited` moves past a constructor only on
//!   [`LeanInhabited::No`], where both Leans fail too; anything else refuses,
//!   since a later constructor than Lean's would change `default`.
//!
//! The table was measured on 2026-10-24 with `#synth Inhabited T` through
//! `bin/lean` of 4.8.0 and of 4.30.0-rc2 (Lean 4.8.0's instances are in
//! `src/lean/Init`): a type is `Yes` when both synthesize it, `No` when both
//! fail, and [`LeanInhabited::Unknown`] when they disagree (`Sum`, `PSum`,
//! `Thunk`, `ULift`) or the type was not measured.

use super::ElabCtx;
use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Literal};
use clean_parser::SurfaceName;

/// What both pinned Leans' instance search does with `Inhabited T`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LeanInhabited {
    /// Both synthesize it.
    Yes,
    /// Both fail.
    No,
    /// They disagree, or the type is outside the measured table.
    Unknown,
}

/// Heads both Leans have an argument-free instance for (`#synth`, 2026-10-24).
const ALWAYS: &[&str] = &[
    "Nat",
    "Int",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "USize",
    "Float",
    "Char",
    "String",
    "Bool",
    "Unit",
    "PUnit",
    "Prop",
    "True",
    "Substring",
    "ByteArray",
    "FloatArray",
    "Lean.Name",
    "Lean.Syntax",
    "StdGen",
    "Ordering",
    "Std.Format",
    "System.FilePath",
    "NonemptyType",
    "IO",
    "Option",
    "List",
    "Array",
    "BitVec",
    "Task",
];

/// Heads both Leans fail on, whatever the arguments.
const NEVER: &[&str] = &["Empty", "PEmpty", "False", "Subtype", "PLift"];

impl ElabCtx<'_> {
    /// [`LeanInhabited`] for `ty`, read in the current local context; a local
    /// instance in scope counts, as it does for Lean.
    pub(super) fn lean_init_inhabited(&mut self, ty: &Expr) -> LeanInhabited {
        self.lean_init_inhabited_at(ty, 0)
    }

    fn lean_init_inhabited_at(&mut self, ty: &Expr, depth: u64) -> LeanInhabited {
        use LeanInhabited::{No, Unknown, Yes};
        if depth > 32 {
            return Unknown;
        }
        let ty = self.metas.instantiate(ty);
        // `instance (α) {β : α → Sort v} [(a : α) → Inhabited (β a)] :
        // Inhabited ((a : α) → β a)`: the codomain under a plain local. The
        // binder is NOT a local instance, even when it is `[…]`: Lean only
        // introduces a declaration's header binders, never its type's.
        if let ExprKind::Pi(_, dom, body) = ty.kind() {
            let saved = self.locals.len();
            let fvar = self.fresh_fvar();
            self.push_local_with_fvar(
                SurfaceName::unspellable("__lean_inhabited", depth),
                fvar,
                dom.as_ref().clone(),
            );
            let answer =
                self.lean_init_inhabited_at(&body.instantiate(&Expr::fvar(fvar)), depth + 1);
            self.locals.truncate(saved);
            return answer;
        }
        if matches!(ty.kind(), ExprKind::Sort(_)) {
            return Yes;
        }
        if self.clean_synthesizes_inhabited(&ty) {
            return Yes;
        }
        // A proposition other than `True` (measured: `0 = 0`, `n < 256`).
        if self.infer_sort(&ty).is_ok_and(|level| level.is_zero()) {
            return if is_const(&ty, "True") { Yes } else { No };
        }
        let head = ty.get_app_fn().clone();
        let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();
        let name = match head.kind() {
            // A local (a parameter, a field, the inductive being derived) has
            // only the instances in scope, which Clean searched above.
            ExprKind::FVar(id) if MetaState::from_fvar(*id).is_none() => return No,
            ExprKind::Const(name, _) => name.clone(),
            _ => return Unknown,
        };
        let spelled = name.to_string();
        let arg = |i: usize| args.get(i).cloned();
        if ALWAYS.contains(&spelled.as_str()) {
            return Yes;
        }
        if NEVER.contains(&spelled.as_str()) {
            return No;
        }
        match (spelled.as_str(), args.len()) {
            ("Prod" | "MProd" | "PProd", 2) => {
                let (Some(a), Some(b)) = (arg(0), arg(1)) else {
                    return Unknown;
                };
                both(self.lean_init_inhabited_at(&a, depth + 1), || {
                    self.lean_init_inhabited_at(&b, depth + 1)
                })
            }
            // `[Inhabited ε]` (measured `Except String Empty`: both `Yes`).
            ("Except" | "EStateM" | "EIO" | "EST", _) if !args.is_empty() => {
                arg(0).map_or(Unknown, |e| self.lean_init_inhabited_at(&e, depth + 1))
            }
            ("Id", 1) => arg(0).map_or(Unknown, |a| self.lean_init_inhabited_at(&a, depth + 1)),
            // `instInhabitedOfMonad`: `[Monad m] [Inhabited α]`, for the monads
            // whose `Monad` instance both Leans have.
            ("StateM", 2) => arg(1).map_or(Unknown, |a| self.lean_init_inhabited_at(&a, depth + 1)),
            ("StateT" | "ExceptT" | "ReaderT", 3) | ("OptionT", 2) => {
                let monad = if spelled == "OptionT" { arg(0) } else { arg(1) };
                let value = args.last().cloned();
                match (monad, value) {
                    (Some(m), Some(a)) if is_known_monad(&m) => {
                        self.lean_init_inhabited_at(&a, depth + 1)
                    }
                    _ => Unknown,
                }
            }
            ("Fin", 1) => match arg(0) {
                Some(n) if is_successor(&n) => Yes,
                Some(n) if is_zero_literal(&n) => No,
                Some(n) if matches!(n.kind(), ExprKind::FVar(id) if MetaState::from_fvar(*id).is_none()) => {
                    No
                }
                _ => Unknown,
            },
            // A type this source declared: Lean has only the instances the
            // source declared, and Clean searched those above.
            _ if crate::declared_here::declared_in_source(self.env, &name) => No,
            _ => Unknown,
        }
    }

    /// Clean's own `Inhabited ty` search, current local instances included.
    fn clean_synthesizes_inhabited(&mut self, ty: &Expr) -> bool {
        let Ok(level) = self.infer_sort(ty) else {
            return false;
        };
        let goal = Expr::app(
            Expr::const_(Name::from_string("Inhabited"), vec![level]),
            ty.clone(),
        );
        self.resolve_instance(&goal).is_some()
    }
}

/// `Yes` only when both are; `No` when either is.
fn both(first: LeanInhabited, second: impl FnOnce() -> LeanInhabited) -> LeanInhabited {
    match first {
        LeanInhabited::No => LeanInhabited::No,
        LeanInhabited::Yes => second(),
        LeanInhabited::Unknown => match second() {
            LeanInhabited::No => LeanInhabited::No,
            _ => LeanInhabited::Unknown,
        },
    }
}

fn is_const(expr: &Expr, name: &str) -> bool {
    matches!(expr.get_app_fn().kind(), ExprKind::Const(head, _) if head.to_string() == name)
        && expr.get_app_args().is_empty()
}

/// A monad both Leans have a `Monad` instance for, recognised by its head.
fn is_known_monad(m: &Expr) -> bool {
    let head = match m.get_app_fn().kind() {
        ExprKind::Const(head, _) => head.to_string(),
        _ => return false,
    };
    let args = m.get_app_args().len();
    matches!(
        (head.as_str(), args),
        ("Id" | "IO" | "Option" | "BaseIO", 0)
            | ("Except" | "EIO", 1)
            | ("StateT" | "ReaderT" | "ExceptT" | "EStateM", 2)
            | ("StateM" | "OptionT", 1)
    )
}

/// `n + k` (`k ≥ 1`), `Nat.succ n` or a literal `≥ 1`: what Lean's
/// `Fin (no_index (n+1))` instance unifies with.
fn is_successor(n: &Expr) -> bool {
    if let Some(value) = nat_literal(n) {
        return value >= 1;
    }
    let head = match n.get_app_fn().kind() {
        ExprKind::Const(head, _) => head.to_string(),
        _ => return false,
    };
    let args = n.get_app_args();
    match (head.as_str(), args.len()) {
        ("Nat.succ", 1) => true,
        ("HAdd.hAdd", 6) | ("Nat.add", 2) => args
            .last()
            .copied()
            .and_then(nat_literal)
            .is_some_and(|k| k >= 1),
        _ => false,
    }
}

fn is_zero_literal(n: &Expr) -> bool {
    nat_literal(n) == Some(0)
}

/// A natural-number literal, raw or through `OfNat.ofNat`.
fn nat_literal(n: &Expr) -> Option<u64> {
    match n.kind() {
        ExprKind::Lit(Literal::Nat(value)) => value.to_u64(),
        ExprKind::MData(_, inner) => nat_literal(inner),
        _ => {
            let args = n.get_app_args();
            match n.get_app_fn().kind() {
                ExprKind::Const(head, _)
                    if head.to_string() == "OfNat.ofNat" && args.len() == 3 =>
                {
                    nat_literal(args[1])
                }
                _ => None,
            }
        }
    }
}
