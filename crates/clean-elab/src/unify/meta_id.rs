// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core data types for metavariable tracking.

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

/// Unique identifier for metavariables
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MetaId(pub(crate) u64);

impl MetaId {
    /// Returns the raw numeric identifier.
    pub fn as_u64(self) -> u64 {
        self.0
    }
}

/// Which metavariables the unifier may restrict to a smaller local context.
///
/// Lean's `MetavarKind` (`Lean/MetavarContext.lean`) reduced to the one
/// distinction Clean's unifier reads: `CheckAssignment.checkMVar`
/// (`Lean/Meta/ExprDefEq.lean:856-890`) approximates the context of a NATURAL
/// metavariable and refuses a synthetic-opaque one.
///
/// The default is [`MetaKind::Opaque`], deliberately the conservative side of
/// Lean's rule: Clean has consumers that hold on to a metavariable's identity
/// and scope — the deferred-instance list (`resolve_deferred_instances`), the
/// tactic goal list and its assignment-scope check, and the `refine` bridge's
/// hole collector — and a meta minted by an unaudited site must never have its
/// scope narrowed behind their backs. Only the minting sites that correspond
/// to Lean's natural metavariables (implicit arguments, anonymous `_` holes,
/// unannotated binder types) opt in with [`MetaKind::Natural`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum MetaKind {
    /// Lean's `.natural`: its local context may be approximated.
    Natural,
    /// Every other metavariable: never approximated.
    #[default]
    Opaque,
}

/// A metavariable
#[derive(Debug, Clone)]
pub struct MetaVar {
    /// The type of the metavariable
    pub ty: Expr,
    /// Local context visible when the metavariable was created.
    ///
    /// Only ever NARROWED after creation, by the unifier's `ctxApprox` port
    /// (`MetaState::restrict_locals`), and only for a [`MetaKind::Natural`]
    /// metavariable.
    pub locals: Vec<(clean_parser::SurfaceName, clean_kernel::FVarId, Expr)>,
    /// Whether the unifier may approximate [`Self::locals`] (see [`MetaKind`]).
    pub(crate) kind: MetaKind,
    /// The assigned value (if any)
    pub assignment: Option<Expr>,
    /// Source span of the surface hole (`_`) that created this metavariable,
    /// when it originates from a user-written hole.
    ///
    /// Additive and informational only: it lets IDE surfaces (e.g. the LSP
    /// `$/lean/plainTermGoal` request) map a metavariable back to the hole the
    /// user can hover. `None` for the vast majority of metavariables, which are
    /// synthesized internally (implicit arguments, fresh sorts, etc.) and have
    /// no user-visible source token.
    pub span: Option<clean_parser::Span>,
}

// ============================================================================
// Undo Trail Pattern (Part of #383)
// ============================================================================
//
// The undo trail enables efficient backtracking for tactic proof search without
// cloning the entire MetaState. Inspired by ay's EUF undo trail pattern.
//
// Design: `reports/research/2026-01-28-R325-cross-repo-patterns.md` Pattern #3
// Reference: `~/ay/crates/ay-theories/euf/src/lib.rs` UndoRecord

/// Record of a change made to MetaState that can be undone.
///
/// When modifications are made to MetaState, an UndoRecord is pushed to the
/// undo_trail. When `pop_scope()` is called, records are replayed in reverse
/// order to restore the previous state.
#[derive(Debug, Clone)]
pub(super) enum UndoRecord {
    /// A metavariable was assigned a value
    /// Stores: (meta_id, previous_assignment)
    MetaAssign {
        /// The metavariable that was modified
        id: MetaId,
        /// Previous assignment (None if it was unassigned)
        old_value: Option<Expr>,
    },
    /// A new metavariable was created
    /// On undo: remove it from the metas map
    MetaCreate {
        /// The metavariable that was created
        id: MetaId,
    },
    /// A metavariable's captured local scope was narrowed (`ctxApprox`).
    /// On undo: restore the previous scope.
    MetaLocals {
        /// The metavariable whose scope was narrowed
        id: MetaId,
        /// The scope before narrowing
        old_locals: Vec<(clean_parser::SurfaceName, clean_kernel::FVarId, Expr)>,
    },
    /// The fresh metavariable id cursor changed.
    ///
    /// This is independent from `MetaCreate`: importing an existing high-id
    /// metavariable can advance the cursor without creating that metavariable,
    /// while merging several new metavariables should record only one cursor
    /// change. Storing the exact previous value also handles sparse/high ids.
    NextId {
        /// Exact cursor value before the change
        old_value: u64,
    },
    /// A level equation was POSTPONED (pushed onto the deferred queue).
    ///
    /// On undo: pop it. The queue must not survive a rolled-back speculative
    /// branch, or a constraint from an abandoned path would be drained — and
    /// fail — against a state that never produced it.
    ///
    /// (A `LevelConstraint` variant sat below this one, guarding the legacy
    /// `level_constraints` map — and the stray `/// A level constraint was
    /// added (legacy map)` line that had drifted onto THIS variant's doc was
    /// its. Both removed 2026-08-26 with the map: U2 stage-3 deferral 2,
    /// `docs/analysis/u2-stage3-deferrals-2026-08-26.md`.)
    LevelPostpone,
    /// A numeral was postponed (pushed onto `postponed_numerals`). On undo:
    /// pop it, so an entry never outlives the branch that minted its
    /// metavariable (whose id a later branch may re-mint).
    NumeralPostpone,
    /// A level parent pointer was set (union-find)
    LevelParent {
        /// The parameter name
        name: Name,
        /// Previous parent (None if not present)
        old_parent: Option<Name>,
    },
    /// A concrete level was assigned
    LevelConcrete {
        /// The root parameter name
        name: Name,
        /// Previous concrete level (None if not present)
        old_level: Option<Level>,
    },
    /// A compound (params-containing, non-param) level was assigned (U2 rung-1a)
    LevelBound {
        /// The root parameter name
        name: Name,
        /// Previous bound level (None if not present)
        old_level: Option<Level>,
    },
}
