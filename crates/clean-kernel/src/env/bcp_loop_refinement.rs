// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for BCP loop refinement.
//!
//! Formalizes the Boolean Constraint Propagation inner loop as a refinement
//! layer over the existing IsaSAT and CDCL soundness overlays:
//! 1. Abstract BCP specification over a propagation state.
//! 2. Imperative watched-literal loop with mutable watch arrays.
//! 3. Local helper operations for blocker checks, XOR-based watched-literal
//!    recovery, binary-clause detection, and in-place watch-list compaction.
//!
//! This module intentionally follows the lightweight overlay pattern used by
//! `isasat_refinement.rs`: it registers only the type and operation surfaces
//! needed by later theorem modules.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all BCP loop refinement declarations.
pub(super) struct BCPLoopConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// BCPLoop.Literal : Type
    pub(super) literal: Expr,
    /// BCPLoop.WatchEntry : Type
    pub(super) watch_entry: Expr,
    /// BCPLoop.WatchList : Type
    pub(super) watch_list: Expr,
    /// BCPLoop.ImperativeState : Type
    pub(super) imperative_state: Expr,
    /// BCPLoop.AbstractBCPState : Type
    pub(super) abstract_bcp_state: Expr,
    /// BCPLoop.BCPResult : Type
    pub(super) bcp_result: Expr,
}

impl BCPLoopConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            literal: Expr::const_(Name::from_string("BCPLoop.Literal"), vec![]),
            watch_entry: Expr::const_(Name::from_string("BCPLoop.WatchEntry"), vec![]),
            watch_list: Expr::const_(Name::from_string("BCPLoop.WatchList"), vec![]),
            imperative_state: Expr::const_(Name::from_string("BCPLoop.ImperativeState"), vec![]),
            abstract_bcp_state: Expr::const_(Name::from_string("BCPLoop.AbstractBCPState"), vec![]),
            bcp_result: Expr::const_(Name::from_string("BCPLoop.BCPResult"), vec![]),
        }
    }
}

/// Register an axiom with idempotency check.
fn add_bcp_loop_axiom(env: &mut Environment, name: &str, type_: Expr) -> Result<(), EnvError> {
    if env.get_const(&Name::from_string(name)).is_some() {
        return Ok(());
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
}

impl Environment {
    /// Initialize BCP loop refinement declarations.
    ///
    /// Depends on: `init_bool()`, `init_nat()`, `init_isasat_refinement()`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_bcp_loop_refinement(&mut self) -> Result<(), EnvError> {
        if self.bcp_loop_refinement_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;
        self.init_isasat_refinement()?;

        let c = BCPLoopConsts::new();

        // Type definitions
        self.register_bcp_loop_literal(&c)?;
        self.register_bcp_loop_watch_entry(&c)?;
        self.register_bcp_loop_watch_list(&c)?;
        self.register_bcp_loop_imperative_state(&c)?;
        self.register_bcp_loop_abstract_bcp_state(&c)?;
        self.register_bcp_loop_bcp_result(&c)?;

        // Operation definitions
        self.register_bcp_loop_propagate_abstract(&c)?;
        self.register_bcp_loop_propagate_imperative(&c)?;
        self.register_bcp_loop_xor_other_watched(&c)?;
        self.register_bcp_loop_blocker_check(&c)?;
        self.register_bcp_loop_is_binary_clause(&c)?;
        self.register_bcp_loop_compaction_step(&c)?;

        // Theorem registrations (in bcp_loop_refinement_theorems.rs)
        self.register_two_pointer_compaction_invariant(&c)?;
        self.register_xor_identity(&c)?;
        self.register_watch_consistency_preserved(&c)?;
        self.register_bcp_refinement(&c)?;
        self.register_blocker_soundness(&c)?;
        self.register_binary_clause_propagation(&c)?;
        self.register_replacement_search_complete(&c)?;
        self.register_compaction_preserves_watches(&c)?;

        self.bcp_loop_refinement_init = true;
        Ok(())
    }

    // ====================================================================
    // Type definitions
    // ====================================================================

    /// `Literal : Type` -- Nat-indexed literal surface.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_literal(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        add_bcp_loop_axiom(self, "BCPLoop.Literal", c.type0.clone())?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.Literal.index",
            Expr::pi(BinderInfo::Default, c.literal.clone(), c.nat.clone()),
        )
    }

    /// `WatchEntry : Type` -- watched-literal entry for one clause occurrence.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_watch_entry(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        add_bcp_loop_axiom(self, "BCPLoop.WatchEntry", c.type0.clone())?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.WatchEntry.blocker",
            Expr::pi(
                BinderInfo::Default,
                c.watch_entry.clone(),
                c.literal.clone(),
            ),
        )?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.WatchEntry.clause_idx",
            Expr::pi(BinderInfo::Default, c.watch_entry.clone(), c.nat.clone()),
        )?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.WatchEntry.lit0",
            Expr::pi(
                BinderInfo::Default,
                c.watch_entry.clone(),
                c.literal.clone(),
            ),
        )?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.WatchEntry.lit1",
            Expr::pi(
                BinderInfo::Default,
                c.watch_entry.clone(),
                c.literal.clone(),
            ),
        )
    }

    /// `WatchList : Type` -- mutable array of watch entries.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_watch_list(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        add_bcp_loop_axiom(self, "BCPLoop.WatchList", c.type0.clone())
    }

    /// `ImperativeState : Type` -- mutable BCP loop state with scan pointers.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_imperative_state(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        let isasat_trail = Expr::const_(Name::from_string("IsaSAT.Trail"), vec![]);

        add_bcp_loop_axiom(self, "BCPLoop.ImperativeState", c.type0.clone())?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.ImperativeState.watches",
            Expr::pi(
                BinderInfo::Default,
                c.imperative_state.clone(),
                c.watch_list.clone(),
            ),
        )?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.ImperativeState.assignment",
            Expr::pi(
                BinderInfo::Default,
                c.imperative_state.clone(),
                Expr::pi(BinderInfo::Default, c.literal.clone(), c.bool_.clone()),
            ),
        )?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.ImperativeState.trail",
            Expr::pi(
                BinderInfo::Default,
                c.imperative_state.clone(),
                isasat_trail,
            ),
        )?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.ImperativeState.i_ptr",
            Expr::pi(
                BinderInfo::Default,
                c.imperative_state.clone(),
                c.nat.clone(),
            ),
        )?;
        add_bcp_loop_axiom(
            self,
            "BCPLoop.ImperativeState.j_ptr",
            Expr::pi(
                BinderInfo::Default,
                c.imperative_state.clone(),
                c.nat.clone(),
            ),
        )
    }

    /// `AbstractBCPState : Type` -- abstract propagation state used by the
    /// high-level BCP specification.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_abstract_bcp_state(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        add_bcp_loop_axiom(self, "BCPLoop.AbstractBCPState", c.type0.clone())
    }

    /// `BCPResult : Type` -- propagation outcome with `ok` and `conflict`
    /// constructors.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_bcp_result(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        add_bcp_loop_axiom(self, "BCPLoop.BCPResult", c.type0.clone())?;
        add_bcp_loop_axiom(self, "BCPLoop.BCPResult.ok", c.bcp_result.clone())?;
        add_bcp_loop_axiom(self, "BCPLoop.BCPResult.conflict", c.bcp_result.clone())
    }

    // ====================================================================
    // Operation definitions
    // ====================================================================

    /// `propagate_abstract : AbstractBCPState -> BCPResult`.
    ///
    /// The abstract BCP specification over the propagation state.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_propagate_abstract(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        add_bcp_loop_axiom(
            self,
            "BCPLoop.propagate_abstract",
            Expr::pi(
                BinderInfo::Default,
                c.abstract_bcp_state.clone(),
                c.bcp_result.clone(),
            ),
        )
    }

    /// `propagate_imperative : ImperativeState -> BCPResult`.
    ///
    /// The imperative BCP loop using a mutable watch array and two-pointer scan.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_propagate_imperative(
        &mut self,
        c: &BCPLoopConsts,
    ) -> Result<(), EnvError> {
        add_bcp_loop_axiom(
            self,
            "BCPLoop.propagate_imperative",
            Expr::pi(
                BinderInfo::Default,
                c.imperative_state.clone(),
                c.bcp_result.clone(),
            ),
        )
    }

    /// `xor_other_watched : WatchEntry -> Literal -> Literal`.
    ///
    /// Given a watch entry and one watched literal, recover the other watched
    /// literal using the usual XOR trick.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_xor_other_watched(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (we_id, _) = b.fresh_local(c.watch_entry.clone());
            let (lit_id, _) = b.fresh_local(c.literal.clone());
            let e = b.mk_pi(
                lit_id,
                BinderInfo::Default,
                c.literal.clone(),
                c.literal.clone(),
            );
            let e = b.mk_pi(we_id, BinderInfo::Default, c.watch_entry.clone(), e);
            b.finish(e)
        };
        add_bcp_loop_axiom(self, "BCPLoop.xor_other_watched", ty)
    }

    /// `blocker_check : ImperativeState -> WatchEntry -> Bool`.
    ///
    /// Fast-path check: if the blocker literal is satisfied, the watch entry can
    /// stay in place without scanning the full clause body.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_blocker_check(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (st_id, _) = b.fresh_local(c.imperative_state.clone());
            let (we_id, _) = b.fresh_local(c.watch_entry.clone());
            let e = b.mk_pi(
                we_id,
                BinderInfo::Default,
                c.watch_entry.clone(),
                c.bool_.clone(),
            );
            let e = b.mk_pi(st_id, BinderInfo::Default, c.imperative_state.clone(), e);
            b.finish(e)
        };
        add_bcp_loop_axiom(self, "BCPLoop.blocker_check", ty)
    }

    /// `is_binary_clause : WatchEntry -> Bool`.
    ///
    /// Detect whether the watched clause is binary, enabling the direct
    /// propagation/conflict fast path.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_is_binary_clause(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        add_bcp_loop_axiom(
            self,
            "BCPLoop.is_binary_clause",
            Expr::pi(BinderInfo::Default, c.watch_entry.clone(), c.bool_.clone()),
        )
    }

    /// `compaction_step : ImperativeState -> ImperativeState`.
    ///
    /// One in-place watch-list compaction step using the standard `j <= i`
    /// invariant of the imperative two-pointer scan.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_bcp_loop_compaction_step(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        add_bcp_loop_axiom(
            self,
            "BCPLoop.compaction_step",
            Expr::pi(
                BinderInfo::Default,
                c.imperative_state.clone(),
                c.imperative_state.clone(),
            ),
        )
    }
}
