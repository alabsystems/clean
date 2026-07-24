// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for IsaSAT stepwise refinement.
//!
//! Formalizes the abstract CDCL_W transition system and the concrete
//! watched-literal refinement from IsaSAT, the only verified SAT solver
//! competitive at SAT-COMP.
//!
//! The formalization follows the stepwise refinement architecture:
//! 1. Abstract CDCL_W: non-deterministic transition system (Propagate,
//!    Decide, Conflict, Learn, Forget, Restart, Backtrack).
//! 2. Concrete state with two-watched literal data structures.
//! 3. Simulation relation connecting abstract and concrete states.
//! 4. Invariant preservation across all transition steps.
//!
//! Type and operation definitions live here; theorem registrations are in
//! `isasat_refinement_theorems.rs`.
//!
//! References:
//!   Fleury & Lammich (2019), "A Verified SAT Solver with Watched
//!     Literals Using Imperative HOL," CPP 2019;
//!   Fleury & Lammich (2020), "A Pragmatic Approach to CDCL for
//!     IsaSAT," FMCAD 2020.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all IsaSAT refinement declarations.
pub(super) struct IsaSATConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// IsaSAT.CDCLState : Type
    pub(super) cdcl_state: Expr,
    /// IsaSAT.Trail : Type
    pub(super) trail: Expr,
    /// IsaSAT.ClauseDB : Type
    pub(super) clause_db: Expr,
    /// IsaSAT.Conflict : Type
    pub(super) conflict: Expr,
    /// IsaSAT.WatchList : Type
    pub(super) watch_list: Expr,
    /// IsaSAT.ConcreteState : Type
    pub(super) concrete_state: Expr,
}

impl IsaSATConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            cdcl_state: Expr::const_(Name::from_string("IsaSAT.CDCLState"), vec![]),
            trail: Expr::const_(Name::from_string("IsaSAT.Trail"), vec![]),
            clause_db: Expr::const_(Name::from_string("IsaSAT.ClauseDB"), vec![]),
            conflict: Expr::const_(Name::from_string("IsaSAT.Conflict"), vec![]),
            watch_list: Expr::const_(Name::from_string("IsaSAT.WatchList"), vec![]),
            concrete_state: Expr::const_(Name::from_string("IsaSAT.ConcreteState"), vec![]),
        }
    }
}

impl Environment {
    /// Initialize IsaSAT refinement declarations.
    ///
    /// Depends on: `init_bool()`, `init_nat()`.
    pub(crate) fn init_isasat_refinement(&mut self) -> Result<(), EnvError> {
        if self.isasat_refinement_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;

        let c = IsaSATConsts::new();

        // Type definitions
        self.register_isasat_cdcl_state(&c)?;
        self.register_isasat_trail(&c)?;
        self.register_isasat_clause_db(&c)?;
        self.register_isasat_conflict(&c)?;
        self.register_isasat_cdcl_transition(&c)?;

        // Operation definitions
        self.register_isasat_cdcl_step(&c)?;
        self.register_isasat_cdcl_invariant(&c)?;
        self.register_isasat_trail_consistent(&c)?;
        self.register_isasat_all_propagated(&c)?;
        self.register_isasat_trail_of(&c)?;

        // Concrete refinement types and operations
        self.register_isasat_watch_list(&c)?;
        self.register_isasat_concrete_state(&c)?;
        self.register_isasat_refinement_relation(&c)?;
        self.register_isasat_abstract_of(&c)?;
        self.register_isasat_concrete_propagate(&c)?;

        // Theorem registrations (in isasat_refinement_theorems.rs)
        self.register_invariant_preserved_by_propagate(&c)?;
        self.register_invariant_preserved_by_decide(&c)?;
        self.register_invariant_preserved_by_backtrack(&c)?;
        self.register_refinement_simulation_propagate(&c)?;
        self.register_refinement_preserves_invariant(&c)?;
        self.register_trail_consistency_preserved(&c)?;

        self.isasat_refinement_init = true;
        Ok(())
    }

    // ====================================================================
    // Type definitions
    // ====================================================================

    /// `CDCLState : Type` -- abstract CDCL state with trail, clause DB,
    /// and conflict.
    fn register_isasat_cdcl_state(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.CDCLState"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.CDCLState"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `Trail : Type` -- assignment trail with decision levels.
    fn register_isasat_trail(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("IsaSAT.Trail")).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.Trail"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `ClauseDB : Type` -- clause database (set of clauses).
    fn register_isasat_clause_db(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.ClauseDB"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.ClauseDB"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `Conflict : Type` -- conflict status (None or Some clause).
    fn register_isasat_conflict(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.Conflict"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.Conflict"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `CDCLTransition : Type` -- abstract transition kind.
    ///
    /// Registered as an opaque type with nullary constructor constants
    /// for `Propagate`, `Decide`, `Conflict`, `Learn`, `Forget`,
    /// `Restart`, and `Backtrack`.
    fn register_isasat_cdcl_transition(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.CDCLTransition"))
            .is_some()
        {
            return Ok(());
        }
        let cdcl_transition = Expr::const_(Name::from_string("IsaSAT.CDCLTransition"), vec![]);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.CDCLTransition"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;

        for ctor in [
            "Propagate",
            "Decide",
            "Conflict",
            "Learn",
            "Forget",
            "Restart",
            "Backtrack",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(&format!("IsaSAT.CDCLTransition.{ctor}")),
                level_params: vec![],
                type_: cdcl_transition.clone(),
            })?;
        }
        Ok(())
    }

    // ====================================================================
    // Operation definitions
    // ====================================================================

    /// `cdcl_step : CDCLState -> CDCLTransition -> CDCLState`.
    ///
    /// The abstract transition function: given a state and a transition
    /// kind, produce the next state.
    fn register_isasat_cdcl_step(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.cdcl_step"))
            .is_some()
        {
            return Ok(());
        }
        let cdcl_transition = Expr::const_(Name::from_string("IsaSAT.CDCLTransition"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
            let (t_id, _) = b.fresh_local(cdcl_transition.clone());
            let e = b.mk_pi(
                t_id,
                BinderInfo::Default,
                cdcl_transition,
                c.cdcl_state.clone(),
            );
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.cdcl_step"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cdcl_invariant : CDCLState -> ClauseDB -> Prop`.
    ///
    /// The abstract state invariant: trail is consistent, all assignments
    /// are justified by propagation or decision, and no falsified clause
    /// is undetected.
    fn register_isasat_cdcl_invariant(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.cdcl_invariant"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
            let (db_id, _) = b.fresh_local(c.clause_db.clone());
            let e = b.mk_pi(
                db_id,
                BinderInfo::Default,
                c.clause_db.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.cdcl_invariant"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `trail_consistent : Trail -> Prop`.
    ///
    /// No variable appears both positively and negatively on the trail.
    fn register_isasat_trail_consistent(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.trail_consistent"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.trail.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.trail_consistent"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `all_propagated : CDCLState -> Prop`.
    ///
    /// All unit propagations have been exhaustively applied.
    fn register_isasat_all_propagated(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.all_propagated"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.all_propagated"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `trail_of : CDCLState -> Trail`.
    ///
    /// Projects the assignment trail from an abstract CDCL state.
    fn register_isasat_trail_of(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.trail_of"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.trail.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.trail_of"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Concrete refinement types and operations
    // ====================================================================

    /// `WatchList : Type` -- two-watched literal data structure for the
    /// concrete implementation.
    fn register_isasat_watch_list(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.WatchList"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.WatchList"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `ConcreteState : Type` -- concrete state carrying watch lists.
    ///
    /// Also registers the projection `ConcreteState.watch_list`.
    fn register_isasat_concrete_state(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.ConcreteState"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.ConcreteState"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;

        // Projection: ConcreteState.watch_list : ConcreteState -> WatchList
        let watch_list_ty = Expr::pi(
            BinderInfo::Default,
            c.concrete_state.clone(),
            c.watch_list.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.ConcreteState.watch_list"),
            level_params: vec![],
            type_: watch_list_ty,
        })
    }

    /// `refinement_relation : CDCLState -> ConcreteState -> Prop`.
    ///
    /// The simulation relation between abstract and concrete states:
    /// the concrete state faithfully represents the abstract state.
    fn register_isasat_refinement_relation(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.refinement_relation"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
            let (cs_id, _) = b.fresh_local(c.concrete_state.clone());
            let e = b.mk_pi(
                cs_id,
                BinderInfo::Default,
                c.concrete_state.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.refinement_relation"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `abstract_of : ConcreteState -> CDCLState`.
    ///
    /// Abstraction function: extracts the abstract CDCL state from a
    /// concrete state by forgetting implementation details.
    fn register_isasat_abstract_of(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.abstract_of"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.concrete_state.clone(),
            c.cdcl_state.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.abstract_of"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `concrete_propagate : ConcreteState -> ConcreteState`.
    ///
    /// The concrete propagation step using two-watched literals.
    fn register_isasat_concrete_propagate(&mut self, c: &IsaSATConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("IsaSAT.concrete_propagate"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.concrete_state.clone(),
            c.concrete_state.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("IsaSAT.concrete_propagate"),
            level_params: vec![],
            type_: ty,
        })
    }
}
