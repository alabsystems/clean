// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for bounded-width resolution automatizability.
//!
//! Formalizes the Atserias-Dalmau (2008) result: for unsatisfiable CNF F
//! with tree-width tw(G_F) <= k, there exists a resolution refutation of
//! width <= k+1 and size <= n^{O(k)}, findable in time O(n^{k+1}).
//!
//! Type and operation definitions live here; theorem registrations are in
//! `bounded_width_automatizability_theorems.rs`.
//!
//! References:
//!   Atserias & Dalmau (2008), "A combinatorial characterization of
//!     resolution width";
//!   Atserias, Fichte & Thurley (2011), "Clause-learning algorithms with
//!     many restarts and bounded-width resolution";
//!   Ben-Sasson & Wigderson (2001), "Short proofs are narrow — resolution
//!     made simple".

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across bounded-width automatizability declarations.
pub(super) struct BoundedWidthConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ResComplexity.CNF : Type (reused from resolution_complexity)
    pub(super) cnf: Expr,
    /// ResComplexity.Clause : Type (reused)
    pub(super) clause: Expr,
    /// BoundedWidth.PartialAssignment : Type
    pub(super) partial_assignment: Expr,
    /// BoundedWidth.ResProof : Type (dag-like resolution)
    pub(super) res_proof: Expr,
    /// BoundedWidth.CDCLTrace : Type
    pub(super) cdcl_trace: Expr,
}

impl BoundedWidthConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            cnf: Expr::const_(Name::from_string("ResComplexity.CNF"), vec![]),
            clause: Expr::const_(Name::from_string("ResComplexity.Clause"), vec![]),
            partial_assignment: Expr::const_(
                Name::from_string("BoundedWidth.PartialAssignment"),
                vec![],
            ),
            res_proof: Expr::const_(Name::from_string("BoundedWidth.ResProof"), vec![]),
            cdcl_trace: Expr::const_(Name::from_string("BoundedWidth.CDCLTrace"), vec![]),
        }
    }

    /// `PrimalGraph f` — application of PrimalGraph to a CNF formula.
    pub(super) fn primal_graph_of(&self, f: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoundedWidth.PrimalGraph"), vec![]),
            f.clone(),
        )
    }
}

impl Environment {
    /// Initialize bounded-width automatizability declarations.
    ///
    /// Depends on: `init_resolution_complexity()` (for CNF, Clause).
    pub(crate) fn init_bounded_width_automatizability(&mut self) -> Result<(), EnvError> {
        if self.bounded_width_automatizability_init {
            return Ok(());
        }
        self.init_resolution_complexity()?;

        let c = BoundedWidthConsts::new();
        // Definitions (this file)
        self.register_bw_partial_assignment(&c)?;
        self.register_bw_partial_assignment_width(&c)?;
        self.register_bw_primal_graph(&c)?;
        self.register_bw_tree_decomposition(&c)?;
        self.register_bw_tree_width(&c)?;
        self.register_bw_has_tree_width_le(&c)?;
        self.register_bw_res_proof(&c)?;
        self.register_bw_res_proof_width(&c)?;
        self.register_bw_res_proof_size(&c)?;
        self.register_bw_res_refutes(&c)?;
        self.register_bw_k_consistency(&c)?;
        self.register_bw_cdcl_trace(&c)?;
        self.register_bw_cdcl_simulates(&c)?;
        self.register_bw_poly_bound(&c)?;
        // Theorem registrations (in bounded_width_automatizability_theorems.rs)
        self.register_bw_consistency_detects_unsat(&c)?;
        self.register_bw_consistency_to_refutation(&c)?;
        self.register_bw_automatizability(&c)?;
        self.register_bw_non_automatizability_general(&c)?;
        self.register_bw_cdcl_simulates_bounded_width(&c)?;

        self.bounded_width_automatizability_init = true;
        Ok(())
    }

    // ====================================================================
    // Definitions
    // ====================================================================

    /// `BoundedWidth.PartialAssignment : Type`
    ///
    /// A partial assignment to a subset of propositional variables.
    /// Abstractly maps a subset of variable indices to Bool values.
    fn register_bw_partial_assignment(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.PartialAssignment";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `BoundedWidth.PartialAssignment.width (a : PartialAssignment) : Nat`
    ///
    /// The number of variables assigned (the domain size of the partial map).
    fn register_bw_partial_assignment_width(
        &mut self,
        c: &BoundedWidthConsts,
    ) -> Result<(), EnvError> {
        let name = "BoundedWidth.PartialAssignment.width";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.partial_assignment.clone(),
            c.nat.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.PrimalGraph (f : CNF) : Type`
    ///
    /// The primal graph of a CNF formula: vertices are variables, edges
    /// connect variables appearing together in some clause.
    fn register_bw_primal_graph(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.PrimalGraph";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.type0.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.TreeDecomposition (f : CNF) (g : PrimalGraph f) : Type`
    ///
    /// A tree decomposition of the primal graph: a tree whose nodes are
    /// labeled with bags of vertices satisfying the tree-decomposition
    /// axioms (coverage, edge, and connectedness).
    fn register_bw_tree_decomposition(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.TreeDecomposition";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let pg = c.primal_graph_of(&f);
            let (g_id, _) = b.fresh_local(pg.clone());
            let e = b.mk_pi(g_id, BinderInfo::Default, pg, c.type0.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.tree_width (f : CNF) (g : PrimalGraph f)
    ///     (td : TreeDecomposition f g) : Nat`
    ///
    /// The width of a tree decomposition: max bag size minus one.
    fn register_bw_tree_width(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.tree_width";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let td_const = Expr::const_(Name::from_string("BoundedWidth.TreeDecomposition"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let pg = c.primal_graph_of(&f);
            let (g_id, g) = b.fresh_local(pg.clone());
            let td_fg = Expr::app(Expr::app(td_const, f.clone()), g.clone());
            let (td_id, _) = b.fresh_local(td_fg.clone());
            let e = b.mk_pi(td_id, BinderInfo::Default, td_fg, c.nat.clone());
            let e = b.mk_pi(g_id, BinderInfo::Default, pg, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.has_tree_width_le (f : CNF) (k : Nat) : Prop`
    ///
    /// There exists a tree decomposition of the primal graph of f
    /// with width at most k.
    fn register_bw_has_tree_width_le(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.has_tree_width_le";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.ResProof : Type`
    ///
    /// A general (dag-like) resolution proof. Unlike TreeResProof from
    /// resolution_complexity, this allows intermediate results to be reused.
    fn register_bw_res_proof(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.ResProof";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `BoundedWidth.res_proof_width (p : ResProof) : Nat`
    ///
    /// Maximum clause width (number of literals) appearing in the proof.
    fn register_bw_res_proof_width(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.res_proof_width";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.res_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.res_proof_size (p : ResProof) : Nat`
    ///
    /// Total number of resolution steps in the proof.
    fn register_bw_res_proof_size(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.res_proof_size";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.res_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.res_refutes (p : ResProof) (f : CNF) : Prop`
    ///
    /// States that `p` is a valid resolution refutation of `f`
    /// (derives the empty clause from clauses of f).
    fn register_bw_res_refutes(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.res_refutes";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.res_proof.clone());
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), c.prop.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.res_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.k_consistency (f : CNF) (k : Nat) : Prop`
    ///
    /// The CNF formula f is k-consistent: every consistent partial assignment
    /// of width < k can be extended by one variable while remaining consistent
    /// with f. When f is unsatisfiable, (k+1)-consistency fails for tw <= k,
    /// and the failure trace yields a width-(k+1) refutation.
    fn register_bw_k_consistency(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.k_consistency";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.CDCLTrace : Type`
    ///
    /// Execution trace of a CDCL solver with restarts. Records the
    /// sequence of decisions, propagations, conflicts, learned clauses,
    /// and restart points.
    fn register_bw_cdcl_trace(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.CDCLTrace";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `BoundedWidth.cdcl_simulates (t : CDCLTrace) (p : ResProof) : Prop`
    ///
    /// The CDCL trace t p-simulates the resolution proof p: every clause
    /// in p is either an input clause or is learned by t, and the final
    /// conflict in t derives the empty clause.
    fn register_bw_cdcl_simulates(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.cdcl_simulates";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (t_id, _) = b.fresh_local(c.cdcl_trace.clone());
            let (p_id, _) = b.fresh_local(c.res_proof.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.res_proof.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(t_id, BinderInfo::Default, c.cdcl_trace.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `BoundedWidth.poly_bound (n k : Nat) : Nat`
    ///
    /// Polynomial bound function: represents n^{k+1}. Used to state
    /// that the refutation size is at most poly_bound(|f|, k).
    fn register_bw_poly_bound(&mut self, c: &BoundedWidthConsts) -> Result<(), EnvError> {
        let name = "BoundedWidth.poly_bound";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.nat.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }
}
