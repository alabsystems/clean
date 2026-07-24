// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for tree-width bounds on resolution proof width
//! and size.
//!
//! Registers the foundational types and definitions needed to state:
//! - the Atserias-Dalmau width upper bound via primal graph tree-width
//! - the Ben-Sasson-Wigderson width-size tradeoff
//! - polynomial-size resolution refutations for bounded tree-width CNFs
//! - minimality of width and size among all refutations
//!
//! Type and operation definitions live here; theorem registrations are in
//! `tree_width_resolution_theorems.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all tree-width resolution declarations.
pub(super) struct TreeWidthResConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ResComplexity.CNF : Type (from resolution_complexity)
    pub(super) cnf: Expr,
    /// TreeWidthRes.PrimalGraph : Type
    pub(super) primal_graph: Expr,
    /// TreeWidthRes.TreeDecomposition : Type
    pub(super) tree_decomposition: Expr,
    /// TreeWidthRes.ResolutionProof : Type
    pub(super) resolution_proof: Expr,
}

impl TreeWidthResConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            cnf: Expr::const_(Name::from_string("ResComplexity.CNF"), vec![]),
            primal_graph: Expr::const_(Name::from_string("TreeWidthRes.PrimalGraph"), vec![]),
            tree_decomposition: Expr::const_(
                Name::from_string("TreeWidthRes.TreeDecomposition"),
                vec![],
            ),
            resolution_proof: Expr::const_(
                Name::from_string("TreeWidthRes.ResolutionProof"),
                vec![],
            ),
        }
    }
}

impl Environment {
    /// Initialize tree-width bounds for general resolution proofs.
    ///
    /// Depends on: `init_bool()`, `init_nat()`, `init_resolution_complexity()`.
    pub(crate) fn init_tree_width_resolution(&mut self) -> Result<(), EnvError> {
        if self.tree_width_resolution_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;
        self.init_resolution_complexity()?;

        let c = TreeWidthResConsts::new();
        // Definitions
        self.register_primal_graph_type(&c)?;
        self.register_primal_graph(&c)?;
        self.register_tree_decomposition(&c)?;
        self.register_is_valid_decomposition(&c)?;
        self.register_bag_size(&c)?;
        self.register_tree_width_of(&c)?;
        self.register_tree_width(&c)?;
        self.register_tree_width_res_resolution_proof(&c)?;
        self.register_res_proof_width(&c)?;
        self.register_resolution_width(&c)?;
        self.register_res_proof_size(&c)?;
        self.register_resolution_size(&c)?;
        self.register_initial_width(&c)?;
        self.register_num_variables(&c)?;
        self.register_is_refutation(&c)?;
        // Theorems (in tree_width_resolution_theorems.rs)
        self.register_atserias_dalmau_helper(&c)?;
        self.register_atserias_dalmau(&c)?;
        self.register_ben_sasson_wigderson_helper(&c)?;
        self.register_ben_sasson_wigderson(&c)?;
        self.register_bounded_tw_poly_size_helper(&c)?;
        self.register_bounded_tw_poly_size(&c)?;
        self.register_width_lower_bound_helper(&c)?;
        self.register_width_lower_bound(&c)?;
        self.register_size_lower_bound_helper(&c)?;
        self.register_size_lower_bound(&c)?;

        self.tree_width_resolution_init = true;
        Ok(())
    }

    /// `TreeWidthRes.PrimalGraph : Type` -- the primal graph of a CNF.
    fn register_primal_graph_type(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.PrimalGraph"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.PrimalGraph"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `TreeWidthRes.primal_graph : ResComplexity.CNF -> TreeWidthRes.PrimalGraph`
    fn register_primal_graph(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.primal_graph"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.primal_graph.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.primal_graph"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.TreeDecomposition : Type` -- a tree decomposition with bags.
    fn register_tree_decomposition(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.TreeDecomposition"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.TreeDecomposition"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `TreeWidthRes.is_valid_decomposition :
    ///     TreeWidthRes.PrimalGraph -> TreeWidthRes.TreeDecomposition -> Prop`
    fn register_is_valid_decomposition(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.is_valid_decomposition"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, _) = b.fresh_local(c.primal_graph.clone());
            let (td_id, _) = b.fresh_local(c.tree_decomposition.clone());
            let e = b.mk_pi(
                td_id,
                BinderInfo::Default,
                c.tree_decomposition.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(g_id, BinderInfo::Default, c.primal_graph.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.is_valid_decomposition"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.bag_size : TreeWidthRes.TreeDecomposition -> Nat`
    fn register_bag_size(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.bag_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.tree_decomposition.clone(),
            c.nat.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.bag_size"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.tree_width_of : TreeWidthRes.TreeDecomposition -> Nat`
    ///
    /// Tree-width of a specific decomposition = max bag size - 1.
    /// Registered as an opaque axiom; the semantic content "bag_size(td) - 1"
    /// is captured informally to avoid depending on Nat.sub reduction.
    fn register_tree_width_of(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.tree_width_of"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.tree_decomposition.clone(),
            c.nat.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.tree_width_of"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.tree_width : TreeWidthRes.PrimalGraph -> Nat`
    fn register_tree_width(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.tree_width"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.primal_graph.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.tree_width"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.ResolutionProof : Type` -- a general DAG-like resolution proof.
    fn register_tree_width_res_resolution_proof(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.ResolutionProof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.ResolutionProof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `TreeWidthRes.res_proof_width : TreeWidthRes.ResolutionProof -> Nat`
    fn register_res_proof_width(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.res_proof_width"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.resolution_proof.clone(),
            c.nat.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.res_proof_width"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.resolution_width : ResComplexity.CNF -> Nat`
    fn register_resolution_width(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.resolution_width"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.resolution_width"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.res_proof_size : TreeWidthRes.ResolutionProof -> Nat`
    fn register_res_proof_size(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.res_proof_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.resolution_proof.clone(),
            c.nat.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.res_proof_size"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.resolution_size : ResComplexity.CNF -> Nat`
    fn register_resolution_size(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.resolution_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.resolution_size"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.initial_width : ResComplexity.CNF -> Nat`
    fn register_initial_width(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.initial_width"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.initial_width"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.num_variables : ResComplexity.CNF -> Nat`
    fn register_num_variables(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.num_variables"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.num_variables"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.is_refutation :
    ///     TreeWidthRes.ResolutionProof -> ResComplexity.CNF -> Prop`
    fn register_is_refutation(&mut self, c: &TreeWidthResConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("TreeWidthRes.is_refutation"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.resolution_proof.clone());
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), c.prop.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.resolution_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("TreeWidthRes.is_refutation"),
            level_params: vec![],
            type_: ty,
        })
    }
}
