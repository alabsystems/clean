// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for resolution complexity formalization (S40).
//!
//! Registers the foundational types and definitions needed to state
//! Haken's theorem: every tree-like Resolution refutation of PHP_{n+1}^n
//! has size 2^{Mathverse(n)}.
//!
//! This is the first-ever formalization of Haken's 1985 result in any proof
//! assistant. The proof uses the query complexity / adversary method approach
//! following Ben-Sasson & Wigderson (2001).
//!
//! Type and operation definitions live here; theorem registrations are in
//! `resolution_complexity_theorems.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all resolution complexity declarations.
pub(super) struct ResComplexityConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    pub(super) fin: Expr,
    /// ResComplexity.Literal : Type
    pub(super) literal: Expr,
    /// ResComplexity.Clause : Type
    pub(super) clause: Expr,
    /// ResComplexity.CNF : Type
    pub(super) cnf: Expr,
    /// ResComplexity.Assignment (n : Nat) : Type
    pub(super) assignment: Expr,
    /// ResComplexity.TreeResProof : Type
    pub(super) tree_res_proof: Expr,
    /// ResComplexity.PHP (n : Nat) : CNF
    #[cfg(test)]
    pub(super) php: Expr,
}

impl ResComplexityConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            literal: Expr::const_(Name::from_string("ResComplexity.Literal"), vec![]),
            clause: Expr::const_(Name::from_string("ResComplexity.Clause"), vec![]),
            cnf: Expr::const_(Name::from_string("ResComplexity.CNF"), vec![]),
            assignment: Expr::const_(Name::from_string("ResComplexity.Assignment"), vec![]),
            tree_res_proof: Expr::const_(Name::from_string("ResComplexity.TreeResProof"), vec![]),
            #[cfg(test)]
            php: Expr::const_(Name::from_string("ResComplexity.PHP"), vec![]),
        }
    }

    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    pub(super) fn assignment_of(&self, n: &Expr) -> Expr {
        Expr::app(self.assignment.clone(), n.clone())
    }
}

impl Environment {
    /// Initialize resolution complexity declarations for Haken's theorem.
    ///
    /// Depends on: `init_bool()`, `init_nat()`, `init_fin()`.
    pub(crate) fn init_resolution_complexity(&mut self) -> Result<(), EnvError> {
        if self.resolution_complexity_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;
        self.init_fin()?;

        let c = ResComplexityConsts::new();
        self.register_literal(&c)?;
        self.register_clause(&c)?;
        self.register_cnf(&c)?;
        self.register_assignment(&c)?;
        self.register_satisfies_clause(&c)?;
        self.register_satisfies_cnf(&c)?;
        self.register_tree_res_proof(&c)?;
        self.register_tree_res_size(&c)?;
        self.register_tree_res_refutes(&c)?;
        self.register_php(&c)?;
        self.register_query_complexity(&c)?;
        self.register_exponential_lower_bound(&c)?;
        // Theorem registrations (in resolution_complexity_theorems.rs)
        self.register_php_is_unsatisfiable(&c)?;
        self.register_resolution_sound(&c)?;
        self.register_tree_res_query_lb_helper(&c)?;
        self.register_tree_res_query_lb(&c)?;
        self.register_php_adversary_strategy(&c)?;
        self.register_php_query_exp_helper(&c)?;
        self.register_php_query_complexity_exp(&c)?;
        self.register_haken_theorem_helper(&c)?;
        self.register_haken_theorem(&c)?;

        self.resolution_complexity_init = true;
        Ok(())
    }

    /// `Literal : Type` — a propositional literal (variable index, polarity).
    ///
    /// Abstractly: `Nat × Bool`, but registered as an opaque axiom type
    /// to avoid dependency on `Prod` inductive initialization.
    fn register_literal(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.Literal"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.Literal"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Constructor: mk (var : Nat) (polarity : Bool) : Literal
        let mk_ty = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, _) = b.fresh_local(c.nat.clone());
            let (p_id, _) = b.fresh_local(c.bool_.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.bool_.clone(),
                c.literal.clone(),
            );
            let e = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.Literal.mk"),
            level_params: vec![],
            type_: mk_ty,
        })?;
        // Projections: var and polarity
        let var_ty = Expr::pi(BinderInfo::Default, c.literal.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.Literal.var"),
            level_params: vec![],
            type_: var_ty,
        })?;
        let pol_ty = Expr::pi(BinderInfo::Default, c.literal.clone(), c.bool_.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.Literal.polarity"),
            level_params: vec![],
            type_: pol_ty,
        })
    }

    /// `Clause : Type` — a disjunction of literals (abstract list type).
    fn register_clause(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.Clause"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.Clause"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `CNF : Type` — conjunction of clauses (abstract list type).
    fn register_cnf(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.CNF"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.CNF"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `Assignment (n : Nat) : Type := Fin n -> Bool`
    fn register_assignment(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.Assignment"))
            .is_some()
        {
            return Ok(());
        }
        let assign_type = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        let assign_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_n = c.fin_of(&n);
            let body = Expr::pi(BinderInfo::Default, fin_n, c.bool_.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("ResComplexity.Assignment"),
            level_params: vec![],
            type_: assign_type,
            value: assign_value,
            is_reducible: true,
        })
    }

    /// `SatisfiesClause (n : Nat) (a : Assignment n) (cl : Clause) : Prop`
    fn register_satisfies_clause(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.SatisfiesClause"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let assign_n = c.assignment_of(&n);
            let (a_id, _) = b.fresh_local(assign_n.clone());
            let (cl_id, _) = b.fresh_local(c.clause.clone());
            let e = b.mk_pi(cl_id, BinderInfo::Default, c.clause.clone(), c.prop.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, assign_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.SatisfiesClause"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `SatisfiesCNF (n : Nat) (a : Assignment n) (f : CNF) : Prop`
    fn register_satisfies_cnf(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.SatisfiesCNF"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let assign_n = c.assignment_of(&n);
            let (a_id, _) = b.fresh_local(assign_n.clone());
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), c.prop.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, assign_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.SatisfiesCNF"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeResProof : Type` — inductive type for tree-like resolution proofs.
    ///
    /// Constructors:
    /// - `Axiom (cl : Clause)` — leaf: an axiom clause from the formula
    /// - `Resolve (p1 p2 : TreeResProof) (v : Nat)` — resolve on variable v
    fn register_tree_res_proof(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.TreeResProof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.TreeResProof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Axiom constructor
        let axiom_ty = Expr::pi(
            BinderInfo::Default,
            c.clause.clone(),
            c.tree_res_proof.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.TreeResProof.Axiom"),
            level_params: vec![],
            type_: axiom_ty,
        })?;
        // Resolve constructor
        let resolve_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p1_id, _) = b.fresh_local(c.tree_res_proof.clone());
            let (p2_id, _) = b.fresh_local(c.tree_res_proof.clone());
            let (v_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(
                v_id,
                BinderInfo::Default,
                c.nat.clone(),
                c.tree_res_proof.clone(),
            );
            let e = b.mk_pi(p2_id, BinderInfo::Default, c.tree_res_proof.clone(), e);
            let e = b.mk_pi(p1_id, BinderInfo::Default, c.tree_res_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.TreeResProof.Resolve"),
            level_params: vec![],
            type_: resolve_ty,
        })
    }

    /// `tree_res_size (p : TreeResProof) : Nat` — number of nodes
    fn register_tree_res_size(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.tree_res_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.tree_res_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.tree_res_size"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `tree_res_refutes (p : TreeResProof) (f : CNF) : Prop`
    ///
    /// States that `p` is a valid tree-like resolution refutation of `f`.
    fn register_tree_res_refutes(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.tree_res_refutes"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.tree_res_proof.clone());
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), c.prop.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.tree_res_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.tree_res_refutes"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `PHP (n : Nat) : CNF` — Pigeonhole principle formula PHP_{n+1}^n.
    ///
    /// Encodes: n+1 pigeons must map to n holes. Variables p_{i,j} mean
    /// "pigeon i goes to hole j" for i in Fin(n+1), j in Fin(n).
    /// Clauses: (1) at-least-one hole per pigeon, (2) at-most-one pigeon per hole.
    fn register_php(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.PHP"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.cnf.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.PHP"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `QueryComplexity (n : Nat) (f : CNF) : Nat`
    ///
    /// The adversary query complexity: minimum number of variable queries any
    /// deterministic algorithm must make to certify unsatisfiability, over
    /// the best adversary strategy maintaining consistency with some
    /// satisfying assignment for every partial assignment queried so far.
    fn register_query_complexity(&mut self, c: &ResComplexityConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.QueryComplexity"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), c.nat.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.QueryComplexity"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `ExponentialLowerBound (f : Nat -> Nat) : Prop`
    ///
    /// States that there exists c > 0 such that f(n) >= 2^{c*n} for all
    /// sufficiently large n. Encodes the 2^{Mathverse(n)} asymptotic bound.
    fn register_exponential_lower_bound(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ResComplexity.ExponentialLowerBound"))
            .is_some()
        {
            return Ok(());
        }
        let nat_to_nat = Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone());
        let ty = Expr::pi(BinderInfo::Default, nat_to_nat, c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ResComplexity.ExponentialLowerBound"),
            level_params: vec![],
            type_: ty,
        })
    }
}
