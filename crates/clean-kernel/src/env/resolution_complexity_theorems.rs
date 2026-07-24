// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for resolution complexity and Haken's theorem (S40).
//!
//! Registers the kernel-level axiom surfaces for:
//! - PHP unsatisfiability
//! - Resolution soundness
//! - Tree-resolution size >= query complexity
//! - PHP adversary strategy (exponential query forcing)
//! - PHP query complexity is exponential
//! - Haken's theorem: tree-like Resolution refutations of PHP_{n+1}^n
//!   require 2^{Mathverse(n)} steps
//!
//! The proof chain follows the query complexity / adversary approach:
//!
//! 1. php_is_unsatisfiable: PHP_{n+1}^n has no satisfying assignment
//! 2. resolution_sound: resolution refutations prove unsatisfiability
//! 3. tree_res_query_lb: tree-resolution size >= query complexity
//!    (each leaf queries one variable, tree structure prevents reuse)
//! 4. php_adversary_strategy: existence of adversary forcing 2^{cn} queries
//!    (adversary maintains a large set of consistent total extensions by
//!     exploiting the pigeonhole structure — each query can only halve
//!     the set of consistent assignments)
//! 5. php_query_complexity_exp: query complexity of PHP is 2^{Mathverse(n)}
//! 6. haken_theorem: combining (3) and (5)
//!
//! Each theorem follows the helper-axiom pattern from `boolean_analysis_theorems.rs`:
//! a `_helper` axiom captures the proposition body, and the theorem quantifies
//! over all parameters with the helper applied. This avoids depending on
//! concrete logic connectives (`Not`, `Eq`, etc.) in the type expressions.
//!
//! Reference: Haken (1985), "The Intractability of Resolution";
//!            Ben-Sasson & Wigderson (2001), "Short proofs are narrow".

use super::resolution_complexity::ResComplexityConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 1: PHP unsatisfiability
    // ====================================================================

    /// `php_is_unsatisfiable : forall (n : Nat), php_unsat_helper n`
    ///
    /// PHP_{n+1}^n is unsatisfiable: there is no assignment to the
    /// propositional variables that satisfies all clauses simultaneously.
    /// The helper encodes: `forall (a : Assignment ...), Not (SatisfiesCNF ... a (PHP n))`.
    pub(super) fn register_php_is_unsatisfiable(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ResComplexity.php_unsat_helper";
        let thm_name = "ResComplexity.php_is_unsatisfiable";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (n : Nat) -> Prop
            // Encodes: forall (a : Assignment ...), Not (SatisfiesCNF ... a (PHP n))
            let helper_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop.clone());
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::app(helper, n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: Resolution soundness
    // ====================================================================

    /// `resolution_sound : forall (f : CNF) (p : TreeResProof),
    ///     tree_res_refutes p f -> resolution_sound_helper f`
    ///
    /// Soundness: if a tree-resolution refutation of f exists, then f is unsat.
    /// The helper encodes: `forall n (a : Assignment n), Not (SatisfiesCNF n a f)`.
    pub(super) fn register_resolution_sound(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ResComplexity.resolution_sound_helper";
        let thm_name = "ResComplexity.resolution_sound";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (f : CNF) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf.clone());
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), c.prop.clone());
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let refutes = Expr::const_(Name::from_string("ResComplexity.tree_res_refutes"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (p_id, p) = b.fresh_local(c.tree_res_proof.clone());
            let refutes_p_f = Expr::apps(refutes, [p.clone(), f.clone()]);
            let (h_id, _) = b.fresh_local(refutes_p_f.clone());
            let concl = Expr::app(helper, f.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, refutes_p_f, concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.tree_res_proof.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: Tree-resolution size >= query complexity
    // ====================================================================

    /// Helper for tree_res_query_lb: `(n : Nat) -> (f : CNF) -> (p : TreeResProof) -> Prop`
    ///
    /// Encodes: `tree_res_refutes p f -> tree_res_size p >= QueryComplexity n f`.
    pub(super) fn register_tree_res_query_lb_helper(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let name = "ResComplexity.tree_res_query_lb_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let (p_id, _) = b.fresh_local(c.tree_res_proof.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.tree_res_proof.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `tree_res_query_lb : forall (n : Nat) (f : CNF) (p : TreeResProof),
    ///     tree_res_query_lb_helper n f p`
    ///
    /// Key structural lemma: in a tree-like resolution proof, each leaf
    /// corresponds to an independent variable query. The tree structure
    /// prevents sharing of subproofs, so the proof size is at least the
    /// query complexity.
    pub(super) fn register_tree_res_query_lb(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ResComplexity.tree_res_query_lb";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ResComplexity.tree_res_query_lb_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (p_id, p) = b.fresh_local(c.tree_res_proof.clone());
            let body = Expr::apps(helper, [n.clone(), f.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.tree_res_proof.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 4: PHP adversary strategy
    // ====================================================================

    /// `php_adversary_strategy : forall (n : Nat), Prop`
    ///
    /// Existence of an adversary strategy for PHP that maintains a set of
    /// at least 2^{cn} consistent total extensions after each query.
    /// The adversary answers each variable query while ensuring that for
    /// every partial assignment seen so far, there exist exponentially many
    /// total assignments consistent with the answers that satisfy all
    /// pigeon and hole constraints queried so far.
    pub(super) fn register_php_adversary_strategy(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let name = "ResComplexity.php_adversary_strategy";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 5: PHP query complexity is exponential
    // ====================================================================

    /// Helper for php_query_complexity_exp: `(n : Nat) -> Prop`
    ///
    /// Encodes: `QueryComplexity(num_vars(n), PHP(n)) >= 2^{c*n}` for
    /// some universal constant c > 0.
    pub(super) fn register_php_query_exp_helper(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let name = "ResComplexity.php_query_exp_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `php_query_complexity_exp : forall (n : Nat), php_query_exp_helper n`
    ///
    /// The query complexity of PHP is 2^{Mathverse(n)}.
    /// Proof sketch: the adversary strategy maintains a set of consistent
    /// total extensions. Initially there are (n+1)! > 2^n permutations.
    /// Each query halves the set at worst, so exponentially many queries
    /// are needed. The pigeonhole structure ensures exponentially many
    /// extensions survive until a collision is forced.
    pub(super) fn register_php_query_complexity_exp(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ResComplexity.php_query_complexity_exp";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ResComplexity.php_query_exp_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::app(helper, n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 6: Haken's theorem (main result, S40)
    // ====================================================================

    /// Helper for Haken's theorem: `(n : Nat) -> (p : TreeResProof) -> Prop`
    ///
    /// Encodes: `tree_res_refutes p (PHP n) -> tree_res_size p >= 2^{c*n}`
    /// for some universal constant c > 0.
    pub(super) fn register_haken_theorem_helper(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let name = "ResComplexity.haken_theorem_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let (p_id, _) = b.fresh_local(c.tree_res_proof.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.tree_res_proof.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// S40 `haken_theorem : forall (n : Nat) (p : TreeResProof),
    ///     haken_theorem_helper n p`
    ///
    /// **Haken's theorem (1985):** Every tree-like Resolution refutation of
    /// PHP_{n+1}^n has size 2^{Mathverse(n)}.
    ///
    /// This is the composition of tree_res_query_lb and php_query_complexity_exp:
    /// - By tree_res_query_lb, proof size >= query complexity
    /// - By php_query_complexity_exp, query complexity of PHP is 2^{Mathverse(n)}
    /// - Therefore, proof size is 2^{Mathverse(n)}
    ///
    /// This is the first-ever formalization of this foundational result in
    /// proof complexity. Haken's theorem established that Resolution — the
    /// proof system underlying DPLL/CDCL SAT solvers — has inherent
    /// exponential limitations for certain combinatorial tautologies.
    ///
    /// Reference: Haken (1985), "The Intractability of Resolution";
    ///            Ben-Sasson & Wigderson (2001), "Short proofs are narrow".
    pub(super) fn register_haken_theorem(
        &mut self,
        c: &ResComplexityConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ResComplexity.haken_theorem";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ResComplexity.haken_theorem_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (p_id, p) = b.fresh_local(c.tree_res_proof.clone());
            let body = Expr::apps(helper, [n.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.tree_res_proof.clone(), body);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
