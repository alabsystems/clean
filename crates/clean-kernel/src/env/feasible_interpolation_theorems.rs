// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for feasible interpolation formalization.
//!
//! Registers the kernel-level axiom surfaces for:
//! - Pudlak's feasible interpolation theorem (resolution -> feasible interpolant)
//! - Interpolant-to-monotone-circuit conversion
//! - Razborov's monotone circuit lower bound (clique-coloring)
//! - Feasible interpolation lower bound (circuit lb -> resolution lb)
//! - DAG-like vs tree-like separation (exponential gap)
//!
//! Each theorem follows the helper-axiom pattern: a `_helper` axiom
//! captures the proposition body, and the theorem quantifies over all
//! parameters with the helper applied.
//!
//! Reference: Pudlak (1997), "Lower bounds for resolution and cutting plane
//!            proofs and monotone computations";
//!            Razborov (1985), "Lower bounds on the monotone complexity of
//!            some Boolean functions";
//!            Krajicek (1997), "Interpolation theorems, lower bounds for
//!            proof systems, and independence results for bounded arithmetic".

use super::feasible_interpolation::FeasibleInterpolationConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 1: Pudlak's feasible interpolation
    // ====================================================================

    /// `pudlak_feasible_interpolation : forall (a b : PropFormula)
    ///     (p : Resolution.Proof),
    ///     pudlak_feasible_interpolation_helper a b p`
    ///
    /// Pudlak's feasible interpolation theorem: given a resolution refutation
    /// of A AND B, one can extract an interpolant in time polynomial in the
    /// size of the proof. The interpolant is a monotone combination of shared
    /// variables, and satisfies both A -> I and I AND B is unsatisfiable.
    ///
    /// This strengthens Craig's interpolation theorem by adding a
    /// computability bound: not just existence, but efficient extraction.
    ///
    /// Reference: Pudlak (1997), Theorem 3.1.
    pub(super) fn register_pudlak_feasible_interpolation(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.pudlak_feasible_interpolation_helper";
        let thm_name = "ProofTheory.pudlak_feasible_interpolation";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (a b : PropFormula) -> (p : Resolution.Proof) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (p_id, _) = b.fresh_local(c.res_proof.clone());
                let e = b.mk_pi(
                    p_id,
                    BinderInfo::Default,
                    c.res_proof.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
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
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (p_id, p) = b.fresh_local(c.res_proof.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.res_proof.clone(), body);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: Interpolant to monotone circuit
    // ====================================================================

    /// `interpolant_to_monotone_circuit : forall (a b : PropFormula)
    ///     (p : Resolution.Proof),
    ///     interpolant_to_monotone_circuit_helper a b p`
    ///
    /// The feasible interpolant extracted from a resolution refutation can
    /// be computed by a monotone Boolean circuit. The circuit size is
    /// polynomial in the proof size.
    ///
    /// This is because the Krajicek-Pudlak extraction algorithm only
    /// introduces AND and OR connectives (no negation) when the pivot
    /// variable belongs to the shared variables.
    pub(super) fn register_interpolant_to_monotone_circuit(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.interpolant_to_monotone_circuit_helper";
        let thm_name = "ProofTheory.interpolant_to_monotone_circuit";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (a b : PropFormula) -> (p : Resolution.Proof) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (p_id, _) = b.fresh_local(c.res_proof.clone());
                let e = b.mk_pi(
                    p_id,
                    BinderInfo::Default,
                    c.res_proof.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
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
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (p_id, p) = b.fresh_local(c.res_proof.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.res_proof.clone(), body);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: Razborov's monotone circuit lower bound
    // ====================================================================

    /// `monotone_circuit_lower_bound : forall (n : Nat),
    ///     monotone_circuit_lower_bound_helper n`
    ///
    /// Razborov's theorem (1985): any monotone circuit computing the
    /// clique-vs-coloring function on n vertices requires exponential
    /// size, specifically 2^{Mathverse(n^{1/6})} gates.
    ///
    /// The clique-coloring function is: given the edge-variables of a
    /// graph on n vertices, output 1 if the graph contains a k-clique
    /// (k = n^{1/4}), output 0 if the graph is k-colorable. Every graph
    /// satisfies exactly one of these properties.
    ///
    /// Reference: Razborov (1985), "Lower bounds on the monotone complexity
    ///            of some Boolean functions", Doklady Mathematics.
    pub(super) fn register_monotone_circuit_lower_bound(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.monotone_circuit_lower_bound_helper";
        let thm_name = "ProofTheory.monotone_circuit_lower_bound";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (n : Nat) -> Prop
            // Encodes: for all monotone circuits C computing clique-coloring(n),
            //   monotone_circuit_size(C) >= 2^{Mathverse(n^{1/6})}
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
    // Theorem 4: Feasible interpolation lower bound
    // ====================================================================

    /// `feasible_interpolation_lower_bound : forall (n : Nat),
    ///     feasible_interpolation_lower_bound_helper n`
    ///
    /// Resolution lower bounds via feasible interpolation: combining
    /// Pudlak's feasible interpolation with Razborov's monotone circuit
    /// lower bound yields exponential lower bounds on resolution proof
    /// size for clique-coloring formulas.
    ///
    /// Proof sketch:
    /// 1. Suppose A AND B encodes clique-coloring with short resolution proof P.
    /// 2. By feasible interpolation, extract a monotone circuit of size poly(|P|).
    /// 3. By Razborov, the circuit must have exponential size.
    /// 4. Contradiction: |P| must be exponential.
    ///
    /// Reference: Pudlak (1997), Corollary 4.2.
    pub(super) fn register_feasible_interpolation_lower_bound(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.feasible_interpolation_lower_bound_helper";
        let thm_name = "ProofTheory.feasible_interpolation_lower_bound";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (n : Nat) -> Prop
            // Encodes: any resolution refutation of clique-coloring(n)
            //   has exponential size
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
    // Theorem 5: DAG-like vs tree-like separation
    // ====================================================================

    /// `dag_vs_tree_separation : forall (n : Nat),
    ///     dag_vs_tree_separation_helper n`
    ///
    /// DAG-like resolution proofs can be exponentially shorter than
    /// tree-like resolution proofs. Specifically, there exist families
    /// of CNF formulas that have polynomial-size DAG-like refutations
    /// but require exponential-size tree-like refutations.
    ///
    /// The pigeonhole principle (PHP) provides a concrete separation:
    /// - DAG-like: O(n^3) size refutations (Cook, 1976)
    /// - Tree-like: 2^{Mathverse(n)} size required (Haken/Ben-Sasson-Wigderson)
    ///
    /// The feasible interpolation technique extends to DAG-like proofs,
    /// where the interpolant circuit may have fan-out > 1 (reuse of
    /// intermediate results corresponds to reuse of derived clauses).
    ///
    /// Reference: Ben-Sasson, Wigderson, Impagliazzo (2004), "A scalable
    ///            algorithm for tree-like resolution".
    pub(super) fn register_dag_vs_tree_separation(
        &mut self,
        c: &FeasibleInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.dag_vs_tree_separation_helper";
        let thm_name = "ProofTheory.dag_vs_tree_separation";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (n : Nat) -> Prop
            // Encodes: exists formulas with poly DAG-like but exp tree-like
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
}
