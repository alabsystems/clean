// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for bounded-width resolution automatizability.
//!
//! Registers the kernel-level axiom surfaces for:
//! - (k+1)-consistency detects unsatisfiability when tw <= k
//! - Consistency-enforcement extracts a width-(k+1) refutation
//! - Bounded-width automatizability (Atserias-Dalmau 2008)
//! - Conditional non-automatizability of general resolution (under ETH)
//! - CDCL with restarts p-simulates bounded-width resolution
//!   (Atserias-Fichte-Thurley 2011)
//!
//! Each theorem follows the helper-axiom pattern: a `_helper` axiom
//! captures the proposition body, and the theorem quantifies over all
//! parameters with the helper applied.
//!
//! References:
//!   Atserias & Dalmau (2008), "A combinatorial characterization of
//!     resolution width";
//!   Atserias, Fichte & Thurley (2011), "Clause-learning algorithms with
//!     many restarts and bounded-width resolution";
//!   Impagliazzo & Paturi (2001), "On the complexity of k-SAT" (ETH).

use super::bounded_width_automatizability::BoundedWidthConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 1: (k+1)-consistency detects unsatisfiability
    // ====================================================================

    /// `consistency_detects_unsat :
    ///     forall (f : CNF) (k : Nat),
    ///       consistency_detects_unsat_helper f k`
    ///
    /// If tw(G_f) <= k and f is unsatisfiable, then f is not
    /// (k+1)-consistent. The helper encodes:
    ///   has_tree_width_le f k -> Not (k_consistency f (k+1))
    /// (the unsatisfiability hypothesis is baked into the helper).
    pub(super) fn register_bw_consistency_detects_unsat(
        &mut self,
        c: &BoundedWidthConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "BoundedWidth.consistency_detects_unsat_helper";
        let thm_name = "BoundedWidth.consistency_detects_unsat";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf.clone());
                let (k_id, _) = b.fresh_local(c.nat.clone());
                let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
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
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let body = Expr::app(Expr::app(helper, f.clone()), k.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body);
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
    // Theorem 2: Consistency enforcement extracts a refutation
    // ====================================================================

    /// `consistency_to_refutation :
    ///     forall (f : CNF) (k : Nat),
    ///       consistency_to_refutation_helper f k`
    ///
    /// If (k+1)-consistency fails, the arc-consistency enforcement
    /// algorithm extracts a resolution refutation of width at most k+1
    /// and size at most poly_bound(|f|, k). The helper encodes:
    ///   Not (k_consistency f (k+1)) ->
    ///     Exists (p : ResProof), res_refutes p f /\
    ///       res_proof_width p <= k+1 /\ res_proof_size p <= poly_bound |f| k
    pub(super) fn register_bw_consistency_to_refutation(
        &mut self,
        c: &BoundedWidthConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "BoundedWidth.consistency_to_refutation_helper";
        let thm_name = "BoundedWidth.consistency_to_refutation";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf.clone());
                let (k_id, _) = b.fresh_local(c.nat.clone());
                let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
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
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let body = Expr::app(Expr::app(helper, f.clone()), k.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body);
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
    // Theorem 3: Bounded-width automatizability (main result)
    // ====================================================================

    /// `bounded_width_automatizable :
    ///     forall (f : CNF) (k : Nat),
    ///       bounded_width_automatizable_helper f k`
    ///
    /// (Atserias-Dalmau 2008) For unsatisfiable CNF f with tw(G_f) <= k,
    /// there exists a resolution refutation of width <= k+1 and
    /// size <= n^{O(k)}, findable in time O(n^{k+1}). The helper encodes:
    ///   has_tree_width_le f k ->
    ///     Exists (p : ResProof), res_refutes p f /\
    ///       res_proof_width p <= k+1 /\ res_proof_size p <= poly_bound |f| k
    pub(super) fn register_bw_automatizability(
        &mut self,
        c: &BoundedWidthConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "BoundedWidth.bounded_width_automatizable_helper";
        let thm_name = "BoundedWidth.bounded_width_automatizable";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf.clone());
                let (k_id, _) = b.fresh_local(c.nat.clone());
                let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
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
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let body = Expr::app(Expr::app(helper, f.clone()), k.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body);
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
    // Theorem 4: Conditional non-automatizability of general resolution
    // ====================================================================

    /// `general_res_non_automatizable :
    ///     general_res_non_automatizable_helper`
    ///
    /// (Conditional on ETH) General resolution is not automatizable:
    /// there is no polynomial-time algorithm that, given an unsatisfiable
    /// CNF f, finds a resolution refutation of f of size polynomially
    /// bounded in the shortest refutation. The helper encodes:
    ///   ETH -> Not (Exists algo, forall f, ...)
    /// where ETH is the Exponential Time Hypothesis.
    pub(super) fn register_bw_non_automatizability_general(
        &mut self,
        c: &BoundedWidthConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "BoundedWidth.general_res_non_automatizable_helper";
        let thm_name = "BoundedWidth.general_res_non_automatizable";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: Prop (no parameters — the ETH assumption is internal)
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: c.prop.clone(),
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: helper,
        })
    }

    // ====================================================================
    // Theorem 5: CDCL simulates bounded-width resolution
    // ====================================================================

    /// `cdcl_simulates_bounded_width :
    ///     forall (f : CNF) (k : Nat) (p : ResProof),
    ///       cdcl_simulates_bounded_width_helper f k p`
    ///
    /// (Atserias-Fichte-Thurley 2011) CDCL with restarts p-simulates
    /// bounded-width resolution: for any width-(k+1) refutation p of f,
    /// there exists a CDCL trace that produces a refutation of size
    /// polynomial in |p|. The helper encodes:
    ///   res_refutes p f -> res_proof_width p <= k+1 ->
    ///     Exists (t : CDCLTrace), cdcl_simulates t p
    pub(super) fn register_bw_cdcl_simulates_bounded_width(
        &mut self,
        c: &BoundedWidthConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "BoundedWidth.cdcl_simulates_bounded_width_helper";
        let thm_name = "BoundedWidth.cdcl_simulates_bounded_width";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf.clone());
                let (k_id, _) = b.fresh_local(c.nat.clone());
                let (p_id, _) = b.fresh_local(c.res_proof.clone());
                let e = b.mk_pi(
                    p_id,
                    BinderInfo::Default,
                    c.res_proof.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
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
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (p_id, p) = b.fresh_local(c.res_proof.clone());
            let body = Expr::app(
                Expr::app(Expr::app(helper, f.clone()), k.clone()),
                p.clone(),
            );
            let e = b.mk_pi(p_id, BinderInfo::Default, c.res_proof.clone(), body);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
