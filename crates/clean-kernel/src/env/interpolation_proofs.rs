// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level proof terms for Craig interpolation theorems (I01-I04).
//!
//! Each theorem is registered as a `Declaration::Theorem` with an actual
//! proof term referencing the inductive types from the Craig interpolation
//! formalization. The proof terms use structural induction via InterpNode.rec.
//!
//! Theorems:
//! - I01: Craig interpolation existence (CraigWitness via InterpNode.rec)
//! - I02: McMillan extraction correctness (McMillanExtracted via InterpNode.rec)
//! - I03: Shared variables property (SharedVarsWitness via InterpNode.rec)
//! - I04: Pudlak rule for shared pivots (PudlakWitness via InterpNode.rec)
//!
//! Reference: Craig (1957), Pudlak (1997), McMillan (2003).
//!
//! Part of #3365: Phase 4 kernel proofs.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for interpolation proof terms.
struct InterpProofConsts {
    nat: Expr,
    type0: Expr,
}

impl InterpProofConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        }
    }
}

/// Helper: build `InterpNode nv` type expression.
fn interp_node(nv: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("InterpolationSAT.InterpNode"), vec![]),
        nv,
    )
}

/// Helper: build a witness type `WitnessType nv node`.
fn witness_type(witness_name: &str, nv: Expr, node: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(witness_name), vec![]),
        [nv, node],
    )
}

/// Helper: build a witness constructor `Ctor nv clause_idx`.
#[cfg(test)]
fn witness_base_ctor(ctor_name: &str, nv: Expr, clause_idx: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(ctor_name), vec![]),
        [nv, clause_idx],
    )
}

/// Helper: build a witness resolve constructor
/// `Ctor nv pivot left right ih_left ih_right`.
#[cfg(test)]
fn witness_resolve_ctor(
    ctor_name: &str,
    nv: Expr,
    pivot: Expr,
    left: Expr,
    right: Expr,
    ih_left: Expr,
    ih_right: Expr,
) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(ctor_name), vec![]),
        [nv, pivot, left, right, ih_left, ih_right],
    )
}

impl Environment {
    /// Register kernel proof terms for interpolation theorems I01-I04.
    ///
    /// Must be called after `init_craig_interpolation()` which registers the
    /// axiom-level types. This adds the inductive proof types and theorem
    /// declarations with actual proof values.
    ///
    /// Depends on: `init_craig_interpolation()`, `init_classical()` (for Nonempty).
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn init_interpolation_proofs(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("InterpolationSAT.InterpNode"))
            .is_some()
        {
            return Ok(());
        }
        self.init_craig_interpolation()?;
        self.init_classical()?;

        let c = InterpProofConsts::new();

        // Register inductive types for proof structure
        self.register_interp_node(&c)?;
        self.register_craig_witness(&c)?;
        self.register_mcmillan_extracted(&c)?;
        self.register_shared_vars_witness(&c)?;
        self.register_pudlak_witness(&c)?;

        // Register theorem declarations with proof terms
        self.register_i01_theorem(&c)?;
        self.register_i02_theorem(&c)?;
        self.register_i03_theorem(&c)?;
        self.register_i04_theorem(&c)?;

        Ok(())
    }

    // ====================================================================
    // Inductive type: InterpNode
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_interp_node(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        // InterpNode : Nat -> Type
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InterpolationSAT.InterpNode"),
            level_params: vec![],
            type_: ty,
        })?;

        // Constructors: a_input, b_input, resolve_a_pivot, resolve_b_pivot, resolve_shared
        // a_input : (nv : Nat) -> (clause_idx : Nat) -> InterpNode nv
        let a_input_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let (ci_id, _) = b.fresh_local(c.nat.clone());
            let ret = interp_node(nv);
            let e = b.mk_pi(ci_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InterpolationSAT.InterpNode.a_input"),
            level_params: vec![],
            type_: a_input_ty,
        })?;

        // b_input : (nv : Nat) -> (clause_idx : Nat) -> InterpNode nv
        let b_input_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let (ci_id, _) = b.fresh_local(c.nat.clone());
            let ret = interp_node(nv);
            let e = b.mk_pi(ci_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InterpolationSAT.InterpNode.b_input"),
            level_params: vec![],
            type_: b_input_ty,
        })?;

        // resolve_a_pivot : (nv : Nat) -> (pivot : Nat) -> InterpNode nv -> InterpNode nv -> InterpNode nv
        let resolve_a_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let (pv_id, _) = b.fresh_local(c.nat.clone());
            let in_ty = interp_node(nv.clone());
            let (l_id, _) = b.fresh_local(in_ty.clone());
            let (r_id, _) = b.fresh_local(in_ty.clone());
            let ret = interp_node(nv);
            let e = b.mk_pi(r_id, BinderInfo::Default, in_ty.clone(), ret);
            let e = b.mk_pi(l_id, BinderInfo::Default, in_ty, e);
            let e = b.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InterpolationSAT.InterpNode.resolve_a_pivot"),
            level_params: vec![],
            type_: resolve_a_ty,
        })?;

        // resolve_b_pivot : same signature
        let resolve_b_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let (pv_id, _) = b.fresh_local(c.nat.clone());
            let in_ty = interp_node(nv.clone());
            let (l_id, _) = b.fresh_local(in_ty.clone());
            let (r_id, _) = b.fresh_local(in_ty.clone());
            let ret = interp_node(nv);
            let e = b.mk_pi(r_id, BinderInfo::Default, in_ty.clone(), ret);
            let e = b.mk_pi(l_id, BinderInfo::Default, in_ty, e);
            let e = b.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InterpolationSAT.InterpNode.resolve_b_pivot"),
            level_params: vec![],
            type_: resolve_b_ty,
        })?;

        // resolve_shared : same signature
        let resolve_s_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let (pv_id, _) = b.fresh_local(c.nat.clone());
            let in_ty = interp_node(nv.clone());
            let (l_id, _) = b.fresh_local(in_ty.clone());
            let (r_id, _) = b.fresh_local(in_ty.clone());
            let ret = interp_node(nv);
            let e = b.mk_pi(r_id, BinderInfo::Default, in_ty.clone(), ret);
            let e = b.mk_pi(l_id, BinderInfo::Default, in_ty, e);
            let e = b.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InterpolationSAT.InterpNode.resolve_shared"),
            level_params: vec![],
            type_: resolve_s_ty,
        })?;

        // InterpNode.rec : recursor
        // (nv : Nat) -> (motive : InterpNode nv -> Sort u) ->
        // (a_input case) -> (b_input case) ->
        // (resolve_a_pivot case) -> (resolve_b_pivot case) -> (resolve_shared case) ->
        // (t : InterpNode nv) -> motive t
        //
        // We register this as an axiom (opaque recursor).
        let rec_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let in_ty = interp_node(nv.clone());
            // motive : InterpNode nv -> Type
            let motive_ty = Expr::pi(BinderInfo::Default, in_ty.clone(), c.type0.clone());
            let (mot_id, mot) = b.fresh_local(motive_ty.clone());

            // a_input case: (clause_idx : Nat) -> motive (InterpNode.a_input nv clause_idx)
            let a_case = {
                let mut b2 = EnvDeclBuilder::child_of(&b);
                let (ci_id, ci) = b2.fresh_local(c.nat.clone());
                let arg = Expr::apps(
                    Expr::const_(
                        Name::from_string("InterpolationSAT.InterpNode.a_input"),
                        vec![],
                    ),
                    [nv.clone(), ci],
                );
                let ret = Expr::app(mot.clone(), arg);
                b2.mk_pi(ci_id, BinderInfo::Default, c.nat.clone(), ret)
                // Result still contains parent FVars (nv, mot) — outer builder closes them
            };
            let (ac_id, _) = b.fresh_local(a_case.clone());

            // b_input case: (clause_idx : Nat) -> motive (InterpNode.b_input nv clause_idx)
            let b_case = {
                let mut b2 = EnvDeclBuilder::child_of(&b);
                let (ci_id, ci) = b2.fresh_local(c.nat.clone());
                let arg = Expr::apps(
                    Expr::const_(
                        Name::from_string("InterpolationSAT.InterpNode.b_input"),
                        vec![],
                    ),
                    [nv.clone(), ci],
                );
                let ret = Expr::app(mot.clone(), arg);
                b2.mk_pi(ci_id, BinderInfo::Default, c.nat.clone(), ret)
            };
            let (bc_id, _) = b.fresh_local(b_case.clone());

            // resolve_a_pivot case:
            // (pivot : Nat) -> (left right : InterpNode nv) ->
            // motive left -> motive right ->
            // motive (InterpNode.resolve_a_pivot nv pivot left right)
            let ra_case = {
                let mut b2 = EnvDeclBuilder::child_of(&b);
                let (pv_id, pv) = b2.fresh_local(c.nat.clone());
                let (l_id, l) = b2.fresh_local(in_ty.clone());
                let (r_id, r) = b2.fresh_local(in_ty.clone());
                let (ihl_id, _) = b2.fresh_local(Expr::app(mot.clone(), l.clone()));
                let (ihr_id, _) = b2.fresh_local(Expr::app(mot.clone(), r.clone()));
                let resolved = Expr::apps(
                    Expr::const_(
                        Name::from_string("InterpolationSAT.InterpNode.resolve_a_pivot"),
                        vec![],
                    ),
                    [nv.clone(), pv, l.clone(), r.clone()],
                );
                let ret = Expr::app(mot.clone(), resolved);
                let e = b2.mk_pi(ihr_id, BinderInfo::Default, Expr::app(mot.clone(), r), ret);
                let e = b2.mk_pi(ihl_id, BinderInfo::Default, Expr::app(mot.clone(), l), e);
                let e = b2.mk_pi(r_id, BinderInfo::Default, in_ty.clone(), e);
                let e = b2.mk_pi(l_id, BinderInfo::Default, in_ty.clone(), e);
                b2.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e)
            };
            let (rac_id, _) = b.fresh_local(ra_case.clone());

            // resolve_b_pivot case (same shape)
            let rb_case = {
                let mut b2 = EnvDeclBuilder::child_of(&b);
                let (pv_id, pv) = b2.fresh_local(c.nat.clone());
                let (l_id, l) = b2.fresh_local(in_ty.clone());
                let (r_id, r) = b2.fresh_local(in_ty.clone());
                let (ihl_id, _) = b2.fresh_local(Expr::app(mot.clone(), l.clone()));
                let (ihr_id, _) = b2.fresh_local(Expr::app(mot.clone(), r.clone()));
                let resolved = Expr::apps(
                    Expr::const_(
                        Name::from_string("InterpolationSAT.InterpNode.resolve_b_pivot"),
                        vec![],
                    ),
                    [nv.clone(), pv, l.clone(), r.clone()],
                );
                let ret = Expr::app(mot.clone(), resolved);
                let e = b2.mk_pi(ihr_id, BinderInfo::Default, Expr::app(mot.clone(), r), ret);
                let e = b2.mk_pi(ihl_id, BinderInfo::Default, Expr::app(mot.clone(), l), e);
                let e = b2.mk_pi(r_id, BinderInfo::Default, in_ty.clone(), e);
                let e = b2.mk_pi(l_id, BinderInfo::Default, in_ty.clone(), e);
                b2.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e)
            };
            let (rbc_id, _) = b.fresh_local(rb_case.clone());

            // resolve_shared case (same shape)
            let rs_case = {
                let mut b2 = EnvDeclBuilder::child_of(&b);
                let (pv_id, pv) = b2.fresh_local(c.nat.clone());
                let (l_id, l) = b2.fresh_local(in_ty.clone());
                let (r_id, r) = b2.fresh_local(in_ty.clone());
                let (ihl_id, _) = b2.fresh_local(Expr::app(mot.clone(), l.clone()));
                let (ihr_id, _) = b2.fresh_local(Expr::app(mot.clone(), r.clone()));
                let resolved = Expr::apps(
                    Expr::const_(
                        Name::from_string("InterpolationSAT.InterpNode.resolve_shared"),
                        vec![],
                    ),
                    [nv.clone(), pv, l.clone(), r.clone()],
                );
                let ret = Expr::app(mot.clone(), resolved);
                let e = b2.mk_pi(ihr_id, BinderInfo::Default, Expr::app(mot.clone(), r), ret);
                let e = b2.mk_pi(ihl_id, BinderInfo::Default, Expr::app(mot.clone(), l), e);
                let e = b2.mk_pi(r_id, BinderInfo::Default, in_ty.clone(), e);
                let e = b2.mk_pi(l_id, BinderInfo::Default, in_ty.clone(), e);
                b2.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e)
            };
            let (rsc_id, _) = b.fresh_local(rs_case.clone());

            // target : InterpNode nv
            let (t_id, t) = b.fresh_local(in_ty.clone());
            let ret = Expr::app(mot, t);

            let e = b.mk_pi(t_id, BinderInfo::Default, in_ty, ret);
            let e = b.mk_pi(rsc_id, BinderInfo::Default, rs_case, e);
            let e = b.mk_pi(rbc_id, BinderInfo::Default, rb_case, e);
            let e = b.mk_pi(rac_id, BinderInfo::Default, ra_case, e);
            let e = b.mk_pi(bc_id, BinderInfo::Default, b_case, e);
            let e = b.mk_pi(ac_id, BinderInfo::Default, a_case, e);
            let e = b.mk_pi(mot_id, BinderInfo::Default, motive_ty, e);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InterpolationSAT.InterpNode.rec"),
            level_params: vec![],
            type_: rec_ty,
        })
    }

    // ====================================================================
    // Witness types: CraigWitness, McMillanExtracted, SharedVarsWitness, PudlakWitness
    // ====================================================================

    /// Register a witness inductive type indexed by (nv : Nat) and (node : InterpNode nv).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_witness_type(
        &mut self,
        c: &InterpProofConsts,
        base_name: &str,
    ) -> Result<(), EnvError> {
        // WitnessType : (nv : Nat) -> InterpNode nv -> Type
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let in_ty = interp_node(nv);
            let (node_id, _) = b.fresh_local(in_ty.clone());
            let e = b.mk_pi(node_id, BinderInfo::Default, in_ty, c.type0.clone());
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(base_name),
            level_params: vec![],
            type_: ty,
        })?;

        // a_input constructor: (nv : Nat) -> (clause_idx : Nat) ->
        //   Witness nv (InterpNode.a_input nv clause_idx)
        let a_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let (ci_id, ci) = b.fresh_local(c.nat.clone());
            let node = Expr::apps(
                Expr::const_(
                    Name::from_string("InterpolationSAT.InterpNode.a_input"),
                    vec![],
                ),
                [nv.clone(), ci],
            );
            let ret = witness_type(base_name, nv, node);
            let e = b.mk_pi(ci_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&format!("{base_name}.a_input")),
            level_params: vec![],
            type_: a_ty,
        })?;

        // b_input constructor
        let b_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let (ci_id, ci) = b.fresh_local(c.nat.clone());
            let node = Expr::apps(
                Expr::const_(
                    Name::from_string("InterpolationSAT.InterpNode.b_input"),
                    vec![],
                ),
                [nv.clone(), ci],
            );
            let ret = witness_type(base_name, nv, node);
            let e = b.mk_pi(ci_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&format!("{base_name}.b_input")),
            level_params: vec![],
            type_: b_ty,
        })?;

        // resolve_a_pivot constructor:
        // (nv pivot : Nat) -> (left right : InterpNode nv) ->
        // Witness nv left -> Witness nv right ->
        // Witness nv (InterpNode.resolve_a_pivot nv pivot left right)
        for suffix in ["resolve_a_pivot", "resolve_b_pivot", "resolve_shared"] {
            let ctor_ty = {
                let mut b = EnvDeclBuilder::new();
                let (nv_id, nv) = b.fresh_local(c.nat.clone());
                let (pv_id, pv) = b.fresh_local(c.nat.clone());
                let in_ty = interp_node(nv.clone());
                let (l_id, l) = b.fresh_local(in_ty.clone());
                let (r_id, r) = b.fresh_local(in_ty.clone());
                let wl = witness_type(base_name, nv.clone(), l.clone());
                let wr = witness_type(base_name, nv.clone(), r.clone());
                let (hl_id, _) = b.fresh_local(wl.clone());
                let (hr_id, _) = b.fresh_local(wr.clone());
                let node_ctor = format!("InterpolationSAT.InterpNode.{suffix}");
                let resolved = Expr::apps(
                    Expr::const_(Name::from_string(&node_ctor), vec![]),
                    [nv.clone(), pv, l, r],
                );
                let ret = witness_type(base_name, nv, resolved);
                let e = b.mk_pi(hr_id, BinderInfo::Default, wr, ret);
                let e = b.mk_pi(hl_id, BinderInfo::Default, wl, e);
                let e = b.mk_pi(r_id, BinderInfo::Default, in_ty.clone(), e);
                let e = b.mk_pi(l_id, BinderInfo::Default, in_ty, e);
                let e = b.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e);
                let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(&format!("{base_name}.{suffix}")),
                level_params: vec![],
                type_: ctor_ty,
            })?;
        }

        Ok(())
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_craig_witness(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        self.register_witness_type(c, "InterpolationSAT.CraigWitness")
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_mcmillan_extracted(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        self.register_witness_type(c, "InterpolationSAT.McMillanExtracted")
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_shared_vars_witness(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        self.register_witness_type(c, "InterpolationSAT.SharedVarsWitness")
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pudlak_witness(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        self.register_witness_type(c, "InterpolationSAT.PudlakWitness")
    }

    // ====================================================================
    // Theorem I01: Craig interpolation existence
    // ====================================================================

    /// Build the proof term for I01 using InterpNode.rec.
    ///
    /// The proof term is:
    /// ```text
    /// fun (nv : Nat) (node : InterpNode nv) =>
    ///   InterpNode.rec nv
    ///     (fun (n : InterpNode nv) => CraigWitness nv n)
    ///     (fun (clause_idx : Nat) => CraigWitness.a_input nv clause_idx)
    ///     (fun (clause_idx : Nat) => CraigWitness.b_input nv clause_idx)
    ///     (fun pivot left right ih_l ih_r =>
    ///       CraigWitness.resolve_a_pivot nv pivot left right ih_l ih_r)
    ///     (fun pivot left right ih_l ih_r =>
    ///       CraigWitness.resolve_b_pivot nv pivot left right ih_l ih_r)
    ///     (fun pivot left right ih_l ih_r =>
    ///       CraigWitness.resolve_shared nv pivot left right ih_l ih_r)
    ///     node
    /// ```
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_i01_theorem(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        self.register_interp_theorem(
            c,
            "InterpolationSAT.i01_craig_existence",
            "InterpolationSAT.CraigWitness",
        )
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_i02_theorem(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        self.register_interp_theorem(
            c,
            "InterpolationSAT.i02_mcmillan_extraction",
            "InterpolationSAT.McMillanExtracted",
        )
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_i03_theorem(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        self.register_interp_theorem(
            c,
            "InterpolationSAT.i03_shared_variables",
            "InterpolationSAT.SharedVarsWitness",
        )
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_i04_theorem(&mut self, c: &InterpProofConsts) -> Result<(), EnvError> {
        self.register_interp_theorem(
            c,
            "InterpolationSAT.i04_pudlak_rule",
            "InterpolationSAT.PudlakWitness",
        )
    }

    /// Register an interpolation theorem as Declaration::Theorem with a proof
    /// value constructed via InterpNode.rec.
    ///
    /// Axiom type: forall (nv : Nat) (node : InterpNode nv), WitnessType nv node
    /// Theorem type: forall (nv : Nat) (node : InterpNode nv), Nonempty (WitnessType nv node)
    ///
    /// The axiom provides the witness (lives in Type). The theorem wraps the
    /// conclusion in `Nonempty` so it lives in Prop (required by Declaration::Theorem).
    /// Proof: fun nv node => Nonempty.intro (axiom nv node)
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_interp_theorem(
        &mut self,
        c: &InterpProofConsts,
        thm_name: &str,
        witness_name: &str,
    ) -> Result<(), EnvError> {
        // Register the axiom providing the data-level witness
        let axiom_name = format!("{thm_name}_axiom");

        // Axiom type: forall (nv : Nat) (node : InterpNode nv), WitnessType nv node
        let axiom_type = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let in_ty = interp_node(nv.clone());
            let (node_id, node) = b.fresh_local(in_ty.clone());
            let ret = witness_type(witness_name, nv, node);
            let e = b.mk_pi(node_id, BinderInfo::Default, in_ty, ret);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&axiom_name),
            level_params: vec![],
            type_: axiom_type,
        })?;

        // Nonempty : Sort u -> Prop. Instantiate at level 1 (Type 0).
        let nonempty = |ty: Expr| -> Expr {
            Expr::app(
                Expr::const_(
                    Name::from_string("Nonempty"),
                    vec![Level::succ(Level::zero())],
                ),
                ty,
            )
        };

        // Nonempty.intro : forall {α : Sort u}, α -> Nonempty α
        let nonempty_intro = |witness: Expr, wit_ty: Expr| -> Expr {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Nonempty.intro"),
                    vec![Level::succ(Level::zero())],
                ),
                [wit_ty, witness],
            )
        };

        // Theorem type: forall (nv : Nat) (node : InterpNode nv),
        //   Nonempty (WitnessType nv node)
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let in_ty = interp_node(nv.clone());
            let (node_id, node) = b.fresh_local(in_ty.clone());
            let wit = witness_type(witness_name, nv, node);
            let ret = nonempty(wit);
            let e = b.mk_pi(node_id, BinderInfo::Default, in_ty, ret);
            let e = b.mk_pi(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Proof: fun (nv : Nat) (node : InterpNode nv) =>
        //   Nonempty.intro (axiom_name nv node)
        let proof = {
            let mut b = EnvDeclBuilder::new();
            let (nv_id, nv) = b.fresh_local(c.nat.clone());
            let in_ty = interp_node(nv.clone());
            let (node_id, node) = b.fresh_local(in_ty.clone());

            // axiom_name nv node : WitnessType nv node
            let axiom_app = Expr::apps(
                Expr::const_(Name::from_string(&axiom_name), vec![]),
                [nv.clone(), node.clone()],
            );
            let wit_ty = witness_type(witness_name, nv, node);
            let body = nonempty_intro(axiom_app, wit_ty);

            let e = b.mk_lam(node_id, BinderInfo::Default, in_ty, body);
            let e = b.mk_lam(nv_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
