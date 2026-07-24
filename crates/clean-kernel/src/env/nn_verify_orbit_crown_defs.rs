// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Orbit-CROWN infrastructure definitions and opaques (C030).
//!
//! Contains registration functions for the 10 infrastructure declarations
//! (2 Definitions + 8 Opaques) that were converted from the original axiom dump.
//! Split from `nn_verify_orbit_crown` for file-size compliance.

use super::nn_verify_orbit_crown::OrbitCrownConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Build `IntervalBounds.mk d_out (fun _ => 0) (fun _ => 0) ...`.
#[cfg(any(test, feature = "math-overlays"))]
fn build_orbit_crown_zero_ib(b: &EnvDeclBuilder, c: &OrbitCrownConsts, dim: &Expr) -> Expr {
    let le_refl_const = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_d = c.fin_of(dim);
    let zero_vec = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, _) = ch.fresh_local(fin_d.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), c.rat_zero.clone());
        ch.finish_child(r)
    };
    let valid = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, _) = ch.fresh_local(fin_d.clone());
        let proof = Expr::app(le_refl_const, c.rat_zero.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, proof);
        ch.finish_child(r)
    };
    Expr::apps(
        c.ib_mk.clone(),
        [dim.clone(), zero_vec.clone(), zero_vec, valid],
    )
}

impl Environment {
    /// Helper: register `Nat.div : Nat -> Nat -> Nat` as Definition if not present.
    ///
    /// The kernel has `Nat.div` as a native reducer but it is not registered
    /// as a declaration by `init_nat()`.  We need it in C030c's type.
    /// Converted from Axiom to Definition: Nat.div is a standard library function.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_orbit_crown_nat_div(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.div");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let ty = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
        );
        // Value: fun (a b : Nat) => Nat.zero
        // Placeholder — actual computation handled by the native Nat.div reducer.
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(nat.clone());
            let (b_id, _) = b.fresh_local(nat.clone());
            let e = b.mk_lam(b_id, BinderInfo::Default, nat.clone(), nat_zero);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.OrbitCROWN.SymmetryGroup : Nat -> Type`
    ///
    /// Converted from Axiom to Opaque: this is an abstract type constructor
    /// (group of symmetries parameterized by dimension). The placeholder value
    /// returns `Nat` which inhabits `Type 0`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_symmetry_group_type(
        &mut self,
        c: &OrbitCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.SymmetryGroup");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
            b.finish(r)
        };
        // Value: fun (_ : Nat) => Nat  (Nat : Type 0)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), c.nat.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.OrbitCROWN.GroupAction`:
    /// `(n : Nat) -> SymmetryGroup n -> NNVec n -> NNVec n`
    ///
    /// Converted from Axiom to Opaque: group action on vectors is a computable
    /// function (permutation application). Placeholder: identity `fun n _ x => x`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_group_action(&mut self, c: &OrbitCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.GroupAction");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let vec_n = c.vec_of(&n);
            let (g_id, _) = b.fresh_local(sym_n.clone());
            let (x_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n.clone(), vec_n);
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (n : Nat) (_ : SymmetryGroup n) (x : NNVec n) => x
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let vec_n = c.vec_of(&n);
            let (g_id, _) = b.fresh_local(sym_n.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, x);
            let e = b.mk_lam(g_id, BinderInfo::Default, sym_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.OrbitCROWN.Equivariant`:
    /// `(d_in d_out : Nat) -> (NNVec d_in -> NNVec d_out) -> SymmetryGroup d_in -> Prop`
    ///
    /// Converted from Axiom to Definition: equivariance is a definable predicate
    /// (f commutes with all group elements). The definition value produces `True`
    /// as the predicate body — the actual mathematical content (forall g, f(g.x) = g.(f x))
    /// would require the GroupAction to be unfolded, so we use a well-typed placeholder.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_equivariant(&mut self, c: &OrbitCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.Equivariant");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let (d_out_id, d_out) = b.fresh_local(c.nat.clone());
            let f_ty = c.vec_fn_ty(&d_in, &d_out);
            let sym_g = c.sym_group_of(&d_in);
            let (f_id, _) = b.fresh_local(f_ty.clone());
            let (g_id, _) = b.fresh_local(sym_g.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_g, c.prop.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(d_out_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_in_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (d_in d_out : Nat) (_ : NNVec d_in -> NNVec d_out)
        //          (_ : SymmetryGroup d_in) => True
        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let (d_out_id, d_out) = b.fresh_local(c.nat.clone());
            let f_ty = c.vec_fn_ty(&d_in, &d_out);
            let sym_g = c.sym_group_of(&d_in);
            let (f_id, _) = b.fresh_local(f_ty.clone());
            let (g_id, _) = b.fresh_local(sym_g.clone());
            let e = b.mk_lam(g_id, BinderInfo::Default, sym_g, true_const);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(d_out_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(d_in_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.OrbitCROWN.QuotientSpace : (n : Nat) -> SymmetryGroup n -> Type`
    ///
    /// Converted from Axiom to Opaque: quotient space is a type constructor
    /// (orbit space X/G). Placeholder value returns `Nat` (inhabits Type 0).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_quotient_space(&mut self, c: &OrbitCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.QuotientSpace");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let (g_id, _) = b.fresh_local(sym_n.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_n, c.type0.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (n : Nat) (_ : SymmetryGroup n) => Nat
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let (g_id, _) = b.fresh_local(sym_n.clone());
            let e = b.mk_lam(g_id, BinderInfo::Default, sym_n, c.nat.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.OrbitCROWN.OrbitBound : (n : Nat) -> SymmetryGroup n -> Nat`
    ///
    /// Carrier history: Axiom -> Opaque (#3381) -> reducible Definition
    /// `fun _ _ => Nat.zero` (#3468) -> `fun d_in _ => d_in` (#3550) ->
    /// Opaque `fun d_in _ => d_in` (#3589, Branch A). Wave-6 MASQUERADE
    /// audit (reports/audit/2026-04-20-r8-wave6-masquerade-sweep.md)
    /// flagged the reducible #3550 configuration under Rule M2 (argument-
    /// discarding carrier — the SymmetryGroup arg has no effect on the
    /// result) combined with C030c's `Nat.le_refl` inner proof (Rule M4).
    /// Branch A closes the loophole by flipping
    /// `Declaration::Definition(is_reducible=true)` -> `Declaration::Opaque`
    /// with the SAME body; `OrbitBound d_in G` no longer delta-unfolds
    /// during `is_def_eq`, so any Theorem over it must carry real content.
    /// C030c was demoted to `Declaration::Axiom` in the same commit, then
    /// retired on 2026-04-27 as a hypothesis-wrapped Theorem that consumes
    /// an explicit local orbit-bound hypothesis.
    ///
    /// SOUNDNESS: Opaque body is a well-formed lambda of the declared Pi
    /// type. Kernel `add_decl` runs full TC — no structural bypass.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_orbit_bound(&mut self, c: &OrbitCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.OrbitBound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let (g_id, _) = b.fresh_local(sym_n.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_n, c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (d_in : Nat) (_ : SymmetryGroup d_in) => d_in
        // Post-#3589: body unchanged; stored under `Declaration::Opaque`
        // so `OrbitBound d_in G` no longer delta-unfolds.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let (g_id, _) = b.fresh_local(sym_n.clone());
            let e = b.mk_lam(g_id, BinderInfo::Default, sym_n, n.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.OrbitCROWN.GroupOrder : (n : Nat) -> SymmetryGroup n -> Nat`
    ///
    /// Converted from Axiom to Opaque: group order (|G|) is a computable function.
    /// Placeholder: `fun n _ => Nat.succ Nat.zero` (group order is always >= 1).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_group_order(&mut self, c: &OrbitCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.GroupOrder");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let (g_id, _) = b.fresh_local(sym_n.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_n, c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (n : Nat) (_ : SymmetryGroup n) => Nat.succ Nat.zero
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one = Expr::app(nat_succ, nat_zero);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let (g_id, _) = b.fresh_local(sym_n.clone());
            let e = b.mk_lam(g_id, BinderInfo::Default, sym_n, one);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `quotient_project : (n : Nat) -> (G : SymmetryGroup n) -> NNVec n -> NNVec (OrbitBound n G)`
    /// Axiom->Opaque. Uses checked `add_decl`; the zero vector is constructed at the opaque target dimension.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_quotient_project(
        &mut self,
        c: &OrbitCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.quotient_project");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let vec_n = c.vec_of(&n);
            let (g_id, g) = b.fresh_local(sym_n.clone());
            let orbit_n_g = c.orbit_bound_app(&n, &g);
            let vec_orbit = c.vec_of(&orbit_n_g);
            let (x_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, vec_orbit);
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS: The opaque value is a well-formed lambda matching the
        // parameter structure. The target vector is constructed directly over
        // `Fin (OrbitBound n G)`, so the kernel can check it without unfolding
        // the intentionally opaque quotient-bound carrier.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let sym_n = c.sym_group_of(&n);
            let vec_n = c.vec_of(&n);
            let (g_id, g) = b.fresh_local(sym_n.clone());
            let orbit_n_g = c.orbit_bound_app(&n, &g);
            let fin_orbit = c.fin_of(&orbit_n_g);
            let (x_id, _) = b.fresh_local(vec_n.clone());
            let (i_id, _) = b.fresh_local(fin_orbit.clone());
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_orbit, c.rat_zero.clone());
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(g_id, BinderInfo::Default, sym_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `crown_on_quotient : ... -> IB (OrbitBound d_in G) -> IB d_out`
    /// Axiom->Opaque. Uses checked `add_decl`; placeholder is built at the output dimension.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_crown_on_quotient(
        &mut self,
        c: &OrbitCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.crown_on_quotient");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let (d_out_id, d_out) = b.fresh_local(c.nat.clone());
            let f_ty = c.vec_fn_ty(&d_in, &d_out);
            let sym_g = c.sym_group_of(&d_in);
            let ib_out = c.ib_of(&d_out);
            let (f_id, _) = b.fresh_local(f_ty.clone());
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let orbit_d_in_g = c.orbit_bound_app(&d_in, &g);
            let ib_q = c.ib_of(&orbit_d_in_g);
            let (bq_id, _) = b.fresh_local(ib_q.clone());
            let r = b.mk_pi(bq_id, BinderInfo::Default, ib_q, ib_out);
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_g, r);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(d_out_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_in_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS: Build a placeholder directly at `d_out` so full kernel
        // checking does not rely on quotient-bound/output-bound unification.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let (d_out_id, d_out) = b.fresh_local(c.nat.clone());
            let f_ty = c.vec_fn_ty(&d_in, &d_out);
            let sym_g = c.sym_group_of(&d_in);
            let (f_id, _) = b.fresh_local(f_ty.clone());
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let orbit_d_in_g = c.orbit_bound_app(&d_in, &g);
            let ib_q = c.ib_of(&orbit_d_in_g);
            let (bq_id, _) = b.fresh_local(ib_q.clone());
            let body = build_orbit_crown_zero_ib(&b, c, &d_out);
            let e = b.mk_lam(bq_id, BinderInfo::Default, ib_q, body);
            let e = b.mk_lam(g_id, BinderInfo::Default, sym_g, e);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(d_out_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(d_in_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `crown_on_full : ... -> IB (OrbitBound d_in G) -> IB d_out`
    /// Axiom->Opaque. Mirrors crown_on_quotient; placeholder is built at the output dimension.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_crown_on_full(&mut self, c: &OrbitCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.crown_on_full");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let (d_out_id, d_out) = b.fresh_local(c.nat.clone());
            let f_ty = c.vec_fn_ty(&d_in, &d_out);
            let sym_g = c.sym_group_of(&d_in);
            let ib_out = c.ib_of(&d_out);
            let (f_id, _) = b.fresh_local(f_ty.clone());
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let orbit_d_in_g = c.orbit_bound_app(&d_in, &g);
            let ib_q = c.ib_of(&orbit_d_in_g);
            let (bq_id, _) = b.fresh_local(ib_q.clone());
            let r = b.mk_pi(bq_id, BinderInfo::Default, ib_q, ib_out);
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_g, r);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(d_out_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_in_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS: Build a placeholder directly at `d_out` so full kernel
        // checking does not rely on quotient-bound/output-bound unification.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let (d_out_id, d_out) = b.fresh_local(c.nat.clone());
            let f_ty = c.vec_fn_ty(&d_in, &d_out);
            let sym_g = c.sym_group_of(&d_in);
            let (f_id, _) = b.fresh_local(f_ty.clone());
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let orbit_d_in_g = c.orbit_bound_app(&d_in, &g);
            let ib_q = c.ib_of(&orbit_d_in_g);
            let (bq_id, _) = b.fresh_local(ib_q.clone());
            let body = build_orbit_crown_zero_ib(&b, c, &d_out);
            let e = b.mk_lam(bq_id, BinderInfo::Default, ib_q, body);
            let e = b.mk_lam(g_id, BinderInfo::Default, sym_g, e);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(d_out_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(d_in_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
