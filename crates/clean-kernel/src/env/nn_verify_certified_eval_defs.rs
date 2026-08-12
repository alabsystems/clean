// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitions for certified computation mode.
//!
//! Registers kernel-level types for certified evaluation of neural networks
//! on concrete inputs. These definitions formalize:
//!
//! - `NNVerify.concrete_input` — a vector of rational values as network input
//! - `NNVerify.concrete_output` — a vector of rational values as network output
//! - `NNVerify.eval_trace` — trace of intermediate layer values during evaluation
//! - `NNVerify.eval_certificate` — certificate that an eval trace is correct
//! - `NNVerify.eval_matches_spec` — predicate: eval output matches specification
//!
//! Part of #3186.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for certified eval definitions.
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct CertEvalConsts {
    pub(crate) nat: Expr,
    pub(crate) rat: Expr,
    pub(crate) fin: Expr,
    pub(crate) prop: Expr,
    pub(crate) type0: Expr,
    pub(crate) nn_vec: Expr,
    pub(crate) ib: Expr,
    pub(crate) ib_contains: Expr,
    pub(crate) concrete_input: Expr,
    pub(crate) concrete_output: Expr,
    pub(crate) eval_trace: Expr,
    pub(crate) eval_certificate: Expr,
    pub(crate) list: Expr,
    pub(crate) eq: Expr,
}

#[cfg(test)]
impl CertEvalConsts {
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            concrete_input: Expr::const_(Name::from_string("NNVerify.concrete_input"), vec![]),
            concrete_output: Expr::const_(Name::from_string("NNVerify.concrete_output"), vec![]),
            eval_trace: Expr::const_(Name::from_string("NNVerify.eval_trace"), vec![]),
            eval_certificate: Expr::const_(Name::from_string("NNVerify.eval_certificate"), vec![]),
            list: Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

    /// Build `NNVec n`.
    #[cfg(test)]
    pub(crate) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    /// Build `IntervalBounds d`.
    #[cfg(test)]
    pub(crate) fn ib_of(&self, d: Expr) -> Expr {
        Expr::app(self.ib.clone(), d)
    }

    /// Build `IntervalBounds.contains d bounds vec`.
    #[cfg(test)]
    pub(crate) fn contains(&self, d: Expr, bounds: Expr, vec: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), d), bounds),
            vec,
        )
    }

    /// Build `Eq @T a b`.
    #[cfg(test)]
    pub(crate) fn mk_eq(&self, ty: Expr, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.eq.clone(), ty), a), b)
    }

    /// Build `List @T`.
    #[cfg(test)]
    pub(crate) fn list_of(&self, ty: Expr) -> Expr {
        Expr::app(self.list.clone(), ty)
    }
}

#[cfg(test)]
impl Environment {
    /// Register `NNVerify.concrete_input (n : Nat) : Type := NNVec n`.
    ///
    /// A concrete input is just a vector of rational values indexed by Fin n.
    #[cfg(test)]
    pub(crate) fn register_concrete_input(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = c.vec_of(n);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.concrete_input"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// Register `NNVerify.concrete_output (m : Nat) : Type := NNVec m`.
    ///
    /// A concrete output is a vector of rational values indexed by Fin m.
    #[cfg(test)]
    pub(crate) fn register_concrete_output(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let body = c.vec_of(m);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.concrete_output"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// Register `NNVerify.eval_trace (layers : Nat) (n : Nat) : Type := List (NNVec n)`.
    ///
    /// An eval trace records the intermediate values at each layer boundary
    /// during a forward pass. `layers` is the number of layer boundaries
    /// and `n` is the common dimension (simplified: uniform width).
    #[cfg(test)]
    pub(crate) fn register_eval_trace(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (layers_id, _layers) = b.fresh_local(c.nat.clone());
            let (n_id, _n) = b.fresh_local(c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
            let r = b.mk_pi(layers_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (layers_id, _layers) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(n);
            let body = c.list_of(vec_n);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(layers_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.eval_trace"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// Register `NNVerify.eval_certificate (layers n : Nat) : Type := Prop`.
    ///
    /// An eval certificate is a proposition asserting that the eval trace
    /// is correct — each step follows from applying the layer function to
    /// the previous step's output. The certificate type is Prop because
    /// it will be inhabited by a proof term.
    #[cfg(test)]
    pub(crate) fn register_eval_certificate(&mut self, c: &CertEvalConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (layers_id, _layers) = b.fresh_local(c.nat.clone());
            let (n_id, _n) = b.fresh_local(c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
            let r = b.mk_pi(layers_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (layers_id, _layers) = b.fresh_local(c.nat.clone());
            let (n_id, _n) = b.fresh_local(c.nat.clone());
            let body = c.prop.clone();
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(layers_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.eval_certificate"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// Register `NNVerify.eval_matches_spec (m : Nat) (output : NNVec m) (spec : NNVec m -> Prop) : Prop := spec output`.
    ///
    /// Predicate that the evaluation output matches a given specification.
    /// The spec is a predicate on output vectors (e.g., "classified as class k").
    #[cfg(test)]
    pub(crate) fn register_eval_matches_spec(
        &mut self,
        c: &CertEvalConsts,
    ) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let vec_m = c.vec_of(m);
            let (out_id, _out) = b.fresh_local(vec_m.clone());
            // spec : NNVec m -> Prop
            let spec_ty = Expr::pi(BinderInfo::Default, vec_m.clone(), c.prop.clone());
            let (spec_id, _spec) = b.fresh_local(spec_ty.clone());
            let r = b.mk_pi(spec_id, BinderInfo::Default, spec_ty, c.prop.clone());
            let r = b.mk_pi(out_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let vec_m = c.vec_of(m);
            let (out_id, out) = b.fresh_local(vec_m.clone());
            let spec_ty = Expr::pi(BinderInfo::Default, vec_m.clone(), c.prop.clone());
            let (spec_id, spec) = b.fresh_local(spec_ty.clone());
            let body = Expr::app(spec, out);
            let e = b.mk_lam(spec_id, BinderInfo::Default, spec_ty, body);
            let e = b.mk_lam(out_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.eval_matches_spec"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
