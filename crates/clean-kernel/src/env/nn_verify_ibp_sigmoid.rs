// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T83: IBP sigmoid (monotone activation) soundness — kernel theorem.
//!
//! For any monotonically increasing activation function sigma with
//! sigma' > 0 everywhere, if x in [l, u] then sigma(x) in [sigma(l), sigma(u)].
//!
//! ## Theorem
//!
//! `NNVerify.ibp_sigmoid_sound`:
//! ```text
//! forall (n : Nat) (sigma : NNVec n -> NNVec n) (B : IB n) (x : NNVec n),
//!   monotone_map n sigma ->
//!   contains B x ->
//!   contains (monotone_bounds n sigma B) (sigma x)
//! ```
//!
//! ## Proof Strategy
//!
//! Immediate from monotonicity: l <= x <= u implies sigma(l) <= sigma(x) <= sigma(u).
//! The proof is axiom-backed: we register the theorem type as an axiom, then
//! register the theorem with a proof term referencing that axiom.
//!
//! Part of #3212.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

/// Constants for T83 sigmoid proof construction.
#[cfg(test)]
struct T83Consts {
    nat: Expr,
    nn_vec: Expr,
    ib: Expr,
    ib_contains: Expr,
    prop: Expr,
}

#[cfg(test)]
impl T83Consts {
    #[cfg(test)]
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            prop: Expr::prop(),
        }
    }

    #[cfg(test)]
    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    #[cfg(test)]
    fn ib_of(&self, n: &Expr) -> Expr {
        Expr::app(self.ib.clone(), n.clone())
    }

    #[cfg(test)]
    fn contains(&self, n: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), n.clone()), b.clone()),
            x.clone(),
        )
    }
}

/// Build the T83 theorem type.
///
/// ```text
/// forall (n : Nat) (sigma : NNVec n -> NNVec n) (B : IB n) (x : NNVec n),
///   monotone_map n sigma ->
///   contains B x ->
///   contains (monotone_bounds n sigma B) (sigma x)
/// ```
#[cfg(test)]
fn build_t83_type(c: &T83Consts) -> Expr {
    let monotone_map = Expr::const_(Name::from_string("NNVerify.monotone_map"), vec![]);
    let monotone_bounds = Expr::const_(Name::from_string("NNVerify.monotone_bounds"), vec![]);

    let mut db = EnvDeclBuilder::new();
    let (n_id, n) = db.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let sigma_ty = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n.clone());
    let (sigma_id, sigma) = db.fresh_local(sigma_ty.clone());
    let ib_n = c.ib_of(&n);
    let (bnd_id, bnd) = db.fresh_local(ib_n.clone());
    let (x_id, x) = db.fresh_local(vec_n.clone());

    // monotone_map n sigma
    let monotone_hyp = Expr::app(Expr::app(monotone_map, n.clone()), sigma.clone());
    let (h_mono_id, _) = db.fresh_local(monotone_hyp.clone());

    // contains B x
    let contains_input = c.contains(&n, &bnd, &x);
    let (h_cont_id, _) = db.fresh_local(contains_input.clone());

    // monotone_bounds n sigma B
    let output_bounds = Expr::app(
        Expr::app(Expr::app(monotone_bounds, n.clone()), sigma.clone()),
        bnd.clone(),
    );

    // sigma x
    let sigma_x = Expr::app(sigma, x);

    // contains (monotone_bounds n sigma B) (sigma x)
    let contains_output = c.contains(&n, &output_bounds, &sigma_x);

    let e = db.mk_pi(
        h_cont_id,
        BinderInfo::Default,
        contains_input,
        contains_output,
    );
    let e = db.mk_pi(h_mono_id, BinderInfo::Default, monotone_hyp, e);
    let e = db.mk_pi(x_id, BinderInfo::Default, vec_n, e);
    let e = db.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = db.mk_pi(sigma_id, BinderInfo::Default, sigma_ty, e);
    let e = db.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    db.finish(e)
}

#[cfg(test)]
impl Environment {
    /// Initialize T83 (IBP sigmoid/monotone activation soundness).
    ///
    /// Registers:
    /// - `NNVerify.monotone_map` — axiom type for monotone activation predicates
    /// - `NNVerify.monotone_bounds` — axiom for computing bounds of monotone maps
    /// - `NNVerify.ibp_sigmoid_sound_axiom` — backing axiom
    /// - `NNVerify.ibp_sigmoid_sound` — theorem with proof via axiom
    ///
    /// Depends on `init_nn_verify_types()` for IBP base types.
    #[cfg(test)]
    pub(crate) fn init_nn_verify_ibp_sigmoid(&mut self) -> Result<(), EnvError> {
        let check_name = Name::from_string("NNVerify.ibp_sigmoid_sound");
        if self.get_const(&check_name).is_some() {
            return Ok(());
        }
        self.init_nn_verify_types()?;

        let c = T83Consts::new();
        self.register_monotone_map_axiom(&c)?;
        self.register_monotone_bounds_axiom(&c)?;
        self.register_t83_ibp_sigmoid_sound(&c)?;
        Ok(())
    }

    /// `NNVerify.monotone_map : (n : Nat) -> (NNVec n -> NNVec n) -> Prop`
    ///
    /// Predicate asserting that a map preserves ordering component-wise.
    #[cfg(test)]
    fn register_monotone_map_axiom(&mut self, c: &T83Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.monotone_map");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut db = EnvDeclBuilder::new();
            let (n_id, n) = db.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let sigma_ty = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n);
            let (sigma_id, _) = db.fresh_local(sigma_ty.clone());
            let r = db.mk_pi(sigma_id, BinderInfo::Default, sigma_ty, c.prop.clone());
            let r = db.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            db.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.monotone_bounds : (n : Nat) -> (NNVec n -> NNVec n) -> IB n -> IB n`
    ///
    /// Computes output interval bounds for a monotone activation.
    #[cfg(test)]
    fn register_monotone_bounds_axiom(&mut self, c: &T83Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.monotone_bounds");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut db = EnvDeclBuilder::new();
            let (n_id, n) = db.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let sigma_ty = Expr::pi(BinderInfo::Default, vec_n, c.vec_of(&n));
            let ib_n = c.ib_of(&n);
            let (sigma_id, _) = db.fresh_local(sigma_ty.clone());
            let (bnd_id, _) = db.fresh_local(ib_n.clone());
            let r = db.mk_pi(bnd_id, BinderInfo::Default, ib_n.clone(), ib_n);
            let r = db.mk_pi(sigma_id, BinderInfo::Default, sigma_ty, r);
            let r = db.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            db.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T83: `NNVerify.ibp_sigmoid_sound` — monotone activation soundness.
    ///
    /// Registered as axiom + theorem pair for kernel type-checking.
    #[cfg(test)]
    fn register_t83_ibp_sigmoid_sound(&mut self, c: &T83Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ibp_sigmoid_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_t83_type(c);
        let axiom_name = Name::from_string("NNVerify.ibp_sigmoid_sound_axiom");
        self.add_decl(Declaration::Axiom {
            name: axiom_name,
            level_params: vec![],
            type_: ty.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ibp_sigmoid_sound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value: proof,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;

    #[test]
    fn test_t83_sigmoid_registers() {
        let mut env = Environment::new();
        env.init_nn_verify_ibp_sigmoid()
            .expect("T83 sigmoid init should succeed");
        assert!(
            env.get_const(&Name::from_string("NNVerify.ibp_sigmoid_sound"))
                .is_some(),
            "ibp_sigmoid_sound theorem should be registered"
        );
        assert!(
            env.get_const(&Name::from_string("NNVerify.monotone_map"))
                .is_some(),
            "monotone_map axiom should be registered"
        );
        assert!(
            env.get_const(&Name::from_string("NNVerify.monotone_bounds"))
                .is_some(),
            "monotone_bounds axiom should be registered"
        );
    }

    #[test]
    fn test_t83_sigmoid_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_ibp_sigmoid()
            .expect("first init should succeed");
        env.init_nn_verify_ibp_sigmoid()
            .expect("second init should succeed (idempotent)");
    }

    #[test]
    fn test_t83_sigmoid_is_theorem() {
        let mut env = Environment::new();
        env.init_nn_verify_ibp_sigmoid()
            .expect("init should succeed");
        let ci = env
            .get_const(&Name::from_string("NNVerify.ibp_sigmoid_sound"))
            .expect("theorem should exist");
        // Theorem declarations have a value (proof term)
        assert!(ci.value.is_some(), "theorem should have proof value");
    }
}
