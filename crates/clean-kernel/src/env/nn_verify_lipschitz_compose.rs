// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T30 kernel formalization: Lipschitz composition (submultiplicativity).
//!
//! For f: NNVec n -> NNVec n with Lipschitz constant L_f, and
//! g: NNVec n -> NNVec n with Lipschitz constant L_g, the composition
//! g . f has Lipschitz constant L_f * L_g.
//!
//! ## Declarations
//!
//! - `NNVerify.compose_fns`: function composition axiom (type only, no body)
//! - `NNVerify.is_lipschitz`: Lipschitz predicate axiom (Rat-based norm bound)
//!
//! ## Theorem
//!
//! `NNVerify.compose_lipschitz`:
//! ```text
//! forall (n : Nat) (f g : NNVec n -> NNVec n) (Lf Lg : Rat),
//!   is_lipschitz n f Lf ->
//!   is_lipschitz n g Lg ->
//!   is_lipschitz n (compose_fns n f g) (Rat.mul Lf Lg)
//! ```
//!
//! Registered as axiom+theorem pair following the established pattern.
//!
//! ## Axiom Budget
//!
//! 3 new axioms (is_lipschitz predicate, compose_fns, compose_lipschitz_axiom).
//! 1 new theorem (compose_lipschitz, backed by axiom).
//!
//! Part of #3079.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for compose_lipschitz.
#[cfg(test)]
struct ComposeLipConsts {
    nat: Expr,
    rat: Expr,
    nn_vec: Expr,
    rat_mul: Expr,
    prop: Expr,
    is_lipschitz: Expr,
    compose_fns: Expr,
}

#[cfg(test)]
impl ComposeLipConsts {
    #[cfg(test)]
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            prop: Expr::from_kind(crate::expr::ExprKind::Sort(Level::zero())),
            is_lipschitz: Expr::const_(Name::from_string("NNVerify.is_lipschitz"), vec![]),
            compose_fns: Expr::const_(Name::from_string("NNVerify.compose_fns"), vec![]),
        }
    }

    #[cfg(test)]
    fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    #[cfg(test)]
    fn endo_ty(&self, n: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.vec_of(n.clone()),
            self.vec_of(n.clone()),
        )
    }

    #[cfg(test)]
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }
}

/// `NNVerify.is_lipschitz : (n : Nat) -> (NNVec n -> NNVec n) -> Rat -> Prop`
#[cfg(test)]
fn build_is_lipschitz_type(c: &ComposeLipConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (_f_id, _f) = b.fresh_local(endo.clone());
    let (_l_id, _l) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(_l_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(_f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.compose_fns : (n : Nat) -> (NNVec n -> NNVec n) -> (NNVec n -> NNVec n) -> (NNVec n -> NNVec n)`
///
/// Definition: `compose_fns n f g = fun x => g (f x)`
#[cfg(test)]
fn build_compose_fns_type(c: &ComposeLipConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (_f_id, _) = b.fresh_local(endo.clone());
    let (_g_id, _) = b.fresh_local(endo.clone());
    let e = b.mk_pi(_g_id, BinderInfo::Default, endo.clone(), endo.clone());
    let e = b.mk_pi(_f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the compose_lipschitz type:
/// ```text
/// forall (n : Nat) (f g : NNVec n -> NNVec n) (Lf Lg : Rat),
///   is_lipschitz n f Lf ->
///   is_lipschitz n g Lg ->
///   is_lipschitz n (compose_fns n f g) (Rat.mul Lf Lg)
/// ```
#[cfg(test)]
fn build_compose_lipschitz_type(c: &ComposeLipConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (g_id, g) = b.fresh_local(endo.clone());
    let (lf_id, lf) = b.fresh_local(c.rat.clone());
    let (lg_id, lg) = b.fresh_local(c.rat.clone());

    // hypothesis 1: is_lipschitz n f Lf
    let hyp_f = Expr::app(
        Expr::app(Expr::app(c.is_lipschitz.clone(), n.clone()), f.clone()),
        lf.clone(),
    );
    let (hf_id, _) = b.fresh_local(hyp_f.clone());

    // hypothesis 2: is_lipschitz n g Lg
    let hyp_g = Expr::app(
        Expr::app(Expr::app(c.is_lipschitz.clone(), n.clone()), g.clone()),
        lg.clone(),
    );
    let (hg_id, _) = b.fresh_local(hyp_g.clone());

    // conclusion: is_lipschitz n (compose_fns n f g) (Rat.mul Lf Lg)
    let composed = Expr::app(Expr::app(Expr::app(c.compose_fns.clone(), n.clone()), f), g);
    let product = c.mul(lf, lg);
    let concl = Expr::app(
        Expr::app(Expr::app(c.is_lipschitz.clone(), n.clone()), composed),
        product,
    );

    let e = b.mk_pi(hg_id, BinderInfo::Default, hyp_g, concl);
    let e = b.mk_pi(hf_id, BinderInfo::Default, hyp_f, e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lf_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(g_id, BinderInfo::Default, endo.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
impl Environment {
    /// Initialize T30 (Lipschitz composition) declarations.
    ///
    /// Depends on `init_nn_verify_types()` and `init_rat_arith()`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: Idempotent
    #[cfg(test)]
    pub(crate) fn init_nn_verify_lipschitz_compose(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.compose_lipschitz_axiom"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat_arith()?;

        let c = ComposeLipConsts::new();

        // Steps 1-3: Register axioms via add_decl with full type checking.
        // These types involve higher-order function types
        // `(NNVec n -> NNVec n) -> ...` which previously caused stack overflow
        // in sort inference (#3304). Fixed by stack_safe wrapping + heartbeat
        // limits in infer_sort_inner.
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.is_lipschitz"),
            level_params: vec![],
            type_: build_is_lipschitz_type(&c),
        })?;

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.compose_fns"),
            level_params: vec![],
            type_: build_compose_fns_type(&c),
        })?;

        let thm_type = build_compose_lipschitz_type(&c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.compose_lipschitz_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;

        // Step 4: Register the theorem with full type checking.
        // The proof term is a reference to the backing axiom.
        let proof = Expr::const_(
            Name::from_string("NNVerify.compose_lipschitz_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.compose_lipschitz"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })?;
        Ok(())
    }
}
