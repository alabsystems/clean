// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — B1 order toolkit.
//!
//! The Rat-order lemma layer that the (2,4)-hypercontractivity induction
//! (and, downstream, KKL) consumes. Every lemma here is a kernel-checked
//! `Declaration::Theorem` registered through the CHECKED `add_decl` path,
//! built entirely from the genuinely-`Constructive` Rat field/order surface
//! (`Rat.mul_nonneg`, `Rat.mul_pos`, `Rat.mul_neg`, `Rat.le_total`,
//! `Rat.add_le_add`, `Rat.mul_sub`, `Rat.sub_nonneg_of_le`,
//! `Rat.le_of_sub_nonneg`, `Rat.add_right_cancel`, `Rat.add_neg_self`,
//! `Rat.add_left_neg`, `Rat.mul_comm`, `Rat.add_comm`, ...). Because every
//! dependency is itself `ProofQuality::Constructive` (empty domain-axiom
//! closure), so is every lemma registered here.
//!
//! ## Toolkit (this run, "run 1")
//!
//! Supporting neg-algebra helpers (constructive Theorems, foundational):
//! - `Rat.neg_neg`      : `∀ a, Rat.neg (Rat.neg a) = a`
//! - `Rat.neg_mul_neg`  : `∀ a b, Rat.mul (Rat.neg a) (Rat.neg b) = Rat.mul a b`
//!
//! Order monotonicity (item 3):
//! - `Rat.mul_le_mul_of_nonneg_left`  : `b ≤ c → 0 ≤ a → a·b ≤ a·c`
//! - `Rat.mul_le_mul_of_nonneg_right` : `b ≤ c → 0 ≤ a → b·a ≤ c·a`
//!
//! Square nonnegativity + bounds (items 1, 6):
//! - `Rat.sq_nonneg`            : `∀ a, 0 ≤ a·a`
//! - `Rat.sq_le_one_of_abs_le_one` : `−1 ≤ a → a ≤ 1 → a·a ≤ 1`
//!
//! `Rat.add_le_add` (item 2), `Fin.sum_le` / `Fin.sum_nonneg` (item 5) already
//! exist in the live environment (see `nn_verify_interval_arith_proofs` /
//! `nn_verify_fin_sum`); they are reused, not re-registered.

use super::boolean_analysis_order_toolkit_proofs::{
    build_mul_le_mul_of_nonneg_left_proof, build_mul_le_mul_of_nonneg_right_proof,
    build_neg_mul_neg_proof, build_neg_neg_proof, build_sq_le_one_proof, build_sq_nonneg_proof,
    mul_le_mul_left_type, mul_le_mul_right_type, sq_le_one_type,
};
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the order-toolkit proof construction.
///
/// `pub(super)` so the split proof-term builders in
/// `boolean_analysis_order_toolkit_proofs` can construct terms without
/// duplicating the plumbing.
pub(super) struct OrderConsts {
    pub(super) rat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_one: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_neg: Expr,
    pub(super) rat_sub: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) eq: Expr,
    pub(super) eq_refl: Expr,
    pub(super) eq_symm: Expr,
    pub(super) eq_trans: Expr,
    pub(super) eq_subst: Expr,
}

impl OrderConsts {
    pub(super) fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_neg: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![u1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![u1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![u1]),
        }
    }

    pub(super) fn rat_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.rat.clone(), a, b])
    }

    pub(super) fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }

    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }

    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }

    pub(super) fn neg(&self, a: Expr) -> Expr {
        Expr::app(self.rat_neg.clone(), a)
    }

    pub(super) fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }

    /// `Eq.symm.{1} @Rat @a @b h : Eq b a`.
    pub(super) fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }

    /// `Eq.trans.{1} @Rat @a @b @c h1 h2 : Eq a c`.
    pub(super) fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, c, h1, h2])
    }

    /// `Eq.subst.{1} @Rat motive @a @b h_eq h_motive_a : motive b`.
    pub(super) fn subst(
        &self,
        motive: Expr,
        a: Expr,
        b: Expr,
        h_eq: Expr,
        h_motive_a: Expr,
    ) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h_motive_a],
        )
    }
}

impl Environment {
    /// Initialize the Bonami-Beckner B1 order toolkit.
    ///
    /// Registers the neg-algebra helpers and order-monotonicity / square
    /// lemmas as kernel-checked `Declaration::Theorem`s. Idempotent.
    ///
    /// Depends on `init_nn_verify_interval_arith_proofs`, which transitively
    /// initializes the constructive Rat field/order surface this toolkit
    /// builds on (`Rat.mul_nonneg`, `Rat.add_le_add`, `Rat.mul_neg`,
    /// `Rat.le_total`, the `sub_nonneg`/`le_of_sub_nonneg` bridge, etc.).
    pub fn init_boolean_analysis_order_toolkit(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_order_toolkit_init {
            return Ok(());
        }
        self.init_nn_verify_interval_arith_proofs()?;

        let c = OrderConsts::new();
        self.register_rat_neg_neg(&c)?;
        self.register_rat_neg_mul_neg(&c)?;
        self.register_rat_mul_le_mul_of_nonneg_left(&c)?;
        self.register_rat_mul_le_mul_of_nonneg_right(&c)?;
        self.register_rat_sq_nonneg(&c)?;
        self.register_rat_sq_le_one_of_abs_le_one(&c)?;

        self.boolean_analysis_order_toolkit_init = true;
        Ok(())
    }

    /// `Rat.neg_neg : ∀ a : Rat, Rat.neg (Rat.neg a) = a`.
    ///
    /// Proof: `Rat.add_neg_self (-a) : (-a) + (-(-a)) = 0` and
    /// `Rat.add_neg_self a : a + (-a) = 0` (used as `(-(-a)) + (-a) = 0` and
    /// `a + (-a) = 0` after a comm). Rewriting `(-a) + (-(-a))` to
    /// `(-(-a)) + (-a)` via `Rat.add_comm`, both sides equal `0`, hence equal
    /// each other, and `Rat.add_right_cancel` (cancel `(-a)` on the right)
    /// yields `-(-a) = a`.
    fn register_rat_neg_neg(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.neg_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let body = c.rat_eq(c.neg(c.neg(a.clone())), a);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        let value = build_neg_neg_proof(c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.neg_mul_neg : ∀ a b : Rat,
    ///     Rat.mul (Rat.neg a) (Rat.neg b) = Rat.mul a b`.
    ///
    /// Proof chain (all constructive):
    ///   (-a)·(-b) = -((-a)·b)   [Rat.mul_neg (-a) b]
    ///   (-a)·b    = b·(-a)      [Rat.mul_comm]
    ///   b·(-a)    = -(b·a)      [Rat.mul_neg b a]
    ///   b·a       = a·b         [Rat.mul_comm]
    /// so (-a)·b = -(a·b), hence -((-a)·b) = -(-(a·b)) = a·b  [Rat.neg_neg].
    fn register_rat_neg_mul_neg(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.neg_mul_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let lhs = c.mul(c.neg(a.clone()), c.neg(bv.clone()));
            let rhs = c.mul(a.clone(), bv.clone());
            let body = c.rat_eq(lhs, rhs);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_neg_mul_neg_proof(c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_le_mul_of_nonneg_left :
    ///     ∀ a b c, Rat.le b c → Rat.le 0 a → Rat.le (a·b) (a·c)`.
    ///
    /// Mirror of `nn_verify`'s `mul_nonneg_le_left`, registered under the
    /// canonical Mathlib name with binders ordered `(a b c)`:
    ///   1. `Rat.sub_nonneg_of_le b c h_bc : 0 ≤ c - b`
    ///   2. `Rat.mul_nonneg a (c-b) h_a h1 : 0 ≤ a·(c-b)`
    ///   3. `Rat.mul_sub a c b           : a·(c-b) = a·c - a·b`
    ///   4. Eq.subst transports (2) along (3): `0 ≤ a·c - a·b`
    ///   5. `Rat.le_of_sub_nonneg (a·b)(a·c) : a·b ≤ a·c`
    fn register_rat_mul_le_mul_of_nonneg_left(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_le_mul_of_nonneg_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = mul_le_mul_left_type(c);
        let value = build_mul_le_mul_of_nonneg_left_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_le_mul_of_nonneg_right :
    ///     ∀ a b c, Rat.le b c → Rat.le 0 a → Rat.le (b·a) (c·a)`.
    ///
    /// Derived from `Rat.mul_le_mul_of_nonneg_left` by commuting both products
    /// (`Rat.mul_comm`) and Eq.subst-transporting the conclusion endpoints.
    fn register_rat_mul_le_mul_of_nonneg_right(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_le_mul_of_nonneg_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = mul_le_mul_right_type(c);
        let value = build_mul_le_mul_of_nonneg_right_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.sq_nonneg : ∀ a : Rat, Rat.le 0 (Rat.mul a a)`.
    ///
    /// Case-split on `Rat.le_total 0 a`:
    /// - `0 ≤ a`: `Rat.mul_nonneg a a h h : 0 ≤ a·a`.
    /// - `a ≤ 0`: `Rat.sub_nonneg_of_le a 0 h : 0 ≤ 0 - a`, and `0 - a` is
    ///   definitionally `0 + (-a)`; `Rat.zero_add (-a)` rewrites it to `-a`,
    ///   giving `0 ≤ -a`. Then `Rat.mul_nonneg (-a) (-a) : 0 ≤ (-a)·(-a)`,
    ///   and `Rat.neg_mul_neg a a : (-a)·(-a) = a·a` transports it to
    ///   `0 ≤ a·a`.
    fn register_rat_sq_nonneg(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sq_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let body = c.rat_le(c.rat_zero.clone(), c.mul(a.clone(), a.clone()));
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        let value = build_sq_nonneg_proof(c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.sq_le_one_of_abs_le_one :
    ///     ∀ a, Rat.le (-1) a → Rat.le a 1 → Rat.le (a·a) 1`.
    ///
    /// `pm`-valued bound for the hypercontractivity coordinate. Case-split on
    /// `Rat.le_total 0 a`:
    /// - `0 ≤ a`: `Rat.mul_le_mul_of_nonneg_right a 1 a h_le1 h0 : a·a ≤ 1·a`,
    ///   then `Rat.one_mul a` rewrites `1·a` to `a`, giving `a·a ≤ a`; with
    ///   `a ≤ 1` (`h_le1`) and `Rat.le_trans` we get `a·a ≤ 1`.
    /// - `a ≤ 0`: from `-1 ≤ a` and `a ≤ 0` we have `-1 ≤ a ≤ 0`; the product
    ///   route uses `Rat.neg_le_neg` to turn `-1 ≤ a` into `-a ≤ 1` and
    ///   `0 ≤ -a` (via `sub_nonneg`); then `mul_le_mul_of_nonneg_right` on
    ///   `(-a) ≤ 1` with `0 ≤ -a` gives `(-a)·(-a) ≤ 1·(-a)`, and
    ///   `neg_mul_neg`, `one_mul`, `le_trans` close it against `a ≤ ... ≤ 1`.
    fn register_rat_sq_le_one_of_abs_le_one(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sq_le_one_of_abs_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = sq_le_one_type(c);
        let value = build_sq_le_one_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if the order toolkit has been initialized.
    #[cfg(test)]
    pub(crate) fn has_boolean_analysis_order_toolkit(&self) -> bool {
        self.boolean_analysis_order_toolkit_init
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    /// Lemmas registered by this module (run 1).
    const TOOLKIT: &[&str] = &[
        "Rat.neg_neg",
        "Rat.neg_mul_neg",
        "Rat.mul_le_mul_of_nonneg_left",
        "Rat.mul_le_mul_of_nonneg_right",
        "Rat.sq_nonneg",
        "Rat.sq_le_one_of_abs_le_one",
    ];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_order_toolkit()
            .expect("init_boolean_analysis_order_toolkit should succeed");
        env
    }

    /// Walk an expression; return true if any `sorry`/`sorryAx` const appears.
    fn contains_sorry(expr: &Expr) -> bool {
        let mut stack = vec![expr];
        while let Some(e) = stack.pop() {
            match e.kind() {
                ExprKind::Const(name, _) => {
                    let s = name.to_string();
                    if s == "sorry" || s == "sorryAx" {
                        return true;
                    }
                }
                ExprKind::App(f, a) => {
                    stack.push(f);
                    stack.push(a);
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    stack.push(ty);
                    stack.push(body);
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    stack.push(ty);
                    stack.push(val);
                    stack.push(body);
                }
                ExprKind::Proj(_, _, src) => stack.push(src),
                ExprKind::MData(_, body) => stack.push(body),
                _ => {}
            }
        }
        false
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis_order_toolkit()
            .expect("first init");
        env.init_boolean_analysis_order_toolkit()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_order_toolkit());
    }

    #[test]
    fn test_all_registered_as_theorems() {
        let env = env();
        for name in TOOLKIT {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be Declaration::Theorem, got {:?}",
                info.kind
            );
            assert!(info.value.is_some(), "{name} Theorem must retain a value");
        }
    }

    #[test]
    fn test_all_type_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in TOOLKIT {
            let e = Expr::const_(Name::from_string(name), vec![]);
            let ty = tc
                .infer_type(&e)
                .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got: {err:?}"));
            assert!(
                matches!(ty.kind(), ExprKind::Pi(..)),
                "{name} type should be a Pi, got {:?}",
                ty.kind()
            );
        }
    }

    #[test]
    fn test_all_sorry_free() {
        let env = env();
        for name in TOOLKIT {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            let value = info.value.as_ref().expect("Theorem has value");
            assert!(
                !contains_sorry(value),
                "{name} proof value must not contain sorry/sorryAx"
            );
        }
    }

    /// Each toolkit lemma has an empty domain-axiom closure and is therefore
    /// classified `ProofQuality::Constructive` — the foundational Rat
    /// field/order surface they build on is itself fully constructive over the
    /// quotient carrier.
    #[test]
    fn test_all_constructive_empty_axiom_closure() {
        let env = env();
        for name in TOOLKIT {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("axiom_deps should work for {name}"));
            let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name} must have empty domain-axiom closure, got {dep_names:?}"
            );
            let q = env
                .proof_quality(&Name::from_string(name))
                .unwrap_or_else(|| panic!("proof_quality should report for {name}"));
            assert!(
                matches!(q, ProofQuality::Constructive),
                "{name} must be ProofQuality::Constructive, got {q:?}"
            );
        }
    }
}
