// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — B1b lt↔sub bridge toolkit.
//!
//! The strict-order layer that lifts the B1 `≤`-monotonicity lemmas to the
//! strict `<` regime, en route to `Rat.le_of_sq_le_sq` (the square-root
//! monotonicity step the (2,4)-hypercontractivity envelope consumes). Every
//! lemma is a kernel-checked `Declaration::Theorem` registered through the
//! CHECKED `add_decl` path.
//!
//! `Rat.lt a b` is a `Quot.lift` over `Int.lt` and does NOT iota-reduce for
//! variable `a`/`b`; we therefore work *propositionally* through
//! `Rat.lt_iff_le_not_le a b : Iff (Rat.lt a b) (And (Rat.le a b) (Not (Rat.le b a)))`
//! in both directions, never reducing `Rat.lt` itself.
//!
//! ## Toolkit (this run, "run 4")
//!
//! Sub/add cancellation helper:
//! - `Rat.sub_add_cancel` : `∀ b c, (c − b) + b = c`
//!
//! The lt↔sub bridge:
//! - `Rat.sub_pos_of_lt`           : `∀ b c, Rat.lt b c → Rat.lt 0 (c − b)`
//! - `Rat.lt_of_sub_pos`           : `∀ b c, Rat.lt 0 (c − b) → Rat.lt b c`
//! - `Rat.mul_lt_mul_of_pos_left`  : `∀ a b c, Rat.lt b c → Rat.lt 0 a → Rat.lt (a·b) (a·c)`
//!
//! Every lemma here has an **empty domain-axiom closure** and classifies
//! `ProofQuality::Constructive`: the strict-order surface they build on
//! (`Rat.lt_iff_le_not_le` → the kernel-checked `Int.lt_iff_le_not_le`,
//! `Rat.mul_pos`) is itself fully constructive over the quotient carrier.
//!
//! ## Deferred to run 5
//!
//! - `Rat.le_of_sq_le_sq` : `∀ a b, 0 ≤ a → 0 ≤ b → a·a ≤ b·b → a ≤ b`.
//!   The `b ≤ a` branch of `Rat.le_total a b` needs a *strict* `b·b < a·a`
//!   (to contradict the `a·a ≤ b·b` hypothesis), hence `Rat.lt_of_lt_of_le`,
//!   which must be lifted from the constructive `Int.lt_cross_trans'` through
//!   the `Rat.effDenom`-positivity bridge. Not registered in run 4.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::boolean_analysis_order_toolkit_b1b_proofs::{
    build_lt_of_sub_pos_proof, build_mul_lt_mul_of_pos_left_proof, build_sub_add_cancel_proof,
    build_sub_pos_of_lt_proof, lt_of_sub_pos_type, mul_lt_mul_left_type, sub_add_cancel_type,
    sub_pos_of_lt_type,
};
use crate::env::{Declaration, EnvError, Environment};

impl Environment {
    /// Initialize the Bonami-Beckner B1b lt↔sub bridge toolkit.
    ///
    /// Registers `Rat.sub_add_cancel` and the strict-order bridge
    /// (`Rat.sub_pos_of_lt`, `Rat.lt_of_sub_pos`, `Rat.mul_lt_mul_of_pos_left`)
    /// as kernel-checked `Declaration::Theorem`s. Idempotent.
    ///
    /// Depends on `init_boolean_analysis_order_toolkit` (the B1 `≤`-monotonicity
    /// surface) and `register_rat_order_proofs` (which provides
    /// `Rat.lt_iff_le_not_le`, `Rat.mul_pos`, `Rat.zero_lt_one`).
    pub fn init_boolean_analysis_order_toolkit_b1b(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_order_toolkit_b1b_init {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?;
        // Provides Rat.lt_iff_le_not_le, Rat.mul_pos, Rat.zero_lt_one.
        self.register_rat_order_proofs()?;

        let c = OrderConsts::new();
        self.register_rat_sub_add_cancel(&c)?;
        self.register_rat_sub_pos_of_lt(&c)?;
        self.register_rat_lt_of_sub_pos(&c)?;
        self.register_rat_mul_lt_mul_of_pos_left(&c)?;
        // `Rat.le_of_sq_le_sq` (deliverable 5) is the run-5 residual: its
        // `b ≤ a` branch needs a strict `b·b < a·a` and hence `Rat.lt_of_lt_of_le`,
        // which must be lifted from the constructive `Int.lt_cross_trans'` through
        // the `Rat.effDenom`-positivity bridge. Not registered in run 4.

        self.boolean_analysis_order_toolkit_b1b_init = true;
        Ok(())
    }

    /// `Rat.sub_add_cancel : ∀ b c : Rat, (c − b) + b = c`.
    ///
    /// Since `Rat.sub c b` delta-reduces to `Rat.add c (Rat.neg b)`,
    /// `(c−b)+b ≡ (c+(-b))+b`. Then:
    ///   1. `Rat.add_assoc c (-b) b : (c+(-b))+b = c+((-b)+b)`
    ///   2. `Rat.add_left_neg b : (-b)+b = 0`, transported under `fun x => c+x`
    ///      via `Eq.subst` to give `(c−b)+b = c+0`
    ///   3. `Rat.add_zero c : c+0 = c`
    ///
    /// chained by `Eq.trans`.
    fn register_rat_sub_add_cancel(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = crate::name::Name::from_string("Rat.sub_add_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = sub_add_cancel_type(c);
        let value = build_sub_add_cancel_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.sub_pos_of_lt : ∀ b c : Rat, Rat.lt b c → Rat.lt 0 (c − b)`.
    ///
    /// Assembled propositionally through `Rat.lt_iff_le_not_le` in both
    /// directions (`Rat.lt` never reduced):
    ///   - `le` half: `Rat.sub_nonneg_of_le b c (And.left (mp lt_bc)) : 0 ≤ c−b`.
    ///   - `¬(c−b ≤ 0)` half: suppose `h : c−b ≤ 0`. `add_le_add_left h b`
    ///     gives `(c−b)+b ≤ 0+b`; rewriting LHS via `sub_add_cancel` and RHS
    ///     via `zero_add` yields `c ≤ b`, contradicting `And.right (mp lt_bc)`.
    ///   - `Iff.mpr (lt_iff_le_not_le 0 (c−b)) (And.intro …)` closes `0 < c−b`.
    fn register_rat_sub_pos_of_lt(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = crate::name::Name::from_string("Rat.sub_pos_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = sub_pos_of_lt_type(c);
        let value = build_sub_pos_of_lt_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.lt_of_sub_pos : ∀ b c : Rat, Rat.lt 0 (c − b) → Rat.lt b c`.
    ///
    /// Mirror of `Rat.sub_pos_of_lt`, reversing through the same identities:
    ///   - `le` half: `le_of_sub_nonneg b c (And.left (mp lt_0_cb)) : b ≤ c`.
    ///   - `¬(c ≤ b)` half: suppose `h : c ≤ b`. `add_le_add c b (-b) (-b) h
    ///     (le_refl (-b))` gives `c+(-b) ≤ b+(-b)`; the LHS is `c−b` by def-eq
    ///     and the RHS rewrites to `0` via `add_neg_self`, so `c−b ≤ 0`,
    ///     contradicting `And.right (mp lt_0_cb) : ¬(c−b ≤ 0)`.
    ///   - `Iff.mpr (lt_iff_le_not_le b c) (And.intro …)` closes `b < c`.
    fn register_rat_lt_of_sub_pos(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = crate::name::Name::from_string("Rat.lt_of_sub_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = lt_of_sub_pos_type(c);
        let value = build_lt_of_sub_pos_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_lt_mul_of_pos_left :
    ///     ∀ a b c, Rat.lt b c → Rat.lt 0 a → Rat.lt (a·b) (a·c)`.
    ///
    /// Via the bridge:
    ///   1. `Rat.sub_pos_of_lt b c h_bc : 0 < c−b`.
    ///   2. `Rat.mul_pos a (c−b) h_a (1) : 0 < a·(c−b)`.
    ///   3. `Rat.mul_sub a c b : a·(c−b) = a·c − a·b`, transported under
    ///      `fun x => 0 < x` ⇒ `0 < a·c − a·b`.
    ///   4. `Rat.lt_of_sub_pos (a·b) (a·c) (3) : a·b < a·c`.
    fn register_rat_mul_lt_mul_of_pos_left(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = crate::name::Name::from_string("Rat.mul_lt_mul_of_pos_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = mul_lt_mul_left_type(c);
        let value = build_mul_lt_mul_of_pos_left_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if the B1b lt↔sub bridge toolkit has been initialized.
    pub(crate) fn has_boolean_analysis_order_toolkit_b1b(&self) -> bool {
        self.boolean_analysis_order_toolkit_b1b_init
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    /// Lemmas registered by this module (run 4).
    const TOOLKIT: &[&str] = &[
        "Rat.sub_add_cancel",
        "Rat.sub_pos_of_lt",
        "Rat.lt_of_sub_pos",
        "Rat.mul_lt_mul_of_pos_left",
    ];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_order_toolkit_b1b()
            .expect("init_boolean_analysis_order_toolkit_b1b should succeed");
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
        env.init_boolean_analysis_order_toolkit_b1b()
            .expect("first init");
        env.init_boolean_analysis_order_toolkit_b1b()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_order_toolkit_b1b());
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

    /// Each B1b lemma has an empty domain-axiom closure and is therefore
    /// classified `ProofQuality::Constructive`. The strict-order surface they
    /// build on (`Rat.lt_iff_le_not_le` → `Int.lt_iff_le_not_le`, `Rat.mul_pos`)
    /// is itself a fully-constructive kernel-checked Theorem.
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
