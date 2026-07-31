// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — B1d square-root monotonicity.
//!
//! The square-root monotonicity step the (2,4)-hypercontractivity envelope
//! consumes, finally unblocked by the B1c mixed-transitivity lemmas
//! (`Rat.lt_of_le_of_lt`, `Rat.lt_of_lt_of_le`):
//!
//! - `Rat.sq_lt_sq_of_lt_of_nonneg` : `∀ a b, 0 ≤ b → b < a → b·b < a·a`
//! - `Rat.le_of_sq_le_sq`           : `∀ a b, 0 ≤ a → 0 ≤ b → a·a ≤ b·b → a ≤ b`
//!
//! Both are kernel-checked `Declaration::Theorem`s registered through the
//! CHECKED `add_decl` path. `Rat.lt` is a `Quot.lift` and is NEVER reduced for
//! variable arguments; all strict-order reasoning threads through
//! `Rat.lt_iff_le_not_le`, exactly as the B1b / B1c layers do.
//!
//! ## Route for `Rat.le_of_sq_le_sq` (the run-5 blocker, now resolved)
//!
//! The `b ≤ a` branch of `Rat.le_total a b` is genuinely true only because
//! `a = b` is possible, so it cannot be closed without a *strictness source*.
//! We supply it with `Classical.em (a ≤ b)`: the negative branch hands us
//! `¬(a ≤ b)`, which — paired with `b ≤ a` from `le_total` — yields the strict
//! `b < a` via `Rat.lt_iff_le_not_le`. The contrapositive
//! `Rat.sq_lt_sq_of_lt_of_nonneg` then gives `b·b < a·a`, contradicting the
//! hypothesis `a·a ≤ b·b` through `Rat.lt_of_lt_of_le` (a self-strict
//! `b·b < b·b`), and `False.elim` closes the impossible branch.
//!
//! ## proof_quality: Constructive (empty domain-axiom closure)
//!
//! `Classical.em`'s transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS`
//! (`{propext, funext, Classical.choice}` — see `classical_em_proof.rs`), and
//! `Environment::axiom_deps` filters foundational axioms out of the reported
//! deps set. Both lemmas therefore have an **empty** domain-axiom closure and
//! classify `ProofQuality::Constructive`. (Verified explicitly in
//! `test_all_constructive_empty_axiom_closure` below, which asserts the deps
//! set is empty AND the quality is `Constructive`.)

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::boolean_analysis_order_toolkit_b1d_proofs::{
    build_le_of_sq_le_sq_proof, build_sq_lt_sq_proof, le_of_sq_le_sq_type, sq_lt_sq_type,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize the Bonami-Beckner B1d square-root monotonicity toolkit.
    ///
    /// Registers `Rat.sq_lt_sq_of_lt_of_nonneg` and `Rat.le_of_sq_le_sq` as
    /// kernel-checked `Declaration::Theorem`s. Idempotent.
    ///
    /// Depends on `init_boolean_analysis_order_toolkit_b1c` (which transitively
    /// provides the B1 ≤-monotonicity surface, the B1b strict-order bridge, and
    /// the B1c mixed-transitivity lemmas) and `init_classical` (which provides
    /// `Classical.em` + `Or` / `Or.rec`).
    pub fn init_boolean_analysis_order_toolkit_b1d(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_order_toolkit_b1d_init {
            return Ok(());
        }
        // B1c provides Rat.lt_of_le_of_lt + Rat.lt_of_lt_of_le (and, transitively,
        // the B1/B1b ≤- and strict-order surfaces this layer consumes).
        self.init_boolean_analysis_order_toolkit_b1c()?;
        // Classical.em + Or + Or.rec.
        self.init_classical()?;

        let c = OrderConsts::new();
        self.register_rat_sq_lt_sq_of_lt_of_nonneg(&c)?;
        self.register_rat_le_of_sq_le_sq(&c)?;

        self.boolean_analysis_order_toolkit_b1d_init = true;
        Ok(())
    }

    /// `Rat.sq_lt_sq_of_lt_of_nonneg : ∀ a b, Rat.le 0 b → Rat.lt b a →
    ///     Rat.lt (b·b) (a·a)`.
    ///
    /// `b ≤ a` (from `mp (b<a)`) and `0 ≤ b` give `b·b ≤ a·b`
    /// (`mul_le_mul_of_nonneg_right`); `b < a` and `0 < a`
    /// (`lt_of_le_of_lt 0 b a`) give `a·b < a·a` (`mul_lt_mul_of_pos_left`);
    /// chained by `lt_of_le_of_lt (b·b) (a·b) (a·a)`.
    fn register_rat_sq_lt_sq_of_lt_of_nonneg(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sq_lt_sq_of_lt_of_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = sq_lt_sq_type(c);
        let value = build_sq_lt_sq_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.le_of_sq_le_sq : ∀ a b, Rat.le 0 a → Rat.le 0 b →
    ///     Rat.le (a·a) (b·b) → Rat.le a b`.
    ///
    /// `Classical.em (a ≤ b)`; positive branch returns the witness. Negative
    /// branch (`¬(a ≤ b)`): `le_total a b` re-splits — `a ≤ b` returns the
    /// witness; `b ≤ a` builds `b < a` from `lt_iff.mpr ⟨b≤a, ¬(a≤b)⟩`, applies
    /// `sq_lt_sq_of_lt_of_nonneg` for `b·b < a·a`, contradicts `a·a ≤ b·b` via
    /// `lt_of_lt_of_le` (a self-strict `b·b < b·b`), and `False.elim` closes it.
    fn register_rat_le_of_sq_le_sq(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_sq_le_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = le_of_sq_le_sq_type(c);
        let value = build_le_of_sq_le_sq_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if the B1d square-root monotonicity toolkit has been initialized.
    #[cfg(test)]
    pub(crate) fn has_boolean_analysis_order_toolkit_b1d(&self) -> bool {
        self.boolean_analysis_order_toolkit_b1d_init
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    /// Lemmas registered by this module (run 6).
    const TOOLKIT: &[&str] = &["Rat.sq_lt_sq_of_lt_of_nonneg", "Rat.le_of_sq_le_sq"];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_order_toolkit_b1d()
            .expect("init_boolean_analysis_order_toolkit_b1d should succeed");
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
        env.init_boolean_analysis_order_toolkit_b1d()
            .expect("first init");
        env.init_boolean_analysis_order_toolkit_b1d()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_order_toolkit_b1d());
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

    /// Each B1d lemma has an empty domain-axiom closure and is therefore
    /// classified `ProofQuality::Constructive`. `Rat.le_of_sq_le_sq` routes
    /// through `Classical.em`, whose transitive axiom closure is `⊆
    /// FOUNDATIONAL_AXIOMS` (`{propext, funext, Classical.choice}`) and is
    /// filtered out of the reported deps set by `Environment::axiom_deps`.
    /// This test makes the em-subtlety classification explicit: it asserts both
    /// that the domain-axiom set is EMPTY and that the quality is
    /// `Constructive`.
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

    /// Belt-and-suspenders: `Rat.le_of_sq_le_sq` genuinely reaches
    /// `Classical.em` (and hence `Classical.choice`) in its transitive const
    /// closure — confirming the foundational-filtering is what keeps the deps
    /// set empty, not an accidentally-em-free proof.
    /// Walk an expression; return true if a `Classical.em` const appears.
    fn references_classical_em(expr: &Expr) -> bool {
        let mut stack = vec![expr];
        while let Some(e) = stack.pop() {
            match e.kind() {
                ExprKind::Const(name, _) if name.to_string() == "Classical.em" => {
                    return true;
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
    fn test_le_of_sq_le_sq_routes_through_classical_em() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.le_of_sq_le_sq"))
            .expect("Rat.le_of_sq_le_sq registered");
        let value = info.value.as_ref().expect("has value");
        assert!(
            references_classical_em(value),
            "Rat.le_of_sq_le_sq proof must reference Classical.em directly"
        );
    }
}
