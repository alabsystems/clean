// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — B1c mixed strict/non-strict transitivity.
//!
//! Lifts the predecessor's exact prerequisite for `Rat.le_of_sq_le_sq`: the two
//! mixed-transitivity lemmas
//!
//! - `Rat.lt_of_le_of_lt` : `∀ a b c, Rat.le a b → Rat.lt b c → Rat.lt a c`
//! - `Rat.lt_of_lt_of_le` : `∀ a b c, Rat.lt a b → Rat.le b c → Rat.lt a c`
//!
//! Both are **purely propositional** consequences of `Rat.le_trans` +
//! `Rat.lt_iff_le_not_le` (the simpler of the two routes the run-5 brief
//! sketched — no `Int.lt_cross_trans` lift is needed). `Rat.lt` is a
//! `Quot.lift` and is NEVER reduced for variable arguments; all strict-order
//! reasoning threads through `Rat.lt_iff_le_not_le` in both directions, exactly
//! as the B1b layer does.
//!
//! Additionally registers the Int-level STRICTNESS SPLITTER
//!
//! - `Int.lt_or_eq_of_le` : `∀ a b : Int, Int.le a b → Or (Int.lt a b) (Eq a b)`
//!
//! from the constructive `Int.lt_trichotomy` + `Int.lt_of_lt_of_le` +
//! `Int.lt_irrefl` (two nested `Or.rec`s; the `lt b a` disjunct is refuted).
//!
//! Every lemma here has an **empty domain-axiom closure** and classifies
//! `ProofQuality::Constructive`: `Rat.le_trans` is the constructive
//! cross-multiply transitivity Theorem (`Int.le_cross_trans` over the quotient
//! carrier) and `Rat.lt_iff_le_not_le` now reduces to the constructive
//! `Int.lt_iff_le_not_le` Theorem.
//!
//! ## Downstream
//!
//! `Rat.le_of_sq_le_sq` is registered by the B1d layer
//! (`boolean_analysis_order_toolkit_b1d.rs`), which sources the strictness its
//! `b ≤ a` branch needs from `Classical.em` (the kernel-checked Diaconescu
//! Theorem — foundational-only closure, so still `Constructive`). The
//! `Int.lt_or_eq_of_le` splitter registered here is the em-free alternative
//! core: its `Quot.sound`-lift to a `Rat.lt_or_eq_of_le` (for representatives
//! the hypothesis reduces to the cross-multiplied `Int.le`, the `lt` disjunct
//! is `Rat.lt` definitionally, and the `Eq` disjunct maps through `Quot.sound`
//! over the cross-multiplication equivalence) would make the B1d layer fully
//! em-free if that is ever wanted.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::boolean_analysis_order_toolkit_b1c_proofs::{
    build_int_lt_or_eq_of_le_proof, build_lt_of_le_of_lt_proof, build_lt_of_lt_of_le_proof,
    int_lt_or_eq_of_le_type, lt_of_le_of_lt_type, lt_of_lt_of_le_type,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize the Bonami-Beckner B1c mixed-transitivity toolkit.
    ///
    /// Registers `Rat.lt_of_le_of_lt` and `Rat.lt_of_lt_of_le` as kernel-checked
    /// `Declaration::Theorem`s. Idempotent.
    ///
    /// Depends on `init_boolean_analysis_order_toolkit_b1b` (which transitively
    /// provides `Rat.lt_iff_le_not_le`) and `register_rat_le_trans_proof`
    /// (which provides the constructive `Rat.le_trans`).
    pub fn init_boolean_analysis_order_toolkit_b1c(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_order_toolkit_b1c_init {
            return Ok(());
        }
        // B1b provides Rat.lt_iff_le_not_le (+ the B1 ≤-monotonicity surface).
        self.init_boolean_analysis_order_toolkit_b1b()?;
        // The constructive cross-multiply Rat.le_trans Theorem.
        self.register_rat_le_trans_proof()?;

        let c = OrderConsts::new();
        self.register_rat_lt_of_le_of_lt(&c)?;
        self.register_rat_lt_of_lt_of_le(&c)?;
        self.register_int_lt_or_eq_of_le()?;

        self.boolean_analysis_order_toolkit_b1c_init = true;
        Ok(())
    }

    /// `Rat.lt_of_le_of_lt : ∀ a b c, Rat.le a b → Rat.lt b c → Rat.lt a c`.
    ///
    /// le half: `Rat.le_trans a b c hab (And.left (mp hbc))`.
    /// not-le half: from `c ≤ a` and `a ≤ b`, `Rat.le_trans c a b` gives `c ≤ b`,
    /// contradicting `¬(c ≤ b)` (the `And.right` of `mp hbc`). Closed by
    /// `Iff.mpr (lt_iff a c)`.
    fn register_rat_lt_of_le_of_lt(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_of_le_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = lt_of_le_of_lt_type(c);
        let value = build_lt_of_le_of_lt_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.lt_of_lt_of_le : ∀ a b c, Rat.lt a b → Rat.le b c → Rat.lt a c`.
    ///
    /// le half: `Rat.le_trans a b c (And.left (mp hab)) hbc`.
    /// not-le half: from `b ≤ c` and `c ≤ a`, `Rat.le_trans b c a` gives `b ≤ a`,
    /// contradicting `¬(b ≤ a)` (the `And.right` of `mp hab`). Closed by
    /// `Iff.mpr (lt_iff a c)`.
    fn register_rat_lt_of_lt_of_le(&mut self, c: &OrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_of_lt_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = lt_of_lt_of_le_type(c);
        let value = build_lt_of_lt_of_le_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Int.lt_or_eq_of_le : ∀ a b : Int, Int.le a b → Or (Int.lt a b) (Eq a b)`.
    ///
    /// The Int-level STRICTNESS SPLITTER — the exact piece run 6 needs to close
    /// `Rat.le_of_sq_le_sq` (the `b ≤ a` branch of `Rat.le_total` must split
    /// into `b < a` — the strict contradiction chain — and `b = a` — the
    /// transport case; this lemma is that split's constructive core, awaiting
    /// only the `Quot.sound` lift to `Rat`).
    ///
    /// Eliminates `Int.lt_trichotomy a b` with two nested `Or.rec`s:
    /// the `lt b a` disjunct is impossible (`Int.lt_of_lt_of_le b a b` builds
    /// `lt b b`, refuted by `Int.lt_irrefl b`; `False.elim` closes the goal).
    /// All three delegates are constructive Theorems, so this is too.
    fn register_int_lt_or_eq_of_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Int.lt_or_eq_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Delegates (each idempotent / skip-if-present). The b1b/le_trans chain
        // above already pulls in lt_irrefl + trichotomy via Int.lt_iff_le_not_le's
        // registrar, but the dependency is stated explicitly here.
        self.register_int_lt_trichotomy_proof()?;
        self.register_int_lt_of_lt_of_le_proof()?;
        self.register_int_lt_irrefl_proof()?;

        let ty = int_lt_or_eq_of_le_type();
        let value = build_int_lt_or_eq_of_le_proof();
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

    /// Check if the B1c mixed-transitivity toolkit has been initialized.
    pub(crate) fn has_boolean_analysis_order_toolkit_b1c(&self) -> bool {
        self.boolean_analysis_order_toolkit_b1c_init
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    /// Lemmas registered by this module (run 5).
    const TOOLKIT: &[&str] = &[
        "Rat.lt_of_le_of_lt",
        "Rat.lt_of_lt_of_le",
        "Int.lt_or_eq_of_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_order_toolkit_b1c()
            .expect("init_boolean_analysis_order_toolkit_b1c should succeed");
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
        env.init_boolean_analysis_order_toolkit_b1c()
            .expect("first init");
        env.init_boolean_analysis_order_toolkit_b1c()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_order_toolkit_b1c());
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

    /// Each B1c lemma has an empty domain-axiom closure and is therefore
    /// classified `ProofQuality::Constructive`: it is built solely from the
    /// constructive `Rat.le_trans` and `Rat.lt_iff_le_not_le` (which now reduces
    /// to the constructive `Int.lt_iff_le_not_le` Theorem) via And/Iff plumbing.
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
