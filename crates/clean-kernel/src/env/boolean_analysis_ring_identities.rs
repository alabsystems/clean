// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — pure `Rat` ring identities (B5 even-pair core).
//!
//! The equational layer that the (2,4)-hypercontractivity B5 step consumes:
//! square expansion and the fourth-power even-pair identity. Every lemma is a
//! kernel-checked `Declaration::Theorem` registered through the CHECKED
//! `add_decl` path, built entirely from the genuinely-`Constructive` `Rat` ring
//! surface (`Rat.left_distrib`, `Rat.right_distrib`, `Rat.mul_comm`,
//! `Rat.mul_assoc`, `Rat.add_assoc`, `Rat.add_comm`, `Rat.one_mul`,
//! `Rat.mul_neg`, `Rat.neg_neg`). Because every dependency is itself
//! `ProofQuality::Constructive` (empty domain-axiom closure), so is every lemma
//! registered here.
//!
//! ## Toolkit (this run, "run 2")
//!
//! - `Rat.add_sq`     : `(x+y)·(x+y) = (x·x + (1+1)·(x·y)) + y·y`
//!
//! Numerals are built from `Rat.one` (`2 := Rat.add Rat.one Rat.one`); the live
//! environment has no `OfNat`-based `Rat` numeral constants, so coefficients are
//! `Rat.one`-sums and the closed forms do NOT refl-reduce — they are reached by
//! chaining the proven ring lemmas above.

use super::boolean_analysis_ring_identities_proofs::{
    add_sq_type, build_add_sq_proof, build_sub_sq_proof, sub_sq_type, RingConsts,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize the Bonami-Beckner ring-identity layer (B5 even-pair core).
    ///
    /// Registers the pure `Rat` ring identities as kernel-checked
    /// `Declaration::Theorem`s. Idempotent.
    ///
    /// Depends on `init_boolean_analysis_order_toolkit`, which transitively
    /// initializes the constructive `Rat` field/ring surface this layer builds
    /// on (`Rat.left_distrib`, `Rat.right_distrib`, `Rat.mul_comm`,
    /// `Rat.mul_assoc`, `Rat.add_assoc`, `Rat.one_mul`, `Rat.mul_neg`,
    /// `Rat.neg_neg`, …).
    pub fn init_boolean_analysis_ring_identities(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_ring_identities_init {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?;

        let c = RingConsts::new();
        self.register_rat_add_sq(&c)?;
        self.register_rat_sub_sq(&c)?;

        self.boolean_analysis_ring_identities_init = true;
        Ok(())
    }

    /// `Rat.add_sq : ∀ x y : Rat, (x+y)·(x+y) = (x·x + (1+1)·(x·y)) + y·y`.
    ///
    /// Pure ring identity: `left_distrib` splits `(x+y)·(x+y)` into
    /// `(x+y)·x + (x+y)·y`; two `right_distrib`s expand each to
    /// `(x·x+y·x)+(x·y+y·y)`; `mul_comm` folds `y·x → x·y`; `add_assoc`
    /// regroups the two `x·y` terms; and `(1+1)·(x·y) = x·y + x·y`
    /// (`right_distrib` + `one_mul`) collapses them into the `2·x·y`
    /// coefficient. Constructive (empty domain-axiom closure).
    fn register_rat_add_sq(&mut self, c: &RingConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = add_sq_type(c);
        let value = build_add_sq_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.sub_sq : ∀ x y : Rat, (x−y)·(x−y) = (x·x + (1+1)·(x·(−y))) + y·y`.
    ///
    /// The `(x−y)²` mirror of `Rat.add_sq`, completing the B5 even-pair square
    /// core. Derived by instantiating the shared `add_sq_core` at `(x, −y)`
    /// (the LHS is definitionally `(x−y)·(x−y)` since `Rat.sub` is reducible),
    /// then folding the trailing `(−y)·(−y) → y·y` via `Rat.neg_mul_neg`. The
    /// cross term is left as `x·(−y)` so it is a syntactic negative of the
    /// `add_sq` cross term `x·y` (cancels in the fourth-power assembly).
    /// Constructive (empty domain-axiom closure).
    fn register_rat_sub_sq(&mut self, c: &RingConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sub_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = sub_sq_type(c);
        let value = build_sub_sq_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if the ring-identity layer has been initialized.
    pub(crate) fn has_boolean_analysis_ring_identities(&self) -> bool {
        self.boolean_analysis_ring_identities_init
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    /// Lemmas registered by this module (run 2 + run 3).
    const RING_IDENTITIES: &[&str] = &["Rat.add_sq", "Rat.sub_sq"];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_ring_identities()
            .expect("init_boolean_analysis_ring_identities should succeed");
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
        env.init_boolean_analysis_ring_identities()
            .expect("first init");
        env.init_boolean_analysis_ring_identities()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_ring_identities());
    }

    #[test]
    fn test_all_registered_as_theorems() {
        let env = env();
        for name in RING_IDENTITIES {
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
        for name in RING_IDENTITIES {
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
        for name in RING_IDENTITIES {
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

    /// Each ring identity has an empty domain-axiom closure and is therefore
    /// classified `ProofQuality::Constructive` — the foundational `Rat` ring
    /// surface they build on is itself fully constructive over the quotient
    /// carrier.
    #[test]
    fn test_all_constructive_empty_axiom_closure() {
        let env = env();
        for name in RING_IDENTITIES {
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
